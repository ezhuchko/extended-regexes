import Regex.Finiteness.ListHelpers
import Regex.Finiteness.NeSubsets
import Regex.Finiteness.Similarity

open RE List Sim

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

/-!
# Permute

This file contains the definitions of `toSum` and `toSumSubsets`.
These functions are needed in order to define the overapproximation for the set of
all derivatives.

The permutations inside `neSubsets` are due to using deduplication instead
of commutativity in `Sim`, so the over-approximation must contain every ordering.
-/

/-- Folds a given list of regexes into a sum, where a one-element list folds to
a singleton. -/
def toSum : List (RE α) → RE α
  | []  => Pred ⊥
  | [a] => a
  | a::b::bs => a ⋓ toSum (b::bs)

@[simp] theorem toSum_nil : toSum ([] : List (RE α)) = Pred ⊥ := rfl

@[simp] theorem toSum_singleton (a : RE α) : toSum [a] = a := rfl

@[simp] theorem toSum_cons_cons (a b : RE α) (bs : List (RE α)) :
  toSum (a :: b :: bs) = (a ⋓ toSum (b :: bs)) := rfl

/-- `toSum` of a cons is literally a `⋓` when the tail is nonempty. -/
theorem toSum_cons {as : List (RE α)} (a : RE α) (h : as ≠ []) :
  toSum (a :: as) = (a ⋓ toSum as) := by
  match as with
  | _ :: _ => rfl

def toSumSubsets (xs : List (RE α)) : List (RE α) := xs |> neSubsets |> map toSum
prefix:max "⊕" => toSumSubsets

/-! ### Similarity of folds -/

/-- Splitting a fold at an append, up to `≅`. -/
theorem toSum_append {xs ys : List (RE α)} (hx : xs ≠ []) (hy : ys ≠ []) :
  toSum (xs ++ ys) ≅ (toSum xs ⋓ toSum ys) := by
  match xs with
  | [x] =>
    rw [singleton_append, toSum_cons x hy]
    exact refl
  | x :: x' :: xs =>
    have ih := toSum_append (xs := x' :: xs) (by simp) hy
    simp only [cons_append, toSum_cons_cons] at ih ⊢
    exact trans (alt_cong refl ih) (symm assoc)

theorem toSum_alt_cong {x y : RE α} {xs ys : List (RE α)} (hx : xs ≠ []) (hy : ys ≠ [])
  (eqv : x ≅ y) (eqv_fs : toSum xs ≅ toSum ys) :
  toSum (x :: xs) ≅ toSum (y :: ys) := by
  rw [toSum_cons x hx, toSum_cons y hy]
  exact alt_cong eqv eqv_fs

/-- A fold absorbs any summand it already contains. -/
theorem toSum_absorb_mem {x : RE α} {xs : List (RE α)} (h : x ∈ xs) :
  toSum xs ≅ (toSum xs ⋓ x) := by
  match xs with
  | [] => simp at h
  | [y] =>
    obtain rfl := mem_singleton.mp h
    exact symm idem
  | y :: y' :: ys =>
    rw [toSum_cons_cons]
    rcases mem_cons.mp h with rfl | h
    · exact trans (symm dedup) (symm assoc)
    · exact trans (alt_cong refl (toSum_absorb_mem h)) (symm assoc)

/-- If `x` already occurs in the prefix `l₁`,
    a further occurrence anywhere after it can be dropped. -/
theorem toSum_dedup {x : RE α} {l₁ l₂ : List (RE α)} (h : x ∈ l₁) :
  toSum (l₁ ++ x :: l₂) ≅ toSum (l₁ ++ l₂) := by
  have h1 : l₁ ≠ [] := ne_nil_of_mem h
  have habs : (toSum l₁ ⋓ x) ≅ toSum l₁ := symm (toSum_absorb_mem h)
  match l₂ with
  | [] =>
    rw [append_nil]
    exact trans (toSum_append (ys := [x]) h1 (by simp)) habs
  | y :: ys =>
    refine trans (toSum_append h1 (by simp)) ?_
    rw [toSum_cons_cons]
    refine trans (symm assoc) ?_
    exact trans (alt_cong habs refl) (symm (toSum_append h1 (by simp)))

/-- Erasing every copy of `x` from `l₂` leaves the fold unchanged, provided `x`
    still occurs in the prefix `l₁`. -/
theorem toSum_eraseAll [BEq (RE α)] [LawfulBEq (RE α)] {x : RE α} {l₁ l₂ : List (RE α)}
  (h : x ∈ l₁) :
  toSum (l₁ ++ List.eraseAll x l₂) ≅ toSum (l₁ ++ l₂) := by
  match l₂ with
  | [] => exact refl
  | a :: as =>
    by_cases hax : a = x
    · subst hax
      rw [eraseAll_cons_self]
      exact trans (toSum_eraseAll (l₂ := as) h) (symm (toSum_dedup h))
    · rw [eraseAll_cons_of_ne (fun he => hax he.symm)]
      simpa using toSum_eraseAll (x := x) (l₁ := l₁ ++ [a]) (l₂ := as) (mem_append_left _ h)

/-- Deduplicating a fold does not change it up to `≅`. -/
theorem toSum_smartDedup [BEq (RE α)] [LawfulBEq (RE α)] (xs : List (RE α)) :
  toSum (smartDedup xs) ≅ toSum xs := by
  match xs with
  | [] => exact refl
  | x :: xs =>
    have hstep : toSum (x :: List.eraseAll x (smartDedup xs)) ≅ toSum (x :: smartDedup xs) := by
      simpa using toSum_eraseAll (x := x) (l₁ := [x]) (l₂ := smartDedup xs) (by simp)
    have htail : toSum (x :: smartDedup xs) ≅ toSum (x :: xs) := by
      by_cases hne : xs = []
      · subst hne; exact refl
      · rw [toSum_cons _ (smartDedup_ne_nil hne), toSum_cons _ hne]
        exact alt_cong refl (toSum_smartDedup xs)
    rw [smartDedup_cons]
    exact trans hstep htail

theorem subset_sim_toSum {xs ys : List (RE α)} (ne : xs ≠ []) (h : xs ⊆[ (· ≅ ·) ] ys) :
  ∃ us : List (RE α), us ⊆ ys ∧ us ≠ [] ∧ toSum xs ≅ toSum us := by
  match xs with
  | [x] =>
    obtain ⟨y, hxy, hy⟩ := h x (by simp)
    exact ⟨[y], by simpa using hy, cons_ne_nil y [], hxy⟩
  | x :: x' :: xs =>
    obtain ⟨y, hxy, hy⟩ := h x (by simp)
    obtain ⟨us, sb, hus, eq⟩ :=
      subset_sim_toSum (cons_ne_nil x' xs) fun z hz => h z (mem_cons_of_mem x hz)
    exact ⟨y :: us, cons_subset.mpr ⟨hy, sb⟩, cons_ne_nil y us,
      toSum_alt_cong (cons_ne_nil x' xs) hus hxy eq⟩

/-- Every nonempty fold is similar to the fold of a duplicate-free sublist: its
    `smartDedup`. -/
theorem nodup_equiv (xs : List (RE α)) (ne : xs ≠ []) :
  ∃ zs : List (RE α), Nodup zs ∧ zs ≠ [] ∧ zs ⊆ xs ∧ toSum xs ≅ toSum zs := by
  classical
  exact ⟨smartDedup xs, smartDedup_nodup, smartDedup_ne_nil ne,
    fun x hx => (mem_smartDedup_iff x xs).mp hx, symm (toSum_smartDedup xs)⟩

theorem toSumnodup_equiv {xs ys : List (RE α)} (ne : xs ≠ []) (h : xs ⊆[ (· ≅ ·) ] ys) :
  ∃ us : List (RE α), Nodup us ∧ us ≠ [] ∧ us ⊆ ys ∧ toSum xs ≅ toSum us :=
  have ⟨xs', xs'_ys, xs'_ne, xs_xs'⟩ := subset_sim_toSum ne h
  have ⟨us, nd, us_xs', p, xs'_us⟩ := nodup_equiv xs' xs'_ne
  ⟨us, nd, us_xs', List.Subset.trans p xs'_ys, trans xs_xs' xs'_us⟩

/-- A sum over a non-empty subset of `ps` is in `⊕ps`. -/
theorem mem_toSumSubsets {xs ps : List (RE α)} (h : xs ∈ neSubsets ps) :
  toSum xs ∈ ⊕ps :=
  mem_map_of_mem h

theorem mem_map_toSumSubsets {β : Type} {xs ps : List (RE α)} {g : RE α → β}
  (h : xs ∈ neSubsets ps) : g (toSum xs) ∈ map g ⊕ps :=
  mem_map_of_mem (mem_toSumSubsets h)

theorem subset_sim_perm {xs ys : List (RE α)} (ne : xs ≠ []) (h : xs ⊆[ (· ≅ ·) ] ys) :
  toSum xs ∈[ (· ≅ ·) ] ⊕ ys :=
  have ⟨us, ndup, ne, us_ys, ftoSum⟩ := toSumnodup_equiv ne h
  ⟨toSum us, ftoSum, mem_toSumSubsets (mem_neSubsets_of_nodup ne us_ys ndup)⟩

theorem toSumSubsets_to_neSubset {x : RE α} {xs : List (RE α)} (h : x ∈ ⊕xs) :
  ∃ zs, zs ≠ [] ∧ x = toSum zs ∧ zs ⊆ xs :=
  have ⟨zs, zs_mem, zs_eq⟩ := mem_map.mp h
  ⟨zs, ne_nil_of_mem_neSubsets zs_mem, zs_eq.symm, subset_of_mem_neSubsets zs_mem⟩

theorem toSumSubsets_monotone {xs ys : List (RE α)} (h : xs ⊆[ (· ≅ ·) ] ys) :
  ⊕xs ⊆[ (· ≅ ·) ] ⊕ys := fun x x_mem => by
  obtain ⟨zs, p1, rfl, p3⟩ := toSumSubsets_to_neSubset x_mem
  exact subset_sim_perm p1 (subset_up_to_trans_sim (subset_to_subset_up_to_sim p3) h)

theorem toSum_appendL {xs : List (RE α)} (h : x ∈ ⊕xs) : x ∈ ⊕(xs ++ ys) := by
  obtain ⟨zs, zs_mem, rfl⟩ := mem_map.mp h
  exact mem_toSumSubsets (mem_neSubsets.mpr ⟨ne_nil_of_mem_neSubsets zs_mem,
    (subperm_of_mem_neSubsets zs_mem).trans (sublist_append_left xs ys).subperm⟩)

theorem toSum_appendR {xs : List (RE α)} (h : x ∈ ⊕ys) : x ∈ ⊕(xs ++ ys) := by
  obtain ⟨zs, zs_mem, rfl⟩ := mem_map.mp h
  exact mem_toSumSubsets (mem_neSubsets.mpr ⟨ne_nil_of_mem_neSubsets zs_mem,
    (subperm_of_mem_neSubsets zs_mem).trans (sublist_append_right xs ys).subperm⟩)
