import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Perm.Subperm

open List

variable {α : Type _}

/-- Non-empty sub-multisets of `ys`. -/
def neSubsets (ys : List α) : List (List α) :=
  (ys.sublists.flatMap permutations').filter fun xs => !xs.isEmpty

/-- The characterisation of `neSubsets`. -/
@[simp]
theorem mem_neSubsets {xs ys : List α} : xs ∈ neSubsets ys ↔ xs ≠ [] ∧ xs <+~ ys := by
  simp only [neSubsets, mem_filter, mem_flatMap, mem_sublists, mem_permutations']
  constructor
  · rintro ⟨⟨zs, hzs, hp⟩, hne⟩
    exact ⟨by simpa using hne, zs, hp.symm, hzs⟩
  · rintro ⟨hne, zs, hp, hzs⟩
    exact ⟨⟨zs, hzs, hp.symm⟩, by simpa using hne⟩

theorem ne_nil_of_mem_neSubsets {xs ys : List α} (h : xs ∈ neSubsets ys) : xs ≠ [] :=
  (mem_neSubsets.mp h).1

theorem subperm_of_mem_neSubsets {xs ys : List α} (h : xs ∈ neSubsets ys) : xs <+~ ys :=
  (mem_neSubsets.mp h).2

theorem neSubsets_refl {xs : List α} (ne : xs ≠ []) : xs ∈ neSubsets xs :=
  mem_neSubsets.mpr ⟨ne, Subperm.refl xs⟩

theorem neSubsets_append {x y xs ys : List α} (hl : x ∈ neSubsets xs) (hr : y ∈ neSubsets ys) :
    x ++ y ∈ neSubsets (xs ++ ys) :=
  mem_neSubsets.mpr ⟨append_ne_nil_of_left_ne_nil (ne_nil_of_mem_neSubsets hl) _,
                     (subperm_of_mem_neSubsets hl).append (subperm_of_mem_neSubsets hr)⟩

theorem neSubsets_singleton {x : α} {xs : List α} (h : x ∈ xs) : [x] ∈ neSubsets xs :=
  mem_neSubsets.mpr ⟨cons_ne_nil x [], (singleton_sublist.mpr h).subperm⟩

/-- A non-empty duplicate-free selection from `ys` is a `neSubset` of it. -/
theorem mem_neSubsets_of_nodup {xs ys : List α}
    (h : xs ≠ []) (sb : xs ⊆ ys) (nd : Nodup xs) : xs ∈ neSubsets ys :=
  mem_neSubsets.mpr ⟨h, nd.subperm sb⟩

theorem subset_of_mem_neSubsets {xs ys : List α} (h : xs ∈ neSubsets ys) : xs ⊆ ys :=
  (subperm_of_mem_neSubsets h).subset
