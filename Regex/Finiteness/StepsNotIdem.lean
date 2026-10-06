import Regex.Definitions
import Regex.Finiteness.Permute

open RE TTerm List

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

/-!
# Step function is not idempotent

Contains a proof that the `step` function violates the idempotence property.
-/

@[simp]
def asList (e : RE α) : List (RE α) :=
  match e with
  | e1 ⋓ e2 => asList e1 ++ asList e2
  | e => [e]

@[simp]
def basic (e : RE α) : Prop :=
  match e with
  | ε | Pred _ | ?=_ | ?!_ | ?<=_ | ?<!_ => True
  | _⋒_ | ~ _ | _⬝_ | .Star _ => False
  | l ⋓ r => basic l ∧ basic r

theorem basic_equiv {e f : RE α} (h  : e ≅ f) : basic e ↔ basic f := by
  induction h with
  | refl => exact ⟨id, id⟩
  | symm _ _ | trans _ _ _ _ => simp_all only
  | assoc => simp_all only [basic]; exact and_assoc
  | idem => simp_all only [basic, and_self]
  | dedup => simp_all only [basic, and_congr_right_iff, and_true, implies_true]
  | alt_cong _ _ _ _ | cat_cong | star_cong | neg_cong | inter_cong => simp_all only [basic]

theorem equiv_exprs_lists {e f : RE α} (be : basic e) (bf : basic f) (h : e ≅ f) :
  asList e ⊆ asList f ∧ asList f ⊆ asList e := by
  induction h with
  | refl => simp only [Subset.refl, and_self]
  | symm _ ih => exact And.comm.mp (ih bf be)
  | @trans r1 r2 r3 h1 _ ih1 ih2 =>
      have br2 := (basic_equiv h1).1 be
      have ⟨l1, r1⟩ := ih1 be br2
      have ⟨l2, r2⟩ := ih2 br2 bf
      exact ⟨fun _ a_1 => l2 (l1 a_1), fun _ a_1 => r1 (r2 a_1)⟩
  | assoc => simp only [asList, append_assoc, Subset.refl, and_self]
  | idem  => simp only [asList, append_subset, Subset.refl, and_self, subset_append_of_subset_left]
  | dedup => simp only [asList, append_subset, Subset.refl, subset_append_of_subset_left, subset_append_of_subset_right, and_self]
  | alt_cong _ _ ih1 ih2 =>
      simp only [basic] at be bf
      simp only [asList, append_subset]
      have ⟨g1, g2⟩ := ih1 be.1 bf.1
      have ⟨h1, h2⟩ := ih2 be.2 bf.2
      exact ⟨⟨subset_append_of_subset_left _ g1,subset_append_of_subset_right _ h1⟩,
             ⟨subset_append_of_subset_left _ g2,subset_append_of_subset_right _ h2⟩⟩
  | cat_cong | star_cong | neg_cong | inter_cong => simp only [basic] at be

theorem eps_bot_not_eps {a : α} (h : ε ⋓ Pred a ≅ ε) : False := by
  have b1 : basic (ε ⋓ Pred a) := (basic_equiv h).mpr trivial
  have b2 : basic (ε : RE α) := trivial
  have ⟨s1, _⟩ := equiv_exprs_lists b1 b2 h
  simp only [asList, cons_append, nil_append, cons_subset, mem_cons, not_mem_nil, or_false,
    reduceCtorEq, or_self, Subset.refl, subset_cons_of_subset, and_true, and_false] at s1

theorem eps_bot_not_bot {a : α} (h : ε ⋓ Pred a ≅ Pred a) : False := by
  have b1 : basic (ε ⋓ Pred a) := (basic_equiv h).mpr trivial
  have b2 : basic (Pred a) := trivial
  have ⟨s1, _⟩ := equiv_exprs_lists b1 b2 h
  simp only [asList, cons_append, nil_append, cons_subset, mem_cons, reduceCtorEq, not_mem_nil,
    or_self, Subset.refl, and_true] at s1

theorem step_not_idem {a : α} :
  ∃ (r : RE α), ¬ step (r ⋓ r) ⊆[ (· ≅ ·) ] step r := by
  exists (Pred a)
  intro h
  simp only [subset_up_to] at h
  let b : RE α := Pred ⊥
  let e : RE α := ε
  have eb_in : e ⋓ b ∈ step (Pred a ⋓ Pred a) := by
    simp_all only [step, derivative, leaves_binary, productWith, leaves, cons_append, nil_append, mem_map,
      Prod.exists, pair_mem_product, mem_cons, not_mem_nil, or_false, Function.uncurry_apply_pair, mem_up_to,
      leaves, forall_exists_index, and_imp, Alternation.injEq, exists_eq_right_right, reduceCtorEq, or_true,
      and_true, exists_eq_right, e, b]
  have ⟨y, y_eq, y_mem⟩ := h (e ⋓ b) eb_in
  simp only [step, derivative, leaves, cons_append, nil_append, mem_cons, not_mem_nil, or_false] at y_mem
  match y_mem with
  | Or.inl q => subst q; apply eps_bot_not_eps y_eq
  | Or.inr q => subst q; apply eps_bot_not_bot y_eq
