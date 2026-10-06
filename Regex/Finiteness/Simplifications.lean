import Regex.Finiteness.Finite

open RE List Sim

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

/-!
# Simplifications

This file contains the simplifications which preserve the finiteness result.
This gives rise to the following criterion: a simplification function `f : RE α → RE α` is admissible
if it is `NonIncreasing`.
-/

@[simp]
def simplify (f : RE α → RE α) : RE α → RE α
  | l ⋒ r  => simplify f l ⋒ simplify f r
  | ~r     => ~(simplify f r)
  | l ⬝ r  => f (simplify f l ⬝ r)
  | l ⋓ r  => f (simplify f l ⋓ simplify f r)
  | r      => r

-- define a type for nonincreasing fs
@[simp]
def NonIncreasing (f : RE α → RE α) := ∀ ⦃r⦄, pieces (f r) ⊆ pieces r

theorem NonIncreasing_comp {f g : RE α → RE α} (ni_f : NonIncreasing f) (ni_g : NonIncreasing g):
  NonIncreasing (g ∘ f) := fun _ _ h => ni_f (ni_g h)

theorem NonIncreasing_pieces {r : RE α} (ni_f : NonIncreasing f) :
  pieces (simplify f r) ⊆[ (· ≅ ·) ] pieces r := fun e h =>
  match r with
  | ε | Pred _ | ?=_ | ?!_ | ?<=_ | ?<!_ | .Star _ => ⟨e, refl, h⟩
  | l ⬝ _ =>
    pieces_cat_mono (NonIncreasing_pieces (r := l) ni_f) subset_up_to_refl_sim refl e (ni_f h)
  | l ⋓ r =>
    pieces_alt_mono (NonIncreasing_pieces (r := l) ni_f) (NonIncreasing_pieces (r := r) ni_f)
      e (ni_f h)
  | l ⋒ r =>
    pieces_inter_mono (NonIncreasing_pieces (r := l) ni_f) (NonIncreasing_pieces (r := r) ni_f) e h
  | ~r => pieces_neg_mono (NonIncreasing_pieces (r := r) ni_f) e h

@[simp]
def plus_bot_l [DecidableEq α] : RE α → RE α
  | Pred ψ ⋓ r => if ψ = ⊥ then r else Pred ψ ⋓ r
  | r => r

@[simp]
def plus_bot_r [DecidableEq α] : RE α → RE α
  | l ⋓ Pred ψ => if ψ = ⊥ then l else l ⋓ Pred ψ
  | r => r

@[simp]
def mult_eps : RE α → RE α
  | ε ⬝ r => r
  | r => r

@[simp]
def mult_bot [DecidableEq α] : RE α → RE α
  | r ⬝ Pred ψ => if ψ = ⊥ then Pred ⊥ else r ⬝ Pred ψ
  | r => r

@[simp]
def distr : RE α → RE α
  | (l ⋓ r) ⬝ p => l ⬝ p ⋓ r ⬝ p
  | r => r

-- ~⊥ + r → ~⊥
@[simp]
def plus_not_bot [DecidableEq α] : RE α → RE α
  | ~(Pred ψ) ⋓ r => if ψ = ⊥ then ~(Pred ψ) else ~(Pred ψ) ⋓ r
  | r => r

-- e ⬝ ⊥ -> ⊥ less useful than ⊥ ⬝ f -> ⊥
-- this would allow to stop the derivative early

theorem plus_bot_l_ni [DecidableEq α] :
  NonIncreasing (α := α) plus_bot_l := fun _ _ h => by
  unfold plus_bot_l at h
  split at h
  · split_ifs at h with g
    · subst g; exact mem_append_right _ h
    · exact h
  · exact h

theorem plus_bot_r_ni [DecidableEq α] :
  NonIncreasing (α := α) plus_bot_r := fun _ _ h => by
  unfold plus_bot_r at h
  split at h
  · split_ifs at h with g
    · subst g; exact mem_append_left _ h
    · exact h
  · exact h

theorem mult_eps_ni :
  NonIncreasing (α := α) mult_eps := fun _ _ h => by
  unfold mult_eps at h
  split at h
  · exact mem_append_right _ h
  · exact h

theorem mult_bot_ni [DecidableEq α] :
  NonIncreasing (α := α) mult_bot := fun _ _ h => by
  unfold mult_bot at h
  split at h
  · split_ifs at h with g
    · subst g; exact mem_append_right _ h
    · exact h
  · exact h

theorem distr_ni :
  NonIncreasing (α := α) distr := fun _ _ h => by
  unfold distr at h
  split at h
  · simp only [pieces, mem_append, mem_map] at h ⊢
    rcases h with (⟨a, ha, rfl⟩ | h) | (⟨a, ha, rfl⟩ | h)
    · exact .inl ⟨a, toSum_appendL ha, rfl⟩
    · exact .inr h
    · exact .inl ⟨a, toSum_appendR ha, rfl⟩
    · exact .inr h
  · exact h

theorem plus_not_bot_ni [DecidableEq α] :
  NonIncreasing (α := α) plus_not_bot := fun _ _ h => by
  unfold plus_not_bot at h
  split at h
  · split_ifs at h with g
    · exact mem_append_left _ h
    · exact h
  · exact h

-- define as a fold
def NonIncreasing_simps [DecidableEq α] : RE α → RE α :=
  plus_not_bot ∘ plus_bot_l ∘ plus_bot_r ∘ mult_eps ∘ mult_bot ∘ distr

theorem NonIncreasing_simps_proof [DecidableEq α] :
  NonIncreasing (α := α) NonIncreasing_simps :=
  NonIncreasing_comp (NonIncreasing_comp (NonIncreasing_comp (NonIncreasing_comp
    (NonIncreasing_comp distr_ni mult_bot_ni) mult_eps_ni) plus_bot_r_ni) plus_bot_l_ni) plus_not_bot_ni

def step_with_simp [DecidableEq α] (r : RE α) : List (RE α) :=
  map (simplify NonIncreasing_simps) (step r)

@[simp]
def steps_with_simp [DecidableEq α] (r : RE α) : ℕ → List (RE α)
  | 0 => [r]
  | Nat.succ n => map step_with_simp (steps_with_simp r n) |> flatten

theorem fin_step_with_simp [DecidableEq α] {r : RE α} :
  step_with_simp r ⊆[ (· ≅ ·) ] ⊕(pieces r) := fun _ h => by
  obtain ⟨a, a_step, rfl⟩ := mem_map.mp h
  obtain ⟨b, hb, b_mem⟩ := toSumSubsets_pieces_refl (r := simplify NonIncreasing_simps a)
  obtain ⟨c, hc, c_mem⟩ :=
    toSumSubsets_monotone (NonIncreasing_pieces NonIncreasing_simps_proof) b b_mem
  exact toSumSubsets_pieces_trans ⟨c, trans hb hc, c_mem⟩ (step_to_toSumSubsets _ a_step)

theorem finiteness_simp [DecidableEq α] {r : RE α} :
  steps_with_simp r n ⊆[ (· ≅ ·) ] ⊕(pieces r) := fun e h =>
  match n with
  | 0 => by
    obtain rfl := mem_singleton.mp h
    exact toSumSubsets_pieces_refl
  | n + 1 => by
    simp only [steps_with_simp, mem_flatten, mem_map, exists_exists_and_eq_and] at h
    obtain ⟨e', e'_steps, e_step⟩ := h
    exact toSumSubsets_pieces_trans (fin_step_with_simp e e_step) (finiteness_simp e' e'_steps)
