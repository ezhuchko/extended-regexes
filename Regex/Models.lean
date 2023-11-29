import Regex.Definitions
import Regex.Metrics
import Regex.Derives

open RE

/-!
# Match semantics

Contains the specification of the matching relation, which follows the same approach
of language-based matching, using spans and locations instead of words.
The semantics is provided directly as an inductive predicate, in Prop.
The correctness of the `derives` algorithm then implies that this predicate is decidable.
-/

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

@[simp]
def models (sp : Span σ) (R : RE α) : Prop :=
  match R with
  | ε      => sp.match.length = 0
  | Pred φ => sp.match.length = 1 ∧ sp.match_head?.any (denote φ)
  | l ⬝ r  =>
      ∃ u₁ u₂,
          have : (star_metric l) < (star_metric (l ⬝ r)) := star_metric_Cat_l
          have : (star_metric r) < (star_metric (l ⬝ r)) := star_metric_Cat_r
          models ⟨sp.left, u₁, u₂ ++ sp.right⟩ l
        ∧ models ⟨u₁.reverse ++ sp.left, u₂, sp.right⟩ r
        ∧ u₁ ++ u₂ = sp.match
  | l ⋓ r  =>
      have : star_metric l < star_metric (l ⋓ r) := star_metric_Alt_l
      have : star_metric r < star_metric (l ⋓ r) := star_metric_Alt_r
      models sp l ∨ models sp r
  | l ⋒ r  =>
      have : star_metric l < star_metric (l ⋒ r) := star_metric_Inter_l
      have : star_metric r < star_metric (l ⋒ r) := star_metric_Inter_r
    models sp l ∧ models sp r
  | r *    =>
      ∃ (m : ℕ),
      have : star_metric (r ⁽ m ⁾) < star_metric (r *) := star_metric_repeat
      models sp (r ⁽ m ⁾)
  | ~ r    =>
      have : (star_metric r) < (star_metric (Negation r)) := star_metric_Negation
      ¬ models sp r
  | ?= r   =>
      have : (star_metric r) < (star_metric (?= r)) := star_metric_Lookahead
      sp.match.length = 0 ∧ ∃ (spM : Span σ), models spM r ∧ spM.beg = sp.beg
  | ?<= r  =>
      have : star_metric r < star_metric (?<= r) := star_metric_Lookbehind
      sp.match.length = 0 ∧ ∃ (spM : Span σ), models spM.reverse r ∧ spM.beg = sp.reverse.beg
  | ?! r   =>
      have : (star_metric r) < (star_metric (?= r)) := star_metric_Lookahead
      sp.match.length = 0 ∧ ¬ (∃ (spM : Span σ), models spM r ∧ spM.beg = sp.beg)
  | ?<! r  =>
      have : star_metric r < star_metric (?<= r) := star_metric_Lookbehind
      sp.match.length = 0 ∧ ¬ (∃ (spM : Span σ), models spM.reverse r ∧ spM.beg = sp.reverse.beg)
termination_by
  models sp R => star_metric R
decreasing_by
  simp only[InvImage, WellFoundedRelation.rel];
  assumption

infix:30 " ⊨ " => models
