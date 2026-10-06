import Regex.Derives

open RE

/-!
# Match semantics

Contains the specification of the matching relation, which follows the same approach
of language-based matching, using spans and locations instead of words.
The semantics is a recursive function into `Prop`, by well-founded recursion on `star_metric`.
The correctness of the `derives` algorithm then implies that this predicate is decidable.
-/

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

@[simp]
def RE.Matches (sp : Span σ) (R : RE α) : Prop :=
  match R with
  | ε      => sp.mid = []
  | Pred φ => ∃ a, sp.mid = [a] ∧ a ⊨ φ
  | l ⬝ r  =>
    ∃ u₁ u₂,
        have : (star_metric l) < (star_metric (l ⬝ r)) := star_metric_Cat_l
        have : (star_metric r) < (star_metric (l ⬝ r)) := star_metric_Cat_r
        RE.Matches ⟨sp.left, u₁, u₂ ++ sp.right⟩ l
      ∧ RE.Matches ⟨u₁.reverse ++ sp.left, u₂, sp.right⟩ r
      ∧ u₁ ++ u₂ = sp.mid
  | l ⋓ r  =>
    have : star_metric l < star_metric (l ⋓ r) := star_metric_Alt_l
    have : star_metric r < star_metric (l ⋓ r) := star_metric_Alt_r
    RE.Matches sp l ∨ RE.Matches sp r
  | l ⋒ r  =>
    have : star_metric l < star_metric (l ⋒ r) := star_metric_Inter_l
    have : star_metric r < star_metric (l ⋒ r) := star_metric_Inter_r
    RE.Matches sp l ∧ RE.Matches sp r
  | .Star r =>
    ∃ (m : ℕ),
    have : star_metric (r ⁽ m ⁾) < star_metric (r *) := star_metric_repeat
    RE.Matches sp (r ⁽ m ⁾)
  | ~ r    =>
    have : (star_metric r) < (star_metric (Negation r)) := star_metric_Negation
    ¬ RE.Matches sp r
  -- lookaheads: some match of `r` begins where `sp` is
  | ?= r   =>
    have : star_metric r < star_metric (?= r) := star_metric_Lookahead
    sp.mid = [] ∧ ∃ sp', RE.Matches sp' r ∧ sp'.beg = sp.beg
  | ?! r   =>
    have : star_metric r < star_metric (?! r) := star_metric_NegLookahead
    sp.mid = [] ∧ ¬ ∃ sp', RE.Matches sp' r ∧ sp'.beg = sp.beg
  -- lookbehinds: some match of `r` ends where `sp` is
  | ?<= r  =>
    have : star_metric r < star_metric (?<= r) := star_metric_Lookbehind
    sp.mid = [] ∧ ∃ sp', RE.Matches sp' r ∧ sp'.end = sp.beg
  | ?<! r  =>
    have : star_metric r < star_metric (?<! r) := star_metric_NegLookbehind
    sp.mid = [] ∧ ¬ ∃ sp', RE.Matches sp' r ∧ sp'.end = sp.beg
termination_by star_metric R
decreasing_by
  simp_wf; repeat assumption

notation:52 lhs:53 " ⊫ " rhs:53 => RE.Matches lhs rhs
