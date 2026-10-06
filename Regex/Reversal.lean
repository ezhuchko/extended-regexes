import Regex.MatchesReasoning

open RE

/-!
# Correctness of reversal

Contains only the main theorem stating that the reversal operation is
correct, using the classical match semantics `Matches` for simplicity.
-/

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

/-- Main correctness of reversal. -/
theorem matches_reversal {R : RE α} {sp : Span σ} :
  sp ⊫ R ↔ sp.reverse ⊫ (R ʳ) :=
  match R with
  | ε => by simp only [RE.Matches, RE.reverse, Span.mid_reverse, List.reverse_eq_nil_iff]
  | Pred φ => by
    simp only [RE.Matches, RE.reverse, Span.mid_reverse, List.reverse_eq_cons_iff, List.reverse_nil,
      List.nil_append]
  | l ⬝ r => by
    have : (star_metric l) < (star_metric (l ⬝ r)) := star_metric_Cat_l
    have : (star_metric r) < (star_metric (l ⬝ r)) := star_metric_Cat_r
    match sp with
    | ⟨s,u,v⟩ =>
      simp [@matches_reversal l, @matches_reversal r]
      exact ⟨by simp; intro h1 h2 h3 h4 h5;
                exists h2.reverse; exists h1.reverse; simp;
                exact ⟨h4,h3, by rw[←List.reverse_append, h5]⟩,
             by simp; intro h1 h2 h3 h4 h5;
                exists h2.reverse; exists h1.reverse; simp;
                exact ⟨h4,h3, by rw[←List.reverse_append, h5, List.reverse_reverse]⟩⟩
  | l ⋓ r  => by
    have : star_metric l < star_metric (l ⋓ r) := star_metric_Alt_l
    have : star_metric r < star_metric (l ⋓ r) := star_metric_Alt_r
    simp [@matches_reversal l, @matches_reversal r]
  | l ⋒ r  => by
    have : star_metric l < star_metric (l ⋒ r) := star_metric_Inter_l
    have : star_metric r < star_metric (l ⋒ r) := star_metric_Inter_r
    simp [@matches_reversal l, @matches_reversal r]
  | .Star r => by
    have : star_metric r < star_metric (r *) := star_metric_Star
    match sp with
    | ⟨s, u, v⟩ =>
      unfold RE.reverse; simp
      exact exists_congr fun m =>
      (match m with
       | 0 => by simp
       | .succ m => by
         have : star_metric (r⁽Nat.succ m⁾) < star_metric r* := star_metric_repeat
         simp only [@matches_reversal (repeat_cat r m.succ)]
         exact (equiv_trans (equiv_cat_cong equiv_reverse_regex_repeat_cat equiv_refl) equiv_repeat_cat_cat))
  -- reversal swaps lookaheads and lookbehinds, as it swaps the beginning and end of spans
  | ?= r | ?<= r | ?! r | ?<! r => by
    simp only [RE.Matches, RE.reverse, Span.mid_reverse, List.reverse_eq_nil_iff, and_congr_right_iff]
    intro h
    rw [Span.exists_reverse]
    simp only [@matches_reversal r, reverse_span_involution, Span.beg_reverse, Span.end_reverse,
      Span.end_eq_beg h, Loc.reverse_eq_iff]
  | ~ r    => by
    have : star_metric r < star_metric (Negation r) := star_metric_Negation;
    simp [@matches_reversal r]
termination_by star_metric R
decreasing_by
  -- all four lookarounds have the same metric as `?= r`
  all_goals first | assumption | exact star_metric_Lookahead
