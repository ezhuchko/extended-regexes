import Regex.Definitions
import Regex.Metrics
import Regex.Derives
import Regex.Models
import Regex.ModelsReasoning

open RE

/-!
# Correctness of reversal

Contains only the main theorem stating that the reversal operation is
correct, using the classical match semantics `models` for simplicity.
-/

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

/-- Main correctness of reversal. -/
theorem models_reversal {R : RE α} {sp : Span σ} :
  sp ⊨ R ↔ sp.reverse ⊨ (R ʳ) :=
  match R with
  | ε => by aesop
  | Pred φ =>
    match sp with
    | ⟨s, u, v⟩ =>
      match u with
      | [] => by simp
      | a::us => by
        simp; intro h;
        have hp : us = [] := by simp[List.length_eq_zero.mp] at *;
                                rw [List.length_eq_zero] at h; assumption
        aesop
  | l ⬝ r => by
    have : (star_metric l) < (star_metric (l ⬝ r)) := star_metric_Cat_l
    have : (star_metric r) < (star_metric (l ⬝ r)) := star_metric_Cat_r
    match sp with
    | ⟨s,u,v⟩ =>
      simp [@models_reversal l, @models_reversal r] -- inductive hypothesis
      exact ⟨by simp; intro h1 h2 h3 h4 h5;
                exists h2.reverse; exists h1.reverse; simp;
                exact ⟨h4,h3, by rw[←List.reverse_append, h5]⟩,
             by simp; intro h1 h2 h3 h4 h5;
                exists h2.reverse; exists h1.reverse; simp;
                exact ⟨h4,h3, by rw[←List.reverse_append, h5, List.reverse_reverse]⟩⟩
  | l ⋓ r  => by
    have : star_metric l < star_metric (l ⋓ r) := star_metric_Alt_l
    have : star_metric r < star_metric (l ⋓ r) := star_metric_Alt_r
    simp [@models_reversal l, @models_reversal r] -- inductive hypothesis
  | l ⋒ r  => by
    have : star_metric l < star_metric (l ⋒ r) := star_metric_Inter_l
    have : star_metric r < star_metric (l ⋒ r) := star_metric_Inter_r
    simp [@models_reversal l, @models_reversal r] -- inductive hypothesis
  | r *    => by
    have : star_metric r < star_metric (r *) := star_metric_Star
    match sp with
    | ⟨s, u, v⟩ =>
      unfold RE.reverse; simp;
      refine exists_congr fun m => ?_
      match m with
      | 0 => simp
      | .succ m =>
        have : star_metric (r⁽Nat.succ m⁾) < star_metric r* := star_metric_repeat
        simp only [@models_reversal (repeat_cat r m.succ)] -- inductive hypothesis
        exact (equiv_trans (equiv_cat_cong equiv_reverse_regex_repeat_cat equiv_refl) equiv_repeat_cat_cat)
  | ?= r   => by
    have : (star_metric r) < (star_metric (?= r)) := star_metric_Lookahead
    have : star_metric r < star_metric ?<=r := star_metric_NegLookbehind
    match sp with
    | ⟨s, u, v⟩ =>
      simp [@models_reversal r] -- inductive hypothesis
  | ?<= r  => by
    have : star_metric r < star_metric ?<=r := star_metric_NegLookbehind
    match sp with
    | ⟨s, u, v⟩ =>
      simp [@models_reversal r] -- inductive hypothesis
      intro _
      refine exists_congr fun m => ?_
      simp; intro h1 h2; subst h1;
      match m with
      | ⟨ss,uu,vv⟩ => simp
  | ?! r   => by
    have : star_metric r < star_metric ?!r := star_metric_NegLookahead
    match sp with
    | ⟨s, u, v⟩ =>
      simp [@models_reversal r] -- inductive hypothesis
  | ?<! r  => by
    have : star_metric r < star_metric ?<!r := star_metric_NegLookbehind
    match sp with
    | ⟨s, u, v⟩ =>
      simp
      intro _
      simp [@models_reversal r] -- inductive hypothesis
      refine forall_congr' fun m => ?_
      match m with
      | ⟨ss, uu, vv⟩ => simp
  | ~ r    => by
    have : star_metric r < star_metric (Negation r) := star_metric_Negation;
    simp [@models_reversal r] -- inductive hypothesis
termination_by
  models_reversal sp r _ => star_metric r
decreasing_by
  simp only[InvImage, WellFoundedRelation.rel]
  assumption
