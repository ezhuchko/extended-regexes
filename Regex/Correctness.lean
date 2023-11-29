import Regex.Definitions
import Regex.Metrics
import Regex.Derives
import Regex.Models
import Regex.Reversal

/-!
# Main correctness theorem

Contains each lemma required to show that `models` and `derives` are equivalent,
along with the main correctness proof.
-/

open BA
open RE

variable [EffectiveBooleanAlgebra α σ]

theorem derives_Bot : (sp ⊢ (Pred ⊥ : RE α)) = false :=
  match sp with
  | ⟨s,u,v⟩ =>
    match u with
    | [] => by simp
    | a::u => by
      simp;
      by_cases (denote (⊥ : α) a)
      . simp; simp at h
      . simp; apply derives_Bot
termination_by
  derives_Bot sp => sp.2.1

theorem derives_Eps  :
  sp ⊢ (ε : RE α) ↔ sp.match.length = 0 :=
  match sp with
  | ⟨s,u,v⟩ =>
   match u with
   | [] => by simp
   | a::u => by
     simp [derives]
     apply derives_Bot

theorem derives_Pred :
  sp ⊢ (Pred φ : RE α) ↔ sp.match.length = 1 ∧ sp.match_head?.any (denote φ) :=
  match sp with
   | ⟨s,u,v⟩ =>
    match u with
    | [] => by simp
    | a::u => by
      by_cases h1 : denote φ a
      . simp at *; rw[h1]; simp [derives_Eps, Option.any, h1]
      . simp at h1; simp at *;
        have contra : derives (a::s, u, v) (Pred ⊥ : RE α) = false := derives_Bot;
        rw [h1]; simp; aesop

theorem derives_to_existsMatch {loc : Loc σ} {r : RE α} :
  existsMatch r loc ↔ ∃ sp, sp ⊢ r ∧ sp.beg = loc :=
  ⟨λ h => by
     match loc with
     | ⟨u,[]⟩ => simp at h; exists ⟨u,[],[]⟩
     | ⟨u,a::v⟩ =>
       simp at h;
       match h with
       | Or.inl p => exists ⟨u,[],a::v⟩;
       | Or.inr p =>
         match derives_to_existsMatch.mp p with
         | ⟨spM,ism,eq⟩ =>
           simp at eq;
           match eq with
           | ⟨eq1, eq2⟩ =>
             subst eq2;
             exact ⟨⟨u, a::(spM.match), spM.right⟩,
                   (by simp; rw[←eq1]; exact ism)⟩,
   λ h => by
     match h with
     | ⟨sp, ism, eq⟩ =>
       match loc with
       | ⟨u,[]⟩ =>
         match sp with
         | ⟨s,[],v⟩ =>
           simp at eq ism; simp;
           match eq with
           | ⟨eq1,eq2⟩ => subst eq1 eq2; exact ism
         | ⟨s,a::u,v⟩ => simp at eq
       | ⟨u,a::v⟩ =>
         match sp with
         | ⟨s,[],v⟩ =>
           simp at eq ism; simp;
           match eq with
           | ⟨eq1,eq2⟩ => subst eq1 eq2; exact Or.inl ism;
         | ⟨s,a::u,v⟩ =>
           simp at eq ism; simp;
           match eq with
           | ⟨eq1,eq2,eq3⟩ =>
             subst eq1 eq2 eq3;
             exact Or.inr (derives_to_existsMatch.mpr ⟨(a :: s, u, v), ism, by simp⟩)⟩
termination_by
  derives_to_existsMatch x r => (x.2, star_metric r)

theorem derives_Lookahead {r : RE α} :
  sp ⊢ (?= r) ↔ (sp.match.length = 0 ∧ ∃ spM, spM ⊢ r ∧ spM.beg = sp.beg) :=
  ⟨ λ h =>
    match sp with
    | ⟨s,[],v⟩ => by
      simp at h;
      simp;
      rw [derives_to_existsMatch] at h;
      simp at h; exact h
    | ⟨s,a::u,v⟩ => by
      unfold derives der at h;
      rw[derives_Bot] at h;
      contradiction,
    λ h =>
    match h with
    | ⟨sp0, spM, inr, eq⟩ => by
      simp at eq;
      match eq with
      | ⟨eq1, eq2⟩ =>
        match sp with
        | ⟨s,[],v⟩ =>
          simp at eq;
          match eq with
          | ⟨eq1,eq2⟩ =>
            subst eq1 eq2; simp;
            apply derives_to_existsMatch.mpr;
            exact ⟨_, inr, by aesop⟩
        | ⟨s,a::u,v⟩ => contradiction⟩

theorem derives_Lookbehind {r : RE α} :
  sp ⊢ (?<= r) ↔ (sp.match.length = 0 ∧ ∃ spM, spM ⊢ (r ʳ) ∧ spM.beg = sp.reverse.beg) :=
  ⟨ λ h =>
    match sp with
    | ⟨s,[],v⟩ => by
      simp at h;
      simp; rw [derives_to_existsMatch] at h;
      simp at h; exact h
    | ⟨s,a::u,v⟩ => by
      unfold derives der at h;
      rw[derives_Bot] at h;
      contradiction,
    λ h =>
    match h with
    | ⟨sp0, spM, inr, eq⟩ => by
      simp at eq;
      match eq with
      | ⟨eq1, eq2⟩ =>
        match sp with
        | ⟨s,[],v⟩ =>
          simp at eq;
          match eq with
          | ⟨eq1,eq2⟩ =>
            subst eq1 eq2; simp;
            rw [derives_to_existsMatch];
            exact ⟨_, inr, by aesop⟩
        | ⟨s,a::u,v⟩ => contradiction⟩

theorem derives_NegLookahead {r : RE α} :
  sp ⊢ (?! r) ↔ sp.match.length = 0 ∧ ¬ (∃ spM, spM ⊢ r ∧ spM.beg = sp.beg) :=
  ⟨ λ h => by
    simp;
    match sp with
    | ⟨s,[],v⟩ =>
      simp at h;
      simp; intro h1 h2 h3;
      subst h3; intro h4; rw [←h4] at h;
      have h5 : h1.beg = (h1.fst, h1.snd.fst ++ h1.snd.snd) := by simp;
      have contra := derives_to_existsMatch.mpr ⟨h1, ⟨h2, h5⟩⟩;
      simp_all only
    | ⟨s,a::u,v⟩ =>
      unfold derives der at h;
      rw[derives_Bot] at h;
      contradiction,
    λ h' => by
    simp at h';
    match h' with
    | ⟨a, b⟩ =>
      match sp with
        | ⟨s,[],v⟩ =>
          unfold derives null;
          simp;
          by_cases (existsMatch r (s, v) = false)
          . assumption
          . simp at h; rw[derives_to_existsMatch] at h; simp at h;
            match h with
            | ⟨a1,a2,a3,a4⟩ => exact False.elim (b a1 a2 a3 a4)
        | ⟨s,a::u,v⟩ => contradiction⟩

theorem derives_NegLookbehind {r : RE α} :
  sp ⊢ (?<! r) ↔ sp.match.length = 0 ∧ ¬ (∃ spM, spM ⊢ (r ʳ) ∧ spM.beg = sp.reverse.beg) :=
  ⟨ λ h => by
    simp;
    match sp with
    | ⟨s,[],v⟩ =>
      simp at h;
      simp; intro h1 h2 h3;
      subst h3; intro h4; rw [←h4] at h;
      have h5 : h1.beg = (h1.fst, h1.snd.fst ++ h1.snd.snd) := by simp;
      have contra := derives_to_existsMatch.mpr ⟨h1, ⟨h2, h5⟩⟩;
      simp_all only
    | ⟨s,a::u,v⟩ =>
      unfold derives at h
      unfold der at h
      rw[derives_Bot] at h
      contradiction,
    λ h' => by
    simp at h';
    match h' with
    | ⟨a, b⟩ =>
      match sp with
        | ⟨s,[],v⟩ =>
          unfold derives; unfold null;
          simp;
          by_cases (existsMatch rʳ (v, s) = false)
          . assumption
          . simp at h; rw [derives_to_existsMatch] at h; simp at h;
            match h with
            | ⟨a1,a2,a3,a4⟩ => exact False.elim (b a1 a2 a3 a4)
        | ⟨s,a::u,v⟩ => contradiction⟩

theorem derives_Alt {sp : Span σ} {r : RE α} :
  sp ⊢ (l ⋓ r) ↔ sp ⊢ l ∨ sp ⊢ r :=
  match sp with
  | ⟨s,u,v⟩ =>
    match u with
    | [] => by simp
    | a::u => by
      simp
      simp [@derives_Alt ((der l (s, a :: (u ++ v))).1) (a::s,u,v)] -- inductive hypothesis
termination_by
  derives_Alt => sp.2.1

theorem derives_Inter {sp : Span σ} {r : RE α} :
  sp ⊢ (l ⋒ r) ↔ sp ⊢ l ∧ sp ⊢ r :=
  match sp with
  | ⟨s,u,v⟩ =>
    match u with
    | [] => by simp
    | a::u => by
      simp [@derives_Inter ((der l (s, a :: (u ++ v))).1) (a::s,u,v)] -- inductive hypothesis
termination_by
  derives_Inter => sp.2.1

theorem derives_Negation {sp : Span σ} {r : RE α} :
  sp ⊢ (~ r) ↔ ¬ (sp ⊢ r) :=
  match sp with
  | ⟨s,u,v⟩ =>
    match u with
    | [] => by simp
    | a::u => by
      simp
      simp [@derives_Negation (a::s,u,v) (der r (s, a :: (u ++ v))).1] -- inductive hypothesis
termination_by
  derives_Negation => sp.2.1

theorem derives_Cat {r : RE α} :
  sp ⊢ (l ⬝ r) ↔
  ∃ u₁ u₂,
     ⟨sp.left, u₁, u₂ ++ sp.right⟩ ⊢ l
   ∧ ⟨u₁.reverse ++ sp.left, u₂, sp.right⟩ ⊢ r
   ∧ u₁ ++ u₂ = sp.match := by
  match sp with
  | ⟨s,[],v⟩ =>
    simp;
    exact ⟨by intro h; exact (⟨[],[],by simp; assumption⟩),
           by intro h;
              let ⟨g1,g2,g3,g4,⟨g5,g6⟩⟩ := h;
              subst g5 g6; simp at g3 g4; exact ⟨g3,g4⟩⟩
  | ⟨s,a::u,v⟩ =>
    exact ⟨by intro h; simp at h;
              by_cases h1 : null l (s, a :: (u ++ v))
              . rw [h1] at h; simp at h;
                match derives_Alt.mp h with
                  | Or.inl h1 =>
                    match derives_Cat.mp h1 with
                    | ⟨g1,g2,g3,g4,g5⟩ => simp at g3; subst g5;
                                          exact ⟨a::g1,g2, ⟨by simp_all, by simp_all, by simp_all⟩⟩
                  | Or.inr h1 => exact ⟨[],a::u, ⟨by simp_all, by simp_all, by simp_all⟩⟩
              . simp at h1; rw [h1] at h; simp at h;
                match derives_Cat.mp h with
                | ⟨g1,g2,g3,g4,g5⟩ => exact ⟨a::g1,g2, ⟨by subst g5; simp_all, by simp_all, by simp_all⟩⟩,
           by intro h; let ⟨g1,g2,g3,g4,g5⟩ := h; simp at h;
              by_cases h1 : null l (s, a :: (u ++ v))
              . simp; rw [h1]; simp;
                match g1 with
                | [] =>
                  simp at g5; subst g5; simp at g3; rw[g3] at h1; simp at g4;
                  exact derives_Alt.mpr (Or.inr (by exact g4))
                | b::t =>
                  simp at g5;
                  let ⟨g5a,g5b⟩ := g5;
                  subst g5a g5b;
                  simp at g3 g4;
                  exact derives_Alt.mpr (Or.inl (derives_Cat.mpr ⟨_, _, (by simp; exact g3), (by exact g4), rfl⟩))
              . simp at h1; simp; rw [h1]; simp;
                simp at g4 g3 g5;
                match g1 with
                | [] => simp at g5; subst g5; simp at g3; rw[g3] at h1; contradiction;
                | b::t =>
                  simp at g5;
                  let ⟨g5a,g5b⟩ := g5;
                  subst g5a g5b;
                  exact derives_Cat.mpr ⟨t, g2, by simp_all, by simp_all, by simp_all⟩⟩
termination_by
  derives_Cat => sp.2.1.length

theorem derives_Star_mp {r : RE α} :
  sp ⊢ (r *) → ∃ (m : ℕ), sp ⊢ (r ⁽ m ⁾) :=
  λ h =>
   match sp with
   | ⟨s,u,v⟩ =>
    match u with
    | [] => by simp at h; exists 0; simp
    | a::u => by
      simp at h;
      match derives_Cat.mp h with
      | ⟨g1,g2,g3,g4,g5⟩ =>
        match g1 with
        | [] =>
          simp at g5; rw [g5] at g4;
          have ⟨gg, iH⟩ := derives_Star_mp g4;
          exists gg.succ; simp;
          split
          . apply derives_Alt.mpr; apply Or.inl; apply derives_Cat.mpr; subst g5;
            exact ⟨[],g2,g3,iH,by simp only [List.nil_append, Span.match]⟩
          . apply derives_Cat.mpr; subst g5;
            exact ⟨[],g2,g3,iH,by simp only [List.nil_append, Span.match]⟩
        | b::t =>
          simp at g5;
          have ⟨gg, iH⟩ := derives_Star_mp g4;
          exists gg.succ;
          simp;
          split
          . apply derives_Alt.mpr; apply Or.inl; apply derives_Cat.mpr; subst g5;
            exact ⟨b::t,g2,g3,iH,by simp⟩
          . apply derives_Cat.mpr; subst g5;
            exact ⟨b::t,g2,g3,iH,by simp⟩
termination_by
  derives_Star_mp => sp.2.1.length

/-- Additional lemma used in derives_Star_mpr. -/
theorem derives_Star_contraction {r : RE α} : sp ⊢ r ⬝ r* → sp ⊢ r* :=
  λ hyp =>
  match sp with
  | ⟨s,[],v⟩ => by simp
  | ⟨s,a::u,v⟩ => by
    simp at hyp
    by_cases (null r (s, a :: (u ++ v)) = true)
    . simp_all;
      match derives_Alt.mp hyp with
      | Or.inl h => simp at h; assumption
      | Or.inr h => simp at h; assumption
    . simp at h; rw[h] at hyp; simp at hyp; simp; assumption

/-- This lemma needs to be declared separately in order to correctly capture the inductive step. -/
theorem derives_Star_mpr {r : RE α} : sp ⊢ (r ⁽ m ⁾) → sp ⊢ (r *) :=
  λ h =>
    match m with
    | 0 =>
      match sp with
      | ⟨s,[],v⟩ => by simp
      | ⟨s,a::u,v⟩ => by have := @derives_Bot α _ _ ⟨a::s,u,v⟩; simp at h; rw[h] at this; contradiction
    | .succ m => by
      simp at h;
      match derives_Cat.mp h with
      | ⟨u1,u2,m1,m2,a⟩ =>
        simp at m2
        have p := derives_Star_mpr m2
        have q := derives_Cat.mpr ⟨u1,u2,m1,p,a⟩
        exact derives_Star_contraction q

theorem derives_Star {r : RE α} : sp ⊢ (r *) ↔ ∃ m, sp ⊢ (r ⁽ m ⁾) :=
  ⟨derives_Star_mp, λ ⟨_,h⟩ => derives_Star_mpr h⟩

theorem exists_span_iff (p : Span σ → Prop) : (∃ s, p s) ↔ ∃ u v w, p ⟨u,v,w⟩ :=
  ⟨by rintro ⟨⟩; exact ⟨_, _, _, ‹_›⟩, by rintro ⟨_,_,_,_⟩; exact ⟨_, ‹_›⟩⟩

theorem models_reversal' {R : RE α} {sp : Span σ} :
    sp ⊨ (R ʳ) ↔ sp.reverse ⊨ R := by
  simpa using models_reversal (R := Rʳ)

/-- Main correctness theorem. -/

theorem correctness : ∀ {R : RE α}, sp ⊢ R ↔ sp ⊨ R
  | ε      => derives_Eps
  | Pred φ => derives_Pred
  | ?= r   => by
    have : star_metric r < star_metric (?= r) := star_metric_Lookahead
    rw [derives_Lookahead, models]
    simp [@correctness _ r] -- induction hypothesis
  | ?<= r  => by
    have : star_metric (r ʳ) < star_metric (?<= r) := star_metric_Lookbehind_reverse
    rw [derives_Lookbehind, models]
    cases sp
    simp [@correctness _ (r ʳ), exists_span_iff, models_reversal'] -- induction hypothesis
  | ?! r   => by
    have : star_metric r < star_metric ?!r := star_metric_NegLookahead
    rw [derives_NegLookahead]
    simp [@correctness _ r] -- induction hypothesis
  | ?<! r  => by
    have : star_metric rʳ < star_metric ?<!r := star_metric_NegLookbehind_reverse
    rw [derives_NegLookbehind, models]
    cases sp
    simp [@correctness _ (r ʳ), exists_span_iff, models_reversal'] -- induction hypothesis
  | ~ r    => by
    have : star_metric r < star_metric (Negation r) := star_metric_Negation
    rw [derives_Negation]
    simp [@correctness _ r] -- induction hypothesis
  | r *    => by
    have : star_metric r < star_metric (Star r) := star_metric_Star
    simp [derives_Star];
    refine exists_congr fun m => ?_
    have : star_metric (r⁽m⁾) < star_metric r* := star_metric_repeat
    simp [@correctness _ (repeat_cat r m)] -- induction hypothesis
  | l ⋒ r  => by
    have : star_metric l < star_metric (l ⋒ r) := star_metric_Inter_l
    have : star_metric r < star_metric (l ⋒ r) := star_metric_Inter_r
    rw [derives_Inter]
    simp [@correctness _ l, @correctness _ r] -- induction hypothesis
  | l ⋓ r  => by
    have : star_metric l < star_metric (l ⋓ r) := star_metric_Alt_l
    have : star_metric r < star_metric (l ⋓ r) := star_metric_Alt_r
    rw [derives_Alt]
    simp [@correctness _ l, @correctness _ r] -- induction hypothesis
  | l ⬝ r  => by
    have : star_metric l < star_metric (l ⬝ r) := star_metric_Cat_l
    have : star_metric r < star_metric (l ⬝ r) := star_metric_Cat_r
    rw [derives_Cat]
    simp [@correctness _ l, @correctness _ r] -- induction hypothesis
termination_by
  correctness sp r => star_metric r
decreasing_by
  simp only[InvImage, WellFoundedRelation.rel];
  assumption

/- Main reversal theorem using the derivation relation instead of `models`. -/
theorem derives_reversal {R : RE α} : sp ⊢ R ↔ sp.reverse ⊢ (R ʳ) :=
  correctness.trans (models_reversal.trans correctness.symm)
