import Regex.Definitions
import Regex.Metrics
import Regex.Derives
import Regex.Models
import Regex.MatchingAlgorithm

/-!
# Elimination of General Negative Lookarounds

Contains the result that negative lookarounds are not needed when we add the start and end anchors as primitive regexes.
-/

open BA
open RE

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

@[simp]
theorem models_TopStar {sp : Span σ} : sp ⊨ (Pred (⊤ : α))* :=
  derives_TopStar |> correctness.mp

@[simp]
theorem models_NegLookahead_Top {sp : Span σ}:
  sp ⊨ (?!(Pred (⊤ : α))) ↔ sp.match.length = 0 ∧ sp.right.length = 0 :=
  match sp with
  | ⟨s,u,v⟩ =>
    -- match on u
    match u with
    | [] =>
      -- match on v
      match v with
      | [] => by
        simp; unfold Option.any; intro x h1 _ h2 h3 _; aesop
      | a::u => by
        simp;
        exists ⟨s,[a],u⟩;
        unfold Option.any;
        simp_all
    -- contradiction as u has to be empty by definition
    | a::u => by simp

/-- We define the helper notations. The notation for \z is endAnchor and the notation for ⊤* is pad. -/
def endAnchor : RE α := (?!(Pred (⊤ : α)))

def pad : RE α := (Pred (⊤ : α))*

theorem eliminationNegLookaroundsL {R : RE α} {sp : Span σ} :
  sp ⊨ (?=((~(R ⬝ pad)) ⬝ endAnchor)) → sp ⊨ (?! R) :=
  λ h =>
  match hu:sp with
  | ⟨s,u,v⟩ =>
    -- match on u
    match u with
    | [] => by
      -- simplify hypothesis/unfold defs
      unfold models at h;
      simp only at h;
      let ⟨h1,h2⟩ := h;
      clear h1 h;
      -- simplify goal/unfold defs
      simp; intro sp1 g1 g2 g3;
      match sp1 with
      | ⟨ss,uu,vv⟩ =>
        -- more simplifications in hypothesis
        unfold Span.beg Span.left Span.right Span.match models at h2;
        simp only at h2;
        let ⟨sp2,⟨⟨xs,ys,⟨h3,h4,h5⟩⟩,h6⟩⟩ := h2;
        -- more simplifications on ~(R ⬝ pad) and endAnchor parts
        delta Span.left Span.right Span.match at h3 h4 h5;
        have hEndAnch := models_NegLookahead_Top.mp h4;
        simp at hEndAnch h3;
        let ⟨j1,j2⟩ := hEndAnch;
        rw [List.length_eq_zero] at j1 j2;
        rw [j2] at h6 h3;
        subst j1; simp at h3 h5 h6; subst h5;
        -- match on uu
        match uu with
        | [] =>
          simp at g1 g2 g3; subst hu g2 g3;
          let ⟨g1,g2⟩ := h6;
          subst g1; simp at h6;
          subst h6;
          -- derive a contradiction using h3
          apply (h3 [] sp2.snd.fst) g1
          simp;
          apply models_TopStar; rfl
        | a::uu =>
          simp at g1 g2 g3; subst hu g2 g3;
          let ⟨g1,_⟩ := h6;
          subst g1;
          simp at h6;
          apply (h3 (a::uu) vv) g1 $ models_TopStar; exact Eq.symm h6
    -- contradiction as u has to be empty by definition
    | a::u => by simp at h

theorem eliminationNegLookaroundsR {R : RE α} {sp : Span σ} :
  sp ⊨ (?! R) → sp ⊨ (?=((~(R ⬝ pad)) ⬝ endAnchor)) :=
  λ h =>
  match hu:sp with
  | ⟨s,u,v⟩ =>
    -- match on u
    match hh:u with
    | [] => by
      -- simplifications/unfolding defs on the goal
      subst hu; simp;
      -- simplify the hypothesis
      simp at h;
      -- match on v
      match hv:v with
      | [] =>
        exists (s,u,v);
        subst hh; simp;
        exact ⟨by exists []; exists []; simp;
                  unfold endAnchor;
                  rw [models_NegLookahead_Top];
                  simp; rw [List.length_eq_zero];
                  subst hv; simp;
                  intro xs ys h1 h2 h3 h4;
                  subst h3 h4;
                  apply (h (s,[],[])) h1; rfl; rfl,
               hv⟩
      | a::v =>
        exists (s,a::v,[]);
        subst hh hv; simp;
        exists a::v; exists [];
        unfold endAnchor;
        exact ⟨by simp;
                  intro xs ys h1 _ h3;
                  apply (h (s,xs,ys)) h1; rfl; simp; exact h3,
               by rw [models_NegLookahead_Top]; simp⟩
    -- contradiction as u has to be empty by definition
    | a::u => by simp at h

/- The main result which implies that if we add \z as primitive regex then negative lookahead is not needed. -/
theorem eliminationNegLookarounds {R : RE α} {sp : Span σ} :
  sp ⊨ (?=((~(R ⬝ pad)) ⬝ endAnchor)) ↔ sp ⊨ (?! R) :=
  ⟨eliminationNegLookaroundsL, eliminationNegLookaroundsR⟩
