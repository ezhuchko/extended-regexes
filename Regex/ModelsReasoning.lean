import Regex.Models

open RE

/-!
# Match semantics with setoid reasoning

We develop some helper functions to obtain a lemma for the match semantics.
The main property derived here is the characterization of `repeat_cat` and
its interaction with `reverse_regex`.
-/

variable {α σ : Type} [EffectiveBooleanAlgebra α σ] {r p q : RE α}

/-- correctness of regular expressions. -/
def models_equivalence (r q : RE α) : Prop :=
  ∀ {sp}, sp ⊫ r ↔ sp ⊫ q

infixr:30 " ↔ᵣ " => models_equivalence

/-- ↔ᵣ is an equivalence relation. -/
theorem equiv_trans (rq : r ↔ᵣ q) (qp : q ↔ᵣ p) : r ↔ᵣ p :=
  ⟨ Iff.mp qp ∘ Iff.mp rq , Iff.mpr rq ∘ Iff.mpr qp ⟩

theorem equiv_sym (rq : r ↔ᵣ q) : q ↔ᵣ r :=
  ⟨ Iff.mpr rq , Iff.mp rq ⟩

theorem equiv_refl : r ↔ᵣ r := ⟨ id , id ⟩

/-- Core properties of associativity, using `models`. -/
theorem equiv_cat_assoc :
  ((r ⬝ q) ⬝ w) ↔ᵣ (r ⬝ (q ⬝ w)) :=
  λ {sp} =>
  ⟨ λ h => by
    match sp with
    | ⟨s,u,v⟩ =>
      simp at h;
      simp;
      match h with
      | ⟨sp1,sp2,⟨ss1,ss2,b1,b2,k⟩,a2,c⟩ =>
        subst c k;
        clear h
        simp at b2 a2
        exists (ss1); exists (ss2 ++ (sp2)); simp;
        exists b1; exists ss2;
        exists sp2;
        ,
    λ h => by
    match sp with
    | ⟨s,u,v⟩ =>
      simp at h;
      simp;
      match h with
      | ⟨sp1,sp2,a1,⟨ss1,ss2,b1,b2,k⟩,c⟩ =>
        subst c k;
        exact ⟨(sp1 ++ ss1),_,(⟨_,_,
                (by rw[←List.append_assoc]; exact a1),b1,rfl⟩),
                        (by simp; exact b2),
                        (List.append_assoc sp1 ss1 ss2)⟩
  ⟩

/-- Congruence of matching with respect to concatenation, using `models`. -/
theorem equiv_cat_cong (rr : r ↔ᵣ r') (qq : q ↔ᵣ q') :
  r ⬝ q ↔ᵣ r' ⬝ q' :=
  λ {sp} =>
  ⟨ λ h => by
    match sp with
    | ⟨s,u,v⟩ =>
      simp at h;
      match h with
      | ⟨sp1,sp2,a1,b1,c⟩ => simp; exact ⟨sp1,sp2,rr.mp a1,qq.mp b1,c⟩,
    λ h => by
    match sp with
    | ⟨s,u,v⟩ =>
      simp at h;
      match h with
      | ⟨sp1,sp2,a1,b1,c⟩ => simp; exact ⟨sp1,sp2,rr.mpr a1,qq.mpr b1,c⟩
  ⟩

/-- Epsilon is the left unit with respect to concatenation, using `models`. -/
theorem equiv_eps_cat :
  ε ⬝ r ↔ᵣ r :=
  λ {sp} =>
  match sp with
  | ⟨b,n,l⟩ =>
  ⟨ λ h => by
      simp at h
      exact h,
    λ h => by
     simp; exact h⟩

/-- Epsilon is the right unit with respect to concatenation, using `models`. -/
theorem equiv_cat_eps :
  r ⬝ ε ↔ᵣ r :=
  λ {sp} =>
  match sp with
  | ⟨b,n,l⟩ =>
  ⟨ λ h => by simp at h; exact h,
    λ h => by simp; exact h⟩

/-- Symmetry of iterated product, using `models`. -/
theorem equiv_repeat_cat_cat :
  (r ⁽ m ⁾) ⬝ r ↔ᵣ r ⬝ (r ⁽ m ⁾)  :=
  match m with
  | 0 => equiv_trans equiv_eps_cat (equiv_sym equiv_cat_eps)
  | .succ _ => equiv_trans equiv_cat_assoc
                           (equiv_cat_cong equiv_refl equiv_repeat_cat_cat)

/-- Reversal of repetition is repetition of reversal and vice versa, using `models`. -/
theorem equiv_reverse_regex_repeat_cat {r : RE α} {m : ℕ} :
  ((r ⁽ m ⁾) ʳ) ↔ᵣ
  ((r ʳ) ⁽ m ⁾) :=
  match m with
  | 0       => equiv_refl
  | .succ _ => equiv_trans (equiv_cat_cong equiv_reverse_regex_repeat_cat equiv_refl)
                           equiv_repeat_cat_cat
