import Regex.Matches

open RE

/-!
# Reasoning about the match semantics

Unfolding lemmas for `Matches` on explicit spans, and the equivalence `↔ᵣ` of regular
expressions together with its basic properties (associativity and congruence of
concatenation, units, and the interaction of `repeat_cat` with reversal).
-/

variable {α σ : Type} [EffectiveBooleanAlgebra α σ] {r p q : RE α}

/-! ### `Matches` on explicit spans

Unfolding lemmas stating each clause of `Matches` in terms of the components of a span `⟨s, u, v⟩`.
Proofs can rewrite with these instead of unfolding `Matches`, which unfolds every constructor. -/

section
variable {s u v : List σ} {sp : Span σ} {X Y : RE α}

theorem matches_eps : ⟨s, u, v⟩ ⊫ (ε : RE α) ↔ u = [] := by simp

theorem matches_pred {φ : α} : ⟨s, u, v⟩ ⊫ Pred φ ↔ ∃ a, u = [a] ∧ a ⊨ φ := by simp

theorem matches_alt : sp ⊫ X ⋓ Y ↔ sp ⊫ X ∨ sp ⊫ Y := by simp only [RE.Matches]

theorem matches_inter : sp ⊫ X ⋒ Y ↔ sp ⊫ X ∧ sp ⊫ Y := by simp only [RE.Matches]

theorem matches_neg : sp ⊫ ~X ↔ ¬ sp ⊫ X := by simp only [RE.Matches]

theorem matches_cat :
    ⟨s, u, v⟩ ⊫ X ⬝ Y ↔
    ∃ u₁ u₂, ⟨s, u₁, u₂ ++ v⟩ ⊫ X ∧ ⟨u₁.reverse ++ s, u₂, v⟩ ⊫ Y ∧ u₁ ++ u₂ = u := by
  simp only [RE.Matches]

theorem matches_lookahead :
    ⟨s, u, v⟩ ⊫ ?= X ↔ u = [] ∧ ∃ v₁ v₂, ⟨s, v₁, v₂⟩ ⊫ X ∧ v₁ ++ v₂ = v := by
  simp only [RE.Matches, Span.beg, Loc.mk.injEq, and_congr_right_iff]
  rintro rfl
  exact ⟨fun ⟨⟨_, a, b⟩, h, rfl, e⟩ => ⟨a, b, h, e⟩, fun ⟨a, b, h, e⟩ => ⟨⟨s, a, b⟩, h, rfl, e⟩⟩

theorem matches_lookbehind :
    ⟨s, u, v⟩ ⊫ ?<= X ↔ u = [] ∧ ∃ s' m, ⟨s', m, v⟩ ⊫ X ∧ m.reverse ++ s' = s := by
  simp only [RE.Matches, Span.beg, Span.end, Loc.mk.injEq, and_congr_right_iff]
  rintro rfl
  exact ⟨fun ⟨⟨a, b, _⟩, h, e, rfl⟩ => ⟨a, b, h, e⟩, fun ⟨a, b, h, e⟩ => ⟨⟨a, b, v⟩, h, e, rfl⟩⟩

theorem matches_neglookahead :
    ⟨s, u, v⟩ ⊫ ?! X ↔ u = [] ∧ ¬ ∃ v₁ v₂, ⟨s, v₁, v₂⟩ ⊫ X ∧ v₁ ++ v₂ = v := by
  have : ⟨s, u, v⟩ ⊫ ?! X ↔ u = [] ∧ ¬ ⟨s, u, v⟩ ⊫ ?= X := by
    simp only [RE.Matches]
    exact and_congr_right fun h => by simp [h]
  rw [this, matches_lookahead]; exact and_congr_right fun h => by simp [h]

theorem matches_neglookbehind :
    ⟨s, u, v⟩ ⊫ ?<! X ↔ u = [] ∧ ¬ ∃ s' m, ⟨s', m, v⟩ ⊫ X ∧ m.reverse ++ s' = s := by
  have : ⟨s, u, v⟩ ⊫ ?<! X ↔ u = [] ∧ ¬ ⟨s, u, v⟩ ⊫ ?<= X := by
    simp only [RE.Matches]
    exact and_congr_right fun h => by simp [h]
  rw [this, matches_lookbehind]; exact and_congr_right fun h => by simp [h]

end

/-- Equivalence of regular expressions: they match exactly the same spans. -/
def matches_equivalence (r q : RE α) : Prop :=
  ∀ {sp}, sp ⊫ r ↔ sp ⊫ q

infixr:30 " ↔ᵣ " => matches_equivalence

/-! ### `↔ᵣ` is an equivalence relation -/

theorem equiv_trans (rq : r ↔ᵣ q) (qp : q ↔ᵣ p) : r ↔ᵣ p := rq.trans qp

theorem equiv_sym (rq : r ↔ᵣ q) : q ↔ᵣ r := rq.symm

theorem equiv_refl : r ↔ᵣ r := Iff.rfl

/-! ### Concatenation -/

theorem equiv_cat_assoc : ((r ⬝ q) ⬝ w) ↔ᵣ (r ⬝ (q ⬝ w)) := by
  rintro ⟨s, u, v⟩
  simp only [matches_cat]
  constructor
  · rintro ⟨_, u₃, ⟨u₁, u₂, h₁, h₂, rfl⟩, h₃, rfl⟩
    exact ⟨u₁, u₂ ++ u₃, by simpa using h₁, ⟨u₂, u₃, h₂, by simpa using h₃, rfl⟩, by simp⟩
  · rintro ⟨u₁, _, h₁, ⟨u₂, u₃, h₂, h₃, rfl⟩, rfl⟩
    exact ⟨u₁ ++ u₂, u₃, ⟨u₁, u₂, by simpa using h₁, h₂, rfl⟩, by simpa using h₃, by simp⟩

theorem equiv_cat_cong (rr : r ↔ᵣ r') (qq : q ↔ᵣ q') : r ⬝ q ↔ᵣ r' ⬝ q' := by
  rintro ⟨s, u, v⟩
  simp only [matches_cat]
  exact exists_congr fun _ => exists_congr fun _ => and_congr rr (and_congr qq Iff.rfl)

/-- `ε` is the left unit of concatenation. -/
theorem equiv_eps_cat : ε ⬝ r ↔ᵣ r := by
  rintro ⟨s, u, v⟩; simp

/-- `ε` is the right unit of concatenation. -/
theorem equiv_cat_eps : r ⬝ ε ↔ᵣ r := by
  rintro ⟨s, u, v⟩; simp only [matches_cat, matches_eps]
  constructor
  · rintro ⟨u₁, _, h, rfl, rfl⟩; simpa using h
  · intro h; exact ⟨u, [], by simpa using h, rfl, by simp⟩

/-! ### Iterated concatenation -/

/-- `rᵐ r = r rᵐ` -/
theorem equiv_repeat_cat_cat : (r ⁽ m ⁾) ⬝ r ↔ᵣ r ⬝ (r ⁽ m ⁾) :=
  match m with
  | 0 => equiv_trans equiv_eps_cat (equiv_sym equiv_cat_eps)
  | _ + 1 => equiv_trans equiv_cat_assoc (equiv_cat_cong equiv_refl equiv_repeat_cat_cat)

/-- Reversal of repetition is repetition of reversal. -/
theorem equiv_reverse_regex_repeat_cat {r : RE α} {m : ℕ} : ((r ⁽ m ⁾) ʳ) ↔ᵣ ((r ʳ) ⁽ m ⁾) :=
  match m with
  | 0 => equiv_refl
  | _ + 1 =>
    equiv_trans (equiv_cat_cong equiv_reverse_regex_repeat_cat equiv_refl) equiv_repeat_cat_cat
