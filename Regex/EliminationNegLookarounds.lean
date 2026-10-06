import Regex.Correctness

/-!
# Elimination of General Negative Lookarounds

Contains the result that negative lookarounds are not needed when we add the start and end anchors as primitive regexes.
-/

open BA RE

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

@[simp]
theorem RE.matches_TopStar {sp : Span σ} : sp ⊫ (Pred (⊤ : α))* :=
  derives_TopStar |> correctness.mp

@[simp]
theorem matches_NegLookahead_Top {sp : Span σ}:
  sp ⊫ (?!(Pred (⊤ : α))) ↔ sp.mid = [] ∧ sp.right = [] := by
  obtain ⟨s, u, _ | ⟨a, v⟩⟩ := sp <;> simp only [matches_neglookahead, matches_pred] <;> simp

/-- We define the helper notations. The notation for \z is endAnchor and the notation for ⊤* is pad. -/
def endAnchor : RE α := (?!(Pred (⊤ : α)))

def pad : RE α := (Pred (⊤ : α))*

@[simp]
theorem matches_pad {sp : Span σ} : sp ⊫ (pad : RE α) := matches_TopStar

@[simp]
theorem matches_endAnchor {sp : Span σ} : sp ⊫ (endAnchor : RE α) ↔ sp.mid = [] ∧ sp.right = [] :=
  matches_NegLookahead_Top

/- The main result which implies that if we add \z as primitive regex then negative lookahead is not needed. -/
theorem nla_elim {R : RE α} :
  (?! R) ↔ᵣ (?=((~(R ⬝ pad)) ⬝ endAnchor)) := by
  rintro ⟨s, u, v⟩
  simp only [matches_neglookahead, matches_lookahead, matches_cat, matches_neg, matches_endAnchor,
    matches_pad]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h; exact ⟨v, [], ⟨v, [], by simpa using h, ⟨rfl, rfl⟩, by simp⟩, by simp⟩
  · rintro ⟨_, _, ⟨_, _, h, ⟨rfl, rfl⟩, rfl⟩, rfl⟩; simpa using h

theorem eliminationNegLookaroundsL {R : RE α} {sp : Span σ} :
  sp ⊫ (?=((~(R ⬝ pad)) ⬝ endAnchor)) → sp ⊫ (?! R) :=
  nla_elim.mpr

theorem eliminationNegLookaroundsR {R : RE α} {sp : Span σ} :
  sp ⊫ (?! R) → sp ⊫ (?=((~(R ⬝ pad)) ⬝ endAnchor)) :=
  nla_elim.mp
