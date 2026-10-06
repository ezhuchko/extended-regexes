import Regex.Matches
import Regex.Reversal

/-!
# Main correctness theorem

Contains each lemma required to show that `Matches` and `derives` are equivalent,
along with the main correctness proof.
-/

open BA RE

variable [EffectiveBooleanAlgebra α σ]

/-! ### Unfolding `derives` -/

/-- An empty span is matched iff the expression is nullable at its location. -/
theorem derives_nil {R : RE α} : (⟨s, [], v⟩ ⊢ R) = null R ⟨s, v⟩ := by
  rw [derives]; rfl

/-- A non-empty span is matched iff the rest of it is matched by the derivative. -/
theorem derives_cons {R : RE α} :
    (⟨s, a :: u, v⟩ ⊢ R) = (⟨a :: s, u, v⟩ ⊢ (der R ⟨s, a :: (u ++ v)⟩).1) := by
  rw [derives]; rfl

theorem derives_Bot : (sp ⊢ (Pred ⊥ : RE α)) = false :=
  match sp with
  | ⟨_, [], _⟩ => by simp
  | ⟨s, a::u, v⟩ => by rw [derives_cons]; simpa using derives_Bot (sp := ⟨a :: s, u, v⟩)
termination_by sp.mid

theorem derives_Eps :
  sp ⊢ (ε : RE α) ↔ sp.mid = [] :=
  match sp with
  | ⟨_, [], _⟩ => by simp
  | ⟨_, _::_, _⟩ => by simp [derives_Bot]

theorem derives_Pred :
  sp ⊢ (Pred φ : RE α) ↔ ∃ a, sp.mid = [a] ∧ a ⊨ φ :=
  match sp with
  | ⟨_, [], _⟩ => by simp
  | ⟨_, a::_, _⟩ => by by_cases h : a ⊨ φ <;> simp [h, derives_Eps, derives_Bot, and_assoc]

/-! ### Lookarounds -/

theorem derives_to_existsMatch {loc : Loc σ} {r : RE α} :
  existsMatch r loc ↔ ∃ sp, sp ⊢ r ∧ sp.beg = loc :=
  match loc with
  | ⟨s, []⟩ => by
    constructor
    · intro h; exact ⟨⟨s, [], []⟩, by simpa using h, rfl⟩
    · rintro ⟨⟨_, _ | _, _ | _⟩, h, e⟩ <;> simp_all
  | ⟨s, a :: v⟩ => by
    have ih := @derives_to_existsMatch ⟨a :: s, v⟩ (der r ⟨s, a :: v⟩).1
    rw [existsMatch, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨⟨s', u, v'⟩, h, e⟩)
      · exact ⟨⟨s, [], a :: v⟩, by rwa [derives_nil], rfl⟩
      · simp at e; obtain ⟨rfl, rfl⟩ := e
        exact ⟨⟨s, a :: u, v'⟩, by rwa [derives_cons], rfl⟩
    · rintro ⟨⟨s', _ | ⟨b, u⟩, v'⟩, h, e⟩ <;> simp at e
      · obtain ⟨rfl, rfl⟩ := e; exact .inl (by rwa [derives_nil] at h)
      · obtain ⟨rfl, rfl, rfl⟩ := e; exact .inr ⟨⟨b :: s', u, v'⟩, by rwa [derives_cons] at h, rfl⟩
termination_by (loc.right, star_metric r)

/-- Lookarounds have no derivative, so they only match empty spans, where they reduce to `null`. -/
theorem derives_zeroWidth {R : RE α} (h : ∀ x, (der R x).1 = Pred ⊥) :
    sp ⊢ R ↔ sp.mid = [] ∧ null R sp.beg :=
  match sp with
  | ⟨_, [], _⟩ => by simp
  | ⟨_, _::_, _⟩ => by simp [h, derives_Bot]

theorem derives_Lookahead {r : RE α} :
  sp ⊢ (?= r) ↔ (sp.mid = [] ∧ ∃ spM, spM ⊢ r ∧ spM.beg = sp.beg) := by
  rw [derives_zeroWidth fun _ => by rw [der], null, derives_to_existsMatch]

theorem derives_Lookbehind {r : RE α} :
  sp ⊢ (?<= r) ↔ (sp.mid = [] ∧ ∃ spM, spM ⊢ (r ʳ) ∧ spM.beg = sp.beg.reverse) := by
  rw [derives_zeroWidth fun _ => by rw [der], null, ← derives_to_existsMatch]

theorem derives_NegLookahead {r : RE α} :
  sp ⊢ (?! r) ↔ sp.mid = [] ∧ ¬ (∃ spM, spM ⊢ r ∧ spM.beg = sp.beg) := by
  rw [derives_zeroWidth fun _ => by rw [der], null, ← derives_to_existsMatch]; simp

theorem derives_NegLookbehind {r : RE α} :
  sp ⊢ (?<! r) ↔ sp.mid = [] ∧ ¬ (∃ spM, spM ⊢ (r ʳ) ∧ spM.beg = sp.beg.reverse) := by
  rw [derives_zeroWidth fun _ => by rw [der], null, ← derives_to_existsMatch]; simp

/-! ### Boolean operators and concatenation -/

theorem derives_Alt {sp : Span σ} {r : RE α} :
  sp ⊢ (l ⋓ r) ↔ sp ⊢ l ∨ sp ⊢ r :=
  match sp with
  | ⟨_, [], _⟩ => by simp
  | ⟨s, a::u, v⟩ => by
    simp only [derives_cons, der]; exact derives_Alt
termination_by sp.mid

theorem derives_Inter {sp : Span σ} {r : RE α} :
  sp ⊢ (l ⋒ r) ↔ sp ⊢ l ∧ sp ⊢ r :=
  match sp with
  | ⟨_, [], _⟩ => by simp
  | ⟨s, a::u, v⟩ => by
    simp only [derives_cons, der]; exact derives_Inter
termination_by sp.mid

theorem derives_Negation {sp : Span σ} {r : RE α} :
  sp ⊢ (~ r) ↔ ¬ (sp ⊢ r) :=
  match sp with
  | ⟨_, [], _⟩ => by simp
  | ⟨s, a::u, v⟩ => by
    simp only [derives_cons, der]; exact derives_Negation
termination_by sp.mid

theorem derives_Cat {r : RE α} :
  sp ⊢ (l ⬝ r) ↔
  ∃ u₁ u₂,
     ⟨sp.left, u₁, u₂ ++ sp.right⟩ ⊢ l
   ∧ ⟨u₁.reverse ++ sp.left, u₂, sp.right⟩ ⊢ r
   ∧ u₁ ++ u₂ = sp.mid :=
  match sp with
  | ⟨s, [], v⟩ => by 
    simp only [List.append_eq_nil_iff, derives_nil, null, Bool.and_eq_true]
    constructor
    · rintro ⟨h₁, h₂⟩; exact ⟨[], [], by simpa using h₁, by simpa using h₂, rfl, rfl⟩
    · rintro ⟨_, _, h₁, h₂, rfl, rfl⟩; simp_all
  | ⟨s, a::u, v⟩ => by
    let x : Loc σ := ⟨s, a :: (u ++ v)⟩
    have ih := derives_Cat (l := (der l x).1) (r := r) (sp := ⟨a :: s, u, v⟩)
    -- the derivative either continues inside `l`, or `l` is done and `r` takes over
    have step : ⟨a :: s, u, v⟩ ⊢ (der (l ⬝ r) x).1 ↔
        ⟨a :: s, u, v⟩ ⊢ (der l x).1 ⬝ r ∨ null l x ∧ ⟨a :: s, u, v⟩ ⊢ (der r x).1 := by
      rw [der]; split <;> simp_all [derives_Alt]
    rw [derives_cons, step, ih]
    constructor
    · rintro (⟨u₁, u₂, h₁, h₂, rfl⟩ | ⟨hl, h⟩)
      · refine ⟨a :: u₁, u₂, ?_, by simpa using h₂, rfl⟩
        rw [derives_cons]; simpa [x] using h₁
      · exact ⟨[], a :: u, by rw [derives_nil]; exact hl, by rw [derives_cons]; simpa using h, rfl⟩
    · rintro ⟨_ | ⟨b, u₁⟩, u₂, h₁, h₂, e⟩ <;> simp at e
      · subst e; exact .inr ⟨by rwa [derives_nil] at h₁, by rw [derives_cons] at h₂; simpa using h₂⟩
      · obtain ⟨rfl, rfl⟩ := e
        refine .inl ⟨u₁, u₂, ?_, by simpa using h₂, rfl⟩
        rw [derives_cons] at h₁; simpa [x] using h₁
termination_by sp.mid.length

/-! ### Star -/

theorem derives_Star_mp {r : RE α} :
  sp ⊢ (r *) → ∃ (m : ℕ), sp ⊢ (r ⁽ m ⁾) :=
  match sp with
  | ⟨_, [], _⟩ => fun _ => ⟨0, by simp⟩
  | ⟨s, a::u, v⟩ => fun h => by
    rw [derives_cons, der] at h
    obtain ⟨u₁, u₂, h₁, h₂, rfl⟩ := derives_Cat.mp h
    obtain ⟨m, hm⟩ := derives_Star_mp h₂
    refine ⟨m + 1, derives_Cat.mpr ⟨a :: u₁, u₂, ?_, by simpa using hm, rfl⟩⟩
    rw [derives_cons]; simpa using h₁
termination_by sp.mid.length

/-- An iteration in front of a star is absorbed by it. -/
theorem derives_Star_contraction {r : RE α} : sp ⊢ r ⬝ r* → sp ⊢ r* := by
  obtain ⟨s, u, v⟩ := sp
  intro h
  obtain ⟨_ | ⟨a, u₁⟩, u₂, h₁, h₂, e⟩ := derives_Cat.mp h <;> simp at e <;> subst e
  · simpa using h₂
  · rw [derives_cons, der]
    rw [derives_cons] at h₁
    exact derives_Cat.mpr ⟨u₁, u₂, by simpa using h₁, by simpa using h₂, rfl⟩

theorem derives_Star_mpr {r : RE α} : sp ⊢ (r ⁽ m ⁾) → sp ⊢ (r *) :=
  match m with
  | 0 => fun h => by
    obtain ⟨s, u, v⟩ := sp
    obtain rfl : u = [] := derives_Eps.mp h
    simp
  | m + 1 => fun h => by
    obtain ⟨u₁, u₂, h₁, h₂, e⟩ := derives_Cat.mp h
    exact derives_Star_contraction (derives_Cat.mpr ⟨u₁, u₂, h₁, derives_Star_mpr h₂, e⟩)

theorem derives_Star {r : RE α} : sp ⊢ (r *) ↔ ∃ m, sp ⊢ (r ⁽ m ⁾) :=
  ⟨derives_Star_mp, fun ⟨_, h⟩ => derives_Star_mpr h⟩

/-- For any span, iterated true always matches. -/
theorem derives_TopStar {sp : Span σ} : sp ⊢ (Pred (⊤ : α))* :=
  match sp with
  | ⟨_, [], _⟩ => by simp
  | ⟨_, c::m, _⟩ => derives_Star_contraction <|
      derives_Cat.mpr ⟨[c], m, derives_Pred.mpr ⟨c, rfl, by simp⟩, derives_TopStar, rfl⟩
termination_by sp.mid.length

/-! ### Main correctness theorem -/

theorem matches_reversal' {R : RE α} {sp : Span σ} :
    sp ⊫ (R ʳ) ↔ sp.reverse ⊫ R := by
  simpa using matches_reversal (R := Rʳ)

/-- Main correctness theorem. -/
theorem correctness {R : RE α} : sp ⊢ R ↔ sp ⊫ R :=
  match R with
  | ε      => by rw [derives_Eps, RE.Matches]
  | Pred φ => by rw [derives_Pred, RE.Matches]
  | ?= r   => by
    have : star_metric r < star_metric (?= r) := star_metric_Lookahead
    simp only [derives_Lookahead, RE.Matches, @correctness _ r]
  | ?! r   => by
    have : star_metric r < star_metric ?!r := star_metric_NegLookahead
    simp only [derives_NegLookahead, RE.Matches, @correctness _ r]
  | ?<= r  => by
    have : star_metric (r ʳ) < star_metric (?<= r) := star_metric_Lookbehind_reverse
    rw [derives_Lookbehind, RE.Matches, Span.exists_reverse]
    simp only [@correctness _ (r ʳ), matches_reversal', reverse_span_involution, Span.beg_reverse,
      Loc.reverse_inj]
  | ?<! r  => by
    have : star_metric rʳ < star_metric ?<!r := star_metric_NegLookbehind_reverse
    rw [derives_NegLookbehind, RE.Matches, Span.exists_reverse]
    simp only [@correctness _ (r ʳ), matches_reversal', reverse_span_involution, Span.beg_reverse,
      Loc.reverse_inj]
  | ~ r    => by
    have : star_metric r < star_metric (Negation r) := star_metric_Negation
    simp only [derives_Negation, RE.Matches, @correctness _ r]
  | .Star r => by
    have : star_metric r < star_metric (Star r) := star_metric_Star
    rw [derives_Star, RE.Matches]
    exact exists_congr fun m =>
      have : star_metric (r⁽m⁾) < star_metric r* := star_metric_repeat
      correctness
  | l ⋒ r  => by
    have : star_metric l < star_metric (l ⋒ r) := star_metric_Inter_l
    have : star_metric r < star_metric (l ⋒ r) := star_metric_Inter_r
    simp only [derives_Inter, RE.Matches, @correctness _ l, @correctness _ r]
  | l ⋓ r  => by
    have : star_metric l < star_metric (l ⋓ r) := star_metric_Alt_l
    have : star_metric r < star_metric (l ⋓ r) := star_metric_Alt_r
    simp only [derives_Alt, RE.Matches, @correctness _ l, @correctness _ r]
  | l ⬝ r  => by
    have : star_metric l < star_metric (l ⬝ r) := star_metric_Cat_l
    have : star_metric r < star_metric (l ⬝ r) := star_metric_Cat_r
    simp only [derives_Cat, RE.Matches, @correctness _ l, @correctness _ r]
termination_by star_metric R
decreasing_by
  repeat {assumption}

/- Main reversal theorem using the derivation relation instead of `Matches`. -/
theorem derives_reversal {R : RE α} : sp ⊢ R ↔ sp.reverse ⊢ (R ʳ) :=
  correctness.trans (matches_reversal.trans correctness.symm)
