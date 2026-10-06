import Regex.EliminationNegLookarounds
import Regex.Reversal
import Regex.MatchesReasoning

/-!
# Rewrite rules

Contains the correctness proofs for the collection of different simplification rules.
-/

open RE List

variable {α σ : Type} [EffectiveBooleanAlgebra α σ] {s u v : List σ} {sp : Span σ}

theorem pad_reverse : (pad : RE α)ʳ = pad := rfl

/-! ### Zero-width expressions

Concatenating with an expression that only matches the empty word (such as a lookaround)
amounts to a conjunction. -/

/-- `R` only ever matches the empty word. -/
def ZeroWidth (R : RE α) : Prop := ∀ {s u v : List σ}, ⟨s, u, v⟩ ⊫ R → u = []

theorem matches_zeroWidth_cat {R Y : RE α} (h : ZeroWidth R) :
    ⟨s, u, v⟩ ⊫ R ⬝ Y ↔ ⟨s, [], u ++ v⟩ ⊫ R ∧ ⟨s, u, v⟩ ⊫ Y := by
  rw [matches_cat]
  constructor
  · rintro ⟨_, u, hR, hY, rfl⟩
    obtain rfl := h hR
    exact ⟨hR, by simpa using hY⟩
  · rintro ⟨hR, hY⟩
    exact ⟨[], u, hR, by simpa using hY, rfl⟩

theorem matches_cat_zeroWidth {R Y : RE α} (h : ZeroWidth R) :
    ⟨s, u, v⟩ ⊫ Y ⬝ R ↔ ⟨s, u, v⟩ ⊫ Y ∧ ⟨u.reverse ++ s, [], v⟩ ⊫ R := by
  rw [matches_cat]
  constructor
  · rintro ⟨u, _, hY, hR, rfl⟩
    obtain rfl := h hR
    exact ⟨by simpa using hY, by simpa using hR⟩
  · rintro ⟨hY, hR⟩
    exact ⟨u, [], by simpa using hY, by simpa using hR, by simp⟩

theorem zeroWidth_lookahead {X : RE α} : ZeroWidth (?= X) :=
  fun h => (matches_lookahead.mp h).1

theorem zeroWidth_lookbehind {X : RE α} : ZeroWidth (?<= X) :=
  fun h => (matches_lookbehind.mp h).1

theorem zeroWidth_neglookahead {X : RE α} : ZeroWidth (?! X) :=
  fun h => (matches_neglookahead.mp h).1

theorem zeroWidth_neglookbehind {X : RE α} : ZeroWidth (?<! X) :=
  fun h => (matches_neglookbehind.mp h).1

theorem zeroWidth_cat {R Y : RE α} (hR : ZeroWidth R) (hY : ZeroWidth Y) :
    ZeroWidth (R ⬝ Y) :=
  fun h => hY ((matches_zeroWidth_cat hR).mp h).2

/-! Properties of lookarounds, used by the rewrite rules below. -/

theorem matches_lookbehind_cat {X Y : RE α} :
    ⟨s, u, v⟩ ⊫ (?<= X) ⬝ Y ↔ ⟨s, [], u ++ v⟩ ⊫ ?<= X ∧ ⟨s, u, v⟩ ⊫ Y :=
  matches_zeroWidth_cat zeroWidth_lookbehind

theorem matches_neglookbehind_cat {X Y : RE α} :
    ⟨s, u, v⟩ ⊫ (?<! X) ⬝ Y ↔ ⟨s, [], u ++ v⟩ ⊫ ?<! X ∧ ⟨s, u, v⟩ ⊫ Y :=
  matches_zeroWidth_cat zeroWidth_neglookbehind

theorem matches_lookahead_cat {X Y : RE α} :
    ⟨s, u, v⟩ ⊫ (?= X) ⬝ Y ↔ ⟨s, [], u ++ v⟩ ⊫ ?= X ∧ ⟨s, u, v⟩ ⊫ Y :=
  matches_zeroWidth_cat zeroWidth_lookahead

theorem matches_cat_lookahead {X Y : RE α} :
    ⟨s, u, v⟩ ⊫ Y ⬝ (?= X) ↔ ⟨s, u, v⟩ ⊫ Y ∧ ⟨u.reverse ++ s, [], v⟩ ⊫ ?= X :=
  matches_cat_zeroWidth zeroWidth_lookahead

theorem matches_cat_neglookahead {X Y : RE α} :
    ⟨s, u, v⟩ ⊫ Y ⬝ (?! X) ↔ ⟨s, u, v⟩ ⊫ Y ∧ ⟨u.reverse ++ s, [], v⟩ ⊫ ?! X :=
  matches_cat_zeroWidth zeroWidth_neglookahead

/-- Concatenation of two lookaheads. -/
theorem matches_cat_lookaheads {X Y Z : RE α} :
    ⟨s, u, v⟩ ⊫ Y ⬝ ((?= X) ⬝ (?= Z)) ↔
    ⟨s, u, v⟩ ⊫ Y ∧ ⟨u.reverse ++ s, [], v⟩ ⊫ ?= X ∧ ⟨u.reverse ++ s, [], v⟩ ⊫ ?= Z := by
  rw [matches_cat_zeroWidth (zeroWidth_cat zeroWidth_lookahead zeroWidth_lookahead),
    matches_lookahead_cat, List.nil_append]

/-- On an empty span, a negative lookahead is the negation of the positive one. -/
theorem matches_neglookahead_nil {X : RE α} : ⟨s, [], v⟩ ⊫ ?! X ↔ ¬ ⟨s, [], v⟩ ⊫ ?= X := by
  rw [matches_neglookahead, matches_lookahead]; simp

/-- On an empty span, a negative lookbehind is the negation of the positive one. -/
theorem matches_neglookbehind_nil {X : RE α} : ⟨s, [], v⟩ ⊫ ?<! X ↔ ¬ ⟨s, [], v⟩ ⊫ ?<= X := by
  rw [matches_neglookbehind, matches_lookbehind]; simp

def startAnchor : RE α := (?<!(Pred (⊤ : α)))

theorem matches_startAnchor {sp : Span σ}:
  sp ⊫ (startAnchor : RE α) ↔ sp.mid = [] ∧ sp.left = [] := by
  obtain ⟨_ | ⟨a, s⟩, u, v⟩ := sp <;> rw [startAnchor, matches_neglookbehind] <;> simp

/-! ### Rewrite rules -/

theorem equiv_concat_distr_r {r q w : RE α} :
  (r ⬝ (q ⋓ w)) ↔ᵣ ((r ⬝ q) ⋓ (r ⬝ w)) := by
  rintro ⟨s, u, v⟩; simp only [matches_cat, matches_alt, or_and_right, and_or_left, exists_or]

theorem equiv_concat_distr_l {r q w : RE α} :
  ((q ⋓ w) ⬝ r) ↔ᵣ ((q ⬝ r) ⋓ (w ⬝ r)) := by
  rintro ⟨s, u, v⟩; simp only [matches_cat, matches_alt, or_and_right, exists_or]

theorem equiv_inter_comm {r q : RE α} : r ⋒ q ↔ᵣ q ⋒ r := by
  intro sp; simp only [matches_inter, and_comm]

theorem inter_congr {X Y Z Z' : RE α} :
  X ↔ᵣ Z → Y ↔ᵣ Z' → X ⋒ Y ↔ᵣ Z ⋒ Z' :=
  fun h1 h2 {_} => by simp only [matches_inter]; exact and_congr h1 h2

theorem equiv_concat_congr {r : RE α} (h : r ↔ᵣ t) : (r ⬝ q) ↔ᵣ (t ⬝ q) :=
  equiv_cat_cong h equiv_refl

theorem equiv_concat_congr2 {r : RE α} (h : r ↔ᵣ t) : (q ⬝ r) ↔ᵣ (q ⬝ t) :=
  equiv_cat_cong equiv_refl h

/-! ### Lookarounds as matches over their context

A lookaround at a position is a match over the rest of the word (lookahead) or over the
word before the position (lookbehind), padded with `pad` on the side away from the position. -/

/-- A lookahead holds iff `X ⬝ pad` matches the entire rest of the word. -/
theorem lookahead_iff_cat_pad {X : RE α} :
    ⟨s, u, v⟩ ⊫ ?= X ↔ u = [] ∧ ⟨s, v, []⟩ ⊫ X ⬝ pad := by
  rw [matches_lookahead]
  refine and_congr_right fun _ => ?_
  simp

/-- A lookbehind holds iff `pad ⬝ X` matches the entire word before the position. -/
theorem lookbehind_iff_pad_cat {X : RE α} :
    ⟨s, u, v⟩ ⊫ ?<= X ↔ u = [] ∧ ⟨[], s.reverse, v⟩ ⊫ pad ⬝ X := by
  rw [matches_lookbehind]
  refine and_congr_right fun _ => ?_
  simp only [matches_cat, matches_pad, true_and, append_nil]
  constructor
  · rintro ⟨s', m, h, rfl⟩; exact ⟨s'.reverse, m, by simpa, by simp⟩
  · rintro ⟨a, b, h, e⟩; exact ⟨a.reverse, b, h, by rw [← reverse_append, e, reverse_reverse]⟩

/-- `lookahead_iff_cat_pad`, stated for an arbitrary span. -/
theorem claim1 {X : RE α} :
  sp ⊫ (?= X) ↔
  sp.mid.length = 0 ∧ (⟨sp.left, sp.right, sp.mid⟩ ⊫ X ⬝ pad) := by
  obtain ⟨s, u, v⟩ := sp
  simp only [lookahead_iff_cat_pad, length_eq_zero_iff]
  exact and_congr_right fun h => by subst h; rfl

/-- `lookbehind_iff_pad_cat`, stated for an arbitrary span. -/
theorem claim2 {X : RE α} :
  sp ⊫ (?<= X) ↔
  sp.mid.length = 0 ∧ (⟨sp.mid.reverse, sp.left.reverse, sp.right⟩ ⊫ pad ⬝ X) := by
  obtain ⟨s, u, v⟩ := sp
  simp only [lookbehind_iff_pad_cat, length_eq_zero_iff]
  exact and_congr_right fun h => by subst h; rfl

theorem nlb_elim {X : RE α} :
  (?<! X) ↔ᵣ (?<=(startAnchor ⬝ ~(pad ⬝ X))) := by
  intro sp
  erw [matches_reversal, nla_elim, matches_reversal (R := ?<= _)]
  rfl

theorem append_decompose {b g : List σ}
  (h : b ++ g = e ++ f) :
  ∃ x,   b = e ++ x ∧ f = x ++ g
       ∨ e = b ++ x ∧ g = x ++ f :=
  exists_or.mpr (append_eq_append_iff.mp h).symm

theorem lookahead_inter_pad {X Y : RE α} :
  ((?= X) ⋒ (?= Y)) ↔ᵣ (?= (((X ⬝ pad) ⋒ (Y ⬝ pad)))) := by
  rintro ⟨s, u, v⟩
  simp only [matches_inter, matches_lookahead, matches_cat, matches_pad, true_and]
  constructor
  · rintro ⟨⟨rfl, a, b, hX, eX⟩, -, c, d, hY, eY⟩
    exact ⟨rfl, v, [], ⟨⟨a, b, by simpa, by simpa⟩, ⟨c, d, by simpa, eY⟩⟩, by simp⟩
  · rintro ⟨rfl, v₁, v₂, ⟨⟨a, b, hX, rfl⟩, ⟨c, d, hY, e⟩⟩, rfl⟩
    exact ⟨⟨rfl, a, b ++ v₂, hX, by simp⟩, ⟨rfl, c, d ++ v₂, hY, by simp [← e]⟩⟩

theorem concat_lookaheads_inter {X Y : RE α} :
  ((?= X) ⬝ (?= Y)) ↔ᵣ ((?= X) ⋒ (?= Y)) := by
  rintro ⟨s, u, v⟩; simp; aesop

theorem RE.la_join {X Y : RE α} :
  ((?=X) ⬝ (?=Y)) ↔ᵣ (?=((X ⬝ pad) ⋒ (Y ⬝ pad))) :=
  equiv_trans concat_lookaheads_inter lookahead_inter_pad

theorem concat_lookbehinds_inter {X Y : RE α} :
  ((?<= X) ⬝ (?<= Y)) ↔ᵣ ((?<= X) ⋒ (?<= Y)) := by
  rintro ⟨s, u, v⟩; simp; aesop

/-- Same as `la_join`, obtained by reversal. -/
theorem RE.lb_join {X Y : RE α} :
  ((?<=X) ⬝ (?<=Y)) ↔ᵣ (?<=((pad ⬝ X) ⋒ (pad ⬝ Y))) := fun {sp} => by
  rw [matches_reversal, matches_reversal (R := ?<= _)]
  exact equiv_trans concat_lookaheads_inter (equiv_trans equiv_inter_comm lookahead_inter_pad)

theorem lookbehind_concat_distr_inter {X Y Z : RE α} :
  (?<= Z) ⬝ (X ⋒ Y) ↔ᵣ (?<= Z) ⬝ X ⋒ (?<= Z) ⬝ Y := by
  rintro ⟨s, u, v⟩; simp only [matches_lookbehind_cat, matches_inter]; tauto

theorem lookahead_concat_distr_inter {X Y Z : RE α} :
  sp ⊫ (X ⋒ Y) ⬝ (?= Z) ↔ (sp ⊫ (X ⬝ (?= Z)) ⋒ (Y ⬝ (?= Z))) := by
  obtain ⟨s, u, v⟩ := sp; simp only [matches_cat_lookahead, matches_inter]; tauto

theorem and_elim1 {X Y : RE α} :
  (((?<= X) ⬝ (?<= X')) ⬝ (Y ⋒ Y')) ↔ᵣ ((?<= X) ⬝ Y) ⋒ ((?<= X') ⬝ Y') :=
  equiv_trans equiv_cat_assoc (by
    rintro ⟨s, u, v⟩; simp only [matches_lookbehind_cat, matches_inter]; tauto)

theorem and_elim2 {X Y : RE α} :
  (X ⋒ Y) ⬝ (?=Z) ⬝ (?=Z') ↔ᵣ (X ⬝ (?=Z)) ⋒ (Y ⬝ (?=Z')) := by
  rintro ⟨s, u, v⟩; simp only [matches_cat_lookaheads, matches_cat_lookahead, matches_inter]; tauto

theorem RE.and_elim {X Y Z : RE α} :
  (?<= X) ⬝ Y ⬝ (?= Z) ⋒ (?<= X') ⬝ Y' ⬝ (?= Z') ↔ᵣ ((?<= X) ⬝ (?<= X') ⬝ (Y ⋒ Y') ⬝ (?= Z) ⬝ (?= Z')) := by
  rintro ⟨s, u, v⟩
  simp only [matches_inter, matches_lookbehind_cat, matches_cat_lookahead, matches_cat_lookaheads]
  tauto

theorem not_elim_helper1 {Y : RE α} {sp: Span σ} :
  sp ⊫ ~ (Y ⬝ (?=Z)) ↔ sp ⊫ ~ Y ⋓ (pad ⬝ ?!Z) := by
  obtain ⟨s, u, v⟩ := sp
  simp only [matches_neg, matches_alt, matches_cat_lookahead, matches_cat_neglookahead, matches_pad,
    true_and, matches_neglookahead_nil]
  tauto

theorem not_elim_helper2 {Y : RE α} {sp: Span σ} :
  sp ⊫ ~ ((?<= X) ⬝ Y) ↔ sp ⊫ (?<! X ⬝ pad) ⋓ ~ Y := by
  obtain ⟨s, u, v⟩ := sp
  simp only [matches_neg, matches_alt, matches_lookbehind_cat, matches_neglookbehind_cat, matches_pad,
    and_true, matches_neglookbehind_nil]
  tauto

theorem not_elim {X Y : RE α} {sp: Span σ}:
  sp ⊫ ~((?<= X) ⬝ Y ⬝ (?=Z)) ↔
  sp ⊫ ((?<!X) ⬝ pad) ⋓ ~Y ⋓ (pad ⬝ ?!Z) := by
  obtain ⟨s, u, v⟩ := sp
  simp only [matches_neg, matches_alt, matches_lookbehind_cat, matches_neglookbehind_cat,
    matches_cat_lookahead, matches_cat_neglookahead, matches_pad, true_and, and_true,
    matches_neglookbehind_nil, matches_neglookahead_nil]
  tauto

theorem nm1 {R : RE α} :
  sp ⊫ R ↔ sp ⊫ ((?<=ε) ⬝ R ⬝ (?=ε)) := by
  obtain ⟨s, u, v⟩ := sp
  simp only [matches_lookbehind_cat, matches_cat_lookahead, matches_lookbehind, matches_lookahead,
    matches_eps]
  simp
