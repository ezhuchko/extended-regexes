import Regex.Definitions

open RE

/-
# Metrics

Collection of all the various metrics used in the formalization
to ensure the well-foundedness of the algorithm.
-/

/-- Lookaround height, counting the level of nested applications of lookarounds. -/
@[simp]
def lookaround_height (R : RE α) : Nat :=
  match R with
  | ε | Pred _ => 0
  | l ⋓ r | l ⋒ r | l ⬝ r => max (lookaround_height l) (lookaround_height r)
  | .Star r | ~ r => lookaround_height r
  | ?= r | ?<= r | ?! r | ?<! r => 1 + lookaround_height r

/-- Star height, counting the level of nested applications of star. -/
@[simp]
def star_height (R : RE α) : Nat :=
  match R with
  | ε | Pred _ => 0
  | l ⋓ r | l ⋒ r | l ⬝ r => max (star_height l) (star_height r)
  | .Star r => 1 + star_height r
  | ~ r | ?= r | ?<= r | ?! r | ?<! r => star_height r

/-- Lexicographic combination of star height and size of regex. -/
@[simp]
noncomputable def star_metric (R : RE α) : Nat ×ₗ Nat := (star_height R, sizeOf R)

/-! ### Reversal preserves all metrics -/

@[simp]
theorem reverse_RE_involution (r : RE α) : (r ʳ) ʳ = r := by
  induction r <;> simp_all

theorem sizeOf_reverse_RE (r : RE α) : sizeOf r = sizeOf (r ʳ) := by
  induction r <;> simp_all; omega

theorem lookaround_height_reverse_RE (r : RE α) :
    lookaround_height r = lookaround_height (r ʳ) := by
  induction r <;> simp_all [Nat.max_comm]

theorem star_height_reverse (r : RE α) : star_height r = star_height (r ʳ) := by
  induction r <;> simp_all [Nat.max_comm]

theorem star_metric_reverse_RE (r : RE α) : star_metric r = star_metric (r ʳ) := by
  rw [star_metric, star_metric, ← star_height_reverse, ← sizeOf_reverse_RE]

/-! ### The star metric decreases on subexpressions -/

theorem lex_lt_max_left {a b x y : Nat} : toLex (a, x) < toLex (max a b, 1 + x + y) :=
  Prod.Lex.toLex_lt_toLex.mpr (by omega)

theorem lex_lt_max_right {a b x y : Nat} : toLex (b, y) < toLex (max a b, 1 + x + y) :=
  Prod.Lex.toLex_lt_toLex.mpr (by omega)

theorem lex_lt_succ {a x : Nat} : toLex (a, x) < toLex (a, 1 + x) :=
  Prod.Lex.toLex_lt_toLex.mpr (by omega)

theorem star_metric_Cat_l : star_metric l < star_metric (l ⬝ r) := lex_lt_max_left
theorem star_metric_Cat_r : star_metric r < star_metric (l ⬝ r) := lex_lt_max_right
theorem star_metric_Alt_l : star_metric l < star_metric (l ⋓ r) := lex_lt_max_left
theorem star_metric_Alt_r : star_metric r < star_metric (l ⋓ r) := lex_lt_max_right
theorem star_metric_Inter_l : star_metric l < star_metric (l ⋒ r) := lex_lt_max_left
theorem star_metric_Inter_r : star_metric r < star_metric (l ⋒ r) := lex_lt_max_right

@[simp]
theorem star_metric_Negation : star_metric r < star_metric (~ r) := lex_lt_succ
theorem star_metric_Lookahead : star_metric r < star_metric (?= r) := lex_lt_succ
theorem star_metric_Lookbehind : star_metric r < star_metric (?<= r) := lex_lt_succ
theorem star_metric_NegLookahead : star_metric r < star_metric (?! r) := lex_lt_succ
theorem star_metric_NegLookbehind : star_metric r < star_metric (?<! r) := lex_lt_succ

theorem star_metric_Lookbehind_reverse : star_metric (r ʳ) < star_metric (?<= r) := by
  rw [← star_metric_reverse_RE]; exact star_metric_Lookbehind

theorem star_metric_NegLookbehind_reverse : star_metric (r ʳ) < star_metric (?<! r) := by
  rw [← star_metric_reverse_RE]; exact star_metric_NegLookbehind

theorem star_metric_Star : star_metric r < star_metric (r *) :=
  Prod.Lex.left _ _ (by simp)

theorem star_metric_repeat_first : star_height (r ⁽ n ⁾) < 1 + star_height r := by
  induction n with
  | zero => simp; omega
  | succ n ih => simp_all

theorem star_metric_repeat : star_metric (r ⁽ n ⁾) < star_metric (r *) :=
  Prod.Lex.left _ _ star_metric_repeat_first
