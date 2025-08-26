import Regex.Definitions

open RE

/-
# Metrics

Collection of all the various metrics used in the formalization
to ensure the well-foundedness of the algorithm.
-/

/-- Size of metric function, counting the number of constructors. -/
@[simp]
def sizeOf_RE (R : RE α) : Nat :=
  match R with
  | ε       => 0
  | Pred _  => 0
  | l ⋓ r   => 1 + sizeOf_RE l + sizeOf_RE r
  | l ⋒ r   => 1 + sizeOf_RE l + sizeOf_RE r
  | l ⬝ r   => 1 + sizeOf_RE l + sizeOf_RE r
  | .Star r => 1 + sizeOf_RE r
  | ~ r     => 1 + sizeOf_RE r
  | ?= r    => 1 + sizeOf_RE r
  | ?<= r   => 1 + sizeOf_RE r
  | ?! r    => 1 + sizeOf_RE r
  | ?<! r   => 1 + sizeOf_RE r

/-- Lookaround height, counting the level of nested applications of lookarounds. -/
@[simp]
def lookaround_height (R : RE α) : Nat :=
  match R with
  | ε       => 0
  | Pred _  => 0
  | l ⋓ r   => max (lookaround_height l) (lookaround_height r)
  | l ⋒ r   => max (lookaround_height l) (lookaround_height r)
  | l ⬝ r   => max (lookaround_height l) (lookaround_height r)
  | .Star r => lookaround_height r
  | ~ r     => lookaround_height r
  | ?= r    => 1 + lookaround_height r
  | ?<= r   => 1 + lookaround_height r
  | ?! r    => 1 + lookaround_height r
  | ?<! r   => 1 + lookaround_height r

/-- Lexicographic combination of star height and size of regexp. -/
@[simp]
def star_metric (R : RE α) : Nat ×ₗ Nat :=
  match R with
  | ε       => (0, 0)
  | Pred _  => (0, 0)
  | l ⋓ r   => (max (star_metric l).1 (star_metric r).1, 1 + (star_metric l).2 + (star_metric r).2)
  | l ⋒ r   => (max (star_metric l).1 (star_metric r).1, 1 + (star_metric l).2 + (star_metric r).2)
  | l ⬝ r   => (max (star_metric l).1 (star_metric r).1, 1 + (star_metric l).2 + (star_metric r).2)
  | .Star r => (1 + (star_metric r).1, 1 + (star_metric r).2)
  | ~ r     => ((star_metric r).1, 1 + (star_metric r).2)
  | ?= r    => ((star_metric r).1, 1 + (star_metric r).2)
  | ?<= r   => ((star_metric r).1, 1 + (star_metric r).2)
  | ?! r    => ((star_metric r).1, 1 + (star_metric r).2)
  | ?<! r   => ((star_metric r).1, 1 + (star_metric r).2)

instance : WellFoundedRelation (Nat ×ₗ Nat) where
  rel := (· < ·)
  wf  := WellFounded.prod_lex WellFoundedRelation.wf WellFoundedRelation.wf

@[simp]
theorem sizeOf_reverse_RE (r : RE α) :
  sizeOf r = sizeOf (r ʳ) :=
  match r with
  | ε | Pred _ => rfl
  | l ⬝ r   => by simp; rw [←(sizeOf_reverse_RE l),←(sizeOf_reverse_RE r)]; ac_rfl
  | l ⋓ r | l ⋒ r  => by simp; rw [←(sizeOf_reverse_RE l),←(sizeOf_reverse_RE r)]
  | .Star r      => by simp[sizeOf_reverse_RE r]
  | ~ r | ?= r | ?<= r | ?! r | ?<! r => by simp[←sizeOf_reverse_RE r]

theorem sizeOf_reverse_RE' (r : RE α) :
  sizeOf_RE r = sizeOf_RE (r ʳ) :=
  match r with
  | ε | Pred _  => rfl
  | l ⬝ r   => by simp; rw [←(sizeOf_reverse_RE' l),←(sizeOf_reverse_RE' r)]; ac_rfl
  | l ⋓ r | l ⋒ r => by simp; rw [←(sizeOf_reverse_RE' l),←(sizeOf_reverse_RE' r)]
  | .Star r | ~ r | ?= r | ?<= r | ?! r | ?<! r  => by simp[←sizeOf_reverse_RE' r]

@[simp]
theorem reverse_RE_involution (r : RE α) :
  (r ʳ) ʳ = r :=
  match r with
  | ε | Pred _ => rfl
  | l ⬝ r | l ⋓ r | l ⋒ r => by simp; rw [(reverse_RE_involution l),(reverse_RE_involution r)]; exact ⟨rfl,rfl⟩
  | .Star r | ~ r | ?= r | ?<= r | ?! r | ?<! r  => by simp; rw [reverse_RE_involution r]

theorem star_metric_reverse_RE (r : RE α) :
  star_metric r = star_metric (r ʳ) :=
  match r with
  | ε | Pred _  => rfl
  | l ⬝ r   => by simp[←star_metric_reverse_RE l,←star_metric_reverse_RE r]; ac_rfl
  | l ⋓ r | l ⋒ r => by simp; rw [←star_metric_reverse_RE l,←star_metric_reverse_RE r]
  | .Star r | ~ r | ?= r | ?<= r | ?! r | ?<! r  => by simp[star_metric_reverse_RE r]

instance : WellFoundedRelation (Nat ×ₗ Nat ×ₗ Nat ×ₗ Nat) where
  rel := (· < ·)
  wf  :=  WellFounded.prod_lex WellFoundedRelation.wf
          (WellFounded.prod_lex WellFoundedRelation.wf
          (WellFounded.prod_lex WellFoundedRelation.wf WellFoundedRelation.wf))

/--
  Main termination metric used in the definition of derivative, nullability and existence of match
  We employ a trick on the metric used with Nat being either 0/1 to
  ensure that existsMatch will be prioritized in determining the termination order.
-/
def der_termination_metric (r : RE α) (x : Loc σ) (n : Nat) : Nat ×ₗ Nat ×ₗ Nat ×ₗ Nat :=
  (lookaround_height r, sizeOf x.right, sizeOf_RE r, n)

def der_metric (r : RE α) : Nat ×ₗ Nat :=
  (sizeOf_RE r, lookaround_height r)

/- Lemmas on the metric functions defined previously. -/

/-- Lookaround is preserved by reversal. -/
theorem lookaround_height_reverse_RE (r : RE α) :
  lookaround_height r = lookaround_height (r ʳ) :=
  match r with
  | ε | Pred _ => rfl
  | l ⬝ r  => by simp; rw [←(lookaround_height_reverse_RE l),←(lookaround_height_reverse_RE r)]; ac_rfl
  | l ⋓ r | l ⋒ r  => by simp; rw [←(lookaround_height_reverse_RE l),←(lookaround_height_reverse_RE r)]
  | .Star r | ~ r | ?= r | ?<= r | ?! r | ?<! r => by simp[←lookaround_height_reverse_RE r]

/- Coherence with respect to the derivative termination metric and constructors. -/

@[simp]
theorem lookaround_height_Cat_L :
  der_termination_metric l x 0 < der_termination_metric (l ⬝ r) x 0 := by
  by_cases h: (lookaround_height l = lookaround_height (l ⬝ r))
  . unfold der_termination_metric; rw [h]
    apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.left; simp only [sizeOf_RE]; linarith
  . exact Prod.Lex.left _ _ (Nat.lt_of_le_of_ne (by simp only [lookaround_height, le_sup_left]) h)

@[simp]
theorem lookaround_height_Cat_R :
  der_termination_metric r x 0 < der_termination_metric (l ⬝ r) x 0 := by
  by_cases h : (lookaround_height r = lookaround_height (l ⬝ r));
  . unfold der_termination_metric; rw [h]
    apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.left
    simp only [sizeOf_RE, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, true_or]
  . exact Prod.Lex.left _ _ (Nat.lt_of_le_of_ne (by simp only [lookaround_height, le_sup_right]) h)

@[simp]
theorem lookaround_height_Alt_L :
  der_termination_metric l x 0 < der_termination_metric (l ⋓ r) x 0 := by
  by_cases h : (lookaround_height l = lookaround_height (l ⋓ r));
  . unfold der_termination_metric; rw [h]
    apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.left; simp; linarith
  . exact Prod.Lex.left _ _ (Nat.lt_of_le_of_ne (by simp only [lookaround_height, le_sup_left]) h)

@[simp]
theorem lookaround_height_Alt_R :
  der_termination_metric r x 0 < der_termination_metric (l ⋓ r) x 0 := by
  by_cases h : (lookaround_height r = lookaround_height (l ⋓ r));
  . unfold der_termination_metric; rw [h]
    apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.left; simp
  . exact Prod.Lex.left _ _ (Nat.lt_of_le_of_ne (by simp only [lookaround_height, le_sup_right]) h)

@[simp]
theorem lookaround_height_Inter_L :
  der_termination_metric l x 0 < der_termination_metric (l ⋒ r) x 0 := by
  by_cases h : (lookaround_height l = lookaround_height (l ⋒ r));
  . unfold der_termination_metric; rw [h]
    apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.left; simp; linarith
  . exact Prod.Lex.left _ _ (Nat.lt_of_le_of_ne (by simp only [lookaround_height, le_sup_left]) h)

@[simp]
theorem lookaround_height_Inter_R :
  der_termination_metric r x 0 < der_termination_metric (l ⋒ r) x 0 := by
  by_cases h : (lookaround_height r = lookaround_height (l ⋒ r));
  . unfold der_termination_metric; rw [h]
    apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.left; simp
  . exact Prod.Lex.left _ _ (Nat.lt_of_le_of_ne (by simp only [lookaround_height, le_sup_right]) h)

@[simp]
theorem der_termination_metric_Star :
  der_termination_metric r x 0 < der_termination_metric (r *) x 0 := by
  apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.left
  simp only [sizeOf_RE, lt_add_iff_pos_left, zero_lt_one]

@[simp]
theorem der_termination_metric_Negation :
  der_termination_metric r x 0 < der_termination_metric (~ r) x 0 := by
  apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.left
  simp only [sizeOf_RE, lt_add_iff_pos_left, zero_lt_one]

@[simp]
theorem der_termination_metric_Lookahead :
  der_termination_metric r x 1 < der_termination_metric (?= r) x 0 :=
  Prod.Lex.left _ _ (by simp only [lookaround_height, lt_add_iff_pos_left, zero_lt_one])

@[simp]
theorem der_termination_metric_Lookbehind_reverse :
  der_termination_metric (r ʳ) (x.snd, x.fst) 1 < der_termination_metric (?<! r) x 0 := by
  apply Prod.Lex.left
  simp only [lookaround_height, lookaround_height_reverse_RE r, lt_add_iff_pos_left, zero_lt_one]

@[simp]
theorem der_termination_metric_NegLookahead :
  der_termination_metric r x 1 < der_termination_metric (?! r) x 0 :=
  by apply Prod.Lex.left; simp only [lookaround_height, lt_add_iff_pos_left, zero_lt_one]

@[simp]
theorem der_termination_metric_NegLookbehind_reverse :
  der_termination_metric (r ʳ) (x.snd, x.fst) 1 < der_termination_metric (?<= r) x 0 :=
  by apply Prod.Lex.left
     simp only [← lookaround_height_reverse_RE, lookaround_height, lt_add_iff_pos_left, zero_lt_one]

@[simp]
theorem der_termination_metric_Nat_decrease :
  der_termination_metric r x 0 < der_termination_metric r x 1 :=
  by repeat (first | apply Prod.Lex.right | apply Nat.zero_lt_succ)

@[simp]
theorem der_termination_metric_List_decrease :
  lookaround_height r ≤ lookaround_height q → der_termination_metric r (y :: xs, ys) 1 < der_termination_metric q (xs, y :: ys) 1 := fun h =>
  match Nat.eq_or_lt_of_le h with
  | Or.inl g => by
    simp [der_termination_metric, g]
    apply Prod.Lex.right; apply Prod.Lex.left; simp
  | Or.inr g => Prod.Lex.left _ _ g

theorem star_metric_Cat_r :
  (star_metric r) < (star_metric (l ⬝ r)) := by
  by_cases g : (star_metric l).fst ≤ (star_metric r).fst
  . simp only [star_metric, Nat.instMax, maxOfLe, max, g]
    apply Prod.Lex.right
    simp only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, true_or]
  . exact Prod.Lex.left _ _ (lt_sup_of_lt_left (not_le.mp g))

theorem star_metric_Cat_l :
  (star_metric l) < (star_metric (l ⬝ r)) := by
  simp only [star_metric, Nat.instMax, maxOfLe, max]
  by_cases g : (star_metric l).fst ≤ (star_metric r).fst
  . by_cases h : ((star_metric l).fst = (star_metric r).fst)
    . simp only [← h, le_refl]; exact Prod.Lex.right _ (by linarith)
    . simp_all only; apply Prod.Lex.left _ _ (Nat.lt_of_le_of_ne g h)
  . simp only [g]; exact Prod.Lex.right _ (by linarith)

theorem star_metric_Alt_l :
  star_metric l < star_metric (l ⋓ r) := by
  simp only [star_metric, Nat.instMax, maxOfLe, max]
  by_cases g : (star_metric l).fst ≤ (star_metric r).fst
  . simp only [g]
    by_cases g1 : ((star_metric l).fst = (star_metric r).fst)
    . rw[←g1]; exact Prod.Lex.right _ (by linarith);
    . exact Prod.Lex.left _ _ (Nat.lt_of_le_of_ne g g1);
  . simp only [g]; exact Prod.Lex.right _ (by linarith)

theorem star_metric_Alt_r :
  star_metric r < star_metric (l ⋓ r) := by
  simp only [star_metric, Nat.instMax, maxOfLe, max]
  by_cases g : (star_metric l).fst ≤ (star_metric r).fst
  . simp only [g]; exact Prod.Lex.right _ (by linarith)
  . simp only [g]; exact Prod.Lex.left _ _ (Nat.gt_of_not_le g)

theorem star_metric_Inter_l :
  star_metric l < star_metric (l ⋒ r) := by
  simp only [star_metric, Nat.instMax, maxOfLe, max]
  split
  . have g : (star_metric l).fst ≤ (star_metric r).fst := by assumption
    by_cases h : ((star_metric l).fst = (star_metric r).fst)
    . rw[←h]; exact Prod.Lex.right _ (by linarith)
    . exact Prod.Lex.left _ _ (Nat.lt_of_le_of_ne g h)
  . exact Prod.Lex.right _ (by linarith)

theorem star_metric_Inter_r :
  star_metric r < star_metric (l ⋒ r) := by
  simp [star_metric,max, Nat.instMax, maxOfLe]
  split
  . have g : (star_metric l).fst ≤ (star_metric r).fst := by assumption
    exact Prod.Lex.right _ (by linarith)
  . exact Prod.Lex.left _ _ (by rename_i h; exact Nat.gt_of_not_le h)

@[simp]
theorem star_metric_Negation :
  star_metric r < star_metric (~ r) := Prod.Lex.right _ (lt_one_add (star_metric r).2)

theorem star_metric_Lookahead : star_metric r < star_metric (?= r) := Prod.Lex.right _ (lt_one_add (star_metric r).2)

theorem star_metric_Lookbehind : star_metric r < star_metric (?<= r) := Prod.Lex.right _ (lt_one_add (star_metric r).2)

theorem star_metric_NegLookahead : star_metric r < star_metric (?! r) := Prod.Lex.right _ (lt_one_add (star_metric r).2)

theorem star_metric_NegLookbehind : star_metric r < star_metric (?<! r) := Prod.Lex.right _ (lt_one_add (star_metric r).2)

theorem star_metric_Lookahead_reverse : star_metric (r ʳ) < star_metric (?= r) := by
  rw [star_metric_reverse_RE, reverse_RE_involution]
  exact star_metric_Lookahead

theorem star_metric_Lookbehind_reverse : star_metric (r ʳ) < star_metric (?<= r) := by
  rw [star_metric_reverse_RE, reverse_RE_involution];
  exact star_metric_Lookbehind

theorem star_metric_NegLookahead_reverse : star_metric (r ʳ) < star_metric (?! r) := by
  rw [star_metric_reverse_RE, reverse_RE_involution];
  exact star_metric_NegLookahead

theorem star_metric_NegLookbehind_reverse : star_metric (r ʳ) < star_metric (?<! r) := by
  rw [star_metric_reverse_RE, reverse_RE_involution];
  exact star_metric_NegLookbehind

theorem star_metric_repeat_first : (star_metric (r ⁽ n ⁾)).fst < 1 + (star_metric r).fst :=
  match n with
  | 0          => by simp[star_metric]
  | Nat.succ n => by
    simp only [repeat_cat, star_metric, sup_lt_iff, lt_add_iff_pos_left, zero_lt_one, true_and]
    exact (@star_metric_repeat_first _ r n)

theorem star_metric_repeat : (star_metric (r ⁽ n ⁾)) < (star_metric (r *)) := Prod.Lex.left _ _ star_metric_repeat_first

theorem star_metric_Star : (star_metric r) < (star_metric (r *)) := Prod.Lex.left _ _ (lt_one_add (star_metric r).1)

theorem star_metric_cat_Star : star_metric (r ⬝ (r ⁽ m ⁾)) < star_metric (r *) := by
  apply Prod.Lex.left
  simp only [sup_lt_iff, lt_add_iff_pos_left, zero_lt_one, true_and]
  exact star_metric_repeat_first
