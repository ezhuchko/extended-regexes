import Regex.Definitions

open RE

/--
# Metrics

Collection of all the various metrics used in the formalization
to ensure the well-foundedness of the algorithm.
-/

@[simp]
theorem sizeOf_reverse_RE (r : RE α) :
  sizeOf r = sizeOf (r ʳ) :=
  match r with
  | ε | Pred _ => rfl
  | l ⬝ r   => by simp; rw [←(sizeOf_reverse_RE l),←(sizeOf_reverse_RE r)]; ac_rfl
  | l ⋓ r | l ⋒ r  => by simp; rw [←(sizeOf_reverse_RE l),←(sizeOf_reverse_RE r)]
  | r *     => by simp[sizeOf_reverse_RE r]
  | ~ r | ?= r | ?<= r | ?! r | ?<! r => by simp[←sizeOf_reverse_RE r]

theorem sizeOf_reverse_RE' (r : RE α) :
  sizeOf_RE r = sizeOf_RE (r ʳ) :=
  match r with
  | ε | Pred _  => rfl
  | l ⬝ r   => by simp; rw [←(sizeOf_reverse_RE' l),←(sizeOf_reverse_RE' r)]; ac_rfl
  | l ⋓ r | l ⋒ r => by simp; rw [←(sizeOf_reverse_RE' l),←(sizeOf_reverse_RE' r)]
  | r * | ~ r | ?= r | ?<= r | ?! r | ?<! r  => by simp[←sizeOf_reverse_RE' r]

@[simp]
theorem reverse_RE_involution (r : RE α) :
  (r ʳ) ʳ = r :=
  match r with
  | ε | Pred _ => rfl
  | l ⬝ r  => by simp; rw [(reverse_RE_involution l),(reverse_RE_involution r)]; simp
  | l ⋓ r | l ⋒ r => by simp; rw [(reverse_RE_involution l),(reverse_RE_involution r)]; simp
  | r * | ~ r | ?= r | ?<= r | ?! r | ?<! r  => by simp; rw [reverse_RE_involution r]

theorem star_metric_reverse_RE (r : RE α) :
  star_metric r = star_metric (r ʳ) :=
  match r with
  | ε | Pred _  => rfl
  | l ⬝ r   => by simp[←star_metric_reverse_RE l,←star_metric_reverse_RE r]; ac_rfl
  | l ⋓ r | l ⋒ r => by simp; rw [←star_metric_reverse_RE l,←star_metric_reverse_RE r]
  | r * | ~ r | ?= r | ?<= r | ?! r | ?<! r  => by simp[star_metric_reverse_RE r]

/--
Main termination metric used in the definition of derivative, nullability and existence of match
We employ a trick on the metric used with Nat being either 0/1 to
ensure that existsMatch will be prioritized in determining the termination order.
-/

instance : WellFoundedRelation (ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ) where
  rel := (· < ·)
  wf  :=  WellFounded.prod_lex WellFoundedRelation.wf
          (WellFounded.prod_lex WellFoundedRelation.wf
          (WellFounded.prod_lex WellFoundedRelation.wf WellFoundedRelation.wf))

def der_termination_metric (r : RE α) (x : Loc σ) (n : ℕ) : ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ :=
  (lookaround_height r, sizeOf x.right, sizeOf_RE r, n)

def der_metric (r : RE α) : ℕ ×ₗ ℕ :=
  (sizeOf_RE r, lookaround_height r)

/-- Lemmas on the metric functions defined previously. -/

/- Lookaround is preserved by reversal. -/
theorem lookaround_height_reverse_RE (r : RE α) :
  lookaround_height r = lookaround_height (r ʳ) :=
  match r with
  | ε | Pred _ => rfl
  | l ⬝ r  => by
    simp; rw [←(lookaround_height_reverse_RE l),←(lookaround_height_reverse_RE r)]; ac_rfl
  | l ⋓ r | l ⋒ r  => by
    simp; rw [←(lookaround_height_reverse_RE l),←(lookaround_height_reverse_RE r)]
  | r * | ~ r | ?= r | ?<= r | ?! r | ?<! r => by simp[←lookaround_height_reverse_RE r]

/- Coherence with respect to the derivative termination metric and constructors. -/

@[simp]
theorem lookaround_height_Cat_L :
  der_termination_metric l x 0 < der_termination_metric (l ⬝ r) x 0 :=
  by by_cases h: (lookaround_height l = lookaround_height (l ⬝ r));
     unfold der_termination_metric;
     rw [h]; apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.left; simp; linarith;
     have h1 : lookaround_height l < lookaround_height (l ⬝ r) :=
      Nat.lt_of_le_of_ne (by aesop) h
     apply Prod.Lex.left; exact h1

@[simp]
theorem lookaround_height_Cat_R :
  der_termination_metric r x 0 < der_termination_metric (l ⬝ r) x 0 :=
  by by_cases h : (lookaround_height r = lookaround_height (l ⬝ r));
     unfold der_termination_metric;
     rw [h]; apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.left; simp;
     have h1 : lookaround_height r < lookaround_height (l ⬝ r) :=
      by apply Nat.lt_of_le_of_ne (by aesop) h
     apply Prod.Lex.left; exact h1

@[simp]
theorem lookaround_height_Alt_L :
  der_termination_metric l x 0 < der_termination_metric (l ⋓ r) x 0 :=
  by by_cases h : (lookaround_height l = lookaround_height (l ⋓ r));
     unfold der_termination_metric;
     rw [h]; apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.left; simp; linarith;
     have h1 : lookaround_height l < lookaround_height (l ⬝ r) :=
      Nat.lt_of_le_of_ne (by aesop) h;
     apply Prod.Lex.left; exact h1

@[simp]
theorem lookaround_height_Alt_R :
  der_termination_metric r x 0 < der_termination_metric (l ⋓ r) x 0 :=
  by by_cases h : (lookaround_height r = lookaround_height (l ⋓ r));
     unfold der_termination_metric;
     rw [h]; apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.left; simp;
     have h1 : lookaround_height r < lookaround_height (l ⬝ r) :=
      Nat.lt_of_le_of_ne (by aesop) h;
     apply Prod.Lex.left; exact h1

@[simp]
theorem lookaround_height_Inter_L :
  der_termination_metric l x 0 < der_termination_metric (l ⋒ r) x 0 :=
  by by_cases h : (lookaround_height l = lookaround_height (l ⋒ r));
     unfold der_termination_metric;
     rw [h]; apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.left; simp; linarith;
     have h1 : lookaround_height l < lookaround_height (l ⬝ r) :=
      Nat.lt_of_le_of_ne (by aesop) h;
     apply Prod.Lex.left; exact h1

@[simp]
theorem lookaround_height_Inter_R :
  der_termination_metric r x 0 < der_termination_metric (l ⋒ r) x 0 :=
  by by_cases h : (lookaround_height r = lookaround_height (l ⋒ r));
     unfold der_termination_metric;
     rw [h]; apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.left; simp;
     have h1 : lookaround_height r < lookaround_height (l ⬝ r) :=
      Nat.lt_of_le_of_ne (by aesop) h;
     apply Prod.Lex.left; exact h1

@[simp]
theorem der_termination_metric_Star :
  der_termination_metric r x 0 < der_termination_metric (r *) x 0 :=
  by apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.left;
     simp only [sizeOf_RE, lt_add_iff_pos_left]; simp

@[simp]
theorem der_termination_metric_Negation :
  der_termination_metric r x 0 < der_termination_metric (~ r) x 0 :=
  by apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.left;
     simp only [sizeOf_RE, lt_add_iff_pos_left]; simp

@[simp]
theorem der_termination_metric_Lookahead :
  der_termination_metric r x 1 < der_termination_metric (?= r) x 0 :=
  by unfold der_termination_metric; apply Prod.Lex.left; simp

@[simp]
theorem der_termination_metric_Lookbehind_reverse :
  der_termination_metric (r ʳ) (x.snd, x.fst) 1 < der_termination_metric (?<! r) x 0 :=
  by unfold der_termination_metric; apply Prod.Lex.left; simp; rw [←lookaround_height_reverse_RE]; simp

@[simp]
theorem der_termination_metric_NegLookahead :
  der_termination_metric r x 1 < der_termination_metric (?! r) x 0 :=
  by unfold der_termination_metric; apply Prod.Lex.left; simp

@[simp]
theorem der_termination_metric_NegLookbehind_reverse :
  der_termination_metric (r ʳ) (x.snd, x.fst) 1 < der_termination_metric (?<= r) x 0 :=
  by unfold der_termination_metric; apply Prod.Lex.left; simp; rw [←lookaround_height_reverse_RE]; simp

@[simp]
theorem der_termination_metric_Nat_decrease :
  der_termination_metric r x 0 < der_termination_metric r x 1 :=
  by unfold der_termination_metric; repeat (first | apply Prod.Lex.right | apply Nat.zero_lt_succ)

@[simp]
theorem der_termination_metric_List_decrease :
  lookaround_height r ≤ lookaround_height q → der_termination_metric r (y :: xs, ys) 1 < der_termination_metric q (xs, y :: ys) 1 :=
  λ h =>
  by unfold der_termination_metric; have g := Nat.eq_or_lt_of_le h;
     match g with | Or.inl g => rw [g]; simp; apply Prod.Lex.right; apply Prod.Lex.left; simp;
                  | Or.inr g => apply Prod.Lex.left; exact g

theorem star_metric_Cat_r : (star_metric r) < (star_metric (l ⬝ r)) := by
  simp [star_metric, ge_iff_le,max, Nat.instMax, maxOfLe]
  by_cases g : (star_metric l).fst ≤ (star_metric r).fst
  . simp_all only [sup_of_le_right]
    apply Prod.Lex.right
    simp only [lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff, pos_of_gt, true_or]
  . simp only [not_le] at g;
    exact Prod.Lex.left _ _ (lt_sup_of_lt_left g)

theorem star_metric_Cat_l : (star_metric l) < (star_metric (l ⬝ r)) := by
  simp [star_metric, ge_iff_le,max, Nat.instMax, maxOfLe]
  unfold max Nat.instMax_mathlib inferInstance Nat.instMax maxOfLe
  simp only
  by_cases g : (star_metric l).fst ≤ (star_metric r).fst
  . by_cases h : ((star_metric l).fst = (star_metric r).fst)
    . simp_all only [max_self]; rw[←h]
      apply Prod.Lex.right _ (by linarith)
    . simp_all only [sup_of_le_right]; apply Prod.Lex.left _ _ (Nat.lt_of_le_of_ne g h)
  . simp only [g, ↓reduceIte]
    exact Prod.Lex.right _ (by linarith)

theorem star_metric_Alt_l : star_metric l < star_metric (l ⋓ r) := by
  simp [star_metric, ge_iff_le,max, Nat.instMax, maxOfLe]
  unfold max Nat.instMax_mathlib inferInstance Nat.instMax maxOfLe
  by_cases g : (star_metric l).fst ≤ (star_metric r).fst
  . simp_rw [g]; simp only [ite_true];
    by_cases g1 : ((star_metric l).fst = (star_metric r).fst)
    . rewrite[←g1]; exact Prod.Lex.right _ (by linarith);
    . simp only at *; exact Prod.Lex.left _ _ (Nat.lt_of_le_of_ne g g1);
  . simp_rw [g]; simp only [ite_false];
    simp only [not_le] at g;
    exact Prod.Lex.right _ (by linarith)

theorem star_metric_Alt_r : star_metric r < star_metric (l ⋓ r) := by
  simp [star_metric, ge_iff_le,max, Nat.instMax, maxOfLe]
  unfold max Nat.instMax_mathlib inferInstance Nat.instMax maxOfLe
  simp only
  by_cases g : (star_metric l).fst ≤ (star_metric r).fst
  . simp_all only [ite_true]; exact Prod.Lex.right _ (by linarith);
  . simp_rw[g]; simp_all only [not_le]
    exact Prod.Lex.left _ _ (by exact g)

theorem star_metric_Inter_l : star_metric l < star_metric (l ⋒ r) := by
  simp [star_metric, ge_iff_le,max, Nat.instMax, maxOfLe]
  unfold max Nat.instMax_mathlib inferInstance Nat.instMax maxOfLe
  simp only
  split
  . have g : (star_metric l).fst ≤ (star_metric r).fst := by assumption;
    by_cases h : ((star_metric l).fst = (star_metric r).fst)
    . rewrite[←h]; exact Prod.Lex.right _ (by linarith);
    . simp only at h; exact Prod.Lex.left _ _ (Nat.lt_of_le_of_ne g h);
  . have g : ¬(star_metric l).fst ≤ (star_metric r).fst := by assumption;
    simp only [not_le] at g;
    exact Prod.Lex.right _ (by linarith)

theorem star_metric_Inter_r : star_metric r < star_metric (l ⋒ r) := by
  simp [star_metric, ge_iff_le,max, Nat.instMax, maxOfLe]
  unfold max Nat.instMax_mathlib inferInstance Nat.instMax maxOfLe
  simp only
  split
  . have g : (star_metric l).fst ≤ (star_metric r).fst := by assumption;
    simp only at g;
    exact Prod.Lex.right _ (by linarith);
  . have g : ¬(star_metric l).fst ≤ (star_metric r).fst := by assumption;
    simp only [not_le] at g;
    exact Prod.Lex.left _ _ (by exact g)

@[simp]
theorem star_metric_Negation : star_metric r < star_metric (~ r) := by
  simp only [star_metric]; apply Prod.Lex.right _ (by simp)

theorem star_metric_Lookahead : star_metric r < star_metric (?= r) := by
  simp only [star_metric]; apply Prod.Lex.right; simp

theorem star_metric_Lookbehind : star_metric r < star_metric (?<= r) := by
  simp only [star_metric];
  apply Prod.Lex.right; simp

theorem star_metric_NegLookahead : star_metric r < star_metric (?! r) := by
  simp only [star_metric]; apply Prod.Lex.right; simp

theorem star_metric_NegLookbehind : star_metric r < star_metric (?<! r) := by
  simp only [star_metric];
  apply Prod.Lex.right; simp

theorem star_metric_Lookahead_reverse : star_metric (r ʳ) < star_metric (?= r) := by
  rw [star_metric_reverse_RE];
  rw [reverse_RE_involution];
  apply star_metric_Lookahead

theorem star_metric_Lookbehind_reverse : star_metric (r ʳ) < star_metric (?<= r) := by
  rw [star_metric_reverse_RE];
  rw [reverse_RE_involution];
  apply star_metric_Lookbehind

theorem star_metric_NegLookahead_reverse : star_metric (r ʳ) < star_metric (?! r) := by
  rw [star_metric_reverse_RE];
  rw [reverse_RE_involution];
  apply star_metric_Lookahead

theorem star_metric_NegLookbehind_reverse : star_metric (r ʳ) < star_metric (?<! r) := by
  rw [star_metric_reverse_RE];
  rw [reverse_RE_involution];
  apply star_metric_Lookbehind

@[simp]
theorem star_metric_repeat_first : (star_metric (r ⁽ n ⁾)).fst < 1 + (star_metric r).fst :=
  match n with
  | 0          => by simp[star_metric]
  | Nat.succ n => by
    simp only [repeat_cat, star_metric, sup_lt_iff, lt_add_iff_pos_left, Nat.lt_one_iff, pos_of_gt,
      true_and]
    exact (@star_metric_repeat_first _ r n)

@[simp]
theorem star_metric_repeat : (star_metric (r ⁽ n ⁾)) < (star_metric (r *)) := by
  simp only [star_metric]; apply Prod.Lex.left; apply star_metric_repeat_first

@[simp]
theorem star_metric_Star : (star_metric r) < (star_metric (r *)) := by
  simp only [star_metric]; apply Prod.Lex.left; simp

@[simp]
theorem star_metric_cat_Star : star_metric (r ⬝ (r ⁽ m ⁾)) < star_metric (r *) := by
  simp only [star_metric]; apply Prod.Lex.left; simp
