import Regex.Finiteness.Pieces
import Regex.Finiteness.Similarity

open RE List Sim

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

/-!
# Finiteness of the state space

Contains the proof of finiteness for symbolic derivatives.

The main approach here is to relate the `step` function to the `pieces` function, which
is the overapproximation of the state space.

-/

theorem step_to_pieces {f e : RE α} (e_in : e ∈ step f) :
  ∃ xs, toSum xs ≅ e ∧ xs ∈ neSubsets (pieces f) := by
  induction f generalizing e with
  | ε | Lookahead _ _ | Lookbehind _ _ | NegLookahead _ _ | NegLookbehind _ _ =>
    obtain rfl : e = Pred ⊥ := by simpa using e_in
    exact ⟨[_], refl, neSubsets_singleton (by simp [pieces])⟩
  | Pred φ =>
    simp only [step, derivative, leaves, cons_append, nil_append, mem_cons, not_mem_nil,
      or_false] at e_in
    rcases e_in with rfl | rfl <;> exact ⟨[_], refl, neSubsets_singleton (by simp [pieces])⟩
  | Alternation l r ihl ihr =>
    simp only [step, derivative, leaves_binary, mem_productWith] at e_in
    obtain ⟨a, ha, b, hb, rfl⟩ := e_in
    obtain ⟨xs, hx, xs_in⟩ := ihl ha
    obtain ⟨ys, hy, ys_in⟩ := ihr hb
    exact ⟨xs ++ ys,
      trans (toSum_append (ne_nil_of_mem_neSubsets xs_in) (ne_nil_of_mem_neSubsets ys_in)) (alt_cong hx hy),
      neSubsets_append xs_in ys_in⟩
  | Intersection l r ihl ihr =>
    simp only [step, derivative, leaves_binary, mem_productWith] at e_in
    obtain ⟨a, ha, b, hb, rfl⟩ := e_in
    obtain ⟨xs, hx, xs_in⟩ := ihl ha
    obtain ⟨ys, hy, ys_in⟩ := ihr hb
    exact ⟨[_], inter_cong hx hy, neSubsets_singleton <| mem_productWith.mpr
      ⟨_, mem_toSumSubsets xs_in, _, mem_toSumSubsets ys_in, rfl⟩⟩
  | Concatenation l r ihl ihr =>
    simp only [step, derivative, leaves, leaves_binary, leaves_unary, mem_append,
      mem_productWith, mem_map] at e_in
    rcases e_in with ⟨_, ⟨a, ha, rfl⟩, b, hb, rfl⟩ | ⟨a, ha, rfl⟩
    · obtain ⟨xs, hx, xs_in⟩ := ihl ha
      obtain ⟨ys, hy, ys_in⟩ := ihr hb
      exact ⟨(toSum xs ⬝ r) :: ys,
        trans (toSum_append (cons_ne_nil _ []) (ne_nil_of_mem_neSubsets ys_in)) (alt_cong (cat_cong hx refl) hy),
        neSubsets_append
          (neSubsets_singleton (mem_map_toSumSubsets xs_in)) ys_in⟩
    · obtain ⟨xs, hx, xs_in⟩ := ihl ha
      exact ⟨[_], cat_cong hx refl, neSubsets_singleton <|
        mem_append_left _ (mem_map_toSumSubsets xs_in)⟩
  | Star r ih =>
    simp only [step, derivative, leaves_unary, mem_map] at e_in
    obtain ⟨a, ha, rfl⟩ := e_in
    obtain ⟨xs, hx, xs_in⟩ := ih ha
    exact ⟨[_], cat_cong hx refl, neSubsets_singleton <|
      mem_cons_of_mem _ (mem_map_toSumSubsets xs_in)⟩
  | Negation r ih =>
    simp only [step, derivative, leaves_unary, mem_map] at e_in
    obtain ⟨a, ha, rfl⟩ := e_in
    obtain ⟨xs, hx, xs_in⟩ := ih ha
    exact ⟨[_], neg_cong hx, neSubsets_singleton (mem_map_toSumSubsets xs_in)⟩

theorem step_to_toSumSubsets {r : RE α} :
  step r ⊆[ (· ≅ ·) ] ⊕(pieces r) := fun _ in_step =>
  have ⟨xs, hx, xs_in⟩ := step_to_pieces in_step
  ⟨toSum xs, symm hx, mem_toSumSubsets xs_in⟩

theorem steps_to_toSumSubsets {r : RE α} :
  steps r n ⊆[ (· ≅ ·) ] ⊕(pieces r) := fun e1 h =>
  match n with
  | 0 => by
    simp only [steps, mem_cons, not_mem_nil, or_false] at h
    subst h
    exact toSumSubsets_pieces_refl -- reflexivity
  | Nat.succ n => by
    simp only [steps, mem_flatten, mem_map, step, exists_exists_and_eq_and] at h
    let ⟨e2,e2_steps_n,e1_step_e2⟩ := h
    have ⟨q1,q1_eqv,ih⟩  := steps_to_toSumSubsets e2 e2_steps_n -- inductive hypothesis
    have ⟨xs,xs_eqv,hxs⟩ := step_to_toSumSubsets _ e1_step_e2   -- single-step closure
    have e2_in : e2 ∈[ (· ≅ ·) ] ⊕(pieces r) := ⟨q1,q1_eqv,ih⟩
    have e_in  : e1 ∈[ (· ≅ ·) ] ⊕(pieces e2) := ⟨xs,xs_eqv,hxs⟩
    exact toSumSubsets_pieces_trans e_in e2_in -- transitivity

theorem finiteness {r : RE α} :
  ∃ (xs : List (RE α)), ∀ {n : ℕ}, steps r n ⊆[ (· ≅ ·) ] xs :=
  ⟨⊕(pieces r),steps_to_toSumSubsets⟩

/-- Alternative way to state finiteness with the closure operator. -/
theorem finiteness_piecesS {r : RE α}:
  steps r n ⊆[(· ≅ ·)] piecesS [r] :=
  match n with
  | 0 => piecesS_extensive
  | n + 1 => fun re re_in => by
    simp only [steps, mem_flatten, mem_map, exists_exists_and_eq_and] at re_in
    let ⟨e,_,e_step⟩ := re_in
    have ⟨f,f_equiv,_⟩ : re ∈[(· ≅ ·)] ⊕(pieces e) :=
      have ⟨xs,h1,h2⟩ := step_to_pieces (f:=e) e_step
      ⟨toSum xs,symm h1,mem_toSumSubsets h2⟩
    have ⟨_,g_equiv,g_piece⟩ : re ∈[(· ≅ ·)] piecesS (steps r n) :=
      ⟨f,f_equiv,
       by simp only [piecesS, mem_flatten, mem_map, exists_exists_and_eq_and]
          exists e⟩
    have step1 := piecesS_monotone (finiteness_piecesS (r:=r) (n:=n))
    have step2 := piecesS_idem (xs:= [r])
    have ⟨h,h_equiv,h_piece⟩ := subset_up_to_trans_sim step1 step2 _ g_piece
    exact ⟨h,Sim.trans g_equiv h_equiv,h_piece⟩
