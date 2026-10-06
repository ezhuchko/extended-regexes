import Regex.Finiteness.Permute
import Regex.Finiteness.Similarity

open RE List Sim

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

/-!
# Pieces

This file contains the definitions of `pieces` which is the key component of the overapproximation for the set of
all derivatives.

-/

/-- This is an overapproximation of the set of pieces of all possible derivatives. -/
def pieces : RE α → List (RE α)
  | ε         => [ε, Pred ⊥]
  | ?= r      => [?= r, ε, Pred ⊥]
  | ?! r      => [?! r, ε, Pred ⊥]
  | ?<= r     => [?<= r, ε, Pred ⊥]
  | ?<! r     => [?<! r, ε, Pred ⊥]
  | Pred φ    => [Pred φ, ε, Pred ⊥]
  | l ⋓ r     => pieces l ++ pieces r
  | l ⋒ r     => productWith (· ⋒ ·) ⊕(pieces l) ⊕(pieces r)
  | l ⬝ r     => map (· ⬝ r) ⊕(pieces l) ++ pieces r
  | .Star r   => r* :: map (· ⬝ r*) ⊕(pieces r)
  | ~ r       => map (~ ·) ⊕(pieces r)

theorem topmost_not_union {r x y : RE α} : ¬ ((x ⋓ y) ∈ pieces r) := fun h =>
  match r with
  | ε | ?=_ | ?!_ | ?<=_ | ?<!_ => by
    simp only [pieces, mem_cons, reduceCtorEq, not_mem_nil, or_self] at h
  | Pred φ    => by simp only [pieces, mem_cons, reduceCtorEq, not_mem_nil, or_self] at h
  | l ⋓ r     =>
    match mem_append.mp h with
    | Or.inl h1 => topmost_not_union h1
    | Or.inr h1 => topmost_not_union h1
  | l ⋒ r     => by
    simp only [pieces, productWith, product] at h
    simp only [mem_map, mem_flatMap, exists_exists_and_exists_and_eq_and] at h
    let ⟨a,b,c,d,e⟩ := h
    simp only [Function.uncurry_apply_pair, reduceCtorEq] at e
  | l ⬝ r     => by
    simp only [pieces, mem_append, mem_map, reduceCtorEq, and_false, exists_false, false_or] at h
    exact topmost_not_union h
  | .Star r   => by simp only [pieces, mem_cons, reduceCtorEq, mem_map, and_false, exists_false, or_self] at h
  | ~ r       => by simp only [pieces, mem_map, reduceCtorEq, and_false, exists_false] at h

theorem pieces_refl {r : RE α} :
  ∃ xs, xs ∈ neSubsets (pieces r) ∧ toSum xs ≅ r :=
  match r with
  | ε         => ⟨[ε],neSubsets_singleton mem_cons_self,refl⟩
  | ?= r      => ⟨[?= r],neSubsets_singleton mem_cons_self,refl⟩
  | ?! r      => ⟨[?! r],neSubsets_singleton mem_cons_self,refl⟩
  | ?<= r     => ⟨[?<= r],neSubsets_singleton mem_cons_self,refl⟩
  | ?<! r     => ⟨[?<! r],neSubsets_singleton mem_cons_self,refl⟩
  | Pred φ    => ⟨[Pred φ],neSubsets_singleton mem_cons_self,refl⟩
  | l ⋓ r     =>
    have ⟨i1,i2,i3⟩ := pieces_refl (r:=l)
    have ⟨j1,j2,j3⟩ := pieces_refl (r:=r)
    ⟨i1 ++ j1, neSubsets_append i2 j2,
     trans (toSum_append (ne_nil_of_mem_neSubsets i2) (ne_nil_of_mem_neSubsets j2))
       (alt_cong i3 j3)⟩
  | l ⋒ r     =>
    have ⟨i1,i2,i3⟩ := pieces_refl (r:=l)
    have ⟨j1,j2,j3⟩ := pieces_refl (r:=r)
    ⟨[toSum i1 ⋒ toSum j1],
     neSubsets_singleton (mem_productWith.mpr ⟨toSum i1, mem_toSumSubsets i2,
                             toSum j1, mem_toSumSubsets j2, rfl⟩),
     inter_cong i3 j3⟩
  | .Star r   => ⟨[r*],neSubsets_singleton mem_cons_self,refl⟩
  | ~ r       =>
    have ⟨i1,i2,i3⟩ := pieces_refl (r:=r)
    ⟨[~(toSum i1)],
     neSubsets_singleton (mem_map_toSumSubsets i2),
     neg_cong i3⟩
  | l ⬝ r     =>
    have ⟨i1,i2,i3⟩ := pieces_refl (r:=l)
    ⟨[toSum i1 ⬝ r],
     neSubsets_singleton (mem_append_left _
       (mem_map_toSumSubsets i2)),
     cat_cong i3 refl⟩

/-! ### Congruence of `pieces` under `≅` -/
section Congruence
variable {l₁ l₂ r₁ r₂ : RE α}

theorem pieces_assoc {R₁ R₂ R₃ : RE α} :
  pieces ((R₁ ⋓ R₂) ⋓ R₃) = pieces (R₁ ⋓ (R₂ ⋓ R₃)) := by
  simp only [pieces, append_assoc]

theorem pieces_idem {R : RE α} : pieces (R ⋓ R) =[ (· ≅ ·) ] pieces R :=
  ⟨subset_to_subset_up_to_sim
     (fun _ hx => by simpa only [pieces, mem_append, or_self] using hx),
   subset_to_subset_up_to_sim (by intro x hx; simp only [pieces, mem_append]; exact Or.inl hx)⟩

theorem pieces_dedup {R₁ R₂ : RE α} :
  pieces (R₁ ⋓ R₂ ⋓ R₁) =[ (· ≅ ·) ] pieces (R₁ ⋓ R₂) :=
  ⟨subset_to_subset_up_to_sim (by intro x hx; simp only [pieces, mem_append] at hx ⊢; tauto),
   subset_to_subset_up_to_sim (by intro x hx; simp only [pieces, mem_append] at hx ⊢; tauto)⟩

theorem pieces_alt_mono
  (hl : pieces l₁ ⊆[ (· ≅ ·) ] pieces l₂) (hr : pieces r₁ ⊆[ (· ≅ ·) ] pieces r₂) :
  pieces (l₁ ⋓ r₁) ⊆[ (· ≅ ·) ] pieces (l₂ ⋓ r₂) := by
  intro e he
  rcases mem_append.mp he with h | h
  · obtain ⟨i1,i2,i3⟩ := hl e h; exact ⟨i1,i2,mem_append_left _ i3⟩
  · obtain ⟨i1,i2,i3⟩ := hr e h; exact ⟨i1,i2,mem_append_right _ i3⟩

theorem pieces_inter_mono
  (hl : pieces l₁ ⊆[ (· ≅ ·) ] pieces l₂) (hr : pieces r₁ ⊆[ (· ≅ ·) ] pieces r₂) :
  pieces (l₁ ⋒ r₁) ⊆[ (· ≅ ·) ] pieces (l₂ ⋒ r₂) := by
  intro e he
  obtain ⟨a,ha,b,hb,rfl⟩ := mem_productWith.mp he
  obtain ⟨i1,i2,i3⟩ := toSumSubsets_monotone hl _ ha
  obtain ⟨j1,j2,j3⟩ := toSumSubsets_monotone hr _ hb
  exact ⟨i1 ⋒ j1, inter_cong i2 j2, mem_productWith.mpr ⟨i1,i3,j1,j3,rfl⟩⟩

theorem pieces_cat_mono
  (hl : pieces l₁ ⊆[ (· ≅ ·) ] pieces l₂) (hr : pieces r₁ ⊆[ (· ≅ ·) ] pieces r₂)
  (hsim : r₁ ≅ r₂) :
  pieces (l₁ ⬝ r₁) ⊆[ (· ≅ ·) ] pieces (l₂ ⬝ r₂) := by
  intro e he
  simp only [pieces, mem_append, mem_map] at he
  rcases he with ⟨xs,g1,rfl⟩ | g1
  · obtain ⟨i1,i2,i3⟩ := toSumSubsets_monotone hl _ g1
    exact ⟨i1 ⬝ r₂, cat_cong i2 hsim, mem_append_left _ (mem_map_of_mem i3)⟩
  · obtain ⟨i1,i2,i3⟩ := hr _ g1
    exact ⟨i1, i2, mem_append_right _ i3⟩

theorem pieces_star_mono
  (h : pieces r₁ ⊆[ (· ≅ ·) ] pieces r₂) (hsim : r₁ ≅ r₂) :
  pieces (r₁*) ⊆[ (· ≅ ·) ] pieces (r₂*) := by
  intro e he
  simp only [pieces, mem_cons, mem_map] at he
  rcases he with rfl | ⟨zs,hz1,rfl⟩
  · exact ⟨r₂*, star_cong hsim, mem_cons_self⟩
  · obtain ⟨i1,i2,i3⟩ := toSumSubsets_monotone h _ hz1
    exact ⟨i1 ⬝ r₂*, cat_cong i2 (star_cong hsim),
           mem_cons_of_mem _ (mem_map_of_mem i3)⟩

theorem pieces_neg_mono (h : pieces r₁ ⊆[ (· ≅ ·) ] pieces r₂) :
  pieces (~r₁) ⊆[ (· ≅ ·) ] pieces (~r₂) := by
  intro e he
  obtain ⟨zs,hz1,rfl⟩ := mem_map.mp he
  obtain ⟨i1,i2,i3⟩ := toSumSubsets_monotone h _ hz1
  exact ⟨~i1, neg_cong i2, mem_map_of_mem i3⟩

end Congruence

/-- `pieces` is a congruence for `≅`, up to `≅`. -/
theorem pieces_equiv {f f' : RE α} (eqv : f ≅ f') :
  pieces f =[ (· ≅ ·) ] pieces f' := by
  induction eqv with
  | refl                   => exact equality_up_to_refl_sim
  | symm _ ih              => exact equality_up_to_symm ih
  | trans _ _ ih1 ih2      => exact equality_up_to_trans_sim ih1 ih2
  | assoc                  => rw [pieces_assoc]; exact equality_up_to_refl_sim
  | idem                   => exact pieces_idem
  | dedup                  => exact pieces_dedup
  | alt_cong _ _ ih1 ih2   => exact ⟨pieces_alt_mono ih1.1 ih2.1, pieces_alt_mono ih1.2 ih2.2⟩
  | inter_cong _ _ ih1 ih2 => exact ⟨pieces_inter_mono ih1.1 ih2.1, pieces_inter_mono ih1.2 ih2.2⟩
  | cat_cong _ g ih1 ih2   =>
    exact ⟨pieces_cat_mono ih1.1 ih2.1 g, pieces_cat_mono ih1.2 ih2.2 (symm g)⟩
  | star_cong h ih         => exact ⟨pieces_star_mono ih.1 h, pieces_star_mono ih.2 (symm h)⟩
  | neg_cong _ ih          => exact ⟨pieces_neg_mono ih.1, pieces_neg_mono ih.2⟩

/-- A piece of a sum is a piece of one of the summands. -/
theorem pieces_toSum {e : RE α} {xs : List (RE α)} (ne : xs ≠ []) (h : e ∈ pieces (toSum xs)) :
  ∃ g ∈ xs, e ∈ pieces g :=
  match xs with
  | _::[] => exists_mem_cons_of [] h
  | e1::e2::es =>
    match mem_append.mp h with
    | Or.inl h1 => ⟨e1,mem_cons_self,h1⟩
    | Or.inr h1 =>
      have ⟨i1,i2,ih⟩ := pieces_toSum (cons_ne_nil e2 es) h1
      ⟨i1,mem_cons_of_mem e1 i2,ih⟩

theorem toSumSubsets_pieces_step {ps : List (RE α)} {a b : RE α}
  (ih : ∀ {x y : RE α}, y ∈ ps → x ∈ pieces y → x ∈[ (· ≅ ·) ] ps)
  (ha : a ∈ ⊕ps) (hb : b ∈ ⊕(pieces a)) :
  b ∈[ (· ≅ ·) ] ⊕ps := by
  obtain ⟨zs, ne_zs, rfl, zs_ps⟩ := toSumSubsets_to_neSubset ha
  obtain ⟨as, ne_as, rfl, as_sub⟩ := toSumSubsets_to_neSubset hb
  refine toSumSubsets_monotone (fun x hx => ?_) (toSum as)
           (mem_toSumSubsets (neSubsets_refl ne_as))
  obtain ⟨pi, pi_in, pi_piece⟩ := pieces_toSum ne_zs (as_sub hx)
  exact ih (zs_ps pi_in) pi_piece

/-- `pieces` is idempotent, up to `≅`. -/
theorem pieces_trans {e : RE α}
  (h1 : e ∈ pieces f)
  (h2 : f ∈ pieces g) :
  e ∈[ (· ≅ ·) ] pieces g := by
  match g with
  -- a piece of a piece of an atom is already a piece of it
  | ε | Pred _ | ?=_ | ?!_ | ?<=_ | ?<!_ =>
    refine ⟨e, refl, ?_⟩
    simp only [pieces, mem_cons, not_mem_nil, or_false] at h2 ⊢
    rcases h2 with rfl | rfl | rfl <;> simp_all [pieces]
    all_goals tauto
  | g₁ ⋓ g₂ =>
    simp only [pieces, mem_append] at h2
    rcases h2 with g | g <;> obtain ⟨i1, i2, i3⟩ := pieces_trans h1 g
    · exact ⟨i1, i2, mem_append_left _ i3⟩
    · exact ⟨i1, i2, mem_append_right _ i3⟩
  | l ⋒ r =>
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_productWith.mp h2
    obtain ⟨c, hc, d, hd, rfl⟩ := mem_productWith.mp h1
    obtain ⟨c', c'_sim, c'_mem⟩ :=
      toSumSubsets_pieces_step (fun hy hx => pieces_trans hx hy) ha hc
    obtain ⟨d', d'_sim, d'_mem⟩ :=
      toSumSubsets_pieces_step (fun hy hx => pieces_trans hx hy) hb hd
    exact ⟨c' ⋒ d', inter_cong c'_sim d'_sim,
           mem_productWith.mpr ⟨c', c'_mem, d', d'_mem, rfl⟩⟩
  | l ⬝ r =>
    simp only [pieces, mem_append, mem_map] at h2
    rcases h2 with ⟨a, ha, rfl⟩ | g
    · simp only [pieces, mem_append, mem_map] at h1
      rcases h1 with ⟨b, hb, rfl⟩ | g
      · obtain ⟨b', b'_sim, b'_mem⟩ :=
          toSumSubsets_pieces_step (fun hy hx => pieces_trans hx hy) ha hb
        exact ⟨b' ⬝ r, cat_cong b'_sim refl,
               mem_append_left _ (mem_map_of_mem b'_mem)⟩
      · exact ⟨e, refl, mem_append_right _ g⟩
    · obtain ⟨i1, i2, i3⟩ := pieces_trans h1 g
      exact ⟨i1, i2, mem_append_right _ i3⟩
  | ~ g' =>
    simp only [pieces, mem_map] at h2
    obtain ⟨a, ha, rfl⟩ := h2
    simp only [pieces, mem_map] at h1
    obtain ⟨b, hb, rfl⟩ := h1
    obtain ⟨b', b'_sim, b'_mem⟩ :=
      toSumSubsets_pieces_step (fun hy hx => pieces_trans hx hy) ha hb
    exact ⟨~b', neg_cong b'_sim, mem_map_of_mem b'_mem⟩
  | .Star r =>
    simp only [pieces, mem_cons, mem_map] at h2
    rcases h2 with rfl | ⟨a, ha, rfl⟩
    · exact ⟨e, refl, h1⟩
    · simp only [pieces, mem_append, mem_map] at h1
      rcases h1 with ⟨b, hb, rfl⟩ | g
      · obtain ⟨b', b'_sim, b'_mem⟩ :=
          toSumSubsets_pieces_step (fun hy hx => pieces_trans hx hy) ha hb
        exact ⟨b' ⬝ r*, cat_cong b'_sim refl,
               mem_cons_of_mem _ (mem_map_of_mem b'_mem)⟩
      · exact ⟨e, refl, g⟩

theorem toSumSubsets_pieces_refl {r : RE α} : r ∈[ (· ≅ ·) ] ⊕(pieces r) :=
  have ⟨xs,xs_in,xs_eqv⟩ := pieces_refl (r:=r)
  ⟨toSum xs,symm xs_eqv, mem_toSumSubsets xs_in⟩

theorem toSumSubsets_pieces_trans {e : RE α}
  (h1 : e ∈[ (· ≅ ·) ] ⊕(pieces f))
  (h2 : f ∈[ (· ≅ ·) ] ⊕(pieces g)) :
        e ∈[ (· ≅ ·) ] ⊕(pieces g) := by
  obtain ⟨ff, e_ff, hff⟩ := h1
  obtain ⟨gg, f_gg, hgg⟩ := h2
  obtain ⟨as, ne_as, rfl, as_sub⟩ := toSumSubsets_to_neSubset hff
  obtain ⟨zs, ne_zs, rfl, zs_sub⟩ := toSumSubsets_to_neSubset hgg
  -- every summand of `e` is, up to `≅`, a piece of `g`: transport it along
  -- `f ≅ toSum zs` with `pieces_equiv`, split the sum with `pieces_toSum`, then
  -- collapse the nesting with `pieces_trans`.
  have sub : as ⊆[ (· ≅ ·) ] pieces g := fun x hx =>
    have ⟨i1, x_i1, i1_mem⟩ := (pieces_equiv f_gg).1 _ (as_sub hx)
    have ⟨gi, gi_mem, i1_piece⟩ := pieces_toSum ne_zs i1_mem
    have ⟨j1, i1_j1, j1_mem⟩ := pieces_trans i1_piece (zs_sub gi_mem)
    ⟨j1, trans x_i1 i1_j1, j1_mem⟩
  -- a sum over `pieces g` is `≅` a *nodup* such sum, which is in `⊕(pieces g)`
  obtain ⟨y, sum_y, y_mem⟩ := subset_sim_perm ne_as sub
  exact ⟨y, trans e_ff sum_y, y_mem⟩

/-- `pieces` as a closure operator. -/
@[simp]
def piecesS (xs : List (RE α)) : List (RE α) :=
  map ((⊕ ·) ∘ (pieces ·)) xs |> flatten

theorem piecesS_extensive {xs : List (RE α)} :
  xs ⊆[(· ≅ ·)] piecesS xs := fun x hx =>
  have ⟨x', x'_eq, x'_mem⟩ := toSumSubsets_pieces_refl (r := x)
  ⟨x',x'_eq,by simp only [piecesS, mem_flatten, mem_map, exists_exists_and_eq_and]; exists x⟩

theorem piecesS_monotone {xs ys : List (RE α)} (h : xs ⊆[(· ≅ ·)] ys) :
  piecesS xs ⊆[(· ≅ ·)] piecesS ys := fun px hpx => by
  simp only [subset_up_to] at h
  simp only [piecesS] at hpx
  have ⟨l, l_in, px_in⟩ := mem_flatten.mp hpx
  have ⟨x', x'_in, x'_pcs⟩ := mem_map.mp l_in
  subst x'_pcs
  have ⟨y', y'_eq, y'_in⟩ := h x' x'_in
  have pcs_x'_y' := (pieces_equiv y'_eq).1
  have ⟨py, py_eq, py_in⟩ := toSumSubsets_monotone pcs_x'_y' px px_in
  exact ⟨py,py_eq,by simp only [piecesS, mem_flatten, mem_map, exists_exists_and_eq_and]; exists y'⟩

theorem piecesS_idem (xs : List (RE α)) :
  piecesS (piecesS xs) ⊆[(· ≅ ·)] piecesS xs := fun px hpx => by
  have ⟨l, l_in, px_l⟩ := mem_flatten.mp hpx
  have ⟨m, m_in, pcs_m_l⟩ := mem_map.mp l_in
  have ⟨n, n_in, m_n⟩ := mem_flatten.mp m_in
  have ⟨x, x_in, pcs_x_n⟩ := mem_map.mp n_in
  subst pcs_m_l pcs_x_n
  have r1 : px ∈[(· ≅ ·)] ⊕(pieces m) := ⟨px, refl, px_l⟩
  have r2 : m ∈[(· ≅ ·)] ⊕(pieces x) := ⟨m, refl, m_n⟩
  have ⟨px', px'_eq, px'_in⟩ := toSumSubsets_pieces_trans r1 r2
  exact ⟨px', px'_eq, by simp only [piecesS, mem_flatten, mem_map, exists_exists_and_eq_and]; exists x⟩
