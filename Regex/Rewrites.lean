import Regex.EliminationNegLookarounds
import Regex.Reversal
import Regex.ModelsReasoning

/-!
# Rewrite rules

Contains the correctness proofs for the collection of different simplification rules.
-/

open RE List

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

theorem equiv_concat_distr_r {r q w : RE α} :
  (r ⬝ (q ⋓ w)) ↔ᵣ ((r ⬝ q) ⋓ (r ⬝ w)) :=
  λ {sp} =>
  ⟨ λ h => by
    simp_all only [models]
    let ⟨sp1,sp2,a1,a2,c⟩ := h
    match a2 with
    | Or.inl a3 => exact Or.inl ⟨sp1,sp2,a1,a3,c⟩
    | Or.inr a4 => exact Or.inr ⟨sp1,sp2,a1,a4,c⟩,
    λ h => by
    simp_all only [models]
    match h with
    | Or.inl ⟨sp1,sp2,a1,a2,c⟩ => exact ⟨sp1,sp2,a1,Or.inl a2,c⟩
    | Or.inr ⟨sp1,sp2,a1,a2,c⟩ => exact ⟨sp1,sp2,a1,Or.inr a2,c⟩⟩

theorem equiv_concat_distr_l {r q w : RE α} :
  ((q ⋓ w) ⬝ r) ↔ᵣ ((q ⬝ r) ⋓ (w ⬝ r)) :=
  λ {sp} =>
  ⟨ λ h => by
    simp_all only [models]
    let ⟨sp1,sp2,a1,a2,c⟩ := h
    match a1 with
    | Or.inl a3 => exact Or.inl ⟨sp1,sp2,a3,a2,c⟩
    | Or.inr a4 => exact Or.inr ⟨sp1,sp2,a4,a2,c⟩,
    λ h => by
    simp_all only [models]
    match h with
    | Or.inl ⟨sp1,sp2,a1,a2,c⟩ => exact ⟨sp1,sp2,Or.inl a1,a2,c⟩
    | Or.inr ⟨sp1,sp2,a1,a2,c⟩ => exact ⟨sp1,sp2,Or.inr a1,a2,c⟩⟩

theorem equiv_inter_comm {r q : RE α} : r ⋒ q ↔ᵣ q ⋒ r :=
  λ {sp} => by simp_all only [models]; exact And.comm

@[simp]
def startAnchor : RE α := (?<!(Pred (⊤ : α)))

-- context dependent
theorem claim1 {X : RE α} :
  sp ⊫ (?= X) ↔
  sp.match.length = 0 ∧ ((sp.1,sp.2.2,sp.2.1) ⊫ X ⬝ pad) := by
  simp only [models, Span.match, length_eq_zero_iff, Span.beg, Span.left, Span.right,
    Prod.mk.injEq, and_congr_right_iff]
  intro h; let ⟨a,b,c⟩ := sp; subst h
  apply Iff.intro
  . intro ⟨(a,b,c),g1,g2,g3⟩
    simp_all only [nil_append, append_nil]; subst g2 g3
    exact ⟨b,c,g1,by unfold pad; exact models_TopStar,rfl⟩
  . intro ⟨u1,u2,h1,h2,h3⟩
    simp_all only [append_nil, nil_append]; subst h3; exists (a,u1,u2)

theorem nlb_elim {X : RE α} :
  (?<! X) ↔ᵣ (?<=(startAnchor ⬝ ~(pad ⬝ X))) :=
  λ {sp} => by
  erw[models_reversal, nla_elim]
  conv => rhs; rw[models_reversal]; simp only [List.reverse]
  exact Eq.to_iff rfl

theorem append_decompose {b g : List σ}
  (h : b ++ g = e ++ f) :
  ∃ x,   b = e ++ x ∧ f = x ++ g
       ∨ e = b ++ x ∧ g = x ++ f :=
  match b with
  | [] => exists_or.mpr $ Or.inr ⟨e,rfl,h⟩
  | b::bs =>
    match e with
    | [] => exists_or.mpr $ Or.inl ⟨b::bs,rfl,Eq.symm h⟩
    | e::es =>
      have eq : b = e := head_eq_of_cons_eq h
      have ⟨xs,ih⟩ := append_decompose (tail_eq_of_cons_eq h)
      match ih with
      | Or.inl ⟨eq1,eq2⟩ =>
        exists_or.mpr $ Or.inl ⟨xs,by subst eq; exact (cons_inj_right b).mpr eq1,eq2⟩
      | Or.inr ⟨eq1,eq2⟩ =>
        exists_or.mpr $ Or.inr ⟨xs,by subst eq; exact (cons_inj_right b).mpr eq1,eq2⟩

theorem RE.la_join {X Y : RE α} :
  ((?=X) ⬝ (?=Y)) ↔ᵣ (?=((X ⬝ pad) ⋒ (Y ⬝ pad))) :=
  λ {sp} =>
  let ⟨s,u,v⟩ := sp
  ⟨ λ h => by
    simp only [models, Span.left, Span.right, Span.match, length_eq_zero_iff, Span.beg,
      Prod.mk.injEq] at h
    let ⟨u1,u2,⟨⟨heq,h1⟩,⟨heq1,h2⟩,h3⟩⟩ := h
    subst heq heq1 h3; simp only [nil_append, reverse_nil] at h1 h2
    let ⟨(a,b,c),g2,g3,g4⟩ := h1
    let ⟨(d,e,f),g6,g7,g8⟩ := h2
    subst g3 g8 g7; simp_all only
    have ⟨x,h1⟩ := append_decompose g4
    match h1 with
    | Or.inl ⟨h2,h3⟩ =>
      subst h2 h3; unfold models
      exact ⟨by simp only [Span.match, append_nil, length_nil],
             ⟨(d,e++x,c),by unfold models
                            exact ⟨by unfold models; exact ⟨e++x,[],g2,by simp; unfold pad; exact models_TopStar⟩,
                                   by unfold models; exact ⟨e,x,g6,by simp; unfold pad; exact models_TopStar⟩⟩,by simp⟩⟩
    | Or.inr ⟨h2,h3⟩ =>
      subst h2 h3; unfold models
      exact ⟨by simp only [Span.match, append_nil, length_nil],
             ⟨(d,b++x,f),by unfold models;
                            exact ⟨by unfold models; exact ⟨b,x,g2,by unfold pad; exact ⟨models_TopStar, by simp⟩⟩,
                                   by unfold models; exact ⟨b++x,[],g6,by simp; unfold pad; apply models_TopStar⟩⟩,by simp⟩⟩,
    λ h => by
    simp only [models, Span.match, length_eq_zero_iff, Span.left, Span.right, Span.beg, Prod.mk.injEq] at h
    let ⟨h1,h2⟩ := h; subst h1
    let ⟨(d,e,f),⟨⟨⟨as,bs,g2,g3,gg3⟩,g4,⟨cs,ds,g5⟩⟩,gg,gg1⟩⟩ := h2
    simp at gg gg1 g3 gg3
    subst gg gg1
    simp only [models, Span.left, Span.right, Span.match, length_eq_zero_iff, Span.beg, Prod.mk.injEq]
    exists []; simp only [nil_append, true_and, reverse_nil, exists_eq_right_right]
    exact ⟨⟨(d,as,bs++f),g2,by simp[←append_assoc, gg3]⟩,
           ⟨(d,g4,cs++f),ds,by simp only [true_and,←append_assoc,g5]⟩⟩⟩

theorem lookahead_inter_pad {X Y : RE α} :
  ((?= X) ⋒ (?= Y)) ↔ᵣ (?= (((X ⬝ pad) ⋒ (Y ⬝ pad)))) :=
  λ {sp} =>
  let ⟨s,u,v⟩ := sp
  ⟨λ h => by
    unfold models at h
    let ⟨h1,h2⟩ := h; rw[claim1] at h1; let ⟨h3,h4⟩ := h1
    unfold models; simp only at h2 h4
    simp only [Span.match, length_eq_zero_iff] at h3; subst h3
    unfold models at h2; simp only at h2
    let ⟨k1,(a,b,c),k3,k4⟩ := h2
    simp only [Span.beg, Span.left, Span.match, Span.right, nil_append, Prod.mk.injEq] at k4
    let ⟨j1,j2⟩ := k4; subst j1 j2
    simp_all only [models, Span.match, length_nil, Span.beg, Span.left, Span.right,
      nil_append, Prod.mk.injEq, true_and, and_self, append_nil]
    let ⟨a1,a2,a3,a4⟩ := h4
    exact ⟨(a,b++c,[]),
           ⟨⟨a1,a2,by simp only [append_nil]; exact a3,a4⟩,
            ⟨b,c,by simp only [append_nil]; exact k3,by unfold pad; exact models_TopStar,rfl⟩⟩,
           by simp only [append_nil, and_self]⟩,
  λ h => by
    unfold models at h
    let ⟨h1,⟨(sp1,sp2,sp3),h2,h3⟩⟩ := h
    simp at h3; let ⟨h4,h5⟩ := h3; subst h4
    simp_all only [models, Span.left, Span.right, Span.match, true_and,
      length_eq_zero_iff, Span.beg, Prod.mk.injEq, length_nil, nil_append]
    let ⟨⟨o1,o2,o3,o4,o5⟩,⟨l1,l2,l3,l4,l5⟩⟩ := h2
    exact ⟨⟨(sp1,o1,o2++sp3),o3,rfl,
            by simp only [←append_assoc]; subst o5 v; rfl⟩,
           ⟨(sp1,l1,l2++sp3),l3,rfl,
            by simp only [←append_assoc]; subst l5 h3; rfl⟩⟩⟩

theorem concat_lookaheads_inter {X Y : RE α} :
  ((?= X) ⬝ (?= Y)) ↔ᵣ ((?= X) ⋒ (?= Y)) := λ {_} =>
  Iff.trans la_join (Iff.symm lookahead_inter_pad)

theorem RE.lb_join {X Y : RE α} :
  ((?<=X) ⬝ (?<=Y)) ↔ᵣ (?<=((pad ⬝ X) ⋒ (pad ⬝ Y))) :=
  λ {sp} => by
  apply Iff.trans models_reversal
  apply Iff.trans concat_lookaheads_inter
  apply Iff.trans equiv_inter_comm
  apply Iff.trans (Iff.symm concat_lookaheads_inter)
  apply Iff.trans la_join
  apply Iff.trans models_reversal
  simp only [reverse,reverse_RE_involution,reverse_span_involution]
  exact equiv_refl

theorem equiv_concat_congr {r : RE α} (h : r ↔ᵣ t) : (r ⬝ q) ↔ᵣ (t ⬝ q) :=
  λ {sp} =>
  ⟨λ h1 => by
    unfold models at h1; let ⟨sp1,sp2,a1,a2,c⟩ := h1
    unfold models; exact ⟨sp1,sp2,h.mp a1,a2,c⟩,
   λ h1 => by
    unfold models at h1; let ⟨sp1,sp2,a1,a2,c⟩ := h1
    unfold models; exact ⟨sp1,sp2,h.mpr a1,a2,c⟩⟩

theorem equiv_concat_congr2 {r : RE α} (h : r ↔ᵣ t) : (q ⬝ r) ↔ᵣ (q ⬝ t) :=
  λ {sp} =>
  ⟨λ h1 => by
    unfold models at h1; let ⟨sp1,sp2,a1,a2,c⟩ := h1
    unfold models; exact ⟨sp1,sp2,a1,h.mp a2,c⟩,
   λ h1 => by
    unfold models at h1; let ⟨sp1,sp2,a1,a2,c⟩ := h1
    unfold models; exact ⟨sp1,sp2,a1,h.mpr a2,c⟩⟩

theorem lookbehind_concat_distr_inter {X Y Z : RE α} :
  (?<= Z) ⬝ (X ⋒ Y) ↔ᵣ (?<= Z) ⬝ X ⋒ (?<= Z) ⬝ Y :=
  λ {sp} =>
  let ⟨s,u,v⟩ := sp
  ⟨ λ h => by
    unfold models at h; let ⟨u1,u2,h1,h2,h3⟩ := h; unfold models at h2
    simp only [Span.match] at h3
    simp only [Span.left, Span.right] at h1 h2
    unfold models; unfold models
    exact ⟨⟨u1,u2,h1,h2.1,h3⟩,⟨u1,u2,h1,h2.2,h3⟩⟩,
    by
    unfold models; intro ⟨h1,h2⟩; unfold models at h1 h2
    let ⟨u1,u2,h3,h4,h5⟩ := h1; let ⟨u3,u4,h6,h7,h8⟩ := h2
    have ⟨eq1,eq2⟩ : u1 = u3 ∧ u2 = u4 := by
      subst h5; simp only [Span.left, Span.right, models, Span.match, length_eq_zero_iff,
        Span.reverse, Span.beg, Prod.mk.injEq] at h3 h6
      let ⟨p1,p2⟩ := h3; subst p1; simp only [Span.match, nil_append] at h8
      let ⟨p3,p4⟩ := h6; subst p3; simp only [nil_append] at h8; subst h8; simp only [and_self]
    subst eq1 eq2; exact ⟨u1,u2,h3,by unfold models; exact ⟨h4,h7⟩,h5⟩⟩

theorem concat_lookbehinds_inter {X Y : RE α} :
  ((?<= X) ⬝ (?<= Y)) ↔ᵣ ((?<= X) ⋒ (?<= Y)) :=
  λ {sp} => by
  apply Iff.trans models_reversal
  apply Iff.trans concat_lookaheads_inter
  apply Iff.trans models_reversal
  simp only [RE.reverse, reverse_RE_involution, reverse_span_involution]
  unfold models
  exact And.comm

theorem inter_congr {X Y Z Z' : RE α} :
  X ↔ᵣ Z → Y ↔ᵣ Z' → X ⋒ Y ↔ᵣ Z ⋒ Z' :=
  λ h1 h2 {sp} => by unfold models; exact and_congr h1 h2

theorem helper_inter_cat {X Y' : RE α}:
  (?<=X ⋒ ?<=X') ⬝ Y' ↔ᵣ (?<=X ⬝ ?<=X') ⬝ Y' :=
  λ {_} => Iff.symm (equiv_concat_congr (concat_lookbehinds_inter))

theorem and_elim1_helper {X Y : RE α} :
  sp ⊫ (?<=X ⬝ ?<=X') ⬝ Y → (sp ⊫ ?<=X ⬝ Y) := fun h => by
  let ⟨s,u,v⟩ := sp
  unfold models at h; let ⟨a1,a2,a3,a4,a5⟩ := h
  unfold models at a3; let ⟨b1,b2,b3,b4,b5⟩ := a3
  unfold models; simp_all only [Span.left, Span.right]
  simp only [Span.match] at b5; subst b5
  simp only [reverse_append, append_assoc, Span.match] at a4 a5; subst a5
  simp only [models, Span.match, length_eq_zero_iff, Span.reverse, Span.beg,
    Span.left, Span.right, Prod.mk.injEq] at b4; let ⟨c1,c2,c4⟩ := b4; subst c1
  exact ⟨b1,a2,b3,a4,rfl⟩

-- context dependent
theorem claim2 {X : RE α} :
  sp ⊫ (?<= X) ↔
  sp.match.length = 0 ∧ ((sp.2.1.reverse,sp.1.reverse,sp.2.2) ⊫ pad ⬝ X) := by
  simp only [models, Span.match, length_eq_zero_iff, Span.reverse, Span.beg, Span.left, Span.right,
    Prod.mk.injEq, and_congr_right_iff]
  intro h; let ⟨d,e,f⟩ := sp; subst h
  apply Iff.intro
  . intro ⟨(a,b,c),g1,g2,g3⟩
    simp_all only [reverse_nil, nil_append, append_nil]; subst g2 g3
    exact ⟨c.reverse,b.reverse,
           by simp [reverse_reverse, reverse_append, and_true]
              exact ⟨by unfold pad; exact models_TopStar,g1⟩⟩
  . intro ⟨u1,u2,h1,h2,h3⟩
    simp_all only [reverse_nil, append_nil, nil_append]
    exists (f,u2.reverse,u1.reverse)
    simp only [reverse_reverse, true_and]
    exact ⟨h2,by rw[←reverse_append, h3]; exact reverse_reverse _⟩

theorem and_elim1_helper1 {X Y : RE α} :
  sp ⊫ ?<=X ⬝ Y →
  sp ⊫ ?<=X' ⬝ Y' →
  sp ⊫ (?<=X ⬝ ?<=X') ⬝ Y := by
  let ⟨s,u,v⟩ := sp
  intro g g1
  unfold models at g g1; simp only at g g1
  let ⟨a1,a2,a3,a4,a5⟩ := g
  let ⟨b1,b2,b3,b4,b5⟩ := g1
  unfold models; simp only
  simp_all only [Span.left,Span.right, Span.match]
  rw[claim2] at b3 a3
  simp at a3 b3
  let ⟨c1,c2,c3,c4⟩ := a3; let ⟨d1,d2,d3,d4⟩ := b3
  subst c1 d1; simp at b5 a5 a4; subst b5 a5
  exact ⟨[],a2,by unfold models; simp only
                  simp_rw[claim2]
                  simp only [Span.left,Span.right, Span.match]
                  exists []; exists []; simp;
                  simp only [reverse_nil, append_nil] at c4; exact ⟨⟨c2,c3,c4.1,c4.2⟩,
                  by simp only [reverse_nil, append_nil] at d4; exact ⟨d2,d3,d4.1,d4.2⟩⟩, a4,rfl⟩

theorem and_elim1 {X Y : RE α} :
  (((?<= X) ⬝ (?<= X')) ⬝ (Y ⋒ Y')) ↔ᵣ ((?<= X) ⬝ Y) ⋒ ((?<= X') ⬝ Y') :=
  λ {sp} => by
  apply Iff.trans (equiv_concat_congr (lb_join (X := X) (Y := X')))
  apply Iff.trans lookbehind_concat_distr_inter
  apply Iff.trans (inter_congr (Iff.symm $ equiv_concat_congr (lb_join))
                               (Iff.symm $ equiv_concat_congr (lb_join)))
  apply Iff.intro
  . intro g
    unfold models; simp only; unfold models at g; let ⟨g1,g2⟩ := g
    have : sp ⊫ (?<=X' ⬝ ?<=X) ⬝ Y' := by
      have a2 := equiv_concat_congr
                (equiv_trans (concat_lookbehinds_inter (X:=X) (Y:=X'))
                             (equiv_inter_comm (r:=?<=X) (q:=?<=X'))) (q:=Y') (sp:=sp)
      rw[helper_inter_cat] at a2; rw[←a2]; exact g2
    exact ⟨and_elim1_helper g1, and_elim1_helper this⟩
  . intro g
    unfold models at g; let ⟨g1,g2⟩ := g
    unfold models; simp only
    have := and_elim1_helper1 g2 g1
    rw [←helper_inter_cat, equiv_concat_congr (equiv_inter_comm), helper_inter_cat] at this
    exact ⟨and_elim1_helper1 g1 g2,this⟩

theorem lookahead_concat_distr_inter {X Y Z : RE α} :
  sp ⊫ (X ⋒ Y) ⬝ (?= Z) ↔ (sp ⊫ (X ⬝ (?= Z)) ⋒ (Y ⬝ (?= Z))) := by
  unfold models
  apply Iff.intro
  . intro ⟨u1,u2,h1,h2,h3⟩
    unfold models at h1; unfold models
    exact ⟨⟨u1,u2,h1.1,h2,h3⟩,⟨u1,u2,h1.2,h2,h3⟩⟩
  . intro ⟨h1,h2⟩
    let ⟨s,u,v⟩ := sp
    unfold models at h1 h2
    let ⟨u1,u2,h3,h4,h5⟩ := h1
    let ⟨u3,u4,h6,h7,h8⟩ := h2
    have ⟨eq1,eq2⟩ : u1 = u3 ∧ u2 = u4 := by
      subst h5; simp at h4 h7; let ⟨p1,p2⟩ := h4; subst p1; simp at h8; let ⟨p3,p4⟩ := h7; subst p3
      simp at h8; subst h8; simp only [and_self]
    subst eq1 eq2
    exact ⟨u1,u2,by unfold models; exact ⟨h3,h6⟩,h4,h8⟩

theorem and_elim2 {X Y : RE α} :
  (X ⋒ Y) ⬝ (?=Z) ⬝ (?=Z') ↔ᵣ (X ⬝ (?=Z)) ⋒ (Y ⬝ (?=Z')) :=
  λ {sp} => by
  let ⟨s,u,v⟩ := sp
  rw[equiv_concat_congr2 la_join]
  rw[lookahead_concat_distr_inter]
  unfold models; simp only; unfold models; simp only [Span.left, Span.right, Span.match]
  apply Iff.intro
  . intro ⟨⟨u1,u2,u3,u4,u5⟩,v1,v2,v3,v4,v5⟩
    subst u5; rw[←la_join] at v4 u4
    rw[concat_lookaheads_inter] at v4 u4
    unfold models at v4 u4; rw[claim1] at v4 u4
    simp only at v4 u4
    rw[claim1] at v4 u4; simp at v4 u4
    simp_rw[claim1]
    let ⟨a1,a2,a3,a4,a5,a6,a7⟩ := u4; let ⟨⟨d1,d2,d3,d4,d5,d6⟩,b2,b3,b4,b5,b6,b7⟩ := v4
    subst b2 a2; simp at v5; subst v5
    simp at v3 u3 a1 b5 a5
    simp; subst b7
    let ⟨c1,c2,c3,c4,c5⟩ := a1
    clear a1 u4 v4
    exact ⟨⟨u3,c1,c2,c3,by unfold pad; exact models_TopStar,c5⟩,
           ⟨v3,a3,a4,a5,by unfold pad; exact models_TopStar,a7⟩⟩
  . intro ⟨⟨v1,v2,v3,v4,v5⟩,u1,u2,u3,u4,u5⟩
    rw[claim1] at v4 u4; simp at v4 u4
    subst u5
    let ⟨a1,a2,a3,a4⟩ := u4; let ⟨b1,b2,b3,b4⟩ := v4
    subst a1 b1; simp at v5; subst v5; simp at v3 u3 a4 b4
    exact ⟨⟨v1,[],v3,
            by rw[←la_join,concat_lookaheads_inter]
               unfold models; rw[claim1,claim1]; simp
               exact ⟨⟨b2,b3,b4.1,b4.2⟩,⟨a2,a3,a4.1,a4.2⟩⟩,rfl⟩,
           ⟨v1,[],u3,
            by rw[←la_join,concat_lookaheads_inter]
               unfold models; rw[claim1,claim1]; simp
               exact ⟨⟨b2,b3,b4.1,b4.2⟩,⟨a2,a3,a4.1,a4.2⟩⟩,rfl⟩⟩

theorem RE.and_elim {X Y Z : RE α} :
  (?<= X) ⬝ Y ⬝ (?= Z) ⋒ (?<= X') ⬝ Y' ⬝ (?= Z') ↔ᵣ ((?<= X) ⬝ (?<= X') ⬝ (Y ⋒ Y') ⬝ (?= Z) ⬝ (?= Z')) :=
  λ {sp} => by
  have step1 :=
    equiv_concat_congr (sp:=sp) (q:=(?= Z) ⬝ (?= Z')) (and_elim1 (X:=X) (X':=X') (Y:=Y) (Y':=Y'))
  rw[equiv_cat_assoc] at step1
  rw[←equiv_cat_assoc, step1]; clear step1
  have step2 := equiv_concat_congr (sp:=sp) (q:=?=Z') (lookahead_concat_distr_inter (X:=?<=X ⬝ Y) (Y:=?<=X' ⬝ Y') (Z:=Z))
  rw[equiv_cat_assoc] at step2
  rw[step2]; clear step2
  have step3 := lookahead_concat_distr_inter (X:=(?<=X ⬝ Y) ⬝ ?=Z) (Y:=((?<=X' ⬝ Y') ⬝ ?=Z)) (Z:=Z') (sp:=sp)
  rw[step3]; clear step3
  have step4 := equiv_concat_congr2 (sp:=sp) (q:=(?<=X' ⬝ Y')) $ concat_lookaheads_inter (X:=Z) (Y:=Z')
  conv => rhs; unfold models; rw[equiv_cat_assoc (r:=?<=X' ⬝ Y')]
  rw[step4]; clear step4
  have step5 := equiv_concat_congr2 (sp:=sp) (q:=(?<=X ⬝ Y)) $ concat_lookaheads_inter (X:=Z) (Y:=Z')
  rw[equiv_cat_assoc, step5]; clear step5
  conv => lhs; unfold models; simp only; rw[←equiv_cat_assoc (r:=?<=X),←equiv_cat_assoc (r:=?<=X')]
  apply Iff.intro
  . intro ⟨h1,h2⟩
    let ⟨s,u,v⟩ := sp
    unfold models at h1; let ⟨u1,u2,h3,h4,h5⟩ := h1; clear h1
    unfold models at h2; let ⟨u3,u4,h6,h7,h8⟩ := h2; clear h2
    simp at h5 h8; subst h5; rw[claim1] at h4 h7; simp at h4 h7
    let ⟨o1,o2,o3,o4,o5,o6⟩ := h4; subst o1 o6; clear h4
    let ⟨l1,l2,l3,l4,l5⟩ := h7; subst l1; clear h7
    exact ⟨by unfold models; exists u1; exists []; exists h3; aesop,
           by unfold models; exists u3; exists []; exists h6; aesop⟩
  . intro ⟨h1,h2⟩; unfold models at h1 h2
    let ⟨s,u,v⟩ := sp
    let ⟨u1,u2,h3,h4,h5⟩ := h1; clear h1
    let ⟨u3,u4,h6,h7,h8⟩ := h2; clear h2
    simp only [Span.match] at h5 h8; subst h5
    unfold models at h4; let ⟨g1,g2⟩ := h4; clear h4
    rw[claim1] at g1 g2; simp at g1 g2
    let ⟨o1,o2,o3,o4,o5⟩ := g1; clear g1
    let ⟨l1,l2,l3,l4,l5⟩ := g2; clear g2
    subst o1; simp at h8; subst h8
    exact ⟨by unfold models; exists (u3++u4); exists []; exists h3
              rw[claim1]; simp; aesop,
           by unfold models; exists u3; exists u4; exists h6
              rw[claim1]; simp; aesop⟩

theorem not_elim_helper1 {Y : RE α} {sp: Span σ} :
  sp ⊫ ~ (Y ⬝ (?=Z)) ↔ sp ⊫ ~ Y ⋓ (pad ⬝ ?!Z) :=
  ⟨λ h => by
    unfold models at h; unfold models
    by_cases r : (sp ⊫ ~ Y)
    . exact (Or.inl r)
    . apply Or.inr
      simp only [models, not_not] at r
      unfold models
      exists sp.match; exists []
      simp; unfold pad; exists (models_TopStar)
      intro ww zz pp rr
      apply h; unfold models
      exact ⟨sp.match,[],by simp; exists r; exists ww⟩,
   λ h => by
    let ⟨s,u,v⟩ := sp
    unfold models at h
    match h with
    | Or.inl o =>
      simp; intro xs ys h1 yse sp; simp_all
    | Or.inr o =>
      unfold models at o; unfold models; simp only
      intro qe
      let ⟨o1,o2,o3,o4,o5⟩ := o
      unfold models at qe
      let ⟨q1,q2,q3,q4,q5⟩ := qe
      simp at o4; let ⟨eq,eq1⟩ := o4
      subst eq
      simp only [append_nil, Span.match] at o5; subst o5
      simp at q3 q5 eq1
      rw[claim1] at q4
      simp at q4; let ⟨eq2,⟨as,bs,eq3⟩⟩ := q4; subst eq2
      simp at q5 eq3; subst q5
      exact eq1 (q1.reverse ++ s, as, bs) eq3.1 rfl (by simp_all)⟩

theorem not_elim_helper2 {Y : RE α} {sp: Span σ} :
  sp ⊫ ~ ((?<= X) ⬝ Y) ↔ sp ⊫ (?<! X ⬝ pad) ⋓ ~ Y := by
  apply Iff.intro
  . intro h
    unfold models at h; unfold models
    by_cases z: (sp ⊫ Y)
    . apply Or.inl
      unfold models
      exists []; exists sp.match
      simp
      apply And.intro
      . intro ⟨s1,u1,v1⟩ p mm ww
        apply h
        unfold models
        exists []; exists sp.match
        simp
        exists ⟨⟨s1,u1,v1⟩,by simp; exists p⟩
      . unfold pad; exact models_TopStar
    . unfold models; exact Or.inr z
  . let ⟨s,u,v⟩ := sp
    intro h; unfold models at h
    match h with
    | Or.inl h1 =>
      unfold models; simp only; intro h2
      unfold models at h1 h2; simp only at h1 h2
      let ⟨as,bs,g1,g2,g3⟩ := h1
      let ⟨xs,ys,f1,f2,f3⟩ := h2
      simp at f2 f3 g3 g1 f1
      let ⟨eq,g4⟩ := g1
      let ⟨eq1,⟨s1,u1,v1⟩,f5,f6,f7⟩ := f1
      subst eq; simp at g3; subst g3
      subst eq1; simp at f3; subst f3
      simp at f2 g4 f6 f7
      subst f6
      exact (g4 ⟨ys ++ v,u1,v1⟩ f5 rfl) f7
    | Or.inr h1 =>
      unfold models; simp only; intro h2
      unfold models at h1 h2; simp only at h1 h2
      let ⟨xs,ys,f1,f2,f3⟩ := h2
      simp at f2 f3 f1
      let ⟨a1,a2⟩ := f1
      subst a1; simp at f3; subst f3
      exact h1 f2

theorem not_elim {X Y : RE α} {sp: Span σ}:
  sp ⊫ ~((?<= X) ⬝ Y ⬝ (?=Z)) ↔
  sp ⊫ ((?<!X) ⬝ pad) ⋓ ~Y ⋓ (pad ⬝ ?!Z) := by
  have t1 := not_elim_helper2 (X:=X) (sp:=sp) (Y:=Y ⬝ ?=Z)
  have t2 := not_elim_helper1 (sp:=sp) (Y:=Y) (Z:=Z)
  simp only [models, ←t2, t1]

theorem nm1 {R : RE α} :
  sp ⊫ R ↔ sp ⊫ ((?<=ε) ⬝ R ⬝ (?=ε)) := by
  let ⟨s,u,v⟩ := sp
  apply Iff.intro
  . intro g; unfold models; exists []; exists u
    exact ⟨by rw[claim2]; simp; unfold pad; exact models_TopStar,
           by unfold models; exists u; exists []
              exact ⟨g, by unfold models; exact ⟨⟨rfl,(u.reverse++s,[],v),
                        by unfold models; rfl,rfl⟩,append_nil u⟩⟩, rfl⟩
  . intro g; unfold models at g
    let ⟨a1,a2,a3,a4,a5⟩ := g; subst a5
    rw[claim2] at a3; simp at a3; let ⟨h1,h2⟩ := a3; subst h1
    simp only [nil_append];
    simp only [reverse_nil, Span.left, nil_append,
      Span.right, models, Span.match, length_eq_zero_iff, Span.beg, Prod.mk.injEq] at a4
    let ⟨b1,b2,b3,⟨b4,b5⟩,b6⟩ := a4; subst b4
    simp only [append_nil] at b6; subst b6
    simp only [nil_append] at b3; exact b3

@[simp]
theorem models_startAnchor {sp : Span σ}:
  sp ⊫ (startAnchor : RE α) ↔ sp.match.length = 0 ∧ sp.left.length = 0 :=
  match sp with
  | ⟨[],[],v⟩ => by
    simp [Option.any]
    intro x h1 _ h2 h3 _
    aesop
  | ⟨a::u,[],v⟩ => by
    conv => rhs; simp
    apply iff_false_intro
    intro contra
    simp at contra
    have := contra ⟨v,[a],u⟩
    simp [Option.any] at this
  | ⟨s,a::u,v⟩ => by simp -- contradiction as u has to be empty by definition
