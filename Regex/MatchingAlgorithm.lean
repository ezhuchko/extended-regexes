import Regex.Reversal
import Regex.Correctness -- needed for reversal of derives

open RE

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

/-!
# Top-level algorithm

Contains the top-level algorithm and all definitions
required, along with proofs of its correctness.
-/

/-- Helper function to provide only those spans which are nullable. -/
@[simp]
def null? (r : RE α) (x : Loc σ) : Option (Span σ) :=
  if null r x then
    some x.as_span
  else
    none

/-- Main helper function for the top-level matching algorithm.
    Given a start position, returns the span with longest
    match size such that the input regex matches the output span.
    Note that the start location of the input is the same
    as of that of the output one, crucially using `increase_match_left`
    in the inductive case.
-/
@[simp]
def maxMatchEnd (r : RE α) (x : Loc σ) : Option (Span σ) :=
  match x with
  | ⟨_,[]⟩ => null? r x
  | ⟨u,c::v⟩ =>
    match maxMatchEnd (der r x) ⟨c::u,v⟩ with
    | none => null? r x
    | some res => some res.increase_match_left
termination_by x.right

/-- The location of the result of the null? function coincides with the input location.
    (i.e. it is a splitting of the original word) -/
def null?_split_as_loc {r : RE α} {x : Loc σ} {sp_out : Span σ}
  (matching : null? r x = some sp_out) : sp_out.beg = x := by
  unfold null? at matching
  by_cases h : null r x
  . simp at h;
    rw[h] at matching; simp at matching;
    subst matching;
    simp
  . simp at h;
    rw[h] at matching; simp at matching;

/-- The location of the result of the maxMatchEnd function coincides with the input location.
    (i.e. it is a splitting of the original word) -/
def maxMatchEnd_split_as_loc {r : RE α} {x : Loc σ} {sp_out : Span σ}
  (matching : maxMatchEnd r x = some sp_out) : sp_out.beg = x :=
  match x with
  | ⟨_,[]⟩ => by
    simp; simp at matching; let ⟨_,m2⟩ := matching; subst m2; simp
  | ⟨a,c::b⟩ => by
    match match_eq:maxMatchEnd (der (r : RE α) ⟨a,c::b⟩).val ⟨c::a,b⟩ with
    | none =>
      unfold maxMatchEnd at matching
      rw[match_eq] at matching;
      exact null?_split_as_loc matching
    | some sp =>
      have ind := maxMatchEnd_split_as_loc match_eq
      unfold maxMatchEnd at matching
      rw[match_eq] at matching;
      simp at matching;
      subst matching;
      match sp with
      | ⟨[],_,_⟩ => simp at ind
      | ⟨cc::aa,m,r⟩ =>
        simp_all
termination_by x.right

/-- Given a precise split on the left location, derive that the entire word coincides. -/
def split_as_loc_word {x : Loc σ} {sp : Span σ}
  (h : sp.beg = x) : sp.word = x.word := by
  subst h
  simp_all

/-- The span output by `maxMatchEnd` is indeed a match for the regex given. -/
theorem maxMatchEnd_matches {x : Loc σ} {r : RE α} {sp_out : Span σ}
  (matching : maxMatchEnd r x = some sp_out) : sp_out ⊢ r :=
  match x with
  | ⟨a,[]⟩ => by
    simp at matching
    by_cases h : null r ⟨a,[]⟩
    . rw[h] at matching; simp at matching; subst matching; simp; exact h
    . simp at h
      rw[h] at matching
      simp at matching
  | ⟨a,c::b⟩ => by
    match match_eq:maxMatchEnd (der r ⟨a,c::b⟩).val ⟨c::a,b⟩ with
    | none =>
      unfold maxMatchEnd at matching;
      rw[match_eq] at matching;
      simp at matching;
      by_cases h : null r ⟨a,c::b⟩
      . simp at h; rw[h] at matching; simp at matching;
        subst matching;
        simp; assumption
      . simp at h; rw[h] at matching; simp at matching;
    | some sp =>
      have ind := maxMatchEnd_matches match_eq
      unfold maxMatchEnd at matching;
      rw[match_eq] at matching;
      simp at matching;
      subst matching;
      have p := maxMatchEnd_split_as_loc match_eq
      simp at p
      match sp with
      | ⟨spl,spm,spr⟩ =>
        simp_all
termination_by x.right

/-- Preliminary definitions on spans.
The main idea is to place enough infrastructure to be able
to seamlessly convert between right-handed definitions and left-handed definitions
(e.g. switch from min to max by reversing the word.) -/

/- A location is a match start location when they refer to the same word
   and its left indices coincide. -/
@[simp]
def derivesStartLocation (loc : Loc σ) (sp2 : Span σ) : Prop :=
    loc.pos = sp2.i
  ∧ loc.word = sp2.word

/- A location is a match end location when they refer to the same word
   and its right indices coincide. -/
@[simp]
def derivesEndLocation (loc : Loc σ) (sp2 : Span σ) : Prop :=
    loc.pos = sp2.j
  ∧ loc.word = sp2.word

/- A location is a match end location whenever it is a start for the reversal of both. -/
theorem match_end_start (h : derivesEndLocation x sp) :
  derivesStartLocation x.reverse sp.reverse := by
  match x with
  | ⟨x1,x2⟩ =>
  match eq2:sp with
  | ⟨sp1,sp2,sp3⟩ =>
    simp_all
    match h with
    | ⟨h1,h2⟩ =>
      have snd := congrArg List.reverse h2
      simp at snd
      rw[←List.append_assoc] at h2
      exact ⟨congrArg List.length $ List.append_inj_right h2
               (by simp; exact h1),snd⟩

/- A location is a match start location whenever it is an end for the reversal of both. -/
theorem match_start_end (h : derivesStartLocation x sp) :
  derivesEndLocation x.reverse sp.reverse := by
  match x with
  | ⟨x1,x2⟩ =>
  match eq2:sp with
  | ⟨sp1,sp2,sp3⟩ =>
    simp_all
    match h with
    | ⟨h1,h2⟩ =>
      have snd := congrArg List.reverse h2
      simp at snd
      exact ⟨(by
        have p := congrArg List.length
                $ List.append_inj_right h2 (by simp; exact h1);
        simp at p;
        rw[Nat.add_comm] at p
        exact p),snd⟩

/- Similar lemma to the previous one, referring directly to the indices. -/
theorem start_end_reverse {sp1 sp2 : Span σ} :
    sp1.word = sp2.word
  → Span.j (Span.reverse sp1) ≤ Span.j (Span.reverse sp2)
  → Span.i sp2 ≤ Span.i sp1 :=
  λ split _ =>
  match sp1 with
  | ⟨_,_,_⟩ =>
  match sp2 with
  | ⟨_,_,_⟩ => by
    have lengths := congrArg List.length split
    simp at lengths
    simp_all
    linarith

/-- Helper function showing that reversing a word is injective.
    TODO: PR this to mathlib4 -/
theorem reverse_injective {sp1 sp2 : List σ} (h : sp1.reverse = sp2.reverse) : sp1 = sp2 :=
  match sp1,sp2 with
  | [],[] => rfl
  | [],c::cs => by simp at h;
  | c::cs,[] => by simp at h;
  | c::cs,d::ds => by
    simp at h
    have ⟨s1,s2⟩ := List.append_inj' h (by simp)
    simp at s2
    rw[s2, reverse_injective s1]

/- Knowing that a position is a starting position for a span, either the
   end match location coincides with the starting location (i.e., the span and
   the location are equal) or it is strictly greater than the location. -/
theorem derivesStartLocation_equal_or_lt
   (leL : derivesStartLocation loc sp) :
  sp = loc.as_span ∨ loc.pos < sp.j := by
  match sp with
  | ⟨sp1,[],sp3⟩ =>
    simp_all
    match leL with
    | ⟨le1,le2⟩ =>
      have : (List.length (List.reverse loc.fst)) = List.length (List.reverse sp1) := by
        rw[List.length_reverse,List.length_reverse]
        exact le1
      have : List.reverse loc.fst = List.reverse sp1 := by
        exact List.append_inj_left le2 this
      have : loc.fst = sp1 := reverse_injective this
      simp_all
  | ⟨sp1,c::sp2,sp3⟩ =>
    simp_all

/-- If the location is the end of the word, the span must be empty on the right. -/
theorem match_start_empty_empty
  (h : derivesStartLocation (a, []) sp) :
  sp = (a, [], []) :=
  match sp with
  | ⟨sp1,sp2,sp3⟩ => by
    simp_all
    match h with
    | ⟨h1,h2⟩ =>
      have : List.length sp2 + List.length sp3 = 0 := by
        have asd := congrArg List.length h2
        simp at asd
        rw[h1] at asd
        linarith
      simp at this
      simp_all only [List.reverse_nil, List.nil_append, and_self]

/-- The starting location of maxMatchEnd coincides with the input location. -/
def maxMatchEnd_derivesStartLocation {r : RE α} {x : Loc σ} {sp_out : Span σ}
  (matching : maxMatchEnd r x = some sp_out) :
  derivesStartLocation x sp_out := by
  have := maxMatchEnd_split_as_loc matching
  match x with
  | ⟨x1,x2⟩ => simp_all

/-- Given `derivesStartLocation`, the first character and the left boundary of the
    location and the span must coincide. -/
theorem match_start_cons_equal {x x' : List σ}
  (h : derivesStartLocation ⟨x,c::y⟩ ⟨x',c'::m',y'⟩) :
  c = c' ∧ x = x' := by
  match h with
  | ⟨h1,h3⟩ =>
  have t2'' : ((c::x).reverse) = ((c'::x').reverse) := by
    simp at h3
    simp
    simp at h1
    exact List.append_inj_left (by simp; exact h3)
      (by simp; exact h1)
  have := reverse_injective t2''
  simp at this
  exact this

/-- Lemma for the completeness theorem for `maxMatchEnd`.
    If maxMatchEnd returns none, then no match is possible for the span
    at the same location that was given. -/
theorem maxMatchEnd_no_match_here {x : Loc σ} {r : RE α}
  (matching : maxMatchEnd r x = none) :
  ¬(x.as_span ⊢ r) :=
  match x with
  | ⟨xl,[]⟩ => by
    simp at matching; simp
    exact matching
  | ⟨xl,xc::xr⟩ => by
    unfold maxMatchEnd at matching
    match hyp:maxMatchEnd (der r (xl, xc :: xr)).val (xc :: xl, xr) with
    | none =>
      rw[hyp] at matching;
      simp at matching; simp
      exact matching
    | some _ =>
      rw[hyp] at matching;
      simp at matching

/-- Main completeness theorem for `maxMatchEnd`.
    If maxMatchEnd returns none, then no match is possible for any span
    that starts at the position provided. -/
theorem maxMatchEnd_no_match {x : Loc σ} {r : RE α}
  (matching : maxMatchEnd r x = none) :
  (∀ sp, derivesStartLocation x sp → ¬(sp ⊢ r)) :=
  λ sp lb sp_match => by
    match derivesStartLocation_equal_or_lt lb with
    | Or.inl rcase =>
      subst rcase
      simp at sp_match
      exact maxMatchEnd_no_match_here matching (by simp; exact sp_match)
    | Or.inr rcase =>
      match x_eq:x with
      | ⟨xl,[]⟩ =>
        have := match_start_empty_empty lb
        simp_all
      | ⟨xl,xc::xr⟩ =>
        unfold maxMatchEnd at matching
        match hyp:maxMatchEnd (der r (xl, xc :: xr)).val (xc :: xl, xr) with
        | none =>
          rw[hyp] at matching;
          simp at matching
          match sp_eq:sp with
          | ⟨_,[],_⟩ =>
            simp_all
          | ⟨a,spc::spm,spa⟩ =>
            match fissi:match_start_cons_equal lb with
            | ⟨eq1,eq2⟩ =>
              subst eq1 eq2
              simp at lb
              have : sizeOf (spm ++ spa) < 1 + sizeOf xr :=
                by subst lb; simp
              subst lb
              have := maxMatchEnd_no_match hyp (xc :: xl, spm, spa)
                                            (by simp)
                                            (by simp at sp_match; exact sp_match)
              simp_all
        | some _ =>
          rw[hyp] at matching;
          simp at matching
termination_by x.right

/-- Main location correctness theorem for `maxMatchEnd`.
    If maxMatchEnd returns a span, then it is the one with longest
    match length among those that share the same position and are a match. -/
theorem maxMatchEnd_max {r : RE α} {sp_out : Span σ} {x : Loc σ}
  (m : maxMatchEnd r x = some sp_out) :
  (∀ sp, derivesStartLocation x sp
       → sp ⊢ r
       → sp.j ≤ sp_out.j) := by
  intro sp lb sp_match
  unfold maxMatchEnd at m
  match x_eq:x with
  | ⟨a,[]⟩ =>
    simp at m
    by_cases h : null r (a, []) = true
    . rw[h] at m; simp at m; subst m;
      have := match_start_empty_empty lb
      subst this
      simp
    . simp at h; rw[h] at m; simp at m;
  | ⟨a,c::b⟩ =>
    simp at m;
    match match_eq:maxMatchEnd (der r (a, c :: b)).val (c :: a, b)  with
    | none =>
      rw[match_eq] at m
      simp at m
      match eq:null r (a, c :: b) with
      | true =>
        rw[eq] at m; simp at m; subst m
        match sp_eq:sp with
        | ⟨_,[],_⟩ => simp_all
        | ⟨spl,spc::spm,spr⟩ =>
          match match_start_cons_equal lb with
          | ⟨eq1,eq2⟩ =>
            subst eq1 eq2
            simp_all
            exact maxMatchEnd_no_match match_eq
              (c :: a, spm, spr) (by simp) sp_match
      | false => rw[eq] at m; simp at m;
    | some sp_mme =>
      rw[match_eq] at m;
      simp at m;
      match derivesStartLocation_equal_or_lt lb with
      | Or.inl a =>
        subst a m
        have d := maxMatchEnd_split_as_loc match_eq
        match sp_mme with
        | ⟨[],_,_⟩ => simp at d
        | ⟨c::cs,spmm,spmr⟩ =>
          aesop
      | Or.inr q =>
        have po := maxMatchEnd_matches match_eq
        match sp_eq:sp with
        | ⟨_,[],_⟩ =>
          simp_all
        | ⟨spl,spc::spm,spr⟩ =>
          match match_start_cons_equal lb with
          | ⟨eq1,eq2⟩ =>
            subst eq1 eq2
            have ultima := maxMatchEnd_max match_eq (c :: a, spm, spr)
              (by simp_all)
              (by simp_all)
            match mme_eq:sp_mme with
            | ⟨[],spmme2,spmm3⟩ =>
              simp at m;
              subst m
              simp_all
              linarith
            | ⟨c::spmme1,spmme2,spmm3⟩ =>
              simp at m
              subst m
              simp_all
              linarith
termination_by x.right

/-
# Dual theorems for `minMatchStart`
-/

/- Definition of `minMatchStart` by reversing all inputs and the output. -/
def minMatchStart (r : RE α) (x : Loc σ) : Option (Span σ) :=
  Option.map Span.reverse (maxMatchEnd (r ʳ) x.reverse)

theorem minMatchStart_derivesEndLocation {r : RE α} {x : Loc σ} {sp_out : Span σ}
  (matching : minMatchStart r x = some sp_out) :
  derivesEndLocation x sp_out := by
  unfold minMatchStart at matching
  match eqq:maxMatchEnd rʳ (Loc.reverse x) with
  | none => rw[eqq] at matching; simp at matching;
  | some a =>
    rw[eqq] at matching;
    simp only [Option.map_some', Option.some.injEq] at matching
    subst matching
    have pip := maxMatchEnd_derivesStartLocation eqq
    have := match_start_end pip
    simp only [reverse_loc_involution] at this
    exact this

/-- The span output by `minMatchStart` is indeed a match for the regex given. -/
theorem minMatchStart_matches {r : RE α} {sp_out : Span σ}
  (matching : minMatchStart r x = some sp_out) :
  (sp_out ⊢ r) := by
  unfold minMatchStart at matching
  match eqq:maxMatchEnd rʳ (Loc.reverse x) with
  | none => rw[eqq] at matching; simp at matching;
  | some a =>
    rw[eqq] at matching;
    simp only [Option.map_some', Option.some.injEq] at matching
    subst matching
    have correct := maxMatchEnd_matches eqq
    have eq := @reverse_span_involution _ a
    rw[←eq] at correct
    have := derives_reversal.mp correct
    rw[reverse_span_involution,reverse_RE_involution] at this
    exact this

/-- See location correctness theorem above. -/
theorem minMatchStart_min {r : RE α} {x : Loc σ} {sp_out : Span σ}
  (matching : minMatchStart r x = some sp_out) :
  (∀ sp, derivesEndLocation x sp
       → sp ⊢ r
       → sp_out.i ≤ sp.i) :=
  λ sp right_le is_match => by
    unfold minMatchStart at matching
    match eqq:maxMatchEnd (r ʳ) x.reverse with
    | none => rw[eqq] at matching; simp at matching;
    | some sp_call =>
      rw[eqq] at matching;
      simp only [Option.map,Option.some.injEq] at matching;
      have : sp_call = sp_out.reverse := by
        have a := congrArg Span.reverse matching;
        simp only [reverse_span_involution] at a;
        exact a
      subst this
      have jle := maxMatchEnd_max eqq sp.reverse
        (match_end_start right_le)
        (derives_reversal.mp is_match)
      have := maxMatchEnd_split_as_loc eqq
      have str : sp.word = sp_out.word := by
        simp at this;
        match sp_out with
        | ⟨_,_,_⟩ =>
        match x with
        | ⟨_,_⟩ =>
          aesop
      exact start_end_reverse str jle

/-- See completeness theorem above. -/
theorem minMatchStart_no_match {r : RE α} {x : Loc σ}
  (matching : minMatchStart r x = none) :
  (∀ sp, derivesEndLocation x sp → ¬(sp ⊢ r)) := by
  unfold minMatchStart at matching
  match eq:maxMatchEnd rʳ (Loc.reverse x) with
  | none =>
    intro sp rb sp_match
    have p := maxMatchEnd_no_match eq sp.reverse (match_end_start rb)
    exact p (derives_reversal.mp sp_match)
  | some _ =>
    rw[eq] at matching
    simp_all

/- Note that no correctness theorem (i.e., it is indeed a match)
   for `minMatchStart` is required. -/

/-- Given a span, preserve the left boundary and maximally
    extend the match to cover the rest of word. -/
@[simp]
def max_right_extension (sp : Span σ) : Span σ := ⟨sp.left, sp.match ++ sp.right, []⟩

/-- For any span, iterated true always matches. -/
theorem derives_TopStar {sp : Span σ} : sp ⊢ (Pred (⊤ : α))* :=
  match sp with
  | ⟨_,[],_⟩ => by simp
  | ⟨l,c::m,r⟩ => by
    let p := @derives_TopStar (sp := ⟨c::l,m,r⟩)
    simp
    exact derives_Cat.mpr ⟨[],_,(by simp),p,by simp⟩
termination_by sp.match.length

/-- Any match can be lifted to the match on the maximal right extension
    and concatenating true to the regex accordingly. -/
theorem match_right_extension
  (matching : sp ⊢ R) :
  (max_right_extension sp) ⊢ (R ⬝ (Pred (⊤ : α))*) :=
  match sp with
  | ⟨s,u,v⟩ => by
    simp;
    exact derives_Cat.mpr ⟨u,v, (by simp; exact matching), derives_TopStar, rfl⟩

/-- Crucial correctness of `max_right_extension`:
    the end location of the extension is indeed a match end location of any word
    for which it is a splitting. -/
theorem derivesEndLocation_max_right_extension
  (splitting : sp.word = w) :
  derivesEndLocation (List.as_end_location w) (max_right_extension sp) := by
    simp at splitting
    simp
    subst splitting
    simp_all

/-
# Top-level algorithm
-/

/-- The top-level matching algorithm takes a word `w` and a regex `R` and
   either returns the leftmost longest span in the word or none if
   no match for the regex exists. Uses `do`-notation in the `Option` monad.
-/
@[simp]
def llmatch (R : RE α) (w : List σ) : Option (Span σ) := do
  let leftmost_sp ← minMatchStart (R ⬝ (Pred (⊤ : α))*) w.as_end_location
  maxMatchEnd R leftmost_sp.beg

----------- main correctness proofs -----------------

/- The start location of the span returned by `llmatch` is
   the leftmost among those on the same word `w`. -/
theorem llmatch_leftmost {r : RE α} {sp_out : Span σ} {w : List σ}
  (m : llmatch r w = some sp_out) :
  (∀ sp, sp.word = w
       → sp ⊢ r
       → sp_out.i ≤ sp.i) := by
  unfold llmatch at m
  match first_call:minMatchStart (r ⬝ (Pred (⊤ : α))*) w.as_end_location with
  | none => rw[first_call] at m;
            unfold instMonadOption at m
            simp at m;
  | some first_call_sp =>
    rw[first_call] at m; simp at m;
    intro sp splitting is_match
    subst splitting
    let first_call_le_sp : Span.i first_call_sp ≤ Span.i (max_right_extension sp) :=
      minMatchStart_min
        first_call
        (max_right_extension sp)
        (by simp; linarith)
        (match_right_extension is_match)
    match maxMatchEnd_derivesStartLocation m with
    | ⟨e1,_⟩ =>
      simp at first_call_le_sp
      simp
      simp at e1
      rw[←e1]
      exact first_call_le_sp

/- The span returned by `llmatch` is the longest match among those
   on the same word `w` that start at the same location. -/
theorem llmatch_longest {r : RE α} {sp_out : Span σ}
  (m : llmatch r w = some sp_out) :
  (∀ sp, sp.word = w
       → sp.i = sp_out.i
       → sp ⊢ r
       → sp_out.match.length ≥ sp.match.length) := by
  intro sp splitting same_location is_match
  unfold llmatch at m
  match first_call:minMatchStart (r ⬝ (Pred (⊤ : α))*) w.as_end_location with
  | none => rw[first_call] at m;
            unfold instMonadOption at m
            simp at m
  | some first_call_sp =>
    rw[first_call] at m; simp at m;
    have second_call_preserve :=
      maxMatchEnd_derivesStartLocation m
    have leftmost_boundary : derivesStartLocation first_call_sp.beg sp := by
      have fb := minMatchStart_derivesEndLocation first_call
      simp_all
    have direct :=
      maxMatchEnd_max
        m
        sp
        leftmost_boundary
        is_match
    aesop

/- If `llmatch` returned none, then no match exists in the entire word. -/
theorem llmatch_no_match {r : RE α} {w : List σ}
  (m : llmatch r w = none) :
  (∀ sp, sp.word = w
       → ¬(sp ⊢ r)) := by
  unfold llmatch at m
  intro sp splitting sp_match
  match first_call:minMatchStart (r ⬝ (Pred ⊤)*) (List.as_end_location w) with
  | none =>
    exact minMatchStart_no_match first_call
              (max_right_extension sp)
              (derivesEndLocation_max_right_extension splitting)
              (match_right_extension sp_match)
  | some leftmost =>
    rw[first_call] at m
    simp at m
    have f1 := minMatchStart_matches first_call
    have f2 := maxMatchEnd_no_match m
    match derives_Cat.mp f1 with
    | ⟨u1,u2,m1,_,t⟩ =>
      exact f2 _ (by simp_all; rw[←t]; simp) m1

/- The span returned by `llmatch` is indeed a match for the regex given. -/
theorem llmatch_matches {r : RE α} {sp_out : Span σ} {w : List σ}
  (m : llmatch r w = some sp_out) :
  (sp_out ⊢ r) := by
  unfold llmatch at m
  match first_call:minMatchStart (r ⬝ (Pred ⊤)*) (List.as_end_location w) with
  | none => rw[first_call] at m;
            unfold instMonadOption at m
            simp at m
  | some first_call_sp =>
    rw[first_call] at m; simp at m;
    have second_call_correct := maxMatchEnd_matches m
    exact second_call_correct
