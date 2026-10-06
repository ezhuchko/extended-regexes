import Regex.Correctness -- needed for reversal of `derives`

open RE

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

/-!
# Top-level algorithm

Contains the top-level algorithm and all definitions
required, along with proofs of its correctness.
-/

/-- Helper function to provide only those spans which are nullable. -/
def null? (r : RE α) (x : Loc σ) : Option (Span σ) :=
  if null r x then
    some x.as_span
  else
    none

/--
  Main helper function for the top-level matching algorithm.
  Given a start position, returns the span with longest
  match size such that the input regex matches the output span.
  Note that the start location of the input is the same
  as of that of the output one, crucially using `increase_match_left`
  in the inductive case.
-/
def maxMatchEnd (r : RE α) (x : Loc σ) : Option (Span σ) :=
  match x with
  | ⟨_,[]⟩ => null? r x
  | ⟨u,c::v⟩ =>
    match maxMatchEnd (der r x) ⟨c::u,v⟩ with
    | none => null? r x
    | some res => some res.increase_match_left
termination_by x.right

theorem null?_eq_some {r : RE α} {x : Loc σ} :
    null? r x = some sp ↔ null r x ∧ x.as_span = sp := by
  unfold null?; split <;> simp_all

theorem null?_eq_none {r : RE α} {x : Loc σ} : null? r x = none ↔ ¬ null r x := by
  unfold null?; split <;> simp_all

/-- A span begins at a location iff its left parts agree and the rest of the word agrees. -/
theorem beg_eq_iff {s m r u w : List σ} :
    Span.beg ⟨s, m, r⟩ = (⟨u, w⟩ : Loc σ) ↔ s = u ∧ m ++ r = w :=
  by simp

/-! ### Correctness of `maxMatchEnd` -/

/-- The span returned by `maxMatchEnd` begins at the given location. -/
theorem maxMatchEnd_beg {r : RE α} {x : Loc σ} {sp : Span σ}
    (h : maxMatchEnd r x = some sp) : sp.beg = x :=
  match x with
  | ⟨u, []⟩ => by
    rw [maxMatchEnd, null?_eq_some] at h; obtain ⟨-, rfl⟩ := h; rfl
  | ⟨u, c :: v⟩ => by
    rw [maxMatchEnd] at h
    split at h
    · rw [null?_eq_some] at h; obtain ⟨-, rfl⟩ := h; rfl
    · next sp' h' =>
      obtain ⟨_, m, r'⟩ := sp'
      obtain ⟨rfl, rfl⟩ := beg_eq_iff.mp (maxMatchEnd_beg h')
      cases h; rfl
termination_by x.right

/-- The span returned by `maxMatchEnd` is a match. -/
theorem maxMatchEnd_matches {r : RE α} {x : Loc σ} {sp : Span σ}
    (h : maxMatchEnd r x = some sp) : sp ⊢ r :=
  match x with
  | ⟨u, []⟩ => by
    rw [maxMatchEnd, null?_eq_some] at h; obtain ⟨hn, rfl⟩ := h; rwa [Loc.as_span, derives_nil]
  | ⟨u, c :: v⟩ => by
    rw [maxMatchEnd] at h
    split at h
    · rw [null?_eq_some] at h; obtain ⟨hn, rfl⟩ := h; rwa [Loc.as_span, derives_nil]
    · next sp' h' =>
      obtain ⟨_, m, r'⟩ := sp'
      obtain ⟨rfl, rfl⟩ := beg_eq_iff.mp (maxMatchEnd_beg h')
      cases h
      rw [Span.increase_match_left, derives_cons]
      exact maxMatchEnd_matches h'
termination_by x.right

/-- If `maxMatchEnd` returns `none`, no span beginning at the given location is a match. -/
theorem maxMatchEnd_none {r : RE α} {x : Loc σ}
    (h : maxMatchEnd r x = none) : ∀ sp, sp.beg = x → ¬ sp ⊢ r :=
  match x with
  | ⟨u, []⟩ => by
    rintro ⟨_, m, r'⟩ e
    obtain ⟨rfl, e₁⟩ := beg_eq_iff.mp e
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp e₁
    rw [maxMatchEnd, null?_eq_none] at h
    rwa [derives_nil]
  | ⟨u, c :: v⟩ => by
    rw [maxMatchEnd] at h
    split at h
    · next h' =>
      rw [null?_eq_none] at h
      rintro ⟨_, _ | ⟨c', m⟩, r'⟩ e <;> obtain ⟨rfl, e₁⟩ := beg_eq_iff.mp e
      · subst e₁; rwa [derives_nil]
      · obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp e₁
        rw [derives_cons]
        exact maxMatchEnd_none h' _ rfl
    · cases h
termination_by x.right

/-- The span returned by `maxMatchEnd` is the longest match beginning at the given location. -/
theorem maxMatchEnd_max {r : RE α} {x : Loc σ} {sp_out : Span σ}
    (h : maxMatchEnd r x = some sp_out) :
    ∀ sp, sp.beg = x → sp ⊢ r → sp.mid.length ≤ sp_out.mid.length :=
  match x with
  | ⟨u, []⟩ => by
    rintro ⟨_, m, _⟩ e -
    obtain rfl : m = [] := (List.append_eq_nil_iff.mp (beg_eq_iff.mp e).2).1
    simp
  | ⟨u, c :: v⟩ => by
    rintro ⟨_, _ | ⟨c', m⟩, r'⟩ e hm
    · simp
    obtain ⟨rfl, e₁⟩ := beg_eq_iff.mp e
    obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp e₁
    rw [derives_cons] at hm
    rw [maxMatchEnd] at h
    split at h
    · next h' => exact absurd hm (maxMatchEnd_none h' _ rfl)
    · next sp' h' =>
      obtain ⟨_, m', _⟩ := sp'
      obtain ⟨rfl, -⟩ := beg_eq_iff.mp (maxMatchEnd_beg h')
      cases h
      simpa using maxMatchEnd_max h' _ rfl hm
termination_by x.right

/-! ### Words and locations -/

theorem word_eq_of_beg {sp : Span σ} {x : Loc σ} (h : sp.beg = x) : sp.word = x.word := by
  subst h; simp

theorem word_eq_of_end {sp : Span σ} {x : Loc σ} (h : sp.end = x) : sp.word = x.word := by
  subst h; simp

/-- Two spans of the same word that start at the same index begin at the same location. -/
theorem beg_eq_of_word {sp sp' : Span σ} (hw : sp.word = sp'.word) (hi : sp.i = sp'.i) :
    sp.beg = sp'.beg := by
  obtain ⟨s, u, v⟩ := sp; obtain ⟨s', u', v'⟩ := sp'
  simp only [Span.word, List.append_assoc, Span.i] at hw hi
  obtain ⟨h₁, h₂⟩ := List.append_inj hw (by simpa using hi)
  simp_all

/-! ### `minMatchStart`: the dual of `maxMatchEnd`, by reversal -/

def minMatchStart (r : RE α) (x : Loc σ) : Option (Span σ) :=
  Option.map Span.reverse (maxMatchEnd (r ʳ) x.reverse)

theorem minMatchStart_eq_some {r : RE α} {x : Loc σ} {sp : Span σ}
    (h : minMatchStart r x = some sp) : maxMatchEnd (r ʳ) x.reverse = some sp.reverse := by
  obtain ⟨sp', h', rfl⟩ := Option.map_eq_some_iff.mp h
  rwa [reverse_span_involution]

/-- The span returned by `minMatchStart` ends at the given location. -/
theorem minMatchStart_end {r : RE α} {x : Loc σ} {sp : Span σ}
    (h : minMatchStart r x = some sp) : sp.end = x := by
  have := maxMatchEnd_beg (minMatchStart_eq_some h)
  rw [Span.beg_reverse] at this
  exact Loc.reverse_inj.mp this

/-- The span returned by `minMatchStart` is a match. -/
theorem minMatchStart_matches {r : RE α} {x : Loc σ} {sp : Span σ}
    (h : minMatchStart r x = some sp) : sp ⊢ r := by
  have := maxMatchEnd_matches (minMatchStart_eq_some h)
  rwa [← derives_reversal] at this

/-- If `minMatchStart` returns `none`, no span ending at the given location is a match. -/
theorem minMatchStart_none {r : RE α} {x : Loc σ}
    (h : minMatchStart r x = none) : ∀ sp, sp.end = x → ¬ sp ⊢ r := by
  intro sp e hm
  exact maxMatchEnd_none (Option.map_eq_none_iff.mp h) sp.reverse
    (by rw [Span.beg_reverse, e]) (derives_reversal.mp hm)

/-- The span returned by `minMatchStart` is the leftmost match ending at the given location. -/
theorem minMatchStart_min {r : RE α} {x : Loc σ} {sp_out : Span σ}
    (h : minMatchStart r x = some sp_out) : ∀ sp, sp.end = x → sp ⊢ r → sp_out.i ≤ sp.i := by
  intro sp e hm
  have hlen := maxMatchEnd_max (minMatchStart_eq_some h) sp.reverse
    (by rw [Span.beg_reverse, e]) (derives_reversal.mp hm)
  have hend := congrArg (fun l => l.left.length) (e.trans (minMatchStart_end h).symm)
  obtain ⟨_, _, _⟩ := sp; obtain ⟨_, _, _⟩ := sp_out
  simp at hlen hend ⊢
  omega

/-! ### Top-level algorithm -/

/-- Given a span, preserve the left boundary and maximally
    extend the match to cover the rest of word. -/
def max_right_extension (sp : Span σ) : Span σ := ⟨sp.left, sp.mid ++ sp.right, []⟩

/-- Any match can be lifted to the match on the maximal right extension
    and concatenating true to the regex accordingly. -/
theorem match_right_extension {sp : Span σ} {R : RE α} (h : sp ⊢ R) :
    max_right_extension sp ⊢ (R ⬝ (Pred (⊤ : α))*) := by
  obtain ⟨s, u, v⟩ := sp
  refine derives_Cat.mpr ⟨u, v, ?_, derives_TopStar, rfl⟩
  simp only [max_right_extension, List.append_nil]
  exact h

/-- The maximal right extension of a span of `w` ends at the end of `w`. -/
theorem max_right_extension_end {sp : Span σ} (h : sp.word = w) :
    (max_right_extension sp).end = w.as_end_location := by
  obtain ⟨s, u, v⟩ := sp; subst h; simp [max_right_extension]

/-- The top-level matching algorithm takes a word `w` and a regex `R` and
   either returns the leftmost longest span in the word or none if
   no match for the regex exists. Uses `do`-notation in the `Option` monad.
-/
def llmatch (R : RE α) (w : List σ) : Option (Span σ) := do
  let leftmost_sp ← minMatchStart (R ⬝ (Pred (⊤ : α))*) w.as_end_location
  maxMatchEnd R leftmost_sp.beg

theorem llmatch_eq_some {r : RE α} :
    llmatch r w = some sp ↔
    ∃ f, minMatchStart (r ⬝ (Pred ⊤)*) w.as_end_location = some f ∧ maxMatchEnd r f.beg = some sp := by
  simp [llmatch, Option.bind_eq_some_iff]

/-! ### Main correctness theorems -/

/-- The start location of the span returned by `llmatch` is
   the leftmost among those on the same word `w`. -/
theorem llmatch_leftmost {r : RE α} {sp_out : Span σ} {w : List σ}
  (m : llmatch r w = some sp_out) :
  (∀ sp, sp.word = w
       → sp ⊢ r
       → sp_out.i ≤ sp.i) := by
  intro sp hw hsp
  obtain ⟨f, hf, hm⟩ := llmatch_eq_some.mp m
  have h₁ := minMatchStart_min hf _ (max_right_extension_end hw) (match_right_extension hsp)
  have h₂ := congrArg (fun l => l.left.length) (maxMatchEnd_beg hm)
  simp [max_right_extension] at h₁ h₂ ⊢
  omega

/-- The span returned by `llmatch` is the longest match among those
   on the same word `w` that start at the same location. -/
theorem llmatch_longest {r : RE α} {sp_out : Span σ}
  (m : llmatch r w = some sp_out) :
  (∀ sp, sp.word = w
       → sp.i = sp_out.i
       → sp ⊢ r
       → sp_out.mid.length ≥ sp.mid.length) := by
  intro sp hw hi hsp
  obtain ⟨f, hf, hm⟩ := llmatch_eq_some.mp m
  have hb := maxMatchEnd_beg hm
  have hw' : sp_out.word = w := by
    rw [word_eq_of_beg hb, ← word_eq_of_beg rfl, word_eq_of_end (minMatchStart_end hf)]; simp
  exact maxMatchEnd_max hm sp ((beg_eq_of_word (hw.trans hw'.symm) hi).trans hb) hsp

/-- If `llmatch` returned none, then no match exists in the entire word. -/
theorem llmatch_no_match {r : RE α} {w : List σ}
  (m : llmatch r w = none) :
  (∀ sp, sp.word = w
       → ¬(sp ⊢ r)) := by
  intro sp hw hsp
  cases hf : minMatchStart (r ⬝ (Pred ⊤)*) w.as_end_location with
  | none => exact minMatchStart_none hf _ (max_right_extension_end hw) (match_right_extension hsp)
  | some f =>
    have hm : maxMatchEnd r f.beg = none := by simp [llmatch] at m; exact m f hf
    obtain ⟨u₁, u₂, h₁, -, e⟩ := derives_Cat.mp (minMatchStart_matches hf)
    exact maxMatchEnd_none hm _ (by simp [← e]) h₁

/-- The span returned by `llmatch` is indeed a match for the regex given. -/
theorem llmatch_matches {r : RE α} {sp_out : Span σ} {w : List σ}
  (m : llmatch r w = some sp_out) :
  (sp_out ⊢ r) := by
  obtain ⟨f, -, hm⟩ := llmatch_eq_some.mp m
  exact maxMatchEnd_matches hm
