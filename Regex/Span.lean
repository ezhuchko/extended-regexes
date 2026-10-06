/-!
# Locations and spans

A location is a position in a word, and a span is a segment of a word. Both store the part of
the word to the left of them reversed, so that moving one character to the right is a `cons`.
-/

/-- A position in a word. -/
structure Loc (σ : Type) where
  /-- The characters before the position, reversed. -/
  left : List σ
  /-- The characters after the position. -/
  right : List σ
  deriving Repr

/-- A segment of a word, i.e. the match of a regex in it. -/
structure Span (σ : Type) where
  /-- The characters before the match, reversed. -/
  left : List σ
  /-- The matched characters. -/
  mid : List σ
  /-- The characters after the match. -/
  right : List σ
  deriving Repr

/-! ### Operations on locations -/

/-- The entire word a location refers to. -/
@[simp]
def Loc.word (loc : Loc σ) : List σ := loc.left.reverse ++ loc.right

/-- The same position in the reversed word. -/
@[simp]
def Loc.reverse (loc : Loc σ) : Loc σ := ⟨loc.right, loc.left⟩

@[simp]
theorem Loc.reverse_reverse {loc : Loc σ} : loc.reverse.reverse = loc := rfl

@[simp]
theorem Loc.reverse_inj {l₁ l₂ : Loc σ} : l₁.reverse = l₂.reverse ↔ l₁ = l₂ := by
  obtain ⟨_, _⟩ := l₁; obtain ⟨_, _⟩ := l₂; simp [and_comm]

theorem Loc.reverse_eq_iff {l₁ l₂ : Loc σ} : l₁.reverse = l₂ ↔ l₁ = l₂.reverse := by
  rw [← Loc.reverse_inj, Loc.reverse_reverse]

/-- The end of the word `w`. -/
@[simp]
def List.as_end_location (w : List σ) : Loc σ := ⟨w.reverse, []⟩

/-- The empty span at a location. -/
@[simp]
def Loc.as_span (l : Loc σ) : Span σ := ⟨l.left, [], l.right⟩

/-! ### Operations on spans -/

/-- The same segment in the reversed word. -/
@[simp]
def Span.reverse (sp : Span σ) : Span σ := ⟨sp.right, sp.mid.reverse, sp.left⟩

@[simp]
theorem reverse_span_involution {sp : Span σ} : sp.reverse.reverse = sp := by
  obtain ⟨_, _, _⟩ := sp; simp

/-- Start of the match position. -/
@[simp]
def Span.i (sp : Span σ) : Nat := sp.left.length

/-- The entire word a span refers to. -/
@[simp]
def Span.word (sp : Span σ) : List σ := sp.left.reverse ++ sp.mid ++ sp.right

/-- Increase the match on the left by adding back the last character seen on the left. -/
@[simp]
def Span.increase_match_left (sp : Span σ) : Span σ :=
  match sp with
  | ⟨[], u, v⟩ => ⟨[], u, v⟩
  | ⟨a::s, u, v⟩ => ⟨s, a::u, v⟩

/-- The location where a span begins. -/
@[simp]
def Span.beg (sp : Span σ) : Loc σ := ⟨sp.left, sp.mid ++ sp.right⟩

/-- The location where a span ends. -/
@[simp]
def Span.end (sp : Span σ) : Loc σ := ⟨sp.mid.reverse ++ sp.left, sp.right⟩

/-! ### Reversal swaps beginning and end -/

theorem Span.mid_reverse {sp : Span σ} : sp.reverse.mid = sp.mid.reverse := rfl

theorem Span.beg_reverse {sp : Span σ} : sp.reverse.beg = sp.end.reverse := rfl

theorem Span.end_reverse {sp : Span σ} : sp.reverse.end = sp.beg.reverse := by
  obtain ⟨s, u, v⟩ := sp; simp

/-- An empty span begins where it ends. -/
theorem Span.end_eq_beg {sp : Span σ} (h : sp.mid = []) : sp.end = sp.beg := by
  obtain ⟨s, u, v⟩ := sp; simp_all

/-- Quantifying over spans is the same as quantifying over their reversals. -/
theorem Span.exists_reverse {p : Span σ → Prop} : (∃ sp, p sp) ↔ ∃ sp : Span σ, p sp.reverse :=
  ⟨fun ⟨sp, h⟩ => ⟨sp.reverse, by rwa [reverse_span_involution]⟩, fun ⟨_, h⟩ => ⟨_, h⟩⟩

@[simp]
theorem Span.reverse_word {sp : Span σ} : sp.word.reverse = sp.reverse.word := by
  obtain ⟨s, u, v⟩ := sp; simp
