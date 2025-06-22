import Mathlib.Tactic.Linarith

/--
Main definition of a span.
Note that, semantically speaking, the first component of the span is supposed to be reversed.
However, we do not enforce this in the type, as it would complicate the definition of operations.
Components:
  - left context (reversed)
  - match
  - right context
-/
def Span (σ : Type) := List σ × List σ × List σ

/--
Locations.
Similarly to spans, the first component is supposed to be reversed.
Components:
  - left context (reversed)
  - right context
-/
def Loc (σ : Type) := List σ × List σ

/-
# Operations on Locations
-/

@[simp]
def Loc.left (loc : Loc σ) : List σ := loc.1

-- (sʳ, _)
@[simp]
def Loc.pos (loc : Loc σ) : Nat := loc.1.length

-- (_, v)
@[simp]
def Loc.right (loc : Loc σ) : List σ := loc.2

/-- Entire word represented whose location refers to. -/
@[simp]
def Loc.word (loc : Loc σ) : List σ := loc.left.reverse ++ loc.right

/-- Reversal of locations: notice that the reversal of the word is implicit to the fact that the left is already semantically reversed. -/
@[simp]
def Loc.reverse (loc : Loc σ) : Loc σ :=
  match loc with
  | ⟨s, u⟩ => ⟨u, s⟩

/-- Reversal of locations is an involution. -/
def reverse_loc_involution {loc : Loc σ} : loc.reverse.reverse = loc :=
  match loc with
  | ⟨s, u⟩ => by simp

/-- Consider a location as end location (i.e.: reverse the entire word on the left, have no remaining characters on the right) -/
@[simp]
def List.as_end_location (w : List σ) : Loc σ := ⟨w.reverse, []⟩

/-- Convert a word to a span by having an empty match in the middle. -/
@[simp]
def Loc.as_span (l : Loc σ) : Span σ :=
  ⟨l.1, [], l.2⟩

/-
# Operations on spans
-/

-- (sʳ, u, v)ʳ = (v, uʳ, sʳ)
@[simp]
def Span.reverse (sp : Span σ) : Span σ :=
  match sp with
  | ⟨s, u, v⟩ => ⟨v, u.reverse, s⟩

-- (s, u, v)ʳm = (s, uʳ, v)
@[simp]
def Span.reverse_match (sp : Span σ) : Span σ :=
  match sp with
  | ⟨s, u, v⟩ => ⟨s, u.reverse, v⟩

-- ((sʳ, u, v)ʳ)ʳ = (sʳ, u, v)
@[simp]
theorem reverse_span_involution {sp : Span σ} : sp.reverse.reverse = sp :=
  match sp with
  | ⟨s,u,v⟩ => by simp

-- (s, uʳʳ, v) = (s, u, v)
@[simp]
theorem reverse_match_involution {sp : Span σ} : sp.reverse_match.reverse_match = sp :=
  match sp with
  | ⟨s,u,v⟩ => by simp

/-
## Main accessors for span
-/

/-- (Sʳ, _, _) -/
@[simp]
def Span.left (sp : Span σ) : List σ := sp.1

/-- (_, u, _) -/
@[simp]
def Span.match (sp : Span σ) : List σ := sp.2.1

/-- (_, _, v) -/
@[simp]
def Span.right (sp : Span σ) : List σ := sp.2.2

/-- Everything after the first match position. -/
@[simp]
def Span.after (sp : Span σ) : List σ := sp.match ++ sp.right

/-- Start of the match position. -/
@[simp]
def Span.i (sp : Span σ) : Nat := sp.left.length

/-- End of the match position. -/
@[simp]
def Span.j (sp : Span σ) : Nat := sp.i + sp.match.length

/-- (sʳ, u, v) is the entire word s ++ u ++ v that the span refers to. -/
@[simp]
def Span.word (sp : Span σ) : List σ := sp.left.reverse ++ sp.match ++ sp.right

/-- Increase the match on the left by adding back the last character seen on the left. -/
@[simp]
def Span.increase_match_left (sp : Span σ) : Span σ :=
  match sp with
  | ⟨[], u, v⟩ => ⟨[], u, v⟩
  | ⟨a::s, u, v⟩ => ⟨s, a::u, v⟩

/-- Increasing the match on the left still produces a splitting of the original word. -/
theorem increase_match_left_splitting {sp : Span σ} :
    sp.increase_match_left.word = sp.word :=
  match sp with
  | ⟨[], u, v⟩ => rfl
  | ⟨a::s, u, v⟩ => by simp

/-- The (begin) location view of a span is simply obtained by concatenating
    match and remaining characters, thus forgetting the match length. -/
@[simp]
def Span.beg (sp : Span σ) : List σ × List σ :=
  ⟨sp.left, sp.match ++ sp.right⟩

/-- The (end) location view of a span is obtained by reversing the span, converting it to a begin location and reversing it. -/
@[simp]
def Span.end (sp : Span σ) : List σ × List σ :=
  Loc.reverse (sp.reverse.beg)

/-- Two equivalent ways to express a span's end location. -/
theorem end_loc_equivalence (sp : Span σ) : sp.end = ⟨sp.match.reverse ++ sp.left, sp.right⟩ := by aesop

/-- Take the first character, if not empty. -/
@[simp]
def Span.match_head? (sp : Span σ) : Option σ :=
  let ⟨_,u,_⟩ := sp
  match u with
  | []   => none
  | u::_ => some u

@[simp]
theorem Span.reverse_word {sp : Span σ} :
  sp.word.reverse = sp.reverse.word := by
  match sp with
  | ⟨s,u,v⟩ => simp
