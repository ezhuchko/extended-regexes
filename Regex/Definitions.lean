import Mathlib.Tactic.Linarith
import Mathlib.Data.Prod.Lex
import Mathlib.Order.BooleanAlgebra

/-!
# Main definitions

Contains the definition of regular expressions, effective boolean algebras,
spans and locations and operations on them.
-/

/-- Denotation typeclass, used to equip a boolean algebra with a denotation function. -/
class Denotation (α : Type u) (σ : outParam (Type v)) where
  denote : α → σ → Bool
export Denotation (denote)

/-- Effective boolean algebra typeclass, with laws. -/
class EffectiveBooleanAlgebra (α : Type u) (σ : outParam (Type v))
    extends Denotation α σ, Bot α, Top α, Inf α, Sup α, HasCompl α where
  denote_bot : denote ⊥ c = false
  denote_top : denote ⊤ c = true
  denote_compl : denote aᶜ c = !denote a c
  denote_inf : denote (a ⊓ b) c = (denote a c && denote b c)
  denote_sup : denote (a ⊔ b) c = (denote a c || denote b c)

open EffectiveBooleanAlgebra in
attribute [simp] denote_bot denote_top denote_inf denote_sup denote_compl

/-- Freely generated boolean algebra on a set of predicates. -/
inductive BA (α : Type u)
  | atom (a : α)
  | top | bot
  | and (a b : BA α)
  | or (a b : BA α)
  | not (a : BA α)
  deriving Repr, DecidableEq
open BA

/-- Denotation function induced on the free boolean algebra. -/
protected def BA.denote [Denotation α σ] (c : σ) : BA α → Bool
  | atom a => denote a c
  | not a => !(a.denote c)
  | and a b => a.denote c && b.denote c
  | or a b => a.denote c || b.denote c
  | bot => false
  | top => true

/-- The free boolean algebra is indeed an effective boolean algebra. -/
instance [Denotation α σ] : EffectiveBooleanAlgebra (BA α) σ where
  bot := BA.bot
  top := BA.top
  inf := BA.and
  sup := BA.or
  compl := BA.not
  denote_bot := rfl
  denote_top := rfl
  denote_inf := rfl
  denote_sup := rfl
  denote_compl := rfl
  denote a c := a.denote c

variable (α : Type u) in

/-- Class of regular expressions with lookarounds. -/
inductive RE : Type _ where
  | ε                 : RE
  | Pred (e : α)      : RE
  | Alternation       : RE → RE → RE
  | Intersection      : RE → RE → RE
  | Concatenation     : RE → RE → RE
  | Star              : RE → RE
  | Negation          : RE → RE
  | Lookahead         : RE → RE
  | Lookbehind        : RE → RE
  | NegLookahead      : RE → RE
  | NegLookbehind     : RE → RE
open RE

infixr:35 " ⋓ "  => Alternation
infixr:40 " ⋒ "  => Intersection
infixr:50 " ⬝ "  => Concatenation
postfix:max "*"  => Star
prefix:max "~"   => Negation
prefix:max "?="  => Lookahead
prefix:max "?<=" => Lookbehind
prefix:max "?!"  => NegLookahead
prefix:max "?<!" => NegLookbehind

/-- Size of metric function, counting the number of constructors. -/
@[simp]
def sizeOf_RE (R : RE α) : ℕ :=
  match R with
  | ε      => 0
  | Pred _ => 0
  | l ⋓ r  => 1 + sizeOf_RE l + sizeOf_RE r
  | l ⋒ r  => 1 + sizeOf_RE l + sizeOf_RE r
  | l ⬝ r  => 1 + sizeOf_RE l + sizeOf_RE r
  | r *    => 1 + sizeOf_RE r
  | ~ r    => 1 + sizeOf_RE r
  | ?= r   => 1 + sizeOf_RE r
  | ?<= r  => 1 + sizeOf_RE r
  | ?! r   => 1 + sizeOf_RE r
  | ?<! r  => 1 + sizeOf_RE r

/-- Lookaround height, counting the level of nested applications of lookarounds. -/
@[simp]
def lookaround_height (R : RE α) : ℕ :=
  match R with
  | ε      => 0
  | Pred _ => 0
  | l ⋓ r  => max (lookaround_height l) (lookaround_height r)
  | l ⋒ r  => max (lookaround_height l) (lookaround_height r)
  | l ⬝ r  => max (lookaround_height l) (lookaround_height r)
  | r *    => lookaround_height r
  | ~ r    => lookaround_height r
  | ?= r   => 1 + lookaround_height r
  | ?<= r  => 1 + lookaround_height r
  | ?! r   => 1 + lookaround_height r
  | ?<! r  => 1 + lookaround_height r

/-- Lexicographic combination of star height and size of regexp. -/
@[simp]
def star_metric (R : RE α) : ℕ ×ₗ ℕ :=
  match R with
  | ε       => (0, 0)
  | Pred _  => (0, 0)
  | l ⋓ r   => (max (star_metric l).1 (star_metric r).1, 1 + (star_metric l).2 + (star_metric r).2)
  | l ⋒ r   => (max (star_metric l).1 (star_metric r).1, 1 + (star_metric l).2 + (star_metric r).2)
  | l ⬝ r   => (max (star_metric l).1 (star_metric r).1, 1 + (star_metric l).2 + (star_metric r).2)
  | r *     => (1 + (star_metric r).1, 1 + (star_metric r).2)
  | ~ r     => ((star_metric r).1, 1 + (star_metric r).2)
  | ?= r    => ((star_metric r).1, 1 + (star_metric r).2)
  | ?<= r   => ((star_metric r).1, 1 + (star_metric r).2)
  | ?! r    => ((star_metric r).1, 1 + (star_metric r).2)
  | ?<! r   => ((star_metric r).1, 1 + (star_metric r).2)

instance : WellFoundedRelation (ℕ ×ₗ ℕ) where
  rel := (· < ·)
  wf  := WellFounded.prod_lex WellFoundedRelation.wf WellFoundedRelation.wf

/-- Reversal function for regular expressions. -/
@[simp]
def RE.reverse (R : RE α) : RE α :=
  match R with
  | ε      => ε
  | Pred φ => Pred φ
  | l ⋓ r  => l.reverse ⋓ r.reverse
  | l ⋒ r  => l.reverse ⋒ r.reverse
  | l ⬝ r  => r.reverse ⬝ l.reverse
  | r *    => r.reverse *
  | ~ r    => ~ r.reverse
  | ?= r   => ?<= r.reverse
  | ?<= r  => ?= r.reverse
  | ?! r   => ?<! r.reverse
  | ?<! r  => ?! r.reverse
open RE.reverse

postfix:max "ʳ" => RE.reverse

-- /-- Elementary denotation predicates for (Unicode) characters. -/
instance : Denotation Char Char where
  denote a b := a == b

/-- Helper function to convert strings into regexp literals (string as a sequence of characters) -/
def String.toRE (s : String) : RE (BA Char) :=
  s.toList |>.map (Pred ∘ BA.atom) |>.foldr (· ⬝ ·) ε

/-- Implicit coercion to convert strings to regexp to make them more readable. -/
instance : Coe String (RE (BA Char)) where
  coe := String.toRE

/-- Helper function to obtain a string as character class. -/
def String.characterClass (s : String) : BA Char :=
  s.toList |>.map .atom |>.foldr .or .bot

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
  | ⟨a::s, u, v⟩ => by unfold Span.increase_match_left; simp;

/-- The (begin) location view of a span is simply obtained by concatenating
    match and remaining characters, thus forgetting the match length. -/
@[simp]
def Span.beg (sp : Span σ) : List σ × List σ :=
  ⟨sp.left, sp.match ++ sp.right⟩

/- The (end) location view of a span is obtained by reversing the span, converting it to a begin location and reversing it. -/
@[simp]
def Span.end (sp : Span σ) : List σ × List σ :=
  Loc.reverse (sp.reverse.beg)

/- Two equivalent ways to express a span's end location. -/
theorem end_loc_equivalence (sp : Span σ) : sp.end = ⟨sp.match.reverse ++ sp.left, sp.right⟩ := by aesop

/-- Take the first character, if not empty. -/
@[simp]
def Span.match_head? (sp : Span σ) : Option σ :=
  let ⟨_,u,_⟩ := sp
  match u with
  | []   => none
  | u::_ => some u

/-- Encoding of Star using bounded loops. -/
@[simp]
def repeat_cat (R : RE σ) (n : ℕ) : RE σ :=
  match n with
  | 0          => ε
  | Nat.succ n => R ⬝ (repeat_cat R n)

notation f "⁽" n "⁾" => repeat_cat f n
