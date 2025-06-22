import Mathlib.Data.Prod.Lex
import Regex.EBA
import Regex.Span

/-!
# Main definitions

Contains the definition of regular expressions and some operations on them.
-/

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
  deriving DecidableEq, Repr
open RE

infixr:55 " ⋓ "  => Alternation
infixr:60 " ⋒ "  => Intersection
infixr:65 " ⬝ "  => Concatenation
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

postfix:max "ʳ" => RE.reverse

/-- Encoding of Star using bounded loops. -/
@[simp]
def repeat_cat (R : RE σ) (n : ℕ) : RE σ :=
  match n with
  | 0          => ε
  | Nat.succ n => R ⬝ (repeat_cat R n)

notation f "⁽" n "⁾" => repeat_cat f n

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
