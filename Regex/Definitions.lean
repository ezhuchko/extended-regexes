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
  | ε
  | Pred (e : α)
  | Alternation (l r : RE)
  | Intersection (l r : RE)
  | Concatenation (l r : RE)
  | Star (r : RE)
  | Negation (r : RE)
  | Lookahead (r : RE)
  | Lookbehind (r : RE)
  | NegLookahead (r : RE)
  | NegLookbehind (r : RE)
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

/-- Reversal function for regular expressions. -/
@[simp]
def RE.reverse (R : RE α) : RE α :=
  match R with
  | ε       => ε
  | Pred φ  => Pred φ
  | l ⋓ r   => l.reverse ⋓ r.reverse
  | l ⋒ r   => l.reverse ⋒ r.reverse
  | l ⬝ r   => r.reverse ⬝ l.reverse
  | .Star r => r.reverse *
  | ~ r     => ~ r.reverse
  | ?= r    => ?<= r.reverse
  | ?<= r   => ?= r.reverse
  | ?! r    => ?<! r.reverse
  | ?<! r   => ?! r.reverse

postfix:max "ʳ" => RE.reverse

/-- Encoding of Star using bounded loops. -/
@[simp]
def RE.repeat_cat (R : RE σ) (n : Nat) : RE σ :=
  match n with
  | 0          => ε
  | Nat.succ n => R ⬝ (repeat_cat R n)

notation f "⁽" n "⁾" => repeat_cat f n

/-- Elementary denotation predicates for (Unicode) characters. -/
instance : Denotation Char Char where
  denote a b := a == b

/-- Helper function to convert strings into regexp literals (string as a sequence of characters) -/
def String.toRE (s : String) : RE (BA Char) :=
  s.toList |>.map (Pred ∘ BA.atom) |>.foldr (· ⬝ ·) ε

/-- Implicit coercion to convert strings to regexp to make them more readable. -/
instance : Coe String (RE (BA Char)) where
  coe := String.toRE

/-- Implicit coercion to convert chars to regexp. -/
instance : Coe Char (RE (BA Char)) where
  coe c := Pred (.atom c)

/-- Helper function to obtain a string as character class. -/
def String.characterClass (s : String) : BA Char :=
  s.toList |>.map .atom |>.foldr .or .bot
