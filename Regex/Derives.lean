import Regex.Definitions
import Regex.Metrics

open RE BA

/-!
  # Derivatives and derivation relation

  Contains the specification of the derivation relation, which directly uses Bool
  to represent whether a span is a match for a regex.

  The main approach here is to define nullability and derivation of regex with
  respect to the span. The `existsMatch` is defined to represent the existence of a match in the
  lookahead and lookbehind cases.

  The definition is somewhat technical to ensure that it is well-founded, and thus ensure that it is decidable.

  The correctness of the `derives` algorithm then implies that the `Matches` semantics is decidable.

  All three functions terminate by the lexicographic measure
  `(lookaround height of R, characters left to read, size of R, 0 or 1)`.
  The last component is 1 for `existsMatch` and 0 otherwise, so that `existsMatch R x`
  may call `null R x` on the same expression and location.
-/
variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

mutual
  @[simp]
  def null (R : RE α) (x : Loc σ) : Bool :=
    match R with
    | ε       => true
    | Pred _  => false
    | L ⬝ R   => null L x && null R x
    | L ⋓ R   => null L x || null R x
    | L ⋒ R   => null L x && null R x
    | .Star _ => true
    | ~ R     => ¬ null R x
    | ?= R    => existsMatch R x
    | ?<= R   => existsMatch (R ʳ) x.reverse
    | ?! R    => ¬ existsMatch R x
    | ?<! R   => ¬ existsMatch (R ʳ) x.reverse
  termination_by (lookaround_height R, x.right.length, sizeOf R, 0)
  decreasing_by all_goals simp [Prod.lex_def, ← lookaround_height_reverse_RE]; try omega

  @[simp]
  def existsMatch (R : RE α) (x : Loc σ) : Bool :=
    -- How many characters are left to read?
    match x with
    | ⟨s, []⟩    =>
      null R ⟨s, []⟩
    | ⟨s, a::v⟩ =>
      -- the bound on the lookaround height of `R'` is needed for termination
      have ⟨R', _⟩ := der R ⟨s, a::v⟩
      null R ⟨s, a::v⟩ || existsMatch R' ⟨a::s, v⟩
  termination_by (lookaround_height R, x.right.length, sizeOf R, 1)
  decreasing_by all_goals simp [Prod.lex_def]; try omega

  /-- Derivative of a regular expression in a location.
      The subtype records that the derivative has no more nested lookarounds than the
      original expression; `existsMatch` needs this to show that its call on the
      derivative terminates. -/
  @[simp]
  def der (R : RE α) (x : Loc σ) : {r : RE α // lookaround_height r ≤ lookaround_height R} :=
    match R with
    | ε      => ⟨Pred ⊥, Nat.zero_le _⟩
    | Pred φ =>
      match x with
      | ⟨_, a::_⟩ => if a ⊨ φ then ⟨ε, Nat.zero_le _⟩ else ⟨Pred ⊥, Nat.zero_le _⟩
      | ⟨_, []⟩   => ⟨Pred ⊥, Nat.zero_le _⟩
    | L ⬝ R =>
      have := (der L x).2; have := (der R x).2
      if null L x then ⟨der L x ⬝ R ⋓ der R x, by simp; omega⟩
      else ⟨der L x ⬝ R, by simp; omega⟩
    | L ⋓ R =>
      have := (der L x).2; have := (der R x).2
      ⟨der L x ⋓ der R x, by simp; omega⟩
    | L ⋒ R =>
      have := (der L x).2; have := (der R x).2
      ⟨der L x ⋒ der R x, by simp; omega⟩
    | .Star R => have := (der R x).2; ⟨der R x ⬝ R *, by simp; omega⟩
    | ~ R     => ⟨~(der R x), (der R x).2⟩
    | ?= _ | ?<= _ | ?! _ | ?<! _ => ⟨Pred ⊥, Nat.zero_le _⟩
  termination_by (lookaround_height R, x.right.length, sizeOf R, 0)
  decreasing_by all_goals simp [Prod.lex_def]; try omega
end

/-- Main derivation relation, by induction on the match length. -/
@[simp]
def derives (sp : Span σ) (R : RE α) : Bool :=
  match sp with
  | ⟨_, [], _⟩   => null R sp.beg
  | ⟨s, a::u, v⟩ => derives ⟨a::s, u, v⟩ (der R sp.beg)
termination_by sp.mid

infix:40 " ⊢ " => derives
