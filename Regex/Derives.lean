import Regex.Definitions
import Regex.Metrics

open RE
open BA

/-!
# Derivatives and derivation relation

Contains the specification of the derivation relation, which directly uses Bool
to represent whether a span is a match for a regex.

The main approach here is to define nullability and derivation of regex with
respect to the span. The `existsMatch` is defined to represent the existence of a match in the
lookahead and lookbehind cases.

The definition is somewhat technical to ensure that it is
well-founded, and thus ensure that it is decidable.

The correctness of the `derives` algorithm then implies that the `models` semantics is decidable.

We employ a trick on the metric used (`der_termination_metric`) with Nat being either 0/1 to
ensure that existsMatch is prioritized in determining the termination order (see `termination_by`).
-/
variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

mutual
  @[simp]
  def null (R : RE α) (x : Loc σ) : Bool :=
    match R with
    | ε      => true
    | Pred _ => false
    | L ⬝ R  => null L x && null R x
    | L ⋓ R  => null L x || null R x
    | L ⋒ R  => null L x && null R x
    | _ *    => true
    | ~ R    => ¬ null R x
    | ?= R   => existsMatch R x
    | ?<= R  => existsMatch (R ʳ) (x.snd, x.fst)
    | ?! R   => ¬ existsMatch R x
    | ?<! R  => ¬ existsMatch (R ʳ) (x.snd, x.fst)

  @[simp]
  def existsMatch (R : RE α) (x : Loc σ) : Bool :=
    -- How many characters are left to read?
    match x with
    | (s, [])    =>
      null R (s, [])
    | (s, a::v) =>
      have ⟨R', hr'⟩ := der R (s, a::v)
      have : der_termination_metric R' (a :: s, v) 1 < der_termination_metric R (s, a :: v) 1 := der_termination_metric_List_decrease hr'
      null R (s, a::v) || existsMatch R' (a::s, v)

   /-- Derivative of a regular expression in a location.
       Note the use of the subtype to ensure that the height of the derivative is
       less than the height of the original expression. This needs to be coupled in
       the definition of the derivative relation itself to ensure that the mutual
       induction is well-founded, in particular for the `der` call in `existsMatch`.
   -/
   @[simp]
   def der (R : RE α) (x : Loc σ) : {r : RE α // lookaround_height r ≤ lookaround_height R} :=
    match R with
    | ε      => ⟨Pred ⊥, zero_le _⟩
    | Pred φ =>
      match x with
      | (_ , [])   => ⟨Pred ⊥, zero_le _⟩
      | (_ , a::_) =>
        if denote φ a then ⟨ε, zero_le _⟩
        else ⟨Pred ⊥, zero_le _⟩
    | L ⬝ R =>
      if null L x then
        ⟨der L x ⬝ R ⋓ der R x,
         have ⟨g, hg⟩ := der L x;
         have ⟨f, hf⟩ := der R x;
         max_le_iff.mpr ⟨max_le_max_right (lookaround_height R) hg, le_max_of_le_right hf⟩⟩
      else
        ⟨der L x ⬝ R,
        have ⟨g, hg⟩ := der L x;
        max_le_max_right (lookaround_height R) hg⟩
    | L ⋓ R =>
      ⟨der L x ⋓ der R x,
       have ⟨g, hg⟩ := der L x;
       have ⟨f, hf⟩ := der R x;
       max_le_max hg hf⟩
    | L ⋒ R =>
      ⟨der L x ⋒ der R x,
       have ⟨g, hg⟩ := der L x;
       have ⟨f, hf⟩ := der R x;
       max_le_max hg hf⟩
    | R *   =>
      ⟨(der R x) ⬝ R *, have ⟨g, hg⟩ := der R x;
                        by simp; exact hg⟩
    | ~ R   => ⟨~(der R x), (der R x).2⟩
    | ?= _  => ⟨Pred ⊥, zero_le _⟩
    | ?<= _ => ⟨Pred ⊥, zero_le _⟩
    | ?! _  => ⟨Pred ⊥, zero_le _⟩
    | ?<! _ => ⟨Pred ⊥, zero_le _⟩
end
termination_by
  null R x => der_termination_metric R x 0
  existsMatch R x => der_termination_metric R x 1
  der R x => der_termination_metric R x 0
decreasing_by (first | assumption | simp_wf)

/-- Main derivation relation, by induction on the match length. -/
@[simp]
def derives (sp : Span σ) (R : RE α) : Bool :=
  match sp with
  | ⟨_, [], _⟩   => null R sp.beg
  | ⟨s, a::u, v⟩ => derives ⟨a::s, u, v⟩ (der R sp.beg)
termination_by
  derives sp R => sp.2.1

infix:40 " ⊢ " => derives
