import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Order.BooleanAlgebra.Basic

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
    extends Denotation α σ, Bot α, Top α, Min α, Max α, HasCompl α where
  denote_bot : denote ⊥ c = false
  denote_top : denote ⊤ c = true
  denote_compl : denote aᶜ c = !denote a c
  denote_inf : denote (a ⊓ b) c = (denote a c && denote b c)
  denote_sup : denote (a ⊔ b) c = (denote a c || denote b c)

open EffectiveBooleanAlgebra in
attribute [simp] denote_bot denote_top denote_inf denote_sup denote_compl

@[simp]
def modelsEBA (a : σ) (φ : α) [EffectiveBooleanAlgebra α σ] := denote φ a
infixr:40 " ⊨ " => modelsEBA

/-- Freely generated boolean algebra on a set of predicates. -/
inductive BA (α : Type u)
  | atom (a : α)
  | top | bot
  | and (a b : BA α)
  | or (a b : BA α)
  | not (a : BA α)
  deriving Repr, DecidableEq
open BA

-- rename this later
/-- Denotation function induced on the free boolean algebra. -/
protected def BA.denote [Denotation α σ] (c : σ) : BA α → Bool
  | atom a => denote a c -- diff denote
  | not a  => !(a.denote c)
  | and a b => a.denote c && b.denote c
  | or a b  => a.denote c || b.denote c
  | bot => false
  | top => true

/-- The free boolean algebra is indeed an effective boolean algebra. -/
instance [Denotation α σ] : EffectiveBooleanAlgebra (BA α) σ where
  bot := BA.bot
  top := BA.top
  min := BA.and
  max := BA.or
  compl := BA.not
  denote_bot := rfl
  denote_top := rfl
  denote_inf := rfl
  denote_sup := rfl
  denote_compl := rfl
  denote a c := a.denote c
