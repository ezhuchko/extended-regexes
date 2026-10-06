import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Order.BooleanAlgebra.Basic

/-!
# Effective Boolean Algebras for Symbolic Alphabets

This module introduces the `EffectiveBooleanAlgebra` typeclass for symbolic alphabets.
-/

/-- Models typeclass, used to equip a boolean algebra with a models function. -/
class Models (α : Type u) (σ : outParam (Type v)) where
  models : α → σ → Bool
export Models (models)

notation:51 c:52 " ⊨ " p:52 => Models.models p c

/-- Effective boolean algebra typeclass: a type of predicates `α` together with a
computable denotation `models : α → σ → Bool`. -/
class EffectiveBooleanAlgebra (α : Type u) (σ : outParam (Type v))
    extends Models α σ, Bot α, Top α, Min α, Max α, Compl α where
  models_bot : models ⊥ c = false
  models_top : models ⊤ c = true
  models_compl : models aᶜ c = !models a c
  models_min : models (a ⊓ b) c = (models a c && models b c)
  models_max : models (a ⊔ b) c = (models a c || models b c)

open EffectiveBooleanAlgebra in
attribute [simp] models_bot models_top models_min models_max models_compl

/-- Syntax for Boolean predicates equipped with Boolean semantics. -/
inductive BA (α : Type u)
  | atom (a : α)
  | top | bot
  | and (a b : BA α)
  | or (a b : BA α)
  | not (a : BA α)
  deriving Repr, DecidableEq, Hashable
open BA

/-- The Boolean structure lives on the syntax, independent of any denotation for
the atoms. This is what lets `(⊥ : BA α)` elaborate with no `Models α σ` instance in scope. -/
instance : Bot (BA α) := ⟨bot⟩
instance : Top (BA α) := ⟨top⟩
instance : Min (BA α) := ⟨and⟩
instance : Max (BA α) := ⟨or⟩
instance : Compl (BA α) := ⟨not⟩

/-- Models function induced on the term algebra. -/
protected def BA.models [Models α σ] (c : σ) : BA α → Bool
  | atom a => models a c
  | not a  => !(a.models c)
  | and a b => a.models c && b.models c
  | or a b  => a.models c || b.models c
  | bot => false
  | top => true

/-- The term algebra is indeed an effective boolean algebra. -/
instance [Models α σ] : EffectiveBooleanAlgebra (BA α) σ where
  models a c := a.models c
  models_bot := rfl
  models_top := rfl
  models_min := rfl
  models_max := rfl
  models_compl := rfl
