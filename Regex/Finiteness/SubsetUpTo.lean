import Mathlib.Order.Defs.Unbundled

/-!
# Definitions of up-to relations

Includes the definitions of `mem_up_to`, `subset_up_to` and `equality_up_to`, as well as
their basic properties.

-/

variable {α : Type _} {R : α → α → Prop}

/-- Defines membership of an element in a list, modulo a relation R. -/
@[simp]
def mem_up_to (R : α → α → Prop) : α → List α → Prop :=
  fun x ys => ∃ y, R x y ∧ y ∈ ys

notation x " ∈[ " R " ] " ys => mem_up_to R x ys

/-- Lifts the notion of set inclusion to lists, modulo a relation R. -/
@[simp]
def subset_up_to (R : α → α → Prop) : List α → List α → Prop :=
  fun xs ys => ∀ x ∈ xs, x ∈[ R ] ys

notation xs " ⊆[ " R " ] " ys => subset_up_to R xs ys

/-- Two lists are equivalent up to R if both are subsets of each other under R. -/
@[simp]
def equality_up_to (R : α → α → Prop) : List α → List α → Prop :=
  fun xs ys => (xs ⊆[ R ] ys) ∧ (ys ⊆[ R ] xs)

notation xs " =[ " R " ] " ys => equality_up_to R xs ys

theorem subset_up_to_refl {xs : List α} (hr : Std.Refl R) :
  xs ⊆[ R ] xs := fun x h => ⟨x,Std.Refl.refl x,h⟩

theorem subset_up_to_trans {xs ys zs : List α} (ht : IsTrans α R)
  (h1 : xs ⊆[ R ] ys) (h2 : ys ⊆[ R ] zs) :
  xs ⊆[ R ] zs :=
  fun r hr =>
  have ⟨g1,g2,g3⟩ := h1 r hr
  have ⟨i1,i2,i3⟩ := h2 g1 g3
  ⟨i1,ht.trans _ _ _ g2 i2,i3⟩

theorem subset_to_subset_up_to {xs ys : List α} (hr : Std.Refl R) (h : xs ⊆ ys) :
  xs ⊆[ R ] ys := fun g g1 => ⟨g,Std.Refl.refl g,h g1⟩

theorem equality_up_to_refl {xs : List α} (hr : Std.Refl R) :
  xs =[ R ] xs := ⟨subset_up_to_refl hr, subset_up_to_refl hr⟩

theorem equality_up_to_symm {xs ys : List α} (h : xs =[ R ] ys) :
  ys =[ R ] xs := ⟨h.2, h.1⟩

theorem equality_up_to_trans {xs ys zs : List α} (ht : IsTrans α R)
  (h1 : xs =[ R ] ys) (h2 : ys =[ R ] zs) :
  xs =[ R ] zs :=
  ⟨subset_up_to_trans ht h1.1 h2.1, subset_up_to_trans ht h2.2 h1.2⟩
