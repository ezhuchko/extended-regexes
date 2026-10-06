import Batteries.Data.List.Basic
import Init.Data.List.Lemmas
import Aesop
import Mathlib.Data.List.Monad

/-!
# Order-preserving deduplication of lists

`smartDedup` keeps the first occurrence of each element, in order.
-/

variable {α : Type _}

section Dedup
variable [BEq α]

/-- Remove every occurrence of `x` (`List.erase` removes only the first). -/
def List.eraseAll (x : α) (xs : List α) : List α :=
  xs.filter (· != x)

/-- Push `x` onto `xs`, keeping only this occurrence of it. -/
def List.addErase (x : α) (xs : List α) : List α :=
  x :: xs.eraseAll x

/-- Left-biased union: the elements of `xs` and then of `ys`, first occurrence wins. -/
def allAddErase (xs ys : List α) : List α :=
  xs.foldr List.addErase ys

/-- Deduplication keeping the first occurrence of each element. -/
def smartDedup (xs : List α) : List α :=
  xs.foldr List.addErase []

theorem smartDedup_eq_allAddErase (xs : List α) : smartDedup xs = allAddErase xs [] := rfl

@[simp] theorem eraseAll_nil (x : α) : List.eraseAll x [] = [] := rfl

@[simp] theorem allAddErase_nil_left (ys : List α) : allAddErase [] ys = ys := rfl

@[simp] theorem smartDedup_nil : smartDedup ([] : List α) = [] := rfl

theorem allAddErase_cons (x : α) (xs ys : List α) :
    allAddErase (x :: xs) ys = List.addErase x (allAddErase xs ys) := rfl

/-- Deduplicating a cons gives a cons with the same head. -/
theorem smartDedup_cons {x : α} {xs : List α} :
    smartDedup (x :: xs) = x :: List.eraseAll x (smartDedup xs) := rfl

theorem smartDedup_ne_nil {xs : List α} (h : xs ≠ []) : smartDedup xs ≠ [] := by
  match xs with
  | _ :: _ => exact List.cons_ne_nil _ _

section LawfulBEq
variable [LawfulBEq α]

/-! ### `eraseAll` -/

@[simp] theorem mem_eraseAll_iff (x y : α) (xs : List α) :
    x ∈ xs.eraseAll y ↔ x ∈ xs ∧ x ≠ y := by
  simp [List.eraseAll]

theorem eraseAll_cons_self {x : α} {xs : List α} :
    List.eraseAll x (x :: xs) = List.eraseAll x xs := by
  simp [List.eraseAll]

theorem eraseAll_cons_of_ne {x i : α} {xs : List α} (h : x ≠ i) :
    List.eraseAll x (i :: xs) = i :: List.eraseAll x xs := by
  simp [List.eraseAll, Ne.symm h]

/-! ### `allAddErase` -/

theorem mem_allAddErase_iff (x : α) (xs ys : List α) :
    x ∈ allAddErase xs ys ↔ x ∈ xs ∨ x ∈ ys := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    simp only [allAddErase_cons, List.addErase, List.mem_cons, mem_eraseAll_iff, ih]
    grind

/-! ### `smartDedup` -/

@[simp] theorem mem_smartDedup_iff (x : α) (xs : List α) : x ∈ smartDedup xs ↔ x ∈ xs := by
  simp [smartDedup_eq_allAddErase, mem_allAddErase_iff]

theorem smartDedup_nodup {xs : List α} : (smartDedup xs).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [smartDedup_cons, List.nodup_cons, List.eraseAll]
    exact ⟨by simp, ih.filter _⟩

end LawfulBEq

end Dedup
