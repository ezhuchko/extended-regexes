import Regex.Definitions
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Sublists

/-!
# Transition terms

Collection of all definitions and theorems about transition terms.

-/

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

open List

/-- Transition terms where `α` is the type of the alphabet and
    `β` is the type of leaves which represents the language of the automata. -/
inductive TTerm (α β : Type) : Type where
  | Leaf : β → TTerm α β
  | Node (condition : α) (_then : TTerm α β) (_else : TTerm α β) : TTerm α β
  deriving Repr, DecidableEq
open TTerm

/-- Identity element for `TTerm`, placing a value into a leaf. -/
@[simp]
def TTerm.pure (b : β) : TTerm α β := TTerm.Leaf b

/-- Flatten a nested `TTerm`. -/
@[simp]
def TTerm.join (b : TTerm α (TTerm α β)) : TTerm α β :=
  match b with
  | Leaf b => b
  | Node p f g => Node p (join f) (join g)

/-- Apply a function to each leaf of a `TTerm`. -/
@[simp]
def TTerm.fmap (f : β → γ) (b : TTerm α β) : TTerm α γ :=
  match b with
  | Leaf b => pure (f b)
  | Node p a b => Node p (fmap f a) (fmap f b)

@[simp]
theorem TTerm.fmap_id (b : TTerm α β) : fmap id b = b :=
  match b with
  | Leaf b => rfl
  | Node p a b => by simp only [fmap, TTerm.fmap_id a, TTerm.fmap_id b]

@[simp]
theorem TTerm.fmap_compose (f : β → γ) (g : γ → δ) (b : TTerm α β) :
  fmap (g ∘ f) b = fmap g (fmap f b) :=
  match b with
  | Leaf b => rfl
  | Node p a b => by
    simp only [fmap]
    rw[TTerm.fmap_compose f g a, TTerm.fmap_compose f g b]

/-- Bind operation for `TTerm`, replacing leaves with new `TTerm`s. -/
@[simp]
def TTerm.bind (f : β → TTerm α γ) : TTerm α β → TTerm α γ :=
  fun b => join (fmap f b)

/-- `TTerm` forms a `Monad`. -/
instance : Monad (TTerm α) where
  pure {β : Type} (b : β) := pure b
  bind q e := join (fmap e q)

def lift_unary (op : β → β') (g : TTerm α β) : TTerm α β' := fmap op g

def lift_binary (op : β → β → β') (l r : TTerm α β) : TTerm α β' :=
  bind (fun x => lift_unary (op x) r) l

/-- Collect all leaves of a `TTerm`. -/
@[simp]
def leaves : TTerm α β → List β
  | Leaf r     => [r]
  | Node _ f g => leaves f ++ leaves g

@[simp]
theorem leaves_unary (op : β → β) (g : TTerm α β) :
  leaves (lift_unary op g) = map op (leaves g) :=
  match g with
  | Leaf g     => rfl
  | Node _ f g => by
    simp only [leaves, map_append]
    rw[←leaves_unary op f,←leaves_unary op g]
    rfl

/-- Compute the Cartesian product of `xs` and `ys`, then apply `op` to each pair. -/
@[simp]
def List.productWith (op : α -> α -> α) (xs ys : List α) : List α :=
  map (Function.uncurry op) (product xs ys)

theorem mem_productWith {op : α → α → α} {xs ys : List α} {e : α} :
  e ∈ productWith op xs ys ↔ ∃ x ∈ xs, ∃ y ∈ ys, e = op x y := by
  simp only [productWith, mem_map, Prod.exists, pair_mem_product, Function.uncurry_apply_pair]
  aesop

@[simp]
theorem leaves_fmap : leaves (fmap op g) = map op (leaves g) := by
  match g with
  | Leaf r     => rfl
  | Node _ f g =>
    simp only [leaves, fmap]
    rw[leaves_fmap, leaves_fmap]
    exact Eq.symm map_append

/-- `productWith` distributes over list append. -/
@[simp]
theorem productWith_append :
  productWith op (leaves ff ++ leaves gg) (leaves g) =
  productWith op (leaves ff) (leaves g) ++ productWith op (leaves gg) (leaves g) := by
  simp only [productWith, product, List.flatMap_append, map_append]

@[simp]
theorem leaves_binary (op : β → β → β) (f g : TTerm α β) :
  leaves (lift_binary op f g) = productWith op (leaves f) (leaves g) := by
  match f with
  | Leaf r     =>
    simp only [lift_binary, TTerm.bind, fmap, TTerm.pure, lift_unary, productWith, leaves]
    match g with
    | Leaf s     =>
      simp only [fmap, product, leaves]; rfl
    | Node p f g =>
      simp only [leaves, leaves_fmap, product, map_append, flatMap_cons, flatMap_nil,
                 append_nil, map_map, TTerm.join, fmap, leaves_fmap]; rfl
  | Node pp ff gg =>
    simp only [leaves, productWith_append]
    simp only [←(leaves_binary op ff g), ←(leaves_binary op gg g)]; rfl

/- Apply `op` to each leaf in a `TTerm`. -/
@[simp]
def lift_unary_join (op : β → TTerm α β) (r : TTerm α β) : TTerm α β :=
  match r with
  | Leaf r     => op r
  | Node p f g => Node p (lift_unary_join op f) (lift_unary_join op g)

@[simp]
theorem leaves_lift_unary_join (op : β → TTerm α β) (g : TTerm α β) :
  leaves (lift_unary_join op g) = List.flatten (map (leaves ∘ op) (leaves g)) := by
  match g with
  | Leaf g     =>
    simp only [lift_unary_join, leaves, map_cons, Function.comp_apply, map_nil, flatten_cons,
      flatten_nil, append_nil]
  | Node _ f g =>
    simp only [lift_unary_join, leaves, map_append, flatten_append]
    simp only [leaves_lift_unary_join]
