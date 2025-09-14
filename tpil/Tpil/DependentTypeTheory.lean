-- def keyword declares new constant symbols
def m : Nat := 1
def n : Nat := 0
def b1 : Bool := true
def b2 : Bool := false

-- #check command asks Lean to report their types
-- #eval command asks Lean to evaluate the given expression

-- #check Nat × Nat → Nat
-- #check Nat.succ
-- #check Nat.add
-- #check (5,9).1

-- types themselves(Nat, Bool) are first-class citizens
def α : Type := Nat
def β : Type := Bool
def F : Type -> Type := List
def G : Type -> Type -> Type := Prod

-- #check G α β
-- #check G α Nat
-- #check Prod α β

-- Type 0 as a universe of "small" or "ordinary" types
-- #check Type 5

-- Polymorphic constants
-- Prod's type: Prod.{u, v} (α : Type u) (β : Type v) : Type (max u v)
-- #check Prod

universe u
def F' (α : Type u) : Type u := Prod α α
-- #check F' -- F'.{u} (α : Type u) : Type u
-- Avoid universe command
def F''.{v} (α : Type v) : Type v := Prod α α

-- fun(or λ) keyword to create a function
-- #check fun (x : Nat) => x + 5
-- #check λ (x : Nat) => x + 5
-- #check fun x => x + 5
-- #check λ x => x + 5

-- Lambda abstraction, create a functon from another expression
def lamAbsF := fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
def lamAbsF' := fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
def lamAbsF'' := fun x y => if not y then x + 1 else x + 2

def double (x: Nat) : Nat := x + x

def compose (α β γ : Type) (g : β → γ) (f : α → β) x := g (f x)

-- let α := t1; t2 means replacing every occurence of α in t2 by t1
-- ; can be omitted when a line break is used
def twice_double (x : Nat) : Nat :=
  let y := x + x
  y * y

def doTwice (α : Type) (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (α : Type) (h : α → α) (x : α) : α :=
  h (h (h x))

-- Declare variables of any type not just Type itself
-- `section` command can be used to limit the scope of a variable
section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose' := g (f x)
  def doTwice' := h (h x)
  def doTrice' := h (h (h x))
end useful

-- Lean provides the ability to group definitions into nested, hiearchical `namespace`
-- unlike section, namspaces always require a name
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
  def ffa : Nat := f (f a)
end Foo
-- `open` command brings the shorter names into the current context
-- especially after declaring import other modules
-- Like section, namespaces can be nested
-- Namespaces that have been closed can latter be reopened, even in another file

-- Dependent arrow(function) type
-- Given α : Type, β : α → Type, (a : α) → β makes sence for any expression β : Type
-- When β depends on α, it denotes a dependent function type
-- When β does not, it does not have any difference from the type α → β
def cons (α : Type) (a : α) (as : List α) : List α := List.cons a as

-- Sigma types (Dependent cartesian product) (a, α) × β a
-- it can also be written as Σ a : α, β a,
-- the dependent pair can be made by using ⟨ ⟩
def f.{v, w} (α : Type v) (β : α → Type w) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩
def g.{v, w} (α : Type v) (β : α → Type w) (a : α) (b : β a) : (a : α) × β a :=
  Sigma.mk a b
def h1 (x : Nat) : Nat :=
  (f Type (fun α => α) Nat x).2
def h2 (x : Nat) : Nat :=
  (g Type (fun α => α) Nat x).2

-- Implicit arguments
-- #check List.cons 0 List.nil
