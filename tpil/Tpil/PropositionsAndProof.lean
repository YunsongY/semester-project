section propositionsAsTypes

def Implies (p q : Prop) : Prop := p → q
structure Proof (p : Prop) : Type where
  proof : p

variable (p q r : Prop)
-- #check And p q
-- #check Implies (And p q) (And q p)
-- #check Prop -- Prop : Type

axiom and_commut (p q : Prop) : Proof (Implies (And p q)  (And q p))
-- #check and_commut p q

axiom modus_ponens (p q : Prop) :
  Proof (Implies p q) → Proof p →
  Proof q

axiom implies_intro (p q : Prop) :
  (Proof p → Proof q) → Proof (Implies p q)

-- However, we can interpret p : Prop as a type
-- which means we can read t : p as the assertion that t is a proof of p
-- approach followed in the **Calculus of Constructions**

-- Moreover, the type Prop is syntactic sugar for Sort 0
-- Type u is also syntactic sugar for Sort (u + 1)
end propositionsAsTypes

section workingWithPaT
set_option linter.unusedVariables false

-- `theorem` command introduces a new theorem
variable {p : Prop}
variable {q : Prop}
theorem t1 : p → q → p :=
  fun hp : p => fun hq : q => hp
-- has no difference from fun x : α => fun y : β => x except for the type
-- #print t1

-- with `show` statement, we can specify the type of the final term hp
theorem t1' : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp

-- the lambda-abstracted variables can alos be moved to left of the colon
theorem t1'' (hp : p) (hq : q) : p := hp

-- `axiom` declaration postulates the existence of an element of the given type
axiom hp : p
-- then theorem t1 just as a function application
theorem t2 : q → p := t1 hp

-- however, `axiom` may compromise logical consistency
axiom unsound : False
-- everything follows from False
theorem ex : 1 = 0 := False.elim unsound

-- we can also rewrite theorem t1 as
theorem t1''' {p q : Prop} (hp : p) (hq : q) : p := hp
-- #print t1'''
theorem t1'''': ∀ {p q : Prop}, p → q → p :=
  fun {p q : Prop} (hp : p) (hq : q) => hp

variable (p q r s: Prop)
theorem t2' (h₁ : q →  r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)

end workingWithPaT

section propositionalLogic

variable (p q : Prop)
-- #check p → q → p ∧ q
-- #check ¬ p → p ↔ False
-- #check p ∨ q → q ∨ p

section Conjuction
  -- `example` command states a theorem without naming it or
  -- storing it in the permanent context
  example (hp : p) (hq : q) : p ∧ q := And.intro hp hq
  example (h : p ∧ q) : p := And.left h
  example (h : p ∧ q) : q := And.right h
  example (h : p ∧ q) : q ∧ p :=
    And.intro (And.right h) (And.left h)
  -- ⟨ ⟩ is anonymous constructor
  variable (hp : p) (hq : q)
  -- #check (⟨hp, hq⟩ : p ∧ q)

  -- Given an inductive type Foo, the notation
  -- e.bar is shorthand for Foo.bar e
  variable (xs : List Nat)
  -- #check List.length xs
  -- #check xs.length
  -- As a result, the sample proof can be rewritten as follows:
  example (h : p ∧ q) : q ∧ p :=
    ⟨h.right, h.left⟩
  -- Lean also allows to flatten nested constructor that associate to the right
  example (h : p ∧ q) : q ∧ p ∧ q :=
    ⟨h.right, h.left, h.right⟩
end Conjuction

section Disjunction
  variable (p q : Prop)
  example (hp : p) : p ∨ q := Or.intro_left q hp
  example (hq : q) : p ∨ q := Or.intro_right p hq

  -- or-elimination rule(Or.elim takes three arguments)
  -- Or.elim (p ∨ q) → (p → r) → (q → r)
  example (h : p ∨ q) : q ∨ p :=
    Or.elim h
      (fun hp : p =>
        show q ∨ p from Or.intro_right q hp)
      (fun hq : q =>
        show q ∨ p from Or.intro_left p hq)
  -- in most cases, the first argument of Or.intro_right and
  -- Or.intro_left can be inferred automatically, hence we
  -- can utilize Or.inr and Or.inl
  example (h : p ∨ q) : q ∨ p :=
    Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)
end Disjunction

section negationAndFalsity
  variable (p q r: Prop)
  example (hpq : p → q) (hnq : ¬q) : ¬p :=
    fun hp : p =>
    show False from hnq (hpq hp)

  -- False has a single elimination rule `False.elim`
  -- which expresses that fact that anything follows from a contradiction
  example (hp : p) (hnp : ¬p) : q :=
    False.elim (hnp hp)

  -- `absurd` is used to derive an arbitrary fact from contradictory hypothesis
  example (hp : p) (hnp : ¬p) : q :=
    absurd hp hnp
  example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
    absurd (hqp hq) hnp

  -- False has only an elimination rule, Ture has only an introduction rule
  -- `True.intro : True`
end negationAndFalsity

section logicalEquiv
  -- `Iff.intro` produces a proof p ↔ q from h1 : p → q and h2 : q → p
  -- `Iff.mp` produces a proof of p → q from h : p ↔ q
  -- `Iff.mpr` produces a proof of q → p from h : p ↔ q
  variable (p q r : Prop)
  theorem and_swap : p ∧ q ↔ q ∧ p :=
    Iff.intro
      (fun h : p ∧ q =>
        show q ∧ p from And.intro (And.right h) (And.left h))
      (fun h : q ∧ p =>
        show p ∧ q from And.intro (And.right h) (And.left h))
  example (h: p ∧ q) : q ∧ p := Iff.mp (and_swap p q) h
end logicalEquiv

end propositionalLogic

section introducingAuxSub
variable (p q : Prop)
-- `have` h : p := s; t produces the term (fun (h : p) => t) s
example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp

-- Lean also supports a structured way of reasoning backwards from
-- a goal, which models the "suffices to show" construction in ordinary
-- mathematics
example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from And.right h
end introducingAuxSub

section classicalLogic
open Classical
variable (p q : Prop)
-- #check em p
-- double-negation elimination
theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

example (h : ¬¬p) : p :=
  byCases
    (fun h1 : p => h1)
    (fun h1 : ¬p => absurd h1 h)

example (h : ¬¬p) : p :=
  byContradiction
    (fun h1 : ¬p =>
      show False from h h1)

example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (fun hp : p =>
      Or.inr
        (show ¬q from
          fun hq : q =>
            h ⟨hp, hq⟩))
    (fun hnp : ¬p =>
      Or.inl hnp)
end classicalLogic

section exampleOfPropoValid
-- `sorry` can produces a proof of anything, or provides
-- an object of any data types at all.
-- it can be used for incremental programming
open Classical
-- distributivity
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim (h.right)
        (fun hq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
      (fun hpq : p ∧ q =>
        have hp : p := hpq.left
        have hq : q := hpq.right
        show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
      (fun hpr : p ∧ r =>
        have hp : p := hpr.left
        have hr : r := hpr.right
        show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))
-- an example that requires classical reasoning
example (p q : Prop) : ¬(p ∧ ¬q) → (p → q) :=
  fun h : ¬(p ∧ ¬q) =>
  fun hp : p =>
  show q from
    Or.elim (em q)
      (fun hq : q => hq)
      (fun hnq : ¬q => absurd (And.intro hp hnq) h)
end exampleOfPropoValid

section exercise
variable (p q r : Prop)

-- commutattivity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun hpq => And.intro hpq.right hpq.left)
    (fun hqp => And.intro hqp.right hqp.left)
example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun hpq => hpq.elim Or.inr Or.inl)
    (fun hqp => hqp.elim Or.inr Or.inl)

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun hpqr => And.intro hpqr.left.left (And.intro hpqr.left.right hpqr.right))
    (fun hpqr => And.intro (And.intro hpqr.left hpqr.right.left) hpqr.right.right)
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h => h.elim (fun hpq => hpq.elim Or.inl (Or.inr ∘ Or.inl)) (Or.inr ∘ Or.inr))
    (fun h => h.elim (Or.inl ∘ Or.inl) (fun hqr => hqr.elim (Or.inl ∘ Or.inr) Or.inr))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h => h.right.elim
      (fun hq => Or.inl ⟨h.left, hq⟩)
      (fun hr => Or.inr ⟨h.left, hr⟩))
    (fun h => h.elim
      (fun hpq => ⟨hpq.left, Or.inl hpq.right⟩)
      (fun hpr => ⟨hpr.left, Or.inr hpr.right⟩))
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun h => h.elim
      (fun hp => And.intro (Or.inl hp) (Or.inl hp))
      (fun hqr => And.intro (Or.inr hqr.left) (Or.inr hqr.right)))
    (fun h => h.left.elim
      (fun hp => Or.inl hp)
      (fun hq => h.right.elim
        (fun hp => Or.inl hp)
        (fun hr => Or.inr (And.intro hq hr))))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun h => fun hpq => h hpq.left hpq.right)
    (fun h => fun hp => fun hq => h (And.intro hp hq))
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun h => And.intro (fun hp => h (Or.inl hp)) (fun hq => h (Or.inr hq)) )
    (fun h => fun hpq => hpq.elim (fun hp => h.left hp) (fun hq => h.right hq))
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun h => And.intro (fun fp => h (Or.inl fp)) (fun fq => h (Or.inr fq)))
    (fun h => fun fpq => fpq.elim (fun hp => h.left hp) (fun hq => h.right hq))
example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun hfpfq => fun hpq =>
    hfpfq.elim (fun fp => fp hpq.left) (fun fq => fq hpq.right)
example : ¬(p ∧ ¬p) :=
  fun hpfp => hpfp.right hpfp.left
example : p ∧ ¬q → ¬(p → q) :=
  fun hpfq => fun h => hpfq.right (h hpfq.left)
example : ¬p → (p → q) :=
  fun fp => fun hp => show q from absurd hp fp
example : (¬p ∨ q) → (p → q) :=
  fun hnpq => fun hp => hnpq.elim (fun np => show q from absurd hp np) (fun q => q)
example : p ∨ False ↔ p :=
  Iff.intro
    (fun h => h.elim (fun hp => hp) (fun fls => False.elim fls))
    (fun hp => Or.inl hp)
example : p ∧ False ↔ False :=
  Iff.intro
    (fun h => h.right)
    (fun fls => False.elim fls)
example : (p → q) → (¬q → ¬p) :=
  fun h => fun nq => fun hp => nq (h hp)

open Classical
variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun h => byCases
    (fun hpq => Or.inl hpq)
    (fun hnpq => Or.inr (fun hp => (h hp).elim
      (fun hq => absurd (fun _ => hq) hnpq)
      (fun hr => hr)))
example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun h => byCases
    (fun hnp => Or.inl hnp)
    (fun hp => Or.inr (fun hq => h (And.intro (not_not.mp hp) hq)))
example : ¬(p → q) → p ∧ ¬q :=
  fun h => And.intro
    (byContradiction (fun np => h (fun hp => absurd hp np)))
    (fun hq => h (fun _ => hq))
example : (p → q) → (¬p ∨ q) :=
  fun h => byCases
    (fun hnp => Or.inl hnp)
    (fun hp => Or.inr (h (not_not.mp hp)))
example : (¬q → ¬p) → (p → q) :=
  fun h hp => byContradiction (fun nq => (h nq) hp)
example : p ∨ ¬p :=
  byCases (fun hp => Or.inl hp) (fun np => Or.inr np)
example : (((p → q) → p) → p) :=
  fun h => byCases
    (fun hp => hp)
    (fun np => h (fun hp => absurd hp np))
example : ¬(p ↔ ¬p) :=
  fun h =>
    let hp := h.mpr (fun hp' => h.mp hp' hp')
    h.mp hp hp
end exercise
