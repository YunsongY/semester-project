section universalQuantifier
-- ∀ x: α, p x is nothing more than alternative notation
-- for (x : α) → p
example (α : Type) (p q : α → Prop) :
  (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
    fun h : ∀ x : α, p x ∧ q x =>
    fun y : α =>
    show p y from (h y).left
-- we can show the relation r is transitive
variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀x y z, r x y → r y z → r x z)
-- some arguments can be written as implicit
-- however the disadvantage is that Lean does not have enough
-- information to infer the types of arguments in the expression
variable (trans_r : ∀{x y z}, r x y → r y z → r x z)
variable (a b c : α)
variable (hab : r a b) (hbc : r b c)
-- #check trans_r

-- dependent arrow types has its own typing rule
-- suppose we have α : Sort i and β : Sort j
-- where β may depend on a variable x : α then
-- (x : α) → β is an element of Sort (imax i j)
-- the reason behind this is
--  1. suppose j is not 0, then (x : α) → β is an element
--  of Sort (max i j)
--  2. suppose j is 0, then β is an element of Prop, hence
--  (x : α) → β is an element of Prop as well, which can be
--  interpreted as ∀ (x : α), β
end universalQuantifier

section equality
-- -- Eq.refl, Eq.symm, Eq.trans are three fundamental properties of equality
-- #check Eq.refl
-- #check Eq.symm
-- #check Eq.trans
universe u
-- .{u} tells Lean to instantiate the constans at the universe u
-- #check @Eq.refl.{u}
-- #check @Eq.symm.{u}
-- #check @Eq.trans.{u}

variable (α β: Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd
example : a = d := (hab.trans hcb.symm).trans hcd

example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _
-- library defines a notation rfl for Eq.refl _
example : 2 + 3 = 5 := rfl
-- Equality is much more than an equivalence relation
-- `Eq.subst` can replace the equality formula in another hypothesis
example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2
-- ▸ is a replacement of Eq.subst
-- however, ▸ has more power than Eq.subst
example (a b : α) (p : α → Prop) (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2

-- the following three commands are designed to deal with applicaitve terms
-- `congrArg` can be used to replace the argument
-- `congrFun` can be used to replace the term that is being applied
-- `congr` can be used to replace both at once
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)
example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁

-- Lean's library contains a large number of common identities
variable (a b c : Nat)

example : a + 0 = a := Nat.add_zero a
example : 0 + a = a := Nat.zero_add a
example : a * 1 = a := Nat.mul_one a
example : 1 * a = a := Nat.one_mul a
example : a + b = b + a := Nat.add_comm a b
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
example : a * b = b * a := Nat.mul_comm a b
example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c
-- example of a calculation in the natural numbers
example (x y : Nat) :
    (x + y) * (x + y) =
    x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm
end equality


section calculationalProofs
-- a calculational proof is just a chain of intermediate results
-- that are meant to be composed by basic principles
-- `calc` is a keyword to start a calculational proof
variable (a b c d e : Nat)
theorem T
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d) : a = e :=
calc
  a = b := h1
  _ = c + 1 := h2
  _ = d + 1 := congrArg Nat.succ h3
  _ = 1 + d := Nat.add_comm d 1
  _ = e := Eq.symm h4
-- we can use `simp` and `rw` tactics to improve effect
-- `rw` tactic uses a given equality to "rewrite" the goal
-- if doing so reduces the goal to an identity t = t
-- the tactic applies reflexivity to prove it
theorem T'
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d) : a = e :=
calc
  a = b := by rw [h1]
  _ = c + 1 := by rw [h2]
  _ = d + 1 := by rw [h3]
  _ = 1 + d := by rw [Nat.add_comm]
  _ = e := by rw [h4]
theorem T''
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d) :
  a = e :=
  by rw [h1, h2, h3, Nat.add_comm, h4]
-- `simp` tactic rewrites the goal by applying the given identities
-- repeatedly in any order, anywhere they are applicable in a term
theorem T'''
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d) :
  a = e :=
  by simp [h1, h2, h3, Nat.add_comm, h4]
-- `calc` commands can be configured for any relation that supports
-- some form of transitivity
variable (a b c d : Nat)
example (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d := h3

-- adding new instances of `Trans` type class can teach
-- `calc` new transitivity theorems
def divides (x y : Nat) : Prop :=
  ∃ k, k * x = y

def divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨k₁, d₁⟩ := h₁
  let ⟨k₂, d₂⟩ := h₂
  ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩

def divides_mul (x : Nat) (k : Nat) : divides x (k*x) :=
  ⟨k, rfl⟩

instance : Trans divides divides divides where
  trans := divides_trans

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    divides x y     := h₁
    _ = z           := h₂
    divides _ (2*z) := divides_mul ..

infix:50 " | " => divides

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    x | y   := h₁
    _ = z   := h₂
    _ | 2*z := divides_mul ..
-- with `calc`, the proof in the last section can be written in a more
-- natural and perspicuous way
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
      by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y :=
      by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y) :=
      by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y :=
      by rw [←Nat.add_assoc]
-- here the left arrow tells rewrite the use the identity in the
-- opposite direction
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc]
end calculationalProofs

section existentialQuantifier
-- library includes both an introduction rule and elimination rule
-- the introduction rule is straightforward: to prove ∃ x : α, p x
-- it suffices to provide a suitable term t and a proof of p t
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h
example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h
example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)
-- we can also use the anonymous constructor notation ⟨t, h⟩ for
-- Exists.intro t h
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  ⟨1, h⟩
example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃w, x < w ∧ w < z :=
  ⟨y, hxy, hyz⟩

variable (g : Nat → Nat → Nat)

-- multiple cases for ⟨⟩
set_option pp.explicit true  -- display implicit arguments
theorem gex1 (hg : g 0 0 = 0) : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 (hg : g 0 0 = 0) : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 (hg : g 0 0 = 0) : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 (hg : g 0 0 = 0) : ∃ x, g x x = 0 := ⟨0, hg⟩

-- existential elimination rule, `Exists.elim` allows us to
-- prove a proposition q from ∃ x : α, p x
variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
      fun hw : p w ∧ q w =>
      show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)
-- the difference between the existential proposition and sigma type
-- 1. existential propositions are propositions,
--    Exists.intro a h has type (∃ x : α, p x) : Prop
-- 2. sigma types are types, Sigma.mk a h' has type (Σ x : α, β x)
-- a more convenient way to eliminate from an existential quantifier
-- with `match ` expression:
example (h: ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩
-- we can even use the match statement to decompose the conjunction
example (h: ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩
-- Lean also provides a pattern-match `let` expression:
example (h: ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩
-- Lean also allows us to use an implicit match in the `fun` expression
example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

def IsEven (a : Nat) := ∃ b, a = 2 * b
theorem even_plus_even (h1 : IsEven a) (h2 : IsEven b) :
    IsEven (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ =>
    ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩

-- constructive "or" is stronger than the classical "or",
-- the constructive "exists" stronger than the classical "exists"
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _ : α, r) → r :=
  fun ⟨_, p⟩ => p
example (a : α) : r → (∃ _ : α, r) :=
  fun hr => ⟨a, hr⟩
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (fun ⟨w, hpr⟩ => And.intro ⟨w, hpr.left⟩ hpr.right)
    (fun ⟨⟨w, hp⟩, hr⟩ => ⟨w, And.intro hp hr⟩)
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun ⟨w, hpq⟩ => hpq.elim (fun hp => Or.inl ⟨w, hp⟩) (fun hq => Or.inr ⟨w, hq⟩))
    (fun h => h.elim (fun ⟨w, hp⟩ => ⟨w,  Or.inl hp⟩) (fun ⟨w, hq⟩ => ⟨w, Or.inr hq⟩))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (fun hp => fun ⟨x, np⟩ => np (hp x))
    (fun h => byContradiction
      (fun nh => h (not_forall.mp nh)))
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
    (fun ⟨w, hp⟩ => fun h => h w hp)
    (fun h => byContradiction
      (fun nh => h (not_exists.mp nh)))
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
    (fun nh => byContradiction
      (fun nfh => nh (not_forall_not.mp nfh)))
    (fun h => fun ⟨w, hp⟩ => (h w) hp)
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h => byContradiction
      (fun nh => h (not_exists_not.mp nh)))
    (fun ⟨w, np⟩ => fun h => np (h w))

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (fun h => fun ⟨w, hp⟩ => (h w) hp)
    (fun h => show ∀ x, p x -> r from byCases
      (fun hep => fun _ => fun _ => h hep)
      (fun hnep => fun x => fun hx => absurd ⟨x, hx⟩ hnep))
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨w, hpr⟩ => fun h => hpr (h w))
    (fun h => byCases
      (fun hap => ⟨a, fun _ => h hap⟩)
      (fun hnap => byContradiction
        fun hnepr => have hap  := fun x =>
            byContradiction (fun hnp : ¬p x =>
              have hepr := ⟨x, fun hp => False.elim (hnp hp)⟩
              hnepr hepr)
          hnap hap))
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (fun ⟨w, hrp⟩ => fun r => ⟨w,  hrp r⟩)
    (fun h => byCases
      (fun hr => have ⟨w, hp⟩ := h hr
        ⟨w, fun _ => hp⟩)
      (fun hnr => ⟨a, fun hr' => absurd hr' hnr⟩))
end existentialQuantifier

section moreOnProof
-- `have` expressions to introduce an auxiliary goal
-- without having to label it. we can refer to the
-- last expression introduced in this way using `this`
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans this (h 1)
  show f 0 ≤ f 3 from Nat.le_trans this (h 2)

-- when the goal can be inferred, we can also ask Lean
-- instead to fill in the proof by writing `by assumption`
example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
  show f 0 ≤ f 3 from Nat.le_trans (by assumption) (h 2)

-- we can also ask Lean to fill in the proof by writting ‹ ›
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
  fun _ : f 0 ≥ f 1 =>
  fun _ : f 1 ≥ f 2 =>
  have : f 0 ≥ f 2 := Nat.le_trans ‹f 1 ≥ f 2› ‹f 0 ≥ f 1›
  have : f 0 ≤ f 2 := Nat.le_trans (h 0) (h 1)
  show f 0 = f 2 from Nat.le_antisymm this ‹f 0 ≥ f 2›
end moreOnProof

section exercise
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (fun hpq => And.intro (fun x => (hpq x).left) (fun hp => (hpq hp).right))
    (fun hpq => fun x => And.intro (hpq.left x) (hpq.right x))
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun hpq hp => fun x =>  hpq x (hp x)
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun hpq => hpq.elim
    (fun hp => fun x => Or.inl (hp x))
    (fun hq => fun x => Or.inr (hq x))
-- (∀ x, p x ∨ q x) → (∀ x, p x) ∨ (∀ x, q x) fails,
-- x can holds p or q, but we can never say
-- forall x holds p or forall x holds q, it is restricted on parameter order

open Classical
example : α → ((∀ _ : α, r) ↔ r) :=
  fun x => Iff.intro (fun h => h x) (fun hr => (fun _ => hr))
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (fun h => byCases
      (fun hr => Or.inr hr)
      (fun hnr => Or.inl (fun x =>
          (h x).elim
            (fun hp => hp)
            (fun hr => absurd hr hnr))))
    (fun hpr => hpr.elim
      (fun hp => fun x => Or.inl (hp x))
      (fun hr => fun _ => Or.inr hr))
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (fun h hr hx => h hx hr)
    (fun h hx hr => h hr hx)

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  byCases
  (fun hself => have h_barber := h barber
    h_barber.mp hself hself)
  (fun nhself => have h_barber := h barber
     nhself (h_barber.mpr nhself))

def even (n : Nat) : Prop :=
  ∃ k, n = 2 * k

def prime (n : Nat) : Prop :=
  n > 1 ∧ ¬ ∃ k : Nat, k ≠ 1 ∧ k ≠ n ∧ k ∣ n

def infinitely_many_primes : Prop :=
  ∀ N : Nat, ∃ p : Nat, p > N ∧ prime p

def Fermat_prime (n : Nat) : Prop :=
  prime n ∧ ∃ k, n = 2^(2^k) + 1

def infinitely_many_Fermat_primes : Prop :=
  ∀ N : Nat, ∃ p : Nat, p > N ∧ Fermat_prime p

def goldbach_conjecture : Prop :=
  ∀ n : Nat, n > 2 ∧ even n →
    ∃ n1 n2 : Nat, prime n1 ∧ prime n2 ∧ n = n1 + n2

def Goldbach's_weak_conjecture : Prop :=
  ∀ n : Nat, n > 5 ∧ ¬ even n →
    ∃ n1 n2 n3 : Nat, prime n1 ∧ prime n2 ∧ prime n3 ∧ n = n1 + n2 + n3

def Fermat's_last_theorem : Prop :=
  ∀ n : Nat, n > 2 →
    ¬∃ a b c : Nat, a > 0 ∧ b > 0 ∧ c > 0 ∧ a^n + b^n = c^n
end exercise
