variable (p q r s : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := 
  Iff.intro 
    (fun h : p ∧ q => -- The type of h : p ∧ q can be inferred
        And.intro (h.right) (h.left))
    (fun h : q ∧ p => 
        And.intro (h.right) (h.left))

-- The following proof is from Mathlib4, It's not for beginners.
-- Mathlib4 can be found at 
-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Init/Logic.lean
example : p ∧ q ↔ q ∧ p := ⟨λ ⟨hp, hq⟩ => ⟨hq, hp⟩, λ ⟨hp, hq⟩ => ⟨hq, hp⟩⟩
-- Here we don't provide more proof from Mathlib4, you can find it by yourself.
-- In Chapter *Induction and Recursion*, a technic called pattern matching could simplify those proofs.

example : p ∨ q ↔ q ∨ p := 
  Iff.intro
    (fun h : p ∨ q => 
        Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq))
    (fun h : q ∨ p => 
        Or.elim h (fun hq => Or.inr hq) (fun hp => Or.inl hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := 
  Iff.intro
    (fun h : (p ∧ q) ∧ r => 
        And.intro (h.left.left) (And.intro (h.left.right) (h.right)))
    (fun h : p ∧ (q ∧ r) => 
        And.intro (And.intro (h.left) (h.right.left)) (h.right.right))

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
  Iff.intro
    (fun h : (p ∨ q) ∨ r => 
        Or.elim h 
          (fun hpq => 
            Or.elim hpq 
              (fun hp => Or.inl hp)
              (fun hq => Or.inr (Or.inl hq)))
          (fun hr => Or.inr (Or.inr hr)))
    (fun h : p ∨ (q ∨ r) => 
        Or.elim h 
          (fun hp => Or.inl (Or.inl hp))
          (fun hqr => 
            Or.elim hqr
              (fun hq => Or.inl (Or.inr hq))
              (fun hr => Or.inr hr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp := h.left
      Or.elim (h.right)
        (fun hq => Or.inl ⟨hp, hq⟩)
        (fun hr => Or.inr ⟨hp, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun hpq => ⟨hpq.left, Or.inl hpq.right⟩)
        (fun hpr => ⟨hpr.left, Or.inr hpr.right⟩))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
  Iff.intro
    (fun h : p ∨ (q ∧ r) => 
      Or.elim h 
        (fun hp => 
          have hpq : p ∨ q := Or.inl hp
          have hpr : p ∨ r := Or.inl hp
          ⟨hpq, hpr⟩)
        (fun hqr => 
          have hq := hqr.left
          have hr := hqr.right
          have hpq : p ∨ q := Or.inr hq
          have hpr : p ∨ r := Or.inr hr
          ⟨hpq, hpr⟩))
    (fun h : (p ∨ q) ∧ (p ∨ r) => 
      have hpq := h.left
      have hpr := h.right
      Or.elim hpq 
        (fun hp => Or.inl hp)
        (fun hq => 
          Or.elim hpr
            (fun hp => Or.inl hp)
            (fun hr => Or.inr ⟨hq, hr⟩)))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := 
  Iff.intro
    (fun h : p → (q → r) => 
     fun hpq : p ∧ q => 
      show r from h hpq.left hpq.right)
    (fun h : p ∧ q → r =>
     fun hp => fun hq => 
      show r from h ⟨hp, hq⟩)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
  Iff.intro
    (fun h : (p ∨ q) → r =>
      And.intro
        (fun hp =>
          have hpq := Or.inl hp
          show r from h hpq)
        (fun hq =>
          have hpq := Or.inr hq
          show r from h hpq))
    (fun h : (p → r) ∧ (q → r) =>
      have hpr := h.left
      have hqr := h.right
      fun hpq => 
        show r from 
          Or.elim hpq
            (fun hp => hpr hp)
            (fun hq => hqr hq))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
  Iff.intro
    (fun h : p ∨ q → False =>
      And.intro
        (fun hp =>
          have hpq := Or.inl hp
          show False from h hpq)
        (fun hq =>
          have hpq := Or.inr hq
          show False from h hpq))
    (fun h : (p → False) ∧ (q → False) =>
      have hnp := h.left
      have hnq := h.right
      fun hpq => 
        show False from 
          Or.elim hpq
            (fun hp => hnp hp)
            (fun hq => hnq hq))

example : ¬p ∨ ¬q → ¬(p ∧ q) := 
  fun h : (p → False) ∨ (q → False) =>
  fun hpq => show False from 
    Or.elim h 
      (fun hnp => hnp hpq.left)
      (fun hnq => hnq hpq.right)

example : ¬(p ∧ ¬p) := 
  fun h : p ∧ ¬p => h.right h.left

example : p ∧ ¬q → ¬(p → q) := 
  fun h₁ : p ∧ ¬q =>
  fun h₂ : p → q =>
    have hq := h₂ h₁.left
    show False from h₁.right hq

example : ¬p → (p → q) := 
  fun hnp => fun hp => False.elim (hnp hp)

example : (¬p ∨ q) → (p → q) := 
  fun h : ¬p ∨ q =>
  fun hp => show q from
    Or.elim h
      (fun hnp => False.elim (hnp hp))
      (.) -- q → q , can also use ``id``

example : p ∨ False ↔ p := 
  Iff.intro
    (fun h : p ∨ False =>
    Or.elim h (.) (False.elim .))
    (Or.inl .)

example : p ∧ False ↔ False := 
  Iff.intro
    (fun h : p ∧ False => h.right)
    (False.elim .)

example : (p → q) → (¬q → ¬p) := 
  fun h : p → q => fun hnq => fun hp =>
    show False from hnq (h hp)

--------------------
open Classical

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := 
  fun h : p → r ∨ s => 
    Or.elim (em p)
      (fun hp : p => 
        have hrs : r ∨ s := h hp
        Or.elim hrs
          (fun hr => Or.inl (fun hp => hr))
          (fun hs => Or.inr (fun hp => hs)))
      (fun hnp : ¬p =>
        suffices hpr : p → r from Or.inl hpr
        show (p → r) from
        fun hp : p => absurd hp hnp)

example : ¬(p ∧ q) → ¬p ∨ ¬q := 
  fun h : ¬(p ∧ q) =>
    Or.elim (em p)
      (fun hp : p =>
        Or.inr
          (show ¬q from
            fun hq : q => h ⟨hp, hq⟩))
      (fun hp : ¬p => Or.inl hp)   

example : ¬(p → q) → p ∧ ¬q := 
  fun h : ¬(p → q) =>
    Or.elim (em q)
      (fun hq => 
        suffices hpq : p → q from False.elim (h hpq)
        fun hp : p => hq)
      (fun hnq => 
        Or.elim (em p)
          (fun hp => ⟨hp, hnq⟩)
          (fun hnp =>
            suffices hpq : p → q from False.elim (h hpq)
            fun hp => absurd hp hnp))

example : (p → q) → (¬p ∨ q) := 
  fun hpq : p → q => 
    Or.elim (em p)
      (fun hp => Or.inr (hpq hp))
      (fun hnp => Or.inl hnp)

example : (¬q → ¬p) → (p → q) := 
  fun hqp : ¬q → ¬p => fun hp =>
    byContradiction
      (fun hnq => hqp hnq hp)

example : p ∨ ¬p := em p

example : (((p → q) → p) → p) := 
  fun h : (p → q) → p => 
    show p from 
      Or.elim (em p)
        (.)
        (fun hnp => 
          have hpq : p → q := fun hp => absurd hp hnp
          absurd (h hpq) hnp)

-----------------------
example : ¬(p ↔ ¬p) :=
  fun h : p ↔ ¬p => 
    show False from 
      have h1 : p → ¬p := Iff.mp h
      have h2 : ¬p → p := Iff.mpr h
      have hnp : ¬p := 
        (fun hp : p => absurd hp (h1 hp))
      absurd (h2 hnp) hnp