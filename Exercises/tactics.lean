-- There are many possible ways of tactic proofs, 
-- and the following implementations are just FYI.

variable (p q r : Prop)

macro "triv" : tactic => `(
  apply Iff.intro
  <;> intros
  <;> simp [*])
--
theorem And_comm : p ∧ q ↔ q ∧ p := by triv

theorem Or_comm : p ∨ q ↔ q ∨ p := by 
  apply Iff.intro
  . intro
    | Or.inl hp => apply Or.inr; assumption
    | Or.inr hq => apply Or.inl; assumption
  . intro
    | Or.inl hq => apply Or.inr; assumption
    | Or.inr hp => apply Or.inl; assumption

-- 
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by triv

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by 
  apply Iff.intro
  . intro
    | Or.inl hpq => 
      cases hpq with
      | inl hp => apply Or.inl; assumption
      | inr hq => apply Or.inr; apply Or.inl; assumption
    | Or.inr hr => apply Or.inr; apply Or.inr; assumption
  . intro
    | Or.inl hp => apply Or.inl; apply Or.inl; assumption
    | Or.inr hqr =>       
      cases hqr
      . apply Or.inl; apply Or.inr; assumption
      . apply Or.inr; assumption

-- 
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by admit
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by admit
-- 
example : (p → (q → r)) ↔ (p ∧ q → r) := by triv
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry

open Classical

variable (p q r s : Prop)

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry


example : ¬(p ↔ ¬p) := sorry

------------------------------------





------------------------------------
example (p q r : Prop) (hp : p) :
    (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
    simp [*]