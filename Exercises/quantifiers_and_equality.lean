variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := 
  Iff.intro
    (fun h : ∀ x, p x ∧ q x => 
    ⟨(fun x => (h x).left), (fun x => (h x).right)⟩)
    (fun h : (∀ x, p x) ∧ (∀ x, q x) =>
      fun x : α => ⟨h.left x, h.right x⟩)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := 
  fun h : ∀ x, p x → q x =>
  fun hp : ∀ x, p x => fun x => (h x) (hp x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
  fun h : (∀ x, p x) ∨ (∀ x, q x) => 
  fun x =>
    Or.elim (h)
      (fun hp => Or.inl (hp x))
      (fun hq => Or.inr (hq x))

---------------------------------
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := 
  fun a : α => Iff.intro 
    (fun h : ∀ x : α, r => h a)
    (fun h : r => fun x => h)

open Classical
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := 
  Iff.intro 
    (fun h : ∀ x, p x ∨ r => 
      Or.elim (em r)
        (Or.inr)
        (fun hnr: ¬r => 
          Or.inl ( show ∀ x, p x from
            fun x => 
            Or.elim (h x)
              id
              (fun hr : r => absurd hr hnr))))
    (fun h => fun x =>
      Or.elim h
        (fun h1 : ∀ x, p x => Or.inl (h1 x))
        (Or.inr))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := 
  Iff.intro
    (fun h : ∀ x, r → p x => fun hr => fun x => (h x) hr)
    (fun h : r → ∀ x, p x => fun x => fun hr => (h hr) x)


---------------------------------
section paradox

variable (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false :=
  have hparadox : shaves barber barber ↔ ¬shaves barber barber :=
      h barber
  have hn_self_shave : ¬shaves barber barber :=
    (fun h_self_shave : shaves barber barber =>
      absurd h_self_shave (hparadox.mp h_self_shave))
  absurd (hparadox.mpr hn_self_shave) hn_self_shave

end paradox

---------------------------------
namespace hidden

def divides (m n : Nat) : Prop := ∃ k, m * k = n

def even (n : Nat) : Prop := divides 2 n

-- BEGIN
def prime (n : Nat) : Prop :=
¬∃ m, m > 1 ∧ m < n ∧ divides m n

def infinitely_many_primes : Prop :=
∀ n, ∃ p, p > n ∧ prime p

def Fermat_number (n : Nat) : Prop :=
∃ k : Nat, 2^(2^k) + 1 = n

def Fermat_prime (n : Nat) : Prop :=
prime n ∧ Fermat_number n

def infinitely_many_Fermat_primes : Prop :=
∀ n, ∃ fp, fp > n ∧ Fermat_prime fp

-- Every even integer greater than 2 can be expressed as the sum of two primes
def goldbach_conjecture : Prop :=
∀ n, n > 2 → ∃ p q, p + q = n ∧ prime p ∧ prime q

-- Every odd number greater than 5 can be expressed as the sum of three primes
def Goldbach's_weak_conjecture : Prop :=
∀ n, even n ∧ n > 5 → ∃ p p' p'', p + p' + p'' = n ∧ prime p ∧ prime p' ∧ prime p''

-- no three positive integers a, b, and c satisfy the equation an + bn = cn for
-- any integer value of n greater than 2
def Fermat's_last_theorem : Prop :=
∀ n, n > 2 → ¬∃ a b c, a^n + b^n = c^n ∧ a > 0 ∧ b > 0 ∧ c > 0

-- END

end hidden
------------------------------

open Classical

--variable (α : Type) (p q : α → Prop)
--variable (r : Prop)

example : (∃ x : α, r) → r := 
  fun ⟨x, hr⟩ => hr

example (a : α) : r → (∃ x : α, r) := 
  fun hr => ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := 
  Iff.intro
    (fun ⟨x, hpr⟩ => ⟨⟨x, hpr.left⟩, hpr.right⟩)
    (fun ⟨⟨x, hx⟩, hr⟩ => ⟨x, hx, hr⟩)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := 
  Iff.intro
    (fun ⟨x, (h1 : p x ∨ q x)⟩ =>
      Or.elim h1
        (fun hpx : p x => Or.inl ⟨x, hpx⟩)
        (fun hqx : q x => Or.inr ⟨x, hqx⟩))
    (fun h : (∃ x, p x) ∨ (∃ x, q x) =>
      Or.elim h
        (fun ⟨x, hpx⟩ => ⟨x, (Or.inl hpx)⟩)
        (fun ⟨x, hqx⟩ => ⟨x, (Or.inr hqx)⟩))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := 
  Iff.intro
    (fun hap => fun ⟨x, hnp⟩ => 
      show False from hnp (hap x))
    (fun h : ¬ (∃ x, ¬ p x) =>
      fun x =>
        show p x from
          byContradiction
            (fun hnpx : ¬ p x =>
              show False from h ⟨x, hnpx⟩))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := 
  Iff.intro
    (fun ⟨x, hx⟩ => fun hanp => 
        show False from absurd hx (hanp x))
    (fun nhanp => 
      byContradiction
        (fun nhep => 
          have hanp : ∀ x, ¬ p x := fun x => fun hp => nhep ⟨x, hp⟩
          absurd hanp nhanp))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
    (fun nhep => fun x => fun hx => nhep ⟨x, hx⟩)
    (fun hanp => fun ⟨x, hp⟩ => absurd hp (hanp x))

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := 
  Iff.intro
    (fun nhap => 
      byContradiction
        (fun nhenp => 
          have hap : ∀ x, p x := fun x => 
            show p x from 
              byContradiction
                (fun hnp => nhenp ⟨x, hnp⟩)
          absurd hap nhap))
    (fun ⟨x, hnp⟩ => fun hap => absurd (hap x) hnp)

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := 
  Iff.intro
    (fun hapr => fun ⟨x, hp⟩ => hapr x hp)
    (fun hepr => fun x => fun hp => hepr ⟨x, hp⟩)

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := 
  Iff.intro
    (fun ⟨b, (hb : p b → r)⟩ =>
     fun h2 : ∀ x, p x =>
     show r from  hb (h2 b))
    (fun h1 : (∀ x, p x) → r =>
     show ∃ x, p x → r from
       byCases
         (fun hap : ∀ x, p x => ⟨a, λ h' => h1 hap⟩)
         (fun hnap : ¬ ∀ x, p x =>
          byContradiction
            (fun hnex : ¬ ∃ x, p x → r =>
              have hap : ∀ x, p x :=
                fun x =>
                byContradiction
                  (fun hnp : ¬ p x =>
                    have hex : ∃ x, p x → r := ⟨x, (fun hp => absurd hp hnp)⟩
                    show False from hnex hex)
              show False from hnap hap)))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := 
  Iff.intro
    (fun ⟨a, hrp⟩ => fun hr => ⟨a, (hrp hr)⟩)
    (fun hrep => 
      byCases
        (fun hr =>
          have ⟨a, hp⟩ := hrep hr
          ⟨a, (fun hr => hp)⟩)
        (fun hnr => ⟨a, (fun hr => absurd hr hnr)⟩))