--------------- SECTION 2.1

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

--- These chunks allow us to use 0,1,2,3, in MyNat objects.
instance : OfNat MyNat (nat_lit 0) where
  ofNat := MyNat.zero

instance [OfNat MyNat n] : OfNat MyNat (n + 1) where
  ofNat := MyNat.succ (OfNat.ofNat n)

-- Define isNatural as a property
axiom isNatural : MyNat → Prop

--- Axiom 2.1
axiom zero_natural : isNatural MyNat.zero

--- Axiom 2.2
axiom succ_natural : ∀ n, isNatural n → isNatural (MyNat.succ n)

-- Example theorems

theorem one_natural : isNatural (1):= by
    have h1 : isNatural 0 := zero_natural
    exact (succ_natural 0 h1)

theorem two_natural : isNatural (2):= by
    have h1 : isNatural 1 := one_natural
    exact (succ_natural 1 h1)

--- Proposition 2.1.4

theorem three_natural : isNatural (3):= by
    have h1 : isNatural 2 := two_natural
    apply succ_natural 2
    apply h1

--- Axiom 2.3
axiom succ_not_zero : ∀ n, isNatural n → MyNat.succ n ≠ 0

--- Proposition 2.1.6
theorem four_neq_zero : (4 : MyNat) ≠ (0: MyNat) := by
    have h1: isNatural 3 := three_natural
    have h2: MyNat.succ (3) ≠ 0 := succ_not_zero 3 h1
    have h3: 4 = MyNat.succ 3 := rfl
    rw [h3]

--- Axiom 2.4
axiom succ_inj : ∀ n m, isNatural n → isNatural m → MyNat.succ n = MyNat.succ m → n = m


theorem four_natural : isNatural 4 := by
    have h1 : isNatural 3 := three_natural
    apply succ_natural 3 h1

theorem five_natural : isNatural 5 := by
    have h1 : isNatural 4 := four_natural
    apply succ_natural 4 h1

--- Proposition 2.1.8
theorem six_neq_four: 6 ≠ 2 := by
    intro h
    have  h1: 5 = 1 := succ_inj 5 1 five_natural one_natural h
    have  h2: 4 = 0 := succ_inj 4 0 four_natural zero_natural h1
    have  h3: False := four_neq_zero h2
    exact h3

--- Axiom 2.5

axiom induction : ∀ P : Nat → Prop,
P 0 → (∀ n, P n → P (n.succ)) → ∀ n, P n






--------------- SECTION 2.2

--- Definition 2.2.1
def add (x y : Nat) : Nat :=
    match x with
    | 0 => y
    | MyNat.succ x' => MyNat.succ (add x' y)

--- Lemma 2.2.2
theorem add_zero (n : Nat) : add n 0 = n := by
    have h1: add 0 0 = 0 := rfl

    have h2: ∀ m, add m 0 = m → add m.succ 0 = m.succ := by
        intro m
        intro h
        have h1: add m.succ 0 = MyNat.succ (add m 0) := rfl
        rw [h1,h]

    have h3: ∀ m, add m 0 = m := by
        apply induction
        exact h1
        exact h2
    exact h3 n

-- I'm gonna use built-in induction from now one for convenience.
