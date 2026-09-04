

-- Making some select imports as necessary because I don't wanna wait for
-- the entire Tactic and Logic module to be integrated
import Mathlib.Logic.ExistsUnique
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Use
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Cases

/-
I wrote most of chapter 2 independently, before referencing Tao's lean
implementation.
It resulted in some minor edits, as well as the entire recursion section, and
me getting around to implementing a typeclass for Peano that I was hoping to.
-/

--------------- SECTION 2.1 EXPERIMENTAL
--- Note: in this section, we'll be using the peano's
---     axioms approach to constructing natural numbers.
--- This approach seems to be somewhat incompatible with
---     Lean's type theoretic system.
--- In Lean, it seems like the correct move is to instead
---     prove the axioms using the inductive MyNat, and
---     Lean's built-in induction.
--- But as an experiment, I'm gonna force the issue anyway.
---     This may cause problems I don't anticipate.

--- Moreover, I've structured these axioms to be as
---     Type-agnostic as possible.
---     After all, I technically don't have it as a prior
---     guarantee that MyNat are the only values that fit
---     isNatural.

--- Maybe there's a way to do it properly, but this is just
---     a learning exercise, so I'm not gonna force it.

namespace experiment

inductive MyNat where
| zero : MyNat
| succ : MyNat → MyNat



--- Convert Lean nats to our nats
def natToMyNat : Nat → MyNat
| 0 => MyNat.zero
| n + 1 => MyNat.succ (natToMyNat n)

/-
Definition 2.1.3. We define 1 to be the number 0++, 2 to be
the number (0++ )++, 3 to be the number ((0++ )++)++,etc. (In
other words, 1 := 0++, 2 := 1 ++, 3 := 2++, etc. In this text I
use "x := y" to denote the statement that xis defined to equal y.)
-/

@[default_instance 200] -- In this file, nat lits are MyNat
instance (n : Nat) : OfNat MyNat n where
ofNat := natToMyNat n


--- Define isNatural as a property
axiom isNatural {α : Type} : α → Prop

--- Axiom 2.1
---     Zero is a natural number.
axiom zero_natural : isNatural 0

--- Axiom 2.2
---     Successors of natural numbers are natural numbers.
axiom succ_natural {α : Type} (succ : α → α) (n : α) :
    isNatural n → isNatural (succ n)

--- Proposition 2.1.4.
---     3 is a natural number.

theorem three_natural : isNatural (3):= by
    repeat apply succ_natural
    exact zero_natural

--- Axiom 2.3
---     If our number is natural, then zero is not its
---     successor.
axiom succ_ne_zero {α : Type}
(succ : α → α) (zero : α) (n : α) :
    isNatural n → succ n ≠ zero

--- Proposition 2.1.6.
---     4 is not equal to 0.
theorem four_neq_zero : (4 ≠ 0) := by
    apply succ_ne_zero
    exact three_natural

--- Axiom 2.4.
---     Different natural numbers must have different
---     successors
axiom succ_inj {α : Type} (succ : α → α) (n m : α) :
    isNatural n ∧ isNatural m →
    n ≠ m → succ n ≠ succ m

--- Proposition 2.1.8.
---     6 is not equal to 2.


theorem six_neq_four : (6 ≠ 2) := by
    -- This one is arduous...
    have nat5 : isNatural 5 := by
        repeat apply succ_natural
        exact zero_natural
    have nat1: isNatural 1 := by
        repeat apply succ_natural
        exact zero_natural
    have nat4 : isNatural 4 := by
        repeat apply succ_natural
        exact zero_natural
    have nat0: isNatural 0 := by
        exact zero_natural

    apply succ_inj

    constructor;
    · apply nat5
    · apply nat1
    apply succ_inj



    constructor
    · apply nat4
    · apply nat0

    exact four_neq_zero

--- Axioms 2.5
---     Axiom 2.5 (Principle of mathematical induction).
---     Let P(n) be any property pertaining to a natural
---     number n. Suppose that P(O) is true, and suppose
---     that whenever P(n) is true, P(n++) is also
---     true. Then P( n) is true for every natural number n.
axiom induction_principle {α : Type} (P : α → Prop)
(zero : α) (succ : α → α) :
    P zero →
    (∀ n : α, isNatural n → P n → P (succ n)) →
    ∀ n : α, isNatural n → P n


--- Assumption 2.6. (Informal) There exists a number system
---     N, whose elements we will call natural numbers,
---     for which Axioms 2.1-2.5 are true.

--- We're reaching the limits of what I know how to do with these
---     axioms in such an aggressively type-independent way.

end experiment




--------------- SECTION 2.1
namespace myNat



inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat
deriving Repr, DecidableEq

--- Convert Lean nats to our nats
def natToMyNat : Nat → MyNat
  | 0 => MyNat.zero
  | n + 1 => MyNat.succ (natToMyNat n)

/-
Definition 2.1.3. We define 1 to be the number 0++, 2 to be
the number (0++ )++, 3 to be the number ((0++ )++)++,etc. (In
other words, 1 := 0++, 2 := 1 ++, 3 := 2++, etc. In this text I
use "x := y" to denote the statement that xis defined to equal y.)
-/
@[default_instance 200] -- In this file, nat lits are MyNat
instance (n : Nat) : OfNat MyNat n where
  ofNat := natToMyNat n

--- This is required because Lean is bad at treating
--- these the same.
@[simp]
theorem ofNat_zero : MyNat.zero = 0 := rfl


-- notation "S" => MyNat.succ
postfix:100 "++" => MyNat.succ -- Switched notation from S to ++
-- because S gets used a lot

-- All 5 of Peano's axioms are essentially built into
-- the inductive type.

-- Axiom 2.1 is satisfied by the inductive definition
-- Axiom 2.2 is satisfied by the inductive definition

--- Axiom 2.3
---     Zero is not the successor of any natural number.
theorem zero_ne_succ (n : MyNat) : 0 ≠ (n++) := by
    intro h
    contradiction

theorem succ_ne_zero (n : MyNat) : (n++) ≠ 0 := by
    intro h
    contradiction

--- Proposition 2.1.6.
---     4 is not equal to 0.
theorem four_neq_zero : (4 ≠ 0) := by
    change 3++ ≠ 0 -- Borrowing this line from Tao's version
    apply succ_ne_zero


--- Axiom 2.4.
---     Different natural numbers must have different
---     successors.
theorem succ_inj {m n : MyNat} : m++ = n++ → m = n := by
  intro h
  -- Use the fact that succ is injective
  injection h

theorem succ_ne_succ {m n : MyNat} : m ≠ n → m++ ≠ n++ := by
  contrapose!
  exact succ_inj

--- Proposition 2.1.8.
---     6 is not equal to 2.

theorem six_neq_four : (6 ≠ 2) := by
  change (5++) ≠  (1++) -- Borrowed from Tao
  change (4++ ++) ≠ (0++ ++) -- Borrowed from Tao
  apply succ_ne_succ
  apply succ_ne_succ
  apply succ_ne_zero


--- Axioms 2.5
---     Axiom 2.5 (Principle of mathematical induction).
---     Let P(n) be any property pertaining to a natural
---     number n. Suppose that P(O) is true, and suppose
---     that whenever P(n) is true, P(n++) is also
---     true. Then P( n) is true for every natural number
theorem induction_principle (P : MyNat → Prop)
    (hbase : P 0)
    (hstep : ∀ n : MyNat, P n → P (n++))
    : ∀ (n : MyNat), P n := by

    intro n
    induction n with
    | zero => exact hbase
    | succ n ih => exact hstep n ih

--- In the future, rather than using the induction_principle
--- theorem directly, we just use Lean's built-in
--- induction syntax.

/-
Proposition 2.1.16 (Recursive definitions). Suppose for each
natuml number n, we have some function fn : N -+ N from
the natuml numbers to the natuml numbers. Let c be a natuml
number. Then we can assign a unique natuml number an to each
natuml number n, such that ao = c and an++ = fn(an) for each
natuml number n.
-/

/-
Honestly, I didn't really know how to do this section.

So the below section is partly copied from
https://github.com/teorth/analysis

In my defense, it felt weird to use functions when the book hasn't
formally defined them.
So I wasn't going to do it without external prompting.


-/

abbrev recurse (f : MyNat → MyNat → MyNat) (c : MyNat) :
MyNat → MyNat :=
fun n ↦ match n with
| 0 => c
| n++ =>
  let f_n := f n -- ∀ natural n, we have fn : N → N
  f_n (recurse f c n)



theorem rec_zero (f : MyNat → MyNat → MyNat) (c : MyNat) :
  recurse f c 0 = c := rfl

theorem rec_succ (f : MyNat → MyNat → MyNat) (c : MyNat) (n : MyNat) :
    recurse f c (n++) = f n (recurse f c n) := rfl

/-
It seems that Tao has chosen to encode the concept

"Then we can assign a unique natural number a_n to each
natural number n, such that..."

as

"There exists a unique function that matches our recurse definition"

If we break this into parts:

* "We can assign... to each natural number" => we can represent such an
assignment with a function.

* "We can assign a *unique natural number*" => if each assignment is unique,
that specifies exactly one function f: MyNat → MyNat
-/

/-
 First: iff a function g follows the properties laid out in the
    recursive definition, it equals that recursive function.

This implementation+proof is almost identical to Tao's: I just went through
the motions for myself to get a feel for what is happening here.
-/

theorem eq_recurse (f : MyNat → MyNat → MyNat) (c : MyNat) (g : MyNat → MyNat) :
    (g 0 = c ∧ ∀ n, g (n++) = f n (g n)) ↔ g = recurse f c := by
  constructor
  · intro ⟨hg0, hgs⟩
    apply funext
    apply induction_principle
    · rw [hg0]
      apply rec_zero f c
    · intro n hgf
      rw [hgs, rec_succ, hgf]
  · intro hgf
    rw [hgf]
    constructor
    · apply rec_zero
    · intro n
      apply rec_succ



/-
Second: there is exactly one function with that matches the properties
laid out in the recursive definition.

Once again, very similar to Tao's proof.
-/
theorem recurse_uniq (f : MyNat → MyNat → MyNat) (c : MyNat) :
    ∃! (a: MyNat → MyNat), a 0 = c ∧ ∀ n, a (n++) = f n (a n) := by
  use recurse f c
  simp
  constructor
  · apply rec_zero
  · intro g hg hn
    apply (eq_recurse f c g).1
    apply And.intro hg hn



/-
Another way to deal with the axiomatic approach to the natural
numbers is to use a typeclass.

Similar once again to Tao, this time I'd somewhat came to
the same idea separately. But my implementation is influenced to be
more consistent with it.
-/

@[ext]
class NaturalNumbers where
  NatType : Type
  zero : NatType  -- Axiom 2.1
  succ : NatType → NatType -- Axiom 2.2
  succ_ne_zero : ∀ (n : NatType), succ n ≠ zero -- Axiom 2.3
  succ_ne_succ : ∀ (n m : NatType), n ≠ m → succ n ≠ succ m -- Axiom 2.4
  induction : ∀ (P : NatType → Prop),
    (P zero) ∧ (∀ n : NatType, P n → P (succ n)) →
    ∀ (n : NatType), P n -- Axiom 2.5





--------------- SECTION 2.2

--- This was the definition of addition I used, because I didn't figure out
--- the recursion section until I read Tao's Lean implementation.
def add (n m : MyNat) : MyNat :=
    match n with
    | 0 => m
    | MyNat.succ n' => ( add n' m )++

--- Allow for the plus sign
instance : Add MyNat where
  add := add



--- To match the textbook, we'll instead express these as
--- theorems, rather than definition.

theorem zero_add (m : MyNat) : 0 + m = m := rfl

theorem succ_add (n m : MyNat) : n++ + m =  (n+m)++:= rfl

--- Lemma 2.2.2. For any natural number n, n + 0 = n.
theorem add_zero (n : MyNat) : n + 0 = n := by
    induction n with
    | zero => simp; rw [zero_add]  -- MyNat.zero + 0 = MyNat.zero by definition
    | succ n' ih =>
        rw [succ_add]  -- S n' + 0 = S (n' + 0)
        rw [ih]        -- = S n' by induction hypothesi

--- Lemma 2.2.3. For any natural numbers n and m,
---     n+ (m++)= (n+m)++.

theorem add_succ (n m : MyNat) : n + m++ = (n+m)++ := by
    induction n with
    | zero => simp; repeat rw [zero_add]
    | succ n' ih =>
        rw [succ_add]
        rw [ih]
        rw [succ_add]

--- Proposition 2.2.4 (Addition is commutative).
---     For any natural numbers n and m, n + m = m + n.

theorem add_comm (n m : MyNat) : n + m = m + n := by
    induction n with
    | zero => simp; rw [zero_add, add_zero]
    | succ n' ih => rw [succ_add, add_succ, ih]

--- Proposition 2.2.5 (Addition is associative). For any natural
--- numbers a, b, c, we have (a+ b)+ c =a+ (b +c).

theorem add_assoc (a b c : MyNat) : a + b + c = a + (b + c) := by
    induction a with
    | zero => simp; repeat rw [zero_add]
    | succ a' ih => rw [succ_add, succ_add, succ_add, ih]

--- Proposition 2.2.6 (Cancellation law). Let a, b, c be natural numbers
--- such that a + b = a + c. Then we have b = c.

theorem add_left_cancel {a b c : MyNat} (h : a + b = a + c) : b = c := by
    induction a with
    | zero => simp at h; rw [zero_add, zero_add] at h; exact h
    | succ a' ih => apply ih
                    apply succ_inj
                    rw [← succ_add, ← succ_add]
                    exact h

theorem add_right_cancel {a b c : MyNat} (h : a + b = c + b) : a = c := by
    apply add_left_cancel
    rw [add_comm b a, add_comm b c]
    exact h


--- Definition 2.2.7 (Positive natural numbers). A natural number
--- n is said to be positive iff it is not equal to 0.

def positive (a : MyNat) : Prop := a ≠ 0

--- Proposition 2.2.8. If a is positive and b is a natural number,
--- then a + b is positive.

theorem pos_add (a b : MyNat) (ha : positive a) : positive (a+b) :=by
    induction b with
    | zero => simp; rw [add_zero]; exact ha
    | succ b' ih => rw [add_succ]; apply succ_ne_zero

theorem add_pos (a b : MyNat) (hb : positive b) : positive (a+b) := by
    rw [add_comm]
    apply pos_add
    exact hb

--- Corollary 2.2.9. If a and bare natural numbers such that a+b =
--- 0, then a = 0 and b = 0.


theorem add_eq_zero {a b : MyNat} : a + b = 0 ↔ a = 0 ∧ b = 0 := by
    constructor
    · intro h;
      constructor
      · by_contra h'; push_neg at h'
        have this:= pos_add a b h'
        contradiction
      · by_contra h'; push_neg at h'
        have this:= add_pos a b h'
        contradiction
    · intro ⟨ha, hb⟩
      rw [ha,hb]
      rw [add_zero]

--- Lemma 2.2.10. Let a be a positive number.
--- Then there exists
--- exactly one natural number b such that b++ =a.

theorem pred_exists_unique {a : MyNat} (ha : positive a) :
  ∃! b : MyNat, b++ = a := by
  induction a with
  | zero => contradiction -- 0 is not
  | succ a' ih =>
    use a'
    constructor
    · change a'++ = (a'++) -- Show a' is a valid soln
      rfl
    · dsimp -- Any valid soln will be equal to a'
      intro y
      apply succ_inj

/-
Definition 2.2.11 (Ordering of the natural numbers). Let n and
m be natural numbers. We say that n is greater than or equal to
m, and write n ;:::: m or m ~ n, iff we have n = m + a for some
natural number a. We say that n is strictly greater than m, and
write n > m or m < n, iff n ;:::: m and n =f. m.
-/

--- instance allows us to use the notation n ≤ m

def le (n m : MyNat) : Prop :=
    ∃a : MyNat, m = n + a

instance : LE MyNat where
  le := le

def lt (n m : MyNat) : Prop :=
    n ≤ m ∧ n ≠ m

instance : LT MyNat where
  lt := lt

/-
Proposition 2.2.12 (Basic properties of order for natural num
bers). Let a, b, c be natural numbers. Then
(a) (Order is reflexive) a ;:::: a.
(b) (Order is transitive) If a ;:::: b and b ;:::: c, then a ;:::: c.
(c) (Order is anti-symmetric) If a ;:::: b and b ;:::: a, then a = b.
(d) (Addition preserves order) a ;:::: b if and only if a+ c ;:::: b +c.
(e) a< b if and only if a++~ b.
(f) a < b if and only if b = a + d for some positive number d.
-/

theorem le_refl (a : MyNat) : a ≤ a := by
    use 0; rw [add_zero]

theorem le_trans {a b c : MyNat} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
    obtain ⟨d, hd⟩  := hab
    obtain ⟨e, he⟩  := hbc
    use d + e
    rw [he, hd]
    rw [add_assoc]

theorem le_antisymm {a b : MyNat} : a ≤ b → b ≤ a → a = b := by
    intro hab hba
    obtain ⟨d, hd⟩ := hab
    obtain ⟨e, he⟩ := hba
    rw [hd] at he
    rw [add_assoc] at he
    nth_rw 1 [← add_zero a] at he
    have:= add_left_cancel he
    have:= this.symm
    have:= add_eq_zero.1 this
    have:= this.left
    rw [this, add_zero] at hd
    rw [hd]


theorem add_le_add_iff_right (a b c : MyNat) : a ≤ b ↔ a + c ≤ b + c := by
    constructor
    · intro ⟨d,hd⟩
      use d
      rw [hd]
      rw [add_assoc, add_assoc]
      rw [add_comm d c]
    · intro ⟨d,hd⟩
      use d
      rw [add_assoc, add_comm c d] at hd
      rw [← add_assoc] at hd
      apply add_right_cancel hd

--- My preferred way to deal with the next theorem is with this lemma.

lemma succ_eq_add_one (a : MyNat) : a++ = a + 1 := by
    have: 1 = (0++) := by rfl
    rw [this, add_succ, add_zero]

lemma lt_succ_self (a : MyNat) : a < a++ := by
    constructor
    · use 1; apply succ_eq_add_one
    · intro h
      rw [succ_eq_add_one, ] at h
      nth_rw 1 [← add_zero a] at h
      have h:= add_left_cancel h.symm
      apply succ_ne_zero
      apply h



theorem lt_iff_add_pos {a b : MyNat} : a < b ↔ ∃ d : MyNat, positive d ∧ b = a + d := by
    /- This whole proof is based on the concept that, with b = a + d,
    a ≠ b ↔ d ≠ 0
    Proof by contradiction both ways, because it's easier to assert
    = than ≠
    -/
    constructor
    · intro ⟨ h1, h2⟩
      obtain ⟨ d, hd⟩ := h1
      use d
      constructor
      · by_contra hpos; unfold positive at hpos; push_neg at hpos
        rw [hpos, add_zero] at hd -- d must be positive, or a=b (contra)
        apply h2 hd.symm

      ·  exact hd

    · intro ⟨ d, hd ⟩
      obtain ⟨ h1, h2 ⟩ := hd
      constructor
      · use d
      · intro hab -- a ≠ b must be true, else d isn't positive (contra)
        rw [hab] at h2
        nth_rw 1 [← add_zero b] at h2
        have h2:= add_left_cancel h2
        exact h1 h2.symm

theorem lt_iff_succ_le {a b : MyNat} : a < b ↔ a++ ≤ b := by
    constructor
    · intro h
      have h':= ( lt_iff_add_pos.1 h )
      obtain ⟨d, h2, h3⟩ := h' -- Positive d in the >= expression
      have := pred_exists_unique h2 -- d is a successor
      obtain ⟨ c, hc1, hc2 ⟩ := this
      use c
      rw [succ_add, ← add_succ, hc1] -- Turn a to S a
      exact h3

    · intro h
      rw [← add_zero (a++) ] at h
      rw [succ_add, ← add_succ] at h
      apply lt_iff_add_pos.2
      obtain ⟨c, hc⟩ := h
      use (0++ + c)
      constructor
      · apply pos_add
        apply succ_ne_zero
      · rw [add_assoc] at hc
        exact hc


-- theorem
--- Some bonus theorems I like:

theorem lt_trans {a b c : MyNat} (hab : a < b) (hbc : b < c) : a < c := by
    apply lt_iff_add_pos.2
    have hab := lt_iff_add_pos.1 hab
    have hbc := lt_iff_add_pos.1 hbc
    obtain ⟨ d, hd1, hd2⟩ := hab
    obtain ⟨ e, he1, he2⟩ := hbc
    use d+e
    constructor
    · apply add_pos; exact he1
    · rw [hd2] at he2
      rw [←  add_assoc]
      exact he2




/-
Proposition 2.2.13 (Trichotomy of order for natural numbers).
Let a and b be natural numbers. Then exactly one of the following
statements is true: a< b, a= b, or a> b.
-/

lemma zero_le (a : MyNat) : 0 ≤ a := by use a; rw [zero_add]

-- ≤ must be either < or =.
lemma lt_or_eq_of_le {a b : MyNat} (hab : a ≤ b) : a < b ∨ a = b := by
    by_cases h': a = b
    · right; exact h'
    · push_neg at h'
      left
      exact And.intro hab h'

lemma le_of_lt_or_eq {a b : MyNat} (hab : a < b ∨ a = b) : a ≤ b := by
  rcases hab with hab | hab
  · exact hab.1
  · use 0; rw [add_zero, hab]

lemma lt_succ_iff_le {a b : MyNat} : a < b++ ↔ a ≤ b := by
  constructor
  · intro h
    have h' := lt_iff_add_pos.1 h -- < gives us a positive number to add
    obtain ⟨ c, hc1, hc2 ⟩ := h'
    have hc1' := pred_exists_unique hc1 -- We can turn into a successor
    obtain ⟨d, hd1, _⟩ := hc1'
    rw [← hd1] at hc2
    rw [add_succ] at hc2
    have hc2' := succ_inj hc2 -- Then erase successor from both sides
    use d -- Instead of Sb we now have b
  · intro h
    have hbsb:= lt_succ_self b
    rcases lt_or_eq_of_le h with h | h | h
    · exact lt_trans h hbsb -- If <, then a < b < S b
    · exact hbsb -- If =, then a = b < S b

lemma eq_zero_of_le_zero {a : MyNat} (h : a ≤ 0) : a = 0 := by
  obtain ⟨ b, hb ⟩ := h
  have := add_eq_zero.1 hb.symm -- Both terms must be 0
  exact this.left


--- Must be at least one
theorem lt_trichotomy (a b : MyNat) : a < b ∨ a = b ∨ a > b := by
    induction a with
    | zero =>
        simp
        rw [← or_assoc]
        left
        have := zero_le b
        exact lt_or_eq_of_le this
    | succ a' ih =>
        rcases ih with h | h | h
        · have := (lt_iff_succ_le).1 h
          rw [← or_assoc]
          left
          exact lt_or_eq_of_le this
        · have:= lt_succ_self a'
          nth_rw 1 [h] at this
          right; right
          simp
          exact this
        · simp at h
          have := lt_succ_self a'
          have := lt_trans h this
          right; right
          simp
          exact this

---Each pair is exclusive
theorem ne_of_lt {a b : MyNat} (hab : a < b) : a ≠ b := hab.2

theorem ne_of_gt {a b : MyNat} (hab : a > b) : a ≠ b := hab.2.symm

theorem lt_asymm {a b : MyNat} (hab : a < b) : ¬ b < a := by
    by_contra h2
    have := le_antisymm hab.1 h2.1 -- Having both means b = a
    exact hab.2 this -- But they both claim this isn't true!


-- We also know that ≥ is the opposite of <, and ≤ is the opposite of >

lemma not_lt_of_ge {a b : MyNat} (hab : a ≤ b) : ¬ b < a := by
  rcases lt_or_eq_of_le hab with hab | hab
  · exact lt_asymm hab
  · intro hba; exact hba.2 hab.symm

lemma not_le_of_gt {a b : MyNat} (hab : a < b) : ¬ b ≤ a := by
  contrapose hab; push_neg at hab; exact not_lt_of_ge hab

lemma gt_of_not_le {a b : MyNat} (hab : ¬ b ≤ a) : a < b := by
  have contra  := le_of_lt_or_eq.mt hab; push_neg at contra
  obtain ⟨  contra1, contra2⟩ := contra
  by_contra contra3
  rcases lt_trichotomy b a with h | h | h
  · contradiction
  · contradiction
  · apply contra3 h

lemma ge_of_not_lt {a b : MyNat} (hab : ¬ a < b) : b ≤ a := by
  contrapose hab; push_neg; exact gt_of_not_le hab

/-
Proposition 2.2.14 (Strong principle of induction). Let mo be
a natural number, and Let P( m) be a property pertaining to an
arbitrary natural number m. Suppose that for each m ~ mo, we
have the following implication: if P( m') is true for all natural
numbers mo ::; m' < m, then P( m) is also true. (In particular,
this means that P(mo) is true, since in this case the hypothesis is
vacuous.) Then we can conclude that P( m) is true for all natural
numbers m~ mo.
-/

lemma not_lt_zero (a : MyNat) : ¬ a < 0:=by
  by_contra h
  obtain ⟨h1,h2⟩ := h
  obtain ⟨x,hx⟩ := h1 -- 0 = a + x
  have h0:= add_eq_zero.1 hx.symm
  exact h2 h0.1

theorem positive_iff_gt_zero (a : MyNat) : positive a ↔ a > 0 := by
  constructor
  · intro h; simp
    have h2 := zero_le a
    exact And.intro h2 h.symm
  · intro ⟨h1,h2⟩
    exact h2.symm

theorem strong_induction {P : MyNat → Prop} {m0 : MyNat}
  (h : ∀ m1 : MyNat, m0 ≤ m1 →
            ((∀ n : MyNat, m0 ≤ n ∧ n < m1 →
                  P n)
            → P m1)) :
  ∀ x : MyNat, m0 ≤ x → P x := by
  intro m1 hm01 -- Get our variable m1 and its bound
  apply h m1 hm01 -- h can give us P m1

  induction m1 with
  | zero =>
    simp
    intro n h1 h2
    exfalso -- 0 can never be the upper bound!
    exact (not_lt_zero n) h2

  | succ m1' ih =>
    simp
    intro n hm0n _

    rcases lt_trichotomy n m1' with ht | ht | ht
    · have ih_req:= le_trans hm0n ht.1 -- n only non-vacuous if m0 ≤ m1'
      apply ih ih_req n -- any desired previous P n stored in ih
      exact And.intro hm0n ht -- Show we're in ih range

    · rw [← ht] at ih
      apply h n hm0n -- We need all previous claims to get our new one
      apply ih hm0n -- Luckily, ih gives us all previous claims

    · have ht := lt_iff_succ_le.1 ht -- If n > m1', not relevant
      have contra := not_lt_of_ge ht -- Can't have both ≤ and >
      contradiction


/-
Exercise 2.2.6. Let n be a natural number, and let P(m) be a property
pertaining to the natural numbers such that whenever P( m++) is true,
then P(m) ·is true. Suppose that P(n) is also true. Prove that P(m)
is true for all natural numbers m :$ n; this is known as the principle of
backwards induction. (Hint: apply induction to the variable n.)
-/

theorem backwards_induction {P : MyNat → Prop} {n : MyNat}
(h0 : P n) (hbi : ∀ (m : MyNat), P (m++) → P m) :
∀ (m : MyNat), m ≤ n → P m := by
  intro m hmn
  induction n with
  | zero => -- P m is true, and m=0, so P 0 must be true
    have heq := eq_zero_of_le_zero hmn
    rw [heq]; exact h0
  | succ n' ih =>

    rcases lt_or_eq_of_le hmn with hlt | heq
    · apply ih -- We fulfill the reqs for the ih
      · exact hbi n' h0 -- One step backwards: S n' to n'
      · apply lt_succ_iff_le.1 hlt -- We're at n' or below

    · rw [heq]; exact h0 -- Base case

/-
Note to future self: check how to invoke strong induction and
backward induction in Lean (similar to simple induction with
the induction command.)-/

--------------- SECTION 2.3

def mul (n m : MyNat) : MyNat :=
    match n with
    | 0 => 0
    | MyNat.succ n' => (mul n' m) + m

--- Allow for the * sign
instance : Mul MyNat where
  mul := mul

/-
Lemma 2.3.2 (Multiplication is commutative). Let n, m be nat
uml numbers. Then n x m = m x n.
-/

lemma zero_mul (m : MyNat) : 0 * m = 0 := rfl

lemma succ_mul (n m : MyNat) : (n++) * m = (n * m) + m := rfl

lemma mul_zero (n : MyNat) : n * 0 = 0 := by
  induction n with
  | zero => simp; exact zero_mul 0
  | succ n' ih => rw [succ_mul,ih]; exact add_zero 0

lemma mul_succ (n m : MyNat) : n * (m++) = (n * m) + n := by
  induction n with
  | zero => simp; rw [zero_mul, zero_mul]; exact add_zero 0
  | succ n' ih => rw [succ_mul, ih, succ_mul]
                  rw [add_succ, add_succ]
                  rw [add_assoc, add_comm n' m]
                  rw [← add_assoc]

theorem mul_comm (n m : MyNat) : n * m = m * n := by
  induction n with
  | zero => simp; rw [zero_mul, mul_zero]
  | succ n' ih => rw [mul_succ, succ_mul, ih]

/-
Lemma 2.3.3 (Natural numbers have no zero divisors). Let n, m
be natuml numbers. Then n x m = 0 if and only if at least one of
n, m is equal to zero.
-/

lemma exists_eq_succ_of_ne_zero {n : MyNat} (h : n ≠ 0) :
∃ (k : MyNat), n = k++ := by
  induction n with
  |zero => contradiction
  |succ n' ih => use n'

theorem zero_eq_mul (n m : MyNat) : n * m = 0 ↔ n = 0 ∨ m = 0 := by
  constructor
  · intro h; by_contra contra; push_neg at contra
    obtain ⟨h1,h2⟩ := contra
    obtain ⟨a,ha⟩ := exists_eq_succ_of_ne_zero h1
    obtain ⟨b,hb⟩ := exists_eq_succ_of_ne_zero h2
    rw [ha,hb] at h
    rw [succ_mul,add_succ] at h
    apply succ_ne_zero
    apply h

  · intro h
    rcases h with h | h
    · rw [h]; apply zero_mul
    · rw [h]; apply mul_zero

/-
In particular, if n and m are both positive,
then nm is also positive.
-/

lemma mul_pos {n m : MyNat} : positive n → positive m → positive (n*m) := by
  have := (zero_eq_mul n m).1.mt
  push_neg at this
  unfold positive
  simp at this
  exact this

/-
Proposition 2.3.4 (Distributive law). For any natuml numbers
a, b, c, we have a(b +c) = ab+ ac and (b + c)a = ba +ea.
-/

theorem left_distrib {a b c : MyNat} : a*(b+c) = a*b+a*c := by
  induction c with
  |zero => simp; rw [add_zero, mul_zero, add_zero]
  |succ c' ih => rw [add_succ, mul_succ, mul_succ]
                 rw [← add_assoc, ih]

theorem right_distrib {a b c : MyNat} : (b+c)*a = b*a+c*a:= by
  rw [mul_comm, mul_comm b a, mul_comm c a]
  exact left_distrib

/-
Proposition 2.3.5 (Multiplication is associative). For any nat
uml numbers a, b, c, we have (a x b) x c =a x (b x c).
-/

theorem mul_assoc {a b c : MyNat} : (a*b)*c = a*(b*c) := by
  induction a with
  |zero => simp; rw [zero_mul, zero_mul, zero_mul]
  |succ a' ih => rw [succ_mul, succ_mul]
                 rw [right_distrib]
                 rw [ih]

/-
Proposition 2.3.6 (Multiplication preserves order). If a, b are
natuml numbers1
such that a < b, and c is positive, then ac < be.
-/

theorem mul_lt_mul_of_pos_right {a b c : MyNat} (hab : a < b) (hc : positive c) :
a * c < b * c := by
  have:= lt_iff_add_pos.1 hab
  obtain ⟨d,hd1, hd2⟩ := this

  constructor
  · use d*c; rw [← right_distrib, hd2] -- Instead of adding d, we add d*c
  · rw [hd2, right_distrib]
    nth_rw 1 [←  add_zero (a*c)]
    intro contra
    have:= add_left_cancel contra -- If ac = bc, then dc must be 0
    have hpos := mul_pos hd1 hc -- But d and c are both positive
    apply hpos this.symm -- Contradiction


/-
Corollary 2.3. 7 (Cancellation law). Let a, b, e be natuml numbers
such that ac =bc and c is non-zero. Then a= b.
-/

theorem mul_cancel_right {a b c : MyNat} (h : a * c = b * c) (hc : positive c) :
a = b := by
  rcases lt_trichotomy a b with hab | hab | hab -- If a<b or a>b, then ac ≠ bc
  · exfalso
    have habc:= mul_lt_mul_of_pos_right hab hc
    exact habc.2 h
  · exact hab
  · exfalso
    simp at hab
    have habc:= mul_lt_mul_of_pos_right hab hc
    exact habc.2 h.symm

/-
Proposition 2.3.9 . (Euclidean algorithm). Let n be a natuml
number, and let q be a positive number. Then there exist natuml
numbers m, r such that 0 :S r < q and n = mq + r.
-/

-- The official theorems related to this seem to use n / q and n % q, which
-- are not defined here. So, we'll treat this as its own theorem.
theorem euclid_algorithm {n q : MyNat} (hq : positive q) :
∃ (m r : MyNat), (0 ≤ r ∧ r < q ∧ n = m * q + r):= by
  induction n with
  | zero =>
    use 0; use 0
    constructor
    · apply zero_le 0
    constructor
    · apply (positive_iff_gt_zero q).1 hq
    · simp; rw [zero_mul, add_zero]
  | succ n' ih =>
    obtain ⟨m, r, hr, hrq, hih⟩ := ih
    by_cases h : (r++) < q -- In this case, we just increment r, and leave m alone
    · use m; use (r++)
      constructor
      · apply zero_le ((r++))
      constructor
      · exact h
      · rw [add_succ, hih]
    · use m++; use 0
      constructor
      · apply zero_le 0
      constructor
      · exact (positive_iff_gt_zero q).1 hq
      · rw [add_zero]
        have hSrge := ge_of_not_lt h
        have hSrle := lt_iff_succ_le.1 hrq
        have hSrq := le_antisymm hSrge hSrle
        -- We're showing that incrementing n' can either increase r by one
        -- Or decrease r by q-1, and increase m*q by 1
        rw [succ_mul] -- Our "r" term went from q-1 to q, which is why loop to 0
        rw [hih]
        rw [← add_succ, hSrq] -- So, we just have to add 1 to r, to get +q


def pow (m n : MyNat) : MyNat :=
    match n with
    | 0 => 1
    | MyNat.succ n' => (pow m n') * m

--- Allow for the ^ sign
instance : Pow MyNat MyNat where
  pow := pow

theorem pow_zero (m : MyNat) : m^0 = 1 := rfl

theorem pow_succ (m n : MyNat) : m^(n++) = (m^n)*m := rfl



end myNat
