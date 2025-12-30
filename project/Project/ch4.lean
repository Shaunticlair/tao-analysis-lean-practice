import Mathlib.Logic.ExistsUnique
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Use
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Tauto
import Mathlib.Order.Notation
import Mathlib.Logic.Embedding.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Qify

import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Order.Ring.InjSurj
import Mathlib.Algebra.Order.Hom.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Ring.Rat
import Mathlib.Algebra.Order.Field.Basic

import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic

--import Mathlib.Algebra.Order.Ring.InjSurj
--import Mathlib.Algebra.Order.Ring.Defs
-- import Init.Prelude

--import Project
import Project.ExistsUnique

-- Only necessary so I don't see some yellow lines
set_option linter.unusedVariables false
set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.unusedSectionVars false

--------------- SECTION 4.1 ---------------

def Rat.Close (ε : ℚ) (x y:ℚ) := |x-y| ≤ ε

namespace Chapter4_1

structure PreInt where
  minuend : ℕ
  subtrahend : ℕ

/-- Definition 4.1.1 -/
instance PreInt.instSetoid : Setoid PreInt where
  r a b := a.minuend + b.subtrahend = b.minuend + a.subtrahend
  iseqv := {
    refl := by intro x; rfl
    symm := by intro a b h; symm; exact h
    trans := by
      -- This proof is written to follow the structure of the original text.
      intro ⟨ a,b ⟩ ⟨ c,d ⟩ ⟨ e,f ⟩ h1 h2; simp_all
      have h3 := congrArg₂ (· + ·) h1 h2; simp at h3
      have := calc
        (a + f) + (c + d) = a + d + (c + f) := by abel
        _ = c + b + (e + d) := h3
        _ = (e + b) + (c + d) := by abel
      exact Nat.add_right_cancel this
    }

-- Equality simp
@[simp]
theorem PreInt.eq (a b c d:ℕ) : (⟨ a,b ⟩: PreInt) ≈ ⟨ c,d ⟩ ↔ a + d = c + b := by rfl

-- Allow us to use Setoid equality as normal equality
abbrev Int := Quotient PreInt.instSetoid

-- Convert nat pair into a preint, then into an int (using quotient, since it has a setoid)
abbrev Int.formalDiff (a b:ℕ)  : Int := Quotient.mk PreInt.instSetoid ⟨ a,b ⟩

infix:100 " —— " => Int.formalDiff

/-- Definition 4.1.1 (Integers) -/
-- Quotient.exact and Quotient.sound are the two directions of the iff arrow
theorem Int.eq (a b c d:ℕ): a —— b = c —— d ↔ a + d = c + b :=
  ⟨ Quotient.exact, by intro h; exact Quotient.sound h ⟩

/-- Decidability of equality -/
instance Int.decidableEq : DecidableEq Int := by
  intro a b
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n = Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    rw [eq]
    exact decEq _ _
  exact Quotient.recOnSubsingleton₂ a b this

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq_diff (n:Int) : ∃ a b, n = a —— b := by
apply n.ind _; intro ⟨ a, b ⟩; use a, b

/-- Lemma 4.1.3 (Addition well-defined) -/
instance Int.instAdd : Add Int where
  add := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a+c) —— (b+d) ) (by
    -- If (a,b) ~ (a',b') and (c,d) ~ (c',d')
    -- Then (a,b) + (c,d) = (a',b') + (c',d')
    -- (Obeys substitution: x ~ y implies f(x) ~ f(y))
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    simp [Setoid.r] at *
    calc
      _ = (a+b') + (c+d') := by abel
      _ = (a'+b) + (c'+d) := by rw [h1,h2]
      _ = _ := by abel)

/-- Definition 4.1.2 (Definition of addition) -/
theorem Int.add_eq (a b c d:ℕ) : a —— b + c —— d = (a+c)——(b+d) := Quotient.lift₂_mk _ _ _ _
-- Quotient.lift₂_mk seems to say that we can apply the function to the elements which
-- are inside Quotient.mk, rather than the Quotient itself

-- We check substitution rule for one side, then another
-- We use them consecutively to prove the general case (and get well-definedness)

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_left (a b a' b' c d : ℕ) (h: a —— b = a' —— b') :
    (a*c+b*d) —— (a*d+b*c) = (a'*c+b'*d) —— (a'*d+b'*c) := by
  simp only [eq] at *
  calc
    _ = c*(a+b') + d*(a'+b) := by ring
    _ = c*(a'+b) + d*(a+b') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_right (a b c d c' d' : ℕ) (h: c —— d = c' —— d') :
    (a*c+b*d) —— (a*d+b*c) = (a*c'+b*d') —— (a*d'+b*c') := by
  simp only [eq] at *
  calc
    _ = a*(c+d') + b*(c'+d) := by ring
    _ = a*(c'+d) + b*(c+d') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr {a b c d a' b' c' d' : ℕ} (h1: a —— b = a' —— b') (h2: c —— d = c' —— d') :
  (a*c+b*d) —— (a*d+b*c) = (a'*c'+b'*d') —— (a'*d'+b'*c') := by
  rw [mul_congr_left a b a' b' c d h1, mul_congr_right a' b' c d c' d' h2]

instance Int.instMul : Mul Int where
  mul := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a * c + b * d) —— (a * d + b * c)) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2; simp at h1 h2
    convert mul_congr _ _ <;> simpa
    )

-- Again, we use Quotient.lift₂_mk to avoid repeating the decomposition
-- we can just apply the function to the elements inside Quotient.mk
/-- Definition 4.1.2 (Multiplication of integers) -/
theorem Int.mul_eq (a b c d:ℕ) : a —— b * c —— d = (a*c+b*d) —— (a*d+b*c) := Quotient.lift₂_mk _ _ _ _

-- Allows us to cast nat literals (0, 1, 2, 3, ...) to Int
instance Int.instOfNat {n:ℕ} : OfNat Int n where
  ofNat := n —— 0

-- Allows us to cast nat variables (n, m, k, ...) to Int
instance Int.instNatCast : NatCast Int where
  natCast n := n —— 0

theorem Int.ofNat_eq (n:ℕ) : ofNat(n) = n —— 0 := rfl

theorem Int.natCast_eq (n:ℕ) : (n:Int) = n —— 0 := rfl

@[simp]
theorem Int.natCast_ofNat (n:ℕ) : ((ofNat(n):ℕ): Int) = ofNat(n) := by rfl

@[simp]
theorem Int.ofNat_inj (n m:ℕ) : (ofNat(n) : Int) = (ofNat(m) : Int) ↔ ofNat(n) = ofNat(m) := by
  simp only [ofNat_eq, eq, add_zero]; rfl

@[simp]
theorem Int.natCast_inj (n m:ℕ) : (n : Int) = (m : Int) ↔ n = m := by
  simp only [natCast_eq, eq, add_zero]

example : 3 = 3 —— 0 := rfl

example : 3 = 4 —— 1 := by rw [Int.ofNat_eq, Int.eq]

/-- (Not from textbook) 0 is the only natural whose cast is 0 -/
lemma Int.cast_eq_0_iff_eq_0 (n : ℕ) : (n : Int) = 0 ↔ n = 0 := by
  constructor <;> intro h
  · rw [← Int.natCast_inj, h]; rfl
  · rw [h]; rfl

/-- Definition 4.1.4 (Negation of integers) / Exercise 4.1.2 -/
instance Int.instNeg : Neg Int where
  neg := Quotient.lift (fun ⟨ a, b ⟩ ↦ b —— a) (by
  intro ⟨a1, a2⟩ ⟨b1,b2⟩ h1; simp at h1
  simp [Setoid.r] at * -- Simplify the equivalence relation
  symm; nth_rw 1 [add_comm]; nth_rw 2 [add_comm]
  exact h1)

theorem Int.neg_eq (a b:ℕ) : -(a —— b) = b —— a := rfl

example : -(3 —— 5) = 5 —— 3 := rfl

abbrev Int.IsPos (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = n
abbrev Int.IsNeg (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = -n

/-- Lemma 4.1.5 (trichotomy of integers ) -/
theorem Int.trichotomous (x:Int) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  -- This proof is slightly modified from that in the original text.
  obtain ⟨ a, b, rfl ⟩ := eq_diff x
  obtain h_lt | rfl | h_gt := _root_.trichotomous (r := LT.lt) a b -- Root knowledge that ℕ is trichotomous on <
  · obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_lt
    right; right; refine ⟨ c+1, by linarith, ?_ ⟩
    simp_rw [natCast_eq, neg_eq, eq]; abel
  · left; simp_rw [ofNat_eq, eq, add_zero, zero_add]
  · obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_gt
    right; left; refine ⟨ c+1, by linarith, ?_ ⟩
    simp_rw [natCast_eq, eq]; abel

/-- Lemma 4.1.5 (trichotomy of integers) -/
theorem Int.not_pos_zero (x:Int) : x = 0 ∧ x.IsPos → False := by
  rintro ⟨ rfl, ⟨ n, _, _ ⟩ ⟩; simp_all [←natCast_ofNat]

/-- Lemma 4.1.5 (trichotomy of integers) -/
theorem Int.not_neg_zero (x:Int) : x = 0 ∧ x.IsNeg → False := by
  rintro ⟨ rfl, ⟨ n, _, hn ⟩ ⟩; simp_rw [←natCast_ofNat, natCast_eq, neg_eq, eq] at hn
  linarith

/-- Lemma 4.1.5 (trichotomy of integers) -/
theorem Int.not_pos_neg (x:Int) : x.IsPos ∧ x.IsNeg → False := by
  rintro ⟨ ⟨ n, _, rfl ⟩, ⟨ m, _, hm ⟩ ⟩; simp_rw [natCast_eq, neg_eq, eq] at hm
  linarith

/-
Get our commutative ring structure
-/

lemma Int.n_n_eq_zero (n:ℕ) : (n —— n) = 0 := by
  rw [ofNat_eq, eq]; abel

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddGroup : AddGroup Int :=
AddGroup.ofLeftAxioms
  (by intro a b c; -- add_assoc
      obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
      obtain ⟨ b1, b2, rfl ⟩ := eq_diff b
      obtain ⟨ c1, c2, rfl ⟩ := eq_diff c
      repeat rw [add_eq]
      rw [Int.eq]; abel)
  (by intro a; -- zero_add
      obtain ⟨ a1, a2, rfl ⟩ := eq_diff a;
      rw [ofNat_eq, add_eq]; simp)
  (by intro a; -- add_left_neg
      obtain ⟨ a1, a2, rfl ⟩ := eq_diff a;
      rw [neg_eq, add_eq]; abel_nf;
      apply Int.n_n_eq_zero _)


/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddCommGroup : AddCommGroup Int where
  add_comm := by
    intro a b;
    obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
    obtain ⟨ b1, b2, rfl ⟩ := eq_diff b
    repeat rw [add_eq]
    abel_nf

lemma Int.mul_comm' (a b:Int) : a * b = b * a := by
  obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
  obtain ⟨ b1, b2, rfl ⟩ := eq_diff b
  repeat rw [mul_eq]
  rw [eq]; ring

lemma Int.one_mul' (a:Int) : 1 * a = a := by
  obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
  rw [ofNat_eq, mul_eq]; simp

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommMonoid : CommMonoid Int where
  mul_comm := mul_comm'

  mul_assoc := by
    -- This proof is written to follow the structure of the original text.
    intro x y z
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, rfl ⟩ := eq_diff z
    simp_rw [mul_eq]; congr 1 <;> ring
  one_mul := one_mul'
  mul_one := by intro a; rw [mul_comm', one_mul']

lemma Int.left_distrib' (a b c:Int) : a * (b + c) = a * b + a * c := by
  obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
  obtain ⟨ b1, b2, rfl ⟩ := eq_diff b
  obtain ⟨ c1, c2, rfl ⟩ := eq_diff c
  rw [add_eq]; repeat rw [mul_eq];
  rw [add_eq]; congr 1 <;> ring

lemma Int.zero_mul' (a:Int) : 0 * a = 0 := by
  obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
  rw [ofNat_eq, mul_eq]; simp
/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommRing : CommRing Int where
  left_distrib := Int.left_distrib'
  right_distrib := by
    intro a b c
    rw [mul_comm]
    rw [Int.left_distrib']
    rw [mul_comm a c, mul_comm b c]
  zero_mul := zero_mul'
  mul_zero := by
    intro a; rw [mul_comm, zero_mul']

/-Subtraction naturally arises from negation and addition-/

/-- Definition of subtraction -/
theorem Int.sub_eq (a b:Int) : a - b = a + (-b) := by rfl

theorem Int.sub_eq_formal_sub (a b:ℕ) : (a:Int) - (b:Int) = a —— b := by
  rw [Int.sub_eq]; repeat rw [natCast_eq]
  rw [neg_eq, add_eq]; simp

lemma Int.nonzero_imp_pos_or_neg (a : Int) (h : a ≠ 0) : a.IsPos ∨ a.IsNeg := by
  rcases a.trichotomous with h | h | h
  · contradiction
  · left; exact h
  · right; exact h

lemma Int.pos_mul_pos_eq_pos (a b : Int) (ha : a.IsPos) (hb : b.IsPos) : (a * b).IsPos := by
  obtain ⟨ a, ha, rfl ⟩ := ha
  obtain ⟨ b, hb, rfl ⟩ := hb
  use a * b; simp_all

lemma Int.pos_mul_neg_eq_neg (a b : Int) (ha : a.IsPos) (hb : b.IsNeg) : (a * b).IsNeg := by
  obtain ⟨ a, ha, rfl ⟩ := ha
  obtain ⟨ b, hb, rfl ⟩ := hb
  use a * b; simp_all

lemma Int.neg_mul_neg_eq_pos (a b : Int) (ha : a.IsNeg) (hb : b.IsNeg) : (a * b).IsPos := by
  obtain ⟨ a, ha, rfl ⟩ := ha
  obtain ⟨ b, hb, rfl ⟩ := hb
  use a * b; simp_all

/-- Proposition 4.1.8 (No zero divisors) / Exercise 4.1.5 -/
theorem Int.mul_eq_zero {a b:Int} (h: a * b = 0) : a = 0 ∨ b = 0 := by
  contrapose! h
  have ha := Int.nonzero_imp_pos_or_neg a h.1
  have hb := Int.nonzero_imp_pos_or_neg b h.2
  simp;
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> by_contra heq
  · have := Int.pos_mul_pos_eq_pos a b ha hb
    apply not_pos_zero _ ⟨heq, this⟩
  · have := Int.pos_mul_neg_eq_neg a b ha hb
    apply not_neg_zero _ ⟨heq, this⟩
  · have := Int.pos_mul_neg_eq_neg b a hb ha
    rw [mul_comm] at heq
    apply not_neg_zero _ ⟨heq, this⟩
  · have := Int.neg_mul_neg_eq_pos a b ha hb
    apply not_pos_zero _ ⟨heq, this⟩

lemma Int.neg_eq_mul_neg_one : ∀ a : Int, -a = -1 * a := by
  intro a
  obtain ⟨a1, a2, rfl⟩ := eq_diff a
  rw [ofNat_eq, neg_eq, neg_eq, mul_eq]
  simp

-- This has a built-in version from our above proven infrastructure,
-- But I figured it was more in the spirit to do it manually
lemma Int.sub_eq_zero' (a b : Int) : a - b = 0 ↔ a = b := by
  constructor <;> intro h
  · have : a - b + b = b := by rw [h, zero_add]
    simp at this; exact this
  · simp [h]

/-- Corollary 4.1.9 (Cancellation law) / Exercise 4.1.6 -/
theorem Int.mul_right_cancel₀ (a b c:Int) (h: a*c = b*c) (hc: c ≠ 0) : a = b := by
  have : a * c - b * c = 0 := by simp [h]
  rw [sub_eq, neg_eq_mul_neg_one, ← mul_assoc] at this
  rw [← right_distrib] at this
  apply mul_eq_zero at this
  simp [hc] at this
  rw [← sub_eq] at this
  rw [sub_eq_zero] at this; exact this

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLE : LE Int where
  le n m := ∃ a:ℕ, m = n + a

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLT : LT Int where
  lt n m := n ≤ m ∧ n ≠ m

theorem Int.le_iff (a b:Int) : a ≤ b ↔ ∃ t:ℕ, b = a + t := by rfl

theorem Int.lt_iff (a b:Int): a < b ↔ (∃ t:ℕ, b = a + t) ∧ a ≠ b := by rfl

/-- Lemma 4.1.11(a) (Properties of order) / Exercise 4.1.7 -/
theorem Int.lt_iff_exists_positive_difference (a b:Int) :
a < b ↔ ∃ n:ℕ, n ≠ 0 ∧ b = a + n := by
  constructor <;> intro h
  · rw [lt_iff] at h;
    obtain ⟨ ⟨t, ht⟩, hab ⟩ := h
    use t
    rw [ht]; simp
    by_contra h0; rw [h0] at ht; simp at ht;
    symm at ht; contradiction
  · choose n hn using h
    rw [lt_iff]
    simp [hn,cast_eq_0_iff_eq_0]

/-- Lemma 4.1.11(b) (Addition preserves order) / Exercise 4.1.7 -/
theorem Int.add_lt_add_right {a b:Int} (c:Int) (h: a < b) : a+c < b+c := by
  rw [lt_iff_exists_positive_difference] at *
  obtain ⟨n, ⟨h1,h2⟩ ⟩ := h
  use n; simp [h1, h2]; abel

/-- Lemma 4.1.11(c) (Positive multiplication preserves order) / Exercise 4.1.7 -/
theorem Int.mul_lt_mul_of_pos_right {a b c:Int} (hab : a < b) (hc: 0 < c) : a*c < b*c := by
  rw [lt_iff_exists_positive_difference] at *
  obtain ⟨n, ⟨h1,h2⟩ ⟩ := hab
  obtain ⟨m, ⟨h3,h4⟩ ⟩ := hc
  simp at h4
  use n*m
  simp_all
  rw [right_distrib]

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_gt_neg {a b:Int} (h: b < a) : -a < -b := by
  rw [lt_iff_exists_positive_difference] at *
  obtain ⟨n, ⟨h1,h2⟩ ⟩ := h
  use n; simp [h1, h2]

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_ge_neg {a b:Int} (h: b ≤ a) : -a ≤ -b := by
  obtain ⟨n, hn⟩ := h
  use n; simp [hn]

/-- Lemma 4.1.11(e) (Order is transitive) / Exercise 4.1.7 -/
theorem Int.lt_trans {a b c:Int} (hab: a < b) (hbc: b < c) : a < c := by
  rw [lt_iff_exists_positive_difference] at *
  obtain ⟨n, ⟨h1,h2⟩ ⟩ := hab
  obtain ⟨m, ⟨h3,h4⟩ ⟩ := hbc
  use n + m;
  constructor
  · simp; tauto
  · rw [h2] at h4; rw [h4];
    simp; rw [add_assoc]

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.trichotomous' (a b:Int) : a > b ∨ a < b ∨ a = b := by
  have := trichotomous ( a - b )
  rcases this with (h | h | h)
  · right; right; rw [sub_eq_zero'] at h; exact h
  · left; obtain ⟨n, ⟨h1,h2⟩⟩ := h
    -- Flip a > b to b < a
    change b < a
    rw [lt_iff_exists_positive_difference]
    use n
    constructor
    · by_contra h; rw [h] at h1;
      simp_all -- Overdoing it the first time
    · simp [← h2]

  · right; left
    obtain ⟨n, ⟨h1,h2⟩⟩ := h
    rw [lt_iff_exists_positive_difference]
    use n
    constructor
    · exact ne_of_gt h1 -- Not overdoing it this time
    · have : a - b + b = -n + b := by rw [h2]
      simp at this; simp [this]


lemma Int.a_lt_b_imp_pos_diff {a b : Int} (h : a < b) :
IsPos (b - a) := by
  rw [lt_iff_exists_positive_difference] at h
  obtain ⟨n, ⟨hn1, hn2⟩⟩ := h
  unfold IsPos; use n
  constructor
  · apply Nat.pos_of_ne_zero hn1
  · rw [hn2]; simp

lemma Int.neg_pos_is_neg {a : Int} (h : IsPos a) : IsNeg (-a) := by
  obtain ⟨n, ⟨hn1, hn2⟩⟩ := h
  unfold IsNeg; use n
  constructor
  · use hn1
  · rw [hn2]

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_lt (a b:Int) : ¬ (a > b ∧ a < b):= by
  change ¬ (b < a ∧ a < b)
  intro ⟨h1,h2⟩
  apply a_lt_b_imp_pos_diff at h1
  apply a_lt_b_imp_pos_diff at h2
  apply neg_pos_is_neg at h2
  simp at h2
  apply not_pos_neg (a-b); exact And.intro h1 h2

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_eq (a b:Int) : ¬ (a > b ∧ a = b):= by
  change ¬ (b < a ∧ a = b)
  intro ⟨h1,h2⟩
  apply a_lt_b_imp_pos_diff at h1
  rw [← sub_eq_zero'] at h2
  apply not_pos_zero (a-b); exact And.intro h2 h1

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_lt_and_eq (a b:Int) : ¬ (a < b ∧ a = b):= by
  intro ⟨h1,h2⟩
  apply a_lt_b_imp_pos_diff at h1
  rw [← sub_eq_zero'] at h2
  apply neg_pos_is_neg at h1; simp at h1
  apply not_neg_zero (a-b); exact And.intro h2 h1


/-- (Not from textbook) Establish the decidability of this order. -/
instance Int.decidableRel : DecidableRel (· ≤ · : Int → Int → Prop) := by
  intro n m
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n ≤ Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    change Decidable (a —— b ≤ c —— d)
    cases (a + d).decLe (b + c) with
      | isTrue h =>
        apply isTrue
        rw [le_iff]
        obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le h
        use t
        rw [natCast_eq, add_eq, eq]
        simp; rw [add_comm]; rw [ht]; abel
      | isFalse h =>
        apply isFalse
        contrapose! h
        rw [le_iff] at h
        choose t ht using h
        rw [natCast_eq, add_eq, eq] at ht
        simp at ht;
        omega
  exact Quotient.recOnSubsingleton₂ n m this

/-- (Not from textbook) 0 is the only additive identity -/
lemma Int.is_additive_identity_iff_eq_0 (b : Int) : (∀ a, a = a + b) ↔ b = 0 := by
  constructor <;> intro h
  · specialize h 0; rw [h]; simp
  · rw [h]; simp

lemma Int.le_antisymm' (a b : Int) : (a ≤ b) → (b ≤ a) →  a = b := by
  intro h1 h2
  obtain ⟨ t, ht ⟩ := h1
  obtain ⟨ s, hs ⟩ := h2
  rw [ht] at hs; symm at hs
  rw [add_assoc,add_eq_left] at hs
  rw [natCast_eq, natCast_eq, ofNat_eq] at hs
  rw [add_eq, eq] at hs; simp at hs
  have : t = 0 := by omega
  simp [this] at ht; exact ht.symm


/-- (Not from textbook) Int has the structure of a linear ordering. -/
instance Int.instLinearOrder : LinearOrder Int where
  le_refl := by intro a; use 0; simp
  le_trans := by
    intro a b c hab hbc;
    obtain ⟨ t1, ht1 ⟩ := hab
    obtain ⟨ t2, ht2 ⟩ := hbc
    use t1 + t2; simp [ht1, ht2]; abel
  lt_iff_le_not_ge := by
    intro a b; constructor <;> intro h
    · constructor
      · rw [lt_iff] at h; exact h.1
      · rw [lt_iff] at h; obtain ⟨h1,hba⟩ := h
        contrapose! hba
        have hab: a ≤ b := by choose t _ using h1; use t
        apply le_antisymm' _ _ hab hba

    · obtain ⟨h1,h2⟩ := h
      obtain ⟨t, ht⟩ := h1
      constructor
      · use t
      · contrapose! h2
        use 0; simp [h2]

  le_antisymm := le_antisymm'
  le_total := by
    intro a b
    have := trichotomous' a b
    rcases this with (h | h | h)
    · right; exact h.1
    · left; exact h.1
    · rw [h]; left; use 0; simp
  toDecidableLE := decidableRel

/-- Exercise 4.1.3 -/
theorem Int.neg_one_mul (a:Int) : -1 * a = -a := by
  obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
  rw [ofNat_eq, neg_eq, neg_eq, mul_eq]
  simp

/-- Exercise 4.1.8 -/
theorem Int.no_induction : ∃ P: Int → Prop, (P 0 ∧ ∀ n, P n → P (n+1)) ∧ ¬ ∀ n, P n := by
  use fun z ↦ z ≥ 0
  simp
  constructor
  · intro n hn;
    choose t ht using hn
    use t+1; simp [ht]
  · use -1;
    rw [lt_iff_exists_positive_difference]
    use 1
    constructor
    · omega
    · rw [natCast_eq, ofNat_eq, ofNat_eq,neg_eq, add_eq, eq]

/- A nonnegative number squared is nonnegative. This is a special case of 4.1.9 that's useful for proving the general case. --/
lemma Int.sq_nonneg_of_pos (n:Int) (h: 0 ≤ n) : 0 ≤ n*n := by
  choose t ht using h; simp at ht
  use t*t; simp [ht]

lemma Int.pos_iff_gt_zero (n:Int) : n.IsPos ↔ 0 < n := by
  constructor <;> intro h
  · obtain ⟨ m, hm1, hm2 ⟩ := h
    rw [lt_iff_exists_positive_difference]
    use m; simp [hm2]; omega
  · have ⟨h1,h2⟩ := h
    choose t ht using h1
    use t; simp [ht];
    simp at ht;
    suffices t ≠ 0 by omega
    contrapose! h2; simp [h2] at ht; exact ht.symm


lemma Int.neg_iff_lt_zero (n:Int) : n.IsNeg ↔ n < 0 := by
  constructor <;> intro h
  · obtain ⟨ m, hm1, hm2 ⟩ := h
    rw [lt_iff_exists_positive_difference]
    use m; simp [hm2]; omega
  · have ⟨h1,h2⟩ := h
    choose t ht using h1
    use t;
    have : 0 - t = t - t + n := by simp [ht]
    simp at this; simp [this]
    suffices t ≠ 0 by omega
    contrapose! h2; simp [h2] at ht; exact ht.symm

/-- Exercise 4.1.9. The square of any integer is nonnegative. -/
theorem Int.sq_nonneg (n:Int) : 0 ≤ n*n := by
  rcases trichotomous' 0 n with (h | h | h)
  · conv at h => change n < 0
    have := h.1
    rw [← neg_iff_lt_zero] at h
    choose t ht using h
    simp [ht.2];
    have : 0 ≤ t := by omega
    have : 0 ≤ (t:Int) := by use t; simp
    apply Int.sq_nonneg_of_pos _ this
  · have := h.1
    apply Int.sq_nonneg_of_pos _ this
  · rw [← h]; simp

/-- Exercise 4.1.9 -/
theorem Int.sq_nonneg' (n:Int) : ∃ (m:Nat), n*n = m := by
  have := Int.sq_nonneg n
  choose t ht using this
  use t
  simp [ht]

end Chapter4_1
--------------- SECTION 4.2 ---------------
namespace Chapter4_2

structure PreRat where
  numerator : ℤ
  denominator : ℤ
  nonzero : denominator ≠ 0

/-- Exercise 4.2.1 -/
instance PreRat.instSetoid : Setoid PreRat where
  r a b := a.numerator * b.denominator = b.numerator * a.denominator
  iseqv := {
    refl := by
      intro rat; rfl
    symm := by
      intro rat1 rat2 hrat; rw [hrat]
    trans := by
      intro a b c hab hbc
      let a1 := a.numerator
      let a2 := a.denominator
      let b1 := b.numerator
      let b2 := b.denominator
      let c1 := c.numerator
      let c2 := c.denominator
      suffices a1*c2 * b2  = c1*a2 * b2 by
          have h:= b.nonzero; apply mul_right_cancel₀ h this
      suffices c2 * (a1 * b2) = a2 * (c1 * b2) by linarith
      rw [hab, ← hbc]; linarith
    }

@[simp]
theorem PreRat.eq (a b c d:ℤ) (hb: b ≠ 0) (hd: d ≠ 0) :
    (⟨ a,b,hb ⟩: PreRat) ≈ ⟨ c,d,hd ⟩ ↔ a * d = c * b := by rfl

abbrev Rat := Quotient PreRat.instSetoid

/-- We give division a "junk" value of 0//1 if the denominator is zero -/
abbrev Rat.formalDiv (a b:ℤ) : Rat :=
  Quotient.mk PreRat.instSetoid (if h:b ≠ 0 then ⟨ a,b,h ⟩ else ⟨ 0, 1, by decide ⟩)

infix:100 " // " => Rat.formalDiv

/-- Definition 4.2.1 (Rationals) -/
theorem Rat.eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0): a // b = c // d ↔ a * d = c * b := by
  simp [hb, hd]; --Needed to unfold and verify that we're not in the junk case
  simp [Setoid.r] -- Use equality def

/-- Definition 4.2.1 (Rationals) -/
theorem Rat.eq_diff (n:Rat) : ∃ a b, b ≠ 0 ∧ n = a // b := by
  -- Establish that you can decompose any rational
  apply Quotient.ind _ n; -- Retrieve the construction for a quotient
  intro ⟨ a, b, h ⟩ -- Get the components of the construction
  refine ⟨ a, b, h, ?_ ⟩
  simp [formalDiv, h] -- Use nonzero to get a//b; then use equality def (@[simp])

/-
  Decidability of equality. Hint: modify the proof of `DecidableEq Int` from the previous
  section. However, because formal division handles the case of zero denominator separately, it
  may be more convenient to avoid that operation and work directly with the `Quotient` API.
-/

instance Rat.decidableEq : DecidableEq Rat := by
  intro a b
  have : ∀ (n:PreRat) (m: PreRat),
      Decidable (Quotient.mk PreRat.instSetoid n = Quotient.mk PreRat.instSetoid m) := by
    intro ⟨ a,b, hb ⟩ ⟨ c,d, hd ⟩
    simp [Setoid.r]
    exact decEq _ _
  exact Quotient.recOnSubsingleton₂ a b this

/-- Lemma 4.2.3 (Addition well-defined) -/
instance Rat.add_inst : Add Rat where
  add := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*d+b*c) // (b*d)) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ⟨ a', b', h1' ⟩ ⟨ c', d', h2' ⟩ h3 h4
    simp_all [Setoid.r]
    calc
      _ = (a*b')*d*d' + b*b'*(c*d') := by ring
      _ = (a'*b)*d*d' + b*b'*(c'*d) := by rw [h3, h4]
      _ = _ := by ring
  )

/-- Definition 4.2.2 (Addition of rationals) -/
theorem Rat.add_eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0) :
    (a // b) + (c // d) = (a*d + b*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Lemma 4.2.3 (Multiplication well-defined) -/
instance Rat.mul_inst : Mul Rat where
  mul := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*c) // (b*d)) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ⟨ a', b', h1' ⟩ ⟨ c', d', h2' ⟩ h3 h4
    simp_all [Setoid.r]
    calc
      _ = (a * b') * (c * d') := by ring
      _ = (a'*b)*(c'*d) := by rw [h3, h4]
      _ = _ := by ring )

/-- Definition 4.2.2 (Multiplication of rationals) -/
theorem Rat.mul_eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0) :
    (a // b) * (c // d) = (a*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Lemma 4.2.3 (Negation well-defined) -/
instance Rat.neg_inst : Neg Rat where
  neg := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ (-a) // b) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ h3
    simp_all [Setoid.r])

/-- Definition 4.2.2 (Negation of rationals) -/
theorem Rat.neg_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : - (a // b) = (-a) // b := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

/-- Embedding the integers in the rationals -/
instance Rat.instIntCast : IntCast Rat where
  intCast a := a // 1

instance Rat.instNatCast : NatCast Rat where
  natCast n := (n:ℤ) // 1

instance Rat.instOfNat {n:ℕ} : OfNat Rat n where
  ofNat := (n:ℤ) // 1

theorem Rat.coe_Int_eq (a:ℤ) : (a:Rat) = a // 1 := rfl

theorem Rat.coe_Nat_eq (n:ℕ) : (n:Rat) = n // 1 := rfl

theorem Rat.of_Nat_eq (n:ℕ) : (ofNat(n):Rat) = (ofNat(n):Nat) // 1 := rfl

/- Proves part of the fact that these casts are homomorphisms-/

/-- natCast distributes over successor -/
theorem Rat.natCast_succ (n: ℕ) : ((n + 1: ℕ): Rat) = (n: Rat) + 1 := by
  simp [coe_Nat_eq, coe_Nat_eq, of_Nat_eq, add_eq]


/-- intCast distributes over addition -/
lemma Rat.intCast_add (a b:ℤ) : (a:Rat) + (b:Rat) = (a+b:ℤ) := by
  simp [coe_Int_eq, coe_Int_eq, coe_Int_eq, add_eq]

/-- intCast distributes over multiplication -/
lemma Rat.intCast_mul (a b:ℤ) : (a:Rat) * (b:Rat) = (a*b:ℤ) := by
  simp [coe_Int_eq, coe_Int_eq, coe_Int_eq, mul_eq]

/-- intCast commutes with negation -/
lemma Rat.intCast_neg (a:ℤ) : - (a:Rat) = (-a:ℤ) := rfl

@[simp]
theorem Rat.coe_Int_inj : Function.Injective (fun n:ℤ ↦ (n:Rat)) := by
  intro z1 z2 h; simp at h;
  rw [coe_Int_eq, coe_Int_eq, eq] at h
  simp at h; exact h; decide; decide

/-
  Whereas the book leaves the inverse of 0 undefined, it is more convenient in Lean to assign a
  "junk" value to this inverse; we arbitrarily choose this junk value to be 0.
-/
instance Rat.instInv : Inv Rat where
  inv := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ b // a) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ h3
    simp_all [Setoid.r]
    by_cases ha : a = 0
    · simp_all -- Junk case: a=0, then c=0, so both sides are junk (0//1)
    · simp [ha]
      have hc : c ≠ 0 := by -- If c=0, then ad=0, so a=0 or d=0, both wrong
        by_contra hc; simp [hc] at h3; simp_all
      simp [hc]; linarith -- We end up with ad=cb, which is known by rat equality
      -- Since inverse just flips the equation, we end up with the commuted ver
)

-- Use operation as a lemma
lemma Rat.inv_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : (a // b)⁻¹ = b // a := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

@[simp] -- Dealing with the junk case
theorem Rat.inv_zero : (0:Rat)⁻¹ = 0 := rfl

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.addGroup_inst : AddGroup Rat :=
AddGroup.ofLeftAxioms (by
  -- this proof is written to follow the structure of the original text.
  intro x y z
  obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
  obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
  obtain ⟨ e, f, hf, rfl ⟩ := eq_diff z
  have hbd : b*d ≠ 0 := Int.mul_ne_zero hb hd     -- can also use `observe hbd : b*d ≠ 0` here
  have hdf : d*f ≠ 0 := Int.mul_ne_zero hd hf     -- can also use `observe hdf : d*f ≠ 0` here
  have hbdf : b*d*f ≠ 0 := Int.mul_ne_zero hbd hf -- can also use `observe hbdf : b*d*f ≠ 0` here
  rw [add_eq _ _ hb hd, add_eq _ _ hbd hf, add_eq _ _ hd hf,
      add_eq _ _ hb hdf, ←mul_assoc b, eq _ _ hbdf hbdf]
  ring
)
 (by
  intro a;
  obtain ⟨ a1, a2, h, rfl⟩ := eq_diff a
  rw [of_Nat_eq, add_eq]; simp; decide; exact h)
 (by
  intro a;
  obtain ⟨ a1, a2, h, rfl⟩ := eq_diff a
  rw [neg_eq, add_eq, of_Nat_eq, eq];
  ring; simp [h]; decide; repeat exact h;
 )

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instAddCommGroup : AddCommGroup Rat where
  add_comm := by
    intro x y
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
    rw [add_eq, add_eq]; ring_nf; repeat simp_all

@[simp]
lemma Rat.zero_num_invariant {a b:ℤ} (ha : a ≠ 0) (hb: b ≠ 0) :
(0//a : Rat) = (0//b : Rat) := by
  rw [eq]; repeat simp_all

/-
∀ (a b : Rat), a * b = b * a
-/
lemma Rat.mul_comm' (x y:Rat) : x * y = y * x := by
  obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
  obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
  rw [mul_eq, mul_eq]; ring_nf; repeat simp_all

lemma Rat.one_mul' (x:Rat) : 1 * x = x := by
  obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
  rw [of_Nat_eq, mul_eq]; simp; decide; exact hb

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instCommMonoid : CommMonoid Rat where
  mul_comm := mul_comm'
  mul_assoc := by
    intro x y z
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, hf, rfl ⟩ := eq_diff z
    rw [mul_eq, mul_eq, mul_eq, mul_eq]
    ring_nf; repeat simp_all
  one_mul := one_mul'

  mul_one := by
    intro x; rw [mul_comm', one_mul']

-- ∀ (a b c : Rat), a * (b + c) = a * b + a * c
lemma Rat.left_distrib' (a b c : Rat) : a * (b + c) = a * b + a * c := by
  obtain ⟨ a1, a2, ha2, rfl ⟩ := eq_diff a
  obtain ⟨ b1, b2, hb2, rfl ⟩ := eq_diff b
  obtain ⟨ c1, c2, hc2, rfl ⟩ := eq_diff c
  rw [add_eq, mul_eq, mul_eq, mul_eq, add_eq, eq];
  ring
  repeat simp_all

lemma Rat.zero_mul' (x:Rat) : 0 * x = 0 := by
  obtain ⟨ a1, a2, ha2, rfl ⟩ := eq_diff x
  rw [of_Nat_eq, mul_eq]; ring_nf;
  apply zero_num_invariant; exact ha2; decide; decide; exact ha2

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instCommRing : CommRing Rat where
  left_distrib := left_distrib'
  right_distrib := by intro a b c;
                      rw [mul_comm, left_distrib', mul_comm a c, mul_comm b c]
  zero_mul := zero_mul'
  mul_zero := by intro x; rw [mul_comm, zero_mul']
  mul_assoc := mul_assoc
  -- Usually CommRing will generate a natCast instance and a proof for this.
  -- However, we are using a custom natCast for which `natCast_succ` cannot
  -- be proven automatically by `rfl`. Luckily we have proven it already.
  natCast_succ := natCast_succ

instance Rat.instRatCast : RatCast Rat where
  ratCast q := q.num // q.den

theorem Rat.ratCast_inj : Function.Injective (fun n:ℚ ↦ (n:Rat)) := by
  intro q1 q2 h
  simp at h;
  -- Nonzero denominators
  have h1 : q1.den ≠ 0 := Rat.den_nz q1
  have h2 : q2.den ≠ 0 := Rat.den_nz q2
  conv at h => change (q1.num // q1.den : Rat) = (q2.num // q2.den : Rat)
  rw [eq] at h;
  rw [Rat.eq_iff_mul_eq_mul]
  exact h
  repeat simp

theorem Rat.coe_Rat_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : (a/b:ℚ) = a // b := by
  set q := (a/b:ℚ)
  set num :ℤ := q.num
  set den :ℤ := (q.den:ℤ)
  have hden : den ≠ 0 := by simp [den, q.den_nz]
  change num // den = a // b
  rw [eq _ _ hden hb]
  qify
  have hq : num / den = q := Rat.num_div_den q
  rwa [div_eq_div_iff] at hq <;> simp [hden, hb]

/-- Default definition of division -/
instance Rat.instDivInvMonoid : DivInvMonoid Rat where

theorem Rat.div_eq (q r:Rat) : q/r = q * r⁻¹ := by rfl

lemma Rat.div_int_eq (a b : ℤ) (hb : b ≠ 0) :  (a // b) = (a / b) := by
  rw [div_eq, coe_Int_eq, coe_Int_eq, inv_eq, mul_eq, eq ]; repeat simp_all


lemma Rat.zero_iff_num_zero (qnum qden:ℤ) (hden: qden ≠ 0) :
  (qnum // qden = 0) ↔ qnum = 0 := by
  constructor <;> intro h
  · rw [of_Nat_eq, eq] at h; simp at h; exact h; exact hden; decide
  · rw [of_Nat_eq, eq]; simp; exact h; exact hden; decide

-- Contrapositive equivalence
lemma Rat.zero_iff_num_zero' (qnum qden:ℤ) (hden: qden ≠ 0) :
  (qnum // qden ≠ 0) ↔ qnum ≠ 0 := by
  constructor <;> intro h
  · contrapose! h; revert h; apply (zero_iff_num_zero _ _ hden ).2
  · contrapose! h; revert h; apply (zero_iff_num_zero _ _ hden ).1

lemma Rat.mul_inv_cancel' (a : Rat) (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  obtain ⟨ a1, a2, ha2, rfl ⟩ := eq_diff a
  have ha1 : a1 ≠ 0 := (Rat.zero_iff_num_zero' a1 a2 ha2).mp ha
  rw [inv_eq, mul_eq, of_Nat_eq, eq]; simp; linarith
  simp [ha1, ha2]; repeat simp_all

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instField : Field Rat where
  exists_pair_ne := by
    use 0, 1; simp;rw [of_Nat_eq, of_Nat_eq, eq]; repeat simp
  mul_inv_cancel := mul_inv_cancel'
  inv_zero := rfl
  ratCast_def := by
    intro q
    set num := q.num
    set den := q.den
    have hden : (den:ℤ) ≠ 0 := by simp [den, q.den_nz]
    rw [← Rat.num_div_den q]
    convert coe_Rat_eq _ hden
    rw [coe_Int_eq, coe_Nat_eq, div_eq, inv_eq, mul_eq, eq] <;> simp [num, den, q.den_nz]
  qsmul := _
  nnqsmul := _

example : (3//4) / (5//6) = 9 // 10 := by
  rw [Rat.div_eq, Rat.inv_eq, Rat.mul_eq, Rat.eq]; ring; repeat decide

/-
  Embedding the integers in the rationals is a ring homomorphism.

  We already proved these homomorphic properties above.
-/
def Rat.coe_int_hom : ℤ →+* Rat where
  toFun n := (n:Rat)
  map_zero' := rfl
  map_one' := rfl
  map_add' := by intro x y; rw [intCast_add]
  map_mul' := by intro x y; rw [intCast_mul]

/-- Definition 4.2.6 (positivity) -/
def Rat.isPos (q:Rat) : Prop := ∃ a b:ℤ, a > 0 ∧ b > 0 ∧ q = a/b

/-- Definition 4.2.6 (negativity) -/
def Rat.isNeg (q:Rat) : Prop := ∃ r:Rat, r.isPos ∧ q = -r



/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.trichotomous (x:Rat) : x = 0 ∨ x.isPos ∨ x.isNeg := by
  obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
  by_cases ha0 : a = 0
  · left; rw [of_Nat_eq, eq]; simp [ha0]; repeat simp_all
  right
  by_cases ha : a > 0 <;> by_cases hb0 : b > 0
  · left; use a, b; simp_all; apply div_int_eq; apply hb
  · right; use (a/(-b)); constructor; use a, (-b); simp [ha]; omega
    have : -b ≠ 0 := by omega
    rw [intCast_neg, ← div_int_eq, neg_eq, eq]; repeat simp_all
  · right; use (-a/b); constructor; use (-a), b; simp [hb0]; omega
    rw [intCast_neg, ← div_int_eq, neg_eq, eq]; repeat simp_all
  · left; use -a, -b;
    have : -a > 0 := by omega;
    have : -b > 0 := by omega;
    simp_all; apply div_int_eq _ _ hb


/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_zero_and_pos (x:Rat) : ¬(x = 0 ∧ x.isPos) := by
  by_contra h; obtain ⟨ h1, h2 ⟩ := h;
  obtain ⟨ a, b, ha, hb, rfl ⟩ := h2
  rw [← div_int_eq] at h1;
  rw [of_Nat_eq, eq] at h1; simp at h1
  repeat omega

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_zero_and_neg (x:Rat) : ¬(x = 0 ∧ x.isNeg) := by
  by_contra h; obtain ⟨ h1, h2 ⟩ := h;
  obtain ⟨ r, h3, rfl ⟩ := h2;
  obtain ⟨ a, b, ha, hb, rfl ⟩ := h3
  rw [← div_int_eq] at h1;
  rw [of_Nat_eq, neg_eq, eq] at h1; simp at h1
  repeat omega

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_pos_and_neg (x:Rat) : ¬(x.isPos ∧ x.isNeg) := by
  by_contra h; obtain ⟨ h1, h2 ⟩ := h;
  obtain ⟨ a, b, ha, hb, rfl ⟩ := h1;
  obtain ⟨ r, h3, h4 ⟩ := h2;
  obtain ⟨ c, d, hc, hd, rfl ⟩ := h3;
  repeat rw [← div_int_eq] at h4;
  rw [neg_eq, eq] at h4;
  have had: a*d > 0 := by clear h4; apply Int.mul_pos; apply ha; apply hd
  have hcb: c*b > 0 := by clear h4; positivity
  linarith
  repeat omega

/-- Definition 4.2.8 (Ordering of the rationals) -/
instance Rat.instLT : LT Rat where
  lt x y := (x-y).isNeg

/-- Definition 4.2.8 (Ordering of the rationals) -/
instance Rat.instLE : LE Rat where
  le x y := (x < y) ∨ (x = y)

theorem Rat.lt_iff (x y:Rat) : x < y ↔ (x-y).isNeg := by rfl
theorem Rat.le_iff (x y:Rat) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

lemma Rat.isPos_iff_neg_isNeg (x:Rat) : x.isPos ↔ (-x).isNeg := by
  constructor <;> intro h
  · obtain ⟨ a, b, ha, hb, rfl ⟩ := h
    use a/b; constructor; use a, b; rfl
  · obtain ⟨ r, h1, h2 ⟩ := h; simp at h2
    rw [h2]; assumption

lemma Rat.isNeg_iff_neg_isPos (x:Rat) : x.isNeg ↔ (-x).isPos := by
  constructor <;> intro h
  · obtain ⟨ r, h1, h2 ⟩ := h;
    rw [h2]; simp; assumption
  · obtain ⟨ a, b, ha, hb, h ⟩ := h
    use a/b; constructor; use a, b; simp [← h]

theorem Rat.gt_iff (x y:Rat) : x > y ↔ (x-y).isPos := by
  change y < x ↔ (x-y).isPos
  rw [lt_iff]
  have : y - x = -(x - y) := by ring
  rw [this]; symm; apply isPos_iff_neg_isNeg

theorem Rat.ge_iff (x y:Rat) : x ≥ y ↔ (x > y) ∨ (x = y) := by
  change y ≤ x ↔ (y < x) ∨ (x = y)
  rw [eq_comm]
  apply le_iff y x

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.trichotomous' (x y:Rat) : x > y ∨ x < y ∨ x = y := by
  rcases Rat.trichotomous (x - y) with (h | h | h)
  · right; right; apply sub_eq_zero.mp h
  · left; rw [gt_iff]; exact h
  · right; left; rw [lt_iff]; exact h

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_gt_and_lt (x y:Rat) : ¬ (x > y ∧ x < y):= by
  rw [gt_iff, lt_iff]; apply Rat.not_pos_and_neg

lemma Rat.dist_zero (x y : Rat):  x = y ↔ x - y = 0 := by
  constructor <;> intro h
  · rw [h]; ring
  · apply sub_eq_zero.mp h

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_gt_and_eq (x y:Rat) : ¬ (x > y ∧ x = y):= by
  rw [gt_iff, dist_zero, and_comm]
  apply Rat.not_zero_and_pos


/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_lt_and_eq (x y:Rat) : ¬ (x < y ∧ x = y):= by
  rw [lt_iff, dist_zero, and_comm]
  apply Rat.not_zero_and_neg

/-- Proposition 4.2.9(b) (order is anti-symmetric) / Exercise 4.2.5 -/
theorem Rat.antisymm (x y:Rat) : x < y ↔ (y - x).isPos := by
  rw [lt_iff, isPos_iff_neg_isNeg]; simp

/-- Proposition 4.2.9(c) (order is transitive) / Exercise 4.2.5 -/
theorem Rat.lt_trans {x y z:Rat} (hxy: x < y) (hyz: y < z) : x < z := by
  simp [lt_iff, isNeg_iff_neg_isPos] at *
  obtain ⟨ a1, b1, ha1, hb1, hxy ⟩ := hxy
  obtain ⟨ a2, b2, ha2, hb2, hyz ⟩ := hyz
  have : z - x = (y - x) + (z - y) := by ring
  rw [this, hxy, hyz]
  rw [← div_int_eq, ← div_int_eq, add_eq]
  use a1*b2 + b1*a2, b1*b2; simp
  constructor; positivity; constructor; positivity;
  rw [div_int_eq]; simp_all
  have : b1 * b2 > 0 := by positivity
  repeat omega

/-- Proposition 4.2.9(d) (addition preserves order) / Exercise 4.2.5 -/
theorem Rat.add_lt_add_right {x y:Rat} (z:Rat) (hxy: x < y) : x + z < y + z := by
  rw [lt_iff] at *; simp [hxy]

lemma Rat.pos_times_pos {a b: Rat} (ha: isPos a) (hb: isPos b) : isPos (a * b) := by
  obtain ⟨ a1, a2, ha1, ha2, rfl ⟩ := ha
  obtain ⟨ b1, b2, hb1, hb2, rfl ⟩ := hb
  rw [← div_int_eq, ← div_int_eq, mul_eq]
  use a1*b1, a2*b2; simp
  constructor; positivity; constructor; positivity
  rw [div_int_eq]; simp_all;
  have : a2 * b2 > 0 := by positivity
  repeat omega



/-- Proposition 4.2.9(e) (positive multiplication preserves order) / Exercise 4.2.5 -/
theorem Rat.mul_lt_mul_right {x y z:Rat} (hxy: x < y) (hz: z.isPos) : x * z < y * z := by
  rw [lt_iff, isNeg_iff_neg_isPos] at *;
  have : (x - y) * z = (x * z) - (y * z) := by ring  -- It's just distributivity
  rw [← this];
  have : (-((x - y) * z)) = ((-(x - y)) * z) := by ring
  rw [this]
  apply pos_times_pos hxy hz



lemma Rat.sub_eq {a b : Rat} : a - b = a + (-b) := by rfl


/-
If we started with Rat.formalDiv, then we'd have to check the case where
we have junk values.

Since we started with the PreRat quotient, and then used it to create a formalDiv,
we have nonzero denominator built-in, so we can avoid junk values.
-/

/-
Making a formaldiv using a quotient is safe, unlike just making a
formaldiv plainly.-/
lemma Rat.mk_eq_formalDiv (a b : ℤ) (hb : b ≠ 0) :
    (⟦{ numerator := a, denominator := b, nonzero := hb }⟧ : Rat) = a // b := by
  simp only [formalDiv]
  simp [hb]

lemma Rat.div_neg (a b : Rat) : a / (-b) = -(a / b) := by
  rw [div_eq, div_eq]; ring

lemma Rat.neg_div (a b : Rat) : (-a)/b = -(a / b) := by
  rw [div_eq, div_eq]; ring



lemma Rat.neg_sub (a b : Rat) : -(a - b) = b - a := by
  rw [sub_eq, sub_eq]; ring


lemma Rat.lt_iff' (x y:Rat) : x < y ↔ ∃ z, z.isPos ∧ x + z = y := by
  rw [lt_iff]
  constructor <;> intro h
  · use (y-x); constructor;
    · rw [← neg_sub]; rw [isNeg_iff_neg_isPos] at h; exact h
    · ring
  · obtain ⟨ z, hpz, hz ⟩ := h; rw [isNeg_iff_neg_isPos]
    have : z =-(x-y) := by rw [← hz]; ring
    rw [← this]; exact hpz

lemma Rat.le_iff' (x y:Rat) : x ≤ y ↔ ∃ z, ¬ (z.isNeg) ∧ x + z = y := by
  constructor <;> intro h
  · rw [le_iff] at h
    rcases h with (h | h)
    · rw [lt_iff'] at h; obtain ⟨ z, hpz, hz ⟩ := h;
      use z; constructor; intro hneg;
      apply Rat.not_pos_and_neg _ ⟨ hpz, hneg⟩; exact hz
    · use y-x; simp; symm at h; rw [dist_zero] at h;
      intro h'; apply not_zero_and_neg _ ⟨h, h'⟩
  · obtain ⟨ z, hnz, hz ⟩ := h; rw [le_iff]
    rcases Rat.trichotomous z with (h | h | h)
    · right; simp [h] at hz; exact hz
    · left; rw [lt_iff']; use z
    · contradiction

lemma Rat.not_isNeg (z : Rat): ¬(z.isNeg) ↔ ∃ (a b : ℤ), a ≥ 0 ∧ b > 0 ∧ z = a/b := by
  constructor <;> intro h
  · by_cases hz : z = 0
    · use 0, 1; simp [hz];
    · rcases Rat.trichotomous z with (h | h | h)
      · contradiction
      · obtain ⟨ a, b, ha, hb, rfl ⟩ := h; use a, b; simp_all; omega;
      · contradiction
  · obtain ⟨ a, b, ha, hb, rfl ⟩ := h
    rcases lt_or_eq_of_le ha with (ha | ha)
    · intro h; apply Rat.not_pos_and_neg; refine And.intro ?_ h; use a, b;
    · intro h; apply Rat.not_zero_and_neg; refine And.intro ?_ h;
      rw [← div_int_eq, ← ha, of_Nat_eq, eq]; repeat simp_all;
      simp [← ha]; repeat simp_all; omega

-- Honestly, it feels like there should've been a less tedious way to do this.

--Contrapose of Rat.coe_Int_inj
@[simp]
lemma Rat.coe_Int_inj_mt :  ∀ {a b : ℤ},  ¬ a = b → ¬ (a : Rat) = b  := by
  intros a b h; contrapose! h; apply Rat.coe_Int_inj; exact h

-- Version where you use an ofnat for one of the ints is a natlit
@[simp]
lemma Rat.coe_Int_mt' {a:ℤ} {b:ℕ} :  ¬ a = ofNat(b) → ¬ (a : Rat) = ofNat(b) := by
  intros h; contrapose! h; apply Rat.coe_Int_inj; exact h

lemma Rat.lt_iff_isNeg (x : ℤ ): x < 0 ↔ (x : Rat).isNeg := by
  constructor <;> intro h
  · rw [isNeg_iff_neg_isPos]; use -x, 1; simp [h]
  · rw [isNeg_iff_neg_isPos] at h;  suffices -x > 0 by omega
    rw [coe_Int_eq] at h; obtain ⟨ a, b, ha, hb, h ⟩ := h
    rw [neg_eq, ← div_int_eq, eq, mul_one] at h; rw [← h] at ha;
    change 0 < -x; rw [mul_comm] at ha
    apply Int.pos_of_mul_pos_right ha; repeat omega

-- Made an alternate version that I like more because it feels more natural.
-- I also made it dense because I don't like scrolling forever to get past it.
-- Probably a waste of time, but I had fun.
instance Rat.decidableRel' : DecidableRel (· ≤ · : Rat → Rat → Prop) := by
  intro n m
  simp
  have : ∀ (n:PreRat) (m: PreRat),
      Decidable (Quotient.mk PreRat.instSetoid n ≤ Quotient.mk PreRat.instSetoid m) := by
    intro ⟨ a,b,hb ⟩ ⟨ c,d,hd ⟩
    -- at this point, the goal is morally `Decidable(a//b ≤ c//d)`, but there are technical
    -- issues due to the junk value of formal division when the denominator vanishes.
    -- It may be more convenient to avoid formal division and work directly with `Quotient.mk`.
    cases (0:ℤ).decLe (b*d) with
      | isTrue hbd =>
        cases (a * d).decLe (b * c) with
          | isTrue h =>
            apply isTrue; rw [ mk_eq_formalDiv, mk_eq_formalDiv, le_iff']
            obtain ⟨k, hk1, hk2⟩ := le_iff_exists_nonneg_add.mp h
            use k/((b*d):ℤ ); constructor
            · rw [not_isNeg]; use k; use (b*d:ℤ)
              constructor; omega; constructor; positivity; rfl
            · rw [← div_int_eq]; rw [add_eq]; rw [eq]
              have : c * (b * (b * d)) = (b*c) * (b * d) := by ring;
              rw [this, ← hk2]; ring; repeat positivity

          | isFalse h =>
            apply isFalse; rw [ mk_eq_formalDiv, mk_eq_formalDiv]
            rw [le_iff']; by_contra hdiv; push_neg at h
            obtain ⟨ r, hrpos, hr ⟩ := hdiv; apply hrpos
            have : r = (c//d) - (a//b) := by rw [← hr]; ring
            rw [sub_eq, neg_eq, add_eq] at this; rw [this]
            rw [div_int_eq, isNeg_iff_neg_isPos, ← neg_div]; simp
            use (d*a-c*b), (b*d); constructor; linarith
            constructor; positivity; simp; ring; repeat simp_all

      | isFalse hbd =>
        cases (b * c).decLe (a * d) with
          | isTrue h =>
            apply isTrue
            rw [mk_eq_formalDiv, mk_eq_formalDiv, le_iff']
            obtain ⟨k, hk1, hk2⟩ := le_iff_exists_nonneg_add.mp h
            use k/(-(b*d):ℤ); constructor
            · rw [not_isNeg]; use k; use (-(b*d):ℤ)
              constructor; omega; constructor; push_neg at hbd; omega; rfl
            · rw [← div_int_eq, add_eq, eq]; simp
              have : a * (b * d) = (a* d) * b := by ring
              rw [this, ← hk2]; ring; repeat simp_all

          | isFalse h =>
            apply isFalse
            rw [mk_eq_formalDiv, mk_eq_formalDiv, le_iff']; by_contra hdiv; push_neg at h
            obtain ⟨ r, hrpos, hr ⟩ := hdiv; apply hrpos
            have : r = (c//d) - (a//b) := by rw [← hr]; ring
            rw [sub_eq, neg_eq, add_eq] at this; rw [this]
            rw [div_int_eq, isNeg_iff_neg_isPos, ← neg_div]; simp
            use (c*b-d*a), (-(b*d)); constructor; linarith
            constructor; push_neg at hbd; linarith; simp; ring; repeat simp_all

  exact Quotient.recOnSubsingleton₂ n m this

/-- (Not from textbook) Establish the decidability of this order. -/
instance Rat.decidableRel : DecidableRel (· ≤ · : Rat → Rat → Prop) := by
  intro n m
  simp
  have : ∀ (n:PreRat) (m: PreRat),
      Decidable (Quotient.mk PreRat.instSetoid n ≤ Quotient.mk PreRat.instSetoid m) := by
    intro ⟨ a,b,hb ⟩ ⟨ c,d,hd ⟩
    -- at this point, the goal is morally `Decidable(a//b ≤ c//d)`, but there are technical
    -- issues due to the junk value of formal division when the denominator vanishes.
    -- It may be more convenient to avoid formal division and work directly with `Quotient.mk`.
    cases (0:ℤ).decLe (b*d) with
      | isTrue hbd =>
        cases (a * d).decLe (b * c) with
          | isTrue h =>
            apply isTrue
            rw [ mk_eq_formalDiv, mk_eq_formalDiv]
            rw [le_iff, lt_iff, isNeg, eq]
            rcases lt_or_eq_of_le h with (h | h)
            · left; rw [sub_eq, neg_eq, add_eq]
              use (b*c - a*d)/(b*d)
              constructor ; use (b*c - a*d), (b*d)
              constructor; apply Int.sub_pos_of_lt h
              constructor; positivity; simp
              rw [div_int_eq]; simp; ring
              have : b * d > 0 := by positivity
              repeat omega
            · right; rw [h]; ring
            exact hb; exact hd
          | isFalse h =>
            apply isFalse;
            rw [le_iff]; push_neg
            simp [Setoid.r]
            constructor
            · simp at h; rw [lt_iff, isNeg]; push_neg
              rw [ mk_eq_formalDiv, mk_eq_formalDiv]
              intro r rpos; rw [sub_eq, neg_eq, add_eq]
              have : (a*d + b *(-c)) = a*d - b*c := by ring
              rw [this]

              have : ((a * d - b * c) // (b * d) ).isPos := by
                use (a*d - b*c), (b*d)
                constructor; apply Int.sub_pos_of_lt h
                constructor; positivity;
                rw [← div_int_eq]; simp_all
              have hcontra: (-r).isNeg := (isPos_iff_neg_isNeg _ ).1 rpos
              intro hr; rw [← hr] at hcontra
              apply Rat.not_pos_and_neg; apply And.intro this hcontra
              repeat simp_all
            · linarith
      | isFalse hbd =>
        cases (b * c).decLe (a * d) with
          | isTrue h =>
            apply isTrue
            rw [le_iff, lt_iff, isNeg, sub_eq]; simp [Setoid.r]
            rw [ mk_eq_formalDiv, mk_eq_formalDiv, neg_eq, add_eq]
            rcases lt_or_eq_of_le h with (h | h)
            · left; use -((a*d - b*c )/(b*d))
              simp
              constructor
              · use (a*d-b*c), (-b*d)
                constructor; apply Int.sub_pos_of_lt h
                constructor; push_neg at hbd; linarith
                simp; rw [div_neg]
              · rw [div_int_eq]; congr 1; simp; ring; omega
            · right; rw [← h]; ring
            repeat simp_all
          | isFalse h =>
            apply isFalse
            rw [le_iff]; push_neg
            simp [Setoid.r]
            constructor
            · simp at h; rw [lt_iff, isNeg]; push_neg
              rw [mk_eq_formalDiv, mk_eq_formalDiv]
              intro r rpos; rw [sub_eq, neg_eq, add_eq]
              have : (a*d + b *(-c)) = a*d - b*c := by ring
              rw [this]

              have : ((a * d - b * c) // (b * d) ).isPos := by
                use (b*c - a*d), (-b*d)
                constructor; apply Int.sub_pos_of_lt h
                constructor; push_neg at hbd; linarith
                rw [div_int_eq]; simp; ring;
                simp at hbd; linarith

              have hcontra: (-r).isNeg := (isPos_iff_neg_isNeg _).1 rpos
              intro hr; rw [← hr] at hcontra
              apply Rat.not_pos_and_neg; apply And.intro this hcontra
              repeat simp_all
            · linarith

  exact Quotient.recOnSubsingleton₂ n m this

/-- (Not from textbook) Rat has the structure of a linear ordering. -/
instance Rat.instLinearOrder : LinearOrder Rat where
  le_refl := by
    intro a; right; rfl
  le_trans := by
    intro a b c hab hbc; rw [le_iff'] at *
    obtain ⟨ x, hnx, h1 ⟩ := hab; obtain ⟨ y, hny, h2 ⟩ := hbc
    use (x + y); rw [not_isNeg] at *; constructor
    · obtain ⟨ a1, b1, ha1, hb1, rfl ⟩ := hnx
      obtain ⟨ a2, b2, ha2, hb2, rfl ⟩ := hny
      use (a1*b2 + a2*b1), (b1*b2);
      constructor; positivity; constructor; positivity;
      repeat rw [← div_int_eq];
      rw [add_eq]; nth_rw 2 [mul_comm]
      repeat ((have hb12: b1*b2 > 0 := by positivity); repeat omega)
    · rw [← h2, ← h1]; ring
  lt_iff_le_not_ge := by
    intro a b;
    constructor <;> intro h1
    · constructor;
      · left; exact h1
      · rw [le_iff]; push_neg
        constructor <;> intro h2;
        · apply not_gt_and_lt _ _ ⟨h2, h1⟩
        · apply Rat.not_lt_and_eq _ _ ⟨h1, h2.symm⟩
    · rcases Rat.trichotomous' b a with (h | h | h)
      · omega
      · have : b ≤ a := by left; exact h
        exfalso; simp_all
      · have : b ≤ a := by right; exact h
        exfalso; simp_all

  le_antisymm := by
    intro a b hab hba; rw [le_iff] at *;
    rcases hab with (hab | hab) <;> rcases hba with (hba | hba)
    · exfalso; apply not_gt_and_lt; exact ⟨hab, hba⟩
    · exact hba.symm
    · exact hab
    · exact hab

  le_total := by
    intro a b;
    rcases Rat.trichotomous' a b with (h | h | h)
    · right; left; omega
    · left; left; exact h
    · right; right; exact h.symm
  toDecidableLE := decidableRel

lemma Rat.pos_iff_gt_zero (n:Rat) : n.isPos ↔ 0 < n := by
  constructor <;> intro h
  · simp [lt_iff,isNeg_iff_neg_isPos,h]
  · simp [lt_iff,isNeg_iff_neg_isPos] at h; exact h

lemma Rat.add_le_add_right' (a b : Rat) (hab : a ≤ b) (c : Rat) :
a + c ≤ b + c := by
  rw [le_iff] at hab
  rcases hab with (hab | hab)
  · left; apply add_lt_add_right _ hab
  · rw [hab]

lemma Rat.add_le_add_left' (a b : Rat) (hab : a ≤ b) (c : Rat) :
c + a ≤ c + b := by rw [add_comm c a, add_comm c b];
                    apply Rat.add_le_add_right' a b hab c

lemma Rat.mul_lt_mul_right' (x y z:Rat) (hxy: x < y) (hz: 0 < z) : x * z < y * z := by
  rw [← pos_iff_gt_zero] at hz; apply Rat.mul_lt_mul_right hxy hz

/-- (Not from textbook) Rat has the structure of a strict ordered ring. -/
instance Rat.instIsStrictOrderedRing : IsStrictOrderedRing Rat where
  add_le_add_left := by intro a b hab c; rw [add_comm c a, add_comm c b];
                        apply add_le_add_right' a b hab c
  add_le_add_right := add_le_add_right'
  mul_lt_mul_of_pos_left := by intro a b c hab hc; rw [mul_comm, mul_comm c b];
                               apply mul_lt_mul_right' a b c hab hc
  mul_lt_mul_of_pos_right := mul_lt_mul_right'
  le_of_add_le_add_left := by
    intro a b c h; have := add_le_add_left' (a+b) (a+c) h (-a)
    simp at this; exact this
  zero_le_one := by rw [le_iff']; use 1; rw [not_isNeg];
                    constructor; (use 1, 1; simp) ; (simp)

/-- Exercise 4.2.6 -/
theorem Rat.mul_lt_mul_right_of_neg (x y z:Rat) (hxy: x < y) (hz: z.isNeg) :
x * z > y * z := by
  rw [isNeg_iff_neg_isPos] at hz; change y*z < x*z; rw [lt_iff'] at *
  choose u hu using hxy; use u * (-z)
  constructor
  · apply pos_times_pos hu.1 hz
  · rw [← hu.2]; ring


end Chapter4_2

--------------- SECTION 4.3 ---------------

namespace Chapter4_3

/-- Definition 4.3.1 (Absolute value) -/
abbrev abs (x:ℚ) : ℚ := if x > 0 then x else (if x < 0 then -x else 0)


theorem abs_of_pos {x: ℚ} (hx: 0 < x) : abs x = x := by grind

theorem abs_of_pos' {x: ℚ} (hx: 0 ≤  x) : abs x = x := by
  rw [le_iff_lt_or_eq] at hx
  rcases hx with hx | hx <;> simp [hx]

/-- Definition 4.3.1 (Absolute value) -/

theorem abs_of_neg {x: ℚ} (hx: x < 0) : abs x = -x := by
  have : ¬ (x > 0) := by linarith
  unfold abs; simp [this, hx]

theorem abs_of_neg' {x: ℚ} (hx: x ≤  0) : abs x = -x := by
  rw [le_iff_lt_or_eq] at hx
  rcases hx with hx | hx
  · exact abs_of_neg hx
  · simp [hx]

/-- Definition 4.3.1 (Absolute value) -/

theorem abs_of_zero : abs 0 = 0 := rfl

/-
  (Not from textbook) This definition of absolute value agrees with the Mathlib one.
  Henceforth we use the Mathlib absolute value.
-/
@[simp]
theorem abs_eq_abs (x: ℚ) : |x| = abs x  := by
  by_cases h : x > 0
  · rw [abs_of_pos h,_root_.abs_of_pos h]
  · by_cases h' : x < 0
    · rw [abs_of_neg h', _root_.abs_of_neg h']
    · have : x = 0 := by linarith
      rw [this, abs_of_zero, _root_.abs_zero]

abbrev dist (x y : ℚ) := |x - y|

/-
  Definition 4.2 (Distance).
  We avoid the Mathlib notion of distance here because it is real-valued.
-/
theorem dist_eq (x y: ℚ) : dist x y = |x-y| := rfl

/-- Proposition 4.3.3(a) / Exercise 4.3.1 -/
theorem abs_nonneg (x: ℚ) : |x| ≥ 0 := by
  rcases le_total x 0 with (h | h)
  · simp [abs_of_neg' h]; exact h
  · simp [abs_of_pos' h]; exact h

theorem abs_nonneg' (x: ℚ) : abs (x) ≥ 0 := by
  rw [← abs_eq_abs]; apply abs_nonneg

/-- Proposition 4.3.3(a) / Exercise 4.3.1 -/
theorem abs_eq_zero_iff (x: ℚ) : |x| = 0 ↔ x = 0 := by
  constructor <;> intro h1
  · rcases le_total x 0 with (h | h)
    · simp [abs_of_neg' h] at h1; exact h1
    · simp [abs_of_pos' h] at h1; exact h1
  · simp [h1];

/-- Proposition 4.3.3(c) / Exercise 4.3.1 -/
theorem le_abs (x:ℚ) : -|x| ≤ x ∧ x ≤ |x| := by
  rcases le_total x 0 with (h | h)
  · rw [abs_eq_abs, abs_of_neg' h]; ring_nf;
    constructor; simp;
    -- Show the method once to demonstrate that I know what's going on
    · (have : x ≤ 0 := h); (have : 0 ≤ -x := by linarith); linarith
  · simp [abs_of_pos' h]; exact h


lemma negx_le_abs (x:ℚ) : -x ≤ |x| := by have:= le_abs x; linarith

/-- Proposition 4.3.3(b) / Exercise 4.3.1 -/
theorem abs_add (x y:ℚ) : |x + y| ≤ |x| + |y| := by
  rcases le_total (x+y) 0 with (h | h)
  · rw [abs_eq_abs, abs_of_neg' h]; ring_nf
    linarith [negx_le_abs x, negx_le_abs y]
  · rw [abs_eq_abs, abs_of_pos' h]; ring_nf
    linarith [le_abs x, le_abs y]




/-- Proposition 4.3.3(c) / Exercise 4.3.1 -/
theorem abs_le_iff (x y:ℚ) : -y ≤ x ∧ x ≤ y ↔ |x| ≤ y := by
  rcases le_total x 0 with (hx | hx)
  · simp [abs_of_neg' hx]; constructor <;> intro h
    · linarith -- Flip the sign of h.1
    · constructor
      · linarith -- Flip signs on h
      · have : 0 ≤ -x := by linarith -- x ≤ 0 ≤ -x ≤ y
        linarith
  · simp [abs_of_pos' hx]; intro h
    have : 0 ≤ y := by linarith -- 0 ≤ x ≤ y
    have : -y ≤ 0 := by linarith -- Flip sign
    linarith -- -y ≤ 0 ≤ x


/-
    The alternative for case 1 used before looked something like this (ew):
    have : (x*y) = (-x)*(-y) := by ring;
    rw [this]; (have : 0 ≤ (-x) := by linarith); have : 0 ≤ (-y) := by linarith;
    have : 0 ≤ (-x)*(-y) := by positivity;
    rw [abs_of_pos' this]
    -/

/-- Proposition 4.3.3(d) / Exercise 4.3.1 -/
theorem abs_mul (x y:ℚ) : |x * y| = |x| * |y| := by
  rcases le_total x 0 with (hx | hx) <;> rcases le_total y 0 with (hy | hy)
  · (repeat rw [abs_eq_abs]); rw [abs_of_neg' hx, abs_of_neg' hy];
    suffices (x*y) ≥ 0  by rw [abs_of_pos' this]; ring
    apply mul_nonneg_of_nonpos_of_nonpos hx hy
  · (repeat rw [abs_eq_abs]); rw [abs_of_neg' hx, abs_of_pos' hy];
    suffices (x*y) ≤ 0  by rw [abs_of_neg' this]; ring
    apply mul_nonpos_of_nonpos_of_nonneg hx hy
  · (repeat rw [abs_eq_abs]); rw [abs_of_pos' hx, abs_of_neg' hy];
    suffices (x*y) ≤ 0  by rw [abs_of_neg' this]; ring
    apply mul_nonpos_of_nonneg_of_nonpos hx hy
  · (repeat rw [abs_eq_abs]); rw [abs_of_pos' hx, abs_of_pos' hy];
    suffices (x*y) ≥ 0  by rw [abs_of_pos' this];
    apply mul_nonneg hx hy

/-- Proposition 4.3.3(d) / Exercise 4.3.1 -/
theorem abs_neg (x:ℚ) : |-x| = |x| := by
  have : |x * (-1)| = |x| * |-1| := abs_mul x (-1)
  rw [abs_eq_abs] at *; simp at *; exact this


/-- Proposition 4.3.3(e) / Exercise 4.3.1 -/
theorem dist_nonneg (x y:ℚ) : dist x y ≥ 0 := abs_nonneg _

/-- Proposition 4.3.3(e) / Exercise 4.3.1 -/
theorem dist_eq_zero_iff (x y:ℚ) : dist x y = 0 ↔ x = y := by
  rw [abs_eq_zero_iff]; grind

/-- Proposition 4.3.3(f) / Exercise 4.3.1 -/
theorem dist_symm (x y:ℚ) : dist x y = dist y x := by
  unfold dist; rw [← neg_sub, abs_neg];

/-- Proposition 4.3.3(f) / Exercise 4.3.1 -/
theorem dist_le (x y z:ℚ) : dist x z ≤ dist x y + dist y z := by
  have : (x - z) = (x - y) + (y - z) := by ring
  unfold dist; rw [this]; apply abs_add

/-
  Definition 4.3.4 (eps-closeness).  In the text the notion is undefined for ε zero or negative,
  but it is more convenient in Lean to assign a "junk" definition in this case.  But this also
  allows some relaxations of hypotheses in the lemmas that follow.
-/
theorem close_iff (ε x y:ℚ): ε.Close x y ↔ |x - y| ≤ ε := by rfl

/-- Examples 4.3.6 -/
example : (0.1:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by
  rw [close_iff]; norm_num; rw [abs_of_pos (by norm_num)]; norm_num

/-- Examples 4.3.6 -/
example : ¬ (0.01:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by
  rw [close_iff]; norm_num; rw [abs_of_pos (by norm_num)]; norm_num

/-- Examples 4.3.6 -/
example (ε : ℚ) (hε : ε > 0) : ε.Close 2 2 := by
  rw [close_iff]; simp; linarith

theorem close_refl (x:ℚ) : (0:ℚ).Close x x := by rw [close_iff]; simp;

/-- Proposition 4.3.7(a) / Exercise 4.3.2 -/
theorem eq_if_close (x y:ℚ) : x = y ↔ ∀ ε:ℚ, ε > 0 → ε.Close x y := by
  constructor <;> intro h
  · intro e he; rw [h]; rw [close_iff]; simp; linarith
  · contrapose! h; use |x-y|/2
    have hnng:= abs_nonneg (x-y)
    have : |x-y| > 0 := by
      suffices |x-y| ≠ 0 by apply lt_of_le_of_ne hnng this.symm
      rw [abs_ne_zero]; contrapose! h; linarith
    constructor
    · suffices |x-y| > 0 by linarith
      exact this
    · rw [close_iff]; push_neg
      linarith

/-- Proposition 4.3.7(b) / Exercise 4.3.2 -/
theorem close_symm (ε x y:ℚ) : ε.Close x y ↔ ε.Close y x := by
  repeat rw [close_iff]; have := dist_symm x y
  unfold dist at this; rw [this]

/-- Proposition 4.3.7(c) / Exercise 4.3.2 -/
theorem close_trans {ε δ x y z:ℚ} (hxy: ε.Close x y) (hyz: δ.Close y z) :
    (ε + δ).Close x z := by
    repeat rw [close_iff] at *;
    have := dist_le x y z; unfold dist at this; linarith

/-- Proposition 4.3.7(d) / Exercise 4.3.2 -/
theorem add_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x+z) (y+w) := by
    rw [close_iff] at *;
    have : |(x + z) - (y + w)| = |(x - y) + (z - w)| := by ring_nf
    have:= abs_add (x - y) (z - w); linarith

/-- Proposition 4.3.7(d) / Exercise 4.3.2 -/
theorem sub_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x-z) (y-w) := by
    rw [close_iff] at *;
    rw [← abs_neg] at hzw; conv at hzw => lhs; arg 1 ; simp
    have : |(x - z) - (y - w)| = |(x - y) + (w - z)| := by ring_nf
    have := abs_add (x - y) (w - z); linarith


/-- Proposition 4.3.7(e) / Exercise 4.3.2, slightly strengthened -/
theorem close_mono {ε ε' x y:ℚ} (hxy: ε.Close x y) (hε: ε' ≥  ε) :
    ε'.Close x y := by rw [close_iff] at *; linarith

theorem close_between' {e x y z w:ℚ} (hxy: e.Close x y) (hxz: e.Close x z)
  (hbetween: (y ≤ w ∧ w ≤ z)) : e.Close x w := by
  rw [close_iff] at *;
  rcases le_total w x with (h | h)
  · have : 0 ≤ x - w := by linarith;
    simp [abs_of_pos' this]
    (have : y ≤ x := by linarith); have : 0 ≤ x - y := by linarith
    simp [abs_of_pos' this] at hxy
    linarith -- x ≤ y + e ≤ x + w + e  (being close to y is more restrictive)
  · have : x-w ≤ 0 := by linarith;
    simp [abs_of_neg' this]
    (have : x ≤ z := by linarith); have : (x-z) ≤  0 := by linarith
    simp [abs_of_neg' this] at hxz
    linarith -- x ≥ z - e ≥ x - w - e  (being close to z is more restrictive)

/-- Proposition 4.3.7(f) / Exercise 4.3.2 -/
theorem close_between {ε x y z w:ℚ} (hxy: ε.Close x y) (hxz: ε.Close x z)
  (hbetween: (y ≤ w ∧ w ≤ z) ∨ (z ≤ w ∧ w ≤ y)) : ε.Close x w := by
  rw [close_iff] at *;
  rcases hbetween with (h | h)
  · apply close_between' hxy hxz h
  · apply close_between' hxz hxy h

/-- Proposition 4.3.7(g) / Exercise 4.3.2 -/
theorem close_mul_right {ε x y z:ℚ} (hxy: ε.Close x y) :
    (ε*|z|).Close (x * z) (y * z) := by
    rw [close_iff] at *;
    (have : (x * z) - (y * z) = (x - y) * z := by ring); rw [this]
    rw [abs_mul]; have := abs_nonneg z
    gcongr -- Mul |z| on both sides of hxy

/-- Proposition 4.3.7(h) / Exercise 4.3.2 -/
theorem close_mul_mul {ε δ x y z w:ℚ} (hε: ε ≥ 0) (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε*|z|+δ*|x|+ε*δ).Close (x * z) (y * w) := by
  -- The proof is written to follow the structure of the original text, though
  -- on formalization it was revealed that the hypothesis δ ≥ 0 was unnecessary.
  set a := y-x
  have ha : y = x + a := by grind
  have haε: |a| ≤ ε := by rwa [close_symm, close_iff] at hxy
  set b := w-z
  have hb : w = z + b := by grind
  have hbδ: |b| ≤ δ := by rwa [close_symm, close_iff] at hzw
  have : y*w = x * z + a * z + x * b + a * b := by grind
  rw [close_symm, close_iff]
  calc
    _ = |a * z + b * x + a * b| := by
        rw [mul_comm b]; rw [this]; simp; congr; ring -- grind wasn't working
    _ ≤ |a * z + b * x| + |a * b| := abs_add _ _
    _ ≤ |a * z| + |b * x| + |a * b| := by
      have := abs_add (a*z) (b*x); linarith -- grind wasn't working
    _ = |a| * |z| + |b| * |x| + |a| * |b| := by grind [abs_mul]
    _ ≤ _ := by gcongr

/-- This variant of Proposition 4.3.7(h) was not in the textbook, but can be useful
in some later exercises. -/
theorem close_mul_mul' {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε*|z|+δ*|y|).Close (x * z) (y * w) := by
    -- Fun fact, I actually found this proof before I found the one above.
    rw [close_iff] at *;

    have h:= abs_add (x*z - y*z) (y*z - y*w);
    have h3: x*z - y*z = (x - y) * z := by ring;
    nth_rw 2 [h3] at h; rw [abs_mul] at h
    have h4: y*z - y*w = y * (z - w) := by ring
    nth_rw 2 [h4] at h; rw [abs_mul] at h; nth_rw 6 [mul_comm] at h
    calc
      _ = |x * z - y * z + (y * z - y * w)| := by ring_nf
      _ ≤ |x - y| * |z| + |z - w| * |y|:= h
    gcongr


/-- Definition 4.3.9 (exponentiation).  Here we use the Mathlib definition. -/
lemma pow_zero (x:ℚ) : x^0 = 1 := rfl

example : (0:ℚ)^0 = 1 := pow_zero 0

/-- Definition 4.3.9 (exponentiation).  Here we use the Mathlib definition. -/
lemma pow_succ (x:ℚ) (n:ℕ) : x^(n+1) = x^n * x := _root_.pow_succ x n


/-
For the sake of Chapter 5, I'm gonna write these proofs in such a way
that they apply to both the rationals and the reals.

I'll be borrowing some typeclasses from Mathlib to do so in a clean way.
Seems easy, but there was a remarkable amount of re-configuring a couple proofs
so that they are compatible with the type class.

I considered just using the Field typeclass for everything and calling it a day, but I'd rather use the weaker typeclasses if possible: keeps my proofs
more general, and prevents me from using overkill theorems that I don't
need.
-/

theorem pow_add' {G : Type*} [inst : Monoid G] (x : G) (m n : ℕ):
  x^n * x^m = x^(n+m) := by
  induction' n with n ih
  · rw [zero_add, _root_.pow_zero, one_mul];
  · rw [show n + 1 + m = (n + m) + 1 by ring]
    repeat rw [_root_.pow_succ']
    rw [← ih, mul_assoc]


theorem pow_mul' {G : Type*} [inst : Monoid G] (x : G) (m n : ℕ):
  (x^n)^m = x^(n*m) := by
  induction' m with m ih
  · rw [mul_zero, _root_.pow_zero, _root_.pow_zero];
  · rw [_root_.pow_succ]; have : n * (m + 1) = n * m + n := by ring;
    rw [this, ← pow_add', ih]


theorem mul_pow' {G : Type*} [inst : CommMonoid G] (x y : G) (n : ℕ):
  (x * y)^n = x^n * y^n := by
  induction' n with n ih
  · rw [_root_.pow_zero, _root_.pow_zero, _root_.pow_zero, one_mul];
  · rw [_root_.pow_succ, _root_.pow_succ, _root_.pow_succ, ih];
    nth_rw 2 [mul_assoc]; nth_rw 3 [← mul_assoc]
    rw [mul_comm x (y^n)]
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc]


theorem pow_eq_zero' {G : Type*} [inst : MonoidWithZero G] [NoZeroDivisors G]
  (x : G) (n : ℕ) (hn : 0 < n) :
  x^n = 0 ↔ x = 0 := by
  constructor <;> intro h
  · induction' n with n ih
    · tauto
    · by_cases hn : 0 < n
      · rw [_root_.pow_succ] at h
        rw [mul_eq_zero] at h; rcases h with (h | h)
        · exact ih hn h
        · exact h
      · have : n = 0 := by linarith;
        simp [this] at h; exact h
  · have hp1 : ∃ r, n = r + 1 := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn);
    rw [hp1.choose_spec]; rw [_root_.pow_succ]; simp [h]


theorem pow_ne_zero' {G : Type*} [inst : MonoidWithZero G] [NoZeroDivisors G]
  (x : G) (n : ℕ) (hn : 0 < n) :
  x^n ≠ 0 ↔ (x ≠ 0) := by
  constructor <;> contrapose!;
  exact (pow_eq_zero' _ _ hn).2; exact (pow_eq_zero' _ _ hn).1



theorem pow_nonneg' {G : Type*} [inst : MonoidWithZero G] [Preorder G]
  [ZeroLEOneClass G] [PosMulMono G]
  {x : G} (n:ℕ) (hx: x ≥ 0) : x^n ≥ 0 := by
  induction' n with n ih
  · rw [_root_.pow_zero]; norm_num
  · rw [_root_.pow_succ]; apply mul_nonneg ih hx

/-
theorem pow_nonneg{G : Type u_2} [MonoidWithZero G] [Preorder G] {a : G} [ZeroLEOneClass G] [PosMulMono G] (ha : 0 ≤ a) (n : ℕ) :
0 ≤ a ^ n
-/

/-
Important, weird thing I learned: we need
nontriviality for Lean to infer that 0 < 1

It seems that 0 ≠ 1 isn't promised if G isn't nontrivial (doesn't just contain nothing or one object).

Lean can figure out that this type is nontrivial, but it won't check for that fact if we don't ask it to.

Once we've reminded it that this could be relevant information, it's smart
enough to then combine this knowledge with the other typeclass
instances for G, and infer that
(0:G) ≠ (1:G).

In other words: it *could* find the information we need to solve the problem, but it won't do so automatically (presumably, there are too many facts that *could* be useful, and it doesn't bother grabbing them all). So, we tell it to grab that info, and once it has that in hand, it'll figure out the rest.
-/
#check pow_pos

theorem pow_pos' {G : Type*} [inst : MonoidWithZero G] [PartialOrder G]
  [ZeroLEOneClass G] [PosMulStrictMono G]
  {x : G} (hx: x > 0) : ∀ (n : ℕ), x^n > 0 := by
  intro n; induction' n with n ih
  · nontriviality; -- G is nontrivial! This allows Lean to infer 0 < 1
    rw [_root_.pow_zero]; norm_num
  · rw [_root_.pow_succ]; apply mul_pos ih hx

#check Chapter4_2.Rat.mul_lt_mul_right'
-- Using mul_lt_mul_right' to justify using mul_le_mul_of_nonneg_left below


theorem pow_ge_pow' {G : Type*} [MonoidWithZero G] [Preorder G] [ZeroLEOneClass G] [PosMulMono G] [MulPosMono G]
(x y:G) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 0) : x^n ≥ y^n := by
  induction' n with n ih
  · rw [_root_.pow_zero, _root_.pow_zero];
  · rw [_root_.pow_succ, _root_.pow_succ];
    have hx:= le_trans hy hxy
    have := pow_nonneg' n hx; have := pow_nonneg' n hy
    change y^n * y ≤ x^n * x
    calc
      _ ≤ y^n * x := mul_le_mul_of_nonneg_left hxy this
      _ ≤ x^n * x := mul_le_mul_of_nonneg_right ih hx



theorem pow_gt_pow' {G : Type*} [MonoidWithZero G] [PartialOrder G] [ZeroLEOneClass G] [PosMulStrictMono G] [MulPosMono G]
(x y:G) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) :
x^n > y^n := by
  induction' n with n ih
  · contradiction
  · by_cases hn : 0 < n
    · rw [_root_.pow_succ, _root_.pow_succ]; have hx:= lt_of_le_of_lt hy hxy
      have := pow_pos' hx n; have := pow_nonneg' n hy
      suffices y * y^n  < x* x^n by gcongr
      calc
        _ ≤ x * y^n  := mul_le_mul_of_nonneg_right (le_of_lt hxy) this
        _ < x * x^n := mul_lt_mul_of_pos_left (ih hn) hx
    · have :  n = 0 := by linarith;
      rw [this]; simp; exact hxy

theorem pow_abs' {G : Type*} [inst : Ring G] [inst1 : LinearOrder G] [IsStrictOrderedRing G]
  (x : G) (n : ℕ) : |x|^n = |x^n| := by
  induction' n with n ih
  · rw [_root_.pow_zero, _root_.pow_zero]; norm_num
  · rw [_root_.pow_succ, _root_.pow_succ, _root_.abs_mul, ih]

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_add (x:ℚ) (m n:ℕ) : x^n * x^m = x^(n+m) := pow_add' x m n

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_mul (x:ℚ) (m n:ℕ) : (x^n)^m = x^(n*m) := pow_mul' x m n

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem mul_pow (x y:ℚ) (n:ℕ) : (x*y)^n = x^n * y^n := mul_pow' x y n

/-- Proposition 4.3.10(b) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_eq_zero (x:ℚ) (n:ℕ) (hn : 0 < n) : x^n = 0 ↔ x = 0 := pow_eq_zero' x n hn

theorem pow_ne_zero (x:ℚ) (n:ℕ) (hn: 0 < n)  : x^n ≠ 0 ↔ (x ≠ 0) := pow_ne_zero' x n hn

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_nonneg {x:ℚ} (n:ℕ) (hx: x ≥ 0) : x^n ≥ 0 := pow_nonneg' n hx

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_pos {x:ℚ} (n:ℕ) (hx: x > 0) : x^n > 0 := pow_pos' hx n

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_ge_pow (x y:ℚ) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 1) : x^n ≥ y^n :=
pow_ge_pow' x y n hxy (by linarith [hy])

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_gt_pow (x y:ℚ) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) :
x^n > y^n := pow_gt_pow' x y n hxy hy hn

/-- Proposition 4.3.10(d) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_abs (x:ℚ) (n:ℕ) : |x|^n = |x^n| := pow_abs' x n



/-
  Definition 4.3.11 (Exponentiation to a negative number).
  Here we use the Mathlib notion of integer exponentiation
-/
theorem zpow_neg {G : Type*} [DivisionMonoid G] (x:G) (n:ℕ) : x^(-(n:ℤ)) = 1/(x^n) := by simp

example (x:ℚ): x^(-3:ℤ) = 1/(x^3) := zpow_neg x 3

example (x:ℚ): x^(-3:ℤ) = 1/(x*x*x) := by convert zpow_neg x 3; ring

theorem pow_eq_zpow {G : Type*} [DivisionMonoid  G] (x:G) (n:ℕ): x^(n:ℤ) = x^n := zpow_natCast x n


theorem zpow_neg' {G : Type*} [DivisionMonoid G] (x:G) (z: ℤ ) : x^(-z) = 1/(x^z) := by
  rcases le_total z 0 with (hz | hz)
  · nth_rw 2 [show z = -(-z).toNat by simp [hz]];
    rw [zpow_neg, ← pow_eq_zpow];
    rw [show (-z).toNat = -z  by simp [hz]];
    simp
  · rw [show z = (z.toNat:ℤ) by simp [hz] ]
    rw [zpow_neg, pow_eq_zpow];

-- Exists already in Int but I don't wanna have to grab it
theorem toNat_of_nonneg {z:ℤ} (hz: z ≥ 0) : ∃ m : ℕ, z = (m:ℤ) := by
  use z.toNat; simp [hz]

theorem toNat_of_neg {z:ℤ} (hz: z < 0) : ∃ n : ℕ, z = -(n:ℤ) := by
  use (-z).toNat; rw [← neg_neg z]; congr; simp; omega

theorem toNat_of_nonpos {z:ℤ} (hz: z ≤ 0) : ∃ n : ℕ, z = -(n:ℤ) := by
  use (-z).toNat; rw [← neg_neg z]; congr; simp; omega
/-
I didn't want to figure out which coercions would be useful,
so I borrowed from https://github.com/rkirov/analysis-/

lemma cast_add (a b:ℕ): (a + b: ℕ) = (a: ℤ) + (b: ℤ) := by rfl
lemma cast_mul (a b:ℕ): (a * b: ℕ) = (a: ℤ) * (b: ℤ) := by rfl
lemma cast_sub (a b:ℕ) (h: b ≤ a): (a - b: ℕ) = (a: ℤ) - (b: ℤ) := by exact Int.ofNat_sub h
lemma cast_add_int_toNat (a:ℕ) (b:ℕ): ((a + b):ℤ) = a + (b:ℤ) := by rfl




theorem zpow_ne_zero {G : Type*} [GroupWithZero G] {x : G} (n : ℤ ) (hx : x ≠ 0 ) : x^n ≠ 0 := by
  rcases lt_trichotomy n 0 with (h | h | h)
  · rw [show n = -((-n).toNat) by omega]; rw [zpow_neg]
    apply one_div_ne_zero
    apply _root_.pow_ne_zero
    exact hx
  · simp [h]
  · lift n to ℕ using (by linarith);
    rw [pow_eq_zpow]; simp at h
    apply _root_.pow_ne_zero
    exact hx

#check inv_zpow

theorem inv_zpow {G : Type*} [DivisionMonoid G] (a : G) (n : ℤ) :
  a^(-n) = (a^n)⁻¹ := by rw [← one_div, zpow_neg']

#check inv_pow
theorem inv_zpow' {G : Type*} [DivisionMonoid G] (a : G) (n : ℤ) :
a^(-n) = (a⁻¹)^n := by -- Both cases: revert to a case of inv_pow
  by_cases h : n ≥ 0
  · lift n to ℕ using h; rw [zpow_neg, one_div, ← inv_pow, pow_eq_zpow]
  · nth_rw 2 [show n = - - n by omega ]; lift (-n) to ℕ using (by linarith) with k hk
    rw [zpow_neg', one_div]; repeat rw [pow_eq_zpow]
    rw [inv_pow, inv_inv];

/-
This was my original approach that only worked with Field G.
Relies on commutativity, which is not given in GroupWithZero.
-/
theorem zpow_add'' {G : Type*} [Field G] (x:G) (n m:ℤ) (hx: x ≠ 0): x^n * x^m = x^(n+m) := by
  -- Assume n has greater magnitude (determines the sign of the sum): works by symm
  wlog hnm : |n| ≥ |m|
  · push_neg at hnm; specialize this x m n hx (by omega)
    rw [mul_comm, add_comm, this];
  obtain ⟨a, ha⟩ := Int.eq_nat_or_neg n
  -- Assume n is positive: if n is negative, then we move all terms to the opposite side of the equation, making the negative exponent positive.
  wlog han : a = n
  · push_neg at han; simp [han.symm] at ha
    specialize this x (-n) (-m) hx (by simp [hnm]) a (by omega) (by omega)
    (have hnm : -n + (- m) = -(n + m) := by ring); rw [hnm] at this
    repeat rw [zpow_neg'] at this
    field_simp [(zpow_ne_zero n hx), (zpow_ne_zero m hx), (zpow_ne_zero (n+m) hx)] at this
    exact this.symm
  -- Last split: check whether m is positive or negative
  obtain ⟨b, hb⟩ := Int.eq_nat_or_neg m
  rcases hb with rfl | rfl
  · rw [← han, pow_eq_zpow, pow_eq_zpow, ← _root_.pow_add, ← pow_eq_zpow];
    congr -- Positive case: reducible to nat exponentiation
  · rw [← han] at *; -- Negative case: move to the other side, add
    rw [zpow_neg']; repeat rw [pow_eq_zpow]; field_simp; ring_nf
    simp at hnm; rw [← cast_sub _ _ hnm]
    rw [pow_eq_zpow, pow_add']; congr; omega

/-
Clean approach to zpow_add where we gradually build up multiplication with a
zpow element:
· first, multiplying by x,
· then multiplying by x^n (where (n : ℕ )),
· then finally multiplying by x^m (where (m : ℤ )).
-/
#check zpow_add_one₀
theorem zpow_succ {G : Type*} [GroupWithZero G] (z : ℤ) (x : G) (hx : x ≠ 0) :
  x^(z + 1) = x^z * x := by
  by_cases h : z ≥ 0
  · lift z to ℕ using h; rw [pow_eq_zpow, ← _root_.pow_succ, ← pow_eq_zpow];
    rw [show (z+1 :ℤ) = (z+1 :ℕ) by omega ];
  · rw [← inv_mul_eq_iff_eq_mul₀]; symm; rw [ ← mul_inv_eq_iff_eq_mul₀]
    repeat rw [← inv_zpow]
    lift (-(z+1)) to ℕ using (by linarith) with k hk
    rw [pow_eq_zpow, ← _root_.pow_succ', ← pow_eq_zpow]
    simp [hk]; apply zpow_ne_zero (z+1) hx;apply zpow_ne_zero z hx

theorem zpow_add_pow {G : Type*} [GroupWithZero G] (z : ℤ ) (x : G) (n : ℕ ) (hx : x ≠ 0) :
  x^(z + (n:ℤ)) = x^z * x^n := by
  induction' n with n ih
  · simp
  · simp [← add_assoc]; rw [zpow_succ, ih]
    rw [mul_assoc, _root_.pow_succ]; exact hx

#check zpow_add₀
theorem zpow_add''' {G : Type*} [GroupWithZero G] (x:G) (n m:ℤ) (hx: x ≠ 0): x^n * x^m = x^(n+m) := by
  rcases le_total m 0 with (h | h)
  · nth_rw 1 [show m = - (- m).toNat by omega];
    rw [zpow_neg', pow_eq_zpow];
    field_simp [zpow_ne_zero (-m).toNat hx]
    rw [← zpow_add_pow]; congr; omega; exact hx
  · lift m to ℕ using h
    · rw [zpow_add_pow]; simp; exact hx

/-
Third approach: this one builds on the second approach, but also derives
commutativity of x^n and x^m.
-/
lemma zpow_mul_self_zpow_comm {G : Type*} [GroupWithZero G] (x:G) (n m:ℤ) (hx: x ≠ 0):
  x^n * x^m = x^m * x^n := by
  wlog hn : n ≥ 0
  · push_neg at hn; specialize this x (-n) m hx (by linarith)
    field_simp [(zpow_ne_zero n hx)] at this
    nth_rw 1 [← this];
    rw [mul_assoc, ← mul_assoc]; simp [(zpow_ne_zero n hx)]
  wlog hm : m ≥ 0
  · push_neg at hm; specialize this x n (-m) hx hn (by linarith)
    field_simp [(zpow_ne_zero m hx)] at this
    nth_rw 2 [this];
    rw [mul_assoc, ← mul_assoc]; simp [(zpow_ne_zero m hx)]
  lift n to ℕ using hn; lift m to ℕ using hm;
  repeat rw [pow_eq_zpow];
  repeat rw [← _root_.pow_add]
  congr 1; ring

theorem pow_add_zpow {G : Type*} [GroupWithZero G] (z : ℤ ) (x : G) (n : ℕ ) (hx: x ≠ 0):
  x^((n:ℤ) + z) = x^n * x^z := by
  rw [add_comm, ← pow_eq_zpow, zpow_mul_self_zpow_comm, zpow_add_pow];
  simp; exact hx; exact hx


theorem zpow_add'''' {G : Type*} [GroupWithZero G] (x:G) (n m:ℤ) (hx: x ≠ 0): x^n * x^m = x^(n+m) := by
  by_cases h : n ≥ 0
  · lift n to ℕ using h; rw [pow_add_zpow, pow_eq_zpow]; exact hx
  · nth_rw 1 [show n = - (- n).toNat by omega];
    rw [zpow_neg', pow_eq_zpow];
    rw [one_div,inv_mul_eq_iff_eq_mul₀]
    rw [← pow_add_zpow]; congr; omega
    exact hx; apply _root_.pow_ne_zero _ hx


/-
Fourth approach: this method successfully solves the problem with only 3 cases!
(Technically m=0 is a case but it's trivial and doesn't require any work.)
-/
theorem zpow_add''''' {G : Type*} [GroupWithZero G] (x:G) (n m:ℤ) (hx: x ≠ 0):
  x^n * x^m = x^(n+m) := by
  wlog hnm : n + m ≥ 0 -- Invert both sides --> make sum positive
  · specialize this x (-m) (-n) hx (by omega)
    field_simp [zpow_ne_zero (n) hx, zpow_ne_zero (m) hx] at this
    rw [show -m + - n = -(n + m) by ring] at this
    symm at this
    rw [zpow_neg',one_div, mul_assoc, inv_mul_eq_iff_eq_mul₀] at this
    rw [this]; simp; apply zpow_ne_zero _ hx

  by_cases hn: m ≥ 0
  · lift m to ℕ using hn
    clear hnm
    induction' m with m ih;
    · simp
    simp; rw [← add_assoc]; repeat rw [zpow_succ]
    rw [← ih, ← mul_assoc]
    exact hx; exact hx

  · symm; rw [← mul_inv_eq_iff_eq_mul₀, ← inv_zpow];
    lift (-m) to ℕ using (by linarith) with a ha
    lift (n+m) to ℕ using (by linarith) with b hb
    repeat rw [pow_eq_zpow];
    rw [← _root_.pow_add, ← pow_eq_zpow]; congr; omega;
    apply zpow_ne_zero _ hx;

/-
Fifth approach: only two cases! I guess three, if you choose to separate out the
inductive base case. This matches the performance of the Mathlib proof.

This was accomplished by
1. cutting out half the space with n+m < 0
2. Inducting perpendicular to that boundary: inducting over values of n+m,
    rather than n or m individually. This meant I didn't need a separate case
    for n < 0 or m < 0: they were already accommodated.

This approach most directly mirrors the structure of the problem, based on x^(n+m).
-/

theorem zpow_add' {G : Type*} [GroupWithZero G] (x:G) (n m:ℤ) (hx: x ≠ 0):
  x^n * x^m = x^(n+m) := by
  wlog hnm : n + m ≥ 0 -- Invert both sides --> make sum positive
  · specialize this x (-m) (-n) hx (by omega)
    field_simp [zpow_ne_zero (n) hx, zpow_ne_zero (m) hx] at this
    rw [show -m + - n = -(n + m) by ring] at this
    symm at this
    rw [zpow_neg',one_div, mul_assoc, inv_mul_eq_iff_eq_mul₀] at this
    rw [this]; simp; apply zpow_ne_zero _ hx
  lift (n + m) to ℕ using hnm with y hy
  induction' y with y ih generalizing n m
  · rw [show n = -m by omega]; field_simp [zpow_ne_zero m hx]
  specialize ih n (m-1) (by simp at *; linarith)
  simp; rw [show m = (m-1) + 1 by omega]; repeat rw [zpow_succ]
  rw [← ih, mul_assoc]; exact hx; exact hx

/-
Misc stuff I never ended up using
-/

theorem neg_pow_add {G : Type*} [GroupWithZero G] (x:G) (n m:ℕ) (hx: x ≠ 0) :
  x^(-(n:ℤ)) * x^(-(m:ℤ)) = x^(-((n+m : ℕ):ℤ)) := by
  repeat rw [zpow_neg']
  field_simp
  rw [one_div, mul_assoc, ← _root_.pow_add]
  have := _root_.pow_ne_zero (m + n) hx
  convert (inv_mul_cancel₀ this).symm
  rw [← pow_eq_zpow]; congr; omega

#check zpow_mul
#check inv_inj

/-
Back to normal stuff
-/


lemma neg_zpow_inj' {G : Type*} [DivisionMonoid G] {a b : G} {n m : ℤ} (h : a^(-n) = b^(-m)) : a^n = b^m :=
  by
    have := congr_arg (· * a^n) h
    have := congr_arg (b^m * · ) this
    simp_all


#check inv_zpow
#check inv_zpow'
theorem zpow_mul' {G : Type*} [DivisionMonoid G] (x:G) (n m:ℤ) : (x^n)^m = x^(n*m) := by
  -- Negative cases can be generalized to positive
  -- Then, we just invoke pow_mul
  wlog hn: n ≥ 0
  · specialize this x (-n) (-m) (by omega)
    nth_rw 2 [inv_zpow] at this; rw [inv_zpow', inv_inv] at this
    simpa
  lift n to ℕ using hn
  wlog hm: m ≥ 0
  · specialize this x (-m) n (by omega)
    rw [show n * (-m) = -(n*m) by ring] at this
    simpa [neg_zpow_inj']
  lift m to ℕ using hm
  rw [← cast_mul]; repeat rw [pow_eq_zpow];
  rw [_root_.pow_mul];

theorem pow_div' {G : Type*} [DivisionMonoid G] (x:G) (m:ℕ) : (1/x)^m = 1/(x^m) := by
  induction' m with m ih
  · rw [_root_.pow_zero, _root_.pow_zero]; norm_num
  · rw [_root_.pow_succ', _root_.pow_succ, ih];
    simp

#check mul_zpow
#check inv_inv

theorem mul_zpow' {G : Type*} [DivisionCommMonoid G] (x y:G) (n:ℤ) :
(x*y)^n = x^n * y^n := by
  wlog hn : n ≥ 0
  · specialize this x y (-n) (by omega)
    field_simp [zpow_neg'] at this
    rwa [← inv_inj, ← one_div, ← one_div]
  lift n to ℕ using hn; repeat rw [pow_eq_zpow];
  apply mul_pow'


/-
This is basically pulled directly from Basic.lean, for practice-/
theorem inv_pos{G : Type*} [GroupWithZero G] [PartialOrder G] [PosMulReflectLT G] {a : G} :
  0 < a⁻¹ ↔ 0 < a := by
  suffices h : ∀ (x:G), 0 < x → 0 < x⁻¹ from -- The "from" keyword seems to be
    ⟨by nth_rw 2 [← inv_inv a];exact h a⁻¹, h a⟩ -- for construction instead of proof
  intro x hx
  apply lt_of_mul_lt_mul_left _ hx.le -- Also learning about .le convention, cool
  apply lt_of_mul_lt_mul_left _ hx.le -- Instead of 0 < 1, we want 0 < x
  rw [mul_inv_cancel₀ hx.ne']
  simpa

/-
This one is a little messy: it requires PosMulStrictMono to use pow_pos (which
is the obvious solution), but Lean is too dumb to infer it.

So, I used the Basic.lean approach to convert PosMulReflectLT ∧ GroupWithZero to
PosMulStrictMono.
This feels a little like cheating, but whatever. I could manually re-define the
lemma with (ostensibly but not really) weaker constraints, but that
seems like a waste of time.
-/
theorem zpow_pos' {G : Type*} [inst : GroupWithZero G] [inst_1 : PartialOrder G]
[PosMulReflectLT G] [ZeroLEOneClass G]
{x:G} (n:ℤ) (hx: x > 0) : x^n > 0 := by
  haveI : PosMulStrictMono G := PosMulReflectLT.toPosMulStrictMono G
  rcases lt_trichotomy n 0 with (h | h | h)
  · rw [show n = - - n by omega]; rw [zpow_neg', one_div];
    rw [gt_iff_lt, inv_pos]
    lift (-n) to ℕ using (by linarith) with m hm
    rw [pow_eq_zpow]; apply pow_pos' hx
  · simp [h]
  · lift n to ℕ using (by linarith); rw [pow_eq_zpow];
    rw [gt_iff_lt]; apply pow_pos' hx

/-
At this point, I got into a weird insane mess realizing that only SOME VERSIONS
of pow_le_pow_left₀ require ZeroLEOneClass.

Apparently, it's because 4 months ago (today is 12/29/2025, so like August I guess),
someone modified pow_le_pow_left₀ to not require ZeroLEOneClass, by using a clever
n+2 induction.

Also zpow_le_zpow_left₀ was added 4 days ago LOL, I guess that explains why I was
confused that I couldn't find it locally.

So, for sanity's sake, I'll just use ZeroLEOneClass. Especially since pow_le_pow_left₀
uses weird induction, and I'm not currently practicing that.

Sure did learn a lot, though.
-/

#check pow_le_pow_left₀

-- Used to infer desired typeclass instances (borrowed from Basic.lean)
attribute [local instance] PosMulReflectLT.toPosMulStrictMono
  PosMulReflectLT.toPosMulReflectLE PosMulReflectLT.toMulPosReflectLT
  MulPosReflectLT.toMulPosReflectLE


theorem zpow_ge_zpow' {G : Type*} [GroupWithZero G] [PartialOrder G]
[PosMulReflectLT G] [MulPosMono G] [ZeroLEOneClass G]
{x y : G} {n : ℤ} (hxy : x ≥ y) (hy : y > 0) (hn : n > 0) : x^n ≥ y^n := by
  lift n to ℕ using (by linarith)
  repeat rw [pow_eq_zpow];
  apply pow_ge_pow' _ _ _ hxy hy.le

/-
This theorem doesn't seem to have an exact match in mathlib
I wasn't sure exactly how much I need, so I just added the instance I
immediately wanted: MulPosReflectLT.
-/

theorem zpow_ge_zpow_ofneg' {G : Type*} [GroupWithZero G] [PartialOrder G]
[PosMulReflectLT G] [MulPosReflectLT G] [MulPosMono G] [ZeroLEOneClass G]
{x y : G} {n : ℤ} (hxy : x ≥ y) (hy : y > 0) (hn : n < 0) : x^n ≤ y^n := by
  refine le_of_mul_le_mul_left ?_ (zpow_pos' (-n) hy) -- Move y^m to the other side
  rw [zpow_add'];
  have : x > 0 := lt_of_lt_of_le hy hxy
  refine le_of_mul_le_mul_right ?_ (zpow_pos' (-n) this) -- Move x^m to the other side
  rw [mul_assoc, zpow_add' ];
  simp [-_root_.zpow_neg] -- Cancel out terms
  apply zpow_ge_zpow' hxy hy (by linarith)
  exact this.ne'; exact hy.ne'

-- Another indirect victim of removing [ZeroLEOneClass G]
-- I'll just add it back in; I don't wanna deal with the current proof, relies on
-- similar n+2 cleverness.

theorem pow_inj' {G : Type*} [MonoidWithZero G] [LinearOrder G] [PosMulStrictMono G] [ZeroLEOneClass G]
{x y : G} {n : ℕ} [MulPosMono G] (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) :
x = y := by
  rcases lt_trichotomy x y with (h | h | h)
  · have := pow_gt_pow' y x n h (le_of_lt hx) (by omega);
    have := ne_of_gt this; symm at this; contradiction
  · exact h
  · have := pow_gt_pow' x y n h (le_of_lt hy) (by omega);
    have := ne_of_gt this; contradiction

theorem zpow_inj' {G : Type*} [GroupWithZero G] [LinearOrder G] [PosMulStrictMono G] [ZeroLEOneClass G]
{x y : G} {n : ℤ} [MulPosMono G] (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n)
: x = y := by
  wlog hnp: n > 0
  · have hn': -n > 0 := by omega;
    refine this hx hy hn'.ne' ?_ hn'
    repeat rw [zpow_neg'];
    rw [hxy]
  lift n to ℕ using (by linarith); repeat rw [pow_eq_zpow] at hxy
  apply pow_inj' hx hy (by linarith) hxy

lemma abs_one_div' {G : Type*} [Field G] [LinearOrder G] [IsStrictOrderedRing G] (a : G) :
|1 / a| = 1 / |a| := by
  rcases le_total a 0 with (ha0 | ha0)
  · rw [abs_of_nonpos (one_div_nonpos.mpr ha0), abs_of_nonpos ha0]; ring
  · rw [abs_of_nonneg (one_div_nonneg.mpr ha0), abs_of_nonneg ha0];

/-
Mathlib uses abs_zpow, which has the same constraints as abs_one_div. So,
we use the same typeclasses here.
-/

theorem zpow_abs' {G : Type*} [Field G] [LinearOrder G] [IsStrictOrderedRing G] (x : G) (n : ℤ) : |x|^n = |x^n| := by
  wlog hn0 : n ≥ 0
  · push_neg at hn0; obtain ⟨m, hm⟩ := toNat_of_neg (by omega); subst hm
    rw [zpow_neg', zpow_neg', this x m (by omega), abs_one_div']
  obtain ⟨m, hm⟩ := toNat_of_nonneg hn0; subst hm; repeat rw [pow_eq_zpow];
  apply pow_abs'


theorem zpow_add (x : ℚ) (n m : ℤ ) (hx: x ≠ 0): x^n * x^m = x^(n + m) := zpow_add' x n m hx

lemma pow_div (x : ℚ ) (m : ℕ ): (1/x)^m = 1/(x^m) := pow_div' x m

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_mul (x:ℚ) (n m:ℤ) : (x^n)^m = x^(n*m) := zpow_mul' x n m

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem mul_zpow (x y:ℚ) (n:ℤ) : (x*y)^n = x^n * y^n := mul_zpow' x y n

/-- Proposition 4.3.12(b) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_pos {x:ℚ} (n:ℤ) (hx: x > 0) : x^n > 0 := zpow_pos' n hx

/-- Proposition 4.3.12(b) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_ge_zpow {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n > 0):
x^n ≥ y^n := zpow_ge_zpow' hxy hy hn



theorem zpow_ge_zpow_ofneg {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n < 0)
: x^n ≤ y^n := zpow_ge_zpow_ofneg' hxy hy hn

#check pow_lt_pow_left₀


#check zpow_left_inj


theorem pow_inj {x y:ℚ} {n:ℕ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n)
: x = y := pow_inj' hx hy hn hxy

/-
theorem zpow_right_inj₀{G₀ : Type u_3} [GroupWithZero G₀] [LinearOrder G₀] {a : G₀} {m n : ℤ} [PosMulStrictMono G₀] [ZeroLEOneClass G₀] (ha₀ : 0 < a) (ha₁ : a ≠ 1) :
a ^ m = a ^ n ↔ m = n
-/



/-- Proposition 4.3.12(c) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_inj {x y:ℚ} {n:ℤ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n)
: x = y := zpow_inj' hx hy hn hxy

#check abs_one_div




lemma abs_one_div {x : ℚ} : |1/x| = 1/|x| := abs_one_div' x



/-- Proposition 4.3.12(d) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_abs (x:ℚ) (n:ℤ) : |x|^n = |x^n| := zpow_abs' x n

/-- Exercise 4.3.5 -/
theorem two_pow_geq (N:ℕ) : 2^N ≥ N := by
  induction' N with N ih
  · norm_num;
  · rw [Nat.pow_succ];
    by_cases hn : N ≥ 1
    · suffices 2*N ≥ N + 1 by linarith
      linarith
    · have : N = 0 := by linarith;
      subst this; rw [Nat.pow_zero, Nat.one_mul, Nat.zero_add]; norm_num

end Chapter4_3
--------------- SECTION 4.4 ---------------

namespace Chapter4_4

#check Nat.div_add_mod

theorem toNat_of_nonneg {z:ℤ} (hz: z ≥ 0) : ∃ m : ℕ, z = (m:ℤ) := by
  use z.toNat; simp [hz]

theorem toNat_of_neg {z:ℤ} (hz: z < 0) : ∃ n : ℕ, z = -(n:ℤ) := by
  use (-z).toNat; rw [← neg_neg z]; congr; simp; omega

theorem toNat_of_nonpos {z:ℤ} (hz: z ≤ 0) : ∃ n : ℕ, z = -(n:ℤ) := by
  use (-z).toNat; rw [← neg_neg z]; congr; simp; omega

lemma cast_sub (a b:ℕ) (h: b ≤ a): (a - b: ℕ) = (a: ℤ) - (b: ℤ) := by exact Int.ofNat_sub h

-- We were suggested to use Proposition 2.3.9
theorem euclid_algorithm (n q : ℕ) (hq : q > 0) :
∃ (m r : ℕ), (0 ≤ r ∧ r < q ∧ n = m * q + r):= by
  use n / q, n % q
  simp_all
  constructor
  · apply Nat.mod_lt n hq
  · have := Nat.div_add_mod n q
    rw [mul_comm, this]

-- But we need to generalize this to integers
theorem euclid_algorithm' (z : ℤ) (q : ℕ) (hq : q > 0) :
∃ (m : ℤ )(r : ℕ), (r < q ∧ z = m * q + r):= by
  rcases le_total z 0 with (hz | hz)
  · choose z' hz' using toNat_of_nonpos hz
    choose a b hab using (euclid_algorithm z' q hq)
    by_cases hb : b = 0
    · use -a, 0; simp [hq, hz', hab.2, hb]
    · use -(a+1), q - b; observe : 0 < b
      simp [hq, this, hz', hab.2.2]
      simp [cast_sub q b (by omega)]; ring
  · choose z' hz' using toNat_of_nonneg hz
    choose a b hab using (euclid_algorithm z' q hq)
    use a, b; simp [hab.2.1, hz', hab.2.2];


/-- Proposition 4.4.1 (Interspersing of integers by rationals) / Exercise 4.4.1 -/
theorem Rat.between_int (x:ℚ) : ∃! n:ℤ, n ≤ x ∧ x < n+1 := by
  choose m r hr hmr using euclid_algorithm' x.num x.den (by positivity)
  apply existsUnique_of_exists_of_unique
  · use m
    constructor
    · rw [←Rat.num_div_den x, hmr, le_iff_exists_nonneg_add];
      use r/x.den; field_simp;
      apply div_nonneg (by positivity) (by positivity)

    · rw [←Rat.num_div_den x, hmr, ]; simp; simp [add_div];
      have: (r : ℚ ) < (x.den : ℚ) := by field_simp; exact hr
      rw [div_lt_one (by positivity)]; exact this


  · intro z1 z2 ⟨hz11, hz12⟩ ⟨hx21, hx22⟩
    rcases lt_trichotomy z1 z2 with (h | h | h)
    · exfalso; have : ((z1 + 1) : ℚ) ≤ z2 := by exact_mod_cast (by linarith);
      linarith
    · exact h
    · exfalso; have : ((z2 + 1) : ℚ) ≤ z1 := by exact_mod_cast (by linarith);
      linarith

theorem Nat.exists_gt (x:ℚ) : ∃ n:ℕ, n > x := by
  choose n hn1 _ using Rat.between_int x; obtain ⟨hn11, hn12⟩ := hn1
  choose m hm using Int.eq_nat_or_neg n
  rcases hm with rfl | rfl
  · simp at hn12; use m + 1; simp [hn12]
  · use 1; simp at hn12; simp;
    linarith [show (m + 1 : ℚ) > 0 by positivity]

/-- Proposition 4.4.3 (Interspersing of rationals) -/
theorem Rat.exists_between_rat {x y:ℚ} (h: x < y) : ∃ z:ℚ, x < z ∧ z < y := by
  use (x+y)/2
  have h' : x/2 < y/2 := by
    rw [show x/2 = x*(1/2) by ring, show y/2 = y*(1/2) by ring]
    apply mul_lt_mul_of_pos_right h; positivity
  constructor
  · convert add_lt_add_right h' (x/2) using 1 <;> ring
  convert add_lt_add_right h' (y/2) using 1 <;> ring

theorem Rat.exists_between_rat' {x y:ℚ} (h: x < y) : ∃ z:ℚ, x < z ∧ z < y := by
  use (x+y)/2; constructor <;> linarith

/-- Exercise 4.4.2 -/
theorem Nat.no_infinite_descent : ¬ ∃ a:ℕ → ℕ, ∀ n, a (n+1) < a n := by
  intro h; choose f hf using h
  have : ∀ k n, f n > k:= by
    intro k
    induction' k with k ih
    · intro n; by_contra h; have : f n = 0 := by omega;
      specialize hf n; rw [this] at hf; contradiction
    · intro n; specialize ih (n+1)
      specialize hf n; linarith
  specialize this (f 0) 0; omega

def Int.infinite_descent : Decidable (∃ a:ℕ → ℤ, ∀ n, a (n+1) < a n) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isTrue; use fun n ↦ -n; intro n; simp

#check even_iff_exists_two_mul
#check odd_iff_exists_bit1

theorem Nat.even_or_odd'' (n:ℕ) : Even n ∨ Odd n := by
  induction' n with n ih
  · left; use 0
  · rcases ih with (ihe | iho)
    · right; choose k hk using ihe; use k; rw [hk]; ring
    · left; choose k hk using iho; use k + 1; rw [hk]; ring

theorem Nat.not_even_and_odd (n:ℕ) : ¬ (Even n ∧ Odd n) := by
  intro ⟨he,ho⟩; choose k hk using he; choose m hm using ho
  rw [hk] at hm; have : 2*(k - m) = 1 := by ring; omega
  by_cases h: k - m ≤ 0
  · observe hkm: k-m = 0
    rw [hkm] at this; simp at this
  · push_neg at h; observe h2 : 2*(k - m) ≥ 2
    rw [this] at h2; simp at h2

#check Nat.rec
#check Int.eq_natCast_toNat -- This could be useful! Note to self

/-- Proposition 4.4.4 / Exercise 4.4.3 -/
theorem Rat.not_exist_sqrt_two : ¬ ∃ x:ℚ, x^2 = 2 := by
  -- This proof is written to follow the structure of the original text.
  by_contra h; choose x hx using h
  have hnon : x ≠ 0 := by aesop
  wlog hpos : x > 0
  · push_neg at hpos; observe hx0 : -x ≥ 0 ; observe h0 : -x ≠ 0
    exact this (-x) (by simp [hx]) h0 (lt_of_le_of_ne hx0 h0.symm)
  have hrep : ∃ p q:ℕ, p > 0 ∧ q > 0 ∧ p^2 = 2*q^2 := by
    use x.num.toNat, x.den
    observe hnum_pos : x.num > 0
    observe hden_pos : x.den > 0
    refine ⟨ by simp [hpos], hden_pos, ?_ ⟩
    rw [←Rat.num_div_den x] at hx; field_simp at hx
    have hnum_cast : x.num = x.num.toNat := Int.eq_natCast_toNat.mpr (by positivity)
    rw [hnum_cast] at hx; norm_cast at hx --norm_cast can close goals
  -- P p := p^2 can be split in half to get another number q^2
  set P : ℕ → Prop := fun p ↦ p > 0 ∧ ∃ q > 0, p^2 = 2*q^2
  have hP : ∃ p, P p := by aesop
  -- If p^2 can be split, then there's some smaller q^2 that can be split
  have hiter (p:ℕ) (hPp: P p) : ∃ q, q < p ∧ P q := by
    obtain hp | hp := p.even_or_odd
    · -- p is even
      obtain ⟨ k, rfl ⟩ := hp --Because p was even, we can break it into 2*k
      rw [show k+k = 2*k by ring] at *
      choose q hpos hq using hPp.2 -- Split p^2 to get q^2
      -- q^2 and k^2 both come from p^2, but q^2 is smaller
      have : q^2 = 2 * k^2 := by linarith -- We can split q^2 to get k^2
      use q; constructor
      · rcases lt_trichotomy q (2*k) with hlt | heq | hgt
        · exact hlt
        · rw [heq] at hq; ring_nf at hq; have : k > 0 := by linarith
          have : k^2 > 0 := by apply pow_pos; exact this
          have : 4 = 8 := by linarith
          contradiction
        · exfalso;
          have:= pow_lt_pow_left₀ (n := 2) hgt (by linarith) (by norm_num)
          have : (2*k)^2 < 2 * q^2 := by omega
          omega
      · unfold P; exact ⟨ hpos, k, by linarith [hPp.1], this ⟩
    · -- p can't be odd because p^2 = 2*q^2 is even
      have h1 : Odd (p^2) := by
        choose k hk using hp; rw [hk]; use 2*k + 2*k^2; ring
      have h2 : Even (p^2) := by
        choose q hpos hq using hPp.2
        use q^2; rw [hq]; ring
      observe : ¬(Even (p ^ 2) ∧ Odd (p ^ 2))
      tauto
  classical
  -- Function f produces the smaller number q from p
  set f : ℕ → ℕ := fun p ↦ if hPp: P p then (hiter p hPp).choose else 0
  -- f always produces a smaller number q (= f p) from p that can be split (again)
  have hf (p:ℕ) (hPp: P p) : (f p < p) ∧ P (f p) := by
    simp [f, hPp]; exact (hiter p hPp).choose_spec
  -- Grab some p that can be split
  choose p hP using hP
  -- Recursively apply f to produce an infinite descending chain of natural numbers
  set a : ℕ → ℕ := Nat.rec p (fun n p ↦ f p)
  -- Prove that all a n have the desired properties (smaller, splittable)
  have ha (n:ℕ) : P (a n) := by
    induction n with
    | zero => exact hP -- Original p known to be splittable
    | succ n ih => exact (hf (a n) ih).2 -- f p is splittable if p is
  -- Prove that all a n are strictly descending
  have hlt (n:ℕ) : a (n+1) < a n := by
    have : a (n+1) = f (a n) := n.rec_add_one p (fun n p ↦ f p)
    rw [this]; specialize hf (a n) (ha n); exact hf.1
    --grind
  exact Nat.no_infinite_descent ⟨ a, hlt ⟩


/-- Proposition 4.4.5 -/
theorem Rat.exist_approx_sqrt_two {ε:ℚ} (hε:ε>0) : ∃ x ≥ (0:ℚ), x^2 < 2 ∧ 2 < (x+ε)^2 := by
  -- This proof is written to follow the structure of the original text.
  by_contra! h
  have (n:ℕ): (n*ε)^2 < 2 := by
    induction' n with n hn; simp
    simp [add_mul]
    apply lt_of_le_of_ne
    · apply (h (n*ε) (by positivity) hn)
    · have := not_exist_sqrt_two
      aesop
  choose n hn using Nat.exists_gt (2/ε)
  rw [gt_iff_lt, div_lt_iff₀', mul_comm, ←sq_lt_sq₀] at hn <;> try positivity
  have hne: 2 < (n*ε)^2 := by linarith
  have hne' := this n
  linarith

/-- Example 4.4.6 -/
example :
  let ε:ℚ := 1/1000
  let x:ℚ := 1414/1000
  x^2 < 2 ∧ 2 < (x+ε)^2 := by norm_num

end Chapter4_4
