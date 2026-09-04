
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
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Peel
import Mathlib.Tactic.CancelDenoms

import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Order.Ring.InjSurj
import Mathlib.Algebra.Order.Hom.Ring
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Ring.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity

import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

import Project
open scoped Pointwise -- to use `s + t` for sets




-- Only necessary so I don't see some yellow lines
set_option linter.unusedVariables false
set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.unusedSectionVars false
set_option linter.style.docString false

--------------- SECTION 5.1 ---------------

namespace Chapter5

attribute [-simp] Chapter4_3.abs_eq_abs

lemma abs_eq_abs' (x : ℚ) :  Chapter4_3.abs x = |x| := by
  symm; exact Chapter4_3.abs_eq_abs x

/-
  Definition 5.1.1 (Sequence). To avoid some technicalities involving dependent types, we extend
  sequences by zero to the left of the starting point `n₀`.
-/
@[ext]
structure Sequence where
  n₀ : ℤ
  seq : ℤ → ℚ
  vanish : ∀ n < n₀, seq n = 0

/-- Sequences can be thought of as functions from ℤ to ℚ. -/
instance Sequence.instCoeFun : CoeFun Sequence (fun _ ↦ ℤ → ℚ) where
  coe := fun a ↦ a.seq

/--
Functions from ℕ to ℚ can be thought of as sequences starting from 0; `ofNatFun` performs this conversion.

The `coe` attribute allows the delaborator to print `Sequence.ofNatFun f` as `↑f`, which is more concise; you may safely remove this if you prefer the more explicit notation.
-/
@[coe]
def Sequence.ofNatFun (a : ℕ → ℚ) : Sequence where
    n₀ := 0
    seq n := if n ≥ 0 then a n.toNat else 0
    vanish := by grind

-- Notice how the delaborator prints this as `↑fun x ↦ ↑x ^ 2 : Sequence`.
--#check Sequence.ofNatFun (· ^ 2)

/--
If `a : ℕ → ℚ` is used in a context where a `Sequence` is expected, automatically coerce `a` to `Sequence.ofNatFun a` (which will be pretty-printed as `↑a`)
-/
instance : Coe (ℕ → ℚ) Sequence where
  coe := Sequence.ofNatFun

-- Set builder usually creates subset, but since we're in a typed system we instead
-- get a sub-TYPE `{ n // n ≥ n₀ }`
abbrev Sequence.mk' (n₀:ℤ) (a: { n // n ≥ n₀ } → ℚ) : Sequence where
  n₀ := n₀
  seq n := if h : n ≥ n₀ then a ⟨n, h⟩ else 0
  vanish := by grind

lemma Sequence.eval_mk {n n₀:ℤ} (a: { n // n ≥ n₀ } → ℚ) (h: n ≥ n₀) :
    (Sequence.mk' n₀ a) n = a ⟨ n, h ⟩ := by grind

@[simp]
lemma Sequence.eval_coe (n:ℕ) (a: ℕ → ℚ) : (a:Sequence) n = a n := by norm_cast

@[simp]
lemma Sequence.eval_coe_at_int (n:ℤ) (a: ℕ → ℚ) : (a:Sequence) n = if n ≥ 0 then a n.toNat else 0 := by norm_cast

@[simp]
lemma Sequence.n0_coe (a: ℕ → ℚ) : (a:Sequence).n₀ = 0 := by norm_cast

/-- Example 5.1.2 -/
abbrev Sequence.squares : Sequence := ((fun n:ℕ ↦ (n^2:ℚ)):Sequence)

/-- Example 5.1.2 -/
example (n:ℕ) : Sequence.squares n = n^2 := Sequence.eval_coe _ _

/-- Example 5.1.2 -/
abbrev Sequence.three : Sequence := ((fun (_:ℕ) ↦ (3:ℚ)):Sequence)

/-- Example 5.1.2 -/
example (n:ℕ) : Sequence.three n = 3 := Sequence.eval_coe _ (fun (_:ℕ) ↦ (3:ℚ))

/-- Example 5.1.2 -/
abbrev Sequence.squares_from_three : Sequence := mk' 3 (·^2)

/-- Example 5.1.2 -/
example (n:ℤ) (hn: n ≥ 3) : Sequence.squares_from_three n = n^2 := Sequence.eval_mk _ hn

-- need to temporarily leave the `Chapter5` namespace to introduce the following notation

end Chapter5

/--
A slight generalization of Definition 5.1.3 - definition of ε-steadiness for a sequence with an
arbitrary starting point n₀
-/
abbrev Rat.Steady (ε: ℚ) (a: Chapter5.Sequence) : Prop :=
  ∀ n ≥ a.n₀, ∀ m ≥ a.n₀, ε.Close (a n) (a m)

lemma Rat.steady_def (ε: ℚ) (a: Chapter5.Sequence) :
  ε.Steady a ↔ ∀ n ≥ a.n₀, ∀ m ≥ a.n₀, ε.Close (a n) (a m) := by rfl

namespace Chapter5

/--
Definition 5.1.3 - definition of ε-steadiness for a sequence starting at 0
-/
lemma Rat.Steady.coe (ε : ℚ) (a:ℕ → ℚ) :
    ε.Steady a ↔ ∀ n m : ℕ, ε.Close (a n) (a m) := by
  constructor
  · intro h n m; specialize h n ?_ m ?_ <;> simp_all
  intro h x hx y hy
  lift x to ℕ using hx
  lift y to ℕ using hy
  simp [h x y]

/--
Not in textbook: the sequence 3, 3 ... is 1-steady
Intended as a demonstration of `Rat.Steady.coe`
-/
example : (1:ℚ).Steady ((fun _:ℕ ↦ (3:ℚ)):Sequence) := by
  simp [Rat.Steady.coe, Rat.Close]

/--
Compare: if you need to work with `Rat.Steady` on the coercion directly, there will be side
conditions `hn : n ≥ 0` and `hm : m ≥ 0` that you will need to deal with.
-/
example : (1:ℚ).Steady ((fun _:ℕ ↦ (3:ℚ)):Sequence) := by
  intro n _ m _; simp_all [Sequence.n0_coe, Sequence.eval_coe_at_int, Rat.Close]

/--
Example 5.1.5: The sequence `1, 0, 1, 0, ...` is 1-steady.
-/
example : (1:ℚ).Steady ((fun n:ℕ ↦ if Even n then (1:ℚ) else (0:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]
  intro n m
  -- Split into four cases based on whether n and m are even or odd
  -- In each case, we know the exact value of a n and a m
  split_ifs <;> simp [Rat.Close]

/--
Example 5.1.5: The sequence `1, 0, 1, 0, ...` is not ½-steady.
-/
example : ¬ (0.5:ℚ).Steady ((fun n:ℕ ↦ if Even n then (1:ℚ) else (0:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]
  by_contra h; specialize h 0 1; simp [Rat.Close] at h
  norm_num at h

/--
Example 5.1.5: The sequence 0.1, 0.01, 0.001, ... is 0.1-steady.
-/
example : (0.1:ℚ).Steady ((fun n:ℕ ↦ (10:ℚ) ^ (-(n:ℤ)-1) ):Sequence) := by
  rw [Rat.Steady.coe]
  intro n m; unfold Rat.Close
  wlog h : m ≤ n
  · specialize this m n (by linarith); rwa [abs_sub_comm]
  rw [abs_sub_comm, abs_of_nonneg]
  · rw [show (0.1:ℚ) = (10:ℚ)^(-1:ℤ) - 0 by norm_num]
    gcongr; norm_num
    · grind
    · apply zpow_nonneg; norm_num
  linarith [show (10:ℚ) ^ (-(n:ℤ)-1) ≤ (10:ℚ) ^ (-(m:ℤ)-1) by gcongr; norm_num]

/--
Example 5.1.5: The sequence 0.1, 0.01, 0.001, ... is not 0.01-steady. Left as an exercise.
-/
example : ¬(0.01:ℚ).Steady ((fun n:ℕ ↦ (10:ℚ) ^ (-(n:ℤ)-1) ):Sequence) := by
  rw [Rat.Steady.coe]; push_neg;
  use 0, 1; unfold Rat.Close;
  rw [abs_of_nonneg] <;> (simp; norm_num)

/-- Example 5.1.5: The sequence 1, 2, 4, 8, ... is not ε-steady for any ε. Left as an exercise.
-/
example (ε:ℚ) : ¬ ε.Steady ((fun n:ℕ ↦ (2 ^ (n+1):ℚ) ):Sequence) := by
  -- Notably, the sequence seems to start at 2 instead of 1 for some reason
  rw [Rat.Steady.coe]; push_neg
  choose n hn using exists_nat_gt ε
  use n+1, n; unfold Rat.Close; push_neg; rw [abs_of_nonneg]
  · calc
      ε < n+1 := by linarith
      _ < 2 ^ (n+1) := by norm_cast; apply Nat.lt_two_pow_self
      _ = 2 ^ (n + 1 + 1) - 2 ^ (n + 1) := by ring
  · simp; gcongr <;> norm_num


/-- Example 5.1.5:The sequence 2, 2, 2, ... is ε-steady for any ε > 0.
-/
example (ε:ℚ) (hε: ε>0) : ε.Steady ((fun _:ℕ ↦ (2:ℚ) ):Sequence) := by
  rw [Rat.Steady.coe]; simp [Rat.Close]; positivity

/--
The sequence 10, 0, 0, ... is 10-steady.
-/
example : (10:ℚ).Steady ((fun n:ℕ ↦ if n = 0 then (10:ℚ) else (0:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]; intro n m
  -- Split into 4 cases based on whether n and m are 0 or not
  split_ifs <;> simp [Rat.Close]

/--
The sequence 10, 0, 0, ... is not ε-steady for any smaller value of ε.
-/
example (ε:ℚ) (hε:ε<10):  ¬ ε.Steady ((fun n:ℕ ↦ if n = 0 then (10:ℚ) else (0:ℚ)):Sequence) := by
  contrapose! hε; rw [Rat.Steady.coe] at hε; specialize hε 0 1;
  simpa [Rat.Close] using hε

/-
  a.from n₁ starts `a:Sequence` from `n₁`.  It is intended for use when `n₁ ≥ n₀`, but returns
  the "junk" value of the original sequence `a` otherwise.
-/
abbrev Sequence.from (a:Sequence) (n₁:ℤ) : Sequence :=
  mk' (max a.n₀ n₁) (fun n ↦ a (n:ℤ))

lemma Sequence.from_eval (a:Sequence) {n₁ n:ℤ} (hn: n ≥ n₁) :
  (a.from n₁) n = a n := by simp [hn]; intro h; exact (a.vanish _ h).symm

end Chapter5

/-- Definition 5.1.6 (Eventually ε-steady) -/
abbrev Rat.EventuallySteady (ε: ℚ) (a: Chapter5.Sequence) : Prop :=
  ∃ N ≥ a.n₀, ε.Steady (a.from N)

lemma Rat.eventuallySteady_def (ε: ℚ) (a: Chapter5.Sequence) :
  ε.EventuallySteady a ↔ ∃ N ≥ a.n₀, ε.Steady (a.from N) := by rfl


namespace Chapter5

/--
Example 5.1.7: The sequence 1, 1/2, 1/3, ... is not 0.1-steady
-/
lemma Sequence.ex_5_1_7_a : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence) := by
  intro h; rw [Rat.Steady.coe] at h; specialize h 0 1;
  simp [Rat.Close] at h; norm_num at h
  rw [abs_eq_abs',abs_of_nonneg] at h
  · norm_num at h
  · positivity

/--
Example 5.1.7: The sequence a_10, a_11, a_12, ... is 0.1-steady
-/
lemma Sequence.ex_5_1_7_b : (0.1:ℚ).Steady (((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence).from 10) := by
  rw [Rat.Steady]
  intro n hn m hm; simp at hn hm
  lift n to ℕ using (by omega)
  lift m to ℕ using (by omega)
  simp_all [Rat.Close]
  wlog h : m ≤ n
  · specialize this m n _ _ _ <;> try omega
    rw [abs_eq_abs'] at *; rwa [abs_sub_comm] at this
  rw [abs_eq_abs']; rw [abs_sub_comm]
  have : ((n:ℚ) + 1)⁻¹ ≤ ((m:ℚ) + 1)⁻¹ := by gcongr
  rw [abs_of_nonneg (by linarith), show (0.1:ℚ) = (10:ℚ)⁻¹ - 0 by norm_num]
  gcongr
  · norm_cast; omega
  · positivity

/--
Example 5.1.7: The sequence 1, 1/2, 1/3, ... is eventually 0.1-steady
-/
lemma Sequence.ex_5_1_7_c : (0.1:ℚ).EventuallySteady ((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence) :=
  ⟨10, by simp, ex_5_1_7_b⟩ -- ⟨witness, proof⟩ for existence

/--
Example 5.1.7

The sequence 10, 0, 0, ... is eventually ε-steady for every ε > 0. Left as an exercise.
-/
lemma Sequence.ex_5_1_7_d {ε:ℚ} (hε:ε>0) :
    ε.EventuallySteady ((fun n:ℕ ↦ if n=0 then (10:ℚ) else (0:ℚ) ):Sequence) := by
      use 1; simp; rw [Rat.Steady]; intro n hn m hm; simp at hn hm
      simp [hn, hm, ]; rw [Rat.Close]
      split_ifs <;> try omega
      simp_all; positivity


abbrev Sequence.IsCauchy (a:Sequence) : Prop := ∀ ε > (0:ℚ), ε.EventuallySteady a

lemma Sequence.isCauchy_def (a:Sequence) :
  a.IsCauchy ↔ ∀ ε > (0:ℚ), ε.EventuallySteady a := by rfl



/-- Definition of Cauchy sequences, for a sequence starting at 0 -/
lemma Sequence.IsCauchy.coe (a:ℕ → ℚ) :
    (a:Sequence).IsCauchy ↔ ∀ ε > (0:ℚ), ∃ N, ∀ j ≥ N, ∀ k ≥ N,
    Chapter4_3.dist (a j) (a k) ≤ ε := by
  unfold Chapter4_3.dist
  constructor <;> intro h ε hε
  · choose N hN h' using h ε hε
    lift N to ℕ using hN; use N
    intro j _ k _; simp [Rat.steady_def] at h';
    specialize h' j _ k _  <;> try omega
    simp_all; rw [abs_eq_abs']; exact h'
  · choose N h' using h ε hε
    refine ⟨ N, by simp, ?_ ⟩ -- Why use max N 0?? N is a nat
    intro n hn m hm; simp at hn hm
    have npos : 0 ≤ n := ?_
    have mpos : 0 ≤ m := ?_
    lift n to ℕ using npos
    lift m to ℕ using mpos
    simp [hn, hm]; specialize h' n _ m _
    all_goals try omega
    norm_cast


lemma Sequence.IsCauchy.mk {n₀:ℤ} (a: {n // n ≥ n₀} → ℚ) :
    (mk' n₀ a).IsCauchy ↔ ∀ ε > (0:ℚ), ∃ N ≥ n₀, ∀ j ≥ N, ∀ k ≥ N,
    Chapter4_3.dist (mk' n₀ a j) (mk' n₀ a k) ≤ ε := by
  unfold Chapter4_3.dist
  constructor <;> intro h ε hε <;> choose N hN h' using h ε hε
  · --- N is the bound for both steadiness and accessing the sequence
    dsimp at hN; refine ⟨ N, hN, ?_ ⟩; intro j _ k _
    specialize h' j _ k _ <;> try simp; try omega -- j, k ≥ N ≥ n₀
    simp_all; rw [abs_eq_abs']; exact h'
  · refine ⟨ N, ?_ ⟩; simp [hN] -- max n₀ N not necessary
    intro n _ m _; simp_all;
    specialize h' n _ m _ <;> try omega
    simp only [abs_eq_abs'] at *; exact h'

lemma Sequence.IsCauchy.mk'' {n₀:ℤ} (a: {n // n ≥ n₀} → ℚ) :
    (mk' n₀ a).IsCauchy ↔ ∀ ε > (0:ℚ), ∃ N ≥ n₀, ∀ j ≥ N, ∀ k ≥ N,
    Chapter4_3.dist (mk' n₀ a j) (mk' n₀ a k) ≤ ε := by
  constructor <;> intro h ε hε <;> choose N hN h' using h ε hε
  · refine ⟨ N, hN, ?_ ⟩; dsimp at hN; intro j _ k _
    -- Clipped sequence starts from max of n₀ or N → starts from N
    simp only [Rat.Steady, show max n₀ N = N by omega] at h'
    specialize h' j _ k _ <;> try omega
    -- Applying function a is only valid if j, k ≥ N ≥ n₀
    simp_all [show n₀ ≤ j by omega, show n₀ ≤ k by omega]
    rw [abs_eq_abs']; exact h'
  refine ⟨ max n₀ N, by simp, ?_ ⟩
  intro n _ m _; simp_all
  simp only [abs_eq_abs'] at *;
  apply h' n _ m <;> omega

noncomputable def Sequence.sqrt_two : Sequence := (fun n:ℕ ↦ ((⌊ (Real.sqrt 2)*10^n ⌋ / 10^n):ℚ))




/-- Proposition 5.1.11. The harmonic sequence, defined as a₁ = 1, a₂ = 1/2, ... is a Cauchy sequence. -/
theorem Sequence.IsCauchy.harmonic : (mk' 1 (fun n ↦ (1:ℚ)/n)).IsCauchy := by
  rw [IsCauchy.mk]
  intro ε hε
  -- We go by reverse from the book - first choose N such that N > 1/ε
  obtain ⟨ N, hN ⟩ := exists_nat_gt (1 / ε) --  obtain ⟨ N, hN : N > 1/ε ⟩
  have hN' : N > 0 := by
    observe : (1/ε) > 0
    observe : (N:ℚ) > 0
    norm_cast at this
  refine ⟨ N, by norm_cast, ?_ ⟩
  intro j hj k hk
  lift j to ℕ using (by linarith)
  lift k to ℕ using (by linarith)
  norm_cast at hj hk
  simp [show j ≥ 1 by linarith, show k ≥ 1 by linarith]

  have hdist : Chapter4_3.dist ((1:ℚ)/j) ((1:ℚ)/k) ≤ (1:ℚ)/N := by
    rw [Chapter4_3.dist_eq]
    wlog h : j ≤ k
    · specialize this ε hε N hN hN' k j hk hj (by linarith)
      rwa [abs_sub_comm] at this
    rw [abs_of_nonneg]
    · rw [← sub_zero (1/(N:ℚ))]
      gcongr
      · positivity
    · simp; gcongr; norm_num; linarith
  simp at *; apply hdist.trans
  rw [inv_le_comm₀] <;> try positivity
  order

abbrev BoundedBy {n:ℕ} (a: Fin n → ℚ) (M:ℚ) : Prop := ∀ i, |a i| ≤ M

/--
  Definition 5.1.12 (bounded sequences). Here we start sequences from 0 rather than 1 to align better with Mathlib conventions.
-/
lemma boundedBy_def {n:ℕ} (a: Fin n → ℚ) (M:ℚ) : BoundedBy a M ↔ ∀ i, |a i| ≤ M := by rfl

abbrev Sequence.BoundedBy (a:Sequence) (M:ℚ) : Prop := ∀ n, |a n| ≤ M

/-- Definition 5.1.12 (bounded sequences) -/
lemma Sequence.boundedBy_def (a:Sequence) (M:ℚ) : a.BoundedBy M ↔ ∀ n, |a n| ≤ M := by rfl

attribute [-simp] Chapter4_3.abs_eq_abs

lemma Sequence.boundedBy_def' (a:Sequence) (M:ℚ) : a.BoundedBy M ↔ ∀ n ≥ a.n₀, |a n| ≤ M := by
  constructor <;> intro h n
  · intro hn; apply h
  · by_cases hn : n ≥ a.n₀
    · exact h n hn
    · specialize h (a.n₀ ) (by linarith)
      rw [a.vanish n (by linarith)]; apply le_trans _ h
      simp

abbrev Sequence.IsBounded (a:Sequence) : Prop := ∃ M ≥ 0, a.BoundedBy M

/-- Definition 5.1.12 (bounded sequences) -/
lemma Sequence.isBounded_def (a:Sequence) : a.IsBounded ↔ ∃ M ≥ 0, a.BoundedBy M := by rfl

/-- Example 5.1.13 -/
example : BoundedBy ![1,-2,3,-4] 4 := by intro i; fin_cases i <;> norm_num

lemma Sequence.isBounded_def.coe (a:ℕ → ℚ) :
    (a:Sequence).IsBounded ↔ ∃ M ≥ 0, ∀ n, |a n| ≤ M := by
  constructor <;> intro h <;> choose M hM ha using h
  <;> refine ⟨ M, hM, ?_ ⟩ <;> intro n;
  · exact ha n
  · by_cases hn : n ≥ 0 <;> simp [hn];
    · lift n to ℕ using hn; exact ha n
    · omega

/-- Example 5.1.13 -/
example : ¬((fun n:ℕ ↦ (-1)^n * (n+1:ℚ)):Sequence).IsBounded := by
  unfold Sequence.IsBounded Sequence.BoundedBy
  push_neg; intro M hM;
  choose N hN using exists_nat_gt M; use N;
  simp [abs_mul, abs_pow]
  rw [abs_of_pos] <;> linarith

/-- Example 5.1.13 -/
example : ((fun n:ℕ ↦ (-1:ℚ)^n):Sequence).IsBounded := by
  refine ⟨ 1, by norm_num, ?_ ⟩; intro i; by_cases h: 0 ≤ i <;> simp [h]

/-- Example 5.1.13 -/
example : ¬((fun n:ℕ ↦ (-1:ℚ)^n):Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe]
  by_contra h; specialize h (1/2 : ℚ) (by norm_num)
  choose N h using h; specialize h N _ (N+1) _ <;> try omega
  by_cases h': Even N
  · simp [h'.neg_one_pow, (h'.add_one).neg_one_pow, Chapter4_3.dist] at h;
    norm_num at h

  · observe h₁: Odd N
    observe h₂: Even (N+1)
    simp [h₁.neg_one_pow, h₂.neg_one_pow, Chapter4_3.dist] at h
    norm_num at h

/-- Lemma 5.1.14 -/
lemma IsBounded.finite {n:ℕ} (a: Fin n → ℚ) : ∃ M ≥ 0,  BoundedBy a M := by
  -- this proof is written to follow the structure of the original text.
  induction' n with n hn
  · use 0; simp
  set a' : Fin n → ℚ := fun m ↦ a m.castSucc
  choose M hpos hM using hn a'
  have h1 : BoundedBy a' (M + |a (Fin.ofNat _ n)|) := fun m ↦ (hM m).trans (by simp)
  have h2 : |a (Fin.ofNat _ n)| ≤ M + |a (Fin.ofNat _ n)| := by simp [hpos]
  refine ⟨ M + |a (Fin.ofNat _ n)|, by positivity, ?_ ⟩
  intro m; obtain ⟨ j, rfl ⟩ | rfl := Fin.eq_castSucc_or_eq_last m
  · grind
  · convert h2; simp

/-- Lemma 5.1.15 (Cauchy sequences are bounded) / Exercise 5.1.1 -/
lemma Sequence.isBounded_of_isCauchy {a:Sequence} (h: a.IsCauchy) : a.IsBounded := by
  -- Split sequence into finite region and 1-steady region
  choose N hN h using h 1 (by norm_num)
  -- Length of the finite region + 1
  let finN:= N - a.n₀ + 1
  -- Shift the finite region to start from 0
  let b : Fin (finN.toNat) → ℚ := fun m ↦ a (m + a.n₀)
  -- Finite bounded by M
  obtain ⟨ M, hMpos, hM ⟩ := IsBounded.finite b
  -- Bound of 1-steady region will be |a N| + 1; combine bounds
  have h1 : Chapter5.BoundedBy b (M + |(a N)|+1) := fun m ↦ (hM m).trans (by simp [add_assoc]; positivity)
  -- Because a n has to be 1-close to a N, |a n| can only be +/- 1 |a N|
  have h2' : ∀ n ≥ N, |a n| ≤ |a N|+1 := by
    intro n hn;
    specialize h n _ N _ <;> try simp [hn] <;> try linarith
    simp_all; rw [Rat.Close] at h
    calc -- Traveling 0 → a N → a n , second step can only add at most 1
      _ =  |(a n - a N) + a N| := by ring_nf
      _ ≤  |a n - a N| + |a N| := abs_add _ _
      _ ≤ |a N| + 1 := by linarith
  -- Combine bounds
  have h2 : ∀ n ≥ N, |a n| ≤ M + |a N| + 1 := fun n hn ↦
    (h2' n hn).trans (by simp; positivity)
  -- Use combined bound
  refine ⟨ M + |a N| + 1, by positivity, ?_ ⟩
  rw [Sequence.boundedBy_def']
  intro n hn0
  -- Split cases: finite region vs 1-steady region
  by_cases hn : n < N
  · specialize h1 ⟨ (n - a.n₀).toNat, by omega ⟩ -- Shifted index
    convert h1 -- To use finite proof, we just need to shift index back
    simp [hn0]
  · push_neg at hn; exact h2 n hn -- No work necessary

/-- Exercise 5.1.2 -/
theorem Sequence.isBounded_add {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hb: (b:Sequence).IsBounded):
    (a + b:Sequence).IsBounded := by
  rw [Sequence.isBounded_def.coe] at *
  choose M hM ha using ha
  choose N hN hb using hb
  refine ⟨ M + N, by positivity, ?_ ⟩
  intro n; specialize ha n; specialize hb n
  simp; have := abs_add (a n) (b n)
  linarith

lemma Sequence.isBounded_neg {a:ℕ → ℚ} (ha: (a:Sequence).IsBounded) :
    ((-a : ℕ → ℚ ):Sequence).IsBounded := by
  rw [Sequence.isBounded_def.coe] at *
  choose M hM ha using ha
  refine ⟨ M, hM, ?_ ⟩
  intro n; specialize ha n
  simp; exact ha

theorem Sequence.isBounded_sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hb: (b:Sequence).IsBounded):
    (a - b:Sequence).IsBounded := by
  rw [show a - b = a + (-b) by ring]
  apply isBounded_neg at hb
  exact isBounded_add ha hb

theorem Sequence.isBounded_mul {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hb: (b:Sequence).IsBounded):
    (a * b:Sequence).IsBounded := by
  rw [Sequence.isBounded_def.coe] at *
  choose M hM ha using ha
  choose N hN hb using hb
  refine ⟨ M * N, by positivity, ?_ ⟩
  intro n; specialize ha n; specialize hb n
  simp; rw [abs_mul (a n) (b n)]
  apply mul_le_mul ha hb <;> positivity

end Chapter5

--------------- SECTION 5.2 ---------------

abbrev Rat.CloseSeq (ε: ℚ) (a b: Chapter5.Sequence) : Prop :=
  ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n)

abbrev Rat.EventuallyClose (ε: ℚ) (a b: Chapter5.Sequence) : Prop :=
  ∃ N, ε.CloseSeq (a.from N) (b.from N)

namespace Chapter5

/-- Definition 5.2.1 ($ε$-close sequences) -/
lemma Rat.closeSeq_def (ε: ℚ) (a b: Sequence) :
    ε.CloseSeq a b ↔ ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n) := by rfl

attribute [-simp] Chapter4_3.abs_eq_abs

/-- Example 5.2.2 -/
example : (0.1:ℚ).CloseSeq ((fun n:ℕ ↦ ((-1)^n:ℚ)):Sequence)
((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence) := by
  simp [Rat.closeSeq_def]; intro n hn; simp [hn]
  lift n to ℕ using hn
  by_cases h: Even n <;> rw [Rat.Close]
  · simp [h.neg_one_pow];
    rw [abs_sub_comm, abs_of_nonneg] <;> norm_num;
  · observe h': Odd n
    simp [h'.neg_one_pow];
    rw [abs_of_nonneg] <;> norm_num

/-- Example 5.2.2 -/
example : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ ((-1)^n:ℚ)):Sequence)
:= by
  intro h; rw [Rat.Steady.coe] at h; specialize h 0 1; simp [Rat.Close] at h
  norm_num at h

/-- Example 5.2.2 -/
example : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence)
:= by
  intro h; rw [Rat.Steady.coe] at h; specialize h 0 1; simp [Rat.Close] at h
  rw [abs_of_nonneg] at h; norm_num at h; norm_num

/-- Definition 5.2.3 (Eventually ε-close sequences) -/
lemma Rat.eventuallyClose_def (ε: ℚ) (a b: Sequence) :
    ε.EventuallyClose a b ↔ ∃ N, ε.CloseSeq (a.from N) (b.from N) := by rfl

/-- Definition 5.2.3 (Eventually ε-close sequences) -/
-- I think this might be true for sequences starting at any n₀ actually lol
lemma Rat.eventuallyClose_iff (ε: ℚ) (a b: ℕ → ℚ) :
    ε.EventuallyClose (a:Sequence) (b:Sequence) ↔  ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by
  rw [Rat.eventuallyClose_def]
  constructor <;> intro h <;> choose N h using h
  · let N' := max N 0; use N'.toNat
    intro n hn
    specialize h n (by simp; omega) (by simp; omega)
    simp [show n ≥ N by omega] at h; exact h
  · use N; simp [Rat.CloseSeq];
    intro n hn; lift n to ℕ using (by linarith)
    simp [hn]; exact h n (by linarith)

/-
If we didn't want to use max N 0, here's an alternative:
    by_cases hN: N ≥ 0
    · lift N to ℕ using hN
      use N; intro n hn; simp [Rat.CloseSeq] at h;
      specialize h n (by linarith)
      simp [hn] at h; exact h
    · push_neg at hN; use 0; intro n hn; simp [Rat.CloseSeq] at h;
      have hN: N ≤ n := by linarith
      specialize h n _ _ _ _
      all_goals try linarith
      simp [hN] at h; exact h
    -/

/-- Example 5.2.5 -/
example : ¬ (0.1:ℚ).CloseSeq ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
  intro h; specialize h 0 (by simp) (by simp); simp at h;
  rw [Rat.Close, abs_of_nonneg] at h <;> norm_num at *

example : (0.1:ℚ).EventuallyClose ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
  use 1; simp [Rat.CloseSeq]; intro n hn; simp [hn, show 0 ≤ n by linarith]
  rw [Rat.Close, abs_of_nonneg]; norm_num; simp; ring_nf;
  rw [show -1 - n = -(1+n) by ring];
  calc
    _ ≤ (10:ℚ) ^ (-(2:ℤ)) * 2 := by gcongr; norm_num; linarith
    _ ≤ 1 / 10 := by norm_num
  field_simp; apply zpow_nonneg (by norm_num)

example : (0.01:ℚ).EventuallyClose ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
  use 2; simp [Rat.CloseSeq]; intro n hn; simp [hn, show 0 ≤ n by linarith]
  rw [Rat.Close, abs_of_nonneg]; norm_num; simp; ring_nf;
  rw [show -1 - n = -(1+n) by ring];
  calc
    _ ≤ (10:ℚ) ^ (-(3:ℤ)) * 2 := by gcongr; norm_num; linarith
    _ ≤ 1 / 100 := by norm_num
  field_simp; apply zpow_nonneg (by norm_num)

/-- Definition 5.2.6 (Equivalent sequences) -/
abbrev Sequence.Equiv (a b: ℕ → ℚ) : Prop :=
  ∀ ε > (0:ℚ), ε.EventuallyClose (a:Sequence) (b:Sequence)

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_def (a b: ℕ → ℚ) :
    Equiv a b ↔ ∀ (ε:ℚ), ε > 0 → ε.EventuallyClose (a:Sequence) (b:Sequence) := by rfl

-- Simple def because all we've added is ∀ ε > 0 in front of the previous iff

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_iff (a b: ℕ → ℚ) : Equiv a b ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by
  constructor <;> intro h e he <;> specialize h e he
  <;> rw [Rat.eventuallyClose_iff] at * <;> exact h


lemma ten_pow_geq (N : ℕ ) : 10^N ≥ N := by
  have h1 := pow_le_pow_left₀ (a:= 2) (b:= 10) (by norm_num) (by norm_num)
  refine le_trans ?_ (h1 N)
  apply Chapter4_3.two_pow_geq

/-- Proposition 5.2.8 -/
lemma Sequence.equiv_example :
  Equiv (fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)) (fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)) := by
  set a := fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1) --let creates a name, does nothing
  set b := fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1) --set replaces all instances with name
  rw [equiv_iff]; intro ε hε

  have hab (n:ℕ) : |a n - b n| = 2 * 10 ^ (-(n:ℤ)-1) := by
    unfold a b; ring_nf; field_simp; apply zpow_nonneg; norm_num
  have hab' (N:ℕ) : ∀ n ≥ N, |a n - b n| ≤ 2 * 10 ^(-(N:ℤ)-1) := by
    intro n hn; rw [hab n]; gcongr; norm_num

  have hN' (N:ℕ) : 2 * (10:ℚ)^(-(N:ℤ)-1) ≤ 2/(N+1) := by
      have h3 := ten_pow_geq (N+1)
      rw [show (- (N:ℤ) - 1) = -(N+1) by ring, zpow_neg]; field_simp; gcongr
      norm_cast

  have hN : ∃ N:ℕ, 2 * (10:ℚ) ^(-(N:ℤ)-1) ≤ ε := by
    choose N hN using exists_nat_ge (2 / ε - 1)
    refine ⟨ N, (hN' N).trans ?_ ⟩ -- Transitivity to clean up intermediate
    have:  2/ε ≤ (N:ℚ) + 1  := by linarith
    rw [div_le_iff₀ (by positivity)] at *
    linarith

  choose N hN using hN; use N; intro n hn
  linarith [hab' N n hn]

lemma Close_symm {ε:ℚ} {a b: ℚ} (hab: ε.Close a b) : ε.Close b a := by
  rw [Rat.Close] at *; rwa [abs_sub_comm] at hab

lemma Sequence.closeSeq_symm {ε:ℚ} {a b: Chapter5.Sequence} (hab: ε.CloseSeq a b) :
    ε.CloseSeq b a := by
  rw [Rat.closeSeq_def] at *;
  intro hn hb ha; specialize hab _ ha hb
  apply Close_symm hab

lemma Sequence.eventuallyClose_symm {ε:ℚ} {a b: Chapter5.Sequence}
    (hab: ε.EventuallyClose a b) : ε.EventuallyClose b a := by
  rw [Rat.eventuallyClose_def] at *; choose N hN using hab; use N;
  apply Sequence.closeSeq_symm hN

lemma Sequence.equiv_symm {a b: ℕ → ℚ} (hab: Equiv a b) : Equiv b a := by
  rw [Sequence.equiv_def] at *;
  peel hab with ε hε hab --intro ε hε; specialize hab ε hε
  apply Sequence.eventuallyClose_symm hab

/-- Exercise 5.2.1 -/
theorem Sequence.isCauchy_of_equiv' {a b: ℕ → ℚ} (hab: Equiv a b) :
    (a:Sequence).IsCauchy → (b:Sequence).IsCauchy := by
  intro ha; intro e he;
  specialize ha (e/3) (by linarith); specialize hab (e/3) (by linarith);
  choose N hN ha using ha; choose M hab using hab; simp at hN

  refine ⟨max N M, by simp_all, ?_⟩
  intro n hn m hm; simp at hn hm

  specialize ha n (by simp [hn]) m (by simp [hm])
  have hab1 := hab n (by simp [hn]) (by simp [hn])
  have hab2 := hab m (by simp [hm]) (by simp [hm])
  simp_all;
  apply Close_symm at hab1
  have h1 := Chapter4_3.close_trans hab1 ha
  have h2 := Chapter4_3.close_trans h1 hab2
  convert h2; linarith

  --rw [Rat.Close] at *;
  --rw [abs_sub_comm] at hab1

  -- Use triangle inequality
  --have hbn_am:= abs_sub_le (b n.toNat) (a n.toNat) (a m.toNat)
  --have hbn_bm := abs_sub_le (b n.toNat) (a m.toNat) (b m.toNat)
  --linarith


theorem Sequence.isCauchy_of_equiv {a b: ℕ → ℚ} (hab: Equiv a b) :
    (a:Sequence).IsCauchy ↔ (b:Sequence).IsCauchy := by
  constructor <;> apply Sequence.isCauchy_of_equiv'
  · apply hab
  · apply (Sequence.equiv_symm hab)

lemma Sequence.isBounded_of_isCauchy' {a:Sequence} (h: a.IsCauchy) : a.IsBounded := by
  choose N hN h using h 1 (by norm_num)
  let finN:= N - a.n₀ + 1
  let b : Fin (finN.toNat) → ℚ := fun m ↦ a (m + a.n₀)
  obtain ⟨ M, hMpos, hM ⟩ := IsBounded.finite b
  have h1 : Chapter5.BoundedBy b (M + |(a N)|+1) := fun m ↦ (hM m).trans (by simp [add_assoc]; positivity)
  have h2' : ∀ n ≥ N, |a n| ≤ |a N|+1 := by
    intro n hn;
    specialize h n _ N _ <;> try simp [hn] <;> try linarith
    simp_all; rw [Rat.Close] at h
    calc
      _ =  |(a n - a N) + a N| := by ring_nf
      _ ≤  |a n - a N| + |a N| := abs_add _ _
      _ ≤ |a N| + 1 := by linarith
  have h2 : ∀ n ≥ N, |a n| ≤ M + |a N| + 1 := fun n hn ↦
    (h2' n hn).trans (by simp; positivity)
  refine ⟨ M + |a N| + 1, by positivity, ?_ ⟩
  rw [Sequence.boundedBy_def']
  intro n hn0
  -- Split cases: finite region vs 1-steady region
  by_cases hn : n < N
  · specialize h1 ⟨ (n - a.n₀).toNat, by omega ⟩ -- Shifted index
    convert h1 -- To use finite proof, we just need to shift index back
    simp [hn0]
  · push_neg at hn; exact h2 n hn -- No work necessary

theorem Sequence.isBounded_of_eventuallyClose' {ε:ℚ} {a b: ℕ → ℚ} (hab: ε.EventuallyClose a b) :
    (a:Sequence).IsBounded → (b:Sequence).IsBounded := by
  intro ha;
  rw [Sequence.isBounded_def.coe] at *; rw [Rat.eventuallyClose_iff] at hab
  choose A hA ha using ha; choose N hab using hab;
  -- Finite region of b bounded by B
  let fin : Fin N → ℚ := fun m ↦ b m
  obtain ⟨ B, hBpos, hB ⟩ := IsBounded.finite fin
  have h1 : Chapter5.BoundedBy fin ( B + (A + |ε| )) := fun m ↦ (hB m).trans (by simp; positivity)
  -- ε-close region is bounded by A + |ε|
  have h2' (n : ℕ ) (hn : n ≥ N) : |b n| ≤ A + |ε| := by
    rw [show b n = a n + (b n - a n) by ring]
    have := abs_add (a n) (b n - a n); specialize ha n; specialize hab n hn
    rw [abs_sub_comm] at hab; have:= (le_abs_self ε);
    linarith

  have h2 (n : ℕ ) (hn : n ≥ N) : |b n| ≤ B + (A + |ε|) := by linarith [h2' n hn]

  refine ⟨ B + (A + |ε| )  , by positivity, ?_ ⟩
  intro n;
  by_cases hn : n < N
  · specialize h1 ⟨ n, hn ⟩; apply h1;
  · push_neg at hn; exact h2 n hn

/-- Exercise 5.2.2 -/
theorem Sequence.isBounded_of_eventuallyClose {ε:ℚ} {a b: ℕ → ℚ} (hab: ε.EventuallyClose a b) :
    (a:Sequence).IsBounded ↔ (b:Sequence).IsBounded := by
  constructor <;> apply Sequence.isBounded_of_eventuallyClose'
  · apply hab
  · apply Sequence.eventuallyClose_symm hab

end Chapter5
--------------- SECTION 5.3 ---------------



/-!
# Analysis I, Section 5.3: The construction of the real numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Notion of a formal limit of a Cauchy sequence.
- Construction of a real number type `Chapter5.Real`.
- Basic arithmetic operations and properties.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- A class of Cauchy sequences that start at zero -/
@[ext]
class CauchySequence extends Sequence where
  zero : n₀ = 0
  cauchy : toSequence.IsCauchy

theorem CauchySequence.ext' {a b: CauchySequence} (h: a.seq = b.seq) : a = b := by
  apply CauchySequence.ext _ h
  rw [a.zero, b.zero]

/-- A sequence starting at zero that is Cauchy, can be viewed as a Cauchy sequence.-/
abbrev CauchySequence.mk' {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) : CauchySequence where
  n₀ := 0
  seq := (a:Sequence).seq
  vanish := by aesop
  zero := rfl
  cauchy := ha

@[simp] -- Cauchy sequences are still equivalent to their underlying sequences
theorem CauchySequence.coe_eq {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) :
    (mk' ha).toSequence = (a:Sequence) := rfl

-- We can turn Cauchy sequences into functions ℕ → ℚ
instance CauchySequence.instCoeFun : CoeFun CauchySequence (fun _ ↦ ℕ → ℚ) where
  coe a n := a.toSequence (n:ℤ)

@[simp] -- Casting to a function agrees with toSequence
theorem CauchySequence.coe_to_sequence (a: CauchySequence) :
    ((a:ℕ → ℚ):Sequence) = a.toSequence := by
  apply Sequence.ext (by simp [Sequence.n0_coe, a.zero])
  ext n; by_cases h:n ≥ 0 <;> simp_all
  -- Left side simplifies because we always know n₀ = 0
  -- So eval_coe_at_int auto-simplifies it out
  rw [a.vanish]; rwa [a.zero] -- Right side doesn't simplify until we vanish

@[simp] -- Coercing function → cauchy → function gives original function
theorem CauchySequence.coe_coe {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) : mk' ha = a := by rfl

/-- Proposition 5.3.3 / Exercise 5.3.1 -/
theorem Sequence.equiv_trans {a b c:ℕ → ℚ} (hab: Equiv a b) (hbc: Equiv b c) :
  Equiv a c := by
    intro e he;
    specialize hab (e/2) (by linarith); specialize hbc (e/2) (by linarith);
    rw [Rat.eventuallyClose_iff] at *;
    choose N hab using hab; choose M hbc using hbc; use N+M
    intro n hn
    specialize hab n (by linarith); specialize hbc n (by linarith)
    have h1 := abs_sub_le (a n) (b n) (c n)
    linarith

theorem Sequence.equiv_refl (a:ℕ → ℚ) : Equiv a a := by
  rw [equiv_iff]; intro ε hε; use 0; intro n hn; simp; linarith

/-- Proposition 5.3.3 / Exercise 5.3.1 -/
instance CauchySequence.instSetoid : Setoid CauchySequence where
  r := fun a b ↦ Sequence.Equiv a b
  iseqv := {
     refl := by intro x; apply Sequence.equiv_refl
     symm := Sequence.equiv_symm
     trans := Sequence.equiv_trans
  }

theorem CauchySequence.equiv_iff (a b: CauchySequence) : a ≈ b ↔ Sequence.Equiv a b := by rfl

/-- Every constant sequence is Cauchy -/
theorem Sequence.IsCauchy.const (a:ℚ) : ((fun _:ℕ ↦ a):Sequence).IsCauchy := by
  intro e he; refine ⟨0, by simp_all, ?_⟩; intro n hn m hm; simp_all
  rw [Rat.Close]; simp; linarith

instance CauchySequence.instZero : Zero CauchySequence where
  zero := CauchySequence.mk' (a := fun _: ℕ ↦ 0) (Sequence.IsCauchy.const (0:ℚ))

-- Two real numbers are equal if their Cauchy sequences are equivalent
abbrev Real := Quotient CauchySequence.instSetoid

open Classical in
/--
  It is convenient in Lean to assign the "dummy" value of 0 to `LIM a` when `a` is not Cauchy.
  This requires Classical logic, because the property of being Cauchy is not computable or
  decidable.
-/

-- LIM takes a function and returns the *quotient* element that
-- it is included in, where two functions are in the same equivalence class if
-- they create equivalent cauchy sequences
noncomputable abbrev LIM (a:ℕ → ℚ) : Real :=
  Quotient.mk _ (if h : (a:Sequence).IsCauchy then CauchySequence.mk' h else (0:CauchySequence))

theorem LIM_def {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) :
    LIM a = Quotient.mk _ (CauchySequence.mk' ha) := by
  rw [LIM]; split_ifs ; rfl -- rw [dif_pos ha]

-- All real numbers have some function that 1. isCauchy 2.generates them using LIM
/-- Definition 5.3.1 (Real numbers) -/
theorem Real.eq_lim (x:Real) : ∃ (a:ℕ → ℚ), (a:Sequence).IsCauchy ∧ x = LIM a := by
  apply Quotient.ind _ x;  -- Any real number has a representative Cauchy sequence
  intro a; use (a:ℕ → ℚ);
  observe : ((a:ℕ → ℚ):Sequence) = a.toSequence -- Convert back into sequence
  rw [this, LIM_def (by convert a.cauchy)] -- a is cauchy so it has valid LIM
  refine ⟨ a.cauchy, ?_ ⟩
  congr; ext n; -- Check that their representatives are equal
  simp; replace := congr(($this n)); simp_all

/-- Definition 5.3.1 (Real numbers) -/
theorem Real.LIM_eq_LIM {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a = LIM b ↔ Sequence.Equiv a b := by
  constructor <;> intro h -- Equivalence class match -> equivalent under setoid relation
  · replace h := Quotient.exact h -- Completeness: equiv finds all quots
    rwa [dif_pos ha, dif_pos hb, -- Both cauchy, so we can remove junk case
      CauchySequence.equiv_iff] at h -- ≈ and .Equiv are the same
  · apply Quotient.sound -- Soundness: equiv *only* finds valid quots
    rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff]

/--Lemma 5.3.6 (Sum of Cauchy sequences is Cauchy)-/
theorem Sequence.IsCauchy.add {a b:ℕ → ℚ}  (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    (a + b:Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  rw [IsCauchy.coe] at *
  intro ε hε
  choose N1 ha using ha _ (half_pos hε)
  choose N2 hb using hb _ (half_pos hε)
  use max N1 N2
  intro j hj k hk
  have h1 := ha j ?_ k ?_ <;> try omega
  have h2 := hb j ?_ k ?_ <;> try omega
  simp [Chapter4_3.dist] at *; rw [abs_eq_abs', ←Rat.Close] at *
  convert Chapter4_3.add_close h1 h2
  linarith



/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ) (haa': Equiv a a') :
    Equiv (a + b) (a' + b) := by
  -- This proof is written to follow the structure of the original text.
  rw [equiv_def] at *

  -- peel (number of peels) (where to specialize) with (variables) (new name for specialized hypothesis)
  peel 2 haa' with ε hε haa'
  rw [Rat.eventuallyClose_def] at *
  choose N haa' using haa'; use N
  simp [Rat.closeSeq_def] at *
  peel 5 haa' with n hn hN _ _ haa'
  simp [hn, hN] at *
  convert Chapter4_3.add_close haa' (Chapter4_3.close_refl (b n.toNat))
  simp

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv_right {b b':ℕ → ℚ} (a:ℕ → ℚ) (hbb': Equiv b b') :
    Equiv (a + b) (a + b') := by simp_rw [add_comm]; exact add_equiv_left _ hbb'

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv {a b a' b':ℕ → ℚ} (haa': Equiv a a')
  (hbb': Equiv b b') :
    Equiv (a + b) (a' + b') :=
  equiv_trans (add_equiv_left _ haa') (add_equiv_right _ hbb')

/-- Definition 5.3.4 (Addition of reals) -/

noncomputable instance Real.add_inst : Add Real where
  add := fun x y ↦
    Quotient.liftOn₂ x y (fun a b ↦ LIM (a + b)) (by
      intro a b a' b' _ _
      change LIM ((a:ℕ → ℚ) + (b:ℕ → ℚ)) = LIM ((a':ℕ → ℚ) + (b':ℕ → ℚ))
      rw [LIM_eq_LIM]
      · solve_by_elim [Sequence.add_equiv]
      all_goals apply Sequence.IsCauchy.add <;> rw [CauchySequence.coe_to_sequence] <;> convert @CauchySequence.cauchy ?_
      )

-- This method also works! lift and liftOn just have slightly different
-- type signatures
noncomputable instance Real.add_inst' : Add Real where
  add :=
      Quotient.lift₂ (fun a b ↦ LIM (a + b)) (by
      -- Substitution theorem
      intro a b a' b' _ _
      simp only -- simp only applies the function without having to use change
      rw [LIM_eq_LIM];
      · solve_by_elim [Sequence.add_equiv] -- Equiv has add substitution theorem
      -- Make sure all sequences are cauchy, so LIM_eq_LIM applies
      all_goals apply Sequence.IsCauchy.add <;> rw [CauchySequence.coe_to_sequence] <;> convert @CauchySequence.cauchy ?_
      )

/-- Definition 5.3.4 (Addition of reals) -/
theorem Real.LIM_add {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a + LIM b = LIM (a + b) := by
  rw [LIM_def ha, LIM_def hb, LIM_def (Sequence.IsCauchy.add ha hb)]
  -- liftOn₂ (Quot.mk a) (Quot.mk b) add = add a b
  -- In other words, you can replace addition of mk-quotients with addition of representatives
  convert Quotient.liftOn₂_mk _ _ _ _
  -- Simplify based on cauchy property (remove junk case)
  rw [dif_pos]

attribute [-simp] Chapter4_3.abs_eq_abs
/-- Proposition 5.3.10 (Product of Cauchy sequences is Cauchy) -/
theorem Sequence.IsCauchy.mul {a b:ℕ → ℚ}  (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    (a * b:Sequence).IsCauchy := by
  choose A hApos hA using (isBounded_of_isCauchy ha)
  choose B hBpos hB using (isBounded_of_isCauchy hb)
  rw [IsCauchy.coe] at *
  intro ε hε
  have : (A+B+1) > 0 := by linarith
  choose N1 ha using ha ((ε /2) / (A+B+1)) (by apply div_pos (half_pos hε) (by linarith))
  choose N2 hb using hb ((ε /2) / (A+B+1)) (by apply div_pos (half_pos hε) (by linarith))

  use max N1 N2
  intro j hj k hk
  specialize ha j ?_ k ?_  <;> try omega
  specialize hb j ?_ k ?_ <;> try omega
  rw [Chapter4_3.dist] at *; rw [ ←Rat.Close] at *
  have h1 := Chapter4_3.close_mul_mul' ha hb
  convert Chapter4_3.close_mono h1 ?_
  specialize hA k; simp at hA;
  specialize hB j; simp at hB;
  rw [show ε = (ε /2) + (ε /2) by ring]
  gcongr
  · field_simp; rw [div_le_div_iff₀] <;> try positivity
    suffices |b j| ≤  (A + B + 1)  by nlinarith
    linarith [hB]
  · field_simp; rw [div_le_div_iff₀] <;> try positivity
    suffices |a k| ≤  (A + B + 1)  by nlinarith
    linarith [hA]


-- Note that we require the condition that one of the sequences is Cauchy to ensure boundedness

/-- Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ) (hb : (b:Sequence).IsCauchy) (haa': Equiv a a') :
  Equiv (a * b) (a' * b) := by
  rw [equiv_def] at *
  intro ε hε;
  choose B hBpos hB using (isBounded_of_isCauchy hb)

  specialize haa' (ε / (B+1)) (by apply div_pos hε (by linarith))
  rw [Rat.eventuallyClose_def] at *
  choose A haa' using haa';
  simp [Rat.closeSeq_def] at *
  use A
  peel 5 haa' with n hn hN _ _ haa'
  specialize hB n; simp at hB;
  simp [hn, hN] at *

  apply Chapter4_3.close_mul_right (z:= b n.toNat) at haa'
  apply Chapter4_3.close_mono haa'
  calc
    _ = ε / (B + 1) * (B + 1) := by field_simp
    _ ≥ ε / (B + 1) * |b n.toNat| := by gcongr; linarith


/--Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv_right {b b':ℕ → ℚ} (a:ℕ → ℚ)  (ha : (a:Sequence).IsCauchy)  (hbb': Equiv b b') :
  Equiv (a * b) (a * b') := by simp_rw [mul_comm]; exact mul_equiv_left a ha hbb'

/--Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv
{a b a' b':ℕ → ℚ}
(ha : (a:Sequence).IsCauchy)
(hb' : (b':Sequence).IsCauchy)
(haa': Equiv a a')
(hbb': Equiv b b') : Equiv (a * b) (a' * b') :=
  equiv_trans (mul_equiv_right _ ha hbb') (mul_equiv_left _ hb' haa')

/-- Definition 5.3.9 (Product of reals) -/
noncomputable instance Real.mul_inst : Mul Real where
  mul := fun x y ↦
    Quotient.liftOn₂ x y (fun a b ↦ LIM (a * b)) (by
      intro a b a' b' haa' hbb'
      simp only
      rw [LIM_eq_LIM]
      · exact Sequence.mul_equiv
          (by rw [CauchySequence.coe_to_sequence]; exact a.cauchy)
          (by rw [CauchySequence.coe_to_sequence]; exact b'.cauchy) haa' hbb'
      all_goals apply Sequence.IsCauchy.mul <;> rw [CauchySequence.coe_to_sequence] <;> convert @CauchySequence.cauchy ?_
      )

theorem Real.LIM_mul {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a * LIM b = LIM (a * b) := by
  rw [LIM_def ha, LIM_def hb, LIM_def (Sequence.IsCauchy.mul ha hb)]
  -- In other words, you can replace multiplication of mk-quotients with multiplication of representatives
  convert Quotient.liftOn₂_mk _ _ _ _
  rw [dif_pos]

-- Embed the rationals into the reals via constant Cauchy sequences
instance Real.instRatCast : RatCast Real where
  ratCast := fun q ↦
    Quotient.mk _ (CauchySequence.mk' (a := fun _ ↦ q) (Sequence.IsCauchy.const q))

theorem Real.ratCast_def (q:ℚ) : (q:Real) = LIM (fun _ ↦ q) := by rw [LIM_def]; rfl

/-- Exercise 5.3.3 -/
@[simp]
theorem Real.ratCast_inj (q r:ℚ) : (q:Real) = (r:Real) ↔ q = r := by
  constructor <;> intro h
  · repeat rw [Real.ratCast_def] at h
    rw [LIM_eq_LIM, Sequence.equiv_iff] at h
    contrapose! h
    wlog h': q > r
    · push_neg at h'; have hqr: q < r := lt_of_le_of_ne h' h
      choose e he habs using this r q h.symm hqr
      rw [abs_sub_comm] at habs; use e, he
    use |q-r|/2; have : q - r > 0 := by linarith;
    refine ⟨by rw [abs_of_pos this]; linarith, ?_⟩
    intro n; use n; simp; push_neg; linarith
    apply Sequence.IsCauchy.const
    apply Sequence.IsCauchy.const
  · rw [h]

instance Real.instOfNat {n:ℕ} : OfNat Real n where
  ofNat := ((n:ℚ):Real)

instance Real.instNatCast : NatCast Real where
  natCast n := ((n:ℚ):Real)

theorem Real.natCast_def (n:ℕ) : (n:Real) = LIM (fun _ ↦ n) := by rw [LIM_def]; rfl

theorem Real.OfNat_def (n:ℕ) : OfNat.ofNat n = LIM (fun _ ↦ n) := by rw [LIM_def]; rfl

lemma Real.NatCast_eq_ratCast (n:ℕ) : n = ((n:ℚ):Real) := rfl

lemma Real.OfNat_eq_ratCast (n:ℕ) : OfNat.ofNat n = ((n:ℚ):Real) := rfl

@[simp]
theorem Real.LIM.zero : LIM (fun _ ↦ (0:ℚ)) = 0 := by rw [←ratCast_def 0]; rfl

@[simp]
theorem Real.LIM.one : LIM (fun _ ↦ (1:ℚ)) = 1 := by rw [←ratCast_def 1]; rfl

instance Real.instIntCast : IntCast Real where
  intCast n := ((n:ℚ):Real)

theorem Real.intCast_def (n:ℤ) : (n:Real) = LIM (fun _ ↦ n) := by rw [LIM_def]; rfl

lemma Real.IntCast_eq_ratCast (n:ℤ) : n = ((n:ℚ):Real) := rfl

/-- ratCast distributes over addition -/
theorem Real.ratCast_add (a b:ℚ) : (a:Real) + (b:Real) = (a+b:ℚ) := by
  rw [Real.ratCast_def, Real.ratCast_def, Real.ratCast_def]
  apply Real.LIM_add
  <;> apply Sequence.IsCauchy.const


/-- ratCast distributes over multiplication -/
theorem Real.ratCast_mul (a b:ℚ) : (a:Real) * (b:Real) = (a*b:ℚ) := by
  rw [Real.ratCast_def, Real.ratCast_def, Real.ratCast_def]
  apply Real.LIM_mul
  <;> apply Sequence.IsCauchy.const

noncomputable instance Real.instNeg : Neg Real where
  neg x := ((-1:ℚ):Real) * x

lemma Real.neg_one_mul (x:Real) : ((-1:ℚ):Real) * x = -x := by rfl

/-- ratCast commutes with negation -/
theorem Real.neg_ratCast (a:ℚ) : -(a:Real) = (-a:ℚ) := by
  simp [← neg_one_mul, Real.ratCast_mul]

/-- It may be possible to omit the Cauchy sequence hypothesis here. -/
theorem Real.neg_LIM (a:ℕ → ℚ) (ha: (a:Sequence).IsCauchy) : -LIM a = LIM (-a) := by
  rw [← neg_one_mul, Real.ratCast_def, Real.LIM_mul];
  congr; ext n; simp
  apply Sequence.IsCauchy.const
  exact ha

theorem Real.IsCauchy.neg (a:ℕ → ℚ) (ha: (a:Sequence).IsCauchy) :
    ((-a:ℕ → ℚ):Sequence).IsCauchy := by
  peel 8 ha with e he N hN i hi j hj ha
  simp_all; simp [le_trans hN hi, le_trans hN hj] at *
  rw [Rat.Close] at *; rw [abs_sub_comm]; simp;
  convert ha using 2; ring


/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.addGroup_inst : AddGroup Real :=
AddGroup.ofLeftAxioms
(by
  intro a b c
  choose x hx using eq_lim a
  choose y hy using eq_lim b
  choose z hz using eq_lim c
  rw [hx.2, hy.2, hz.2]
  repeat rw [Real.LIM_add]
  congr 1; ring
  on_goal 2 => apply Sequence.IsCauchy.add
  on_goal 6 => apply Sequence.IsCauchy.add
  any_goals exact hx.1
  any_goals exact hy.1
  any_goals exact hz.1
)
(by
  intro a
  choose x hx using eq_lim a
  rw [hx.2, ← Real.LIM.zero, Real.LIM_add]
  congr 1; ext n; simp
  apply Sequence.IsCauchy.const
  exact hx.1
)
(by
  intro a
  choose x hx using eq_lim a
  rw [hx.2, ← Real.LIM.zero, Real.neg_LIM, Real.LIM_add]
  congr 1; ext n; simp
  apply Real.IsCauchy.neg
  all_goals exact hx.1)

theorem Real.sub_eq_add_neg (x y:Real) : x - y = x + (-y) := rfl

theorem Sequence.IsCauchy.sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    ((a-b:ℕ → ℚ):Sequence).IsCauchy := by
  rw [show a-b = a + (-b) by ring]
  apply Sequence.IsCauchy.add
  exact ha; exact Real.IsCauchy.neg _ hb

/-- LIM distributes over subtraction -/
theorem Real.LIM_sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a - LIM b = LIM (a - b) := by
  rw [Real.sub_eq_add_neg, Real.neg_LIM, Real.LIM_add ]
  congr; ring
  on_goal 2 => apply Real.IsCauchy.neg
  any_goals exact ha
  any_goals exact hb

/-- ratCast distributes over subtraction -/
theorem Real.ratCast_sub (a b:ℚ) : (a:Real) - (b:Real) = (a-b:ℚ) := by
  rw [Real.sub_eq_add_neg, Real.neg_ratCast, Real.ratCast_add]
  congr; ring


/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instAddCommGroup : AddCommGroup Real where
  add_comm := by
    intro a b
    choose x hx using eq_lim a
    choose y hy using eq_lim b
    rw [hx.2, hy.2]
    rw [Real.LIM_add, Real.LIM_add]
    congr 1; ring
    any_goals apply hx.1
    any_goals apply hy.1

lemma Real.mul_comm' (a b:Real) : a * b = b * a := by
  choose x hx using eq_lim a
  choose y hy using eq_lim b
  rw [hx.2, hy.2]
  rw [Real.LIM_mul, Real.LIM_mul]
  congr 1; ring
  any_goals apply hx.1
  any_goals apply hy.1

lemma Real.one_mul' (a:Real) : (1:Real) * a = a := by
  choose x hx using eq_lim a
  rw [hx.2,← Real.LIM.one, Real.LIM_mul]
  congr 1; ext n; simp
  apply Sequence.IsCauchy.const
  exact hx.1

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instCommMonoid : CommMonoid Real where
  mul_comm := Real.mul_comm'
  mul_assoc := by
    intro a b c
    choose x hx using eq_lim a
    choose y hy using eq_lim b
    choose z hz using eq_lim c
    rw [hx.2, hy.2, hz.2]
    rw [Real.LIM_mul, Real.LIM_mul, Real.LIM_mul, Real.LIM_mul]
    congr 1; ring
    on_goal 2 => apply Sequence.IsCauchy.mul
    on_goal 6 => apply Sequence.IsCauchy.mul
    any_goals apply hx.1
    any_goals apply hy.1
    any_goals apply hz.1
  one_mul := Real.one_mul'
  mul_one := by intro x; rw [mul_comm']; apply Real.one_mul'

lemma Real.left_distrib' (a b c:Real) : a * (b + c) = a * b + a * c := by
  choose x hx using eq_lim a
  choose y hy using eq_lim b
  choose z hz using eq_lim c
  rw [hx.2, hy.2, hz.2]
  rw [Real.LIM_mul, Real.LIM_add, Real.LIM_mul, Real.LIM_mul, Real.LIM_add]
  congr 1; ring
  on_goal 1 => apply Sequence.IsCauchy.mul
  on_goal 3 => apply Sequence.IsCauchy.mul
  on_goal 8 => apply Sequence.IsCauchy.add
  any_goals apply hx.1
  any_goals apply hy.1
  any_goals apply hz.1

lemma Real.zero_mul' (a:Real) : (0:Real) * a = 0 := by
  obtain ⟨x, hx, rfl⟩ := eq_lim a
  rw [← Real.LIM.zero, Real.LIM_mul]
  congr 1; ext n; simp
  apply Sequence.IsCauchy.const
  exact hx

/-- Proposition 5.3.11 (laws of algebra)-/
noncomputable instance Real.instCommRing : CommRing Real where
  left_distrib := Real.left_distrib'
  right_distrib := by
    intro a b c
    rw [mul_comm, Real.left_distrib', mul_comm c a, mul_comm c b]
  zero_mul := Real.zero_mul'
  mul_zero := by intro a; rw [mul_comm']; apply Real.zero_mul'
  mul_assoc := mul_assoc
  natCast_succ := by
    intro n;
    have hn:= NatCast_eq_ratCast n
    have h1 := Real.OfNat_eq_ratCast 1
    simp only [Nat.cast] at * -- Fix weird slightly different casting pathways
    rw [hn, h1]
    rw [Real.ratCast_add]
    norm_cast
  intCast_negSucc := by
    intro n;
    have hn:= NatCast_eq_ratCast (n+1)
    have h1 := Real.IntCast_eq_ratCast (Int.negSucc n)
    simp only [Int.cast] at *
    rw [hn, h1]
    rw [Real.neg_ratCast] -- Move the negative into the int domain
    -- We just need to check the ints are the same
    congr 1 -- Leave it to the int machinery

-- The embedding of rationals into reals is a ring homomorphism
-- In other words: zero, one, addition, and multiplication are preserved
abbrev Real.ratCast_hom : ℚ →+* Real where
  toFun := RatCast.ratCast
  map_zero' := rfl -- real 0 is constructed as ratCast 0
  map_one' := rfl
  map_add' := by intro x y; rw [Real.ratCast_add]
  map_mul' := by intro x y; rw [Real.ratCast_mul]

/--
  Definition 5.3.12 (sequences bounded away from zero). Sequences are indexed to start from zero
  as this is more convenient for Mathlib purposes.
-/
abbrev BoundedAwayZero (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, |a n| ≥ c

theorem bounded_away_zero_def (a:ℕ → ℚ) : BoundedAwayZero a ↔
  ∃ (c:ℚ), c > 0 ∧ ∀ n, |a n| ≥ c := by rfl

/-- Examples 5.3.13 -/
example : BoundedAwayZero (fun n ↦ (-1)^n) := by use 1; simp


--set_option diagnostics true
/-- Examples 5.3.13 -/
example : ¬ BoundedAwayZero (fun n ↦ 10^(-(n:ℤ)-1)) := by
  rw [bounded_away_zero_def]; push_neg; intro c hc
  -- For any c, we can go farther in the sequence to get closer than c to 0
  choose m hm using exists_nat_ge (1/c); use m
  replace hm : 1/c < m + 1 := by linarith
  rw [show ((-(m:ℤ) - 1) = -(m+1)) by ring, abs_of_nonneg]
  rw [zpow_neg, show c =(1/c)⁻¹ by field_simp] -- Remove abs
  -- Cancel out ⁻¹
  gcongr
  -- 1/c < m+1 ≤ 10^(m+1)
  apply lt_of_lt_of_le hm
  norm_cast; apply ten_pow_geq -- norm_cast to deal with how our nat is cast
  -- 0 < 10, so exponent is pos
  apply zpow_nonneg (by norm_num)

/-- Examples 5.3.13 -/
example : ¬ BoundedAwayZero (fun n ↦ 1 - 10^(-(n:ℤ))) := by
  rw [bounded_away_zero_def]; push_neg; intro c hc
  use 0; simp [hc]

/-- Examples 5.3.13 -/
example : BoundedAwayZero (fun n ↦ 10^(n+1)) := by
  use 10^0, by norm_num
  intro n; dsimp -- Note: dsimp gets rid of some redundant fun calls
  rw [abs_of_nonneg (by positivity)]
  gcongr <;> norm_num

/-- Examples 5.3.13 -/
example : ¬ ((fun (n:ℕ) ↦ (10:ℚ)^(n+1)):Sequence).IsBounded := by
  rw [Sequence.isBounded_def]; push_neg; intro M hM
  rw [Sequence.boundedBy_def]; push_neg
  choose N hN using exists_nat_gt M
  have := ten_pow_geq (N+1)
  use N; simp
  apply lt_of_lt_of_le hN
  norm_cast; linarith

abbrev Real.truncated_seq (n : ℕ ) (C : ℚ ) (a : ℕ → ℚ) : ℕ → ℚ :=
  fun k ↦ if k < n then C else a k

lemma Real.truncated_seq_equiv (n : ℕ ) (C : ℚ ) (a : ℕ → ℚ):
  Sequence.Equiv a (Real.truncated_seq n C a) := by
  unfold Real.truncated_seq
  intro e he; use n; intro i hia _; simp at hia; simp [hia]
  simp [show 0 ≤ i by linarith, show ¬ i < n by linarith]
  rw [Rat.Close]; simp; linarith

lemma Real.truncated_seq_isCauchy (n : ℕ ) (C : ℚ ) (a : ℕ → ℚ)
  (ha: (a:Sequence).IsCauchy) :
  (Real.truncated_seq n C a :Sequence).IsCauchy := by
  have := Real.truncated_seq_equiv n C a
  have := Sequence.isCauchy_of_equiv this
  rwa [this] at ha

lemma Real.truncated_seq_eq_LIM (n : ℕ ) (C : ℚ ) (a : ℕ → ℚ)
  (ha: (a:Sequence).IsCauchy) :
  LIM a  = LIM (Real.truncated_seq n C a) := by
  rw [LIM_eq_LIM ha (Real.truncated_seq_isCauchy n C a ha)]
  apply Real.truncated_seq_equiv n C a

/-- Lemma 5.3.14 -/
theorem Real.boundedAwayZero_of_nonzero {x:Real} (hx: x ≠ 0) :
    ∃ a:ℕ → ℚ, (a:Sequence).IsCauchy ∧ BoundedAwayZero a ∧ x = LIM a := by
  obtain ⟨ b, hb, rfl ⟩ := eq_lim x -- x has a corresponding sequence b
  simp only [←LIM.zero, ne_eq] at hx -- x is nonzero => b equal 0 sequence
  -- x ≠ 0 → sequences not equivalent → they always eventually separate by some ε > 0
  rw [LIM_eq_LIM hb (by convert Sequence.IsCauchy.const 0), Sequence.equiv_iff] at hx
  simp at hx
  -- Grab the distance ε that b and 0 always manage to separate by
  choose ε hε hx using hx -- a "fence" that b always breaks out of
  -- At some time N, b is trapped inside a fence of ε/2 (can't get too far from itself)
  choose N hb' using (Sequence.IsCauchy.coe _).mp hb _ (half_pos hε)
  -- b must exit the ε fence sometime n₀ after time N
  choose n₀ hn₀ hx using hx N
  -- b must stay within ε/2 distance of that time n₀ where it broke out of the ε
  -- fence, so it can only be at best ε/2 close to 0
  have how : ∀ j ≥ N, |b j| ≥ ε/2 := by
    intro j hj; -- (b j) stays close to (b n₀)
    have := hb' j hj n₀ hn₀; rw [Chapter4_3.dist] at this
    suffices ε ≤ |b j| + ε/2  by linarith
    apply le_trans (le_of_lt hx)
    suffices |b n₀| ≤ |b j| + |b j - b n₀|  by linarith
    have := Chapter4_3.dist_le 0 (b j) (b n₀)
    repeat rw [Chapter4_3.dist_eq] at this
    field_simp at this
    exact this

  -- Define a new sequence that removes terms that aren't guaranteed to be bounded away from 0
  -- This sequence is equivalent to our old one, so it's also cauchy
  have not_hard := Real.truncated_seq_equiv n₀ (ε/2) b
  replace not_hard := Sequence.equiv_symm not_hard
  set a := truncated_seq n₀ (ε/2) b

  have ha := (Sequence.isCauchy_of_equiv not_hard).mpr hb
  -- We'll use a as our bounded-away sequence
  refine ⟨ a, ha, ?_, by rw [(LIM_eq_LIM ha hb).mpr not_hard] ⟩
  rw [bounded_away_zero_def]
  use ε/2, half_pos hε
  -- Check that it's bounded away by ε/2
  -- Low sequence: exactly ε/2. High sequence: already proven.
  intro n; by_cases hn: n < n₀ <;> simp [a, truncated_seq, hn, le_abs_self _]
  grind

/--
  This result was not explicitly stated in the text, but is needed in the theory. It's a good
  exercise, so I'm setting it as such.
-/
theorem Real.lim_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) :
    LIM a ≠ 0 := by
  rw [←LIM.zero, ne_eq]
  rw [LIM_eq_LIM ha_cauchy (by convert Sequence.IsCauchy.const 0)]
  choose e he ha using ha
  rw [Sequence.equiv_iff]; push_neg
  use e/2, half_pos he; intro N; use N+1, (by linarith)
  specialize ha (N+1); simp
  linarith

theorem Real.nonzero_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a) (n: ℕ) :
a n ≠ 0 := by
   choose c hc ha using ha; specialize ha n; contrapose! ha; simp [ha, hc]

-- Since we know that our terms have a lower bound, the 1/x terms cannot blow up
-- So, we just have to scale down a1-a2 closeness sufficiently (by 1/c^2)
/-- Lemma 5.3.15 -/
theorem Real.inv_isCauchy_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) :
    ((a⁻¹:ℕ → ℚ):Sequence).IsCauchy := by
  -- Each term is nonzero: useful for making sure reciprocals are defined
  have ha' (n:ℕ) : a n ≠ 0 := nonzero_of_boundedAwayZero ha n
  -- Each term is at least c away from zero
  rw [bounded_away_zero_def] at ha; choose c hc ha using ha

  simp_rw [Sequence.IsCauchy.coe, Chapter4_3.dist_eq] at ha_cauchy ⊢
  -- Reciprocal Cauchy ↔ reciprocals all eventually become close
  intro ε hε;
  -- We'll get a within c² * ε closeness on the original sequence
  -- Because when we compare reciprocals, we divide by at least c²
  -- 1/x - 1/y = (y - x) / (xy) and |xy| ≥ c²
  specialize ha_cauchy (c^2 * ε) (by positivity)
  choose N ha_cauchy using ha_cauchy; use N;
  -- Select arbitrary n, m ≥ N to show closeness
  peel 4 ha_cauchy with n hn m hm ha_cauchy
  -- Algebraic manipulation
  calc
    -- Valid reciprocals because a m, a n ≠ 0
    _ = |(a m - a n) / (a m * a n)| := by congr; field_simp [ha' m, ha' n]; grind
    -- Use c bound, then flip order
    _ ≤ |a m - a n| / c^2 := by rw [abs_div, abs_mul, sq]; gcongr <;> solve_by_elim
    _ = |a n - a m| / c^2 := by rw [abs_sub_comm]
    -- Use the bound: c^2 term cancels nicely
    _ ≤ (c^2 * ε) / c^2 := by gcongr
    _ = ε := by field_simp [hc]

/-- Lemma 5.3.17 (Reciprocation is well-defined) -/
theorem Real.inv_of_equiv {a b:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) (hb: BoundedAwayZero b)
  (hb_cauchy: (b:Sequence).IsCauchy) (hlim: LIM a = LIM b) :
    LIM a⁻¹ = LIM b⁻¹ := by
  -- This proof is written to follow the structure of the original text.
  set P := LIM a⁻¹ * LIM a * LIM b⁻¹
  ---- Set up cauchy conditions so that we can work with sequence limits
  have hainv_cauchy := Real.inv_isCauchy_of_boundedAwayZero ha ha_cauchy
  have hbinv_cauchy := Real.inv_isCauchy_of_boundedAwayZero hb hb_cauchy
  have haainv_cauchy := hainv_cauchy.mul ha_cauchy
  have habinv_cauchy := hainv_cauchy.mul hb_cauchy
  -- Cancel out terms to get the desired equality
  -- We do this by moving inside the LIM, and proving the *sequences* are equal
  have claim1 : P = LIM b⁻¹ := by
    -- Can combine multiplication under LIM (terms are cauchy)
    simp only [P, LIM_mul hainv_cauchy ha_cauchy, LIM_mul haainv_cauchy hbinv_cauchy]
    -- Use congr to remove LIM, then prove for any arbitrary input to sequences
    rcongr n;
    -- If a n ≠ 0, then inverse sequence behaves normally, can cancel
    simp [nonzero_of_boundedAwayZero ha n]
  have claim2 : P = LIM a⁻¹ := by
    -- Combine multiplication under LIM *and* swap LIM a and LIM b
    simp only [P, hlim, LIM_mul hainv_cauchy hb_cauchy, LIM_mul habinv_cauchy hbinv_cauchy]
    -- Now, we can cancel out the inverse the *other* way
    rcongr n; simp [nonzero_of_boundedAwayZero hb n]
  simp_all

open Classical in
/--
  Definition 5.3.16 (Reciprocation of real numbers).  Requires classical logic because we need to
  assign a "junk" value to the inverse of 0.
-/
noncomputable instance Real.instInv : Inv Real where
  -- Grab a bounded-away-from-zero sequence representative of x
  -- Then, invert that sequence termwise
  -- Take the limit of the result
  inv x := if h: x ≠ 0 then LIM (boundedAwayZero_of_nonzero h).choose⁻¹ else 0

-- If we *start* with a bounded-away-from-zero sequence,
-- Then the inverse can just be defined using this sequence
-- Rather than needing to find a new one
theorem Real.inv_def {a:ℕ → ℚ} (h: BoundedAwayZero a) (hc: (a:Sequence).IsCauchy) :
    (LIM a)⁻¹ = LIM a⁻¹ := by
  observe hx : LIM a ≠ 0 -- From bounded away from zero, the limit can't be zero
  set x := LIM a
  -- Grab the bounded-away sequence that inv uses to define x⁻¹
  have ⟨ h1, h2, h3 ⟩ := (boundedAwayZero_of_nonzero hx).choose_spec
  simp [instInv, hx, -Quotient.eq]
  -- Lims equivalent → inverse lims equivalent
  exact inv_of_equiv h2 h1 h hc h3.symm

@[simp]
theorem Real.inv_zero : (0:Real)⁻¹ = 0 := by simp [Inv.inv] -- Junk val

theorem Real.self_mul_inv {x:Real} (hx: x ≠ 0) : x * x⁻¹ = 1 := by
  choose a ha hba hla using boundedAwayZero_of_nonzero hx
  rw [hla, Real.inv_def hba ha]
  rw [Real.LIM_mul ha (Real.inv_isCauchy_of_boundedAwayZero hba ha)]
  rw [OfNat_eq_ratCast, Real.ratCast_def]
  rcongr n; simp [(nonzero_of_boundedAwayZero hba n)]

theorem Real.inv_mul_self {x:Real} (hx: x ≠ 0) : x⁻¹ * x = 1 := by
  rw [mul_comm]; apply Real.self_mul_inv hx

-- Constant sequences are bounded away from zero if the constant is nonzero
lemma BoundedAwayZero.const {q : ℚ} (hq : q ≠ 0) : BoundedAwayZero fun _ ↦ q := by
  use |q|; simp [hq];

-- Inverse carries over ratCast
theorem Real.inv_ratCast (q:ℚ) : (q:Real)⁻¹ = (q⁻¹:ℚ) := by
  by_cases h : q = 0 -- In the zero case, inverse is junk value 0
  · rw [h, ← show (0:Real) = (0:ℚ) by norm_cast]; norm_num; norm_cast
  -- Turn into LIM form for both. Move ⁻¹ from outside the LIM to inside
  simp_rw [ratCast_def, inv_def (BoundedAwayZero.const h) (by apply Sequence.IsCauchy.const)]; congr

/-- Default definition of division -/
noncomputable instance Real.instDivInvMonoid : DivInvMonoid Real where

theorem Real.div_eq (x y:Real) : x/y = x * y⁻¹ := rfl

noncomputable instance Real.instField : Field Real where
  exists_pair_ne := by use (0:ℚ), (1:ℚ); simp; -- Use injectivity of ratCast, rats are distinct
  mul_inv_cancel := by intro a ha; apply Real.self_mul_inv ha
  inv_zero := Real.inv_zero
  ratCast_def := by
    intro q;
    observe hden: q.den ≠ 0
    observe hq : q = q.num / q.den
    nth_rw 1 [hq]; -- We want to show that ratCast passes through div
    rw [div_eq, div_eq_mul_inv, ← Real.ratCast_mul]; -- Div = invmul, ratCast mul
    congr
    -- Move inv inside cast and LIM
    rw [ratCast_def, natCast_def ]
    rw [inv_def (BoundedAwayZero.const ?_) (Sequence.IsCauchy.const _)]
    -- Clean up
    congr
    norm_cast


  qsmul := _
  nnqsmul := _

-- Cancellation law
theorem Real.mul_right_cancel₀ {x y z:Real} (hz: z ≠ 0) (h: x * z = y * z) : x = y := by
  observe: x * z * z⁻¹ = y * z * z⁻¹
  --field_simp at this; exact this
  have : x * (z * z⁻¹) = y * (z * z⁻¹) := by rw [← mul_assoc, ← mul_assoc, this]
  rw [Real.self_mul_inv hz, mul_one, mul_one] at this; exact this


-- ONLY works if we know z = 0
theorem Real.mul_right_nocancel : ¬ ∀ (x y z:Real), (hz: z = 0) → (x * z = y * z) → x = y := by
  push_neg; use 0, 1, 0; simp

/-- Exercise 5.3.4 -/
theorem Real.IsBounded.equiv {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hab: Sequence.Equiv a b) :
    (b:Sequence).IsBounded := by
    rw [Sequence.equiv_def] at hab
    specialize hab 1 (by norm_num)
    rw [Sequence.isBounded_of_eventuallyClose hab] at ha
    exact ha

/--
  Same as `Sequence.IsCauchy.harmonic` but reindexing the sequence as a₀ = 1, a₁ = 1/2, ...
  This form is more convenient for the upcoming proof of Theorem 5.5.9.
-/
theorem Sequence.IsCauchy.harmonic' : ((fun n ↦ 1/((n:ℚ)+1): ℕ → ℚ):Sequence).IsCauchy := by
  rw [coe]; intro ε hε; choose N h1 h2 using (mk _).mp harmonic ε hε
  use N.toNat; intro j _ k _; specialize h2 (j+1) _ (k+1) _ <;> try omega
  simp_all

/-- Exercise 5.3.5 -/
theorem Real.LIM.harmonic : LIM (fun n ↦ 1/((n:ℚ)+1)) = 0 := by
  rw [Real.OfNat_def, show ((0:ℕ):ℚ) = 0 by norm_cast]
  -- Equivalent sequences
  rw [LIM_eq_LIM (Sequence.IsCauchy.harmonic') (Sequence.IsCauchy.const 0)]
  rw [Sequence.equiv_def]; intro e he
  -- N > 1/e means that for n ≥ N, 1/(n+1) < e
  choose N hN using exists_nat_ge (1/e)
  use N+1; intro i hi _; simp at hi;
  lift i to ℕ using (by linarith)
  simp [hi, Rat.Close]
  rw [abs_of_nonneg] -- 1/(i+1) is nonneg
  -- Handle inequality chain
  observe hip: 0 < ((i:ℚ)+1)
  have hN : (N:ℚ) + 1 ≤ (i:ℚ) + 1 := by norm_cast; linarith
  have he : 1/e ≤ (i:ℚ)+1 := by linarith
  -- We just need to invert both sides
  rw [ inv_le_comm₀ (by linarith) (by linarith)];
  field_simp [he]
  apply Rat.inv_nonneg (by linarith)

end Chapter5


namespace Chapter5

attribute [-simp] Chapter4_3.abs_eq_abs
/--
  Definition 5.4.1 (sequences bounded away from zero with sign). Sequences are indexed to start
  from zero as this is more convenient for Mathlib purposes.
-/
abbrev BoundedAwayPos (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≥ c

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
abbrev BoundedAwayNeg (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≤ -c

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
theorem boundedAwayPos_def (a:ℕ → ℚ) : BoundedAwayPos a ↔ ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≥ c := by
  rfl

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
theorem boundedAwayNeg_def (a:ℕ → ℚ) : BoundedAwayNeg a ↔ ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≤ -c := by
  rfl

/-- Examples 5.4.2 -/
example : BoundedAwayPos (fun n ↦ 1 + 10^(-(n:ℤ)-1)) := ⟨ 1, by norm_num, by intros; simp; apply zpow_nonneg; norm_num⟩

/-- Examples 5.4.2 -/
example : BoundedAwayNeg (fun n ↦ -1 - 10^(-(n:ℤ)-1)) := ⟨ 1, by norm_num, by intros; simp; apply zpow_nonneg; norm_num ⟩

/-- Examples 5.4.2 -/
example : ¬ BoundedAwayPos (fun n ↦ (-1)^n) := by
  intro ⟨ c, h1, h2 ⟩; specialize h2 1; simp at h2; linarith
/-- Examples 5.4.2 -/
example : ¬ BoundedAwayNeg (fun n ↦ (-1)^n) := by
  intro ⟨ c, h1, h2 ⟩; specialize h2 0; simp at h2; linarith

/-- Examples 5.4.2 -/
example : BoundedAwayZero (fun n ↦ (-1)^n) := ⟨ 1, by norm_num, by intros; simp ⟩

theorem BoundedAwayZero.boundedAwayPos {a:ℕ → ℚ} (ha: BoundedAwayPos a) : BoundedAwayZero a := by
  peel 3 ha with c h1 n hn; rwa [abs_of_nonneg (by linarith)]


theorem BoundedAwayZero.boundedAwayNeg {a:ℕ → ℚ} (ha: BoundedAwayNeg a) : BoundedAwayZero a := by
  peel 3 ha with c h1 n h2; rw [abs_of_neg (by linarith)]; linarith

theorem not_boundedAwayPos_boundedAwayNeg {a:ℕ → ℚ} : ¬ (BoundedAwayPos a ∧ BoundedAwayNeg a) := by
  intro ⟨ ⟨ _, _, h2⟩ , ⟨ _, _, h4 ⟩ ⟩; linarith [h2 0, h4 0]

abbrev Real.IsPos (x:Real) : Prop :=
  ∃ a:ℕ → ℚ, BoundedAwayPos a ∧ (a:Sequence).IsCauchy ∧ x = LIM a

abbrev Real.IsNeg (x:Real) : Prop :=
  ∃ a:ℕ → ℚ, BoundedAwayNeg a ∧ (a:Sequence).IsCauchy ∧ x = LIM a

theorem Real.isPos_def (x:Real) :
    IsPos x ↔ ∃ a:ℕ → ℚ, BoundedAwayPos a ∧ (a:Sequence).IsCauchy ∧ x = LIM a := by rfl

theorem Real.isNeg_def (x:Real) :
    IsNeg x ↔ ∃ a:ℕ → ℚ, BoundedAwayNeg a ∧ (a:Sequence).IsCauchy ∧ x = LIM a := by rfl

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.trichotomous (x:Real) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  by_cases hx0 : x = 0
  · left; exact hx0
  · -- This feels so redundant but I can't for the life of me figure out how to fix that
    right; choose a hac hab hax using Real.boundedAwayZero_of_nonzero hx0
    choose c hc hca using hab
    choose N hN hNc using hac (c/2) (half_pos hc); simp at hN
    lift N to ℕ using (by linarith)
    specialize hca N
    -- Create truncated sequence: valid equivalent for a, doesn't cross through zero
    let b := Real.truncated_seq N (a N) a
    have hbc := Real.truncated_seq_equiv N (a N) a
    have hbcauchy := (Sequence.isCauchy_of_equiv hbc).mp hac
    -- b is either positive or negative
    by_cases hcaN : a N > 0
    · left; simp [abs_of_pos hcaN] at hca
      refine ⟨b, ?_, hbcauchy, by rw [hax, (LIM_eq_LIM hac hbcauchy ).mpr hbc]⟩
      use c/2, half_pos hc; intro n
      -- Obvious case: n < N, truncated to a N, which is bounded below: c/2 < c ≤ a N
      by_cases hn: n < N <;> simp [b, Real.truncated_seq, hn]; linarith
      -- Other case: a N ≥ c, and |a n - a N| < c/2, so a n ≥ c/2
      specialize hNc n (by simp; linarith) N (by simp)
      push_neg at hn
      simp [hn, Rat.Close] at hNc -- |a n - a N| < c/2
      by_cases hnan : a n - a N ≥ 0
      · rw [abs_of_nonneg hnan] at hNc; linarith -- If a n ≥ a N, then c-bound holds
      -- Else, a n + c/2 ≥ a N ≥ c: a n is stuck within c/2 of a N
      · push_neg at hnan; simp [abs_of_neg hnan] at hNc; linarith
    · right; push_neg at hcaN; simp [abs_of_nonpos hcaN] at hca
      refine ⟨b, ?_, hbcauchy, by rw [hax, (LIM_eq_LIM hac hbcauchy ).mpr hbc]⟩
      use c/2, half_pos hc; intro n
      by_cases hn: n < N <;> simp [b, Real.truncated_seq, hn]; linarith
      specialize hNc n (by simp; linarith) N (by simp)
      push_neg at hn
      simp [hn, Rat.Close] at hNc
      by_cases hnan : a n - a N ≤ 0
      · rw [abs_of_nonpos hnan] at hNc; linarith -- Below a N: c-bound holds
      · push_neg at hnan; simp [abs_of_pos hnan] at hNc; linarith

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_zero_pos (x:Real) : ¬(x = 0 ∧ x.IsPos) := by
  intro ⟨h1,h2⟩; contrapose! h1
  choose a hab hac hax using h2
  rw [hax]
  apply Real.lim_of_boundedAwayZero (BoundedAwayZero.boundedAwayPos hab) hac

theorem Real.nonzero_of_pos {x:Real} (hx: x.IsPos) : x ≠ 0 := by
  simpa [hx] using not_zero_pos x

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_zero_neg (x:Real) : ¬(x = 0 ∧ x.IsNeg) := by
  intro ⟨h1,h2⟩; contrapose! h1
  choose a hab hac hax using h2
  rw [hax]
  apply Real.lim_of_boundedAwayZero (BoundedAwayZero.boundedAwayNeg hab) hac

theorem Real.nonzero_of_neg {x:Real} (hx: x.IsNeg) : x ≠ 0 := by
  simpa [hx] using not_zero_neg x

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_pos_neg (x:Real) : ¬(x.IsPos ∧ x.IsNeg) := by
  intro ⟨h1,h2⟩;
  choose a hap hac hax using h1
  choose z hz haz using hap

  choose b han hbc hbx using h2
  choose w hw hbw using han

  rw [hax, LIM_eq_LIM hac hbc, Sequence.equiv_iff] at hbx;
  choose N hN using hbx ((z+w)/2) (by linarith) -- an and bn should be eventually close
  specialize hN N (by linarith); specialize haz N; specialize hbw N;
  rw [abs_of_nonneg (by linarith)] at hN
  contrapose! hN
  linarith



/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
@[simp]
theorem Real.neg_iff_pos_of_neg (x:Real) : x.IsNeg ↔ (-x).IsPos := by
  constructor <;> intro h <;> choose a ha hac hax using h
  <;> refine ⟨-a, by peel 3 ha with c hc n hcn; simp; linarith,
              Real.IsCauchy.neg _ hac, ?_⟩
  <;> simp [← Real.neg_LIM _ hac, ← hax]

theorem Real.pos_iff_neg_of_pos (x:Real) : x.IsPos ↔ (-x).IsNeg := by
  constructor <;> intro h <;> choose a ha hac hax using h
  <;> refine ⟨-a, by peel 3 ha with c hc n hcn; simp; linarith,
              Real.IsCauchy.neg _ hac, ?_⟩
  <;> simp [← Real.neg_LIM _ hac, ← hax]

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.pos_add {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x+y).IsPos := by
  choose a hap hac hax using hx; choose A hA0 hA using hap
  choose b hbp hbc hby using hy; choose B hB0 hB using hbp
  refine ⟨a + b, ?_, (hac.add hbc), by rw [hax, hby, Real.LIM_add hac hbc]⟩
  refine ⟨A+B, by linarith, ?_⟩
  intro n; simp; linarith [hA n, hB n]


/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.pos_mul {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x*y).IsPos := by
  choose a hap hac hax using hx; choose A hA0 hA using hap
  choose b hbp hbc hby using hy; choose B hB0 hB using hbp
  refine ⟨a * b, ?_, (hac.mul hbc), by rw [hax, hby, Real.LIM_mul hac hbc]⟩
  refine ⟨A*B, by nlinarith, ?_⟩
  intro n; simp; nlinarith [hA n, hB n]

theorem Real.pos_of_coe (q:ℚ) : (q:Real).IsPos ↔ q > 0 := by
  constructor <;> intro h
  · choose a hap hac hax using h; choose A hA0 hA using hap
    rw [ratCast_def q,
        LIM_eq_LIM (Sequence.IsCauchy.const _) hac,
        Sequence.equiv_iff] at hax;
    choose N hN using hax (A/2) (by linarith);
    specialize hN N (by linarith)
    suffices q ≥ A/2 by linarith
    by_cases hqan : q - (a N) ≥ 0
    · rw [abs_of_nonneg hqan] at hN; linarith [hA N]
    · push_neg at hqan; rw [abs_of_neg hqan] at hN; linarith [hA N]
  · refine ⟨(fun n ↦ q),?_, Sequence.IsCauchy.const _, ratCast_def q⟩
    use q; simp [h]

theorem Real.neg_of_coe (q:ℚ) : (q:Real).IsNeg ↔ q < 0 := by
  constructor <;> intro h
  · choose a hbp hbc hbx using h; choose B hB0 hB using hbp
    rw [ratCast_def q,
        LIM_eq_LIM (Sequence.IsCauchy.const _) hbc,
        Sequence.equiv_iff] at hbx;
    choose N hN using hbx (B/2) (by linarith);
    specialize hN N (by linarith)
    suffices q ≤ -B/2 by linarith
    by_cases hqan : q - (a N) ≤ 0
    · rw [abs_of_nonpos hqan] at hN; linarith [ hB N]
    · push_neg at hqan; rw [abs_of_pos hqan] at hN; linarith [ hB N]
  · refine ⟨(fun n ↦ q),?_, Sequence.IsCauchy.const _, ratCast_def q⟩
    use -q; simp [h]

open Classical in
/-- Need to use classical logic here because isPos and isNeg are not decidable -/
noncomputable abbrev Real.abs (x:Real) : Real := if x.IsPos then x else (if x.IsNeg then -x else 0)

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_pos (x:Real) (hx: x.IsPos) : abs x = x := by
  simp [abs, hx]

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_neg (x:Real) (hx: x.IsNeg) : abs x = -x := by
  have : ¬x.IsPos := by have := not_pos_neg x; simpa [hx] using this
  simp [abs, hx, this]

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_zero : abs 0 = 0 := by
  have hpos: ¬(0:Real).IsPos := by have := not_zero_pos 0; simpa using this
  have hneg: ¬(0:Real).IsNeg := by have := not_zero_neg 0; simpa using this
  simp [abs, hpos, hneg]

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLT : LT Real where
  lt x y := (x-y).IsNeg

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLE : LE Real where
  le x y := (x < y) ∨ (x = y)

theorem Real.lt_iff (x y:Real) : x < y ↔ (x-y).IsNeg := by rfl
theorem Real.le_iff (x y:Real) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

theorem Real.gt_iff (x y:Real) : x > y ↔ (x-y).IsPos := by
  simp [lt_iff]

theorem Real.ge_iff (x y:Real) : x ≥ y ↔ (x > y) ∨ (x = y) := by
  simp [le_iff, show y = x ↔ x = y by aesop]


theorem Real.lt_of_coe (q q':ℚ): q < q' ↔ (q:Real) < (q':Real) := by
  simp [lt_iff, Real.ratCast_sub, Real.neg_of_coe (q-q')]

theorem Real.gt_of_coe (q q':ℚ): q > q' ↔ (q:Real) > (q':Real) := Real.lt_of_coe _ _

theorem Real.isPos_iff (x:Real) : x.IsPos ↔ x > 0 := by simp [gt_iff]
theorem Real.isNeg_iff (x:Real) : x.IsNeg ↔ x < 0 := by simp [lt_iff]

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.trichotomous' (x y:Real) : x > y ∨ x < y ∨ x = y := by
  have := Real.trichotomous (x - y)
  rw [← gt_iff, ← lt_iff, sub_eq_zero] at this
  tauto

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_gt_and_lt (x y:Real) : ¬ (x > y ∧ x < y):= by
  rw [gt_iff, lt_iff]; apply not_pos_neg

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_gt_and_eq (x y:Real) : ¬ (x > y ∧ x = y):= by
  rw [gt_iff, ← sub_eq_zero, And.comm]; apply not_zero_pos (x-y)

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_lt_and_eq (x y:Real) : ¬ (x < y ∧ x = y):= by
  rw [lt_iff, ← sub_eq_zero, And.comm]; apply not_zero_neg (x-y)

/-- Proposition 5.4.7(b) (order is anti-symmetric) / Exercise 5.4.2 -/
theorem Real.antisymm (x y:Real) : x < y ↔ (y - x).IsPos := by
  rw [lt_iff, neg_iff_pos_of_neg (x - y), show -(x-y) = y-x by ring];

/-- Proposition 5.4.7(c) (order is transitive) / Exercise 5.4.2 -/
theorem Real.lt_trans {x y z:Real} (hxy: x < y) (hyz: y < z) : x < z := by
  rw [antisymm] at *; convert pos_add hxy hyz using 1; ring

/-- Proposition 5.4.7(d) (addition preserves order) / Exercise 5.4.2 -/
theorem Real.add_lt_add_right {x y:Real} (z:Real) (hxy: x < y) : x + z < y + z := by
  rw [lt_iff] at *; simp_all

/-- Proposition 5.4.7(e) (positive multiplication preserves order) / Exercise 5.4.2 -/
theorem Real.mul_lt_mul_right {x y z:Real} (hxy: x < y) (hz: z.IsPos) : x * z < y * z := by
  rw [antisymm] at *; convert pos_mul hxy hz using 1; ring



/-- Proposition 5.4.7(e) (positive multiplication preserves order) / Exercise 5.4.2 -/
theorem Real.mul_le_mul_left {x y z:Real} (hxy: x ≤ y) (hz: z.IsPos) : z * x ≤ z * y := by
  rw [le_iff] at *;
  rcases hxy with (hxy | rfl)
  · left; convert mul_lt_mul_right hxy hz using 1 <;> ring
  · simp

theorem Real.mul_le_mul_right {x y z:Real} (hxy: x ≤ y) (hz: z.IsPos) : x * z ≤ y * z := by
  rw [mul_comm x z, mul_comm y z]; apply Real.mul_le_mul_left hxy hz

theorem Real.mul_pos_neg {x y:Real} (hx: x.IsPos) (hy: y.IsNeg) : (x * y).IsNeg := by
  rw [neg_iff_pos_of_neg] at *; convert pos_mul hx hy using 1; ring



theorem Real.mul_lt_mul_right_mpr {x y z:Real} (hxy: x * z < y * z) (hz: z.IsPos) : x < y := by
  rw [antisymm, show y*z-x*z=(y-x)*z by ring] at *;
  rcases Real.trichotomous (y - x) with h' | h' | h'
  · rw [h'] at hxy; simp at hxy; exfalso
    have := Real.nonzero_of_pos hxy;
    contradiction
  · exact h'
  · have := mul_pos_neg hz h'
    exfalso; convert Real.not_pos_neg _ ⟨hxy, ?_⟩
    convert this using 1; ring

open Classical in
/--
  (Not from textbook) Real has the structure of a linear ordering. The order is not computable,
  and so classical logic is required to impose decidability.
-/
noncomputable instance Real.instLinearOrder : LinearOrder Real where
  le_refl := by intro a; rw [le_iff]; right; rfl
  le_trans := by
    intro a b c hab hbc; rw [le_iff] at *
    rcases hab with (hab | rfl) <;> rcases hbc with (hbc | rfl) <;> try tauto
    · left; exact lt_trans hab hbc
  lt_iff_le_not_ge := by
    intro a b; simp [le_iff]; push_neg
    constructor <;> intro h
    · refine ⟨by left; exact h, ⟨?_, ?_⟩⟩
      · have := Real.not_gt_and_lt a b; tauto
      · simp [Eq.comm]; have := Real.not_lt_and_eq a b; tauto
    · have := trichotomous' a b; tauto
  le_antisymm := by
    intro a b hab hba; rw [le_iff] at *;
    rcases hab with (hab | rfl) <;> rcases hba with (hba | hba) <;> try rfl
    · exfalso; exact not_gt_and_lt a b ⟨hba, hab⟩
    · symm; exact hba
  le_total := by
    intro a b; repeat rw [le_iff]
    rcases Real.trichotomous' a b with (hab | hab | hab) <;> tauto
  toDecidableLE := Classical.decRel _

/--
  (Not from textbook) Linear Orders come with a definition of absolute value |.|
  Show that it agrees with our earlier definition.
-/

@[simp]
theorem Real.abs_eq_abs (x:Real) : |x| = abs x := by
  rcases Real.trichotomous x with h | h | h <;> simp [h, _root_.abs]
  · have hp := h; rw [isPos_iff] at hp
    have hn := h; rw [pos_iff_neg_of_pos] at hn; rw [isNeg_iff] at hn
    apply le_trans (le_of_lt hn) (le_of_lt hp)
  · have hp := h; rw [isNeg_iff] at hp
    have hn := h; rw [neg_iff_pos_of_neg] at hn; rw [isPos_iff] at hn
    apply le_trans (le_of_lt hp) (le_of_lt hn)

/-- Proposition 5.4.8 -/
theorem Real.inv_of_pos {x:Real} (hx: x.IsPos) : x⁻¹.IsPos := by
  observe hnon: x ≠ 0
  observe hident : x⁻¹ * x = 1
  have hinv_non: x⁻¹ ≠ 0 := by contrapose! hident; simp [hident]
  have hnonneg : ¬x⁻¹.IsNeg := by
    intro h
    observe : (x * x⁻¹).IsNeg
    have id : -(1:Real) = (-1:ℚ) := by simp
    rw [neg_iff_pos_of_neg, self_mul_inv hnon, id, pos_of_coe] at this
    linarith
  have trich := trichotomous x⁻¹
  simpa [hinv_non, hnonneg] using trich

theorem Real.div_of_pos {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x/y).IsPos := by
  have := Real.inv_of_pos hy; convert (Real.pos_mul hx this) using 1



theorem Real.inv_of_gt {x y:Real} (hx: x.IsPos) (hy: y.IsPos) (hxy: x > y) : x⁻¹ < y⁻¹ := by
  observe hxnon: x ≠ 0
  observe hynon: y ≠ 0
  observe hxinv : x⁻¹.IsPos
  by_contra! this
  have : (1:Real) > 1 := calc
    1 = x * x⁻¹ := (self_mul_inv hxnon).symm
    _ > y * x⁻¹ := mul_lt_mul_right hxy hxinv
    _ ≥ y * y⁻¹ := mul_le_mul_left this hy
    _ = _ := self_mul_inv hynon
  simp at this

theorem Real.mul_lt_mul_left {x y z:Real} (hxy: x < y) (hz: z.IsPos) : z * x < z * y := by
  rw [antisymm] at *; convert pos_mul hxy hz using 1; ring

theorem Real.self_inv_mul {x:Real} (hx: x ≠ 0) : x⁻¹ * x = 1 := by
  rw [mul_comm]; apply self_mul_inv hx

-- My preferred way to prove inv_of_gt
theorem Real.inv_of_gt' {x y:Real} (hx: x.IsPos) (hy: y.IsPos) (hxy: x > y) : x⁻¹ < y⁻¹ := by
  observe hxnon: x ≠ 0
  observe hynon: y ≠ 0
  have hxinv : x⁻¹.IsPos := Real.inv_of_pos hx
  have hyinv : y⁻¹.IsPos := Real.inv_of_pos hy
  have : x * x⁻¹ > y * x⁻¹ :=  mul_lt_mul_right hxy hxinv
  have : y⁻¹ * (x * x⁻¹) > y⁻¹ * (y * x⁻¹) := mul_lt_mul_left this hyinv
  simpa [self_mul_inv hxnon, ← mul_assoc, self_inv_mul hynon] using this



theorem Real.add_le_add_right' (a b :Real) (hab: a ≤ b) (c : Real): a + c ≤ b + c := by
  rw [le_iff] at *
  rcases hab with (hab | rfl)
  · left; exact Real.add_lt_add_right _ hab
  · right; rfl

theorem Real.mul_lt_mul_of_pos_right' (a b c :Real) (hab: a < b) (hc: 0 < c) : a * c < b * c := by
  simp [← isPos_iff] at hc
  apply mul_lt_mul_right hab hc

/-- (Not from textbook) Real has the structure of a strict ordered ring. -/
instance Real.instIsStrictOrderedRing : IsStrictOrderedRing Real where
  add_le_add_left := by
    intro a b hab c; rw [add_comm c a, add_comm c b]
    apply Real.add_le_add_right'; exact hab
  add_le_add_right := Real.add_le_add_right'
  mul_lt_mul_of_pos_left := by
    intro a b c hab hc; rw [mul_comm c a, mul_comm c b]
    apply mul_lt_mul_of_pos_right' _ _ _ hab hc
  mul_lt_mul_of_pos_right := Real.mul_lt_mul_of_pos_right'
  le_of_add_le_add_left := by
    intro a b c habc; rw [add_comm a b, add_comm a c] at habc
    rw [le_iff] at *; rcases habc with (habc | habc)
    · left; rw [lt_iff] at *; simp at habc
      rw [pos_iff_neg_of_pos] at habc
      simpa using habc
    · right; simpa using habc
  zero_le_one := by
    rw [le_iff]; left; simp [lt_iff];
    rw [Real.OfNat_eq_ratCast, pos_of_coe]; norm_num

/-- Proposition 5.4.9 (The non-negative reals are closed)-/
theorem Real.LIM_of_nonneg {a: ℕ → ℚ} (ha: ∀ n, a n ≥ 0) (hcauchy: (a:Sequence).IsCauchy) :
    LIM a ≥ 0 := by
  by_contra! hlim
  set x := LIM a
  rw [←isNeg_iff, isNeg_def] at hlim; choose b hb hb_cauchy hlim using hlim
  -- b n is negative-bounded, so it's trapped behind some negative constant -c
  rw [boundedAwayNeg_def] at hb; choose c cpos hb using hb
  -- Since a n is trapped behind +0 and b n is trapped behind -c, so distance > c/2
  have claim1 : ∀ n, ¬ (c/2).Close (a n) (b n) := by
    intro n; specialize ha n; specialize hb n
    simp [Rat.Close];
    calc
      _ < c := by linarith
      _ ≤ a n - b n := by linarith
      _ ≤ _ := le_abs_self _
  -- Thus, a and b cannot get c/2-close
  have claim2 : ¬(c/2).EventuallyClose (a:Sequence) (b:Sequence) := by
    contrapose! claim1; rw [Rat.eventuallyClose_iff] at claim1;
    peel claim1 with N claim1; apply claim1 N (by linarith)
  -- And therefore, they're separate, non-equal sequences
  have claim3 : ¬Sequence.Equiv a b := by
    contrapose! claim2; rw [Sequence.equiv_def] at claim2; solve_by_elim [half_pos]
  -- But they're supposed to be equivalent: come from same Real
  simp_rw [x, LIM_eq_LIM hcauchy hb_cauchy] at hlim
  contradiction

/-- Corollary 5.4.10 -/
theorem Real.LIM_mono {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy)
  (hmono: ∀ n, a n ≤ b n) :
    LIM a ≤ LIM b := by
  have := LIM_of_nonneg (a := b - a) (by intro n; simp [hmono n]) (Sequence.IsCauchy.sub hb ha)
  rw [←Real.LIM_sub hb ha] at this; linarith

/-- Remark 5.4.11 --/
theorem Real.LIM_mono_fail :
    ∃ (a b:ℕ → ℚ), (a:Sequence).IsCauchy
    ∧ (b:Sequence).IsCauchy
    ∧ (∀ n, a n > b n)
    ∧ ¬LIM a > LIM b := by
  use ((fun (n:ℕ) ↦ (1:ℚ) ) + (fun (n:ℕ) ↦ 1/((n:ℚ) + 1)))
  use ((fun (n:ℕ) ↦ (1:ℚ) ) - (fun (n:ℕ) ↦ 1/((n:ℚ) + 1)))
  have hch:= Sequence.IsCauchy.harmonic'
  have hx1 := Sequence.IsCauchy.const 1
  constructor; convert Sequence.IsCauchy.add hx1 hch
  constructor; convert Sequence.IsCauchy.sub hx1 hch
  constructor; intro n; simp; have : ((n:ℚ) + 1)⁻¹ > 0 := by positivity
  linarith;
  push_neg; rw [le_iff]; right
  rw [← LIM_add hx1 hch, ← LIM_sub hx1 hch, Real.LIM.harmonic]; simp

/-- Proposition 5.4.12 (Bounding reals by rationals) -/
theorem Real.exists_rat_le_and_nat_gt {x:Real} (hx:x.IsPos)  :
    (∃ q:ℚ, q > 0 ∧ (q:Real) ≤ x) ∧ ∃ N:ℕ, x < (N:Real) := by
  ---- Find the positive rational q ≤ x
  -- Each elem x_i bounded below by q: 0 < q ≤ x_i
  rw [isPos_def] at hx; choose a hbound hcauchy heq using hx
  rw [boundedAwayPos_def] at hbound; choose q hq hbound using hbound

  -- q ≤ x_i → q ≤ x
  refine ⟨ ⟨ q, hq, ?_ ⟩, ?_ ⟩
  · -- q can be treated as a constant sequence, then we can use mono
    convert LIM_mono (Sequence.IsCauchy.const _) hcauchy hbound
    exact Real.ratCast_def q
  ---- Find the natural number N > r
  -- Magnitude is bounded above by rational r: |x_i| ≤ r, 0 ≤ r
  have := Sequence.isBounded_of_isCauchy hcauchy
  rw [Sequence.isBounded_def] at this; choose r hr0 hr using this
  simp [Sequence.boundedBy_def] at hr
  -- There exists a natural N > r
  choose N hN using exists_nat_gt r; use N
  -- Thus, x < r < N → x < N
  calc
    x ≤ r := by
      rw [Real.ratCast_def r] -- Compare sequences, use mono
      convert LIM_mono hcauchy (Sequence.IsCauchy.const r) ?_
      -- We know each elem |x_i| ≤ r
      intro n; specialize hr n; simp at hr
      exact (le_abs_self _).trans hr -- x_i ≤ |x_i| ≤ r → x_i ≤ r
    _ < N := by simp [hN]

theorem Real.exists_rat_le {x:Real} (hx: x.IsPos) :
    (∃ q:ℚ, q > 0 ∧ (q:Real) ≤ x):= by
  choose q hq1 hq2 using (exists_rat_le_and_nat_gt hx).1
  use q

theorem Real.exists_nat_gt (x:Real) :
    ∃ N:ℕ, x < (N:Real) := by
  obtain rfl | hx | hx := trichotomous x
  · use 1; simp
  · choose N _ using (exists_rat_le_and_nat_gt hx).2
    use N
  · rw [isNeg_iff] at hx
    use 0; simp [hx]



theorem Real.exists_rat_lt {x:Real} (hx: x.IsPos) :
    (∃ q:ℚ, q > 0 ∧ (q:Real) < x) := by
  choose q hq1 hq2 using exists_rat_le hx
  use q/2; simp_all
  observe : 0 < (q:Real)
  linarith


theorem Real.exists_rat_le_strong (x:Real):
  ∃ q:ℚ, (q:Real) ≤ x := by
  obtain rfl | hx | hx := trichotomous x
  · use -1; simp
  · choose q _ _ using exists_rat_le hx
    use q
  · have hx' := (neg_iff_pos_of_neg _).1 hx
    choose N _ using exists_nat_gt (-x)
    use -N; simp; linarith

/-- Corollary 5.4.13 (Archimedean property ) -/
theorem Real.le_mul {ε:Real} (hε: ε.IsPos) (x:Real) : ∃ M:ℕ, M > 0 ∧ M * ε > x := by
  -- This proof is written to follow the structure of the original text.
  obtain rfl | hx | hx := trichotomous x
  · use 1; simpa [isPos_iff] using hε -- x = 0, so 1*ε = ε > 0 = x
  · -- We know x/ε > 0, so we can find N > x/ε
    choose N hN using exists_nat_gt (x/ε)
    -- We'll use N+1 to ensure N+1 > 0 rather than N ≥ 0
    set M := N+1; refine ⟨ M, by positivity, ?_ ⟩
    replace hN : x/ε < M := hN.trans (by simp [M]) -- by unfold M; simp; linarith
    simp
    convert mul_lt_mul_right hN hε -- Multiply both sides of hN
    rw [isPos_iff] at hε; field_simp -- Cancel out ε/ε=1 : requires ε ≠ 0
  · use 1; simp_all [isPos_iff]; linarith -- x < 0, so 1*ε = ε > 0 > x

-- The exercise in the book said to use 5.4.4 to do this, but since Tao
-- put this exercise first, I decided to approach it without using 5.4.4.
/-- Proposition 5.4.14 / Exercise 5.4.5 -/
theorem Real.rat_between {x y:Real} (hxy: x < y) : ∃ q:ℚ, x < (q:Real) ∧ (q:Real) < y := by
  by_contra h
  conv at h => arg 1; arg 1; intro q; rw [and_comm]
  push_neg at h
  choose q hq using exists_rat_le_strong x
  observe hxy' : 0 < y - x
  choose r hr1 hr2 using exists_rat_lt ((isPos_iff  _).2 hxy')

  -- We're restricted from going between x and y. So, if q ≤ x, and we add some r
  -- small enough to not exceed y, then we still need to be q + r ≤ x
  -- We can repeat this process to get q + n*r ≤ x
  have hcontra (n : ℕ ): q + n * r ≤ x := by
    induction' n with n ih
    · simp_all
    · have : (((q + n * r + r):ℚ):Real) < y := by push_cast; linarith
      specialize h _ this;
      simp_all; ring_nf; exact h

  -- This is absurd: we can always pick large enough n to exceed x, and cross the gap
  contrapose! hcontra
  choose n hn1 hn2 using le_mul ((isPos_iff r).2 (by norm_cast)) (x-q)
  use n; linarith

/-- Exercise 5.4.3 -/
theorem Real.floor_exist (x:Real) : ∃! n:ℤ, (n:Real) ≤ x ∧ x < (n:Real)+1 := by
  apply existsUnique_of_exists_of_unique
  · by_cases h0: x = 0
    · subst h0; use 0; simp
    wlog hpos : x > 0
    · have hlt: x < 0 := by push_neg at hpos; apply lt_of_le_of_ne hpos h0
      specialize this (-x) (by simp [h0]) (by linarith)
      choose n hn1 hn2 using this
      by_cases hxn : x = -(n:Real)
      · use -n; simp; refine ⟨by linarith, by linarith⟩
      · use -(n+1); simp;
        refine ⟨by linarith, ?_⟩
        apply lt_of_le_of_ne; linarith; exact hxn
    by_contra! h;
    have hcontra (n : ℕ ): n ≤ x := by
      induction' n with n ih
      · simp_all; linarith
      · specialize h n
        specialize h (by simp [ih])
        norm_cast at h
    choose N hN using exists_nat_gt x
    specialize hcontra N; linarith

  · intro y z ⟨hy1, hy2⟩ ⟨hz1, hz2⟩
    by_cases heq : y = z
    · tauto
    · wlog hyz : y < z
      · specialize this x z y hz1 hz2 hy1 hy2 (by apply Ne.symm; apply heq)
        specialize this (by simp_all; apply lt_of_le_of_ne hyz (Ne.symm heq))
        exact Eq.symm this
      have : y + 1 ≤ z:= by linarith -- If y < z, then y+1 ≤ z
      have : (y : Real) + 1 ≤ (z : Real) := by norm_cast
      linarith -- But then, x < y+1 ≤ z

/-- Exercise 5.4.4 -/
theorem Real.exist_inv_nat_le {x:Real} (hx: x.IsPos) : ∃ N:ℤ, N>0 ∧ (N:Real)⁻¹ < x := by
  choose N hN using exists_nat_gt (1/x)
  rw [isPos_iff] at hx;
  observe hpos : 0 < 1/x; observe hNpos : (N:Real) > 0
  use N; refine ⟨by norm_cast at *, ?_⟩
  simp_all; exact inv_lt_of_inv_lt₀ hx hN

-- noncomputable abbrev Real.abs (x:Real) : Real := if x.IsPos then x else (if x.IsNeg then -x else 0)

/-- Exercise 5.4.6 -/
theorem Real.dist_lt_iff (ε x y:Real) : |x-y| < ε ↔ y-ε < x ∧ x < y+ε := by
  rcases Real.trichotomous (x-y) with ( hxy | hxy | hxy )
  · simp [hxy]
    constructor <;> intro h
    · refine ⟨by linarith, by linarith⟩
    · linarith
  · simp [ abs_of_pos _ hxy]
    constructor <;> intro h
    · replace hxy := (isPos_iff _ ).1 hxy
      refine ⟨by linarith, by linarith⟩
    · linarith
  · simp [ abs_of_neg _ hxy]
    constructor <;> intro h
    · replace hxy := (isNeg_iff _ ).1 hxy
      refine ⟨by linarith, by linarith⟩
    · linarith

/-- Exercise 5.4.6 -/
theorem Real.dist_le_iff (ε x y:Real) : |x-y| ≤ ε ↔ y-ε ≤ x ∧ x ≤ y+ε := by
  rcases Real.trichotomous (x-y) with ( hxy | hxy | hxy )
  · simp [hxy]
    constructor <;> intro h
    · refine ⟨by linarith, by linarith⟩
    · linarith
  · simp [ abs_of_pos _ hxy]
    constructor <;> intro h
    · replace hxy := (isPos_iff _ ).1 hxy
      refine ⟨by linarith, by linarith⟩
    · linarith
  · simp [ abs_of_neg _ hxy]
    constructor <;> intro h
    · replace hxy := (isNeg_iff _ ).1 hxy
      refine ⟨by linarith, by linarith⟩
    · linarith

/-- Exercise 5.4.7 -/
theorem Real.le_add_eps_iff (x y:Real) : (∀ ε > 0, x ≤ y+ε) ↔ x ≤ y := by
  constructor <;> intro h
  · by_contra! hcontra; specialize h ((x-y)/2) (by linarith)
    linarith
  · intro e he; linarith

theorem Real.ne_zero_abs_pos (x:Real) (h : x ≠ 0): |x| > 0 := by
  rcases Real.trichotomous x with ( rfl | hpos | hneg )
  · contradiction
  · simp [abs_of_pos _ hpos]; rw [isPos_iff] at hpos; linarith
  · simp [abs_of_neg _ hneg]; rw [isNeg_iff] at hneg; linarith

/-- Exercise 5.4.7 -/
theorem Real.dist_le_eps_iff (x y:Real) : (∀ ε > 0, |x-y| ≤ ε) ↔ x = y := by
  constructor <;> intro h
  · contrapose! h;
    observe : x - y ≠ 0
    apply ne_zero_abs_pos at this
    use |x - y| / 2; simp_all
  · simp [h]; tauto

-- Suppose that LIM a broke past x, despite all a n terms being below it
-- That creates a whole range of rationals that LIM a managed to break past as well

-- But we know this isn't possible: we already proved that a sequence can't cross
-- a rational that bounds all its terms
-- All we have to do is pick one
/-- Exercise 5.4.8 -/
theorem Real.LIM_of_le {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy) (h: ∀ n, a n ≤ x) :
  LIM a ≤ x := by
    by_contra! hlim
    choose q hq1 hq2 using Real.rat_between hlim -- x < q < A
    contrapose! hq2; rw [ratCast_def q] -- A can't come after q:
    apply LIM_mono hcauchy (Sequence.IsCauchy.const q) -- a n ≤ x < q → a n ≤ q → A ≤ q
    intro n; specialize h n;
    suffices (a n : Real) ≤ (q : Real) by norm_cast at * -- Type management
    linarith

/-- Exercise 5.4.8 -/
theorem Real.LIM_of_ge {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy) (h: ∀ n, a n ≥ x) :
    LIM a ≥ x := by
  suffices LIM (-a) ≤ -x by rw [← neg_LIM _ hcauchy] at this; simpa using this
  apply Real.LIM_of_le (Real.IsCauchy.neg _ hcauchy) (by simpa)

theorem Real.max_eq (x y:Real) : max x y = if x ≥ y then x else y := max_def' x y

theorem Real.min_eq (x y:Real) : min x y = if x ≤ y then x else y := rfl

/-- Exercise 5.4.9 -/
theorem Real.neg_max (x y:Real) : max x y = - min (-x) (-y) := by
  simp [max_eq, min_eq]; split_ifs <;> simp

/-- Exercise 5.4.9 -/
theorem Real.neg_min (x y:Real) : min x y = - max (-x) (-y) := by
  simp [max_eq, min_eq]; split_ifs <;> simp

/-- Exercise 5.4.9 -/
theorem Real.max_comm (x y:Real) : max x y = max y x := by
  simp [max_eq]; split_ifs <;> linarith

/-- Exercise 5.4.9 -/
theorem Real.max_self (x:Real) : max x x = x := by
  rw [max_eq]; split_ifs <;> rfl -- Alternatively, simp works fine

/-- Exercise 5.4.9 -/
theorem Real.max_add (x y z:Real) : max (x + z) (y + z) = max x y + z := by
  by_cases h : y ≤ x <;> simp [max_eq] <;> simp [h]

/-- Exercise 5.4.9 -/
theorem Real.max_mul (x y :Real) {z:Real} (hz: z.IsPos) : max (x * z) (y * z) = max x y * z := by
  by_cases h : y ≤ x <;> simp [max_eq];
  · simp [Real.mul_le_mul_right h hz, h]
  · simp only [h]; push_neg at h;
    simp [not_le_of_gt (Real.mul_lt_mul_right h hz)]

/- Additional exercise: What happens if z is negative? -/

theorem Real.max_mul_neg (x y :Real) {z:Real} (hz: z.IsNeg) : max (x * z) (y * z) = min x y * z := by
  rw [neg_iff_pos_of_neg] at hz
  rw [neg_min, show -max (-x) (-y) * z = max (-x) (-y) * -z by ring]
  simp [← max_mul (-x) (-y) hz]


/-- Exercise 5.4.9 -/
theorem Real.min_comm (x y:Real) : min x y = min y x := by
  simp [min_eq]; split_ifs <;> linarith

/-- Exercise 5.4.9 -/
theorem Real.min_self (x:Real) : min x x = x := by
  rw [min_eq]; split_ifs <;> rfl

/-- Exercise 5.4.9 -/
theorem Real.min_add (x y z:Real) : min (x + z) (y + z) = min x y + z := by
  by_cases h : x ≤ y <;> simp [min_eq] <;> simp [h]

/-- Exercise 5.4.9 -/
theorem Real.min_mul (x y :Real) {z:Real} (hz: z.IsPos) : min (x * z) (y * z) = min x y * z := by
  simp [neg_min, ← max_mul _ _ hz]

/-- Exercise 5.4.9 -/
theorem Real.inv_max {x y :Real} (hx:x.IsPos) (hy:y.IsPos) : (max x y)⁻¹ = min x⁻¹ y⁻¹ := by
  by_cases h : y ≤ x <;> simp [max_eq, min_eq];
  · rw [isPos_iff] at *; simp [h, (inv_le_inv₀ hx hy).mpr h]
  · simp only [h]; push_neg at h;
    simp [not_le_of_gt (Real.inv_of_gt hy hx h)]

/-- Exercise 5.4.9 -/
theorem Real.inv_min {x y :Real} (hx:x.IsPos) (hy:y.IsPos) : (min x y)⁻¹ = max x⁻¹ y⁻¹ := by
  by_cases h : x ≤ y <;> simp [min_eq, max_eq];
  · rw [isPos_iff] at *; simp [h, (inv_le_inv₀ hy hx).mpr h]
  · simp only [h]; push_neg at h;
    simp [not_le_of_gt (Real.inv_of_gt hx hy h)]

/-- Not from textbook: the rationals map as an ordered ring homomorphism into the reals. -/
abbrev Real.ratCast_ordered_hom : ℚ →+*o Real where
  toRingHom := ratCast_hom
  monotone' := by intro x y hxy; simp [hxy]
  -- We're just showing that ratCast is order-preserving
  -- simp handles the previously established facts that
  -- < and = are both homomorphisms under ratCast

end Chapter5










namespace Chapter5

attribute [-simp] Chapter4_3.abs_eq_abs

/-- Definition 5.5.1 (upper bounds).  Here we use the `upperBounds` set defined in Mathlib. -/
theorem Real.upperBound_def (E: Set Real) (M: Real) : M ∈ upperBounds E ↔ ∀ x ∈ E, x ≤ M :=
  mem_upperBounds

theorem Real.lowerBound_def (E: Set Real) (M: Real) : M ∈ lowerBounds E ↔ ∀ x ∈ E, x ≥ M :=
  mem_lowerBounds

-- .Icc x y = Interval [x,y]
/-- API for Example 5.5.2 -/
theorem Real.Icc_def (x y:Real) : .Icc x y = { z | x ≤ z ∧ z ≤ y } := rfl

/-- API for Example 5.5.2 -/
theorem Real.mem_Icc (x y z:Real) : z ∈ Set.Icc x y ↔ x ≤ z ∧ z ≤ y := by simp [Real.Icc_def]

/-- Example 5.5.2 -/
example (M: Real) : M ∈ upperBounds (.Icc 0 1) ↔ M ≥ 1 := by
  rw [Real.upperBound_def]
  constructor <;> intro h
  · apply h 1 (by rw [Real.mem_Icc]; norm_num)
  · intro x hx; rw [Real.mem_Icc] at hx; linarith

-- .Ioi x = Interval (x, ∞)
/-- API for Example 5.5.3 -/
theorem Real.Ioi_def (x:Real) : .Ioi x = { z | z > x } := rfl



/-- Example 5.5.3 -/
example : ¬ ∃ M, M ∈ upperBounds (.Ioi (0:Real)) := by
  push_neg; intro M;
  rw [Real.upperBound_def, Real.Ioi_def];
  push_neg; use max (M+1) 1; simp

/-- Example 5.5.4 -/
example : ∀ M, M ∈ upperBounds (∅ : Set Real) := by
  intro M; rw [Real.upperBound_def]; intro x hx; contradiction

theorem Real.upperBound_upper {M M': Real} (h: M ≤ M') {E: Set Real} (hb: M ∈ upperBounds E) :
    M' ∈ upperBounds E := by
  rw [Real.upperBound_def] at *; peel hb with  _ _ hxm;
  apply le_trans hxm h

/-- Definition 5.5.5 (least upper bound).  Here we use the `isLUB` predicate defined in Mathlib. -/
theorem Real.isLUB_def (E: Set Real) (M: Real) :
    IsLUB E M ↔ M ∈ upperBounds E ∧ ∀ M' ∈ upperBounds E, M' ≥ M := by rfl

theorem Real.isGLB_def (E: Set Real) (M: Real) :
    IsGLB E M ↔ M ∈ lowerBounds E ∧ ∀ M' ∈ lowerBounds E, M' ≤ M := by rfl

/-- Example 5.5.6 -/
example : IsLUB (.Icc 0 1) (1:Real) := by
  rw [Real.isLUB_def, Real.upperBound_def, Real.Icc_def];
  constructor
  · intro x hx; simp at hx; exact hx.2
  · intro M hM; rw [Real.upperBound_def] at hM; apply hM 1 (by simp)


lemma upper_empty : ∀ M, M ∈ upperBounds (∅ : Set Real) := by
  intro M; rw [Real.upperBound_def]; intro x hx; contradiction

/-- Example 5.5.7 -/
example : ¬∃ M, IsLUB (∅: Set Real) M := by
  intro h; choose M hM using h; rw [Real.isLUB_def, Real.upperBound_def] at hM;
  obtain ⟨ _, hM ⟩ := hM; -- M-1 will be a lesser upper bound than M
  specialize hM (M-1) (upper_empty (M-1)); linarith -- No possible "least" UB


/-- Proposition 5.5.8 (Uniqueness of least upper bound)-/
theorem Real.LUB_unique {E: Set Real} {M M': Real} (h1: IsLUB E M) (h2: IsLUB E M') : M = M' := by
  rw [Real.isLUB_def] at *; choose h1key h1 using h1; choose h2key h2 using h2;
  specialize h1 M' h2key; specialize h2 M h1key;
  linarith -- grind didn't work for unknown reasons

/-- definition of "bounded above", using Mathlib notation -/
theorem Real.bddAbove_def (E: Set Real) : BddAbove E ↔ ∃ M, M ∈ upperBounds E := Set.nonempty_def

theorem Real.bddBelow_def (E: Set Real) : BddBelow E ↔ ∃ M, M ∈ lowerBounds E := Set.nonempty_def

lemma Real.upper_vs_nonupper {E: Set Real} {x y: Real}
  (hupper: x ∈ upperBounds E) (hnupper: y ∉ upperBounds E) : y < x := by
  rw [Real.upperBound_def] at *;
  push_neg at hnupper; choose z he h1 using hnupper
  specialize hupper z he; linarith



/-- Exercise 5.5.2 -/
theorem Real.upperBound_between {E: Set Real} {n:ℕ} {L K:ℤ} (hLK: L < K)
  (hK: (K*(1/(n+1):ℚ):Real) ∈ upperBounds E) (hL: (L*(1/(n+1):ℚ):Real) ∉ upperBounds E) :
    ∃ m, L < m
    ∧ m ≤ K
    ∧ m*((1/(n+1):ℚ):Real) ∈ upperBounds E
    ∧ (m-1)*((1/(n+1):ℚ):Real) ∉ upperBounds E := by
  have : n+1 > 0 := by positivity
  have : ((1/(n + 1):ℚ):Real) > 0 := by positivity
  by_contra! h
  -- If we can't ever cross over from non-upper bound to upper bound,
  -- Any amount we add to L still won't be an upper bound
  have hnupper: ∀ (x : ℕ ), ((L+x)*((1/(n+1)):ℚ):Real) ∉ upperBounds E := by
    intro x;
    induction' x with x ih
    · simp_all
    · -- We know L + x + 1 fits into the (L, K] range
      have := upper_vs_nonupper hK ih
      have: (L+x:Real) < K := by nlinarith
      have: L + x <   K := by exact_mod_cast this
      have : L + x + 1 ≤ K := by linarith
      -- Thus, we cannot have L + x below the bound, and L + x + 1 above it
      specialize h (L+x+1) (by linarith) (by linarith)
      -- Meaning: if L + x is not an upper bound, then neither is L + x + 1
      have h := mt h
      conv at h => lhs; arg 1; arg 2; arg 1; simp
      -- And we already know by induction that L + x is not an upper bound
      specialize h ih
      convert h; simp; rw [add_assoc]

  -- This means we can never exceed K either, since K *is* an upper bound
  have hcontra : ∀ (x : ℕ), x < (K-L) := by
    intro x; specialize hnupper x
    have heq := upper_vs_nonupper hK hnupper;
    suffices (L + x : Real) < K  by norm_cast at *; linarith
    nlinarith
  -- This is, of course, absurd: we can simply choose x = K-L
  specialize hcontra ((K-L).toNat); contrapose! hcontra; simp



/-- Exercise 5.5.3 -/
theorem Real.upperBound_discrete_unique {E: Set Real} {n:ℕ} {m m':ℤ}
(hm1: (((m:ℚ) / (n+1):ℚ):Real) ∈ upperBounds E)
(hm2: (((m:ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∉ upperBounds E)
(hm'1: (((m':ℚ) / (n+1):ℚ):Real) ∈ upperBounds E)
(hm'2: (((m':ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∉ upperBounds E) :
m = m' := by
  by_contra! hne
  wlog hlt : m < m' -- Flipping m and m' doesn't matter
  · exact this hm'1 hm'2 hm1 hm2 (Ne.symm hne) (by push_neg at hlt; omega)
  -- 1. If m' greater, then m can only be as large as m'-1
  have hmm': m ≤ m' - 1 := by linarith
  -- 2. But if m/(n+1) is an upper bound, that makes (m'-1)/(n+1) one, too
  apply hm'2; --Which is a contradiction
  refine (Real.upperBound_upper ?_ hm1)
  -- Cleanup work for the obvious link: m-1 ≤ m → m/(n+1) ≤ (m'-1)/(n+1)
  have h0: (n+1:Real) > 0 := by positivity
  push_cast; field_simp
  rw [div_le_div_iff₀ h0 h0]; field_simp
  exact_mod_cast hmm'


-- I realized this is a built-in lemma, but since I proved it
-- myself, I might as well keep it
lemma abs_abs_sub_abs_le_abs_sub' (a b : ℚ) : |(|a| - |b|)| ≤ |a - b| := by
  by_cases hjk : |a| - |b| ≥ 0
  · rw [abs_of_nonneg hjk]
    exact abs_sub_abs_le_abs_sub _ _
  · rw [abs_of_neg (by linarith), abs_sub_comm]
    convert abs_sub_abs_le_abs_sub b _ using 1; ring

/-- Lemmas that can be helpful for proving 5.5.4 -/
theorem Sequence.IsCauchy.abs {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy):
  ((|a| : ℕ → ℚ) : Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe] at *; peel ha with e he N j hj k hk h
  rw [Chapter4_3.dist_eq] at *
  refine le_trans (by apply abs_abs_sub_abs_le_abs_sub) h


theorem Real.LIM.abs_eq {a b:ℕ → ℚ} (ha: (a: Sequence).IsCauchy)
    (hb: (b: Sequence).IsCauchy) (h: LIM a = LIM b): LIM |a| = LIM |b| := by
  rw [LIM_eq_LIM ha hb] at h;
  rw [LIM_eq_LIM (Sequence.IsCauchy.abs ha) (Sequence.IsCauchy.abs hb)]
  rw [Sequence.equiv_iff] at *
  peel h with e he N n hn h
  apply le_trans (by apply abs_abs_sub_abs_le_abs_sub) h


lemma Rat.dist_le_iff (ε a b : ℚ) : |a - b| ≤ ε ↔ b - ε ≤ a ∧ a ≤ b + ε := by
  exact_mod_cast Real.dist_le_iff ε a b

theorem Real.LIM.abs_eq_pos {a: ℕ → ℚ} (h: LIM a > 0) (ha: (a:Sequence).IsCauchy):
LIM a = LIM |a| := by
  rw [← isPos_iff, Real.isPos_def] at h
  choose b hbound hb heq using h
  choose B hBpos hbB using hbound
  rw [heq, Real.LIM.abs_eq ha hb heq]
  congr; ext n; simp; rw [abs_of_nonneg];
  specialize hbB n; linarith

-- My original messy proof before I realized I could use abs_eq to
-- get rid of a entirely and only use the b bound
theorem Real.LIM.abs_eq_pos' {a: ℕ → ℚ} (h: LIM a > 0) (ha: (a:Sequence).IsCauchy):
  LIM a = LIM |a| := by -- Our goal: a n and |a| n become arbitrarily close
  rw [LIM_eq_LIM ha (Sequence.IsCauchy.abs ha), Sequence.equiv_iff]
  intro e he;
  rw [← isPos_iff, Real.isPos_def] at h  -- Positive LIM a means that...
  choose b hbound hb heq using h  --It is equivalent to b, which is bounded below
  choose B hBpos hbB using hbound

  rw [LIM_eq_LIM ha hb, Sequence.equiv_iff] at heq
  choose N hN using heq B hBpos
  have: ∀ n ≥ N, a n ≥ 0 := by-- At some point, a n is trapped in a B-fence around b n
    peel hN with n hn hB
    specialize hbB n
    rw [Rat.dist_le_iff] at hB  -- Thus, a n can't go below b n - B, which is positive
    linarith
  use N; intro n hN; simp [abs_of_nonneg (this n hN)]; linarith


theorem Real.LIM_abs {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy): |LIM a| = LIM |a| := by
  have habs := Sequence.IsCauchy.abs ha
  have haneg := Real.IsCauchy.neg _ ha
  rcases Real.trichotomous' (LIM a) 0 with ( hpos | hneg | heq)
  · rw [_root_.abs_of_pos hpos]; apply Real.LIM.abs_eq_pos hpos ha
  · rw [_root_.abs_of_neg hneg];
    have : LIM (-a) > 0 := by rw [← neg_LIM _ ha]; linarith
    rw [neg_LIM _ ha, show (|a| = |-a|) by simp];
    apply Real.LIM.abs_eq_pos this haneg
  · rw [abs_of_nonneg (by linarith), heq];
    rw [← LIM.zero,LIM_eq_LIM, Sequence.equiv_iff] at *;
    peel heq with e he N n hN h; simp_all;
    any_goals apply (Sequence.IsCauchy.const 0);
    apply ha; apply habs

-- LIM_mono uses a rational as a bound
-- LIM_of_le uses a real as a bound
-- LIM_of_le' allows us to start partway through the sequence
theorem Real.LIM_of_le' {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy)
(h: ∃ N, ∀ n ≥ N, a n ≤ x) : LIM a ≤ x := by
  choose N hN using h
  set b := Real.truncated_seq N (a N) a -- Use truncated sequence
  have hbcauchy := truncated_seq_isCauchy N (a N) a hcauchy
  rw [truncated_seq_eq_LIM N (a N) a hcauchy]
  apply Real.LIM_of_le hbcauchy; intro n
  unfold Real.truncated_seq;
  by_cases hn : n < N <;> simp [hn]
  · exact hN N (by linarith)
  · exact hN n (by linarith)


/-- Exercise 5.5.4 -/
theorem Real.LIM_of_Cauchy' {q:ℕ → ℚ} (hq: ∀ M, ∀ n ≥ M, ∀ n' ≥ M, |q n - q n'| ≤ 1 / (M+1)) :
(q:Sequence).IsCauchy:= by
  -- If our terms can be 1/M close, they can be arbitrarily close (by increasing M)
  rw [Sequence.IsCauchy.coe]; intro e he
  choose N hN using exists_nat_gt (1/e);
  have hN : 0 < N + 1 := by positivity
  have h : 1 / e ≤ (N:Real) + 1 := by linarith
  have h: 1 / (N + 1) ≤ e := by
    rw [div_le_iff₀ (by norm_cast)] at *; rw [mul_comm]; exact_mod_cast h
  specialize hq N; use N; intro j hj k hk
  specialize hq j hj k hk
  rw [Chapter4_3.dist]; linarith




theorem Real.LIM_of_Cauchy'' {q:ℕ → ℚ} (hq: ∀ M, ∀ n ≥ M, ∀ n' ≥ M, |q n - q n'| ≤ 1 / (M+1)) :
∀ M, |q M - LIM q| ≤ 1 / (M+1):= by
  -- We know that n,m are trapped within 1/(M+1) of each other for n,m ≥ M
  have hqcauchy := Real.LIM_of_Cauchy' hq
  -- So, we know that any q n must be trapped that close to q M
  peel hq with M hq; specialize hq M (by linarith)
  -- Grab cauchy properties
  have hqconst := Sequence.IsCauchy.const (q M)
  have hqsub := Sequence.IsCauchy.sub hqconst hqcauchy
  have hqabs := Sequence.IsCauchy.abs hqsub
  -- For q M to be close to LIM q, that means the limit of their difference must be small
  -- More precisely, the limit of the distance between q n and q M must be small
  rw [ratCast_def, LIM_sub hqconst hqcauchy, LIM_abs hqsub];
  -- We know the limit is small if every term is small
  apply LIM_of_le' hqabs
  -- But our premise already gives us that q n and q M are close together
  use M; peel hq with n hn h
  rw [show (1/(M+1):Real) = ((1/(M+1):ℚ):Real) by simp]
  rw [Rat.cast_le (K := Real)]
  convert h


theorem Real.LIM_of_Cauchy {q:ℕ → ℚ} (hq: ∀ M, ∀ n ≥ M, ∀ n' ≥ M, |q n - q n'| ≤ 1 / (M+1)) :
    (q:Sequence).IsCauchy ∧ ∀ M, |q M - LIM q| ≤ 1 / (M+1) := ⟨ Real.LIM_of_Cauchy' hq, Real.LIM_of_Cauchy'' hq ⟩




/--
The sequence m₁, m₂, … is well-defined.
This proof uses a different indexing convention than the text
-/
lemma Real.LUB_claim1 (n : ℕ) {E: Set Real} (hE: Set.Nonempty E) (hbound: BddAbove E)
:  ∃! m:ℤ,
      (((m:ℚ) / (n+1):ℚ):Real) ∈ upperBounds E
      ∧ ¬ (((m:ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∈ upperBounds E := by
  set x₀ := Set.Nonempty.some hE -- Grab an element of E
  observe hx₀ : x₀ ∈ E
  set ε := ((1/(n+1):ℚ):Real) -- All our terms include a 1/(n+1) factor
  have hpos : ε.IsPos := by simp [isPos_iff, ε]; positivity
  apply existsUnique_of_exists_of_unique
  · -- Take even increments of 1/(n+1), and find the crossing point to upper bounds
    rw [bddAbove_def] at hbound; obtain ⟨ M, hbound ⟩ := hbound
    choose K _ hK using le_mul hpos M -- K * ε is an upper bound increment
    choose L' _ hL using le_mul hpos (-x₀)
    set L := -(L':ℤ)
    have claim1_1 : L * ε < x₀ := by simp [L]; linarith
    have claim1_2 : L * ε ∉ upperBounds E := by -- L * ε is NOT an upper bound increment
      rw [Real.upperBound_def]; push_neg; use x₀;
    have claim1_3 : (K:Real) > (L:Real) := by -- Thus, L < K
      contrapose! claim1_2
      replace claim1_2 := mul_le_mul_left claim1_2 hpos
      simp_rw [mul_comm] at claim1_2
      replace claim1_2 : M ≤ L * ε := by order
      grind [upperBound_upper]
    -- We previously found a crossing point m between L and K
    have claim1_4 : ∃ m:ℤ, L < m ∧ m ≤ K ∧ m*ε ∈ upperBounds E ∧ (m-1)*ε ∉ upperBounds E := by
      convert Real.upperBound_between (n := n) _ _ claim1_2
      · qify; rwa [←gt_iff_lt, gt_of_coe]
      · simp [ε] at *; apply upperBound_upper _ hbound; order
    choose m _ _ hm hm' using claim1_4; use m -- Use crossing point
    have : (m/(n+1):ℚ) = m*ε := by simp [ε]; field_simp -- Convert formatting
    exact ⟨ by convert hm, by convert hm'; simp [this, sub_mul, ε] ⟩
  · -- We previously proved uniqueness of such m
    grind [upperBound_discrete_unique]

/-
  Each term is an upper bound, but subtracting 1/(n+1) makes it not an upper bound.
  We claim that this means that sequence terms can't get more than 1/(N+1) apart
-/
lemma Real.LUB_claim2 {E : Set Real} (N:ℕ) {a b: ℕ → ℚ}
  (hb : ∀ n, b n = 1 / (↑n + 1))
  (hm1 : ∀ (n : ℕ), ↑(a n) ∈ upperBounds E)
  (hm2 : ∀ (n : ℕ), ↑((a - b) n) ∉ upperBounds E)
: ∀ n ≥ N, ∀ n' ≥ N, |a n - a n'| ≤ 1 / (N+1) := by
    -- The basic concept: because a n and a n' both straddle the upper bound by a
    -- tiny amount, they can't be too far apart
    intro n hn n' hn'
    -- In particular, adding/subtracting a small amount to either will cause them
    -- to cross over each other
    -- Each of these operations show that one can't be too big or too small
    -- Otherwise, the gap would be too large to be crossed so easily
    rw [abs_le]
    -- We break this into two cases, accounting for which of a n or a n' is larger
    split_ands
    · ---- a n can't be too much smaller: if we add only a small amount, it beats a n'
      specialize hm1 n; specialize hm2 n'; specialize hb n'
      -- x is an upper bound and y isn't →  x > y
      have bound1 : ((a-b) n') < a n := by rw [lt_of_coe]; contrapose! hm2; grind [upperBound_upper]
      -- Since we're beyond 1/(N+1), we can use that as a simplifying bound
      have bound3 : 1/((n':ℚ)+1) ≤ 1/(N+1) := by gcongr
      rw [Pi.sub_apply] at bound1; linarith
    · ---- a n can't be too much larger: if we subtract a small amount, it loses to a n'
      specialize hm1 n'; specialize hm2 n
      have bound1 : ((a-b) n) < a n' := by rw [lt_of_coe]; contrapose! hm2; grind [upperBound_upper]
      have bound2 : ((a-b) n) = a n - 1 / (n+1) := by simp [hb n]
      have bound3 : 1/((n+1):ℚ) ≤ 1/(N+1) := by gcongr
      linarith



/-- Theorem 5.5.9 (Existence of least upper bound)-/
theorem Real.LUB_exist {E: Set Real} (hE: Set.Nonempty E) (hbound: BddAbove E): ∃ S, IsLUB E S := by
  -- Our goal is to fence in the sup above and below by multiples of ε
  -- Which can then we tightened to a single value by increasing n
  set x₀ := hE.some
  have hx₀ : x₀ ∈ E := hE.some_mem
  -- We retrieve the crossing-over discrete value m for each n
  set m : ℕ → ℤ := fun n ↦ (LUB_claim1 n hE hbound).exists.choose
  -- We divide by n+1 to get desired upper bound approximations
  set a : ℕ → ℚ := fun n ↦ (m n:ℚ) / (n+1)
  set b : ℕ → ℚ := fun n ↦ 1 / (n+1)
  have hb : (b:Sequence).IsCauchy := .harmonic'
  -- Properties of a n (and, consequently, m n)
  have claim1 (n: ℕ) := LUB_claim1 n hE hbound
  have hm1 (n:ℕ) := (claim1 n).exists.choose_spec.1
  have hm2 (n:ℕ) : ¬((a - b) n: Real) ∈ upperBounds E := (claim1 n).exists.choose_spec.2
  -- Our discretized approximation of the upper bound gets arbitrarily close together
  have claim2 (N:ℕ) := LUB_claim2 N (by aesop) hm1 hm2 -- a n and a n' close by 1/(N+1)
  have claim3 : (a:Sequence).IsCauchy := (LIM_of_Cauchy claim2).1
  -- LIM a = LIM (a-b) is our candidate for the least upper bound
  -- a and a-b fence in our sup from above and below, arbitrarily closely
  set S := LIM a; use S -- a will allow us to prove it's an upper bound
  -- We know that it's an arbitrarily close fence, because they converge to the same value
  have claim4 : S = LIM (a - b) := by -- (a-b) will allow us to prove it's the LEAST upper bound
    have : LIM b = 0 := LIM.harmonic
    simp [←LIM_sub claim3 hb, S, this]
  rw [isLUB_def, upperBound_def]
  split_ands
  · -- All terms of (a) are upper bounds, so LIM a is an upper bound
    intros; apply LIM_of_ge claim3; grind [upperBound_def]
  · -- All terms of (a-b) are ≤ any upper bound, so LIM (a-b) is ≤ any upper bound
    intro y hy
    have claim5 (n:ℕ) : y ≥ (a-b) n := by contrapose! hm2; use n; apply upperBound_upper _ hy; order
    rw [claim4]; apply LIM_of_le _ claim5; solve_by_elim [Sequence.IsCauchy.sub]

/-- A bare-bones extended real class to define supremum. -/
inductive ExtendedReal where
| neg_infty : ExtendedReal
| real (x:Real) : ExtendedReal
| infty : ExtendedReal

/-- Mathlib prefers ⊤ to denote the +∞ element. -/
instance ExtendedReal.inst_Top : Top ExtendedReal where
  top := infty

/-- Mathlib prefers ⊥ to denote the -∞ element.-/
instance ExtendedReal.inst_Bot: Bot ExtendedReal where
  bot := infty

instance ExtendedReal.coe_real : Coe Real ExtendedReal where
  coe x := ExtendedReal.real x

instance ExtendedReal.real_coe : Coe ExtendedReal Real where
  coe X := match X with
  | neg_infty => 0
  | real x => x
  | infty => 0

abbrev ExtendedReal.IsFinite (X : ExtendedReal) : Prop := match X with
  | neg_infty => False
  | real _ => True
  | infty => False

theorem ExtendedReal.finite_eq_coe {X: ExtendedReal} (hX: X.IsFinite) :
    X = ((X:Real):ExtendedReal) := by
  cases X <;> try simp [IsFinite] at hX
  simp

open Classical in
/-- Definition 5.5.10 (Supremum)-/
noncomputable abbrev ExtendedReal.sup (E: Set Real) : ExtendedReal :=
  if h1:E.Nonempty then (if h2:BddAbove E then ((Real.LUB_exist h1 h2).choose:Real) else ⊤) else ⊥

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_empty : sup ∅ = ⊥ := by simp [sup]

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_unbounded {E: Set Real} (hb: ¬ BddAbove E) : sup E = ⊤ := by
  have hE : E.Nonempty := by contrapose! hb; simp [hb]
  simp [sup, hE, hb]

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    IsLUB E (sup E) := by
  simp [sup, hnon, hb]; exact (Real.LUB_exist hnon hb).choose_spec

theorem ExtendedReal.sup_of_bounded_finite {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    (sup E).IsFinite := by simp [sup, hnon, hb, IsFinite]


/-- Proposition 5.5.12 -/
theorem Real.exist_sqrt_two : ∃ x:Real, x^2 = 2 := by
  -- This proof is written to follow the structure of the original text.
  set E := { y:Real | y ≥ 0 ∧ y^2 < 2 }
  -- Bound sup E : 1 ≤ sup E ≤ 2
  have claim1: 2 ∈ upperBounds E := by
    rw [upperBound_def]
    intro y hy; simp [E] at hy; contrapose! hy
    intro hpos
    calc
      _ ≤ 2 * 2 := by norm_num
      _ ≤ y * y := by gcongr
      _ = y^2 := by ring
  have claim1' : BddAbove E := by rw [bddAbove_def]; use 2
  have claim2: 1 ∈ E := by simp [E]
  observe claim2': E.Nonempty
  set x := ((ExtendedReal.sup E):Real) -- Important: sup E is a real number
  have claim3 : IsLUB E x := by grind [ExtendedReal.sup_of_bounded]
  have claim4 : x ≥ 1 := by grind [isLUB_def, upperBound_def]
  have claim5 : x ≤ 2 := by grind [isLUB_def]
  -- We also know that it's positive
  have claim6 : x.IsPos := by rw [isPos_iff]; linarith
  -- We'll show that sup E ^ 2 = 2 by ruling out <2 and >2
  -- If sup E^2 was away from 2, then there's a gap between 2 and sup E^2
  -- Thus, there's an amount that we could nudge it closer to 2, without crossing over
  -- But then, this close value will either violate the upper bound or the least-ness
  use x; obtain h | h | h := trichotomous' (x^2) 2
  · -- First case: x^2 > 2
    exfalso; rw [isLUB_def] at claim3; have claim3 := claim3.2
    contrapose! claim3
    -- Our goal is to find ε that gives (x-ε)^2 > 2: shows x^2 isn't the LEAST upper bound
    suffices ∃ e, e > 0 ∧ e < 1 ∧ (x - e)^2 > 2 by
      choose e he1 he2 he3 using this; use (x-e); simp [he1]
      have why (y:Real) (hy: y ∈ E) : x - e ≥ y := by
        simp [E] at hy
        have : (x-e)^2 ≥ y^2 := by linarith
        contrapose! this; -- (x-e)^2 < y^2 → x-e < y if both nonnegative
        apply pow_lt_pow_left₀ this (by linarith) (by norm_num)
      rwa [upperBound_def]

    -- Expand (x-e)^2
    conv => arg 1; intro e; rw [show (x - e)^2 = x^2 - 2*x*e + e^2 by ring]
    -- Since x^2 > 2, we know that we can subtract a small amount to get above 2
    -- We just want x^2 - C*e: so, we'll lower-bound (x - e)^2 to get a term like this
    -- Specifically: lower-bound e^2 → 0, and lower-bound 2*x*e → 2*2*e
    suffices ∃ e, e > 0 ∧ e < 1 ∧ x^2 - 4*e + 0 > 2 by
      choose e he1 he2 he3 using this; refine ⟨ e, he1, he2, ?_ ⟩;
      apply lt_of_lt_of_le he3;
      gcongr; linarith; nlinarith
    -- x^2 - 4*e > 2 → e < (x^2-2)/4 (thus, (x^2-2)/8 is sufficient)
    -- e < 1 (thus, 1/2 is sufficient)
    -- These are both upper bounds, so we take the minimum of both
    set e := min (1/2) ((x^2-2)/8)
    refine ⟨e, by simp [e, h], by simp [e]; left; norm_num, ?_⟩
    observe he: e ≤ (x^2-2)/8
    linarith

  · -- This is a more-or-less equivalent argument: preserving Tao's original form
    have claim7 : ∃ ε, 0 < ε ∧ ε < 1 ∧ x^2 + 5*ε < 2 := by
      set ε := min (1/2) ((2-x^2)/10)
      have hx : 2 - x^2 > 0 := by linarith
      have hε: 0 < ε := by positivity
      have hε1: ε ≤ 1/2 := min_le_left _ _
      have hε2: ε ≤ (2 - x^2)/10 := min_le_right _ _
      refine ⟨ ε, hε, ?_, ?_ ⟩ <;> linarith
    choose ε hε1 hε2 hε3 using claim7
    have claim8 : (x+ε)^2 < 2 := calc
      _ = x^2 + (2*x)*ε + ε*ε := by ring
      _ ≤ x^2 + (2*2)*ε + 1*ε := by gcongr
      _ = x^2 + 5*ε := by ring
      _ < 2 := hε3
    have claim9 : x + ε ∈ E := by simp [E, claim8]; linarith
    have claim10 : x + ε ≤ x := by grind [isLUB_def, upperBound_def]
    linarith
  · -- Third case: the correct case
    assumption

/-- Remark 5.5.13 -/
theorem Real.exist_irrational : ∃ x:Real, ¬ ∃ q:ℚ, x = (q:Real) := by
  choose sqrt_two hsqrt using Real.exist_sqrt_two
  use sqrt_two --√ 2 is our irrational candidate
  have := Chapter4_4.Rat.not_exist_sqrt_two -- We already showed no (q:ℚ)^2=2
  intro h; choose q hq using h
  rw [hq] at hsqrt
  apply this; use q;
  exact_mod_cast hsqrt

/-- Helper lemma for Exercise 5.5.1. -/
theorem Real.mem_neg (E: Set Real) (x:Real) : x ∈ -E ↔ -x ∈ E := Set.mem_neg

theorem Real.mem_lowerBounds_neg (E: Set Real) (x:Real) :
    x ∈ lowerBounds (-E) ↔ -x ∈ upperBounds E := by
  rw [lowerBound_def, upperBound_def];
  constructor <;>
    (intro h z hz; specialize h (-z);
     simp at *; specialize h hz; linarith)

/-- Exercise 5.5.1-/
theorem Real.inf_neg {E: Set Real} {M:Real} (h: IsLUB E M) : IsGLB (-E) (-M) := by
  rw [isGLB_def, lowerBound_def]; rw [isLUB_def, upperBound_def] at h
  have ⟨h1,h2⟩ := h
  split_ands
  · intro x hx; rw [Real.mem_neg] at hx; specialize h1 (-x) hx; linarith
  · intro N hN; specialize h2 (-N); rw [mem_lowerBounds_neg] at hN
    specialize h2 hN; linarith

-- To get the GLB of E, we just get the LUB of -E
theorem Real.GLB_exist {E: Set Real} (hE: Set.Nonempty E) (hbound: BddBelow E): ∃ S, IsGLB E S := by
  rw [bddBelow_def] at hbound; choose M hM using hbound;
  choose x hx using hE
  have := Real.LUB_exist ( E := -E)
    (by use -x; simp_all)
    (by rw [bddAbove_def]; use -M; rw [← mem_lowerBounds_neg]; simp_all)
  choose S hS using this -- Get the LUB
  use -S; convert inf_neg hS; simp -- Convert to GLB

/-
Create similar machinery to sup for inf
-/

-- Reversed version of sup def, using GLB instead of LUB in the Real case
open Classical in
noncomputable abbrev ExtendedReal.inf (E: Set Real) : ExtendedReal :=
  if h1:E.Nonempty then (if h2:BddBelow E then ((Real.GLB_exist h1 h2).choose:Real) else ⊥) else ⊤

theorem ExtendedReal.inf_of_empty : inf ∅ = ⊤ := by simp [inf]

theorem ExtendedReal.inf_of_unbounded {E: Set Real} (hb: ¬ BddBelow E) : inf E = ⊥ := by
  have hE : E.Nonempty := by contrapose! hb; simp [hb]
  simp [inf, hE, hb]

theorem ExtendedReal.inf_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddBelow E) :
    IsGLB E (inf E) := by simp [hnon, hb, inf]; exact (Real.GLB_exist hnon hb).choose_spec

theorem ExtendedReal.inf_of_bounded_finite {E: Set Real} (hnon: E.Nonempty) (hb: BddBelow E) :
    (inf E).IsFinite := by simp [inf, hnon, hb, IsFinite]

abbrev Real.IsIrrational (x:Real) : Prop := ¬ ∃ q:ℚ, x = (q:Real)

lemma Real.exist_irrational' : ∃ x:Real, Real.IsIrrational x := Real.exist_irrational

lemma Real.irrational_plus_rational {x:Real} (hx: Real.IsIrrational x) (q:ℚ) :
    Real.IsIrrational (x + (q:Real)) := by
  contrapose! hx; push_neg at *; choose p hp using hx
  use p-q; simp; linarith



lemma Real.irrational_times_rational {x:Real} (hx: Real.IsIrrational x) (q:ℚ) (hq: q ≠ 0) :
    Real.IsIrrational (x * (q:Real)) := by
  contrapose! hx; push_neg at *; choose p hp using hx
  use p/q; field_simp [hp]

lemma Real.irrational_div_rational {x:Real} (hx: Real.IsIrrational x) (q:ℚ) (hq: q ≠ 0) :
    Real.IsIrrational (x / (q:Real)) := by
  conv => arg 1; rw [show (x / (q:Real)) = x * ((1/q:ℚ):Real) by field_simp]
  apply Real.irrational_times_rational hx
  simp_all


lemma Real.exists_positive_irrational : ∃ x:Real, x > 0 ∧ Real.IsIrrational x := by
  choose x hx using Real.exist_irrational'
  rcases trichotomous' x 0 with ( hpos | hneg | heq)
  · use x
  · use -x; refine ⟨by linarith, ?_⟩
    rw [show (-x) = x * ((-1:ℚ) : Real) by ring];
    apply irrational_times_rational hx; norm_num
  · contrapose! hx; push_neg; use 0; simp_all

lemma Real.exists_positive_irrational_lt_one : ∃ x:Real, x > 0 ∧ x < 1 ∧ Real.IsIrrational x := by
  choose x hx1 hx2 using Real.exists_positive_irrational
  choose n hn using exists_nat_gt x
  use x / (n+1); have: x < (n+1) := by linarith
  refine ⟨ by field_simp; positivity,
    by rw [div_lt_one]; exact this; positivity, ?_⟩
  rw [show ((n+1):Real) = (((n+1):ℚ):Real) by field_simp]
  apply Real.irrational_div_rational hx2; linarith

/-- Exercise 5.5.5 -/
theorem Real.irrat_between {x y:Real} (hxy: x < y) :
    ∃ z, x < z ∧ z < y ∧ ¬ ∃ q:ℚ, z = (q:Real) := by
    -- x < a < b < y
  choose a ha using rat_between hxy
  choose b hb using rat_between ha.2
  choose z hz1 hz2 hz3 using Real.exists_positive_irrational_lt_one
  use z * (b - a) + a
  split_ands
  · apply lt_trans (y := a) (by linarith)
    simp; apply mul_pos hz1 (by linarith)
  · refine lt_trans (y := b) (by nlinarith) hb.2
  · apply Real.irrational_plus_rational
    rw [show (b - a) = ( ((b - a):ℚ) : Real) by field_simp]
    apply Real.irrational_times_rational hz3
    simp at hb; linarith



/- Use the notion of supremum in this section to define a Mathlib `sSup` operation -/
noncomputable instance Real.inst_SupSet : SupSet Real where
  sSup E := ((ExtendedReal.sup E):Real)

/-- Use the `sSup` operation to build a conditionally complete lattice structure on `Real`-/
noncomputable instance Real.inst_conditionallyCompleteLattice :
    ConditionallyCompleteLattice Real :=
  conditionallyCompleteLatticeOfLatticeOfsSup Real
  (by intros; solve_by_elim [ExtendedReal.sup_of_bounded])

theorem ExtendedReal.sSup_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    IsLUB E (sSup E) := sup_of_bounded hnon hb

-- Note to self: remember that congrArg exists

end Chapter5

namespace Chapter5

/-- Definition 5.6.1 (Exponentiating a real by a natural number). Here we use the
    Mathlib definition coming from `Monoid`. -/

lemma Real.pow_zero (x: Real) : x ^ 0 = 1 := rfl

lemma Real.pow_succ (x: Real) (n:ℕ) : x ^ (n+1) = (x ^ n) * x := rfl

/-
Basically says
pow_real_eq_real_pow (casting the base to Real before/after is the same)-/
lemma Real.pow_of_coe (q: ℚ) (n:ℕ) : (q:Real) ^ n = (q ^ n:ℚ) := by induction' n with n hn <;> simp

/- The claims below can be handled easily by existing Mathlib API (as `Real` already is known
to be a `Field`), but the spirit of the exercises is to adapt the proofs of
Proposition 4.3.10 that you previously established. -/

/-
Counterpoint: I just retroactively rewrote these
theorems for chapter 4 to work for any type that's
got the right machinery (whether that's `Monoid` or
`CommMonoid` or whatever).
This is in the spirit of the problem (re-using the
proof for different objects with the same structure)
without just using the built-in tools.

Since it was just gonna be copy/pasted anyway, I think
it's more interesting for me to get more used to
dealing with the types themselves.

-/

/-
Message to my past self: this was a lot more work than you expected lol

Especially since instead of just using `Field` for everything, I actually tried to
make it match the typeclasses that Mathlib uses. So 1. I had to get creative with proofs
2. it was sometimes hard to figure out the correct typeclass to use.
-/

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.pow_add (x:Real) (m n:ℕ) : x^n * x^m = x^(n+m) := Chapter4_3.pow_add' x m n


/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.pow_mul (x:Real) (m n:ℕ) : (x^n)^m = x^(n*m) := Chapter4_3.pow_mul' x m n

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.mul_pow (x y:Real) (n:ℕ) : (x*y)^n = x^n * y^n := Chapter4_3.mul_pow' x y n

/-- Analogue of Proposition 4.3.10(b) -/
theorem Real.pow_eq_zero (x:Real) (n:ℕ) (hn : 0 < n) : x^n = 0 ↔ x = 0 := Chapter4_3.pow_eq_zero' x n hn

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_nonneg {x:Real} (n:ℕ) (hx: x ≥ 0) : x^n ≥ 0 := Chapter4_3.pow_nonneg' n hx

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_pos {x:Real} (n:ℕ) (hx: x > 0) : x^n > 0 := Chapter4_3.pow_pos' hx n

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_ge_pow (x y:Real) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 0) : x^n ≥ y^n := Chapter4_3.pow_ge_pow' x y n hxy hy

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_gt_pow (x y:Real) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) : x^n > y^n := Chapter4_3.pow_gt_pow' x y n hxy hy hn

theorem Real.pow_ge_pow_converse (x y:Real) (n:ℕ) (hxy: x^n ≥ y^n) (hx: x ≥ 0) (hn: n > 0) : x ≥ y := by
  contrapose! hxy; apply pow_gt_pow y x n hxy hx hn

theorem Real.pow_gt_pow_converse (x y:Real) (n:ℕ) (hxy: x^n > y^n) (hx: x ≥ 0) (hn: n > 0) : x > y := by
  contrapose! hxy; apply pow_ge_pow y x n hxy hx

/-- Analogue of Proposition 4.3.10(d) -/
theorem Real.pow_abs (x:Real) (n:ℕ) : |x|^n = |x^n| := Chapter4_3.pow_abs' x n

/-- Definition 5.6.2 (Exponentiating a real by an integer). Here we use the Mathlib definition coming from `DivInvMonoid`. -/
lemma Real.pow_eq_pow (x: Real) (n:ℕ): x ^ (n:ℤ) = x ^ n := by rfl

@[simp]
lemma Real.zpow_zero (x: Real) : x ^ (0:ℤ) = 1 := by rfl

lemma Real.zpow_neg {x:Real} (n:ℕ) : x^(-n:ℤ) = 1 / (x^n) := by simp

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.zpow_add (x:Real) (n m:ℤ) (hx: x ≠ 0): x^n * x^m = x^(n+m) := Chapter4_3.zpow_add' x n m hx

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.zpow_mul (x:Real) (n m:ℤ) : (x^n)^m = x^(n*m) := Chapter4_3.zpow_mul' x n m

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.mul_zpow (x y:Real) (n:ℤ) : (x*y)^n = x^n * y^n := Chapter4_3.mul_zpow' x y n

/-- Analogue of Proposition 4.3.12(b) -/
theorem Real.zpow_pos {x:Real} (n:ℤ) (hx: x > 0) : x^n > 0 := Chapter4_3.zpow_pos' n hx

/-- Analogue of Proposition 4.3.12(b) -/
theorem Real.zpow_ge_zpow {x y:Real} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n > 0): x^n ≥ y^n := Chapter4_3.zpow_ge_zpow' hxy hy hn

theorem Real.zpow_ge_zpow_ofneg {x y:Real} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n < 0) : x^n ≤ y^n := Chapter4_3.zpow_ge_zpow_ofneg' hxy hy hn

/-- Analogue of Proposition 4.3.12(c) -/
theorem Real.zpow_inj {x y:Real} {n:ℤ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := Chapter4_3.zpow_inj' hx hy hn hxy

/-- Analogue of Proposition 4.3.12(d) -/
theorem Real.zpow_abs (x:Real) (n:ℤ) : |x|^n = |x^n| := Chapter4_3.zpow_abs' x n

-- It was so satisfying to finally fill in all of these theorems after revising chapter 4...

/-- Definition 5.6.2.  We permit ``junk values'' when `x` is negative or `n` vanishes. -/
noncomputable abbrev Real.rootset (x:Real) (n:ℕ) : Set Real := { y:Real | y ≥ 0 ∧ y^n ≤ x }

noncomputable abbrev Real.root (x:Real) (n:ℕ) : Real := sSup (rootset x n)

noncomputable abbrev Real.sqrt (x:Real) := x.root 2

/-- Lemma 5.6.5 (Existence of n^th roots) -/
theorem Real.rootset_nonempty {x:Real} (hx: x ≥ 0) (n:ℕ) (hn: n ≥ 1) : (rootset x n).Nonempty := by
  use 0; simp; rw [← ge_iff_le]; convert hx; simp; linarith


theorem le_self_pow₀' {G : Type*} [MonoidWithZero G] [Preorder G] [ZeroLEOneClass G]
  [PosMulMono G] {a : G} {n : ℕ} (ha : 1 ≤ a) (hn : n ≠ 0) : a ≤ a ^ n := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  clear hn -- Unnecessary premise
  induction' n with n ih
  · simp
  · rw [pow_succ']
    nth_rw 1 [← mul_one a]
    exact mul_le_mul_of_nonneg_left (le_trans ha ih) (le_trans zero_le_one ha)


theorem Real.rootset_bddAbove {x:Real} (n:ℕ) (hn: n ≥ 1) : BddAbove { y:Real | y ≥ 0 ∧ y^n ≤ x } := by
  -- This proof is written to follow the structure of the original text.
  rw [_root_.bddAbove_def]
  obtain h | h := le_or_gt x 1
  · use 1; intro y hy; simp at hy
    by_contra! hy'
    replace hy' : 1 < y^n := by
      rw [show (1:Real) = 1^n by ring]
      apply Real.pow_gt_pow y 1 n hy' (by linarith) hn
    linarith
  use x; intro y hy; simp at hy
  by_contra! hy'
  replace hy' : x < y^n := by
    apply lt_of_lt_of_le hy'
    apply le_self_pow₀' (by linarith) (by linarith)
  linarith



lemma Real.root_LUB_rootset {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) :
IsLUB (rootset x n) (x.root n) :=
  ExtendedReal.sSup_of_bounded (Real.rootset_nonempty hx n hn) (Real.rootset_bddAbove n hn)



lemma Real.linear_upper_bound_of_pow (y: Real) (n : ℕ) (hy : y ≥ 0) (hn : n ≠ 0):
∃ C > 0, ∀(ε : Real), ε ≥ 0 → ε ≤ 1 → (y+ε)^n ≤ y^n + C * ε := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simp at *
  induction' k with k ih
  · use 1; simp
  choose C hC1 hC2 using ih
  use C + C*y + (y^(k+1))
  refine ⟨by nlinarith [Real.pow_nonneg (k+1) hy],?_⟩
  intro e he0 he1; specialize hC2 e he0 he1
  rw [pow_succ'];
  calc
    _ ≤ (y+e) * (y^(k+1) + C * e) := by gcongr
    _ = y* (y^(k+1) + C * e) + e*y^(k+1) + C*(e*e) := by ring_nf
    _ ≤ y* (y^(k+1) + C * e) + e*y^(k+1) + C*e := by gcongr; nlinarith
    _ = _ := by ring_nf;

lemma Real.linear_lower_bound_of_pow (y: Real) (n : ℕ) (hy : y ≥ 0) (hn : n ≠ 0):
∃ C > 0, ∀(ε : Real), ε ≥ 0 → ε ≤ y → (y - ε)^n ≥ y^n - C * ε := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [show k.succ = k + 1 by aesop] at *
  induction' k with k ih
  · use 1; simp
  choose C hC1 hC2 using ih (by linarith)
  use C + C*y + y^(k+1)
  refine ⟨by nlinarith [Real.pow_nonneg (k+1) hy],?_⟩
  intro e he0 hey; specialize hC2 e he0 hey
  rw [pow_succ'];
  calc
    _ ≥ (y - e) * (y^(k+1) - C * e) := by gcongr; linarith
    _ = y* (y^(k+1) - C * e) - e*y^(k+1) + C*(e*e) := by ring_nf
    _ ≥ y* (y^(k+1) - C * e) - e*y^(k+1) + (-C*e) := by gcongr 1; nlinarith
    _ = _ := by ring_nf;

#check Real.pow_ge_pow_converse
#check Real.zpow_inj
/-- Lemma 5.6.6 (ab) / Exercise 5.6.1 -/
theorem Real.eq_root_iff_pow_eq {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) :
y = x.root n ↔ y^n = x := by
  have hlub:= Real.root_LUB_rootset hx hn;
  rw [isLUB_def, upperBound_def] at hlub
  obtain ⟨h1, h2⟩ := hlub
  constructor <;> intro h
  · apply le_antisymm
    · contrapose! h2;
      have hy : y > 0 := by   by_contra hy0; have hy0 : y = 0 := by linarith
                              rw [← pow_eq_zero _ n (by linarith)] at hy0;
                              rw [hy0] at h2; linarith
      rw [← h] at *
      choose C hC1 hC2 using Real.linear_lower_bound_of_pow y n (by linarith) (by linarith)
      let e := min ( (y^n - x) / C) y
      use y - e; have he0 : e > 0 := by aesop
      simp [he0]; rw [upperBound_def, Real.rootset]
      intro r hr; simp at hr;
      apply pow_ge_pow_converse _ _ n ?_ (by simp [e]) hn
      apply le_trans hr.2;
      apply le_trans ?_ (hC2 e he0.le (min_le_right _ _))
      have := min_le_left ((y ^ n - x) / C) y
      simp [e]
      calc
        _ = y^n - C * ((y^n - x) / C) := by field_simp
        _ ≤ _ := by gcongr
    · contrapose! h1; rw [← h] at *
      choose C hC1 hC2 using Real.linear_upper_bound_of_pow y n (by linarith) (by linarith)
      let e := min ( (x - y^n) / C) 1
      use y + e; have he0 : e > 0 := by aesop
      simp [rootset, he0]
      refine ⟨ by linarith, ?_⟩
      apply le_trans (hC2 e he0.le (min_le_right _ _))
      have he2 : e ≤ (x - y ^ n) / C := min_le_left _ _
      calc
        _ ≤ y^n + C * ((x - y^n) / C) := by gcongr
        _ = x := by field_simp
  subst x
  apply le_antisymm
  · apply h1; simp [Real.rootset, hy]
  · apply h2; simp [upperBound_def, Real.rootset]; intro r hr1 hr2;
    apply pow_ge_pow_converse _ _ n hr2 hy hn

/-- Lemma 5.6.6 (c) / Exercise 5.6.1 -/
theorem Real.root_nonneg {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : x.root n ≥ 0 := by
  have hlub:= Real.root_LUB_rootset hx hn; rw [isLUB_def, upperBound_def] at hlub
  obtain ⟨h1, h2⟩ := hlub -- 0 is in rootset, so the LUB is ≥ 0
  apply h1; simp [Real.rootset]; field_simp [hx]



lemma lt_iff_ne_given_le {G: Type*} [LinearOrder G] {a b : G} (h : a ≤ b) : a < b ↔ a ≠ b := by
  constructor <;> intro h'; aesop; apply lt_of_le_of_ne h h';

/-- Lemma 5.6.6 (c) / Exercise 5.6.1 -/
theorem Real.root_pos {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : x.root n > 0 ↔ x > 0 := by
  have := Real.root_nonneg hx hn
  simp; rw [lt_iff_ne_given_le this, lt_iff_ne_given_le hx]
  nth_rw 2 [show (0:Real) = 0^n by field_simp];
  rw [not_iff_not]; apply eq_root_iff_pow_eq; all_goals linarith


theorem Real.pow_of_root {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  (x.root n)^n = x := by
  rw [← Real.eq_root_iff_pow_eq]; any_goals apply root_nonneg;
  all_goals assumption;

theorem Real.root_of_pow {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  (x^n).root n = x := by
  symm; rw [Real.eq_root_iff_pow_eq]; apply pow_nonneg
  all_goals assumption;

/-- Lemma 5.6.6 (d) / Exercise 5.6.1 -/
theorem Real.root_mono {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) : x > y ↔ x.root n > y.root n := by
  rw [← not_iff_not]; simp
  nth_rw 1 [← pow_of_root hx hn, ← pow_of_root hy hn]
  constructor <;> intro h <;> [apply Real.pow_ge_pow_converse; apply Real.pow_ge_pow]
  (any_goals apply h); (any_goals apply root_nonneg); (all_goals linarith)


theorem one_le_pow₀'{G : Type*} [MonoidWithZero G] [Preorder G] {a : G} [ZeroLEOneClass G] [PosMulMono G] (ha : 1 ≤ a) {n : ℕ} :
1 ≤ a ^ n := by
  by_cases hn : n = 0
  · simp_all
  apply le_trans ha (le_self_pow₀ ha hn)

lemma pow_le_pow_right' {G : Type*} [MonoidWithZero G] [Preorder G]
[ZeroLEOneClass G] [PosMulMono G] {a : G} {m n : ℕ}
(ha : 1 ≤ a) (hmn : m ≤ n) : a ^ m ≤ a ^ n := by
  set k := n - m; rw [show n = m + k by omega]
  rw [← mul_one (a^m), ← Chapter4_3.pow_add']
  apply mul_le_mul_of_nonneg_left
  apply one_le_pow₀' ha
  apply pow_nonneg (by apply le_trans zero_le_one ha)


theorem one_lt_pow₀'{G : Type*} [MonoidWithZero G] [Preorder G] {a : G} [ZeroLEOneClass G] [PosMulStrictMono G] (ha : 1 < a) {n : ℕ} (hn : n ≠ 0) :
1 < a ^ n := by
  obtain ⟨k,rfl ⟩ := Nat.exists_eq_succ_of_ne_zero hn
  induction' k with k ih
  · simp [ha]
  simp at *; rw [pow_succ];
  apply lt_trans ih; nth_rw 1 [← mul_one (a ^ (k + 1))]
  apply mul_lt_mul_of_pos_left ha (lt_of_le_of_lt zero_le_one ih)


lemma pow_lt_pow_right' {G : Type*} [MonoidWithZero G] [Preorder G]
[PosMulStrictMono G] [ZeroLEOneClass G]  {a : G} {m n : ℕ}
(h : 1 < a) (hmn : m < n) : a ^ m < a ^ n := by
  by_cases hm : m = 0
  · subst m; simp; apply one_lt_pow₀' h
    linarith
  set k := n - m; rw [show n = m + k by omega]
  rw [← mul_one (a^m), ← Chapter4_3.pow_add']
  apply mul_lt_mul_of_pos_left
  apply one_lt_pow₀' h
  unfold k; exact Nat.sub_ne_zero_iff_lt.mpr hmn
  apply lt_of_le_of_lt (zero_le_one) (one_lt_pow₀' h hm)

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_mono_of_gt_one {x : Real} (hx: x > 1) {k l: ℕ} (hkl: k > l) (hl: l ≥ 1) : x.root k < x.root l := by
  apply pow_gt_pow_converse _ _ l ?_ (by apply root_nonneg; all_goals linarith)
    (by linarith)
  rw [pow_of_root (by linarith) hl]
  nth_rw 1 [← pow_of_root (n := k) (x := x) (by linarith) (by linarith)]
  apply pow_lt_pow_right' ?_ hkl
  apply pow_gt_pow_converse _ _ k ?_ (by apply root_nonneg; all_goals linarith)
    (by linarith)
  simp; rw [pow_of_root (by linarith) (by linarith)]
  exact hx



/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_of_one {k: ℕ} (hk: k ≥ 1): (1:Real).root k = 1 := by
  symm; rw [eq_root_iff_pow_eq]; all_goals simp [hk]

theorem Real.root_gt_one {x : Real} (hx: x > 1) {n: ℕ} (hn: n ≥ 1) : x.root n > 1 := by
  rw [← root_of_one (k:= n), ← root_mono]; all_goals linarith

theorem Real.root_ge_one {x : Real} (hx: x ≥ 1) {n: ℕ} (hn: n ≥ 1) : x.root n ≥ 1 := by
  by_cases h : x = 1
  · subst x; rw [root_of_one (k:= n)]; exact hn
  · have h' : x > 1 := by order
    apply le_of_lt; apply Real.root_gt_one h' hn

theorem Real.root_of_zero {k: ℕ} (hk: k ≥ 1) : (0:Real).root k = 0 := by
  symm; rw [eq_root_iff_pow_eq]; all_goals simp [hk];
  linarith

/-- Lemma 5.6.6 (f) / Exercise 5.6.1 -/
theorem Real.root_mul {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) : (x*y).root n = (x.root n) * (y.root n) := by
  symm; rw [eq_root_iff_pow_eq, mul_pow, pow_of_root, pow_of_root]
  any_goals assumption;
  positivity
  apply mul_nonneg; all_goals apply root_nonneg
  any_goals assumption

theorem Real.root_inv {x:Real} (hx: x > 0) {n:ℕ} (hn: n ≥ 1) : (x⁻¹).root n = (x.root n)⁻¹ := by
  have := (Real.root_pos hx.le hn).mpr hx
  field_simp [this]
  rw [← root_mul]; field_simp [hx]
  apply root_of_one
  any_goals positivity
  any_goals exact hn

-- Moved this one down so I could take the inverse and use the other method
-- Because I don't wanna redo the other method slightly more complicated, boring
/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_mono_of_lt_one {x : Real} (hx0: 0 < x) (hx: x < 1) {k l: ℕ} (hkl: k > l) (hl: l ≥ 1) : x.root k > x.root l := by
  have hkp := (Real.root_pos hx0.le hl).mpr hx0
  have hlp := (Real.root_pos (n:= k) hx0.le (by linarith)).mpr hx0
  simp; rw [← inv_lt_inv₀ hlp hkp, ← root_inv hx0 hl, ← root_inv (n:=k) hx0 (by linarith)]
  rw [← one_lt_inv₀ hx0] at hx
  apply Real.root_mono_of_gt_one (x := x⁻¹) hx hkl hl


/-- Lemma 5.6.6 (g) / Exercise 5.6.1 -/
theorem Real.root_root {x:Real} (hx: x ≥ 0) {n m:ℕ} (hn: n ≥ 1) (hm: m ≥ 1): (x.root n).root m = x.root (n*m) := by
  have : x.root n ≥ 0 := by apply root_nonneg hx hn;
  rw [eq_root_iff_pow_eq]; rw [mul_comm, ← pow_mul, pow_of_root, pow_of_root]
  any_goals assumption;
  apply root_nonneg this; all_goals nlinarith

theorem Real.root_one {x:Real} (hx: x > 0): x.root 1 = x := by
  symm; rw [eq_root_iff_pow_eq]; all_goals linarith

/-
This is basically the same as pow_inj from last chapter
But now we have a funny way to prove it
-/
theorem Real.pow_cancel {y z:Real} (hy: y > 0) (hz: z > 0) {n:ℕ} (hn: n ≥ 1)
  (h: y^n = z^n) : y = z := by
  rw [← eq_root_iff_pow_eq] at h
  rw [h]; apply root_of_pow; any_goals apply pow_nonneg
  all_goals linarith

example : ¬(∀ (y:Real) (z:Real) (n:ℕ) (_: n ≥ 1) (_: y^n = z^n), y = z) := by
  simp; refine ⟨ (-3), 3, 2, ?_, ?_, ?_ ⟩ <;> norm_num

/-- Definition 5.6.7 -/
noncomputable abbrev Real.ratPow (x:Real) (q:ℚ) : Real := (x.root q.den)^(q.num)

noncomputable instance Real.instRatPow : Pow Real ℚ where
  pow x q := x.ratPow q

theorem Rat.eq_quot (q:ℚ) : ∃ a:ℤ, ∃ b:ℕ, b > 0 ∧ q = a / b := by
  use q.num, q.den; have := q.den_nz
  refine ⟨ by omega, (Rat.num_div_den q).symm ⟩

lemma Real.pow_root_cancel {x : Real} {a: ℤ  } {b c: ℕ } (hb: b > 0) (hc: c > 0) (hx: x > 0) :
( x.root b ) ^ a = (x.root (b * c))^(a * c) := by
  rw [← root_root, mul_comm, ← zpow_mul, Chapter4_3.pow_eq_zpow, pow_of_root]
  apply root_nonneg; any_goals linarith

lemma Real.pow_root_cancel' {x : Real} {a: ℤ  } {b c: ℕ } (hb: b > 0) (hc: c > 0) (hx: x > 0) :
( x.root b ) ^ a = (x.root (c * b))^(c * a) := by
  rw [mul_comm c b, mul_comm (c:ℤ) a]
  apply Real.pow_root_cancel hb hc hx

/-- Lemma 5.6.8 -/
theorem Real.pow_root_eq_pow_root {a a':ℤ} {b b':ℕ} (hb: b > 0) (hb' : b' > 0)
  (hq : (a/b:ℚ) = (a'/b':ℚ)) {x:Real} (hx: x > 0) :
    (x.root b')^(a') = (x.root b)^(a) := by
  wlog ha: a > 0 generalizing a b a' b'
  · simp at ha
    obtain ha | ha := le_iff_lt_or_eq.mp ha
    · -- Negative exp can turn into positive by inverting both sides
      replace hq : ((-a:ℤ)/b:ℚ) = ((-a':ℤ)/b':ℚ) := by -- Cast to ℤ, turn to neg
        push_cast at *; ring_nf at *; simp [hq]
      specialize this hb hb' hq (by linarith)
      simpa [zpow_neg] using this
    have : a' = 0 := by -- If a' = 0, then a = 0
      subst a; field_simp [hb'] at hq; norm_cast at hq; rw [hq]
    simp_all -- This case is simple: both sides are 1
  have : a' > 0 := by
    have : a * b' > 0 := by positivity
    field_simp [hb'] at hq; norm_cast at hq; rw [hq] at this
    nlinarith
  field_simp at hq
  -- Modified using pow_root_cancel
  lift a to ℕ using by order
  lift a' to ℕ using by order
  rw [pow_root_cancel (c := a) ]
  norm_cast at hq; rw [mul_comm, hq, mul_comm]; nth_rw 2 [mul_comm]
  rw [← pow_root_cancel (c := a')]
  all_goals linarith


-- Requires a little bit of massaging because we're doing a/b, rather than
-- taking q.num/q.den directly
theorem Real.ratPow_def {x:Real} (hx: x > 0) (a:ℤ) {b:ℕ} (hb: b > 0) : x^(a/b:ℚ) = (x.root b)^a := by
  set q := (a/b:ℚ)
  convert pow_root_eq_pow_root hb _ _ hx
  · have := q.den_nz; omega
  rw [Rat.num_div_den q]

theorem Real.ratPow_eq_root {x:Real} (hx: x > 0) {n:ℕ} (hn: n ≥ 1) : x^(1/n:ℚ) = x.root n := by
  rw [show (1:ℚ) = (1:ℤ) by simp, Real.ratPow_def ]
  simp; all_goals linarith

theorem Real.ratPow_eq_pow {x:Real} (hx: x > 0) (n:ℤ) : x^(n:ℚ) = x^n := by
  rw [show (n:ℚ) = (n/(1:ℕ):ℚ) by simp, Real.ratPow_def, root_one ]
  all_goals tauto


/-- Lemma 5.6.9(a) / Exercise 5.6.2 -/
theorem Real.ratPow_pos {x:Real} (hx: x > 0) (q:ℚ) : x^q > 0 := by
  obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot q
  rw [Real.ratPow_def]
  apply zpow_pos; rw [root_pos]; any_goals linarith


#check Real.pow_root_cancel
/-- Lemma 5.6.9(b) / Exercise 5.6.2 -/
theorem Real.ratPow_add {x:Real} (hx: x > 0) (q r:ℚ) : x^(q+r) = x^q * x^r := by
  obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot q
  obtain ⟨c, d, hd, rfl⟩ := Rat.eq_quot r
  rw [show ((a/b) + (c/d):ℚ) = ((a*d + b*c):ℤ)/(b*d:ℕ) by field_simp; ring]
  repeat rw [Real.ratPow_def]
  rw [pow_root_cancel (b := b) (c := d), pow_root_cancel' (b := d) (c := b)]
  rw [zpow_add]
  apply ne_of_gt; rw [← gt_iff_lt, root_pos]
  any_goals positivity
  suffices b*d > 0 by linarith
  positivity

theorem Real.root_pow_eq_pow_root {x:Real} {a:ℤ} {b:ℕ} (hb: b > 0) (hx : x ≥ 0):
  (x^a).root b = (x.root b)^a := by
  symm; rw [Real.eq_root_iff_pow_eq]
  rw [← Chapter4_3.pow_eq_zpow, zpow_mul, mul_comm, ← zpow_mul, Chapter4_3.pow_eq_zpow]
  rw [pow_of_root]
  any_goals apply zpow_nonneg
  any_goals apply root_nonneg
  any_goals linarith

/-- Lemma 5.6.9(b) / Exercise 5.6.2 -/
theorem Real.ratPow_ratPow {x:Real} (hx: x > 0) (q r:ℚ) : (x^q)^r = x^(q*r) := by
  obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot q
  obtain ⟨c, d, hd, rfl⟩ := Rat.eq_quot r
  rw [Real.ratPow_def, Real.ratPow_def]
  rw [root_pow_eq_pow_root, root_root, zpow_mul]
  rw [← Real.ratPow_def]; congr; field_simp
  any_goals apply root_nonneg
  any_goals linarith
  positivity
  rw [Real.ratPow_def]; apply zpow_pos; rw [root_pos]; any_goals linarith

/-- Lemma 5.6.9(c) / Exercise 5.6.2 -/
theorem Real.ratPow_neg {x:Real} (hx: x > 0) (q:ℚ) : x^(-q) = 1 / x^q := by
  obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot q
  rw [show - (a/b:ℚ) = (-a:ℤ)/b by field_simp, Real.ratPow_def, Real.ratPow_def]
  field_simp; all_goals assumption

theorem Real.ratPow_neg' {x:Real} (hx: x > 0) (q:ℚ) : x^(-q) = (1 / x)^q := by
  obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot q
  rw [ratPow_neg, Real.ratPow_def, Real.ratPow_def]
  simp; rw [Real.root_inv]; simp
  any_goals linarith
  positivity

/-- Lemma 5.6.9(d) / Exercise 5.6.2 -/
theorem Real.ratPow_mono {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (h: q > 0) : x > y ↔ x^q > y^q := by
  obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot q
  field_simp at h
  lift a to ℕ using by omega
  rw [Real.ratPow_def, Real.ratPow_def]
  constructor <;> intro hxy
  · apply pow_gt_pow; rw [← root_mono]; exact hxy
    any_goals apply root_nonneg;
    any_goals linarith
  · rw [root_mono (n := b)]; apply pow_gt_pow_converse _ _ a
    convert hxy
    apply root_nonneg; any_goals linarith
  any_goals assumption

#check Real.root_mono_of_gt_one
/-- Lemma 5.6.9(e) / Exercise 5.6.2 -/
theorem Real.ratPow_mono_of_gt_one {x:Real} (hx: x > 1) {q r:ℚ} : x^q > x^r ↔ q > r := by
  obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot q
  obtain ⟨c, d, hd, rfl⟩ := Rat.eq_quot r
  have : b*d > 0 := by nlinarith
  nth_rw 1 [show (a/b:ℚ) = (a*d: ℤ )/(b*d:ℕ)  by field_simp; ring,
      show (c/d:ℚ) = (b*c: ℤ)/(b*d:ℕ) by field_simp; ring]
  rw [Real.ratPow_def, Real.ratPow_def]
  constructor <;> intro hxy
  · contrapose! hxy; rw [div_le_div_iff₀] at hxy
    rw [← ge_iff_le]; apply zpow_le_zpow_right₀ -- Similar to proven theorems
    apply Real.root_ge_one
    any_goals linarith
    norm_cast at hxy; linarith
    any_goals positivity
  · rw [gt_iff_lt, div_lt_div_iff₀] at hxy;
    rw [gt_iff_lt]; apply zpow_lt_zpow_right₀; apply Real.root_gt_one
    any_goals linarith
    norm_cast at hxy; linarith
    any_goals positivity
  any_goals positivity

/-- Lemma 5.6.9(e) / Exercise 5.6.2 -/
theorem Real.ratPow_mono_of_lt_one {x:Real} (hx0: 0 < x) (hx: x < 1) {q r:ℚ} : x^q > x^r ↔ q < r := by
  nth_rw 1 [show q = -(-q) by ring, show r = -(-r) by ring]
  rw [ratPow_neg']; nth_rw 2 [ratPow_neg']; simp
  rw [← gt_iff_lt, Real.ratPow_mono_of_gt_one (x := x⁻¹)]
  simp; rw [gt_iff_lt,one_lt_inv₀ hx0]
  all_goals linarith

/-- Lemma 5.6.9(f) / Exercise 5.6.2 -/
theorem Real.ratPow_mul {x y:Real} (hx: x > 0) (hy: y > 0) (q:ℚ) : (x*y)^q = x^q * y^q := by
  obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot q
  rw [Real.ratPow_def, Real.ratPow_def, Real.ratPow_def]
  rw [← mul_zpow, root_mul]
  any_goals positivity
  linarith

-- I could nuke this with positivity but I won't
theorem Real.squared_nonneg (x:Real) : x^2 ≥ 0 := by
  by_cases h : x ≥ 0
  · apply pow_nonneg; exact h
  · have : -x > 0 := by linarith
    rw [show x^2 = (-x)^2 by ring]
    apply pow_nonneg; linarith

/-- Exercise 5.6.3 -/
theorem Real.pow_even (x:Real) {n:ℕ} (hn: Even n) : x^n ≥ 0 := by
  obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp hn
  rw [mul_comm, ← pow_mul]
  apply Real.squared_nonneg

/-
Exercise 5.6.4 If x is a real number, show that |x| = (x2)1/2.
-/

theorem Real.abs_eq_sqrt_of_sq (x:Real) (hx : x ≠ 0) : |x| = (x^2)^(1/2:ℚ) := by
  wlog h : x > 0
  · have h0: -x > 0 := by
      apply lt_of_le_of_ne (by linarith) (by simp; apply hx)
    specialize this (-x) (by aesop) (by push_neg at h; linarith)
    rw [show ( |-x| = |x|) by simp, show ( (-x)^2 = x^2) by ring] at this
    exact this
  rw [show (1/2:ℚ) = (1/(2:ℕ)) by simp, ratPow_eq_root]
  rw [Real.root_of_pow]
  rw [_root_.abs_of_pos h]
  any_goals linarith
  positivity

/-- Exercise 5.6.5 -/
theorem Real.max_ratPow {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q > 0) :
  max (x^q) (y^q) = (max x y)^q := by
  by_cases hxy : x ≥ y
  · simp [hxy]; contrapose! hxy
    rw [← gt_iff_lt, Real.ratPow_mono];
    all_goals assumption
  · simp at hxy; simp [hxy.le]; apply le_of_lt;
    rw [← gt_iff_lt, ← Real.ratPow_mono];
    all_goals assumption

/-- Exercise 5.6.5 -/
theorem Real.min_ratPow {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q > 0) :
  min (x^q) (y^q) = (min x y)^q := by
  by_cases hxy : x ≥ y
  · simp [hxy]; contrapose! hxy
    rw [← gt_iff_lt, Real.ratPow_mono];
    all_goals assumption
  · simp at hxy; simp [hxy.le]; apply le_of_lt;
    rw [← gt_iff_lt, ← Real.ratPow_mono];
    all_goals assumption

-- Final part of Exercise 5.6.5: state and prove versions of the above lemmas covering the case of negative q.

#check Real.inv_of_gt
#check Real.inv_max
#check Real.inv_min

theorem Real.max_ratPow_neg {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q < 0) :
  max (x^q) (y^q) = (min x y)^q := by
  nth_rw 1 [show q = -(-q) by ring]; nth_rw 2 [show q = -(-q) by ring]
  rw [ratPow_neg']; nth_rw 2 [ratPow_neg']; simp
  rw [max_ratPow, ← Real.inv_min, ratPow_neg']; simp
  any_goals positivity
  any_goals linarith
  simp_all [isPos_iff]; simp_all [isPos_iff]

theorem Real.min_ratPow_neg {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q < 0) :
  min (x^q) (y^q) = (max x y)^q := by
  nth_rw 1 [show q = -(-q) by ring]; nth_rw 2 [show q = -(-q) by ring]
  rw [ratPow_neg']; nth_rw 2 [ratPow_neg']; simp
  rw [min_ratPow, ← Real.inv_max, ratPow_neg']; simp
  any_goals positivity
  any_goals linarith
  simp_all [isPos_iff]; simp_all [isPos_iff]

end Chapter5


namespace Chapter5


structure DedekindCut where
  E : Set ℚ
  nonempty : E.Nonempty
  bounded : BddAbove E
  lower: IsLowerSet E
  nomax : ∀ q ∈ E, ∃ r ∈ E, r > q

theorem isLowerSet_iff (E: Set ℚ) : IsLowerSet E ↔ ∀ q r, r < q → q ∈ E → r ∈ E :=
  isLowerSet_iff_forall_lt

abbrev Real.toSet_Rat (x:Real) : Set ℚ := { q | (q:Real) < x }

lemma Real.toSet_Rat_nonempty (x:Real) : x.toSet_Rat.Nonempty := by sorry

lemma Real.toSet_Rat_bounded (x:Real) : BddAbove x.toSet_Rat := by sorry

lemma Real.toSet_Rat_lower (x:Real) : IsLowerSet x.toSet_Rat := by sorry

lemma Real.toSet_Rat_nomax {x:Real} : ∀ q ∈ x.toSet_Rat, ∃ r ∈ x.toSet_Rat, r > q := by sorry

abbrev Real.toCut (x:Real) : DedekindCut :=
 {
   E := x.toSet_Rat
   nonempty := x.toSet_Rat_nonempty
   bounded := x.toSet_Rat_bounded
   lower := x.toSet_Rat_lower
   nomax := x.toSet_Rat_nomax
 }

abbrev DedekindCut.toSet_Real (c: DedekindCut) : Set Real := (fun (q:ℚ) ↦ (q:Real)) '' c.E

lemma DedekindCut.toSet_Real_nonempty (c: DedekindCut) : c.toSet_Real.Nonempty := by sorry

lemma DedekindCut.toSet_Real_bounded (c: DedekindCut) : BddAbove c.toSet_Real := by sorry

noncomputable abbrev DedekindCut.toReal (c: DedekindCut) : Real := sSup c.toSet_Real

lemma DedekindCut.toReal_isLUB (c: DedekindCut) : IsLUB c.toSet_Real c.toReal :=
  ExtendedReal.sSup_of_bounded c.toSet_Real_nonempty c.toSet_Real_bounded

noncomputable abbrev Real.equivCut : Real ≃ DedekindCut where
  toFun := toCut
  invFun := DedekindCut.toReal
  left_inv x := by
    sorry
  right_inv c := by
    sorry

end Chapter5



/-- Now to develop analogous results for the Mathlib reals. -/

abbrev Real.toSet_Rat (x:ℝ) : Set ℚ := { q | (q:ℝ) < x }

lemma Real.toSet_Rat_nonempty (x:ℝ) : x.toSet_Rat.Nonempty := by sorry

lemma Real.toSet_Rat_bounded (x:ℝ) : BddAbove x.toSet_Rat := by sorry

lemma Real.toSet_Rat_lower (x:ℝ) : IsLowerSet x.toSet_Rat := by sorry

lemma Real.toSet_Rat_nomax (x:ℝ) : ∀ q ∈ x.toSet_Rat, ∃ r ∈ x.toSet_Rat, r > q := by sorry

abbrev Real.toCut (x:ℝ) : Chapter5.DedekindCut :=
 {
   E := x.toSet_Rat
   nonempty := x.toSet_Rat_nonempty
   bounded := x.toSet_Rat_bounded
   lower := x.toSet_Rat_lower
   nomax := x.toSet_Rat_nomax
 }

namespace Chapter5

abbrev DedekindCut.toSet_R (c: DedekindCut) : Set ℝ := (fun (q:ℚ) ↦ (q:ℝ)) '' c.E

lemma DedekindCut.toSet_R_nonempty (c: DedekindCut) : c.toSet_R.Nonempty := by sorry

lemma DedekindCut.toSet_R_bounded (c: DedekindCut) : BddAbove c.toSet_R := by sorry

noncomputable abbrev DedekindCut.toR (c: DedekindCut) : ℝ := sSup c.toSet_R

lemma DedekindCut.toR_isLUB (c: DedekindCut) : IsLUB c.toSet_R c.toR :=
  isLUB_csSup c.toSet_R_nonempty c.toSet_R_bounded

end Chapter5

noncomputable abbrev Real.equivCut : ℝ ≃ Chapter5.DedekindCut where
  toFun := _root_.Real.toCut
  invFun := Chapter5.DedekindCut.toR
  left_inv x := by
    sorry
  right_inv c := by
    sorry

namespace Chapter5

/-- The isomorphism between the Chapter 5 reals and the Mathlib reals. -/
noncomputable abbrev Real.equivR : Real ≃ ℝ := Real.equivCut.trans _root_.Real.equivCut.symm

lemma Real.equivR_iff (x : Real) (y : ℝ) : y = Real.equivR x ↔ y.toCut = x.toCut := by
  simp only [equivR, Equiv.trans_apply, ←Equiv.apply_eq_iff_eq_symm_apply]
  rfl

/-- The isomorphism preserves order and ring operations -/
noncomputable abbrev Real.equivR_ordered_ring : Real ≃+*o ℝ where
  toEquiv := equivR
  map_add' := by sorry
  map_mul' := by sorry
  map_le_map_iff' := by sorry

theorem Real.pow_of_equivR (x:Real) (n:ℕ) : equivR (x^n) = (equivR x)^n := by
  sorry

theorem Real.zpow_of_equivR (x:Real) (n:ℤ) : equivR (x^n) = (equivR x)^n := by
  sorry


theorem Real.ratPow_of_equivR (x:Real) (q:ℚ) : equivR (x^q) = (equivR x)^(q:ℝ) := by
  sorry


end Chapter5
