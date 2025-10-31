
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


import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Real.Sqrt

--import Mathlib.Algebra.Order.Ring.InjSurj
--import Mathlib.Algebra.Order.Ring.Defs
-- import Init.Prelude

--import Project
import Project

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
#check Sequence.ofNatFun (· ^ 2)

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
      have h1 := pow_le_pow_left₀ (a:= 2) (b:= 10) (by norm_num) (by norm_num)
      have h2 := (Chapter4_3.two_pow_geq (N+1))
      have h3 := le_trans h2 (h1 (N+1))
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
  rw [Rat.closeSeq_def] at *; intro hn hb ha; specialize hab _ ha hb
  apply Close_symm hab

lemma Sequence.eventuallyClose_symm {ε:ℚ} {a b: Chapter5.Sequence}
    (hab: ε.EventuallyClose a b) : ε.EventuallyClose b a := by
  rw [Rat.eventuallyClose_def] at *; choose N hN using hab; use N;
  apply Sequence.closeSeq_symm hN

lemma Sequence.equiv_symm {a b: ℕ → ℚ} (hab: Equiv a b) : Equiv b a := by
  rw [Sequence.equiv_def] at *; intro ε hε; specialize hab ε hε
  apply Sequence.eventuallyClose_symm hab

#check abs_sub_le
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
  simp_all; rw [Rat.Close] at *;
  rw [abs_sub_comm] at hab1

  -- Use triangle inequality
  have hbn_am:= abs_sub_le (b n.toNat) (a n.toNat) (a m.toNat)
  have hbn_bm := abs_sub_le (b n.toNat) (a m.toNat) (b m.toNat)
  linarith


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

@[simp]
theorem CauchySequence.coe_eq {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) :
    (mk' ha).toSequence = (a:Sequence) := rfl

instance CauchySequence.instCoeFun : CoeFun CauchySequence (fun _ ↦ ℕ → ℚ) where
  coe a n := a.toSequence (n:ℤ)

@[simp]
theorem CauchySequence.coe_to_sequence (a: CauchySequence) :
    ((a:ℕ → ℚ):Sequence) = a.toSequence := by
  apply Sequence.ext (by simp [Sequence.n0_coe, a.zero])
  ext n; by_cases h:n ≥ 0 <;> simp_all
  rw [a.vanish]; rwa [a.zero]

@[simp]
theorem CauchySequence.coe_coe {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) : mk' ha = a := by rfl

/-- Proposition 5.3.3 / Exercise 5.3.1 -/
theorem Sequence.equiv_trans {a b c:ℕ → ℚ} (hab: Equiv a b) (hbc: Equiv b c) :
  Equiv a c := by sorry

/-- Proposition 5.3.3 / Exercise 5.3.1 -/
instance CauchySequence.instSetoid : Setoid CauchySequence where
  r := fun a b ↦ Sequence.Equiv a b
  iseqv := {
     refl := sorry
     symm := sorry
     trans := sorry
  }

theorem CauchySequence.equiv_iff (a b: CauchySequence) : a ≈ b ↔ Sequence.Equiv a b := by rfl

/-- Every constant sequence is Cauchy -/
theorem Sequence.IsCauchy.const (a:ℚ) : ((fun _:ℕ ↦ a):Sequence).IsCauchy := by sorry

instance CauchySequence.instZero : Zero CauchySequence where
  zero := CauchySequence.mk' (a := fun _: ℕ ↦ 0) (Sequence.IsCauchy.const (0:ℚ))

abbrev Real := Quotient CauchySequence.instSetoid

open Classical in
/--
  It is convenient in Lean to assign the "dummy" value of 0 to `LIM a` when `a` is not Cauchy.
  This requires Classical logic, because the property of being Cauchy is not computable or
  decidable.
-/
noncomputable abbrev LIM (a:ℕ → ℚ) : Real :=
  Quotient.mk _ (if h : (a:Sequence).IsCauchy then CauchySequence.mk' h else (0:CauchySequence))

theorem LIM_def {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) :
    LIM a = Quotient.mk _ (CauchySequence.mk' ha) := by
  rw [LIM, dif_pos ha]

/-- Definition 5.3.1 (Real numbers) -/
theorem Real.eq_lim (x:Real) : ∃ (a:ℕ → ℚ), (a:Sequence).IsCauchy ∧ x = LIM a := by
  apply Quotient.ind _ x; intro a; use (a:ℕ → ℚ)
  observe : ((a:ℕ → ℚ):Sequence) = a.toSequence
  rw [this, LIM_def (by convert a.cauchy)]
  refine ⟨ a.cauchy, ?_ ⟩
  congr; ext n; simp; replace := congr($this n); simp_all

/-- Definition 5.3.1 (Real numbers) -/
theorem Real.LIM_eq_LIM {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a = LIM b ↔ Sequence.Equiv a b := by
  constructor
  . intro h; replace h := Quotient.exact h
    rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff] at h
  intro h; apply Quotient.sound
  rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff]

/--Lemma 5.3.6 (Sum of Cauchy sequences is Cauchy)-/
theorem Sequence.IsCauchy.add {a b:ℕ → ℚ}  (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    (a + b:Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  rw [coe] at *
  intro ε hε
  choose N1 ha using ha _ (half_pos hε)
  choose N2 hb using hb _ (half_pos hε)
  use max N1 N2
  intro j hj k hk
  have h1 := ha j ?_ k ?_ <;> try omega
  have h2 := hb j ?_ k ?_ <;> try omega
  simp [Section_4_3.dist] at *; rw [←Rat.Close] at *
  convert Section_4_3.add_close h1 h2
  linarith


/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ) (haa': Equiv a a') :
    Equiv (a + b) (a' + b) := by
  -- This proof is written to follow the structure of the original text.
  rw [equiv_def] at *
  peel 2 haa' with ε hε haa'
  rw [Rat.eventuallyClose_def] at *
  choose N haa' using haa'; use N
  simp [Rat.closeSeq_def] at *
  peel 5 haa' with n hn hN _ _ haa'
  simp [hn, hN] at *
  convert Section_4_3.add_close haa' (Section_4_3.close_refl (b n.toNat))
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
      . solve_by_elim [Sequence.add_equiv]
      all_goals apply Sequence.IsCauchy.add <;> rw [CauchySequence.coe_to_sequence] <;> convert @CauchySequence.cauchy ?_
      )

/-- Definition 5.3.4 (Addition of reals) -/
theorem Real.LIM_add {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a + LIM b = LIM (a + b) := by
  simp_rw [LIM_def ha, LIM_def hb, LIM_def (Sequence.IsCauchy.add ha hb)]
  convert Quotient.liftOn₂_mk _ _ _ _
  rw [dif_pos]

/-- Proposition 5.3.10 (Product of Cauchy sequences is Cauchy) -/
theorem Sequence.IsCauchy.mul {a b:ℕ → ℚ}  (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    (a * b:Sequence).IsCauchy := by
  sorry

/-- Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ) (hb : (b:Sequence).IsCauchy) (haa': Equiv a a') :
  Equiv (a * b) (a' * b) := by
  sorry

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
      change LIM ((a:ℕ → ℚ) * (b:ℕ → ℚ)) = LIM ((a':ℕ → ℚ) * (b':ℕ → ℚ))
      rw [LIM_eq_LIM]
      . exact Sequence.mul_equiv (by rw [CauchySequence.coe_to_sequence]; exact a.cauchy) (by rw [CauchySequence.coe_to_sequence]; exact b'.cauchy) haa' hbb'
      all_goals apply Sequence.IsCauchy.mul <;> rw [CauchySequence.coe_to_sequence] <;> convert @CauchySequence.cauchy ?_
      )

theorem Real.LIM_mul {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a * LIM b = LIM (a * b) := by
  simp_rw [LIM_def ha, LIM_def hb, LIM_def (Sequence.IsCauchy.mul ha hb)]
  convert Quotient.liftOn₂_mk _ _ _ _
  rw [dif_pos]

instance Real.instRatCast : RatCast Real where
  ratCast := fun q ↦
    Quotient.mk _ (CauchySequence.mk' (a := fun _ ↦ q) (Sequence.IsCauchy.const q))

theorem Real.ratCast_def (q:ℚ) : (q:Real) = LIM (fun _ ↦ q) := by rw [LIM_def]; rfl

/-- Exercise 5.3.3 -/
@[simp]
theorem Real.ratCast_inj (q r:ℚ) : (q:Real) = (r:Real) ↔ q = r := by
  sorry

instance Real.instOfNat {n:ℕ} : OfNat Real n where
  ofNat := ((n:ℚ):Real)

instance Real.instNatCast : NatCast Real where
  natCast n := ((n:ℚ):Real)

@[simp]
theorem Real.LIM.zero : LIM (fun _ ↦ (0:ℚ)) = 0 := by rw [←ratCast_def 0]; rfl

instance Real.instIntCast : IntCast Real where
  intCast n := ((n:ℚ):Real)

/-- ratCast distributes over addition -/
theorem Real.ratCast_add (a b:ℚ) : (a:Real) + (b:Real) = (a+b:ℚ) := by sorry

/-- ratCast distributes over multiplication -/
theorem Real.ratCast_mul (a b:ℚ) : (a:Real) * (b:Real) = (a*b:ℚ) := by sorry

noncomputable instance Real.instNeg : Neg Real where
  neg x := ((-1:ℚ):Real) * x

/-- ratCast commutes with negation -/
theorem Real.neg_ratCast (a:ℚ) : -(a:Real) = (-a:ℚ) := by sorry

/-- It may be possible to omit the Cauchy sequence hypothesis here. -/
theorem Real.neg_LIM (a:ℕ → ℚ) (ha: (a:Sequence).IsCauchy) : -LIM a = LIM (-a) := by sorry

theorem Real.IsCauchy.neg (a:ℕ → ℚ) (ha: (a:Sequence).IsCauchy) :
    ((-a:ℕ → ℚ):Sequence).IsCauchy := by sorry


/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.addGroup_inst : AddGroup Real :=
AddGroup.ofLeftAxioms (by sorry) (by sorry) (by sorry)

theorem Real.sub_eq_add_neg (x y:Real) : x - y = x + (-y) := rfl

theorem Sequence.IsCauchy.sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    ((a-b:ℕ → ℚ):Sequence).IsCauchy := by sorry

/-- LIM distributes over subtraction -/
theorem Real.LIM_sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a - LIM b = LIM (a - b) := by sorry

/-- ratCast distributes over subtraction -/
theorem Real.ratCast_sub (a b:ℚ) : (a:Real) - (b:Real) = (a-b:ℚ) := by sorry


/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instAddCommGroup : AddCommGroup Real where
  add_comm := by sorry

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instCommMonoid : CommMonoid Real where
  mul_comm := by sorry
  mul_assoc := by sorry
  one_mul := by sorry
  mul_one := by sorry

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instCommRing : CommRing Real where
  left_distrib := by sorry
  right_distrib := by sorry
  zero_mul := by sorry
  mul_zero := by sorry
  mul_assoc := by sorry
  natCast_succ := by sorry
  intCast_negSucc := by sorry

abbrev Real.ratCast_hom : ℚ →+* Real where
  toFun := RatCast.ratCast
  map_zero' := by sorry
  map_one' := by sorry
  map_add' := by sorry
  map_mul' := by sorry

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

/-- Examples 5.3.13 -/
example : ¬ BoundedAwayZero (fun n ↦ 10^(-(n:ℤ)-1)) := by sorry

/-- Examples 5.3.13 -/
example : ¬ BoundedAwayZero (fun n ↦ 1 - 10^(-(n:ℤ))) := by sorry

/-- Examples 5.3.13 -/
example : BoundedAwayZero (fun n ↦ 10^(n+1)) := by
  use 1, by norm_num
  intro n; dsimp
  rw [abs_of_nonneg (by positivity), show (1:ℚ) = 10^0 by norm_num]
  gcongr <;> grind

/-- Examples 5.3.13 -/
example : ¬ ((fun (n:ℕ) ↦ (10:ℚ)^(n+1)):Sequence).IsBounded := by sorry

/-- Lemma 5.3.14 -/
theorem Real.boundedAwayZero_of_nonzero {x:Real} (hx: x ≠ 0) :
    ∃ a:ℕ → ℚ, (a:Sequence).IsCauchy ∧ BoundedAwayZero a ∧ x = LIM a := by
  -- This proof is written to follow the structure of the original text.
  obtain ⟨ b, hb, rfl ⟩ := eq_lim x
  simp only [←LIM.zero, ne_eq] at hx
  rw [LIM_eq_LIM hb (by convert Sequence.IsCauchy.const 0), Sequence.equiv_iff] at hx
  simp at hx
  choose ε hε hx using hx
  choose N hb' using (Sequence.IsCauchy.coe _).mp hb _ (half_pos hε)
  choose n₀ hn₀ hx using hx N
  have how : ∀ j ≥ N, |b j| ≥ ε/2 := by sorry
  set a : ℕ → ℚ := fun n ↦ if n < n₀ then ε/2 else b n
  have not_hard : Sequence.Equiv a b := by sorry
  have ha := (Sequence.isCauchy_of_equiv not_hard).mpr hb
  refine ⟨ a, ha, ?_, by rw [(LIM_eq_LIM ha hb).mpr not_hard] ⟩
  rw [bounded_away_zero_def]
  use ε/2, half_pos hε
  intro n; by_cases hn: n < n₀ <;> simp [a, hn, le_abs_self _]
  grind

/--
  This result was not explicitly stated in the text, but is needed in the theory. It's a good
  exercise, so I'm setting it as such.
-/
theorem Real.lim_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) :
    LIM a ≠ 0 := by sorry

theorem Real.nonzero_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a) (n: ℕ) : a n ≠ 0 := by
   choose c hc ha using ha; specialize ha n; contrapose! ha; simp [ha, hc]

/-- Lemma 5.3.15 -/
theorem Real.inv_isCauchy_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) :
    ((a⁻¹:ℕ → ℚ):Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  have ha' (n:ℕ) : a n ≠ 0 := nonzero_of_boundedAwayZero ha n
  rw [bounded_away_zero_def] at ha; choose c hc ha using ha
  simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq] at ha_cauchy ⊢
  intro ε hε; specialize ha_cauchy (c^2 * ε) (by positivity)
  choose N ha_cauchy using ha_cauchy; use N;
  peel 4 ha_cauchy with n hn m hm ha_cauchy
  calc
    _ = |(a m - a n) / (a m * a n)| := by congr; field_simp [ha' m, ha' n]; grind
    _ ≤ |a m - a n| / c^2 := by rw [abs_div, abs_mul, sq]; gcongr <;> solve_by_elim
    _ = |a n - a m| / c^2 := by rw [abs_sub_comm]
    _ ≤ (c^2 * ε) / c^2 := by gcongr
    _ = ε := by field_simp [hc]

/-- Lemma 5.3.17 (Reciprocation is well-defined) -/
theorem Real.inv_of_equiv {a b:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) (hb: BoundedAwayZero b)
  (hb_cauchy: (b:Sequence).IsCauchy) (hlim: LIM a = LIM b) :
    LIM a⁻¹ = LIM b⁻¹ := by
  -- This proof is written to follow the structure of the original text.
  set P := LIM a⁻¹ * LIM a * LIM b⁻¹
  have hainv_cauchy := Real.inv_isCauchy_of_boundedAwayZero ha ha_cauchy
  have hbinv_cauchy := Real.inv_isCauchy_of_boundedAwayZero hb hb_cauchy
  have haainv_cauchy := hainv_cauchy.mul ha_cauchy
  have habinv_cauchy := hainv_cauchy.mul hb_cauchy
  have claim1 : P = LIM b⁻¹ := by
    simp only [P, LIM_mul hainv_cauchy ha_cauchy, LIM_mul haainv_cauchy hbinv_cauchy]
    rcongr n; simp [nonzero_of_boundedAwayZero ha n]
  have claim2 : P = LIM a⁻¹ := by
    simp only [P, hlim, LIM_mul hainv_cauchy hb_cauchy, LIM_mul habinv_cauchy hbinv_cauchy]
    rcongr n; simp [nonzero_of_boundedAwayZero hb n]
  grind

open Classical in
/--
  Definition 5.3.16 (Reciprocation of real numbers).  Requires classical logic because we need to
  assign a "junk" value to the inverse of 0.
-/
noncomputable instance Real.instInv : Inv Real where
  inv x := if h: x ≠ 0 then LIM (boundedAwayZero_of_nonzero h).choose⁻¹ else 0

theorem Real.inv_def {a:ℕ → ℚ} (h: BoundedAwayZero a) (hc: (a:Sequence).IsCauchy) :
    (LIM a)⁻¹ = LIM a⁻¹ := by
  observe hx : LIM a ≠ 0
  set x := LIM a
  have ⟨ h1, h2, h3 ⟩ := (boundedAwayZero_of_nonzero hx).choose_spec
  simp [instInv, hx, -Quotient.eq]
  exact inv_of_equiv h2 h1 h hc h3.symm

@[simp]
theorem Real.inv_zero : (0:Real)⁻¹ = 0 := by simp [Inv.inv]

theorem Real.self_mul_inv {x:Real} (hx: x ≠ 0) : x * x⁻¹ = 1 := by
  sorry

theorem Real.inv_mul_self {x:Real} (hx: x ≠ 0) : x⁻¹ * x = 1 := by
  sorry

lemma BoundedAwayZero.const {q : ℚ} (hq : q ≠ 0) : BoundedAwayZero fun _ ↦ q := by
  use |q|; simp [hq]

theorem Real.inv_ratCast (q:ℚ) : (q:Real)⁻¹ = (q⁻¹:ℚ) := by
  by_cases h : q = 0
  . rw [h, ← show (0:Real) = (0:ℚ) by norm_cast]; norm_num; norm_cast
  simp_rw [ratCast_def, inv_def (BoundedAwayZero.const h) (by apply Sequence.IsCauchy.const)]; congr

/-- Default definition of division -/
noncomputable instance Real.instDivInvMonoid : DivInvMonoid Real where

theorem Real.div_eq (x y:Real) : x/y = x * y⁻¹ := rfl

noncomputable instance Real.instField : Field Real where
  exists_pair_ne := by sorry
  mul_inv_cancel := by sorry
  inv_zero := by sorry
  ratCast_def := by sorry
  qsmul := _
  nnqsmul := _

theorem Real.mul_right_cancel₀ {x y z:Real} (hz: z ≠ 0) (h: x * z = y * z) : x = y := by sorry

theorem Real.mul_right_nocancel : ¬ ∀ (x y z:Real), (hz: z = 0) → (x * z = y * z) → x = y := by
  sorry

/-- Exercise 5.3.4 -/
theorem Real.IsBounded.equiv {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hab: Sequence.Equiv a b) :
    (b:Sequence).IsBounded := by sorry

/--
  Same as `Sequence.IsCauchy.harmonic` but reindexing the sequence as a₀ = 1, a₁ = 1/2, ...
  This form is more convenient for the upcoming proof of Theorem 5.5.9.
-/
theorem Sequence.IsCauchy.harmonic' : ((fun n ↦ 1/((n:ℚ)+1): ℕ → ℚ):Sequence).IsCauchy := by
  rw [coe]; intro ε hε; choose N h1 h2 using (mk _).mp harmonic ε hε
  use N.toNat; intro j _ k _; specialize h2 (j+1) _ (k+1) _ <;> try omega
  simp_all

/-- Exercise 5.3.5 -/
theorem Real.LIM.harmonic : LIM (fun n ↦ 1/((n:ℚ)+1)) = 0 := by sorry

end Chapter5
end Chapter5
