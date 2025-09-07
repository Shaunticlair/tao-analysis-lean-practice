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
-- import Init.Prelude

--import Project
import Project.ExistsUnique

-- Only necessary so I don't see some yellow lines
set_option linter.unusedVariables false
set_option linter.style.commandStart false
set_option linter.style.longLine false


#check existsUnique_of_exists_of_unique
#check ExistsUnique.exists
#check ExistsUnique.unique
#check ExistsUnique.intro




namespace mySet

--------------- SECTION 3.1

/-
Axiom 3.1 (Sets are objects). If A is a set, then A is also an
object. In particular, given two sets A and B, it is meaningful to
ask whether A is also an element of B.
-/

@[ext]
structure MySet (U : Type) where -- Sets can only contain objects of one type in Lean
  elements : U → Prop -- Sets are defined by what they contain

variable {U α : Type} -- Our objects will all be from the same type, so we
-- don't have to worry about incompatible sets.


def mem (A : MySet U) (x : U) : Prop := A.elements x

-- Allow using ∈ notation
instance : Membership U (MySet U) where
  mem := mem



/-
Definition 3.1.4 (Equality of sets). Two sets A and Bare equal,
A = B, iff every element of A is an element of B and vice versa.
To put it another way, A = B if and only if every element x of A
belongs also to B, and every element y of B belongs also to A.
-/

@[ext] -- ext allows me to use this definition
theorem MySet.ext_mem {A B : MySet U} (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B := by
  ext x
  exact h x

/-
Axiom 3.2 (Empty set). There exists a set 0, known as the empty
set, which contains no elements, i.e., for every object x we have
x~0.
-/

def emptySet : MySet U where
  elements := fun _ => False -- No elements in the empty set

-- Make it so we can use ∅ notation

instance : EmptyCollection (MySet U) where
  emptyCollection := emptySet




theorem notMem_empty (x : U) : x ∉ (∅ : MySet U) := by
  intro h
  contradiction

theorem mem_empty_iff_false (x : U) : x ∈ (∅ : MySet U) ↔ False := by
  constructor
  · intro h; exact notMem_empty x h
  · tauto


/-Lemma 3.1.6 (Single choice). Let A be a non-empty set. Then
there exists an object x such that x EA. -/

theorem eq_empty_iff_forall_notMem (s : MySet U) :
s = (∅ : MySet U) ↔ ∀ (x : U), x ∉ s := by
  constructor
  · intro h x; rw [h]
    apply notMem_empty
  · intro h; ext y
    constructor
    · intro hy
      have hycontra := h y
      contradiction
    · intro he
      contradiction

theorem nonempty_def {A : MySet U} : A ≠ (∅ : MySet U) ↔ ∃ (x : U), x ∈ A := by
  constructor
  · contrapose!
    intro h
    exact (eq_empty_iff_forall_notMem A).2 h
  · intro h
    contrapose! h
    apply (eq_empty_iff_forall_notMem A).1 h


/-
Axiom 3.3 (Singleton sets and pair sets). If a i..'l an object, then
there exists a set {a} whose only element is a, i.e., for every object
y, we have yE {a} if and only if y =a; we refer to {a} as the
singleton set whose element is a. Furthermore, if a and b are
objects, then there exists a set {a, b} whose only elements are a
and b; i.e., for every object y, we have y E {a, b} if and only if
y = a or y = b; we refer to this set as the pair set formed by a
and b.
-/

def singletonSet (a : U) : MySet U where
  elements := fun x => x = a

-- Adding the tick because we're gonna replace the pairSet definition
-- soon anyway

def pairSet' (a b : U) : MySet U where
  elements := fun x => x = a ∨ x = b

@[default_instance 1000]
instance : Singleton U (MySet U) where
  singleton := singletonSet



theorem mem_singleton (a : U) : a ∈ { a } := by rfl -- a = a

theorem mem_singleton_iff {a x : U} : x ∈ {a} ↔ x = a := by rfl

-- I didn't create {a,b} for pairSet because it was buggy and is
-- about to be replaced by insert anyway
theorem mem_pair' {a b x : U} : x ∈ (pairSet' a b) ↔ x = a ∨ x = b := by rfl
/-
Axiom 3.4 (Pairwise union). Given any two sets A, B, there
exists a set A U B, called the union A U B of A and B, whose
elements consists of all the elements which belong to A or B or
both.
-/

def union (A B : MySet U) : MySet U where
  elements := fun x => x ∈ A ∨ x ∈ B

-- Allow using ∪ notation
instance : Union (MySet U) where
  union := union

theorem mem_union (x : U) (A B : MySet U) : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B :=
  by rfl

-- mem_union allows us to construct any arbitrarily long finite
-- set of known elements. So, we'll allow shorthand such as
-- {a,b} or {a,b,c}

instance : Insert U (MySet U) where
  insert x s := {x} ∪ s

-- We can now create a new pairSet definition that uses Insert
def pairSet (a b : U) := {a, b}

-- We'll quickly prove that pairSet is equivalent to pairSet'
theorem pairSet_eq_pairSet' (a b : U) : pairSet a b = pairSet' a b := rfl

-- We'll use pairSet going forward
theorem mem_pair {a b x : U} : x ∈ {a,b} ↔ x = a ∨ x = b := by rfl





/-
Lemma 3.1.13. If a and b are objects, then {a, b} ={a} U {b}.
If A, B, C are sets, then the union operation is commutative (i.e.,
AUB = BUA) and associative (i.e., (AUB)UC = AU (BUG)).
Also, we have A U A = A U 0 = 0 U A = A.
-/

lemma pair_of_union (a b : U) : {a,b} = {a} ∪ {b} := by
  ext x
  rw [mem_union, mem_pair]
  repeat rw [mem_singleton_iff]

theorem union_comm (A B : MySet U) : A ∪ B = B ∪ A := by
  ext x
  rw [mem_union, mem_union]
  exact Or.comm -- Or commutes

theorem union_assoc (A B C : MySet U) : A ∪ B ∪ C = A ∪ (B ∪ C) := by
  ext x
  rw [mem_union, mem_union, mem_union, mem_union]
  tauto -- Or is associative

theorem union_self (A : MySet U) : A ∪ A = A := by
  ext x
  rw [mem_union]
  tauto -- P or P is the same as P

theorem union_empty (A : MySet U) : A ∪ ∅ = A := by
  have := union_self ({A, A, A} : MySet (MySet U))
  ext x
  rw [mem_union]
  rw [mem_empty_iff_false]
  tauto -- Remove the false case and they're the same

theorem empty_union (A : MySet U) : ∅ ∪ A = A := by
  rw [union_comm]; apply union_empty


/-
Definition 3.1.15 (Subsets). Let A, B be sets. We say that A is
a subset of B, denoted A ~ B, iff every element of A is also an
element of B, i.e.
-/

def subset (A B : MySet U) := ∀ (x : U), x ∈ A → x ∈ B

-- Allow ⊆ notation
instance : HasSubset (MySet U) where
  Subset := subset

def ssubset (A B : MySet U) := A ⊆ B ∧ A ≠ B

-- Allow ⊂ notation
instance : HasSSubset (MySet U) where
  SSubset := ssubset

/-
Examples 3.1.17. Given any set A, we always have
A~ A (why?) and 0 ~A (why?).
-/

theorem subset.refl (A : MySet U) : A ⊆ A := by
  intro x; tauto

theorem empty_subset (A : MySet U) : ∅ ⊆ A := by
  intro x; intro h
  contradiction -- No elements in the empty set

/-
Proposition 3.1.18 (Sets are partially ordered by set inclusion).
Let A, B, C be sets. If A ~ B and B ~ C then A ~ C. If A ~ B
and B ~ A, then A = B. Finally, if A ~ B and B ~ C then
A~C.
-/

theorem subset_trans (A B C : MySet U) : A ⊆ B → B ⊆ C → A ⊆ C := by
  intro hAB hBC x hA
  apply hBC; apply hAB
  exact hA


theorem subset_antisymm (A B : MySet U) : A ⊆ B → B ⊆ A → A = B := by
  intro hAB hBA
  ext x
  constructor
  · apply hAB
  · apply hBA

theorem ssubset_trans (A B C : MySet U) : A ⊂ B → B ⊂ C → A ⊂ C := by
  intro hAB hBC
  constructor
  · intro x hA; apply hBC.1; apply hAB.1; exact hA
  · by_contra hcontra
    apply hBC.2

    apply subset_antisymm
    · apply hBC.1
    -- The basic idea is that, if C ⊆ A, then we have
    -- A ⊆ B ⊆ C ⊆ A. It forms a loop.

    -- And that means if x is in any one of the three, it can reach
    -- any of the others by cycling through.
    -- So, A=B=C.
    intro x hC
    apply hAB.1
    rw [hcontra]
    exact hC


/-
Axiom 3.5 (Axiom of specification). Let A be a set, and for each
x EA, let P(x) be a property pertaining to x (i.e., P(x) is either
a true statement or a false statement). Then there exists a set,
called {x ∈ A: P(x) is true} (or simply {x ∈ A: P(x)} for short),
whose elements are precisely the elements x in A for which P( x)
is true.
-/

def specifiedSet (A : MySet U) (P : U → Prop) : MySet U where
  elements := fun x => x ∈ A ∧ (P x)

-- It's really hard to get Lean to use {} without turning it into a Set
-- So instead I use fancy braces to get around it
-- Set builder notation for bounded sets: ⦃ x ∈ A | P x ⦄
syntax (name := mySetBuilderMem) "⦃" ident " ∈ " term " | " term "⦄" : term

macro_rules (kind := mySetBuilderMem)
  | `(⦃ $x:ident ∈ $A:term | $p:term ⦄) => `(specifiedSet $A (fun $x:ident => $p))

theorem mem_sep_iff (A : MySet U) (P : U → Prop) (x : U) :
  x ∈ ⦃ z ∈ A | P z ⦄ ↔ x ∈ A ∧ P x := by rfl

/-
Definition 3.1.23 (Intersections). The intersection S1 n S2 of
two sets  consists of all the elements which belong
to both S1 and S2
-/

def intersection (A B : MySet U) := ⦃ x ∈ A | x ∈ B ⦄

-- Allow using ∩  notation
instance : Inter (MySet U) where
  inter:= intersection

theorem mem_inter_iff (A B : MySet U) (x : U) :
  x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := by rfl

/-
Two sets A, B are said to be disjoint if A n B = 0
-/

def disjoint (A B : MySet U) := A ∩ B = ∅

/-
 (Difference sets). Given two sets A and B, we
define the set A - B or A \B to be the set A with any elements of
B removed:
-/

def difference (A B : MySet U) := ⦃x ∈ A | x ∉ B⦄

-- Allows for backslash
instance : SDiff (MySet U) where
  sdiff := difference

/-
Proposition 3.1.28 (Sets form a boolean algebra). Let A, B, 0
be sets, and let X be a set containing A, B, C as subsets.
(a) {Minimal element) We have A U 0 =A and An 0 = 0.
(b) {Maximal element) We have A U X= X and An X= A.
(c) {Identity) We have An A= A and A U A= A.
(d) {Commutativity) We have AUB = BUA and AnB = BnA.
(e) {Associativity) We have (A U B) U C = A U (B U C) and
(An B) n C =An (B n C).
(f) {Distributivity) We have An (B u C)= (An B) U (An 0)
and A u (B n C)= (A u B) n (A u C).
(g) {Partition) We have A U (X\A) =X and An (X\A) = 0.
(h) {De Morgan laws) We have X\(A u B) = (X\A) n (X\B)
and X\(A n B)= (X\A) U (X\B).
-/

--- First, we define a couple things: univ, compl

def gen_univ (α : Type) : MySet α where
  elements := (fun _ => True)

def univ : MySet U := gen_univ U

-- trivial would work for this theorem, but I want to try to dissect
-- the Lean structure a bit
theorem mem_univ (x : U) : x ∈ univ := by
  unfold univ -- univ is defined with (fun x => True)
  unfold gen_univ
  dsimp [Membership.mem] -- Remove ∈ symbol to get back mem
  dsimp [mem] -- mem tells us to apply the function, we get true

theorem mem_univ_iff_true (x : U) : (x ∈ univ ↔ True) := by
  tauto


def compl (A : MySet U) := univ \ A

-- Allow using ᶜ notation for complements
instance : HasCompl (MySet U) where
  compl := compl

theorem mem_compl {A : MySet U} {x : U} (h : x ∉ A) : x ∈ Aᶜ := by
  constructor
  · exact mem_univ x -- x in univ
  · simp; exact h -- x not in A

theorem notMem_of_mem_compl {A : MySet U} {x : U} (h : x ∈ Aᶜ) : x ∉ A := by
  exact h.right

theorem notMem_compl_iff {A : MySet U} {x : U} : x ∉ A ↔ x ∈ Aᶜ := by
  constructor
  · apply mem_compl
  · apply notMem_of_mem_compl

theorem compl_compl {A : MySet U} : Aᶜᶜ = A := by
  ext x
  rw [← notMem_compl_iff, ← notMem_compl_iff] -- Equivalent to not-not x ∈ A
  tauto
--- Now, we can begin with the proposition
--- Honestly, a lot of these are probably meant to be handled using
--- constructor, and showing that the two sides are equivalent
--- But I think using direct logic is good enough since I'm confident
--- in these, after doing the set theory game.
--- If anything, I'll mostly focus on how my construction of sets
--- interacts with these.

theorem inter_comm (A B : MySet U) : A ∩ B = B ∩ A := by
  ext x; rw [mem_inter_iff]; rw [mem_inter_iff]
  tauto -- Or is commutative



theorem inter_empty (A : MySet U) : A ∩ ∅ = ∅  := by
  ext x
  rw [ mem_inter_iff, mem_empty_iff_false]
  tauto -- P and False is always False

theorem empty_inter (A : MySet U) : ∅ ∩ A = ∅  := by
  rw [inter_comm]
  apply inter_empty



theorem union_univ (A : MySet U) : A ∪ univ = univ := by
  ext x; rw [mem_univ_iff_true]
  rw [mem_union, mem_univ_iff_true]
  tauto

theorem univ_union (A : MySet U) : univ ∪ A    = univ := by
  rw [union_comm]; apply union_univ



theorem inter_univ (A : MySet U) : A ∩ univ = A := by
  ext x; rw [mem_inter_iff, mem_univ_iff_true ]
  simp -- If we remove True, we just have x ∈ A on both sides

theorem univ_inter (A : MySet U) : univ ∩ A    = A := by
  rw [inter_comm]; apply inter_univ

theorem inter_self (A : MySet U) : A ∩ A = A := by
  ext x; rw [mem_inter_iff]; tauto -- Same goals on both sides

theorem inter_assoc (A B C : MySet U) : A ∩ B ∩ C = A ∩ (B ∩ C) := by
  ext x
  rw [mem_inter_iff]; rw [mem_inter_iff];
  rw [mem_inter_iff]; rw [mem_inter_iff]
  tauto -- Logic intersection is associative
  -- I could do both ways manually, but it'd just be a bunch of casework


theorem inter_union_distrib_left (A B C : MySet U) :
A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  rw [mem_inter_iff, mem_union, mem_union, mem_inter_iff]
  -- Casework, but mildly more interesting
  constructor
  · intro ⟨ha, hbc⟩
    rcases hbc with hb | hc
    · left; apply And.intro ha hb
    · right; apply And.intro ha hc
  · intro habc
    rcases habc with hab | hac
    · constructor
      · apply hab.1
      · left; apply hab.2
    · constructor
      · apply hac.1
      · right; apply hac.2

theorem union_inter_distrib_left (A B C : MySet U) :
A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  rw [mem_inter_iff, mem_union, mem_union, mem_inter_iff, mem_union]
  constructor
  · intro habc
    rcases habc with ha | hbc
    · constructor <;> apply Or.inl ha
    · constructor
      · apply Or.inr hbc.1
      · apply Or.inr hbc.2
  · intro ⟨hab, hac⟩
    rcases hab with ha | hb
    · apply Or.inl ha
    · rcases hac with ha | hc
      · apply Or.inl ha
      · apply Or.inr; apply And.intro hb hc


theorem union_compl_self (A : MySet U) : A ∪ Aᶜ  = univ := by
  ext x; rw [mem_union]; tauto -- P and not P

theorem inter_compl_self (A : MySet U) : A ∩ Aᶜ  = ∅ := by
  ext x; rw [mem_inter_iff, mem_empty_iff_false]
  constructor
  · intro ⟨ha,hac⟩
    have hanot := hac.2
    contradiction -- x ∈ A; x ∉ A
  · tauto


theorem compl_union (A B : MySet U) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  rw [← notMem_compl_iff, mem_inter_iff, mem_union]
  rw [← notMem_compl_iff, ← notMem_compl_iff]
  constructor
  · intro hor
    constructor
    · contrapose! hor
      apply Or.inl hor
    · contrapose! hor
      apply Or.inr hor
  · intro ⟨hac,hbc⟩
    by_contra hab
    rcases hab with ha | hb
    · contradiction
    · contradiction

theorem compl_inter (A B : MySet U) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  ext x
  rw [← compl_compl (A := Aᶜ ∪ Bᶜ)]
  rw [compl_union]
  rw [compl_compl, compl_compl]


/-
Axiom 3.6 (Replacement). Let A be a set. For any object x E
A, and any object y, suppose we have a statement P(x, y) per
taining to x and y, such that for each x E A there is at most
one y for which P(x, y) is true. Then there exists a set {y
P(x, y) is true for some x EA}, such that for any object z,
-/

def partial_function (P : U → U → Prop) : Prop:=
  ∀ (x y1 y2), P x y1 → P x y2 → y1=y2

def replacedSet (A : MySet U) (P : U → U → Prop) (hP : partial_function P) :
MySet U where
  elements := fun y => ∃ (x : U), (P x y) ∧ (x ∈ A)

-- Honestly I couldn't easily think of a way to construct notation for this
-- So, I'll deal with that problem later

/-
Axiom 3. 7 (Infinity). There exists a set N, whose elements are
called natural numbers, as well as an object 0 in N, and an object
n-++ assigned to every natural number n E N, such that the Peano
axioms (Axioms 2.1 - 2. 5) hold.
-/

-- We showed in ch2 that MyNat obeys Peano's axioms.
-- We'll use Nat here instead though.

def natural_numbers : MySet Nat := gen_univ Nat

/-
Exercise 3.1.2. Using only Definition 3.1.4, Axiom 3.2, and Axiom 3.3,
prove that the sets 0, {0}, { {0} }, and {0, {0}} are all distinct (i.e., no
two of them are equal to each other).


def empty := (emptySet: MySet U)
def setempty := ({empty}: MySet (MySet U))
def setsetempty := ({setempty}: MySet (MySet (MySet U)))
def setemptysetempty := ({setempty, empty }: MySet (MySet (MySet U)))

def empty_ne_setempty : empty ≠ setempty := by sorry
def emtpy_ne_setsetempty : empty ≠ setsetempty := by sorry

It's weirdly hard to get this to work in lean.
-/

/-
Exercise 3.1.5. Let A, B be sets. Show that the three statements A ~ B,
A U B = B, An B = A are logically equivalent (any one of them implies
the other two).
-/

theorem union_eq_right (A B : MySet U) :A ⊆ B ↔ A ∪ B = B := by
  constructor
  · intro h; ext x
    rw [mem_union]
    constructor
    · intro hAB
      rcases hAB with hA | hB
      · apply h; exact hA
      · exact hB
    · tauto -- Q → P ∨ Q
  · intro h x hA
    have: x ∈ A ∪ B := Or.inl hA
    rw [h] at this
    exact this

theorem inter_eq_left (A B : MySet U) : A ⊆ B ↔ A ∩ B = A := by
  constructor
  · intro h; ext x
    constructor
    · intro hAB; exact hAB.1
    · intro hA
      have hB := h x hA
      exact And.intro hA hB
  · intro h x hA
    rw [← h] at hA
    exact hA.2

--- This isn't a real mathlib theorem afaik
theorem union_eq_right_iff_inter_eq_left (A B : MySet U) :
  A ∪ B = B ↔ A ∩ B = A := by
  rw [← union_eq_right, ← inter_eq_left]

/-
Exercise 3.1.7. Let A, B, C be sets. Show that AnB ⊆A and AnB ⊆B.
Furthermore, show that C ⊆ A and C ⊆ B if and only if C ⊆ An B. In
a similar spirit, show that A⊆ A U Band B ⊆A U B, and furthermore
that A ⊆ C and B ⊆ C if and only if A U B ⊆ C.
-/


theorem inter_subset_left (A B : MySet U) : A ∩ B ⊆ A := by
  intro x hx; apply hx.1

theorem inter_subset_right (A B : MySet U) : A ∩ B ⊆ B := by
  intro x hx; apply hx.2

theorem subset_inter_iff (A B C : MySet U) : A ⊆ B ∩ C ↔ A ⊆ B ∧ A ⊆ C := by
  constructor
  · intro h
    constructor
    · intro x hA
      have hBC := h x hA
      exact hBC.1
    · intro x hA
      have hBC := h x hA
      exact hBC.2
  · intro h x hA
    constructor
    · apply h.1 x hA
    · apply h.2 x hA


theorem subset_union_left (A B : MySet U) : A ⊆ A ∪ B := by
  intro x hA; apply Or.inl hA

theorem subset_union_right (A B : MySet U) : B ⊆ A ∪ B := by
  intro x hB; apply Or.inr hB

theorem union_subset_iff (A B C : MySet U) : A ∪ B ⊆ C ↔ A ⊆ C ∧ B ⊆ C := by
  constructor
  · intro h
    constructor
    · intro x hA
      apply h
      apply Or.inl hA
    · intro x hB
      apply h
      apply Or.inr hB
  · intro ⟨hAC, hBC ⟩
    intro x hAB
    rcases hAB with hA | hB
    · apply hAC; apply hA
    · apply hBC; apply hB



/-
Exercise 3.1.8. Let A, B be sets. Prove the absorption laws An(AUB) :::::
A and A U (An B) = A.
-/

theorem inf_sup_self (A B C : MySet U) : A ∩ (A ∪ B) = A := by
  ext x
  constructor
  · intro h; exact h.1
  · intro hA;
    constructor
    · apply hA
    · apply Or.inl hA

theorem sup_inf_self (A B C : MySet U) : A ∪ (A ∩ B) = A := by
  ext x
  constructor
  · intro h
    rcases h with hA | hAB
    · apply hA
    · apply hAB.1
  · intro hA; apply Or.inl hA


/-
Exercise 3.1.9. Let A, B, X be sets such that AUB =X and AnB = 0.
Show that A = X\B and B = X\A.
-/

--- Can't find a mathlib name for this

theorem partition_left {A B X : MySet U} (h1 : A ∪ B = X) (h2 : A ∩ B = ∅) :
A = X \ B := by
  ext x
  constructor
  · intro hA
    constructor
    · rw [← h1]
      apply Or.inl hA
    · simp
      intro hB
      rw [← mem_empty_iff_false x]
      rw [← h2]
      apply And.intro hA hB
  · intro ⟨ hX, hB' ⟩
    simp at hB'
    rw [← h1] at hX
    rcases hX with hA | hB
    · exact hA
    · contradiction

theorem partition_right {A B X : MySet U} (h1 : A ∪ B = X) (h2 : A ∩ B = ∅) :
  B = X \ A := by
  rw [union_comm] at h1
  rw [inter_comm] at h2
  apply partition_left h1 h2

/-
Exercise 3.1.10. Let A and B be sets. Show that the three sets A\B,
A n B, and B\A are disjoint, and that their union is A U B.
-/

theorem disjoint_sdiff_inter {A B : MySet U} : disjoint (A \ B) (A ∩ B) := by
  ext x
  rw [mem_empty_iff_false]
  simp
  intro ⟨hdiff, hab⟩
  apply hdiff.2 hab.2 -- We can't have and not have x ∈ B

theorem disjoint_sdiff_sdiff {A B : MySet U} : disjoint (A \ B) (B \ A) := by
  ext x
  rw [mem_empty_iff_false]
  simp
  intro ⟨hab, hba⟩
  apply hab.2 hba.1 -- x ∈ A and its opposite

theorem union_eq_diff_union_diff_union_inter {A B : MySet U} :
  A ∪ B = (A \ B) ∪ (B \ A) ∪ (A ∩ B) := by
  ext x
  repeat rw [mem_union]
  constructor
  · intro hAB
    rcases hAB with hA | hB
    · by_cases hB: x ∈ B
      · right; apply And.intro hA hB
      · left; left; apply And.intro hA hB
    · by_cases hA : x ∈ A
      · right; apply And.intro hA hB
      · left; right; apply And.intro hB hA
  · intro hAB
    simp at hAB
    rcases hAB with h2 | hAB -- A bit weird that rcases doesn't work; oh well
    · rcases h2 with hA | hB
      · apply Or.inl hA.1
      · apply Or.inr hB.1
    · apply Or.inl hAB.1

-- This one doesn't seem to be a real mathlib theorem

theorem disjoint_inter_sdiff {A B : MySet U} : disjoint (B \ A) (A ∩ B) := by
  rw [inter_comm]
  apply disjoint_sdiff_inter



/-
Exercise 3.1.11. Show that the axiom of replacement implies the axiom
of specification.
-/

def replacement_set_for_specification (A : MySet U) (P : U → Prop) : MySet U :=
  let Q := fun (x: U) (y : U) => x = y ∧ P x
  have hQ: partial_function Q:= by
    unfold partial_function
    intro x y1 y2
    unfold Q
    intro ⟨h1, _⟩  ⟨h2,_⟩
    rw [← h1,← h2]
  replacedSet A Q hQ

--- Not a mathlib theorem

--- Demonstrates that our replacement set is equivalent to the
--- desired specification set.

theorem replacement_imp_specification {P : U → Prop} {A : MySet U} :
specifiedSet A P = replacement_set_for_specification A P := by
  unfold specifiedSet
  unfold replacement_set_for_specification
  unfold replacedSet
  simp
  ext x
  tauto



end mySet

--------------- SECTION 3.1: Tao's version
namespace mySetAxioms


/-
After completing 3.1, I then reference the Terence Tao version at
https://github.com/teorth/analysis

As per Tao, we use a typeclass for our Set Theory.
-/
universe u v

class SetTheory where -- Directly copy-pasted from Tao (heavily annotated for my learning)
  Set : Type u -- Axiom 3.1

  Object : Type v -- Axiom 3.1

  set_to_object : Set ↪ Object -- Axiom 3.1

  mem : Object → Set → Prop -- Axiom 3.1

  extensionality X Y : (∀ x, mem x X ↔ mem x Y) → X = Y -- Definition 3.1.4

  emptyset: Set -- Axiom 3.2

  emptyset_mem x : ¬ mem x emptyset -- Axiom 3.2

  singleton : Object → Set -- Axiom 3.3

  singleton_axiom x y : mem x (singleton y) ↔ x = y -- Axiom 3.3

  union_pair : Set → Set → Set -- Axiom 3.4

  union_pair_axiom X Y x : mem x (union_pair X Y) ↔ (mem x X ∨ mem x Y) -- Axiom 3.4

  specify A (P: Subtype (mem · A) → Prop) : Set -- Axiom 3.5

  specification_axiom A (P: Subtype (mem · A) → Prop) : -- Axiom 3.5
    (∀ x, mem x (specify A P) → mem x A) ∧ -- Specify is a subset of A
    (∀ x, mem x.val (specify A P) ↔ P x)   -- Specify is exactly the elements that obey P
    -- x.val because P x refers to x as the subtype where x ∈ A

  replace A (P: Subtype (mem ·  A) → Object → Prop)
    (hP: ∀ x y y', P x y ∧ P x y' → y = y') : Set -- Axiom 3.6

  replacement_axiom A (P: Subtype (mem ·  A) → Object → Prop)
    (hP: ∀ x y y', P x y ∧ P x y' → y = y') :
    ∀ y, mem y (replace A P hP) ↔ ∃ x, P x y -- Axiom 3.6

  nat : Set -- Axiom 3.7

  nat_equiv : ℕ  ≃ Subtype (mem · nat) -- Axiom 3.7

  -- Axiom 3.8 is universal comprehension: bad!

  regularity_axiom A  -- Axiom 3.9
  (hA : ∃ x, mem x A) : -- If A is nonempty
    ∃ x, mem x A ∧      -- There's some x ∈ A such that
      ∀ S,
        x = set_to_object S →      -- Either x is not a set,
          ¬ ∃ y, mem y A ∧ mem y S -- Or no elements are in both x and A (they're disjoint)

  pow : Set → Set → Set -- Axiom 3.10: The powerset Y^X

  function_to_object (X: Set) (Y: Set) : -- Axiom 3.10: turn functions into objects
    (Subtype (mem ·  X) → Subtype (mem ·  Y)) -- Take any f: X → Y
    ↪ Object -- Turn it into an Object

  powerset_axiom (X: Set) (Y: Set) (F:Object) : -- Axiom 3.10
    mem F (pow X Y) ↔  -- If F is in X ^ Y
      ∃ f: Subtype (mem ·  Y) → Subtype (mem ·  X), -- Then F corresponds to
        function_to_object Y X f = F                  -- some function f: Y → X

  union : Set → Set -- Axiom 3.12: Union of sets

  union_axiom A x : -- Axiom 3.12
    mem x (union A) ↔               -- The union over A is defined to
      ∃ S, mem x S ∧                -- Contain elements such that
      mem (set_to_object S) A       -- They exist in some set S ∈ A

-- This enables one to use `Set` and `Object` instead of `SetTheory.Set` and `SetTheory.Object`.
export SetTheory (Set Object)
-- This instance implicitly imposes the axioms of Zermelo-Frankel set theory with atoms.
variable [SetTheory]
abbrev U := Object -- Makes it more compatible with my old code.

-- Allows `∈` notation between our `Object` and `Set`.
instance SetTheory.objects_mem_sets : Membership Object Set where
  mem X x := mem x X


/-
Axiom 3.1 (Sets are objects). If A is a set, then A is also an
object. In particular, given two sets A and B, it is meaningful to
ask whether A is also an element of B.
-/

-- Here, we seem to be defining *how* we coerce a set into an object? I guess?
instance SetTheory.sets_are_objects : Coe Set Object where
  coe X := set_to_object X

-- Now, we're showing that the coercion doesn't damage equality between sets
-- Equality in the Set world is equivalent to equality in the Object world, if you will
@[simp]
theorem SetTheory.Set.coe_eq_iff (X Y : Set) : (X : U) = (Y : U) ↔  X = Y := by
  constructor
  · intro h; apply set_to_object.inj' h -- Embeddings have injectivity built-in, apparently
  · intro h; rw [h] -- Coercion is a function: same input, same output

/-
Definition 3.1.4 (Equality of sets). Two sets A and Bare equal,
A = B, iff every element of A is an element of B and vice versa.
To put it another way, A = B if and only if every element x of A
belongs also to B, and every element y of B belongs also to A.
-/

-- Allows for ext to be used directly
abbrev SetTheory.Set.ext {X Y : Set} (h : ∀ x, x ∈ X ↔ x ∈ Y) : X = Y :=
extensionality _ _ h


theorem SetTheory.Set.ext_iff (X Y : Set) : X = Y ↔ ∀ x, x ∈ X ↔ x ∈ Y := by
  constructor
  · intro h x; rw [h] -- Forward version is true because substitution
  · intro h; apply ext h

/-
Axiom 3.2 (Empty set). There exists a set 0, known as the empty
set, which contains no elements, i.e., for every object x we have
x~0.
-/

-- Allows for ∅ notation
instance SetTheory.Set.instEmpty : EmptyCollection Set where
  emptyCollection := emptyset

@[simp]
theorem SetTheory.Set.notMem_empty (x : U) : x ∉ (∅:Set) := by apply emptyset_mem

-- From here on, I'll start re-using my previous code more often

theorem SetTheory.Set.mem_empty_iff_false (x : U) : x ∈ (∅ : Set) ↔ False := by
  constructor
  · intro h; exact notMem_empty x h
  · tauto

/-Lemma 3.1.6 (Single choice). Let A be a non-empty set. Then
there exists an object x such that x EA. -/
theorem SetTheory.Set.eq_empty_iff_forall_notMem (s : Set) :
  s = (∅ : Set) ↔ ∀ x, x ∉ s := by
  constructor
  · intro h x; rw [h]
    apply notMem_empty
  · intro h; apply ext; intro y
    constructor
    · intro hy
      have hycontra := h y
      contradiction
    · intro he
      have he' := notMem_empty y
      contradiction



theorem SetTheory.Set.nonempty_def {A : Set} : A ≠ (∅ : Set) ↔ ∃ (x : U), x ∈ A := by
  constructor
  · contrapose!
    intro h
    exact (eq_empty_iff_forall_notMem A).2 h
  · intro h
    contrapose! h
    apply (eq_empty_iff_forall_notMem A).1 h


theorem SetTheory.Set.empty_unique : ∃! (X:Set), ∀ x, x ∉ X :=
by
  use (∅ : Set)
  simp -- If an object y has this property, then it must equal ∅
  intro y hy
  apply ext
  intro x
  constructor
  · intro hxy; have hxy' := hy x; contradiction -- x ∉ y
  · intro he; have := notMem_empty x; contradiction -- x ∉ ∅

/-
Axiom 3.3 (Singleton sets and pair sets). If a i..'l an object, then
there exists a set {a} whose only element is a, i.e., for every object
y, we have yE {a} if and only if y =a; we refer to {a} as the
singleton set whose element is a. Furthermore, if a and b are
objects, then there exists a set {a, b} whose only elements are a
and b; i.e., for every object y, we have y E {a, b} if and only if
y = a or y = b; we refer to this set as the pair set formed by a
and b.
-/

--- Anything involving a new construction will still need to derive from Tao's work
--- since that's what everything is built on now

-- Now we can use the `{x}` notation for a single element `Set`.
instance SetTheory.Set.instSingleton : Singleton Object Set where
  singleton := singleton

@[simp]
theorem SetTheory.Set.mem_singleton (x a : U) : x ∈ ({a} : Set) ↔ x = a :=
  singleton_axiom x a

/-
Axiom 3.4 (Pairwise union). Given any two sets A, B, there
exists a set A U B, called the union A U B of A and B, whose
elements consists of all the elements which belong to A or B or
both.
-/

-- Now we can use the `X ∪ Y` notation for a union of two `Set`s.
instance SetTheory.Set.instUnion : Union Set where
  union := union_pair

@[simp]
theorem SetTheory.Set.mem_union (x : U) (X Y : Set) : x ∈ (X ∪ Y) ↔ (x ∈ X ∨ x ∈ Y) :=
  union_pair_axiom X Y x


/-
Interestingly, Tao *also* skips the pair set part of his own theorem, similar to what
I eventually did.

More convenient for me: we'll skip straight to the fact that the pairwise axiom can be
used to create arbitrarily large finite sets of known elements using pairing with
singleton sets.
-/

instance SetTheory.Set.instInsert : Insert Object Set where
  insert x X := {x} ∪ X

@[simp]
theorem SetTheory.Set.mem_triple (x a b c : U) : x ∈ ({a,b,c}:Set) ↔ (x = a ∨ x = b ∨ x = c) := by
  simp [Insert.insert, mem_union, mem_singleton]

-- Ngl I'm too lazy to check the various things in the remarks


/-
Lemma 3.1.13. If a and b are objects, then {a, b} ={a} U {b}.
If A, B, C are sets, then the union operation is commutative (i.e.,
AUB = BUA) and associative (i.e., (AUB)UC = AU (BUG)).
Also, we have A U A = A U 0 = 0 U A = A.
-/
theorem SetTheory.Set.pair_eq (a b : U) : ({a,b}:Set) = {a} ∪ {b} := by rfl

@[simp]
theorem SetTheory.Set.mem_pair (x a b : U) : x ∈ ({a,b}:Set) ↔ (x = a ∨ x = b) := by
  simp [pair_eq, mem_union, mem_singleton]


theorem SetTheory.Set.union_comm (A B : Set) : A ∪ B = B ∪ A := by
  apply ext; intro x
  rw [mem_union, mem_union]
  exact Or.comm -- Or commutes

theorem SetTheory.Set.union_assoc (A B C : Set) : A ∪ B ∪ C = A ∪ (B ∪ C) := by
  apply ext; intro x
  rw [mem_union, mem_union, mem_union, mem_union]
  tauto -- Or is associative

theorem SetTheory.Set.union_self (A : Set) : A ∪ A = A := by
  apply ext; intro x
  rw [mem_union]
  tauto -- P or P is the same as P

theorem SetTheory.Set.union_empty (A : Set) : A ∪ ∅ = A := by
  apply ext; intro x
  rw [mem_union]
  rw [mem_empty_iff_false]
  tauto -- Remove the false case and they're the same

theorem SetTheory.Set.empty_union (A : Set) : ∅ ∪ A = A := by
  rw [union_comm]; apply union_empty


/-
Definition 3.1.15 (Subsets). Let A, B be sets. We say that A is
a subset of B, denoted A ~ B, iff every element of A is also an
element of B, i.e.
-/

def subset (A B : Set) := ∀ (x : U), x ∈ A → x ∈ B

-- Allow ⊆ notation
instance SetTheory.Set.instSubset : HasSubset Set where
  Subset := subset

def ssubset (A B : Set) := A ⊆ B ∧ A ≠ B

-- Allow ⊂ notation
instance SetTheory.Set.instSSubset : HasSSubset Set where
  SSubset := ssubset

theorem SetTheory.Set.subset_def (X Y : Set) : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y :=
by rfl

theorem SetTheory.Set.ssubset_def (X Y : Set) : X ⊂ Y ↔ (X ⊆ Y ∧ X ≠ Y) :=
by rfl


/-
Examples 3.1.17. Given any set A, we always have
A~ A (why?) and 0 ~A (why?).
-/

theorem SetTheory.Set.subset.refl (A : Set) : A ⊆ A := by
  intro x; tauto

theorem SetTheory.Set.subset_self (A : Set) : A ⊆ A := by apply subset.refl

theorem SetTheory.Set.empty_subset (A : Set) : (∅: Set) ⊆ A := by
  intro x; intro h
  rw [mem_empty_iff_false] at h; contradiction -- No elements in the empty set

/-
Proposition 3.1.18 (Sets are partially ordered by set inclusion).
Let A, B, C be sets. If A ~ B and B ~ C then A ~ C. If A ~ B
and B ~ A, then A = B. Finally, if A ~ B and B ~ C then
A~C.
-/

theorem SetTheory.Set.subset_trans {A B C : Set} : A ⊆ B → B ⊆ C → A ⊆ C := by
  intro hAB hBC x hA
  apply hBC; apply hAB
  exact hA

--theorem SetTheory.Set.subset_trans {A B C:Set} (hAB:A ⊆ B) (hBC:B ⊆ C) : A ⊆ C :=

theorem SetTheory.Set.subset_antisymm {A B : Set} : A ⊆ B → B ⊆ A → A = B := by
  intro hAB hBA
  apply ext; intro x
  constructor
  · apply hAB
  · apply hBA

theorem SetTheory.Set.ssubset_trans {A B C : Set} : A ⊂ B → B ⊂ C → A ⊂ C := by
  intro hAB hBC
  constructor
  · intro x hA; apply hBC.1; apply hAB.1; exact hA
  · by_contra hcontra
    apply hBC.2

    apply subset_antisymm
    · apply hBC.1
    -- The basic idea is that, if C ⊆ A, then we have
    -- A ⊆ B ⊆ C ⊆ A. It forms a loop.

    -- And that means if x is in any one of the three, it can reach
    -- any of the others by cycling through.
    -- So, A=B=C.
    intro x hC
    apply hAB.1
    rw [hcontra]
    exact hC


/-
Axiom 3.5 (Axiom of specification). Let A be a set, and for each
x EA, let P(x) be a property pertaining to x (i.e., P(x) is either
a true statement or a false statement). Then there exists a set,
called {x ∈ A: P(x) is true} (or simply {x ∈ A: P(x)} for short),
whose elements are precisely the elements x in A for which P( x)
is true.
-/

-- Useful abbreviation for specification
abbrev SetTheory.Set.toSubtype (A : Set) := Subtype (fun x ↦ x ∈ A)

-- Now, we can treat A as if it were a type
-- Specifically, it is the Subtype (fun x ↦ x ∈ A)
instance : CoeSort (Set) (Type v) where
  coe A := A.toSubtype

lemma SetTheory.Set.subtype_property (A : Set) (x : A) : x.val ∈ A := x.property

-- Interesting: x is equal to its value
lemma SetTheory.Set.subtype_coe (A : Set) (x : A) : x.val = x := rfl
lemma SetTheory.Set.coe_inj (A : Set) (x y : A) : x.val = y.val ↔ x = y := Subtype.coe_inj

-- This turns a proof of x ∈ A into a cast of (x : A)
def SetTheory.Set.subtype_mk (A : Set) {x : U} (hx : x ∈ A) : A := ⟨ x, hx ⟩

-- This demonstrates that the object pre and post-casting are equal
lemma SetTheory.Set.subtype_mk_coe {A : Set} {x : U} (hx : x ∈ A) : A.subtype_mk hx = x :=
by rfl

abbrev SetTheory.Set.specify (A : Set) (P : A → Prop) : Set := SetTheory.specify A P

-- Axiom is broken into two parts

-- x ∈ S_A → x ∈ A
theorem SetTheory.Set.specification_axiom {A : Set} {P : A → Prop} {x : U}
(h : x ∈ A.specify P) :
    x ∈ A :=
  (SetTheory.specification_axiom A P).1 x h

-- if x ∈ A, then x ∈ S_A ↔ P x
theorem SetTheory.Set.specification_axiom' {A : Set} (P : A → Prop) (x : A) :
    x.val ∈ A.specify P ↔ P x :=
  (SetTheory.specification_axiom A P).2 x

theorem SetTheory.Set.specification_axiom'' {A : Set} (P: A → Prop) (x : U) :
    x ∈ A.specify P ↔ ∃ h:x ∈ A, P ⟨ x, h ⟩ := by
    -- x ∈ S_A iff there is some proof that x ∈ A, such that P x is then also true
    -- They have to use "such that" rather than "and" because P x is only defined IF
    -- x ∈ A.
  constructor
  · intro h; use specification_axiom h
    simp [←specification_axiom' P]; apply h
  · intro ⟨ h, hP ⟩
    rw [specification_axiom' P ⟨x,h⟩ ]
    exact hP


theorem SetTheory.Set.specify_subset {A:Set} (P: A → Prop) : A.specify P ⊆ A := by
  intro x hx
  rw [specification_axiom''] at hx
  obtain ⟨h, P'⟩ := hx
  exact h


/-
Definition 3.1.23 (Intersections). The intersection S1 n S2 of
two sets  consists of all the elements which belong
to both S1 and S2
-/

def SetTheory.Set.intersection (A B : Set) := A.specify (fun x ↦ x.val ∈ B)

instance SetTheory.Set.instIntersection : Inter Set where
  inter := SetTheory.Set.intersection

-- My version that uses rw and simp to avoid constructor
@[simp]
theorem SetTheory.Set.mem_inter_iff (A B : Set) (x : U) : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := by
  unfold instIntersection; simp; unfold intersection -- Get things in specify terms

  let P := fun (x : A) ↦ x.val ∈ B
  have := SetTheory.Set.specification_axiom'' P x
  simp [P] at this -- Replace specify
  rw [this]

-- Constructor method: similar to Tao
theorem SetTheory.Set.mem_inter_iff' (A B : Set) (x : U) : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := by
  let P := fun (x : A) ↦ x.val ∈ B

  constructor
  · intro h
    have hA := specification_axiom h
    simp [hA]

    apply (specification_axiom' P ⟨x, hA⟩).1
    exact h

  · intro ⟨hA, hB⟩
    apply (specification_axiom' P ⟨x, hA⟩).2
    exact hB


/-
Two sets A, B are said to be disjoint if A n B = 0
-/

def disjoint (A B : Set) := A ∩ B = ∅

/-
 (Difference sets). Given two sets A and B, we
define the set A - B or A \B to be the set A with any elements of
B removed:
-/

def difference (A B : Set) := A.specify (fun x ↦ x.val ∉ B)

-- Allows for backslash
instance SetTheory.Set.instSDiff: SDiff (Set) where
  sdiff := difference

-- I can use the exact same proof as I did for mem_inter
@[simp]
theorem SetTheory.Set.mem_sdiff (x : U) (A B:Set) : x ∈ (A \ B) ↔ (x ∈ A ∧ x ∉ B) := by
  unfold instSDiff; simp; unfold difference -- Get things in specify terms

  let P := fun (x : A) ↦ x.val ∉  B
  have := SetTheory.Set.specification_axiom'' P x
  simp [P] at this -- Replace specify
  rw [this]

/-
Proposition 3.1.28 (Sets form a boolean algebra). Let A, B, 0
be sets, and let X be a set containing A, B, C as subsets.
(a) {Minimal element) We have A U 0 =A and An 0 = 0.
(b) {Maximal element) We have A U X= X and An X= A.
(c) {Identity) We have An A= A and A U A= A.
(d) {Commutativity) We have AUB = BUA and AnB = BnA.
(e) {Associativity) We have (A U B) U C = A U (B U C) and
(An B) n C =An (B n C).
(f) {Distributivity) We have An (B u C)= (An B) U (An 0)
and A u (B n C)= (A u B) n (A u C).
(g) {Partition) We have A U (X\A) =X and An (X\A) = 0.
(h) {De Morgan laws) We have X\(A u B) = (X\A) n (X\B)
and X\(A n B)= (X\A) U (X\B).
-/



theorem SetTheory.Set.inter_comm (A B : Set) : A ∩ B = B ∩ A := by
  apply ext; intro x;
  rw [mem_inter_iff]; rw [mem_inter_iff]
  tauto -- Or is commutative


theorem SetTheory.Set.inter_empty (A : Set) : A ∩ ∅ = ∅  := by
  apply ext; intro x;
  rw [ mem_inter_iff, mem_empty_iff_false]
  tauto -- P and False is always False

theorem SetTheory.Set.empty_inter (A : Set) : ∅ ∩ A = ∅  := by
  rw [inter_comm]
  apply inter_empty


theorem SetTheory.Set.union_eq_right {A X : Set}: A ∪ X = X ↔ A ⊆ X := by
  constructor
  · intro hax x hA
    rw [← hax]
    rw [mem_union]; left; exact hA
  · intro hAX; apply ext; intro x;
    rw [mem_union]
    constructor
    · intro h
      rcases h with hA | hx
      · apply hAX x hA
      · exact hx
    · intro hx; right; exact hx

theorem SetTheory.Set.union_eq_left {A X : Set}: X ∪ A = X ↔ A ⊆ X := by
  rw [union_comm]; exact union_eq_right


theorem SetTheory.Set.inter_eq_right {A X : Set}: X ∩ A = A ↔ A ⊆ X := by
  constructor
  · intro hAX x hA
    rw [← hAX] at hA
    rw [mem_inter_iff] at hA
    exact hA.1
  · intro hAsX; apply ext; intro x
    constructor
    · intro hAX; rw [mem_inter_iff] at hAX;
      exact hAX.2
    · intro hA; rw [mem_inter_iff]
      exact ⟨ hAsX x hA, hA⟩

theorem SetTheory.Set.inter_eq_left {A X : Set}: A ∩ X = A ↔ A ⊆ X := by
  rw [inter_comm]; exact inter_eq_right


theorem SetTheory.Set.inter_self (A : Set) : A ∩ A = A := by
  apply ext; intro x;  rw [mem_inter_iff]; tauto -- Same goals on both sides

theorem SetTheory.Set.inter_assoc (A B C : Set) : A ∩ B ∩ C = A ∩ (B ∩ C) := by
  apply ext; intro x;
  rw [mem_inter_iff]; rw [mem_inter_iff];
  rw [mem_inter_iff]; rw [mem_inter_iff]
  tauto -- Logic intersection is associative
  -- I could do both ways manually, but it'd just be a bunch of casework


theorem SetTheory.Set.inter_union_distrib_left (A B C : Set) :
A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  apply ext; intro x;
  rw [mem_inter_iff, mem_union, mem_union, mem_inter_iff]
  -- Casework, but mildly more interesting
  rw [mem_inter_iff]
  constructor
  · intro ⟨ha, hbc⟩
    rcases hbc with hb | hc
    · left; apply And.intro ha hb
    · right; apply And.intro ha hc
  · intro habc
    rcases habc with hab | hac
    · constructor
      · apply hab.1
      · left; apply hab.2
    · constructor
      · apply hac.1
      · right; apply hac.2

theorem SetTheory.Set.union_inter_distrib_left (A B C : Set) :
A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  apply ext; intro x;
  rw [mem_inter_iff, mem_union, mem_union, mem_inter_iff, mem_union]
  constructor
  · intro habc
    rcases habc with ha | hbc
    · constructor <;> apply Or.inl ha
    · constructor
      · apply Or.inr hbc.1
      · apply Or.inr hbc.2
  · intro ⟨hab, hac⟩
    rcases hab with ha | hb
    · apply Or.inl ha
    · rcases hac with ha | hc
      · apply Or.inl ha
      · apply Or.inr; apply And.intro hb hc


theorem SetTheory.Set.union_compl_self {A X : Set} (hAX : A ⊆ X) : A ∪ (X \ A)  = X := by
  apply ext; intro x;  rw [mem_union, mem_sdiff]; tauto -- P and not P

theorem SetTheory.Set.inter_compl_self {A X : Set} (hAX : A ⊆ X) : A ∩ (X \ A)  = ∅ := by
  apply ext; intro x;
  rw [mem_inter_iff, mem_sdiff, mem_empty_iff_false]
  constructor
  · intro ⟨ha,hac⟩
    have hanot := hac.2
    contradiction -- x ∈ A; x ∉ A
  · tauto


theorem SetTheory.Set.compl_union {A B X:Set} (hAX: A ⊆ X) (hBX: B ⊆ X) :
    X \ (A ∪ B) = (X \ A) ∩ (X \ B) := by
  apply ext; intro x;
  rw [mem_sdiff, mem_union, mem_inter_iff, mem_sdiff, mem_sdiff]

  constructor
  · intro ⟨hX, hAB⟩
    constructor
    constructor
    · exact hX
    · contrapose! hAB; left; exact hAB
    constructor
    · exact hX
    · contrapose! hAB; right; exact hAB
  · intro ⟨hAX, hBX⟩
    constructor
    · exact hAX.left
    by_contra hAB
    rcases hAB with hA | hB
    · exact hAX.right hA
    · exact hBX.right hB

theorem SetTheory.Set.compl_inter {A B X:Set} (hAX: A ⊆ X) (hBX: B ⊆ X) :
    X \ (A ∩ B) = (X \ A) ∪ (X \ B) :=
by
  apply ext; intro x;
  rw [mem_sdiff, mem_union, mem_inter_iff, mem_sdiff, mem_sdiff]
  tauto -- I'm too lazy to do it the other way, it's basically the same


/-
Axiom 3.6 (Replacement). Let A be a set. For any object x E
A, and any object y, suppose we have a statement P(x, y) per
taining to x and y, such that for each x E A there is at most
one y for which P(x, y) is true. Then there exists a set {y
P(x, y) is true for some x EA}, such that for any object z,
-/

def partial_function {A : Set} (P : A → U → Prop) : Prop:=
  ∀ (x y1 y2), P x y1 ∧ P x y2 → y1=y2

abbrev SetTheory.Set.replace (A : Set) {P : A → U → Prop}
(hP : partial_function P) : Set :=
  SetTheory.replace A P hP

theorem SetTheory.Set.replacement_axiom {A : Set} {P : A → U → Prop}
  (hP : partial_function P) (y : U) :
    y ∈ A.replace hP ↔ ∃ x, P x y := SetTheory.replacement_axiom A P hP y

/-
Axiom 3. 7 (Infinity). There exists a set N, whose elements are
called natural numbers, as well as an object 0 in N, and an object
n-++ assigned to every natural number n E N, such that the Peano
axioms (Axioms 2.1 - 2. 5) hold.
-/

abbrev Nat := SetTheory.nat

def SetTheory.Set.nat_equiv : ℕ ≃ Nat := SetTheory.nat_equiv


/-
All of this is Tao stuff
-/
-- Below are some API for handling coercions. This may not be the optimal way to set things up.
instance SetTheory.Set.instOfNat {n:ℕ} : OfNat Nat n where
  ofNat := nat_equiv n

-- Now we can define `Nat` with a natural literal.
example : Nat := 5
example : (5 : Nat).val ∈ Nat := (5 : Nat).property

instance SetTheory.Set.instNatCast : NatCast Nat where
  natCast n := nat_equiv n

-- Now we can turn `ℕ` into `Nat`.
example (n : ℕ) : Nat := n
example (n : ℕ) : (n : Nat).val ∈ Nat := (n : Nat).property

instance SetTheory.Set.toNat : Coe Nat ℕ where
  coe n := nat_equiv.symm n

-- Now we can turn `Nat` into `ℕ`.
example (n : Nat) : ℕ := n

instance SetTheory.Object.instNatCast : NatCast Object where
  natCast n := (n:Nat).val

-- Now we can turn `ℕ` into an `Object`.
example (n: ℕ) : Object := n
example (n: ℕ) : Set := {(n: Object)}

instance SetTheory.Object.instOfNat {n:ℕ} : OfNat Object n where
  ofNat := ((n:Nat):Object)

-- Now we can define `Object` with a natural literal.
example : Object := 1
example : Set := {1, 2, 3}

@[simp]
lemma SetTheory.Object.ofnat_eq {n:ℕ} : ((n:Nat):Object) = (n:Object) := rfl

lemma SetTheory.Object.ofnat_eq' {n:ℕ} : (ofNat(n):Object) = (n:Object) := rfl

lemma SetTheory.Set.nat_coe_eq {n:ℕ} : (n:Nat) = OfNat.ofNat n := rfl

@[simp]
lemma SetTheory.Set.nat_equiv_inj (n m:ℕ) : (n:Nat) = (m:Nat) ↔ n=m  :=
  Equiv.apply_eq_iff_eq nat_equiv

@[simp]
lemma SetTheory.Set.nat_equiv_symm_inj (n m:Nat) : (n:ℕ) = (m:ℕ) ↔ n = m :=
  Equiv.apply_eq_iff_eq nat_equiv.symm

@[simp]
theorem SetTheory.Set.ofNat_inj (n m:ℕ) :
    (ofNat(n) : Nat) = (ofNat(m) : Nat) ↔ ofNat(n) = ofNat(m) := by
      convert nat_equiv_inj _ _

example : (5:Nat) ≠ (3:Nat) := by
  simp

@[simp]
theorem SetTheory.Set.ofNat_inj' (n m:ℕ) :
    (ofNat(n) : Object) = (ofNat(m) : Object) ↔ ofNat(n) = ofNat(m) := by
      simp only [←Object.ofnat_eq, Object.ofnat_eq', Set.coe_inj, Set.nat_equiv_inj]
      rfl

example : (0:Object) ≠ (1:Object) := by
  simp

@[simp]
lemma SetTheory.Set.nat_coe_eq_iff {m n : ℕ} : (m:Object) = ofNat(n) ↔ m = n := by exact ofNat_inj' m n

example (n: ℕ) : (n: Object) = 2 ↔ n = 2 := by
  simp

@[simp]
theorem SetTheory.Object.natCast_inj (n m:ℕ) :
    (n : Object) = (m : Object) ↔ n = m := by
      simp [←ofnat_eq, Subtype.val_inj]

@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe (n:ℕ) : ((n:Nat):ℕ) = n :=
  Equiv.symm_apply_apply nat_equiv n

@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe' (n:Nat) : ((n:ℕ):Nat) = n :=
  Equiv.symm_apply_apply nat_equiv.symm n

@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe'' (n:ℕ) : ((ofNat(n):Nat):ℕ) = n :=
  nat_equiv_coe_of_coe n

@[simp]
lemma SetTheory.Set.nat_coe_eq_iff' {m: Nat} {n : ℕ} : (m:Object) = (ofNat(n):Object) ↔ (m:ℕ) = ofNat(n) := by
  constructor <;> intro h <;> rw [show m = n by aesop]
  · apply nat_equiv_coe_of_coe
  · rfl

-- Previously had some weird issues with Tao's lemmas (I messed up the
-- notation priorities, I think).
-- This is why you'll later see me go out of my way to avoid using
-- numbers, and instead use ∅ and {∅} when I need two objects that are
-- definitely distinct.


/-
Exercise 3.1.5. Let A, B be sets. Show that the three statements A ~ B,
A U B = B, An B = A are logically equivalent (any one of them implies
the other two).
-/

theorem SetTheory.Set.union_eq_right' (A B : Set) :A ⊆ B ↔ A ∪ B = B := by
  exact SetTheory.Set.union_eq_right.symm

theorem SetTheory.Set.inter_eq_left' (A B : Set) : A ⊆ B ↔ A ∩ B = A := by
  exact SetTheory.Set.inter_eq_left.symm

--- This isn't a real mathlib theorem afaik
theorem SetTheory.Set.union_eq_right_iff_inter_eq_left (A B : Set) :
  A ∪ B = B ↔ A ∩ B = A := by
  rw [union_eq_right, inter_eq_left]

/-
Exercise 3.1.7. Let A, B, C be sets. Show that AnB ⊆A and AnB ⊆B.
Furthermore, show that C ⊆ A and C ⊆ B if and only if C ⊆ An B. In
a similar spirit, show that A⊆ A U Band B ⊆A U B, and furthermore
that A ⊆ C and B ⊆ C if and only if A U B ⊆ C.
-/


theorem SetTheory.Set.inter_subset_left (A B : Set) : A ∩ B ⊆ A := by
  intro x hx; rw [mem_inter_iff] at hx; apply hx.1

theorem SetTheory.Set.inter_subset_right (A B : Set) : A ∩ B ⊆ B := by
  intro x hx; rw [mem_inter_iff] at hx; apply hx.2

theorem SetTheory.Set.subset_inter_iff (A B C : Set) : A ⊆ B ∩ C ↔ A ⊆ B ∧ A ⊆ C := by
  constructor
  · intro h
    constructor
    · intro x hA
      have hBC := h x hA
      rw [mem_inter_iff] at hBC
      exact hBC.1
    · intro x hA
      have hBC := h x hA
      rw [mem_inter_iff] at hBC
      exact hBC.2
  · intro h x hA
    rw [mem_inter_iff]
    constructor
    · apply h.1 x hA
    · apply h.2 x hA


theorem SetTheory.Set.subset_union_left (A B : Set) : A ⊆ A ∪ B := by
  intro x hA; rw [mem_union]; apply Or.inl hA

theorem SetTheory.Set.subset_union_right (A B : Set) : B ⊆ A ∪ B := by
  intro x hB; rw [mem_union]; apply Or.inr hB

theorem SetTheory.Set.union_subset_iff (A B C : Set) : A ∪ B ⊆ C ↔ A ⊆ C ∧ B ⊆ C := by
  constructor
  · intro h
    constructor
    · intro x hA
      apply h
      rw [mem_union];
      apply Or.inl hA
    · intro x hB
      apply h
      rw [mem_union];
      apply Or.inr hB
  · intro ⟨hAC, hBC ⟩
    intro x hAB
    rw [mem_union] at hAB
    rcases hAB with hA | hB
    · apply hAC; apply hA
    · apply hBC; apply hB



/-
Exercise 3.1.8. Let A, B be sets. Prove the absorption laws An(AUB) :::::
A and A U (An B) = A.
-/

theorem SetTheory.Set.inf_sup_self (A B C : Set) : A ∩ (A ∪ B) = A := by
  apply ext; intro x;
  rw [mem_inter_iff, mem_union]
  constructor
  · intro h; exact h.1
  · intro hA;

    constructor
    · apply hA
    · apply Or.inl hA

theorem SetTheory.Set.sup_inf_self (A B C : Set) : A ∪ (A ∩ B) = A := by
  apply ext; intro x;
  rw [mem_union,mem_inter_iff]
  constructor
  · intro h
    rcases h with hA | hAB
    · apply hA
    · apply hAB.1
  · intro hA; apply Or.inl hA


/-
Exercise 3.1.9. Let A, B, X be sets such that AUB =X and AnB = 0.
Show that A = X\B and B = X\A.
-/

--- Can't find a mathlib name for this

theorem SetTheory.Set.partition_left {A B X : Set} (h1 : A ∪ B = X) (h2 : A ∩ B = ∅) :
A = X \ B := by
  apply ext; intro x;
  simp
  constructor
  · intro hA
    constructor
    · rw [← h1]
      rw [mem_union]
      apply Or.inl hA
    · intro hB
      rw [← mem_empty_iff_false x]
      rw [← h2]
      simp
      apply And.intro hA hB
  · intro ⟨ hX, hB' ⟩
    rw [← h1] at hX
    rw [mem_union] at hX
    rcases hX with hA | hB
    · exact hA
    · contradiction

theorem SetTheory.Set.partition_right {A B X : Set} (h1 : A ∪ B = X) (h2 : A ∩ B = ∅) :
  B = X \ A := by
  rw [union_comm] at h1
  rw [inter_comm] at h2
  apply partition_left h1 h2

/-
Exercise 3.1.10. Let A and B be sets. Show that the three sets A\B,
A n B, and B\A are disjoint, and that their union is A U B.
-/

theorem SetTheory.Set.disjoint_sdiff_inter {A B : Set} : disjoint (A \ B) (A ∩ B) := by
  apply ext; intro x;
  rw [mem_empty_iff_false]
  rw [mem_inter_iff, mem_sdiff, mem_inter_iff ]
  simp
  tauto

theorem SetTheory.Set.disjoint_sdiff_sdiff {A B : Set} : disjoint (A \ B) (B \ A) := by
  apply ext; intro x;
  rw [mem_empty_iff_false]
  simp
  tauto

theorem SetTheory.Set.union_eq_diff_union_diff_union_inter {A B : Set} :
  A ∪ B = (A \ B) ∪ (B \ A) ∪ (A ∩ B) := by
  apply ext; intro x;
  repeat rw [mem_union]
  constructor
  · intro hAB
    rcases hAB with hA | hB
    · by_cases hB: x ∈ B
      · right; simp; apply And.intro hA hB
      · left; left; simp; apply And.intro hA hB
    · by_cases hA : x ∈ A
      · right; simp; apply And.intro hA hB
      · left; right; simp; apply And.intro hB hA
  · intro hAB
    simp at hAB
    rcases hAB with h2 | hAB -- A bit weird that rcases doesn't work; oh well
    · rcases h2 with hA | hB
      · apply Or.inl hA.1
      · apply Or.inr hB.1
    · apply Or.inl hAB.1

-- This one doesn't seem to be a real mathlib theorem

theorem SetTheory.Set.disjoint_inter_sdiff {A B : Set} : disjoint (B \ A) (A ∩ B) := by
  rw [inter_comm]
  apply disjoint_sdiff_inter



/-
Exercise 3.1.11. Show that the axiom of replacement implies the axiom
of specification.
-/
theorem SetTheory.Set.specification_from_replacement {A:Set} {P: A → Prop} :
    ∃ B, B ⊆ A ∧ ∀ x, x.val ∈ B ↔ P x := by
    let Q := fun (x : A) (y : U) ↦ (x=y) ∧ (P x)
    have hQ: partial_function Q := by
      unfold partial_function
      rintro x y1 y2 ⟨Q1, Q2⟩
      unfold Q at *
      rw [← Q1.left, ← Q2.left]
    use replace A hQ

    constructor
    · intro y hy
      rw [replacement_axiom] at hy
      obtain ⟨x, hx⟩ := hy
      obtain ⟨hxy, hP⟩:= hx
      rw [← hxy]
      exact x.property
    · intro y -- Given that y ∈ A
      constructor
      · intro hyR
        rw [replacement_axiom] at hyR  -- y ∈ Replace will give us x ∈ A, P x
        obtain ⟨x, ⟨hxy, hPx⟩⟩ := hyR

        -- Lean requires us to be careful about the difference between
        -- (x : A) vs (x : U). So, we convert all things to (x y : A)
        -- Since our expressions are written in subtype land.
        have:= (coe_inj _ y x).1 hxy.symm

        rw [this] -- x, from our original function, has property P x.
        exact hPx -- So its identical counterpart in replace must have P y.

      · intro hPy -- If we know P y
        rw [replacement_axiom] -- Then we know P y must be in the replace function
        use y -- Since (y : A) is already satisfied by the premise.



/-
I will continue using Tao's version of set theory for the rest of the chapter.
I like it a lot more than mine.-/




--------------- SECTION 3.2


/-
This section was difficult to structure in my original format.
I might have even had access to universal specification within my type U?
Unclear.

Tao's structure makes this easier to conceive of and work through.

I guess that Lean protects itself via the type hierarchy: preventing a type of all
types, among other things.
-/

-- I'll try implementing this section myself, and take references from
-- Tao wherever I get stuck.

/-
Axiom 3.8 (Universal specification). (Dangerous!) Suppose for
every object x we have a property P(x) pertaining to x (so that
for every x, P(x) is either a true statement or a false statement).
Then there exists a set { x : P( x) is true} such that for every object
y,
yE {x: P(x) is true} {::=:::> P(y) is true.
-/

abbrev universal_specification: Prop :=
∀ (P : U → Prop), ∃ (C : Set), ∀ (x : U), x ∈ C ↔ P x

/-
The paradox runs as follows. Let P(x) be
the statement
P(x) {::=:::> "xis a set, and x ~ x";
-/

theorem russells_paradox : ¬ universal_specification := by
  let P := fun (x : Object) ↦ ∃ (X : Set), x = X ∧ x ∉ X
  intro h
  have hbadset := h P
  obtain ⟨B, hB⟩ := hbadset
  by_cases hcontra: (B : Object) ∈ B
  · have := ( hB B ).1 hcontra -- If B ∈ B, then P B
    unfold P at this
    obtain ⟨X, hBX, hBnotX⟩ := this -- P B says that B ∉ B
    simp at hBX
    rw [← hBX] at hBnotX
    contradiction -- It both is and isn't in itself!

  · apply hcontra -- We're gonna show that B ∈ B, despite B ∉ B
    apply (hB (SetTheory.set_to_object B)).2 -- So, we need to show that P B
    unfold P -- But P B is exactly the fact that B ∉ B
    use B -- We get our desired contradiction


/-
Axiom 3.9 (Regularity). If A is a non-empty set, then there is
at least one element x of A which is either not a set, or is disjoint
from A.
-/

theorem SetTheory.Set.axiom_of_regularity {A:Set} (h: A ≠ ∅) :
    ∃ x : A, ∀ S:Set, x.val = S → disjoint S A :=
by
  obtain ⟨ x, h, h' ⟩ := SetTheory.regularity_axiom A (nonempty_def.1 h)
  use ⟨x, h⟩
  intro S hS
  specialize h' S hS -- Directly cribbing from Tao but I'm curious about specialize

  -- Disjoint is equivalent to not allowing membership in both
  dsimp [disjoint]
  push_neg at h'
  apply ext; intro x
  rw [mem_empty_iff_false]
  simp -- x ∈ P ↔ x ∈ ∅ can be reduced to x ∉ P
  contrapose! -- Make the two definitions match up
  exact h' x -- aesop apparently also works?



/-
Exercise 3.2.1. Show that the universal specification axiom, Axiom 3.8,
if assumed to be true, would imply Axioms 3.2, 3.3, 3.4, 3.5, and 3.6. (If
we assume that all natural numbers are objects, we also obtain Axiom
3.7.)
-/

-- Axiom 3.2
theorem SetTheory.Set.emptyset_exists (h: universal_specification):
    ∃ (X : Set), ∀ x, x ∉ X :=
by
  let P : U → Prop:= fun x ↦ False
  obtain ⟨empty, hempty⟩ := h P
  use empty
  unfold P at hempty
  simp at hempty
  exact hempty

-- Axiom 3.3
theorem SetTheory.Set.singleton_exists (h: universal_specification) (x : U):
    ∃ (X : Set), ∀ (y : U), y ∈ X ↔ y=x :=
by
  let P : U → Prop:= fun y ↦ y = x
  obtain ⟨single, hsingle⟩ := h P
  use single

theorem SetTheory.Set.pair_exists (h: universal_specification) (x1 x2:Object):
    ∃ (X:Set), ∀ y, y ∈ X ↔ y = x1 ∨ y = x2 :=
by
  let P : U → Prop:= fun y ↦ y = x1 ∨ y = x2
  obtain ⟨pair, hpair⟩ := h P
  use pair

-- Axiom 3.4
theorem SetTheory.Set.pair_union_exists (h: universal_specification) (A B : Set):
    ∃ (X : Set), ∀ (x : U), x ∈ X ↔ x ∈ A ∨ x ∈ B :=
by
  let P : U → Prop:= fun x ↦ x ∈ A ∨ x ∈ B
  obtain ⟨union, hunion⟩ := h P
  use union

-- Axiom 3.5
theorem SetTheory.Set.specify_exists (h : universal_specification) (A : Set)
(P : A → Prop):
    ∃ (X : Set), ∀ (x : U), x ∈ X ↔ ∃ (h : x ∈ A), P ⟨x, h⟩ := by
  let P : U → Prop := fun x ↦ ∃ (h : x ∈ A), P ⟨x, h⟩
  obtain ⟨specify, hspecify⟩ := h P
  use specify

-- Axiom 3.6
theorem SetTheory.Set.replace_exists (h : universal_specification) (A : Set)
(P : A → U → Prop) (hP : partial_function P):
  ∃ (X : Set), ∀ (y : U), y ∈ X ↔ (∃ (x : A), P x y ) := by
  let P : U → Prop := fun y ↦ ∃ (x : A), P x y
  obtain ⟨replace, hreplace⟩ := h P
  use replace

/-
Exercise 3.2.2. Use the axiom of regularity (and the singleton set axiom)
to show that if A is a set, then A f/. A. Furthermore, show that if A and
Bare two sets, then either A f/. B orB f/. A (or both).
-/

theorem SetTheory.Set.not_mem_self (A : Set) : (A : U) ∉ A := by
  intro h
  let Asing := ({(A : U)} : Set)
  have hnonempty: Asing ≠ ∅ := by
    rw [nonempty_def]; use A; rw [mem_singleton]

  obtain ⟨x,hx⟩ := axiom_of_regularity hnonempty
  specialize hx A
  contrapose! hx

  constructor
  · rw [← mem_singleton]
    apply x.property
  · rw [disjoint]
    push_neg
    rw [nonempty_def]
    use set_to_object A
    simp
    constructor
    · exact h
    · rw [mem_singleton]

theorem SetTheory.Set.not_mem_mem (A B:Set) : (A:U) ∉ B ∨ (B:U) ∉ A :=
by
  by_contra h
  push_neg at h
  obtain ⟨hAB, hBA⟩ := h

  -- We'll show that {A,B} overlaps with both A and B
  let AB := ({(A:U)}:Set) ∪ ({(B:U)}: Set)
  have: AB ≠ ∅ := by rw [nonempty_def]; unfold AB; simp
  have := axiom_of_regularity this

  -- Unpacking
  unfold disjoint at this
  obtain ⟨x, hx⟩ := this
  have := x.property
  unfold AB at this; simp at this

  -- We check A and B respectively
  rcases this with hA | hB
  · specialize hx A hA
    contrapose! hx
    rw [nonempty_def]
    use B; simp
    constructor
    · exact hBA -- B ∈ A
    · unfold AB; simp -- B ∈ {A,B}

  · specialize hx B hB
    contrapose! hx
    rw [nonempty_def]
    use A; simp
    constructor
    · exact hAB -- A ∈ B
    · unfold AB; simp -- A ∈ {A,B}

/-
Exercise 3.2.3. Show (assuming the other axioms of set theory) that
the universal specification axiom, Axiom 3.8, is equivalent to an axiom
postulating the existence of a "universal set" n consisting of all objects
(i.e., for all objects x, we have x E 0). In other words, if Axiom 3.8 is
true, then a universal set exists, and conversely, if a universal set exists,
then Axiom 3.8 is true.
-/

/-
theorem SetTheory.Set.specification_axiom'' {A : Set} (P: A → Prop) (x : U) :
    x ∈ A.specify P ↔ ∃ h:x ∈ A, P ⟨ x, h ⟩ := by

theorem SetTheory.Set.specification_axiom' {A : Set} (P : A → Prop) (x : A) :
  x.val ∈ A.specify P ↔ P x :=
    -/

theorem SetTheory.Set.univ_iff:
  universal_specification ↔ ∃ (V : Set), ∀ (x : U), x ∈ V := by
  unfold universal_specification
  constructor
  · intro h
    specialize h (fun x ↦ True) -- Universal set: just specify the set with all elements
    simp at h
    exact h
  · intro h P -- Take the universal set, and specialize it down to any desired level
    obtain ⟨V, hV⟩ := h
    let P' :(V → Prop):= fun x ↦ P x
    let S:= specify V P'
    use S
    intro x
    unfold S
    let z : V := ⟨x, hV x⟩ -- Cast x into V subtype
    constructor
    · intro h
      apply (specification_axiom' P' z).1 --Specification axiom: get P from specify P
      apply h
    · intro h
      apply (specification_axiom' P' z).2 -- Get specify P from P
      apply h


theorem SetTheory.Set.no_univ : ¬ ∃ (U:Set), ∀ (x:Object), x ∈ U := by
  by_contra h
  obtain ⟨V, hV⟩ := h
  specialize hV V
  apply not_mem_self V hV -- We have V ∈ V but also V ∉ V



--------------- SECTION 3.3

--- We start off using Tao's constructions: I've found that they tend to
--- work better with Lean, and I don't know Lean well enough to make similarly good
--- constructions yet.

@[ext]
structure Function (X Y: Set) where
  P : X → Y → Prop
  unique : ∀ x: X, ∃! y: Y, P x y

--- Create a Lean function from a Tao function
noncomputable def Function.to_fn {X Y: Set} (f: Function X Y) : X → Y :=
  fun x ↦ (f.unique x).choose

--- Use this to coerce Tao functions into Lean functions
noncomputable instance Function.inst_coefn (X Y: Set) : CoeFun (Function X Y) (fun _ ↦ X → Y) where
  coe := Function.to_fn

--- They're the same!
theorem Function.to_fn_eval {X Y: Set} (f: Function X Y) (x:X) : f.to_fn x = f x := rfl

-- Make a Tao function from a Lean function
abbrev Function.mk_fn {X Y: Set} (f: X → Y) : Function X Y :=
  Function.mk (fun x y ↦ y = f x) (by simp) -- by simp provides the uniqueness proof

-- I have no idea how this works but given that it involves
-- choice and constructivism, it's way outside my playing field I think
theorem Function.eval {X Y: Set} (f: Function X Y) (x: X) (y: Y) : y = f x ↔ f.P x y :=
by convert ((f.unique x).choose_iff y).symm

-- I guess this is what allows us to later casually
-- resolve straightforward functions
@[simp]
theorem Function.eval_of {X Y: Set} (f: X → Y) (x:X) : (Function.mk_fn f) x = f x :=
by symm; rw [eval]

/-
Definition 3.3. 7 (Equality offunctions). Two functions f :X ---t
Y, g : X ---t Y with the same domain and range are said to be
equal, f = g, if and only if f(x) = g(x) for all x E X. (If f(x)
and g(x) agree for some value$ of x, but not others, then we do
not consider f and g to be equal2.)
-/

theorem Function.eq_iff {X Y: Set} (f g: Function X Y) : f = g ↔ ∀ x: X, f x = g x :=
by
  constructor <;> intro h
  · rw [h]; intro x; rfl -- or just simp
  · ext x y
    constructor <;> intro
    · rwa [← eval, ← h x, eval]
    · rwa [← eval,   h x, eval]

/-
Definition 3.3.10 (Composition). Let f: X-+ Y and g: Y-+ Z
be two functions, such that the range off is the same set as the
domain of g. We then define the composition go f : X -+ Z of the
two functions g and f to be the function defined explicitly by the
formula
(go f)(x) := g(f(x)).
-/

--noncomputable because of choice, I presume?
noncomputable abbrev Function.comp {X Y Z: Set} (g: Function Y Z)
(f: Function X Y) :
    Function X Z :=
  Function.mk_fn (fun x ↦ g (f x))

-- `∘` is already taken in Mathlib for the composition of Mathlib functions,
-- so we use `○` here instead to avoid ambiguity.
infix:90 "○" => Function.comp
theorem Function.comp_eval {X Y Z: Set} (g: Function Y Z) (f: Function X Y) (x: X) :
    (g ○ f) x = g (f x) := Function.eval_of _ _

theorem Function.comp_eq_comp {X Y Z: Set} (g: Function Y Z) (f: Function X Y) :
    (g ○ f).to_fn = g.to_fn ∘ f.to_fn :=
by
  ext; simp only [Function.comp_eval,
                  Function.comp_apply] -- Not sure where this comes from

/-
Lemma 3.3.12 (Composition is associative). Let f: X-+ Y, g:
Y-+ Z, and h: Z ~ W be functions. Then fo(goh) =(fog) oh.
-/
theorem SetTheory.Set.comp_assoc {W X Y Z: Set}
(h: Function Y Z) (g: Function X Y)(f: Function W X) :
h ○ (g ○ f) = (h ○ g) ○ f := by
  rw [Function.eq_iff]
  intro x
  repeat rw [Function.comp_eval]

/-
Definition 3.3.14 (One-to-one functions). A function f is one
to-one (or injective) if different elements map to different elements:
-/

-- Injectivity
abbrev Function.one_to_one {X Y: Set} (f: Function X Y) : Prop :=
∀ x x': X, x ≠ x' → f x ≠ f x'

theorem Function.one_to_one_iff {X Y: Set} (f: Function X Y) :
    f.one_to_one ↔ ∀ x x': X, f x = f x' → x = x' := by
    unfold one_to_one
    constructor <;> intro h x1 x2;
    · contrapose!;apply h
    · contrapose!;apply h

theorem Function.one_to_one_iff' {X Y: Set} (f: Function X Y) :
    f.one_to_one ↔ Function.Injective f.to_fn :=
by
  rw [one_to_one_iff, Function.Injective]


/-
Definition 3.3.1 7 (Onto functions). A function f is onto (or sur
jective) if f(X) = Y, i.e., every element in Y comes from applying
f to some element in X:
For every y E Y, there exists x E X such that f ( x) = y.
-/

-- Surjectivity
abbrev Function.onto {X Y : Set} (f: Function X Y) :=
  ∀ (y : Y), ∃ (x : X), f x = y

theorem Function.onto_iff {X Y: Set} (f: Function X Y) :
f.onto ↔ Function.Surjective f.to_fn := by rfl



abbrev Function.bijective {X Y : Set} (f: Function X Y) :=
  onto f ∧ one_to_one f

abbrev Function.inverse {X Y: Set} (f: Function X Y) (h: f.bijective) :
    Function Y X :=
  Function.mk (fun y x ↦ f x = y) (by
    intro y
    obtain ⟨x, hx⟩ := h.1 y -- Get an x value that maps to y
    use x; simp
    constructor
    · exact hx
    · have := (one_to_one_iff f).1 h.2
      intro x' hx'
      let z : X := ⟨x',hx'⟩
      change f.to_fn z = y → z = x
      rw [← hx]
      apply this
  )

theorem Function.inverse_eval {X Y: Set} {f: Function X Y} (h: f.bijective) (y: Y) (x: X) :
    x = (f.inverse h) y ↔ f x = y := Function.eval _ _ _

/-
Exercise 3.3.1. Show that the definition of equality in Definition 3.3.7 is
reflexive, s:rmmetric, and transitive. Also verify the substitution proP:.
erty: if f, f : X -+ Y an_9. g, g : Y -+ Z are functions such that f = f
and g = g, then f o g = f o g.
-/

theorem Function.refl {X Y : Set}(f : Function X Y) : f = f := by
  rw [Function.eq_iff]; intro x; rfl

theorem Function.symm {X Y : Set}(f g : Function X Y) : f=g ↔ g=f := by
  rw [Function.eq_iff]; rw [Function.eq_iff]
  constructor <;> intro h
  · intro x; rw [h]
  · intro x; rw [h]

theorem Function.trans {X Y: Set}(f g h : Function X Y)
(hfg: f = g) (hgh: g=h): f = h := by
  rw [Function.eq_iff] at *
  intro x
  rw [hfg]
  rw [hgh]

theorem Function.comp_congr {X Y Z:Set} {f f': Function X Y} (hff': f = f') {g g': Function Y Z}
  (hgg': g = g') : g ○ f = g' ○ f' := by
  rw [Function.eq_iff] at *
  intro x
  repeat rw [Function.comp_eval]
  rw [hff']
  rw [hgg' (f'.to_fn x)]

/-
Exercise 3.3.2. Let f : X -+ Y and g : Y -+ Z be functions. Show that
if J and g are both injective, then so is go f; similarly, show that if f
and g are both surjective, then so is g o f.
-/

theorem Function.comp_of_inj {X Y Z : Set} (f : Function X Y)
(g: Function Y Z) (hf: f.one_to_one) (hg: g.one_to_one):
(g ○ f).one_to_one:= by -- x1 and x2 stay split by injection as we go forward
  unfold one_to_one at *
  intro x1 x2 h12
  repeat rw [Function.comp_eval]
  apply hg
  apply hf
  apply h12

theorem Function.comp_of_surj {X Y Z : Set} (f : Function X Y)
(g: Function Y Z) (hf: f.onto) (hg: g.onto) :
(g ○ f).onto := by -- z has a guaranteed g(y)=z, y has guaranteed f(x)=y
  unfold onto at *
  intro z
  obtain ⟨y, hy⟩ := hg z
  obtain ⟨x, hx⟩ := hf y
  use x
  repeat rw [Function.comp_eval]
  rw [hx, hy]


/-
Exercise 3.3.3. When is the empty function injective? surjective? bijec
tive?
-/

abbrev SetTheory.Set.empty_function (X:Set) : Function (∅:Set) X :=
  Function.mk (fun _ _ ↦ True) (
by intro ⟨ x,hx ⟩; simp at hx)

theorem type_empty_false (x : (∅ : Set)): False := by
  apply SetTheory.Set.notMem_empty x
  apply x.property


lemma emptyfunc_one_to_one (X: Set) : (SetTheory.Set.empty_function X).one_to_one :=
by
  intro x; exfalso; apply type_empty_false x

example (X: Set) : (SetTheory.Set.empty_function X).onto ↔ ((∅:Set) = X):=
by
  unfold Function.onto
  constructor
  · intro h; symm
    by_contra hcontra
    change X ≠ (∅: Set) at hcontra
    rw [SetTheory.Set.nonempty_def] at hcontra -- If X ≠ ∅, then x ∈ X

    obtain ⟨x,hx⟩ := hcontra
    let z : X := ⟨x,hx⟩
    specialize h z
    obtain ⟨w,hw⟩ := h -- We retrieve f(w)=y by surjectivity
    apply type_empty_false w

  · intro h; rw [← h]; intro y -- ∅ has no element y: vacuous surjectivity
    exfalso; apply type_empty_false y


/-
Exercise 3.3.4. In this section we give some cancellation laws for com
position. Let f : X -+ Y, J : X -+ _Y, g : Y -+ Z, and g : Y -+ ~ be
functions. Show that if g o f = g o f and g is injective, then f = f. Is
the same statement true if g is not injective? Show that if go f =go f
and· f is surjective, then g = g. Is the same statement true if f is not
surjective?
-/

theorem Function.comp_cancel_left {X Y Z:Set} {f f': Function X Y} {g : Function Y Z}
(heq : g ○ f = g ○ f') (hg: g.one_to_one) : f = f' := by
  rw [Function.eq_iff] at *
  rw [Function.one_to_one_iff] at hg -- Injectivity

  intro x -- Get any particular x
  specialize heq x -- We know that g(f(x))=g(f'(x))
  repeat rw [Function.comp_eval] at heq
  apply hg   -- Injectivity allows us to match inputs (f and f')
  exact heq  -- based on matching output (gf and gf')

theorem Function.comp_cancel_right {X Y Z:Set} {f: Function X Y} {g g': Function Y Z}
(heq : g ○ f = g' ○ f) (hf: f.onto) : g = g' :=by
  rw [Function.eq_iff] at *
  unfold Function.onto at hf

  intro y
  specialize hf y -- Can grab some x: f x = g
  obtain ⟨x,hx⟩ := hf
  repeat rw [← hx]
  specialize heq x
  repeat rw [Function.comp_eval] at heq
  exact heq

-- the first line of this construction should be either `apply isTrue` or `apply isFalse`.




/-
I was originally going to use 1 and 2, but
without Tao API above that seems to be broken, so I removed it
(probably because I'm not importing all of tactics/analysis),
and it turns out it's hard to prove 1 ≠ 2 when they have Object type

So, instead we'll use two distinct objects I know how to work with.

Update: I fixed Tao's API (the issue was probably priorities for
different types for ofNat). I'm not gonna change this because
1. I'm too lazy to fix it and 2. it's kinda funny.-/
abbrev empty : Set := ∅
abbrev emptyU : U := empty

abbrev eempty : Set := {emptyU}
abbrev eemptyU : U := eempty

theorem empty_ne_eempty: empty ≠ eempty:= by
  symm
  rw [SetTheory.Set.nonempty_def]
  use empty; simp

theorem emptyU_ne_eemptyU: emptyU ≠ eemptyU := by
  intro h
  rw [SetTheory.Set.coe_eq_iff] at h -- Convert to Set
  contrapose! h; apply empty_ne_eempty -- False claim

theorem emp_ne_eemp {X : Set} {he : emptyU ∈ X} {hee : eemptyU ∈ X} :
(⟨emptyU, he⟩ : X) ≠ (⟨eemptyU, hee⟩ : X) := by
  intro h
  rw [← SetTheory.Set.coe_inj X (⟨emptyU, he⟩ : X) (⟨eemptyU, hee⟩ : X)] at h -- Convert to Object
  contrapose! h
  apply emptyU_ne_eemptyU

def Function.comp_cancel_left_without_hg : Decidable (∀ (X Y Z:Set)
(f f': Function X Y) (g : Function Y Z) (heq : g ○ f = g ○ f'), f = f') := by
  apply isFalse; push_neg
  let A := ({emptyU}∪{eemptyU}: Set)
  let emp : A := ⟨emptyU, by unfold A; simp⟩
  let eemp : A := ⟨eemptyU, by unfold A; simp⟩
  let f  : A → A := fun x ↦ emp
  let f' : A → A := fun x ↦ eemp
  let g  : A → A := fun x ↦ emp

  let F  := mk_fn f
  let F' := mk_fn f'
  let G  := mk_fn g

  use A; use A; use A; use F; use F'; use G
  rw [Function.eq_iff] at *

  constructor
  · intro x
    repeat rw [Function.comp_eval]
    rw [Function.eval_of f x, Function.eval_of f' ]
    unfold f; unfold f' -- Doesn't matter what x is, f and f' are constant functions
    unfold G; unfold g; simp -- And g is a constant function as well

  · intro h -- We show they're not equal by comparing their outputs
    rw [Function.eq_iff] at h
    specialize h emp
    unfold F f F' f' at h; simp at h

    exact emp_ne_eemp h

def Function.comp_cancel_right_without_hg : Decidable (∀ (X Y Z:Set)(f: Function X Y) (g g': Function Y Z) (heq : g ○ f = g' ○ f), g = g') :=by
  apply isFalse; push_neg
  let A := ({emptyU}∪{eemptyU}: Set)
  let emp : A := ⟨emptyU, by unfold A; simp⟩
  let eemp : A := ⟨eemptyU, by unfold A; simp⟩
  let f  : A → A := fun x ↦ emp
  let g : A → A := fun x ↦ emp
  let g' : A → A := fun x ↦ x

  let F  := mk_fn f
  let G  := mk_fn g
  let G' := mk_fn g'

  use A; use A; use A; use F; use G; use G'
  rw [Function.eq_iff] at *

  constructor
  · intro x; repeat rw [Function.comp_eval]
    rw [Function.eval_of f x, Function.eval_of g]
    unfold f -- Always returns emp
    unfold g; rw [Function.eval_of g'] -- Both return emp
  · intro h; rw [Function.eq_iff] at h
    specialize h eemp
    unfold G G' at h; simp at h
    unfold g g' at h -- They're different at input eemp

    exact emp_ne_eemp h



/-
Exercise 3.3.5. Let f : X -+ Y and g : Y -+ Z be functions. Show that
if g o f is injective, then f must be injective. Is it true that g must also
be injective? Show that if go f is surjective, then g must be surjective.
Is it true that f must also be surjective?
-/

theorem Function.comp_injective {X Y Z:Set} {f: Function X Y} {g : Function Y Z}
(hinj : (g ○ f).one_to_one) : f.one_to_one := by
  rw [one_to_one_iff] at *
  intro x1 x2 hf; specialize hinj x1 x2
  apply hinj
  repeat rw [Function.comp_eval]
  rw [hf]

theorem Function.comp_surjective {X Y Z:Set} {f: Function X Y} {g : Function Y Z}
(hinj : (g ○ f).onto) : g.onto := by
  unfold onto at *
  intro z; specialize hinj z
  obtain ⟨x,hx⟩:=  hinj
  rw [Function.comp_eval] at hx
  use f.to_fn x

def Function.comp_injective' : Decidable (∀ (X Y Z:Set) (f: Function X Y) (g : Function Y Z) (hinj :
    (g ○ f).one_to_one), g.one_to_one) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isFalse; push_neg
  let A := empty
  let B := ({emptyU}∪{eemptyU}: Set)
  let emp : B := ⟨emptyU, by unfold B; simp⟩
  let eemp : B := ⟨eemptyU, by unfold B; simp⟩
  let g : B → B := fun x ↦ emp

  let F  := SetTheory.Set.empty_function B
  let G  := mk_fn g

  use A; use B; use B; use F; use G
  constructor -- Empty set input: injective!
  · intro x; exfalso; apply type_empty_false x
  · unfold one_to_one; push_neg
    use emp; use eemp

    constructor
    · intro h
      exact emp_ne_eemp h
    · rfl -- It's a constant function

def Function.comp_surjective' : Decidable (∀ (X Y Z:Set) (f: Function X Y) (g : Function Y Z) (hinj :
    (g ○ f).onto), f.onto) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isFalse; push_neg
  let A := ({emptyU} : Set)
  let B := ({emptyU}∪{eemptyU}: Set)
  let empA : A := ⟨emptyU, by unfold A; simp⟩
  let empB : B := ⟨emptyU, by unfold B; simp⟩
  let eempB : B := ⟨eemptyU, by unfold B; simp⟩
  let f  : A → B := fun x ↦ empB
  let g  : B → A := fun x ↦ empA

  let F  := mk_fn f
  let G  := mk_fn g

  use A; use B; use A; use F; use G

  constructor
  · unfold onto; intro y; unfold A at y
    have := y.property
    rw [SetTheory.Set.mem_singleton] at this
    use empA; rw [Function.comp_eval];
    unfold F f; simp -- empA => empB
    unfold G g; simp -- empB => empA
    rw [← SetTheory.Set.coe_inj]
    symm; apply this

  · unfold onto; push_neg
    use eempB; intro x
    unfold F f; simp; intro h
    exact emp_ne_eemp h

/-
Exercise 3.3.6. Let f : X -+ Y be a bijective function, and let f-1 :
Y-+ X be its inverse. Verify the cancellation laws f-1(/(x)) = x for
all x EX and f(f-1(y)) = y for ally E Y. Conclude that f-1 is also
invertible, and has f as its inverse (thus u-1)-1 =f).
-/

@[simp]
theorem Function.inverse_comp_self {X Y : Set} (f : Function X Y)
(hf: f.bijective) (x: X): (f.inverse hf) (f x) = x := by
  let y := f x
  have:= f.inverse_eval hf y x
  unfold y at this
  symm; apply this.2
  rfl

@[simp]
theorem Function.self_comp_inverse {X Y : Set} (f : Function X Y)
(hf: f.bijective) (y: Y): f ((f.inverse hf) y)  = y := by
  let x := (f.inverse hf) y
  have := f.inverse_eval hf y x
  unfold x at this
  apply this.1
  rfl

theorem Function.inverse_bijective {X Y : Set} (f : Function X Y)
(hf: f.bijective): (f.inverse hf).bijective := by
  constructor
  · unfold onto; intro x;
    let y := f x
    use y
    have := f.inverse_eval hf y x
    symm; apply this.2; simp [y]
  · rw [one_to_one_iff]
    intro y1 y2 h12
    let x := (f.inverse hf) y1
    have := f.inverse_eval hf y2 x
    apply this.1 at h12
    rw [← h12]
    unfold x;
    simp

theorem Function.inverse_inverse {X Y : Set} (f : Function X Y)
(hf: f.bijective):
(f.inverse hf).inverse (f.inverse_bijective hf) = f := by
  rw [Function.eq_iff]; intro x -- (f⁻¹)⁻¹ x = f x
  have := (f.inverse_bijective hf).2 -- f_inverse is injective
  rw [one_to_one_iff] at this
  apply this; -- f⁻¹ (f⁻¹)⁻¹ x = f⁻¹ f x
  rw [inverse_comp_self] -- Cancel out f⁻¹ f
  rw [self_comp_inverse] -- Cancel out f⁻¹ (f⁻¹)⁻¹ -- Could instead use simp

theorem Function.inverse_inverse' {X Y : Set} (f : Function X Y)
(hf: f.bijective):
(f.inverse hf).inverse (f.inverse_bijective hf) = f := by
  rw [Function.eq_iff]; intro x -- (f⁻¹)⁻¹ x = f x
  -- Move (f⁻¹)⁻¹ to the other side: (f⁻¹)⁻¹ x = y ↔ x = f⁻¹ y
  let y := f x
  have := (f.inverse hf).inverse_eval (f.inverse_bijective hf)
  have := this x y
  symm; apply this.2
  -- Cancel
  unfold y; simp


/-
Exercise 3.3. 7. Let f : X -+ Y and g : Y -+ Z be functions. Show that if
f and g are bijective, then so is go f, and we have (go f) - 1 = f-1 o g-1.
-/

--
theorem Function.comp_bijective {X Y Z: Set} {f : Function X Y}
{g : Function Y Z} (hf : f.bijective) (hg : g.bijective) :
(g ○ f).bijective := by
  unfold bijective at *
  constructor
  · apply comp_of_surj _ _ hf.1 hg.1
  · apply comp_of_inj _ _ hf.2 hg.2

theorem Function.inv_of_comp {X Y Z : Set} (f : Function X Y)
(g : Function Y Z) (hf : f.bijective) (hg : g.bijective) :
(g ○ f).inverse (Function.comp_bijective hf hg) =
(f.inverse hf) ○ (g.inverse hg) := by
  rw [Function.eq_iff]; intro z;
  rw [Function.comp_eval]

  let x := (f.inverse hf) ((g.inverse hg) z)
  --(g ○ f)⁻¹ z = x
  have := (g ○ f).inverse_eval (Function.comp_bijective hf hg)
  have := this z x --
  symm; apply this.2 -- z = (g ○ f) x

  -- Now, we just cancel out g f f⁻¹ g⁻¹  = gg⁻¹ = i
  rw [Function.comp_eval]; unfold x
  simp




/-

Exercise 3.3.8. If X is a subset ofY, let tx-.Y: X-+ Y be the inclusion
map from X to Y, defined by mapping x ~---+ x for all x E X, i.e.,
tx-.y(x) := x for all x EX. The map tx-x is in particular called the
identity map on X.
•
(a) Show that if X~ Y ~ Z then ty-.z o £X-+Y = tx-z.
(b) Show that if f : A -+ B is any function, then f = f o £A-.A =
£B-+B 0 f.
(c) Show that, if f : A -+ B is a bijective function, then f o f-1 =
£B-.B and /-1 of= £A-+A•
(d) Show that if X and Y are disjoint sets, and f : X -+ Z and
g : Y -+ Z are functions, then there is a unique function h
X U Y-+ Z such that h o tx-+XUY = f and h o £Y-+XUY =g.
-/
-/

-- Preserves identity, but converts type from X to Y
abbrev Function.inclusion {X Y:Set} (h: X ⊆ Y) : Function X Y :=
    Function.mk_fn (fun x ↦ ⟨ x.val, h x.val x.property ⟩ )

abbrev Function.id (X:Set) : Function X X := Function.mk_fn (fun x ↦ x)

theorem Function.inclusion_id (X:Set) :
Function.inclusion (SetTheory.Set.subset_self X) = Function.id X := by
    let inc := Function.inclusion (SetTheory.Set.subset_self X)
    let idd := Function.id X

    have := Function.eq_iff inc idd
    apply this.2
    intro x
    unfold inc idd inclusion id
    simp only [mk_fn] -- They're the same function

theorem Function.inclusion_id' (X:Set) :
Function.inclusion (SetTheory.Set.subset_self X) = Function.id X := by
    simp -- This seems to be able to do it all by myself

theorem Function.inclusion_comp (X Y Z:Set) (hXY: X ⊆ Y) (hYZ: Y ⊆ Z) :
Function.inclusion hYZ ○ Function.inclusion hXY =
Function.inclusion (SetTheory.Set.subset_trans hXY hYZ) := by
    rw [eq_iff]; intro x; rw [comp_eval]
    unfold inclusion
    simp -- Both sides simplify to x = x after function application

theorem Function.comp_id {A B:Set} (f: Function A B) :
f ○ Function.id A = f := by
    rw [eq_iff]; intro x; rw [comp_eval]
    congr -- Remove f: id x = x
    unfold id;
    simp -- Id by definition, returns x ↦ x. So we get our desired result

theorem Function.id_comp {A B:Set} (f: Function A B) :
Function.id B ○ f = f := by -- Simp is insanely powerful I keep avoiding
    rw [eq_iff]; intro x; simp -- it, but it's hard to work with Tao funcs

-- I guess it keeps finding the P x y terms and instantly solving them?
-- Probably because x=x is auto-solved by Lean, and that's what
-- P x y is retrieving
theorem Function.comp_inv {A B:Set} (f: Function A B) (hf: f.bijective) :
    f ○ f.inverse hf = Function.id B := by
    rw [eq_iff]; intro x; rw [comp_eval]
    rw [self_comp_inverse f hf x]
    unfold id
    simp only [eval]


theorem Function.inv_comp {A B:Set} (f: Function A B) (hf: f.bijective) :
    f.inverse hf ○ f = Function.id A := by
    rw [eq_iff]; intro x; simp -- Similar to previous case

theorem mem_union_and_not_mem_left {A B : Set} {x : U}
(hAB : x ∈ A ∪ B) (ha : x ∉ A) : x ∈ B := by
  have := SetTheory.Set.mem_union x A B
  tauto

/-
let h : (X ∪ Y : Set) → Z → Prop := fun w z ↦
      if p : (w.val ∈ X) then (z=f ⟨w.val, p⟩ ) else
      z = g ⟨w.val, by exact (mem_union_and_not_mem_left w.property p)⟩-/

-- I think Classical is being used here for decidability?
open Classical in
theorem Function.glue {X Y Z:Set} (hXY: disjoint X Y) (f: Function X Z) (g: Function Y Z) :
    ∃! h: Function (X ∪ Y) Z, (h ○ Function.inclusion (SetTheory.Set.subset_union_left X Y) = f)
    ∧ (h ○ Function.inclusion (SetTheory.Set.subset_union_right X Y) = g) := by

    -- Assign to f w if w ∈ X, assign to g w if w ∈ Y
    let h : (X ∪ Y : Set) → Z := fun w ↦
      if p : (w.val ∈ X) then (f ⟨w.val, p⟩ ) else
      g ⟨w.val, by exact (mem_union_and_not_mem_left w.property p)⟩

    let H := mk_fn h
    use H; simp
    constructor
    · constructor
      · rw [eq_iff]; intro x; rw [Function.comp_eval]
        simp; unfold H h; -- simp resolves inclusion
        simp; -- Think this automatically handled the case where x ∈ X
        -- So now, all that's left is x ∉ X case: contradiction
        intro hX; exfalso; apply hX x.property
      · rw [eq_iff]; intro y; rw [Function.comp_eval]
        simp; unfold H h;
        simp; -- Think this automatically handled the case where y ∈ Y
        -- So now, all that's left is x ∈  X case
        intro hX;
        have :=  SetTheory.Set.mem_inter_iff X Y y
        have :=  this.2 (And.intro hX y.property)
        rw [hXY] at this
        simp at this -- We can't be in both X and Y per our assumptions
    · intro H' Hf Hg
      rw [eq_iff]
      intro x
      have :=  SetTheory.Set.mem_union x X Y
      have :=  this.1 x.property

      rcases this with hX | hY
      · simp [H, h, hX] -- We know that x ∈ X; so we can limit to f
        rw [← Hf]
        simp -- Removes inclusion: we're done!
      · have hX': x.val ∉ X := by
          by_contra hX; unfold disjoint at hXY
          have :=  SetTheory.Set.mem_inter_iff X Y x
          have := this.2 (And.intro hX hY)
          rw [hXY] at this
          simp at this
        simp [H, h, hX'] -- We know that x ∉ X, so we use other case
        rw [← Hg]
        simp -- Removes inclusion: we're done!

open Classical in
theorem Function.glue' {X Y Z:Set} (f: Function X Z) (g: Function Y Z)
    (hfg : ∀ x : ((X ∩ Y): Set), f ⟨x.val, by aesop⟩ = g ⟨x.val, by aesop⟩)  :
    ∃! h: Function (X ∪ Y) Z, (h ○ Function.inclusion (SetTheory.Set.subset_union_left X Y) = f)
    ∧ (h ○ Function.inclusion (SetTheory.Set.subset_union_right X Y) = g) := by

    let h : (X ∪ Y : Set) → Z := fun w ↦
      if p : (w.val ∈ X) then (f ⟨w.val, p⟩ ) else
      g ⟨w.val, by exact (mem_union_and_not_mem_left w.property p)⟩

    let H := mk_fn h
    use H; simp
    constructor
    · constructor
      · rw [eq_iff]; intro x; rw [Function.comp_eval]
        simp; unfold H h; -- simp resolves inclusion
        simp; -- Think this automatically handled the case where x ∈ X
        -- So now, all that's left is x ∉ X case: contradiction
        intro hX; exfalso; apply hX x.property
      · rw [eq_iff]; intro y; rw [Function.comp_eval]
        simp; unfold H h;
        simp; -- Think this automatically handled the case where y ∈ Y
        -- So now, all that's left is x ∈  X case
        intro hX;
        have :=  SetTheory.Set.mem_inter_iff X Y y
        have :=  this.2 (And.intro hX y.property) -- We're in X ∩ Y
        specialize hfg ⟨y, this⟩ -- In such a case, values guaranteed equal
        apply hfg
    · intro H' Hf Hg
      rw [eq_iff]
      intro x
      have :=  SetTheory.Set.mem_union x X Y
      have :=  this.1 x.property

      rcases this with hX | hY
      · simp [H, h, hX] -- We know that x ∈ X; so we can limit to f
        rw [← Hf]
        simp -- Removes inclusion: we're done!
      · by_cases hX : (x.val ∈ X)
        · simp [H, h, hX] -- Use hX to choose case of h
          rw [← Hf] -- Turn f into H'
          simp -- Neutralize inclusion
        · simp [H, h, hX]
          rw [← Hg]
          simp




--------------- SECTION 3.4

-- Tao has already deprecated the Function object.
-- This makes my life easier to I'll do the same.

/-
Definition 3.4.1 (Images of sets). If f : X ---t Y is a function
from X to Y, and S is a set in X, we define f ( S) to be the set
f(S) := {f(x) : x E S};
-/

abbrev SetTheory.Set.image {X Y : Set} (f : X → Y) (S : Set ) :=
  X.replace (P := fun x y ↦ x.val ∈ S ∧ y = f x )
  (by unfold partial_function;
      intro x y1 y2; simp;
      intro hx hy1 hx hy2; simp [*] at *
      )


theorem SetTheory.Set.mem_image {X Y:Set} (f : X → Y) (S: Set) (y:Object) :
  y ∈ image f S ↔ ∃ x:X, x.val ∈ S ∧ f x = y := by
  rw [SetTheory.Set.replacement_axiom];
  tauto -- definitionally equivalent

theorem SetTheory.Set.image_in_codomain {X Y:Set} (f:X → Y) (S: Set) :
  image f S ⊆ Y := by
  intro y him
  rw [mem_image] at him
  obtain ⟨x, hx, hxy⟩ := him -- obtain ⟨x, hx, rfl⟩ will apply the equality
  rw [← hxy]
  exact (f x).property

/-

Note that
but in general
x E S ====> f(x) E f(S)
65
f(x) E f(S) =I? x E S;
-/

theorem SetTheory.Set.mem_image_of_eval {X Y : Set}(f: X → Y) (S: Set)
(x : X): x.val ∈ S → (f x).val ∈ image f S := by
  intro hxS;  rw [mem_image]; use x -- Follows from definition

theorem SetTheory.Set.mem_image_of_eval_counter :
∃ (X Y :Set) (f: X → Y) (S: Set) (x : X),
¬ ( (f x).val ∈ image f S → x.val ∈ S ):= by
  let X : Set := {emptyU, eemptyU}
  let Y : Set := {3}

  let emp : X := ⟨emptyU, by unfold X; simp⟩
  let three : Y :=⟨ 3, by unfold Y; simp⟩

  let f : X → Y := fun x ↦ three
  let S : Set := {emptyU}


  let eemp : X := ⟨eemptyU, by unfold X; simp⟩
  use X; use Y; use f; use S; use eemp
  push_neg
  constructor
  · rw [mem_image]; simp [f]; -- Always outputs 1
    use emp;
    exact ⟨emp.property, by unfold S emp; simp⟩
  · intro h; unfold S at h; simp at h
    contrapose! h; symm; apply emptyU_ne_eemptyU

/-
Definition 3.4.4 (Inverse images). If U is a subset of Y, we define
the set f-1(U) to be the set
f-1(U) := {x EX: f(x) E U}.
-/

abbrev SetTheory.Set.preimage {X Y : Set} (f : X → Y) (U : Set) :=
  X.specify (fun x ↦ (f (x)).val ∈ U)

@[simp]
theorem SetTheory.Set.mem_preimage {X Y:Set} (f:X → Y) (U: Set) (x:X) :
    x.val ∈ preimage f U ↔ (f x).val ∈ U := by rw [specification_axiom']

-- Alternate version that doesn't require x : X

theorem SetTheory.Set.mem_preimage' {X Y:Set} (f:X → Y) (U: Set) (x:Object) :
    x ∈ preimage f U ↔ ∃ x': X, x'.val = x ∧ (f x').val ∈ U := by
    constructor
    · intro h
      by_cases hx: x ∈ X
      · let z : X := ⟨x, hx⟩
        use z; unfold z; simp
        apply (mem_preimage f U z).1 at h
        exact h
      · have := X.specification_axiom h; contradiction
    · rintro ⟨ z, rfl, hfz ⟩
      rwa [mem_preimage]

-- Change from explicit to implicit parameters
theorem SetTheory.Set.mem_preimage'' {X Y U: Set} {f : X → Y} {x : Object}
: x ∈ preimage f U ↔  ∃ x': X, x'.val = x ∧ (f x').val ∈ U := by
  exact (SetTheory.Set.mem_preimage' f U x)

theorem SetTheory.Set.preimage_in_domain {X Y:Set} (f:X → Y) (U: Set) :
(preimage f U) ⊆ X := by
  intro x hx;
  apply X.specification_axiom hx



/-
Axiom 3.10 (Power set axiom). Let X and Y be sets. Then there
exists a set, denoted Y x, which consists of all the functions from
X toY, thus
f
E Y X <==> (! is a function with domain X and range Y).
-/

instance SetTheory.Set.inst_pow : Pow Set Set where
  pow := SetTheory.pow

-- Turn functions into objects
@[coe]
def SetTheory.Set.coe_of_fun {X Y:Set} (f: X → Y) : Object := function_to_object X Y f

instance SetTheory.Set.inst_coe_of_fun {X Y:Set} : CoeOut (X → Y) Object where
  coe := coe_of_fun

@[simp]
theorem SetTheory.Set.coe_of_fun_inj {X Y:Set} (f g:X → Y) : (f:Object) = (g:Object) ↔ f = g := by
  simp [coe_of_fun]

@[simp]
theorem SetTheory.Set.powerset_axiom' {X Y:Set} (F:Object) :
  F ∈ (X ^ Y) ↔ ∃ f: Y → X, f = F := SetTheory.powerset_axiom X Y F

/-
Lemma 3.4.9. Let X be a set. Then the set
{Y : Y is a subset of X}
is a set.
-/


/-
FINALLY fixed the natural numbers so now I don't have to use the
set-theory versions of 0 and 1 :sob:
-/

def SetTheory.Set.powerset (X:Set) : Set :=
  ({0,1}^X : Set).replace
  (P := fun F y ↦ ∃ (f : X → ({0,1} : Set) ),
                      y = preimage f ({1}: Set) ∧
                      (f = (F : U)) )

  (by unfold partial_function; intro F y1 y2 h
      obtain ⟨⟨f1, ⟨hy1, hf1⟩⟩ ,⟨f2,⟨hy2, hf2⟩⟩⟩ := h
      rw [hy1, hy2]
      suffices f1 = f2 by rw [this]
      apply ( coe_of_fun_inj f1 f2).1
      simp [*] -- We already know f1 and f2 are the same (they're both equal to F)
      )

open Classical in
/-- Exercise 3.4.6 (i) -/
@[simp]
theorem SetTheory.Set.mem_powerset {X:Set} (x:Object) :
    x ∈ powerset X ↔ ∃ Y:Set, x = Y ∧ Y ⊆ X := by
    constructor <;> intro h
    · -- If Y = f⁻¹({1}), we know Y ⊆ X
      unfold powerset at h;
      rw [replacement_axiom] at h
      obtain ⟨F, f, hx,hf⟩ := h
      use preimage f {1}
      simp [hx]
      apply preimage_in_domain
    · -- Construct an f that corresponds to Y
      obtain ⟨Y, rfl, hXY⟩ := h
      unfold powerset
      rw [replacement_axiom]
      let f : X.toSubtype → ({0, 1}: Set):= fun x ↦
                                      if x.val ∈ Y then
                                      ⟨1, by simp⟩  else ⟨0, by simp⟩
      let F := function_to_object X ({0, 1}: Set) f
      use ⟨F, by rw [powerset_axiom']; use f; rfl⟩
      use f
      -- Show that f corresponds to Y
      constructor
      · suffices Y = (preimage f {1}) by rw [this]
        apply SetTheory.Set.ext; intro x
        have := mem_preimage f {1}
        by_cases hX : x ∈ X
        · -- x ∈ X allows us to get preimage (proceed normally)
          let z : X := ⟨x, hX⟩
          rw [this z]; simp [f, z]
          constructor <;> intro h -- f gives 1 iff x ∈ Y : thus, f⁻¹({1})=Y
          · simp [h]
          · by_contra h'; simp [h'] at h
        · -- x ∉ X, then it isn't in either set (vacuous case)
          suffices ¬ x ∈ Y ∧ ¬ x ∈ preimage f {1} by -- False ↔ False
                                                    simp [this]
          constructor -- Show that x is in neither
          · have hXY' := hXY x
            apply hXY'.mt hX
          · have := preimage_in_domain f {1} x
            apply this.mt hX

      · rfl -- F = f

theorem SetTheory.Set.exists_powerset (X:Set) :
   ∃ (Z: Set), ∀ x, x ∈ Z ↔ ∃ Y:Set, x = Y ∧ Y ⊆ X := by
   use powerset X; apply mem_powerset

/-
Axiom 3.11 (Union). Let A be a set, all of whose elements are
themselves sets. Then there exists a set U A whose elements are
precisely those objects which are elements of the elements of A,
thus for all objects x
-/

theorem SetTheory.Set.union_axiom (A: Set) (x:Object) :
x ∈ union A ↔ ∃ (S:Set), x ∈ S ∧ (S:Object) ∈ A :=
    SetTheory.union_axiom A x

/-
Another
important consequence of this axiom is that if one has some set
I, and for every element a E I we have some set AQ, then we can
form the union set UQEI AQ by defining
U AQ := U{AQ: a E I},
-/

abbrev SetTheory.Set.iUnion (I : Set) (A : I → Set): Set :=
  union ( I.replace (P := fun i S ↦ A i = S) (by simp [partial_function]) )

theorem SetTheory.Set.mem_iUnion {I:Set} (A: I → Set) (x:Object) :
x ∈ iUnion I A ↔ ∃ i : I, x ∈ A i := by
  rw [union_axiom]
  constructor <;> intro h
  · obtain ⟨S, hxS, hSI⟩ := h -- ∃ S : x ∈ S
    rw [replacement_axiom] at hSI -- Function definition gives us S = A i
    obtain ⟨i, hAS⟩ := hSI
    use i; simp_all -- We're done
  · obtain ⟨i, hi⟩ := h
    use A i -- All we need is to show that A i ∈ U_{i} (A_i)
    simp [hi]
    rw [replacement_axiom]; use i -- i matches A i

/-
Note that
if I was empty, then UQEI AQ would automatically also be empty
(why?).
-/
theorem SetTheory.Set.iUnion_of_empty (A: (∅:Set) → Set) :
iUnion (∅:Set) A = ∅ := by  -- Empty index → Empty union
  rw [ext_iff]; intro x
  simp -- We know x ∉ ∅
  rw [mem_iUnion]
  intro ⟨i, hi⟩
  have := i.property
  simp_all -- Requires i ∈ ∅ to pair with x: impossible

/-
More specifically, given any nonempty set I, and given an assignment of a set Aa to each a E I, we
can define the intersection naEI Aa by first choosing some element
f3 of I (which we can do since I is non-empty), and setting
n Aa := {x E A.a: X E Aa for all a E I},
-/
noncomputable abbrev SetTheory.Set.nonempty_choose {I:Set} (hI: I ≠ ∅) : I :=
  ⟨(nonempty_def.1 hI).choose, (nonempty_def.1 hI).choose_spec⟩

abbrev SetTheory.Set.iInter' (I:Set) (j:I) (A: I → Set) : Set :=
  (A j).specify (P := fun x ↦ ∀ i:I, x.val ∈ A i)

noncomputable abbrev SetTheory.Set.iInter (I: Set) (hI: I ≠ ∅) (A: I → Set) : Set :=
  iInter' I (nonempty_choose hI) A

theorem SetTheory.Set.mem_iInter {I:Set} (hI: I ≠ ∅) (A: I → Set) (x:Object) :
x ∈ iInter I hI A ↔ ∀ i:I, x ∈ A i := by
  constructor <;> intro h
  · simp [iInter, iInter', specification_axiom''] at h
    intro i
    have ⟨h1,h2⟩ := h
    have := h2 i.val i.property
    apply this
  · simp [iInter, iInter', specification_axiom'']
    constructor
    · apply h -- chosen elem is part of i
    · intro ival iprop -- Condition matches h for any i we look at
      apply h

/-
Exercise 3.4.1. Let f : X --+ Y be a bijective function, and let f- 1 :
Y --+ X be its inverse. Let V be any subset of Y. Prove that the forward
image of V under f- 1 is the same set as the inverse image of V under
f; thus the fact that both sets are denoted by f- 1 (V) will not lead to
any inconsistency.
-/
#check SetTheory.Set.image

theorem SetTheory.Set.preimage_eq_image_of_inv {V X Y : Set} (f: X → Y)
(f_inv: Y → X)
(hf: Function.LeftInverse f_inv f ∧ Function.RightInverse f_inv f)
(hV: V ⊆ Y):
image f_inv V = preimage f V := by
  rw [ext_iff]; intro x
  by_cases hX: x ∈ X
  · simp [mem_image] -- Unfold image/preimage
    simp [mem_preimage'']
    constructor <;> intro h
    · use hX
      obtain ⟨y,hyV,hyY,hinv⟩ := h
      suffices ↑(f ⟨x, hX⟩) = y by simp [this, hyV]
      let z : Y := ⟨y, hyY⟩
      change (f ⟨x, hX⟩).val = z.val
      simp [← hinv]
      rw [coe_inj]
      apply hf.2

    · obtain ⟨hX, h⟩ := h
      use ↑(f ⟨x, hX⟩)
      simp [h, hV ↑(f ⟨x, hX⟩) h]
      let z : X := ⟨x, hX⟩
      change (f_inv (f z)).val = z.val
      rw [coe_inj]
      apply hf.1

  · -- Vacuous x ∉ X case
    suffices ¬( x ∈ image f_inv V) ∧ ¬( x ∈ preimage f V)  by simp [this]
    constructor
    · contrapose! hX
      have hsub :=  (image_in_codomain f_inv V )
      apply hsub x hX
    · contrapose! hX
      have hsub := preimage_in_domain f V
      apply hsub x hX


/-
Exercise 3.4.2. Let f: X--+ Y be a function from one set X to another
set Y, let S be a subset of X, and let U be a subset of Y. What, in
general, can one say about f- 1 (!(8)) and S? What about f(f- 1(U))
and U?
-/

theorem SetTheory.Set.preimage_of_image {X Y: Set} (f : X → Y) (S: Set)
(hS : S ⊆ X): S ⊆ preimage f (image f S) := by
  intro x hxS
  have hxX := hS x hxS
  let z : X := ⟨x, hxX⟩
  rw [ mem_preimage'']; use z
  rw [ mem_image]
  simp [z]
  use x; simp [hxS, hxX]

theorem SetTheory.Set.image_of_preimage {X Y:Set} (f : X → Y) (U : Set) :
image f (preimage f U) ⊆ U := by
  intro y hy
  simp only [mem_image] at hy -- x ∈ preimage
  obtain ⟨x,hpre, hfxy⟩ := hy -- y = f x
  rw [ mem_preimage''] at hpre -- f x ∈ U
  simp_all -- Combine those last two: y ∈ U

/-
Exercise 3.4.3. Let A, B be two subsets of a set X, and let f: X --+ Y
be a function. Show that f(A n B) ~ f(A) n f(B), that f(A)\f(B) ~
f(A\B), f(A U B) = f(A) U f(B). For the first two statements, is it
true that the~ relation can be improved to=?
-/

theorem SetTheory.Set.image_of_inter {X Y:Set} (f:X → Y) (A B: Set) :
image f (A ∩ B) ⊆ (image f A) ∩ (image f B) := by
  intro y hAB
  rw [mem_image] at hAB
  obtain ⟨x, hxAB, xfx⟩ := hAB
  simp;
  constructor <;> (rw [mem_image]; use x; simp_all)

theorem SetTheory.Set.image_of_diff {X Y:Set} (f:X → Y) (A B: Set) :
(image f A) \ (image f B) ⊆ image f (A \ B) := by
  intro y hAB; simp [mem_image] at *
  obtain ⟨hA, hB⟩ := hAB
  obtain ⟨x, hxA, hxX, hfxy⟩ := hA
  use x
  constructor
  · -- We know that y = f x, so we know that x ∉ B
    simp [hxA]
    have := (hB x ).mt; push_neg at this
    apply this
    simp [hxX, hfxy]
  · simp [hxX, hfxy]

theorem SetTheory.Set.image_of_union {X Y:Set} (f:X → Y) (A B: Set) :
image f (A ∪ B) = (image f A) ∪ (image f B) := by
  rw [ext_iff]; intro y
  simp [mem_image]
  constructor <;> intro h
  · obtain ⟨x, hAB, hX, hfx⟩ := h
    rcases hAB with hA | hB
    · left; use x; simp [hA]; use hX
    · right; use x; simp [hB]; use hX
  · rcases h with hA | hB
    · obtain ⟨x,hA,hX,hfx⟩ := hA
      use x; simp [hA]; use hX
    · obtain ⟨x,hB,hX,hfx⟩ := hB
      use x; simp [hB]; use hX


def SetTheory.Set.image_of_inter' : Decidable (∀ X Y:Set, ∀ f:X → Y,
∀ A B: Set, image f (A ∩ B) = (image f A) ∩ (image f B)) := by
-- The first line of this construction should be either `apply isTrue` or `apply isFalse`
  apply isFalse; push_neg
  let X : Set := {1,2}
  let Y : Set := {3}
  let f : X → Y := fun x ↦ ⟨3, by simp [Y]⟩
  let A : Set := {1}
  let B : Set := {2}
  use X; use Y; use f; use A; use B

  intro h; rw [ext_iff] at h
  specialize h 3
  simp at h
  have: 3 ∉ image f (A ∩ B) := by
    intro h; rw [mem_image] at h;
    obtain ⟨x, h1, _⟩ := h
    simp [A, B] at h1 -- Each set contains one distinct element
    obtain ⟨h1,h2⟩ := h1
    simp_all -- So nothing can be in both sets
  apply this; simp [h] -- So it has a partner in both A and B, contradiction
  simp [A, B] -- One of its partners must be 1, one partner must be 2
  simp [f, mem_image, X] -- Which are exactly what X includes

def SetTheory.Set.image_of_diff' : Decidable (∀ X Y:Set, ∀ f:X → Y,
∀ A B: Set, image f (A \ B) = (image f A) \ (image f B)) := by
-- The first line of this construction should be either `apply isTrue` or `apply isFalse`
  apply isFalse; push_neg
  let X : Set := {1,2}
  let Y : Set := {3}
  let f : X → Y := fun x ↦ ⟨3, by simp [Y]⟩
  let A : Set := {1}
  let B : Set := {2}
  use X; use Y; use f; use A; use B
  change ¬ (image f (A \ B) = image f A \ image f B)
  rw [ext_iff]
  push_neg; use 3; left
  constructor
  · -- Looking for value of x that goes to 3 in A \ B
    simp [f, mem_image] -- All values of x go to 3, so we just need any
    use 1; simp [A, X, B] -- 1 is in A, not in B, in X
  · intro h; simp [mem_image] at h
    obtain ⟨hA,hB⟩ := h
    -- 3 ∉ f(A) \ f(B): f(B) contains 3
    specialize hB 2; simp [B, X] at hB -- Use 2 ∈ B
    simp [f] at hB -- f 2 = 3

/-
Exercise 3.4.4. Let f : X --+ Y be a function from one set X to another
set y, and let U, V be subsets of Y. Show that f- 1 (U U V) = r 1 (U) U
r1(V), that / -1 (U n V)= f-1(U) n / - 1 (V), and that f-1(U\V) =
r1(U)\f-1(V).
-/

-- Preimage theorems are simpler than image theorems because x can only
-- have one partner f x.

theorem SetTheory.Set.preimage_of_union {X Y : Set} (f : X → Y) (U V : Set) :
preimage f (U ∪ V) = (preimage f U) ∪ (preimage f V) := by
  rw [ext_iff]; intro x
  simp [mem_preimage'']
  constructor <;> intro h
  · obtain ⟨hX,hUV⟩:=h
    rcases hUV with hU | hV
    · left; use hX
    · right; use hX
  · rcases h with hU | hV
    · obtain ⟨hX,hf⟩ := hU
      use hX; simp [hf]
    · obtain ⟨hX,hf⟩ := hV
      use hX; simp [hf]

theorem SetTheory.Set.preimage_of_inter {X Y : Set} (f : X → Y) (U V : Set) :
preimage f (U ∩ V) = (preimage f U) ∩ (preimage f V) := by
  rw [ext_iff]; intro x
  simp [mem_preimage'']
  constructor <;> intro h
  · obtain ⟨hX, hU, hV⟩ := h
    simp [hU, hV, hX] -- x is in both sets, so it fulfills both conditions
  · obtain ⟨⟨hX, hU⟩, ⟨_, hV⟩⟩ := h
    use hX -- x only creates a single f x: it's in both sets

theorem SetTheory.Set.preimage_of_diff {X Y : Set} (f : X → Y) (U V : Set) :
preimage f (U \ V) = (preimage f U) \ (preimage f V) := by
  -- Nearly identical to inter case
  rw [ext_iff]; intro x
  simp [mem_preimage'']
  constructor <;> intro h
  · obtain ⟨hX, hU, hV⟩ := h
    simp [hX, hU, hV]
  · obtain ⟨⟨hX, hU⟩, hV⟩ := h
    simp [hU, hV, hX]
/-
Exercise 3.4.5. Let f: X--+ Y be a function from one set X to another
set Y. Show that f(f- 1 (8)) = S for every S ~ Y if and only if f is
surjective. Show that f- 1(!(8)) = S for every S ~X if and only if f is
injective.
-/

/-- Exercise 3.4.5 -/
theorem SetTheory.Set.image_preimage_of_surj {X Y:Set} (f:X → Y) :
  (∀ U, U ⊆ Y → image f (preimage f U) = U) ↔ Function.Surjective f := by
    constructor <;> intro h
    · unfold Function.Surjective
      intro y
      -- We need to find x s.t. y = f x
      let U : Set := {y.val} -- A set literally only containing y to get x
      have : U ⊆ Y := by intro y' hy; simp [U] at hy; simp [hy, y.property]
      specialize h U this
      have : y.val ∈ U := by simp [U]
      -- Our hypothesis gives us y ∈ f (f⁻¹ U)
      rw [← h] at this
      rw [mem_image] at this
      -- Being in the image means we can directly get the partner x
      obtain ⟨x, hpre, hfx⟩ := this
      use x
      rw [← coe_inj]
      simp [hfx]

    · intro U hUY
      apply subset_antisymm
      · apply image_of_preimage --Always true
      · intro y hyU
        --let z : Y :=
        have := h ⟨y, hUY y hyU⟩ -- Each y has a partner x ∈ X
        obtain ⟨x, hxy⟩ := this
        simp only [mem_image]; use x; -- Check whether x ∈ f⁻¹ U
        simp [hxy, hyU] -- We know it is because y ∈ U



/-- Exercise 3.4.5 -/
theorem SetTheory.Set.preimage_image_of_inj {X Y:Set} (f:X → Y) :
  (∀ S, S ⊆ X → preimage f (image f S) = S) ↔ Function.Injective f := by
    unfold Function.Injective
    constructor <;> intro h
    · intro x1 x2 hfx
      let S : Set := {x1.val}
      have: S ⊆ X:= by intro x hS; simp [S] at hS; simp [hS, x1.property]
      -- If we can show x2 ∈ S = {x1}, then we know x2 = x1
      suffices x2.val ∈ S by simp [S, coe_inj] at this; rw [this]
      specialize h S this
      -- We'll instead show that x2 ∈ f⁻¹ (f(S)), since that's equivalent
      rw [← h]
      rw [mem_preimage'']; use x2; simp
      -- We'll need to get f x2 ∈ f(S); we'll instead show f x1 ∈ f (S)
      rw [← hfx]
      -- Which is easy to prove because S = {x1}
      simp [mem_image, S, x1.property]


    · intro S hSX
      apply subset_antisymm
      · intro x hx
        simp [mem_preimage''] at hx
        obtain ⟨hXx, hf⟩ := hx
        simp [mem_image] at hf
        obtain ⟨x', hx', hXx', hfx'⟩ := hf -- Retrieve an x' that gives f x'
        rw [coe_inj] at hfx'
        apply h at hfx' -- f x' = f x. By inj, these must be the same
        rw [← coe_inj] at hfx'
        simp_all -- So, we know that the x' we retrieved must be in S
      · apply preimage_of_image; apply hSX -- Always true


/-
Exercise 3.4.7. Let X, Y be sets. Define a partial function from X to
y to be any function f : X' --+ Y' whose domain X' is a subset of X,
and whose range, Y' is a subset of Y. Show that the collection of all
partial functions from X to Y is itself a set. (Hint: use Exercise 3.4.6,
the power set axiom, the replacement axiom, and the union axiom.)
-/

/- Helper lemma for Exercise 3.4.7. -/

@[simp]
lemma SetTheory.Set.mem_powerset' {S S' : Set} : (S': Object) ∈ S.powerset ↔ S' ⊆ S := by
  simp [mem_powerset]

/- Another helper lemma for Exercise 3.4.7. -/

lemma SetTheory.Set.mem_union_powerset_replace_iff {S : Set} {P : S.powerset → Object → Prop} {hP : _} {x : Object} :
    x ∈ union (S.powerset.replace (P := P) hP) ↔
    ∃ (Spow : S.powerset) (U : Set), P Spow U ∧ x ∈ U := by
  simp only [union_axiom, replacement_axiom]; tauto

/-- Exercise 3.4.7 -/
theorem SetTheory.Set.partial_functions {X Y:Set} :
  ∃ Z:Set, ∀ F:Object, F ∈ Z ↔
  (∃ X' Y':Set, X' ⊆ X ∧ Y' ⊆ Y ∧ ∃ f: X' → Y', F = f) := by
    let PX := powerset X
    let PY := powerset Y
    let f : Set → Set := fun A ↦ PY.replace
      (P:= fun x y ↦ ∃B: Set, (x.val = set_to_object B) ∧ ((B ^ A : Set) = y))
      (by unfold partial_function; rintro x y1 y2 ⟨h1,h2⟩;
          obtain ⟨_, _, h1⟩ := h1;  obtain ⟨_, _, h2⟩ := h2
          simp_all
       )

    let G : Set := PX.replace
      (P := fun x y ↦ ∃ C: Set, (x.val = set_to_object C) ∧ y = union (f C) )
      (by unfold partial_function; rintro x y1 y2 ⟨h1,h2⟩;
          obtain ⟨_, _, h1⟩ := h1;  obtain ⟨_, _, h2⟩ := h2
          simp_all
      )

    let H : Set := union G
    use H; intro x
    -- Unpacking H
    unfold H G; rw [mem_union_powerset_replace_iff]

    constructor <;> intro h
    · --- Check whether an object in H is a partial function
      -- Union → x ∈ S, S ∈ G
      obtain ⟨A_in_PX, UfA, ⟨⟨A, hA_convert, h_UfA_convert⟩,h_UfA⟩⟩ := h
      -- S = U f (A)
      rw [coe_eq_iff] at h_UfA_convert; rw [h_UfA_convert] at h_UfA
      -- Unpacking f: union over B^A sets
      unfold f at h_UfA
      rw [mem_union_powerset_replace_iff] at h_UfA
      -- Thus, x ∈ B^A
      obtain ⟨B_in_PY, BpowA, ⟨⟨B, hB_convert, h_BpowA_convert⟩,h_BpowA⟩⟩ := h_UfA
      rw [coe_eq_iff] at h_BpowA_convert; rw [← h_BpowA_convert] at h_BpowA
      -- Meaning, x is a function f: A → B
      rw [SetTheory.Set.powerset_axiom'] at h_BpowA
      use A; use B;
      repeat' apply And.intro -- Because A and B are in their power sets, they're subsets as desired
      · rw [← mem_powerset']
        rw [← hA_convert]
        apply A_in_PX.property
      · rw [← mem_powerset']
        rw [← hB_convert]
        apply B_in_PY.property
      · obtain ⟨f,hf⟩:=h_BpowA -- And we already established that x is f : A → B
        use f; rw [hf]

    · -- Check whether any partial function is in H
      obtain ⟨A,B,hAX, hBY, f', hf'⟩ := h -- Retrieve our partial function
      let A_in_PX: PX := ⟨A, by unfold PX; rw [mem_powerset]; use A ⟩
      use A_in_PX;
      -- We narrow H down to union (f A): can only have domain A
      use union (f A )
      constructor
      · use A
      · simp [f]; rw [mem_union_powerset_replace_iff]
        let B_in_PY :PY := ⟨B, by unfold PY; rw [mem_powerset]; use B⟩
        -- We narrow H down to B^A : we can only have codomain B
        use B_in_PY; use B^A;
        constructor
        · use B
        · simp; use f'; rw [hf'] -- B^A means f : A → B

/-
Exercise 3.4.8. Show that Axiom 3.4 can be deduced from Axiom 3.3
and Axiom 3.11.
-/

theorem SetTheory.Set.union_pair_exists (X Y:Set) : ∃ Z:Set, ∀ x, x ∈ Z ↔ (x ∈ X ∨ x ∈ Y) := by
  use union {set_to_object X, set_to_object Y}
  intro x
  rw [union_axiom]
  constructor <;> intro h
  · obtain ⟨S, h1, h2⟩ := h
    rw [mem_pair] at h2
    repeat rw [coe_eq_iff] at h2
    rcases h2 with hX | hY
    · left;  simp_all
    · right; simp_all
  · rcases h with hX | hY
    · use X; simp [hX]
    · use Y; simp [hY]


/-
Exercise 3.4.9. Show that if (3 and (3' are two elements of a set I, and
to each a E I we assign a set Aa, then
{x E A.a: x E Aa for all a E I}= {x E Aw : x E Aa for all a E I},
and so the definition of naE/ Aa defined in (3.3) does not depend on (3.
Also explain why (3.4) is true.
-/

theorem SetTheory.Set.iInter'_insensitive {I: Set} (i1 i2 : I) (A: I → Set):
  iInter' I i1 A = iInter' I i2 A := by
    rw [ext_iff]; intro x; simp [iInter']
    repeat rw [specification_axiom'']
    simp -- Lean is smart enough to pull out the common assumption on both sides
    intro h
    simp [h] -- Both sides are true if h is true, because they're just special cases

/-
Exercise 3.4.10. Suppose that I and J are two sets, and for all a E IUJ
let Aa be a set. Show that (UaEI Aa) U (UaEJ Aa) = UaE~UJ Aa. If I
and J are non-empty, show that (naEI Aa) n (naEJ Aa) = naEIUJ Aa.
-/

theorem SetTheory.Set.union_iUnion {I J:Set} (A: (I ∪ J:Set) → Set) :
    -- We have to narrow down i ∈ A ∪ B to I and J, respectively
    -- So, we use a function that takes i ∈ I as input
    -- And then lift it back up (i ∈ I → i ∈ I ∪ J) so we access A_i
    iUnion I (fun α ↦ A ⟨ α.val, by simp [α.property]⟩) --
    ∪ iUnion J (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    = iUnion (I ∪ J) A := by
    simp [ext_iff, mem_iUnion]; intro x
    constructor <;> intro h
    · rcases h with hI | hJ
      · obtain ⟨i, hI, hx⟩ := hI
        use i; use (by simp [hI])
      · obtain ⟨i, hJ, hx⟩ := hJ
        use i; use (by simp [hJ])
    · obtain ⟨i, hi, hx⟩ := h
      rcases hi with hI | hJ
      · left; use i; use hI
      · right; use i; use hJ

theorem SetTheory.Set.union_of_nonempty {I J:Set} (hI: I ≠ ∅) (hJ: J ≠ ∅) :
  I ∪ J ≠ ∅ := by
    rw [nonempty_def] at *
    obtain ⟨i, hI⟩ := hI
    use i; simp; left; exact hI

theorem SetTheory.Set.inter_iInter {I J : Set} (hI: I ≠ ∅) (hJ: J ≠ ∅) (A: (I ∪ J: Set) → Set):
  iInter I hI (fun i ↦ A ⟨i.val, by simp [i.property]⟩ ) ∩
  iInter J hJ (fun i ↦ A ⟨i.val, by simp [i.property]⟩ ) =
  iInter (I ∪ J) (union_of_nonempty hI hJ) A := by
  simp [ext_iff, mem_iInter]; intro x
  constructor <;> intro h
  · obtain ⟨hI,hJ⟩ := h -- x is in each Ai, and in each Aj
    intro i hIJ --Check each element in I ∪ J
    rcases hIJ with hIi | hJi
    · apply hI i hIi
    · apply hJ i hJi
  · constructor -- Check each Ai and each Aj
    · intro i hI
      refine h i ?_
      left; apply hI
    · intro i hJ
      refine h i ?_
      right; apply hJ

/-
Exercise 3.4.11. Let X be a set, let I be a non-empty set, and for all
a E I let Aa be a subset of X. Show that
X\ U Aa = n (X\Aa)
aEl aEl
and
X\ n Aa = U (X\Aa)·
-/

theorem SetTheory.Set.compl_iUnion {X I: Set} (hI : I ≠ ∅) (A : I → Set):
X \ (iUnion I A) = iInter I hI (fun i ↦ X \ A i) := by
  simp [ext_iff, mem_iUnion, mem_iInter]; intro x
  constructor <;> intro h
  · obtain ⟨hX,h⟩:= h -- Grab an x ∈ X; x ∉ ∪ Ai
    intro i hI -- We grab any particular index in our desired intersection
    -- We make sure we're in that set
    exact ⟨hX, by exact h i hI⟩
  · rw [nonempty_def] at hI
    obtain ⟨i, hI⟩ := hI
    have := (h i hI).1
    apply And.intro this
    intro j hj
    specialize h j hj
    apply h.2

theorem SetTheory.Set.compl_iInter {X I: Set} (hI : I ≠ ∅) (A : I → Set):
X \ iInter I hI A = iUnion I (fun i ↦ X \ A i) := by
  simp [ext_iff]; intro x; rw [mem_iUnion, mem_iInter]
  push_neg
  constructor <;> intro h
  · obtain ⟨hX, i, hi⟩ := h
    use i; simp_all
  · obtain ⟨i, hXAi⟩ := h
    rw [mem_sdiff] at hXAi
    apply And.intro hXAi.1
    use i; apply hXAi.2



--------------- SECTION 3.5

/-
Definition 3.5.1 (Ordered prur). If x and y are any objects (possibly equal), we define the ordered pair (x, y) to be a new object,
consisting of x as its first component and y as its second component. Two ordered pairs (x,y) and (x',y') are considered equal if
and only if both their components match
-/

@[ext]
structure OrderedPair where
  left : Object
  right : Object

@[simp]
theorem OrderedPair.eq (x y x' y' : Object) :
    (⟨ x, y ⟩ : OrderedPair) = (⟨ x', y' ⟩ : OrderedPair) ↔ x = x' ∧ y = y' := by aesop

/- Helper lemma for Exercise 3.5.1 -/

lemma SetTheory.Set.singleton_cancel {a b : Object} : ({a}: Set) = ({b}: Set) ↔ a=b := by
  constructor <;> intro h
  · have: a ∈ ({a}: Set) := by simp
    rw [h] at this
    rw [mem_singleton] at this; exact this
  · rw [h]

lemma SetTheory.Set.pair_eq_singleton_iff {a b c: Object} : {a, b} = ({c}: Set) ↔
    a = c ∧ b = c := by
    constructor <;> (intro h)
    · -- We know a and b are in {a,b}
      -- So they're in {c}
      -- So they equal c
      constructor
      · rw [← (mem_singleton a c)]
        rw [← h]
        simp
      · rw [← (mem_singleton b c)]
        simp [← h]
    · -- You can just substitute in a=c and b=c
      obtain ⟨hac,hbc⟩ := h
      rw [ext_iff]; intro x
      rw [hac, hbc]
      rw [mem_singleton, mem_pair]
      tauto


notation "⦃" S "⦄" => SetTheory.set_to_object S
/- Exercise 3.5.1 can be thought of as saying that we have a coercion
between our structure implementation and their set-based implementation -/

@[simp]
abbrev orderpairleft (left : U) :=  (({left}:Set):Object)
@[simp]
abbrev orderpairright (left right: U) := (({left, right}:Set):Object)
@[simp]
abbrev orderpairset (left right: U) :=  ({orderpairleft left, orderpairright left right}:Set)

-- {{a}, {a,x}} = {{a}, {a,y}} → x=a ∨ x=y
lemma ordered_pair_lemma (a x y : U) (haax_aay : orderpairset a x = orderpairset a y):
x=a ∨ x=y := by
  simp at haax_aay
  -- {a,x} ∈ {{a},{a,x}}
  have hax_aax: (orderpairright a x) ∈ orderpairset a x := by simp
  -- x ∈ {a,x}
  have hx_ax: (x) ∈ ({a,x}:Set) := by simp;

  -- Processing to get {a,x} ∈ {{a},{a,y}}
  simp only [orderpairleft, orderpairset] at hax_aax
  rw [haax_aay] at hax_aax
  let hax_aay := hax_aax
  -- Simplify and turn into logic
  simp [orderpairright] at hax_aay

  rcases hax_aay with hax_a | hax_ay
  · rw [hax_a] at hx_ax
    left
    simp at hx_ax
    exact hx_ax
  · rw [hax_ay] at hx_ax
    simp at hx_ax
    exact hx_ax

/-
It's kinda ridiculous how long this one took me. A few things:

· Multiple things can be called SetTheory.set_to_object S and be completely
  different things that cannot be exchanged under the hood. Ew.
· Decided to make a couple abbreviations because it was too painful to
  write everything otherwise
· It feels like sometimes, I can/can't use apply, rw, or simp, when I would normally expect
  them to work. I should learn their backend details more.
· I wanted to avoid using "have" a dozen times, but honestly, it was much more natural
  to prove this in a forward manner, so I went for it.
· Creating a custom lemma was pretty useful because the manipulation between
  sets and objects can really be a hassle.
· I didn't like the aggressive proof-by-cases approach but it was hard to think of anything
  else that wasn't a pain so I gave up and caved.
· It feels like there should be some machinery that can aggressively golf this, but
  I couldn't figure anything out. Oh well.
-/

def OrderedPair.toObject : OrderedPair ↪ Object where
  toFun p := -- We turn (a,b) into the set {{a}, {a,b}}
  orderpairset p.left p.right
  inj' := by  intro x1 x2 hseteq;

              have hseteq_unsimp := hseteq -- Leave unsimplified for later
              simp only at hseteq -- Only removing function application

              simp at hseteq -- Prove (a,b)=(c,d)
              rw [eq]
              have: (orderpairleft x1.left) ∈ orderpairset x1.left x1.right := by simp
              simp only [orderpairleft, orderpairset] at this
              rw [hseteq] at this
              rw [SetTheory.Set.mem_pair] at this

              have hx1x2: x1.left = x2.left := by -- First, we prove a=c
                rcases this with h2 | h12
                · -- {a} = {c}: gives a=c right away
                  rw [SetTheory.Set.coe_eq_iff] at h2
                  apply SetTheory.Set.singleton_cancel.1
                  exact h2
                · -- {a} = {c,d} : a=c=d using above lemma
                  simp at h12; symm at h12
                  have := SetTheory.Set.pair_eq_singleton_iff.1 h12
                  apply this.left.symm

              simp [hx1x2] -- We only need b=d now

              -- Pre-processing into the correct format
              rw [SetTheory.Set.coe_eq_iff] at hseteq_unsimp
              rw [← hx1x2] at hseteq_unsimp

              -- b = a or b = d
              have h1right:= ordered_pair_lemma x1.left x1.right x2.right
              replace h1right:= h1right hseteq_unsimp

              -- d = a or d = b
              have h2right:= ordered_pair_lemma x1.left x2.right x1.right
              replace h2right := h2right hseteq_unsimp.symm

              rcases h1right with hba | hbd
              · rcases h2right with hda | hdb
                · rw [hba, hda] -- d=a=b
                · exact hdb.symm -- d = b
              · exact hbd -- b = d


-- Coercion
instance OrderedPair.inst_coeObject : Coe OrderedPair Object where
  coe := OrderedPair.toObject

/-
  A technical operation, turning a object `x` and a set `Y` to a set `{x} × Y`, needed to define
  the full Cartesian product
-/
abbrev SetTheory.Set.slice (x:Object) (Y:Set) : Set :=
  Y.replace (P := fun y z ↦ z = (⟨x, y⟩:OrderedPair)) (by unfold partial_function;
                                                          simp_all)

@[simp]
theorem SetTheory.Set.mem_slice (x z:Object) (Y:Set) :
    z ∈ (SetTheory.Set.slice x Y) ↔ ∃ y:Y, z = (⟨x, y⟩:OrderedPair) := replacement_axiom _ _

/-- Definition 3.5.4 (Cartesian product) -/
abbrev SetTheory.Set.cartesian (X Y:Set) : Set :=
  union (X.replace (P := fun x z ↦ z = slice x Y) (by unfold partial_function;
                                                          simp_all))

/-- This instance enables the ×ˢ (\xs) notation for Cartesian product. -/
instance SetTheory.Set.inst_SProd : SProd Set Set Set where
  sprod := cartesian

example (X Y:Set) : X ×ˢ Y = SetTheory.Set.cartesian X Y := rfl

@[simp]
theorem SetTheory.Set.mem_cartesian (z:Object) (X Y:Set) :
    z ∈ X ×ˢ Y ↔ ∃ x:X, ∃ y:Y, z = (⟨x, y⟩:OrderedPair) := by
    simp only [inst_SProd, union_axiom]
    -- One mistake I've been making up until now: simp will break up x : X into
    -- x : U and x ∈ X, which is more tedious.
    -- I presume this is why we use simp only
    constructor
    · --- We need to show elements of X ×ˢ Y are (x,y) elems
      --- Thus, we need to decompose X ×ˢ Y structure
      -- Obtain a set S from the union
      intro ⟨S, hzS, hS⟩
      -- S is derived from the x that makes (x,y)
      rw [replacement_axiom] at hS
      obtain ⟨x,hx⟩ := hS
      use x -- simp_all will finish
      simp at hx --rw [coe_eq_iff] at hx
      -- z ∈ S means that (x,y)=z
      rw [hx] at hzS
      rw [mem_slice] at hzS
      -- We can retrieve y from S unfolded
      exact hzS

    · --- We need to show that (x,y) elem will be in X ×ˢ Y
      --- So we need to check it has the properties needed to fit into the folded sets
      rintro ⟨x,y,rfl⟩ -- z = (y,z). z just exists to contain (x,y), we can use rfl to sub directly
      -- We need some set S
      -- S is generated from x, and iterates over all y : Y
      use slice x Y
      -- Because left goal is easy to check, we could use refine ⟨by simp, ?_⟩
      constructor
      · -- Check that (x,y) ∈ S
        rw [mem_slice]; use y -- We already know S has (x, ?). We just have to select y : Y
      · -- Check that S ∈ X ×ˢ Y
        rw [replacement_axiom]; use x


-- Cleaning this up based on Tao's methodology
-- Main change: simp_all allows me to clean up conversions a bit smoother
theorem SetTheory.Set.partial_functions' {X Y:Set} :
  ∃ Z:Set, ∀ F:Object, F ∈ Z ↔
  (∃ X' Y':Set, X' ⊆ X ∧ Y' ⊆ Y ∧ ∃ f: X' → Y', F = f) := by
    let PX := powerset X
    let PY := powerset Y
    let f : Set → Set := fun A ↦ PY.replace
      (P:= fun x y ↦ ∃B: Set, (x.val = set_to_object B) ∧ ((B ^ A : Set) = y))
      (by unfold partial_function; simp_all)

    let G : Set := PX.replace
      (P := fun x y ↦ ∃ C: Set, (x.val = set_to_object C) ∧ y = union (f C) )
      (by unfold partial_function; simp_all)

    let H : Set := union G
    use H; intro x
    -- Unpacking H
    --unfold H G;
    rw [mem_union_powerset_replace_iff]


    constructor <;> intro h
    · --- Check whether an object in H is a partial function
      -- Union → x ∈ S, S ∈ G
      obtain ⟨A_in_PX, UfA, ⟨⟨A, hA_convert, h_UfA_convert⟩,h_UfA⟩⟩ := h
      use A; simp_all
      -- S = U f (A)
      -- Unpacking f: union over B^A sets
      unfold f at h_UfA
      rw [mem_union_powerset_replace_iff] at h_UfA
      -- Thus, x ∈ B^A
      obtain ⟨B_in_PY, BpowA, ⟨⟨B, hB_convert, h_BpowA_convert⟩,h_BpowA⟩⟩ := h_UfA
      simp_all; rw [← h_BpowA_convert] at h_BpowA
      -- Meaning, x is a function f: A → B
      rw [SetTheory.Set.powerset_axiom'] at h_BpowA
      constructor -- Because A and B are in their power sets, they're subsets as desired
      · rw [← mem_powerset']
        rw [← hA_convert]
        apply A_in_PX.property
      · use B
        rw [← mem_powerset']
        rw [← hB_convert]
        constructor
        · apply B_in_PY.property
        · obtain ⟨f,hf⟩:=h_BpowA -- And we already established that x is f : A → B
          use f; rw [hf]

    · -- Check whether any partial function is in H
      obtain ⟨A,B,hAX, hBY, f', rfl⟩ := h -- Retrieve our partial function
      simp; use A; simp [hAX] -- We identify that our partial function must be in U f A
      rw [mem_union_powerset_replace_iff]
      simp; use B; simp [hBY] -- And we match the B element of U f A

-- Allow us to retrieve x : X and y : Y from z ∈ X ×ˢ Y
-- Without having to first turn it into an ordered pair (x,y)

noncomputable abbrev SetTheory.Set.left {X Y:Set} (z : X ×ˢ Y) : X :=
  ((mem_cartesian _ _ _).mp z.property).choose

noncomputable abbrev SetTheory.Set.right {X Y:Set} (z:X ×ˢ Y) : Y :=
  (exists_comm.mp ((mem_cartesian _ _ _).mp z.property)).choose

-- Allows to convert directly from Subtype X ×ˢ Y to (x,y)
-- Without the intermediate steps
theorem SetTheory.Set.pair_eq_left_right {X Y:Set} (z : X ×ˢ Y) :
    z.val = (⟨ left z, right z ⟩:OrderedPair) := by
  have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ y, hy: z.val = (⟨ left z, y ⟩:OrderedPair)⟩ := this.choose_spec
  obtain ⟨ x, hx: z.val = (⟨ x, right z ⟩:OrderedPair)⟩ := (exists_comm.mp this).choose_spec
  simp_all [EmbeddingLike.apply_eq_iff_eq]

/-
Can use x:X and y:Y to directly get an element in the cartesian subtype
without intermediate steps-/
def SetTheory.Set.mk_cartesian {X Y:Set} (x:X) (y:Y) : X ×ˢ Y :=
  ⟨(⟨ x, y ⟩:OrderedPair), by simp⟩

-- Retrieve x and y from cartesian pair
@[simp]
theorem SetTheory.Set.left_of_mk_cartesian {X Y:Set} (x:X) (y:Y) :
    left (mk_cartesian x y) = x := by
  let z := mk_cartesian x y; have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ y', hy: z.val = (⟨ left z, y' ⟩:OrderedPair) ⟩ := this.choose_spec
  simp [z, mk_cartesian, Subtype.val_inj] at hy ⊢; rw [←hy.1]

@[simp]
theorem SetTheory.Set.right_of_mk_cartesian {X Y:Set} (x:X) (y:Y) :
    right (mk_cartesian x y) = y := by
  let z := mk_cartesian x y; have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ x', hx: z.val = (⟨ x', right z ⟩:OrderedPair) ⟩ := (exists_comm.mp this).choose_spec
  simp [z, mk_cartesian, Subtype.val_inj] at hx ⊢; rw [←hx.2]

-- Converting z into mk_cartesian gets the original
theorem SetTheory.Set.mk_cartesian_left_right_eq {X Y: Set} (z: X ×ˢ Y) :
    (mk_cartesian (left z) (right z)) = z := by
  rw [mk_cartesian, Subtype.mk.injEq, pair_eq_left_right]

/-- Example 3.5.5 / Exercise 3.6.5. There is a bijection between `X ×ˢ Y` and `Y ×ˢ X`. -/
noncomputable abbrev SetTheory.Set.prod_commutator (X Y:Set) : X ×ˢ Y ≃ Y ×ˢ X where
  toFun := fun z ↦ mk_cartesian (right z) (left z)
  invFun := fun z ↦ mk_cartesian (right z) (left z)
  left_inv := by unfold Function.LeftInverse
                 intro z; simp only
                 simp -- right (right left) => left, and vice versa
                 apply mk_cartesian_left_right_eq
  right_inv := by unfold Function.RightInverse
                  intro z; simp only
                  simp -- right (right left) => left, and vice versa
                  apply mk_cartesian_left_right_eq

/-- Example 3.5.5. A function of two variables can be thought of as a function of a pair. -/
noncomputable abbrev SetTheory.Set.curry_equiv {X Y Z:Set} : (X → Y → Z) ≃ (X ×ˢ Y → Z) where
  toFun := fun f z ↦ f (left z) (right z)
  invFun := fun f x y ↦ f ⟨ (⟨ x, y ⟩:OrderedPair), by simp ⟩
  left_inv := by intro; simp
  right_inv := by intro; simp [←pair_eq_left_right]

/-
Definition 3.5.7 (Ordered n-tuple and n-fold Cartesian product). Let n be a natural number. An ordered n-tuple (xihSi$n
(also denoted (x1, ... , xn)) is a collection of objects Xi, one for
every natural number i between 1 and n; we refer to Xi as the ith
component of the ordered n-tuple
-/

-- Tao decides to use an arbitrary indexing set, rather than naturals {i | 1 ≤ i ≤ n}

/-
We allow each element x_i to be from a different subtype X_i
Thus, the function X i tells us which subtype the i^{th} element pulls from
-/
abbrev SetTheory.Set.tuple {I:Set} {X: I → Set} (x: ∀ i, X i) : Object :=
  ((fun i ↦ ⟨ x i,
              by rw [mem_iUnion]; use i; exact (x i).property ⟩):
  I → iUnion I X) -- This is a function; we cast it to an object afterwards
  /-
  Each index goes to some element in one of the X_i sets
  Hence, we take the indexed union over all of them to get all the possible elements
  that we might output
  -/

abbrev SetTheory.Set.iProd {I:Set} (X: I → Set) : Set :=
  ((iUnion I X)^I).specify (fun z ↦ ∃ x: ∀ i, X i, z = tuple x)

theorem SetTheory.Set.mem_iProd {I: Set} {X: I → Set} (z:Object) :
    z ∈ iProd X ↔ ∃ x: ∀ i, X i, z = tuple x := by
    -- Unfold definitions
    -- "simp only" gets rid of tedious stuff like ↑⟨z, h⟩
    simp only [iProd, specification_axiom'']
    -- pq ↔ p can be reduced to p → q
    simp
    -- Now, we just need to show that tuple x is always part of the powerset B^A
    intro x hxz
    rw [hxz]; unfold tuple
    -- We can directly use the function outlined inside tuple
    -- (Alternatively we could've just used simp, but this is clearer)
    use (fun i ↦ ⟨ x i,
              by rw [mem_iUnion]; use i; exact (x i).property ⟩)

theorem SetTheory.Set.tuple_mem_iProd {I: Set} {X: I → Set} (x: ∀ i, X i) :
    tuple x ∈ iProd X := by rw [mem_iProd]; use x

-- Extensionality between tuples
-- If each element is the same (if we use the same index mapping), the tuples are the same
@[simp]
theorem SetTheory.Set.tuple_inj {I:Set} {X: I → Set} (x y: ∀ i, X i) :
tuple x = tuple y ↔ x = y := by
    constructor <;> intro h
    · ext i
      simp at h
      have := congr_fun h i -- Specialize tuple for i: any given xi and yi
      simp at this
      exact this
    · rw [h] -- Easy to just plug in x and y into the tuples

theorem SetTheory.Set.tuple_inj' {I:Set} {X: I → Set} (x y: ∀ i, X i) :
tuple x = tuple y → x = y := (tuple_inj x y).1

/-- Example 3.5.8. There is a bijection between `(X ×ˢ Y) ×ˢ Z` and `X ×ˢ (Y ×ˢ Z)`. -/
noncomputable abbrev SetTheory.Set.prod_associator (X Y Z:Set) : (X ×ˢ Y) ×ˢ Z ≃ X ×ˢ (Y ×ˢ Z) where
  toFun := fun p ↦ mk_cartesian (left (left p)) (mk_cartesian (right (left p)) (right p))
  invFun := fun p ↦ mk_cartesian (mk_cartesian (left p) (left (right p))) (right (right p))
  left_inv := by intro; simp [mk_cartesian_left_right_eq]
  right_inv := by intro; simp [mk_cartesian_left_right_eq]


noncomputable abbrev SetTheory.Set.singleton_iProd_equiv (i:Object) (X:Set) :
    iProd (fun _:({i}:Set) ↦ X) ≃ X where

  -- We want to retrieve the one element of our tuple, stored at index i

  toFun :=  fun x ↦ -- x is a *subtype*, we want the *function* it represents
                    -- We can get membership with x.property
                    -- mem_iProd converts x ∈ iProd into (x: function)
                    -- choose allows us to retrieve that function
                    let x_fun := ((mem_iProd x).1 x.property).choose
                    -- The function requires (i: {i}), which we can verify easily
                    let i_sub_I : ({i} : Set):= ⟨i, by simp⟩
    ⟨x_fun i_sub_I, -- Retrieval successful
    by apply (x_fun i_sub_I).property⟩ -- The function is defined to spit out (xi : X)
                                       -- So it's already built to verify our elem ∈ X

  invFun := fun x ↦
                    let i_sub_I : ({i}: Set) := ⟨i, by simp⟩
                    -- We want our tuple to have the type laid out by our type function
                    let X_type_fun := (fun _:({i}:Set) ↦ X)
                    -- Tuple should only return x
                    let x_fun : (∀ j, X_type_fun j) := fun _ ↦ x
                    let x_tup := tuple x_fun
                    -- Thankfully, we already know that a tuple built from x_fun
                    -- will be inside of iProd x_type_fun
                    ⟨x_tup, tuple_mem_iProd x_fun⟩

  left_inv := by  unfold Function.LeftInverse; intro x; simp
                  -- Turn subtype into object
                  ext; simp
                  -- Object into tuple
                  have prop := (mem_iProd x).1 x.property
                  have htup := prop.choose_spec
                  conv => rhs; rw [htup]
                  -- Tuple into function; grab an element of each function
                  rw [tuple_inj]; ext j
                  -- Both sides are the same function
                  let i_sub_I : ({i}: Set) := ⟨i, by simp⟩
                  let x_fun := prop.choose
                  change (x_fun i_sub_I).val = (x_fun j).val
                  -- Same input would mean same output
                  suffices i_sub_I=j by rw [this]
                  ext; change i = _
                  -- This function has only one input: so, both inputs are same
                  have := j.property
                  simp_all
  right_inv := by unfold Function.RightInverse; intro x;
                  -- invFun x creates a function f: f i = x (wrapped in subtype)
                  -- toFun f returns an output f i (wrapped in subtype)
                  simp only
                  -- toFun only requires the function from f, not the subtype
                  -- so we shed the inner subtype resulting from invFun
                  simp
                  -- We'll re-construct `⋯.choose ⟨i, ⋯⟩`
                  -- so that we can manipulate it directly
                  let i_sub_I : ({i}: Set) := ⟨i, by simp⟩
                  let X_type_fun := (fun _:({i}:Set) ↦ X)
                  let x_fun : (∀ j, X_type_fun j) := fun _ ↦ x
                  let x_tup := tuple x_fun
                  let invFun_x : iProd X_type_fun:=
                    ⟨x_tup, tuple_mem_iProd x_fun⟩
                  let x_prop := ((mem_iProd invFun_x).1 invFun_x.property)

                  -- Now, we can properly interact with the goal
                  change x_prop.choose i_sub_I = x

                  -- Retrieve the x_prop.choose function
                  let fun_tup:=  x_prop.choose_spec

                  -- Our goal is to convert our function to x_fun
                  -- Because x_fun i = x
                  suffices x_prop.choose = x_fun by rw [this]

                  unfold invFun_x at fun_tup; simp at fun_tup;
                  unfold x_tup at fun_tup
                  apply tuple_inj'
                  exact fun_tup.symm

/-- Example 3.5.10 -/
abbrev SetTheory.Set.empty_iProd_equiv (X: (∅:Set) → Set) : iProd X ≃ Unit where
  toFun := fun _ ↦ ()
  invFun := fun _ ↦ let fx: ∀ i, X i := fun i ↦ absurd i.property (SetTheory.Set.notMem_empty i.val)
                     let tup := tuple fx
                    ⟨tuple fx,
                      by apply (mem_iProd tup).2; use fx⟩
  left_inv := by  rw [Function.LeftInverse]; simp; intro x hx;
                  -- toFun gives us (), invFun(toFun) gives us (,)
                  -- We want to show that our original elem x must equal (,)
                  -- since that's the only elem of our type

                  -- We can retrieve (,) from iProd
                  have := (mem_iProd x).1 hx
                  obtain ⟨f, rfl⟩ := this
                  -- Cancel out tuple to just look at empty function
                  let fx: ∀ i, X i := fun i ↦ absurd i.property (SetTheory.Set.notMem_empty i.val)
                  change tuple fx = tuple f
                  suffices fx = f by rw [this]
                  -- Empty functions are vacuously equivalent: no elems
                  ext i
                  have := i.property
                  simp_all
  right_inv := by unfold Function.RightInverse;
                   intro x; simp-- Lean knows that Unit has only one element

/-- Example 3.5.10 -/
/-If our tuple only contains objects of a single type, it's equivalent to
a function using the same index as input, to that type-/
noncomputable abbrev SetTheory.Set.iProd_of_const_equiv (I:Set) (X: Set) :
    iProd (fun i:I ↦ X) ≃ (I → X) where
  toFun := fun t ↦ ((mem_iProd t).1 t.property).choose
                    -- Retrieve the function corresponding to tuple
  invFun := fun f ↦  let X_type_fun := (fun i:I ↦ X)
                      let x_fun : (∀ j, X_type_fun j) := fun j ↦ f j
                      ⟨tuple x_fun, by apply tuple_mem_iProd⟩
                      -- Turn function into a correctly typed function
                      -- and then into a tuple
  left_inv := by  unfold Function.LeftInverse; simp; intro x hx;
                  let prop := ((mem_iProd x).1 hx)--
                  let h_xtup := prop.choose_spec
                  conv => rhs; rw [h_xtup]
                  -- We used the same choose to get the same function on
                  -- both sides, so the sides are equivalent
  right_inv := by unfold Function.RightInverse; intro x; simp only
                  -- Re-construct invFun x
                  -- x is encoded in x_fun (useful later)
                  -- x_fun is stored in a tuple, which goes in a subtype
                  let X_type_fun := (fun i:I ↦ X)
                  let x_fun : (∀ j, X_type_fun j) := fun j ↦ x j
                  let invFun_x : iProd X_type_fun :=
                    ⟨tuple x_fun, by apply tuple_mem_iProd⟩
                  -- Re-construct the left side of the equality
                  -- invFun_x corresponds to a tuple
                  -- invFun_x.choose is the function that defines that tuple
                  let h_invFun:= ((mem_iProd invFun_x).1 invFun_x.property)
                  change h_invFun.choose = x
                  -- Retrieve tuple for invFun_x
                  have h:= h_invFun.choose_spec
                  unfold invFun_x at h
                  -- Retrieve x_fun from tuple using tuple injectivity
                  have h2:= tuple_inj' (x_fun) (h_invFun.choose) h
                  -- x_fun is definitionally equivalent to x
                  rw [← h2]

/- Example 3.5.10 -/


abbrev set01 := ({0,1}:Set)
abbrev zero: Object := 0
abbrev one : Object := 1
abbrev zero01 : set01 := ⟨0, by simp⟩
abbrev one01  : set01 := ⟨1, by simp⟩


--- Two different non-computable approaches

noncomputable instance (i: set01): Decidable (i = one01) := by
  if h : i.val = 1 then
    apply isTrue
    unfold one01
    ext
    simp [h]
  else
    apply isFalse
    intro heq
    have : i.val = 1 := by rw [heq]
    exact h this

lemma complete01 (i: set01): i = one01 ∨ i = zero01 := by
  have := i.property; simp at this
  rcases this with h | h
  · right; ext; simp [h]
  · left; ext; simp [h]

lemma mutual_exclusion01 (i: set01) : i ≠ one01 → i = zero01 := by
  intro h; have := i.property; simp at this
  unfold zero01; ext;
  rcases this with h0 | h1
  · apply h0
  · contrapose! h; ext; simp [h1]

noncomputable abbrev SetTheory.Set.iProd_equiv_prod (X: ({0,1}:Set) → Set) :
    iProd X ≃ (X ⟨ 0, by simp ⟩) ×ˢ (X ⟨ 1, by simp ⟩) where
  toFun := fun x ↦  let x_fun := ((mem_iProd x).1 x.property).choose
                    (mk_cartesian (x_fun zero01) (x_fun one01))

  invFun := fun y ↦  let y0 := left y
                      let y1 := right y
                      have y_fun : ∀ i, X i := fun i ↦ if h: i = one01
                      then ⟨y1, by  have:= y1.property;
                                    change ↑y1 ∈ X one01 at this;
                                    rw [h]; apply this⟩
                      else ⟨y0, by have h':=mutual_exclusion01 i h
                                   have : ↑y0 ∈ X zero01:= by apply y0.property;
                                   rw [h']; apply this⟩
                      let tup := tuple y_fun
                      ⟨tup, tuple_mem_iProd y_fun⟩
  left_inv  := by unfold Function.LeftInverse; intro x; simp; ext
                  -- Retrieve the construction of x as a tuple
                  have x_prop := (mem_iProd x.val).1 x.property
                  have x_fun := x_prop.choose
                  have htup := x_prop.choose_spec
                  -- Turn tuple into function
                  conv => rhs; rw [htup]
                  rw [tuple_inj]; ext j;

                  -- Check both cases for j
                  rcases (complete01 j) with h1 | h2
                  · simp [h1]
                    change (x_prop.choose one01).val = (x_prop.choose j).val
                    rw [h1]
                  · simp [h2]
                    change (x_prop.choose zero01).val = (x_prop.choose j).val
                    rw [h2]

  right_inv := by unfold Function.RightInverse Function.LeftInverse; intro y;

                  -- Reconstruct intermediate steps of function application
                  -- invFun
                  let y0 := left y
                  let y1 := right y
                  let y_fun : ∀ i, X i := fun i ↦ if h: i = one01
                  then ⟨y1, by  have:= y1.property;
                                change ↑y1 ∈ X one01 at this;
                                rw [h]; apply this⟩
                  else ⟨y0, by have h':=mutual_exclusion01 i h;
                               have : ↑y0 ∈ X zero01:= by apply y0.property;
                               rw [h']; apply this⟩
                  let tup := tuple y_fun
                  let x' :iProd X:= ⟨tup, tuple_mem_iProd y_fun⟩
                  -- toFun
                  let x_fun := ((mem_iProd x').1 x'.property).choose
                  let y' := (mk_cartesian (x_fun zero01) (x_fun one01))

                  -- Convert to match our intermediate steps
                  conv => lhs; rhs; simp; change x'
                  simp
                  change y' = y

                  -- We want to make the terms of y' and y match
                  ext
                  have h:= pair_eq_left_right y
                  have h':= pair_eq_left_right y'
                  rw [h,h']
                  suffices
                    left y = left y' ∧ right y = right y'
                    by obtain ⟨h1,h2⟩:=this; rw [h1,h2]
                  unfold y'; simp

                  -- If we can get it into y_fun format, we can use its
                  -- definition, and simplify down to the answer
                  have fun_eq : x_fun = y_fun := by
                    apply tuple_inj'
                    exact ((mem_iProd x').1 x'.property).choose_spec.symm

                  rw [fun_eq]
                  unfold y_fun;simp
                  unfold y0 y1
                  tauto


/-- Example 3.5.10 -/
/-
I'm gonna skip this one because I think the spirit of it is captured
in the previous example, and each of these takes forever to do.
As far as I'm concerned, mission accomplished.-/
/-
noncomputable abbrev SetTheory.Set.iProd_equiv_prod_triple (X: ({0,1,2}:Set) → Set) :
    iProd X ≃ (X ⟨ 0, by simp ⟩) ×ˢ (X ⟨ 1, by simp ⟩) ×ˢ (X ⟨ 2, by simp ⟩) where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
-/


/-
  Here we set up some an analogue of Mathlib `Fin n` types within the Chapter 3 Set Theory,
  with rudimentary API.
-/

abbrev SetTheory.Set.Fin (n:ℕ) : Set := nat.specify (fun m ↦ (m:ℕ) < n)

-- Membership in Fin n means you're less than n
-- Well, it means the natural number m your object corresponds to, is less than n
theorem SetTheory.Set.mem_Fin (n:ℕ) (x:Object) : x ∈ Fin n ↔ ∃ m, m < n ∧ x = m := by
  rw [specification_axiom''];
  constructor
  · intro ⟨ h1, h2 ⟩; use (⟨ x, h1 ⟩:nat); simp [h2]

    calc
      x = (⟨ x, h1 ⟩:nat) := rfl
      _ = _ := by congr; simp
  · intro ⟨ m, hm, h ⟩
    use (by rw [h, ←SetTheory.Object.ofnat_eq]; exact (m:nat).property)
    convert hm; simp [h, Equiv.symm_apply_eq]; rfl

-- Make an element (m : Fin n) from (n: ℕ) given that m < n
abbrev SetTheory.Set.Fin_mk (n m:ℕ) (h: m < n): Fin n := ⟨ m, by rw [mem_Fin]; use m ⟩

-- Having type Fin n means your corresponding natural is less than n

-- This theorem allows us to access the property of (i : Fin n) with type, rather than
-- membership.

-- (m: ℕ ) and (x: Fin n) represent the same conceptual "number" in two different types.
theorem SetTheory.Set.mem_Fin' {n:ℕ} (x:Fin n) : ∃ m, ∃ h : m < n, x = Fin_mk n m h := by
  obtain ⟨ m, hm, this ⟩ := (mem_Fin _ _).mp x.property; use m, hm
  simp [Fin_mk, ←Subtype.val_inj, this]


-- Retrieve the natural that (i: Fin n) represents
-- For example, (3: Fin 4) becomes (3: ℕ)
@[coe]
noncomputable abbrev SetTheory.Set.Fin.toNat {n:ℕ} (i: Fin n) : ℕ :=
  -- choose retrieves the witness: the natural number corresponding to (i: Fin n)
  (mem_Fin' i).choose

-- Use the above to actually complete the Fin n → ℕ coercion
noncomputable instance SetTheory.Set.Fin.inst_coeNat {n:ℕ} : CoeOut (Fin n) ℕ where
  coe := SetTheory.Set.Fin.toNat

-- Check that (i : Fin n) has the properties you expect, when cast to a natural
-- First: (i : ℕ ) < n
-- Second: You can re-create (i : Fin n) using (i : ℕ )
theorem SetTheory.Set.Fin.toNat_spec {n:ℕ} (i: Fin n) :
    -- choose_spec retrieves the proof that the witness satisfies the prop
    ∃ h : i < n, i = Fin_mk n i h := (mem_Fin' i).choose_spec

-- choose_spec is sufficient because we're using (i : ℕ) as the choice-generated witness,
-- and (i: Fin n) as the argument of mem_Fin'
-- which was slightly obscured by the implicit casting above
theorem SetTheory.Set.Fin.toNat_spec' {n:ℕ} (i: Fin n) :
    -- choose_spec retrieves the proof that the witness satisfies the prop
    ∃ h : (i : ℕ) < n, i = Fin_mk n (i: ℕ ) h := (mem_Fin' i).choose_spec

-- toNat_spec already retrieved the proof of (i : N)'s prop
-- toNat_lt goes another layer deeper and retrieves the proof embedded in the prop
-- Thus, we can directly access i < n
theorem SetTheory.Set.Fin.toNat_lt {n:ℕ} (i: Fin n) : i < n :=
    (toNat_spec i).choose

-- Check that when casting (i: Fin n) and (i: ℕ ) to object, you get the same thing
@[simp]
theorem SetTheory.Set.Fin.coe_toNat {n:ℕ} (i: Fin n) : ((i:ℕ):Object) = (i:Object) := by
  set j := (i:ℕ); obtain ⟨ h, h':i = Fin_mk n j h ⟩ := toNat_spec i; rw [h']

-- Check that casting (m : ℕ ) to Fin n, then ℕ again, gets the same number as the
-- original
@[simp]
theorem SetTheory.Set.Fin.toNat_mk {n:ℕ} (m:ℕ) (h: m < n) : (Fin_mk n m h : ℕ) = m := by
  have := coe_toNat (Fin_mk n m h)
  rwa [SetTheory.Object.natCast_inj] at this

-- If a number (m : ℕ) can be cast to Fin n, it can be cast to the "larger" type, Fin N
-- since m < n → m < N
abbrev SetTheory.Set.Fin_embed (n N:ℕ) (h: n ≤ N) (i: Fin n) : Fin N := ⟨ i.val, by
  have := i.property; rw [mem_Fin] at this ⊢
  obtain ⟨ m, hm, im ⟩ := this; use m, by linarith
⟩

/-
Lemma 3.5.12 (Finite choice). Let n ;:::: 1 be a natural number,
and for each natural number 1 ~ i ~ n, let Xi be a non-empty
set. Then there exists an n-tuple (xih < i < n such that Xi E Xi for
all 1 ~ i ~ n. In other words, if each Xi is non-empty, then the
set ITt:s;i:s;n Xi is also non-empty.
-/
lemma SetTheory.Set.fin0_empty: Fin 0 = (∅:Set) := by
  rw [eq_empty_iff_forall_notMem ];
  intro x hx;
  have:= (mem_Fin 0 x).1 hx
  simp_all -- (m : ℕ ) < 0 is impossible

-- Re-did this from scratch, rather than use Tao
theorem SetTheory.Set.finite_choice {n : ℕ } {X : Fin n → Set}
(hempty : ∀ i, X i ≠ ∅): iProd X ≠ ∅ := by
  induction' n with n hn
  · have h_Fin0mem : ∀ i, ¬ (i ∈ Fin 0) := by simp [fin0_empty]
    -- The empty tuple is in iProd X: just use an empty function to generate
    let f: ∀ i, X i := fun i ↦ absurd i.property (h_Fin0mem i.val)
    let tup := tuple f
    rw [nonempty_def]; use tup
    apply (mem_iProd tup).2
    use f

  · -- Grab the first n sets from n+1 sets
    let X' : Fin n → Set := fun i ↦ X (Fin_embed n (n+1) (by linarith) i)

    -- These sets are nonempty
    have hempty' : ∀ (i : (Fin n).toSubtype), X' i ≠ ∅ := by
      intro i; apply hempty
    specialize hn hempty'
    -- Get a function for the first n sets
    obtain ⟨tup', htup'⟩ := (nonempty_def).1 hn
    obtain ⟨f', hf'⟩ := (mem_iProd tup').1 htup'
    -- Get an element for the last set, n
    let n_Fin_np1 := Fin_mk (n+1) (n) (by linarith)
    specialize hempty n_Fin_np1
    obtain ⟨fn,h_fn⟩:= nonempty_def.1 hempty

    rw [ nonempty_def]

    -- Create the example function: use f' for f 0 through f n-1,
    -- use fn for f n
    let f : ∀ i, X i := fun i ↦
      if h : i = n then
        ⟨fn, by -- Check that X i = X n_Fin_np1
                suffices i = n_Fin_np1 by simp_all;
                unfold n_Fin_np1 Fin_mk; ext;
                simp [← Fin.coe_toNat, h] -- Type management
                ⟩
      else
        have := Fin.toNat_lt i
        have : i < n := by omega -- lt_of_le_of_ne (Nat.lt_succ_iff.mp (Fin.toNat_lt i)) h
        let i' := Fin_mk n i this
        ⟨f' i', by have := (f' i').property;
                   suffices X i = X' i' by simp_all;
                   -- X and X' have the same value, we just need to
                   -- check that i and i' do too
                   unfold i' Fin_mk X' Fin_embed; simp -- Type management
        ⟩
    -- Use example function to demonstrate finite choice
    use tuple f
    apply tuple_mem_iProd f


--@[simp]
--abbrev orderpairright (left right: U) := (({left, right}:Set):Object)

/-- Exercise 3.5.1, second part (requires axiom of regularity) -/
abbrev OrderedPair.toObject' : OrderedPair ↪ Object where
  toFun p := ({ p.left, (({p.left, p.right}:Set):Object) }:Set)
  inj' := by
    intro x1 x2 hseteq; simp at hseteq
    let a := x1.left; let b := x1.right
    let c := x2.left; let d := x2.right
    let ab: Set := {a, b}
    let cd: Set := {c, d}
    let abO: Object := ab
    let cdO: Object := cd

    have hseteq : ({a, abO}:Set)= ({c,cdO}:Set) := by unfold a abO ab c cdO cd;
                                                      apply hseteq

    suffices a=c ∧ b=d by
      unfold a b c d at this; obtain ⟨_,_⟩ := this; ext; simp_all; simp_all

    have ha_ab: a ∈ ab := by unfold a ab; simp; unfold a b; simp

    have ha_ne_ab: a ≠ abO := by
      have h2:= SetTheory.Set.not_mem_self ab
      by_contra h3
      unfold abO at h3; rw [← h3] at h2
      exact h2 ha_ab

    -- Both a and abO must match an element from the other set
    have ha_ccd: a ∈ ({a, abO}:Set) := by simp
    rw [hseteq] at ha_ccd
    rw [SetTheory.Set.mem_pair] at ha_ccd

    have hab_ccd: abO ∈ ({a, abO}:Set) := by simp;
    rw [hseteq] at hab_ccd
    rw [SetTheory.Set.mem_pair] at hab_ccd

    have hac : a = c := by
      by_contra h
      simp [h] at ha_ccd -- Assume that a = cd instead
      have habc : abO = c := by by_contra h'; simp_all --Thus ab = c

      -- This causes both sets to be inside each other!
      -- We can't have a ∈ {a,b} and {a,b} ∈ a
      have hcontra:= SetTheory.Set.not_mem_mem ab cd
      contrapose! hcontra;
      -- Since a isn't a set, it's easier to replace {a,b} ∈ a
      -- with c ∈ {c,d}
      unfold cdO at ha_ccd; unfold abO at habc
      rw [← ha_ccd]; rw [habc]
      -- a ∈ {a,b} and c ∈ {c,d} are both obviously true
      simp [ha_ab]
      unfold c cd; simp
      unfold c d; simp

    simp [hac]

    -- If a=c, then we know ab=cd, otherwise a=ab
    have habcd : ab = cd := by
      -- Convert to object
      rw [← SetTheory.Set.coe_eq_iff ab cd]
      -- If ab ≠ cd, then ab = c
      by_contra h
      unfold abO cdO at hab_ccd
      simp [h] at hab_ccd
      -- Which is a contradiction, because then a = c = ab
      unfold abO at ha_ne_ab
      simp_all

    -- Get b ∈ cd
    have: b ∈ ab := by unfold ab; simp;
    rw [habcd] at this; unfold cd at this; simp at this

    rcases this with hbc | hbd
    · -- Get d ∈ ab
      have: d ∈ cd := by unfold cd; simp
      rw [← habcd] at this; unfold ab at this; simp at this

      rcases this with hda | hdb
      · simp_all -- d=a=c=b
      · rw [hdb] -- d=b ↔ b=d

    · exact hbd -- Easy case


/-- An alternate definition of a tuple, used in Exercise 3.5.2 -/
structure SetTheory.Set.Tuple (n:ℕ) where
  X: Set
  f: Fin n → X
  surj: Function.Surjective f

/-
  Custom extensionality lemma for Exercise 3.5.2.
  Placing `@[ext]` on the structure would generate a lemma requiring proof of `t.x = t'.x`,
  but these functions have different types when `t.X ≠ t'.X`. This lemma handles that part.
-/
-- I think this means we don't want to have to risk comparing two functions
-- with different types.
@[ext]
lemma SetTheory.Set.Tuple.ext {n:ℕ} {t s:Tuple n}
    (hX : t.X = s.X)
    (hx : ∀ n : Fin n, ((t.f n):Object) = ((s.f n):Object)) :
    t = s := by
  have ⟨_, _, _⟩ := t; have ⟨_, _, _⟩ := s; subst hX; congr; ext; apply hx

/-- Exercise 3.5.2 -/
theorem SetTheory.Set.Tuple.eq {n:ℕ} (t s:Tuple n) :
    t = s ↔ ∀ n : Fin n, ((t.f n):Object) = ((s.f n):Object) := by
  constructor <;> intro h
  · intro m; rw [h]; -- Same tuple then you can just swap them
  · ext i
    · rw [ext_iff]; intro x -- Check each element of both sets
      constructor <;> intro hX
      · -- x ∈ X, we want x ∈ Z
        -- Get x = f i
        have := t.surj; unfold Function.Surjective at this
        obtain ⟨i,hi⟩ := this ⟨x, hX⟩
        -- f i = g i
        specialize h i
        -- g i ∈ Z
        have := (s.f i).property
        -- Convert back
        rw [← h, hi] at this;
        simp [this]

      · have := s.surj; unfold Function.Surjective at this
        obtain ⟨i,hi⟩ := this ⟨x, hX⟩
        specialize h i
        have := (t.f i).property
        rw [h, hi] at this;
        simp [this]
    · simp [h i]

--- Show that this creates a valid cartesian product
noncomputable abbrev SetTheory.Set.iProd_equiv_tuples (n:ℕ) (X: Fin n → Set) :
    iProd X ≃ { s:Tuple n // ∀ i, (s.f i:Object) ∈ X i } where
  -----------------------------------------
  toFun := fun t ↦
    have t_prop:= ((mem_iProd t).1 t.property)
    have g := t_prop.choose

    let Z := (Fin n).replace
      (P := fun x y ↦ y = g x  ) (by unfold partial_function; simp_all)

    let f : Fin n → Z := fun i ↦ ⟨g i, by rw [replacement_axiom]; use i⟩

    have f_surj : Function.Surjective f := by
      unfold Function.Surjective; intro z
      have hz:= z.property; rw [replacement_axiom] at hz
      obtain ⟨i, hi⟩:= hz
      use i; unfold f;
      ext; simp; rw [← hi]

    let tup := Tuple.mk Z f f_surj
    ⟨tup, by intro i; simp [tup]; unfold f; simp [(g i).property]⟩

  -----------------------------------------
  invFun := fun s ↦
    let tup := s.val;
    have htup := s.property
    let g : (i : (Fin n)) → X i:= fun i ↦ ⟨tup.f i, by
      specialize htup i; simp [tup, htup]⟩
    ⟨tuple g, by rw [mem_iProd]; use g ⟩

  -----------------------------------------
  left_inv := by
    unfold Function.LeftInverse; simp;
    intro t ht;
    have t_prop:= ((mem_iProd t).1 ht)
    have := t_prop.choose_spec
    conv => rhs; rw [this]
  -----------------------------------------

  right_inv := by
    unfold Function.RightInverse; intro s;
    -- Re-construct the forward steps:
    -- invFun
    let tup := s.val; let htup := s.property
    let g : (i : (Fin n)) → X i:= fun i ↦ ⟨tup.f i, by
      specialize htup i; simp [tup, htup]⟩
    let t : iProd X:= ⟨tuple g, by rw [mem_iProd]; use g; ⟩

    -- toFun
    have t_prop:= ((mem_iProd t).1 t.property)

    -- Simplify the invFun application
    conv => lhs; arg 1; simp; arg 1; change t

    -- Connect three functions that are the "same": f, g, t_prop.choose
    have h_fg: ∀ i, (g i).val = (s.val.f i).val := by
        intro i; unfold g; unfold tup; simp

    have h_cg := t_prop.choose_spec; unfold t at h_cg; simp only at h_cg
    replace h_cg: t_prop.choose = g := by apply tuple_inj'; symm; apply h_cg

    have h_cf : ∀ i, (t_prop.choose i).val = (s.val.f i).val := by
      intro i; simp [h_fg, h_cg]

    -- Compare Z = Z' and f = f'
    simp
    ext i
    · simp;
      rw [ext_iff]; intro z; rw [replacement_axiom]
      -- Convert ... to t_prop
      conv => lhs; rhs; intro i; rhs; arg 1; arg 1; change t_prop
      -- Then, convert t_prop.choose to f
      conv => lhs; arg 1; intro i; rw [h_cf i]

      constructor <;> intro h
      · -- z ∈ Z' → Output of f → z ∈ Z
        obtain ⟨i, hi⟩:= h
        have h:= (s.val.f i).property
        simp_all

      · -- z ∈ Z → f i = z → z ∈ Z'
        -- But we already know we're in Z' if it matches some (f i) term
        -- Which is always true given injectivity
        have hsurj := (s.val).surj; unfold Function.Surjective at hsurj
        specialize hsurj ⟨z,h⟩
        obtain ⟨i,hi⟩:= hsurj; use i
        simp [hi]

    · simp
      -- Again, retrieve t_prop
      conv => lhs; arg 1; arg 1; change t_prop
      exact h_cf i

/-
Exercise 3.5.3. Show that the definitions of equality for ordered pair and
ordered n-tuple obey the reflexivity, symmetry, and transitivity axioms.
-/

theorem OrderedPair.refl (p: OrderedPair) : p = p := by
  ext; repeat rfl

theorem OrderedPair.symm (p q: OrderedPair) : p = q ↔ q = p := by
  constructor <;>
  (intro h; rw [eq] at h; ext)
  · apply h.1.symm
  · apply h.2.symm
  · apply h.1.symm
  · apply h.2.symm

theorem OrderedPair.trans {p q r: OrderedPair} (hpq: p=q) (hqr: q=r) : p=r := by
  rw [eq] at *
  constructor
  · rw [hpq.1, hqr.1]
  · rw [hpq.2, hqr.2]

theorem SetTheory.Set.tuple_refl {I:Set} {X: I → Set} (f: ∀ i, X i) :
    tuple f = tuple f := by
    apply (tuple_inj _ _).2
    rfl

theorem SetTheory.Set.tuple_symm {I:Set} {X: I → Set} (f g: ∀ i, X i) :
    tuple f = tuple g ↔ tuple g = tuple f := by
    constructor <;>
    (intro h;
     apply (tuple_inj _ _).2
     replace h := (tuple_inj _ _ ).1 h
     apply h.symm)

theorem SetTheory.Set.tuple_trans {I:Set} {X: I → Set} {f g h: ∀ i, X i}
  (hab: tuple f = tuple g) (hbc : tuple g = tuple h) :
    tuple f = tuple h := by
    apply (tuple_inj _ _).2
    replace hab := (tuple_inj _ _ ).1 hab
    replace hbc := (tuple_inj _ _ ).1 hbc
    rw [hab, hbc]

/-
Exercise 3.5.4. Let A, B, C be sets. Show that A x ( B U C) = (A x B) U
(A x C), that A x (B n C) = (A x B) n (A x C), and that A x (B\C) =
(A x B)\ (A x C).
-/

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_union (A B C:Set) :
A ×ˢ (B ∪ C) = (A ×ˢ B) ∪ (A ×ˢ C) := by
  rw [ext_iff]; intro z
  -- Unfold unions/products
  rw [mem_union]; repeat rw [mem_cartesian]
  constructor <;> intro h
  · obtain ⟨x,y,ha⟩:= h
    have := y.property; rw [mem_union] at this
    rcases this with h | h
    · left; use x; use ⟨y.val, h⟩
    · right; use x; use ⟨y.val, h⟩
  · rcases h with h | h <;> (
    obtain ⟨x,y,h⟩:= h; use x;
    use ⟨y.val, ?_⟩)
    · rw [mem_union]; left; exact y.property
    · rw [mem_union]; right; exact y.property

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_inter (A B C:Set) :
A ×ˢ (B ∩ C) = (A ×ˢ B) ∩ (A ×ˢ C) := by
  rw [ext_iff]; intro z
  simp
  constructor <;> intro h
  · obtain ⟨x,hA,y,hBC, hz⟩ := h
    constructor <;> (use x; use hA; use y; )
    · use hBC.1
    · use hBC.2
  · obtain ⟨h1,h2⟩ := h
    obtain ⟨x,hA,y,hBC,hz⟩ := h1
    obtain ⟨x',hA',y',hBC',hz'⟩ := h2

    use x; use hA; use y;
    refine ⟨⟨hBC, ?_⟩, hz⟩
    rw [hz] at hz'
    simp at hz'
    simp [hz'.2, hBC']

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_diff (A B C:Set) :
A ×ˢ (B \ C) = (A ×ˢ B) \ (A ×ˢ C) := by
  rw [ext_iff]; intro z
  simp
  constructor <;> intro h
  · obtain ⟨x, hA, y, hBC, hz⟩ := h
    constructor
    · use x; use hA; use y; use hBC.1
    · intro a hA b hC
      by_contra hz'; rw [hz'] at hz
      simp at hz; rw [hz.2] at hC
      exact hBC.2 hC
  · obtain ⟨h1,h2⟩:=h
    obtain ⟨x, hA, y, hBC, hz⟩ := h1
    use x; use hA; use y
    refine ⟨ ⟨hBC,?_⟩, hz⟩
    by_contra hC
    specialize h2 x hA y hC
    contradiction


/-
Exercise 3.5.5. Let A, B, C, D be sets. Show that (A x B) n ( C x D) =
(An C) x (BnD). Is it true that (A x B)U (C x D)= (AUC) x (BUD)?
Is it true that (A x B)\(C x D)= (A\C) x (B\D)?
-/

/-- Exercise 3.5.5 -/
theorem SetTheory.Set.inter_of_prod (A B C D:Set) :
    (A ×ˢ B) ∩ (C ×ˢ D) = (A ∩ C) ×ˢ (B ∩ D) := by
  rw [ext_iff]; intro z; simp
  constructor <;> intro h
  · obtain ⟨h1,h2⟩ := h
    obtain ⟨x,hA,y,hB,hz⟩ := h1
    obtain ⟨a,hC,b,hD,hz'⟩:= h2

    have hz'' := hz
    rw [hz'] at hz
    simp at hz;
    rw [hz.1] at hC; rw [hz.2] at hD

    use x; use And.intro hA hC;
    use y;

  · obtain ⟨x,hAC, y, hBD, hz⟩:= h
    constructor <;> use x
    · use hAC.1; use y; use hBD.1
    · use hAC.2; use y; use hBD.2

/- Exercise 3.5.5 -/
def SetTheory.Set.union_of_prod :
  Decidable (∀ (A B C D:Set), (A ×ˢ B) ∪ (C ×ˢ D) = (A ∪ C) ×ˢ (B ∪ D)) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isFalse; push_neg
  let A :Set:= {1}
  let B :Set:= {1}
  let C :Set:= {2}
  let D :Set:= {2}
  use A; use B; use C; use D;
  simp; rw [ext_iff]; push_neg

  let x : OrderedPair := ⟨1,2⟩
  use x; right

  simp
  constructor
  · constructor <;>
    (intro a h1 b h2
     by_contra h
     unfold x at h
     simp at h;)
    · rw [← h.2] at h2
      simp [B] at h2
    · rw [← h.1] at h1
      simp [C] at h1
  · use 1; unfold A; simp;
    use 2; unfold D; simp
    rfl


/- Exercise 3.5.5 -/
def SetTheory.Set.diff_of_prod :
  Decidable (∀ (A B C D:Set), (A ×ˢ B) \ (C ×ˢ D) = (A \ C) ×ˢ (B \ D)) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isFalse; push_neg
  let A : Set := {1}
  let B : Set := {1}
  let C : Set := {1}
  let D : Set := {2}
  use A; use B; use C; use D
  simp; rw [ext_iff]; push_neg
  let x : OrderedPair := ⟨1,1⟩
  use x; left; simp
  constructor
  · constructor <;> simp [A, B, C, D, x]
  · intro a hA hC b hB hD;
    exfalso
    simp [A] at hA; simp [C] at hC
    contradiction


/-
Let A, B, C, D be non-empty sets. Show that A x B ~
c x D if and only if A ~ C and B ~ D, and that A x B = C x D if
and only if A = C and B = D. What happens if the hypotheses that
the A, B, C, D are all non-empty are removed?
-/

/--
  Exercise 3.5.6.
-/
theorem SetTheory.Set.prod_subset_prod {A B C D:Set}
  (hA: A ≠ ∅) (hB: B ≠ ∅) (hC: C ≠ ∅) (hD: D ≠ ∅) :
    A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D := by
    constructor <;> intro hABCD
    · constructor <;> (intro x h; rw [nonempty_def] at *;)
      · obtain ⟨y, hy⟩ := hB
        let z : OrderedPair := ⟨x,y⟩

        have : (z : Object) ∈ A ×ˢ B := by
          rw [mem_cartesian]; simp
          use x; use h; use y
        have zproperty := hABCD _ this

        rw [mem_cartesian] at zproperty
        obtain ⟨x',y', hz⟩:= zproperty

        simp [z] at hz;rw [hz.1];exact x'.property

      · obtain ⟨y, hy⟩ := hA
        let z : OrderedPair := ⟨y,x⟩

        have : (z : Object) ∈ A ×ˢ B := by
          rw [mem_cartesian]; simp
          use y; use hy; use x
        have zproperty := hABCD _ this

        rw [mem_cartesian] at zproperty
        obtain ⟨y',x', hz⟩:= zproperty

        simp [z] at hz;rw [hz.2];exact x'.property
    · intro z hz; simp at ⊢ hz
      obtain ⟨x,hx, y,hy,hz⟩ := hz
      replace hx := hABCD.1 _ hx
      replace hy := hABCD.2 _ hy
      use x; use hx; use y;


def SetTheory.Set.prod_subset_prod' :
  Decidable (∀ (A B C D:Set), A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D) := by
  apply isFalse; push_neg
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  let A : Set := {}
  let B : Set := {1}
  let C : Set := {1}
  let D : Set := {}
  use A; use B; use C; use D; left
  constructor
  · intro z hz
    rw [mem_cartesian] at hz
    obtain ⟨x,y,hz⟩ := hz
    have := x.property; unfold A at this;
    simp_all -- A is empty, so A ×ˢ B is empty

  · intro _ h
    have: 1 ∈ B := by simp [B]
    have := h _ this
    unfold D at *;
    simp_all -- We know that ¬ B ⊆ D because D is empty and B is not

/-
Exercise 3.5.7. Let X, Y be sets, and let 7rXxY-+X : X x Y ---+ X
and 11'XxY-+Y : X x Y ---+ Y be the maps 11'XxY-+x(x, y) := x and
'llXxY-+Y(x, y) := y; these maps are known as the co-ordinate functions
on X x Y. Show that for any functions f : Z ---+ X and g : Z ---+ Y, there
exists a unique function h: Z---+ X x Y such that 7rXxY-+X oh= f and
7lXxY-+Y oh= g. -/

/-- Exercise 3.5.7 -/
theorem SetTheory.Set.direct_sum {X Y Z:Set} (f: Z → X) (g: Z → Y) :
    ∃! h: Z → X ×ˢ Y, left ∘ h = f ∧ right ∘ h = g := by
    let p : Z → X ×ˢ Y := fun z ↦ mk_cartesian (f z) (g z)
    use p; simp
    constructor
    · constructor <;> (ext i; unfold p; simp)
    · intro q hqf hqg; ext i;
      repeat rw [pair_eq_left_right]
      simp
      rw [← hqf, ← hqg]
      simp

/-
Exercise 3.5.8. Let X 1, ... , Xn be sets. Show that the Cartesian product
n~=l xi is empty if and only if at least one of the xi is empty.
-/

/-- Exercise 3.5.8 -/
@[simp]
theorem SetTheory.Set.iProd_empty_iff {n:ℕ} {X: Fin n → Set} :
    iProd X = ∅ ↔ ∃ i, X i = ∅ := by
    apply Iff.intro <;> (intro h; contrapose! h)
    · rw [nonempty_def]
      conv at h => intro i; rw [nonempty_def]

      let f : ∀ i, X i := fun i ↦ ⟨(h i).choose, (h i).choose_spec⟩
      let tup:= tuple f; use tup
      rw [mem_iProd]; use f

    · intro i; rw [nonempty_def] at *
      obtain ⟨tup, htup⟩ := h
      rw [mem_iProd] at htup
      obtain ⟨f, hf⟩ := htup
      use f i
      apply (f i).property

/-
Exercise 3.5.9. Suppose that I and J are two sets, and for all a E I let
Aa be a set, and for all (3 E J let Bf3 be a set. Show that (Uaer Aa) n
(U{3EJ B[j) = U(a,{j)ElxJ(Aa n B[j)·
-/

/-- Exercise 3.5.9-/
theorem SetTheory.Set.iUnion_inter_iUnion {I J: Set} (A: I → Set) (B: J → Set) :
    (iUnion I A) ∩ (iUnion J B) = iUnion (I ×ˢ J)
    (fun k ↦ (A (left k)) ∩ (B (right k))) := by
    rw [ext_iff]; intro x
    simp only [mem_iUnion, mem_inter_iff]
    constructor <;> intro h
    · obtain ⟨ ⟨i,hi⟩ , ⟨j,hj⟩ ⟩ := h
      let k := mk_cartesian i j
      use k
      unfold k; simp_all
    · obtain ⟨i,hA,hB⟩ := h
      constructor
      · use left i
      · use right i

/-
Exercise 3.5.10. If f : X ---+ Y is a function, define the graph of f to
be the subset of X x Y defined by {(x, f(x)) : x E X}. Show that two
functions f : X ---+ Y, J : X ---+ Y are equal if and only if they have the
same graph. Conversely, if G is any subset of X x Y with the property
that for each x E X, the set {y E Y : (x, y) E G} has exactly one
element (or in other words, G obeys the vertical line test), show that
there is exactly one function f :X---+ Y whose graph is equal to G.
-/

def SetTheory.Set.graph {X Y : Set} (f : X → Y) : Set :=
  (X ×ˢ Y).specify (fun z ↦ f (left z) = right z)

theorem SetTheory.Set.graph_inj {X Y:Set} (f f': X → Y) :
    graph f = graph f' ↔ f = f' := by
    constructor <;> intro h
    · ext x
      let z := mk_cartesian x (f x)
      have hz : z.val ∈ graph f := by
        unfold graph; rw [specification_axiom''];
        use z.property; simp;

      rw [h] at hz
      unfold graph at hz; rw [specification_axiom'] at hz
      simp at hz
      rw [hz]

    · rw [h]

abbrev vertline (X Y G : Set):= ∀ x:X, ∃! y:Y, ((⟨x,y⟩:OrderedPair):Object) ∈ G

theorem SetTheory.Set.is_graph {X Y G:Set} (hG: G ⊆ X ×ˢ Y)
  (hvert: vertline X Y G) :
    ∃! f: X → Y, G = graph f := by
    unfold vertline at hvert
    let f : X → Y := fun x ↦ (hvert x).choose
    use f; simp
    constructor
    · rw [ext_iff]; intro z
      constructor <;> intro h
      · --- z ∈ graph f
        -- First: z ∈ X ×ˢ Y
        unfold graph; rw [specification_axiom'']
        have hz := hG _ h
        use hz

        -- Decompose z = (x,y)
        have hz' := hz
        rw [mem_cartesian] at hz'
        obtain ⟨x,y,hz'⟩ := hz'

        -- Apply z = (x,y) to the soln
        conv => lhs; arg 1; arg 1; arg 1; rw [hz']
        conv => rhs; arg 1; arg 1; rw [hz']
        simp
        -- We can see our goal is to get f x = y
        -- Our approach will be to use uniqueness of (x,b) ∈ G
        -- We'll use f x = b = y

        -- Uniqueness of (x,b)
        specialize hvert x
        obtain ⟨b, hb1, hb2⟩ := hvert;

        have hfx := hb2 (f x);
        have hy  := (hb2 y);
        simp at hfx hy

        -- Get f x = b
        rw [← hz'] at hy
        specialize hy h
        rw [hy]


        apply hfx
        apply (hvert x).choose_spec


      · unfold graph at h; rw [specification_axiom''] at h
        obtain ⟨h, hz⟩:=h

        rw [mem_cartesian] at h
        obtain ⟨x,y,h⟩:= h

        conv at hz => lhs; arg 1; arg 1; arg 1; rw [h]
        conv at hz => rhs; arg 1; arg 1; rw [h]
        simp at hz

        have := (hvert x).choose_spec
        rw [← hz] at h; unfold f at h
        rw [h]; exact this


    · intro g hg; ext x
      unfold graph at hg;
      unfold f;

      -- (x,f(x)) ∈ G
      have:= (hvert x).choose_spec
      conv at this => arg 1; rw [hg]

      -- (a,b) ∈ G means b = g(a)
      rw [specification_axiom''] at this
      obtain ⟨hXY, h⟩ := this
      -- So, f(x) = g(x)
      simp at h

      rw [h]


/--
  Exercise 3.5.11. This trivially follows from `SetTheory.Set.powerset_axiom`, but the
  exercise is to derive it from `SetTheory.Set.exists_powerset` instead.
-/
theorem SetTheory.Set.powerset_axiom'' (X Y:Set) :
    ∃! S:Set, ∀(F:Object), F ∈ S ↔ ∃ f: Y → X, f = F := by
    -- Get every possible set of pairings (x,y)
    have := exists_powerset (X ×ˢ Y)
    obtain ⟨P, hP⟩ := this

    -- Filter for the vertical line test: we have all of our graphs
    let GG := P.specify (
      fun z ↦ let prop:= (hP z).1 z.property;
              let Z := prop.choose;
              vertline X Y Z)

    -- Convert each graph to a function

    -- Show that Z corresponds to a graph G we can use for is_graph
    have: ∀ Z, Z ∈ GG → ∃ G, (G ⊆ X ×ˢ Y) ∧ (Z = G):= by
      intro Z hZ; unfold GG at hZ;
      rw [specification_axiom''] at hZ
      obtain ⟨h,_⟩ := hZ
      have := (hP _).1 h
      obtain ⟨G, hG⟩ := this


      sorry

    let FF := GG.replace (P:= fun x F ↦

      sorry) sorry


    sorry





end mySetAxioms
