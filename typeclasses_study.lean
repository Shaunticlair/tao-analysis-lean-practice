--- This isn't my code, it's drawn from https://lean-lang.org/functional_programming_in_lean/type-classes/pos.html
--- Used for learning purposes

inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos

class Plus (α : Type) where
  plus : α → α → α

instance : Plus Nat where
  plus := Nat.add

open Plus (plus)

def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)

instance : Plus Pos where
  plus := Pos.plus

instance : Add Pos where
  add := Pos.plus

def Pos.mul : Pos → Pos → Pos
  | Pos.one, k => k
  | Pos.succ n, k => n.mul k + k

instance : Mul Pos where
  mul := Pos.mul

--- Handling literal numbers

class OfNat (α : Type) (_ : Nat) where
  ofNat : α

instance : OfNat Pos (n + 1) where
ofNat :=
  let rec natPlusOne : Nat → Pos
    | 0 => Pos.one
    | k + 1 => Pos.succ (natPlusOne k)
  natPlusOne n
