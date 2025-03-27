import Mathlib


variable {α β : Type} [LinearOrder β] [Zero β]

open Finsupp in
/-- For any finsupp function from `α` to `β`, if there has instance `[LinearOrder β]`,
  then `Finsupp α β` is a distrib lattice. -/
noncomputable instance : DistribLattice (Finsupp α β) where
  __ := inferInstanceAs (Lattice (Finsupp α β))
  le_sup_inf := by
    simp [le_def]
    intro x y z i
    rcases le_total (x i) (y i) <;> rcases le_total (x i) (z i) <;> tauto
