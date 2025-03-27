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

lemma vp_lcm {p a b : ℕ} (hpp : p.Prime) (ha : 0 < a) (hb : 0 < b) :
    padicValNat p (a.lcm b) = max (padicValNat p a) (padicValNat p b) := by
  simp [← Nat.factorization_def _ hpp, Nat.factorization_lcm ha.ne' hb.ne']

lemma vp_gcd {p a b : ℕ} (hpp : p.Prime) (ha : 0 < a) (hb : 0 < b) :
    padicValNat p (a.gcd b) = min (padicValNat p a) (padicValNat p b) := by
  simp [← Nat.factorization_def _ hpp, Nat.factorization_gcd ha.ne' hb.ne']

lemma gcd_distrib_lcm {x y z : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    (x.lcm y).gcd (x.lcm z) ∣ x.lcm (y.gcd z) := by
  rw [←Nat.factorization_le_iff_dvd, Nat.factorization_gcd]
  repeat rw [Nat.factorization_lcm]
  rw [Nat.factorization_gcd]
  simp [le_sup_inf]
  all_goals try assumption
  all_goals try apply Nat.lcm_ne_zero
  all_goals try assumption
  all_goals try apply Nat.gcd_ne_zero_left hy
  exact Nat.gcd_ne_zero_left <| Nat.lcm_ne_zero hx hy
