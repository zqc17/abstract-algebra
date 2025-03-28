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

lemma lcm_distrib_gcd {x y z : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    x.lcm (y.gcd z) = (x.lcm y).gcd (x.lcm z) := by
  apply Nat.eq_of_factorization_eq _ _
  apply congr_fun
  rw [Nat.factorization_gcd]
  repeat rw [Nat.factorization_lcm]
  rw [Nat.factorization_gcd, sup_inf_left]
  all_goals apply_rules [Nat.gcd_ne_zero_left, Nat.lcm_ne_zero]

lemma gcd_distrib_lcm₁ {x y z : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    (x.gcd y).lcm (x.gcd z) ∣ x.gcd (y.lcm z) := by
  rw [← Nat.factorization_le_iff_dvd, Nat.factorization_gcd,
    Nat.factorization_lcm, Nat.factorization_lcm, Nat.factorization_gcd,
    Nat.factorization_gcd]
  · exact le_inf_sup
  all_goals try apply Nat.lcm_ne_zero
  all_goals try apply Nat.gcd_ne_zero_right
  all_goals first | assumption | exact Nat.lcm_ne_zero hy hz

lemma gcd_distrib_lcm₂ {x y z : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    x.gcd (y.lcm z) ∣ (x.gcd y).lcm (x.gcd z) := by
  rw [← Nat.factorization_le_iff_dvd, Nat.factorization_gcd,
    Nat.factorization_lcm, Nat.factorization_lcm, Nat.factorization_gcd,
    Nat.factorization_gcd, ← inf_sup_left]
  all_goals try apply Nat.lcm_ne_zero
  all_goals try apply Nat.gcd_ne_zero_right
  all_goals first | assumption | exact Nat.lcm_ne_zero hy hz

lemma gcd_distrib_lcm {x y z : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    x.gcd (y.lcm z) = (x.gcd y).lcm (x.gcd z) :=
  (Nat.dvd_antisymm
    (gcd_distrib_lcm₁ hx hy hz) (gcd_distrib_lcm₂ hx hy hz)).symm

lemma gcd_distrib_lcm_aux₁ {y z : ℤ} :
    (0 : ℤ).gcd (y.lcm z) = ((0 : ℤ).gcd y).lcm ((0 : ℤ).gcd z) := by
  simp only [Int.gcd_zero_left, Int.natAbs_ofNat]; rfl

lemma gcd_distrib_lcm_aux₂ {x z : ℤ} :
    x.gcd ((0 : ℤ).lcm z) = (x.gcd (0 : ℤ)).lcm (x.gcd z) := by
  simp only [Int.lcm_zero_left, CharP.cast_eq_zero, Int.gcd_zero_right]
  exact Nat.dvd_antisymm (Nat.dvd_lcm_left x.natAbs (x.gcd z))
    <| Nat.lcm_dvd_iff.2 ⟨Nat.dvd_refl x.natAbs, Nat.gcd_dvd_left x.natAbs z.natAbs⟩

lemma gcd_distrib_lcm_aux₃ {x y : ℤ} :
    x.gcd (y.lcm (0 : ℤ)) = (x.gcd y).lcm (x.gcd (0 : ℤ)) := by
  simp only [Int.lcm_zero_right, CharP.cast_eq_zero, Int.gcd_zero_right]
  exact Nat.dvd_antisymm (Nat.dvd_lcm_right (x.gcd y) x.natAbs)
    <| Nat.lcm_dvd_iff.2 ⟨Nat.gcd_dvd_left x.natAbs y.natAbs, Nat.dvd_refl x.natAbs⟩

lemma gcd_distrib_lcm' {x y z : ℤ} :
    x.gcd (y.lcm z) = (x.gcd y).lcm (x.gcd z) := by
  by_cases hx : x = 0
  · rw [hx, gcd_distrib_lcm_aux₁]
  · by_cases hy : y = 0
    · rw [hy, gcd_distrib_lcm_aux₂]
    · by_cases hz : z = 0
      · rw [hz, gcd_distrib_lcm_aux₃]
      · exact gcd_distrib_lcm (Int.natAbs_ne_zero.mpr hx)
          (Int.natAbs_ne_zero.mpr hy) (Int.natAbs_ne_zero.mpr hz)
