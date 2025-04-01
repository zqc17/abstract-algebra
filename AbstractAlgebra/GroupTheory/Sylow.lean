import Mathlib.GroupTheory.Sylow

variable {G : Type*} [Group G] [Finite G]

/-- If there is only one Slyow p-group then it is normal. -/
lemma sylow_normal_of_card_eq_one {p : ℕ} [Fact p.Prime] (h : Nat.card (Sylow p G) = 1) :
    (default : Sylow p G).Normal := by
  rwa [← Subgroup.normalizer_eq_top_iff, ← Subgroup.index_eq_one, ← Sylow.card_eq_index_normalizer]

/-- Index of Sylow p-group is $|G|/p^k$. -/
lemma index_sylow_eq_ord_compl {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    P.index = Nat.card G / p ^ (Nat.card G).factorization p := by
  apply Nat.eq_div_of_mul_eq_left
  . have : 2 ≤ p := Nat.Prime.two_le Fact.out
    positivity
  . rw [mul_comm]
    convert Subgroup.card_mul_index (P : Subgroup G)
    exact (Sylow.card_eq_multiplicity P).symm
