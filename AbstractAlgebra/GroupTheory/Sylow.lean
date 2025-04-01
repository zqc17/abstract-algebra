import Mathlib.GroupTheory.Sylow

variable {G : Type*} [Group G] [Finite G]

/-- If there is only one Slyow p-group then it is normal. -/
lemma sylow_normal_of_card_eq_one {p : ℕ} [Fact p.Prime] (h : Nat.card (Sylow p G) = 1) :
    (default : Sylow p G).Normal := by
  rwa [← Subgroup.normalizer_eq_top_iff, ← Subgroup.index_eq_one, ← Sylow.card_eq_index_normalizer]
