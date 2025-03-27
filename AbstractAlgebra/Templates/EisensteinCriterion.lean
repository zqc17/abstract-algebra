import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.EisensteinCriterion
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

open Polynomial

attribute [local simp] coeff_X

/-- **Problem**: Apply Eisenstein's criterion (Theorem 5.7) to verify whether the polynomial $4x^5 + 5x^3 - 15x + 20$ is irreducible. -/
noncomputable def p : ℤ[X] := C 4 * X ^ 5 + C 5 * X ^ 3 - C 15 * X + C 20

/-- Firstly, we show that degree of $p(x)$ is $5$. -/
lemma p_natDegree : p.natDegree = 5 := by rw [p]; compute_degree!

/-- It's clear that $p(x)$ is non-zero. -/
lemma p_nezero : p ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by norm_num [p_natDegree])

/-- The leading coefficient of $p(x)$ is $4$. -/
lemma p_leadingCoeff : p.leadingCoeff = 4 := by
  rw [leadingCoeff, p_natDegree, p]; simp

/-- The support set of $p(x)$ is $\{5,3,1,0\}$. -/
lemma p_support : p.support = {5, 3, 1, 0} := by
  ext i
  constructor
  . intro hi
    contrapose! hi
    rcases lt_or_le 5 i with h | h
    . have : p.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by rwa [p_natDegree])
      simpa using this
    . interval_cases i <;> simp at hi <;> simp [p]
  . intro hi
    simp at hi
    casesm* _ ∨ _
    all_goals simp [hi, p]

/-- Given above data, we can prove $p(x)$ is irreducible. -/
theorem irreducible_of_eis : Irreducible p:= by
  -- Apply Eisenstein's criterion.
  apply irreducible_of_eisenstein_criterion (P := Ideal.span {5})
  . -- Prove that $\langle 5\rangle$ is a prime ideal.
    rw [Ideal.span_singleton_prime (by norm_num)]
    norm_num
  . -- Prove that $5$ does not divide leading coefficient of $p(x)$.
    rw [Ideal.mem_span_singleton, p_leadingCoeff]
    norm_num
  . -- Prove that $5$ divides all coefficients of $p(x)$ except the leading coefficient.
    intro n hn
    rw [degree_eq_natDegree p_nezero, p_natDegree] at hn
    norm_cast at hn
    rw [Ideal.mem_span_singleton]
    interval_cases n <;> simp [p] <;> norm_num
  . -- Prove that $p(x)$ is not a constant polynomial.
    rw [degree_eq_natDegree p_nezero, p_natDegree]
    norm_num
  . -- Prove that $5^2$ does not divide the constant coefficient of $p(x)$.
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    simp [p]
    norm_num
  . -- Prove that $p(x)$ is primitive.
    rw [isPrimitive_iff_content_eq_one, content, p_support]
    simp [p]
    decide
