import Mathlib.NumberTheory.Zsqrtd.GaussianInt

open GaussianInt Zsqrtd

/-- Formula to calculate divison of `GaussianInt`. -/
lemma div_eq (x y : GaussianInt) : x / y =
    ⟨round ((x.re * y.re + x.im * y.im) / (y.re * y.re + y.im * y.im) : ℚ),
    round ((-x.re * y.im + x.im * y.re) / (y.re * y.re + y.im * y.im) : ℚ)⟩ := by
  rw [div_def, star_mk, norm_def, mul_re, mul_im]
  simp
