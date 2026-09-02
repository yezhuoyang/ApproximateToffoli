/-
  ApproxToffoli.Helpers
  Auxiliary lemmas for the base case proof:
  - Cauchy-Schwarz for two complex terms
  - Properties of 2×2 unitary matrices
-/

import ApproxToffoli.Defs
import ApproxToffoli.Circuit
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open Complex Matrix

noncomputable section

/-! ## Cauchy-Schwarz for two complex terms -/

lemma cauchy_schwarz_two (a b x y : ℂ) :
    Complex.normSq (a * x + b * y) ≤
      (Complex.normSq a + Complex.normSq b) * (Complex.normSq x + Complex.normSq y) := by
  suffices h : 0 ≤ (Complex.normSq a + Complex.normSq b) *
      (Complex.normSq x + Complex.normSq y) -
      Complex.normSq (a * x + b * y) by linarith
  have h1 := sq_nonneg (a.re * y.re + a.im * y.im - b.re * x.re - b.im * x.im)
  have h2 := sq_nonneg (a.re * y.im - a.im * y.re - b.re * x.im + b.im * x.re)
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
             Complex.mul_re, Complex.mul_im]
  nlinarith [h1, h2, sq_nonneg a.re, sq_nonneg a.im, sq_nonneg b.re, sq_nonneg b.im,
             sq_nonneg x.re, sq_nonneg x.im, sq_nonneg y.re, sq_nonneg y.im]

/-! ## 2×2 unitary matrix properties -/

/-- Helper to convert star(z)*z to normSq in ℂ -/
private lemma star_mul_self (z : ℂ) :
    star z * z = ↑(Complex.normSq z) := by
  change starRingEnd ℂ z * z = ↑(normSq z)
  rw [mul_comm, Complex.mul_conj]

/-- For a 2×2 unitary, |u₀₀|² + |u₁₀|² = 1 (column 0 is unit) -/
lemma unitary2_col0_norm (u : Mat2) (hu : IsUnitary2 u) :
    Complex.normSq (u 0 0) + Complex.normSq (u 1 0) = 1 := by
  unfold IsUnitary2 at hu
  have h00 : (u.conjTranspose * u) 0 0 = 1 := by
    simp [hu]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two] at h00
  -- h00 : star(u 0 0) * u 0 0 + star(u 1 0) * u 1 0 = 1
  rw [star_mul_self, star_mul_self] at h00
  exact_mod_cast h00

/-- For a 2×2 unitary, |u₀₁|² + |u₁₁|² = 1 (column 1 is unit) -/
lemma unitary2_col1_norm (u : Mat2) (hu : IsUnitary2 u) :
    Complex.normSq (u 0 1) + Complex.normSq (u 1 1) = 1 := by
  unfold IsUnitary2 at hu
  have h11 : (u.conjTranspose * u) 1 1 = 1 := by
    simp [hu]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two] at h11
  rw [star_mul_self, star_mul_self] at h11
  exact_mod_cast h11

/-- For a 2×2 unitary, columns are orthogonal -/
lemma unitary2_col_ortho (u : Mat2) (hu : IsUnitary2 u) :
    starRingEnd ℂ (u 0 0) * u 0 1 + starRingEnd ℂ (u 1 0) * u 1 1 = 0 := by
  unfold IsUnitary2 at hu
  have h01 : (u.conjTranspose * u) 0 1 = 0 := by
    simp [hu]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two] at h01
  exact h01

/-- For a 2×2 unitary, |u₀₀|² = |u₁₁|² -/
lemma unitary2_diag_normSq_eq (u : Mat2) (hu : IsUnitary2 u) :
    Complex.normSq (u 0 0) = Complex.normSq (u 1 1) := by
  have h0 := unitary2_col0_norm u hu
  have h1 := unitary2_col1_norm u hu
  have hortho := unitary2_col_ortho u hu
  -- From orthogonality: conj(u00)*u01 = -conj(u10)*u11
  -- Taking normSq: |u00|²|u01|² = |u10|²|u11|²
  have hortho_sq : Complex.normSq (u 0 0) * Complex.normSq (u 0 1) =
      Complex.normSq (u 1 0) * Complex.normSq (u 1 1) := by
    have heq : starRingEnd ℂ (u 0 0) * u 0 1 = -(starRingEnd ℂ (u 1 0) * u 1 1) := by
      linear_combination hortho
    have : Complex.normSq (starRingEnd ℂ (u 0 0) * u 0 1) =
        Complex.normSq (starRingEnd ℂ (u 1 0) * u 1 1) := by
      rw [heq, Complex.normSq_neg]
    simp only [map_mul, Complex.normSq_conj] at this
    exact this
  -- With a+c=1, b+d=1, a·b = c·d we get a=d
  nlinarith [Complex.normSq_nonneg (u 0 0), Complex.normSq_nonneg (u 0 1),
             Complex.normSq_nonneg (u 1 0), Complex.normSq_nonneg (u 1 1)]

/-- For a 2×2 unitary, |u₀₁|² = |u₁₀|² -/
lemma unitary2_offdiag_normSq_eq (u : Mat2) (hu : IsUnitary2 u) :
    Complex.normSq (u 0 1) = Complex.normSq (u 1 0) := by
  have h0 := unitary2_col0_norm u hu
  have h1 := unitary2_col1_norm u hu
  have hd := unitary2_diag_normSq_eq u hu
  linarith

/-- For a 2×2 unitary u, |Tr(u)|² + |u₀₁ + u₁₀|² ≤ 4 -/
lemma unitary2_trace_off_bound (u : Mat2) (hu : IsUnitary2 u) :
    Complex.normSq (u 0 0 + u 1 1) + Complex.normSq (u 0 1 + u 1 0) ≤ 4 := by
  -- |a+b|² + |a-b|² = 2(|a|²+|b|²) for any complex a,b
  have expand1 : Complex.normSq (u 0 0 + u 1 1) + Complex.normSq (u 0 0 - u 1 1) =
      2 * Complex.normSq (u 0 0) + 2 * Complex.normSq (u 1 1) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
               Complex.sub_re, Complex.sub_im]; ring
  have expand2 : Complex.normSq (u 0 1 + u 1 0) + Complex.normSq (u 0 1 - u 1 0) =
      2 * Complex.normSq (u 0 1) + 2 * Complex.normSq (u 1 0) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
               Complex.sub_re, Complex.sub_im]; ring
  nlinarith [Complex.normSq_nonneg (u 0 0 - u 1 1),
             Complex.normSq_nonneg (u 0 1 - u 1 0),
             unitary2_col0_norm u hu, unitary2_col1_norm u hu]

/-- For a 2×2 unitary, |Tr(u)|² ≤ 4|u₀₀|² -/
lemma unitary2_trace_bound_by_diag (u : Mat2) (hu : IsUnitary2 u) :
    Complex.normSq (u 0 0 + u 1 1) ≤ 4 * Complex.normSq (u 0 0) := by
  have heq := unitary2_diag_normSq_eq u hu
  have h_par : Complex.normSq (u 0 0 + u 1 1) + Complex.normSq (u 0 0 - u 1 1) =
      2 * Complex.normSq (u 0 0) + 2 * Complex.normSq (u 1 1) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
               Complex.sub_re, Complex.sub_im]; ring
  nlinarith [Complex.normSq_nonneg (u 0 0 - u 1 1)]

/-! ## Three-term normSq bound -/

/-- |x + y + z|² ≤ 3(|x|² + |y|² + |z|²).
    Proof: the difference = |x-y|² + |x-z|² + |y-z|² ≥ 0. -/
lemma normSq_add3_le (x y z : ℂ) :
    Complex.normSq (x + y + z) ≤ 3 * (Complex.normSq x + Complex.normSq y + Complex.normSq z) := by
  suffices h : 0 ≤ 3 * (Complex.normSq x + Complex.normSq y + Complex.normSq z) -
      Complex.normSq (x + y + z) by linarith
  have h1 := Complex.normSq_nonneg (x - y)
  have h2 := Complex.normSq_nonneg (x - z)
  have h3 := Complex.normSq_nonneg (y - z)
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith [h1, h2, h3,
             sq_nonneg (x.re - y.re), sq_nonneg (x.im - y.im),
             sq_nonneg (x.re - z.re), sq_nonneg (x.im - z.im),
             sq_nonneg (y.re - z.re), sq_nonneg (y.im - z.im)]

/-! ## IsUnitary2 closure properties -/

/-- Product of 2×2 unitaries is unitary -/
lemma isUnitary2_mul {u v : Mat2} (hu : IsUnitary2 u) (hv : IsUnitary2 v) :
    IsUnitary2 (u * v) := by
  unfold IsUnitary2 at *
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc u.conjTranspose, hu,
      Matrix.one_mul, hv]

/-- Conjugate transpose of a 2×2 unitary is unitary -/
lemma isUnitary2_conjTranspose {u : Mat2} (hu : IsUnitary2 u) :
    IsUnitary2 u.conjTranspose := by
  unfold IsUnitary2 at *
  rw [conjTranspose_conjTranspose]
  exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hu

/-! ## Product layer closure -/

/-- Product of single-qubit layers is a single-qubit layer -/
lemma singleQubitLayer_mul (uA uB uC dA dB dC : Mat2) :
    singleQubitLayer uA uB uC * singleQubitLayer dA dB dC =
      singleQubitLayer (uA * dA) (uB * dB) (uC * dC) := by
  unfold singleQubitLayer
  exact kron3_mul uA uB uC dA dB dC

/-- Conjugate transpose of a single-qubit layer -/
lemma singleQubitLayer_conjTranspose (uA uB uC : Mat2) :
    (singleQubitLayer uA uB uC).conjTranspose =
      singleQubitLayer uA.conjTranspose uB.conjTranspose uC.conjTranspose := by
  unfold singleQubitLayer
  exact kron3_conjTranspose uA uB uC

end
