/-
  ApproxToffoli.CNOTTrace
  Key lemma: |Tr(V)|² + |Tr(CNOT·V)|² ≤ 20 for 4×4 unitary V.

  Proof:
  - Parallelogram law: |Tr(V)|²+|Tr(CNOT·V)|² = 2(|x|²+|y|²)
    where x = (Tr(V)+Tr(CNOT·V))/2, y = (Tr(V)-Tr(CNOT·V))/2
  - x = V₀₀ + V₁₁ + (V₂₂+V₂₃+V₃₂+V₃₃)/2
  - y = (V₂₂+V₃₃-V₂₃-V₃₂)/2
  - |V₀₀|,|V₁₁| ≤ 1 (entries of unitary)
  - |V₂₂+V₂₃+V₃₂+V₃₃| ≤ 2 (from column norm/orthogonality)
  - |V₂₂+V₃₃-V₂₃-V₃₂| ≤ 2 (same argument)
  - |x| ≤ 3, |y| ≤ 1, so 2(9+1) = 20
-/

import ApproxToffoli.Defs
import ApproxToffoli.BlockDecomp
import ApproxToffoli.Helpers
import Mathlib.Data.Complex.Basic

open Matrix Complex

noncomputable section

/-! ## 4×4 unitary predicate -/

/-- A 4×4 matrix is unitary: V† V = I -/
def IsUnitary4 (V : Mat4) : Prop := V.conjTranspose * V = 1

/-! ## Helper: star ↔ normSq conversion -/

private lemma star_mul_self_4 (z : ℂ) :
    star z * z = ↑(Complex.normSq z) := by
  change starRingEnd ℂ z * z = ↑(normSq z)
  rw [mul_comm, Complex.mul_conj]

/-! ## CNOT_BC_4 basic properties -/

/-- CNOT_BC_4 is self-inverse: CNOT² = I -/
lemma cnot_bc_4_sq : CNOT_BC_4 * CNOT_BC_4 = (1 : Mat4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CNOT_BC_4, Matrix.mul_apply, Matrix.of_apply, pauliX, Fin.sum_univ_four]

/-- Trace of CNOT_BC_4 = 2 -/
lemma cnot_bc_4_trace : Matrix.trace CNOT_BC_4 = 2 := by
  simp [Matrix.trace, Matrix.diag, CNOT_BC_4, Matrix.of_apply, pauliX, Fin.sum_univ_four]
  norm_num

/-! ## Parallelogram law for complex numbers -/

/-- Parallelogram law: |x+y|² + |x-y|² = 2(|x|² + |y|²) -/
lemma parallelogram_normSq (x y : ℂ) :
    Complex.normSq (x + y) + Complex.normSq (x - y) =
    2 * Complex.normSq x + 2 * Complex.normSq y := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
             Complex.sub_re, Complex.sub_im]
  ring

/-! ## Column properties of 4×4 unitaries -/

/-- Column j of a 4×4 unitary has unit norm: Σ_k |V_{kj}|² = 1 -/
lemma unitary4_col_norm (V : Mat4) (hV : IsUnitary4 V) (j : Fin 4) :
    Complex.normSq (V 0 j) + Complex.normSq (V 1 j) +
    Complex.normSq (V 2 j) + Complex.normSq (V 3 j) = 1 := by
  unfold IsUnitary4 at hV
  have hjj : (V.conjTranspose * V) j j = 1 := by simp [hV]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four] at hjj
  rw [star_mul_self_4, star_mul_self_4, star_mul_self_4, star_mul_self_4] at hjj
  exact_mod_cast hjj

/-- Entry normSq bound: |V_{ij}|² ≤ 1 for a 4×4 unitary -/
lemma unitary4_entry_normSq_le (V : Mat4) (hV : IsUnitary4 V) (i j : Fin 4) :
    Complex.normSq (V i j) ≤ 1 := by
  have hcol := unitary4_col_norm V hV j
  have h0 := Complex.normSq_nonneg (V 0 j)
  have h1 := Complex.normSq_nonneg (V 1 j)
  have h2 := Complex.normSq_nonneg (V 2 j)
  have h3 := Complex.normSq_nonneg (V 3 j)
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by rcases i with ⟨v, hv⟩; omega
  rcases hi with rfl | rfl | rfl | rfl
  · linarith [h1, h2, h3]
  · linarith [h0, h2, h3]
  · linarith [h0, h1, h3]
  · linarith [h0, h1, h2]

/-- Column orthogonality for a 4×4 unitary -/
lemma unitary4_col_ortho (V : Mat4) (hV : IsUnitary4 V) (j₁ j₂ : Fin 4) (h : j₁ ≠ j₂) :
    star (V 0 j₁) * V 0 j₂ + star (V 1 j₁) * V 1 j₂ +
    star (V 2 j₁) * V 2 j₂ + star (V 3 j₁) * V 3 j₂ = 0 := by
  unfold IsUnitary4 at hV
  have hj : (V.conjTranspose * V) j₁ j₂ = 0 := by
    rw [hV]; simp [h]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four] at hj
  exact hj

/-! ## Lower block bounds for 4×4 unitaries

The key sub-lemma: for the 2×2 submatrix at rows/cols {2,3} of a 4×4 unitary V,
|V₂₂+V₂₃+V₃₂+V₃₃|² ≤ 4 and |V₂₂+V₃₃-V₂₃-V₃₂|² ≤ 4.

Proof: v = (V₂₂,V₃₂), w = (V₂₃,V₃₃). ||v||²≤1, ||w||²≤1.
Sum = ⟨(1,1),v+w⟩. |sum|² ≤ 2·||v+w||² ≤ 2(||v||²+||w||²+2√((1-||v||²)(1-||w||²))) ≤ 4.
-/

/-- **Key bound**: |V₂₂+V₂₃+V₃₂+V₃₃|² ≤ 4 for a 4×4 unitary V.
    Proof by SOS decomposition using column norms and orthogonality. -/
lemma unitary4_lower_block_sum_bound (V : Mat4) (hV : IsUnitary4 V) :
    Complex.normSq (V 2 2 + V 2 3 + V 3 2 + V 3 3) ≤ 4 := by
  have hcol2 := unitary4_col_norm V hV 2
  have hcol3 := unitary4_col_norm V hV 3
  have hortho := unitary4_col_ortho V hV 2 3 (by decide)
  -- Extract real part of orthogonality
  have hortho_re : (star (V 0 2) * V 0 3 + star (V 1 2) * V 1 3 +
                    star (V 2 2) * V 2 3 + star (V 3 2) * V 3 3).re = 0 := by
    have : (star (V 0 2) * V 0 3 + star (V 1 2) * V 1 3 +
            star (V 2 2) * V 2 3 + star (V 3 2) * V 3 3) = 0 := hortho
    rw [this]; rfl
  -- Expand normSq into re/im components
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
             Complex.mul_re, Complex.star_def,
             Complex.conj_re, Complex.conj_im, neg_mul] at hcol2 hcol3 hortho_re ⊢
  -- SOS decomposition:
  -- 4 - |sum|² = 2(re(V02)+re(V03))² + 2(im(V02)+im(V03))²
  --            + 2(re(V12)+re(V13))² + 2(im(V12)+im(V13))²
  --            + (re(V22)+re(V23)-re(V32)-re(V33))²
  --            + (im(V22)+im(V23)-im(V32)-im(V33))²
  nlinarith [sq_nonneg ((V 0 2).re + (V 0 3).re),
             sq_nonneg ((V 0 2).im + (V 0 3).im),
             sq_nonneg ((V 1 2).re + (V 1 3).re),
             sq_nonneg ((V 1 2).im + (V 1 3).im),
             sq_nonneg ((V 2 2).re + (V 2 3).re - (V 3 2).re - (V 3 3).re),
             sq_nonneg ((V 2 2).im + (V 2 3).im - (V 3 2).im - (V 3 3).im)]

/-- **Key bound**: |V₂₂+V₃₃-V₂₃-V₃₂|² ≤ 4 for a 4×4 unitary V.
    Same SOS technique as sum bound, with different sign on orthogonality. -/
lemma unitary4_lower_block_diff_bound (V : Mat4) (hV : IsUnitary4 V) :
    Complex.normSq (V 2 2 + V 3 3 - V 2 3 - V 3 2) ≤ 4 := by
  have hcol2 := unitary4_col_norm V hV 2
  have hcol3 := unitary4_col_norm V hV 3
  have hortho := unitary4_col_ortho V hV 2 3 (by decide)
  have hortho_re : (star (V 0 2) * V 0 3 + star (V 1 2) * V 1 3 +
                    star (V 2 2) * V 2 3 + star (V 3 2) * V 3 3).re = 0 := by
    rw [hortho]; rfl
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
             Complex.sub_re, Complex.sub_im,
             Complex.mul_re, Complex.star_def,
             Complex.conj_re, Complex.conj_im, neg_mul] at hcol2 hcol3 hortho_re ⊢
  nlinarith [sq_nonneg ((V 0 2).re - (V 0 3).re),
             sq_nonneg ((V 0 2).im - (V 0 3).im),
             sq_nonneg ((V 1 2).re - (V 1 3).re),
             sq_nonneg ((V 1 2).im - (V 1 3).im),
             sq_nonneg ((V 2 2).re - (V 2 3).re + (V 3 2).re - (V 3 3).re),
             sq_nonneg ((V 2 2).im - (V 2 3).im + (V 3 2).im - (V 3 3).im)]

/-! ## CNOT trace formulas -/

/-- Explicit trace of CNOT_BC_4 * V in terms of entries -/
lemma trace_cnot_mul (V : Mat4) :
    Matrix.trace (CNOT_BC_4 * V) = V 0 0 + V 1 1 + V 3 2 + V 2 3 := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, CNOT_BC_4, Matrix.of_apply,
        pauliX, Fin.sum_univ_four]

/-- Explicit trace of V in terms of entries -/
lemma trace_mat4 (V : Mat4) :
    Matrix.trace V = V 0 0 + V 1 1 + V 2 2 + V 3 3 := by
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_four]

/-! ## The main CNOT trace lemma -/

/-- **CNOT trace lemma**: For a 4×4 unitary V,
    |Tr(V)|² + |Tr(CNOT·V)|² ≤ 20.

    Proof by parallelogram law + eigenspace rank bounds. -/
theorem cnot_trace_bound (V : Mat4) (hV : IsUnitary4 V) :
    Complex.normSq (Matrix.trace V) +
    Complex.normSq (Matrix.trace (CNOT_BC_4 * V)) ≤ 20 := by
  rw [trace_mat4, trace_cnot_mul]
  -- Goal: |V₀₀+V₁₁+V₂₂+V₃₃|² + |V₀₀+V₁₁+V₃₂+V₂₃|² ≤ 20
  -- Strategy: parallelogram law gives 2·LHS = |sum+sum'|² + |sum-sum'|²
  -- where sum-sum' = V₂₂+V₃₃-V₂₃-V₃₂ (≤4) and sum+sum' = 2V₀₀+2V₁₁+S (≤36)
  -- Step 1: Parallelogram law
  have hpara := parallelogram_normSq
    (V 0 0 + V 1 1 + V 2 2 + V 3 3) (V 0 0 + V 1 1 + V 3 2 + V 2 3)
  -- Step 2: Simplify difference
  have hdiff : V 0 0 + V 1 1 + V 2 2 + V 3 3 - (V 0 0 + V 1 1 + V 3 2 + V 2 3) =
    V 2 2 + V 3 3 - V 2 3 - V 3 2 := by ring
  -- Step 3: Simplify sum
  have hsum_eq : V 0 0 + V 1 1 + V 2 2 + V 3 3 + (V 0 0 + V 1 1 + V 3 2 + V 2 3) =
    2 * V 0 0 + 2 * V 1 1 + (V 2 2 + V 2 3 + V 3 2 + V 3 3) := by ring
  rw [hdiff, hsum_eq] at hpara
  -- Step 4: Bound on difference from unitarity
  have hdb := unitary4_lower_block_diff_bound V hV
  -- Step 5: Bound on sum using Cauchy-Schwarz for 3 terms
  have h3 := normSq_add3_le (2 * V 0 0) (2 * V 1 1) (V 2 2 + V 2 3 + V 3 2 + V 3 3)
  -- Step 6: normSq(2z) = 4·normSq(z)
  have hn00 : Complex.normSq (2 * V 0 0) = 4 * Complex.normSq (V 0 0) := by
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]; ring
  have hn11 : Complex.normSq (2 * V 1 1) = 4 * Complex.normSq (V 1 1) := by
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]; ring
  rw [hn00, hn11] at h3
  -- Step 7: Entry and block bounds
  have he00 := unitary4_entry_normSq_le V hV 0 0
  have he11 := unitary4_entry_normSq_le V hV 1 1
  have hsb := unitary4_lower_block_sum_bound V hV
  -- Step 8: Combine: 2·LHS = normSq(sum+sum') + normSq(diff) ≤ 36 + 4 = 40
  linarith

end
