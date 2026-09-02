/-
  ApproxToffoli.BaseCase
  Prove the trace bound for the base case: 0 CX gates (product unitaries).

  For U = kron3 uA uB uC (a product unitary):
    |Tr(U† CCX)|² ≤ 40 ≤ 64 cos²(π/8)

  Proof outline:
  1. Trace formula: |Tr|² = |p·tC + q·offC|² (TraceFormula.lean)
  2. Cauchy-Schwarz: ≤ (|p|² + |q|²)·(|tC|² + |offC|²)
  3. Unitarity of uC: |tC|² + |offC|² ≤ 4
  4. Three-term CS on p: |p|² ≤ 9·|uA₀₀|²·|uB₀₀|²
  5. |q|² = |uA₁₁|²·|uB₁₁|² = |uA₀₀|²·|uB₀₀|²
  6. Sum ≤ 10·|uA₀₀|²·|uB₀₀|² ≤ 10
  7. Total ≤ 10 · 4 = 40
-/

import ApproxToffoli.Gates
import ApproxToffoli.TensorProduct
import ApproxToffoli.Circuit
import ApproxToffoli.Helpers
import ApproxToffoli.TraceFormula
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.LinearAlgebra.Matrix.Trace

open Matrix Complex Real

noncomputable section

/-! ## Numeric bound: 40 ≤ 64 cos²(π/8) -/

lemma forty_le_64_cos_sq_pi_8 :
    (40 : ℝ) ≤ 64 * Real.cos (Real.pi / 8) ^ 2 := by
  have h1 : Real.cos (Real.pi / 8) ^ 2 ≥ 5 / 8 := by
    rw [Real.cos_sq]
    have hcos : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    have h2pi : 2 * (Real.pi / 8) = Real.pi / 4 := by ring
    rw [h2pi, hcos]
    have h2 : Real.sqrt 2 ≥ 1 := by
      rw [ge_iff_le, ← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  linarith

/-! ## Base case: product unitaries (0 CX gates) -/

/-- **Base Case Trace Bound**: |Tr((kron3 uA uB uC)† CCX)|² ≤ 40 -/
theorem product_unitary_trace_bound
    (uA uB uC : Mat2)
    (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC) :
    Complex.normSq (Matrix.trace ((singleQubitLayer uA uB uC).conjTranspose * CCX)) ≤ 40 := by
  -- Unfold singleQubitLayer = kron3
  unfold singleQubitLayer
  -- Step 1: Apply the trace formula
  rw [trace_normSq_formula]
  -- Goal: normSq(p * tC + q * offC) ≤ 40
  -- where p = uA₀₀*(uB₀₀+uB₁₁) + uA₁₁*uB₀₀, q = uA₁₁*uB₁₁,
  --       tC = uC₀₀+uC₁₁, offC = uC₀₁+uC₁₀
  set p := uA 0 0 * (uB 0 0 + uB 1 1) + uA 1 1 * uB 0 0
  set q := uA 1 1 * uB 1 1
  set tC := uC 0 0 + uC 1 1
  set offC := uC 0 1 + uC 1 0
  -- Step 2: Cauchy-Schwarz for 2 terms
  have hCS := cauchy_schwarz_two p q tC offC
  -- Step 3: Bound |tC|² + |offC|² ≤ 4
  have hC_bound := unitary2_trace_off_bound uC hC
  -- Step 4: Bound |p|² using 3-term CS
  -- p = uA₀₀*uB₀₀ + uA₀₀*uB₁₁ + uA₁₁*uB₀₀
  have hp_eq : p = uA 0 0 * uB 0 0 + uA 0 0 * uB 1 1 + uA 1 1 * uB 0 0 := by
    subst p; ring
  have hp_bound : Complex.normSq p ≤
      3 * (Complex.normSq (uA 0 0 * uB 0 0) + Complex.normSq (uA 0 0 * uB 1 1) +
           Complex.normSq (uA 1 1 * uB 0 0)) := by
    rw [hp_eq]
    exact normSq_add3_le _ _ _
  -- Simplify normSq of products
  simp only [map_mul] at hp_bound
  -- Use |uA₀₀|² = |uA₁₁|² and |uB₀₀|² = |uB₁₁|²
  have hA_eq := unitary2_diag_normSq_eq uA hA
  have hB_eq := unitary2_diag_normSq_eq uB hB
  -- So all three terms equal |uA₀₀|²·|uB₀₀|²
  have hp_bound' : Complex.normSq p ≤ 9 * (Complex.normSq (uA 0 0) * Complex.normSq (uB 0 0)) := by
    calc Complex.normSq p
        ≤ 3 * (Complex.normSq (uA 0 0) * Complex.normSq (uB 0 0) +
               Complex.normSq (uA 0 0) * Complex.normSq (uB 1 1) +
               Complex.normSq (uA 1 1) * Complex.normSq (uB 0 0)) := hp_bound
      _ = 3 * (Complex.normSq (uA 0 0) * Complex.normSq (uB 0 0) +
               Complex.normSq (uA 0 0) * Complex.normSq (uB 0 0) +
               Complex.normSq (uA 0 0) * Complex.normSq (uB 0 0)) := by
          rw [hA_eq, hB_eq]
      _ = 9 * (Complex.normSq (uA 0 0) * Complex.normSq (uB 0 0)) := by ring
  -- Step 5: |q|² = |uA₀₀|²·|uB₀₀|²
  have hq_eq : Complex.normSq q = Complex.normSq (uA 0 0) * Complex.normSq (uB 0 0) := by
    subst q
    simp only [map_mul]
    rw [hA_eq, hB_eq]
  -- Step 6: |p|² + |q|² ≤ 10 · |uA₀₀|²·|uB₀₀|²
  have hpq : Complex.normSq p + Complex.normSq q ≤
      10 * (Complex.normSq (uA 0 0) * Complex.normSq (uB 0 0)) := by
    linarith [hp_bound', hq_eq]
  -- Step 6b: |uA₀₀|² ≤ 1 and |uB₀₀|² ≤ 1
  have hA0 := unitary2_col0_norm uA hA   -- |uA₀₀|² + |uA₁₀|² = 1
  have hB0 := unitary2_col0_norm uB hB   -- |uB₀₀|² + |uB₁₀|² = 1
  have hA_le : Complex.normSq (uA 0 0) ≤ 1 := by
    linarith [Complex.normSq_nonneg (uA 1 0)]
  have hB_le : Complex.normSq (uB 0 0) ≤ 1 := by
    linarith [Complex.normSq_nonneg (uB 1 0)]
  -- So |p|² + |q|² ≤ 10
  have hpq_10 : Complex.normSq p + Complex.normSq q ≤ 10 := by
    calc Complex.normSq p + Complex.normSq q
        ≤ 10 * (Complex.normSq (uA 0 0) * Complex.normSq (uB 0 0)) := hpq
      _ ≤ 10 * (1 * 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul hA_le hB_le (Complex.normSq_nonneg _) (by linarith)
      _ = 10 := by ring
  -- Step 7: Combine everything
  -- normSq(p*tC + q*offC) ≤ (|p|²+|q|²)·(|tC|²+|offC|²) ≤ 10 · 4 = 40
  calc Complex.normSq (p * tC + q * offC)
      ≤ (Complex.normSq p + Complex.normSq q) * (Complex.normSq tC + Complex.normSq offC) := hCS
    _ ≤ 10 * 4 := by
        apply mul_le_mul hpq_10 hC_bound
        · exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
        · linarith
    _ = 40 := by norm_num

/-- Base case for achievable_trace_bound: 0 CX gates -/
theorem achievable_trace_bound_base
    (uA uB uC : Mat2)
    (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC) :
    Complex.normSq (Matrix.trace ((singleQubitLayer uA uB uC).conjTranspose * CCX)) ≤
      64 * Real.cos (Real.pi / 8) ^ 2 := by
  calc Complex.normSq (Matrix.trace ((singleQubitLayer uA uB uC).conjTranspose * CCX))
      ≤ 40 := product_unitary_trace_bound uA uB uC hA hB hC
    _ ≤ 64 * Real.cos (Real.pi / 8) ^ 2 := forty_le_64_cos_sq_pi_8

end
