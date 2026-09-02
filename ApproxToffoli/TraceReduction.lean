/-
  ApproxToffoli.TraceReduction
  Reduce the HS distance bound to a trace inequality.

  REFACTORED: the constant `64 cos²(π/8)` and the target `CCX` are no longer baked
  into the reduction.  The general statement is

      normSq (Tr (Uᴴ V)) ≤ K  →  hsDistance U V ≥ √(1 − K/64)

  with matching `≤` and `=` versions; `trace_bound_implies_distance` (unchanged
  statement) is now a two-line corollary.  Nothing downstream breaks.
-/

import ApproxToffoli.HSDistance
import ApproxToffoli.Gates
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds

open Matrix Complex Real

noncomputable section

/-! ## Helper: trig facts about π/8 -/

lemma cos_pi_div_8_pos : Real.cos (Real.pi / 8) > 0 := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_pos, Real.pi_lt_four]

lemma sin_pi_div_8_pos : Real.sin (Real.pi / 8) > 0 := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith [Real.pi_pos]
  · linarith [Real.pi_pos]

lemma sin_pi_div_8_nonneg : Real.sin (Real.pi / 8) ≥ 0 :=
  le_of_lt sin_pi_div_8_pos

lemma cos_sq_eq_one_sub_sin_sq_pi_8 :
    Real.cos (Real.pi / 8) ^ 2 = 1 - Real.sin (Real.pi / 8) ^ 2 := by
  linarith [Real.sin_sq_add_cos_sq (Real.pi / 8)]

/-! ## The general reduction

`hsDistance U V = √(1 − normSq (Tr (Uᴴ V))/64)` is *monotone decreasing* in the
overlap, and `Real.sqrt` is monotone, so all three directions are one-liners.  No
positivity hypothesis on `K` is needed: `Real.sqrt` is `0` on negative input, which
makes the `≥` statement vacuously true exactly when it should be. -/

/-- **Lower bound.**  A trace bound gives a distance bound, for any target `V`. -/
theorem hsDistance_ge_of_normSq_le (U V : Mat8) {K : ℝ}
    (h : Complex.normSq (Matrix.trace (Uᴴ * V)) ≤ K) :
    hsDistance U V ≥ Real.sqrt (1 - K / 64) := by
  unfold hsDistance hsFidelity
  exact Real.sqrt_le_sqrt (by linarith)

/-- **Upper bound.**  A trace *lower* bound gives a distance *upper* bound. -/
theorem hsDistance_le_of_normSq_ge (U V : Mat8) {K : ℝ}
    (h : K ≤ Complex.normSq (Matrix.trace (Uᴴ * V))) :
    hsDistance U V ≤ Real.sqrt (1 - K / 64) := by
  unfold hsDistance hsFidelity
  exact Real.sqrt_le_sqrt (by linarith)

/-- **Equality.**  The version witnesses use: an exact overlap gives an exact
    distance.  This is what turns each computed `Tr(Uᴴ CCX)` into a point of the
    curve `d(n)`. -/
theorem hsDistance_eq_of_normSq_eq (U V : Mat8) {K : ℝ}
    (h : Complex.normSq (Matrix.trace (Uᴴ * V)) = K) :
    hsDistance U V = Real.sqrt (1 - K / 64) := by
  unfold hsDistance hsFidelity; rw [h]

set_option linter.unusedVariables false in
/-- The `CCX`-specialised lower bound.  `hK` is not needed for the proof (see
    `hsDistance_ge_of_normSq_le`); it is kept in the signature because every
    intended call site has it and it documents the intent. -/
theorem trace_bound_implies_distance_gen (U : Mat8) {K : ℝ} (hK : 0 ≤ K)
    (h : Complex.normSq (Matrix.trace (Uᴴ * CCX)) ≤ K) :
    hsDistance U CCX ≥ Real.sqrt (1 - K / 64) :=
  hsDistance_ge_of_normSq_le U CCX h

/-- The `CCX`-specialised equality version. -/
theorem trace_eq_implies_distance_gen (U : Mat8) {K : ℝ}
    (h : Complex.normSq (Matrix.trace (Uᴴ * CCX)) = K) :
    hsDistance U CCX = Real.sqrt (1 - K / 64) :=
  hsDistance_eq_of_normSq_eq U CCX h

/-! ## The original statement, now a corollary

`√(1 − 64cos²(π/8)/64) = √(sin²(π/8)) = sin(π/8)`. -/

/-- If the squared trace norm is at most 64·cos²(π/8),
    then hsDistance ≥ sin(π/8). -/
theorem trace_bound_implies_distance
    (U : Mat8)
    (h : Complex.normSq (Matrix.trace (U.conjTranspose * CCX)) ≤
         64 * Real.cos (Real.pi / 8) ^ 2) :
    hsDistance U CCX ≥ Real.sin (Real.pi / 8) := by
  have hs : Real.sqrt (1 - 64 * Real.cos (Real.pi / 8) ^ 2 / 64)
      = Real.sin (Real.pi / 8) := by
    rw [show (1 : ℝ) - 64 * Real.cos (Real.pi / 8) ^ 2 / 64 = Real.sin (Real.pi / 8) ^ 2 by
      rw [cos_sq_eq_one_sub_sin_sq_pi_8]; ring]
    exact Real.sqrt_sq sin_pi_div_8_nonneg
  rw [← hs]
  exact trace_bound_implies_distance_gen U (by positivity) h

end
