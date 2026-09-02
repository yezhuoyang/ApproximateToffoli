import ApproxToffoli.SharpBounds
import ApproxToffoli.CutMain
import ApproxToffoli.CurveWitnesses
import ApproxToffoli.TraceReduction

open Matrix Complex

noncomputable section

namespace SharpBounds

/-- The one open analytic input of `cut_trace_bound_one_sharp`, packaged. -/
abbrev Key2 : Prop :=
  ∀ Q N : Mat4, IsRefl4 Q → IsUnitary4 N →
    ‖Matrix.trace (Q * N)‖ ^ 2 + ‖Matrix.trace (Zp4 * N)‖ ^ 2 ≤ 20

/-- **`F(0)² ≤ 40`, sharp.** -/
theorem cut_trace_bound_zero_sharp {U : Mat8} (h : BCCut 0 U) :
    Complex.normSq (Matrix.trace (CCZ8 * U)) ≤ 40 := by
  cases h with
  | base M c hM hc =>
    rw [trace_ccz_cut0]
    have hcs := cauchy_schwarz_two (c 0 0) (c 1 1) (Matrix.trace M)
      (Matrix.trace (Zp4 * M))
    have hc0 : Complex.normSq (c 0 0) ≤ 1 := by
      have := unitary2_col0_norm c hc
      nlinarith [Complex.normSq_nonneg (c 1 0)]
    have hc1 : Complex.normSq (c 1 1) ≤ 1 := by
      have := unitary2_col1_norm c hc
      nlinarith [Complex.normSq_nonneg (c 0 1)]
    have hM20 := zp4_trace_bound M hM
    have hnn0 := Complex.normSq_nonneg (Matrix.trace M)
    have hnn1 := Complex.normSq_nonneg (Matrix.trace (Zp4 * M))
    nlinarith [hcs, hc0, hc1, hM20, hnn0, hnn1]

/-- **The sharp cut trace bound, `m ≤ 1`.** -/
theorem cut_trace_bound_cz_one {m : ℕ} {U : Mat8} (h : CZCut m U) (hm : m ≤ 1)
    (key2 : Key2) :
    Complex.normSq (Matrix.trace (CCZ8 * U)) ≤ 40 := by
  cases h with
  | base M c hM hc => exact cut_trace_bound_zero_sharp (BCCut.base M c hM hc)
  | step h1 M1 c1 hM1 hc1 =>
      cases h1 with
      | base M0 c0 hM0 hc0 =>
          have e : CCZ8 * (kronABC M0 c0 * CZBC8 * kronABC M1 c1)
              = CCZ8 * kronABC M0 c0 * CZBC8 * kronABC M1 c1 := by noncomm_ring
          rw [e]
          exact cut_trace_bound_one_sharp hM0 hM1 hc0 hc1 key2
      | step h2 _ _ _ _ => omega

/-- Transported to `BCCut` by R4. -/
theorem cut_trace_bound_bc_one {m : ℕ} {U : Mat8} (h : BCCut m U) (hm : m ≤ 1)
    (key2 : Key2) :
    Complex.normSq (Matrix.trace (CCZ8 * U)) ≤ 40 :=
  cut_trace_bound_cz_one (BCCut_to_CZCut h) hm key2

end SharpBounds

/-- **`min(mBC, mAB) ≤ 1` for `n ≤ 3`.** -/
theorem achievable_min_cut_le_one {n : ℕ} {U : Mat8} (hn : n ≤ 3)
    (h : AchievableCircuit n U) :
    (∃ m ≤ 1, BCCut m U) ∨ (∃ m ≤ 1, ABCut m U) := by
  obtain ⟨mB, mA, hle, h1, h2⟩ := achievable_to_both_cuts h
  by_cases hb : mB ≤ 1
  · exact Or.inl ⟨mB, hb, h1⟩
  · exact Or.inr ⟨mA, by omega, h2⟩

/-- **The `n ≤ 3` trace bound.** -/
theorem achievable_trace_bound_three {n : ℕ} (hn : n ≤ 3) {U : Mat8}
    (h : AchievableCircuit n U) (key2 : SharpBounds.Key2) :
    Complex.normSq (Matrix.trace (Uᴴ * CCX)) ≤ 40 := by
  rw [normSq_trace_ccx_eq]
  obtain ⟨mB, mA, hle, h1, h2⟩ := achievable_to_both_cuts h
  by_cases hb : mB ≤ 1
  · have hW : BCCut mB (kron3 1 1 Hgate * U * kron3 1 1 Hgate) := by
      rw [hC_eq_kronABC, Matrix.mul_assoc]
      exact BCCut_mul_left
        (BCCut_mul_right h1 1 Hgate isUnitary4_one hgate_unitary) 1 Hgate
        isUnitary4_one hgate_unitary
    exact SharpBounds.cut_trace_bound_bc_one hW hb key2
  · have hmA : mA ≤ 1 := by omega
    have hW : ABCut mA (kron3 1 1 Hgate * U * kron3 1 1 Hgate) := by
      rw [hC_eq_kronA_BC, Matrix.mul_assoc]
      exact ABCut_mul_left
        (ABCut_mul_right h2 1 (kron2 1 Hgate) isUnitary2_one isUnitary4_kron2_1_H)
        1 (kron2 1 Hgate) isUnitary2_one isUnitary4_kron2_1_H
    have hbd := SharpBounds.cut_trace_bound_bc_one (ABCut_to_BCCut hW) hmA key2
    rwa [trace_ccz_swapMatAC] at hbd

/-- `√(1 − 40/64) = √6/4`. -/
lemma sqrt_one_sub_forty : Real.sqrt (1 - 40 / 64) = Real.sqrt 6 / 4 := by
  rw [show (1 : ℝ) - 40 / 64 = (Real.sqrt 6 / 4) ^ 2 by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6)]; norm_num]
  exact Real.sqrt_sq (by positivity)

/-- **The `n = 3` lower bound.** -/
theorem approxToffoli_lower_bound_three (U : Mat8) (hU : AchievableCircuit 3 U)
    (key2 : SharpBounds.Key2) :
    hsDistance U CCX ≥ Real.sqrt 6 / 4 := by
  rw [← sqrt_one_sub_forty]
  exact hsDistance_ge_of_normSq_le U CCX
    (achievable_trace_bound_three (le_refl 3) hU key2)

/-- **The minimum at `n = 3` is `√6/4`.** -/
theorem approxToffoli_isLeast_three (key2 : SharpBounds.Key2) :
    IsLeast {r : ℝ | ∃ U, AchievableCircuit 3 U ∧ hsDistance U CCX = r}
      (Real.sqrt 6 / 4) :=
  ⟨⟨Curve.witness2, AchievableCircuit.weaken Curve.witness2_achievable,
    Curve.witness2_distance⟩,
   by rintro r ⟨U, hU, rfl⟩; exact approxToffoli_lower_bound_three U hU key2⟩

/-- The `n = 2` entry, same constant. -/
theorem approxToffoli_isLeast_two (key2 : SharpBounds.Key2) :
    IsLeast {r : ℝ | ∃ U, AchievableCircuit 2 U ∧ hsDistance U CCX = r}
      (Real.sqrt 6 / 4) :=
  ⟨⟨Curve.witness2, Curve.witness2_achievable, Curve.witness2_distance⟩,
   by
     rintro r ⟨U, hU, rfl⟩
     rw [← sqrt_one_sub_forty]
     exact hsDistance_ge_of_normSq_le U CCX
       (achievable_trace_bound_three (by omega) hU key2)⟩

end
