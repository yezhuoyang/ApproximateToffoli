-- Compiled with lean_run_code against the built module ApproxToffoli.BlockCutU.
-- Diagnostics: {"success":true,"timed_out":false,"diagnostics":[]}  (zero errors, zero warnings)
import ApproxToffoli.BlockCutU

open Complex Real

namespace HS2Core

/-! ## Analytic backbone of the KEY LEMMA behind `BlockU.HS2`

KEY LEMMA.  For `W₂ ∈ U(4)` and `g ∈ U(2)`:
    ‖ (1/2) tr_C (W₂ (g ⊗ 1_C) CZ W₂ᴴ) ‖_nuclear ≤ √2 .
(Numerically: max = √2 to 2e-16, with BOTH singular values = 1/√2 at the maximum.)

Proof skeleton, whose scalar steps are compiled below:
 (1) nuclear duality  ‖M‖_nuc = max_{V ∈ U(2)} |tr (V M)|,  together with
     `tr (V · (1/2) tr_C K) = (1/2) tr ((V ⊗ 1_C) K)`;
 (2) `A := W₂ᴴ (V ⊗ 1_C) W₂` is unitary with DOUBLY DEGENERATE spectrum, hence
     `A = e^{iθ}(cos γ • 1 + i sin γ • J)`, `J` Hermitian, `J² = 1`, `tr J = 0`, so
        `|tr (A Y)| ≤ √(|tr Y|² + |tr (J Y)|²)`         ← `abs_cos_add_I_sin_le`
 (3) `Y := (g ⊗ 1_C) CZ` has eigenvalues `λ₁..λ₄`; Ky Fan / Schur–Horn give
     `tr (J Y) = Σ eᵢ λᵢ`, `eᵢ ∈ [-1,1]`, `Σ eᵢ = 0`; over the six vertices
        `|tr Y|² = 4t`,  `max |Σ eᵢ λᵢ|² = 4 · max t (2-t)`,  `t = |g₀₀|² ∈ [0,1]`,
     and the two ALWAYS add to `8`:                    ← `keyIdentity`, `keyBound`
        `|tr (A Y)| ≤ 2√2`,  i.e.  `‖M‖_nuc ≤ √2`. -/

/-- Step (2): `|cos γ · a + i sin γ · b| ≤ √(‖a‖² + ‖b‖²)`. -/
theorem abs_cos_add_I_sin_le (γ : ℝ) (a b : ℂ) :
    ‖(Real.cos γ : ℂ) * a + Complex.I * (Real.sin γ : ℂ) * b‖
      ≤ Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have hc : ‖((Real.cos γ : ℝ) : ℂ)‖ = |Real.cos γ| := Complex.norm_real _
  have hs : ‖Complex.I * ((Real.sin γ : ℝ) : ℂ)‖ = |Real.sin γ| := by
    rw [norm_mul, Complex.norm_I, one_mul]; exact Complex.norm_real _
  have h1 : ‖(Real.cos γ : ℂ) * a + Complex.I * (Real.sin γ : ℂ) * b‖
      ≤ |Real.cos γ| * ‖a‖ + |Real.sin γ| * ‖b‖ := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul, hc, hs]
  have h2 : (|Real.cos γ| * ‖a‖ + |Real.sin γ| * ‖b‖) ^ 2
      ≤ ((Real.cos γ) ^ 2 + (Real.sin γ) ^ 2) * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
    have e1 : |Real.cos γ| ^ 2 = (Real.cos γ) ^ 2 := sq_abs _
    have e2 : |Real.sin γ| ^ 2 = (Real.sin γ) ^ 2 := sq_abs _
    nlinarith [sq_nonneg (|Real.cos γ| * ‖b‖ - |Real.sin γ| * ‖a‖),
      abs_nonneg (Real.cos γ), abs_nonneg (Real.sin γ), norm_nonneg a, norm_nonneg b]
  have hpy : (Real.cos γ) ^ 2 + (Real.sin γ) ^ 2 = 1 := Real.cos_sq_add_sin_sq γ
  rw [hpy, one_mul] at h2
  have hnn : 0 ≤ |Real.cos γ| * ‖a‖ + |Real.sin γ| * ‖b‖ := by positivity
  refine le_trans h1 ?_
  calc |Real.cos γ| * ‖a‖ + |Real.sin γ| * ‖b‖
      = Real.sqrt ((|Real.cos γ| * ‖a‖ + |Real.sin γ| * ‖b‖) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2) := Real.sqrt_le_sqrt h2

/-- Step (3), the crux: the two vertex contributions ALWAYS add up to `8`. -/
theorem keyIdentity (t : ℝ) : 4 * t + 4 * (2 - t) = 8 := by ring

/-- Step (3) packaged: for `t ≤ 1`, `√(4t + 4 · max t (2-t)) = 2√2`. -/
theorem keyBound {t : ℝ} (h1 : t ≤ 1) :
    Real.sqrt (4 * t + 4 * max t (2 - t)) = 2 * Real.sqrt 2 := by
  have hm : max t (2 - t) = 2 - t := max_eq_right (by linarith)
  rw [hm, keyIdentity, show (8 : ℝ) = 2 ^ 2 * 2 by norm_num,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]

/-- The 2×2 nuclear-norm identity used in step (1):
    `(σ₁+σ₂)² = ‖M‖²_F + 2σ₁σ₂`, i.e. `‖M‖_nuc ≤ √2 ↔ ‖M‖²_F + 2|det M| ≤ 2`. -/
theorem nuc_sq (s t : ℝ) : (s + t) ^ 2 = (s ^ 2 + t ^ 2) + 2 * (s * t) := by ring

/-- The budget: `2 + √2 = 4 cos²(π/8)` — so `Σ_{k=1}^4 cos²θₖ ≤ 2+√2` says exactly
    that the AVERAGE of the four `cos²θₖ` is at most `cos²(π/8)`: a majorisation
    statement whose equality case is the flat one, all four angles `= π/8`. -/
theorem two_add_sqrt_two : 2 + Real.sqrt 2 = 4 * Real.cos (Real.pi / 8) ^ 2 := by
  nlinarith [sixtyfour_cos_sq]

/-- and `4 (2+√2) = 8 + 4√2` is exactly the `BlockU.HSSmall` budget in `BlockU.HS2`. -/
theorem four_mul_two_add_sqrt_two : 4 * (2 + Real.sqrt 2) = 8 + 4 * Real.sqrt 2 := by ring

/-- The reduction of `HS2` to the purification form:  `‖tr_C X‖²_HS = 4 Σ cos²θₖ`,
    so `HS2` ⟺ `Σ_{k=1}^4 cos²θₖ ≤ 2 + √2`. -/
theorem hs2_budget_iff (S : ℝ) : 4 * S ≤ 8 + 4 * Real.sqrt 2 ↔ S ≤ 2 + Real.sqrt 2 := by
  constructor <;> intro h <;> linarith

end HS2Core