import ApproxToffoli.BlockCutU

open Matrix

/-!
  The one provable step of the conjectured "two-term" route to `BlockU.HS2`:
  a certificate of the shape `‖Tr_C X‖²_HS ≤ 8 + 4(a+b)` with `a² + b² ≤ 1`
  upgrades to `HSSmall` (i.e. `≤ 8 + 4√2`).  Intended instantiation
  `a = cos 2φ`, `b = sin 2φ`, where `φ = φ(V)` is the misalignment angle.

  Compiled with `lean_run_code` against the built `ApproxToffoli.BlockCutU`:
  0 errors / 0 warnings.  NOT installed in the tree.
-/

namespace BlockU

/-- `a + b ≤ √2` whenever `a² + b² ≤ 1`.  (Cauchy–Schwarz in `ℝ²`.) -/
lemma add_le_sqrt_two_of_sq_add_sq_le_one {a b : ℝ} (h : a ^ 2 + b ^ 2 ≤ 1) :
    a + b ≤ Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2,
    sq_nonneg (a - b), sq_nonneg (a + b - Real.sqrt 2)]

/-- **The two-term certificate.**  If the Hilbert–Schmidt weight of `X` is bounded by
    `8 + 4(a+b)` for two reals with `a² + b² ≤ 1`, then `HSSmall X`. -/
theorem HSSmall_of_two_term {X : Mat4} {a b : ℝ} (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hX : RCLike.re (Matrix.trace (Xᴴ * X)) ≤ 8 + 4 * (a + b)) : HSSmall X := by
  have := add_le_sqrt_two_of_sq_add_sq_le_one hab
  unfold HSSmall
  linarith

/-- The intended instantiation: `a = cos 2φ`, `b = sin 2φ`. -/
theorem HSSmall_of_curve {X : Mat4} {φ : ℝ}
    (hX : RCLike.re (Matrix.trace (Xᴴ * X))
        ≤ 8 + 4 * (Real.cos (2 * φ) + Real.sin (2 * φ))) : HSSmall X :=
  HSSmall_of_two_term (by
    have := Real.sin_sq_add_cos_sq (2 * φ); nlinarith) hX

/-- Sanity: the certificate is TIGHT — the budget is attained at `φ = π/8`. -/
example : Real.cos (2 * (Real.pi / 8)) + Real.sin (2 * (Real.pi / 8)) = Real.sqrt 2 := by
  have h : 2 * (Real.pi / 8) = Real.pi / 4 := by ring
  rw [h, Real.cos_pi_div_four, Real.sin_pi_div_four]
  ring

end BlockU