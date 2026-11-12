/-
Clifford+T decompositions of the one-qubit gates used by the line circuits.

Every one-qubit gate of the constructions other than the phase gates of the phase
operator is, up to a global phase, a product of H, S and T gates:
`X` (no T gate), `P(±π/4)` (one T gate), the rotation `rGate = R_y(π/4)` and its
transpose (one T gate each).  `TCost` is closed under conjugate transpose.
-/
import Mathlib
import ApproxToffoli.Line.TModel
import ApproxToffoli.Line.Cells2

namespace Line

open Matrix ExactLine

/-! ### Phase gates -/

theorem pGate_mul_pGate (a b : ℝ) : pGate a * pGate b = pGate (a + b) := by
  rw [pGate_eq_m2, pGate_eq_m2, pGate_eq_m2, m2_mul, e_add]
  congr 1 <;> ring

theorem e_two_pi : e (2 * Real.pi) = 1 := by
  rw [two_mul, e_add, e_pi]
  norm_num

theorem pGate_add_two_pi (a : ℝ) : pGate (a + 2 * Real.pi) = pGate a := by
  rw [pGate_eq_m2, pGate_eq_m2, e_add, e_two_pi, mul_one]

theorem conjTranspose_pGate (a : ℝ) : (pGate a)ᴴ = pGate (-a) := by
  rw [← Matrix.star_eq_conjTranspose, pGate_eq_m2, pGate_eq_m2, star_m2, star_e]
  simp

theorem conjTranspose_hGate : hGateᴴ = hGate := by
  rw [← Matrix.star_eq_conjTranspose, hGate_eq_m2, star_m2]
  simp

/-- `S³ = P(-π/2)`. -/
theorem sGate_cube : sGate * sGate * sGate = pGate (-(Real.pi / 2)) := by
  unfold sGate
  rw [pGate_mul_pGate, pGate_mul_pGate, ← pGate_add_two_pi (-(Real.pi / 2))]
  congr 1
  ring

/-- `T S³ = P(-π/4)`. -/
theorem tGate_mul_sGate_cube :
    tGate * sGate * sGate * sGate = pGate (-(Real.pi / 4)) := by
  unfold sGate tGate
  rw [pGate_mul_pGate, pGate_mul_pGate, pGate_mul_pGate, ← pGate_add_two_pi (-(Real.pi / 4))]
  congr 1
  ring

theorem tcost_sGate_cube : TCost (pGate (-(Real.pi / 2))) 0 := by
  rw [← sGate_cube]
  exact TCost.mul (TCost.mul TCost.s TCost.s) TCost.s

theorem tcost_pGate_neg_quarter : TCost (pGate (-(Real.pi / 4))) 1 := by
  rw [← tGate_mul_sGate_cube]
  exact TCost.mul (TCost.mul (TCost.mul TCost.t TCost.s) TCost.s) TCost.s

theorem tcost_pGate_neg_quarter' : TCost (pGate (-Real.pi / 4)) 1 := by
  rw [show -Real.pi / 4 = -(Real.pi / 4) by ring]
  exact tcost_pGate_neg_quarter

theorem tcost_pGate_quarter : TCost (pGate (Real.pi / 4)) 1 := TCost.t

/-! ### The NOT gate -/

/-- `X = H S S H`. -/
theorem xGate_eq_hssh : xGate = hGate * (sGate * sGate) * hGate := by
  unfold sGate
  rw [pGate_mul_pGate, show Real.pi / 2 + Real.pi / 2 = Real.pi by ring, pGate_eq_m2, e_pi,
    hGate_mul_mul, xGate_eq_m2]
  congr 1 <;> norm_num

theorem tcost_xGate : TCost xGate 0 := by
  rw [xGate_eq_hssh]
  exact TCost.mul (TCost.mul TCost.h (TCost.mul TCost.s TCost.s)) TCost.h

/-! ### Conjugate transpose -/

/-- `TCost` is closed under conjugate transpose, with the same number of T gates. -/
theorem tcost_conjTranspose {g : Matrix Bool Bool ℂ} {n : ℕ} (hg : TCost g n) :
    TCost gᴴ n := by
  induction hg with
  | one => rw [conjTranspose_one]; exact TCost.one
  | h => rw [conjTranspose_hGate]; exact TCost.h
  | s =>
    unfold sGate
    rw [conjTranspose_pGate]
    exact tcost_sGate_cube
  | t =>
    unfold tGate
    rw [conjTranspose_pGate]
    exact tcost_pGate_neg_quarter
  | @mul g g' m n _ _ ih ih' =>
    rw [conjTranspose_mul, Nat.add_comm]
    exact TCost.mul ih' ih
  | @phase g m c hc _ ih =>
    rw [conjTranspose_smul]
    refine TCost.phase (star c) ?_ ih
    rw [star_star, mul_comm]
    exact hc

/-! ### The rotation `R_y(π/4)` -/

theorem smul_m2 (k a b c d : ℂ) : k • m2 a b c d = m2 (k * a) (k * b) (k * c) (k * d) := by
  ext i j
  cases i <;> cases j <;> simp [m2]

theorem cos_eq_e (x : ℝ) : ((Real.cos x : ℝ) : ℂ) = (e x + e (-x)) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos]
  unfold e
  push_cast
  rfl

theorem sin_eq_e (x : ℝ) : ((Real.sin x : ℝ) : ℂ) = (e (-x) - e x) * Complex.I / 2 := by
  rw [Complex.ofReal_sin, Complex.sin]
  unfold e
  push_cast
  rfl

/-- `ū · S H diag(1, u²) H S³` is the rotation with `cos = (u + ū)/2`. -/
theorem shths (u u' : ℂ) (hu : u * u' = 1) :
    u' • (sGate * hGate * m2 1 0 0 (u * u) * hGate * sGate * sGate * sGate)
      = m2 ((u + u') / 2) (-((u' - u) * Complex.I / 2)) ((u' - u) * Complex.I / 2)
          ((u + u') / 2) := by
  have hI := Complex.I_mul_I
  have hre : sGate * hGate * m2 1 0 0 (u * u) * hGate * sGate * sGate * sGate
      = sGate * (hGate * m2 1 0 0 (u * u) * hGate) * sGate * sGate * sGate := by
    simp only [Matrix.mul_assoc]
  rw [hre, hGate_mul_mul]
  unfold sGate
  rw [pGate_eq_m2, e_pi_div_two, m2_mul, m2_mul, m2_mul, m2_mul, smul_m2]
  congr 1
  · linear_combination (u / 2) * hu
  · linear_combination (u * Complex.I / 2) * hu + (u' * (1 - u * u) / 2 * Complex.I) * hI
  · linear_combination (-(u * Complex.I / 2)) * hu
  · linear_combination (u / 2) * hu
      + (u' * ((1 + u * u) / 2) * (Complex.I * Complex.I - 1)) * hI

/-- `R_y(π/4) = e^{-iπ/8} · S H T H S³`. -/
theorem rGate_eq_shths :
    rGate = e (-(Real.pi / 8))
      • (sGate * hGate * tGate * hGate * sGate * sGate * sGate) := by
  have hu : e (Real.pi / 8) * e (-(Real.pi / 8)) = 1 := by
    rw [← e_add, add_neg_cancel, e_zero]
  have ht : tGate = m2 1 0 0 (e (Real.pi / 8) * e (Real.pi / 8)) := by
    unfold tGate
    rw [pGate_eq_m2, ← e_add]
    congr 2
    ring
  rw [ht, shths _ _ hu, rGate, cos_eq_e, sin_eq_e]

theorem tcost_rGate : TCost rGate 1 := by
  rw [rGate_eq_shths]
  refine TCost.phase _ ?_ ?_
  · rw [star_e, ← e_add, neg_neg, add_neg_cancel, e_zero]
  · exact TCost.mul (TCost.mul (TCost.mul (TCost.mul (TCost.mul (TCost.mul TCost.s TCost.h)
      TCost.t) TCost.h) TCost.s) TCost.s) TCost.s

theorem rGate_transpose_eq : rGateᵀ = rGateᴴ := by
  rw [← Matrix.star_eq_conjTranspose, rGate, transpose_m2, star_m2]
  simp

theorem tcost_rGate_transpose : TCost rGateᵀ 1 := by
  rw [rGate_transpose_eq]
  exact tcost_conjTranspose tcost_rGate

theorem tcost_ryGate_quarter : TCost (ryGate (Real.pi / 4)) 1 := by
  rw [ryGate_quarter]
  exact tcost_rGate

end Line
