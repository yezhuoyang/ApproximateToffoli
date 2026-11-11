/-
  ApproxToffoli.WorstCase

  **The worst-case error of the four-CNOT circuit, and the optimum in worst-case form.**

  `hsDistance` is the *process* distance: the output distance on ONE input, the
  maximally entangled one. The stronger operational guarantee is the worst case over
  ALL inputs, including inputs entangled with an untouched reference register (half the
  diamond distance). For two unitaries `U`, `V` a pure input `ψ` on wires ⊗ reference
  gives outputs with overlap `⟨ψ|(Uᴴ V ⊗ 1)|ψ⟩ = Tr(Uᴴ V ρ)`, where `ρ` is the reduced
  state of the wires, and every density matrix arises this way. So the worst-case error
  is

      wcError U V = sup over density matrices ρ of √(1 − |Tr(Uᴴ V ρ)|²).

  This file proves, for the four-CNOT circuit `Curve.witness4` of the paper's Figure 2(b):

  * `witness4_errOn_le`  : on EVERY state the error is at most `sin(π/8)`;
  * `wcError_witness4`   : the worst-case error is exactly `sin(π/8)`;
  * `hsDistance_le_wcError` : process distance ≤ worst-case error (take `ρ = I/8`);
  * `wcError_lower_bound`: every ≤5-CNOT line circuit has worst-case error ≥ `sin(π/8)`;
  * `wcError_isLeast_four`, `wcError_isLeast_five`: the optimum, in worst-case form.

  The identification of `wcError` with the supremum over pure states of wires ⊗
  reference (purification) is standard and is NOT formalized here.

  Everything is `sorry`-free.
-/

import ApproxToffoli.CurveMain
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix Complex
open scoped ComplexOrder

noncomputable section

namespace WorstCase

/-- A density matrix of the three wires: positive semidefinite with trace one. -/
def IsDensity (ρ : Mat8) : Prop := ρ.PosSemidef ∧ Matrix.trace ρ = 1

/-- Output distance between `U` and `V` when the wires are in state `ρ`. -/
def errOn (U V ρ : Mat8) : ℝ :=
  Real.sqrt (1 - Complex.normSq (Matrix.trace (Uᴴ * V * ρ)))

/-- Worst-case error: the supremum of `errOn` over all density matrices. -/
def wcError (U V : Mat8) : ℝ :=
  sSup {d : ℝ | ∃ ρ : Mat8, IsDensity ρ ∧ errOn U V ρ = d}

/-- The maximally mixed state `I/8`. -/
def maxMixed : Mat8 := Matrix.diagonal fun _ => (((8 : ℝ)⁻¹ : ℝ) : ℂ)

lemma maxMixed_isDensity : IsDensity maxMixed := by
  refine ⟨PosSemidef.diagonal (fun _ => Complex.zero_le_real.mpr (by norm_num)), ?_⟩
  simp [maxMixed, Matrix.trace_diagonal]

lemma errOn_le_one (U V ρ : Mat8) : errOn U V ρ ≤ 1 := by
  unfold errOn
  apply Real.sqrt_le_one.mpr
  linarith [Complex.normSq_nonneg (Matrix.trace (Uᴴ * V * ρ))]

/-- On the maximally mixed state, the error is the process distance. -/
lemma errOn_maxMixed (U V : Mat8) : errOn U V maxMixed = hsDistance U V := by
  have e : maxMixed = ((((8 : ℝ)⁻¹ : ℝ) : ℂ)) • (1 : Mat8) :=
    (Matrix.smul_one_eq_diagonal _).symm
  have h : Matrix.trace (Uᴴ * V * maxMixed)
      = ((((8 : ℝ)⁻¹ : ℝ) : ℂ)) * Matrix.trace (Uᴴ * V) := by
    rw [e, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
  unfold errOn hsDistance hsFidelity
  rw [h, Complex.normSq_mul, Complex.normSq_ofReal]
  congr 1
  ring

/-- **Process distance is a lower bound on the worst-case error.** -/
theorem hsDistance_le_wcError (U V : Mat8) : hsDistance U V ≤ wcError U V := by
  unfold wcError
  refine le_csSup ⟨1, ?_⟩ ⟨maxMixed, maxMixed_isDensity, errOn_maxMixed U V⟩
  rintro d ⟨ρ, -, rfl⟩
  exact errOn_le_one U V ρ

private lemma sandwich (H D C : Mat8) (hH : H * H = 1) :
    H * (D * H) * (H * C * H) = H * (D * C) * H := by
  calc H * (D * H) * (H * C * H) = H * D * (H * H) * C * H := by noncomm_ring
    _ = H * (D * C) * H := by rw [hH]; noncomm_ring

/-- `witness4ᴴ · CCX = H_C · diag(1, ζ̄, 1, ζ̄, ζ̄, 1, ζ̄, 1) · H_C`: the error unitary is
    the phase `ζ̄ = e^{-iπ/4}` on the basis states with `a ≠ c`, up to the Hadamards. -/
lemma witness4_adj_ccx :
    Curve.witness4ᴴ * CCX
      = kron3 1 1 Hgate
          * Matrix.diagonal ![1, Curve.wm, 1, Curve.wm, Curve.wm, 1, Curve.wm, 1]
          * kron3 1 1 Hgate := by
  have hd : (Matrix.diagonal ![1, Curve.wp, 1, Curve.wp, Curve.wp, 1, Curve.wp, -1])ᴴ * CCZ8
      = Matrix.diagonal ![1, Curve.wm, 1, Curve.wm, Curve.wm, 1, Curve.wm, 1] := by
    rw [CCZ8, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [Curve.star_wp]
  rw [Curve.witness4_conj, ccx_eq_ccz_conj, Curve.ccz4Circuit_eq,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, h8_conjTranspose,
    sandwich _ _ _ h8_mul_self, hd]

/-- The scalar core: a mixture of the phases `1` and `e^{-iπ/4}` has squared modulus
    at least `cos²(π/8)`. -/
lemma normSq_two_phase (s r : ℝ) (hs : s + r = 1) :
    (2 + Real.sqrt 2) / 4 ≤ Complex.normSq ((s : ℂ) + (r : ℂ) * Curve.wm) := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  set c : ℝ := (Real.sqrt 2)⁻¹ with hcdef
  have hcpos : 0 < c := inv_pos.mpr hpos
  have hc1 : c * Real.sqrt 2 = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
  have hcc : c * c = 1 / 2 := by nlinarith
  have hsq : Real.sqrt 2 = 2 * c := by nlinarith
  have hcle : c ≤ 1 := by nlinarith
  have hwm : Curve.wm = ((c : ℝ) : ℂ) + ((-c : ℝ) : ℂ) * Complex.I := by
    rw [Curve.wm, invSqrt2, hcdef]; push_cast; ring
  have hz : (s : ℂ) + (r : ℂ) * Curve.wm
      = ((s + r * c : ℝ) : ℂ) + ((-(r * c) : ℝ) : ℂ) * Complex.I := by
    rw [hwm]; push_cast; ring
  rw [hz, Complex.normSq_add_mul_I, hsq]
  have hsr : s = 1 - r := by linarith
  subst hsr
  have key : (1 - r + r * c) ^ 2 + (-(r * c)) ^ 2
      = (2 + 2 * c) / 4 + 2 * (1 - c) * (r - 1 / 2) ^ 2 := by
    linear_combination (2 * r ^ 2) * hcc
  rw [key]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - c) (sq_nonneg (r - 1 / 2))]

/-- **Every input.** On every state of the wires, the four-CNOT circuit is within
    `sin(π/8)` of Toffoli. -/
theorem witness4_errOn_le {ρ : Mat8} (hρ : IsDensity ρ) :
    errOn Curve.witness4 CCX ρ ≤ Real.sin (Real.pi / 8) := by
  have hσpsd : (kron3 1 1 Hgate * ρ * kron3 1 1 Hgate).PosSemidef := by
    have h := hρ.1.conjTranspose_mul_mul_same (kron3 1 1 Hgate)
    rwa [h8_conjTranspose] at h
  have hσtr : Matrix.trace (kron3 1 1 Hgate * ρ * kron3 1 1 Hgate) = 1 := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, h8_mul_self, Matrix.one_mul]
    exact hρ.2
  set σ : Mat8 := kron3 1 1 Hgate * ρ * kron3 1 1 Hgate with hσ
  have htr : Matrix.trace (Curve.witness4ᴴ * CCX * ρ)
      = Matrix.trace
          (Matrix.diagonal ![1, Curve.wm, 1, Curve.wm, Curve.wm, 1, Curve.wm, 1] * σ) := by
    rw [witness4_adj_ccx]
    calc Matrix.trace (kron3 1 1 Hgate
            * Matrix.diagonal ![1, Curve.wm, 1, Curve.wm, Curve.wm, 1, Curve.wm, 1]
            * kron3 1 1 Hgate * ρ)
        = Matrix.trace (kron3 1 1 Hgate
            * (Matrix.diagonal ![1, Curve.wm, 1, Curve.wm, Curve.wm, 1, Curve.wm, 1]
              * kron3 1 1 Hgate * ρ)) := by congr 1; noncomm_ring
      _ = Matrix.trace
            ((Matrix.diagonal ![1, Curve.wm, 1, Curve.wm, Curve.wm, 1, Curve.wm, 1]
              * kron3 1 1 Hgate * ρ) * kron3 1 1 Hgate) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace
            (Matrix.diagonal ![1, Curve.wm, 1, Curve.wm, Curve.wm, 1, Curve.wm, 1] * σ) := by
          congr 1; rw [hσ]; noncomm_ring
  have hdiag : ∀ i, σ i i = (((σ i i).re : ℝ) : ℂ) := by
    intro i
    have h := hσpsd.diag_nonneg (i := i)
    rw [Complex.nonneg_iff] at h
    exact Complex.ext rfl (by simpa using h.2.symm)
  have hsum : Matrix.trace
        (Matrix.diagonal ![1, Curve.wm, 1, Curve.wm, Curve.wm, 1, Curve.wm, 1] * σ)
      = σ 0 0 + Curve.wm * σ 1 1 + σ 2 2 + Curve.wm * σ 3 3 + Curve.wm * σ 4 4 + σ 5 5
        + Curve.wm * σ 6 6 + σ 7 7 := by
    simp [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, Fin.sum_univ_eight]
  have hone : σ 0 0 + σ 1 1 + σ 2 2 + σ 3 3 + σ 4 4 + σ 5 5 + σ 6 6 + σ 7 7 = 1 := by
    have := hσtr
    simpa [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_eight] using this
  set s : ℝ := (σ 0 0).re + (σ 2 2).re + (σ 5 5).re + (σ 7 7).re with hsdef
  set r : ℝ := (σ 1 1).re + (σ 3 3).re + (σ 4 4).re + (σ 6 6).re with hrdef
  have hsr : s + r = 1 := by
    have := congrArg Complex.re hone
    simp only [Complex.add_re, Complex.one_re] at this
    rw [hsdef, hrdef]; linarith
  have hval : Matrix.trace (Curve.witness4ᴴ * CCX * ρ) = (s : ℂ) + (r : ℂ) * Curve.wm := by
    rw [htr, hsum, hdiag 0, hdiag 1, hdiag 2, hdiag 3, hdiag 4, hdiag 5, hdiag 6, hdiag 7,
      hsdef, hrdef]
    push_cast
    ring
  have hn := normSq_two_phase s r hsr
  have hsin : Real.sin (Real.pi / 8) ^ 2 = 1 / 2 - Real.sqrt 2 / 4 := Curve.sin_pi_eight_sq'
  have hsin0 : 0 ≤ Real.sin (Real.pi / 8) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])
  unfold errOn
  rw [hval]
  calc Real.sqrt (1 - Complex.normSq ((s : ℂ) + (r : ℂ) * Curve.wm))
      ≤ Real.sqrt (Real.sin (Real.pi / 8) ^ 2) := Real.sqrt_le_sqrt (by rw [hsin]; linarith)
    _ = Real.sin (Real.pi / 8) := Real.sqrt_sq hsin0

/-- **The worst-case error of the four-CNOT circuit is exactly `sin(π/8)`.** -/
theorem wcError_witness4 : wcError Curve.witness4 CCX = Real.sin (Real.pi / 8) := by
  apply le_antisymm
  · unfold wcError
    refine csSup_le ⟨_, maxMixed, maxMixed_isDensity, rfl⟩ ?_
    rintro d ⟨ρ, hρ, rfl⟩
    exact witness4_errOn_le hρ
  · rw [← Curve.witness4_distance]
    exact hsDistance_le_wcError _ _

/-- **Lower bound, worst-case form.** Every circuit with at most five adjacent CNOTs has
    worst-case error at least `sin(π/8)`. -/
theorem wcError_lower_bound {U : Mat8} (hU : AchievableCircuit 5 U) :
    Real.sin (Real.pi / 8) ≤ wcError U CCX :=
  le_trans (approxToffoli_lower_bound U hU) (hsDistance_le_wcError U CCX)

/-- **The optimum, worst-case form, at budget five.** -/
theorem wcError_isLeast_five :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 5 U ∧ wcError U CCX = d}
      (Real.sin (Real.pi / 8)) :=
  ⟨⟨Curve.witness4, AchievableCircuit.weaken Curve.witness4_achievable, wcError_witness4⟩,
   by rintro d ⟨U, hU, rfl⟩; exact wcError_lower_bound hU⟩

/-- **The optimum, worst-case form, at budget four.** -/
theorem wcError_isLeast_four :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 4 U ∧ wcError U CCX = d}
      (Real.sin (Real.pi / 8)) :=
  ⟨⟨Curve.witness4, Curve.witness4_achievable, wcError_witness4⟩,
   by rintro d ⟨U, hU, rfl⟩; exact wcError_lower_bound (AchievableCircuit.weaken hU)⟩

end WorstCase

end
