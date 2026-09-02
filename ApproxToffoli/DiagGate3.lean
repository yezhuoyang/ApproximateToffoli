/-
  Quantitative Huang-Palsberg, diagonal slice.
  File: C:\Users\yezhu\AppData\Local\Temp\claude\c--Users-yezhu-Documents-ApproximateToffoli\5e27a5cf-3a5d-4198-9eed-65587f254419\scratchpad\HPQuant.lean

  HP prove: a 3-qubit diagonal gate built from five neighbour gates lies in S4 u S5,
  and CCZ does not, hence CCZ needs six.  That is QUALITATIVE: the distance from the
  5-gate reachable set to CCZ is nonzero.

  This file upgrades it to a METRIC statement on the diagonal slice, with the SHARP
  constant: every diagonal gate reachable with five neighbour gates (or four
  unrestricted ones) is at nuclear-Finsler (bi-invariant geodesic) distance at least
  `pi` from CCZ.  `cczDist D = sum_i |arg (d_i * conj(ccz_i))|` is exactly
  `L(D . CCZ^dagger) = ||log (D . CCZ^dagger)||_*`, because D and CCZ are
  simultaneously diagonal.

  Verified with lean_run_code against the built ApproxToffoli.HP.Main.
  `#print axioms` on every theorem below: [propext, Classical.choice, Quot.sound].
-/
import ApproxToffoli.HP.Main
import Mathlib.Analysis.SpecialFunctions.Complex.Log

open Complex

set_option linter.style.longLine false

noncomputable section

/-! ## Generic phase arithmetic -/

private theorem exp_arg_of_normSq_one (z : ℂ) (hz : Complex.normSq z = 1) :
    Complex.exp ((Complex.arg z : ℝ) * Complex.I) = z := by
  have h1 : ‖z‖ = 1 := by
    have h : ‖z‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact hz
    nlinarith [norm_nonneg z]
  have h2 := Complex.norm_mul_exp_arg_mul_I z
  rw [h1] at h2
  simpa using h2

/-- If `exp (T * I) = -1` for a real `T`, then `|T| ≥ π`.
    THIS IS THE SINGLE SOURCE OF THE CONSTANT `π`. -/
private theorem pi_le_abs_of_exp_eq_neg_one (T : ℝ)
    (h : Complex.exp ((T : ℂ) * Complex.I) = -1) : Real.pi ≤ |T| := by
  by_contra hlt
  push_neg at hlt
  have hcos : Real.cos T = -1 := by
    have := congrArg Complex.re h; simpa using this
  have h1 : Real.cos Real.pi < Real.cos |T| :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg T) le_rfl hlt
  rw [Real.cos_abs, hcos, Real.cos_pi] at h1
  exact lt_irrefl _ h1

private theorem exp_four (x y z w : ℝ) :
    Complex.exp (((x + y + z + w : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((x : ℂ) * Complex.I) * Complex.exp ((y : ℂ) * Complex.I) *
        Complex.exp ((z : ℂ) * Complex.I) * Complex.exp ((w : ℂ) * Complex.I) := by
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1; push_cast; ring

private theorem abs_add4 (x y z w : ℝ) : |x + y + z + w| ≤ |x| + |y| + |z| + |w| := by
  have h1 : |x + y + z + w| ≤ |x + y + z| + |w| := abs_add_le _ _
  have h2 : |x + y + z| ≤ |x + y| + |z| := abs_add_le _ _
  have h3 : |x + y| ≤ |x| + |y| := abs_add_le _ _
  linarith

private theorem abs_sub' (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  calc |x - y| = |x + -y| := by rw [sub_eq_add_neg]
    _ ≤ |x| + |-y| := abs_add_le _ _
    _ = |x| + |y| := by rw [abs_neg]

/-- **The workhorse.**  Eight unit-modulus numbers with phases `φ_*`; if the product of
    four of them equals MINUS the product of the other four, the phases cannot all be
    small: `Σ |φ| ≥ π`.  (`S` is any upper bound for that sum, so callers may pass a
    differently-ordered sum.) -/
private theorem pi_le_sum_aux (φa φb φc φd φe φf φg φh S : ℝ)
    (za zb zc zd ze zf zg zh : ℂ)
    (ha : Complex.exp ((φa : ℂ) * Complex.I) = za)
    (hb : Complex.exp ((φb : ℂ) * Complex.I) = zb)
    (hc : Complex.exp ((φc : ℂ) * Complex.I) = zc)
    (hd : Complex.exp ((φd : ℂ) * Complex.I) = zd)
    (he : Complex.exp ((φe : ℂ) * Complex.I) = ze)
    (hf : Complex.exp ((φf : ℂ) * Complex.I) = zf)
    (hg : Complex.exp ((φg : ℂ) * Complex.I) = zg)
    (hh : Complex.exp ((φh : ℂ) * Complex.I) = zh)
    (heq : za * zb * zc * zd = -(ze * zf * zg * zh))
    (hS : |φa| + |φb| + |φc| + |φd| + |φe| + |φf| + |φg| + |φh| ≤ S) :
    Real.pi ≤ S := by
  have hU : Complex.exp (((φa + φb + φc + φd : ℝ) : ℂ) * Complex.I) =
      -Complex.exp (((φe + φf + φg + φh : ℝ) : ℂ) * Complex.I) := by
    rw [exp_four, exp_four, ha, hb, hc, hd, he, hf, hg, hh, heq]
  have hT : Complex.exp ((((φa + φb + φc + φd) - (φe + φf + φg + φh) : ℝ) : ℂ) * Complex.I) = -1 := by
    have hne : Complex.exp (((φe + φf + φg + φh : ℝ) : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    have hcast : (((φa + φb + φc + φd) - (φe + φf + φg + φh) : ℝ) : ℂ) * Complex.I =
        ((φa + φb + φc + φd : ℝ) : ℂ) * Complex.I - ((φe + φf + φg + φh : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hcast, Complex.exp_sub, hU]; field_simp
  have h1 : Real.pi ≤ |(φa + φb + φc + φd) - (φe + φf + φg + φh)| :=
    pi_le_abs_of_exp_eq_neg_one _ hT
  have h2 := abs_sub' (φa + φb + φc + φd) (φe + φf + φg + φh)
  have h3 := abs_add4 φa φb φc φd
  have h4 := abs_add4 φe φf φg φh
  linarith

/-! ## The nuclear-Finsler distance to CCZ, on diagonal gates -/

namespace DiagGate3

/-- Phase of the `i`-th diagonal entry of `D * CCZ†`. -/
def cczArg (D : DiagGate3) (i : Fin 8) : ℝ :=
  Complex.arg (D.d i * starRingEnd ℂ (CCZ_diag.d i))

/-- Nuclear-Finsler (bi-invariant geodesic) distance from `D` to `CCZ`:
    `Σ_k |arg λ_k (D * CCZ†)| = ‖log (D * CCZ†)‖_*`.  `D` and `CCZ` are
    simultaneously diagonal, so the eigenvalues are the entrywise quotients. -/
def cczDist (D : DiagGate3) : ℝ := ∑ i : Fin 8, |D.cczArg i|

theorem cczDist_nonneg (D : DiagGate3) : 0 ≤ D.cczDist :=
  Finset.sum_nonneg fun i _ => abs_nonneg _

private theorem cczExp (D : DiagGate3) (i : Fin 8) :
    Complex.exp ((D.cczArg i : ℂ) * Complex.I) = D.d i * starRingEnd ℂ (CCZ_diag.d i) := by
  refine exp_arg_of_normSq_one _ ?_
  rw [Complex.normSq_mul, Complex.normSq_conj, D.unit i, CCZ_diag.unit i, mul_one]

private theorem cczDist_expand (D : DiagGate3) : D.cczDist =
    |D.cczArg 0| + |D.cczArg 1| + |D.cczArg 2| + |D.cczArg 3| +
    |D.cczArg 4| + |D.cczArg 5| + |D.cczArg 6| + |D.cczArg 7| := by
  rw [cczDist, Fin.sum_univ_eight]

/-- **Quantitative Huang-Palsberg (algebraic core).**
    Every diagonal 3-qubit gate in `S₄ ∪ S₅` is at nuclear-Finsler distance at least
    `π` from `CCZ`.

    Each of the four defining product identities of `S₄`, `S₅¹`, `S₅²`, `S₅³` becomes,
    after dividing entrywise by `CCZ`, the statement that a product of four unit
    numbers equals MINUS the product of the other four -- the `-1` coming from the
    single `-1` entry of `CCZ`.  A product of eight unit numbers equal to `-1` forces
    the total phase budget to be at least `π`. -/
theorem pi_le_cczDist_of_inS4_or_S5 (D : DiagGate3) (h : D.inS4 ∨ D.inS5) :
    Real.pi ≤ D.cczDist := by
  have hexp := D.cczExp
  have hsum := D.cczDist_expand
  rcases h with h4 | (h51 | h52 | h53)
  · rw [DiagGate3.inS4] at h4
    refine pi_le_sum_aux (D.cczArg 0) (D.cczArg 3) (D.cczArg 5) (D.cczArg 6)
      (D.cczArg 1) (D.cczArg 2) (D.cczArg 4) (D.cczArg 7) D.cczDist _ _ _ _ _ _ _ _
      (hexp 0) (hexp 3) (hexp 5) (hexp 6) (hexp 1) (hexp 2) (hexp 4) (hexp 7) ?_ ?_
    · simp only [ccz_d_0, ccz_d_1, ccz_d_2, ccz_d_3, ccz_d_4, ccz_d_5, ccz_d_6, ccz_d_7,
        map_one, map_neg, mul_one, mul_neg]
      linear_combination h4
    · rw [hsum]; linarith
  · refine pi_le_sum_aux (D.cczArg 0) (D.cczArg 3) (D.cczArg 4) (D.cczArg 7)
      (D.cczArg 1) (D.cczArg 2) (D.cczArg 5) (D.cczArg 6) D.cczDist _ _ _ _ _ _ _ _
      (hexp 0) (hexp 3) (hexp 4) (hexp 7) (hexp 1) (hexp 2) (hexp 5) (hexp 6) ?_ ?_
    · simp only [ccz_d_0, ccz_d_1, ccz_d_2, ccz_d_3, ccz_d_4, ccz_d_5, ccz_d_6, ccz_d_7,
        map_one, map_neg, mul_one, mul_neg]
      linear_combination -h51
    · rw [hsum]; linarith
  · refine pi_le_sum_aux (D.cczArg 0) (D.cczArg 2) (D.cczArg 5) (D.cczArg 7)
      (D.cczArg 1) (D.cczArg 3) (D.cczArg 4) (D.cczArg 6) D.cczDist _ _ _ _ _ _ _ _
      (hexp 0) (hexp 2) (hexp 5) (hexp 7) (hexp 1) (hexp 3) (hexp 4) (hexp 6) ?_ ?_
    · simp only [ccz_d_0, ccz_d_1, ccz_d_2, ccz_d_3, ccz_d_4, ccz_d_5, ccz_d_6, ccz_d_7,
        map_one, map_neg, mul_one, mul_neg]
      linear_combination -h52
    · rw [hsum]; linarith
  · refine pi_le_sum_aux (D.cczArg 0) (D.cczArg 1) (D.cczArg 6) (D.cczArg 7)
      (D.cczArg 2) (D.cczArg 3) (D.cczArg 4) (D.cczArg 5) D.cczDist _ _ _ _ _ _ _ _
      (hexp 0) (hexp 1) (hexp 6) (hexp 7) (hexp 2) (hexp 3) (hexp 4) (hexp 5) ?_ ?_
    · simp only [ccz_d_0, ccz_d_1, ccz_d_2, ccz_d_3, ccz_d_4, ccz_d_5, ccz_d_6, ccz_d_7,
        map_one, map_neg, mul_one, mul_neg]
      linear_combination -h53
    · rw [hsum]; linarith

end DiagGate3

/-! ## The consequence for neighbour circuits -/

/-- **Quantitative Huang-Palsberg, diagonal slice.**
    If a diagonal 3-qubit gate `D` is implementable with five neighbour (AB/BC)
    two-qubit unitaries, then `D` is at nuclear-Finsler distance at least `π` from
    `CCZ`:  `Σ_k |arg λ_k (D . CCZ†)| ≥ π`.

    This is CLAIM (G) restricted to diagonal words, with the sharp constant.
    HP's `CCZ_not_five_neighbor` is the special case `D = CCZ` (distance `0 < π`);
    see `ccz_not_five_neighbor_of_quantitative` below. -/
theorem five_unitaryNeighbor_cczDist_ge_pi (D : DiagGate3)
    (h : UnitaryNeighborCircuit 5 D.toMatrix) : Real.pi ≤ D.cczDist :=
  DiagGate3.pi_le_cczDist_of_inS4_or_S5 D (five_unitaryNeighbor_implies_S4_or_S5 D h)

/-- The same bound for the strictly larger class of FOUR arbitrary two-qubit gates
    (AB, BC *or* AC), i.e. HP's `UnitaryUnrestrictedCircuit 4`. -/
theorem four_unitaryUnrestricted_cczDist_ge_pi (D : DiagGate3)
    (h : UnitaryUnrestrictedCircuit 4 D.toMatrix) : Real.pi ≤ D.cczDist :=
  DiagGate3.pi_le_cczDist_of_inS4_or_S5 D (four_unitaryUnrestricted_implies_S4_or_S5 D h)

/-! ## Sharpness, and recovery of the qualitative theorem -/

/-- The identity diagonal gate. -/
def oneDiag : DiagGate3 where
  d := fun _ => 1
  unit := by intro i; simp

theorem oneDiag_inS4 : oneDiag.inS4 := by simp [DiagGate3.inS4, oneDiag]

/-- **The constant `π` is ATTAINED**: the identity is a diagonal gate reachable with
    zero neighbour gates, at nuclear distance exactly `π` from CCZ.  So the `π` in
    `five_unitaryNeighbor_cczDist_ge_pi` cannot be increased, and the minimum of
    `cczDist` over DIAGONAL five-gate words is exactly `π`. -/
theorem oneDiag_cczDist : oneDiag.cczDist = Real.pi := by
  rw [DiagGate3.cczDist, Fin.sum_univ_eight]
  have h : ∀ i : Fin 8, i ≠ 7 → oneDiag.cczArg i = 0 := by
    intro i hi
    rw [DiagGate3.cczArg]
    fin_cases i <;> simp_all [oneDiag]
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide),
      h 4 (by decide), h 5 (by decide), h 6 (by decide)]
  have h7 : oneDiag.cczArg 7 = Real.pi := by
    rw [DiagGate3.cczArg]; simp [oneDiag]
  rw [h7, abs_of_nonneg Real.pi_nonneg]
  ring

/-- CCZ sits at distance `0` from itself. -/
theorem cczDiag_cczDist : CCZ_diag.cczDist = 0 := by
  rw [DiagGate3.cczDist]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [DiagGate3.cczArg, Complex.mul_conj]
  norm_cast
  rw [CCZ_diag.unit i]
  simp

/-- **The quantitative theorem implies the qualitative one.**  A direct re-derivation
    of HP's `CCZ_not_five_neighbor` from the metric bound, confirming the upgrade is
    conservative. -/
theorem ccz_not_five_neighbor_of_quantitative :
    ¬ UnitaryNeighborCircuit 5 CCZ_diag.toMatrix := by
  intro h
  have := five_unitaryNeighbor_cczDist_ge_pi CCZ_diag h
  rw [cczDiag_cczDist] at this
  exact absurd this (not_le.mpr Real.pi_pos)

end
