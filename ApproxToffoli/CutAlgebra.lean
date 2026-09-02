/-
  ApproxToffoli.CutAlgebra

  Gate-level algebra for the cut-form proof of the 5-gate trace bound, plus the
  two purely scalar ingredients (`cos (π/8)` identities, and the C2/C3 pair).

  Contents, in the numbering of `notes/trace_bound_reduction.md`:

  * **R1** `CCX = H_C · CCZ · H_C` (`ccx_eq_ccz_conj`), and its trace form
    `trace_ccx_conj` / `trace_ccx_eq_trace_sub`. Since `H_C² = I`, the map
    `U ↦ H_C U H_C` is an involution of the circuit family, so replacing the
    target `CCX` by `CCZ` is lossless — which matters because `CCZ`, unlike
    `CCX`, is invariant under every permutation of A, B, C.
  * **R2** `CX_BA = (H⊗H⊗I) CX_AB (H⊗H⊗I)` and `CX_CB = (I⊗H⊗H) CX_BC (I⊗H⊗H)`
    (`cx_ba_eq_conj`, `cx_cb_eq_conj`, and the converses): gate DIRECTION is
    free, the Hadamards being absorbed into the adjacent single-qubit layers.
  * **A↔C** the relabelling `swapMatAC` (`|abc⟩ ↦ |cba⟩`), proved unitary,
    self-inverse, to fix `CCZ8`, and to exchange `CX_AB ↔ CX_CB`,
    `CX_BC ↔ CX_BA`. This is what lets the `m ≥ 3` cases be handled through the
    OTHER cut; it is load-bearing, not cosmetic, because `F(3) = F(4) = 8`.
  * **constants** `cos²(π/8) = (2+√2)/4`, `64 cos²(π/8) = 32 + 16√2`, and
    `2√(8+4√2) = 8 cos(π/8)` — the last is the exact form of the
    Cauchy–Schwarz endpoint, and it is an identity, not an estimate.
  * **C3** (`c3`) and **C2 from C3** (`c2_of_c3`).

  Everything in this file is `sorry`-free. Index conventions (read off from
  `TensorProduct.lean` / `Gates.lean`): `Fin 8` is `|abc⟩ ↦ 4a + 2b + c`, so
  qubit A is the most significant bit and qubit C the least; the 1st/2nd/3rd
  argument of `kron3` acts on qubit A/B/C.
-/

import ApproxToffoli.BaseCase
import ApproxToffoli.Helpers
import ApproxToffoli.Kron2
import Mathlib.Analysis.Complex.Polynomial.Basic

open Matrix Complex

noncomputable section

/-! ## The scalar `1/√2` -/

/-- The real scalar `1/√2`, viewed in `ℂ`. -/
def invSqrt2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

lemma invSqrt2_sq : invSqrt2 * invSqrt2 = 2⁻¹ := by
  rw [invSqrt2, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

lemma invSqrt2_pow2 : invSqrt2 ^ 2 = 2⁻¹ := by
  rw [pow_two]; exact invSqrt2_sq

lemma invSqrt2_pow4 : invSqrt2 ^ 4 = 4⁻¹ := by
  have h : invSqrt2 ^ 4 = (invSqrt2 ^ 2) ^ 2 := by ring
  rw [h, invSqrt2_pow2]; norm_num

lemma star_invSqrt2 : star invSqrt2 = invSqrt2 := by
  simp [invSqrt2, ← Complex.ofReal_inv]

/-! ## The Hadamard gate -/

/-- The Hadamard gate `H = (1/√2) * !![1,1;1,-1]`. -/
def Hgate : Mat2 := Matrix.of !![invSqrt2, invSqrt2; invSqrt2, -invSqrt2]

/-- `H` is Hermitian. -/
lemma hgate_hermitian : Hgate.conjTranspose = Hgate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Hgate, Matrix.conjTranspose_apply, star_invSqrt2]

/-- `H² = I`. -/
lemma hgate_sq : Hgate * Hgate = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Hgate, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;>
    norm_num [invSqrt2_pow2, invSqrt2_pow4]

/-- `H` is unitary. -/
lemma hgate_unitary : IsUnitary2 Hgate := by
  rw [IsUnitary2, hgate_hermitian, hgate_sq]

/-- `I ⊗ I ⊗ I = I`. -/
lemma kron3_one : kron3 1 1 1 = (1 : Mat8) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kron3, decode3, Matrix.one_apply]

/-! ## The CCZ target -/

/-- `CCZ = I − 2|111⟩⟨111|`, the target after the R1 reduction. It is invariant
    under every permutation of A, B, C, unlike `CCX`. -/
def CCZ8 : Mat8 := Matrix.diagonal ![1, 1, 1, 1, 1, 1, 1, -1]

lemma ccz8_conjTranspose : CCZ8.conjTranspose = CCZ8 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CCZ8, Matrix.conjTranspose_apply]

lemma ccz8_mul_self : CCZ8 * CCZ8 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CCZ8, Matrix.mul_apply, Fin.sum_univ_eight]

/-! ## R1 : `CCX = H_C · CCZ · H_C` -/

set_option maxHeartbeats 1000000 in
-- Heartbeat bump: 64 entrywise cases, each an 8×8 double `Matrix.mul_apply`
-- expansion, exceeds the default budget.
/-- **R1.** Conjugating `CCZ` by a Hadamard on qubit C gives the Toffoli gate. -/
lemma ccx_eq_ccz_conj :
    CCX = kron3 1 1 Hgate * CCZ8 * kron3 1 1 Hgate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CCX, CCZ8, kron3, decode3, Hgate, pauliX, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.one_apply, Fin.sum_univ_eight] <;>
    ring_nf <;>
    norm_num [invSqrt2_pow2, invSqrt2_pow4]

/-- `H_C := I ⊗ I ⊗ H` is Hermitian. -/
lemma h8_conjTranspose : (kron3 1 1 Hgate).conjTranspose = kron3 1 1 Hgate := by
  rw [kron3_conjTranspose, hgate_hermitian, Matrix.conjTranspose_one]

/-- `H_C² = I`, so `U ↦ H_C U H_C` is an involution — hence a bijection of the
circuit family, which is the substantive content of R1. -/
lemma h8_mul_self : kron3 1 1 Hgate * kron3 1 1 Hgate = (1 : Mat8) := by
  rw [kron3_mul, hgate_sq, mul_one, kron3_one]

/-- `Tr(CCZ · W) = Tr W - 2 · W₇₇`, i.e. `CCZ = I - 2|111⟩⟨111|` at trace level. -/
lemma trace_ccz_mul (W : Mat8) :
    Matrix.trace (CCZ8 * W) = Matrix.trace W - 2 * W 7 7 := by
  simp [CCZ8, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul,
    Fin.sum_univ_eight]
  ring

/-- **R1, trace form.** The Toffoli overlap of `U` equals the `CCZ` overlap of
`H_C U H_C`. -/
lemma trace_ccx_conj (U : Mat8) :
    Matrix.trace (U.conjTranspose * CCX)
      = Matrix.trace ((kron3 1 1 Hgate * U * kron3 1 1 Hgate).conjTranspose * CCZ8) := by
  calc Matrix.trace (U.conjTranspose * CCX)
      = Matrix.trace ((U.conjTranspose * (kron3 1 1 Hgate * CCZ8)) * kron3 1 1 Hgate) := by
        rw [ccx_eq_ccz_conj]; congr 1; noncomm_ring
    _ = Matrix.trace (kron3 1 1 Hgate * (U.conjTranspose * (kron3 1 1 Hgate * CCZ8))) :=
        Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((kron3 1 1 Hgate * U * kron3 1 1 Hgate).conjTranspose * CCZ8) := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, h8_conjTranspose]
        congr 1
        noncomm_ring

/-- The two previous lemmas combined: the quantity optimized in the trace bound is
`Tr W - 2 W₇₇` for `W = (H_C U H_C)†`. -/
lemma trace_ccx_eq_trace_sub (U : Mat8) :
    Matrix.trace (U.conjTranspose * CCX)
      = Matrix.trace ((kron3 1 1 Hgate * U * kron3 1 1 Hgate).conjTranspose)
        - 2 * ((kron3 1 1 Hgate * U * kron3 1 1 Hgate).conjTranspose) 7 7 := by
  rw [trace_ccx_conj U, Matrix.trace_mul_comm, trace_ccz_mul]

/-! ## R2 : the direction of a CX gate is free -/

/-- `H_A H_B` squares to the identity. -/
lemma hAB_mul_self : kron3 Hgate Hgate 1 * kron3 Hgate Hgate 1 = (1 : Mat8) := by
  rw [kron3_mul, hgate_sq, mul_one, kron3_one]

/-- `H_B H_C` squares to the identity. -/
lemma hBC_mul_self : kron3 1 Hgate Hgate * kron3 1 Hgate Hgate = (1 : Mat8) := by
  rw [kron3_mul, hgate_sq, mul_one, kron3_one]

set_option maxHeartbeats 1000000 in
-- Heartbeat bump: 64 entrywise cases with double `Matrix.mul_apply` expansion.
/-- **R2 (AB).** Conjugating `CX_AB` by Hadamards on A and B reverses the gate. -/
lemma cx_ba_eq_conj :
    CX_BA = kron3 Hgate Hgate 1 * CX_AB * kron3 Hgate Hgate 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CX_AB, CX_BA, kron3, decode3, Hgate, pauliX, proj0, proj1, I₂,
      Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply, Fin.sum_univ_eight] <;>
    ring_nf <;>
    norm_num [invSqrt2_pow2, invSqrt2_pow4]

set_option maxHeartbeats 1000000 in
-- Heartbeat bump: 64 entrywise cases with double `Matrix.mul_apply` expansion.
/-- **R2 (BC).** Conjugating `CX_BC` by Hadamards on B and C reverses the gate. -/
lemma cx_cb_eq_conj :
    CX_CB = kron3 1 Hgate Hgate * CX_BC * kron3 1 Hgate Hgate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CX_BC, CX_CB, kron3, decode3, Hgate, pauliX, proj0, proj1, I₂,
      Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply, Fin.sum_univ_eight] <;>
    ring_nf <;>
    norm_num [invSqrt2_pow2, invSqrt2_pow4]

/-- R2 in the opposite direction. -/
lemma cx_ab_eq_conj :
    CX_AB = kron3 Hgate Hgate 1 * CX_BA * kron3 Hgate Hgate 1 := by
  rw [cx_ba_eq_conj]
  calc CX_AB = 1 * CX_AB * 1 := by rw [one_mul, mul_one]
    _ = kron3 Hgate Hgate 1 *
          (kron3 Hgate Hgate 1 * CX_AB * kron3 Hgate Hgate 1) * kron3 Hgate Hgate 1 := by
        rw [← hAB_mul_self]; noncomm_ring

/-- R2 in the opposite direction. -/
lemma cx_bc_eq_conj :
    CX_BC = kron3 1 Hgate Hgate * CX_CB * kron3 1 Hgate Hgate := by
  rw [cx_cb_eq_conj]
  calc CX_BC = 1 * CX_BC * 1 := by rw [one_mul, mul_one]
    _ = kron3 1 Hgate Hgate *
          (kron3 1 Hgate Hgate * CX_BC * kron3 1 Hgate Hgate) * kron3 1 Hgate Hgate := by
        rw [← hBC_mul_self]; noncomm_ring

/-! ## The A ↔ C relabelling -/

/-- `|abc⟩ ↦ |cba⟩` on indices: `4a+2b+c ↦ 4c+2b+a`. -/
def swapIdx : Fin 8 → Fin 8 := ![0, 4, 2, 6, 1, 5, 3, 7]

/-- The permutation matrix exchanging qubits A and C. -/
def swapMatAC : Mat8 := Matrix.of fun i j => if i = swapIdx j then 1 else 0

lemma swapIdx_involutive (i : Fin 8) : swapIdx (swapIdx i) = i := by
  fin_cases i <;> simp [swapIdx]

lemma swapMatAC_mul (M : Mat8) (i j : Fin 8) : (swapMatAC * M) i j = M (swapIdx i) j := by
  fin_cases i <;> simp [swapMatAC, swapIdx, Matrix.mul_apply, Fin.sum_univ_eight]

lemma mul_swapMatAC (M : Mat8) (i j : Fin 8) : (M * swapMatAC) i j = M i (swapIdx j) := by
  fin_cases j <;> simp [swapMatAC, swapIdx, Matrix.mul_apply]

/-- Conjugation by `swapMatAC` is exactly the index relabelling `swapIdx`. -/
lemma swapMatAC_conj_apply (M : Mat8) (i j : Fin 8) :
    (swapMatAC * M * swapMatAC) i j = M (swapIdx i) (swapIdx j) := by
  rw [mul_swapMatAC, swapMatAC_mul]

lemma swapMatAC_mul_self : swapMatAC * swapMatAC = 1 := by
  ext i j
  rw [mul_swapMatAC]
  fin_cases i <;> fin_cases j <;> simp [swapMatAC, swapIdx]

lemma swapMatAC_conjTranspose : swapMatAC.conjTranspose = swapMatAC := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapMatAC, swapIdx, Matrix.conjTranspose_apply]

/-- `swapMatAC` is unitary. -/
lemma swapMatAC_unitary : swapMatAC.conjTranspose * swapMatAC = 1 := by
  rw [swapMatAC_conjTranspose, swapMatAC_mul_self]

/-- **`CCZ` is invariant under the A↔C relabelling.** -/
lemma ccz8_perm_symm_AC : swapMatAC * CCZ8 * swapMatAC = CCZ8 := by
  ext i j
  rw [swapMatAC_conj_apply]
  fin_cases i <;> fin_cases j <;> simp [CCZ8, swapIdx]

set_option maxHeartbeats 800000 in
-- Heartbeat bump: 64 entrywise cases over `kron3`/`decode3` unfolding.
/-- A↔C turns "A controls B" into "C controls B". -/
lemma swapMatAC_cx_ab : swapMatAC * CX_AB * swapMatAC = CX_CB := by
  ext i j
  rw [swapMatAC_conj_apply]
  fin_cases i <;> fin_cases j <;>
    simp [CX_AB, CX_CB, kron3, decode3, swapIdx, proj0, proj1, pauliX, I₂,
      Matrix.add_apply, Matrix.one_apply]

set_option maxHeartbeats 800000 in
-- Heartbeat bump: 64 entrywise cases over `kron3`/`decode3` unfolding.
/-- A↔C turns "B controls C" into "B controls A". -/
lemma swapMatAC_cx_bc : swapMatAC * CX_BC * swapMatAC = CX_BA := by
  ext i j
  rw [swapMatAC_conj_apply]
  fin_cases i <;> fin_cases j <;>
    simp [CX_BC, CX_BA, kron3, decode3, swapIdx, proj0, proj1, pauliX, I₂,
      Matrix.add_apply, Matrix.one_apply]

/-- A↔C turns "C controls B" into "A controls B". -/
lemma swapMatAC_cx_cb : swapMatAC * CX_CB * swapMatAC = CX_AB := by
  ext i j
  rw [swapMatAC_conj_apply, ← swapMatAC_cx_ab, swapMatAC_conj_apply,
    swapIdx_involutive, swapIdx_involutive]

/-- A↔C turns "B controls A" into "B controls C". -/
lemma swapMatAC_cx_ba : swapMatAC * CX_BA * swapMatAC = CX_BC := by
  ext i j
  rw [swapMatAC_conj_apply, ← swapMatAC_cx_bc, swapMatAC_conj_apply,
    swapIdx_involutive, swapIdx_involutive]

set_option maxHeartbeats 800000 in
-- Heartbeat bump: 64 entrywise cases over `kron3`/`decode3` unfolding.
/-- The A↔C relabelling of a single-qubit layer is again a single-qubit layer,
so the whole circuit family is A↔C invariant. -/
lemma swapMatAC_kron3 (A B C : Mat2) :
    swapMatAC * kron3 A B C * swapMatAC = kron3 C B A := by
  ext i j
  rw [swapMatAC_conj_apply]
  fin_cases i <;> fin_cases j <;> simp [kron3, decode3, swapIdx] <;> ring

/-! ## Constant identities for `cos (π/8)`

The target constant is `8 cos(π/8) = 7.3910362601…`, attained exactly, so these
must be identities rather than estimates. -/

/-- `cos (π/8) ≥ 0`, since `π/8 ∈ [-π/2, π/2]`. -/
lemma cos_pi_eight_nonneg : 0 ≤ Real.cos (Real.pi/8) := by
  apply Real.cos_nonneg_of_mem_Icc
  constructor
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

/-- Half-angle: `cos²(π/8) = (2 + √2)/4`, from `cos(2x) = 2cos²x - 1` at `x = π/8`. -/
lemma cos_pi_eight_sq : Real.cos (Real.pi/8) ^ 2 = (2 + Real.sqrt 2)/4 := by
  have h := Real.cos_two_mul (Real.pi/8)
  rw [show (2:ℝ) * (Real.pi/8) = Real.pi/4 by ring, Real.cos_pi_div_four] at h
  linarith

/-- `8 cos(π/8) = 4 √(2 + √2)`. -/
lemma eight_cos_pi_eight :
    8 * Real.cos (Real.pi/8) = 4 * Real.sqrt (2 + Real.sqrt 2) := by
  have hs : Real.sqrt (2 + Real.sqrt 2) = 2 * Real.cos (Real.pi/8) := by
    rw [show (2 + Real.sqrt 2) = (2 * Real.cos (Real.pi/8))^2 by
      rw [mul_pow, cos_pi_eight_sq]; ring]
    exact Real.sqrt_sq (by linarith [cos_pi_eight_nonneg])
  rw [hs]; ring

/-- `64 cos²(π/8) = 32 + 16√2`. -/
lemma sixtyfour_cos_sq :
    64 * Real.cos (Real.pi/8)^2 = 32 + 16 * Real.sqrt 2 := by
  rw [cos_pi_eight_sq]; ring

/-- `(8 cos(π/8))² = 32 + 16√2 = 54.627…`. -/
lemma eight_cos_sq : (8 * Real.cos (Real.pi/8))^2 = 32 + 16 * Real.sqrt 2 := by
  nlinarith [sixtyfour_cos_sq]

/-- `2 √(8 + 4√2) = 8 cos(π/8)`: the exact form of the Cauchy–Schwarz endpoint.
This is the identity that makes the whole chain tight — the Cauchy–Schwarz step
loses nothing precisely because this is an equality. -/
lemma two_sqrt_eight_add :
    2 * Real.sqrt (8 + 4*Real.sqrt 2) = 8 * Real.cos (Real.pi/8) := by
  rw [show (8 + 4*Real.sqrt 2) = (4 : ℝ) * (2 + Real.sqrt 2) by ring,
    Real.sqrt_mul (by norm_num),
    show Real.sqrt 4 = 2 by
      rw [show (4:ℝ) = 2^2 by norm_num]; exact Real.sqrt_sq (by norm_num),
    eight_cos_pi_eight]
  ring

/-! ## C2 from C3

`C2` is the spectral form of the bound: for `μ` and four `λ_k` on the unit
circle, `∑ |μ + λ_k| ≤ 8 cos(π/8)` whenever `|∑ λ_k| ≤ 2√2`. Both the
Cauchy–Schwarz step here and `C3` below are tight at the same configuration
`λ = (1,1,i,i)`, `μ = e^{iπ/4}`, which is why the composition is exact. -/

/-- **C2 from C3.**  If `μ` and the four `l k` are unimodular and
`|∑ k, l k| ≤ 2√2`, then `∑ k, |μ + l k| ≤ 8 cos(π/8)`.

Proof: `|μ + l k|² = 2 + 2 Re(μ · conj (l k))`, so
`∑ |μ + l k|² = 8 + 2 Re(μ · conj S) ≤ 8 + 2‖S‖ ≤ 8 + 4√2`; four-term
Cauchy–Schwarz gives `(∑ |μ + l k|)² ≤ 4 ∑ |μ + l k|² ≤ 32 + 16√2 = (8cos(π/8))²`,
and both sides are nonnegative. -/
lemma c2_of_c3 (l : Fin 4 → ℂ) (μ : ℂ) (hμ : ‖μ‖ = 1)
    (hl : ∀ k, ‖l k‖ = 1)
    (hS : ‖∑ k, l k‖ ≤ 2 * Real.sqrt 2) :
    ∑ k, ‖μ + l k‖ ≤ 8 * Real.cos (Real.pi/8) := by
  have hnμ : Complex.normSq μ = 1 := by rw [← Complex.sq_norm, hμ]; norm_num
  have hnl : ∀ k, Complex.normSq (l k) = 1 := by
    intro k; rw [← Complex.sq_norm, hl k]; norm_num
  have key : ∀ k, ‖μ + l k‖^2 = 2 + 2 * (μ * (starRingEnd ℂ) (l k)).re := by
    intro k
    rw [Complex.sq_norm, Complex.normSq_add, hnμ, hnl k]; ring
  have hsum : ((μ * (starRingEnd ℂ) (l 0)).re + (μ * (starRingEnd ℂ) (l 1)).re
      + (μ * (starRingEnd ℂ) (l 2)).re + (μ * (starRingEnd ℂ) (l 3)).re)
      = (μ * (starRingEnd ℂ) (∑ k, l k)).re := by
    rw [Fin.sum_univ_four]
    simp only [map_add, mul_add, Complex.add_re]
  have hre : (μ * (starRingEnd ℂ) (∑ k, l k)).re ≤ 2 * Real.sqrt 2 := by
    refine le_trans (Complex.re_le_norm _) ?_
    rw [norm_mul, hμ, RCLike.norm_conj, one_mul]
    exact hS
  set a0 := ‖μ + l 0‖ with ha0
  set a1 := ‖μ + l 1‖ with ha1
  set a2 := ‖μ + l 2‖ with ha2
  set a3 := ‖μ + l 3‖ with ha3
  have hn0 : 0 ≤ a0 := norm_nonneg _
  have hn1 : 0 ≤ a1 := norm_nonneg _
  have hn2 : 0 ≤ a2 := norm_nonneg _
  have hn3 : 0 ≤ a3 := norm_nonneg _
  have hsq : a0^2 + a1^2 + a2^2 + a3^2 ≤ 8 + 4 * Real.sqrt 2 := by
    rw [ha0, ha1, ha2, ha3, key 0, key 1, key 2, key 3]
    nlinarith [hsum, hre]
  have hcs : (a0 + a1 + a2 + a3)^2 ≤ 4 * (a0^2 + a1^2 + a2^2 + a3^2) := by
    nlinarith [sq_nonneg (a0 - a1), sq_nonneg (a0 - a2), sq_nonneg (a0 - a3),
      sq_nonneg (a1 - a2), sq_nonneg (a1 - a3), sq_nonneg (a2 - a3)]
  have hfin : (a0 + a1 + a2 + a3)^2 ≤ (8 * Real.cos (Real.pi/8))^2 := by
    rw [eight_cos_sq]; linarith
  have hgoal : a0 + a1 + a2 + a3 ≤ 8 * Real.cos (Real.pi/8) := by
    nlinarith [hfin, hn0, hn1, hn2, hn3, cos_pi_eight_nonneg]
  simpa [Fin.sum_univ_four] using hgoal

/-! ## C3

Four unit complex numbers whose product is `-1` and whose imaginary-part sum is
"balanced" (lies between twice the min and twice the max of the individual
imaginary parts) have `|∑ λ_k| ≤ 2√2`.

The proof is elementary and trigonometry-free, following P1–P7 of
`notes/trace_bound_reduction.md`. P1 is the ONLY place where `∏ λ_k = -1` is
used, and it must be used structurally: an argument passing through the vector
of imaginary parts alone provably cannot work (`y = (1/3,1/3,1/3,1)` satisfies
the balance condition but is not realizable). -/

/-- A unit complex number times its conjugate is `1`. -/
theorem c3_unit_mul_conj (z : ℂ) (h : ‖z‖ = 1) : z * (starRingEnd ℂ) z = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h]; norm_num

/-- `‖z‖ = 1` in coordinates. -/
theorem c3_unit_sq_sum (z : ℂ) (h : ‖z‖ = 1) : z.re ^ 2 + z.im ^ 2 = 1 := by
  have h2 := Complex.normSq_eq_norm_sq z
  rw [h, Complex.normSq_apply] at h2
  linear_combination h2

/-- **P2.** If `u` is a unit square root of `x * y` and `‖x‖ = 1`, then `x` and `y`
are `u` times a unit number and `u` times its conjugate. -/
theorem c3_split (x y u : ℂ) (hun : ‖u‖ = 1) (hu2 : u ^ 2 = x * y) (hxn : ‖x‖ = 1) :
    ∃ t : ℂ, ‖t‖ = 1 ∧ x = u * t ∧ y = u * (starRingEnd ℂ) t := by
  have hu : u * (starRingEnd ℂ) u = 1 := c3_unit_mul_conj u hun
  have hx : x * (starRingEnd ℂ) x = 1 := c3_unit_mul_conj x hxn
  refine ⟨x * (starRingEnd ℂ) u, ?_, ?_, ?_⟩
  · rw [norm_mul, RCLike.norm_conj, hxn, hun]; norm_num
  · linear_combination (-x) * hu
  · rw [map_mul, Complex.conj_conj]
    have h3 : u * ((starRingEnd ℂ) x * u) = u ^ 2 * (starRingEnd ℂ) x := by ring
    rw [h3, hu2]
    linear_combination (-y) * hx

/-- **P1.** `v := i * conj w` is a unit square root of `c * d`; this is the only place
where `a * b * c * d = -1` is used. -/
theorem c3_vexists (a b c d w : ℂ) (hwn : ‖w‖ = 1) (hw2 : w ^ 2 = a * b)
    (hprod : a * b * c * d = -1) :
    ∃ v : ℂ, ‖v‖ = 1 ∧ v ^ 2 = c * d ∧ v.re = w.im ∧ v.im = w.re := by
  refine ⟨Complex.I * (starRingEnd ℂ) w, ?_, ?_, ?_, ?_⟩
  · simp [hwn]
  · have hw0 : w ≠ 0 := by intro h; rw [h] at hwn; simp at hwn
    have hu : w * (starRingEnd ℂ) w = 1 := c3_unit_mul_conj w hwn
    have key : (Complex.I * (starRingEnd ℂ) w) ^ 2 * w ^ 2 = c * d * w ^ 2 := by
      have e1 : (Complex.I * (starRingEnd ℂ) w) ^ 2 * w ^ 2
          = Complex.I ^ 2 * (w * (starRingEnd ℂ) w) ^ 2 := by ring
      rw [e1, hu, Complex.I_sq, hw2]
      linear_combination -hprod
    exact mul_right_cancel₀ (pow_ne_zero 2 hw0) key
  · simp [Complex.mul_re]
  · simp [Complex.mul_im]

/-- Cancel a common nonzero factor inside absolute values. -/
theorem c3_key_sq (x y z : ℝ) (hy : y ≠ 0) (h : |x * y| ≤ |z * y|) : x ^ 2 ≤ z ^ 2 := by
  rw [abs_mul, abs_mul] at h
  have hy' : 0 < |y| := abs_pos.mpr hy
  have hxz : |x| ≤ |z| := le_of_mul_le_mul_right h hy'
  nlinarith [abs_nonneg x, abs_nonneg z, sq_abs x, sq_abs z]

/-- **P5 + P6 + P7.** The real core of C3: with `a₁² + A² = b₁² + B² = c₁² + d₁² = 1`
and the two sign conditions, `J = a₁² + b₁² + 4a₁b₁c₁d₁ ≤ 2`. -/
theorem c3_real (a₁ A b₁ B c₁ d₁ : ℝ)
    (h1 : a₁ ^ 2 + A ^ 2 = 1) (h2 : b₁ ^ 2 + B ^ 2 = 1) (h3 : c₁ ^ 2 + d₁ ^ 2 = 1)
    (hup : b₁ * c₁ ≤ |A * c₁| ∨ a₁ * d₁ ≤ |B * d₁|)
    (hlo : -|A * c₁| ≤ b₁ * c₁ ∨ -|B * d₁| ≤ a₁ * d₁) :
    a₁ ^ 2 + b₁ ^ 2 + 4 * (a₁ * b₁ * c₁ * d₁) ≤ 2 := by
  have hP5 : a₁ ^ 2 + b₁ ^ 2 ≤ 1 ∨ a₁ * b₁ * c₁ * d₁ ≤ 0 := by
    by_cases hsign : a₁ * b₁ * c₁ * d₁ ≤ 0
    · exact Or.inr hsign
    · left
      push_neg at hsign
      have hpp : 0 < (a₁ * d₁) * (b₁ * c₁) := by nlinarith
      rcases mul_pos_iff.mp hpp with ⟨hA1, hB1⟩ | ⟨hA1, hB1⟩
      · rcases hup with h | h
        · have hcc : c₁ ≠ 0 := by rintro rfl; simp at hB1
          have h' : |b₁ * c₁| ≤ |A * c₁| := by rwa [abs_of_pos hB1]
          have := c3_key_sq b₁ c₁ A hcc h'
          linarith
        · have hdd : d₁ ≠ 0 := by rintro rfl; simp at hA1
          have h' : |a₁ * d₁| ≤ |B * d₁| := by rwa [abs_of_pos hA1]
          have := c3_key_sq a₁ d₁ B hdd h'
          linarith
      · rcases hlo with h | h
        · have hcc : c₁ ≠ 0 := by rintro rfl; simp at hB1
          have h' : |b₁ * c₁| ≤ |A * c₁| := by rw [abs_of_neg hB1]; linarith
          have := c3_key_sq b₁ c₁ A hcc h'
          linarith
        · have hdd : d₁ ≠ 0 := by rintro rfl; simp at hA1
          have h' : |a₁ * d₁| ≤ |B * d₁| := by rw [abs_of_neg hA1]; linarith
          have := c3_key_sq a₁ d₁ B hdd h'
          linarith
  have hP6 : 4 * |a₁ * b₁ * c₁ * d₁| ≤ a₁ ^ 2 + b₁ ^ 2 := by
    have e1 : 2 * |a₁ * b₁| ≤ a₁ ^ 2 + b₁ ^ 2 := by
      rcases abs_cases (a₁ * b₁) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
        nlinarith [sq_nonneg (a₁ - b₁), sq_nonneg (a₁ + b₁)]
    have e2 : 2 * |c₁ * d₁| ≤ 1 := by
      rcases abs_cases (c₁ * d₁) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
        nlinarith [sq_nonneg (c₁ - d₁), sq_nonneg (c₁ + d₁)]
    have e3 : |a₁ * b₁ * c₁ * d₁| = |a₁ * b₁| * |c₁ * d₁| := by rw [← abs_mul]; ring_nf
    rw [e3]
    nlinarith [abs_nonneg (a₁ * b₁), abs_nonneg (c₁ * d₁)]
  have hle : a₁ * b₁ * c₁ * d₁ ≤ |a₁ * b₁ * c₁ * d₁| := le_abs_self _
  rcases hP5 with h | h
  · nlinarith
  · nlinarith [sq_nonneg A, sq_nonneg B]

/-- **C3.** Four unit complex numbers with product `-1` whose imaginary-part sum lies in
`[2 min, 2 max]` of the individual imaginary parts satisfy `|a+b+c+d| ≤ 2√2`.

Equality iff `{λ_k} = {ζ,ζ,η,η}` with `ζ ∈ {1,-1}`, `η ∈ {i,-i}`. -/
theorem c3 (a b c d : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1)
    (hprod : a * b * c * d = -1)
    (hup : (a + b + c + d).im ≤ 2 * max (max a.im b.im) (max c.im d.im))
    (hlo : 2 * min (min a.im b.im) (min c.im d.im) ≤ (a + b + c + d).im) :
    ‖a + b + c + d‖ ≤ 2 * Real.sqrt 2 := by
  obtain ⟨w, hw2, hwn⟩ : ∃ w : ℂ, w ^ 2 = a * b ∧ ‖w‖ = 1 := by
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (a * b) (n := 2) (by norm_num)
    refine ⟨w, hw, ?_⟩
    have h1 : ‖w‖ ^ 2 = 1 := by rw [← norm_pow, hw, norm_mul, ha, hb]; norm_num
    nlinarith [norm_nonneg w]
  obtain ⟨v, hvn, hv2, hvre, hvim⟩ := c3_vexists a b c d w hwn hw2 hprod
  obtain ⟨α, hαn, ha', hb'⟩ := c3_split a b w hwn hw2 ha
  obtain ⟨β, hβn, hc', hd'⟩ := c3_split c d v hvn hv2 hc
  have haim : a.im = w.im * α.re + w.re * α.im := by
    rw [ha']; simp [Complex.mul_im] <;> ring
  have hbim : b.im = w.im * α.re - w.re * α.im := by
    rw [hb']; simp [Complex.mul_im] <;> ring
  have hcim : c.im = w.re * β.re + w.im * β.im := by
    rw [hc']; simp [Complex.mul_im, hvre, hvim] <;> ring
  have hdim : d.im = w.re * β.re - w.im * β.im := by
    rw [hd']; simp [Complex.mul_im, hvre, hvim] <;> ring
  have hare : a.re = w.re * α.re - w.im * α.im := by
    rw [ha']; simp [Complex.mul_re] <;> ring
  have hbre : b.re = w.re * α.re + w.im * α.im := by
    rw [hb']; simp [Complex.mul_re] <;> ring
  have hcre : c.re = w.im * β.re - w.re * β.im := by
    rw [hc']; simp [Complex.mul_re, hvre, hvim] <;> ring
  have hdre : d.re = w.im * β.re + w.re * β.im := by
    rw [hd']; simp [Complex.mul_re, hvre, hvim] <;> ring
  have hSre : (a + b + c + d).re = 2 * (α.re * w.re + β.re * w.im) := by
    simp only [Complex.add_re, hare, hbre, hcre, hdre]; ring
  have hSim : (a + b + c + d).im = 2 * (α.re * w.im + β.re * w.re) := by
    simp only [Complex.add_im, haim, hbim, hcim, hdim]; ring
  have hupd : β.re * w.re ≤ |α.im * w.re| ∨ α.re * w.im ≤ |β.im * w.im| := by
    rw [hSim] at hup
    have h0 : α.re * w.im + β.re * w.re ≤ max (max a.im b.im) (max c.im d.im) := by linarith
    rcases le_max_iff.mp h0 with h1 | h1
    · left
      rcases le_max_iff.mp h1 with h2 | h2
      · rw [haim] at h2; linarith [le_abs_self (α.im * w.re)]
      · rw [hbim] at h2; linarith [neg_le_abs (α.im * w.re)]
    · right
      rcases le_max_iff.mp h1 with h2 | h2
      · rw [hcim] at h2; linarith [le_abs_self (β.im * w.im)]
      · rw [hdim] at h2; linarith [neg_le_abs (β.im * w.im)]
  have hlod : -|α.im * w.re| ≤ β.re * w.re ∨ -|β.im * w.im| ≤ α.re * w.im := by
    rw [hSim] at hlo
    have h0 : min (min a.im b.im) (min c.im d.im) ≤ α.re * w.im + β.re * w.re := by linarith
    rcases min_le_iff.mp h0 with h1 | h1
    · left
      rcases min_le_iff.mp h1 with h2 | h2
      · rw [haim] at h2; linarith [neg_abs_le (α.im * w.re)]
      · rw [hbim] at h2; linarith [le_abs_self (α.im * w.re)]
    · right
      rcases min_le_iff.mp h1 with h2 | h2
      · rw [hcim] at h2; linarith [neg_abs_le (β.im * w.im)]
      · rw [hdim] at h2; linarith [le_abs_self (β.im * w.im)]
  have hJ : α.re ^ 2 + β.re ^ 2 + 4 * (α.re * β.re * w.re * w.im) ≤ 2 :=
    c3_real α.re α.im β.re β.im w.re w.im (c3_unit_sq_sum α hαn) (c3_unit_sq_sum β hβn)
      (c3_unit_sq_sum w hwn) hupd hlod
  have hw1 : w.re ^ 2 + w.im ^ 2 = 1 := c3_unit_sq_sum w hwn
  have hsq : ‖a + b + c + d‖ ^ 2 ≤ 8 := by
    have hns : ‖a + b + c + d‖ ^ 2
        = (a + b + c + d).re ^ 2 + (a + b + c + d).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [hns, hSre, hSim]
    nlinarith [hJ, hw1, sq_nonneg α.re, sq_nonneg β.re]
  have hnn : (0:ℝ) ≤ ‖a + b + c + d‖ := norm_nonneg _
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 2, hnn, hsq, hs2]

end
