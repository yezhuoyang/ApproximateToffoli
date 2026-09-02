/-
  ApproxToffoli.BlockCutHS1

  **`HS1` — the `m = 1` analytic residual of `CutBoundU` — PROVED.**

  `BlockCutU.cutBoundU_one_of_HS1` reduces the `m = 1` case of `CutBoundU` to the
  circuit-free Hilbert–Schmidt inequality

      ‖Tr_C (CCZ8 · (M₀ ⊗ 1) · (1 ⊗ W))‖²_HS ≤ 8 + 4√2      (M₀, W ∈ U(4)).

  This file proves it.  Nothing here needs the crossing to be a CNOT or a CZ, so
  this is exactly the generalisation the tree's `m = 1` core does NOT admit: the
  tree routes `m = 1` through `four_trace_bound_of_refl` / `Key2.key2`, whose
  hypothesis is `IsRefl4 Q` (Hermitian ∧ involutive ∧ traceless).  A general
  two-qubit crossing `V` satisfies none of the three, so that route dies.  The
  route below replaces it and uses only:

  1. `trC_ccz_block`   Θ = M₀X₀ + D M₀X₁,  D = diag(1,1,1,-1),  Xᵢ = 1 ⊗ ωᵢᵢ,
                       with ω_{cc'} the C-blocks of `W`.
  2. `re_trace_theta`  ‖Θ‖²_HS = ‖X₀‖² + ‖X₁‖² + 2 Re Tr(X₀ᴴ R X₁),  R = M₀ᴴ D M₀,
                       from M₀ᴴM₀ = 1, Dᴴ = D, D² = 1.
  3. `trace_R_reduce`  R = 1 - 2P with P = M₀ᴴE₃₃M₀ of rank one; tracing out A
                       collapses the 4×4 cross term to a 2×2 one:
                       Tr(X₀ᴴ R X₁) = 2 Tr(N·K),  N = ω₁₁ω₀₀ᴴ,  K = 1 - Q,
                       Q = the partial trace over A of P.
  4. `hs2_le_two_of_col`  ‖ω₀₀‖²_HS, ‖ω₁₁‖²_HS ≤ 2      (column blocks of `W`)
     `hs2_mul_conjT_le`   ‖N‖²_HS ≤ ‖ω₁₁‖²_HS ≤ 2       (defect ‖ω₁₁ω₁₀ᴴ‖²_HS ≥ 0;
                          this is what replaces `‖ω₀₀‖_op ≤ 1`, so no operator
                          norm and no spectral theorem is needed)
     `hs2_one_sub_Qm_le`  ‖K‖²_HS ≤ 1                   (Q is PSD with Tr Q = 1;
                          the 2×2 content is Cauchy–Schwarz in ℂ², whose Lagrange
                          defect is |m₀m₃ - m₂m₁|²)
     `re_trace_mul_le`    Re Tr(N K) ≤ ‖N‖_HS‖K‖_HS ≤ √2 · 1.

  Total:  ‖Θ‖²_HS ≤ 4 + 4 + 4√2 = 8 + 4√2.  ∎

  Numerics (`scratchpad/hs_chain.py`, Gauss–Seidel with exact nuclear-norm block
  updates): the true maximum of the left-hand side is exactly `12`, against the
  budget `8+4√2 = 13.6568…`, so this chain has genuine slack.  (`HS2`, the `m = 2`
  residual, is by contrast exactly tight at `8+4√2` — see the report.)

  VERIFICATION.  Every declaration below was compiled with `lean_run_code` against
  the built tree in a single run: 0 errors (only `linter.flexible` /
  `linter.unusedSimpArgs` style warnings).
-/

import ApproxToffoli.BlockCutU

open Matrix Complex

noncomputable section

namespace HSBound

/-! ## 0. Definitions -/

/-- Hilbert–Schmidt square norm. -/
def hs2 (A : Mat2) : ℝ := RCLike.re (Matrix.trace (Aᴴ * A))
def hs4 (A : Mat4) : ℝ := RCLike.re (Matrix.trace (Aᴴ * A))

/-- Partial trace over qubit C.  Definitionally `BlockU.trC`. -/
def trC (X : Mat8) : Mat4 :=
  Matrix.of fun x y =>
    X ⟨2 * x.val, by omega⟩ ⟨2 * y.val, by omega⟩
      + X ⟨2 * x.val + 1, by omega⟩ ⟨2 * y.val + 1, by omega⟩

/-- `CCZ8`'s lower C-block, on the AB factor. -/
def D4 : Mat4 := Matrix.diagonal ![1, 1, 1, -1]

/-- `E₃₃`; `D4 = 1 - 2E₃₃`. -/
def Em : Mat4 := !![0,0,0,0; 0,0,0,0; 0,0,0,0; 0,0,0,1]

/-- `M₀ᴴ E₃₃ M₀`, written out on row 3 of `M₀`. -/
def Pm (M0 : Mat4) : Mat4 := Matrix.of fun i j => (starRingEnd ℂ) (M0 3 i) * M0 3 j

/-- The partial trace over qubit A of `Pm M0`: PSD 2×2 of trace 1. -/
def Qm (M0 : Mat4) : Mat2 :=
  !![(starRingEnd ℂ) (M0 3 0) * M0 3 0 + (starRingEnd ℂ) (M0 3 2) * M0 3 2,
       (starRingEnd ℂ) (M0 3 0) * M0 3 1 + (starRingEnd ℂ) (M0 3 2) * M0 3 3;
     (starRingEnd ℂ) (M0 3 1) * M0 3 0 + (starRingEnd ℂ) (M0 3 3) * M0 3 2,
       (starRingEnd ℂ) (M0 3 1) * M0 3 1 + (starRingEnd ℂ) (M0 3 3) * M0 3 3]

/-- The C-blocks of a BC gate: `ω_{cc'}[b][b'] = W[2b+c][2b'+c']`. -/
def wblk (W : Mat4) (c c' : Fin 2) : Mat2 :=
  Matrix.of fun b b' => W ⟨2 * b.val + c.val, by omega⟩ ⟨2 * b'.val + c'.val, by omega⟩

/-! ## 1. Hilbert–Schmidt inner product on `Mat2`

Mathlib has no inner-product instance on `Matrix`; transport along the bijection
with `ℂ^(2×2)`, exactly as `CutBound.matToEuc` does for `Mat4`. -/

def mat2ToEuc (A : Mat2) : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)

lemma inner_mat2ToEuc (A B : Mat2) :
    (inner ℂ (mat2ToEuc A) (mat2ToEuc B) : ℂ) = Matrix.trace (Aᴴ * B) := by
  rw [PiLp.inner_apply]
  simp only [mat2ToEuc, WithLp.ofLp_toLp, RCLike.inner_apply,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp; ring

lemma norm_mat2ToEuc_sq (A : Mat2) : ‖mat2ToEuc A‖ ^ 2 = hs2 A := by
  rw [hs2, ← inner_mat2ToEuc A A, inner_self_eq_norm_sq]

lemma hs2_nonneg (A : Mat2) : 0 ≤ hs2 A := by rw [← norm_mat2ToEuc_sq]; positivity

lemma hs2_conjTranspose (A : Mat2) : hs2 Aᴴ = hs2 A := by
  simp [hs2, Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm A Aᴴ]

/-- **Cauchy–Schwarz in the Hilbert–Schmidt inner product on `Mat2`.** -/
theorem re_trace_mul_le (N K : Mat2) :
    RCLike.re (Matrix.trace (N * K)) ≤ Real.sqrt (hs2 N) * Real.sqrt (hs2 K) := by
  have hi : (inner ℂ (mat2ToEuc Nᴴ) (mat2ToEuc K) : ℂ) = Matrix.trace (N * K) := by
    rw [inner_mat2ToEuc, Matrix.conjTranspose_conjTranspose]
  have h1 : ‖mat2ToEuc Nᴴ‖ = Real.sqrt (hs2 N) := by
    rw [← hs2_conjTranspose N, ← norm_mat2ToEuc_sq, Real.sqrt_sq (norm_nonneg _)]
  have h2 : ‖mat2ToEuc K‖ = Real.sqrt (hs2 K) := by
    rw [← norm_mat2ToEuc_sq, Real.sqrt_sq (norm_nonneg _)]
  have hcs := norm_inner_le_norm (𝕜 := ℂ) (mat2ToEuc Nᴴ) (mat2ToEuc K)
  rw [hi, h1, h2] at hcs
  exact le_trans (Complex.re_le_norm _) hcs

/-- `Tr((ACᴴ)ᴴ(ACᴴ)) = Tr(AᴴA(CᴴC))`: cyclicity. -/
lemma trace_sandwich (A C : Mat2) :
    Matrix.trace ((A * Cᴴ)ᴴ * (A * Cᴴ)) = Matrix.trace (Aᴴ * A * (Cᴴ * C)) := by
  have e : (A * Cᴴ)ᴴ * (A * Cᴴ) = C * (Aᴴ * A * Cᴴ) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm]; congr 1; simp only [Matrix.mul_assoc]

/-- A column block of a unitary has `‖·‖²_HS ≤ 2`. -/
lemma hs2_le_two_of_col {A B : Mat2} (h : Aᴴ * A + Bᴴ * B = 1) : hs2 A ≤ 2 := by
  have hB : 0 ≤ hs2 B := hs2_nonneg B
  have key : hs2 A = 2 - hs2 B := by
    rw [hs2, hs2, eq_sub_of_add_eq h, Matrix.trace_sub, Matrix.trace_one]; simp
  linarith

/-- **`‖A Bᴴ‖²_HS ≤ ‖A‖²_HS`** when `B` is a column block of a unitary; the defect
    is exactly `‖A Gᴴ‖²_HS ≥ 0`.  This is the ONB-free replacement for the operator
    bound `‖B‖_op ≤ 1`. -/
lemma hs2_mul_conjT_le {A B G : Mat2} (h : Bᴴ * B + Gᴴ * G = 1) :
    hs2 (A * Bᴴ) ≤ hs2 A := by
  have hG : 0 ≤ hs2 (A * Gᴴ) := hs2_nonneg _
  have key : hs2 (A * Bᴴ) = hs2 A - hs2 (A * Gᴴ) := by
    rw [hs2, trace_sandwich, eq_sub_of_add_eq h, Matrix.mul_sub, Matrix.mul_one,
      Matrix.trace_sub, hs2, hs2, trace_sandwich]
    simp
  linarith

/-! ## 2. The 2×2 Cauchy–Schwarz core: `‖1 - Q‖²_HS ≤ 1` -/

/-- Cauchy–Schwarz in `ℂ²` in real coordinates; the Lagrange defect is
    `|u₀v₁ - u₁v₀|²`. -/
private lemma cs_two (a b c d e f g h : ℝ) :
    (a*c + b*d + e*g + f*h)^2 + (a*d - b*c + e*h - f*g)^2
      ≤ (a^2+b^2+e^2+f^2) * (c^2+d^2+g^2+h^2) := by
  nlinarith [sq_nonneg (a*g - b*h - e*c + f*d), sq_nonneg (a*h + b*g - e*d - f*c)]

/-- `K = 1 - Q` is PSD with `Tr K = 1`, hence `‖K‖²_HS ≤ (Tr K)² = 1`. -/
lemma hs2_one_sub_Qm_le {M0 : Mat4} (hM0 : IsUnitary4 M0) : hs2 (1 - Qm M0) ≤ 1 := by
  have hMM : M0 * M0ᴴ = 1 := mul_eq_one_comm.mpr hM0
  have h33 : (M0 * M0ᴴ) 3 3 = (1 : Mat4) 3 3 := by rw [hMM]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four,
    Matrix.one_apply_eq, Complex.star_def] at h33
  have hnorm : (M0 3 0).re^2 + (M0 3 0).im^2 + ((M0 3 1).re^2 + (M0 3 1).im^2)
      + ((M0 3 2).re^2 + (M0 3 2).im^2) + ((M0 3 3).re^2 + (M0 3 3).im^2) = 1 := by
    have := congrArg Complex.re h33
    simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.one_re] at this
    nlinarith [this]
  rw [hs2]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_two, Matrix.sub_apply, Qm,
    Matrix.one_apply, Complex.star_def]
  norm_num
  nlinarith [hnorm, cs_two (M0 3 0).re (M0 3 0).im (M0 3 1).re (M0 3 1).im
      (M0 3 2).re (M0 3 2).im (M0 3 3).re (M0 3 3).im]

/-! ## 3. The column-block relations of a BC gate -/

lemma wblk_col0 {W : Mat4} (hW : IsUnitary4 W) :
    (wblk W 0 0)ᴴ * (wblk W 0 0) + (wblk W 1 0)ᴴ * (wblk W 1 0) = 1 := by
  have h : ∀ i j : Fin 4, (Wᴴ * W) i j = (1 : Mat4) i j := by
    intro i j; rw [(hW : Wᴴ * W = 1)]
  have h00 := h 0 0; have h02 := h 0 2; have h20 := h 2 0; have h22 := h 2 2
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four] at h00 h02 h20 h22
  ext b b'
  fin_cases b <;> fin_cases b' <;>
    simp [wblk, Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Matrix.of_apply] <;>
    [linear_combination h00; linear_combination h02; linear_combination h20;
     linear_combination h22]

lemma wblk_col1 {W : Mat4} (hW : IsUnitary4 W) :
    (wblk W 1 1)ᴴ * (wblk W 1 1) + (wblk W 0 1)ᴴ * (wblk W 0 1) = 1 := by
  have h : ∀ i j : Fin 4, (Wᴴ * W) i j = (1 : Mat4) i j := by
    intro i j; rw [(hW : Wᴴ * W = 1)]
  have h11 := h 1 1; have h13 := h 1 3; have h31 := h 3 1; have h33 := h 3 3
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four] at h11 h13 h31 h33
  ext b b'
  fin_cases b <;> fin_cases b' <;>
    simp [wblk, Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Matrix.of_apply] <;>
    [linear_combination h11; linear_combination h13; linear_combination h31;
     linear_combination h33]

/-! ## 4. The 4×4 algebra -/

lemma D4_conjTranspose : (D4 : Mat4)ᴴ = D4 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [D4, Matrix.conjTranspose_apply]

lemma D4_mul_self : (D4 : Mat4) * D4 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [D4, Matrix.mul_apply, Fin.sum_univ_four]

lemma D4_eq : (D4 : Mat4) = 1 - (Em + Em) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [D4, Em]

lemma Pm_eq (M0 : Mat4) : M0ᴴ * Em * M0 = Pm M0 := by
  ext i j
  simp [Pm, Em, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four,
    Matrix.of_apply]

/-- `M₀ᴴ D M₀ = 1 - 2P` with `P = M₀ᴴE₃₃M₀` of rank one. -/
lemma conj_D4 {M0 : Mat4} (hM0 : IsUnitary4 M0) :
    M0ᴴ * D4 * M0 = 1 - (Pm M0 + Pm M0) := by
  have step : M0ᴴ * D4 * M0 = M0ᴴ * M0 - (M0ᴴ * Em * M0 + M0ᴴ * Em * M0) := by
    rw [D4_eq]; noncomm_ring
  rw [step, (hM0 : M0ᴴ * M0 = 1), Pm_eq]

set_option maxHeartbeats 1000000 in
-- 4×4 trace expansion matched against a 2×2 one; exceeds the default budget.
/-- **Tracing out A.** `Tr(P · (1 ⊗ N)) = Tr(N · Q)`. -/
lemma trace_Pm_kron2 (M0 : Mat4) (N : Mat2) :
    Matrix.trace (Pm M0 * kron2 1 N) = Matrix.trace (N * Qm M0) := by
  simp [Pm, Qm, kron2, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.of_apply, Matrix.one_apply, Fin.sum_univ_four, Fin.sum_univ_two]
  ring

lemma hs4_kron2_one (w : Mat2) : hs4 (kron2 1 w) = 2 * hs2 w := by
  rw [hs4, kron2_conjTranspose_mul_kron2, trace_kron2_eq_mul, hs2]
  have h1 : ((1 : Mat2)ᴴ * 1).trace = (2 : ℂ) := by simp
  rw [h1]; simp

lemma trace_kron2_one_mul (w0 w1 : Mat2) :
    Matrix.trace ((kron2 1 w0)ᴴ * kron2 1 w1) = 2 * Matrix.trace (w0ᴴ * w1) := by
  rw [kron2_conjTranspose_mul_kron2, trace_kron2_eq_mul]; simp

lemma kron2_one_mul_conjT (w0 w1 : Mat2) :
    kron2 1 w1 * (kron2 1 w0)ᴴ = kron2 1 (w1 * w0ᴴ) := by
  rw [kron2_conjTranspose, kron2_mul]; simp

lemma trace_X0H_P_X1 (M0 : Mat4) (w0 w1 : Mat2) :
    Matrix.trace ((kron2 1 w0)ᴴ * Pm M0 * kron2 1 w1)
      = Matrix.trace (w1 * w0ᴴ * Qm M0) := by
  have e : (kron2 1 w0)ᴴ * Pm M0 * kron2 1 w1
      = (kron2 1 w0)ᴴ * (Pm M0 * kron2 1 w1) := by simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, kron2_one_mul_conjT, trace_Pm_kron2]

/-- **The cross term, reduced to 2×2.** -/
lemma trace_R_reduce {M0 : Mat4} (hM0 : IsUnitary4 M0) (w0 w1 : Mat2) :
    Matrix.trace ((kron2 1 w0)ᴴ * (M0ᴴ * D4 * M0) * kron2 1 w1)
      = 2 * Matrix.trace (w1 * w0ᴴ * (1 - Qm M0)) := by
  rw [conj_D4 hM0]
  have e : (kron2 1 w0)ᴴ * (1 - (Pm M0 + Pm M0)) * kron2 1 w1
      = (kron2 1 w0)ᴴ * kron2 1 w1
        - ((kron2 1 w0)ᴴ * Pm M0 * kron2 1 w1
          + (kron2 1 w0)ᴴ * Pm M0 * kron2 1 w1) := by noncomm_ring
  rw [e, Matrix.trace_sub, Matrix.trace_add, trace_kron2_one_mul, trace_X0H_P_X1,
    Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_mul_comm w0ᴴ w1]
  ring

lemma re_star (z : ℂ) : RCLike.re (star z) = RCLike.re z := rfl

lemma re_two_mul (z : ℂ) : RCLike.re (2 * z) = 2 * RCLike.re z := by simp

lemma trace_swap_herm {R : Mat4} (hR : Rᴴ = R) (X0 X1 : Mat4) :
    Matrix.trace (X1ᴴ * R * X0) = star (Matrix.trace (X0ᴴ * R * X1)) := by
  rw [← Matrix.trace_conjTranspose]
  congr 1
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hR,
    Matrix.mul_assoc]

lemma theta_expand {M0 : Mat4} (hM0 : IsUnitary4 M0) (X0 X1 : Mat4) :
    (M0 * X0 + D4 * M0 * X1)ᴴ * (M0 * X0 + D4 * M0 * X1)
      = X0ᴴ * X0 + X1ᴴ * X1
        + (X0ᴴ * (M0ᴴ * D4 * M0) * X1 + X1ᴴ * (M0ᴴ * D4 * M0) * X0) := by
  have hu : M0ᴴ * M0 = 1 := hM0
  have step : (M0 * X0 + D4 * M0 * X1)ᴴ * (M0 * X0 + D4 * M0 * X1)
      = X0ᴴ * (M0ᴴ * M0) * X0 + X1ᴴ * (M0ᴴ * (D4 * D4) * M0) * X1
        + (X0ᴴ * (M0ᴴ * D4 * M0) * X1 + X1ᴴ * (M0ᴴ * D4 * M0) * X0) := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, D4_conjTranspose]
    noncomm_ring
  rw [step]
  simp only [hu, D4_mul_self, Matrix.mul_one]

/-- **The Hilbert–Schmidt expansion.** -/
lemma re_trace_theta {M0 : Mat4} (hM0 : IsUnitary4 M0) (X0 X1 : Mat4) :
    hs4 (M0 * X0 + D4 * M0 * X1)
      = hs4 X0 + hs4 X1 + 2 * RCLike.re (Matrix.trace (X0ᴴ * (M0ᴴ * D4 * M0) * X1)) := by
  have hR : (M0ᴴ * D4 * M0)ᴴ = M0ᴴ * D4 * M0 := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      D4_conjTranspose, Matrix.mul_assoc]
  rw [hs4, theta_expand hM0, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
    trace_swap_herm hR, map_add, map_add, map_add, re_star, hs4, hs4]
  ring

/-! ## 5. The block identity -/

set_option maxHeartbeats 4000000 in
-- 64-case `fin_cases × fin_cases` on `Fin 8` through two 8×8 products.
/-- **`Θ = M₀X₀ + D M₀X₁`.** -/
lemma trC_ccz_block (M0 W : Mat4) :
    trC (CCZ8 * kronABC M0 1 * embedBC W)
      = M0 * kron2 1 (wblk W 0 0) + D4 * M0 * kron2 1 (wblk W 1 1) := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [trC, D4, wblk, kronABC, embedBC, CCZ8, kron2, Matrix.mul_apply,
      Matrix.of_apply, Matrix.one_apply, Matrix.diagonal, Fin.sum_univ_eight,
      Fin.sum_univ_four]

/-! ## 6. `HS1` -/

/-- **`HS1`.**  `‖Tr_C (CCZ8 · (M₀ ⊗ 1) · (1 ⊗ W))‖²_HS ≤ 8 + 4√2`. -/
theorem hs1_bound {M0 W : Mat4} (hM0 : IsUnitary4 M0) (hW : IsUnitary4 W) :
    hs4 (trC (CCZ8 * kronABC M0 1 * embedBC W)) ≤ 8 + 4 * Real.sqrt 2 := by
  rw [trC_ccz_block, re_trace_theta hM0, hs4_kron2_one, hs4_kron2_one,
    trace_R_reduce hM0, re_two_mul]
  have hb0 : hs2 (wblk W 0 0) ≤ 2 := hs2_le_two_of_col (wblk_col0 hW)
  have hb1 : hs2 (wblk W 1 1) ≤ 2 := hs2_le_two_of_col (wblk_col1 hW)
  have hN : hs2 (wblk W 1 1 * (wblk W 0 0)ᴴ) ≤ 2 :=
    le_trans (hs2_mul_conjT_le (A := wblk W 1 1) (wblk_col0 hW)) hb1
  have hK : hs2 (1 - Qm M0) ≤ 1 := hs2_one_sub_Qm_le hM0
  have hcs := re_trace_mul_le (wblk W 1 1 * (wblk W 0 0)ᴴ) (1 - Qm M0)
  have s1 : Real.sqrt (hs2 (wblk W 1 1 * (wblk W 0 0)ᴴ)) ≤ Real.sqrt 2 :=
    Real.sqrt_le_sqrt hN
  have s2 : Real.sqrt (hs2 (1 - Qm M0)) ≤ 1 := by
    have h := Real.sqrt_le_sqrt hK; simpa using h
  have hprod : Real.sqrt (hs2 (wblk W 1 1 * (wblk W 0 0)ᴴ)) * Real.sqrt (hs2 (1 - Qm M0))
      ≤ Real.sqrt 2 * 1 :=
    mul_le_mul s1 s2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  linarith

end HSBound

/-! ## 7. Consequences in `BlockU`

`HSBound.trC` and `BlockU.trC` are the same definition, and `BlockU.HSSmall X`
unfolds to `HSBound.hs4 X ≤ 8 + 4√2`, so the bridge is definitional. -/

namespace BlockU

/-- **`HS1` holds.** -/
theorem HS1_holds : HS1 := fun _ _ h1 h2 => HSBound.hs1_bound h1 h2

/-- **`CutBoundU` at `m = 1`, unconditionally.** -/
theorem cutBoundU_one {U : Mat8} (h : BCCutU 1 U) :
    Complex.normSq (Matrix.trace (CCZ8 * U)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2 :=
  cutBoundU_one_of_HS1 HS1_holds h

/-- With `HS1` discharged, `CutBoundU` — and hence `Block.PhiFive`, and hence the
    `n = 6, 7` dichotomy — rests on `HS2` ALONE. -/
theorem cutBoundU_of_HS2 (h2 : HS2) : CutBoundU := cutBoundU_of_hs HS1_holds h2

theorem phiFive_of_HS2 (h2 : HS2) :
    ∀ U : Mat8, UnitaryNeighborCircuit 5 U →
      Complex.normSq (Matrix.trace (Uᴴ * CCX)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2 :=
  phiFive_of_hs HS1_holds h2

end BlockU

end
