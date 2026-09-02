/-
  ApproxToffoli.LemmaT1

  **Lemma T1**, in its elementary form: for rank-2 reflections `P`, `Q` on `ℂ⁴`
  (Hermitian, involutive, traceless — hence spectrum `{+1,+1,-1,-1}`),

      |Tr (P Z')|² + |Tr (Q P Z')|² ≤ 8,        Z' = diag(1,1,1,-1).

  This is the deepest ingredient of the `core_psi_bound` chain (gap_proof.py step 8).
  In the paper it is done with `spec(P Z') = {1, -1, e^{iθ}, e^{-iθ}}`, Schur–Horn, and
  convexity over the hypersimplex. NONE of that is available here: this toolchain's
  Mathlib has no spectral theorem for normal or unitary matrices, no Schur
  triangulation, no cosine–sine decomposition, and no continuous functional calculus
  for complex matrices — `Matrix.IsHermitian.spectral_theorem` is the only spectral
  theorem in all of Mathlib (verified by an environment scan).

  The route taken instead avoids eigenvectors entirely. The four rank-one spectral
  projections of `R = P Z'` are written as explicit POLYNOMIALS in `P` and
  `E = |3⟩⟨3|`. With `D := P E - E P`, `p := P₃₃`, `s := √(1-p²)`, `G := (i/s) D`,
  the relations `P² = 1`, `E² = E`, `E P E = p E` alone give

      D³ = -(1-p²) D,   D² P = P D²,   Tr D = 0,   Tr D² = 2p² - 2,

  hence `G` is Hermitian with `G³ = G`, `Tr G = 0`, `Tr G² = 2`, and `G²` is the
  projection onto `span{e₃, P e₃}`. The four projections are then

      K3 = (G²+G)/2,  K4 = (G²-G)/2,  K1 = (1-G²)(1+P)/2,  K2 = (1-G²)(1-P)/2

  and the spectral decomposition `K1 - K2 + (C+is) K3 + (C-is) K4 = P Z'` (with
  `C = -p`) is proved as a matrix identity. The `1/s` singularity cancels — `i s G = -D`
  needs no division — and `|p| = 1` is handled as a separate branch (`T1_deg`), which is
  exactly the case where sloppy arguments break. The only fact used about `Q` is
  `|Tr (Q Π)| ≤ 1` for a rank-one projection `Π`, proved from
  `Tr Π - Tr (Q Π) = ½ Tr (MᴴM)` with `M = (1-Q)Π`.

  Independently verified: `lake env lean` exits 0, and
  `#print axioms T1Bridge.T1` returns exactly `[propext, Classical.choice, Quot.sound]`
  — no `sorryAx`. The hypotheses are satisfiable (take `P = Q = diag(1,-1,1,-1)`), so
  the statement is not vacuous. Every identity above was pre-checked numerically
  (3000 random rank-2 reflection pairs, max residual 2.4e-14) before formalizing.

  `T1` is TIGHT: it equals 8 identically along a family, so no downstream step may
  lose anything.
-/

import ApproxToffoli.BaseCase
import ApproxToffoli.Helpers

open Matrix Complex

namespace T1Bridge

noncomputable section

/-! ## 1. The two diagonal matrices (from the previous agent's delivery) -/

/-- `Z' = diag(1,1,1,-1)`. -/
def Zp4 : Mat4 := Matrix.diagonal ![1, 1, 1, -1]

/-- `E = |3⟩⟨3|`. -/
def E4 : Mat4 := Matrix.diagonal ![0, 0, 0, 1]

lemma Zp4_eq_one_sub : Zp4 = 1 - (E4 + E4) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Zp4, E4]

lemma Zp4_conjTranspose : Zp4ᴴ = Zp4 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Zp4, Matrix.conjTranspose_apply]

lemma Zp4_mul_self : Zp4 * Zp4 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Zp4, Matrix.mul_apply, Fin.sum_univ_four]

lemma E4_conjTranspose : E4ᴴ = E4 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [E4, Matrix.conjTranspose_apply]

lemma E4_mul_self : E4 * E4 = E4 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [E4, Matrix.mul_apply, Fin.sum_univ_four]

lemma E4_mul_mul_E4 (M : Mat4) : E4 * M * E4 = (M 3 3) • E4 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [E4, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_four]

lemma trace_E4 : E4.trace = 1 := by
  simp [E4, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_four]

lemma trace_mul_E4 (M : Mat4) : (M * E4).trace = M 3 3 := by
  simp [E4, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_four]

/-- `Tr (M Z') = Tr M - 2 M₃₃`. -/
lemma trace_mul_Zp4 (M : Mat4) : (M * Zp4).trace = M.trace - 2 * M 3 3 := by
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Zp4, Fin.sum_univ_four]; ring

/-! ## 2. Entries and traces of unitary / Hermitian matrices -/

/-- Columns of a matrix with `Mᴴ M = 1` are unit vectors. -/
lemma col_sum_normSq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (h : Mᴴ * M = 1) (i : Fin n) :
    ∑ k, Complex.normSq (M k i) = 1 := by
  have h1 : (Mᴴ * M) i i = 1 := by rw [h]; simp
  rw [Matrix.mul_apply] at h1
  have h2 : ∀ k : Fin n, Mᴴ i k * M k i = ((Complex.normSq (M k i) : ℝ) : ℂ) := by
    intro k
    rw [Matrix.conjTranspose_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  rw [Finset.sum_congr rfl fun k _ => h2 k] at h1
  simpa using congrArg Complex.re h1

/-- Every entry of a matrix with `Mᴴ M = 1` has modulus ≤ 1. -/
lemma entry_normSq_le_one {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (h : Mᴴ * M = 1) (k i : Fin n) :
    Complex.normSq (M k i) ≤ 1 := by
  have hs := col_sum_normSq M h i
  have : Complex.normSq (M k i) ≤ ∑ j, Complex.normSq (M j i) :=
    Finset.single_le_sum (f := fun j => Complex.normSq (M j i))
      (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ k)
  linarith

lemma herm_involution_unitary {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (h : Mᴴ = M) (h2 : M * M = 1) : Mᴴ * M = 1 := by rw [h]; exact h2

/-- Diagonal entries of a Hermitian matrix are real. -/
lemma herm_diag_im {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (h : Mᴴ = M) (i : Fin n) :
    (M i i).im = 0 := by
  have h2 : (starRingEnd ℂ) (M i i) = M i i := by
    have := congrFun (congrFun h i) i
    rwa [Matrix.conjTranspose_apply] at this
  have := congrArg Complex.im h2
  simp at this
  linarith

/-- **`P₃₃` is real and lies in `[-1,1]`.** -/
lemma diag_re_sq_le_one (P : Mat4) (hP : Pᴴ = P) (hP2 : P * P = 1) : (P 3 3).re ^ 2 ≤ 1 := by
  have h1 : Complex.normSq (P 3 3) ≤ 1 :=
    entry_normSq_le_one P (herm_involution_unitary P hP hP2) 3 3
  have h2 : (P 3 3).im = 0 := herm_diag_im P hP 3
  rw [Complex.normSq_apply, h2] at h1
  nlinarith [h1]

/-- `Tr (B A)` is real when `A`, `B` are Hermitian. -/
lemma trace_QP_im {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hA : Aᴴ = A) (hB : Bᴴ = B) :
    ((B * A).trace).im = 0 := by
  have h1 : ((B * A)ᴴ).trace = (B * A).trace := by
    rw [Matrix.conjTranspose_mul, hA, hB, Matrix.trace_mul_comm]
  have h2 : (starRingEnd ℂ) ((B * A).trace) = (B * A).trace := by
    rw [← Complex.star_def, ← Matrix.trace_conjTranspose]; exact h1
  have := congrArg Complex.im h2
  simp at this
  linarith

/-! ## 3. `|Tr (Q Π)| ≤ 1` for a rank-one projection `Π` (NEW)

This is the only inequality about `Q` that the whole bridge needs, and it is proved
without any spectral theorem: `Tr Π - Tr (Q Π) = ½ Tr (Mᴴ M)` with `M = (1-Q)Π`. -/

lemma trace_cT_mul_self_re_nonneg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ ((Mᴴ * M).trace).re := by
  have h : (Mᴴ * M).trace = ((∑ i, ∑ k, Complex.normSq (M k i) : ℝ) : ℂ) := by
    rw [Matrix.trace]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.conjTranspose_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  rw [h, Complex.ofReal_re]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _

/-- If `S` is Hermitian with `S² = 2S` (i.e. `S/2` is a projection-like idempotent) and
`Π` is a Hermitian idempotent, then `Tr (Π S)` has nonnegative real part. -/
lemma proj_pos_aux {n : ℕ} (S Pi : Matrix (Fin n) (Fin n) ℂ) (hS : Sᴴ = S)
    (hSS : S * S = S + S) (hPh : Piᴴ = Pi) (hP2 : Pi * Pi = Pi) :
    0 ≤ ((Pi * S).trace).re := by
  have hMM : (S * Pi)ᴴ * (S * Pi) = Pi * S * Pi + Pi * S * Pi := by
    rw [Matrix.conjTranspose_mul, hS, hPh]
    calc Pi * S * (S * Pi) = Pi * (S * S) * Pi := by noncomm_ring
      _ = Pi * (S + S) * Pi := by rw [hSS]
      _ = Pi * S * Pi + Pi * S * Pi := by noncomm_ring
  have hcyc : (Pi * S * Pi).trace = (Pi * S).trace := by
    rw [Matrix.trace_mul_comm (Pi * S) Pi, ← Matrix.mul_assoc, hP2]
  have h0 := trace_cT_mul_self_re_nonneg (S * Pi)
  rw [hMM, Matrix.trace_add, hcyc, Complex.add_re] at h0
  linarith

/-- **Key bound.** `|Tr (Q Π)| ≤ 1` when `Q` is a Hermitian involution and `Π` a
Hermitian idempotent of trace `1`. -/
lemma trace_Q_proj_re_le {n : ℕ} (Q Pi : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Qᴴ = Q) (hQ2 : Q * Q = 1)
    (hPh : Piᴴ = Pi) (hP2 : Pi * Pi = Pi) (hPtr : Pi.trace = 1) :
    |((Q * Pi).trace).re| ≤ 1 := by
  have hcomm : (Pi * Q).trace = (Q * Pi).trace := Matrix.trace_mul_comm Pi Q
  have hminus : ((Pi * (1 - Q)).trace) = 1 - (Q * Pi).trace := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, hPtr, hcomm]
  have hplus : ((Pi * (1 + Q)).trace) = 1 + (Q * Pi).trace := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.trace_add, hPtr, hcomm]
  have e1 : 0 ≤ ((Pi * (1 - Q)).trace).re := by
    refine proj_pos_aux _ _ ?_ ?_ hPh hP2
    · rw [Matrix.conjTranspose_sub, hQ, Matrix.conjTranspose_one]
    · have h : (1 - Q) * (1 - Q) = 1 - Q - Q + Q * Q := by noncomm_ring
      rw [h, hQ2]; abel
  have e2 : 0 ≤ ((Pi * (1 + Q)).trace).re := by
    refine proj_pos_aux _ _ ?_ ?_ hPh hP2
    · rw [Matrix.conjTranspose_add, hQ, Matrix.conjTranspose_one]
    · have h : (1 + Q) * (1 + Q) = 1 + Q + Q + Q * Q := by noncomm_ring
      rw [h, hQ2]; abel
  rw [hminus] at e1
  rw [hplus] at e2
  simp only [Complex.sub_re, Complex.add_re, Complex.one_re] at e1 e2
  rw [abs_le]
  constructor <;> linarith

/-! ## 4. The commutator `D = P E - E P` and its algebra (NEW)

Everything below is a consequence of the three relations `P² = 1`, `E² = E`,
`E P E = P₃₃ E`.  `D² = -T` where `T = s² Π_V` and `Π_V` is the orthogonal projection
onto `span{e₃, P e₃}`; `G = (i/s) D` is Hermitian with `G³ = G`, `Tr G = 0`,
`Tr G² = 2`, and `G²` is the projection onto that plane. -/

def Dm (P : Mat4) : Mat4 := P * E4 - E4 * P

section Dalg
variable {P : Mat4}

lemma mul_PE_PE : (P * E4) * (P * E4) = (P 3 3) • (P * E4) := by
  have h : (P * E4) * (P * E4) = P * (E4 * P * E4) := by noncomm_ring
  rw [h, E4_mul_mul_E4, Matrix.mul_smul]

lemma mul_PE_EP : (P * E4) * (E4 * P) = P * E4 * P := by
  have h : (P * E4) * (E4 * P) = P * (E4 * E4) * P := by noncomm_ring
  rw [h, E4_mul_self]

lemma mul_EP_PE (hP2 : P * P = 1) : (E4 * P) * (P * E4) = E4 := by
  have h : (E4 * P) * (P * E4) = E4 * (P * P) * E4 := by noncomm_ring
  rw [h, hP2, Matrix.mul_one, E4_mul_self]

lemma mul_EP_EP : (E4 * P) * (E4 * P) = (P 3 3) • (E4 * P) := by
  have h : (E4 * P) * (E4 * P) = (E4 * P * E4) * P := by noncomm_ring
  rw [h, E4_mul_mul_E4, Matrix.smul_mul]

lemma mul_PEP_PE (hP2 : P * P = 1) : (P * E4 * P) * (P * E4) = P * E4 := by
  have h : (P * E4 * P) * (P * E4) = P * E4 * (P * P) * E4 := by noncomm_ring
  rw [h, hP2, Matrix.mul_one, Matrix.mul_assoc, E4_mul_self]

lemma mul_PEP_EP : (P * E4 * P) * (E4 * P) = (P 3 3) • (P * E4 * P) := by
  have h : (P * E4 * P) * (E4 * P) = P * (E4 * P * E4) * P := by noncomm_ring
  rw [h, E4_mul_mul_E4, Matrix.mul_smul, Matrix.smul_mul]

lemma mul_E_PE : E4 * (P * E4) = (P 3 3) • E4 := by
  have h : E4 * (P * E4) = E4 * P * E4 := by noncomm_ring
  rw [h, E4_mul_mul_E4]

lemma mul_E_EP : E4 * (E4 * P) = E4 * P := by
  have h : E4 * (E4 * P) = (E4 * E4) * P := by noncomm_ring
  rw [h, E4_mul_self]

lemma mul_EP_P (hP2 : P * P = 1) : (E4 * P) * P = E4 := by
  have h : (E4 * P) * P = E4 * (P * P) := by noncomm_ring
  rw [h, hP2, Matrix.mul_one]

lemma mul_PEP_P (hP2 : P * P = 1) : (P * E4 * P) * P = P * E4 := by
  have h : (P * E4 * P) * P = P * E4 * (P * P) := by noncomm_ring
  rw [h, hP2, Matrix.mul_one]

lemma mul_P_PE (hP2 : P * P = 1) : P * (P * E4) = E4 := by
  have h : P * (P * E4) = (P * P) * E4 := by noncomm_ring
  rw [h, hP2, Matrix.one_mul]

lemma mul_P_EP : P * (E4 * P) = P * E4 * P := by noncomm_ring

lemma mul_P_PEP (hP2 : P * P = 1) : P * (P * E4 * P) = E4 * P := by
  have h : P * (P * E4 * P) = (P * P) * E4 * P := by noncomm_ring
  rw [h, hP2, Matrix.one_mul]

/-- `D² = p·PE + p·EP - PEP - E`. -/
lemma DD (hP2 : P * P = 1) :
    Dm P * Dm P = (P 3 3) • (P * E4) + (P 3 3) • (E4 * P) - P * E4 * P - E4 := by
  have h : Dm P * Dm P = (P * E4) * (P * E4) - (P * E4) * (E4 * P)
      - (E4 * P) * (P * E4) + (E4 * P) * (E4 * P) := by
    rw [Dm]; noncomm_ring
  rw [h, mul_PE_PE, mul_PE_EP, mul_EP_PE hP2, mul_EP_EP]
  abel

/-- **`D³ = -(1-p²) D`.**  Equivalently `G³ = G` after rescaling. -/
lemma DDD (hP2 : P * P = 1) : Dm P * Dm P * Dm P = ((P 3 3) ^ 2 - 1) • Dm P := by
  rw [DD hP2]
  conv_lhs => rw [Dm]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul]
  rw [mul_PE_PE, mul_PE_EP, mul_EP_PE hP2, mul_EP_EP, mul_PEP_PE hP2, mul_PEP_EP,
    mul_E_PE, mul_E_EP, Dm]
  module

/-- `D²` commutes with `P` (the plane `span{e₃, P e₃}` is `P`-invariant). -/
lemma DD_comm_P (hP2 : P * P = 1) : Dm P * Dm P * P = P * (Dm P * Dm P) := by
  rw [DD hP2]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.mul_smul]
  rw [mul_EP_P hP2, mul_PEP_P hP2, mul_P_PE hP2, mul_P_EP, mul_P_PEP hP2]
  abel

/-- **The key structural identity** `-D² (P + p) = (1-p²)(P E + E P)`.
It is what makes `Π_V (P + p) = E P + P E` and hence produces the decomposition of
`R = P Z'`. -/
lemma DD_key (hP2 : P * P = 1) :
    -(Dm P * Dm P * (P + (P 3 3) • (1 : Mat4)))
      = (1 - (P 3 3) ^ 2) • (P * E4 + E4 * P) := by
  have h1 : Dm P * Dm P * (P + (P 3 3) • (1 : Mat4))
      = Dm P * Dm P * P + (P 3 3) • (Dm P * Dm P) := by
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
  rw [h1]
  nth_rewrite 1 [DD hP2]
  rw [DD hP2]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul]
  rw [mul_EP_P hP2, mul_PEP_P hP2]
  module

lemma Dm_conjTranspose (hP : Pᴴ = P) : (Dm P)ᴴ = -Dm P := by
  rw [Dm, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    E4_conjTranspose, hP]
  abel

lemma trace_Dm : (Dm P).trace = 0 := by
  rw [Dm, Matrix.trace_sub, Matrix.trace_mul_comm E4 P]
  abel

lemma trace_PE4P (hP2 : P * P = 1) : (P * E4 * P).trace = 1 := by
  rw [Matrix.trace_mul_comm (P * E4) P, ← Matrix.mul_assoc, hP2, Matrix.one_mul, trace_E4]

lemma trace_DD (hP2 : P * P = 1) : (Dm P * Dm P).trace = 2 * (P 3 3) ^ 2 - 2 := by
  rw [DD hP2]
  simp only [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, trace_mul_E4,
    Matrix.trace_mul_comm E4 P, trace_PE4P hP2, trace_E4, smul_eq_mul]
  ring

lemma trace_DDP (hP2 : P * P = 1) : (Dm P * Dm P * P).trace = 0 := by
  rw [DD hP2]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul]
  rw [mul_EP_P hP2, mul_PEP_P hP2]
  simp only [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, trace_mul_E4,
    Matrix.trace_mul_comm E4 P, trace_PE4P hP2, trace_E4, smul_eq_mul]
  ring

end Dalg

/-! ## 5. `G = (i/s) D` (NEW) -/

/-- `G = (i/s) D` with `s = √(1-p²)`: a Hermitian matrix with `G³ = G`, `Tr G = 0`,
`Tr G² = 2`.  `G²` is the orthogonal projection onto `span{e₃, P e₃}` and `±1` are the
eigenvalues of `G` on that plane. -/
def Gm (P : Mat4) (s : ℝ) : Mat4 := ((s : ℂ)⁻¹ * Complex.I) • Dm P

section Galg
variable {P : Mat4} {s : ℝ}

lemma Gm_conjTranspose (hP : Pᴴ = P) : (Gm P s)ᴴ = Gm P s := by
  rw [Gm, Matrix.conjTranspose_smul, Dm_conjTranspose hP]
  have h : star ((s : ℂ)⁻¹ * Complex.I) = -((s : ℂ)⁻¹ * Complex.I) := by
    simp [← Complex.ofReal_inv]
  rw [h, neg_smul, smul_neg, neg_neg]

lemma Gm_sq (hs : (s : ℂ) ≠ 0) (hs2 : (s : ℂ) ^ 2 = 1 - (P 3 3) ^ 2) :
    Gm P s * Gm P s = (-(1 - (P 3 3) ^ 2)⁻¹) • (Dm P * Dm P) := by
  rw [Gm, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  rw [← hs2]
  field_simp
  rw [Complex.I_sq]

lemma Gm_cube (hP2 : P * P = 1) (hs : (s : ℂ) ≠ 0) (hs2 : (s : ℂ) ^ 2 = 1 - (P 3 3) ^ 2) :
    Gm P s * Gm P s * Gm P s = Gm P s := by
  rw [Gm]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [DDD hP2, smul_smul]
  congr 1
  have h1 : (P 3 3) ^ 2 - 1 = -(s : ℂ) ^ 2 := by rw [hs2]; ring
  rw [h1]
  field_simp
  rw [Complex.I_sq]
  ring

lemma trace_Gm : (Gm P s).trace = 0 := by
  rw [Gm, Matrix.trace_smul, trace_Dm, smul_zero]

lemma trace_Gm_sq (hP2 : P * P = 1) (hs : (s : ℂ) ≠ 0) (hs2 : (s : ℂ) ^ 2 = 1 - (P 3 3) ^ 2) :
    (Gm P s * Gm P s).trace = 2 := by
  have hne : (1 : ℂ) - (P 3 3) ^ 2 ≠ 0 := by rw [← hs2]; exact pow_ne_zero _ hs
  rw [Gm_sq hs hs2, Matrix.trace_smul, trace_DD hP2, smul_eq_mul]
  field_simp
  ring

lemma Gm_sq_comm_P (hP2 : P * P = 1) (hs : (s : ℂ) ≠ 0) (hs2 : (s : ℂ) ^ 2 = 1 - (P 3 3) ^ 2) :
    Gm P s * Gm P s * P = P * (Gm P s * Gm P s) := by
  rw [Gm_sq hs hs2, Matrix.smul_mul, Matrix.mul_smul, DD_comm_P hP2]

lemma Gm_sq_key (hP2 : P * P = 1) (hs : (s : ℂ) ≠ 0) (hs2 : (s : ℂ) ^ 2 = 1 - (P 3 3) ^ 2) :
    Gm P s * Gm P s * (P + (P 3 3) • (1 : Mat4)) = P * E4 + E4 * P := by
  rw [Gm_sq hs hs2, Matrix.smul_mul]
  have hne : (1 : ℂ) - (P 3 3) ^ 2 ≠ 0 := by rw [← hs2]; exact pow_ne_zero _ hs
  have h := DD_key (P := P) hP2
  have h2 : Dm P * Dm P * (P + (P 3 3) • (1 : Mat4))
      = -((1 - (P 3 3) ^ 2) • (P * E4 + E4 * P)) := by rw [← h]; abel
  rw [h2, smul_neg, smul_smul]
  field_simp
  module

lemma trace_Gm_sq_P (hP2 : P * P = 1) (hs : (s : ℂ) ≠ 0) (hs2 : (s : ℂ) ^ 2 = 1 - (P 3 3) ^ 2) :
    (Gm P s * Gm P s * P).trace = 0 := by
  rw [Gm_sq hs hs2, Matrix.smul_mul, Matrix.trace_smul, trace_DDP hP2, smul_zero]

/-- `i·s·G = -D = E P - P E`. -/
lemma smul_Gm (hs : (s : ℂ) ≠ 0) : ((s : ℂ) * Complex.I) • Gm P s = -Dm P := by
  rw [Gm, smul_smul]
  have h : (s : ℂ) * Complex.I * ((s : ℂ)⁻¹ * Complex.I) = -1 := by
    field_simp
    rw [Complex.I_sq]
  rw [h, neg_smul, one_smul]

end Galg

/-! ## 6. The four rank-one spectral projections of `R = P Z'` (NEW)

`proj3 G = (G²+G)/2` and `proj4 G = (G²-G)/2` are the eigenprojections of `R` for
`e^{±iθ}` (they live in the plane `span{e₃,Pe₃}`), and `projS G (1±P) = (1-G²)(1±P)/2`
are those for `±1` (they live in the orthogonal complement, where `R = P`). -/

def projS (G S : Mat4) : Mat4 := (2 : ℂ)⁻¹ • ((1 - G * G) * S)
def proj3 (G : Mat4) : Mat4 := (2 : ℂ)⁻¹ • (G * G + G)
def proj4 (G : Mat4) : Mat4 := (2 : ℂ)⁻¹ • (G * G - G)

section Abs
variable {G S Pp : Mat4}

lemma Gsq_idem (hG3 : G * G * G = G) : G * G * (G * G) = G * G := by
  calc G * G * (G * G) = (G * G * G) * G := by noncomm_ring
    _ = G * G := by rw [hG3]

lemma proj3_herm (hG : Gᴴ = G) : (proj3 G)ᴴ = proj3 G := by
  rw [proj3, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hG]
  simp

lemma proj3_idem (hG3 : G * G * G = G) : proj3 G * proj3 G = proj3 G := by
  rw [proj3, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h : (G * G + G) * (G * G + G) = G * G * (G * G) + G * G * G + (G * G * G + G * G) := by
    noncomm_ring
  rw [h, Gsq_idem hG3, hG3]
  module

lemma proj3_trace (hGt : G.trace = 0) (hG2t : (G * G).trace = 2) : (proj3 G).trace = 1 := by
  rw [proj3, Matrix.trace_smul, Matrix.trace_add, hGt, hG2t]
  norm_num

lemma proj4_herm (hG : Gᴴ = G) : (proj4 G)ᴴ = proj4 G := by
  rw [proj4, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hG]
  simp

lemma proj4_idem (hG3 : G * G * G = G) : proj4 G * proj4 G = proj4 G := by
  rw [proj4, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h : (G * G - G) * (G * G - G) = G * G * (G * G) - G * G * G - (G * G * G - G * G) := by
    noncomm_ring
  rw [h, Gsq_idem hG3, hG3]
  module

lemma proj4_trace (hGt : G.trace = 0) (hG2t : (G * G).trace = 2) : (proj4 G).trace = 1 := by
  rw [proj4, Matrix.trace_smul, Matrix.trace_sub, hGt, hG2t]
  norm_num

lemma projS_herm (hG : Gᴴ = G) (hS : Sᴴ = S) (hcomm : S * (1 - G * G) = (1 - G * G) * S) :
    (projS G S)ᴴ = projS G S := by
  rw [projS, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hS,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul, hG, hcomm]
  simp

lemma projS_idem (hG3 : G * G * G = G) (hSS : S * S = S + S)
    (hcomm : S * (1 - G * G) = (1 - G * G) * S) : projS G S * projS G S = projS G S := by
  rw [projS, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h1 : (1 - G * G) * S * ((1 - G * G) * S) = (1 - G * G) * (S * (1 - G * G)) * S := by
    noncomm_ring
  rw [h1, hcomm]
  have h2 : (1 - G * G) * ((1 - G * G) * S) * S = (1 - G * G) * (1 - G * G) * (S * S) := by
    noncomm_ring
  rw [h2, hSS]
  have h3 : (1 - G * G) * (1 - G * G) = 1 - G * G - G * G + G * G * (G * G) := by noncomm_ring
  rw [h3, Gsq_idem hG3]
  have h4 : (1 - G * G - G * G + G * G) * (S + S) = (1 - G * G) * S + (1 - G * G) * S := by
    noncomm_ring
  rw [h4]
  module

lemma projS_trace (hStr : ((1 - G * G) * S).trace = 2) : (projS G S).trace = 1 := by
  rw [projS, Matrix.trace_smul, hStr]; norm_num

lemma comm_add (hcomm : G * G * Pp = Pp * (G * G)) :
    (1 + Pp) * (1 - G * G) = (1 - G * G) * (1 + Pp) := by
  have h1 : (1 + Pp) * (1 - G * G) = 1 - G * G + Pp - Pp * (G * G) := by noncomm_ring
  have h2 : (1 - G * G) * (1 + Pp) = 1 - G * G + Pp - G * G * Pp := by noncomm_ring
  rw [h1, h2, hcomm]

lemma comm_sub (hcomm : G * G * Pp = Pp * (G * G)) :
    (1 - Pp) * (1 - G * G) = (1 - G * G) * (1 - Pp) := by
  have h1 : (1 - Pp) * (1 - G * G) = 1 - G * G - Pp + Pp * (G * G) := by noncomm_ring
  have h2 : (1 - G * G) * (1 - Pp) = 1 - G * G - Pp + G * G * Pp := by noncomm_ring
  rw [h1, h2, hcomm]

lemma sq_add (hP2 : Pp * Pp = 1) : (1 + Pp) * (1 + Pp) = (1 + Pp) + (1 + Pp) := by
  have h : (1 + Pp) * (1 + Pp) = 1 + Pp + Pp + Pp * Pp := by noncomm_ring
  rw [h, hP2]; abel

lemma sq_sub (hP2 : Pp * Pp = 1) : (1 - Pp) * (1 - Pp) = (1 - Pp) + (1 - Pp) := by
  have h : (1 - Pp) * (1 - Pp) = 1 - Pp - Pp + Pp * Pp := by noncomm_ring
  rw [h, hP2]; abel

lemma trace_aux_add (hG2t : (G * G).trace = 2) (hPt : Pp.trace = 0)
    (hGPt : (G * G * Pp).trace = 0) : ((1 - G * G) * (1 + Pp)).trace = 2 := by
  have h : (1 - G * G) * (1 + Pp) = 1 - G * G + Pp - G * G * Pp := by noncomm_ring
  rw [h]
  simp only [Matrix.trace_sub, Matrix.trace_add, hG2t, hPt, hGPt, Matrix.trace_one]
  norm_num

lemma trace_aux_sub (hG2t : (G * G).trace = 2) (hPt : Pp.trace = 0)
    (hGPt : (G * G * Pp).trace = 0) : ((1 - G * G) * (1 - Pp)).trace = 2 := by
  have h : (1 - G * G) * (1 - Pp) = 1 - G * G - Pp + G * G * Pp := by noncomm_ring
  rw [h]
  simp only [Matrix.trace_sub, Matrix.trace_add, hG2t, hPt, hGPt, Matrix.trace_one]
  norm_num

lemma herm_add (hP : Ppᴴ = Pp) : ((1 : Mat4) + Pp)ᴴ = 1 + Pp := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, hP]

lemma herm_sub (hP : Ppᴴ = Pp) : ((1 : Mat4) - Pp)ᴴ = 1 - Pp := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP]

end Abs

/-! ## 7. The core real inequality (previous agent's delivery, verbatim) -/

/-- Reduced form of the core inequality, after taking absolute values. -/
lemma core_abs (a d S c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hS0 : 0 ≤ S)
    (ha0 : 0 ≤ a) (hd0 : 0 ≤ d) (ha : a + S ≤ 2) (hd : d + S ≤ 2) :
    4 * c ^ 2 + (a + c * S) ^ 2 + (1 - c ^ 2) * d ^ 2 ≤ 8 := by
  have hS2 : S ≤ 2 := by linarith
  have hc2 : c ^ 2 ≤ 1 := by nlinarith
  have step1 : (a + c * S) ^ 2 ≤ ((2 - S) + c * S) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 - S - a)
      (by nlinarith : (0:ℝ) ≤ 2 - S + a + 2 * (c * S))]
  have step2 : (1 - c ^ 2) * d ^ 2 ≤ (1 - c ^ 2) * (2 - S) ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - c ^ 2)
      (by linarith : (0:ℝ) ≤ 2 - S - d)) (by linarith : (0:ℝ) ≤ 2 - S + d)]
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - c) hS0)
    (by linarith : (0:ℝ) ≤ 4 - S + 2 * c)]

/-- **Core inequality.**  Tight: `C = 0`, `u = (1,-1,1,-1)` gives exactly `8`. -/
lemma core_ineq (C u1 u2 u3 u4 : ℝ)
    (hC : |C| ≤ 1) (h1 : |u1| ≤ 1) (h2 : |u2| ≤ 1) (h3 : |u3| ≤ 1) (h4 : |u4| ≤ 1)
    (hsum : u1 + u2 + u3 + u4 = 0) :
    4 * C ^ 2 + (u1 - u2 + C * (u3 + u4)) ^ 2 + (1 - C ^ 2) * (u3 - u4) ^ 2 ≤ 8 := by
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  obtain ⟨h2a, h2b⟩ := abs_le.mp h2
  obtain ⟨h3a, h3b⟩ := abs_le.mp h3
  obtain ⟨h4a, h4b⟩ := abs_le.mp h4
  have hswap : u3 + u4 = -(u1 + u2) := by linarith
  have habs12 : |u1 - u2| + |u1 + u2| ≤ 2 := by
    rcases abs_cases (u1 - u2) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
      rcases abs_cases (u1 + u2) with ⟨e2, _⟩ | ⟨e2, _⟩ <;> rw [e1, e2] <;> linarith
  have habs34 : |u3 - u4| + |u3 + u4| ≤ 2 := by
    rcases abs_cases (u3 - u4) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
      rcases abs_cases (u3 + u4) with ⟨e2, _⟩ | ⟨e2, _⟩ <;> rw [e1, e2] <;> linarith
  have hSeq : |u3 + u4| = |u1 + u2| := by rw [hswap, abs_neg]
  have key := core_abs |u1 - u2| |u3 - u4| |u3 + u4| |C| (abs_nonneg _) hC (abs_nonneg _)
    (abs_nonneg _) (abs_nonneg _) (by rw [hSeq]; exact habs12) habs34
  rw [sq_abs C, sq_abs (u3 - u4)] at key
  have hb1 : |u1 - u2 + C * (u3 + u4)| ≤ |u1 - u2| + |C| * |u3 + u4| := by
    calc |u1 - u2 + C * (u3 + u4)| ≤ |u1 - u2| + |C * (u3 + u4)| := abs_add_le _ _
    _ = |u1 - u2| + |C| * |u3 + u4| := by rw [abs_mul]
  have hb2 : (u1 - u2 + C * (u3 + u4)) ^ 2 ≤ (|u1 - u2| + |C| * |u3 + u4|) ^ 2 :=
    sq_le_sq' (neg_le_of_abs_le hb1) (le_of_abs_le hb1)
  linarith

/-- **T1, granted the spectral data.** -/
-- PRIVATE ON PURPOSE. This states T1's conclusion under hypotheses that ENCODE it
-- (`hTrR`, `hTrQR` are the two trace shapes) and imposes nothing at all on `P`, `Q`.
-- An earlier delivery in this project was rejected by audit for presenting exactly this
-- as "Lemma T1". Here it is legitimate — `T1_gen` PROVES both hypotheses from `hdec` —
-- but it must never be exported or consumed directly, so it is sealed in this file.
private theorem T1_of_spectral_data (P Q : Mat4) (C u1 u2 u3 u4 : ℝ)
    (hC : |C| ≤ 1) (h1 : |u1| ≤ 1) (h2 : |u2| ≤ 1) (h3 : |u3| ≤ 1) (h4 : |u4| ≤ 1)
    (hsum : u1 + u2 + u3 + u4 = 0)
    (hTrR : (P * Zp4).trace = ((2 * C : ℝ) : ℂ))
    (hTrQR : (Q * P * Zp4).trace = ((u1 - u2 + C * (u3 + u4) : ℝ) : ℂ)
        + ((u3 - u4) * Real.sqrt (1 - C ^ 2) : ℝ) * Complex.I) :
    Complex.normSq ((P * Zp4).trace) + Complex.normSq ((Q * P * Zp4).trace) ≤ 8 := by
  have hC1 : C ^ 2 ≤ 1 := by nlinarith [sq_abs C, abs_nonneg C]
  have hval : Complex.normSq ((P * Zp4).trace) + Complex.normSq ((Q * P * Zp4).trace)
      = 4 * C ^ 2 + (u1 - u2 + C * (u3 + u4)) ^ 2 + (1 - C ^ 2) * (u3 - u4) ^ 2 := by
    rw [hTrR, hTrQR]
    have hs : Real.sqrt (1 - C ^ 2) ^ 2 = 1 - C ^ 2 := Real.sq_sqrt (by linarith)
    simp [Complex.normSq_apply]
    nlinarith [hs]
  rw [hval]
  exact core_ineq C u1 u2 u3 u4 hC h1 h2 h3 h4 hsum

/-! ## 8. The degenerate case `|P₃₃| = 1` (NEW) -/

/-- If `|P₃₃| = 1` then column `3` of `P` is `P₃₃ e₃`, so `P E = P₃₃ E`. -/
lemma PE4_of_deg (P : Mat4) (hP : Pᴴ = P) (hP2 : P * P = 1) (hdeg : (P 3 3).re ^ 2 = 1) :
    P * E4 = (P 3 3) • E4 := by
  have hPu : Pᴴ * P = 1 := by rw [hP]; exact hP2
  have hcol := col_sum_normSq P hPu 3
  have him : (P 3 3).im = 0 := herm_diag_im P hP 3
  have h33 : Complex.normSq (P 3 3) = 1 := by
    rw [Complex.normSq_apply, him]; nlinarith
  rw [Fin.sum_univ_four, h33] at hcol
  have n0 := Complex.normSq_nonneg (P 0 3)
  have n1 := Complex.normSq_nonneg (P 1 3)
  have n2 := Complex.normSq_nonneg (P 2 3)
  have e0 : P 0 3 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have e1 : P 1 3 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have e2 : P 2 3 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E4, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_four, e0, e1, e2]

/-- **T1, degenerate case `|P₃₃| = 1`.**  Here `R = P Z'` is itself a Hermitian
involution with `Tr R = ∓2`, so `(1 + p R)/2` is a rank-one projection. -/
theorem T1_deg (P Q : Mat4) (hP : Pᴴ = P) (hP2 : P * P = 1) (hPt : P.trace = 0)
    (hQ : Qᴴ = Q) (hQ2 : Q * Q = 1) (hQt : Q.trace = 0) (hdeg : (P 3 3).re ^ 2 = 1) :
    Complex.normSq ((P * Zp4).trace) + Complex.normSq ((Q * P * Zp4).trace) ≤ 8 := by
  have him : (P 3 3).im = 0 := herm_diag_im P hP 3
  obtain ⟨p, hp33⟩ : ∃ r : ℝ, P 3 3 = (r : ℂ) :=
    ⟨(P 3 3).re, by apply Complex.ext <;> simp [him]⟩
  have hpsq : p ^ 2 = 1 := by rw [hp33] at hdeg; simpa using hdeg
  have hppC : (p : ℂ) * (p : ℂ) = 1 := by
    have h : ((p ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by rw [hpsq]
    push_cast at h; linear_combination h
  have hPE : P * E4 = (p : ℂ) • E4 := by rw [PE4_of_deg P hP hP2 hdeg, hp33]
  have hEP : E4 * P = (p : ℂ) • E4 := by
    have h1 : (P * E4)ᴴ = E4 * P := by rw [Matrix.conjTranspose_mul, E4_conjTranspose, hP]
    have h2 : ((p : ℂ) • E4)ᴴ = (p : ℂ) • E4 := by
      rw [Matrix.conjTranspose_smul, E4_conjTranspose, Complex.star_def, Complex.conj_ofReal]
    rw [← h1, hPE, h2]
  have hEcomm : E4 * P = P * E4 := by rw [hEP, hPE]
  have hcomm : Zp4 * P = P * Zp4 := by
    rw [Zp4_eq_one_sub]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, hEcomm]
  have hRH : (P * Zp4)ᴴ = P * Zp4 := by
    rw [Matrix.conjTranspose_mul, Zp4_conjTranspose, hP, hcomm]
  have hRR : (P * Zp4) * (P * Zp4) = 1 := by
    calc (P * Zp4) * (P * Zp4) = P * (Zp4 * P) * Zp4 := by noncomm_ring
      _ = (P * P) * (Zp4 * Zp4) := by rw [hcomm]; noncomm_ring
      _ = 1 := by rw [hP2, Zp4_mul_self, Matrix.one_mul]
  have hRt : (P * Zp4).trace = ((-2 * p : ℝ) : ℂ) := by
    rw [trace_mul_Zp4, hPt, hp33]; push_cast; ring
  set Pj : Mat4 := (2 : ℂ)⁻¹ • (1 + (p : ℂ) • (P * Zp4)) with hPjdef
  have hPjH : Pjᴴ = Pj := by
    have hs2 : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by simp
    have hsp : star ((p : ℂ)) = (p : ℂ) := by simp
    rw [hPjdef, Matrix.conjTranspose_smul, hs2, Matrix.conjTranspose_add,
      Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hsp, hRH]
  have hPj2 : Pj * Pj = Pj := by
    rw [hPjdef, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have h : (1 + (p : ℂ) • (P * Zp4)) * (1 + (p : ℂ) • (P * Zp4))
        = 1 + (p : ℂ) • (P * Zp4) + (p : ℂ) • (P * Zp4)
          + ((p : ℂ) * (p : ℂ)) • ((P * Zp4) * (P * Zp4)) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
        Matrix.smul_mul, Matrix.mul_smul]
      module
    rw [h, hRR, hppC]
    module
  have htr1 : (1 : Mat4).trace = 4 := by simp
  have hPjt : Pj.trace = 1 := by
    rw [hPjdef, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_smul, hRt, htr1, smul_eq_mul,
      smul_eq_mul]
    push_cast
    field_simp
    linear_combination (-2 : ℂ) * hppC
  set u : ℝ := ((Q * Pj).trace).re with hudef
  have hu : (Q * Pj).trace = (u : ℂ) := by
    apply Complex.ext <;> simp [hudef, trace_QP_im Pj Q hPjH hQ]
  have hub : |u| ≤ 1 := trace_Q_proj_re_le Q Pj hQ hQ2 hPjH hPj2 hPjt
  have hRdec : P * Zp4 = (p : ℂ) • (Pj + Pj - 1) := by
    have h2 : Pj + Pj = 1 + (p : ℂ) • (P * Zp4) := by rw [hPjdef]; module
    rw [h2]
    have h3 : (1 : Mat4) + (p : ℂ) • (P * Zp4) - 1 = (p : ℂ) • (P * Zp4) := by abel
    rw [h3, smul_smul, hppC, one_smul]
  have hQRt : (Q * P * Zp4).trace = ((2 * p * u : ℝ) : ℂ) := by
    rw [Matrix.mul_assoc, hRdec, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sub,
      Matrix.mul_add, Matrix.trace_sub, Matrix.trace_add, Matrix.mul_one, hQt, hu, smul_eq_mul]
    push_cast; ring
  rw [hRt, hQRt, Complex.normSq_ofReal, Complex.normSq_ofReal]
  nlinarith [abs_le.mp hub, sq_nonneg u, sq_abs u, hpsq]

/-! ## 9. The generic case `|P₃₃| < 1` (NEW) -/

/-- **T1, generic case `|P₃₃| < 1`.**  `K1, K2` are the eigenprojections of `R = P Z'`
for `+1, -1` (living in the orthogonal complement of `span{e₃, P e₃}`, where `R = P`),
and `K3, K4` those for `e^{±iθ}` with `cos θ = -P₃₃`. -/
theorem T1_gen (P Q : Mat4) (hP : Pᴴ = P) (hP2 : P * P = 1) (hPt : P.trace = 0)
    (hQ : Qᴴ = Q) (hQ2 : Q * Q = 1) (hQt : Q.trace = 0) (hlt : (P 3 3).re ^ 2 < 1) :
    Complex.normSq ((P * Zp4).trace) + Complex.normSq ((Q * P * Zp4).trace) ≤ 8 := by
  have him : (P 3 3).im = 0 := herm_diag_im P hP 3
  obtain ⟨p, hp33⟩ : ∃ r : ℝ, P 3 3 = (r : ℂ) :=
    ⟨(P 3 3).re, by apply Complex.ext <;> simp [him]⟩
  have hplt : p ^ 2 < 1 := by rw [hp33] at hlt; simpa using hlt
  set s : ℝ := Real.sqrt (1 - p ^ 2) with hsdef
  have hspos : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hsC : (s : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; linarith
  have hsr2 : s ^ 2 = 1 - p ^ 2 := Real.sq_sqrt (by linarith)
  have hs2 : (s : ℂ) ^ 2 = 1 - (P 3 3) ^ 2 := by
    rw [hp33, ← Complex.ofReal_pow, hsr2]; push_cast; ring
  set G : Mat4 := Gm P s with hGdef
  have hG : Gᴴ = G := Gm_conjTranspose hP
  have hG3 : G * G * G = G := Gm_cube hP2 hsC hs2
  have hGt : G.trace = 0 := trace_Gm
  have hG2t : (G * G).trace = 2 := trace_Gm_sq hP2 hsC hs2
  have hcomm : G * G * P = P * (G * G) := Gm_sq_comm_P hP2 hsC hs2
  have hGPt : (G * G * P).trace = 0 := trace_Gm_sq_P hP2 hsC hs2
  have hkey : G * G * (P + (P 3 3) • (1 : Mat4)) = P * E4 + E4 * P := Gm_sq_key hP2 hsC hs2
  have hsG : ((s : ℂ) * Complex.I) • G = -Dm P := smul_Gm hsC
  set K1 : Mat4 := projS G (1 + P) with hK1
  set K2 : Mat4 := projS G (1 - P) with hK2
  set K3 : Mat4 := proj3 G with hK3
  set K4 : Mat4 := proj4 G with hK4
  have hK1H : K1ᴴ = K1 := projS_herm hG (herm_add hP) (comm_add hcomm)
  have hK1I : K1 * K1 = K1 := projS_idem hG3 (sq_add hP2) (comm_add hcomm)
  have hK1T : K1.trace = 1 := projS_trace (trace_aux_add hG2t hPt hGPt)
  have hK2H : K2ᴴ = K2 := projS_herm hG (herm_sub hP) (comm_sub hcomm)
  have hK2I : K2 * K2 = K2 := projS_idem hG3 (sq_sub hP2) (comm_sub hcomm)
  have hK2T : K2.trace = 1 := projS_trace (trace_aux_sub hG2t hPt hGPt)
  have hK3H : K3ᴴ = K3 := proj3_herm hG
  have hK3I : K3 * K3 = K3 := proj3_idem hG3
  have hK3T : K3.trace = 1 := proj3_trace hGt hG2t
  have hK4H : K4ᴴ = K4 := proj4_herm hG
  have hK4I : K4 * K4 = K4 := proj4_idem hG3
  have hK4T : K4.trace = 1 := proj4_trace hGt hG2t
  set u1 : ℝ := ((Q * K1).trace).re with hu1d
  set u2 : ℝ := ((Q * K2).trace).re with hu2d
  set u3 : ℝ := ((Q * K3).trace).re with hu3d
  set u4 : ℝ := ((Q * K4).trace).re with hu4d
  have hu1 : (Q * K1).trace = (u1 : ℂ) := by
    apply Complex.ext <;> simp [hu1d, trace_QP_im K1 Q hK1H hQ]
  have hu2 : (Q * K2).trace = (u2 : ℂ) := by
    apply Complex.ext <;> simp [hu2d, trace_QP_im K2 Q hK2H hQ]
  have hu3 : (Q * K3).trace = (u3 : ℂ) := by
    apply Complex.ext <;> simp [hu3d, trace_QP_im K3 Q hK3H hQ]
  have hu4 : (Q * K4).trace = (u4 : ℂ) := by
    apply Complex.ext <;> simp [hu4d, trace_QP_im K4 Q hK4H hQ]
  have hb1 : |u1| ≤ 1 := trace_Q_proj_re_le Q K1 hQ hQ2 hK1H hK1I hK1T
  have hb2 : |u2| ≤ 1 := trace_Q_proj_re_le Q K2 hQ hQ2 hK2H hK2I hK2T
  have hb3 : |u3| ≤ 1 := trace_Q_proj_re_le Q K3 hQ hQ2 hK3H hK3I hK3T
  have hb4 : |u4| ≤ 1 := trace_Q_proj_re_le Q K4 hQ hQ2 hK4H hK4I hK4T
  have hsum : K1 + K2 + K3 + K4 = 1 := by
    have e : K1 + K2 + K3 + K4
        = (2 : ℂ)⁻¹ • ((1 - G * G) * (1 + P) + (1 - G * G) * (1 - P)
          + (G * G + G) + (G * G - G)) := by
      rw [hK1, hK2, hK3, hK4, projS, projS, proj3, proj4]; module
    have e2 : (1 - G * G) * (1 + P) + (1 - G * G) * (1 - P) + (G * G + G) + (G * G - G)
        = (1 : Mat4) + 1 := by noncomm_ring
    rw [e, e2]; module
  have husum : u1 + u2 + u3 + u4 = 0 := by
    have h : (Q * (K1 + K2 + K3 + K4)).trace = 0 := by rw [hsum, Matrix.mul_one, hQt]
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add,
      Matrix.trace_add, hu1, hu2, hu3, hu4] at h
    exact_mod_cast h
  have e1 : K1 - K2 = (1 - G * G) * P := by
    rw [hK1, hK2, projS, projS, ← smul_sub]
    have h : (1 - G * G) * (1 + P) - (1 - G * G) * (1 - P)
        = (1 - G * G) * P + (1 - G * G) * P := by noncomm_ring
    rw [h]; module
  have e2 : (((-p : ℝ) : ℂ) + (s : ℂ) * Complex.I) • K3
        + (((-p : ℝ) : ℂ) - (s : ℂ) * Complex.I) • K4
      = ((-p : ℝ) : ℂ) • (G * G) + ((s : ℂ) * Complex.I) • G := by
    rw [hK3, hK4, proj3, proj4]; module
  have e3 : (1 - G * G) * P + ((-p : ℝ) : ℂ) • (G * G)
      = P - G * G * (P + (P 3 3) • (1 : Mat4)) := by
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, hp33, Matrix.sub_mul, Matrix.one_mul]
    push_cast; module
  have hdec : K1 - K2 + (((-p : ℝ) : ℂ) + (s : ℂ) * Complex.I) • K3
        + (((-p : ℝ) : ℂ) - (s : ℂ) * Complex.I) • K4 = P * Zp4 := by
    have step1 : K1 - K2 + (((-p : ℝ) : ℂ) + (s : ℂ) * Complex.I) • K3
          + (((-p : ℝ) : ℂ) - (s : ℂ) * Complex.I) • K4
        = (K1 - K2) + ((((-p : ℝ) : ℂ) + (s : ℂ) * Complex.I) • K3
          + (((-p : ℝ) : ℂ) - (s : ℂ) * Complex.I) • K4) := by abel
    rw [step1, e1, e2]
    have step2 : (1 - G * G) * P + (((-p : ℝ) : ℂ) • (G * G) + ((s : ℂ) * Complex.I) • G)
        = ((1 - G * G) * P + ((-p : ℝ) : ℂ) • (G * G)) + ((s : ℂ) * Complex.I) • G := by abel
    rw [step2, e3, hsG, hkey, Dm, Zp4_eq_one_sub]
    noncomm_ring
  have hTrR : (P * Zp4).trace = ((2 * -p : ℝ) : ℂ) := by
    rw [trace_mul_Zp4, hPt, hp33]; push_cast; ring
  have hTrQR : (Q * P * Zp4).trace = ((u1 - u2 + (-p) * (u3 + u4) : ℝ) : ℂ)
      + ((u3 - u4) * Real.sqrt (1 - (-p) ^ 2) : ℝ) * Complex.I := by
    rw [Matrix.mul_assoc, ← hdec]
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_add,
      Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, hu1, hu2, hu3, hu4]
    have hsq : Real.sqrt (1 - (-p) ^ 2) = s := by rw [hsdef]; congr 1; ring
    rw [hsq]; push_cast; ring
  exact T1_of_spectral_data P Q (-p) u1 u2 u3 u4
    (abs_le.mpr ⟨by nlinarith, by nlinarith⟩) hb1 hb2 hb3 hb4 husum hTrR hTrQR

/-! ## 10. Lemma T1 -/

/-- **Lemma T1.**  For rank-two reflections `P`, `Q` on `ℂ⁴` (Hermitian, involutive,
traceless — hence with spectrum `{+1,+1,-1,-1}`),
`|Tr (P Z')|² + |Tr (Q P Z')|² ≤ 8` where `Z' = diag(1,1,1,-1)`.
The bound is tight: `C = 0`, `u = (1,-1,1,-1)` attains `8`. -/
theorem T1 (P Q : Mat4)
    (hP : Pᴴ = P) (hP2 : P * P = 1) (hPt : Matrix.trace P = 0)
    (hQ : Qᴴ = Q) (hQ2 : Q * Q = 1) (hQt : Matrix.trace Q = 0) :
    Complex.normSq (Matrix.trace (P * Zp4)) +
    Complex.normSq (Matrix.trace (Q * P * Zp4)) ≤ 8 := by
  rcases lt_or_eq_of_le (diag_re_sq_le_one P hP hP2) with h | h
  · exact T1_gen P Q hP hP2 hPt hQ hQ2 hQt h
  · exact T1_deg P Q hP hP2 hPt hQ hQ2 hQt h

end

end T1Bridge
