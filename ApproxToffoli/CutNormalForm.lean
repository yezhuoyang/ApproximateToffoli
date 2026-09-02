/-
  ApproxToffoli.CutNormalForm

  **R4 and R5**: the reduction of the AB|C cut form to an explicit finite trace
  formula. This is the structural half of `cut_trace_bound`; what remains after
  it is a pure inequality about `Mat4` traces, with no circuits in sight.

  * **R4** (`BCCut_to_CZCut`). Conjugating qubit C by a Hadamard turns the
    crossing gate `CX_BC` into `CZ_BC`, which is C-block-DIAGONAL; the Hadamards
    are absorbed into the adjacent free layers, so the crossing-gate count is
    unchanged. `CX_CB` is handled the same way with a different (also free) cut
    product on each side. The objective `CCZ8` is NOT conjugated — the Hadamards
    live strictly inside the product — so nothing is lost.
  * **R5** (`trace_ccz_cut0/1/2`). Both `CCZ8` and `CZBC8` are C-block-diagonal:
        `CCZ8 = kronABC 1 proj0 + kronABC Zp4  proj1`,   `Zp4  = diag(1,1,1,-1)`
        `CZBC8 = kronABC 1 proj0 + kronABC Zhat4 proj1`, `Zhat4 = diag(1,-1,1,-1)`
    so expanding the product makes the C-index traverse a closed path
    `i → a → b → i`, giving `2^(m+1)` terms, each a product of `c`-entries times
    a `Mat4` trace.

  **Gate-order warning.** `notes/trace_bound_reduction.md` develops R5 with factors
  appended on the LEFT, but `BCCut`/`CZCut` append on the RIGHT (matching
  `AchievableCircuit`). The index roles are therefore REVERSED, and in particular
  the reflections swap: in Lean's order the reduction produces
      `K := M₀ M₁ M₂`,  `Q := M₀ Ẑ M₀ᴴ`,  `P := M₂ᴴ Ẑ M₂`
  whereas the notes have `P := M₀ᴴ Ẑ M₀`, `Q := M₂ Ẑ M₂ᴴ`. Copying the notes
  verbatim would give a false lemma. Re-derived and machine-checked in
  `PyScript/cut_r5_lean_order.py` (all identities to 1.8e-15).

  Everything in this file is `sorry`-free.
-/

import ApproxToffoli.CutForm

open Matrix Complex

noncomputable section

/-! ## The two C-blocks -/

/-- `Z' = diag(1,1,1,-1)`: the odd-C block of `CCZ8`, i.e. CZ on the AB pair. -/
def Zp4 : Mat4 := Matrix.diagonal ![1, 1, 1, -1]

/-- `Ẑ = diag(1,-1,1,-1)`: the odd-C block of `CZ_BC`, i.e. `I_A ⊗ Z_B`. -/
def Zhat4 : Mat4 := Matrix.diagonal ![1, -1, 1, -1]

/-- `CZ_BC = H_C · CX_BC · H_C`, the C-block-diagonal crossing gate. -/
def CZBC8 : Mat8 := kronABC 1 proj0 + kronABC Zhat4 proj1

lemma zp4_conjTranspose : Zp4ᴴ = Zp4 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Zp4, Matrix.conjTranspose_apply]

lemma zp4_mul_self : Zp4 * Zp4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Zp4, Matrix.mul_apply, Fin.sum_univ_four]

lemma zhat4_conjTranspose : Zhat4ᴴ = Zhat4 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Zhat4, Matrix.conjTranspose_apply]

lemma zhat4_mul_self : Zhat4 * Zhat4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Zhat4, Matrix.mul_apply, Fin.sum_univ_four]

/-- `Ẑ` is traceless — this is what makes `M Ẑ Mᴴ` a rank-2 reflection, the shape
    Lemma T1 consumes. -/
lemma trace_zhat4 : Matrix.trace Zhat4 = 0 := by
  simp [Zhat4, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_four]

/-! ## `CCZ8` and `CZBC8` in cut form -/

/-- `CCZ` is C-block-diagonal with blocks `I₄` and `Z'`. -/
lemma ccz8_eq_cut_sum : CCZ8 = kronABC 1 proj0 + kronABC Zp4 proj1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CCZ8, kronABC, Zp4, proj0, proj1, Matrix.add_apply, Matrix.diagonal_apply,
      Matrix.one_apply, Matrix.of_apply]

lemma kron2_one_one : kron2 1 1 = (1 : Mat4) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kron2, Matrix.one_apply, Matrix.of_apply]

/-- `H_C` is a cut product, so it can be absorbed into a free layer. -/
lemma hC_eq_kronABC : kron3 1 1 Hgate = kronABC 1 Hgate := by
  rw [kron3_eq_kronABC, kron2_one_one]

set_option maxHeartbeats 1600000 in
-- Heartbeat bump: 64-case `fin_cases × fin_cases` on `Fin 8`, each an 8-term
-- `Matrix.mul_apply` expansion with `1/√2` arithmetic.
/-- **R4, core computation.** `H_C · CX_BC · H_C = CZ_BC`. -/
lemma czbc_eq_conj : kron3 1 1 Hgate * CX_BC * kron3 1 1 Hgate = CZBC8 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CX_BC, kron3, decode3, Hgate, kronABC, CZBC8, Zhat4, proj0, proj1, pauliX, I₂,
      Matrix.mul_apply, Matrix.add_apply, Matrix.diagonal_apply, Matrix.one_apply,
      Matrix.of_apply, Fin.sum_univ_eight] <;>
    ring_nf <;>
    norm_num [invSqrt2_pow2, invSqrt2_pow4]

/-- **R4 (BC).** `CX_BC` is `CZBC8` conjugated by the cut product `H_C`. -/
lemma cx_bc_eq_cz_conj : CX_BC = kronABC 1 Hgate * CZBC8 * kronABC 1 Hgate := by
  rw [← czbc_eq_conj, ← hC_eq_kronABC]
  calc CX_BC = 1 * CX_BC * 1 := by rw [one_mul, mul_one]
    _ = kron3 1 1 Hgate * (kron3 1 1 Hgate * CX_BC * kron3 1 1 Hgate)
          * kron3 1 1 Hgate := by rw [← h8_mul_self]; noncomm_ring

/-- **R4 (CB).** `CX_CB` too, with a different (still free) cut product on each side. -/
lemma cx_cb_eq_cz_conj :
    CX_CB = kronABC (kron2 1 Hgate) 1 * CZBC8 * kronABC (kron2 1 Hgate) 1 := by
  have hL : kron3 1 Hgate Hgate * kronABC 1 Hgate = kronABC (kron2 1 Hgate) 1 := by
    rw [kron3_eq_kronABC, kronABC_mul, hgate_sq, mul_one]
  have hR : kronABC 1 Hgate * kron3 1 Hgate Hgate = kronABC (kron2 1 Hgate) 1 := by
    rw [kron3_eq_kronABC, kronABC_mul, hgate_sq, one_mul]
  calc CX_CB = kron3 1 Hgate Hgate * CX_BC * kron3 1 Hgate Hgate := cx_cb_eq_conj
    _ = kron3 1 Hgate Hgate * (kronABC 1 Hgate * CZBC8 * kronABC 1 Hgate)
          * kron3 1 Hgate Hgate := by rw [← cx_bc_eq_cz_conj]
    _ = (kron3 1 Hgate Hgate * kronABC 1 Hgate) * CZBC8
          * (kronABC 1 Hgate * kron3 1 Hgate Hgate) := by noncomm_ring
    _ = kronABC (kron2 1 Hgate) 1 * CZBC8 * kronABC (kron2 1 Hgate) 1 := by rw [hL, hR]

lemma isUnitary4_kron2_1_H : IsUnitary4 (kron2 1 Hgate) :=
  isUnitary4_kron2 (by rw [IsUnitary2]; simp) hgate_unitary

/-! ## The CZ cut normal form -/

/-- The cut normal form with the C-block-DIAGONAL crossing gate. Structurally
    identical to `BCCut` but with a single step constructor, since `CZBC8` is its
    own mirror — the `CX_BC`/`CX_CB` distinction has been absorbed. -/
inductive CZCut : ℕ → Mat8 → Prop where
  | base (M : Mat4) (c : Mat2) (hM : IsUnitary4 M) (hc : IsUnitary2 c) :
      CZCut 0 (kronABC M c)
  | step {m : ℕ} {U : Mat8} (h : CZCut m U)
      (M : Mat4) (c : Mat2) (hM : IsUnitary4 M) (hc : IsUnitary2 c) :
      CZCut (m + 1) (U * CZBC8 * kronABC M c)

/-- As for `BCCut_mul_right`, the `∀ M c` must be INSIDE the induction. -/
lemma CZCut_mul_right {m : ℕ} {U : Mat8} (h : CZCut m U) :
    ∀ (M : Mat4) (c : Mat2), IsUnitary4 M → IsUnitary2 c →
      CZCut m (U * kronABC M c) := by
  induction h with
  | base M' c' hM' hc' =>
      intro M c hM hc
      rw [kronABC_mul]
      exact CZCut.base _ _ (isUnitary4_mul hM' hM) (isUnitary2_mul hc' hc)
  | step hrest M' c' hM' hc' _ =>
      intro M c hM hc
      rw [Matrix.mul_assoc, kronABC_mul]
      exact CZCut.step hrest _ _ (isUnitary4_mul hM' hM) (isUnitary2_mul hc' hc)

/-- **R4, structural form.** Every BC-cut circuit is a CZ-cut circuit with the same
    crossing-gate count: the Hadamards are absorbed into the free layers. -/
theorem BCCut_to_CZCut {m : ℕ} {U : Mat8} (h : BCCut m U) : CZCut m U := by
  induction h with
  | base M c hM hc => exact CZCut.base M c hM hc
  | stepBC hrest M c hM hc ih =>
      have e : ∀ V : Mat8, V * CX_BC * kronABC M c
          = (V * kronABC 1 Hgate) * CZBC8 * kronABC (1 * M) (Hgate * c) := by
        intro V; rw [cx_bc_eq_cz_conj, ← kronABC_mul]; noncomm_ring
      rw [e]
      exact CZCut.step (CZCut_mul_right ih _ _ isUnitary4_one hgate_unitary) _ _
        (isUnitary4_mul isUnitary4_one hM) (isUnitary2_mul hgate_unitary hc)
  | stepCB hrest M c hM hc ih =>
      have e : ∀ V : Mat8, V * CX_CB * kronABC M c
          = (V * kronABC (kron2 1 Hgate) 1) * CZBC8
            * kronABC (kron2 1 Hgate * M) (1 * c) := by
        intro V; rw [cx_cb_eq_cz_conj, ← kronABC_mul]; noncomm_ring
      rw [e]
      exact CZCut.step
        (CZCut_mul_right ih _ _ isUnitary4_kron2_1_H isUnitary2_one) _ _
        (isUnitary4_mul isUnitary4_kron2_1_H hM) (isUnitary2_mul isUnitary2_one hc)

/-! ## R5 : the explicit trace formulas -/

/-- Trace factorises across the cut. -/
lemma trace_kronABC (M : Mat4) (c : Mat2) :
    Matrix.trace (kronABC M c) = Matrix.trace M * Matrix.trace c := by
  simp [kronABC, Matrix.trace, Matrix.diag_apply, Matrix.of_apply,
    Fin.sum_univ_eight, Fin.sum_univ_four, Fin.sum_univ_two]
  ring

lemma trace_proj0_mul (c : Mat2) : Matrix.trace (proj0 * c) = c 0 0 := by
  simp [proj0, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply,
    Fin.sum_univ_two]

lemma trace_proj1_mul (c : Mat2) : Matrix.trace (proj1 * c) = c 1 1 := by
  simp [proj1, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply,
    Fin.sum_univ_two]

/-! ### `Tr(Π_i a Π_j b) = a_{ij} b_{ji}` and its three-factor version -/

lemma trace_p00 (a b : Mat2) : Matrix.trace (proj0 * a * proj0 * b) = a 0 0 * b 0 0 := by
  simp [proj0, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply,
    Fin.sum_univ_two]

lemma trace_p01 (a b : Mat2) : Matrix.trace (proj0 * a * proj1 * b) = a 0 1 * b 1 0 := by
  simp [proj0, proj1, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.of_apply, Fin.sum_univ_two]

lemma trace_p10 (a b : Mat2) : Matrix.trace (proj1 * a * proj0 * b) = a 1 0 * b 0 1 := by
  simp [proj0, proj1, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.of_apply, Fin.sum_univ_two]

lemma trace_p11 (a b : Mat2) : Matrix.trace (proj1 * a * proj1 * b) = a 1 1 * b 1 1 := by
  simp [proj1, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply,
    Fin.sum_univ_two]

lemma tq000 (a b c : Mat2) :
    (proj0 * a * proj0 * b * proj0 * c).trace = a 0 0 * b 0 0 * c 0 0 := by
  simp [proj0, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply,
    Fin.sum_univ_two]

lemma tq001 (a b c : Mat2) :
    (proj0 * a * proj0 * b * proj1 * c).trace = a 0 0 * b 0 1 * c 1 0 := by
  simp [proj0, proj1, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.of_apply, Fin.sum_univ_two]

lemma tq010 (a b c : Mat2) :
    (proj0 * a * proj1 * b * proj0 * c).trace = a 0 1 * b 1 0 * c 0 0 := by
  simp [proj0, proj1, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.of_apply, Fin.sum_univ_two]

lemma tq011 (a b c : Mat2) :
    (proj0 * a * proj1 * b * proj1 * c).trace = a 0 1 * b 1 1 * c 1 0 := by
  simp [proj0, proj1, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.of_apply, Fin.sum_univ_two]

lemma tq100 (a b c : Mat2) :
    (proj1 * a * proj0 * b * proj0 * c).trace = a 1 0 * b 0 0 * c 0 1 := by
  simp [proj0, proj1, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.of_apply, Fin.sum_univ_two]

lemma tq101 (a b c : Mat2) :
    (proj1 * a * proj0 * b * proj1 * c).trace = a 1 0 * b 0 1 * c 1 1 := by
  simp [proj0, proj1, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.of_apply, Fin.sum_univ_two]

lemma tq110 (a b c : Mat2) :
    (proj1 * a * proj1 * b * proj0 * c).trace = a 1 1 * b 1 0 * c 0 1 := by
  simp [proj0, proj1, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.of_apply, Fin.sum_univ_two]

lemma tq111 (a b c : Mat2) :
    (proj1 * a * proj1 * b * proj1 * c).trace = a 1 1 * b 1 1 * c 1 1 := by
  simp [proj1, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply,
    Fin.sum_univ_two]

/-- **R5, m = 0.** Two terms. This is `F(0)`: the objective is a unit-weighted
    combination of `Tr M` and `Tr(Z' M)`, which the repo's `cnot_trace_bound`
    already bounds. -/
lemma trace_ccz_cut0 (M : Mat4) (c : Mat2) :
    Matrix.trace (CCZ8 * kronABC M c)
      = c 0 0 * Matrix.trace M + c 1 1 * Matrix.trace (Zp4 * M) := by
  rw [ccz8_eq_cut_sum, Matrix.add_mul, kronABC_mul, kronABC_mul, Matrix.trace_add,
    trace_kronABC, trace_kronABC, trace_proj0_mul, trace_proj1_mul, Matrix.one_mul]
  ring

/-- **R5, m = 1.** Four terms: the C-index traverses the closed path `i → a → i`. -/
lemma trace_ccz_cut1 (M0 M1 : Mat4) (c0 c1 : Mat2) :
    Matrix.trace (CCZ8 * kronABC M0 c0 * CZBC8 * kronABC M1 c1)
      = c0 0 0 * c1 0 0 * Matrix.trace (M0 * M1)
      + c0 0 1 * c1 1 0 * Matrix.trace (M0 * Zhat4 * M1)
      + c0 1 0 * c1 0 1 * Matrix.trace (Zp4 * M0 * M1)
      + c0 1 1 * c1 1 1 * Matrix.trace (Zp4 * M0 * Zhat4 * M1) := by
  rw [ccz8_eq_cut_sum, CZBC8]
  simp only [Matrix.add_mul, Matrix.mul_add, kronABC_mul, Matrix.trace_add,
    trace_kronABC, Matrix.one_mul, Matrix.mul_one, trace_p00, trace_p01, trace_p10,
    trace_p11]
  ring

set_option maxHeartbeats 1000000 in
-- Heartbeat bump: an eight-term expansion of a five-factor product of cut sums.
/-- **R5, m = 2.** Eight terms: the C-index traverses the closed path
    `i → a → b → i`. This is the formula the analytic argument consumes:
    setting `K = M₀M₁M₂`, `Q = M₀ Ẑ M₀ᴴ`, `P = M₂ᴴ Ẑ M₂` (note the Lean gate order —
    see the module docstring) each `Mat4` trace becomes `Tr(Z'ⁱ Qᵃ K Pᵇ)`. -/
lemma trace_ccz_cut2 (M0 M1 M2 : Mat4) (c0 c1 c2 : Mat2) :
    Matrix.trace (CCZ8 * kronABC M0 c0 * CZBC8 * kronABC M1 c1 * CZBC8
        * kronABC M2 c2)
      = c0 0 0 * c1 0 0 * c2 0 0 * (M0 * M1 * M2).trace
      + c0 0 0 * c1 0 1 * c2 1 0 * (M0 * M1 * Zhat4 * M2).trace
      + c0 0 1 * c1 1 0 * c2 0 0 * (M0 * Zhat4 * M1 * M2).trace
      + c0 0 1 * c1 1 1 * c2 1 0 * (M0 * Zhat4 * M1 * Zhat4 * M2).trace
      + c0 1 0 * c1 0 0 * c2 0 1 * (Zp4 * M0 * M1 * M2).trace
      + c0 1 0 * c1 0 1 * c2 1 1 * (Zp4 * M0 * M1 * Zhat4 * M2).trace
      + c0 1 1 * c1 1 0 * c2 0 1 * (Zp4 * M0 * Zhat4 * M1 * M2).trace
      + c0 1 1 * c1 1 1 * c2 1 1 * (Zp4 * M0 * Zhat4 * M1 * Zhat4 * M2).trace := by
  rw [ccz8_eq_cut_sum, CZBC8]
  simp only [Matrix.add_mul, Matrix.mul_add, kronABC_mul, Matrix.trace_add,
    trace_kronABC, Matrix.one_mul, Matrix.mul_one,
    tq000, tq001, tq010, tq011, tq100, tq101, tq110, tq111]
  ring

/-! ## Moduli of the entries of a 2×2 unitary

These are what the bridge inequality consumes: unitarity of the C-side layers forces
the weights attached to the two C-blocks to be SWAPPED (`|c₀₀| = |c₁₁|`,
`|c₀₁| = |c₁₀|`), which is exactly why the four quantities `σ₁, σ₂, τ₁, τ₂` pair up
into two instances of `ψ(K')² + ψ(QK')²`. -/

/-- For a square matrix, `Uᴴ U = 1` forces `U Uᴴ = 1` too. -/
lemma isUnitary2_comm {c : Mat2} (h : IsUnitary2 c) : c * cᴴ = 1 :=
  mul_eq_one_comm.mp h

/-- Columns of a 2×2 unitary are unit vectors. -/
lemma u2_col0 {c : Mat2} (h : IsUnitary2 c) :
    Complex.normSq (c 0 0) + Complex.normSq (c 1 0) = 1 := by
  have h1 : (cᴴ * c) 0 0 = 1 := by rw [h]; simp
  rw [Matrix.mul_apply, Fin.sum_univ_two] at h1
  simp only [Matrix.conjTranspose_apply, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self] at h1
  exact_mod_cast congrArg Complex.re h1

lemma u2_col1 {c : Mat2} (h : IsUnitary2 c) :
    Complex.normSq (c 0 1) + Complex.normSq (c 1 1) = 1 := by
  have h1 : (cᴴ * c) 1 1 = 1 := by rw [h]; simp
  rw [Matrix.mul_apply, Fin.sum_univ_two] at h1
  simp only [Matrix.conjTranspose_apply, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self] at h1
  exact_mod_cast congrArg Complex.re h1

/-- Rows of a 2×2 unitary are unit vectors. -/
lemma u2_row0 {c : Mat2} (h : IsUnitary2 c) :
    Complex.normSq (c 0 0) + Complex.normSq (c 0 1) = 1 := by
  have h1 : (c * cᴴ) 0 0 = 1 := by rw [isUnitary2_comm h]; simp
  rw [Matrix.mul_apply, Fin.sum_univ_two] at h1
  simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj] at h1
  exact_mod_cast congrArg Complex.re h1

/-- **The anti-correlation.** In a 2×2 unitary the two diagonal entries have equal
    modulus, as do the two off-diagonal entries. -/
lemma u2_diag_eq {c : Mat2} (h : IsUnitary2 c) :
    Complex.normSq (c 0 0) = Complex.normSq (c 1 1) := by
  have h0 := u2_col0 h
  have h1 := u2_col1 h
  have hr := u2_row0 h
  linarith

lemma u2_offdiag_eq {c : Mat2} (h : IsUnitary2 c) :
    Complex.normSq (c 0 1) = Complex.normSq (c 1 0) := by
  have h0 := u2_col0 h
  have hr := u2_row0 h
  linarith

end
