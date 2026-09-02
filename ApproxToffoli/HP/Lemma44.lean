/-
  ApproxToffoli.HP.Lemma44
  Formalization of HP paper Lemmas 4.1, 4.2, 4.3, 4.4 (V₃ entangling case)
  and their supporting infrastructure.

  Paper reference: Huang & Palsberg (2026), "Toffoli Requires Six Quantum
  Neighbor Gates", ACM TQC 7(2), Article 10, Lemmas 4.1/4.2/4.3/4.4
  (pages 9-13 of 3787463.pdf).

  ## Status (as of iter 99)

  **FULLY PROVED end-to-end:**
  - `lemma_A_8_trichotomy` — bridge via `py24_lemma_6_1` reuse (iter 4).
  - `paper_lemma_4_3` — 5-iter closure (iters 7-11) via chain rearrangement
    + `py24_lemma_A_27` + `controlled_a_factor` + Lemma A.7 absorption.
  - `paper_lemma_4_4` — full end-to-end via `eq_16_action` + step5 dispatch
    (iters 13-17).
  - `paper_lemma_4_2`'s `d₀ = d₁` branch (iter 32).
  - Paper Lemma A.1's content for our chain (iters 61-65): L commutes with
    Z_B → block-(A,B) diagonality of L → L_00, L_10 unconditionally unitary.

  **SCAFFOLDED with remaining inner sorries:**
  - `paper_lemma_4_2`'s `d₀ ≠ d₁` branch:
    - ~~`hM_joint_unit`~~ ✅ CLOSED (iter 74) via circular-dep break: L_01,
      L_11 unitarity (from `blockA_11_unitary_of_blockA_10_zero`) → X_eig,
      Y_eig unitarity (product of unitaries) → M_joint via
      `controlled_A_unitary`. No paper Eq.7 needed.
    - Case (1) sorry — needs paper Lemma A.2 + `paper_lemma_4_1` invocation.
    - Case (2) chain factorization — paper Eq.7-derived identity, reduced to:
      `embedAC V₂_eff · embedAB V₃_eff · embedBC (kron2 (P_phase d₀) L_00)
       = embedAC U₂ · embedBC Dmid · embedAC U₄` (single inner 3-gate equation
      after W₁/W₅ cancellation via h_chain_target_rearranged + h_chain_factored).
      Iters 97-98 added `h_block00_L_Case2_eq` + `h_block11_L_Case2_eq`
      giving the explicit Eq.(10) sub-block forms in terms of L_00, L_10, d_i.
      Combining these into an L-form requires NEW `mat8_eq_of_block_diag_A`
      infrastructure in BlockDecomp.lean (iter 99 finding).
    - Case (3) chain factorization — symmetric to Case (2).

  See `notes/paper_eq_7_gap.md` for the detailed Case (2)/(3) Eq.7→8→9
  derivation roadmap, `notes/proof_state.md` for the current 8-sorry
  status, and `notes/setchar_audit.md` for SetChar.lean sorry classification.

  **STUBS (multi-week paper algebra):**
  - `paper_lemma_4_1` — Fig.6 base 5→4 reduction.
  - `joint_spec_multiplicity_trichotomy` — multiplicity-based case-split
    derived from `py24_lemma_A_6` (= HP A.12 itself). NOT a direct paper
    lemma; used internally by `paper_lemma_4_2`'s d₀≠d₁ branch.

  ## Helper library (selected)

  - `controlled_A_unitary` — `kron2 proj0 X + kron2 proj1 Y` unitary.
  - `P_phase, P_phase_unitary, P_phase_conjTranspose` — phase gates.
  - `controlled_a_factor` — Lemma A.7-style absorption.
  - `embedAC_commutes_B_only` — disjoint qubit commutation.
  - `blockDiagB_spectral` — paper Lemma A.5 content (spectral decomp).
  - `scalar_blockDiagB_eq_kron2_diag` — scalar-P case simplification.
  - `blockDiagB_kron2_eq_diagonal` — Dmid as `Diag(1,d₀,1,d₁)`.
  - `diagGate3_block00/11_unitary` — diagonal Mat8 block unitarity.
  - `conjTranspose_fixes_ket00`, `embedAC_conjTranspose_apply_ket0_b_ket0`.
  - `eq_16_action` — paper Eq.16 (10-step calc).
  - `diagonal_unitary_normSq` — diagonal Mat2 unitary → unit-modulus entries.

  ## Trajectory summary (iter 87)

  After 86 iters: 4 major paper lemmas closed end-to-end + d₀=d₁ branch of 4_2
  + Lemma A.1 + hM_joint_unit + full d₀≠d₁ scaffolding (V_i unitarities +
  chain target rearrangements). 8 sorry-decls, 3 inner sorries (paper Eq.7-
  level work). Loop is in maintenance mode; remaining gaps are multi-week
  paper algebra. FiveToFour pivot (iter 85) blocked by pattern mismatch
  (ABABA→ACBCAC under SWAP_BC ≠ paper_lemma_4_3's BC-AC-BC-AC-BC).
-/

import ApproxToffoli.PY24.Lemmas
-- Iter 1042: was `import ApproxToffoli.HP.SetChar`, which this file used for
-- NOTHING (measured: 0 referenced declarations). Dropping it, and taking the
-- `IsDiag8` facts from the small upstream `HP/DiagBlocks.lean` instead, removes
-- this file from FiveToFour's downstream cone — so FiveToFour can now import
-- Lemma44 and use `paper_lemma_4_4` in the 5→4 reduction.
import ApproxToffoli.HP.DiagBlocks
-- `IsBlockDiagFirst`, `ZI`, `commutes_ZI_implies_blockDiagFirst` used to reach
-- this file transitively through SetChar; take them directly now.
import ApproxToffoli.HP.Trichotomy
-- Mathlib spectral theorem for Hermitian matrices: supplies the 2×2 SVD that
-- paper Lemma A.4 (cosine-sine decomposition) is built on.
import Mathlib.Analysis.Matrix.Spectrum

open Matrix Complex

noncomputable section

namespace HP

/-! ## Helper: V† fixes |0⟩⊗|0⟩ when V does (used for Eq.16 derivation)

Lemma 4.4's Eq.16 derivation uses `W₄†_AC · (|0⟩⊗|y⟩⊗|0⟩) = |0⟩⊗|y⟩⊗|0⟩`
for arbitrary qubits y. Composes `embedAC_apply_ket0_b_ket0_when_V_fixes_ket00`
with the standard V† fixes |00⟩ derivation from V·V† = 1. -/

/-- If `V (|0⟩⊗|0⟩) = |0⟩⊗|0⟩` and V is unitary, then so does V†. -/
lemma conjTranspose_fixes_ket00 (V : Mat4) (hV : IsUnitary4 V)
    (hV_ket00 : Mat4.apply V (tensor1_1 ket0_1 ket0_1) = tensor1_1 ket0_1 ket0_1) :
    Mat4.apply V.conjTranspose (tensor1_1 ket0_1 ket0_1) =
      tensor1_1 ket0_1 ket0_1 := by
  have step : Mat4.apply (V.conjTranspose * V) (tensor1_1 ket0_1 ket0_1) =
              Mat4.apply V.conjTranspose (tensor1_1 ket0_1 ket0_1) := by
    rw [Mat4.apply_mul, hV_ket00]
  rw [hV, Mat4.apply_one] at step
  exact step.symm

/-- `embedAC V†` acts as identity on `|0⟩_A ⊗ b_B ⊗ |0⟩_C` when V fixes |00⟩. -/
lemma embedAC_conjTranspose_apply_ket0_b_ket0 (V : Mat4) (hV : IsUnitary4 V)
    (hV_ket00 : Mat4.apply V (tensor1_1 ket0_1 ket0_1) = tensor1_1 ket0_1 ket0_1)
    (b : Vec1) :
    Mat8.apply (embedAC V.conjTranspose) (tensor1_2 ket0_1 (tensor1_1 b ket0_1)) =
    tensor1_2 ket0_1 (tensor1_1 b ket0_1) :=
  embedAC_apply_ket0_b_ket0_when_V_fixes_ket00 V.conjTranspose b
    (conjTranspose_fixes_ket00 V hV hV_ket00)

/-! ## Helper: phase gate `P(c) = Diag(1, c)` for unit-modulus c

Used in `paper_lemma_4_2`'s case (2)/(3) constructions where the explicit
V₁..V₄ involve phase gates like `P(β) = Diag(1, e^{iβ})`. Parametrized
by complex c rather than real β so we can use unit-modulus complex
hypotheses directly. -/

/-- Phase gate as 2×2 diagonal: `P(c) = Diag(1, c)`. -/
def P_phase (c : ℂ) : Mat2 := Matrix.diagonal ![1, c]

/-- `P_phase c` is unitary when `|c|² = 1`. -/
lemma P_phase_unitary {c : ℂ} (hc : Complex.normSq c = 1) :
    IsUnitary2 (P_phase c) :=
  isUnitary2_diag_one_u c hc

/-- `(P_phase c)† = P_phase (conj c)`. Conjugate transpose of a diagonal
    matrix is the diagonal of conjugates. -/
lemma P_phase_conjTranspose (c : ℂ) :
    (P_phase c).conjTranspose = P_phase (starRingEnd ℂ c) := by
  unfold P_phase
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Matrix.diagonal,
          Matrix.cons_val_zero, Matrix.cons_val_one]

/-- `P_phase a * P_phase b = P_phase (a * b)`. Phase gates multiply by adding
    their phases (multiplicatively). Used in paper Eq.(11) Case (2)
    simplification: `P_phase β_phase * P_phase d₀ = P_phase d₁` after
    substituting `β_phase = d₁·conj(d₀)` and `|d₀|² = 1`. -/
lemma P_phase_mul (a b : ℂ) : P_phase a * P_phase b = P_phase (a * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P_phase, Matrix.mul_apply, Matrix.diagonal,
          Matrix.cons_val_zero, Matrix.cons_val_one]

/-! ## Helper: controlled-A 2-qubit gate is unitary when both sub-blocks are

The block-diag-A 4×4 matrix `kron2 proj0 X + kron2 proj1 Y` is unitary when
both X and Y are unitary Mat2s. Useful in `paper_lemma_4_2`'s d₀≠d₁ branch
and case-dispatch reconstructions. Symmetric to PY24's `controlled_C_unitary`. -/
lemma controlled_A_unitary {X Y : Mat2}
    (hX : IsUnitary2 X) (hY : IsUnitary2 Y) :
    IsUnitary4 (kron2 proj0 X + kron2 proj1 Y) := by
  unfold IsUnitary4
  rw [block_diag_first_conjT, block_diag_first_mul]
  unfold IsUnitary2 at hX hY
  rw [hX, hY]
  -- Goal: kron2 proj0 1 + kron2 proj1 1 = 1
  rw [← kron2_add_left]
  change kron2 (proj0 + proj1) 1 = 1
  rw [show proj0 + proj1 = (1 : Mat2) from by
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [proj0, proj1, Matrix.add_apply, Matrix.of_apply]]
  exact kron2_one_one_eq_one

/-! ## Helper: diagonal 2×2 unitary has unit-modulus entries

A diagonal Mat2 is unitary iff each entry has `Complex.normSq = 1`.
Forward direction extracted here (the reverse is `isUnitary2_diag_one_u`
and friends in PY24). Used in `paper_lemma_4_2` to derive eigenvalue
unit-modulus from `V† · P · V = Diag(d₀, d₁)`. -/
-- Linter disabled for the simp at h00 h11 below: replacing with `simp only`
-- breaks the proof (Fin.sum doesn't unfold; iter 147 verified). The flexible
-- tactic is intentional here.
set_option linter.flexible false in
lemma diagonal_unitary_normSq (d₀ d₁ : ℂ)
    (h : IsUnitary2 (Matrix.diagonal ![d₀, d₁])) :
    Complex.normSq d₀ = 1 ∧ Complex.normSq d₁ = 1 := by
  unfold IsUnitary2 at h
  have h00 := congrFun (congrFun h 0) 0
  have h11 := congrFun (congrFun h 1) 1
  simp [Matrix.conjTranspose_apply, Matrix.diagonal, Matrix.mul_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one] at h00 h11
  refine ⟨?_, ?_⟩
  · have h_norm : d₀ * starRingEnd ℂ d₀ = ((Complex.normSq d₀ : ℝ) : ℂ) :=
      Complex.mul_conj d₀
    rw [mul_comm] at h_norm
    rw [h_norm] at h00
    exact_mod_cast h00
  · have h_norm : d₁ * starRingEnd ℂ d₁ = ((Complex.normSq d₁ : ℝ) : ℂ) :=
      Complex.mul_conj d₁
    rw [mul_comm] at h_norm
    rw [h_norm] at h11
    exact_mod_cast h11

/-! ## Helper: Dmid as a 4x4 diagonal matrix

After `blockDiagB_spectral`, the middle gate `Dmid` from `paper_lemma_4_2`'s
proof equals `Matrix.diagonal ![1, d₀, 1, d₁]` — a 4×4 diagonal matrix.
This simplifies subsequent reasoning: instead of the abstract kron2-sum
form, we can treat Dmid as a diagonal Mat4 with known entries. -/
lemma blockDiagB_kron2_eq_diagonal (d₀ d₁ : ℂ) :
    kron2 1 proj0 + kron2 (Matrix.diagonal ![d₀, d₁]) proj1 =
    Matrix.diagonal ![1, d₀, 1, d₁] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kron2, proj0, proj1, Matrix.diagonal, Matrix.add_apply, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one]

/-! ## Helper: scalar block-diag-B factors as identity-tensor-diagonal

When `d₀ = d₁` in `blockDiagB_spectral`'s output, the middle "Dmid" gate
becomes purely C-dependent (no B-dependence beyond identity). It factors
cleanly as `kron2 1 (Matrix.diagonal ![1, d])`. -/
lemma scalar_blockDiagB_eq_kron2_diag (d : ℂ) :
    kron2 1 proj0 + kron2 (Matrix.diagonal ![d, d]) proj1 =
    kron2 1 (Matrix.diagonal ![1, d]) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kron2, proj0, proj1, Matrix.diagonal, Matrix.add_apply, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **Iter 1032: WLOG-normalization of the block-diag-B middle gate.**

    `Dmid = Diag(1, d₀, 1, d₁)` factors as a **C-only** phase gate
    `1 ⊗ Diag(1, d₀)` times the NORMALIZED block-diag-B gate
    `Diag(1, 1, 1, d₁·conj d₀)`, whose two branches are `1` and the ratio
    `e := d₁·conj d₀`.

    This is the missing normalization identified in iter 1031: the joint
    spectrum of paper Eq.(6) depends only on `e`, never on `d₀` and `d₁`
    separately (see `joint_spec_general_form_false`). The C-only left factor is
    absorbable into the neighbouring `embedAC` gate via
    `embedBC_kron2_one_eq_embedAC_kron2_one`, which is exactly how
    `paper_lemma_4_2` discharges the `d₀ = 1` hypothesis of
    `paper_lemma_4_2_joint_spec`.

    It plays the role of the paper's determinant-one normalization of the
    Lemma A.5 factors `R(α₀), R(α₁) ↦ R(β) = R(α₁ - α₀)`. -/
lemma blockDiagB_diag_normalize (d₀ d₁ : ℂ) (hd₀ : Complex.normSq d₀ = 1) :
    kron2 1 proj0 + kron2 (Matrix.diagonal ![d₀, d₁]) proj1 =
    kron2 1 (Matrix.diagonal ![1, d₀]) *
      (kron2 1 proj0 + kron2 (Matrix.diagonal ![1, d₁ * starRingEnd ℂ d₀]) proj1) := by
  have hconj : d₀ * starRingEnd ℂ d₀ = 1 := by
    rw [Complex.mul_conj]; exact_mod_cast hd₀
  rw [← scalar_blockDiagB_eq_kron2_diag d₀, blockDiagB_kron2_eq_diagonal,
      blockDiagB_kron2_eq_diagonal, blockDiagB_kron2_eq_diagonal,
      Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  fin_cases k <;> simp
  linear_combination (-d₁) * hconj

/-! ## Helpers for joint_spec_multiplicity_trichotomy Step v case-split

Two reusable helpers used in Case 1 / Case 4 of the trichotomy:
- `diag_two_eq_smul_one`: scalar-diagonal identity `diag(α, α) = α • 1`.
- `scalar_eq_of_unitary_conj_mat2`: if `V† X V = diag(α, α)` with V unitary,
  then `X = diag(α, α)`. -/

lemma diag_two_eq_smul_one (α : ℂ) :
    (Matrix.diagonal ![α, α] : Mat2) = α • (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Matrix.one_apply, Matrix.smul_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one]

/-- pauliX conjugates a 2-diagonal by swapping its entries.
    Used for Case 2/3 (eigenvalue-swap) in Step v. -/
lemma pauliX_diag_pauliX_swap (x y : ℂ) :
    pauliX * Matrix.diagonal ![x, y] * pauliX = Matrix.diagonal ![y, x] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.diagonal, Matrix.mul_apply, Matrix.of_apply,
          Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- pauliX is unitary. -/
lemma isUnitary2_pauliX : IsUnitary2 pauliX := by
  show pauliX.conjTranspose * pauliX = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.conjTranspose_apply, Matrix.mul_apply,
          Matrix.of_apply, Matrix.one_apply, Fin.sum_univ_two]

lemma scalar_eq_of_unitary_conj_mat2
    (V : Mat2) (hV : IsUnitary2 V) (X : Mat2) (α : ℂ)
    (h : V.conjTranspose * X * V = Matrix.diagonal ![α, α]) :
    X = Matrix.diagonal ![α, α] := by
  have hVV : V * V.conjTranspose = 1 := mul_eq_one_comm.mp hV
  have hdiag := diag_two_eq_smul_one α
  calc X = 1 * X * 1 := by rw [one_mul, mul_one]
    _ = V * V.conjTranspose * X * (V * V.conjTranspose) := by rw [hVV]
    _ = V * (V.conjTranspose * X * V) * V.conjTranspose := by noncomm_ring
    _ = V * (α • (1 : Mat2)) * V.conjTranspose := by rw [h, hdiag]
    _ = α • (V * V.conjTranspose) := by
        rw [Matrix.mul_smul, Matrix.smul_mul, mul_one]
    _ = α • (1 : Mat2) := by rw [hVV]
    _ = Matrix.diagonal ![α, α] := hdiag.symm

/-! ## Joint-spectrum multiplicity trichotomy (scaffolding stub)

⚠️ **NAMING NOTE (iter 187 correction)**: this is **NOT** HP Lemma A.12.
HP A.12 (paper page 28) is just the eigenvalue-set equation
`Eigenvalues(|0⟩⟨0| ⊗ P + |1⟩⟨1| ⊗ Q) = Eigenvalues(P) ⊔ Eigenvalues(Q)`
and is already proved as `py24_lemma_A_6` (cited by HP as their A.12 =
"[Palsberg and Yu 2024, Lemma A.6]").

This stub is a **multiplicity-based case-split** derived FROM HP A.12 +
the constraint that the joint spectrum is `{α₀, α₀, α₁, α₁}` (a
multiset with each eigenvalue of multiplicity 2). The paper expresses
this case-split implicitly through the multiplicity argument inside
paper_lemma_4_2's d₀≠d₁ derivation (page 10-11); it has no separate
name in the paper.

Given 2x2 unitaries X, Y and unit-modulus α₀, α₁ ∈ ℂ, IF the joint
spectrum of `kron2 proj0 X + kron2 proj1 Y` is `{α₀, α₀, α₁, α₁}`,
THEN exactly one of three structural conditions holds:
  (1) Each of X, Y is similar to `Diag(α₀, α₁)` (mixed eigenvalues).
  (2) X is the scalar `α₀·I` and Y is the scalar `α₁·I`.
  (3) X is the scalar `α₁·I` and Y is the scalar `α₀·I`.

**Proof sketch** (iter 187 addition): apply `py24_lemma_A_3` to X, Y
to extract their (a, b) and (p, q) eigenvalue pairs. Apply
`py24_lemma_A_6` (= HP A.12) to get the joint spectrum
`{a, b, p, q}` as a multiset. The hypothesis says this multiset
equals `{α₀, α₀, α₁, α₁}`. Multiset arithmetic + the fact that
unitary 2×2 with double eigenvalue is scalar gives the trichotomy.

**Proof status**: scaffolding stub. Tractable (uses only existing PY24
lemmas + multiset arithmetic + unitary-scalar fact). Renamed from
`paper_lemma_A_12_trichotomy` to clarify it is NOT HP A.12. -/
theorem joint_spec_multiplicity_trichotomy
    (X Y : Mat2) (hX : IsUnitary2 X) (hY : IsUnitary2 Y)
    (α₀ α₁ : ℂ)
    (_hα₀ : Complex.normSq α₀ = 1) (_hα₁ : Complex.normSq α₁ = 1)
    (h_joint_spec : ∃ W : Mat4, IsUnitary4 W ∧
      W.conjTranspose * (kron2 proj0 X + kron2 proj1 Y) * W =
        Matrix.diagonal ![α₀, α₀, α₁, α₁]) :
    (∃ Vx Vy : Mat2, IsUnitary2 Vx ∧ IsUnitary2 Vy ∧
      Vx.conjTranspose * X * Vx = Matrix.diagonal ![α₀, α₁] ∧
      Vy.conjTranspose * Y * Vy = Matrix.diagonal ![α₀, α₁]) ∨
    (X = Matrix.diagonal ![α₀, α₀] ∧ Y = Matrix.diagonal ![α₁, α₁]) ∨
    (X = Matrix.diagonal ![α₁, α₁] ∧ Y = Matrix.diagonal ![α₀, α₀]) := by
  -- ============================================================================
  -- PROOF STRUCTURE (mirrors paper page 10-11 derivation after Eq.(7)):
  --   Step (i)   [DONE]: spectral form of X via py24_lemma_A_3 (= HP A.2 for 2×2).
  --   Step (ii)  [DONE]: spectral form of Y similarly.
  --   Step (iii) [DONE]: combine via py24_lemma_A_6 (= HP A.12) — paper invokes
  --                      this exact lemma at the eigenvalue-equation step.
  --   Step (iv)  [SUB-SORRY]: use diag(a,b,p,q) ~ diag(α₀,α₀,α₁,α₁) (both via
  --              joint-spec witness + py24_lemma_A_6 output) ⟹
  --              {a, b, p, q} = {α₀, α₀, α₁, α₁} as multisets. The paper says
  --              this implicitly via "From the above and according to Lemma
  --              A.12, we have three cases".
  --   Step (v)   [SUB-SORRY]: trichotomy case-split — paper Cases (1)/(2)/(3).
  -- ============================================================================
  -- Step (i): apply HP A.2 to X (2×2 case = py24_lemma_A_3).
  obtain ⟨a, b, V_X, hV_X, hX_diag⟩ := py24_lemma_A_3 X hX
  -- Step (ii): apply HP A.2 to Y.
  obtain ⟨p, q, V_Y, hV_Y, hY_diag⟩ := py24_lemma_A_3 Y hY
  -- Derive |a|² = |b|² = 1 from unitarity of `V_X† · X · V_X`.
  have h_diag_X_unit : IsUnitary2 (Matrix.diagonal ![a, b]) := by
    rw [← hX_diag]
    exact isUnitary2_mul
      (isUnitary2_mul (isUnitary2_conjTranspose hV_X) hX) hV_X
  have h_diag_Y_unit : IsUnitary2 (Matrix.diagonal ![p, q]) := by
    rw [← hY_diag]
    exact isUnitary2_mul
      (isUnitary2_mul (isUnitary2_conjTranspose hV_Y) hY) hV_Y
  obtain ⟨ha, hb⟩ := diagonal_unitary_normSq a b h_diag_X_unit
  obtain ⟨hp, hq⟩ := diagonal_unitary_normSq p q h_diag_Y_unit
  -- Step (iii): apply HP A.12 (= py24_lemma_A_6) with the eigenvalue info on
  -- X and Y. This gives the joint diagonalization with explicit eigenvalues.
  -- Paper Eq.(7) eigenvalue argument: "Eigenvalues(|0⟩⟨0|⊗X + |1⟩⟨1|⊗Y) =
  -- Eigenvalues(X) ⊔ Eigenvalues(Y)" by Lemma A.12.
  have hX_eig_exists : ∃ V : Mat2, IsUnitary2 V ∧
      V.conjTranspose * X * V = Matrix.diagonal ![a, b] := ⟨V_X, hV_X, hX_diag⟩
  have hY_eig_exists : ∃ W : Mat2, IsUnitary2 W ∧
      W.conjTranspose * Y * W = Matrix.diagonal ![p, q] := ⟨V_Y, hV_Y, hY_diag⟩
  obtain ⟨U_joint, hU_joint, hU_joint_diag⟩ :=
    py24_lemma_A_6 X Y hX hY a b p q hX_eig_exists hY_eig_exists
  -- Now we have two unitary similarities:
  --   (1) U_joint† · M_joint · U_joint = diag(a, b, p, q) (from py24_lemma_A_6)
  --   (2) W†      · M_joint · W       = diag(α₀, α₀, α₁, α₁) (from hypothesis)
  -- where M_joint := kron2 proj0 X + kron2 proj1 Y.
  -- By transitivity: diag(a,b,p,q) is unitarily similar to diag(α₀,α₀,α₁,α₁),
  -- hence {a, b, p, q} = {α₀, α₀, α₁, α₁} as multisets.
  obtain ⟨W, hW_unit, hW_diag⟩ := h_joint_spec
  -- Step (iv): derive elementary symmetric polynomial equalities e_1..e_4
  -- between {a, b, p, q} and {α₀, α₀, α₁, α₁}, then apply existing helper
  -- `multiset_match_4_eq_pair_pair` to get each element ∈ {α₀, α₁}.
  set M : Mat4 := kron2 proj0 X + kron2 proj1 Y with hM_def
  -- Standard helper: rfl identities for cons access at indices 2, 3.
  have eabpq2 : (![a, b, p, q] : Fin 4 → ℂ) 2 = p := rfl
  have eabpq3 : (![a, b, p, q] : Fin 4 → ℂ) 3 = q := rfl
  have eα2 : (![α₀, α₀, α₁, α₁] : Fin 4 → ℂ) 2 = α₁ := rfl
  have eα3 : (![α₀, α₀, α₁, α₁] : Fin 4 → ℂ) 3 = α₁ := rfl
  -- (e_1): trace M = a+b+p+q (via U_joint) = 2α₀+2α₁ (via W).
  have h_e1 : a + b + p + q = 2 * α₀ + 2 * α₁ := by
    have hU : M.trace = a + b + p + q := by
      have h : (U_joint.conjTranspose * M * U_joint).trace = M.trace := by
        rw [Matrix.trace_mul_comm, ← mul_assoc, mul_eq_one_comm.mp hU_joint,
            Matrix.one_mul]
      rw [hU_joint_diag, Matrix.trace_diagonal, Fin.sum_univ_four] at h
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, eabpq2, eabpq3] at h
      linear_combination -h
    have hW : M.trace = 2 * α₀ + 2 * α₁ := by
      have h : (W.conjTranspose * M * W).trace = M.trace := by
        rw [Matrix.trace_mul_comm, ← mul_assoc, mul_eq_one_comm.mp hW_unit,
            Matrix.one_mul]
      rw [hW_diag, Matrix.trace_diagonal, Fin.sum_univ_four] at h
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, eα2, eα3] at h
      linear_combination -h
    linear_combination hW - hU
  -- Determinant helper.
  have h_det_inv : ∀ (V : Mat4), IsUnitary4 V → ∀ (N : Mat4),
      (V.conjTranspose * N * V).det = N.det := by
    intros V hV N
    rw [Matrix.det_mul, Matrix.det_mul]
    have h : V.conjTranspose.det * V.det = 1 := by
      rw [← Matrix.det_mul, hV, Matrix.det_one]
    linear_combination N.det * h
  -- (e_4): det M = a*b*p*q (via U_joint) = α₀²α₁² (via W).
  have h_e4 : a * b * p * q = α₀ * α₀ * α₁ * α₁ := by
    have hU : M.det = a * b * p * q := by
      have h := h_det_inv U_joint hU_joint M
      rw [hU_joint_diag, Matrix.det_diagonal, Fin.prod_univ_four] at h
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, eabpq2, eabpq3] at h
      linear_combination -h
    have hW : M.det = α₀ * α₀ * α₁ * α₁ := by
      have h := h_det_inv W hW_unit M
      rw [hW_diag, Matrix.det_diagonal, Fin.prod_univ_four] at h
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, eα2, eα3] at h
      linear_combination -h
    linear_combination hW - hU
  -- (e_2 power sum): trace(M²) gives a*a + b*b + p*p + q*q (one side) and
  -- 2α₀² + 2α₁² (other side).
  have h_e2_powersum : a*a + b*b + p*p + q*q = 2 * α₀ * α₀ + 2 * α₁ * α₁ := by
    have h_sq := trace_sq_eq_of_unitary_similar hU_joint hU_joint_diag
    have h_sq_W := trace_sq_eq_of_unitary_similar hW_unit hW_diag
    have hU : (M * M).trace = a*a + b*b + p*p + q*q := by
      rw [h_sq, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal,
          Fin.sum_univ_four]
      simp only [Pi.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
                 eabpq2, eabpq3]
    have hW : (M * M).trace = 2 * α₀ * α₀ + 2 * α₁ * α₁ := by
      rw [h_sq_W, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal,
          Fin.sum_univ_four]
      simp only [Pi.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
                 eα2, eα3]
      ring
    linear_combination hW - hU
  -- (e_2): from e_1 + e_2_powersum via Newton identity.
  -- e_2 of {α₀,α₀,α₁,α₁} = α₀² + 4α₀α₁ + α₁².
  have h_e2 : a*b + a*p + a*q + b*p + b*q + p*q
            = α₀*α₀ + 4*α₀*α₁ + α₁*α₁ := by
    linear_combination
      ((a + b + p + q + 2*α₀ + 2*α₁) / 2) * h_e1 + (-1/2) * h_e2_powersum
  -- (e_3 power sum): trace(M³).
  have h_e3_powersum : a*a*a + b*b*b + p*p*p + q*q*q
                     = 2*α₀*α₀*α₀ + 2*α₁*α₁*α₁ := by
    have h_cu := trace_cube_eq_of_unitary_similar hU_joint hU_joint_diag
    have h_cu_W := trace_cube_eq_of_unitary_similar hW_unit hW_diag
    have hU : (M * M * M).trace = a*a*a + b*b*b + p*p*p + q*q*q := by
      rw [h_cu, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
          Matrix.trace_diagonal, Fin.sum_univ_four]
      simp only [Pi.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
                 eabpq2, eabpq3]
    have hW : (M * M * M).trace = 2*α₀*α₀*α₀ + 2*α₁*α₁*α₁ := by
      rw [h_cu_W, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
          Matrix.trace_diagonal, Fin.sum_univ_four]
      simp only [Pi.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
                 eα2, eα3]
      ring
    linear_combination hW - hU
  -- (e_3): from e_1 + e_2 + e_2_powersum + e_3_powersum via Newton.
  -- e_3 of {α₀,α₀,α₁,α₁} = 2α₀α₁(α₀+α₁).
  have h_e3 : a*b*p + a*b*q + a*p*q + b*p*q = 2*α₀*α₁*(α₀+α₁) := by
    linear_combination (1/3) * h_e3_powersum
      + (-(a+b+p+q)/3) * h_e2_powersum
      + ((a+b+p+q)/3) * h_e2
      + ((-α₀*α₀ + 4*α₀*α₁ - α₁*α₁)/3) * h_e1
  -- Adjust forms for multiset_match_4_eq_pair_pair (which uses c^2, d^2, c^2*d^2).
  have h_e1' : a + b + p + q = 2 * α₀ + 2 * α₁ := h_e1
  have h_e2' : a*b + a*p + a*q + b*p + b*q + p*q
             = α₀^2 + 4*α₀*α₁ + α₁^2 := by
    linear_combination h_e2
  have h_e3' : a*b*p + a*b*q + a*p*q + b*p*q = 2*α₀*α₁*(α₀+α₁) := h_e3
  have h_e4' : a * b * p * q = α₀^2 * α₁^2 := by
    linear_combination h_e4
  -- Apply multiset_match_4_eq_pair_pair with (c, d) = (α₀, α₁).
  obtain ⟨h_a_disj, h_b_disj, h_p_disj, h_q_disj⟩ :=
    multiset_match_4_eq_pair_pair h_e1' h_e2' h_e3' h_e4'
  -- =================== Step (v): trichotomy case-split ======================
  -- At this point, every variable a, b, p, q ∈ {α₀, α₁}. The disjunction
  -- conclusion follows by case-split on h_a_disj × h_b_disj × h_p_disj × h_q_disj.
  --
  -- BLOCKER for Step (v): the 16-way case-split needs:
  -- (a) a helper "unitary × diag(α,α) × unitary† = α · I = diag(α,α)" for
  --     the scalar cases (4 of 16 sub-cases).
  -- (b) a witness construction "V_X · pauliX" to swap eigenvalue order in the
  --     mixed cases (8 of 16 sub-cases).
  -- (c) contradiction derivation for the impossible cases using h_e1 + h_e4
  --     (4 of 16 sub-cases when α₀ ≠ α₁).
  -- Each sub-case is ~10-20 lines. Total ~150-300 lines remaining.
  -- Step v case-split skeleton (iter 191): rcases on (h_a_disj, h_b_disj) gives 4 cases.
  rcases h_a_disj with ha | ha <;> rcases h_b_disj with hb | hb
  · -- Case 1: a = α₀, b = α₀ → X = diag(α₀, α₀); p = q = α₁ → Y = diag(α₁, α₁). Right.Left.
    right; left
    -- Derive p = α₁ and q = α₁ from h_e1, h_e4, h_p_disj, h_q_disj, ha, hb.
    have hα₀sq_ne : α₀ * α₀ ≠ 0 := by
      intro habs
      have hα₀_zero : α₀ = 0 := by
        rcases mul_eq_zero.mp habs with h | h <;> exact h
      rw [hα₀_zero] at _hα₀
      simp at _hα₀
    have h_sum_pq : p + q = 2 * α₁ := by linear_combination h_e1 - ha - hb
    have h_prod_pq : p * q = α₁ * α₁ := by
      have h_factor : α₀ * α₀ * (p * q) = α₀ * α₀ * (α₁ * α₁) := by
        have hab : a * b = α₀ * α₀ := by rw [ha, hb]
        linear_combination h_e4 - (p * q) * hab
      exact mul_left_cancel₀ hα₀sq_ne h_factor
    have h_diff_sum : (p - α₁) + (q - α₁) = 0 := by linear_combination h_sum_pq
    have h_diff_prod : (p - α₁) * (q - α₁) = 0 := by
      linear_combination h_prod_pq - α₁ * h_sum_pq
    have h_pq_eq : p = α₁ ∧ q = α₁ := by
      rcases mul_eq_zero.mp h_diff_prod with hp_zero | hq_zero
      · refine ⟨by linear_combination hp_zero,
                by linear_combination h_diff_sum - hp_zero⟩
      · refine ⟨by linear_combination h_diff_sum - hq_zero,
                by linear_combination hq_zero⟩
    refine ⟨?_, ?_⟩
    · -- X = diag(α₀, α₀)
      apply scalar_eq_of_unitary_conj_mat2 V_X hV_X X α₀
      rw [hX_diag, ha, hb]
    · -- Y = diag(α₁, α₁)
      apply scalar_eq_of_unitary_conj_mat2 V_Y hV_Y Y α₁
      rw [hY_diag, h_pq_eq.1, h_pq_eq.2]
  · -- Case 2: a = α₀, b = α₁ mixed. V_X works as Vx witness; (p, q) ∈ {α₀, α₁}². Left.
    left
    -- ha : a = α₀, hb : b = α₁ mixed. V_X is Vx witness; case-split on h_p_disj for Vy.
    rcases h_p_disj with hp_eq | hp_eq
    · -- p = α₀: then q = α₁, V_Y works as Vy.
      have hq_eq : q = α₁ := by linear_combination h_e1 - ha - hb - hp_eq
      refine ⟨V_X, V_Y, hV_X, hV_Y, ?_, ?_⟩
      · rw [hX_diag, ha, hb]
      · rw [hY_diag, hp_eq, hq_eq]
    · -- p = α₁: then q = α₀, Vy = V_Y · pauliX swaps eigenvalues.
      have hq_eq : q = α₀ := by linear_combination h_e1 - ha - hb - hp_eq
      have hVy_unit : IsUnitary2 (V_Y * pauliX) :=
        isUnitary2_mul hV_Y isUnitary2_pauliX
      have h_pauliX_sa : pauliX.conjTranspose = pauliX := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [pauliX, Matrix.conjTranspose_apply, Matrix.of_apply]
      refine ⟨V_X, V_Y * pauliX, hV_X, hVy_unit, ?_, ?_⟩
      · rw [hX_diag, ha, hb]
      · calc (V_Y * pauliX).conjTranspose * Y * (V_Y * pauliX)
            = pauliX.conjTranspose * (V_Y.conjTranspose * Y * V_Y) * pauliX := by
              rw [Matrix.conjTranspose_mul]; noncomm_ring
          _ = pauliX * (V_Y.conjTranspose * Y * V_Y) * pauliX := by rw [h_pauliX_sa]
          _ = pauliX * Matrix.diagonal ![p, q] * pauliX := by rw [hY_diag]
          _ = pauliX * Matrix.diagonal ![α₁, α₀] * pauliX := by rw [hp_eq, hq_eq]
          _ = Matrix.diagonal ![α₀, α₁] := pauliX_diag_pauliX_swap α₁ α₀
  · -- Case 3: a = α₁, b = α₀ mixed. Vx = V_X · pauliX swaps eigenvalues.
    left
    have h_pauliX_sa : pauliX.conjTranspose = pauliX := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [pauliX, Matrix.conjTranspose_apply, Matrix.of_apply]
    have hVx_unit : IsUnitary2 (V_X * pauliX) :=
      isUnitary2_mul hV_X isUnitary2_pauliX
    rcases h_p_disj with hp_eq | hp_eq
    · -- p = α₀: q = α₁, Vy = V_Y.
      have hq_eq : q = α₁ := by linear_combination h_e1 - ha - hb - hp_eq
      refine ⟨V_X * pauliX, V_Y, hVx_unit, hV_Y, ?_, ?_⟩
      · calc (V_X * pauliX).conjTranspose * X * (V_X * pauliX)
            = pauliX.conjTranspose * (V_X.conjTranspose * X * V_X) * pauliX := by
              rw [Matrix.conjTranspose_mul]; noncomm_ring
          _ = pauliX * (V_X.conjTranspose * X * V_X) * pauliX := by rw [h_pauliX_sa]
          _ = pauliX * Matrix.diagonal ![a, b] * pauliX := by rw [hX_diag]
          _ = pauliX * Matrix.diagonal ![α₁, α₀] * pauliX := by rw [ha, hb]
          _ = Matrix.diagonal ![α₀, α₁] := pauliX_diag_pauliX_swap α₁ α₀
      · rw [hY_diag, hp_eq, hq_eq]
    · -- p = α₁: q = α₀, Vy = V_Y · pauliX.
      have hq_eq : q = α₀ := by linear_combination h_e1 - ha - hb - hp_eq
      have hVy_unit : IsUnitary2 (V_Y * pauliX) :=
        isUnitary2_mul hV_Y isUnitary2_pauliX
      refine ⟨V_X * pauliX, V_Y * pauliX, hVx_unit, hVy_unit, ?_, ?_⟩
      · calc (V_X * pauliX).conjTranspose * X * (V_X * pauliX)
            = pauliX.conjTranspose * (V_X.conjTranspose * X * V_X) * pauliX := by
              rw [Matrix.conjTranspose_mul]; noncomm_ring
          _ = pauliX * (V_X.conjTranspose * X * V_X) * pauliX := by rw [h_pauliX_sa]
          _ = pauliX * Matrix.diagonal ![a, b] * pauliX := by rw [hX_diag]
          _ = pauliX * Matrix.diagonal ![α₁, α₀] * pauliX := by rw [ha, hb]
          _ = Matrix.diagonal ![α₀, α₁] := pauliX_diag_pauliX_swap α₁ α₀
      · calc (V_Y * pauliX).conjTranspose * Y * (V_Y * pauliX)
            = pauliX.conjTranspose * (V_Y.conjTranspose * Y * V_Y) * pauliX := by
              rw [Matrix.conjTranspose_mul]; noncomm_ring
          _ = pauliX * (V_Y.conjTranspose * Y * V_Y) * pauliX := by rw [h_pauliX_sa]
          _ = pauliX * Matrix.diagonal ![p, q] * pauliX := by rw [hY_diag]
          _ = pauliX * Matrix.diagonal ![α₁, α₀] * pauliX := by rw [hp_eq, hq_eq]
          _ = Matrix.diagonal ![α₀, α₁] := pauliX_diag_pauliX_swap α₁ α₀
  · -- Case 4: a = α₁, b = α₁ → X = diag(α₁, α₁); Y = diag(α₀, α₀). Right.Right.
    right; right
    -- Derive p = α₀ and q = α₀ via mirror of Case 1 (swap α₀ ↔ α₁ roles).
    have hα₁sq_ne : α₁ * α₁ ≠ 0 := by
      intro habs
      have hα₁_zero : α₁ = 0 := by
        rcases mul_eq_zero.mp habs with h | h <;> exact h
      rw [hα₁_zero] at _hα₁
      simp at _hα₁
    have h_sum_pq : p + q = 2 * α₀ := by linear_combination h_e1 - ha - hb
    have h_prod_pq : p * q = α₀ * α₀ := by
      have h_factor : α₁ * α₁ * (p * q) = α₁ * α₁ * (α₀ * α₀) := by
        have hab : a * b = α₁ * α₁ := by rw [ha, hb]
        linear_combination h_e4 - (p * q) * hab
      exact mul_left_cancel₀ hα₁sq_ne h_factor
    have h_diff_sum : (p - α₀) + (q - α₀) = 0 := by linear_combination h_sum_pq
    have h_diff_prod : (p - α₀) * (q - α₀) = 0 := by
      linear_combination h_prod_pq - α₀ * h_sum_pq
    have h_pq_eq : p = α₀ ∧ q = α₀ := by
      rcases mul_eq_zero.mp h_diff_prod with hp_zero | hq_zero
      · refine ⟨by linear_combination hp_zero,
                by linear_combination h_diff_sum - hp_zero⟩
      · refine ⟨by linear_combination h_diff_sum - hq_zero,
                by linear_combination hq_zero⟩
    refine ⟨?_, ?_⟩
    · apply scalar_eq_of_unitary_conj_mat2 V_X hV_X X α₁
      rw [hX_diag, ha, hb]
    · apply scalar_eq_of_unitary_conj_mat2 V_Y hV_Y Y α₀
      rw [hY_diag, h_pq_eq.1, h_pq_eq.2]

/-! ## Helper: D₀ = block00 of a diagonal Mat8 is unitary

Lemma 4.4's Eq.16 derivation needs `D₀ := block00 Dg.toMatrix` to be a
unitary Mat4 (to build `V₄ := W₅ · D₀† · W₁` in step5_case_ii dispatch).
This follows directly from `block_diag_A_blocks_unitary` since `Dg.toMatrix`
is diagonal hence block-diag-A. -/

/-- `block00` of a `DiagGate3`'s matrix is unitary. -/
lemma diagGate3_block00_unitary (Dg : DiagGate3) :
    IsUnitary4 (block00 Dg.toMatrix) :=
  (block_diag_A_blocks_unitary Dg.toMatrix_unitary
    (isDiag8_block01 _ ⟨Dg, rfl⟩) (isDiag8_block10 _ ⟨Dg, rfl⟩)).1

/-- `block11` of a `DiagGate3`'s matrix is unitary. -/
lemma diagGate3_block11_unitary (Dg : DiagGate3) :
    IsUnitary4 (block11 Dg.toMatrix) :=
  (block_diag_A_blocks_unitary Dg.toMatrix_unitary
    (isDiag8_block01 _ ⟨Dg, rfl⟩) (isDiag8_block10 _ ⟨Dg, rfl⟩)).2

/-! ## Helper: embedAC commutes with B-only single-qubit layer

For the Lemma A.7 absorption step of `paper_lemma_4_2`: the spectral
decomposition of U₃ produces `kron2 V 1` factors on either side, which
must be moved past adjacent `embedAC` factors. Since `embedBC (kron2 V 1)`
acts as `V` on B only (identity on A,C) — equivalently `singleQubitLayer I₂ V I₂`
— it commutes with any `embedAC X` (which is identity on B). -/

set_option maxHeartbeats 800000 in
-- Heartbeat bump: this proof uses `fin_cases × fin_cases` on Fin 8 × Fin 8
-- (64 cases) plus simp on Matrix.mul_apply + Fin.sum_univ_eight, exceeding
-- the default heartbeat budget.
/-- `embedAC X` commutes with the "V on B only" layer. -/
theorem embedAC_commutes_B_only (X : Mat4) (V : Mat2) :
    embedAC X * embedBC (kron2 V 1) =
    embedBC (kron2 V 1) * embedAC X := by
  rw [embedBC_kron2]
  change embedAC X * singleQubitLayer I₂ V I₂ =
       singleQubitLayer I₂ V I₂ * embedAC X
  ext i j
  simp only [singleQubitLayer, kron3, embedAC, I₂, decode3,
             Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply,
             Fin.sum_univ_eight]
  fin_cases i <;> fin_cases j <;>
    (simp; ring)

/-! ## Helper: block-diag-B → V·Diag·V† spectral form (paper Lemma A.5-style)

A block-diag-B unitary `kron2 1 proj0 + kron2 P proj1` decomposes via the
spectral theorem applied to P (PY24 A.3): P = V·Diag(d₀, d₁)·V†, giving:
  `kron2 1 proj0 + kron2 P proj1 =
    (kron2 V 1) · (kron2 1 proj0 + kron2 (Diag(d₀,d₁)) proj1) · (kron2 V† 1)`
i.e., the controlled-action factor becomes a *diagonal-when-controlled* gate
sandwiched by single-qubit V/V† layers. This is the algebraic content of
paper Lemma A.5 used in Lemma 4.2's Step 1. -/
lemma blockDiagB_spectral (P : Mat2) (hP : IsUnitary2 P) :
    ∃ V : Mat2, ∃ d₀ d₁ : ℂ, IsUnitary2 V ∧
      Complex.normSq d₀ = 1 ∧ Complex.normSq d₁ = 1 ∧
      kron2 1 proj0 + kron2 P proj1 =
      (kron2 V 1) *
        (kron2 1 proj0 + kron2 (Matrix.diagonal ![d₀, d₁]) proj1) *
        (kron2 V.conjTranspose 1) := by
  obtain ⟨d₀, d₁, V, hV, hVPV⟩ := py24_lemma_A_3 P hP
  -- hVPV : V† · P · V = Diag(d₀, d₁), so P = V · Diag · V†.
  have hVV_right : V * V.conjTranspose = 1 := mul_eq_one_comm.mp hV
  have hP_eq : P = V * Matrix.diagonal ![d₀, d₁] * V.conjTranspose := by
    calc P = 1 * P * 1 := by rw [one_mul, mul_one]
      _ = V * V.conjTranspose * P * (V * V.conjTranspose) := by rw [hVV_right]
      _ = V * (V.conjTranspose * P * V) * V.conjTranspose := by noncomm_ring
      _ = V * Matrix.diagonal ![d₀, d₁] * V.conjTranspose := by rw [hVPV]
  -- Derive unit modulus of d₀, d₁ from `V† · P · V = Diag(d₀, d₁)` unitarity.
  have h_diag_unit : IsUnitary2 (Matrix.diagonal ![d₀, d₁]) := by
    rw [← hVPV]
    have hVdag_unit : IsUnitary2 V.conjTranspose := isUnitary2_conjTranspose hV
    exact isUnitary2_mul (isUnitary2_mul hVdag_unit hP) hV
  obtain ⟨hd₀, hd₁⟩ := diagonal_unitary_normSq d₀ d₁ h_diag_unit
  refine ⟨V, d₀, d₁, hV, hd₀, hd₁, ?_⟩
  calc kron2 1 proj0 + kron2 P proj1
      = kron2 (V * V.conjTranspose) proj0 + kron2 P proj1 := by rw [hVV_right]
    _ = kron2 (V * V.conjTranspose) proj0 +
          kron2 (V * Matrix.diagonal ![d₀, d₁] * V.conjTranspose) proj1 := by
            rw [← hP_eq]
    _ = (kron2 V 1) * (kron2 1 proj0) * (kron2 V.conjTranspose 1) +
        (kron2 V 1) * (kron2 (Matrix.diagonal ![d₀, d₁]) proj1) *
          (kron2 V.conjTranspose 1) := by
        simp only [kron2_mul, mul_one, one_mul]
    _ = (kron2 V 1) *
        ((kron2 1 proj0) + (kron2 (Matrix.diagonal ![d₀, d₁]) proj1)) *
        (kron2 V.conjTranspose 1) := by noncomm_ring

/-- **Iter 1032: NORMALIZED block-diag-B spectral form** (paper Lemma A.5 with
    the paper's determinant-style normalization restored).

    Strengthens `blockDiagB_spectral` by splitting off the C-only phase gate
    `kron2 1 C` (with `C = Diag(1, d₀)`), leaving a middle gate whose FIRST
    branch is the identity: `Diag(1, 1, 1, e)` with `e = d₁·conj d₀`.

    Packaged alternative to `blockDiagB_spectral` for callers that want the
    normalization up front. `paper_lemma_4_2` currently applies
    `blockDiagB_diag_normalize` inline instead (it needs the un-normalized `V`
    for `W₁`/`W₅` anyway), so this lemma is presently unused — kept because any
    new consumer of a block-diag-B middle gate needs exactly this form: the
    un-normalized one makes the paper Eq.(6) joint-spectrum claim FALSE (see
    `joint_spec_general_form_false`), the true spectrum being `(1, 1, e, e)`. -/
lemma blockDiagB_spectral_normalized (P : Mat2) (hP : IsUnitary2 P) :
    ∃ V C : Mat2, ∃ e : ℂ, IsUnitary2 V ∧ IsUnitary2 C ∧ Complex.normSq e = 1 ∧
      kron2 1 proj0 + kron2 P proj1 =
      (kron2 V 1) * (kron2 1 C) *
        (kron2 1 proj0 + kron2 (Matrix.diagonal ![1, e]) proj1) *
        (kron2 V.conjTranspose 1) := by
  obtain ⟨V, d₀, d₁, hV, hd₀, hd₁, hspec⟩ := blockDiagB_spectral P hP
  refine ⟨V, Matrix.diagonal ![1, d₀], d₁ * starRingEnd ℂ d₀, hV,
    isUnitary2_diag_one_u d₀ hd₀, ?_, ?_⟩
  · rw [Complex.normSq_mul, Complex.normSq_conj, hd₁, hd₀]; norm_num
  · rw [hspec, blockDiagB_diag_normalize d₀ d₁ hd₀]; noncomm_ring

/-! ## Helper: block-diag-A spectral form (mirror of `blockDiagB_spectral`)

A block-diag-A unitary `kron2 proj0 1 + kron2 proj1 P` (A-controlled, acting
on the second qubit) decomposes via the spectral theorem on P:
  `kron2 proj0 1 + kron2 proj1 P =
    (kron2 1 V) · (kron2 proj0 1 + kron2 proj1 (Diag(d₀,d₁))) · (kron2 1 V†)`
This is the A-controlled mirror of `blockDiagB_spectral`, used in
`paper_lemma_4_1`'s Fig.6 algebra to unfold each `C(M)` / `C(N)` factor. -/
lemma blockDiagA_spectral (P : Mat2) (hP : IsUnitary2 P) :
    ∃ V : Mat2, ∃ d₀ d₁ : ℂ, IsUnitary2 V ∧
      Complex.normSq d₀ = 1 ∧ Complex.normSq d₁ = 1 ∧
      kron2 proj0 1 + kron2 proj1 P =
      (kron2 1 V) *
        (kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![d₀, d₁])) *
        (kron2 1 V.conjTranspose) := by
  obtain ⟨d₀, d₁, V, hV, hVPV⟩ := py24_lemma_A_3 P hP
  have hVV_right : V * V.conjTranspose = 1 := mul_eq_one_comm.mp hV
  have hP_eq : P = V * Matrix.diagonal ![d₀, d₁] * V.conjTranspose := by
    calc P = 1 * P * 1 := by rw [one_mul, mul_one]
      _ = V * V.conjTranspose * P * (V * V.conjTranspose) := by rw [hVV_right]
      _ = V * (V.conjTranspose * P * V) * V.conjTranspose := by noncomm_ring
      _ = V * Matrix.diagonal ![d₀, d₁] * V.conjTranspose := by rw [hVPV]
  have h_diag_unit : IsUnitary2 (Matrix.diagonal ![d₀, d₁]) := by
    rw [← hVPV]
    have hVdag_unit : IsUnitary2 V.conjTranspose := isUnitary2_conjTranspose hV
    exact isUnitary2_mul (isUnitary2_mul hVdag_unit hP) hV
  obtain ⟨hd₀, hd₁⟩ := diagonal_unitary_normSq d₀ d₁ h_diag_unit
  refine ⟨V, d₀, d₁, hV, hd₀, hd₁, ?_⟩
  calc kron2 proj0 1 + kron2 proj1 P
      = kron2 proj0 (V * V.conjTranspose) + kron2 proj1 P := by rw [hVV_right]
    _ = kron2 proj0 (V * V.conjTranspose) +
          kron2 proj1 (V * Matrix.diagonal ![d₀, d₁] * V.conjTranspose) := by
            rw [← hP_eq]
    _ = (kron2 1 V) * (kron2 proj0 1) * (kron2 1 V.conjTranspose) +
        (kron2 1 V) * (kron2 proj1 (Matrix.diagonal ![d₀, d₁])) *
          (kron2 1 V.conjTranspose) := by
        simp only [kron2_mul, mul_one, one_mul]
    _ = (kron2 1 V) *
        ((kron2 proj0 1) + (kron2 proj1 (Matrix.diagonal ![d₀, d₁]))) *
        (kron2 1 V.conjTranspose) := by noncomm_ring

/-! ## Helper: controlled-A → C(M)·(I⊗P₀) factorization (paper Lemma A.7-style)

A controlled-A 2-qubit unitary `kron2 proj0 P₀ + kron2 proj1 P₁` factors as a
canonical-controlled `kron2 proj0 1 + kron2 proj1 M` (with M = P₁·P₀†) acting
after a "second-qubit-only" prefactor `kron2 1 P₀`. This is the algebraic
content of paper Lemma A.7 used in Lemma 4.3's third step. -/

/-- Controlled-A factorization: `U₂ = C(M) · (1⊗P₀)` where `M = P₁P₀†`. -/
lemma controlled_a_factor (P₀ P₁ : Mat2) (hP₀ : IsUnitary2 P₀) :
    kron2 proj0 P₀ + kron2 proj1 P₁ =
    (kron2 proj0 1 + kron2 proj1 (P₁ * P₀.conjTranspose)) * (kron2 1 P₀) := by
  simp only [add_mul, kron2_mul, mul_one, one_mul]
  congr 2
  rw [mul_assoc, hP₀, mul_one]

/-! ## Helper: BC-block-diag-second commutes with AC-controlled-diag (Step 5c of paper_lemma_4_1)

Used in paper Fig.6 row 6 (Lemma 4.1's "key calculation" Step 6): after
applying Paige-Wei + SWAP-conjugation to W_3, the outer factors M, N are
block-diag-second w.r.t. C (slot 2 has projectors). These commute with
embedAC C(R_z(α)) on AC because C(R_z) is diagonal in C's basis — so its
phase action commutes with M's action on B (which is keyed off C's basis
label but doesn't change it). Extracted as a top-level lemma to avoid
heartbeat blow-up when used inside `paper_lemma_4_1`'s large proof context. -/

set_option maxHeartbeats 800000 in
lemma embedBC_blockdiagsec_comm_embedAC_Cdiag
    (α₀ α₁ : ℂ) (Xₘ Yₘ : Mat2) :
    embedBC (kron2 Xₘ proj0 + kron2 Yₘ proj1) *
      embedAC (kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![α₀, α₁])) =
    embedAC (kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![α₀, α₁])) *
      embedBC (kron2 Xₘ proj0 + kron2 Yₘ proj1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedBC, embedAC, kron2, proj0, proj1, decode3, Matrix.diagonal,
          Matrix.mul_apply, Matrix.add_apply, Matrix.of_apply,
          Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

/-! ## HP Appendix A — missing paper-faithful lemma stubs (iter 188)

The following stubs match paper-named HP Appendix A lemmas that were
missing from the codebase. Each maps directly to a specific paper claim
from `3787463.pdf` Appendix A "Known Lemmas". HP A.1, A.2, A.7-A.17 are
already covered by existing helpers (`commutes_ZI_implies_blockDiagFirst`,
`py24_lemma_A_3`, `controlled_a_factor`, PY24 lemmas — see HP→PY24
mapping at top of [PY24/Lemmas.lean](../PY24/Lemmas.lean)).

These four are NEW essentials needed for proof completeness. -/

/-- **HP paper Lemma A.3** (page 26, Fig. for A.3; controlled spectral theorem).
    For a 1-qubit gate V, controlled-V decomposes into an *uncontrolled*
    P on the target qubit, then controlled-Diag, then *uncontrolled* P†
    on the target qubit. The first and last factors carry NO control —
    only the middle `C(Diag)` is controlled. This matches the figure on
    paper page 26 and is the cost-aware form actually used downstream.

    **Convention note — matrix product order vs circuit order**:
    The paper's figure draws (left to right) `P†, Diag, P`. That is
    *circuit order* — read left to right as "applied first to last":
    P† first, then C(Diag), then P last. The corresponding *matrix
    product* expression — which is what we write in Lean — REVERSES
    that order, because the rightmost factor of a matrix product acts
    first on a state. So matrix-product order is `P · C(Diag) · P†`
    with P leftmost (= chronologically LAST) and P† rightmost
    (= chronologically FIRST). Lemma A.2's text equation `P† V P = Diag`
    confirms this: V = P · Diag · P† has P leftmost in matrix product.

    This matches the existing helper `blockDiagA_spectral` exactly:
    the diagonalizing unitary V is leftmost, V.conjTranspose rightmost.

    Provable from `py24_lemma_A_3` (HP A.2 for 2×2 case) + the
    `blockDiagA_spectral` algebra.

    **Proof status**: scaffolding stub (proof mirrors `blockDiagA_spectral`,
    ~30 lines). -/
theorem paper_lemma_A_3 (V : Mat2) (_hV : IsUnitary2 V) :
    ∃ d₀ d₁ : ℂ, ∃ P : Mat2, IsUnitary2 P ∧
      Complex.normSq d₀ = 1 ∧ Complex.normSq d₁ = 1 ∧
      kron2 proj0 1 + kron2 proj1 V =
        (kron2 1 P) *
        (kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![d₀, d₁])) *
        (kron2 1 P.conjTranspose) := by
  -- Closed iter 1044: this IS the 2×2 spectral theorem, conjugated into the
  -- controlled block. `py24_lemma_A_3` supplies `W† V W = Diag(a,b)`; the
  -- controlled form then follows because
  -- `(1⊗W)(proj0⊗1 + proj1⊗D)(1⊗W†) = proj0⊗(WW†) + proj1⊗(W D W†)`.
  obtain ⟨a, b, W, hW, hWeq⟩ := py24_lemma_A_3 V _hV
  have hWWc : W * W.conjTranspose = 1 := mul_eq_one_comm.mp hW
  have hD : IsUnitary2 (Matrix.diagonal ![a, b]) := by
    rw [← hWeq]
    exact isUnitary2_mul (isUnitary2_mul (isUnitary2_conjTranspose hW) _hV) hW
  have hna : Complex.normSq a = 1 := by
    have h := congrArg (fun M => M 0 0) hD
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
               Matrix.one_apply, Fin.sum_univ_two] at h
    have h2 : (Complex.normSq a : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]; simpa using h
    exact_mod_cast h2
  have hnb : Complex.normSq b = 1 := by
    have h := congrArg (fun M => M 1 1) hD
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
               Matrix.one_apply, Fin.sum_univ_two] at h
    have h2 : (Complex.normSq b : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]; simpa using h
    exact_mod_cast h2
  have hVeq : V = W * Matrix.diagonal ![a, b] * W.conjTranspose := by
    rw [← hWeq,
        show W * (W.conjTranspose * V * W) * W.conjTranspose
          = (W * W.conjTranspose) * V * (W * W.conjTranspose) from by noncomm_ring,
        hWWc, one_mul, mul_one]
  refine ⟨a, b, W, hW, hna, hnb, ?_⟩
  rw [hVeq]
  conv_lhs => rw [show (1 : Mat2) = W * W.conjTranspose from hWWc.symm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kron2, proj0, proj1, Matrix.mul_apply, Matrix.add_apply, Matrix.of_apply,
          Matrix.diagonal_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
          Fin.sum_univ_four, Fin.sum_univ_two]

/-! ### Cosine-sine decomposition infrastructure (iter 1045)

Everything below supports `paper_lemma_A_4`, which IS the cosine-sine
decomposition of a 4×4 unitary (Mathlib has no CSD). The three moving parts are
`blk4` (2×2-block algebra on `Mat4`), `mat2_polar_cols`/`mat2_polar_rows` (a 2×2
matrix whose Gram matrix is a real nonneg diagonal square is a unitary times that
diagonal — including the degenerate branches where a singular value vanishes), and
`m11_forced_diagonal` (unitarity forces the LAST block of the middle factor to be
diagonal once the other three are). -/

/-- Assemble a 4x4 matrix from four 2x2 blocks (block index = qubit 1). -/
def blk4 (A B C D : Mat2) : Mat4 :=
  Matrix.of ![![A 0 0, A 0 1, B 0 0, B 0 1],
              ![A 1 0, A 1 1, B 1 0, B 1 1],
              ![C 0 0, C 0 1, D 0 0, D 0 1],
              ![C 1 0, C 1 1, D 1 0, D 1 1]]

/-- Every `Mat4` is the `blk4` assembly of its own four 2x2 blocks. -/
lemma blk4_self (V : Mat4) :
    V = blk4 (Matrix.of !![V 0 0, V 0 1; V 1 0, V 1 1])
             (Matrix.of !![V 0 2, V 0 3; V 1 2, V 1 3])
             (Matrix.of !![V 2 0, V 2 1; V 3 0, V 3 1])
             (Matrix.of !![V 2 2, V 2 3; V 3 2, V 3 3]) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk4]

/-- Block multiplication: `blk4` multiplies like a 2x2 matrix of 2x2 blocks. -/
lemma blk4_mul (A B C D A' B' C' D' : Mat2) :
    blk4 A B C D * blk4 A' B' C' D'
      = blk4 (A*A' + B*C') (A*B' + B*D') (C*A' + D*C') (C*B' + D*D') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk4, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
          Fin.sum_univ_two] <;> ring

/-- Conjugate transpose of a block matrix transposes the block pattern. -/
lemma blk4_conjTranspose (A B C D : Mat2) :
    (blk4 A B C D)ᴴ = blk4 Aᴴ Cᴴ Bᴴ Dᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk4, Matrix.conjTranspose_apply]

/-- The identity in block form. -/
lemma blk4_one : (1 : Mat4) = blk4 1 0 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk4]

/-- Blocks of a blk4 are recoverable, so blk4 is injective. -/
lemma blk4_inj {A B C D A' B' C' D' : Mat2} (h : blk4 A B C D = blk4 A' B' C' D') :
    A = A' ∧ B = B' ∧ C = C' ∧ D = D' := by
  have e : ∀ i j : Fin 4, blk4 A B C D i j = blk4 A' B' C' D' i j := by
    intro i j; rw [h]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j
  · simpa [blk4] using e 0 0
  · simpa [blk4] using e 0 1
  · simpa [blk4] using e 1 0
  · simpa [blk4] using e 1 1
  · simpa [blk4] using e 0 2
  · simpa [blk4] using e 0 3
  · simpa [blk4] using e 1 2
  · simpa [blk4] using e 1 3
  · simpa [blk4] using e 2 0
  · simpa [blk4] using e 2 1
  · simpa [blk4] using e 3 0
  · simpa [blk4] using e 3 1
  · simpa [blk4] using e 2 2
  · simpa [blk4] using e 2 3
  · simpa [blk4] using e 3 2
  · simpa [blk4] using e 3 3

/-- A block-diag-FIRST gate in block form. -/
lemma kron2_blockdiagfirst_eq_blk4 (X Y : Mat2) :
    kron2 proj0 X + kron2 proj1 Y = blk4 X 0 0 Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk4, kron2, proj0, proj1, Matrix.add_apply]

/-- A block-diag-SECOND gate has all four blocks diagonal, and conversely. -/
lemma blk4_diags_eq_kron2_blockdiagsecond (a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : ℂ) :
    blk4 (Matrix.diagonal ![a₀, a₁]) (Matrix.diagonal ![b₀, b₁])
         (Matrix.diagonal ![c₀, c₁]) (Matrix.diagonal ![d₀, d₁])
      = kron2 (Matrix.of !![a₀, b₀; c₀, d₀]) proj0
        + kron2 (Matrix.of !![a₁, b₁; c₁, d₁]) proj1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk4, kron2, proj0, proj1, Matrix.add_apply]

/-- Unitarity of a block-diag-second gate is componentwise. -/
lemma isUnitary2_of_blockdiagsecond {R₀ R₁ : Mat2}
    (h : IsUnitary4 (kron2 R₀ proj0 + kron2 R₁ proj1)) :
    IsUnitary2 R₀ ∧ IsUnitary2 R₁ := by
  have e : ∀ i j : Fin 4,
      ((kron2 R₀ proj0 + kron2 R₁ proj1)ᴴ * (kron2 R₀ proj0 + kron2 R₁ proj1)) i j
        = (1 : Mat4) i j := by
    intro i j; rw [h]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.add_apply,
    kron2, proj0, proj1, Matrix.of_apply, Matrix.one_apply, Fin.sum_univ_four] at e
  refine ⟨?_, ?_⟩
  · change R₀ᴴ * R₀ = (1 : Mat2)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
        Fin.sum_univ_two]
    · simpa using e 0 0
    · simpa using e 0 2
    · simpa using e 2 0
    · simpa using e 2 2
  · change R₁ᴴ * R₁ = (1 : Mat2)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
        Fin.sum_univ_two]
    · simpa using e 1 1
    · simpa using e 1 3
    · simpa using e 3 1
    · simpa using e 3 3

/-- If a sum of two Hermitian squares `conj a * a + conj b * b` vanishes in `ℂ`, then both
`a` and `b` vanish. -/
private lemma conj_self_add_conj_self_eq_zero {a b : ℂ}
    (h : (starRingEnd ℂ) a * a + (starRingEnd ℂ) b * b = 0) : a = 0 ∧ b = 0 := by
  have ha : ((Complex.normSq a : ℝ) : ℂ) + ((Complex.normSq b : ℝ) : ℂ) = 0 := by
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]; exact h
  have hr : Complex.normSq a + Complex.normSq b = 0 := by exact_mod_cast ha
  have hna := Complex.normSq_nonneg a
  have hnb := Complex.normSq_nonneg b
  exact ⟨Complex.normSq_eq_zero.mp (by linarith), Complex.normSq_eq_zero.mp (by linarith)⟩

/-- If `Bᴴ B = Diag(σ₁², σ₂²)` with σᵢ ≥ 0 real, then `B = Q · Diag(σ₁, σ₂)` for some
    unitary Q.  (I.e. B's columns are orthogonal with norms σᵢ; complete the ones that
    vanish to an orthonormal basis.) -/
lemma mat2_polar_cols (B : Mat2) (σ₁ σ₂ : ℝ) (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂)
    (h : Bᴴ * B = Matrix.diagonal ![((σ₁ ^ 2 : ℝ) : ℂ), ((σ₂ ^ 2 : ℝ) : ℂ)]) :
    ∃ Q : Mat2, IsUnitary2 Q ∧ B = Q * Matrix.diagonal ![((σ₁ : ℝ) : ℂ), ((σ₂ : ℝ) : ℂ)] := by
  -- The two diagonal entries of `h` say that the columns of `B` have norms `σ₁`, `σ₂`.
  have e00 : (starRingEnd ℂ) (B 0 0) * B 0 0 + (starRingEnd ℂ) (B 1 0) * B 1 0
      = ((σ₁ : ℝ) : ℂ) ^ 2 := by
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two] using
      congrFun (congrFun h 0) 0
  have e11 : (starRingEnd ℂ) (B 0 1) * B 0 1 + (starRingEnd ℂ) (B 1 1) * B 1 1
      = ((σ₂ : ℝ) : ℂ) ^ 2 := by
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two] using
      congrFun (congrFun h 1) 1
  rcases eq_or_lt_of_le h₁ with hσ₁ | hσ₁
  · -- `σ₁ = 0`: the first column of `B` vanishes.
    subst hσ₁
    have ez : (starRingEnd ℂ) (B 0 0) * B 0 0 + (starRingEnd ℂ) (B 1 0) * B 1 0 = 0 := by
      rw [e00]; norm_num
    obtain ⟨z00, z10⟩ := conj_self_add_conj_self_eq_zero ez
    rcases eq_or_lt_of_le h₂ with hσ₂ | hσ₂
    · -- `σ₁ = σ₂ = 0`, so `B = 0`; take `Q = 1`.
      subst hσ₂
      have ez' : (starRingEnd ℂ) (B 0 1) * B 0 1 + (starRingEnd ℂ) (B 1 1) * B 1 1 = 0 := by
        rw [e11]; norm_num
      obtain ⟨z01, z11⟩ := conj_self_add_conj_self_eq_zero ez'
      refine ⟨1, isUnitary2_one, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, z00, z10, z01, z11]
    · -- `σ₁ = 0 < σ₂`: complete the unit vector `v / σ₂` to an orthonormal basis.
      have c₂ : ((σ₂ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hσ₂.ne'
      refine ⟨Matrix.of !![-((starRingEnd ℂ) (B 1 1) / (σ₂ : ℂ)), B 0 1 / (σ₂ : ℂ);
                           (starRingEnd ℂ) (B 0 1) / (σ₂ : ℂ), B 1 1 / (σ₂ : ℂ)], ?_, ?_⟩
      · unfold IsUnitary2
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
            map_div₀, Complex.conj_ofReal] <;>
          field_simp <;>
          first
            | ring1
            | linear_combination e11
      · ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, z00, z10] <;> field_simp
  · rcases eq_or_lt_of_le h₂ with hσ₂ | hσ₂
    · -- `σ₂ = 0 < σ₁`: complete the unit vector `u / σ₁` to an orthonormal basis.
      subst hσ₂
      have ez' : (starRingEnd ℂ) (B 0 1) * B 0 1 + (starRingEnd ℂ) (B 1 1) * B 1 1 = 0 := by
        rw [e11]; norm_num
      obtain ⟨z01, z11⟩ := conj_self_add_conj_self_eq_zero ez'
      have c₁ : ((σ₁ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hσ₁.ne'
      refine ⟨Matrix.of !![B 0 0 / (σ₁ : ℂ), -((starRingEnd ℂ) (B 1 0) / (σ₁ : ℂ));
                           B 1 0 / (σ₁ : ℂ), (starRingEnd ℂ) (B 0 0) / (σ₁ : ℂ)], ?_, ?_⟩
      · unfold IsUnitary2
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
            map_div₀, Complex.conj_ofReal] <;>
          field_simp <;>
          first
            | ring1
            | linear_combination e00
      · ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, z01, z11] <;> field_simp
    · -- Both singular values are positive: `Q = B · Diag(σ₁⁻¹, σ₂⁻¹)`.
      have c₁ : ((σ₁ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hσ₁.ne'
      have c₂ : ((σ₂ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hσ₂.ne'
      have hDh : (Matrix.diagonal ![(σ₁ : ℂ)⁻¹, (σ₂ : ℂ)⁻¹])ᴴ
          = Matrix.diagonal ![(σ₁ : ℂ)⁻¹, (σ₂ : ℂ)⁻¹] := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.conjTranspose_apply, Complex.conj_ofReal]
      refine ⟨B * Matrix.diagonal ![(σ₁ : ℂ)⁻¹, (σ₂ : ℂ)⁻¹], ?_, ?_⟩
      · unfold IsUnitary2
        rw [Matrix.conjTranspose_mul, hDh, Matrix.mul_assoc, ← Matrix.mul_assoc Bᴴ, h,
          Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
        ext i j
        fin_cases i <;> fin_cases j <;> simp <;> field_simp
      · rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

/-- Row version, by transposition. -/
lemma mat2_polar_rows (G : Mat2) (σ₁ σ₂ : ℝ) (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂)
    (h : G * Gᴴ = Matrix.diagonal ![((σ₁ ^ 2 : ℝ) : ℂ), ((σ₂ ^ 2 : ℝ) : ℂ)]) :
    ∃ Y : Mat2, IsUnitary2 Y ∧ G = Matrix.diagonal ![((σ₁ : ℝ) : ℂ), ((σ₂ : ℝ) : ℂ)] * Y := by
  have h' : (Gᴴ)ᴴ * Gᴴ = Matrix.diagonal ![((σ₁ ^ 2 : ℝ) : ℂ), ((σ₂ ^ 2 : ℝ) : ℂ)] := by
    rw [Matrix.conjTranspose_conjTranspose]; exact h
  obtain ⟨Q, hQ, hEq⟩ := mat2_polar_cols Gᴴ σ₁ σ₂ h₁ h₂ h'
  have hD : (Matrix.diagonal ![((σ₁ : ℝ) : ℂ), ((σ₂ : ℝ) : ℂ)])ᴴ
      = Matrix.diagonal ![((σ₁ : ℝ) : ℂ), ((σ₂ : ℝ) : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, Complex.conj_ofReal]
  refine ⟨Qᴴ, isUnitary2_conjTranspose hQ, ?_⟩
  calc G = (Gᴴ)ᴴ := (Matrix.conjTranspose_conjTranspose G).symm
    _ = (Q * Matrix.diagonal ![((σ₁ : ℝ) : ℂ), ((σ₂ : ℝ) : ℂ)])ᴴ := by rw [hEq]
    _ = (Matrix.diagonal ![((σ₁ : ℝ) : ℂ), ((σ₂ : ℝ) : ℂ)])ᴴ * Qᴴ := Matrix.conjTranspose_mul _ _
    _ = Matrix.diagonal ![((σ₁ : ℝ) : ℂ), ((σ₂ : ℝ) : ℂ)] * Qᴴ := by rw [hD]

/-- In a 2x2-block unitary whose first three blocks are the real diagonal matrices
    `C = Diag(c₁,c₂)`, `S = Diag(s₁,s₂)`, `S` (with `cᵢ² + sᵢ² = 1`, all entries ≥ 0),
    the fourth block `N` is forced to be diagonal too — provided `S ≠ 0`. -/
lemma m11_forced_diagonal (c₁ c₂ s₁ s₂ : ℝ) (N : Mat2)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂)
    (he₁ : c₁ ^ 2 + s₁ ^ 2 = 1) (he₂ : c₂ ^ 2 + s₂ ^ 2 = 1)
    (hSN : Matrix.diagonal ![(s₁ : ℂ), (s₂ : ℂ)] * N
         = -(Matrix.diagonal ![(c₁ : ℂ), (c₂ : ℂ)]
              * Matrix.diagonal ![(s₁ : ℂ), (s₂ : ℂ)]))
    (hcol : Nᴴ * N = Matrix.diagonal ![((c₁ ^ 2 : ℝ) : ℂ), ((c₂ ^ 2 : ℝ) : ℂ)])
    (hrow : N * Nᴴ = Matrix.diagonal ![((c₁ ^ 2 : ℝ) : ℂ), ((c₂ ^ 2 : ℝ) : ℂ)])
    (hs : ¬ (s₁ = 0 ∧ s₂ = 0)) :
    N 0 1 = 0 ∧ N 1 0 = 0 := by
  -- Entrywise consequences of `hSN` (the two off-diagonal ones are the workhorses)
  -- and of the column-orthonormality relation `hcol`.
  have e01 := congrFun (congrFun hSN 0) 1
  have e10 := congrFun (congrFun hSN 1) 0
  have c00 := congrFun (congrFun hcol 0) 0
  have c11 := congrFun (congrFun hcol 1) 1
  have x01 := congrFun (congrFun hcol 0) 1
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.mul_apply,
    Matrix.diagonal_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
    Matrix.diagonal_mul_diagonal, Matrix.neg_apply, zero_ne_one, one_ne_zero, neg_zero,
    mul_eq_zero, Complex.ofReal_eq_zero, Matrix.conjTranspose_apply, RCLike.star_def,
    Fin.sum_univ_two, Complex.ofReal_pow] at e01 e10 c00 c11 x01
  -- e01 : s₁ = 0 ∨ N 0 1 = 0
  -- e10 : s₂ = 0 ∨ N 1 0 = 0
  -- c00 : conj (N 0 0) * N 0 0 + conj (N 1 0) * N 1 0 = ↑c₁ ^ 2
  -- c11 : conj (N 0 1) * N 0 1 + conj (N 1 1) * N 1 1 = ↑c₂ ^ 2
  -- x01 : conj (N 0 0) * N 0 1 + conj (N 1 0) * N 1 1 = 0
  constructor
  · rcases e01 with hz | h
    · -- `s₁ = 0`, hence `c₁ = 1`, and by `hs` also `s₂ ≠ 0`, so `N 1 0 = 0`.
      have hs2 : s₂ ≠ 0 := fun h2 => hs ⟨hz, h2⟩
      have h10 : N 1 0 = 0 := e10.resolve_left hs2
      have hc1 : c₁ = 1 := by nlinarith [he₁, hz]
      rw [h10, map_zero, zero_mul, add_zero] at c00
      rw [h10, map_zero, zero_mul, add_zero] at x01
      -- `c00 : conj (N 0 0) * N 0 0 = 1` forces `N 0 0 ≠ 0`, so `x01` gives `N 0 1 = 0`.
      rcases mul_eq_zero.mp x01 with h | h
      · exfalso
        have h0 : N 0 0 = 0 := by simpa using h
        rw [h0] at c00
        simp [hc1] at c00
      · exact h
    · exact h
  · rcases e10 with hz | h
    · -- `s₂ = 0`, hence `c₂ = 1`, and by `hs` also `s₁ ≠ 0`, so `N 0 1 = 0`.
      have hs1 : s₁ ≠ 0 := fun h1 => hs ⟨h1, hz⟩
      have h01 : N 0 1 = 0 := e01.resolve_left hs1
      have hc2 : c₂ = 1 := by nlinarith [he₂, hz]
      rw [h01, map_zero, zero_mul, zero_add] at c11
      rw [h01, mul_zero, zero_add] at x01
      -- `c11 : conj (N 1 1) * N 1 1 = 1` forces `N 1 1 ≠ 0`, so `x01` gives `N 1 0 = 0`.
      rcases mul_eq_zero.mp x01 with h | h
      · simpa using h
      · exfalso
        rw [h] at c11
        simp [hc2] at c11
    · exact h

/-- `IsUnitary4` is closed under conjugate transpose. -/
lemma isUnitary4_dagger {V : Mat4} (h : IsUnitary4 V) : IsUnitary4 Vᴴ := by
  unfold IsUnitary4 at *
  rw [Matrix.conjTranspose_conjTranspose]
  exact mul_eq_one_comm.mp h

/-- A block-diagonal `blk4` of two unitaries is unitary. -/
lemma isUnitary4_blk4_diag {X Y : Mat2} (hX : IsUnitary2 X) (hY : IsUnitary2 Y) :
    IsUnitary4 (blk4 X 0 0 Y) := by
  unfold IsUnitary4
  rw [blk4_conjTranspose, blk4_mul, blk4_one]
  unfold IsUnitary2 at hX hY
  simp [hX, hY]

/-- A diagonal matrix with real entries is its own conjugate transpose. -/
lemma diagonal_real_conjTranspose (x y : ℝ) :
    (Matrix.diagonal ![((x : ℝ) : ℂ), ((y : ℝ) : ℂ)])ᴴ
      = Matrix.diagonal ![((x : ℝ) : ℂ), ((y : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]

/-- A Gram matrix equal to a real diagonal has nonnegative diagonal entries
    (they are sums of squared moduli of a column). -/
lemma diag_gram_nonneg (M : Mat2) (t₀ t₁ : ℝ)
    (h : Mᴴ * M = Matrix.diagonal ![((t₀ : ℝ) : ℂ), ((t₁ : ℝ) : ℂ)]) :
    0 ≤ t₀ ∧ 0 ≤ t₁ := by
  constructor
  · have hh := congrFun (congrFun h 0) 0
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply,
          Fin.sum_univ_two, ← Complex.normSq_eq_conj_mul_self] at hh
    have hc : ((Complex.normSq (M 0 0) + Complex.normSq (M 1 0) : ℝ) : ℂ) = ((t₀ : ℝ) : ℂ) := by
      push_cast; linear_combination hh
    have h2 : Complex.normSq (M 0 0) + Complex.normSq (M 1 0) = t₀ := by exact_mod_cast hc
    nlinarith [Complex.normSq_nonneg (M 0 0), Complex.normSq_nonneg (M 1 0)]
  · have hh := congrFun (congrFun h 1) 1
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply,
          Fin.sum_univ_two, ← Complex.normSq_eq_conj_mul_self] at hh
    have hc : ((Complex.normSq (M 0 1) + Complex.normSq (M 1 1) : ℝ) : ℂ) = ((t₁ : ℝ) : ℂ) := by
      push_cast; linear_combination hh
    have h2 : Complex.normSq (M 0 1) + Complex.normSq (M 1 1) = t₁ := by exact_mod_cast hc
    nlinarith [Complex.normSq_nonneg (M 0 1), Complex.normSq_nonneg (M 1 1)]

/-- Spectral theorem for the 2×2 Gram matrix `Aᴴ A`, restated in the project's
    `IsUnitary2` / `Matrix.diagonal ![·,·]` vocabulary with REAL eigenvalues.
    (Stated for a Gram matrix rather than a general PSD matrix so that no
    `ComplexOrder` scoped instance is needed; nonnegativity of the eigenvalues
    is recovered where it is used, via `diag_gram_nonneg`.) -/
lemma mat2_gram_diagonalize (A : Mat2) :
    ∃ P : Mat2, IsUnitary2 P ∧ ∃ μ₀ μ₁ : ℝ,
      Aᴴ * A = P * Matrix.diagonal ![((μ₀ : ℝ) : ℂ), ((μ₁ : ℝ) : ℂ)] * Pᴴ := by
  have hH : (Aᴴ * A).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  refine ⟨(hH.eigenvectorUnitary : Mat2), ?_, hH.eigenvalues 0, hH.eigenvalues 1, ?_⟩
  · have h := (hH.eigenvectorUnitary).2
    rw [Matrix.mem_unitaryGroup_iff'] at h
    simpa [IsUnitary2, Matrix.star_eq_conjTranspose] using h
  · have hdiag : Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)
        = Matrix.diagonal ![((hH.eigenvalues 0 : ℝ) : ℂ), ((hH.eigenvalues 1 : ℝ) : ℂ)] := by
      congr 1
      funext i
      fin_cases i <;> simp
    rw [← hdiag]
    conv_lhs => rw [hH.spectral_theorem]
    rfl

set_option maxHeartbeats 1600000 in
-- Heartbeat bump: the cosine-sine construction runs ~20 ext/fin_cases/simp block
-- computations on Mat4 inside a single declaration.
/-- **HP paper Lemma A.4** (page 28, [Paige and Wei 1994]).
    For a 2-qubit gate V, there exist 1-qubit gates P₀, P₁, R_y(θ₀),
    R_y(θ₁), Q₀, Q₁ and 2-qubit gates P = |0⟩⟨0|⊗P₀+|1⟩⟨1|⊗P₁,
    R = R_y(θ₀)⊗|0⟩⟨0|+R_y(θ₁)⊗|1⟩⟨1|, Q = |0⟩⟨0|⊗Q₀+|1⟩⟨1|⊗Q₁,
    such that V = Q · R · P (Paige-Wei 2-qubit decomposition).

    **Note**: stated with generic 1-qubit unitaries R₀, R₁ for the
    R_y(θᵢ) slots — the specific R_y rotation structure is noted but
    not constrained. This is exactly the *cosine-sine decomposition*
    with the CS block left as a pair of generic 2×2 unitaries; the
    construction below in fact produces `R_i = !![cᵢ, sᵢ; sᵢ, nᵢ]` with
    `cᵢ, sᵢ` real, `cᵢ² + sᵢ² = 1`, so tightening to the R_y form is
    only a matter of pinning the phase `nᵢ`.

    **Proof status**: PROVED (iter 1045). Group-theoretically the claim is
    `U(4) = G₁ · G₂ · G₁` with `G₁` the centralizer of `Z⊗I` and `G₂` that
    of `I⊗Z`. The proof is the classical Paige-Wei construction: SVD the
    (0,0) block, read the sines off the (1,0) block, polar-decompose the
    (0,1) block, and then let unitarity force the (1,1) block diagonal.
    The degenerate case `V₁₀ = 0` is split off first (there `V` is already
    block-diagonal and the middle factor is the identity). -/
theorem paper_lemma_A_4 (V : Mat4) (hV : IsUnitary4 V) :
    ∃ P₀ P₁ R₀ R₁ Q₀ Q₁ : Mat2,
      IsUnitary2 P₀ ∧ IsUnitary2 P₁ ∧
      IsUnitary2 R₀ ∧ IsUnitary2 R₁ ∧
      IsUnitary2 Q₀ ∧ IsUnitary2 Q₁ ∧
      V = (kron2 proj0 Q₀ + kron2 proj1 Q₁) *
          (kron2 R₀ proj0 + kron2 R₁ proj1) *
          (kron2 proj0 P₀ + kron2 proj1 P₁) := by
  set A : Mat2 := Matrix.of !![V 0 0, V 0 1; V 1 0, V 1 1] with hAdef
  set B : Mat2 := Matrix.of !![V 0 2, V 0 3; V 1 2, V 1 3] with hBdef
  set C : Mat2 := Matrix.of !![V 2 0, V 2 1; V 3 0, V 3 1] with hCdef
  set D : Mat2 := Matrix.of !![V 2 2, V 2 3; V 3 2, V 3 3] with hDdef
  have hVblk : V = blk4 A B C D := blk4_self V
  have hcolV : (blk4 A B C D)ᴴ * blk4 A B C D = blk4 1 0 0 1 := by
    rw [← hVblk, ← blk4_one]; exact hV
  rw [blk4_conjTranspose, blk4_mul] at hcolV
  obtain ⟨e1, e2, e3, e4⟩ := blk4_inj hcolV
  have hrowV : blk4 A B C D * (blk4 A B C D)ᴴ = blk4 1 0 0 1 := by
    rw [← hVblk, ← blk4_one]; exact mul_eq_one_comm.mp hV
  rw [blk4_conjTranspose, blk4_mul] at hrowV
  obtain ⟨f1, f2, f3, f4⟩ := blk4_inj hrowV
  by_cases hC0 : C = 0
  · -- Degenerate branch: `V₁₀ = 0` forces `V₀₁ = 0`, so `V` is already block-diagonal
    -- and the middle factor may be taken to be the identity.
    have hAA : Aᴴ * A = 1 := by rw [hC0] at e1; simpa using e1
    have hAAr : A * Aᴴ = 1 := mul_eq_one_comm.mp hAA
    have hB0 : B = 0 := by
      have h2 : Aᴴ * B = 0 := by rw [hC0] at e2; simpa using e2
      calc B = (A * Aᴴ) * B := by rw [hAAr, one_mul]
        _ = A * (Aᴴ * B) := by noncomm_ring
        _ = 0 := by rw [h2, mul_zero]
    have hDD : Dᴴ * D = 1 := by rw [hB0] at e4; simpa using e4
    refine ⟨1, 1, 1, 1, A, D, isUnitary2_one, isUnitary2_one, isUnitary2_one,
            isUnitary2_one, hAA, hDD, ?_⟩
    have hmid : kron2 (1 : Mat2) proj0 + kron2 (1 : Mat2) proj1 = (1 : Mat4) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [kron2, proj0, proj1, Matrix.one_apply]
    have hlast : kron2 proj0 (1 : Mat2) + kron2 proj1 (1 : Mat2) = (1 : Mat4) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [kron2, proj0, proj1, Matrix.one_apply]
    rw [hmid, hlast, mul_one, mul_one, kron2_blockdiagfirst_eq_blk4, hVblk, hB0, hC0]
  · -- Main branch: the cosine-sine construction.
    -- Step 1: SVD of the (0,0) block, `A = Q₀ · Diag(c₁,c₂) · Pᴴ`.
    obtain ⟨P, hP, μ₀, μ₁, hAA⟩ := mat2_gram_diagonalize A
    have hPr : P * Pᴴ = 1 := mul_eq_one_comm.mp hP
    have hAPgram0 : (A * P)ᴴ * (A * P)
        = Matrix.diagonal ![((μ₀ : ℝ) : ℂ), ((μ₁ : ℝ) : ℂ)] := by
      rw [Matrix.conjTranspose_mul]
      calc Pᴴ * Aᴴ * (A * P) = Pᴴ * (Aᴴ * A) * P := by noncomm_ring
        _ = Pᴴ * (P * Matrix.diagonal ![((μ₀ : ℝ) : ℂ), ((μ₁ : ℝ) : ℂ)] * Pᴴ) * P := by rw [hAA]
        _ = (Pᴴ * P) * Matrix.diagonal ![((μ₀ : ℝ) : ℂ), ((μ₁ : ℝ) : ℂ)] * (Pᴴ * P) := by
              noncomm_ring
        _ = Matrix.diagonal ![((μ₀ : ℝ) : ℂ), ((μ₁ : ℝ) : ℂ)] := by rw [hP, one_mul, mul_one]
    obtain ⟨hμ₀, hμ₁⟩ := diag_gram_nonneg (A * P) μ₀ μ₁ hAPgram0
    -- Step 2: the complementary "sines", `1 - C² = S²`, and the polar form of `C·P`.
    have hCC : Cᴴ * C = 1 - Aᴴ * A := by rw [← e1]; abel
    have hCPgram0 : (C * P)ᴴ * (C * P)
        = Matrix.diagonal ![((1 - μ₀ : ℝ) : ℂ), ((1 - μ₁ : ℝ) : ℂ)] := by
      rw [Matrix.conjTranspose_mul]
      calc Pᴴ * Cᴴ * (C * P) = Pᴴ * (Cᴴ * C) * P := by noncomm_ring
        _ = Pᴴ * (1 - Aᴴ * A) * P := by rw [hCC]
        _ = Pᴴ * P - (A * P)ᴴ * (A * P) := by rw [Matrix.conjTranspose_mul]; noncomm_ring
        _ = 1 - Matrix.diagonal ![((μ₀ : ℝ) : ℂ), ((μ₁ : ℝ) : ℂ)] := by rw [hP, hAPgram0]
        _ = Matrix.diagonal ![((1 - μ₀ : ℝ) : ℂ), ((1 - μ₁ : ℝ) : ℂ)] := by
              ext i j
              fin_cases i <;> fin_cases j <;>
                simp [Matrix.diagonal_apply, Matrix.one_apply, Matrix.sub_apply] <;>
                push_cast <;> ring
    obtain ⟨hs₁nn0, hs₂nn0⟩ := diag_gram_nonneg (C * P) (1 - μ₀) (1 - μ₁) hCPgram0
    set c₁ : ℝ := Real.sqrt μ₀ with hc₁def
    set c₂ : ℝ := Real.sqrt μ₁ with hc₂def
    set s₁ : ℝ := Real.sqrt (1 - μ₀) with hs₁def
    set s₂ : ℝ := Real.sqrt (1 - μ₁) with hs₂def
    have hc₁nn : 0 ≤ c₁ := Real.sqrt_nonneg _
    have hc₂nn : 0 ≤ c₂ := Real.sqrt_nonneg _
    have hs₁nn : 0 ≤ s₁ := Real.sqrt_nonneg _
    have hs₂nn : 0 ≤ s₂ := Real.sqrt_nonneg _
    have hc₁sq : c₁ ^ 2 = μ₀ := Real.sq_sqrt hμ₀
    have hc₂sq : c₂ ^ 2 = μ₁ := Real.sq_sqrt hμ₁
    have hs₁sq : s₁ ^ 2 = 1 - μ₀ := Real.sq_sqrt hs₁nn0
    have hs₂sq : s₂ ^ 2 = 1 - μ₁ := Real.sq_sqrt hs₂nn0
    have he₁ : c₁ ^ 2 + s₁ ^ 2 = 1 := by rw [hc₁sq, hs₁sq]; ring
    have he₂ : c₂ ^ 2 + s₂ ^ 2 = 1 := by rw [hc₂sq, hs₂sq]; ring
    obtain ⟨Q₀, hQ₀, hAPeq⟩ :=
      mat2_polar_cols (A * P) c₁ c₂ hc₁nn hc₂nn (by rw [hc₁sq, hc₂sq]; exact hAPgram0)
    obtain ⟨Q₁, hQ₁, hCPeq⟩ :=
      mat2_polar_cols (C * P) s₁ s₂ hs₁nn hs₂nn (by rw [hs₁sq, hs₂sq]; exact hCPgram0)
    set Cmat : Mat2 := Matrix.diagonal ![((c₁ : ℝ) : ℂ), ((c₂ : ℝ) : ℂ)] with hCmatdef
    set Smat : Mat2 := Matrix.diagonal ![((s₁ : ℝ) : ℂ), ((s₂ : ℝ) : ℂ)] with hSmatdef
    have hCmatH : Cmatᴴ = Cmat := diagonal_real_conjTranspose c₁ c₂
    have hSmatH : Smatᴴ = Smat := diagonal_real_conjTranspose s₁ s₂
    have hAeq : A = Q₀ * Cmat * Pᴴ := by
      calc A = A * (P * Pᴴ) := by rw [hPr, mul_one]
        _ = (A * P) * Pᴴ := by noncomm_ring
        _ = Q₀ * Cmat * Pᴴ := by rw [hAPeq]
    have hCeq : C = Q₁ * Smat * Pᴴ := by
      calc C = C * (P * Pᴴ) := by rw [hPr, mul_one]
        _ = (C * P) * Pᴴ := by noncomm_ring
        _ = Q₁ * Smat * Pᴴ := by rw [hCPeq]
    have hQ₀r : Q₀ * Q₀ᴴ = 1 := mul_eq_one_comm.mp hQ₀
    have hQ₁r : Q₁ * Q₁ᴴ = 1 := mul_eq_one_comm.mp hQ₁
    -- Step 3: the (0,1) block, `G := Q₀† B`, has `G G† = S²`; polar-decompose its rows.
    have hAAr2 : A * Aᴴ = Q₀ * (Cmat * Cmat) * Q₀ᴴ := by
      conv_lhs => rw [hAeq]
      calc (Q₀ * Cmat * Pᴴ) * (Q₀ * Cmat * Pᴴ)ᴴ
          = Q₀ * Cmat * (Pᴴ * P) * Cmatᴴ * Q₀ᴴ := by
              simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
              noncomm_ring
        _ = Q₀ * (Cmat * Cmat) * Q₀ᴴ := by rw [hP, hCmatH]; noncomm_ring
    have hBBr : B * Bᴴ = 1 - Q₀ * (Cmat * Cmat) * Q₀ᴴ := by rw [← hAAr2, ← f1]; abel
    have hcast1 : ((s₁ ^ 2 : ℝ) : ℂ) = 1 - (c₁ : ℂ) * (c₁ : ℂ) := by
      have h : s₁ ^ 2 = 1 - c₁ ^ 2 := by linarith
      rw [h]; push_cast; ring
    have hcast2 : ((s₂ ^ 2 : ℝ) : ℂ) = 1 - (c₂ : ℂ) * (c₂ : ℂ) := by
      have h : s₂ ^ 2 = 1 - c₂ ^ 2 := by linarith
      rw [h]; push_cast; ring
    have hcastC1 : ((c₁ ^ 2 : ℝ) : ℂ) = 1 - (s₁ : ℂ) * (s₁ : ℂ) := by
      have h : c₁ ^ 2 = 1 - s₁ ^ 2 := by linarith
      rw [h]; push_cast; ring
    have hcastC2 : ((c₂ ^ 2 : ℝ) : ℂ) = 1 - (s₂ : ℂ) * (s₂ : ℂ) := by
      have h : c₂ ^ 2 = 1 - s₂ ^ 2 := by linarith
      rw [h]; push_cast; ring
    have hGgram : (Q₀ᴴ * B) * (Q₀ᴴ * B)ᴴ
        = Matrix.diagonal ![((s₁ ^ 2 : ℝ) : ℂ), ((s₂ ^ 2 : ℝ) : ℂ)] := by
      calc (Q₀ᴴ * B) * (Q₀ᴴ * B)ᴴ = Q₀ᴴ * (B * Bᴴ) * Q₀ := by
              simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
              noncomm_ring
        _ = Q₀ᴴ * (1 - Q₀ * (Cmat * Cmat) * Q₀ᴴ) * Q₀ := by rw [hBBr]
        _ = Q₀ᴴ * Q₀ - (Q₀ᴴ * Q₀) * (Cmat * Cmat) * (Q₀ᴴ * Q₀) := by noncomm_ring
        _ = 1 - Cmat * Cmat := by rw [hQ₀]; noncomm_ring
        _ = Matrix.diagonal ![((s₁ ^ 2 : ℝ) : ℂ), ((s₂ ^ 2 : ℝ) : ℂ)] := by
              rw [hCmatdef, hcast1, hcast2]
              ext i j
              fin_cases i <;> fin_cases j <;>
                simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply,
                      Matrix.sub_apply]
    obtain ⟨Y, hY, hGeq⟩ := mat2_polar_rows (Q₀ᴴ * B) s₁ s₂ hs₁nn hs₂nn hGgram
    have hYr : Y * Yᴴ = 1 := mul_eq_one_comm.mp hY
    set N : Mat2 := Q₁ᴴ * D * Yᴴ with hNdef
    have hBeq : B = Q₀ * Smat * Y := by
      calc B = (Q₀ * Q₀ᴴ) * B := by rw [hQ₀r, one_mul]
        _ = Q₀ * (Q₀ᴴ * B) := by noncomm_ring
        _ = Q₀ * (Smat * Y) := by rw [hGeq]
        _ = Q₀ * Smat * Y := by noncomm_ring
    have hDeq : D = Q₁ * N * Y := by
      rw [hNdef]
      calc D = (Q₁ * Q₁ᴴ) * D * (Yᴴ * Y) := by rw [hQ₁r, hY, one_mul, mul_one]
        _ = Q₁ * (Q₁ᴴ * D * Yᴴ) * Y := by noncomm_ring
    -- Step 4: the three-factor form, and unitarity of the middle factor.
    have hprod : blk4 Q₀ 0 0 Q₁ * blk4 Cmat Smat Smat N * blk4 Pᴴ 0 0 Y
        = blk4 (Q₀ * Cmat * Pᴴ) (Q₀ * Smat * Y) (Q₁ * Smat * Pᴴ) (Q₁ * N * Y) := by
      rw [blk4_mul, blk4_mul]; simp
    have hVfact : V = blk4 Q₀ 0 0 Q₁ * blk4 Cmat Smat Smat N * blk4 Pᴴ 0 0 Y := by
      rw [hprod, hVblk, ← hAeq, ← hBeq, ← hCeq, ← hDeq]
    have hQblk : IsUnitary4 (blk4 Q₀ 0 0 Q₁) := isUnitary4_blk4_diag hQ₀ hQ₁
    have hPblk : IsUnitary4 (blk4 Pᴴ 0 0 Y) :=
      isUnitary4_blk4_diag (isUnitary2_conjTranspose hP) hY
    have hPblkr : blk4 Pᴴ 0 0 Y * (blk4 Pᴴ 0 0 Y)ᴴ = 1 := mul_eq_one_comm.mp hPblk
    have hMeq : blk4 Cmat Smat Smat N = (blk4 Q₀ 0 0 Q₁)ᴴ * V * (blk4 Pᴴ 0 0 Y)ᴴ := by
      rw [hVfact]
      calc blk4 Cmat Smat Smat N
          = ((blk4 Q₀ 0 0 Q₁)ᴴ * blk4 Q₀ 0 0 Q₁) * blk4 Cmat Smat Smat N
              * (blk4 Pᴴ 0 0 Y * (blk4 Pᴴ 0 0 Y)ᴴ) := by
              rw [hQblk, hPblkr, one_mul, mul_one]
        _ = _ := by noncomm_ring
    have hMunit : IsUnitary4 (blk4 Cmat Smat Smat N) := by
      rw [hMeq]
      exact isUnitary4_mul (isUnitary4_mul (isUnitary4_dagger hQblk) hV) (isUnitary4_dagger hPblk)
    have hMcol : (blk4 Cmat Smat Smat N)ᴴ * blk4 Cmat Smat Smat N = blk4 1 0 0 1 := by
      rw [← blk4_one]; exact hMunit
    rw [blk4_conjTranspose, blk4_mul] at hMcol
    obtain ⟨g1, g2, g3, g4⟩ := blk4_inj hMcol
    have hMrow : blk4 Cmat Smat Smat N * (blk4 Cmat Smat Smat N)ᴴ = blk4 1 0 0 1 := by
      rw [← blk4_one]; exact mul_eq_one_comm.mp hMunit
    rw [blk4_conjTranspose, blk4_mul] at hMrow
    obtain ⟨k1, k2, k3, k4⟩ := blk4_inj hMrow
    rw [hCmatH, hSmatH] at g2
    rw [hSmatH] at g4
    rw [hSmatH] at k4
    -- Step 5: the last block is forced diagonal.
    have hSN : Smat * N = -(Cmat * Smat) := by
      have h : Smat * N = (Cmat * Smat + Smat * N) - Cmat * Smat := by abel
      rw [h, g2]; abel
    have hcolN : Nᴴ * N = Matrix.diagonal ![((c₁ ^ 2 : ℝ) : ℂ), ((c₂ ^ 2 : ℝ) : ℂ)] := by
      have h : Nᴴ * N = (Smat * Smat + Nᴴ * N) - Smat * Smat := by abel
      rw [h, g4, hSmatdef, hcastC1, hcastC2]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply, Matrix.sub_apply]
    have hrowN : N * Nᴴ = Matrix.diagonal ![((c₁ ^ 2 : ℝ) : ℂ), ((c₂ ^ 2 : ℝ) : ℂ)] := by
      have h : N * Nᴴ = (Smat * Smat + N * Nᴴ) - Smat * Smat := by abel
      rw [h, k4, hSmatdef, hcastC1, hcastC2]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply, Matrix.sub_apply]
    have hsne : ¬ (s₁ = 0 ∧ s₂ = 0) := by
      rintro ⟨h1, h2⟩
      apply hC0
      have hS0 : Smat = 0 := by
        rw [hSmatdef, h1, h2]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      rw [hCeq, hS0, mul_zero, zero_mul]
    obtain ⟨hN01, hN10⟩ :=
      m11_forced_diagonal c₁ c₂ s₁ s₂ N hc₁nn hc₂nn hs₁nn hs₂nn he₁ he₂
        (by rw [← hCmatdef, ← hSmatdef]; exact hSN) hcolN hrowN hsne
    have hNdiag : N = Matrix.diagonal ![N 0 0, N 1 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply, hN01, hN10]
    -- Step 6: read off `R₀`, `R₁`.
    have hMkron : blk4 Cmat Smat Smat N
        = kron2 (Matrix.of !![(c₁ : ℂ), (s₁ : ℂ); (s₁ : ℂ), N 0 0]) proj0
          + kron2 (Matrix.of !![(c₂ : ℂ), (s₂ : ℂ); (s₂ : ℂ), N 1 1]) proj1 := by
      conv_lhs => rw [hCmatdef, hSmatdef, hNdiag]
      exact blk4_diags_eq_kron2_blockdiagsecond _ _ _ _ _ _ _ _
    have hMunit' : IsUnitary4 (kron2 (Matrix.of !![(c₁ : ℂ), (s₁ : ℂ); (s₁ : ℂ), N 0 0]) proj0
          + kron2 (Matrix.of !![(c₂ : ℂ), (s₂ : ℂ); (s₂ : ℂ), N 1 1]) proj1) := by
      rw [← hMkron]; exact hMunit
    obtain ⟨hR₀, hR₁⟩ := isUnitary2_of_blockdiagsecond hMunit'
    refine ⟨Pᴴ, Y, Matrix.of !![(c₁ : ℂ), (s₁ : ℂ); (s₁ : ℂ), N 0 0],
            Matrix.of !![(c₂ : ℂ), (s₂ : ℂ); (s₂ : ℂ), N 1 1], Q₀, Q₁,
            isUnitary2_conjTranspose hP, hY, hR₀, hR₁, hQ₀, hQ₁, ?_⟩
    rw [kron2_blockdiagfirst_eq_blk4, kron2_blockdiagfirst_eq_blk4, ← hMkron]
    exact hVfact

/-- A 2×2 diagonal matrix with unit-modulus entries is unitary. -/
lemma isUnitary2_diagonal_of_normSq (x y : ℂ)
    (hx : Complex.normSq x = 1) (hy : Complex.normSq y = 1) :
    IsUnitary2 (Matrix.diagonal ![x, y]) := by
  have hx' : (starRingEnd ℂ) x * x = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, hx]; norm_num
  have hy' : (starRingEnd ℂ) y * y = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, hy]; norm_num
  unfold IsUnitary2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, hx', hy']

/-- Structural core of paper Lemma A.5. A block-diag-**first** gate whose two
    blocks are `P·D·Q` and `P·D'·Q` with `D = Diag(x₀,x₁)`, `D' = Diag(y₀,y₁)`
    diagonal splits as `(1⊗P) · R · (1⊗Q)` with `R` block-diag-**second**
    carrying the two *column-wise* diagonal matrices `Diag(x₀,y₀)`,
    `Diag(x₁,y₁)`. (The transposition of the index roles is the whole content:
    slot-1 block index ↔ slot-2 diagonal index.) -/
lemma blockdiagfirst_diag_split (P Q V₀ V₁ : Mat2) (x₀ x₁ y₀ y₁ : ℂ)
    (h0 : V₀ = P * Matrix.diagonal ![x₀, x₁] * Q)
    (h1 : V₁ = P * Matrix.diagonal ![y₀, y₁] * Q) :
    kron2 proj0 V₀ + kron2 proj1 V₁ =
      (kron2 1 P) *
      (kron2 (Matrix.diagonal ![x₀, y₀]) proj0 +
       kron2 (Matrix.diagonal ![x₁, y₁]) proj1) *
      (kron2 1 Q) := by
  subst h0; subst h1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kron2, proj0, proj1, Matrix.mul_apply, Matrix.add_apply, Matrix.of_apply,
          Matrix.diagonal_apply, Matrix.one_apply, Fin.sum_univ_four,
          Fin.sum_univ_two]

/-- **HP paper Lemma A.5** (page 26, [Shende et al. 2005]).
    For 1-qubit gates V₀, V₁, the block-diag-first 2-qubit gate
    `V = |0⟩⟨0|⊗V₀ + |1⟩⟨1|⊗V₁` decomposes (paper figure, circuit order
    left-to-right): `Q[2] · Ctrl(2,R) · P[2]`, where:
    - Q[2], P[2] are 1-qubit gates Q, P acting on qubit 2 unconditionally
      (NO control on either Q or P — only R has structural control).
    - R = R_z(α₀)⊗|0⟩⟨0| + R_z(α₁)⊗|1⟩⟨1| is the block-diag-second
      2-qubit gate (R_z's on qubit 1, structurally controlled by qubit 2).

    **Convention note — matrix product order vs circuit order**:
    Paper figure (circuit order, left-to-right = chronologically first
    to last): Q (left/first), Ctrl(2,R) (middle), P (right/last). The
    Lean expression below is in MATRIX PRODUCT order, which REVERSES
    the figure order — the rightmost matrix factor acts on a state
    first. So in Lean we write `(I⊗P) · R · (I⊗Q)` with P leftmost
    (chronologically LAST) and Q rightmost (chronologically FIRST).
    This mirrors `paper_lemma_A_4` and `paper_lemma_A_3`.

    **Note**: R_z structure on the R parts is noted but not formally
    constrained in this stub (uses generic 1-qubit unitaries Rz₀, Rz₁).

    **Proof status**: PROVED (iter 1045). Note: this is the FULL form of
    Shende 2005; our existing `blockDiagB_spectral` is the simpler
    A.3-style spectral claim, not the full Shende A.5 form (the middle
    factor is C(Diag), not the block-diag-second R_z structure). -/
theorem paper_lemma_A_5 (V₀ V₁ : Mat2)
    (_hV₀ : IsUnitary2 V₀) (_hV₁ : IsUnitary2 V₁) :
    ∃ P Q Rz₀ Rz₁ : Mat2,
      IsUnitary2 P ∧ IsUnitary2 Q ∧
      IsUnitary2 Rz₀ ∧ IsUnitary2 Rz₁ ∧
      -- Iter 285 (2026-05-15): paper-faithful R_z structure. Each Rz_i is
      -- a DIAGONAL Mat2 (paper R_z(α_i) form). Unit-modulus entries follow
      -- from IsUnitary2. This is the key fact joint_spec eigenvalue
      -- derivation requires.
      -- Iter 290 (2026-05-15): strengthen further with det=1 (paper R_z's
      -- property: det(R_z(α)) = 1, i.e., a · b = 1 for each Rz_i diagonal pair).
      (∃ a b : ℂ, a * b = 1 ∧ Rz₀ = Matrix.diagonal ![a, b]) ∧
      (∃ a b : ℂ, a * b = 1 ∧ Rz₁ = Matrix.diagonal ![a, b]) ∧
      kron2 proj0 V₀ + kron2 proj1 V₁ =
        (kron2 1 P) *
        (kron2 Rz₀ proj0 + kron2 Rz₁ proj1) *
        (kron2 1 Q) := by
  -- Closed iter 1045. Componentwise the goal says exactly `V₀ = P·D·Q` and
  -- `V₁ = P·D⁻¹·Q` with `D = Diag(sa,sb)` diagonal — the det-1 constraint on
  -- each `Rz_i` is precisely what forces the second block to be `D⁻¹`.
  -- So diagonalize `V₀V₁† = U·Diag(a,b)·U†` (`py24_lemma_A_3`), take square
  -- roots `sa² = a`, `sb² = b`, and set `P := U`, `D := Diag(sa,sb)`,
  -- `Q := D·U†·V₁`. Then `P·D·Q = U·D²·U†·V₁ = (V₀V₁†)V₁ = V₀` and
  -- `P·D⁻¹·Q = U·U†·V₁ = V₁`. The det-1 slots are `Diag(sa, sa⁻¹)` and
  -- `Diag(sb, sb⁻¹)` — note the *column-wise* pairing (see
  -- `blockdiagfirst_diag_split`).
  have hW : IsUnitary2 (V₀ * V₁.conjTranspose) :=
    isUnitary2_mul _hV₀ (isUnitary2_conjTranspose _hV₁)
  obtain ⟨a, b, U, hU, hUeq⟩ := py24_lemma_A_3 (V₀ * V₁.conjTranspose) hW
  have hUUc : U * U.conjTranspose = 1 := mul_eq_one_comm.mp hU
  have hDunit : IsUnitary2 (Matrix.diagonal ![a, b]) := by
    rw [← hUeq]
    exact isUnitary2_mul (isUnitary2_mul (isUnitary2_conjTranspose hU) hW) hU
  obtain ⟨hna, hnb⟩ := diagonal_unitary_normSq a b hDunit
  obtain ⟨sa, hsa⟩ := IsAlgClosed.exists_pow_nat_eq a (n := 2) (by norm_num)
  obtain ⟨sb, hsb⟩ := IsAlgClosed.exists_pow_nat_eq b (n := 2) (by norm_num)
  have hnsa : Complex.normSq sa = 1 := by
    have h2 : Complex.normSq sa ^ 2 = 1 := by
      rw [show Complex.normSq sa ^ 2 = Complex.normSq (sa ^ 2) from by
            rw [sq, sq, map_mul], hsa, hna]
    nlinarith [Complex.normSq_nonneg sa]
  have hnsb : Complex.normSq sb = 1 := by
    have h2 : Complex.normSq sb ^ 2 = 1 := by
      rw [show Complex.normSq sb ^ 2 = Complex.normSq (sb ^ 2) from by
            rw [sq, sq, map_mul], hsb, hnb]
    nlinarith [Complex.normSq_nonneg sb]
  have hsa0 : sa ≠ 0 := fun h => by simp [h] at hnsa
  have hsb0 : sb ≠ 0 := fun h => by simp [h] at hnsb
  have hnsai : Complex.normSq sa⁻¹ = 1 := by rw [map_inv₀, hnsa, inv_one]
  have hnsbi : Complex.normSq sb⁻¹ = 1 := by rw [map_inv₀, hnsb, inv_one]
  have hsa' : sa * sa = a := by rw [← hsa]; ring
  have hsb' : sb * sb = b := by rw [← hsb]; ring
  set D : Mat2 := Matrix.diagonal ![sa, sb] with hD
  set Di : Mat2 := Matrix.diagonal ![sa⁻¹, sb⁻¹] with hDi
  have hDD : D * D = Matrix.diagonal ![a, b] := by
    rw [hD]; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.diagonal_apply, hsa', hsb']
  have hDiD : Di * D = 1 := by
    rw [hD, hDi]; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.diagonal_apply,
            inv_mul_cancel₀ hsa0, inv_mul_cancel₀ hsb0]
  have hDunit' : IsUnitary2 D := isUnitary2_diagonal_of_normSq _ _ hnsa hnsb
  have hVeq : V₀ * V₁.conjTranspose = U * (D * D) * U.conjTranspose := by
    rw [hDD, ← hUeq,
        show U * (U.conjTranspose * (V₀ * V₁.conjTranspose) * U) * U.conjTranspose
          = (U * U.conjTranspose) * (V₀ * V₁.conjTranspose) * (U * U.conjTranspose)
          from by noncomm_ring, hUUc, one_mul, mul_one]
  refine ⟨U, D * U.conjTranspose * V₁, Matrix.diagonal ![sa, sa⁻¹],
          Matrix.diagonal ![sb, sb⁻¹], hU,
          isUnitary2_mul (isUnitary2_mul hDunit' (isUnitary2_conjTranspose hU)) _hV₁,
          isUnitary2_diagonal_of_normSq _ _ hnsa hnsai,
          isUnitary2_diagonal_of_normSq _ _ hnsb hnsbi,
          ⟨sa, sa⁻¹, mul_inv_cancel₀ hsa0, rfl⟩,
          ⟨sb, sb⁻¹, mul_inv_cancel₀ hsb0, rfl⟩, ?_⟩
  refine blockdiagfirst_diag_split U (D * U.conjTranspose * V₁) V₀ V₁ sa sb sa⁻¹ sb⁻¹ ?_ ?_
  · calc V₀ = V₀ * (V₁.conjTranspose * V₁) := by rw [_hV₁, mul_one]
      _ = (V₀ * V₁.conjTranspose) * V₁ := by noncomm_ring
      _ = U * (D * D) * U.conjTranspose * V₁ := by rw [hVeq]
      _ = U * D * (D * U.conjTranspose * V₁) := by noncomm_ring
  · calc V₁ = (U * U.conjTranspose) * V₁ := by rw [hUUc, one_mul]
      _ = U * (Di * D) * U.conjTranspose * V₁ := by rw [hDiD]; noncomm_ring
      _ = U * Di * (D * U.conjTranspose * V₁) := by noncomm_ring

/-- **HP paper Lemma A.6** (page 26, [Shende and Markov 2008 Eq.(4)]).
    For complex numbers d₀, d₁ with |d_i|=1, C(Diag(d₀, d₁)) decomposes
    as a phase P(φ) on qubit 1 followed by a controlled-R_z(α) on the
    target, where R_z(α) = Diag(α₀, α₁) with α₀·α₁ = 1 (det-1).

    **Convention note — matrix product order vs circuit order**:
    Paper figure (circuit order, left-to-right): P(φ) on top qubit
    (chronologically first), then C(R_z(α)) (chronologically last).
    In MATRIX PRODUCT form (Lean syntax), this REVERSES: the rightmost
    factor is applied first to a state. So Lean writes
    `C(R_z(α)) · (P(φ)⊗I)` with C(R_z) leftmost (chronologically LAST)
    and `P(φ)⊗I` rightmost (chronologically FIRST).

    **Proof status**: scaffolding stub (proof: ~20 lines of phase
    algebra). -/
theorem paper_lemma_A_6 (d₀ d₁ : ℂ)
    (_hd₀ : Complex.normSq d₀ = 1) (_hd₁ : Complex.normSq d₁ = 1) :
    ∃ φ α₀ α₁ : ℂ,
      Complex.normSq φ = 1 ∧
      Complex.normSq α₀ = 1 ∧ Complex.normSq α₁ = 1 ∧
      α₀ * α₁ = 1 ∧
      kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![d₀, d₁]) =
        (kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![α₀, α₁])) *
        (kron2 (P_phase φ) 1) := by
  -- Closed iter 1044. Componentwise the claim is
  -- `Diag(1,1,d₀,d₁) = Diag(1,1,α₀,α₁) · Diag(1,1,φ,φ)`, i.e. `αᵢ = dᵢ/φ`;
  -- the det-1 constraint `α₀α₁ = 1` then forces `φ² = d₀d₁`. So φ is a SQUARE
  -- ROOT of `d₀d₁` — the same phenomenon as the two roots in the Section-3
  -- six-gate construction, and the reason the paper's figure carries a P(φ).
  obtain ⟨φ, hφ⟩ := IsAlgClosed.exists_pow_nat_eq (d₀ * d₁) (n := 2) (by norm_num)
  have hd₀0 : d₀ ≠ 0 := fun h => by simp [h] at _hd₀
  have hd₁0 : d₁ ≠ 0 := fun h => by simp [h] at _hd₁
  have hφ0 : φ ≠ 0 := by intro h; rw [h] at hφ; simp at hφ; tauto
  have hnφ : Complex.normSq φ = 1 := by
    have h2 : Complex.normSq φ ^ 2 = 1 := by
      rw [show Complex.normSq φ ^ 2 = Complex.normSq (φ ^ 2) from by
            rw [sq, sq, map_mul], hφ, map_mul, _hd₀, _hd₁, one_mul]
    nlinarith [Complex.normSq_nonneg φ]
  refine ⟨φ, d₀ / φ, d₁ / φ, hnφ, ?_, ?_, ?_, ?_⟩
  · rw [map_div₀, _hd₀, hnφ, div_one]
  · rw [map_div₀, _hd₁, hnφ, div_one]
  · field_simp
    rw [← hφ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [kron2, proj0, proj1, P_phase, Matrix.mul_apply, Matrix.add_apply,
            Matrix.of_apply, Matrix.diagonal_apply, Matrix.one_apply,
            Fin.sum_univ_four] <;>
      field_simp

/-! ## SWAP-conjugated Paige-Wei (iter 197)

Top-level corollary of `paper_lemma_A_4` (Paige-Wei) producing block-diag-
**second** outer factors (w.r.t. slot 2) and block-diag-**first** middle
factor (w.r.t. slot 1). Used in `paper_lemma_4_1` Step 5 to bypass the
SWAP_BC factors that arise from direct SWAP-conjugation of `paper_lemma_A_4`. -/

/-- SWAP_4 conjugation of `kron2 X Y` swaps slots: gives `kron2 Y X`. -/
lemma swap_4_kron2_eq (X Y : Mat2) :
    SWAP_4 * kron2 X Y * SWAP_4 = kron2 Y X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SWAP_4, swap4_perm, kron2, Matrix.mul_apply, Matrix.of_apply,
          Fin.sum_univ_four] <;> ring

/-- SWAP-conjugated Paige-Wei: corollary of `paper_lemma_A_4` producing
    block-diag-second outer factors and block-diag-first middle factor.
    For BC-gate convention (slot 1 = B, slot 2 = C), this gives outer
    factors block-diag-w.r.t.-C and middle factor controlled-R_y-w.r.t.-B
    — exactly paper Fig.6 row 5's M·R·N decomposition. -/
lemma paige_wei_swapped (V : Mat4) (hV : IsUnitary4 V) :
    ∃ P₀ P₁ R_y_θ0 R_y_θ1 Q₀ Q₁ : Mat2,
      IsUnitary2 P₀ ∧ IsUnitary2 P₁ ∧
      IsUnitary2 R_y_θ0 ∧ IsUnitary2 R_y_θ1 ∧
      IsUnitary2 Q₀ ∧ IsUnitary2 Q₁ ∧
      V = (kron2 Q₀ proj0 + kron2 Q₁ proj1) *
          (kron2 proj0 R_y_θ0 + kron2 proj1 R_y_θ1) *
          (kron2 P₀ proj0 + kron2 P₁ proj1) := by
  have hSwapV : IsUnitary4 (SWAP_4 * V * SWAP_4) :=
    isUnitary4_swap4_conj V hV
  obtain ⟨P₀, P₁, R_y_θ0, R_y_θ1, Q₀, Q₁, hP₀, hP₁, hR0, hR1, hQ₀, hQ₁, hSwapV_paige⟩ :=
    paper_lemma_A_4 (SWAP_4 * V * SWAP_4) hSwapV
  refine ⟨P₀, P₁, R_y_θ0, R_y_θ1, Q₀, Q₁, hP₀, hP₁, hR0, hR1, hQ₀, hQ₁, ?_⟩
  have h := SWAP_4_sq
  calc V = 1 * V * 1 := by rw [one_mul, mul_one]
    _ = (SWAP_4 * SWAP_4) * V * (SWAP_4 * SWAP_4) := by rw [h]
    _ = SWAP_4 * (SWAP_4 * V * SWAP_4) * SWAP_4 := by noncomm_ring
    _ = SWAP_4 * ((kron2 proj0 Q₀ + kron2 proj1 Q₁) *
          (kron2 R_y_θ0 proj0 + kron2 R_y_θ1 proj1) *
          (kron2 proj0 P₀ + kron2 proj1 P₁)) * SWAP_4 := by rw [hSwapV_paige]
    _ = SWAP_4 * (kron2 proj0 Q₀ + kron2 proj1 Q₁) * (SWAP_4 * SWAP_4) *
          (kron2 R_y_θ0 proj0 + kron2 R_y_θ1 proj1) * (SWAP_4 * SWAP_4) *
          (kron2 proj0 P₀ + kron2 proj1 P₁) * SWAP_4 := by rw [h]; noncomm_ring
    _ = (SWAP_4 * (kron2 proj0 Q₀ + kron2 proj1 Q₁) * SWAP_4) *
        (SWAP_4 * (kron2 R_y_θ0 proj0 + kron2 R_y_θ1 proj1) * SWAP_4) *
        (SWAP_4 * (kron2 proj0 P₀ + kron2 proj1 P₁) * SWAP_4) := by noncomm_ring
    _ = (kron2 Q₀ proj0 + kron2 Q₁ proj1) *
        (kron2 proj0 R_y_θ0 + kron2 proj1 R_y_θ1) *
        (kron2 P₀ proj0 + kron2 P₁ proj1) := by
          simp only [mul_add, add_mul, swap_4_kron2_eq]

/-! ## Step 5c-3 chain commutation helper (iter 201)

Extracted from inline paper_lemma_4_1 proof to avoid heartbeat blow-up.
Applies `embedBC_blockdiagsec_comm_embedAC_Cdiag` to commute M_paper past
embedAC CRzM and N_paper past embedAC CRzN, producing paper Fig.6 row 7
form. -/

set_option maxHeartbeats 800000 in
lemma chain_step6_commute
    (G₁ G₃R G₅ Pphase : Mat8) (X Y Z W : Mat2) (α_M0 α_M1 α_N0 α_N1 : ℂ) :
    G₁ * embedAC (kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![α_M0, α_M1])) *
      (embedBC (kron2 X proj0 + kron2 Y proj1) * G₃R *
       embedBC (kron2 Z proj0 + kron2 W proj1)) *
      embedAC (kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![α_N0, α_N1])) *
      G₅ * Pphase
    =
    G₁ * embedBC (kron2 X proj0 + kron2 Y proj1) *
      embedAC (kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![α_M0, α_M1])) *
      G₃R *
      embedAC (kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![α_N0, α_N1])) *
      embedBC (kron2 Z proj0 + kron2 W proj1) * G₅ * Pphase := by
  have hM_comm := embedBC_blockdiagsec_comm_embedAC_Cdiag α_M0 α_M1 X Y
  have hN_comm := embedBC_blockdiagsec_comm_embedAC_Cdiag α_N0 α_N1 Z W
  calc G₁ * embedAC (kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![α_M0, α_M1])) *
        (embedBC (kron2 X proj0 + kron2 Y proj1) * G₃R *
         embedBC (kron2 Z proj0 + kron2 W proj1)) *
        embedAC (kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![α_N0, α_N1])) *
        G₅ * Pphase
      = G₁ *
        (embedAC (kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![α_M0, α_M1])) *
         embedBC (kron2 X proj0 + kron2 Y proj1)) *
        G₃R *
        (embedBC (kron2 Z proj0 + kron2 W proj1) *
         embedAC (kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![α_N0, α_N1]))) *
        G₅ * Pphase := by noncomm_ring
    _ = G₁ *
        (embedBC (kron2 X proj0 + kron2 Y proj1) *
         embedAC (kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![α_M0, α_M1]))) *
        G₃R *
        (embedAC (kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![α_N0, α_N1])) *
         embedBC (kron2 Z proj0 + kron2 W proj1)) *
        G₅ * Pphase := by rw [← hM_comm, hN_comm]
    _ = G₁ * embedBC (kron2 X proj0 + kron2 Y proj1) *
        embedAC (kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![α_M0, α_M1])) *
        G₃R *
        embedAC (kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![α_N0, α_N1])) *
        embedBC (kron2 Z proj0 + kron2 W proj1) * G₅ * Pphase := by noncomm_ring

/-! ## Mat8.ofBlockDiag multiplicativity (iter 210)

Helper for Step 5e-2 of `paper_lemma_4_1`: products of `Mat8.ofBlockDiag 1 X`
factors merge by multiplying the X's. Proof: both sides are block-diagonal
on qubit A with top-left block = 1, and bottom-right = X·Y / X·Y. -/

lemma mat8_ofBlockDiag_one_mul (A B : Mat4) :
    Mat8.ofBlockDiag (1 : Mat4) A * Mat8.ofBlockDiag (1 : Mat4) B =
    Mat8.ofBlockDiag (1 : Mat4) (A * B) := by
  apply mat8_eq_of_blocks_off_diag_zero
  · simp [block00_mul, block00_ofBlockDiag, block01_ofBlockDiag, block10_ofBlockDiag]
  · simp [block11_mul, block11_ofBlockDiag, block10_ofBlockDiag, block01_ofBlockDiag]
  · simp [block01_mul, block00_ofBlockDiag, block01_ofBlockDiag, block11_ofBlockDiag]
  · simp [block10_mul, block10_ofBlockDiag, block00_ofBlockDiag, block11_ofBlockDiag]
  · exact block01_ofBlockDiag _ _
  · exact block10_ofBlockDiag _ _

/-! ## Mat8-diagonal helpers for paper_lemma_4_1 Step 5e-5 (iter 217)

Three top-level lemmas reducing `Mat8.ofBlockDiag 1 (Matrix.diagonal _)`,
`embedAC (Matrix.diagonal _)`, `embedAB (Matrix.diagonal _)` to explicit
`Matrix.diagonal ![...]` form on Fin 8. Used in Step 5e-5 of
`paper_lemma_4_1` to reduce the V_2·V_3 split equation from a 64-case
brute force to an 8-case Fin 8 comparison. -/

set_option maxHeartbeats 800000 in
lemma Mat8_ofBlockDiag_one_diag_Fin4 (a b c d : ℂ) :
    Mat8.ofBlockDiag (1 : Mat4) (Matrix.diagonal ![a, b, c, d]) =
    (Matrix.diagonal ![1, 1, 1, 1, a, b, c, d] : Mat8) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Mat8.ofBlockDiag, Matrix.diagonal, Matrix.of_apply, Matrix.one_apply]

set_option maxHeartbeats 800000 in
lemma embedAC_diag_Fin4 (a b c d : ℂ) :
    embedAC (Matrix.diagonal ![a, b, c, d]) =
    (Matrix.diagonal ![a, b, a, b, c, d, c, d] : Mat8) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedAC, Matrix.diagonal, Matrix.of_apply]

set_option maxHeartbeats 800000 in
lemma embedAB_diag_Fin4 (a b c d : ℂ) :
    embedAB (Matrix.diagonal ![a, b, c, d]) =
    (Matrix.diagonal ![a, a, b, b, c, c, d, d] : Mat8) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedAB, Matrix.diagonal, Matrix.of_apply]

set_option maxHeartbeats 800000 in
lemma embedAC_kron2_P_phase_one (φ : ℂ) :
    embedAC (kron2 (P_phase φ) 1) =
    (Matrix.diagonal ![1, 1, 1, 1, φ, φ, φ, φ] : Mat8) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedAC, kron2, P_phase, Matrix.diagonal, Matrix.of_apply, Matrix.one_apply]

/-! ## Permutation P_σ for paper Eq.(5) D reordering (iter 214)

For our spectral output D = diag![γ_0, γ_0', γ_1, γ_1'] (where γ_b·γ_b'=1),
the V_2·V_3 split into AC + AB controlled R_z factors requires D to be
rank-1 separable: D[0]·D[3] = D[1]·D[2]. This fails for our D in general
but is satisfied by D' = diag![γ_0, γ_1, γ_1', γ_0'] where:
  D'[0]·D'[3] = γ_0·γ_0' = 1
  D'[1]·D'[2] = γ_1·γ_1' = 1
Both = 1 (using γ_b·γ_b'=1 derived from det(R_b)=1).

The permutation σ : Fin 4 → Fin 4 with σ(0)=0, σ(1)=2, σ(2)=3, σ(3)=1
(3-cycle (1 2 3) with 0 fixed) gives D'[k] = D[σ(k)]. The corresponding
matrix P_σ : Mat4 satisfies P_σ.conjTranspose * D * P_σ = D'. -/

/-- Permutation matrix for σ = (0)(1 2 3): swap entries (1,2,3) cyclically.
    Entry P_σ[i, j] = 1 iff i = σ(j) — i.e., P_σ[0,0] = P_σ[2,1] = P_σ[3,2]
    = P_σ[1,3] = 1, all others 0. -/
def P_sigma_4 : Mat4 :=
  !![1, 0, 0, 0;
     0, 0, 0, 1;
     0, 1, 0, 0;
     0, 0, 1, 0]

lemma P_sigma_4_unitary : IsUnitary4 P_sigma_4 := by
  unfold IsUnitary4 P_sigma_4
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose, Matrix.mul_apply, Fin.sum_univ_four,
          Matrix.one_apply]

lemma P_sigma_4_conj_diag (a b c d : ℂ) :
    P_sigma_4.conjTranspose * (Matrix.diagonal ![a, b, c, d] : Mat4) * P_sigma_4 =
    Matrix.diagonal ![a, c, d, b] := by
  unfold P_sigma_4
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose, Matrix.mul_apply, Matrix.diagonal,
          Fin.sum_univ_four]

/-- Permutation matrix for σ_swap = (0)(1 2)(3): swap positions 1 and 2.
    Used by `py24_lemma_A_6_swap_ordering` to convert py24_lemma_A_6's
    diag![a,b,p,q] output to diag![a, p, b, q] ordering. -/
def P_swap_4_12 : Mat4 :=
  !![1, 0, 0, 0;
     0, 0, 1, 0;
     0, 1, 0, 0;
     0, 0, 0, 1]

lemma P_swap_4_12_unitary : IsUnitary4 P_swap_4_12 := by
  unfold IsUnitary4 P_swap_4_12
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose, Matrix.mul_apply, Fin.sum_univ_four,
          Matrix.one_apply]

lemma P_swap_4_12_conj_diag (a b c d : ℂ) :
    P_swap_4_12.conjTranspose * (Matrix.diagonal ![a, b, c, d] : Mat4) * P_swap_4_12 =
    Matrix.diagonal ![a, c, b, d] := by
  unfold P_swap_4_12
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose, Matrix.mul_apply, Matrix.diagonal,
          Fin.sum_univ_four]

/-- Variant of `py24_lemma_A_6` returning the swapped diagonal ordering
    `diag![a, p, b, q]` (instead of `diag![a, b, p, q]`). Used by
    `paper_lemma_4_2_joint_spec` to align with `joint_spec_multiplicity_trichotomy`'s
    expected `diag![d₀, d₀, d₁, d₁]` pattern when (a,b) = (p,q) = (d₀, d₁). -/
lemma py24_lemma_A_6_swap_ordering (P Q : Mat2)
    (hP : IsUnitary2 P) (hQ : IsUnitary2 Q)
    (a b p q : ℂ)
    (hPeig : ∃ V : Mat2, IsUnitary2 V ∧
      V.conjTranspose * P * V = Matrix.diagonal ![a, b])
    (hQeig : ∃ W : Mat2, IsUnitary2 W ∧
      W.conjTranspose * Q * W = Matrix.diagonal ![p, q]) :
    ∃ U : Mat4, IsUnitary4 U ∧
      U.conjTranspose * (kron2 proj0 P + kron2 proj1 Q) * U =
        Matrix.diagonal ![a, p, b, q] := by
  obtain ⟨U₀, hU₀_unit, hU₀_eq⟩ := py24_lemma_A_6 P Q hP hQ a b p q hPeig hQeig
  refine ⟨U₀ * P_swap_4_12, ?_, ?_⟩
  · exact isUnitary4_mul hU₀_unit P_swap_4_12_unitary
  · rw [Matrix.conjTranspose_mul]
    calc P_swap_4_12.conjTranspose * U₀.conjTranspose *
         (kron2 proj0 P + kron2 proj1 Q) * (U₀ * P_swap_4_12)
        = P_swap_4_12.conjTranspose *
          (U₀.conjTranspose * (kron2 proj0 P + kron2 proj1 Q) * U₀) *
          P_swap_4_12 := by noncomm_ring
      _ = P_swap_4_12.conjTranspose *
          (Matrix.diagonal ![a, b, p, q] : Mat4) * P_swap_4_12 := by rw [hU₀_eq]
      _ = Matrix.diagonal ![a, p, b, q] := P_swap_4_12_conj_diag a b p q

/-- Unitary conjugation inversion (Mat2): if V is unitary and V† · A · V = D,
    then A = V · D · V†. Useful for converting spectral hypotheses (which
    are typically stated in V†·A·V form) into the inverse direction A = V·D·V†
    needed for substitution. Iter 233 infrastructure for
    `paper_4_2_eq_7_9_chain_rewrite`. -/
lemma unitary_conj_invert_Mat2 {V A D : Mat2} (hV : IsUnitary2 V)
    (h : V.conjTranspose * A * V = D) :
    A = V * D * V.conjTranspose := by
  have hVV : V * V.conjTranspose = 1 := Matrix.mul_eq_one_comm.mp hV
  have heq : V * (V.conjTranspose * A * V) * V.conjTranspose =
             V * D * V.conjTranspose := by rw [h]
  rw [show V * (V.conjTranspose * A * V) * V.conjTranspose =
        (V * V.conjTranspose) * A * (V * V.conjTranspose) from by noncomm_ring,
      hVV, one_mul, mul_one] at heq
  exact heq

/-- Unitary conjugation inversion (Mat4): if V is unitary4 and V† · A · V = D,
    then A = V · D · V†. Mat4 variant of `unitary_conj_invert_Mat2`. -/
lemma unitary_conj_invert_Mat4 {V A D : Mat4} (hV : IsUnitary4 V)
    (h : V.conjTranspose * A * V = D) :
    A = V * D * V.conjTranspose := by
  have hVV : V * V.conjTranspose = 1 := Matrix.mul_eq_one_comm.mp hV
  have heq : V * (V.conjTranspose * A * V) * V.conjTranspose =
             V * D * V.conjTranspose := by rw [h]
  rw [show V * (V.conjTranspose * A * V) * V.conjTranspose =
        (V * V.conjTranspose) * A * (V * V.conjTranspose) from by noncomm_ring,
      hVV, one_mul, mul_one] at heq
  exact heq

/-- Reusable corollary: if both X_eig and Y_eig have spectrum (d₀, d₁), then
    `kron2 proj0 X_eig + kron2 proj1 Y_eig` is unitarily diagonalizable to
    `diag![d₀, d₀, d₁, d₁]`. This is the exact pattern that
    `paper_lemma_4_2_joint_spec` needs (and what joint_spec_multiplicity_trichotomy
    consumes as its `h_joint_spec` hypothesis).

    Closing `paper_lemma_4_2_joint_spec` reduces to deriving the two spec
    hypotheses from paper Eq.(6)'s chain identity. -/
-- ⚠️ SUPERSEDED (iter 1034): `paper_lemma_4_2_joint_spec` was closed by the
-- Π-decomposition route instead (it produces `M_joint = U₂·(1⊗Diag(1,d₁))·U₂†`
-- directly, so no per-block spec witnesses are needed). This lemma is correct
-- and still usable, but is currently unreferenced.
lemma paper_lemma_4_2_joint_spec_from_pattern
    (X_eig Y_eig : Mat2)
    (hX_unit : IsUnitary2 X_eig) (hY_unit : IsUnitary2 Y_eig)
    (d₀ d₁ : ℂ)
    (h_X_spec : ∃ V : Mat2, IsUnitary2 V ∧
      V.conjTranspose * X_eig * V = Matrix.diagonal ![d₀, d₁])
    (h_Y_spec : ∃ W : Mat2, IsUnitary2 W ∧
      W.conjTranspose * Y_eig * W = Matrix.diagonal ![d₀, d₁]) :
    ∃ W : Mat4, IsUnitary4 W ∧
      W.conjTranspose * (kron2 proj0 X_eig + kron2 proj1 Y_eig) * W =
        Matrix.diagonal ![d₀, d₀, d₁, d₁] :=
  py24_lemma_A_6_swap_ordering X_eig Y_eig hX_unit hY_unit
    d₀ d₁ d₀ d₁ h_X_spec h_Y_spec

/-! ## embedBC absorbs into Mat8.ofBlockDiag conjugation (iter 211)

For F : Mat4 with `F · F† = 1` (right-unitarity), the conjugation
`embedBC F · Mat8.ofBlockDiag 1 X · embedBC F†` collapses to
`Mat8.ofBlockDiag 1 (F · X · F†)`. Proof: block-decomposition on qubit A.
Top-left block becomes F·1·F† = F·F† = 1; bottom-right becomes F·X·F†;
off-diagonals stay zero. -/

lemma embedBC_conj_ofBlockDiag_one (V X : Mat4)
    (hVV : V * V.conjTranspose = 1) :
    embedBC V * Mat8.ofBlockDiag (1 : Mat4) X * embedBC V.conjTranspose =
    Mat8.ofBlockDiag (1 : Mat4) (V * X * V.conjTranspose) := by
  apply mat8_eq_of_blocks_off_diag_zero
  · simp [block00_mul, block00_embedBC, block01_embedBC, block10_embedBC,
          block00_ofBlockDiag, block01_ofBlockDiag, block10_ofBlockDiag, hVV]
  · simp [block11_mul, block11_embedBC, block10_embedBC, block01_embedBC,
          block11_ofBlockDiag, block10_ofBlockDiag, block01_ofBlockDiag]
  · simp [block01_mul, block00_embedBC, block01_embedBC, block11_embedBC,
          block00_ofBlockDiag, block01_ofBlockDiag, block11_ofBlockDiag]
  · simp [block10_mul, block10_embedBC, block00_embedBC, block11_embedBC,
          block10_ofBlockDiag, block00_ofBlockDiag, block11_ofBlockDiag]
  · exact block01_ofBlockDiag _ _
  · exact block10_ofBlockDiag _ _

/-! ## Step 5 prerequisites: paper Lemmas 4.1, 4.2 and 4.3 (scaffolding stubs)

These are the "block-diagonal middle gate" reduction lemmas. Their proofs
are separate paper-level work (~1-2 weeks each); stated here as scaffolding
so Step 5 can call them. -/

/-- **HP paper Lemma 4.1** ("key calculation", page 9, Fig.6).
    The genuine 5→4 BASE REDUCTION: if both AC-acting middle gates of a
    5-gate BC-AC-BC-AC-BC chain are *controlled-A on the |1⟩ branch*
    (i.e., `kron2 proj0 1 + kron2 proj1 M`, equivalently |0⟩⟨0|⊗I + |1⟩⟨1|⊗M),
    then the chain equals a diagonal gate iff it factors as a 4-gate
    BC-AC-AB-BC chain.

    Hypotheses:
    - `F₁, F₃, F₅` : 2-qubit unitaries (outer BC factors).
    - `M, N` : 1-qubit unitaries (the |1⟩-branch single-qubit "controls").
    - the chain `BC F₁ · AC(C(M)) · BC F₃ · AC(C(N)) · BC F₅ = D`.

    **Proof outline** (paper Fig.6): unfold each `C(·)` via Lemma A.5 into
    `Diag(d_q₀, d_q₁) ⊗ I`-style + `L/L†` layers, commute via Lemma A.7,
    identify the canonical `G₅ · F† · R_z · R_z · F · G₁` form.

    **Proof status**: scaffolding stub. The most foundational sorry of the
    HP paper formalization — both Lemma 4.2 (case (1) of its A.12 trichotomy)
    and Lemma 4.3 (final step) reduce to this lemma. -/
theorem paper_lemma_4_1 (Dg : DiagGate3)
    (F₁ F₃ F₅ : Mat4)
    (_hF₁ : IsUnitary4 F₁) (_hF₃ : IsUnitary4 F₃) (_hF₅ : IsUnitary4 F₅)
    (M N : Mat2) (hM : IsUnitary2 M) (hN : IsUnitary2 N)
    (h_chain : Dg.toMatrix =
      embedBC F₁ * embedAC (kron2 proj0 1 + kron2 proj1 M) *
      embedBC F₃ * embedAC (kron2 proj0 1 + kron2 proj1 N) * embedBC F₅) :
    ∃ V₁ V₂ V₃ V₄ : Mat4,
      IsUnitary4 V₁ ∧ IsUnitary4 V₂ ∧ IsUnitary4 V₃ ∧ IsUnitary4 V₄ ∧
      Dg.toMatrix = embedBC V₁ * embedAC V₂ * embedAB V₃ * embedBC V₄ := by
  -- **Paper Fig.6 Step 1**: unfold each `C(M)` and `C(N)` via Lemma A.5
  -- (`blockDiagA_spectral`, added iter 127) into spectral form
  -- `(I⊗V_X) · (P0⊗I + P1⊗Diag) · (I⊗V_X†)`.
  obtain ⟨V_M, d_M0, d_M1, hV_M, hd_M0, hd_M1, hC_M_eq⟩ :=
    blockDiagA_spectral M hM
  obtain ⟨V_N, d_N0, d_N1, hV_N, hd_N0, hd_N1, hC_N_eq⟩ :=
    blockDiagA_spectral N hN
  -- Substitute the spectral forms into the chain hypothesis.
  rw [hC_M_eq, hC_N_eq] at h_chain
  -- **Step 2 (paper Fig.6)**: absorb V_M, V_N single-qubit layers into
  -- adjacent embedBC factors.
  -- (a) Distribute embedAC over inner products + (b) convert embedAC(kron2 1 X)
  -- to embedBC(kron2 1 X), reaching a flat 9-factor chain with
  -- consecutive embedBC factors that can merge.
  have h_chain_flat :
      Dg.toMatrix =
      embedBC F₁ * embedBC (kron2 1 V_M) *
      embedAC (kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![d_M0, d_M1])) *
      embedBC (kron2 1 V_M.conjTranspose) * embedBC F₃ *
      embedBC (kron2 1 V_N) *
      embedAC (kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![d_N0, d_N1])) *
      embedBC (kron2 1 V_N.conjTranspose) * embedBC F₅ := by
    rw [h_chain]
    simp only [← embedAC_mul,
               ← embedBC_kron2_one_eq_embedAC_kron2_one V_M,
               ← embedBC_kron2_one_eq_embedAC_kron2_one V_M.conjTranspose,
               ← embedBC_kron2_one_eq_embedAC_kron2_one V_N,
               ← embedBC_kron2_one_eq_embedAC_kron2_one V_N.conjTranspose]
    noncomm_ring
  -- (c) Combine consecutive embedBC factors via embedBC_mul (forward direction:
  -- `embedBC V * embedBC W = embedBC (V * W)` — merging). Add mul_assoc to
  -- expose all embedBC-pairs (default left-association hides inner pairs).
  simp only [mul_assoc, embedBC_mul] at h_chain_flat
  -- After this, h_chain_flat has the form:
  --   Dg.toMatrix = embedBC G₁
  --              · embedAC (kron2 proj0 1 + kron2 proj1 Diag_M)   -- = C(Diag_M)_AC
  --              · embedBC G₃
  --              · embedAC (kron2 proj0 1 + kron2 proj1 Diag_N)   -- = C(Diag_N)_AC
  --              · embedBC G₅
  -- where G₁ = F₁ · kron2 1 V_M, G₃ = kron2 1 V_M† · F₃ · kron2 1 V_N,
  --       G₅ = kron2 1 V_N† · F₅.
  --
  -- **Step 3 EXECUTED below**: apply paper Lemma A.6 to split each C(Diag).
  -- ============================================================================
  obtain ⟨φ_M, α_M0, α_M1, _hφ_M, _hα_M0, _hα_M1, _hα_M_det, hA6_M⟩ :=
    paper_lemma_A_6 d_M0 d_M1 hd_M0 hd_M1
  obtain ⟨φ_N, α_N0, α_N1, _hφ_N, _hα_N0, _hα_N1, _hα_N_det, hA6_N⟩ :=
    paper_lemma_A_6 d_N0 d_N1 hd_N0 hd_N1
  -- After substitution: each `embedAC (C(Diag_M))` becomes
  --   embedAC (C(R_z(α_M)) · (P_phase φ_M ⊗ I))
  -- (paper-faithful A.6 matrix-product form: C(R_z) leftmost, P(φ)⊗I rightmost).
  rw [hA6_M, hA6_N] at h_chain_flat
  -- Distribute embedAC over the products to get a flat 7-factor chain:
  --   embedBC G₁
  --   · embedAC (C(R_z α_M))
  --   · embedAC (P_phase φ_M ⊗ 1)
  --   · embedBC G₃
  --   · embedAC (C(R_z α_N))
  --   · embedAC (P_phase φ_N ⊗ 1)
  --   · embedBC G₅
  simp only [← embedAC_mul] at h_chain_flat
  -- =========================================================================
  -- Step 4: Move P(φ_M) and P(φ_N) phase factors to the right end via
  -- commutations, then merge them into a single phase.
  -- =========================================================================
  -- Helper C1: kron2 (P_phase φ) 1 commutes with C(Diag α₀ α₁) = kron2 proj0 1
  -- + kron2 proj1 (diagonal ![α₀, α₁]) as 4×4 matrices. Both are block-diag-first
  -- and the |0⟩/|1⟩ branches commute pairwise (P_phase and diagonals commute).
  have hC1 : ∀ (φ α₀ α₁ : ℂ),
      kron2 (P_phase φ) 1 *
        (kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![α₀, α₁])) =
      (kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![α₀, α₁])) *
        kron2 (P_phase φ) 1 := by
    intros φ α₀ α₁
    simp only [mul_add, add_mul, kron2_mul, mul_one, one_mul]
    congr 1
    · -- proj0 branch: P_phase·proj0 = proj0·P_phase (both = proj0)
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [P_phase, proj0, Matrix.mul_apply, Fin.sum_univ_two,
              Matrix.diagonal, Matrix.of_apply]
    · -- proj1 branch: P_phase·proj1 = proj1·P_phase
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [P_phase, proj1, Matrix.mul_apply, Fin.sum_univ_two,
              Matrix.diagonal, Matrix.of_apply]
  -- Helper C2: embedAC (kron2 X 1) commutes with embedBC V (disjoint qubits).
  -- embedAC (kron2 X 1) = singleQubitLayer X I₂ I₂ via embedAC_kron2.
  -- Then embedBC_comm_singleQubitLayer_A gives the commutation.
  have hC2 : ∀ (X : Mat2) (V : Mat4),
      embedAC (kron2 X 1) * embedBC V = embedBC V * embedAC (kron2 X 1) := by
    intros X V
    simp only [embedAC_kron2]
    exact (embedBC_comm_singleQubitLayer_A V X).symm
  -- Lifted commutation: embedAC(P_phase⊗1) commutes with embedAC(C(R_z)).
  -- Proof: lift hC1 through embedAC_mul (embedAC A · embedAC B = embedAC (A·B)).
  have hC1_lifted : ∀ (φ α₀ α₁ : ℂ),
      embedAC (kron2 (P_phase φ) 1) *
        embedAC (kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![α₀, α₁])) =
      embedAC (kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![α₀, α₁])) *
        embedAC (kron2 (P_phase φ) 1) := by
    intros φ α₀ α₁
    rw [embedAC_mul, hC1, ← embedAC_mul]
  -- Merger of two adjacent phase factors:
  --   embedAC (kron2 (P_phase φ₁) 1) · embedAC (kron2 (P_phase φ₂) 1)
  --   = embedAC (kron2 (P_phase (φ₁ · φ₂)) 1)
  have h_phase_merge : ∀ (φ₁ φ₂ : ℂ),
      embedAC (kron2 (P_phase φ₁) 1) * embedAC (kron2 (P_phase φ₂) 1) =
      embedAC (kron2 (P_phase (φ₁ * φ₂)) 1) := by
    intros φ₁ φ₂
    rw [embedAC_mul, kron2_mul, P_phase_mul, mul_one]
  -- Now execute Step 4 chain rewrite using hC1_lifted, hC2, h_phase_merge.
  -- Set abbreviations to keep the chain readable.
  set G₁ : Mat4 := F₁ * kron2 1 V_M with hG₁
  set G₃ : Mat4 := kron2 1 V_M.conjTranspose * (F₃ * kron2 1 V_N) with hG₃
  set G₅ : Mat4 := kron2 1 V_N.conjTranspose * F₅ with hG₅
  set CRzM : Mat4 :=
    kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![α_M0, α_M1]) with hCRzM
  set CRzN : Mat4 :=
    kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![α_N0, α_N1]) with hCRzN
  set PM : Mat4 := kron2 (P_phase φ_M) 1 with hPM
  set PN : Mat4 := kron2 (P_phase φ_N) 1 with hPN
  -- The two specialised commutation facts at the values that appear in the chain.
  have hPM_CRzN : embedAC PM * embedAC CRzN = embedAC CRzN * embedAC PM :=
    hC1_lifted φ_M α_N0 α_N1
  have hPM_G₃ : embedAC PM * embedBC G₃ = embedBC G₃ * embedAC PM :=
    hC2 (P_phase φ_M) G₃
  have hPM_PN : embedAC PM * embedAC PN = embedAC (kron2 (P_phase (φ_M * φ_N)) 1) :=
    h_phase_merge φ_M φ_N
  have hPN_G₅ : embedAC PN * embedBC G₅ = embedBC G₅ * embedAC PN :=
    hC2 (P_phase φ_N) G₅
  have hPM_G₅ : embedAC PM * embedBC G₅ = embedBC G₅ * embedAC PM :=
    hC2 (P_phase φ_M) G₅
  -- Calc block executing Step 4: move PM, PN to the right end and merge.
  have h_step4 : Dg.toMatrix =
      embedBC G₁ * embedAC CRzM * embedBC G₃ * embedAC CRzN * embedBC G₅ *
      embedAC (kron2 (P_phase (φ_M * φ_N)) 1) := by
    calc Dg.toMatrix
        = embedBC G₁ * (embedAC CRzM * embedAC PM *
            (embedBC G₃ * (embedAC CRzN * embedAC PN * embedBC G₅))) := h_chain_flat
      _ = embedBC G₁ * embedAC CRzM * (embedAC PM * embedBC G₃) *
          embedAC CRzN * embedAC PN * embedBC G₅ := by noncomm_ring
      _ = embedBC G₁ * embedAC CRzM * (embedBC G₃ * embedAC PM) *
          embedAC CRzN * embedAC PN * embedBC G₅ := by rw [hPM_G₃]
      _ = embedBC G₁ * embedAC CRzM * embedBC G₃ *
          (embedAC PM * embedAC CRzN) * embedAC PN * embedBC G₅ := by noncomm_ring
      _ = embedBC G₁ * embedAC CRzM * embedBC G₃ *
          (embedAC CRzN * embedAC PM) * embedAC PN * embedBC G₅ := by rw [hPM_CRzN]
      _ = embedBC G₁ * embedAC CRzM * embedBC G₃ * embedAC CRzN *
          (embedAC PM * embedAC PN) * embedBC G₅ := by noncomm_ring
      _ = embedBC G₁ * embedAC CRzM * embedBC G₃ * embedAC CRzN *
          embedAC (kron2 (P_phase (φ_M * φ_N)) 1) * embedBC G₅ := by rw [hPM_PN]
      _ = embedBC G₁ * embedAC CRzM * embedBC G₃ * embedAC CRzN *
          (embedAC (kron2 (P_phase (φ_M * φ_N)) 1) * embedBC G₅) := by noncomm_ring
      _ = embedBC G₁ * embedAC CRzM * embedBC G₃ * embedAC CRzN *
          (embedBC G₅ * embedAC (kron2 (P_phase (φ_M * φ_N)) 1)) := by
        rw [hC2 (P_phase (φ_M * φ_N)) G₅]
      _ = embedBC G₁ * embedAC CRzM * embedBC G₃ * embedAC CRzN * embedBC G₅ *
          embedAC (kron2 (P_phase (φ_M * φ_N)) 1) := by noncomm_ring
  -- =========================================================================
  -- Step 4 DONE: h_step4 has the canonical form
  --   Dg.toMatrix = BC G₁ · AC C(R_z_M) · BC G₃ · AC C(R_z_N) · BC G₅
  --                · AC (kron2 (P_phase (φ_M·φ_N)) 1).
  -- =========================================================================
  -- Step 5 PLAN (per paper Fig.6, rows 5-8; complete construction below).
  --
  -- Paper variable mapping (matrix-product order, our Lean ↔ paper):
  --   G₁ ↔ W₁,   α_M ↔ α (paper),   G₃ ↔ W₃,   α_N ↔ β (paper),   G₅ ↔ W₅.
  -- After Step 4, P_phase(φ_M·φ_N) ↔ paper's P(φ).
  --
  -- 5a (Paige-Wei A.4 decomp of G₃): G₃ = (kron2 proj0 Q₀ + kron2 proj1 Q₁) ·
  --      (kron2 R_y_θ0 proj0 + kron2 R_y_θ1 proj1) ·
  --      (kron2 proj0 P₀ + kron2 proj1 P₁).
  --   Call these M = (Q-side), R = (R_y middle), N = (P-side) for paper-naming.
  --   Each Q_i, P_i, R_y_θ_i are 1-qubit unitaries. R is block-diag-second
  --   (controlled by qubit 2 = C in BC).
  --
  -- 5b (commutation): M and N commute with embedAC C(R_z α_M) and embedAC
  --   C(R_z α_N) respectively, because M/N have block-diag structure w.r.t.
  --   one BC-wire and C(R_z) is diagonal on C. Move M past C(R_z α_M) into
  --   G₁ (defining G_1' = G₁·M_outer), and N past C(R_z α_N) into G₅
  --   (defining G_5' = R·N·G₅).
  --
  -- 5c (insert RR†, absorb): Insert canceling pair RR† around the middle.
  --   The middle controlled-R_y · R_z(α_N) · R_y† · R_z(α_M) collapses,
  --   evaluated on |B=b⟩ branch, to:
  --     R_b = R_z(α_M) · R_y(θ_b) · R_z(α_N) · R_y(-θ_b)
  --   for b ∈ {0,1}. Both R_0, R_1 are det-1 1-qubit unitaries.
  --
  -- 5d (spectral A.2 on R_0, R_1): Each R_b = F_b · diag(e^{iγ_b}, e^{-iγ_b}) · F_b†.
  --   Build F := kron2 proj0 F_0 + kron2 proj1 F_1 (block-diag-first w.r.t. B,
  --   acting on C). F is a 2-qubit BC gate.
  --
  -- 5e (assembly): The middle block, conjugated by F† and F, becomes
  --   diag-controlled-by-AB. Split as:
  --     C(R_z(γ_1 - γ_0)) on AC · C(R_z(γ_0 + γ_1)) on AB
  --   via the standard 2-controlled-Diag decomposition (paper's "if A=1,
  --   ... depending on B, ..." analysis).
  --
  -- Final witnesses (per paper text):
  --   V_1 := G_1 · F                  (BC, 2-qubit)
  --   V_2 := C(R_z(γ_1 - γ_0))        (AC, 2-qubit)
  --   V_3 := C(R_z(γ_0 + γ_1)) · (P_phase φ_total ⊗ I)   (AB, 2-qubit)
  --   V_4 := F† · G_5                 (BC, 2-qubit)
  --
  -- Step 5 is roughly 600-1000 lines of careful chain rewriting + paper
  -- A.4 invocation + spectral A.2 invocation + final assembly. Each
  -- sub-step (5a-5e) is itself a multi-hundred-line lemma.
  -- =========================================================================
  -- Step 5a EXECUTED: apply paper_lemma_A_4 (Paige-Wei) to G₃.
  -- First establish G₃ is unitary (product of unitaries).
  have hG₃_unit : IsUnitary4 G₃ := by
    show IsUnitary4 (kron2 1 V_M.conjTranspose * (F₃ * kron2 1 V_N))
    exact isUnitary4_mul
      (isUnitary4_kron2 isUnitary2_one (isUnitary2_conjTranspose hV_M))
      (isUnitary4_mul _hF₃ (isUnitary4_kron2 isUnitary2_one hV_N))
  -- Paige-Wei decomposition of G₃ = (block-diag-first Q) · (block-diag-second R) ·
  --   (block-diag-first P), with 6 1-qubit unitaries.
  -- Paper-naming: this gives W_3 = M · R · N where M ↔ Q-block, N ↔ P-block.
  obtain ⟨P₀, P₁, R_y_θ0, R_y_θ1, Q₀, Q₁,
          hP₀, hP₁, hR_y_θ0, hR_y_θ1, hQ₀, hQ₁, hG₃_paige⟩ :=
    paper_lemma_A_4 G₃ hG₃_unit
  -- hG₃_paige : G₃ = M_paige · R_paige · N_paige (Paige-Wei form)
  --   M_paige = kron2 proj0 Q₀ + kron2 proj1 Q₁  (block-diag-first w.r.t. B)
  --   R_paige = kron2 R_y_θ0 proj0 + kron2 R_y_θ1 proj1  (block-diag-second w.r.t. C)
  --   N_paige = kron2 proj0 P₀ + kron2 proj1 P₁  (block-diag-first w.r.t. B)
  --
  -- Step 5b EXECUTED: SWAP_4 conjugation helper + adapter.
  -- Helper: SWAP_4 conjugation of a kron2 swaps its slots.
  --   SWAP_4 · (kron2 X Y) · SWAP_4 = kron2 Y X.
  have hSWAP_kron2 : ∀ (X Y : Mat2), SWAP_4 * kron2 X Y * SWAP_4 = kron2 Y X := by
    intros X Y
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SWAP_4, swap4_perm, kron2, Matrix.mul_apply, Matrix.of_apply,
            Fin.sum_univ_four] <;> ring
  -- Swap conjugation of M_paige (block-diag-first w.r.t. B) gives block-diag-
  -- second w.r.t. C, matching paper's M (block-diag-w.r.t.-C-wire).
  have h_M_swap : SWAP_4 * (kron2 proj0 Q₀ + kron2 proj1 Q₁) * SWAP_4 =
      kron2 Q₀ proj0 + kron2 Q₁ proj1 := by
    simp only [mul_add, add_mul, hSWAP_kron2]
  -- Swap conjugation of R_paige (block-diag-second w.r.t. C) gives block-diag-
  -- first w.r.t. B, matching paper's controlled-R_y form.
  have h_R_swap : SWAP_4 * (kron2 R_y_θ0 proj0 + kron2 R_y_θ1 proj1) * SWAP_4 =
      kron2 proj0 R_y_θ0 + kron2 proj1 R_y_θ1 := by
    simp only [mul_add, add_mul, hSWAP_kron2]
  -- Swap conjugation of N_paige (block-diag-first w.r.t. B) gives block-diag-
  -- second w.r.t. C, matching paper's N.
  have h_N_swap : SWAP_4 * (kron2 proj0 P₀ + kron2 proj1 P₁) * SWAP_4 =
      kron2 P₀ proj0 + kron2 P₁ proj1 := by
    simp only [mul_add, add_mul, hSWAP_kron2]
  -- Assembled SWAP-conjugated Paige-Wei form (paper Fig.6 row 5):
  --   SWAP_4 · G₃ · SWAP_4 = M_paper · R_paper · N_paper
  -- where M_paper, N_paper are block-diag-w.r.t.-C and R_paper is the
  -- block-diag-w.r.t.-B controlled-R_y. Equivalent to applying Paige-Wei
  -- in the B↔C-swapped frame.
  have h_G3_swap : SWAP_4 * G₃ * SWAP_4 =
      (kron2 Q₀ proj0 + kron2 Q₁ proj1) *
      (kron2 proj0 R_y_θ0 + kron2 proj1 R_y_θ1) *
      (kron2 P₀ proj0 + kron2 P₁ proj1) := by
    rw [← h_M_swap, ← h_R_swap, ← h_N_swap, hG₃_paige]
    have h := SWAP_4_sq
    calc SWAP_4 * ((kron2 proj0 Q₀ + kron2 proj1 Q₁) *
             (kron2 R_y_θ0 proj0 + kron2 R_y_θ1 proj1) *
             (kron2 proj0 P₀ + kron2 proj1 P₁)) * SWAP_4
        = SWAP_4 * (kron2 proj0 Q₀ + kron2 proj1 Q₁) * (SWAP_4 * SWAP_4) *
          (kron2 R_y_θ0 proj0 + kron2 R_y_θ1 proj1) * (SWAP_4 * SWAP_4) *
          (kron2 proj0 P₀ + kron2 proj1 P₁) * SWAP_4 := by rw [h]; noncomm_ring
      _ = (SWAP_4 * (kron2 proj0 Q₀ + kron2 proj1 Q₁) * SWAP_4) *
          (SWAP_4 * (kron2 R_y_θ0 proj0 + kron2 R_y_θ1 proj1) * SWAP_4) *
          (SWAP_4 * (kron2 proj0 P₀ + kron2 proj1 P₁) * SWAP_4) := by noncomm_ring
  -- Step 5c-1: 3-qubit commutation via top-level `embedBC_blockdiagsec_comm_
  -- embedAC_Cdiag` lemma below (extracted from inline have to avoid heartbeat
  -- timeout in this large proof context).
  -- Step 5c-2 EXECUTED: derive `embedBC G₃` in SWAP_BC-bracketed form.
  -- Using h_G3_swap : SWAP_4·G₃·SWAP_4 = M_paper·R_paper·N_paper and SWAP_4_sq,
  -- we get G₃ = SWAP_4·(M_paper·R_paper·N_paper)·SWAP_4. Distributing embedBC
  -- via embedBC_mul + SWAP_BC_eq_embedBC gives the 5-factor SWAP_BC-bracketed
  -- form of embedBC G₃.
  have h_G3_emit : embedBC G₃ =
      SWAP_BC * embedBC (kron2 Q₀ proj0 + kron2 Q₁ proj1) *
        embedBC (kron2 proj0 R_y_θ0 + kron2 proj1 R_y_θ1) *
        embedBC (kron2 P₀ proj0 + kron2 P₁ proj1) * SWAP_BC := by
    have hG3eq : G₃ = SWAP_4 * ((kron2 Q₀ proj0 + kron2 Q₁ proj1) *
          (kron2 proj0 R_y_θ0 + kron2 proj1 R_y_θ1) *
          (kron2 P₀ proj0 + kron2 P₁ proj1)) * SWAP_4 := by
      have h := SWAP_4_sq
      calc G₃ = 1 * G₃ * 1 := by rw [one_mul, mul_one]
        _ = (SWAP_4 * SWAP_4) * G₃ * (SWAP_4 * SWAP_4) := by rw [h]
        _ = SWAP_4 * (SWAP_4 * G₃ * SWAP_4) * SWAP_4 := by noncomm_ring
        _ = SWAP_4 * ((kron2 Q₀ proj0 + kron2 Q₁ proj1) *
              (kron2 proj0 R_y_θ0 + kron2 proj1 R_y_θ1) *
              (kron2 P₀ proj0 + kron2 P₁ proj1)) * SWAP_4 := by rw [h_G3_swap]
    rw [hG3eq, SWAP_BC_eq_embedBC]
    simp only [← embedBC_mul]
    noncomm_ring
  -- Step 5c-2-NEW (iter 198): re-derive embedBC G₃ via `paige_wei_swapped`
  -- bypassing the SWAP_BC factors that h_G3_emit had. Get fresh primed
  -- decomposition variables to avoid name shadowing with hG₃_paige's M/R/N.
  obtain ⟨P₀', P₁', R_y_θ0', R_y_θ1', Q₀', Q₁', hP₀', hP₁', hR0', hR1', hQ₀', hQ₁',
          hG₃_swapped⟩ := paige_wei_swapped G₃ hG₃_unit
  have h_embedBC_G3 : embedBC G₃ =
      embedBC (kron2 Q₀' proj0 + kron2 Q₁' proj1) *
      embedBC (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
      embedBC (kron2 P₀' proj0 + kron2 P₁' proj1) := by
    rw [hG₃_swapped]
    simp only [← embedBC_mul]
  -- Substitute h_embedBC_G3 into h_step4 to get a SWAP_BC-free chain.
  have h_step5 : Dg.toMatrix =
      embedBC G₁ * embedAC CRzM *
      (embedBC (kron2 Q₀' proj0 + kron2 Q₁' proj1) *
       embedBC (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
       embedBC (kron2 P₀' proj0 + kron2 P₁' proj1)) *
      embedAC CRzN * embedBC G₅ *
      embedAC (kron2 (P_phase (φ_M * φ_N)) 1) := by
    rw [h_step4, h_embedBC_G3]
  -- Step 5c-3 EXECUTED via top-level `chain_step6_commute`.
  -- Result: paper Fig.6 row 7 form — M_paper commuted out to the left,
  -- N_paper commuted out to the right.
  have h_step6 : Dg.toMatrix =
      embedBC G₁ * embedBC (kron2 Q₀' proj0 + kron2 Q₁' proj1) *
      embedAC CRzM *
      embedBC (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
      embedAC CRzN *
      embedBC (kron2 P₀' proj0 + kron2 P₁' proj1) * embedBC G₅ *
      embedAC (kron2 (P_phase (φ_M * φ_N)) 1) := by
    rw [h_step5, hCRzM, hCRzN]
    exact chain_step6_commute (embedBC G₁)
      (embedBC (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1'))
      (embedBC G₅)
      (embedAC (kron2 (P_phase (φ_M * φ_N)) 1))
      Q₀' Q₁' P₀' P₁' α_M0 α_M1 α_N0 α_N1
  -- Step 5c-3-merge EXECUTED: absorb M_paper into G₁ (G_1_new = G₁·M_paper)
  -- and N_paper into G₅ (G_5_new = N_paper·G₅) per paper Fig.6 row 7.
  have h_step7 : Dg.toMatrix =
      embedBC (G₁ * (kron2 Q₀' proj0 + kron2 Q₁' proj1)) *
      embedAC CRzM *
      embedBC (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
      embedAC CRzN *
      embedBC ((kron2 P₀' proj0 + kron2 P₁' proj1) * G₅) *
      embedAC (kron2 (P_phase (φ_M * φ_N)) 1) := by
    calc Dg.toMatrix
        = embedBC G₁ * embedBC (kron2 Q₀' proj0 + kron2 Q₁' proj1) * embedAC CRzM *
          embedBC (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') * embedAC CRzN *
          embedBC (kron2 P₀' proj0 + kron2 P₁' proj1) * embedBC G₅ *
          embedAC (kron2 (P_phase (φ_M * φ_N)) 1) := h_step6
      _ = (embedBC G₁ * embedBC (kron2 Q₀' proj0 + kron2 Q₁' proj1)) * embedAC CRzM *
          embedBC (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') * embedAC CRzN *
          (embedBC (kron2 P₀' proj0 + kron2 P₁' proj1) * embedBC G₅) *
          embedAC (kron2 (P_phase (φ_M * φ_N)) 1) := by noncomm_ring
      _ = embedBC (G₁ * (kron2 Q₀' proj0 + kron2 Q₁' proj1)) * embedAC CRzM *
          embedBC (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') * embedAC CRzN *
          embedBC ((kron2 P₀' proj0 + kron2 P₁' proj1) * G₅) *
          embedAC (kron2 (P_phase (φ_M * φ_N)) 1) := by rw [embedBC_mul, embedBC_mul]
  -- =========================================================================
  -- Step 5c-4a (iter 205): insert R†·R = I between embedAC CRzN and
  -- embedBC G_5_new, then absorb the new R into G_5_new.
  -- =========================================================================
  have hR_paper_unitary : IsUnitary4
      (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') :=
    controlled_A_unitary hR0' hR1'
  have hRdR : (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1').conjTranspose *
              (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') = 1 := hR_paper_unitary
  have h_step8 : Dg.toMatrix =
      embedBC (G₁ * (kron2 Q₀' proj0 + kron2 Q₁' proj1)) *
      embedAC CRzM *
      embedBC (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
      embedAC CRzN *
      embedBC (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1').conjTranspose *
      embedBC ((kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
               ((kron2 P₀' proj0 + kron2 P₁' proj1) * G₅)) *
      embedAC (kron2 (P_phase (φ_M * φ_N)) 1) := by
    rw [h_step7]
    have h_inj : embedBC ((kron2 P₀' proj0 + kron2 P₁' proj1) * G₅) =
        embedBC (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1').conjTranspose *
        embedBC ((kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
                 ((kron2 P₀' proj0 + kron2 P₁' proj1) * G₅)) := by
      rw [embedBC_mul]
      congr 1
      set X := (kron2 P₀' proj0 + kron2 P₁' proj1) * G₅ with hX_def
      calc X = 1 * X := (one_mul _).symm
        _ = ((kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1').conjTranspose *
             (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1')) * X := by rw [hRdR]
        _ = (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1').conjTranspose *
            ((kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') * X) := mul_assoc _ _ _
    rw [h_inj]
    noncomm_ring
  -- =========================================================================
  -- Step 5c-4b (iter 206): extract block00 and block11 of the middle
  -- 4-factor block `embedAC CRzM · embedBC R · embedAC CRzN · embedBC R†`
  -- via `chain_block_decomp_under_controlled` (PY24 helper).
  -- Per paper Eq.(4):
  --   block00 = R · R† (= 1, since R unitary).
  --   block11 = kron2 1 diag_M · R · kron2 1 diag_N · R†
  --           = kron2 proj0 R_0_paper + kron2 proj1 R_1_paper
  --     where R_b_paper = diag_M · R_y_θb' · diag_N · R_y_θb'.conjTranspose.
  -- =========================================================================
  have h_chain_blocks := chain_block_decomp_under_controlled
    CRzM (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') CRzN
    (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1').conjTranspose
    (1 : Mat2) (diagonal ![α_M0, α_M1])
    (1 : Mat2) (diagonal ![α_N0, α_N1])
    hCRzM hCRzN
  -- h_chain_blocks.1 : block00(middle) = kron2 1 1 · R · kron2 1 1 · R†
  -- h_chain_blocks.2 : block11(middle) = kron2 1 diag_M · R · kron2 1 diag_N · R†
  -- Simplify block00 to 1 (since R is unitary, R · R† = 1).
  have h_b00_one : block00 (embedAC CRzM *
      embedBC (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
      embedAC CRzN *
      embedBC (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1').conjTranspose) = 1 := by
    rw [h_chain_blocks.1, kron2_one_one_eq_one, one_mul, mul_one]
    exact Matrix.mul_eq_one_comm.mp hR_paper_unitary
  -- Distribute block11 into the AB-controlled form.
  -- Helper: kron2 1 D = kron2 proj0 D + kron2 proj1 D.
  have h_kron2_1_split : ∀ D : Mat2,
      kron2 (1 : Mat2) D = kron2 proj0 D + kron2 proj1 D := by
    intro D
    rw [← proj0_add_proj1, kron2_add_left]
  have h_b11_form : block11 (embedAC CRzM *
      embedBC (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
      embedAC CRzN *
      embedBC (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1').conjTranspose) =
      kron2 proj0 (diagonal ![α_M0, α_M1] * R_y_θ0' * diagonal ![α_N0, α_N1] *
        R_y_θ0'.conjTranspose) +
      kron2 proj1 (diagonal ![α_M0, α_M1] * R_y_θ1' * diagonal ![α_N0, α_N1] *
        R_y_θ1'.conjTranspose) := by
    rw [h_chain_blocks.2, h_kron2_1_split, h_kron2_1_split, block_diag_first_conjT,
        block_diag_first_mul, block_diag_first_mul, block_diag_first_mul]
  -- block01 / block10 of middle are 0 (every factor is block-diag-A).
  have h_b01_middle : block01 (embedAC CRzM *
      embedBC (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
      embedAC CRzN *
      embedBC (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1').conjTranspose) = 0 := by
    have hAC1 : block01 (embedAC CRzM) = 0 := by
      rw [hCRzM]; exact block01_embedAC_of_controlled _ _
    have hAC3 : block01 (embedAC CRzN) = 0 := by
      rw [hCRzN]; exact block01_embedAC_of_controlled _ _
    have hBC2 := block01_embedBC (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1')
    have hBC4 := block01_embedBC
      (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1').conjTranspose
    have h12 := block01_mul_of_both_zero _ _ hAC1 hBC2
    have h123 := block01_mul_of_both_zero _ _ h12 hAC3
    exact block01_mul_of_both_zero _ _ h123 hBC4
  have h_b10_middle : block10 (embedAC CRzM *
      embedBC (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
      embedAC CRzN *
      embedBC (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1').conjTranspose) = 0 := by
    have hAC1 : block10 (embedAC CRzM) = 0 := by
      rw [hCRzM]; exact block10_embedAC_of_controlled _ _
    have hAC3 : block10 (embedAC CRzN) = 0 := by
      rw [hCRzN]; exact block10_embedAC_of_controlled _ _
    have hBC2 := block10_embedBC (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1')
    have hBC4 := block10_embedBC
      (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1').conjTranspose
    have h12 := block10_mul_of_both_zero _ _ hAC1 hBC2
    have h123 := block10_mul_of_both_zero _ _ h12 hAC3
    exact block10_mul_of_both_zero _ _ h123 hBC4
  -- Combine the four block facts: M_middle = Mat8.ofBlockDiag 1 (AB-ctrl).
  have h_middle_eq : embedAC CRzM *
      embedBC (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
      embedAC CRzN *
      embedBC (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1').conjTranspose =
      Mat8.ofBlockDiag (1 : Mat4)
        (kron2 proj0 (diagonal ![α_M0, α_M1] * R_y_θ0' * diagonal ![α_N0, α_N1] *
          R_y_θ0'.conjTranspose) +
         kron2 proj1 (diagonal ![α_M0, α_M1] * R_y_θ1' * diagonal ![α_N0, α_N1] *
          R_y_θ1'.conjTranspose)) := by
    apply mat8_eq_of_blocks_off_diag_zero
    · rw [h_b00_one, block00_ofBlockDiag]
    · rw [h_b11_form, block11_ofBlockDiag]
    · exact h_b01_middle
    · exact h_b10_middle
    · exact block01_ofBlockDiag _ _
    · exact block10_ofBlockDiag _ _
  -- =========================================================================
  -- Step 5d (iter 207): spectral decomposition of R_0_paper, R_1_paper via
  -- py24_lemma_A_3 (= paper Lemma A.2). Each R_b is unitary (product of
  -- four unitaries: diag_M, R_y_θb', diag_N, R_y_θb'.conjTranspose).
  -- =========================================================================
  have h_diag_M_unit : IsUnitary2 (Matrix.diagonal ![α_M0, α_M1]) := by
    have h := isUnitary2_mul_diag_unit 1 isUnitary2_one α_M0 α_M1 _hα_M0 _hα_M1
    rwa [one_mul] at h
  have h_diag_N_unit : IsUnitary2 (Matrix.diagonal ![α_N0, α_N1]) := by
    have h := isUnitary2_mul_diag_unit 1 isUnitary2_one α_N0 α_N1 _hα_N0 _hα_N1
    rwa [one_mul] at h
  have h_R_0_unit : IsUnitary2 (Matrix.diagonal ![α_M0, α_M1] * R_y_θ0' *
      Matrix.diagonal ![α_N0, α_N1] * R_y_θ0'.conjTranspose) :=
    isUnitary2_mul
      (isUnitary2_mul (isUnitary2_mul h_diag_M_unit hR0') h_diag_N_unit)
      (isUnitary2_conjTranspose hR0')
  have h_R_1_unit : IsUnitary2 (Matrix.diagonal ![α_M0, α_M1] * R_y_θ1' *
      Matrix.diagonal ![α_N0, α_N1] * R_y_θ1'.conjTranspose) :=
    isUnitary2_mul
      (isUnitary2_mul (isUnitary2_mul h_diag_M_unit hR1') h_diag_N_unit)
      (isUnitary2_conjTranspose hR1')
  obtain ⟨γ_0, γ_0', F_0, hF_0, hSpec_0⟩ := py24_lemma_A_3 _ h_R_0_unit
  obtain ⟨γ_1, γ_1', F_1, hF_1, hSpec_1⟩ := py24_lemma_A_3 _ h_R_1_unit
  -- hSpec_b : F_b.conjTranspose * R_b * F_b = Matrix.diagonal ![γ_b, γ_b']
  -- Derive unit modulus of γ_0, γ_0', γ_1, γ_1' via diagonal_unitary_normSq.
  have h_diag_γ_0_unit : IsUnitary2 (Matrix.diagonal ![γ_0, γ_0']) := by
    rw [← hSpec_0]
    exact isUnitary2_mul
      (isUnitary2_mul (isUnitary2_conjTranspose hF_0) h_R_0_unit) hF_0
  have h_diag_γ_1_unit : IsUnitary2 (Matrix.diagonal ![γ_1, γ_1']) := by
    rw [← hSpec_1]
    exact isUnitary2_mul
      (isUnitary2_mul (isUnitary2_conjTranspose hF_1) h_R_1_unit) hF_1
  obtain ⟨hγ_0_unit, hγ_0'_unit⟩ := diagonal_unitary_normSq γ_0 γ_0' h_diag_γ_0_unit
  obtain ⟨hγ_1_unit, hγ_1'_unit⟩ := diagonal_unitary_normSq γ_1 γ_1' h_diag_γ_1_unit
  -- Build F = kron2 proj0 F_0 + kron2 proj1 F_1 (block-diag-first w.r.t. B,
  -- i.e. F is a B-controlled Mat4 that acts as F_0 on C if B=|0⟩, F_1 if B=|1⟩).
  have hF_unit : IsUnitary4 (kron2 proj0 F_0 + kron2 proj1 F_1) :=
    controlled_A_unitary hF_0 hF_1
  -- Paper Eq.(5) (BC piece): F† · R_BC · F = Matrix.diagonal ![γ_0, γ_0', γ_1, γ_1']
  -- where R_BC = kron2 proj0 R_0 + kron2 proj1 R_1 (the A=|1⟩ branch on BC).
  have h_R_BC_diag :
      (kron2 proj0 F_0 + kron2 proj1 F_1).conjTranspose *
      (kron2 proj0 (Matrix.diagonal ![α_M0, α_M1] * R_y_θ0' *
        Matrix.diagonal ![α_N0, α_N1] * R_y_θ0'.conjTranspose) +
       kron2 proj1 (Matrix.diagonal ![α_M0, α_M1] * R_y_θ1' *
        Matrix.diagonal ![α_N0, α_N1] * R_y_θ1'.conjTranspose)) *
      (kron2 proj0 F_0 + kron2 proj1 F_1) =
      Matrix.diagonal ![γ_0, γ_0', γ_1, γ_1'] := by
    rw [block_diag_first_conjT, block_diag_first_mul, block_diag_first_mul,
        hSpec_0, hSpec_1, kron2_proj0_diag_add_kron2_proj1_diag]
  -- =========================================================================
  -- Step 5e-1a (iter 209): collapse the middle 4-factor block into a single
  -- Mat8.ofBlockDiag form using h_step8 + h_middle_eq. Result: h_step9 is a
  -- 4-factor chain: outer-BC · middle-BlockDiag · outer-BC · outer-phase.
  -- =========================================================================
  have h_step9 : Dg.toMatrix =
      embedBC (G₁ * (kron2 Q₀' proj0 + kron2 Q₁' proj1)) *
      Mat8.ofBlockDiag (1 : Mat4)
        (kron2 proj0 (Matrix.diagonal ![α_M0, α_M1] * R_y_θ0' *
          Matrix.diagonal ![α_N0, α_N1] * R_y_θ0'.conjTranspose) +
         kron2 proj1 (Matrix.diagonal ![α_M0, α_M1] * R_y_θ1' *
          Matrix.diagonal ![α_N0, α_N1] * R_y_θ1'.conjTranspose)) *
      embedBC ((kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
               ((kron2 P₀' proj0 + kron2 P₁' proj1) * G₅)) *
      embedAC (kron2 (P_phase (φ_M * φ_N)) 1) := by
    calc Dg.toMatrix
        = embedBC (G₁ * (kron2 Q₀' proj0 + kron2 Q₁' proj1)) *
          (embedAC CRzM *
           embedBC (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
           embedAC CRzN *
           embedBC (kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1').conjTranspose) *
          embedBC ((kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
                   ((kron2 P₀' proj0 + kron2 P₁' proj1) * G₅)) *
          embedAC (kron2 (P_phase (φ_M * φ_N)) 1) := by
            rw [h_step8]; noncomm_ring
      _ = embedBC (G₁ * (kron2 Q₀' proj0 + kron2 Q₁' proj1)) *
          Mat8.ofBlockDiag (1 : Mat4)
            (kron2 proj0 (Matrix.diagonal ![α_M0, α_M1] * R_y_θ0' *
              Matrix.diagonal ![α_N0, α_N1] * R_y_θ0'.conjTranspose) +
             kron2 proj1 (Matrix.diagonal ![α_M0, α_M1] * R_y_θ1' *
              Matrix.diagonal ![α_N0, α_N1] * R_y_θ1'.conjTranspose)) *
          embedBC ((kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
                   ((kron2 P₀' proj0 + kron2 P₁' proj1) * G₅)) *
          embedAC (kron2 (P_phase (φ_M * φ_N)) 1) := by rw [h_middle_eq]
  -- =========================================================================
  -- Step 5e-1b (iter 209 cont.): derive R_BC = F · D · F† from h_R_BC_diag
  -- by left-multiplying by F and right-multiplying by F†. Uses F·F† = 1
  -- (right inverse of F, derived from IsUnitary4 via Matrix.mul_eq_one_comm).
  -- =========================================================================
  have hFF_right : (kron2 proj0 F_0 + kron2 proj1 F_1) *
      (kron2 proj0 F_0 + kron2 proj1 F_1).conjTranspose = 1 :=
    Matrix.mul_eq_one_comm.mp hF_unit
  have h_R_BC_eq_FDFt :
      kron2 proj0 (Matrix.diagonal ![α_M0, α_M1] * R_y_θ0' *
        Matrix.diagonal ![α_N0, α_N1] * R_y_θ0'.conjTranspose) +
      kron2 proj1 (Matrix.diagonal ![α_M0, α_M1] * R_y_θ1' *
        Matrix.diagonal ![α_N0, α_N1] * R_y_θ1'.conjTranspose) =
      (kron2 proj0 F_0 + kron2 proj1 F_1) *
      Matrix.diagonal ![γ_0, γ_0', γ_1, γ_1'] *
      (kron2 proj0 F_0 + kron2 proj1 F_1).conjTranspose := by
    have h_FX_F : ∀ X : Mat4,
        (kron2 proj0 F_0 + kron2 proj1 F_1) *
        ((kron2 proj0 F_0 + kron2 proj1 F_1).conjTranspose * X *
         (kron2 proj0 F_0 + kron2 proj1 F_1)) *
        (kron2 proj0 F_0 + kron2 proj1 F_1).conjTranspose = X := by
      intro X
      calc (kron2 proj0 F_0 + kron2 proj1 F_1) *
            ((kron2 proj0 F_0 + kron2 proj1 F_1).conjTranspose * X *
             (kron2 proj0 F_0 + kron2 proj1 F_1)) *
            (kron2 proj0 F_0 + kron2 proj1 F_1).conjTranspose
          = ((kron2 proj0 F_0 + kron2 proj1 F_1) *
             (kron2 proj0 F_0 + kron2 proj1 F_1).conjTranspose) * X *
            ((kron2 proj0 F_0 + kron2 proj1 F_1) *
             (kron2 proj0 F_0 + kron2 proj1 F_1).conjTranspose) := by noncomm_ring
        _ = 1 * X * 1 := by rw [hFF_right]
        _ = X := by rw [one_mul, mul_one]
    rw [← h_FX_F (kron2 proj0 _ + kron2 proj1 _), h_R_BC_diag]
  -- =========================================================================
  -- Step 5e-2 (iter 210): substitute R_BC = F·D·F† into Mat8.ofBlockDiag of
  -- h_step9 and split into three Mat8.ofBlockDiag factors via the helper
  -- `mat8_ofBlockDiag_one_mul`. Result: h_step10 has explicit F, D, F†
  -- factors as three separate `Mat8.ofBlockDiag 1 _` terms.
  -- =========================================================================
  have h_step10 : Dg.toMatrix =
      embedBC (G₁ * (kron2 Q₀' proj0 + kron2 Q₁' proj1)) *
      (Mat8.ofBlockDiag (1 : Mat4) (kron2 proj0 F_0 + kron2 proj1 F_1) *
       Mat8.ofBlockDiag (1 : Mat4) (Matrix.diagonal ![γ_0, γ_0', γ_1, γ_1']) *
       Mat8.ofBlockDiag (1 : Mat4)
         (kron2 proj0 F_0 + kron2 proj1 F_1).conjTranspose) *
      embedBC ((kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
               ((kron2 P₀' proj0 + kron2 P₁' proj1) * G₅)) *
      embedAC (kron2 (P_phase (φ_M * φ_N)) 1) := by
    rw [h_step9, h_R_BC_eq_FDFt, ← mat8_ofBlockDiag_one_mul,
        ← mat8_ofBlockDiag_one_mul]
  -- =========================================================================
  -- Step 5e-3 (iter 211): use embedBC_conj_ofBlockDiag_one to convert the
  -- F · D · F† Mat8.ofBlockDiag conjugation into embedBC F · ofBlockDiag 1 D
  -- · embedBC F†, then absorb F into G_1 and F† into G_5 via embedBC_mul.
  -- Result: h_step11 has paper's V_1 = G_1·F and V_4 = F†·G_5 form.
  -- =========================================================================
  have h_step11 : Dg.toMatrix =
      embedBC (G₁ * (kron2 Q₀' proj0 + kron2 Q₁' proj1) *
               (kron2 proj0 F_0 + kron2 proj1 F_1)) *
      Mat8.ofBlockDiag (1 : Mat4) (Matrix.diagonal ![γ_0, γ_0', γ_1, γ_1']) *
      embedBC ((kron2 proj0 F_0 + kron2 proj1 F_1).conjTranspose *
               ((kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
                ((kron2 P₀' proj0 + kron2 P₁' proj1) * G₅))) *
      embedAC (kron2 (P_phase (φ_M * φ_N)) 1) := by
    calc Dg.toMatrix
        = embedBC (G₁ * (kron2 Q₀' proj0 + kron2 Q₁' proj1)) *
          (Mat8.ofBlockDiag (1 : Mat4) (kron2 proj0 F_0 + kron2 proj1 F_1) *
           Mat8.ofBlockDiag (1 : Mat4) (Matrix.diagonal ![γ_0, γ_0', γ_1, γ_1']) *
           Mat8.ofBlockDiag (1 : Mat4)
             (kron2 proj0 F_0 + kron2 proj1 F_1).conjTranspose) *
          embedBC ((kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
                   ((kron2 P₀' proj0 + kron2 P₁' proj1) * G₅)) *
          embedAC (kron2 (P_phase (φ_M * φ_N)) 1) := h_step10
      _ = embedBC (G₁ * (kron2 Q₀' proj0 + kron2 Q₁' proj1)) *
          (embedBC (kron2 proj0 F_0 + kron2 proj1 F_1) *
           Mat8.ofBlockDiag (1 : Mat4) (Matrix.diagonal ![γ_0, γ_0', γ_1, γ_1']) *
           embedBC (kron2 proj0 F_0 + kron2 proj1 F_1).conjTranspose) *
          embedBC ((kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
                   ((kron2 P₀' proj0 + kron2 P₁' proj1) * G₅)) *
          embedAC (kron2 (P_phase (φ_M * φ_N)) 1) := by
            rw [mat8_ofBlockDiag_one_mul, mat8_ofBlockDiag_one_mul,
                ← embedBC_conj_ofBlockDiag_one _ _ hFF_right]
      _ = (embedBC (G₁ * (kron2 Q₀' proj0 + kron2 Q₁' proj1)) *
           embedBC (kron2 proj0 F_0 + kron2 proj1 F_1)) *
          Mat8.ofBlockDiag (1 : Mat4) (Matrix.diagonal ![γ_0, γ_0', γ_1, γ_1']) *
          (embedBC (kron2 proj0 F_0 + kron2 proj1 F_1).conjTranspose *
           embedBC ((kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
                    ((kron2 P₀' proj0 + kron2 P₁' proj1) * G₅))) *
          embedAC (kron2 (P_phase (φ_M * φ_N)) 1) := by noncomm_ring
      _ = embedBC (G₁ * (kron2 Q₀' proj0 + kron2 Q₁' proj1) *
                   (kron2 proj0 F_0 + kron2 proj1 F_1)) *
          Mat8.ofBlockDiag (1 : Mat4) (Matrix.diagonal ![γ_0, γ_0', γ_1, γ_1']) *
          embedBC ((kron2 proj0 F_0 + kron2 proj1 F_1).conjTranspose *
                   ((kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
                    ((kron2 P₀' proj0 + kron2 P₁' proj1) * G₅))) *
          embedAC (kron2 (P_phase (φ_M * φ_N)) 1) := by
            rw [embedBC_mul, embedBC_mul]
  -- =========================================================================
  -- Step 5d-prep (iter 213): derive det(R_b) = 1 and γ_b · γ_b' = 1 for
  -- b ∈ {0, 1}. From hα_M_det + hα_N_det + |det R_y_θb'|² = 1 (unitarity).
  -- =========================================================================
  have h_det_diag_M : (Matrix.diagonal ![α_M0, α_M1] : Mat2).det = 1 := by
    rw [det_diagonal_Fin2, _hα_M_det]
  have h_det_diag_N : (Matrix.diagonal ![α_N0, α_N1] : Mat2).det = 1 := by
    rw [det_diagonal_Fin2, _hα_N_det]
  have h_RyA_det_unit : star R_y_θ0'.det * R_y_θ0'.det = 1 := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, hR0', Matrix.det_one]
  have h_RyB_det_unit : star R_y_θ1'.det * R_y_θ1'.det = 1 := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, hR1', Matrix.det_one]
  have h_det_R_0 : (Matrix.diagonal ![α_M0, α_M1] * R_y_θ0' *
      Matrix.diagonal ![α_N0, α_N1] * R_y_θ0'.conjTranspose).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul,
        h_det_diag_M, h_det_diag_N, Matrix.det_conjTranspose, one_mul, mul_one,
        mul_comm]
    exact h_RyA_det_unit
  have h_det_R_1 : (Matrix.diagonal ![α_M0, α_M1] * R_y_θ1' *
      Matrix.diagonal ![α_N0, α_N1] * R_y_θ1'.conjTranspose).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul,
        h_det_diag_M, h_det_diag_N, Matrix.det_conjTranspose, one_mul, mul_one,
        mul_comm]
    exact h_RyB_det_unit
  -- γ_b · γ_b' = 1 via det(F_b†·R_b·F_b) = det(R_b) = 1 = γ_b · γ_b'.
  have h_F0_det_unit : star F_0.det * F_0.det = 1 := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, hF_0, Matrix.det_one]
  have h_F1_det_unit : star F_1.det * F_1.det = 1 := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, hF_1, Matrix.det_one]
  have h_γ_0_det : γ_0 * γ_0' = 1 := by
    have h := congr_arg Matrix.det hSpec_0
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, h_det_R_0,
        mul_one, det_diagonal_Fin2] at h
    rw [← h]
    exact h_F0_det_unit
  have h_γ_1_det : γ_1 * γ_1' = 1 := by
    have h := congr_arg Matrix.det hSpec_1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, h_det_R_1,
        mul_one, det_diagonal_Fin2] at h
    rw [← h]
    exact h_F1_det_unit
  -- =========================================================================
  -- Step 5d-perm (iter 214): apply P_sigma_4 conjugation to permute D into
  -- rank-1 separable form D' = diag![γ_0, γ_1, γ_1', γ_0'].
  -- The conjugation is absorbed into V_1 (via embedBC P_sigma_4) and V_4
  -- (via embedBC P_sigma_4†) on the outer BC factors.
  -- =========================================================================
  have hPP_right : P_sigma_4 * P_sigma_4.conjTranspose = 1 :=
    Matrix.mul_eq_one_comm.mp P_sigma_4_unitary
  have h_D_conj : P_sigma_4 *
      Matrix.diagonal ![γ_0, γ_1, γ_1', γ_0'] * P_sigma_4.conjTranspose =
      Matrix.diagonal ![γ_0, γ_0', γ_1, γ_1'] := by
    have h := P_sigma_4_conj_diag γ_0 γ_0' γ_1 γ_1'
    -- h: P_σ† · diag![γ_0, γ_0', γ_1, γ_1'] · P_σ = diag![γ_0, γ_1, γ_1', γ_0']
    -- Want: P_σ · diag![γ_0, γ_1, γ_1', γ_0'] · P_σ† = diag![γ_0, γ_0', γ_1, γ_1']
    -- Derive: from h, multiply by P_σ on left and P_σ† on right.
    have := congr_arg (fun X => P_sigma_4 * X * P_sigma_4.conjTranspose) h
    simp only at this
    calc P_sigma_4 * Matrix.diagonal ![γ_0, γ_1, γ_1', γ_0'] *
         P_sigma_4.conjTranspose
        = P_sigma_4 * (P_sigma_4.conjTranspose *
           Matrix.diagonal ![γ_0, γ_0', γ_1, γ_1'] * P_sigma_4) *
          P_sigma_4.conjTranspose := by rw [← P_sigma_4_conj_diag]
      _ = (P_sigma_4 * P_sigma_4.conjTranspose) *
          Matrix.diagonal ![γ_0, γ_0', γ_1, γ_1'] *
          (P_sigma_4 * P_sigma_4.conjTranspose) := by noncomm_ring
      _ = 1 * Matrix.diagonal ![γ_0, γ_0', γ_1, γ_1'] * 1 := by rw [hPP_right]
      _ = Matrix.diagonal ![γ_0, γ_0', γ_1, γ_1'] := by rw [one_mul, mul_one]
  -- Rewrite Mat8.ofBlockDiag 1 D as embedBC P_σ · Mat8.ofBlockDiag 1 D' · embedBC P_σ†.
  have h_step12 : Dg.toMatrix =
      embedBC (G₁ * (kron2 Q₀' proj0 + kron2 Q₁' proj1) *
               (kron2 proj0 F_0 + kron2 proj1 F_1) * P_sigma_4) *
      Mat8.ofBlockDiag (1 : Mat4) (Matrix.diagonal ![γ_0, γ_1, γ_1', γ_0']) *
      embedBC (P_sigma_4.conjTranspose *
               ((kron2 proj0 F_0 + kron2 proj1 F_1).conjTranspose *
                ((kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
                 ((kron2 P₀' proj0 + kron2 P₁' proj1) * G₅)))) *
      embedAC (kron2 (P_phase (φ_M * φ_N)) 1) := by
    calc Dg.toMatrix
        = embedBC (G₁ * (kron2 Q₀' proj0 + kron2 Q₁' proj1) *
                   (kron2 proj0 F_0 + kron2 proj1 F_1)) *
          Mat8.ofBlockDiag (1 : Mat4) (Matrix.diagonal ![γ_0, γ_0', γ_1, γ_1']) *
          embedBC ((kron2 proj0 F_0 + kron2 proj1 F_1).conjTranspose *
                   ((kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
                    ((kron2 P₀' proj0 + kron2 P₁' proj1) * G₅))) *
          embedAC (kron2 (P_phase (φ_M * φ_N)) 1) := h_step11
      _ = embedBC (G₁ * (kron2 Q₀' proj0 + kron2 Q₁' proj1) *
                   (kron2 proj0 F_0 + kron2 proj1 F_1)) *
          (embedBC P_sigma_4 *
           Mat8.ofBlockDiag (1 : Mat4) (Matrix.diagonal ![γ_0, γ_1, γ_1', γ_0']) *
           embedBC P_sigma_4.conjTranspose) *
          embedBC ((kron2 proj0 F_0 + kron2 proj1 F_1).conjTranspose *
                   ((kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
                    ((kron2 P₀' proj0 + kron2 P₁' proj1) * G₅))) *
          embedAC (kron2 (P_phase (φ_M * φ_N)) 1) := by
            rw [embedBC_conj_ofBlockDiag_one _ _ hPP_right, h_D_conj]
      _ = (embedBC (G₁ * (kron2 Q₀' proj0 + kron2 Q₁' proj1) *
                   (kron2 proj0 F_0 + kron2 proj1 F_1)) * embedBC P_sigma_4) *
          Mat8.ofBlockDiag (1 : Mat4) (Matrix.diagonal ![γ_0, γ_1, γ_1', γ_0']) *
          (embedBC P_sigma_4.conjTranspose *
           embedBC ((kron2 proj0 F_0 + kron2 proj1 F_1).conjTranspose *
                    ((kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
                     ((kron2 P₀' proj0 + kron2 P₁' proj1) * G₅)))) *
          embedAC (kron2 (P_phase (φ_M * φ_N)) 1) := by noncomm_ring
      _ = embedBC (G₁ * (kron2 Q₀' proj0 + kron2 Q₁' proj1) *
                   (kron2 proj0 F_0 + kron2 proj1 F_1) * P_sigma_4) *
          Mat8.ofBlockDiag (1 : Mat4) (Matrix.diagonal ![γ_0, γ_1, γ_1', γ_0']) *
          embedBC (P_sigma_4.conjTranspose *
                   ((kron2 proj0 F_0 + kron2 proj1 F_1).conjTranspose *
                    ((kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
                     ((kron2 P₀' proj0 + kron2 P₁' proj1) * G₅)))) *
          embedAC (kron2 (P_phase (φ_M * φ_N)) 1) := by
            rw [embedBC_mul, embedBC_mul]
  -- =========================================================================
  -- Step 5e-5 (iter 215): define V_2_paper (AC) and V_3_paper (AB) from γ_0,
  -- γ_1, φ_M*φ_N parameters such that:
  --   embedAC V_2 · embedAB V_3 = Mat8.ofBlockDiag 1 D' · embedAC P_phase.
  -- For our D' = diag![γ_0, γ_1, γ_1', γ_0'] (rank-1 separable since
  -- γ_b·γ_b'=1), the factorization u_c · v_b gives:
  --   u = (γ_0, γ_1)  →  V_2 = kron2 proj0 1 + kron2 proj1 diag![γ_0, γ_1]
  --   v = (φ, φ·γ_1'·γ_0')  →  V_3 = kron2 proj0 1 + kron2 proj1 diag![φ, φ·γ_1'·γ_0']
  -- where φ := φ_M · φ_N. (Verify u_0·v_1 = γ_0·φ·γ_1'·γ_0' = γ_1'·φ ✓
  -- using γ_0·γ_0'=1; and u_1·v_1 = γ_1·φ·γ_1'·γ_0' = γ_0'·φ ✓ using
  -- γ_1·γ_1'=1.)
  -- =========================================================================
  have hφM_φN_unit : Complex.normSq (φ_M * φ_N) = 1 := by
    rw [Complex.normSq_mul, _hφ_M, _hφ_N, mul_one]
  have hφγγ_unit : Complex.normSq (φ_M * φ_N * γ_1' * γ_0') = 1 := by
    rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_mul,
        _hφ_M, _hφ_N, hγ_1'_unit, hγ_0'_unit]
    ring
  have h_V_2_paper_unit : IsUnitary4
      (kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![γ_0, γ_1])) := by
    apply controlled_A_unitary isUnitary2_one
    have h := isUnitary2_mul_diag_unit 1 isUnitary2_one γ_0 γ_1 hγ_0_unit hγ_1_unit
    rwa [one_mul] at h
  have h_V_3_paper_unit : IsUnitary4 (kron2 proj0 1 +
      kron2 proj1 (Matrix.diagonal ![φ_M * φ_N, φ_M * φ_N * γ_1' * γ_0'])) := by
    apply controlled_A_unitary isUnitary2_one
    have h := isUnitary2_mul_diag_unit 1 isUnitary2_one (φ_M * φ_N)
      (φ_M * φ_N * γ_1' * γ_0') hφM_φN_unit hφγγ_unit
    rwa [one_mul] at h
  -- =========================================================================
  -- Step 5e-5 (iter 217): prove the split identity via Mat8-diagonal helpers.
  -- Reduce both sides to Matrix.diagonal![...] form on Fin 8, then compare.
  -- =========================================================================
  have h_split :
      Mat8.ofBlockDiag (1 : Mat4) (Matrix.diagonal ![γ_0, γ_1, γ_1', γ_0']) *
      embedAC (kron2 (P_phase (φ_M * φ_N)) 1) =
      embedAC (kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![γ_0, γ_1])) *
      embedAB (kron2 proj0 1 +
        kron2 proj1 (Matrix.diagonal ![φ_M * φ_N, φ_M * φ_N * γ_1' * γ_0'])) := by
    rw [Mat8_ofBlockDiag_one_diag_Fin4, embedAC_kron2_P_phase_one,
        ← diag_one_one_u_v_decomp γ_0 γ_1,
        ← diag_one_one_u_v_decomp (φ_M * φ_N) (φ_M * φ_N * γ_1' * γ_0'),
        embedAC_diag_Fin4, embedAB_diag_Fin4,
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    fin_cases k <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;>
      first
        | rfl
        | linear_combination -(γ_1' * φ_M * φ_N) * h_γ_0_det
        | linear_combination -(γ_0' * φ_M * φ_N) * h_γ_1_det
  -- =========================================================================
  -- Step 5e-6 (iter 218): derive final chain by combining h_step12 + h_split.
  -- embedAC P_phase commutes with embedBC V_4_pre (via hC2), so we can pull it
  -- in front of embedBC V_4_pre, then apply h_split.
  -- =========================================================================
  have h_commute_V4_phase :
      embedBC (P_sigma_4.conjTranspose *
               ((kron2 proj0 F_0 + kron2 proj1 F_1).conjTranspose *
                ((kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
                 ((kron2 P₀' proj0 + kron2 P₁' proj1) * G₅)))) *
      embedAC (kron2 (P_phase (φ_M * φ_N)) 1) =
      embedAC (kron2 (P_phase (φ_M * φ_N)) 1) *
      embedBC (P_sigma_4.conjTranspose *
               ((kron2 proj0 F_0 + kron2 proj1 F_1).conjTranspose *
                ((kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
                 ((kron2 P₀' proj0 + kron2 P₁' proj1) * G₅)))) :=
    (hC2 (P_phase (φ_M * φ_N)) _).symm
  have h_step13 : Dg.toMatrix =
      embedBC (G₁ * (kron2 Q₀' proj0 + kron2 Q₁' proj1) *
               (kron2 proj0 F_0 + kron2 proj1 F_1) * P_sigma_4) *
      embedAC (kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![γ_0, γ_1])) *
      embedAB (kron2 proj0 1 +
        kron2 proj1 (Matrix.diagonal ![φ_M * φ_N, φ_M * φ_N * γ_1' * γ_0'])) *
      embedBC (P_sigma_4.conjTranspose *
               ((kron2 proj0 F_0 + kron2 proj1 F_1).conjTranspose *
                ((kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
                 ((kron2 P₀' proj0 + kron2 P₁' proj1) * G₅)))) := by
    rw [h_step12]
    rw [show ∀ A B C D : Mat8, A * B * C * D = A * (B * (C * D)) from by
          intros; noncomm_ring]
    rw [h_commute_V4_phase]
    rw [show ∀ A B C D : Mat8, A * (B * (C * D)) = A * (B * C) * D from by
          intros; noncomm_ring]
    rw [h_split]
    noncomm_ring
  -- =========================================================================
  -- Step 5e-7 (iter 218 cont.): extract existentials, prove unitarities,
  -- and CLOSE paper_lemma_4_1.
  -- =========================================================================
  have hG₁_unit : IsUnitary4 G₁ := by
    rw [hG₁]; exact isUnitary4_mul _hF₁ (isUnitary4_kron2 isUnitary2_one hV_M)
  have hG₅_unit : IsUnitary4 G₅ := by
    rw [hG₅]
    exact isUnitary4_mul
      (isUnitary4_kron2 isUnitary2_one (isUnitary2_conjTranspose hV_N)) _hF₅
  have hQ_paper_unit : IsUnitary4 (kron2 Q₀' proj0 + kron2 Q₁' proj1) := by
    unfold IsUnitary4
    rw [block_diag_second_conjT, block_diag_second_mul]
    unfold IsUnitary2 at hQ₀' hQ₁'
    rw [hQ₀', hQ₁']
    exact kron2_one_proj0_add_kron2_one_proj1
  have hP_paper_unit : IsUnitary4 (kron2 P₀' proj0 + kron2 P₁' proj1) := by
    unfold IsUnitary4
    rw [block_diag_second_conjT, block_diag_second_mul]
    unfold IsUnitary2 at hP₀' hP₁'
    rw [hP₀', hP₁']
    exact kron2_one_proj0_add_kron2_one_proj1
  refine ⟨G₁ * (kron2 Q₀' proj0 + kron2 Q₁' proj1) *
           (kron2 proj0 F_0 + kron2 proj1 F_1) * P_sigma_4,
          kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![γ_0, γ_1]),
          kron2 proj0 1 + kron2 proj1
            (Matrix.diagonal ![φ_M * φ_N, φ_M * φ_N * γ_1' * γ_0']),
          P_sigma_4.conjTranspose *
           ((kron2 proj0 F_0 + kron2 proj1 F_1).conjTranspose *
            ((kron2 proj0 R_y_θ0' + kron2 proj1 R_y_θ1') *
             ((kron2 P₀' proj0 + kron2 P₁' proj1) * G₅))),
          ?_, h_V_2_paper_unit, h_V_3_paper_unit, ?_, h_step13⟩
  · -- V_1 unitary: G_1 · Q · F · P_σ
    exact isUnitary4_mul
      (isUnitary4_mul (isUnitary4_mul hG₁_unit hQ_paper_unit) hF_unit)
      P_sigma_4_unitary
  · -- V_4 unitary: P_σ† · F† · R · P · G_5 (right-assoc)
    exact isUnitary4_mul (isUnitary4_conjTranspose P_sigma_4_unitary)
      (isUnitary4_mul (isUnitary4_conjTranspose hF_unit)
        (isUnitary4_mul hR_paper_unitary
          (isUnitary4_mul hP_paper_unit hG₅_unit)))

/-! ## Iter 186: pin-down stubs for `paper_lemma_4_2`'s d₀≠d₁ branch

To reduce internal sorries in `paper_lemma_4_2` (which previously held 2 inner
sorries: line 880 `h_joint_spec_witness` and line 896 Case (1) closure), we
introduce two essential top-level stubs that map to specific paper claims:

- `paper_lemma_4_2_joint_spec` (paper page 10, Eq.(6)) — derives the
  joint-spectrum witness for the trichotomy.
- `paper_lemma_4_2_case_1_witness` (paper page 11, Eq.7-9 + Lemma A.2 +
  `paper_lemma_4_1` invocation) — bundles the entire Case (1) reduction.

Both are SCAFFOLDING STUBS. Their existence pins the essential paper work to
crisp, named claims; once closed, `paper_lemma_4_2` becomes sorry-free
unconditionally.

Cost: +2 essential sorry-decls. Benefit: `paper_lemma_4_2`'s internal proof
becomes a clean invocation chain. -/

/-! ## Iter 1031 (2026-08-14): the ORIGINAL `paper_lemma_4_2_joint_spec`
    statement was FALSE — refutation + required normalization

The iter-186 scaffolding stub asserted that the joint matrix
`M_joint = kron2 proj0 X_eig + kron2 proj1 Y_eig` is unitarily similar to
`diagonal ![d₀, d₀, d₁, d₁]`, where `d₀, d₁` are the eigenvalues of the middle
gate produced by `blockDiagB_spectral`. **That is false.** The correct joint
spectrum is `(1, 1, d₁·conj d₀, d₁·conj d₀)` — it depends only on the RATIO
`d₁/d₀`, not on `d₀` and `d₁` separately.

Reason (paper page 10, Eq.(6)): `Dmid = Diag(1, d₀, 1, d₁)` restricted to
`B = j` acts on qubit C as `Diag(1, d_j)`, so with `L = AC(U₂)·BC(Dmid)·AC(U₄)`,

  `Σ_i |i⟩⟨i|_A ⊗ L_{i0} = U₂·U₄`  and  `Σ_i |i⟩⟨i|_A ⊗ L_{i1} = U₂·(1⊗Diag(1,d₁·conj d₀))·U₂†·U₂U₄`,

hence `M_joint = U₂ · (1 ⊗ Diag(1, d₁·conj d₀)) · U₂†`. The paper avoids this
mismatch because its Lemma A.5 emits DETERMINANT-ONE `R(α₀), R(α₁)` factors and
then works with `R(β) = R(α₁ - α₀)`; our `blockDiagB_spectral` emits raw
eigenvalues with no normalization, so the leftover phase `d₀` must be stripped
first (see `blockDiagB_diag_normalize`).

`joint_spec_general_form_false` below is the machine-checked refutation: it takes
the ORIGINAL statement as a hypothesis and derives `False` from the instance
`U₂ = U₄ = W₁ = W₅ = 1`, `d₀ = i`, `d₁ = 1`, for which `X_eig = Y_eig = Diag(1, -i)`
so `tr M_joint = 2 - 2i` while `tr Diag(d₀,d₀,d₁,d₁) = 2 + 2i`.

Consequence: `paper_lemma_4_2_joint_spec` now carries the extra hypothesis
`hd₀_one : d₀ = 1` (the WLOG normalization), which its caller
`paper_lemma_4_2` discharges at the top of its `d₀ ≠ d₁` branch by absorbing
the C-only phase `Diag(1, d₀)` into `U₂` (via `blockDiagB_diag_normalize` and
`embedBC_kron2_one_eq_embedAC_kron2_one`) and rebinding `U₂, Dmid, d₀, d₁` to
the normalized data. -/

/-- Counterexample gate for `joint_spec_general_form_false`:
    `Diag(1, i, 1, 1, 1, i, 1, 1) = embedBC (Diag(1, i, 1, 1))`. -/
private def jointSpecCexGate : DiagGate3 where
  d := ![1, Complex.I, 1, 1, 1, Complex.I, 1, 1]
  unit := by intro i; fin_cases i <;> simp

-- 8×8 `fin_cases i <;> fin_cases j` block computations on `embedBC`.
set_option maxHeartbeats 1600000 in
/-- **The un-normalized joint-spectrum claim is FALSE** (iter 1031).

    Taking the original (iter-186) statement of `paper_lemma_4_2_joint_spec` as a
    hypothesis `H` yields `False`. Witness: `W₁ = W₅ = U₂ = U₄ = 1`,
    `d₀ = i`, `d₁ = 1`, `Dg = Diag(1, i, 1, 1, 1, i, 1, 1)`. Then
    `X_eig = Y_eig = Diag(1, -i)`, so `M_joint = Diag(1, -i, 1, -i)` has trace
    `2 - 2i`, whereas `Diag(d₀, d₀, d₁, d₁) = Diag(i, i, 1, 1)` has trace `2 + 2i`.
    Unitary similarity preserves trace, contradiction.

    This is a permanent regression guard: it pins down exactly why the
    `_hd₀_one` normalization hypothesis is required. -/
private theorem joint_spec_general_form_false
    (H : ∀ (Dg : DiagGate3) (W₁ W₅ U₂ U₄ Dmid : Mat4),
        IsUnitary4 W₁ → IsUnitary4 W₅ →
        ∀ (X_eig Y_eig : Mat2), IsUnitary2 X_eig → IsUnitary2 Y_eig →
        ∀ d₀ d₁ : ℂ, Complex.normSq d₀ = 1 → Complex.normSq d₁ = 1 →
        Dg.toMatrix =
          embedBC W₁ * (embedAC U₂ * embedBC Dmid * embedAC U₄) * embedBC W₅ →
        Dmid = kron2 1 proj0 + kron2 (Matrix.diagonal ![d₀, d₁]) proj1 →
        X_eig = blockA_11 (block00 (embedAC U₂ * embedBC Dmid * embedAC U₄)) *
          (blockA_00 (block00 (embedAC U₂ * embedBC Dmid * embedAC U₄))).conjTranspose →
        Y_eig = blockA_11 (block11 (embedAC U₂ * embedBC Dmid * embedAC U₄)) *
          (blockA_00 (block11 (embedAC U₂ * embedBC Dmid * embedAC U₄))).conjTranspose →
        ∃ W : Mat4, IsUnitary4 W ∧
          W.conjTranspose * (kron2 proj0 X_eig + kron2 proj1 Y_eig) * W =
            Matrix.diagonal ![d₀, d₀, d₁, d₁]) :
    False := by
  have h1 : IsUnitary4 (1 : Mat4) := by
    show (1 : Mat4).conjTranspose * 1 = 1
    simp
  have hXu : IsUnitary2 (Matrix.diagonal ![1, -Complex.I]) := by
    show (Matrix.diagonal ![(1 : ℂ), -Complex.I]).conjTranspose *
      Matrix.diagonal ![1, -Complex.I] = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hchain : jointSpecCexGate.toMatrix =
      embedBC (1 : Mat4) * (embedAC (1 : Mat4) *
        embedBC (kron2 1 proj0 + kron2 (Matrix.diagonal ![Complex.I, 1]) proj1) *
        embedAC (1 : Mat4)) * embedBC (1 : Mat4) := by
    rw [embedBC_one, embedAC_one, one_mul, mul_one, one_mul, mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [jointSpecCexGate, DiagGate3.toMatrix, embedBC, kron2, proj0, proj1,
            Matrix.diagonal, Matrix.of_apply]
  have hXdef : (Matrix.diagonal ![1, -Complex.I] : Mat2) =
      blockA_11 (block00 (embedAC (1 : Mat4) * embedBC (kron2 1 proj0 +
        kron2 (Matrix.diagonal ![Complex.I, 1]) proj1) * embedAC (1 : Mat4))) *
      (blockA_00 (block00 (embedAC (1 : Mat4) * embedBC (kron2 1 proj0 +
        kron2 (Matrix.diagonal ![Complex.I, 1]) proj1) *
        embedAC (1 : Mat4)))).conjTranspose := by
    rw [embedAC_one, one_mul, mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blockA_11, blockA_00, block00, embedBC, kron2, proj0, proj1,
            Matrix.diagonal, Matrix.mul_apply, Matrix.of_apply,
            Matrix.conjTranspose_apply, Fin.sum_univ_two]
  have hYdef : (Matrix.diagonal ![1, -Complex.I] : Mat2) =
      blockA_11 (block11 (embedAC (1 : Mat4) * embedBC (kron2 1 proj0 +
        kron2 (Matrix.diagonal ![Complex.I, 1]) proj1) * embedAC (1 : Mat4))) *
      (blockA_00 (block11 (embedAC (1 : Mat4) * embedBC (kron2 1 proj0 +
        kron2 (Matrix.diagonal ![Complex.I, 1]) proj1) *
        embedAC (1 : Mat4)))).conjTranspose := by
    rw [embedAC_one, one_mul, mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blockA_11, blockA_00, block11, embedBC, kron2, proj0, proj1,
            Matrix.diagonal, Matrix.mul_apply, Matrix.of_apply,
            Matrix.conjTranspose_apply, Fin.sum_univ_two]
  obtain ⟨W, hW, hWeq⟩ := H jointSpecCexGate 1 1 1 1
      (kron2 1 proj0 + kron2 (Matrix.diagonal ![Complex.I, 1]) proj1) h1 h1
      (Matrix.diagonal ![1, -Complex.I]) (Matrix.diagonal ![1, -Complex.I]) hXu hXu
      Complex.I 1 (by simp) (by simp) hchain rfl hXdef hYdef
  have htr := congrArg Matrix.trace hWeq
  rw [Matrix.trace_mul_cycle, show W * W.conjTranspose = 1 from mul_eq_one_comm.mp hW,
      one_mul] at htr
  simp [Matrix.trace, Matrix.diagonal, kron2, proj0, proj1, Fin.sum_univ_four,
        Matrix.of_apply] at htr
  have hI : Complex.I = 0 := by linear_combination (-1/4 : ℂ) * htr
  exact Complex.I_ne_zero hI

/-! ## Iter 1034 (2026-08-14): Π-decomposition infrastructure for paper Eq.(6)

The middle gate of Lemma 4.2, after the `d₀ = 1` normalization
(`blockDiagB_diag_normalize`), reads `Dmid = C_B(1, Diag(1, d₁))` — a gate
CONTROLLED ON QUBIT B. Writing `Π_j := embedBC (kron2 proj_j 1)` for the two
B-projectors, the whole 3-factor chain therefore splits as

  `L = embedAC U₂ · embedBC Dmid · embedAC U₄ = Π₀ · embedAC G₀ + Π₁ · embedAC G₁`

with `G₀ = U₂·U₄` and `G₁ = U₂·(1 ⊗ Diag(1, d₁))·U₄` — because `Π_j` acts only
on B and hence commutes with both `embedAC` factors
(`embedAC_commutes_B_only`), while the C-only branch gate moves between the
`embedBC` and `embedAC` views via `embedBC_kron2_one_eq_embedAC_kron2_one`.

This is the Lean form of the paper's two page-11 observations ("if qubit B is
|0⟩ … ; if qubit B is |1⟩ …") and it is what makes the joint spectrum
computable: every A-block of `L` is read off from a single A-block of `G₀`
or `G₁`.

These five lemmas are generic (no Lemma-4.2 hypotheses); they live here rather
than in `EmbedLemmas.lean` only to keep `SetChar.lean` from rebuilding. -/

/-- **Π-split of the Lemma 4.2 middle chain.** With the middle gate written in
    B-controlled form `kron2 proj0 1 + kron2 proj1 (Diag(1, d₁))`, the chain
    `AC(U₂)·BC(Dmid)·AC(U₄)` splits into the two B-branches. -/
theorem L_pi_split (U₂ U₄ : Mat4) (d₁ : ℂ) :
    embedAC U₂ *
      embedBC (kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![1, d₁])) * embedAC U₄ =
    embedBC (kron2 proj0 1) * embedAC (U₂ * U₄) +
    embedBC (kron2 proj1 1) *
      embedAC (U₂ * kron2 1 (Matrix.diagonal ![1, d₁]) * U₄) := by
  have hc0 := embedAC_commutes_B_only U₂ proj0
  have hc1 := embedAC_commutes_B_only U₂ proj1
  have hE := embedBC_kron2_one_eq_embedAC_kron2_one (Matrix.diagonal ![1, d₁])
  have hsub : (kron2 proj1 (Matrix.diagonal ![1, d₁]) : Mat4) =
      kron2 proj1 1 * kron2 1 (Matrix.diagonal ![1, d₁]) := by
    rw [kron2_mul, mul_one, one_mul]
  have t0 : embedAC U₂ * embedBC (kron2 proj0 1) * embedAC U₄ =
      embedBC (kron2 proj0 1) * embedAC (U₂ * U₄) := by
    rw [hc0, mul_assoc, embedAC_mul]
  have t1 : embedAC U₂ *
      (embedBC (kron2 proj1 1) * embedAC (kron2 1 (Matrix.diagonal ![1, d₁]))) *
      embedAC U₄ =
      embedBC (kron2 proj1 1) *
        embedAC (U₂ * kron2 1 (Matrix.diagonal ![1, d₁]) * U₄) := by
    rw [← mul_assoc, hc1, mul_assoc, embedAC_mul, mul_assoc, embedAC_mul, ← mul_assoc]
  rw [hsub, embedBC_add, ← embedBC_mul, hE]
  calc embedAC U₂ *
        (embedBC (kron2 proj0 1) +
          embedBC (kron2 proj1 1) * embedAC (kron2 1 (Matrix.diagonal ![1, d₁]))) *
        embedAC U₄
      = embedAC U₂ * embedBC (kron2 proj0 1) * embedAC U₄ +
        embedAC U₂ *
          (embedBC (kron2 proj1 1) *
            embedAC (kron2 1 (Matrix.diagonal ![1, d₁]))) * embedAC U₄ := by
        noncomm_ring
    _ = embedBC (kron2 proj0 1) * embedAC (U₂ * U₄) +
        embedBC (kron2 proj1 1) *
          embedAC (U₂ * kron2 1 (Matrix.diagonal ![1, d₁]) * U₄) := by rw [t0, t1]

/-- A-block (00) of a Π-split chain: controlled-A form built from the
    `blockA_00`s of the two branch gates. -/
theorem block00_pi_split (G₀ G₁ : Mat4) :
    block00 (embedBC (kron2 proj0 1) * embedAC G₀ +
             embedBC (kron2 proj1 1) * embedAC G₁) =
    kron2 proj0 (blockA_00 G₀) + kron2 proj1 (blockA_00 G₁) := by
  simp only [block00_add, block00_mul, block00_embedBC, block01_embedBC,
             block00_embedAC, block10_embedAC, Matrix.zero_mul, add_zero,
             kron2_mul, I₂, mul_one, one_mul]

/-- A-block (11) of a Π-split chain. -/
theorem block11_pi_split (G₀ G₁ : Mat4) :
    block11 (embedBC (kron2 proj0 1) * embedAC G₀ +
             embedBC (kron2 proj1 1) * embedAC G₁) =
    kron2 proj0 (blockA_11 G₀) + kron2 proj1 (blockA_11 G₁) := by
  simp only [block11_add, block11_mul, block11_embedBC, block10_embedBC,
             block11_embedAC, block01_embedAC, Matrix.zero_mul, zero_add,
             kron2_mul, I₂, mul_one, one_mul]

/-- A-block (01) of a Π-split chain. -/
theorem block01_pi_split (G₀ G₁ : Mat4) :
    block01 (embedBC (kron2 proj0 1) * embedAC G₀ +
             embedBC (kron2 proj1 1) * embedAC G₁) =
    kron2 proj0 (blockA_01 G₀) + kron2 proj1 (blockA_01 G₁) := by
  simp only [block01_add, block01_mul, block00_embedBC, block01_embedBC,
             block01_embedAC, block11_embedAC, Matrix.zero_mul, add_zero,
             kron2_mul, I₂, mul_one, one_mul]

/-- A-block (10) of a Π-split chain. -/
theorem block10_pi_split (G₀ G₁ : Mat4) :
    block10 (embedBC (kron2 proj0 1) * embedAC G₀ +
             embedBC (kron2 proj1 1) * embedAC G₁) =
    kron2 proj0 (blockA_10 G₀) + kron2 proj1 (blockA_10 G₁) := by
  simp only [block10_add, block10_mul, block10_embedBC, block11_embedBC,
             block10_embedAC, block00_embedAC, Matrix.zero_mul, zero_add,
             kron2_mul, I₂, mul_one, one_mul]

/-- A Mat4 whose off-diagonal A-blocks vanish is controlled-A.
    (HP-side copy of PY24's private `U_eq_kron2_proj_decomp`.) -/
theorem mat4_controlled_of_blockA_off_zero {U : Mat4}
    (h01 : blockA_01 U = 0) (h10 : blockA_10 U = 0) :
    U = kron2 proj0 (blockA_00 U) + kron2 proj1 (blockA_11 U) := by
  have hU02 : U 0 2 = 0 := by
    have := congr_fun (congr_fun h01 0) 0; simpa [blockA_01] using this
  have hU03 : U 0 3 = 0 := by
    have := congr_fun (congr_fun h01 0) 1; simpa [blockA_01] using this
  have hU12 : U 1 2 = 0 := by
    have := congr_fun (congr_fun h01 1) 0; simpa [blockA_01] using this
  have hU13 : U 1 3 = 0 := by
    have := congr_fun (congr_fun h01 1) 1; simpa [blockA_01] using this
  have hU20 : U 2 0 = 0 := by
    have := congr_fun (congr_fun h10 0) 0; simpa [blockA_10] using this
  have hU21 : U 2 1 = 0 := by
    have := congr_fun (congr_fun h10 0) 1; simpa [blockA_10] using this
  have hU30 : U 3 0 = 0 := by
    have := congr_fun (congr_fun h10 1) 0; simpa [blockA_10] using this
  have hU31 : U 3 1 = 0 := by
    have := congr_fun (congr_fun h10 1) 1; simpa [blockA_10] using this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kron2, proj0, proj1, blockA_00, blockA_11,
          Matrix.add_apply, Matrix.of_apply,
          hU02, hU03, hU12, hU13, hU20, hU21, hU30, hU31]

/-- `1 ⊗ Diag(1, d)` as an explicit Mat4 diagonal. -/
theorem kron2_one_diag_eq (d : ℂ) :
    kron2 1 (Matrix.diagonal ![1, d]) = Matrix.diagonal ![1, d, 1, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kron2, Matrix.diagonal, Matrix.of_apply, Matrix.one_apply]

/-- **Paper page 10, Eq.(6) joint-spectrum witness** — PROVED (iter 1034).

    With the middle gate NORMALIZED so that its first branch is the identity
    (`d₀ = 1`, established by the caller via `blockDiagB_diag_normalize`), the
    joint matrix `M_joint = kron2 proj0 X_eig + kron2 proj1 Y_eig` built from
    `X_eig = L_01·L_00†` and `Y_eig = L_11·L_10†` is unitarily similar to
    `Diag(d₀, d₀, d₁, d₁) = Diag(1, 1, d₁, d₁)`.

    ⚠️ The `d₀ = 1` hypothesis is ESSENTIAL, not cosmetic: without it the
    statement is FALSE — see `joint_spec_general_form_false`. The joint
    spectrum of the un-normalized chain is `(1, 1, d₁·conj d₀, …)`, i.e. it
    depends only on the ratio.

    **Proof** (paper page 11, the two "if qubit B is |0⟩/|1⟩" observations):
    1. `Dmid = C_B(1, Diag(1, d₁))` is controlled on B, so
       `L = Π₀·embedAC G₀ + Π₁·embedAC G₁` with `G₀ = U₂U₄`,
       `G₁ = U₂·(1 ⊗ Diag(1,d₁))·U₄` (`L_pi_split`).
    2. `Dg` diagonal ⇒ `block01 L = block10 L = 0` ⇒ both `G_j` are
       controlled-A (`block01_pi_split`, `mat4_controlled_of_blockA_off_zero`).
    3. Hence `L_{i0} = blockA_ii G₀`, `L_{i1} = blockA_ii G₁`
       (`block00_pi_split`, `block11_pi_split`), so
       `M_joint = G₁·G₀† = U₂·(1 ⊗ Diag(1, d₁))·U₂†` (using `U₄` unitary).
    4. `1 ⊗ Diag(1,d₁) = Diag(1, d₁, 1, d₁)`, so conjugating by
       `W = U₂·P_swap_4_12` reorders it to `Diag(1, 1, d₁, d₁)`
       (`P_swap_4_12_conj_diag`). -/
private theorem paper_lemma_4_2_joint_spec
    (Dg : DiagGate3)
    (W₁ W₅ U₂ U₄ Dmid : Mat4)
    (hW₁ : IsUnitary4 W₁) (hW₅ : IsUnitary4 W₅)
    (hU₂ : IsUnitary4 U₂) (hU₄ : IsUnitary4 U₄)
    (X_eig Y_eig : Mat2)
    (_hX_eig : IsUnitary2 X_eig) (_hY_eig : IsUnitary2 Y_eig)
    (d₀ d₁ : ℂ) (_hd₀ : Complex.normSq d₀ = 1) (_hd₁ : Complex.normSq d₁ = 1)
    (hd₀_one : d₀ = 1)
    (h_chain_factored : Dg.toMatrix =
      embedBC W₁ * (embedAC U₂ * embedBC Dmid * embedAC U₄) * embedBC W₅)
    (hDmid_def : Dmid =
      kron2 1 proj0 + kron2 (Matrix.diagonal ![d₀, d₁]) proj1)
    (hX_eig_def : X_eig =
      blockA_11 (block00 (embedAC U₂ * embedBC Dmid * embedAC U₄)) *
      (blockA_00 (block00 (embedAC U₂ * embedBC Dmid * embedAC U₄))).conjTranspose)
    (hY_eig_def : Y_eig =
      blockA_11 (block11 (embedAC U₂ * embedBC Dmid * embedAC U₄)) *
      (blockA_00 (block11 (embedAC U₂ * embedBC Dmid * embedAC U₄))).conjTranspose) :
    ∃ W : Mat4, IsUnitary4 W ∧
      W.conjTranspose * (kron2 proj0 X_eig + kron2 proj1 Y_eig) * W =
        Matrix.diagonal ![d₀, d₀, d₁, d₁] := by
  -- Step 1: `Dmid` in B-controlled form. THIS is where `d₀ = 1` is used.
  have hDmid_ctrl : Dmid = kron2 proj0 1 + kron2 proj1 (Matrix.diagonal ![1, d₁]) := by
    rw [hDmid_def, hd₀_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [kron2, proj0, proj1, Matrix.diagonal, Matrix.add_apply, Matrix.of_apply,
            Matrix.one_apply]
  -- Step 2: Π-split of L into its two B-branches (paper page 11 observations).
  have hsplit : embedAC U₂ * embedBC Dmid * embedAC U₄ =
      embedBC (kron2 proj0 1) * embedAC (U₂ * U₄) +
      embedBC (kron2 proj1 1) *
        embedAC (U₂ * kron2 1 (Matrix.diagonal ![1, d₁]) * U₄) := by
    rw [hDmid_ctrl]; exact L_pi_split U₂ U₄ d₁
  -- Step 3: L is block-diag-A (paper Lemma A.1 content, from Dg diagonal).
  have hDg_isDiag8 : IsDiag8 Dg.toMatrix := ⟨Dg, rfl⟩
  have h1 : embedBC W₁.conjTranspose * embedBC W₁ = 1 := by
    rw [embedBC_mul, hW₁, embedBC_one]
  have h5 : embedBC W₅ * embedBC W₅.conjTranspose = 1 := by
    rw [embedBC_mul, mul_eq_one_comm.mp hW₅, embedBC_one]
  have hL_absorb : embedBC W₁.conjTranspose * Dg.toMatrix * embedBC W₅.conjTranspose =
      embedAC U₂ * embedBC Dmid * embedAC U₄ := by
    rw [h_chain_factored]
    calc embedBC W₁.conjTranspose *
          (embedBC W₁ * (embedAC U₂ * embedBC Dmid * embedAC U₄) * embedBC W₅) *
          embedBC W₅.conjTranspose
        = (embedBC W₁.conjTranspose * embedBC W₁) *
          (embedAC U₂ * embedBC Dmid * embedAC U₄) *
          (embedBC W₅ * embedBC W₅.conjTranspose) := by noncomm_ring
      _ = 1 * (embedAC U₂ * embedBC Dmid * embedAC U₄) * 1 := by rw [h1, h5]
      _ = embedAC U₂ * embedBC Dmid * embedAC U₄ := by rw [one_mul, mul_one]
  have hb01_L : block01 (embedAC U₂ * embedBC Dmid * embedAC U₄) = 0 := by
    rw [← hL_absorb, block01_embedBC_mul_embedBC, isDiag8_block01 _ hDg_isDiag8]
    simp
  have hb10_L : block10 (embedAC U₂ * embedBC Dmid * embedAC U₄) = 0 := by
    rw [← hL_absorb, block10_embedBC_mul_embedBC, isDiag8_block10 _ hDg_isDiag8]
    simp
  -- Step 4: hence the off-diagonal A-blocks of G₀ and G₁ vanish.
  have h01' := hb01_L
  rw [hsplit, block01_pi_split] at h01'
  have h10' := hb10_L
  rw [hsplit, block10_pi_split] at h10'
  have hA01_G₀ : blockA_01 (U₂ * U₄) = 0 := by
    have := congrArg blockA_00 h01'
    rw [(blockA_of_controlled _ _).1] at this
    simpa [blockA_00] using this
  have hA01_G₁ : blockA_01 (U₂ * kron2 1 (Matrix.diagonal ![1, d₁]) * U₄) = 0 := by
    have := congrArg blockA_11 h01'
    rw [(blockA_of_controlled _ _).2.2.2] at this
    simpa [blockA_11] using this
  have hA10_G₀ : blockA_10 (U₂ * U₄) = 0 := by
    have := congrArg blockA_00 h10'
    rw [(blockA_of_controlled _ _).1] at this
    simpa [blockA_00] using this
  have hA10_G₁ : blockA_10 (U₂ * kron2 1 (Matrix.diagonal ![1, d₁]) * U₄) = 0 := by
    have := congrArg blockA_11 h10'
    rw [(blockA_of_controlled _ _).2.2.2] at this
    simpa [blockA_11] using this
  -- Step 5: read `X_eig`, `Y_eig` off the branch gates' A-blocks.
  have hX : X_eig = blockA_00 (U₂ * kron2 1 (Matrix.diagonal ![1, d₁]) * U₄) *
      (blockA_00 (U₂ * U₄)).conjTranspose := by
    rw [hX_eig_def, hsplit, block00_pi_split, (blockA_of_controlled _ _).1,
        (blockA_of_controlled _ _).2.2.2]
  have hY : Y_eig = blockA_11 (U₂ * kron2 1 (Matrix.diagonal ![1, d₁]) * U₄) *
      (blockA_11 (U₂ * U₄)).conjTranspose := by
    rw [hY_eig_def, hsplit, block11_pi_split, (blockA_of_controlled _ _).1,
        (blockA_of_controlled _ _).2.2.2]
  -- Step 6: therefore `M_joint = G₁ · G₀†`.
  have hMj : kron2 proj0 X_eig + kron2 proj1 Y_eig =
      (U₂ * kron2 1 (Matrix.diagonal ![1, d₁]) * U₄) * (U₂ * U₄).conjTranspose := by
    conv_rhs => rw [mat4_controlled_of_blockA_off_zero hA01_G₁ hA10_G₁,
                    mat4_controlled_of_blockA_off_zero hA01_G₀ hA10_G₀]
    rw [block_diag_first_conjT, block_diag_first_mul, hX, hY]
  -- Step 7: `G₁ · G₀† = U₂ · (1 ⊗ Diag(1, d₁)) · U₂†` (the `U₄`s cancel).
  have hG₁G₀ : (U₂ * kron2 1 (Matrix.diagonal ![1, d₁]) * U₄) * (U₂ * U₄).conjTranspose =
      U₂ * kron2 1 (Matrix.diagonal ![1, d₁]) * U₂.conjTranspose := by
    rw [Matrix.conjTranspose_mul]
    calc U₂ * kron2 1 (Matrix.diagonal ![1, d₁]) * U₄ *
          (U₄.conjTranspose * U₂.conjTranspose)
        = U₂ * kron2 1 (Matrix.diagonal ![1, d₁]) *
            (U₄ * U₄.conjTranspose) * U₂.conjTranspose := by noncomm_ring
      _ = U₂ * kron2 1 (Matrix.diagonal ![1, d₁]) * 1 * U₂.conjTranspose := by
            rw [mul_eq_one_comm.mp hU₄]
      _ = U₂ * kron2 1 (Matrix.diagonal ![1, d₁]) * U₂.conjTranspose := by rw [mul_one]
  -- Step 8: conjugate by `U₂ · P_swap_4_12` to reach `Diag(1, 1, d₁, d₁)`.
  refine ⟨U₂ * P_swap_4_12, isUnitary4_mul hU₂ P_swap_4_12_unitary, ?_⟩
  rw [hMj, hG₁G₀, Matrix.conjTranspose_mul]
  calc P_swap_4_12.conjTranspose * U₂.conjTranspose *
        (U₂ * kron2 1 (Matrix.diagonal ![1, d₁]) * U₂.conjTranspose) *
        (U₂ * P_swap_4_12)
      = P_swap_4_12.conjTranspose * (U₂.conjTranspose * U₂) *
          kron2 1 (Matrix.diagonal ![1, d₁]) * (U₂.conjTranspose * U₂) *
          P_swap_4_12 := by noncomm_ring
    _ = P_swap_4_12.conjTranspose * 1 * kron2 1 (Matrix.diagonal ![1, d₁]) * 1 *
          P_swap_4_12 := by rw [hU₂]
    _ = P_swap_4_12.conjTranspose * Matrix.diagonal ![1, d₁, 1, d₁] * P_swap_4_12 := by
          rw [mul_one, mul_one, kron2_one_diag_eq]
    _ = Matrix.diagonal ![1, 1, d₁, d₁] := P_swap_4_12_conj_diag 1 d₁ 1 d₁
    _ = Matrix.diagonal ![d₀, d₀, d₁, d₁] := by rw [hd₀_one]

/-- **Paper Eq.(7)-(9) chain rewrite for Lemma 4.2 Case (1)** (essential stub).
    ⚠️ Renamed from `paper_lemma_A_2_chain_form` (iter 187b): HP Lemma A.2 is
    the Horn-Johnson spectral theorem `V = P†·Diag·P` (a basic fact, already
    covered by `py24_lemma_A_3` for 2×2), NOT the chain rewrite. The G₀, G₁
    matrices come from APPLYING the spectral theorem to `X_eig` and `Y_eig`
    inside the Eq.(7)-(9) algebra — but the chain rewrite itself is paper
    page 11 algebra, NOT a named appendix lemma.

    Given the Case (1) trichotomy output (`Vx, Vy : Mat2` diagonalizing
    `X_eig` and `Y_eig` to `diag(d₀, d₁)`), produce the rewritten chain in
    the BC-AC(C(M))-BC-AC(C(N))-BC form consumed by `paper_lemma_4_1`.

    **Proof status**: scaffolding stub (essential — paper page 11 algebra).

    **Proof outline** (paper Eq.(7)-(9), L726-746):
    1. By `_hX_eq`: block-A structure of `embedAC U₂ · embedBC Dmid · embedAC U₄`
       has its `block00 := L_00, L_01, ..., L_11` blocks where
       `Vx† · (L_01 · L_00†) · Vx = diag![d₀, d₁]`.
    2. Construct `G₀, G₁ : Mat2` from paper Eq.(8) such that
       `L_01 = G₀ · L_00` and `L_11 = G₁ · L_10`, using Vx, Vy + Lemma A.2
       (= py24_lemma_A_3 spectral).
    3. Construct `F₃` from Vx, Vy, L blocks, and the chain identity.
       Paper's specific construction: `F₃ = (1⊗L_00) · diagonal(... ,Vy†) · ...`.
       (Multi-line paper-specific algebra.)
    4. Paper sets `M = 1` (Mat2 identity) and
       `N = (L_00⁻¹) · diag(d₀, d₁)` (or similar 1-qubit gate).
       Plug into target chain form and verify via Lemma A.7 expansion.

    **Helper landscape** (iter 235 cross-references):
    - `unitary_conj_invert_Mat2` (iter 233): converts `_hX_eq` from
      `Vx† · (L_01·L_00†) · Vx = diag![d₀, d₁]` form into the inverse
      `L_01·L_00† = Vx · diag![d₀, d₁] · Vx†` needed for Eq.(8) substitution.
    - `py24_lemma_A_3` (PY24, oracle): spectral theorem used to construct
      G₀, G₁ in step 2.
    - `block_diag_A_blocks_unitary` (BlockDecomp.lean): extract L_00, L_11
      unitarity from L's unitarity + block-diag-A property. Already used
      inline in paper_lemma_4_2's body. -/
private theorem paper_4_2_eq_7_9_chain_rewrite
    (Dg : DiagGate3)
    (W₁ W₅ U₂ U₄ Dmid : Mat4)
    (_hW₁ : IsUnitary4 W₁) (_hW₅ : IsUnitary4 W₅)
    (Vx Vy : Mat2) (_hVx : IsUnitary2 Vx) (_hVy : IsUnitary2 Vy)
    (d₀ d₁ : ℂ) (_hd₀ : Complex.normSq d₀ = 1) (_hd₁ : Complex.normSq d₁ = 1)
    (_hX_eq : Vx.conjTranspose *
      (blockA_11 (block00 (embedAC U₂ * embedBC Dmid * embedAC U₄)) *
       (blockA_00 (block00 (embedAC U₂ * embedBC Dmid * embedAC U₄))).conjTranspose) * Vx =
      Matrix.diagonal ![d₀, d₁])
    (_hY_eq : Vy.conjTranspose *
      (blockA_11 (block11 (embedAC U₂ * embedBC Dmid * embedAC U₄)) *
       (blockA_00 (block11 (embedAC U₂ * embedBC Dmid * embedAC U₄))).conjTranspose) * Vy =
      Matrix.diagonal ![d₀, d₁])
    (_h_chain_factored : Dg.toMatrix =
      embedBC W₁ * (embedAC U₂ * embedBC Dmid * embedAC U₄) * embedBC W₅)
    (_hDmid_form : Dmid =
      kron2 1 proj0 + kron2 (Matrix.diagonal ![d₀, d₁]) proj1) :
    ∃ F₃ : Mat4, ∃ M N : Mat2,
      IsUnitary4 F₃ ∧ IsUnitary2 M ∧ IsUnitary2 N ∧
      Dg.toMatrix = embedBC W₁ * embedAC (kron2 proj0 1 + kron2 proj1 M) *
        embedBC F₃ * embedAC (kron2 proj0 1 + kron2 proj1 N) * embedBC W₅ := by
  -- =========================================================================
  -- Iter 253+ (user directed): commit to multi-iter closure of paper Eq.(7)-(9).
  -- Step 1 [DONE iter 253]: invert spec hypotheses via unitary_conj_invert_Mat2
  -- to get L_01·L_00† and L_11·L_10† in V·Diag·V† form (paper Eq.(7) substrates).
  -- =========================================================================
  have hX_inv :
      blockA_11 (block00 (embedAC U₂ * embedBC Dmid * embedAC U₄)) *
      (blockA_00 (block00 (embedAC U₂ * embedBC Dmid * embedAC U₄))).conjTranspose =
      Vx * Matrix.diagonal ![d₀, d₁] * Vx.conjTranspose :=
    unitary_conj_invert_Mat2 _hVx _hX_eq
  have hY_inv :
      blockA_11 (block11 (embedAC U₂ * embedBC Dmid * embedAC U₄)) *
      (blockA_00 (block11 (embedAC U₂ * embedBC Dmid * embedAC U₄))).conjTranspose =
      Vy * Matrix.diagonal ![d₀, d₁] * Vy.conjTranspose :=
    unitary_conj_invert_Mat2 _hVy _hY_eq
  -- =========================================================================
  -- Iter 254: derive L unitarity from chain identity (paper Lemma A.1 input).
  -- Strategy: from _h_chain_factored, L = W₁† · Dg · W₅† (after absorbing W₁,
  -- W₅). All three factors are unitary, so L is unitary.
  -- =========================================================================
  have hL_eq_absorb :
      embedBC W₁.conjTranspose * Dg.toMatrix * embedBC W₅.conjTranspose =
      embedAC U₂ * embedBC Dmid * embedAC U₄ := by
    have h_BCW1 : embedBC W₁.conjTranspose * embedBC W₁ = 1 := by
      rw [embedBC_mul, _hW₁, embedBC_one]
    have h_BCW5 : embedBC W₅ * embedBC W₅.conjTranspose = 1 := by
      rw [embedBC_mul, mul_eq_one_comm.mp _hW₅, embedBC_one]
    calc embedBC W₁.conjTranspose * Dg.toMatrix * embedBC W₅.conjTranspose
        = embedBC W₁.conjTranspose *
            (embedBC W₁ * (embedAC U₂ * embedBC Dmid * embedAC U₄) * embedBC W₅) *
            embedBC W₅.conjTranspose := by rw [← _h_chain_factored]
      _ = (embedBC W₁.conjTranspose * embedBC W₁) *
          (embedAC U₂ * embedBC Dmid * embedAC U₄) *
          (embedBC W₅ * embedBC W₅.conjTranspose) := by noncomm_ring
      _ = 1 * (embedAC U₂ * embedBC Dmid * embedAC U₄) * 1 := by
            rw [h_BCW1, h_BCW5]
      _ = embedAC U₂ * embedBC Dmid * embedAC U₄ := by rw [one_mul, mul_one]
  -- =========================================================================
  -- Iter 255: derive L unitarity from hL_eq_absorb. L is product of unitaries
  -- (W₁†, Dg, W₅†), so L is unitary.
  -- =========================================================================
  have hL_unit : (embedAC U₂ * embedBC Dmid * embedAC U₄).conjTranspose *
                 (embedAC U₂ * embedBC Dmid * embedAC U₄) = 1 := by
    rw [← hL_eq_absorb]
    have h_BCW1_right : embedBC W₁ * embedBC W₁.conjTranspose = 1 := by
      rw [embedBC_mul, mul_eq_one_comm.mp _hW₁, embedBC_one]
    have h_BCW5_left : embedBC W₅.conjTranspose * embedBC W₅ = 1 := by
      rw [embedBC_mul, _hW₅, embedBC_one]
    calc (embedBC W₁.conjTranspose * Dg.toMatrix * embedBC W₅.conjTranspose).conjTranspose *
         (embedBC W₁.conjTranspose * Dg.toMatrix * embedBC W₅.conjTranspose)
        = embedBC W₅ * Dg.toMatrix.conjTranspose * embedBC W₁ *
          (embedBC W₁.conjTranspose * Dg.toMatrix * embedBC W₅.conjTranspose) := by
            simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
                       embedBC_conjTranspose]
            noncomm_ring
      _ = embedBC W₅ * Dg.toMatrix.conjTranspose *
          (embedBC W₁ * embedBC W₁.conjTranspose) *
          Dg.toMatrix * embedBC W₅.conjTranspose := by noncomm_ring
      _ = embedBC W₅ * Dg.toMatrix.conjTranspose * 1 *
          Dg.toMatrix * embedBC W₅.conjTranspose := by rw [h_BCW1_right]
      _ = embedBC W₅ * (Dg.toMatrix.conjTranspose * Dg.toMatrix) *
          embedBC W₅.conjTranspose := by noncomm_ring
      _ = embedBC W₅ * 1 * embedBC W₅.conjTranspose := by rw [Dg.toMatrix_unitary]
      _ = embedBC W₅ * embedBC W₅.conjTranspose := by rw [mul_one]
      _ = 1 := by rw [embedBC_mul, mul_eq_one_comm.mp _hW₅, embedBC_one]
  -- =========================================================================
  -- Iter 257: derive L block-diag-A (block01 L = 0 and block10 L = 0).
  -- Strategy: L = W₁† · Dg · W₅† and Dg is diagonal → off-A-blocks vanish.
  -- =========================================================================
  have hL_block01 :
      block01 (embedAC U₂ * embedBC Dmid * embedAC U₄) = 0 := by
    rw [← hL_eq_absorb]
    exact isDiag8_block01_embedBC W₁.conjTranspose W₅.conjTranspose
      Dg.toMatrix ⟨Dg, rfl⟩
  have hL_block10 :
      block10 (embedAC U₂ * embedBC Dmid * embedAC U₄) = 0 := by
    rw [← hL_eq_absorb]
    exact isDiag8_block10_embedBC W₁.conjTranspose W₅.conjTranspose
      Dg.toMatrix ⟨Dg, rfl⟩
  -- =========================================================================
  -- Iter 258: sub-block unitarity via block_diag_A_blocks_unitary, and
  -- define L_00, L_01, L_10, L_11 via set bindings (paper's L_{ab}: the
  -- 2×2 C-action when (A, B) = (a, b)).
  -- =========================================================================
  obtain ⟨hL_block00_unit, hL_block11_unit⟩ :=
    block_diag_A_blocks_unitary hL_unit hL_block01 hL_block10
  set L_00 : Mat2 :=
    blockA_00 (block00 (embedAC U₂ * embedBC Dmid * embedAC U₄))
    with hL_00_def
  set L_01 : Mat2 :=
    blockA_11 (block00 (embedAC U₂ * embedBC Dmid * embedAC U₄))
    with hL_01_def
  set L_10 : Mat2 :=
    blockA_00 (block11 (embedAC U₂ * embedBC Dmid * embedAC U₄))
    with hL_10_def
  set L_11 : Mat2 :=
    blockA_11 (block11 (embedAC U₂ * embedBC Dmid * embedAC U₄))
    with hL_11_def
  -- =========================================================================
  -- Iter 261: derive block-diag-B structure of L via ZI-commutation.
  -- Step (a): block00 L commutes with ZI (Mat4 ZI = kron2 pauliZ I₂).
  -- Strategy: explicit form of block00 L (using block00_mul + embedAC/embedBC
  -- block helpers), then commute ZI through each factor — ZI commutes with
  -- kron2 I₂ X (any X) and with Dmid (using _hDmid_form + diag commute Z).
  -- =========================================================================
  -- Auxiliary commutations.
  have h_kron2_I_ZI : ∀ X : Mat2, kron2 I₂ X * ZI = ZI * kron2 I₂ X := by
    intro X
    show kron2 I₂ X * kron2 pauliZ I₂ = kron2 pauliZ I₂ * kron2 I₂ X
    rw [kron2_mul, kron2_mul]
    unfold I₂
    rw [one_mul, mul_one, mul_one, one_mul]
  have h_diag_pauliZ : (Matrix.diagonal ![d₀, d₁] : Mat2) * pauliZ =
                       pauliZ * Matrix.diagonal ![d₀, d₁] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliZ, Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_two,
            Matrix.of_apply] <;> ring
  have h_Dmid_ZI : Dmid * ZI = ZI * Dmid := by
    rw [_hDmid_form]
    show (kron2 1 proj0 + kron2 (Matrix.diagonal ![d₀, d₁]) proj1) *
           kron2 pauliZ I₂ =
         kron2 pauliZ I₂ *
           (kron2 1 proj0 + kron2 (Matrix.diagonal ![d₀, d₁]) proj1)
    rw [add_mul, mul_add, kron2_mul, kron2_mul, kron2_mul, kron2_mul]
    simp only [I₂, one_mul, mul_one, h_diag_pauliZ]
  -- Explicit form of block00 L.
  have h_block00_L_eq :
      block00 (embedAC U₂ * embedBC Dmid * embedAC U₄) =
        kron2 I₂ (blockA_00 U₂) * Dmid * kron2 I₂ (blockA_00 U₄) +
        kron2 I₂ (blockA_01 U₂) * Dmid * kron2 I₂ (blockA_10 U₄) := by
    rw [block00_mul (embedAC U₂ * embedBC Dmid) (embedAC U₄),
        block00_mul (embedAC U₂) (embedBC Dmid),
        block01_mul (embedAC U₂) (embedBC Dmid)]
    simp only [block00_embedAC, block01_embedAC, block10_embedAC,
               block00_embedBC, block11_embedBC, block01_embedBC,
               block10_embedBC,
               Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  -- Generic term-level commutation helper (iter 262 refactor of iter 261's
  -- two duplicated calcs into one parametric lemma).
  have h_term_ZI : ∀ A B : Mat2,
      kron2 I₂ A * Dmid * kron2 I₂ B * ZI =
      ZI * (kron2 I₂ A * Dmid * kron2 I₂ B) := by
    intros A B
    calc kron2 I₂ A * Dmid * kron2 I₂ B * ZI
        = kron2 I₂ A * Dmid * (kron2 I₂ B * ZI) := by noncomm_ring
      _ = kron2 I₂ A * Dmid * (ZI * kron2 I₂ B) := by rw [h_kron2_I_ZI]
      _ = kron2 I₂ A * (Dmid * ZI) * kron2 I₂ B := by noncomm_ring
      _ = kron2 I₂ A * (ZI * Dmid) * kron2 I₂ B := by rw [h_Dmid_ZI]
      _ = (kron2 I₂ A * ZI) * Dmid * kron2 I₂ B := by noncomm_ring
      _ = (ZI * kron2 I₂ A) * Dmid * kron2 I₂ B := by rw [h_kron2_I_ZI]
      _ = ZI * (kron2 I₂ A * Dmid * kron2 I₂ B) := by noncomm_ring
  -- Commutation: block00 L commutes with ZI.
  have h_block00_L_ZI :
      block00 (embedAC U₂ * embedBC Dmid * embedAC U₄) * ZI =
      ZI * block00 (embedAC U₂ * embedBC Dmid * embedAC U₄) := by
    rw [h_block00_L_eq, add_mul, mul_add]
    congr 1
    · exact h_term_ZI (blockA_00 U₂) (blockA_00 U₄)
    · exact h_term_ZI (blockA_01 U₂) (blockA_10 U₄)
  -- =========================================================================
  -- Iter 262: parallel explicit form + ZI-commutation for block11 L, then
  -- apply commutes_ZI_implies_blockDiagFirst to both block00 L and block11 L
  -- to derive blockA_01/blockA_10 vanishing.
  -- =========================================================================
  have h_block11_L_eq :
      block11 (embedAC U₂ * embedBC Dmid * embedAC U₄) =
        kron2 I₂ (blockA_10 U₂) * Dmid * kron2 I₂ (blockA_01 U₄) +
        kron2 I₂ (blockA_11 U₂) * Dmid * kron2 I₂ (blockA_11 U₄) := by
    rw [block11_mul (embedAC U₂ * embedBC Dmid) (embedAC U₄),
        block10_mul (embedAC U₂) (embedBC Dmid),
        block11_mul (embedAC U₂) (embedBC Dmid)]
    simp only [block00_embedAC, block01_embedAC, block10_embedAC,
               block11_embedAC,
               block00_embedBC, block11_embedBC, block01_embedBC,
               block10_embedBC,
               Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  have h_block11_L_ZI :
      block11 (embedAC U₂ * embedBC Dmid * embedAC U₄) * ZI =
      ZI * block11 (embedAC U₂ * embedBC Dmid * embedAC U₄) := by
    rw [h_block11_L_eq, add_mul, mul_add]
    congr 1
    · exact h_term_ZI (blockA_10 U₂) (blockA_01 U₄)
    · exact h_term_ZI (blockA_11 U₂) (blockA_11 U₄)
  -- Apply commutes_ZI_implies_blockDiagFirst to extract block-diag-B structure.
  have h_block00_L_bdf : IsBlockDiagFirst
      (block00 (embedAC U₂ * embedBC Dmid * embedAC U₄)) :=
    commutes_ZI_implies_blockDiagFirst _ h_block00_L_ZI
  have h_block11_L_bdf : IsBlockDiagFirst
      (block11 (embedAC U₂ * embedBC Dmid * embedAC U₄)) :=
    commutes_ZI_implies_blockDiagFirst _ h_block11_L_ZI
  -- Extract blockA_01/10 vanishing via blockA_of_controlled.
  obtain ⟨P₀_block00, P₁_block00, h_block00_form⟩ := h_block00_L_bdf
  obtain ⟨P₀_block11, P₁_block11, h_block11_form⟩ := h_block11_L_bdf
  have h_block00_L_blockA_01 :
      blockA_01 (block00 (embedAC U₂ * embedBC Dmid * embedAC U₄)) = 0 := by
    rw [h_block00_form]; exact (blockA_of_controlled P₀_block00 P₁_block00).2.1
  have h_block00_L_blockA_10 :
      blockA_10 (block00 (embedAC U₂ * embedBC Dmid * embedAC U₄)) = 0 := by
    rw [h_block00_form]; exact (blockA_of_controlled P₀_block00 P₁_block00).2.2.1
  have h_block11_L_blockA_01 :
      blockA_01 (block11 (embedAC U₂ * embedBC Dmid * embedAC U₄)) = 0 := by
    rw [h_block11_form]; exact (blockA_of_controlled P₀_block11 P₁_block11).2.1
  have h_block11_L_blockA_10 :
      blockA_10 (block11 (embedAC U₂ * embedBC Dmid * embedAC U₄)) = 0 := by
    rw [h_block11_form]; exact (blockA_of_controlled P₀_block11 P₁_block11).2.2.1
  -- =========================================================================
  -- Iter 263: derive Mat2 unitarity of L_00, L_01, L_10, L_11 from
  -- block00/11 L Mat4-unitary + blockA_10 vanishing via existing helpers
  -- `blockA_00_unitary_of_blockA_10_zero` and
  -- `blockA_11_unitary_of_blockA_10_zero` (PY24/Lemmas.lean L2327, L2378).
  -- =========================================================================
  have hL_00_unit : IsUnitary2 L_00 :=
    blockA_00_unitary_of_blockA_10_zero hL_block00_unit h_block00_L_blockA_10
  have hL_01_unit : IsUnitary2 L_01 :=
    blockA_11_unitary_of_blockA_10_zero hL_block00_unit h_block00_L_blockA_10
  have hL_10_unit : IsUnitary2 L_10 :=
    blockA_00_unitary_of_blockA_10_zero hL_block11_unit h_block11_L_blockA_10
  have hL_11_unit : IsUnitary2 L_11 :=
    blockA_11_unitary_of_blockA_10_zero hL_block11_unit h_block11_L_blockA_10
  -- =========================================================================
  -- Iter 265: define F₃, M, N and prove their unitarity per iter 264
  -- reflection-derived paper-faithful construction.
  --   F₃ := kron2 proj0 L_00 + kron2 proj1 L_01  (Mat4 controlled-A on B)
  --   M  := Vy · Vx†                              (Mat2)
  --   N  := L_00† · Vx · Vy† · L_10               (Mat2)
  -- =========================================================================
  set F₃ : Mat4 := kron2 proj0 L_00 + kron2 proj1 L_01 with hF₃_def
  set M : Mat2 := Vy * Vx.conjTranspose with hM_def
  set N : Mat2 := L_00.conjTranspose * Vx * Vy.conjTranspose * L_10 with hN_def
  have hF₃_unit : IsUnitary4 F₃ := controlled_A_unitary hL_00_unit hL_01_unit
  have hM_unit : IsUnitary2 M :=
    isUnitary2_mul _hVy (isUnitary2_conjTranspose _hVx)
  have hN_unit : IsUnitary2 N := by
    refine isUnitary2_mul ?_ hL_10_unit
    refine isUnitary2_mul ?_ (isUnitary2_conjTranspose _hVy)
    exact isUnitary2_mul (isUnitary2_conjTranspose hL_00_unit) _hVx
  -- =========================================================================
  -- Iter 266: key algebraic identities for the M·F₃_b·N = L_(1,b) chain.
  --   M · L_00 · N = L_10   (collapses via L_00·L_00† = 1, Vx unitary, Vy unitary)
  --   M · L_01 · N = L_11   (uses _hX_eq + hY_inv + L_10 unitary)
  -- =========================================================================
  have hL_00_right : L_00 * L_00.conjTranspose = 1 :=
    Matrix.mul_eq_one_comm.mp hL_00_unit
  have hVy_right : Vy * Vy.conjTranspose = 1 :=
    Matrix.mul_eq_one_comm.mp _hVy
  have hM_L00_N : M * L_00 * N = L_10 := by
    show Vy * Vx.conjTranspose * L_00 *
         (L_00.conjTranspose * Vx * Vy.conjTranspose * L_10) = L_10
    calc Vy * Vx.conjTranspose * L_00 *
           (L_00.conjTranspose * Vx * Vy.conjTranspose * L_10)
        = Vy * Vx.conjTranspose * (L_00 * L_00.conjTranspose) *
            Vx * Vy.conjTranspose * L_10 := by noncomm_ring
      _ = Vy * Vx.conjTranspose * 1 * Vx * Vy.conjTranspose * L_10 := by
            rw [hL_00_right]
      _ = Vy * (Vx.conjTranspose * Vx) * Vy.conjTranspose * L_10 := by
            noncomm_ring
      _ = Vy * 1 * Vy.conjTranspose * L_10 := by rw [_hVx]
      _ = (Vy * Vy.conjTranspose) * L_10 := by noncomm_ring
      _ = 1 * L_10 := by rw [hVy_right]
      _ = L_10 := one_mul _
  have hM_L01_N : M * L_01 * N = L_11 := by
    show Vy * Vx.conjTranspose * L_01 *
         (L_00.conjTranspose * Vx * Vy.conjTranspose * L_10) = L_11
    calc Vy * Vx.conjTranspose * L_01 *
           (L_00.conjTranspose * Vx * Vy.conjTranspose * L_10)
        = Vy * (Vx.conjTranspose * (L_01 * L_00.conjTranspose) * Vx) *
            Vy.conjTranspose * L_10 := by noncomm_ring
      _ = Vy * Matrix.diagonal ![d₀, d₁] * Vy.conjTranspose * L_10 := by
            rw [_hX_eq]
      _ = (Vy * Matrix.diagonal ![d₀, d₁] * Vy.conjTranspose) * L_10 := by
            noncomm_ring
      _ = L_11 * L_10.conjTranspose * L_10 := by rw [← hY_inv]
      _ = L_11 * (L_10.conjTranspose * L_10) := by noncomm_ring
      _ = L_11 * 1 := by rw [hL_10_unit]
      _ = L_11 := mul_one _
  -- =========================================================================
  -- Iter 267: block-by-block proof of the 3-factor chain identity
  -- L = embedAC C(M) · embedBC F₃ · embedAC C(N).
  -- =========================================================================
  -- Identify P_block00 and P_block11 destructure outputs with L_ab.
  have hP₀_block11_eq_L_10 : P₀_block11 = L_10 := by
    have h := (blockA_of_controlled P₀_block11 P₁_block11).1
    rw [← h_block11_form] at h
    exact h.symm
  have hP₁_block11_eq_L_11 : P₁_block11 = L_11 := by
    have h := (blockA_of_controlled P₀_block11 P₁_block11).2.2.2
    rw [← h_block11_form] at h
    exact h.symm
  have hP₀_block00_eq_L_00 : P₀_block00 = L_00 := by
    have h := (blockA_of_controlled P₀_block00 P₁_block00).1
    rw [← h_block00_form] at h
    exact h.symm
  have hP₁_block00_eq_L_01 : P₁_block00 = L_01 := by
    have h := (blockA_of_controlled P₀_block00 P₁_block00).2.2.2
    rw [← h_block00_form] at h
    exact h.symm
  -- block00 L = F₃ (via h_block00_form + index identification + F₃ definition).
  have h_block00_L_eq_F₃ :
      block00 (embedAC U₂ * embedBC Dmid * embedAC U₄) = F₃ := by
    rw [h_block00_form, hP₀_block00_eq_L_00, hP₁_block00_eq_L_01]
  -- block11 L = kron2 proj0 L_10 + kron2 proj1 L_11.
  have h_block11_L_eq_LL :
      block11 (embedAC U₂ * embedBC Dmid * embedAC U₄) =
      kron2 proj0 L_10 + kron2 proj1 L_11 := by
    rw [h_block11_form, hP₀_block11_eq_L_10, hP₁_block11_eq_L_11]
  -- Compute block00, block11, block01, block10 of the 3-factor product.
  have h_block00_product :
      block00 (embedAC (kron2 proj0 1 + kron2 proj1 M) * embedBC F₃ *
               embedAC (kron2 proj0 1 + kron2 proj1 N)) = F₃ := by
    rw [block00_mul, block00_mul]
    simp only [block00_embedAC_of_controlled, block01_embedAC_of_controlled,
               block10_embedAC_of_controlled, block11_embedAC_of_controlled,
               block00_embedBC, block01_embedBC, block10_embedBC,
               block11_embedBC, kron2_one_one_eq_one,
               Matrix.mul_zero, Matrix.zero_mul,
               add_zero, zero_add, one_mul, mul_one]
  have h_block11_product_raw :
      block11 (embedAC (kron2 proj0 1 + kron2 proj1 M) * embedBC F₃ *
               embedAC (kron2 proj0 1 + kron2 proj1 N)) =
      kron2 1 M * F₃ * kron2 1 N := by
    rw [block11_mul, block10_mul, block11_mul]
    simp only [block00_embedAC_of_controlled, block01_embedAC_of_controlled,
               block10_embedAC_of_controlled, block11_embedAC_of_controlled,
               block00_embedBC, block01_embedBC, block10_embedBC,
               block11_embedBC, Matrix.mul_zero, Matrix.zero_mul,
               add_zero, zero_add]
  have h_block01_product :
      block01 (embedAC (kron2 proj0 1 + kron2 proj1 M) * embedBC F₃ *
               embedAC (kron2 proj0 1 + kron2 proj1 N)) = 0 := by
    rw [block01_mul, block00_mul, block01_mul]
    simp only [block00_embedAC_of_controlled, block01_embedAC_of_controlled,
               block10_embedAC_of_controlled, block11_embedAC_of_controlled,
               block00_embedBC, block01_embedBC, block10_embedBC,
               block11_embedBC, Matrix.mul_zero, Matrix.zero_mul,
               add_zero, zero_add]
  have h_block10_product :
      block10 (embedAC (kron2 proj0 1 + kron2 proj1 M) * embedBC F₃ *
               embedAC (kron2 proj0 1 + kron2 proj1 N)) = 0 := by
    rw [block10_mul, block10_mul, block11_mul]
    simp only [block00_embedAC_of_controlled, block01_embedAC_of_controlled,
               block10_embedAC_of_controlled, block11_embedAC_of_controlled,
               block00_embedBC, block01_embedBC, block10_embedBC,
               block11_embedBC, Matrix.mul_zero, Matrix.zero_mul,
               add_zero, zero_add]
  -- Expand kron2 1 M · F₃ · kron2 1 N to match block11 L.
  have h_kron2_F₃_expand :
      kron2 1 M * F₃ * kron2 1 N = kron2 proj0 L_10 + kron2 proj1 L_11 := by
    rw [hF₃_def, mul_add, add_mul, kron2_mul, kron2_mul,
        kron2_mul, kron2_mul, one_mul, mul_one, mul_one, one_mul, hM_L00_N,
        hM_L01_N]
  have h_block11_product :
      block11 (embedAC (kron2 proj0 1 + kron2 proj1 M) * embedBC F₃ *
               embedAC (kron2 proj0 1 + kron2 proj1 N)) =
      kron2 proj0 L_10 + kron2 proj1 L_11 := by
    rw [h_block11_product_raw, h_kron2_F₃_expand]
  -- Assemble the chain identity.
  have h_L_eq_product :
      embedAC U₂ * embedBC Dmid * embedAC U₄ =
      embedAC (kron2 proj0 1 + kron2 proj1 M) * embedBC F₃ *
        embedAC (kron2 proj0 1 + kron2 proj1 N) := by
    apply mat8_eq_of_blocks_off_diag_zero
    · rw [h_block00_L_eq_F₃, h_block00_product]
    · rw [h_block11_L_eq_LL, h_block11_product]
    · exact hL_block01
    · exact hL_block10
    · exact h_block01_product
    · exact h_block10_product
  -- Close the existential.
  refine ⟨F₃, M, N, hF₃_unit, hM_unit, hN_unit, ?_⟩
  calc Dg.toMatrix
      = embedBC W₁ * (embedAC U₂ * embedBC Dmid * embedAC U₄) *
          embedBC W₅ := _h_chain_factored
    _ = embedBC W₁ * (embedAC (kron2 proj0 1 + kron2 proj1 M) *
          embedBC F₃ * embedAC (kron2 proj0 1 + kron2 proj1 N)) *
          embedBC W₅ := by rw [h_L_eq_product]
    _ = embedBC W₁ * embedAC (kron2 proj0 1 + kron2 proj1 M) *
          embedBC F₃ * embedAC (kron2 proj0 1 + kron2 proj1 N) *
          embedBC W₅ := by noncomm_ring

/-- **Paper page 11, Case (1) witness**.
    Given the Case (1) trichotomy output (`Vx, Vy : Mat2` diagonalizing
    `X_eig` and `Y_eig` to `diag(d₀, d₁)`), produces the 4-gate decomposition.

    **Proof status**: PROVED via `paper_4_2_eq_7_9_chain_rewrite` +
    `paper_lemma_4_1` (iter 187 pin-down). The two upstream stubs are the
    named essentials. -/
private theorem paper_lemma_4_2_case_1_witness
    (Dg : DiagGate3)
    (W₁ W₅ U₂ U₄ Dmid : Mat4)
    (hW₁ : IsUnitary4 W₁) (hW₅ : IsUnitary4 W₅)
    (Vx Vy : Mat2) (hVx : IsUnitary2 Vx) (hVy : IsUnitary2 Vy)
    (d₀ d₁ : ℂ) (hd₀ : Complex.normSq d₀ = 1) (hd₁ : Complex.normSq d₁ = 1)
    (hX_eq : Vx.conjTranspose *
      (blockA_11 (block00 (embedAC U₂ * embedBC Dmid * embedAC U₄)) *
       (blockA_00 (block00 (embedAC U₂ * embedBC Dmid * embedAC U₄))).conjTranspose) * Vx =
      Matrix.diagonal ![d₀, d₁])
    (hY_eq : Vy.conjTranspose *
      (blockA_11 (block11 (embedAC U₂ * embedBC Dmid * embedAC U₄)) *
       (blockA_00 (block11 (embedAC U₂ * embedBC Dmid * embedAC U₄))).conjTranspose) * Vy =
      Matrix.diagonal ![d₀, d₁])
    (h_chain_factored : Dg.toMatrix =
      embedBC W₁ * (embedAC U₂ * embedBC Dmid * embedAC U₄) * embedBC W₅)
    (hDmid_form : Dmid =
      kron2 1 proj0 + kron2 (Matrix.diagonal ![d₀, d₁]) proj1) :
    ∃ V₁ V₂ V₃ V₄ : Mat4,
      IsUnitary4 V₁ ∧ IsUnitary4 V₂ ∧ IsUnitary4 V₃ ∧ IsUnitary4 V₄ ∧
      Dg.toMatrix = embedBC V₁ * embedAC V₂ * embedAB V₃ * embedBC V₄ := by
  obtain ⟨F₃, M, N, hF₃, hM, hN, h_chain_4_1⟩ :=
    paper_4_2_eq_7_9_chain_rewrite Dg W₁ W₅ U₂ U₄ Dmid hW₁ hW₅ Vx Vy hVx hVy
      d₀ d₁ hd₀ hd₁ hX_eq hY_eq h_chain_factored hDmid_form
  exact paper_lemma_4_1 Dg W₁ F₃ W₅ hW₁ hF₃ hW₅ M N hM hN h_chain_4_1

-- Flexible linter disabled (iter 153): `hDmid_unit` uses flexible `simp at`
-- patterns that resist `simp only` refactor (`Fin.sum` doesn't unfold; see
-- iter 147 finding). The proof body is stable; warning is noise.
set_option linter.flexible false in
set_option maxHeartbeats 800000 in
-- Heartbeat bump (iter 124): `paper_lemma_4_2`'s d₀≠d₁ branch has 3 cases
-- (Cases 1/2/3 from A.12 trichotomy) each with 16-case fin_cases form bridges;
-- the combined proof size exceeds the default heartbeat budget after Case (3)
-- closure landed (iter 124).
/-- **HP paper Lemma 4.2** (page 10). If U₃ is block-diag-B (controlled on B),
    then 5 BC-AC-BC-AC-BC gates reduce to 4 gates BC-AC-AB-BC.
    Hypothesis: `U₃ = I ⊗ |0⟩⟨0| + P ⊗ |1⟩⟨1|` (i.e., `kron2 1 proj0 + kron2 P proj1`).

    **Proof status** (post iter 218):
    - **d₀ = d₁ branch**: closed inline (special case, paper page 12 footnote).
    - **d₀ ≠ d₁ branch** via A.12 trichotomy:
      - **Case 1** (X_eig, Y_eig with mixed eigenvalues): bundled via
        `paper_lemma_4_2_case_1_witness` which depends on
        `paper_4_2_eq_7_9_chain_rewrite` (Lemma44.lean L2201 — STILL SORRY)
        + `paper_lemma_4_1` (PROVED iter 218).
      - **Cases 2, 3** (X_eig, Y_eig scalar): closed INLINE (iters 118, 124,
        ~250 lines per case via paper Eq.(10)-(11) block decomposition).
    - **Joint spectrum witness**: depends on `paper_lemma_4_2_joint_spec`
      (Lemma44.lean L2174 — STILL SORRY).

    With paper_lemma_4_1 closed (iter 218), only 2 upstream stubs block
    paper_lemma_4_2's full sorry-free closure. Both are paper-page-deep
    work (paper page 10-11 Eq.(6)-(9) algebra). -/
theorem paper_lemma_4_2 (Dg : DiagGate3)
    (U₁ U₂ U₃ U₄ U₅ : Mat4)
    (hU₁ : IsUnitary4 U₁) (_hU₂ : IsUnitary4 U₂)
    (_hU₃ : IsUnitary4 U₃) (_hU₄ : IsUnitary4 U₄)
    (_hU₅ : IsUnitary4 U₅)
    (P : Mat2) (hP : IsUnitary2 P)
    (hU₃_form : U₃ = kron2 1 proj0 + kron2 P proj1)
    (h_chain : Dg.toMatrix =
      embedBC U₁ * embedAC U₂ * embedBC U₃ * embedAC U₄ * embedBC U₅) :
    ∃ V₁ V₂ V₃ V₄ : Mat4,
      IsUnitary4 V₁ ∧ IsUnitary4 V₂ ∧ IsUnitary4 V₃ ∧ IsUnitary4 V₄ ∧
      Dg.toMatrix = embedBC V₁ * embedAC V₂ * embedAB V₃ * embedBC V₄ := by
  -- **Step 1** (chain rearrangement, identical to paper_lemma_4_3 iter 8):
  -- rearrange so the middle AC-BC-AC-BC stand alone, multiplied on the left
  -- by `(embedBC U₁)†` absorbed into the RHS. The RHS is block-diag-A
  -- (BC gate times diagonal Mat8 — both block-diag-A trivially).
  set Dprime : Mat8 := embedBC (U₁.conjTranspose) * Dg.toMatrix with hDprime
  have h_chain_rearranged :
      embedAC U₂ * embedBC U₃ * embedAC U₄ * embedBC U₅ = Dprime := by
    have h1 : embedBC (U₁.conjTranspose) * embedBC U₁ = 1 := by
      rw [embedBC_mul, hU₁, embedBC_one]
    calc embedAC U₂ * embedBC U₃ * embedAC U₄ * embedBC U₅
        = 1 * (embedAC U₂ * embedBC U₃ * embedAC U₄ * embedBC U₅) := by rw [one_mul]
      _ = embedBC (U₁.conjTranspose) * embedBC U₁ *
          (embedAC U₂ * embedBC U₃ * embedAC U₄ * embedBC U₅) := by rw [h1]
      _ = embedBC (U₁.conjTranspose) *
          (embedBC U₁ * embedAC U₂ * embedBC U₃ * embedAC U₄ * embedBC U₅) := by
            noncomm_ring
      _ = embedBC (U₁.conjTranspose) * Dg.toMatrix := by rw [← h_chain]
      _ = Dprime := rfl
  have hDg_isDiag8 : IsDiag8 Dg.toMatrix := ⟨Dg, rfl⟩
  have h_Dprime_block01 : block01 Dprime = 0 := by
    rw [hDprime, block01_mul, block01_embedBC, isDiag8_block01 _ hDg_isDiag8]
    simp
  have h_Dprime_block10 : block10 Dprime = 0 := by
    rw [hDprime, block10_mul, block10_embedBC, isDiag8_block10 _ hDg_isDiag8]
    simp
  -- **Step 2** (paper Lemma A.5 spectral decomposition of U₃):
  -- Apply `blockDiagB_spectral P hP` to get V (eigenvector unitary) and
  -- d₀, d₁ (eigenvalues, derived to be unit-modulus via P unitary in A.3),
  -- such that `U₃ = (kron2 V 1) · (kron2 1 proj0 + kron2 (Diag(d₀,d₁)) proj1) · (kron2 V† 1)`.
  obtain ⟨V, d₀, d₁, hV, hd₀, hd₁, hU₃_spectral⟩ := blockDiagB_spectral P hP
  have hU₃_eq : U₃ =
      (kron2 V 1) *
        (kron2 1 proj0 + kron2 (Matrix.diagonal ![d₀, d₁]) proj1) *
        (kron2 V.conjTranspose 1) := by
    rw [hU₃_form]; exact hU₃_spectral
  -- **Step 3** (paper Lemma A.7 absorption):
  -- Substitute hU₃_eq into the chain, then use `embedAC_commutes_B_only`
  -- (iter-22 helper) to move the spectral V/V† factors past adjacent
  -- embedAC gates, and absorb them into U₁, U₅ via embedBC_mul.
  set W₁ : Mat4 := U₁ * (kron2 V 1) with hW₁_def
  set W₅ : Mat4 := (kron2 V.conjTranspose 1) * U₅ with hW₅_def
  set Dmid : Mat4 :=
    kron2 1 proj0 + kron2 (Matrix.diagonal ![d₀, d₁]) proj1 with hDmid_def
  have h_chain_absorbed : Dg.toMatrix =
      embedBC W₁ * embedAC U₂ * embedBC Dmid * embedAC U₄ * embedBC W₅ := by
    calc Dg.toMatrix
        = embedBC U₁ * embedAC U₂ * embedBC U₃ * embedAC U₄ * embedBC U₅ := h_chain
      _ = embedBC U₁ * embedAC U₂ *
            embedBC ((kron2 V 1) * Dmid * (kron2 V.conjTranspose 1)) *
            embedAC U₄ * embedBC U₅ := by rw [hU₃_eq]
      _ = embedBC U₁ * embedAC U₂ *
            (embedBC (kron2 V 1) * embedBC Dmid * embedBC (kron2 V.conjTranspose 1)) *
            embedAC U₄ * embedBC U₅ := by rw [← embedBC_mul, ← embedBC_mul]
      _ = embedBC U₁ * (embedAC U₂ * embedBC (kron2 V 1)) *
            embedBC Dmid *
            (embedBC (kron2 V.conjTranspose 1) * embedAC U₄) * embedBC U₅ := by
          noncomm_ring
      _ = embedBC U₁ * (embedBC (kron2 V 1) * embedAC U₂) *
            embedBC Dmid *
            (embedAC U₄ * embedBC (kron2 V.conjTranspose 1)) * embedBC U₅ := by
          rw [embedAC_commutes_B_only U₂ V,
              ← embedAC_commutes_B_only U₄ V.conjTranspose]
      _ = (embedBC U₁ * embedBC (kron2 V 1)) * embedAC U₂ *
            embedBC Dmid * embedAC U₄ *
            (embedBC (kron2 V.conjTranspose 1) * embedBC U₅) := by noncomm_ring
      _ = embedBC W₁ * embedAC U₂ * embedBC Dmid * embedAC U₄ * embedBC W₅ := by
          rw [embedBC_mul, embedBC_mul]
  -- Dmid is a unitary Mat4 with structure `Diag(1, d₀, 1, d₁)`: useful in
  -- both branches of the upcoming case-split.
  have hDmid_unit : IsUnitary4 Dmid := by
    rw [hDmid_def, blockDiagB_kron2_eq_diagonal]
    unfold IsUnitary4
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply, Matrix.diagonal, Matrix.mul_apply,
            Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    · rw [show starRingEnd ℂ d₀ * d₀ = ((Complex.normSq d₀ : ℝ) : ℂ) from by
            rw [mul_comm]; exact Complex.mul_conj d₀]
      exact_mod_cast hd₀
    · rw [show starRingEnd ℂ d₁ * d₁ = ((Complex.normSq d₁ : ℝ) : ℂ) from by
            rw [mul_comm]; exact Complex.mul_conj d₁]
      exact_mod_cast hd₁
  -- W₁ and W₅ are unitary (shared across both case-split branches).
  have hW₁_unit : IsUnitary4 W₁ := by
    rw [hW₁_def]
    exact isUnitary4_mul hU₁ (isUnitary4_kron2 hV isUnitary2_one)
  have hW₅_unit : IsUnitary4 W₅ := by
    rw [hW₅_def]
    exact isUnitary4_mul
      (isUnitary4_kron2 (isUnitary2_conjTranspose hV) isUnitary2_one) _hU₅
  -- **Step 4** (case-split on d₀ vs d₁):
  -- The scalar sub-case (d₀ = d₁, equivalently `P = d·I`) closes WITHOUT
  -- invoking paper Lemma 4.1 — Dmid becomes a purely C-only diagonal,
  -- absorbing cleanly into embedAC factors.
  --
  -- The d₀ ≠ d₁ sub-case requires the full Lemma A.12 eigenvalue trichotomy
  -- on the matrix products `L_{01}L_{00}†` and `L_{11}L_{10}†` derived from
  -- the chain, then case dispatch via paper_lemma_4_1 (case 1) or direct
  -- construction (case 2/3).
  by_cases h_d_eq : d₀ = d₁
  · -- Case: d₀ = d₁ (scalar P case). Direct construction; no Lemma 4.1.
    subst h_d_eq
    -- Now both eigenvalues are d₀; Dmid simplifies.
    have h_diag_unit : IsUnitary2 (Matrix.diagonal ![(1 : ℂ), d₀]) :=
      isUnitary2_diag_one_u d₀ hd₀
    have h_kron_unit : IsUnitary4 (kron2 1 (Matrix.diagonal ![1, d₀])) :=
      isUnitary4_kron2 isUnitary2_one h_diag_unit
    refine ⟨U₁ * (kron2 V 1),
            U₂ * (kron2 1 (Matrix.diagonal ![1, d₀])) * U₄,
            1,
            (kron2 V.conjTranspose 1) * U₅, ?_, ?_, ?_, ?_, ?_⟩
    · -- IsUnitary4 (U₁ * (kron2 V 1)) = W₁
      exact isUnitary4_mul hU₁ (isUnitary4_kron2 hV isUnitary2_one)
    · -- IsUnitary4 (U₂ · (kron2 1 (Diag 1 d₀)) · U₄) = V₂_eff
      exact isUnitary4_mul (isUnitary4_mul _hU₂ h_kron_unit) _hU₄
    · -- IsUnitary4 1
      exact isUnitary4_one
    · -- IsUnitary4 ((kron2 V† 1) · U₅) = W₅
      exact isUnitary4_mul
        (isUnitary4_kron2 (isUnitary2_conjTranspose hV) isUnitary2_one) _hU₅
    · -- Chain factorization
      calc Dg.toMatrix
          = embedBC W₁ * embedAC U₂ * embedBC Dmid * embedAC U₄ * embedBC W₅ :=
            h_chain_absorbed
        _ = embedBC W₁ * embedAC U₂ *
              embedBC (kron2 1 (Matrix.diagonal ![1, d₀])) *
              embedAC U₄ * embedBC W₅ := by
              rw [hDmid_def, scalar_blockDiagB_eq_kron2_diag]
        _ = embedBC W₁ * embedAC U₂ *
              embedAC (kron2 1 (Matrix.diagonal ![1, d₀])) *
              embedAC U₄ * embedBC W₅ := by
              rw [embedBC_kron2_one_eq_embedAC_kron2_one]
        _ = embedBC W₁ *
              (embedAC U₂ * embedAC (kron2 1 (Matrix.diagonal ![1, d₀])) *
                embedAC U₄) * embedBC W₅ := by noncomm_ring
        _ = embedBC W₁ *
              embedAC (U₂ * (kron2 1 (Matrix.diagonal ![1, d₀])) * U₄) *
              embedBC W₅ := by rw [embedAC_mul, embedAC_mul]
        _ = embedBC W₁ *
              embedAC (U₂ * (kron2 1 (Matrix.diagonal ![1, d₀])) * U₄) *
              1 * embedBC W₅ := by rw [mul_one]
        _ = embedBC W₁ *
              embedAC (U₂ * (kron2 1 (Matrix.diagonal ![1, d₀])) * U₄) *
              embedAB 1 * embedBC W₅ := by rw [embedAB_one]
  · -- Case: d₀ ≠ d₁ (genuine Lemma A.12 trichotomy required).
    -- =====================================================================
    -- **Iter 1033 (2026-08-14): WLOG normalization `d₀ = 1`.**
    --
    -- The RAW eigenvalue pair `(d₀, d₁)` coming out of `blockDiagB_spectral`
    -- makes the paper Eq.(6) joint-spectrum claim FALSE — see
    -- `joint_spec_general_form_false`. The joint spectrum of
    -- `M_joint = C(L_01·L_00†, L_11·L_10†)` is `(1, 1, e, e)` with
    -- `e = d₁·conj d₀`: it depends only on the RATIO. (The paper avoids this
    -- because its Lemma A.5 emits determinant-one `R(α₀), R(α₁)` and then uses
    -- `R(β) = R(α₁ - α₀)`.)
    --
    -- Fix: re-factor `embedAC U₂ · embedBC Dmid` as `embedAC U₂' · embedBC Dmid'`
    -- with `U₂' = U₂ · (1 ⊗ Diag(1, d₀))` and `Dmid' = Diag(1, 1, 1, e)`,
    -- pushing the C-only phase `Diag(1, d₀)` into `U₂` via
    -- `embedBC_kron2_one_eq_embedAC_kron2_one` (`blockDiagB_diag_normalize`).
    -- `L` itself is UNCHANGED as a matrix, so every downstream block fact still
    -- holds verbatim; we simply rebind `U₂, Dmid, d₀, d₁` to the normalized
    -- data. Verified by dependency scan: nothing below this point refers to
    -- `h_d_eq`, `V`, `U₁`, `U₅`, `hU₃_*` or `hDmid_unit` — the branch consumes
    -- only `U₂, U₄, Dmid, d₀, d₁, W₁, W₅` together with `hd₀, hd₁, hDmid_def,
    -- hW₁_unit, hW₅_unit, h_chain_absorbed`, all of which are re-established
    -- below (plus the new `hd₀_one`).
    -- =====================================================================
    obtain ⟨U₂, Dmid, d₀, d₁, hU₂_unit, hd₀, hd₁, hd₀_one, hDmid_def,
            h_chain_absorbed⟩ :
        ∃ (U₂' Dmid' : Mat4) (e₀ e₁ : ℂ),
          IsUnitary4 U₂' ∧
          Complex.normSq e₀ = 1 ∧ Complex.normSq e₁ = 1 ∧ e₀ = 1 ∧
          Dmid' = kron2 1 proj0 + kron2 (Matrix.diagonal ![e₀, e₁]) proj1 ∧
          Dg.toMatrix =
            embedBC W₁ * embedAC U₂' * embedBC Dmid' * embedAC U₄ * embedBC W₅ := by
      refine ⟨U₂ * kron2 1 (Matrix.diagonal ![1, d₀]),
              kron2 1 proj0 +
                kron2 (Matrix.diagonal ![1, d₁ * starRingEnd ℂ d₀]) proj1,
              1, d₁ * starRingEnd ℂ d₀,
              isUnitary4_mul _hU₂
                (isUnitary4_kron2 isUnitary2_one (isUnitary2_diag_one_u d₀ hd₀)),
              by simp, ?_, rfl, rfl, ?_⟩
      · rw [Complex.normSq_mul, Complex.normSq_conj, hd₁, hd₀]; norm_num
      · calc Dg.toMatrix
            = embedBC W₁ * embedAC U₂ * embedBC Dmid * embedAC U₄ *
                embedBC W₅ := h_chain_absorbed
          _ = embedBC W₁ * embedAC U₂ *
                embedBC (kron2 1 (Matrix.diagonal ![1, d₀]) *
                  (kron2 1 proj0 +
                    kron2 (Matrix.diagonal ![1, d₁ * starRingEnd ℂ d₀]) proj1)) *
                embedAC U₄ * embedBC W₅ := by
                rw [hDmid_def, blockDiagB_diag_normalize d₀ d₁ hd₀]
          _ = embedBC W₁ * embedAC U₂ *
                (embedBC (kron2 1 (Matrix.diagonal ![1, d₀])) *
                  embedBC (kron2 1 proj0 +
                    kron2 (Matrix.diagonal ![1, d₁ * starRingEnd ℂ d₀]) proj1)) *
                embedAC U₄ * embedBC W₅ := by rw [embedBC_mul]
          _ = embedBC W₁ * embedAC U₂ *
                (embedAC (kron2 1 (Matrix.diagonal ![1, d₀])) *
                  embedBC (kron2 1 proj0 +
                    kron2 (Matrix.diagonal ![1, d₁ * starRingEnd ℂ d₀]) proj1)) *
                embedAC U₄ * embedBC W₅ := by
                rw [embedBC_kron2_one_eq_embedAC_kron2_one]
          _ = embedBC W₁ *
                (embedAC U₂ * embedAC (kron2 1 (Matrix.diagonal ![1, d₀]))) *
                embedBC (kron2 1 proj0 +
                  kron2 (Matrix.diagonal ![1, d₁ * starRingEnd ℂ d₀]) proj1) *
                embedAC U₄ * embedBC W₅ := by noncomm_ring
          _ = embedBC W₁ *
                embedAC (U₂ * kron2 1 (Matrix.diagonal ![1, d₀])) *
                embedBC (kron2 1 proj0 +
                  kron2 (Matrix.diagonal ![1, d₁ * starRingEnd ℂ d₀]) proj1) *
                embedAC U₄ * embedBC W₅ := by rw [embedAC_mul]
    -- Derive L = chain minus W₁/W₅ end-factors (paper's Eq.7 LHS).
    have hW₁_inv : embedBC W₁.conjTranspose * embedBC W₁ = 1 := by
      rw [embedBC_mul, hW₁_unit, embedBC_one]
    have hW₅_inv : embedBC W₅ * embedBC W₅.conjTranspose = 1 := by
      rw [embedBC_mul, mul_eq_one_comm.mp hW₅_unit, embedBC_one]
    have h_L : embedBC W₁.conjTranspose * Dg.toMatrix * embedBC W₅.conjTranspose =
               embedAC U₂ * embedBC Dmid * embedAC U₄ := by
      calc embedBC W₁.conjTranspose * Dg.toMatrix * embedBC W₅.conjTranspose
          = embedBC W₁.conjTranspose *
              (embedBC W₁ * embedAC U₂ * embedBC Dmid * embedAC U₄ * embedBC W₅) *
              embedBC W₅.conjTranspose := by rw [← h_chain_absorbed]
        _ = (embedBC W₁.conjTranspose * embedBC W₁) *
              (embedAC U₂ * embedBC Dmid * embedAC U₄) *
              (embedBC W₅ * embedBC W₅.conjTranspose) := by noncomm_ring
        _ = 1 * (embedAC U₂ * embedBC Dmid * embedAC U₄) * 1 := by
              rw [hW₁_inv, hW₅_inv]
        _ = embedAC U₂ * embedBC Dmid * embedAC U₄ := by rw [one_mul, mul_one]
    -- Derive that L is block-diag-A: from `L = BC W₁† · Dg · BC W₅†` and
    -- Dg diagonal, by `isDiag8_block01/10_embedBC`. This is paper's Lemma A.1
    -- precondition: the "L commutes with Z_A" fact rephrased.
    have hL_block01 :
        block01 (embedAC U₂ * embedBC Dmid * embedAC U₄) = 0 := by
      rw [← h_L]
      exact isDiag8_block01_embedBC W₁.conjTranspose W₅.conjTranspose
        Dg.toMatrix ⟨Dg, rfl⟩
    have hL_block10 :
        block10 (embedAC U₂ * embedBC Dmid * embedAC U₄) = 0 := by
      rw [← h_L]
      exact isDiag8_block10_embedBC W₁.conjTranspose W₅.conjTranspose
        Dg.toMatrix ⟨Dg, rfl⟩
    -- Derive that L is unitary. Approach: avoid `← h_L` rewriting (which
    -- unfolds the `set`-bound W₅) by deriving via h_L.symm composed with
    -- a fresh `have` capturing the chain-form unitarity.
    have hL_chainform_unit :
        (embedBC W₁.conjTranspose * Dg.toMatrix * embedBC W₅.conjTranspose).conjTranspose *
        (embedBC W₁.conjTranspose * Dg.toMatrix * embedBC W₅.conjTranspose) = 1 := by
      -- Product of three unitaries: BC W₁†, Dg, BC W₅†.
      have h_BCW1 : embedBC W₁ * embedBC W₁.conjTranspose = 1 := by
        rw [embedBC_mul, mul_eq_one_comm.mp hW₁_unit, embedBC_one]
      have h_BCW5 : embedBC W₅ * embedBC W₅.conjTranspose = 1 := by
        rw [embedBC_mul, mul_eq_one_comm.mp hW₅_unit, embedBC_one]
      calc (embedBC W₁.conjTranspose * Dg.toMatrix * embedBC W₅.conjTranspose).conjTranspose *
           (embedBC W₁.conjTranspose * Dg.toMatrix * embedBC W₅.conjTranspose)
          = embedBC W₅ * Dg.toMatrix.conjTranspose * embedBC W₁ *
            (embedBC W₁.conjTranspose * Dg.toMatrix * embedBC W₅.conjTranspose) := by
              simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
                         embedBC_conjTranspose]
              noncomm_ring
        _ = embedBC W₅ * Dg.toMatrix.conjTranspose *
            (embedBC W₁ * embedBC W₁.conjTranspose) *
            Dg.toMatrix * embedBC W₅.conjTranspose := by noncomm_ring
        _ = embedBC W₅ * Dg.toMatrix.conjTranspose * 1 *
            Dg.toMatrix * embedBC W₅.conjTranspose := by rw [h_BCW1]
        _ = embedBC W₅ * (Dg.toMatrix.conjTranspose * Dg.toMatrix) *
            embedBC W₅.conjTranspose := by noncomm_ring
        _ = embedBC W₅ * 1 * embedBC W₅.conjTranspose := by
              rw [Dg.toMatrix_unitary]
        _ = embedBC W₅ * embedBC W₅.conjTranspose := by rw [mul_one]
        _ = 1 := h_BCW5
    have hL_unit : (embedAC U₂ * embedBC Dmid * embedAC U₄).conjTranspose *
                   (embedAC U₂ * embedBC Dmid * embedAC U₄) = 1 := by
      rw [← h_L]; exact hL_chainform_unit
    -- Extract L's diagonal A-blocks (Mat4) and prove their unitarity.
    obtain ⟨hL_block00_unit, hL_block11_unit⟩ :=
      block_diag_A_blocks_unitary hL_unit hL_block01 hL_block10
    -- hL_block00_unit : IsUnitary4 (block00 (embedAC U₂ * embedBC Dmid * embedAC U₄))
    -- hL_block11_unit : IsUnitary4 (block11 (embedAC U₂ * embedBC Dmid * embedAC U₄))
    -- Block-decompose L's A-blocks into 2×2 sub-blocks by qubit B.
    -- Paper's L_{ab} = the 2×2 C-action when (A, B) = (a, b).
    set L_00 : Mat2 :=
      blockA_00 (block00 (embedAC U₂ * embedBC Dmid * embedAC U₄))
      with hL_00_def
    set L_01 : Mat2 :=
      blockA_11 (block00 (embedAC U₂ * embedBC Dmid * embedAC U₄))
      with hL_01_def
    set L_10 : Mat2 :=
      blockA_00 (block11 (embedAC U₂ * embedBC Dmid * embedAC U₄))
      with hL_10_def
    set L_11 : Mat2 :=
      blockA_11 (block11 (embedAC U₂ * embedBC Dmid * embedAC U₄))
      with hL_11_def
    -- Paper's "X" and "Y" — the products whose eigenvalues feed A.12.
    set X_eig : Mat2 := L_01 * L_00.conjTranspose with hX_eig_def
    set Y_eig : Mat2 := L_11 * L_10.conjTranspose with hY_eig_def
    -- Setup A.12 trichotomy invocation. Eigenvalue parameters: paper uses
    -- α₀ = e^{-iβ/2}, α₁ = e^{iβ/2} where β = arg(d₁) − arg(d₀). For now
    -- we use d₀, d₁ themselves as placeholders (will refine when A.12's
    -- joint-spectrum hypothesis is unstubbed).
    --
    -- M_joint, X_eig, Y_eig unitarity derived AFTER L sub-block unitarities
    -- (lines below) — direct path via `controlled_A_unitary` (no Eq.7 needed).
    -- L_00, L_10 unitarity (paper Lemma A.1's block-(A,B) diagonality).
    -- Lifted out of the rcases so all three cases have access.
    --
    -- Path to `blockA_10 (block?? L) = 0`: L commutes with Z_B (since each
    -- chain factor does — embedAC trivially, embedBC Dmid via Dmid·ZI = ZI·Dmid
    -- as both are diagonal Mat4). Z_B-commutation implies block-(A,B) diagonality.
    have h_AC_U₂_comm_ZB :
        embedAC U₂ * embedBC (kron2 pauliZ 1) =
        embedBC (kron2 pauliZ 1) * embedAC U₂ :=
      embedAC_commutes_B_only U₂ pauliZ
    have h_AC_U₄_comm_ZB :
        embedAC U₄ * embedBC (kron2 pauliZ 1) =
        embedBC (kron2 pauliZ 1) * embedAC U₄ :=
      embedAC_commutes_B_only U₄ pauliZ
    -- Dmid · ZI = ZI · Dmid (Mat4 commutation: both are diagonal).
    have h_Dmid_comm_ZI : Dmid * kron2 pauliZ 1 = kron2 pauliZ 1 * Dmid := by
      rw [hDmid_def]
      simp only [add_mul, mul_add, kron2_mul, one_mul, mul_one]
      congr 2
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [pauliZ, Matrix.mul_apply,
              Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
              Matrix.diagonal_apply]
    -- Lift to Mat8: embedBC Dmid commutes with embedBC ZI (= Z_B).
    have h_BC_Dmid_comm_ZB :
        embedBC Dmid * embedBC (kron2 pauliZ 1) =
        embedBC (kron2 pauliZ 1) * embedBC Dmid := by
      rw [embedBC_mul, embedBC_mul, h_Dmid_comm_ZI]
    -- Combine: L = AC U₂ · BC Dmid · AC U₄ commutes with Z_B.
    have h_L_comm_ZB :
        (embedAC U₂ * embedBC Dmid * embedAC U₄) * embedBC (kron2 pauliZ 1) =
        embedBC (kron2 pauliZ 1) * (embedAC U₂ * embedBC Dmid * embedAC U₄) := by
      calc (embedAC U₂ * embedBC Dmid * embedAC U₄) * embedBC (kron2 pauliZ 1)
          = embedAC U₂ * embedBC Dmid *
              (embedAC U₄ * embedBC (kron2 pauliZ 1)) := by noncomm_ring
        _ = embedAC U₂ * embedBC Dmid *
              (embedBC (kron2 pauliZ 1) * embedAC U₄) := by
            rw [h_AC_U₄_comm_ZB]
        _ = embedAC U₂ * (embedBC Dmid * embedBC (kron2 pauliZ 1)) *
              embedAC U₄ := by noncomm_ring
        _ = embedAC U₂ * (embedBC (kron2 pauliZ 1) * embedBC Dmid) *
              embedAC U₄ := by rw [h_BC_Dmid_comm_ZB]
        _ = (embedAC U₂ * embedBC (kron2 pauliZ 1)) * embedBC Dmid *
              embedAC U₄ := by noncomm_ring
        _ = (embedBC (kron2 pauliZ 1) * embedAC U₂) * embedBC Dmid *
              embedAC U₄ := by rw [h_AC_U₂_comm_ZB]
        _ = embedBC (kron2 pauliZ 1) *
              (embedAC U₂ * embedBC Dmid * embedAC U₄) := by noncomm_ring
    -- Derive `block00 L` commutes with ZI (Mat4), via block00 of h_L_comm_ZB.
    have h_block00_L_comm_ZI :
        block00 (embedAC U₂ * embedBC Dmid * embedAC U₄) * ZI =
        ZI * block00 (embedAC U₂ * embedBC Dmid * embedAC U₄) := by
      have h := congrArg block00 h_L_comm_ZB
      rw [block00_mul_of_block01_zero _ _ hL_block01,
          block00_mul_of_block01_zero _ _ (block01_embedBC _),
          block00_embedBC] at h
      exact h
    have h_block00_L_bdf :
        IsBlockDiagFirst (block00 (embedAC U₂ * embedBC Dmid * embedAC U₄)) :=
      commutes_ZI_implies_blockDiagFirst _ h_block00_L_comm_ZI
    have hBlockA_10_block00_L_zero :
        blockA_10 (block00 (embedAC U₂ * embedBC Dmid * embedAC U₄)) = 0 := by
      obtain ⟨P₀, P₁, h_eq⟩ := h_block00_L_bdf
      rw [h_eq]
      exact (blockA_of_controlled P₀ P₁).2.2.1
    have hL_00_unit : IsUnitary2 L_00 :=
      blockA_00_unitary_of_blockA_10_zero hL_block00_unit hBlockA_10_block00_L_zero
    -- Symmetric: block11 L commutes with ZI, hence block-diag-first.
    have h_block11_L_comm_ZI :
        block11 (embedAC U₂ * embedBC Dmid * embedAC U₄) * ZI =
        ZI * block11 (embedAC U₂ * embedBC Dmid * embedAC U₄) := by
      have h := congrArg block11 h_L_comm_ZB
      rw [block11_mul_of_block10_zero _ _ hL_block10,
          block11_mul_of_block10_zero _ _ (block10_embedBC _),
          block11_embedBC] at h
      exact h
    have h_block11_L_bdf :
        IsBlockDiagFirst (block11 (embedAC U₂ * embedBC Dmid * embedAC U₄)) :=
      commutes_ZI_implies_blockDiagFirst _ h_block11_L_comm_ZI
    have hBlockA_10_block11_L_zero :
        blockA_10 (block11 (embedAC U₂ * embedBC Dmid * embedAC U₄)) = 0 := by
      obtain ⟨P₀, P₁, h_eq⟩ := h_block11_L_bdf
      rw [h_eq]
      exact (blockA_of_controlled P₀ P₁).2.2.1
    have hL_10_unit : IsUnitary2 L_10 :=
      blockA_00_unitary_of_blockA_10_zero hL_block11_unit hBlockA_10_block11_L_zero
    -- L_01, L_11 (the blockA_11 sub-blocks) are also unitary, by the analogous
    -- PY24 helper. This breaks the circular dependency: hM_joint_unit can now
    -- be derived from L_00, L_01, L_10, L_11 unitarity directly.
    have hL_01_unit : IsUnitary2 L_01 :=
      blockA_11_unitary_of_blockA_10_zero hL_block00_unit hBlockA_10_block00_L_zero
    have hL_11_unit : IsUnitary2 L_11 :=
      blockA_11_unitary_of_blockA_10_zero hL_block11_unit hBlockA_10_block11_L_zero
    -- Structural facts: `block00 L` and `block11 L` factor as
    -- `kron2 proj0 (top-left) + kron2 proj1 (bottom-right)` (block-diag-first
    -- via `commutes_ZI_implies_blockDiagFirst`).
    have h_block00_L_struct :
        block00 (embedAC U₂ * embedBC Dmid * embedAC U₄) =
        kron2 proj0 L_00 + kron2 proj1 L_01 := by
      obtain ⟨P₀, P₁, h_eq⟩ := h_block00_L_bdf
      have hP₀ : P₀ = L_00 := by
        have h : blockA_00 (block00 (embedAC U₂ * embedBC Dmid * embedAC U₄)) = P₀ := by
          rw [h_eq, (blockA_of_controlled P₀ P₁).1]
        exact h.symm
      have hP₁ : P₁ = L_01 := by
        have h : blockA_11 (block00 (embedAC U₂ * embedBC Dmid * embedAC U₄)) = P₁ := by
          rw [h_eq, (blockA_of_controlled P₀ P₁).2.2.2]
        exact h.symm
      rw [h_eq, hP₀, hP₁]
    have h_block11_L_struct :
        block11 (embedAC U₂ * embedBC Dmid * embedAC U₄) =
        kron2 proj0 L_10 + kron2 proj1 L_11 := by
      obtain ⟨P₀, P₁, h_eq⟩ := h_block11_L_bdf
      have hP₀ : P₀ = L_10 := by
        have h : blockA_00 (block11 (embedAC U₂ * embedBC Dmid * embedAC U₄)) = P₀ := by
          rw [h_eq, (blockA_of_controlled P₀ P₁).1]
        exact h.symm
      have hP₁ : P₁ = L_11 := by
        have h : blockA_11 (block11 (embedAC U₂ * embedBC Dmid * embedAC U₄)) = P₁ := by
          rw [h_eq, (blockA_of_controlled P₀ P₁).2.2.2]
        exact h.symm
      rw [h_eq, hP₀, hP₁]
    -- Factored chain: Dg.toMatrix = embedBC W₁ · L · embedBC W₅ (regrouping of
    -- h_chain_absorbed). Useful for upcoming chain manipulations.
    have h_chain_factored :
        Dg.toMatrix =
        embedBC W₁ * (embedAC U₂ * embedBC Dmid * embedAC U₄) * embedBC W₅ := by
      rw [h_chain_absorbed]; noncomm_ring
    -- 🎯 Direct path to M_joint unitarity: X_eig, Y_eig are products of
    -- unitaries (L_01 · L_00†, L_11 · L_10†) hence unitary; M_joint =
    -- controlled-A with X_eig, Y_eig hence unitary by `controlled_A_unitary`.
    set M_joint : Mat4 := kron2 proj0 X_eig + kron2 proj1 Y_eig with hM_joint_def
    have hM_joint_blockA_10 : blockA_10 M_joint = 0 :=
      (blockA_of_controlled X_eig Y_eig).2.2.1
    have hX_eig_unit : IsUnitary2 X_eig :=
      isUnitary2_mul hL_01_unit (isUnitary2_conjTranspose hL_00_unit)
    have hY_eig_unit : IsUnitary2 Y_eig :=
      isUnitary2_mul hL_11_unit (isUnitary2_conjTranspose hL_10_unit)
    have hM_joint_unit : IsUnitary4 M_joint :=
      controlled_A_unitary hX_eig_unit hY_eig_unit
    -- Joint-spectrum witness for `joint_spec_multiplicity_trichotomy`
    -- (iter-134 refactor, renamed iter 187). Paper page 10, Eq.(6).
    -- Iter 1034: `paper_lemma_4_2_joint_spec` is now PROVED (no longer a stub).
    -- It consumes the `hd₀_one : d₀ = 1` normalization established above —
    -- without it the claim is false (`joint_spec_general_form_false`).
    have h_joint_spec_witness :
        ∃ W : Mat4, IsUnitary4 W ∧
          W.conjTranspose * (kron2 proj0 X_eig + kron2 proj1 Y_eig) * W =
            Matrix.diagonal ![d₀, d₀, d₁, d₁] :=
      paper_lemma_4_2_joint_spec Dg W₁ W₅ U₂ U₄ Dmid hW₁_unit hW₅_unit
        hU₂_unit _hU₄ X_eig Y_eig hX_eig_unit hY_eig_unit d₀ d₁ hd₀ hd₁ hd₀_one
        h_chain_factored hDmid_def hX_eig_def hY_eig_def
    rcases joint_spec_multiplicity_trichotomy X_eig Y_eig hX_eig_unit hY_eig_unit
        d₀ d₁ hd₀ hd₁ h_joint_spec_witness
      with ⟨_Vx, _Vy, _hVx, _hVy, _hX_eq, _hY_eq⟩
        | ⟨hX_scalar, hY_scalar⟩
        | ⟨hX_swap, hY_swap⟩
    · -- Case (1): X_eig and Y_eig similar to Diag(d₀, d₁) — mixed eigenvalues.
      -- Iter 186: closed via `paper_lemma_4_2_case_1_witness` essential stub
      -- (which bundles paper page 11 Eq.7-9 + Lemma A.2 + `paper_lemma_4_1`
      -- invocation). Cases (2) and (3) closed inline (iters 118, 124).
      exact paper_lemma_4_2_case_1_witness Dg W₁ W₅ U₂ U₄ Dmid
        hW₁_unit hW₅_unit _Vx _Vy _hVx _hVy d₀ d₁ hd₀ hd₁
        _hX_eq _hY_eq h_chain_factored hDmid_def
    · -- Case (2): X_eig = d₀·I, Y_eig = d₁·I (scalar eigenvalues).
      -- Unfold X_eig, Y_eig defs to get explicit equations on L_{ab} sub-blocks.
      have hL_01_L_00_dag : L_01 * L_00.conjTranspose = Matrix.diagonal ![d₀, d₀] := by
        rw [← hX_eig_def]; exact hX_scalar
      have hL_11_L_10_dag : L_11 * L_10.conjTranspose = Matrix.diagonal ![d₁, d₁] := by
        rw [← hY_eig_def]; exact hY_scalar
      -- Define β_phase := d₁ · conj(d₀) = e^{iβ} (paper's phase parameter).
      let β_phase : ℂ := d₁ * starRingEnd ℂ d₀
      have hβ_phase : Complex.normSq β_phase = 1 := by
        change Complex.normSq (d₁ * starRingEnd ℂ d₀) = 1
        rw [Complex.normSq_mul, Complex.normSq_conj, hd₁, hd₀]
        norm_num
      -- Paper's V₂ = C(L_10·L_00†). Now `L_10, L_00` unconditionally unitary
      -- (iters 61-65), so V₂'s unitarity is concrete.
      let V₂_eff : Mat4 := kron2 proj0 1 + kron2 proj1 (L_10 * L_00.conjTranspose)
      have hV₂_eff_unit : IsUnitary4 V₂_eff :=
        controlled_A_unitary isUnitary2_one
          (isUnitary2_mul hL_10_unit (isUnitary2_conjTranspose hL_00_unit))
      -- Paper's V₃ = C(P(β)) = `kron2 proj0 1 + kron2 proj1 (P_phase β_phase)`.
      let V₃_eff : Mat4 := kron2 proj0 1 + kron2 proj1 (P_phase β_phase)
      have hV₃_eff_unit : IsUnitary4 V₃_eff :=
        controlled_A_unitary isUnitary2_one (P_phase_unitary hβ_phase)
      -- L_00, L_10 unitarity available from before the rcases (paper Lemma A.1).
      -- Derive `L_01 = Diag(d₀, d₀) · L_00` from `L_01 · L_00† = Diag(d₀, d₀)`
      -- + L_00 unitary (multiply on right by L_00).
      have hL_01_eq : L_01 = Matrix.diagonal ![d₀, d₀] * L_00 := by
        have h : L_01 * L_00.conjTranspose * L_00 =
                 Matrix.diagonal ![d₀, d₀] * L_00 := by
          rw [hL_01_L_00_dag]
        rw [mul_assoc, hL_00_unit, mul_one] at h
        exact h
      have hL_11_eq : L_11 = Matrix.diagonal ![d₁, d₁] * L_10 := by
        have h : L_11 * L_10.conjTranspose * L_10 =
                 Matrix.diagonal ![d₁, d₁] * L_10 := by
          rw [hL_11_L_10_dag]
        rw [mul_assoc, hL_10_unit, mul_one] at h
        exact h
      -- Paper Eq.(10) sub-step: `block00 L` written explicitly in Case (2)
      -- using `hL_01_eq` substituted into `h_block00_L_struct`.
      have h_block00_L_Case2_eq :
          block00 (embedAC U₂ * embedBC Dmid * embedAC U₄) =
          kron2 proj0 L_00 + kron2 proj1 (Matrix.diagonal ![d₀, d₀] * L_00) := by
        rw [h_block00_L_struct, hL_01_eq]
      -- Symmetric Eq.(10) sub-step for `block11 L` in Case (2), via `hL_11_eq`.
      have h_block11_L_Case2_eq :
          block11 (embedAC U₂ * embedBC Dmid * embedAC U₄) =
          kron2 proj0 L_10 + kron2 proj1 (Matrix.diagonal ![d₁, d₁] * L_10) := by
        rw [h_block11_L_struct, hL_11_eq]
      -- Paper Eq.(10): full L-form using `Mat8.ofBlockDiag` reconstruction
      -- (iter 105 infrastructure) + iter-97/98 block-form facts + L's off-diagonal
      -- zero-blocks. This is paper page 11's Eq.(10) content in Lean form.
      have h_L_Case2_eq :
          embedAC U₂ * embedBC Dmid * embedAC U₄ =
          Mat8.ofBlockDiag
            (kron2 proj0 L_00 + kron2 proj1 (Matrix.diagonal ![d₀, d₀] * L_00))
            (kron2 proj0 L_10 + kron2 proj1 (Matrix.diagonal ![d₁, d₁] * L_10)) := by
        apply mat8_eq_of_blocks_off_diag_zero
        · rw [h_block00_L_Case2_eq, block00_ofBlockDiag]
        · rw [h_block11_L_Case2_eq, block11_ofBlockDiag]
        · exact hL_block01
        · exact hL_block10
        · exact block01_ofBlockDiag _ _
        · exact block10_ofBlockDiag _ _
      -- Paper Eq.(11) preparation: the 3-factor RHS
      -- `embedAC V₂_eff · embedAB V₃_eff · embedBC (kron2 (P_phase d₀) L_00)`
      -- is itself block-diag-A. Both off-diagonal blocks are zero by chained
      -- application of `block??_mul_of_both_zero` over the three block-diag-A
      -- factors (each is controlled or pure-BC).
      have h_RHS_block01 :
          block01 (embedAC V₂_eff * embedAB V₃_eff *
                   embedBC (kron2 (P_phase d₀) L_00)) = 0 := by
        apply block01_mul_of_both_zero
        · apply block01_mul_of_both_zero
          · exact block01_embedAC_of_controlled 1 (L_10 * L_00.conjTranspose)
          · rw [block01_embedAB,
                (blockA_of_controlled 1 (P_phase β_phase)).2.1, kron2_zero_left]
        · exact block01_embedBC _
      have h_RHS_block10 :
          block10 (embedAC V₂_eff * embedAB V₃_eff *
                   embedBC (kron2 (P_phase d₀) L_00)) = 0 := by
        apply block10_mul_of_both_zero
        · apply block10_mul_of_both_zero
          · exact block10_embedAC_of_controlled 1 (L_10 * L_00.conjTranspose)
          · rw [block10_embedAB,
                (blockA_of_controlled 1 (P_phase β_phase)).2.2.1, kron2_zero_left]
        · exact block10_embedBC _
      -- block00 of the 3-factor RHS = `kron2 (P_phase d₀) L_00`. Each factor
      -- contributes `block00 = identity` except the rightmost (pure BC) which
      -- contributes the inner Mat4 directly.
      have h_block01_AC_AB_zero :
          block01 (embedAC V₂_eff * embedAB V₃_eff) = 0 := by
        apply block01_mul_of_both_zero
        · exact block01_embedAC_of_controlled 1 (L_10 * L_00.conjTranspose)
        · rw [block01_embedAB,
              (blockA_of_controlled 1 (P_phase β_phase)).2.1, kron2_zero_left]
      have h_block01_AC_zero :
          block01 (embedAC V₂_eff) = 0 :=
        block01_embedAC_of_controlled 1 (L_10 * L_00.conjTranspose)
      have h_RHS_block00 :
          block00 (embedAC V₂_eff * embedAB V₃_eff *
                   embedBC (kron2 (P_phase d₀) L_00)) =
          kron2 (P_phase d₀) L_00 := by
        rw [block00_mul_of_block01_zero _ _ h_block01_AC_AB_zero,
            block00_mul_of_block01_zero _ _ h_block01_AC_zero,
            block00_embedAC_of_controlled,
            block00_embedAB, (blockA_of_controlled 1 (P_phase β_phase)).1,
            block00_embedBC, kron2_one_one_eq_one, Matrix.one_mul]
        change kron2 (1 : Mat2) (I₂ : Mat2) * kron2 (P_phase d₀) L_00 =
               kron2 (P_phase d₀) L_00
        rw [show (I₂ : Mat2) = 1 from rfl, kron2_one_one_eq_one, Matrix.one_mul]
      -- Symmetric for block11: block10's-zero analog of the iter-110 chain.
      have h_block10_AC_AB_zero :
          block10 (embedAC V₂_eff * embedAB V₃_eff) = 0 := by
        apply block10_mul_of_both_zero
        · exact block10_embedAC_of_controlled 1 (L_10 * L_00.conjTranspose)
        · rw [block10_embedAB,
              (blockA_of_controlled 1 (P_phase β_phase)).2.2.1, kron2_zero_left]
      have h_block10_AC_zero :
          block10 (embedAC V₂_eff) = 0 :=
        block10_embedAC_of_controlled 1 (L_10 * L_00.conjTranspose)
      -- block11 of the 3-factor RHS, in the unsimplified product form. The
      -- "clean" form `kron2 (P_phase d₁) L_10` follows by further algebra
      -- (P_phase product law + |d₀|²=1 + L_00 unitarity); deferred to iter 112.
      have h_RHS_block11 :
          block11 (embedAC V₂_eff * embedAB V₃_eff *
                   embedBC (kron2 (P_phase d₀) L_00)) =
          kron2 (1 : Mat2) (L_10 * L_00.conjTranspose) *
          kron2 (P_phase β_phase) (I₂ : Mat2) *
          kron2 (P_phase d₀) L_00 := by
        rw [block11_mul_of_block10_zero _ _ h_block10_AC_AB_zero,
            block11_mul_of_block10_zero _ _ h_block10_AC_zero,
            block11_embedAC_of_controlled,
            block11_embedAB, (blockA_of_controlled 1 (P_phase β_phase)).2.2.2,
            block11_embedBC]
      -- Bridge between the Case (2) block-form (iters 97-98) and the RHS
      -- block00 form (iter 110). Pure Mat4 identity:
      --   proj0 ⊗ L_00 + proj1 ⊗ (Diag(d₀,d₀)·L_00) = (P_phase d₀) ⊗ L_00.
      -- Since P_phase d₀ = Diag(1, d₀) = proj0 + d₀·proj1 and
      -- Diag(d₀,d₀)·L_00 = d₀·L_00.
      have h_block00_form_bridge :
          kron2 proj0 L_00 + kron2 proj1 (Matrix.diagonal ![d₀, d₀] * L_00) =
          kron2 (P_phase d₀) L_00 := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [kron2, proj0, proj1, P_phase, Matrix.diagonal,
                Matrix.mul_apply, Matrix.of_apply, Matrix.add_apply,
                Matrix.cons_val_zero, Matrix.cons_val_one]
      -- Arithmetic helper: β_phase * d₀ = d₁ via |d₀|² = 1.
      -- β_phase = d₁ · conj(d₀) (paper's e^{iβ} = d₁/d₀ when |d₀|=|d₁|=1).
      have h_β_phase_mul_d₀ : β_phase * d₀ = d₁ := by
        change d₁ * starRingEnd ℂ d₀ * d₀ = d₁
        rw [mul_assoc, mul_comm (starRingEnd ℂ d₀) d₀, Complex.mul_conj, hd₀]
        push_cast; ring
      -- Simplified form of h_RHS_block11: collapse the kron2 product chain
      -- via P_phase_mul + L_00 unitarity + β_phase·d₀ = d₁.
      have h_RHS_block11_clean :
          block11 (embedAC V₂_eff * embedAB V₃_eff *
                   embedBC (kron2 (P_phase d₀) L_00)) =
          kron2 (P_phase d₁) L_10 := by
        rw [h_RHS_block11, show (I₂ : Mat2) = 1 from rfl,
            kron2_mul, kron2_mul, one_mul, mul_one, P_phase_mul,
            h_β_phase_mul_d₀]
        congr 1
        rw [mul_assoc, hL_00_unit, mul_one]
      -- Block11 form bridge, symmetric to iter-112's `h_block00_form_bridge`.
      have h_block11_form_bridge :
          kron2 proj0 L_10 + kron2 proj1 (Matrix.diagonal ![d₁, d₁] * L_10) =
          kron2 (P_phase d₁) L_10 := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [kron2, proj0, proj1, P_phase, Matrix.diagonal,
                Matrix.mul_apply, Matrix.of_apply, Matrix.add_apply,
                Matrix.cons_val_zero, Matrix.cons_val_one]
      -- Paper Eq.(11) full assembly: L = (3-factor RHS). Uses
      -- `mat8_eq_of_blocks_off_diag_zero` with both block-equalities
      -- bridged + iter-109's off-diagonal-zero facts on both sides.
      have h_Eq_11_Case2 :
          embedAC U₂ * embedBC Dmid * embedAC U₄ =
          embedAC V₂_eff * embedAB V₃_eff *
            embedBC (kron2 (P_phase d₀) L_00) := by
        apply mat8_eq_of_blocks_off_diag_zero
        · rw [h_block00_L_Case2_eq, h_RHS_block00]
          exact h_block00_form_bridge
        · rw [h_block11_L_Case2_eq, h_RHS_block11_clean]
          exact h_block11_form_bridge
        · exact hL_block01
        · exact hL_block10
        · exact h_RHS_block01
        · exact h_RHS_block10
      -- Paper's V₄ = (P(-β/2) ⊗ L_00) · W₅. In our parametrization, paper's
      -- `e^{-iβ/2}` corresponds to our `d₀` (the X_eig eigenvalue in case (2)),
      -- so `P(-β/2) = P_phase d₀` (no sqrt machinery needed). Then V₄ = kron2
      -- (P_phase d₀) L_00 · W₅, a product of unitaries.
      let V₄_eff : Mat4 := kron2 (P_phase d₀) L_00 * W₅
      have h_kron2_PL_unit : IsUnitary4 (kron2 (P_phase d₀) L_00) :=
        isUnitary4_kron2 (P_phase_unitary hd₀) hL_00_unit
      have hV₄_eff_unit : IsUnitary4 V₄_eff :=
        isUnitary4_mul h_kron2_PL_unit hW₅_unit
      -- Useful factorization: embedBC V₄_eff = embedBC (kron2 (P_phase d₀) L_00)
      -- * embedBC W₅. Splits V₄'s embed into the controlled-phase + L_00 part
      -- (which appears in paper's recipe) and the W₅ tail (which cancels in
      -- the chain identity).
      have h_BC_V₄_eff_factored :
          embedBC V₄_eff =
          embedBC (kron2 (P_phase d₀) L_00) * embedBC W₅ := by
        change embedBC (kron2 (P_phase d₀) L_00 * W₅) = _
        rw [← embedBC_mul]
      -- Chain factorization target, regrouped with W₅ moved to right:
      --   `BC W₁ · AC V₂_eff · AB V₃_eff · BC V₄_eff`
      -- = `BC W₁ · (AC V₂_eff · AB V₃_eff · BC (kron2 P_phase·L_00)) · BC W₅`
      -- The middle parenthesized factor equals L (= AC U₂ · BC Dmid · AC U₄)
      -- by paper Eq.7-derived identity. This rearrangement is a noncomm_ring.
      have h_chain_target_rearranged :
          embedBC W₁ * embedAC V₂_eff * embedAB V₃_eff * embedBC V₄_eff =
          embedBC W₁ *
            (embedAC V₂_eff * embedAB V₃_eff *
              embedBC (kron2 (P_phase d₀) L_00)) *
            embedBC W₅ := by
        rw [h_BC_V₄_eff_factored]; noncomm_ring
      -- Refine existential with V₁ = W₁, V₂ = V₂_eff, V₃ = V₃_eff, V₄ = V₄_eff.
      -- Remaining goal: chain factorization (paper page 11 algebra).
      -- The chain identity (modulo cancellation of BC W₁ on left, BC W₅ on right):
      --   `embedAC U₂ * embedBC Dmid * embedAC U₄ = embedAC V₂_eff * embedAB V₃_eff *
      --    embedBC (kron2 (P_phase d₀) L_00)`
      -- This is paper page 11's specific factorization, derived from L's structure
      -- (Eq.7+8 in the paper) combined with case (2)'s eigenvalue constraints.
      -- Requires the Eq.7-derived form of L which we haven't fully formalized.
      refine ⟨W₁, V₂_eff, V₃_eff, V₄_eff,
              hW₁_unit, hV₂_eff_unit, hV₃_eff_unit, hV₄_eff_unit, ?_⟩
      -- Final closure: chain `h_chain_target_rearranged` (regroup with W₅
      -- to right) + reverse `h_Eq_11_Case2` (paper Eq.(11): inner 3-factor
      -- = L) + `h_chain_factored` (Dg = BC W₁ · L · BC W₅).
      rw [h_chain_target_rearranged, ← h_Eq_11_Case2]
      exact h_chain_factored
    · -- Case (3): X_eig = d₁·I, Y_eig = d₀·I (symmetric scalar case).
      -- Mirror of Case (2) with d₀, d₁ swapped throughout.
      have hL_01_L_00_dag : L_01 * L_00.conjTranspose = Matrix.diagonal ![d₁, d₁] := by
        rw [← hX_eig_def]; exact hX_swap
      have hL_11_L_10_dag : L_11 * L_10.conjTranspose = Matrix.diagonal ![d₀, d₀] := by
        rw [← hY_eig_def]; exact hY_swap
      -- Mirror of iter-32's `hL_01_eq` for Case (3): multiply both sides
      -- by L_00 on the right and use L_00 unitarity.
      have hL_01_eq' : L_01 = Matrix.diagonal ![d₁, d₁] * L_00 := by
        have h : L_01 * L_00.conjTranspose * L_00 =
                 Matrix.diagonal ![d₁, d₁] * L_00 := by
          rw [hL_01_L_00_dag]
        rw [mul_assoc, hL_00_unit, mul_one] at h
        exact h
      have hL_11_eq' : L_11 = Matrix.diagonal ![d₀, d₀] * L_10 := by
        have h : L_11 * L_10.conjTranspose * L_10 =
                 Matrix.diagonal ![d₀, d₀] * L_10 := by
          rw [hL_11_L_10_dag]
        rw [mul_assoc, hL_10_unit, mul_one] at h
        exact h
      -- Mirror of iter-97/98 block-form facts for Case (3).
      have h_block00_L_Case3_eq :
          block00 (embedAC U₂ * embedBC Dmid * embedAC U₄) =
          kron2 proj0 L_00 + kron2 proj1 (Matrix.diagonal ![d₁, d₁] * L_00) := by
        rw [h_block00_L_struct, hL_01_eq']
      have h_block11_L_Case3_eq :
          block11 (embedAC U₂ * embedBC Dmid * embedAC U₄) =
          kron2 proj0 L_10 + kron2 proj1 (Matrix.diagonal ![d₀, d₀] * L_10) := by
        rw [h_block11_L_struct, hL_11_eq']
      -- Mirror of iter-106's `h_L_Case2_eq`: full L-form for Case (3).
      have h_L_Case3_eq :
          embedAC U₂ * embedBC Dmid * embedAC U₄ =
          Mat8.ofBlockDiag
            (kron2 proj0 L_00 + kron2 proj1 (Matrix.diagonal ![d₁, d₁] * L_00))
            (kron2 proj0 L_10 + kron2 proj1 (Matrix.diagonal ![d₀, d₀] * L_10)) := by
        apply mat8_eq_of_blocks_off_diag_zero
        · rw [h_block00_L_Case3_eq, block00_ofBlockDiag]
        · rw [h_block11_L_Case3_eq, block11_ofBlockDiag]
        · exact hL_block01
        · exact hL_block10
        · exact block01_ofBlockDiag _ _
        · exact block10_ofBlockDiag _ _
      let β_phase' : ℂ := d₀ * starRingEnd ℂ d₁
      have hβ_phase' : Complex.normSq β_phase' = 1 := by
        change Complex.normSq (d₀ * starRingEnd ℂ d₁) = 1
        rw [Complex.normSq_mul, Complex.normSq_conj, hd₀, hd₁]
        norm_num
      let V₂_eff' : Mat4 := kron2 proj0 1 + kron2 proj1 (L_10 * L_00.conjTranspose)
      have hV₂_eff'_unit : IsUnitary4 V₂_eff' :=
        controlled_A_unitary isUnitary2_one
          (isUnitary2_mul hL_10_unit (isUnitary2_conjTranspose hL_00_unit))
      let V₃_eff' : Mat4 := kron2 proj0 1 + kron2 proj1 (P_phase β_phase')
      have hV₃_eff'_unit : IsUnitary4 V₃_eff' :=
        controlled_A_unitary isUnitary2_one (P_phase_unitary hβ_phase')
      let V₄_eff' : Mat4 := kron2 (P_phase d₁) L_00 * W₅
      have h_kron2_PL_unit' : IsUnitary4 (kron2 (P_phase d₁) L_00) :=
        isUnitary4_kron2 (P_phase_unitary hd₁) hL_00_unit
      have hV₄_eff'_unit : IsUnitary4 V₄_eff' :=
        isUnitary4_mul h_kron2_PL_unit' hW₅_unit
      -- Mirror iter-109's off-diagonal-zero facts for Case (3)'s 3-factor RHS.
      have h_RHS_block01' :
          block01 (embedAC V₂_eff' * embedAB V₃_eff' *
                   embedBC (kron2 (P_phase d₁) L_00)) = 0 := by
        apply block01_mul_of_both_zero
        · apply block01_mul_of_both_zero
          · exact block01_embedAC_of_controlled 1 (L_10 * L_00.conjTranspose)
          · rw [block01_embedAB,
                (blockA_of_controlled 1 (P_phase β_phase')).2.1, kron2_zero_left]
        · exact block01_embedBC _
      have h_RHS_block10' :
          block10 (embedAC V₂_eff' * embedAB V₃_eff' *
                   embedBC (kron2 (P_phase d₁) L_00)) = 0 := by
        apply block10_mul_of_both_zero
        · apply block10_mul_of_both_zero
          · exact block10_embedAC_of_controlled 1 (L_10 * L_00.conjTranspose)
          · rw [block10_embedAB,
                (blockA_of_controlled 1 (P_phase β_phase')).2.2.1, kron2_zero_left]
        · exact block10_embedBC _
      -- Mirror iter-110: block00 of Case 3's 3-factor RHS.
      have h_block01_AC_AB_zero' :
          block01 (embedAC V₂_eff' * embedAB V₃_eff') = 0 := by
        apply block01_mul_of_both_zero
        · exact block01_embedAC_of_controlled 1 (L_10 * L_00.conjTranspose)
        · rw [block01_embedAB,
              (blockA_of_controlled 1 (P_phase β_phase')).2.1, kron2_zero_left]
      have h_block01_AC_zero' :
          block01 (embedAC V₂_eff') = 0 :=
        block01_embedAC_of_controlled 1 (L_10 * L_00.conjTranspose)
      have h_RHS_block00' :
          block00 (embedAC V₂_eff' * embedAB V₃_eff' *
                   embedBC (kron2 (P_phase d₁) L_00)) =
          kron2 (P_phase d₁) L_00 := by
        rw [block00_mul_of_block01_zero _ _ h_block01_AC_AB_zero',
            block00_mul_of_block01_zero _ _ h_block01_AC_zero',
            block00_embedAC_of_controlled,
            block00_embedAB, (blockA_of_controlled 1 (P_phase β_phase')).1,
            block00_embedBC, kron2_one_one_eq_one, Matrix.one_mul]
        change kron2 (1 : Mat2) (I₂ : Mat2) * kron2 (P_phase d₁) L_00 =
               kron2 (P_phase d₁) L_00
        rw [show (I₂ : Mat2) = 1 from rfl, kron2_one_one_eq_one, Matrix.one_mul]
      -- Mirror iter-111's block10-zero auxiliaries for Case (3).
      have h_block10_AC_AB_zero' :
          block10 (embedAC V₂_eff' * embedAB V₃_eff') = 0 := by
        apply block10_mul_of_both_zero
        · exact block10_embedAC_of_controlled 1 (L_10 * L_00.conjTranspose)
        · rw [block10_embedAB,
              (blockA_of_controlled 1 (P_phase β_phase')).2.2.1, kron2_zero_left]
      have h_block10_AC_zero' :
          block10 (embedAC V₂_eff') = 0 :=
        block10_embedAC_of_controlled 1 (L_10 * L_00.conjTranspose)
      -- Mirror iter-111: block11 of Case 3's 3-factor RHS in unsimplified form.
      have h_RHS_block11' :
          block11 (embedAC V₂_eff' * embedAB V₃_eff' *
                   embedBC (kron2 (P_phase d₁) L_00)) =
          kron2 (1 : Mat2) (L_10 * L_00.conjTranspose) *
          kron2 (P_phase β_phase') (I₂ : Mat2) *
          kron2 (P_phase d₁) L_00 := by
        rw [block11_mul_of_block10_zero _ _ h_block10_AC_AB_zero',
            block11_mul_of_block10_zero _ _ h_block10_AC_zero',
            block11_embedAC_of_controlled,
            block11_embedAB, (blockA_of_controlled 1 (P_phase β_phase')).2.2.2,
            block11_embedBC]
      -- Mirror iter-115's `h_β_phase_mul_d₀` for Case (3): β_phase' · d₁ = d₀.
      have h_β_phase'_mul_d₁ : β_phase' * d₁ = d₀ := by
        change d₀ * starRingEnd ℂ d₁ * d₁ = d₀
        rw [mul_assoc, mul_comm (starRingEnd ℂ d₁) d₁, Complex.mul_conj, hd₁]
        push_cast; ring
      -- Mirror iter-115's `h_RHS_block11_clean` for Case (3): collapse to
      -- `kron2 (P_phase d₀) L_10`.
      have h_RHS_block11_clean' :
          block11 (embedAC V₂_eff' * embedAB V₃_eff' *
                   embedBC (kron2 (P_phase d₁) L_00)) =
          kron2 (P_phase d₀) L_10 := by
        rw [h_RHS_block11', show (I₂ : Mat2) = 1 from rfl,
            kron2_mul, kron2_mul, one_mul, mul_one, P_phase_mul,
            h_β_phase'_mul_d₁]
        congr 1
        rw [mul_assoc, hL_00_unit, mul_one]
      -- Mirror iter-112's `h_block00_form_bridge` for Case (3): d₁ in place of d₀.
      have h_block00_form_bridge' :
          kron2 proj0 L_00 + kron2 proj1 (Matrix.diagonal ![d₁, d₁] * L_00) =
          kron2 (P_phase d₁) L_00 := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [kron2, proj0, proj1, P_phase, Matrix.diagonal,
                Matrix.mul_apply, Matrix.of_apply, Matrix.add_apply,
                Matrix.cons_val_zero, Matrix.cons_val_one]
      -- Mirror iter-116's `h_block11_form_bridge` for Case (3): d₀ in place of d₁.
      have h_block11_form_bridge' :
          kron2 proj0 L_10 + kron2 proj1 (Matrix.diagonal ![d₀, d₀] * L_10) =
          kron2 (P_phase d₀) L_10 := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [kron2, proj0, proj1, P_phase, Matrix.diagonal,
                Matrix.mul_apply, Matrix.of_apply, Matrix.add_apply,
                Matrix.cons_val_zero, Matrix.cons_val_one]
      -- Mirror iter-117's `h_Eq_11_Case2` for Case (3).
      have h_Eq_11_Case3 :
          embedAC U₂ * embedBC Dmid * embedAC U₄ =
          embedAC V₂_eff' * embedAB V₃_eff' *
            embedBC (kron2 (P_phase d₁) L_00) := by
        apply mat8_eq_of_blocks_off_diag_zero
        · rw [h_block00_L_Case3_eq, h_RHS_block00']
          exact h_block00_form_bridge'
        · rw [h_block11_L_Case3_eq, h_RHS_block11_clean']
          exact h_block11_form_bridge'
        · exact hL_block01
        · exact hL_block10
        · exact h_RHS_block01'
        · exact h_RHS_block10'
      -- Symmetric to iter-80's `h_BC_V₄_eff_factored` for Case (3).
      have h_BC_V₄_eff'_factored :
          embedBC V₄_eff' =
          embedBC (kron2 (P_phase d₁) L_00) * embedBC W₅ := by
        change embedBC (kron2 (P_phase d₁) L_00 * W₅) = _
        rw [← embedBC_mul]
      -- Symmetric to iter-82's `h_chain_target_rearranged` for Case (3).
      have h_chain_target_rearranged' :
          embedBC W₁ * embedAC V₂_eff' * embedAB V₃_eff' * embedBC V₄_eff' =
          embedBC W₁ *
            (embedAC V₂_eff' * embedAB V₃_eff' *
              embedBC (kron2 (P_phase d₁) L_00)) *
            embedBC W₅ := by
        rw [h_BC_V₄_eff'_factored]; noncomm_ring
      -- Case (3) chain factorization: symmetric to Case (2) with d₀/d₁
      -- swapped. Goal after this refine:
      --   `Dg.toMatrix = embedBC W₁ * embedAC V₂_eff' * embedAB V₃_eff' *
      --    embedBC V₄_eff'`
      -- Reduces (modulo BC W₁/W₅ cancellation) to a specific Eq.7-derived
      -- 3-gate identity. Requires paper Eq.7 derivation, not yet formalized.
      refine ⟨W₁, V₂_eff', V₃_eff', V₄_eff',
              hW₁_unit, hV₂_eff'_unit, hV₃_eff'_unit, hV₄_eff'_unit, ?_⟩
      -- Final closure (mirror iter 118): chain `h_chain_target_rearranged'`
      -- (regroup with W₅ to right) + reverse `h_Eq_11_Case3` (paper Eq.(11)
      -- for Case 3) + `h_chain_factored`.
      rw [h_chain_target_rearranged', ← h_Eq_11_Case3]
      exact h_chain_factored

/-- **HP paper Lemma 4.3** (page 12). If U₂ is controlled-A (block-diag-first),
    then 5 BC-AC-BC-AC-BC gates reduce to 4 gates BC-AC-AB-BC.
    Hypothesis: `U₂ = |0⟩⟨0| ⊗ P₀ + |1⟩⟨1| ⊗ P₁` (i.e., `kron2 proj0 P₀ + kron2 proj1 P₁`).

    **Proof status**: scaffolding stub. -/
theorem paper_lemma_4_3 (Dg : DiagGate3)
    (U₁ U₂ U₃ U₄ U₅ : Mat4)
    (hU₁ : IsUnitary4 U₁) (hU₂ : IsUnitary4 U₂)
    (hU₃ : IsUnitary4 U₃) (hU₄ : IsUnitary4 U₄)
    (hU₅ : IsUnitary4 U₅)
    (P₀ P₁ : Mat2) (_hP₀ : IsUnitary2 P₀) (_hP₁ : IsUnitary2 P₁)
    (hU₂_form : U₂ = kron2 proj0 P₀ + kron2 proj1 P₁)
    (h_chain : Dg.toMatrix =
      embedBC U₁ * embedAC U₂ * embedBC U₃ * embedAC U₄ * embedBC U₅) :
    ∃ V₁ V₂ V₃ V₄ : Mat4,
      IsUnitary4 V₁ ∧ IsUnitary4 V₂ ∧ IsUnitary4 V₃ ∧ IsUnitary4 V₄ ∧
      Dg.toMatrix = embedBC V₁ * embedAC V₂ * embedAB V₃ * embedBC V₄ := by
  -- **Step 1** (paper page 12): rearrange the chain so the middle three
  -- gates AC-BC-AC stand alone, multiplied on the left by `(embedBC U₁)†`
  -- absorbed into the RHS. Then the RHS is block-diag-A: it's a product
  -- of a BC gate (block-diag-A trivially) with a diagonal Mat8 (also
  -- block-diag-A) on the right, applied via existing helpers.
  set Dprime : Mat8 := embedBC (U₁.conjTranspose) * Dg.toMatrix with hDprime
  -- Rearranged chain (analogue of PY24 A.27's hypothesis shape):
  --   embedAC U₂ · embedBC U₃ · embedAC U₄ · embedBC U₅ = Dprime
  have h_chain_rearranged :
      embedAC U₂ * embedBC U₃ * embedAC U₄ * embedBC U₅ = Dprime := by
    have h1 : embedBC (U₁.conjTranspose) * embedBC U₁ = 1 := by
      rw [embedBC_mul, hU₁, embedBC_one]
    calc embedAC U₂ * embedBC U₃ * embedAC U₄ * embedBC U₅
        = 1 * (embedAC U₂ * embedBC U₃ * embedAC U₄ * embedBC U₅) := by rw [one_mul]
      _ = embedBC (U₁.conjTranspose) * embedBC U₁ *
          (embedAC U₂ * embedBC U₃ * embedAC U₄ * embedBC U₅) := by rw [h1]
      _ = embedBC (U₁.conjTranspose) *
          (embedBC U₁ * embedAC U₂ * embedBC U₃ * embedAC U₄ * embedBC U₅) := by
            noncomm_ring
      _ = embedBC (U₁.conjTranspose) * Dg.toMatrix := by rw [← h_chain]
      _ = Dprime := rfl
  -- Show Dprime is block-diag-A.
  have hDg_isDiag8 : IsDiag8 Dg.toMatrix := ⟨Dg, rfl⟩
  have h_Dprime_block01 : block01 Dprime = 0 := by
    rw [hDprime, block01_mul, block01_embedBC, isDiag8_block01 _ hDg_isDiag8]
    simp
  have h_Dprime_block10 : block10 Dprime = 0 := by
    rw [hDprime, block10_mul, block10_embedBC, isDiag8_block10 _ hDg_isDiag8]
    simp
  -- **Step 2** (paper's Lemma A.1 application): apply `py24_lemma_A_27` to
  -- the rearranged chain. The hypothesis `U₂ = kron2 proj0 P₀ + kron2 proj1 P₁`
  -- gives `V₁` controlled in A.27's terms; block-diag-A of Dprime supplies
  -- the off-diagonal-vanishing condition. Conclude `U₄` is also controlled-A.
  obtain ⟨Q₀, Q₁, hQ₀, hQ₁, hU₄_eq⟩ :=
    py24_lemma_A_27 U₂ U₃ U₄ U₅ hU₂ hU₃ hU₄ hU₅
      P₀ P₁ hU₂_form Dprime h_Dprime_block01 h_Dprime_block10 h_chain_rearranged
  -- Now: `U₂ = kron2 proj0 P₀ + kron2 proj1 P₁` (controlled-A)
  --      `U₄ = kron2 proj0 Q₀ + kron2 proj1 Q₁` (also controlled-A)
  -- **Step 3** (paper Lemma A.7 application): define the single-qubit
  -- "controls" `M := P₁·P₀†`, `N := Q₁·Q₀†` and the absorbed BC gates
  -- `W₃ := (I⊗P₀)·U₃`, `W₅ := (I⊗Q₀)·U₅`. The factorizations
  --   U₂ = C(M) · (1⊗P₀)    and    U₄ = C(N) · (1⊗Q₀)
  -- follow from `controlled_a_factor`; the unitaries M, N are unitary by
  -- `isUnitary2_mul` + `isUnitary2_conjTranspose`.
  set M : Mat2 := P₁ * P₀.conjTranspose with hM_def
  set N : Mat2 := Q₁ * Q₀.conjTranspose with hN_def
  have hM : IsUnitary2 M := isUnitary2_mul _hP₁ (isUnitary2_conjTranspose _hP₀)
  have hN : IsUnitary2 N := isUnitary2_mul hQ₁ (isUnitary2_conjTranspose hQ₀)
  have hU₂_factor :
      U₂ = (kron2 proj0 1 + kron2 proj1 M) * (kron2 1 P₀) := by
    rw [hU₂_form]; exact controlled_a_factor P₀ P₁ _hP₀
  have hU₄_factor :
      U₄ = (kron2 proj0 1 + kron2 proj1 N) * (kron2 1 Q₀) := by
    rw [hU₄_eq]; exact controlled_a_factor Q₀ Q₁ hQ₀
  -- **Step 4** (paper Lemma A.7 absorption finalization): assemble the
  -- rewritten chain in paper_lemma_4_1's form by:
  --   (a) substituting hU₂_factor, hU₄_factor;
  --   (b) splitting `embedAC (X·Y) = embedAC X · embedAC Y` via embedAC_mul;
  --   (c) converting `embedAC (kron2 1 _)` → `embedBC (kron2 1 _)` via the
  --       `embedBC_kron2_one_eq_embedAC_kron2_one` identity (this gate is
  --       second-factor-only, so AC-frame and BC-frame coincide);
  --   (d) regrouping with `noncomm_ring` and absorbing into `embedBC W₃, W₅`.
  set W₃ : Mat4 := kron2 1 P₀ * U₃ with hW₃_def
  set W₅ : Mat4 := kron2 1 Q₀ * U₅ with hW₅_def
  have h_kron2_1_P₀_unit : IsUnitary4 (kron2 1 P₀) :=
    isUnitary4_kron2 isUnitary2_one _hP₀
  have h_kron2_1_Q₀_unit : IsUnitary4 (kron2 1 Q₀) :=
    isUnitary4_kron2 isUnitary2_one hQ₀
  have hW₃_unit : IsUnitary4 W₃ := isUnitary4_mul h_kron2_1_P₀_unit hU₃
  have hW₅_unit : IsUnitary4 W₅ := isUnitary4_mul h_kron2_1_Q₀_unit hU₅
  have h_chain_rewritten : Dg.toMatrix =
      embedBC U₁ * embedAC (kron2 proj0 1 + kron2 proj1 M) *
      embedBC W₃ * embedAC (kron2 proj0 1 + kron2 proj1 N) * embedBC W₅ := by
    calc Dg.toMatrix
        = embedBC U₁ * embedAC U₂ * embedBC U₃ * embedAC U₄ * embedBC U₅ := h_chain
      _ = embedBC U₁ *
            embedAC ((kron2 proj0 1 + kron2 proj1 M) * (kron2 1 P₀)) *
            embedBC U₃ *
            embedAC ((kron2 proj0 1 + kron2 proj1 N) * (kron2 1 Q₀)) *
            embedBC U₅ := by rw [hU₂_factor, hU₄_factor]
      _ = embedBC U₁ *
            (embedAC (kron2 proj0 1 + kron2 proj1 M) * embedAC (kron2 1 P₀)) *
            embedBC U₃ *
            (embedAC (kron2 proj0 1 + kron2 proj1 N) * embedAC (kron2 1 Q₀)) *
            embedBC U₅ := by rw [← embedAC_mul, ← embedAC_mul]
      _ = embedBC U₁ *
            (embedAC (kron2 proj0 1 + kron2 proj1 M) * embedBC (kron2 1 P₀)) *
            embedBC U₃ *
            (embedAC (kron2 proj0 1 + kron2 proj1 N) * embedBC (kron2 1 Q₀)) *
            embedBC U₅ := by
              rw [← embedBC_kron2_one_eq_embedAC_kron2_one,
                  ← embedBC_kron2_one_eq_embedAC_kron2_one]
      _ = embedBC U₁ * embedAC (kron2 proj0 1 + kron2 proj1 M) *
            (embedBC (kron2 1 P₀) * embedBC U₃) *
            embedAC (kron2 proj0 1 + kron2 proj1 N) *
            (embedBC (kron2 1 Q₀) * embedBC U₅) := by noncomm_ring
      _ = embedBC U₁ * embedAC (kron2 proj0 1 + kron2 proj1 M) *
            embedBC (kron2 1 P₀ * U₃) *
            embedAC (kron2 proj0 1 + kron2 proj1 N) *
            embedBC (kron2 1 Q₀ * U₅) := by rw [embedBC_mul, embedBC_mul]
      _ = embedBC U₁ * embedAC (kron2 proj0 1 + kron2 proj1 M) *
            embedBC W₃ *
            embedAC (kron2 proj0 1 + kron2 proj1 N) *
            embedBC W₅ := by rw [← hW₃_def, ← hW₅_def]
  -- **Step 5**: invoke `paper_lemma_4_1` on the rewritten chain to close.
  exact paper_lemma_4_1 Dg U₁ W₃ W₅ hU₁ hW₃_unit hW₅_unit M N hM hN
    h_chain_rewritten

/-! ## Step 4 prerequisite: Lemma A.8 trichotomy on W₃'s action

For any 2-qubit unitary V, V's action on (|y⟩ ⊗ |0⟩) for varying |y⟩
falls into exactly one of three cases:
  (i)   ∃|y⟩ unit qubit: V(|y⟩⊗|0⟩) is entangled.
  (ii)  ∃|ψ⟩ unit qubit: ∀|y⟩ unit: ∃|z⟩: V(|y⟩⊗|0⟩) = |ψ⟩⊗|z⟩
        (first factor of output is fixed at |ψ⟩).
  (iii) ∃|ψ⟩ unit qubit: ∀|y⟩ unit: ∃|z⟩: V(|y⟩⊗|0⟩) = |z⟩⊗|ψ⟩
        (second factor of output is fixed at |ψ⟩).

The three disjuncts match the input shapes of step5_case_i, step5_case_ii,
step5_case_iii respectively, so this trichotomy is the bridge that allows
`paper_lemma_4_4` Step 4 to dispatch to the appropriate Step 5 case.

**Proof status**: scaffolding stub. Proof requires showing that if NOT case (i)
(i.e., all V(|y⟩⊗|0⟩) are tensor products), then by unitarity / span arguments
the tensor factorization must consistently fix one factor across all |y⟩,
giving case (ii) or (iii). -/
theorem lemma_A_8_trichotomy (V : Mat4) (hV : IsUnitary4 V) :
    (∃ y : Vec1, IsQubit1 y ∧ IsEntangled (Mat4.apply V (tensor1_1 y ket0_1))) ∨
    (∃ ψ : Vec1, IsQubit1 ψ ∧ ∀ y : Vec1, IsQubit1 y →
      ∃ z : Vec1, Mat4.apply V (tensor1_1 y ket0_1) = tensor1_1 ψ z) ∨
    (∃ ψ : Vec1, IsQubit1 ψ ∧ ∀ y : Vec1, IsQubit1 y →
      ∃ z : Vec1, Mat4.apply V (tensor1_1 y ket0_1) = tensor1_1 z ψ) := by
  -- Direct reduction to `py24_lemma_6_1`, which proves the same trichotomy
  -- with (ii) and (iii) swapped (PY24 puts "second-factor-fixed" in the
  -- middle disjunct, HP puts "first-factor-fixed" in the middle).
  rcases py24_lemma_6_1 V hV with h_ent | h_second_fixed | h_first_fixed
  · exact Or.inl h_ent
  · -- PY24's middle disjunct = ∃ψ, ∀x, ∃z, V(x⊗|0⟩) = tensor1_1 z ψ
    --                        = second factor fixed at ψ
    --                        = HP's third disjunct.
    exact Or.inr (Or.inr h_second_fixed)
  · -- PY24's third disjunct = ∃ψ, ∀x, ∃z, V(x⊗|0⟩) = tensor1_1 ψ z
    --                       = first factor fixed at ψ
    --                       = HP's middle disjunct.
    exact Or.inr (Or.inl h_first_fixed)

/-! ## Step 5: trichotomy dispatch via PY24 lemmas

The three sub-cases of HP Lemma 4.4's proof (paper page 13). Given:
- The chain `Dg.toMatrix = BC U₁ · AC W₂ · BC W₃ · AC W₄ · BC W₅` with all unitary,
- The normalization `W₄(|0⟩⊗|0⟩) = |0⟩⊗|0⟩` (output of PY24 A.32, our Step 1),
- The W₃ action hypothesis (one of `lemma_A_8_trichotomy`'s three disjuncts),
- The Eq.16 hypothesis (Step 3's diagonal-action derivation),

each case immediately closes via PY24 A.19, A.30, or A.33 followed by
paper_lemma_4_2/4_3. -/

/-- **Step 5 Case (i)**: W₃(|y⟩⊗|0⟩) is entangled for some y.
    Apply PY24 A.19 to derive W₂ controlled-A, then close via paper_lemma_4_3. -/
theorem step5_case_i (Dg : DiagGate3)
    (U₁ W₂ W₃ W₄ W₅ : Mat4)
    (hU₁ : IsUnitary4 U₁) (hW₂ : IsUnitary4 W₂)
    (hW₃ : IsUnitary4 W₃) (hW₄ : IsUnitary4 W₄)
    (hW₅ : IsUnitary4 W₅)
    (h_chain : Dg.toMatrix =
      embedBC U₁ * embedAC W₂ * embedBC W₃ * embedAC W₄ * embedBC W₅)
    -- Step 3+4 hypothesis: ∃ y entangled action witness; package as the
    -- specific PY24 A.19 hypothesis on W₂'s action.
    (ϕ ω : Vec2) (hϕ : IsQubit2 ϕ) (hω : IsQubit2 ω) (hEnt : IsEntangled ϕ)
    (hAct : Mat8.apply (embedAC W₂) (tensor1_2 ket0_1 ϕ) = tensor1_2 ket0_1 ω) :
    ∃ V₁ V₂ V₃ V₄ : Mat4,
      IsUnitary4 V₁ ∧ IsUnitary4 V₂ ∧ IsUnitary4 V₃ ∧ IsUnitary4 V₄ ∧
      Dg.toMatrix = embedBC V₁ * embedAC V₂ * embedAB V₃ * embedBC V₄ := by
  -- Apply PY24 A.19 to W₂: directly conclude W₂ = controlled-A form.
  obtain ⟨P₀, P₁, hP₀, hP₁, hW₂_eq⟩ :=
    py24_lemma_A_19 W₂ hW₂ ϕ ω hϕ hω hAct hEnt
  -- W₂ = kron2 proj0 P₀ + kron2 proj1 P₁ (controlled-A).
  -- Apply paper_lemma_4_3 with U₁=U₁, U₂=W₂, U₃=W₃, U₄=W₄, U₅=W₅.
  exact paper_lemma_4_3 Dg U₁ W₂ W₃ W₄ W₅
    hU₁ hW₂ hW₃ hW₄ hW₅ P₀ P₁ hP₀ hP₁ hW₂_eq h_chain

/-- **Step 5 Case (ii)**: ∃|ψ⟩: ∀|y⟩: ∃|z⟩: W₃(|y⟩⊗|0⟩) = |ψ⟩⊗|z⟩
    (first factor of output is fixed). Apply PY24 A.33 to derive W₂ controlled-A,
    then close via paper_lemma_4_3.

    Per PY24 A.33's signature, the chain action involves W₂, W₃, W₄ (V₅ does
    not appear in A.33's statement, it's only in the surrounding chain). -/
theorem step5_case_ii (Dg : DiagGate3)
    (U₁ W₂ W₃ W₄ W₅ : Mat4)
    (hU₁ : IsUnitary4 U₁) (hW₂ : IsUnitary4 W₂)
    (hW₃ : IsUnitary4 W₃) (hW₄ : IsUnitary4 W₄)
    (hW₅ : IsUnitary4 W₅)
    (h_chain : Dg.toMatrix =
      embedBC U₁ * embedAC W₂ * embedBC W₃ * embedAC W₄ * embedBC W₅)
    -- Step 4 hypothesis: first-factor-fixed action of W₃ on (·⊗|0⟩).
    (h_first_fixed : ∃ ψ : Vec1, IsQubit1 ψ ∧ ∀ y : Vec1, IsQubit1 y →
      ∃ z : Vec1, Mat4.apply W₃ (tensor1_1 y ket0_1) = tensor1_1 ψ z)
    -- Step 3 hypothesis (Eq.16-derived chain action on |0⟩⊗x⊗|0⟩):
    (h_actA33 : ∀ x : Vec1, IsQubit1 x →
      Mat8.apply (embedAC W₂ * embedBC W₃)
        (tensor1_2 ket0_1 (tensor1_1 x ket0_1)) =
      Mat8.apply (embedBC W₄.conjTranspose)
        (tensor1_2 ket0_1 (tensor1_1 x ket0_1))) :
    ∃ V₁ V₂ V₃ V₄ : Mat4,
      IsUnitary4 V₁ ∧ IsUnitary4 V₂ ∧ IsUnitary4 V₃ ∧ IsUnitary4 V₄ ∧
      Dg.toMatrix = embedBC V₁ * embedAC V₂ * embedAB V₃ * embedBC V₄ := by
  -- Apply PY24 A.33: V₁=W₂, V₂=W₃, V₄=W₄. Conclude W₂ controlled-A.
  obtain ⟨P₀, P₁, hP₀, hP₁, hW₂_eq⟩ :=
    py24_lemma_A_33 W₂ W₃ W₄ hW₂ hW₃ hW₄ h_actA33 h_first_fixed
  -- W₂ = kron2 proj0 P₀ + kron2 proj1 P₁ (controlled-A).
  exact paper_lemma_4_3 Dg U₁ W₂ W₃ W₄ W₅
    hU₁ hW₂ hW₃ hW₄ hW₅ P₀ P₁ hP₀ hP₁ hW₂_eq h_chain

/-- **Step 5 Case (iii)**: ∃|x⟩: ∀|y⟩: ∃|z⟩: W₃(|y⟩⊗|0⟩) = |z⟩⊗|x⟩.
    Apply PY24 A.30 to transform W₂W₃W₄W₅ → K₂K₃K₄K₅ with K₃ block-diag-second.
    Then close via paper_lemma_4_2. -/
theorem step5_case_iii (Dg : DiagGate3)
    (U₁ W₂ W₃ W₄ W₅ : Mat4)
    (hU₁ : IsUnitary4 U₁) (hW₂ : IsUnitary4 W₂)
    (hW₃ : IsUnitary4 W₃) (hW₄ : IsUnitary4 W₄)
    (hW₅ : IsUnitary4 W₅)
    (h_chain : Dg.toMatrix =
      embedBC U₁ * embedAC W₂ * embedBC W₃ * embedAC W₄ * embedBC W₅)
    -- Step 4 hypothesis: W₃ has second-factor-fixed action on |·⟩⊗|0⟩.
    -- Note: PY24 A.30 takes the chain `V₁_AC · V₂_BC · V₃_AC · V₄_BC`.
    -- We pass our (W₂, W₃, W₄, W₅) here.
    (h_second_fixed : ∃ ψ : Vec1, IsQubit1 ψ ∧ ∀ x : Vec1, IsQubit1 x →
      ∃ z : Vec1, Mat4.apply W₃ (tensor1_1 x ket0_1) = tensor1_1 z ψ) :
    ∃ V₁ V₂ V₃ V₄ : Mat4,
      IsUnitary4 V₁ ∧ IsUnitary4 V₂ ∧ IsUnitary4 V₃ ∧ IsUnitary4 V₄ ∧
      Dg.toMatrix = embedBC V₁ * embedAC V₂ * embedAB V₃ * embedBC V₄ := by
  -- Apply PY24 A.30 to W₂, W₃, W₄, W₅: get K₂, K₃, K₅ with K₃ block-diag-second.
  -- (PY24 A.30's output V₃ = our W₄ unchanged.)
  obtain ⟨K₂, K₃, K₅, P, hK₂, hK₃, hK₅, hP, h_chain_eq, hK₃_form⟩ :=
    py24_lemma_A_30 W₂ W₃ W₄ W₅ hW₂ hW₃ hW₄ hW₅ h_second_fixed
  -- h_chain_eq: W₂_AC W₃_BC W₄_AC W₅_BC = K₂_AC K₃_BC W₄_AC K₅_BC
  -- hK₃_form: K₃ = kron2 1 proj0 + kron2 P proj1 (block-diag-second).
  -- Substitute into the full chain.
  have h_chain_K : Dg.toMatrix =
      embedBC U₁ * embedAC K₂ * embedBC K₃ * embedAC W₄ * embedBC K₅ := by
    calc Dg.toMatrix
        = embedBC U₁ * embedAC W₂ * embedBC W₃ * embedAC W₄ * embedBC W₅ := h_chain
      _ = embedBC U₁ * (embedAC W₂ * embedBC W₃ * embedAC W₄ * embedBC W₅) := by noncomm_ring
      _ = embedBC U₁ * (embedAC K₂ * embedBC K₃ * embedAC W₄ * embedBC K₅) := by rw [h_chain_eq]
      _ = embedBC U₁ * embedAC K₂ * embedBC K₃ * embedAC W₄ * embedBC K₅ := by noncomm_ring
  -- Apply paper_lemma_4_2 with U₃ = K₃ (block-diag-second).
  exact paper_lemma_4_2 Dg U₁ K₂ K₃ W₄ K₅
    hU₁ hK₂ hK₃ hW₄ hK₅ P hP hK₃_form h_chain_K

/-! ## Eq.16: action of `embedAC W₂ * embedBC W₃` on |0⟩⊗|y⟩⊗|0⟩

Paper page 13 derivation. Given:
- the chain `BC W₁ · AC W₂ · BC W₃ · AC W₄ · BC W₅ = D` (Dg diagonal);
- `W₄(|0⟩⊗|0⟩) = |0⟩⊗|0⟩` (PY24 A.32 normalization);

we have, for any 1-qubit `y`:
  `(AC W₂ · BC W₃) · (|0⟩⊗|y⟩⊗|0⟩) = BC (W₁† · D₀ · W₅†) · (|0⟩⊗|y⟩⊗|0⟩)`
where `D₀ := block00 Dg.toMatrix`.

This is the bridge from chain-equation Eq.15 to PY24 A.33's hypothesis form
(case (ii) of Lemma 4.4) and to PY24 A.19's via composition (case (i)). -/
lemma eq_16_action (Dg : DiagGate3) (W₁ W₂ W₃ W₄ W₅ : Mat4)
    (hW₁ : IsUnitary4 W₁) (hW₅ : IsUnitary4 W₅)
    (hW₄_ket00 : Mat4.apply W₄ (tensor1_1 ket0_1 ket0_1) = tensor1_1 ket0_1 ket0_1)
    (h_chain : Dg.toMatrix =
      embedBC W₁ * embedAC W₂ * embedBC W₃ * embedAC W₄ * embedBC W₅)
    (y : Vec1) :
    Mat8.apply (embedAC W₂ * embedBC W₃)
      (tensor1_2 ket0_1 (tensor1_1 y ket0_1)) =
    Mat8.apply (embedBC
        (W₁.conjTranspose * block00 Dg.toMatrix * W₅.conjTranspose))
      (tensor1_2 ket0_1 (tensor1_1 y ket0_1)) := by
  -- Step 1: chain rearrangement.
  have hBC_W1_inv : embedBC W₁.conjTranspose * embedBC W₁ = 1 := by
    rw [embedBC_mul, hW₁, embedBC_one]
  have hW₅_right : W₅ * W₅.conjTranspose = 1 := mul_eq_one_comm.mp hW₅
  have hBC_W5_inv : embedBC W₅ * embedBC W₅.conjTranspose = 1 := by
    rw [embedBC_mul, hW₅_right, embedBC_one]
  have h_rearr :
      embedAC W₂ * embedBC W₃ * embedAC W₄ =
      embedBC W₁.conjTranspose * Dg.toMatrix * embedBC W₅.conjTranspose := by
    calc embedAC W₂ * embedBC W₃ * embedAC W₄
        = 1 * (embedAC W₂ * embedBC W₃ * embedAC W₄) := by rw [one_mul]
      _ = embedBC W₁.conjTranspose * embedBC W₁ *
          (embedAC W₂ * embedBC W₃ * embedAC W₄) := by rw [hBC_W1_inv]
      _ = embedBC W₁.conjTranspose * embedBC W₁ *
          (embedAC W₂ * embedBC W₃ * embedAC W₄) * 1 := by rw [mul_one]
      _ = embedBC W₁.conjTranspose * embedBC W₁ *
          (embedAC W₂ * embedBC W₃ * embedAC W₄) *
          (embedBC W₅ * embedBC W₅.conjTranspose) := by rw [hBC_W5_inv]
      _ = embedBC W₁.conjTranspose *
          (embedBC W₁ * embedAC W₂ * embedBC W₃ * embedAC W₄ * embedBC W₅) *
          embedBC W₅.conjTranspose := by noncomm_ring
      _ = embedBC W₁.conjTranspose * Dg.toMatrix * embedBC W₅.conjTranspose := by
          rw [← h_chain]
  -- Step 2: AC W₄ fixes (|0⟩⊗y⊗|0⟩).
  have h_AC_W4_fix :
      Mat8.apply (embedAC W₄) (tensor1_2 ket0_1 (tensor1_1 y ket0_1)) =
      tensor1_2 ket0_1 (tensor1_1 y ket0_1) :=
    embedAC_apply_ket0_b_ket0_when_V_fixes_ket00 W₄ y hW₄_ket00
  -- Step 3: D = block-diag-A (since diagonal).
  have hDg_block10 : block10 Dg.toMatrix = 0 :=
    isDiag8_block10 _ ⟨Dg, rfl⟩
  -- Step 4: assemble.
  calc Mat8.apply (embedAC W₂ * embedBC W₃)
        (tensor1_2 ket0_1 (tensor1_1 y ket0_1))
      = Mat8.apply (embedAC W₂ * embedBC W₃)
          (Mat8.apply (embedAC W₄) (tensor1_2 ket0_1 (tensor1_1 y ket0_1))) := by
        rw [h_AC_W4_fix]
    _ = Mat8.apply (embedAC W₂ * embedBC W₃ * embedAC W₄)
          (tensor1_2 ket0_1 (tensor1_1 y ket0_1)) := by
        rw [← Mat8.apply_mul]
    _ = Mat8.apply
          (embedBC W₁.conjTranspose * Dg.toMatrix * embedBC W₅.conjTranspose)
          (tensor1_2 ket0_1 (tensor1_1 y ket0_1)) := by rw [h_rearr]
    _ = Mat8.apply (embedBC W₁.conjTranspose * Dg.toMatrix)
          (Mat8.apply (embedBC W₅.conjTranspose)
            (tensor1_2 ket0_1 (tensor1_1 y ket0_1))) := by rw [Mat8.apply_mul]
    _ = Mat8.apply (embedBC W₁.conjTranspose * Dg.toMatrix)
          (tensor1_2 ket0_1
            (Mat4.apply W₅.conjTranspose (tensor1_1 y ket0_1))) := by
        rw [embedBC_apply_tensor1_2]
    _ = Mat8.apply (embedBC W₁.conjTranspose)
          (Mat8.apply Dg.toMatrix
            (tensor1_2 ket0_1
              (Mat4.apply W₅.conjTranspose (tensor1_1 y ket0_1)))) := by
        rw [Mat8.apply_mul]
    _ = Mat8.apply (embedBC W₁.conjTranspose)
          (tensor1_2 ket0_1
            (Mat4.apply (block00 Dg.toMatrix)
              (Mat4.apply W₅.conjTranspose (tensor1_1 y ket0_1)))) := by
        rw [Mat8.apply_block_diag_A_tensor1_2_ket0 hDg_block10]
    _ = tensor1_2 ket0_1
          (Mat4.apply W₁.conjTranspose
            (Mat4.apply (block00 Dg.toMatrix)
              (Mat4.apply W₅.conjTranspose (tensor1_1 y ket0_1)))) := by
        rw [embedBC_apply_tensor1_2]
    _ = tensor1_2 ket0_1
          (Mat4.apply
            (W₁.conjTranspose * block00 Dg.toMatrix * W₅.conjTranspose)
            (tensor1_1 y ket0_1)) := by
        rw [Mat4.apply_mul, Mat4.apply_mul]
    _ = Mat8.apply (embedBC
            (W₁.conjTranspose * block00 Dg.toMatrix * W₅.conjTranspose))
          (tensor1_2 ket0_1 (tensor1_1 y ket0_1)) := by
        rw [embedBC_apply_tensor1_2]

/-! ## Step 1+2 (proved) + Steps 3-5 (Steps 3-4 future work, Step 5 above)

The HP Lemma 4.4 master theorem assembles all five steps. Step 5 is fully
proved per-case above (modulo paper_lemma_4_2 and paper_lemma_4_3 helpers).
Steps 3 and 4 remain as the genuine remaining work. -/

/-- **HP Lemma 4.4** (paper page 12). 5 neighbor gates can be reduced to 4
    unrestricted gates for any diagonal 3-qubit gate.

    Paper's native pattern: BC-AC-BC-AC-BC input, BC-AC-AB-BC output.

    **Proof status**: Steps 1, 2, and 5 (per-case) are proved/dispatched.
    Steps 3 (Eq.16 derivation) and 4 (Lemma A.8 trichotomy on W₃) are
    future work. -/
theorem paper_lemma_4_4 (Dg : DiagGate3)
    (U₁ U₂ U₃ U₄ U₅ : Mat4)
    (hU₁ : IsUnitary4 U₁) (hU₂ : IsUnitary4 U₂)
    (hU₃ : IsUnitary4 U₃) (hU₄ : IsUnitary4 U₄)
    (hU₅ : IsUnitary4 U₅)
    (h_chain : Dg.toMatrix =
      embedBC U₁ * embedAC U₂ * embedBC U₃ * embedAC U₄ * embedBC U₅) :
    ∃ V₁ V₂ V₃ V₄ : Mat4,
      IsUnitary4 V₁ ∧ IsUnitary4 V₂ ∧ IsUnitary4 V₃ ∧ IsUnitary4 V₄ ∧
      Dg.toMatrix = embedBC V₁ * embedAC V₂ * embedAB V₃ * embedBC V₄ := by
  -- **Step 1**: Apply PY24 A.32 to normalize U₂,U₃,U₄,U₅.
  obtain ⟨W₂, W₃, W₄, W₅, hW₂, hW₃, hW₄, hW₅, h_chain_eq, hW₄_ket00⟩ :=
    py24_lemma_A_32 U₂ U₃ U₄ U₅ hU₂ hU₃ hU₄ hU₅
  -- **Step 2**: Substitute chain equivalence.
  have h_chain_W : Dg.toMatrix =
      embedBC U₁ * embedAC W₂ * embedBC W₃ * embedAC W₄ * embedBC W₅ := by
    calc Dg.toMatrix
        = embedBC U₁ * embedAC U₂ * embedBC U₃ * embedAC U₄ * embedBC U₅ := h_chain
      _ = embedBC U₁ * (embedAC U₂ * embedBC U₃ * embedAC U₄ * embedBC U₅) := by noncomm_ring
      _ = embedBC U₁ * (embedAC W₂ * embedBC W₃ * embedAC W₄ * embedBC W₅) := by rw [h_chain_eq]
      _ = embedBC U₁ * embedAC W₂ * embedBC W₃ * embedAC W₄ * embedBC W₅ := by noncomm_ring
  -- **Step 4**: Apply Lemma A.8 trichotomy to W₃ and dispatch.
  rcases lemma_A_8_trichotomy W₃ hW₃ with h_ent | h_first | h_second
  · -- Case (i): ∃y, W₃(y⊗|0⟩) entangled. Use `eq_16_action` + the
    -- entangled-W₃ witness to derive W₂'s entangling action on (|0⟩ ⊗ ϕ)
    -- where ϕ = W₃·(y⊗|0⟩) is the entangled state.
    obtain ⟨y, hy_qubit, h_y_ent⟩ := h_ent
    set ϕ : Vec2 := Mat4.apply W₃ (tensor1_1 y ket0_1) with hϕ_def
    have hϕ_qubit : IsQubit2 ϕ :=
      IsQubit2_apply_unitary hW₃ (IsQubit2_tensor1_1 hy_qubit IsQubit1_ket0)
    set ω : Vec2 :=
      Mat4.apply (U₁.conjTranspose * block00 Dg.toMatrix * W₅.conjTranspose)
        (tensor1_1 y ket0_1) with hω_def
    have hω_qubit : IsQubit2 ω := by
      have h_prod_unit : IsUnitary4
          (U₁.conjTranspose * block00 Dg.toMatrix * W₅.conjTranspose) :=
        isUnitary4_mul
          (isUnitary4_mul (isUnitary4_conjTranspose hU₁)
            (diagGate3_block00_unitary Dg))
          (isUnitary4_conjTranspose hW₅)
      exact IsQubit2_apply_unitary h_prod_unit
        (IsQubit2_tensor1_1 hy_qubit IsQubit1_ket0)
    have hAct : Mat8.apply (embedAC W₂) (tensor1_2 ket0_1 ϕ) =
                tensor1_2 ket0_1 ω := by
      have h_BC_W3 :
          Mat8.apply (embedBC W₃) (tensor1_2 ket0_1 (tensor1_1 y ket0_1)) =
          tensor1_2 ket0_1 ϕ :=
        embedBC_apply_tensor1_2 W₃ ket0_1 (tensor1_1 y ket0_1)
      have h_BC_eff :
          Mat8.apply
            (embedBC
              (U₁.conjTranspose * block00 Dg.toMatrix * W₅.conjTranspose))
            (tensor1_2 ket0_1 (tensor1_1 y ket0_1)) =
          tensor1_2 ket0_1 ω :=
        embedBC_apply_tensor1_2 _ ket0_1 (tensor1_1 y ket0_1)
      have h_eq16 :=
        eq_16_action Dg U₁ W₂ W₃ W₄ W₅ hU₁ hW₅ hW₄_ket00 h_chain_W y
      rw [← h_BC_W3, ← Mat8.apply_mul, h_eq16, h_BC_eff]
    exact step5_case_i Dg U₁ W₂ W₃ W₄ W₅
      hU₁ hW₂ hW₃ hW₄ hW₅ h_chain_W ϕ ω hϕ_qubit hω_qubit h_y_ent hAct
  · -- Case (ii): ∃ψ, first factor fixed. Inline dispatch (bypassing
    -- step5_case_ii because its h_actA33 is hardcoded to the original
    -- chain's W₄, whereas Eq.16 gives a *constructed* V₄_eff such that
    -- V₄_eff.conjTranspose = U₁† · D₀ · W₅†).
    --
    -- Construct V₄_eff = W₅ · D₀† · U₁ ⟹ V₄_eff† = U₁† · D₀ · W₅†.
    set V₄_eff : Mat4 :=
      W₅ * (block00 Dg.toMatrix).conjTranspose * U₁ with hV₄_eff_def
    have hD₀_unit : IsUnitary4 (block00 Dg.toMatrix) :=
      diagGate3_block00_unitary Dg
    have hV₄_eff_unit : IsUnitary4 V₄_eff :=
      isUnitary4_mul (isUnitary4_mul hW₅ (isUnitary4_conjTranspose hD₀_unit)) hU₁
    -- Derive Eq.16 in V₄_eff.conjTranspose form via eq_16_action.
    have h_actA33 : ∀ x : Vec1, IsQubit1 x →
        Mat8.apply (embedAC W₂ * embedBC W₃)
          (tensor1_2 ket0_1 (tensor1_1 x ket0_1)) =
        Mat8.apply (embedBC V₄_eff.conjTranspose)
          (tensor1_2 ket0_1 (tensor1_1 x ket0_1)) := by
      intro x _hx
      have h_conj :
          V₄_eff.conjTranspose =
          U₁.conjTranspose * block00 Dg.toMatrix * W₅.conjTranspose := by
        rw [hV₄_eff_def, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose]
        noncomm_ring
      rw [h_conj]
      exact eq_16_action Dg U₁ W₂ W₃ W₄ W₅ hU₁ hW₅ hW₄_ket00 h_chain_W x
    -- Apply PY24 A.33 to extract W₂ controlled-A.
    obtain ⟨P₀, P₁, hP₀, hP₁, hW₂_eq⟩ :=
      py24_lemma_A_33 W₂ W₃ V₄_eff hW₂ hW₃ hV₄_eff_unit h_actA33 h_first
    -- Apply paper_lemma_4_3 with the original chain W₄.
    exact paper_lemma_4_3 Dg U₁ W₂ W₃ W₄ W₅
      hU₁ hW₂ hW₃ hW₄ hW₅ P₀ P₁ hP₀ hP₁ hW₂_eq h_chain_W
  · -- Case (iii): ∃ψ, second factor fixed. This directly matches
    -- step5_case_iii's h_second_fixed hypothesis — close end-to-end.
    exact step5_case_iii Dg U₁ W₂ W₃ W₄ W₅
      hU₁ hW₂ hW₃ hW₄ hW₅ h_chain_W h_second

end HP

end
