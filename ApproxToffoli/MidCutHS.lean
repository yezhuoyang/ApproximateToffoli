/-
  ApproxToffoli.MidCutHS

  **The MIDDLE-BLOCK bound (`Block.Mid3Bound` / `Budget3Interior.ICB`) reduced to ONE
  Hilbert–Schmidt inequality of exactly the `HS1`/`HS2` shape.**

  Development copy: compiled with `lean_run_code` against the built
  `ApproxToffoli.MidCut` + `ApproxToffoli.BlockCutHS1`, 0 errors / 0 warnings.
  NOT installed in the tree.

  What this file does
  -------------------
  `Mid3Bound` is the `n = 6` residual: three `CZ_BC` crossings, the two INTERIOR AB
  blocks of CNOT-cost at most one, the two BOUNDARY blocks arbitrary `U(4)`.  The
  objective is LINEAR in the free boundary block `M₀`, so cyclicity plus
  `BlockU.trace_mul_kronABC_one` turns it into `Tr(Θ · M₀)` with `Θ = Tr_C Ξ` for an
  explicit `Ξ` that no longer mentions `M₀`; Hilbert–Schmidt Cauchy–Schwarz
  (`BlockU.normSq_trace_mul_unitary_le`, `‖M₀‖²_HS = 4`) then gives

      |Tr(CCZ8 · U)|²  ≤  4 ‖Θ‖²_HS ,     4(8 + 4√2) = 32 + 16√2 = 64cos²(π/8).

  So a bound `‖Θ‖²_HS ≤ 8 + 4√2` — `HS3` below — is EXACTLY enough.  This is the same
  reduction `BlockCutU` performs for `CutBoundU`, run on the other free block.

  Why this is progress
  --------------------
  * `M₀` (16 real parameters) is eliminated outright.
  * The objective changes from a modulus/nuclear-norm statement to a SUM OF SQUARES:
    no absolute values, no phases, polynomial in the entries.
  * `HS3` has literally the same shape and the same budget `8 + 4√2` as `BlockU.HS2`,
    the OTHER remaining hypothesis of `n = 6` (`PhiFive` reduces to `HS2` by
    `BlockU.phiFive_of_HS2`).  After this file, BOTH open inputs of the `n = 6` lower
    bound are `‖Tr_C(·)‖²_HS ≤ 8 + 4√2` — see `curve_six_of_HS2_HS3`.  In particular
    the scratchpad `BlockCutPauli.lean` development applies verbatim: its
    `pauli_identity` / `hsSmall_iff_pauli` are stated for an ARBITRARY unitary
    `X : Mat8`, so `HS3` is equivalent to the same `8 - 4√2 ≤ pauliContent Ξ`
    C-Pauli lower bound as `HS2`.
  * The step loses NOTHING: see the numerics.

  Numerics (Gauss–Seidel with exact nuclear-norm / conditional-gradient block updates,
  40 restarts per configuration; `scratchpad/mid3.py`, `mid3d.py`, `hs3_check.py`)

      max |Tr(CCZ8 · U)| over the `Mid3Bound` family      7.391036260090 = 8cos(π/8)
      max ‖Θ‖²_HS  (HS3, both interiors cost ≤ 1)        13.656854249  = 8 + 4√2   TIGHT
                   (M₁ cost 1, M₂ local)                 13.656854249  = 8 + 4√2   TIGHT
                   (M₁ local,  M₂ cost 1)                13.656854249  = 8 + 4√2   TIGHT
                   (both local)                          12.000000000
                   (M₁ relaxed to U(4))                  16            FALSE
                   (M₂ relaxed to U(4))                  16            FALSE

  and at the `HS3` argmax all four singular values of `Θ` equal `2cos(π/8)`, i.e. the
  Cauchy–Schwarz step is exactly saturated.  So `HS3` is TRUE, TIGHT, and consumes
  BOTH middle budgets — the three properties `MidCut`'s docstring demands of any
  correct proof.

  `HS3` itself is NOT proved here.  It is the whole remaining gap for `n = 6`.
-/

import ApproxToffoli.MidCut
import ApproxToffoli.BlockCutHS1

open Matrix Complex

noncomputable section

namespace Block

/-! ## 1. Peeling the free boundary block off the objective -/

/-- **Peeling `M₀`.**  The `Mid3Bound` objective is linear in the FREE boundary block
    `M₀`, and cyclicity puts `M₀` last; tracing against a pure AB gate then factors
    through the partial trace over qubit C (`BlockU.trace_mul_kronABC_one`). -/
theorem trace_ccz_peel_M0 (M0 : Mat4) (c0 : Mat2) (X : Mat8) :
    Matrix.trace (CCZ8 * kronABC M0 c0 * X)
      = Matrix.trace (BlockU.trC (kronABC 1 c0 * X * CCZ8) * M0) := by
  calc Matrix.trace (CCZ8 * kronABC M0 c0 * X)
      = Matrix.trace ((CCZ8 * kronABC M0 1) * (kronABC 1 c0 * X)) := by
        rw [BlockU.kronABC_split M0 c0]; congr 1; simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((kronABC 1 c0 * X) * (CCZ8 * kronABC M0 1)) :=
        Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((kronABC 1 c0 * X * CCZ8) * kronABC M0 1) := by
        congr 1; simp only [Matrix.mul_assoc]
    _ = Matrix.trace (BlockU.trC (kronABC 1 c0 * X * CCZ8) * M0) :=
        BlockU.trace_mul_kronABC_one _ _

/-! ## 2. `HS3`, and the reduction of `Mid3Bound` to it -/

/-- **(HS3) — the middle-block residual, in Hilbert–Schmidt form.**  Exactly the shape
    and the budget of `BlockU.HS1` / `BlockU.HS2`: `‖Θ‖²_HS ≤ 8 + 4√2`.  `M₀` has
    disappeared; the two interior blocks keep their CNOT budget and `M₃` is free.

    TIGHT: the maximum of the left-hand side is exactly `8 + 4√2 = 13.6568542495`,
    and at the argmax all four singular values of `Θ` equal `2cos(π/8)`, so the
    Cauchy–Schwarz step below loses NOTHING.  FALSE without either interior budget
    (relaxing `M₁` or `M₂` to `U(4)` raises the maximum to 16). -/
def HS3 : Prop :=
  ∀ (M1 M2 M3 : Mat4) (c0 c1 c2 c3 : Mat2),
    Cost1.Cost1U4 M1 → Cost1.Cost1U4 M2 → IsUnitary4 M3 →
    IsUnitary2 c0 → IsUnitary2 c1 → IsUnitary2 c2 → IsUnitary2 c3 →
    BlockU.HSSmall (BlockU.trC (kronABC 1 c0 * CZBC8 * kronABC M1 c1 * CZBC8
        * kronABC M2 c2 * CZBC8 * kronABC M3 c3 * CCZ8))

set_option maxHeartbeats 800000 in
-- Heartbeat bump: two reassociations of a seven-factor `Mat8` product.
/-- **The reduction.**  `HS3 → Mid3Bound`: `HS3` closes the whole middle-block bound,
    and `4(8+4√2) = 64cos²(π/8)` exactly. -/
theorem mid3Bound_of_HS3 (h : HS3) : Mid3Bound (64 * Real.cos (Real.pi / 8) ^ 2) := by
  intro M0 M1 M2 M3 c0 c1 c2 c3 hM0 hM1 hM2 hM3 hc0 hc1 hc2 hc3
  have e : CCZ8 * kronABC M0 c0 * CZBC8 * kronABC M1 c1 * CZBC8 * kronABC M2 c2
        * CZBC8 * kronABC M3 c3
      = CCZ8 * kronABC M0 c0 * (CZBC8 * kronABC M1 c1 * CZBC8 * kronABC M2 c2
        * CZBC8 * kronABC M3 c3) := by simp only [Matrix.mul_assoc]
  rw [e, trace_ccz_peel_M0]
  refine le_trans (BlockU.normSq_trace_mul_unitary_le _ hM0) ?_
  rw [← BlockU.four_mul_hs_budget]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have e2 : kronABC 1 c0 * (CZBC8 * kronABC M1 c1 * CZBC8 * kronABC M2 c2
        * CZBC8 * kronABC M3 c3) * CCZ8
      = kronABC 1 c0 * CZBC8 * kronABC M1 c1 * CZBC8 * kronABC M2 c2
        * CZBC8 * kronABC M3 c3 * CCZ8 := by simp only [Matrix.mul_assoc]
  rw [e2]
  exact h M1 M2 M3 c0 c1 c2 c3 hM1 hM2 hM3 hc0 hc1 hc2 hc3

/-! ## 3. Downstream: `HS3` closes all of `n = 6` -/

theorem cutSqBound_of_HS3 (h : HS3) {k0 k1 k2 k3 : ℕ} (h1 : k1 ≤ 1) (h2 : k2 ≤ 1) :
    CutSqBound [k3, k2, k1, k0] (64 * Real.cos (Real.pi / 8) ^ 2) :=
  cutSqBound_of_mid3 (mid3Bound_of_HS3 h) h1 h2

/-- The two residual profiles of `n = 6`, and two more of the seven of `n = 7`. -/
theorem budget3_named_of_HS3 (h : HS3) :
    CutSqBound [1, 1, 1, 0] (64 * Real.cos (Real.pi / 8) ^ 2) ∧
    CutSqBound [0, 1, 1, 1] (64 * Real.cos (Real.pi / 8) ^ 2) ∧
    CutSqBound [1, 1, 1, 1] (64 * Real.cos (Real.pi / 8) ^ 2) ∧
    CutSqBound [2, 1, 1, 0] (64 * Real.cos (Real.pi / 8) ^ 2) :=
  ⟨cutSqBound_1110_of_mid3 (mid3Bound_of_HS3 h),
   cutSqBound_0111_of_mid3 (mid3Bound_of_HS3 h),
   cutSqBound_1111_of_mid3 (mid3Bound_of_HS3 h),
   cutSqBound_2110_of_mid3 (mid3Bound_of_HS3 h)⟩

theorem achievable_trace_bound_six_of_HS3 (hphi : PhiFive) (h : HS3)
    {n : ℕ} (hn : n ≤ 6) {U : Mat8} (hU : AchievableCircuit n U) :
    Complex.normSq (Matrix.trace (Uᴴ * CCX)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2 :=
  achievable_trace_bound_six_mid hphi (mid3Bound_of_HS3 h) hn hU

/-- **`d(6) = sin(π/8)` on `PhiFive` and `HS3`.** -/
theorem curve_six_of_HS3 (hphi : PhiFive) (h : HS3) :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 6 U ∧ hsDistance U CCX = d}
      (Real.sin (Real.pi / 8)) :=
  curve_six_mid hphi (mid3Bound_of_HS3 h)

/-- **`d(6) = sin(π/8)` on `BlockU.HS2` and `HS3` ALONE.**  Both remaining hypotheses
    of the `n = 6` lower bound are now Hilbert–Schmidt inequalities of the same shape
    and the same budget: `‖Tr_C(·)‖²_HS ≤ 8 + 4√2`. -/
theorem curve_six_of_HS2_HS3 (h2 : BlockU.HS2) (h : HS3) :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 6 U ∧ hsDistance U CCX = d}
      (Real.sin (Real.pi / 8)) :=
  curve_six_of_HS3 (BlockU.phiFive_of_HS2 h2) h

/-! ## 4. The block form of `Θ`

`Θ` sees only the two C-DIAGONAL blocks of the three-crossing circuit, the second one
twisted by `Z' = CZ_AB`; the Hilbert–Schmidt norm then splits into two block norms and
one cross term.  Together with the block-column relations of a unitary (`‖A‖² + ‖C‖²
= ‖B‖² + ‖D‖² = 4`) this rewrites `HS3` as

    2 Re Tr(Ξ₀₀ᴴ Ξ₁₁ Z')  ≤  4√2 + ‖Ξ₀₁‖²_HS + ‖Ξ₁₀‖²_HS ,

with NO partial trace and NO `CCZ8` left.  Numerically this is an EQUALITY at the
argmax, where in addition `Ξ₀₁ = Ξ₁₀ = 0`. -/

/-- The `(i,j)` C-block of an `8×8` matrix (the C index is the LOW bit). -/
def cblk (X : Mat8) (i j : Fin 2) : Mat4 :=
  Matrix.of fun x y => X ⟨2 * x.val + i.val, by omega⟩ ⟨2 * y.val + j.val, by omega⟩

set_option maxHeartbeats 2000000 in
-- 16-case `fin_cases × fin_cases` on `Fin 4` through an 8×8 product.
/-- `Tr_C(X · CCZ8) = X₀₀ + X₁₁ Z'`. -/
lemma trC_mul_CCZ8 (X : Mat8) :
    BlockU.trC (X * CCZ8) = cblk X 0 0 + cblk X 1 1 * Zp4 := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [BlockU.trC, cblk, CCZ8, Zp4, Matrix.mul_apply, Matrix.of_apply,
      Matrix.diagonal]

/-- `‖A + D Z'‖²_HS = ‖A‖²_HS + ‖D‖²_HS + 2 Re Tr(Aᴴ D Z')`, from `Z'ᴴ = Z'`,
    `Z'² = 1`. -/
lemma hs4_add_mul_zp4 (A D : Mat4) :
    HSBound.hs4 (A + D * Zp4)
      = HSBound.hs4 A + HSBound.hs4 D
        + 2 * RCLike.re (Matrix.trace (Aᴴ * D * Zp4)) := by
  have hz : (Zp4 : Mat4)ᴴ = Zp4 := zp4_conjTranspose
  have hz2 : (Zp4 : Mat4) * Zp4 = 1 := zp4_mul_self
  have e : (A + D * Zp4)ᴴ * (A + D * Zp4)
      = Aᴴ * A + (Aᴴ * D * Zp4) + (Aᴴ * D * Zp4)ᴴ + Zp4 * (Dᴴ * D) * Zp4 := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hz]
    noncomm_ring
  have e2 : Matrix.trace (Zp4 * (Dᴴ * D) * Zp4) = Matrix.trace (Dᴴ * D) := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hz2, Matrix.one_mul]
  rw [HSBound.hs4, e, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
    Matrix.trace_conjTranspose, e2]
  simp only [map_add, HSBound.hs4, HSBound.re_star]
  ring

/-! ## 5. The SHAPE of a cost-one block -/

lemma zp4_eq_ctrl : Zp4 = kron2 proj0 1 + kron2 proj1 pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Zp4, kron2, proj0, proj1, pauliZ, Matrix.add_apply, Matrix.diagonal,
      Matrix.one_apply, Matrix.of_apply]

lemma proj_add' : (proj0 : Mat2) + proj1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [proj0, proj1, Matrix.add_apply, Matrix.of_apply]

/-- **Cost one IS "locally equivalent to an A-controlled gate":**
    `M = (a Π₀ a') ⊗ B₀ + (a Π₁ a') ⊗ B₁` with the A-factors RANK ONE and `B₀, B₁`
    unitary.  This is `Budget3.CXCostLE.one_shape` for the `OneGate` cost predicate —
    the one `Mid3Bound`, `ICB` and `HS3` actually carry.  Numerically the bound
    survives when `B₀, B₁` are relaxed to ARBITRARY unitaries, so this shape is the
    whole of what the budget contributes (and the cost-0 case is included, `B₀ = B₁`). -/
theorem Cost1U4_shape {M : Mat4} (h : Cost1.Cost1U4 M) :
    ∃ a a' B0 B1 : Mat2, IsUnitary2 a ∧ IsUnitary2 a' ∧ IsUnitary2 B0 ∧ IsUnitary2 B1 ∧
      M = kron2 (a * proj0 * a') B0 + kron2 (a * proj1 * a') B1 := by
  cases h with
  | zero x y hx hy =>
      refine ⟨x, 1, y, y, hx, isUnitary2_one, hy, hy, ?_⟩
      rw [Matrix.mul_one, Matrix.mul_one, ← kron2_add_left, ← Matrix.mul_add,
        proj_add', Matrix.mul_one]
  | one x y z w hx hy hz hw =>
      refine ⟨x, z, y * w, y * pauliZ * w, hx, hz, isUnitary2_mul hy hw,
        isUnitary2_mul (isUnitary2_mul hy isUnitary2_pauliZ) hw, ?_⟩
      rw [zp4_eq_ctrl, Matrix.mul_add, Matrix.add_mul, kron2_mul, kron2_mul,
        kron2_mul, kron2_mul, Matrix.mul_one]

end Block

end
