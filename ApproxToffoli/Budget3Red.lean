/-
  ApproxToffoli.Budget3 — the residual of n = 6, 7.

  Development copy: compiled with `lean_run_code` against `ApproxToffoli.CutMain`,
  0 errors / 0 warnings.  NOT installed in the tree.

  Contents
  --------
  1. `CXCostLE k M` — a two-qubit AB gate realisable with at most `k` CNOTs.
     `cost1_decomp` / `CXCostLE.one_shape` : cost ≤ 1 ⟺ locally equivalent to an
     A-controlled gate, `M = (a Π₀ a') ⊗ B₀ + (a Π₁ a') ⊗ B₁` with `Bⱼ` UNITARY.
  2. `BCCutU m` — the AB|C cut form with ARBITRARY two-qubit BC crossings, and
     `CutBoundU 2`, the general-crossing bound (= the missing input for `PhiFive`).
  3. `czbc8_eq_kronA_BC` : `CZ_BC = kronA_BC 1 Zp4`; hence the MERGE lemmas — a LOCAL
     far-side block fuses its adjacent crossing(s) into one arbitrary BC gate.
  4. `cut3_local{1,2}_to_BCCutU2` and `budget3_of_cutBoundU_local{1,2}` : every
     three-crossing profile with a LOCAL INTERIOR block needs nothing beyond
     `CutBoundU 2`.
  5. `InteriorOneBound`, `Budget3Bound` — the statements of what is left.
-/

import ApproxToffoli.CutMain

open Matrix Complex

noncomputable section

namespace Budget3

/-! ## 1. CNOT cost of a two-qubit AB gate -/

/-- `CXCostLE k M` : the two-qubit gate `M` on the AB pair is realisable with at most
    `k` CNOTs and free single-qubit layers.  Direction is irrelevant: `CNOT_BA` is
    `CNOT_AB` conjugated by `H ⊗ H`, so it is already covered by `step`. -/
inductive CXCostLE : ℕ → Mat4 → Prop where
  | loc (a b : Mat2) (ha : IsUnitary2 a) (hb : IsUnitary2 b) : CXCostLE 0 (kron2 a b)
  | step {k : ℕ} {M : Mat4} (h : CXCostLE k M) (a b : Mat2)
      (ha : IsUnitary2 a) (hb : IsUnitary2 b) :
      CXCostLE (k + 1) (M * cutCNOT_AB_4 * kron2 a b)
  | weaken {k : ℕ} {M : Mat4} (h : CXCostLE k M) : CXCostLE (k + 1) M

theorem CXCostLE.isUnitary {k : ℕ} {M : Mat4} (h : CXCostLE k M) : IsUnitary4 M := by
  induction h with
  | loc a b ha hb => exact isUnitary4_kron2 ha hb
  | step _ a b ha hb ih =>
      exact isUnitary4_mul (isUnitary4_mul ih isUnitary4_cutCNOT_AB_4)
        (isUnitary4_kron2 ha hb)
  | weaken _ ih => exact ih

lemma isUnitary2_pauliX : IsUnitary2 pauliX := by
  unfold IsUnitary2; ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]

lemma proj_add : proj0 + proj1 = (1 : Mat2) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [proj0, proj1, Matrix.add_apply, Matrix.of_apply]

/-- **The cost-1 structure identity.**  One CNOT with free local layers is a sum of
    two product terms whose A-factors `a Πⱼ a'` are RANK ONE and whose B-factors
    `b Xʲ b'` are UNITARY. -/
lemma cost1_decomp (a b a' b' : Mat2) :
    kron2 a b * cutCNOT_AB_4 * kron2 a' b'
      = kron2 (a * proj0 * a') (b * b') + kron2 (a * proj1 * a') (b * pauliX * b') := by
  rw [cutCNOT_AB_4, Matrix.mul_add, Matrix.add_mul, kron2_mul, kron2_mul, kron2_mul,
    kron2_mul]
  have h : b * I₂ = b := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [I₂, Matrix.mul_apply, Fin.sum_univ_two]
  rw [h]

/-- **Cost ≤ 1 ⟺ locally equivalent to an A-controlled gate.**  This is the algebraic
    content of the budget that any proof of the residual has to consume; it is FALSE
    for cost 2.  Equivalently (and this is how it is used): the four B-blocks of `M`
    are SIMULTANEOUSLY diagonalised, `m^{(st)} = a · diag(B₀ₛₜ, B₁ₛₜ) · a'`. -/
theorem CXCostLE.one_shape {M : Mat4} (h : CXCostLE 1 M) :
    ∃ a a' B0 B1 : Mat2, IsUnitary2 a ∧ IsUnitary2 a' ∧ IsUnitary2 B0 ∧ IsUnitary2 B1 ∧
      M = kron2 (a * proj0 * a') B0 + kron2 (a * proj1 * a') B1 := by
  cases h with
  | step h0 a' b' ha' hb' =>
      cases h0 with
      | loc a b ha hb =>
          exact ⟨a, a', b * b', b * pauliX * b', ha, ha', isUnitary2_mul hb hb',
            isUnitary2_mul (isUnitary2_mul hb isUnitary2_pauliX) hb',
            cost1_decomp a b a' b'⟩
  | weaken h0 =>
      cases h0 with
      | loc a b ha hb =>
          refine ⟨a, 1, b, b, ha, isUnitary2_one, hb, hb, ?_⟩
          rw [mul_one, mul_one, ← kron2_add_left, ← Matrix.mul_add, proj_add, mul_one]

/-! ## 2. The general-crossing cut form -/

/-- The AB|C cut form with ARBITRARY two-qubit BC crossings — the `U`-analogue of
    `BCCut`.  One maximal RUN of BC gates, with all its interleaved free layers,
    costs exactly one such crossing. -/
inductive BCCutU : ℕ → Mat8 → Prop where
  | base (M : Mat4) (c : Mat2) (hM : IsUnitary4 M) (hc : IsUnitary2 c) :
      BCCutU 0 (kronABC M c)
  | step {m : ℕ} {U : Mat8} (h : BCCutU m U) (V : Mat4) (hV : IsUnitary4 V)
      (M : Mat4) (c : Mat2) (hM : IsUnitary4 M) (hc : IsUnitary2 c) :
      BCCutU (m + 1) (U * kronA_BC 1 V * kronABC M c)

/-- **The general-crossing bound.**  NOT PROVED.  `CutBoundU 2` is TRUE and TIGHT
    (numerically `8cos(π/8)`, attained) and FALSE at `m = 3` (value `8`) — the same
    threshold as its CNOT-crossing ancestor `cut_trace_bound_bc`.  It is exactly the
    missing input for `Block.PhiFive`. -/
def CutBoundU (m : ℕ) : Prop :=
  ∀ U : Mat8, BCCutU m U →
    Complex.normSq (Matrix.trace (CCZ8 * U)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2

/-! ## 3. `CZ_BC` is a MIRROR cut product, and the merge lemmas -/

set_option maxHeartbeats 1600000 in
-- Heartbeat bump: 64-case `fin_cases × fin_cases` on `Fin 8`.
/-- `CZ_BC = I_A ⊗ (CZ on B,C)`, and the `Mat4` factor is literally `Zp4`.  The AB|C
    description `kronABC 1 proj0 + kronABC Zhat4 proj1` and this A|BC description are
    the two block decompositions of the same diagonal gate. -/
lemma czbc8_eq_kronA_BC : CZBC8 = kronA_BC 1 Zp4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CZBC8, kronABC, kronA_BC, Zp4, Zhat4, proj0, proj1,
      Matrix.add_apply, Matrix.diagonal_apply, Matrix.one_apply, Matrix.of_apply]

/-- **Interior-local merge.**  A LOCAL far-side block between two crossings fuses
    BOTH of them into a single arbitrary two-qubit BC gate. -/
lemma czbc_local_czbc (a b c : Mat2) :
    CZBC8 * kron3 a b c * CZBC8 = kronA_BC a (Zp4 * kron2 b c * Zp4) := by
  rw [czbc8_eq_kronA_BC, kron3_eq_kronA_BC, kronA_BC_mul, kronA_BC_mul, one_mul, mul_one]

/-- **Boundary-local merge**, right end. -/
lemma local_czbc (a b c : Mat2) :
    kron3 a b c * CZBC8 = kronA_BC a (kron2 b c * Zp4) := by
  rw [czbc8_eq_kronA_BC, kron3_eq_kronA_BC, kronA_BC_mul, mul_one]

/-- **Boundary-local merge**, left end. -/
lemma czbc_local (a b c : Mat2) :
    CZBC8 * kron3 a b c = kronA_BC a (Zp4 * kron2 b c) := by
  rw [czbc8_eq_kronA_BC, kron3_eq_kronA_BC, kronA_BC_mul, one_mul]

lemma kronA_BC_left_one (a : Mat2) : kronA_BC a 1 = kronABC (kron2 a 1) 1 := by
  rw [← kron2_one_one, ← kron3_eq_kronA_BC, kron3_eq_kronABC]

/-- The A-factor of a mirror cut product splits off as an ordinary cut product, so a
    merged crossing really is a `BCCutU` crossing. -/
lemma kronA_BC_split (a : Mat2) (W : Mat4) :
    kronA_BC a W = kronABC (kron2 a 1) 1 * kronA_BC 1 W := by
  rw [← kronA_BC_left_one, kronA_BC_mul, mul_one, one_mul]

/-! ## 4. Three CZ crossings with a LOCAL interior block are only TWO crossings -/

/-- **Interior-local reduction, first interior slot** (profiles `(k₀, 0, k₂, k₃)`). -/
theorem cut3_local1_to_BCCutU2 {M0 M2 M3 : Mat4} {c0 c2 c3 a b c : Mat2}
    (h0 : IsUnitary4 M0) (h2 : IsUnitary4 M2) (h3 : IsUnitary4 M3)
    (k0 : IsUnitary2 c0) (k2 : IsUnitary2 c2) (k3 : IsUnitary2 c3)
    (ha : IsUnitary2 a) (hb : IsUnitary2 b) (hc : IsUnitary2 c) :
    BCCutU 2 (kronABC M0 c0 * CZBC8 * kron3 a b c * CZBC8 * kronABC M2 c2 * CZBC8
              * kronABC M3 c3) := by
  have hW : IsUnitary4 (Zp4 * kron2 b c * Zp4) :=
    isUnitary4_mul (isUnitary4_mul isUnitary4_zp4 (isUnitary4_kron2 hb hc)) isUnitary4_zp4
  have e : kronABC M0 c0 * CZBC8 * kron3 a b c * CZBC8 * kronABC M2 c2 * CZBC8
        * kronABC M3 c3
      = kronABC (M0 * kron2 a 1) c0 * kronA_BC 1 (Zp4 * kron2 b c * Zp4)
          * kronABC M2 c2 * kronA_BC 1 Zp4 * kronABC M3 c3 :=
    calc kronABC M0 c0 * CZBC8 * kron3 a b c * CZBC8 * kronABC M2 c2 * CZBC8
            * kronABC M3 c3
        = kronABC M0 c0 * (CZBC8 * kron3 a b c * CZBC8) * kronABC M2 c2 * CZBC8
            * kronABC M3 c3 := by noncomm_ring
      _ = kronABC M0 c0 * (kronABC (kron2 a 1) 1
            * kronA_BC 1 (Zp4 * kron2 b c * Zp4)) * kronABC M2 c2 * CZBC8
            * kronABC M3 c3 := by rw [czbc_local_czbc, kronA_BC_split]
      _ = (kronABC M0 c0 * kronABC (kron2 a 1) 1)
            * kronA_BC 1 (Zp4 * kron2 b c * Zp4) * kronABC M2 c2 * CZBC8
            * kronABC M3 c3 := by noncomm_ring
      _ = kronABC (M0 * kron2 a 1) (c0 * 1)
            * kronA_BC 1 (Zp4 * kron2 b c * Zp4) * kronABC M2 c2 * CZBC8
            * kronABC M3 c3 := by rw [kronABC_mul]
      _ = kronABC (M0 * kron2 a 1) c0
            * kronA_BC 1 (Zp4 * kron2 b c * Zp4) * kronABC M2 c2 * kronA_BC 1 Zp4
            * kronABC M3 c3 := by rw [mul_one, czbc8_eq_kronA_BC]
  rw [e]
  exact BCCutU.step (BCCutU.step
    (BCCutU.base _ _ (isUnitary4_mul h0 (isUnitary4_kron2 ha isUnitary2_one)) k0)
    _ hW _ _ h2 k2) _ isUnitary4_zp4 _ _ h3 k3

/-- **Interior-local reduction, second interior slot** (profiles `(k₀, k₁, 0, k₃)`). -/
theorem cut3_local2_to_BCCutU2 {M0 M1 M3 : Mat4} {c0 c1 c3 a b c : Mat2}
    (h0 : IsUnitary4 M0) (h1 : IsUnitary4 M1) (h3 : IsUnitary4 M3)
    (k0 : IsUnitary2 c0) (k1 : IsUnitary2 c1) (k3 : IsUnitary2 c3)
    (ha : IsUnitary2 a) (hb : IsUnitary2 b) (hc : IsUnitary2 c) :
    BCCutU 2 (kronABC M0 c0 * CZBC8 * kronABC M1 c1 * CZBC8 * kron3 a b c * CZBC8
              * kronABC M3 c3) := by
  have hW : IsUnitary4 (Zp4 * kron2 b c * Zp4) :=
    isUnitary4_mul (isUnitary4_mul isUnitary4_zp4 (isUnitary4_kron2 hb hc)) isUnitary4_zp4
  have e : kronABC M0 c0 * CZBC8 * kronABC M1 c1 * CZBC8 * kron3 a b c * CZBC8
        * kronABC M3 c3
      = kronABC M0 c0 * kronA_BC 1 Zp4 * kronABC (M1 * kron2 a 1) c1
          * kronA_BC 1 (Zp4 * kron2 b c * Zp4) * kronABC M3 c3 :=
    calc kronABC M0 c0 * CZBC8 * kronABC M1 c1 * CZBC8 * kron3 a b c * CZBC8
            * kronABC M3 c3
        = kronABC M0 c0 * CZBC8 * kronABC M1 c1 * (CZBC8 * kron3 a b c * CZBC8)
            * kronABC M3 c3 := by noncomm_ring
      _ = kronABC M0 c0 * CZBC8 * kronABC M1 c1 * (kronABC (kron2 a 1) 1
            * kronA_BC 1 (Zp4 * kron2 b c * Zp4)) * kronABC M3 c3 := by
          rw [czbc_local_czbc, kronA_BC_split]
      _ = kronABC M0 c0 * CZBC8 * (kronABC M1 c1 * kronABC (kron2 a 1) 1)
            * kronA_BC 1 (Zp4 * kron2 b c * Zp4) * kronABC M3 c3 := by noncomm_ring
      _ = kronABC M0 c0 * CZBC8 * kronABC (M1 * kron2 a 1) (c1 * 1)
            * kronA_BC 1 (Zp4 * kron2 b c * Zp4) * kronABC M3 c3 := by rw [kronABC_mul]
      _ = kronABC M0 c0 * kronA_BC 1 Zp4 * kronABC (M1 * kron2 a 1) c1
            * kronA_BC 1 (Zp4 * kron2 b c * Zp4) * kronABC M3 c3 := by
          rw [mul_one, czbc8_eq_kronA_BC]
  rw [e]
  exact BCCutU.step (BCCutU.step (BCCutU.base _ _ h0 k0) _ isUnitary4_zp4 _ _
    (isUnitary4_mul h1 (isUnitary4_kron2 ha isUnitary2_one)) k1) _ hW _ _ h3 k3

/-- **Consequence.**  Every three-crossing profile with a LOCAL INTERIOR far-side
    block — `(k₀, 0, k₂, k₃)` or `(k₀, k₁, 0, k₃)`, the other three blocks ARBITRARY
    in `U(4)` — is already covered by `CutBoundU 2`, the very lemma `Block.PhiFive`
    needs.  Nothing new has to be proved for those profiles. -/
theorem budget3_of_cutBoundU_local1 (hU : CutBoundU 2) {M0 M2 M3 : Mat4}
    {c0 c2 c3 a b c : Mat2}
    (h0 : IsUnitary4 M0) (h2 : IsUnitary4 M2) (h3 : IsUnitary4 M3)
    (k0 : IsUnitary2 c0) (k2 : IsUnitary2 c2) (k3 : IsUnitary2 c3)
    (ha : IsUnitary2 a) (hb : IsUnitary2 b) (hc : IsUnitary2 c) :
    Complex.normSq (Matrix.trace (CCZ8 * (kronABC M0 c0 * CZBC8 * kron3 a b c * CZBC8
        * kronABC M2 c2 * CZBC8 * kronABC M3 c3)))
      ≤ 64 * Real.cos (Real.pi / 8) ^ 2 :=
  hU _ (cut3_local1_to_BCCutU2 h0 h2 h3 k0 k2 k3 ha hb hc)

theorem budget3_of_cutBoundU_local2 (hU : CutBoundU 2) {M0 M1 M3 : Mat4}
    {c0 c1 c3 a b c : Mat2}
    (h0 : IsUnitary4 M0) (h1 : IsUnitary4 M1) (h3 : IsUnitary4 M3)
    (k0 : IsUnitary2 c0) (k1 : IsUnitary2 c1) (k3 : IsUnitary2 c3)
    (ha : IsUnitary2 a) (hb : IsUnitary2 b) (hc : IsUnitary2 c) :
    Complex.normSq (Matrix.trace (CCZ8 * (kronABC M0 c0 * CZBC8 * kronABC M1 c1
        * CZBC8 * kron3 a b c * CZBC8 * kronABC M3 c3)))
      ≤ 64 * Real.cos (Real.pi / 8) ^ 2 :=
  hU _ (cut3_local2_to_BCCutU2 h0 h1 h3 k0 k1 k3 ha hb hc)

/-! ## 5. What is actually left -/

/-- The three-crossing objective. -/
def cut3 (M0 M1 M2 M3 : Mat4) (c0 c1 c2 c3 : Mat2) : Mat8 :=
  kronABC M0 c0 * CZBC8 * kronABC M1 c1 * CZBC8 * kronABC M2 c2 * CZBC8
    * kronABC M3 c3

/-- **`INT1`.**  The two INTERIOR far-side blocks have CNOT-cost at most ONE; the two
    boundary blocks are arbitrary `U(4)` and there is NO budget on the sum.  TRUE and
    TIGHT (`8cos(π/8)`, attained; 120-restart exact-block-update Gauss–Seidel to
    1e-14, confirmed by an independent L-BFGS optimiser); FALSE already at interior
    costs `(1,2)` and `(2,1)` with free boundaries, where the maximum is `8`.  Covers
    the residual profiles `(k₀,1,1,k₃)`, i.e. 8 of the 16 residual words. -/
def InteriorOneBound : Prop :=
  ∀ (M0 M1 M2 M3 : Mat4) (c0 c1 c2 c3 : Mat2),
    IsUnitary4 M0 → CXCostLE 1 M1 → CXCostLE 1 M2 → IsUnitary4 M3 →
    IsUnitary2 c0 → IsUnitary2 c1 → IsUnitary2 c2 → IsUnitary2 c3 →
    Complex.normSq (Matrix.trace (CCZ8 * cut3 M0 M1 M2 M3 c0 c1 c2 c3))
      ≤ 64 * Real.cos (Real.pi / 8) ^ 2

/-- **`BUDGET3`**, the full residual: each far-side block of CNOT-cost at most two,
    total at most four.  TRUE numerically; FALSE at total 5 (profile `(2,2,1,0)`
    reaches `8`). -/
def Budget3Bound : Prop :=
  ∀ (k0 k1 k2 k3 : ℕ) (M0 M1 M2 M3 : Mat4) (c0 c1 c2 c3 : Mat2),
    k0 + k1 + k2 + k3 ≤ 4 → k0 ≤ 2 → k1 ≤ 2 → k2 ≤ 2 → k3 ≤ 2 →
    CXCostLE k0 M0 → CXCostLE k1 M1 → CXCostLE k2 M2 → CXCostLE k3 M3 →
    IsUnitary2 c0 → IsUnitary2 c1 → IsUnitary2 c2 → IsUnitary2 c3 →
    Complex.normSq (Matrix.trace (CCZ8 * cut3 M0 M1 M2 M3 c0 c1 c2 c3))
      ≤ 64 * Real.cos (Real.pi / 8) ^ 2

end Budget3

end
