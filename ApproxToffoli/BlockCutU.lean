/-
  ApproxToffoli.BlockCutU

  `CutBoundU` and `Block.PhiFive`: the cut normal form with ARBITRARY two-qubit
  neighbour gates as the crossings.

  Contents
  --------
  1. `BCCutU m U` / `ABCutU m U` — the analogues of `CutForm`'s `BCCut`/`ABCut`
     in which the crossing gate is an arbitrary two-qubit unitary rather than a
     CNOT.  `bccutU_of_bccut` / `abcutU_of_abcut` show they subsume the old forms.
  2. `unitaryNeighbor_to_both_cutsU` — every `UnitaryNeighborCircuit k` circuit is
     simultaneously `BCCutU i` and `ABCutU j` with `i + j ≤ k`; for `k = 5` this
     forces `min(i,j) ≤ 2`, exactly as in `CutForm.achievable_to_both_cuts`.
  3. `ABCutU_to_BCCutU` — the A↔C mirror, which fixes `CCZ8`.
  4. `CutBoundU` — the analytic input, and `phi_bound_of_cutBoundU` /
     `phiFive_of_cutBoundU`, which derive `Block.PhiFive` from it.
  5. `AltBC` — the alternating normal form: every C-side single-qubit layer is
     absorbed into a crossing, so the blocks are pure AB gates.
  6. The Hilbert–Schmidt reduction: `trC` (partial trace over C),
     `normSq_trace_mul_unitary_le` (Cauchy–Schwarz against the free middle block),
     `HS1`/`HS2`, and `cutBoundU_of_hs`.  This reduces `CutBoundU` to ONE
     circuit-free polynomial inequality per crossing count.

  Numerical status (`PyScript`-style scripts, two structurally different
  optimisers — Gauss–Seidel with exact nuclear-norm block updates, and L-BFGS on
  `exp(anti-Hermitian)` parametrisations):

      max |Tr(CCZ8 · U)| over `BCCutU m`      m = 0 : √40        = 6.3245553203
                                              m = 1 : 4 + 2√2    = 6.8284271247
                                              m = 2 : 8cos(π/8)  = 7.3910362601  ← tight
                                              m = 3 : 8                            ← FALSE

  so `CutBoundU` is true and TIGHT at `m = 2` and false at `m = 3`, the same
  threshold as its CNOT-crossing ancestor `cut_trace_bound_cz`.

  Hilbert–Schmidt residual, same scripts:

      max ‖Θ‖²_HS   m = 1 : 12.0000000000
                    m = 2 : 13.6568542495 = 8 + 4√2   ← tight, and at the argmax
                                                        Θ has all four singular
                                                        values equal to 2cos(π/8)

  so `HS2` is exactly tight and loses NOTHING: `4(8+4√2) = 32+16√2 = 64cos²(π/8)`.
-/

import ApproxToffoli.HP.Main
import ApproxToffoli.CutMain

open Matrix Complex

noncomputable section

namespace BlockU

/-! ## 0. `embedAB`/`embedBC` in the cut-product calculus -/

set_option maxHeartbeats 1600000 in
-- 64-case `fin_cases × fin_cases` on `Fin 8`.
lemma embedAB_eq_kronABC (V : Mat4) : embedAB V = kronABC V 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedAB, kronABC, Matrix.of_apply, Matrix.one_apply]

set_option maxHeartbeats 1600000 in
-- 64-case `fin_cases × fin_cases` on `Fin 8`.
lemma embedBC_eq_kronA_BC (W : Mat4) : embedBC W = kronA_BC 1 W := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedBC, kronA_BC, Matrix.of_apply, Matrix.one_apply]

set_option maxHeartbeats 1600000 in
-- 64-case `fin_cases × fin_cases` on `Fin 8`.
/-- A C-local layer is a BC gate: this is what lets the `c`s be absorbed. -/
lemma embedBC_kron2_one (c : Mat2) : embedBC (kron2 1 c) = kronABC 1 c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedBC, kron2, kronABC, Matrix.of_apply, Matrix.one_apply]

lemma kronABC_split (M : Mat4) (c : Mat2) : kronABC M c = kronABC M 1 * kronABC 1 c := by
  rw [kronABC_mul, Matrix.mul_one, Matrix.one_mul]

lemma kronABC_comm (M : Mat4) (c : Mat2) :
    kronABC 1 c * kronABC M 1 = kronABC M 1 * kronABC 1 c := by
  rw [kronABC_mul, kronABC_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul]

set_option maxHeartbeats 2000000 in
-- 64-case `fin_cases × fin_cases` on `Fin 8` under the A↔C index relabelling.
/-- A↔C turns an AB gate into a BC gate (with the pair's two wires exchanged). -/
lemma swapMatAC_embedAB (V : Mat4) :
    swapMatAC * embedAB V * swapMatAC = embedBC (SWAP4 * V * SWAP4) := by
  ext i j
  rw [swapMatAC_conj_apply]
  fin_cases i <;> fin_cases j <;>
    simp [embedAB, embedBC, SWAP4, swapIdx, Matrix.mul_apply, Matrix.of_apply,
      Fin.sum_univ_four]

/-! ## 1. The two cut normal forms with unrestricted crossings -/

/-- The AB|C cut normal form whose crossing is an ARBITRARY two-qubit BC unitary. -/
inductive BCCutU : ℕ → Mat8 → Prop where
  | base (M : Mat4) (c : Mat2) (hM : IsUnitary4 M) (hc : IsUnitary2 c) :
      BCCutU 0 (kronABC M c)
  | step {m : ℕ} {U : Mat8} (h : BCCutU m U) (W : Mat4) (hW : IsUnitary4 W)
      (M : Mat4) (c : Mat2) (hM : IsUnitary4 M) (hc : IsUnitary2 c) :
      BCCutU (m + 1) (U * embedBC W * kronABC M c)

/-- The mirror A|BC cut normal form, crossings arbitrary two-qubit AB unitaries. -/
inductive ABCutU : ℕ → Mat8 → Prop where
  | base (c : Mat2) (M : Mat4) (hc : IsUnitary2 c) (hM : IsUnitary4 M) :
      ABCutU 0 (kronA_BC c M)
  | step {m : ℕ} {U : Mat8} (h : ABCutU m U) (V : Mat4) (hV : IsUnitary4 V)
      (c : Mat2) (M : Mat4) (hc : IsUnitary2 c) (hM : IsUnitary4 M) :
      ABCutU (m + 1) (U * embedAB V * kronA_BC c M)

/-! ### The four allowed CNOTs, as two-qubit unitaries
(local copies of `Block.cnotFwd4` / `Block.cnotRev4` and their embeddings). -/

/-- CNOT on a pair with the FIRST wire of the pair as control. -/
def cnotFwd4 : Mat4 :=
  Matrix.of fun (i j : Fin 4) =>
    match i, j with
    | 0, 0 => (1 : ℂ) | 1, 1 => 1 | 2, 3 => 1 | 3, 2 => 1 | _, _ => 0

/-- CNOT on a pair with the SECOND wire of the pair as control. -/
def cnotRev4 : Mat4 :=
  Matrix.of fun (i j : Fin 4) =>
    match i, j with
    | 0, 0 => (1 : ℂ) | 1, 3 => 1 | 2, 2 => 1 | 3, 1 => 1 | _, _ => 0

set_option maxHeartbeats 1600000 in
-- 16-case `fin_cases × fin_cases` over `Fin 4`.
theorem cnotFwd4_unitary : IsUnitary4 cnotFwd4 := by
  unfold IsUnitary4
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cnotFwd4, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four,
      Matrix.of_apply]

set_option maxHeartbeats 1600000 in
-- 16-case `fin_cases × fin_cases` over `Fin 4`.
theorem cnotRev4_unitary : IsUnitary4 cnotRev4 := by
  unfold IsUnitary4
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cnotRev4, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four,
      Matrix.of_apply]

set_option maxHeartbeats 1600000 in
-- 64-case `fin_cases × fin_cases` over `Fin 8`.
theorem embedAB_cnotFwd4 : embedAB cnotFwd4 = CX_AB := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedAB, cnotFwd4, CX_AB, kron3, proj0, proj1, pauliX, I₂, decode3,
      Matrix.of_apply, Matrix.add_apply, Matrix.one_apply]

set_option maxHeartbeats 1600000 in
-- 64-case `fin_cases × fin_cases` over `Fin 8`.
theorem embedAB_cnotRev4 : embedAB cnotRev4 = CX_BA := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedAB, cnotRev4, CX_BA, kron3, proj0, proj1, pauliX, I₂, decode3,
      Matrix.of_apply, Matrix.add_apply, Matrix.one_apply]

set_option maxHeartbeats 1600000 in
-- 64-case `fin_cases × fin_cases` over `Fin 8`.
theorem embedBC_cnotFwd4 : embedBC cnotFwd4 = CX_BC := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedBC, cnotFwd4, CX_BC, kron3, proj0, proj1, pauliX, I₂, decode3,
      Matrix.of_apply, Matrix.add_apply, Matrix.one_apply]

set_option maxHeartbeats 1600000 in
-- 64-case `fin_cases × fin_cases` over `Fin 8`.
theorem embedBC_cnotRev4 : embedBC cnotRev4 = CX_CB := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedBC, cnotRev4, CX_CB, kron3, proj0, proj1, pauliX, I₂, decode3,
      Matrix.of_apply, Matrix.add_apply, Matrix.one_apply]

/-- **Subsumption.** The CNOT-crossing cut form is a special case, so any bound
    proved for `BCCutU` implies the corresponding bound for `BCCut`. -/
theorem bccutU_of_bccut {m : ℕ} {U : Mat8} (h : BCCut m U) : BCCutU m U := by
  induction h with
  | base M c hM hc => exact .base M c hM hc
  | stepBC hrest M c hM hc ih =>
      rw [← embedBC_cnotFwd4]; exact .step ih _ cnotFwd4_unitary M c hM hc
  | stepCB hrest M c hM hc ih =>
      rw [← embedBC_cnotRev4]; exact .step ih _ cnotRev4_unitary M c hM hc

theorem abcutU_of_abcut {m : ℕ} {U : Mat8} (h : ABCut m U) : ABCutU m U := by
  induction h with
  | base c M hc hM => exact .base c M hc hM
  | stepAB hrest c M hc hM ih =>
      rw [← embedAB_cnotFwd4]; exact .step ih _ cnotFwd4_unitary c M hc hM
  | stepBA hrest c M hc hM ih =>
      rw [← embedAB_cnotRev4]; exact .step ih _ cnotRev4_unitary c M hc hM

/-! ### Closure under cut products -/

lemma BCCutU_mul_right {m : ℕ} {U : Mat8} (h : BCCutU m U) :
    ∀ (M : Mat4) (c : Mat2), IsUnitary4 M → IsUnitary2 c → BCCutU m (U * kronABC M c) := by
  induction h with
  | base M' c' hM' hc' =>
      intro M c hM hc; rw [kronABC_mul]
      exact .base _ _ (isUnitary4_mul hM' hM) (isUnitary2_mul hc' hc)
  | step hrest W hW M' c' hM' hc' _ =>
      intro M c hM hc; rw [Matrix.mul_assoc, kronABC_mul]
      exact .step hrest W hW _ _ (isUnitary4_mul hM' hM) (isUnitary2_mul hc' hc)

lemma BCCutU_mul_left {m : ℕ} {U : Mat8} (h : BCCutU m U) :
    ∀ (M : Mat4) (c : Mat2), IsUnitary4 M → IsUnitary2 c → BCCutU m (kronABC M c * U) := by
  induction h with
  | base M' c' hM' hc' =>
      intro M c hM hc; rw [kronABC_mul]
      exact .base _ _ (isUnitary4_mul hM hM') (isUnitary2_mul hc hc')
  | step hrest W hW M' c' hM' hc' ih =>
      intro M c hM hc; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
      exact .step (ih M c hM hc) W hW _ _ hM' hc'

lemma ABCutU_mul_right {m : ℕ} {U : Mat8} (h : ABCutU m U) :
    ∀ (c : Mat2) (M : Mat4), IsUnitary2 c → IsUnitary4 M → ABCutU m (U * kronA_BC c M) := by
  induction h with
  | base c' M' hc' hM' =>
      intro c M hc hM; rw [kronA_BC_mul]
      exact .base _ _ (isUnitary2_mul hc' hc) (isUnitary4_mul hM' hM)
  | step hrest V hV c' M' hc' hM' _ =>
      intro c M hc hM; rw [Matrix.mul_assoc, kronA_BC_mul]
      exact .step hrest V hV _ _ (isUnitary2_mul hc' hc) (isUnitary4_mul hM' hM)

lemma ABCutU_mul_left {m : ℕ} {U : Mat8} (h : ABCutU m U) :
    ∀ (c : Mat2) (M : Mat4), IsUnitary2 c → IsUnitary4 M → ABCutU m (kronA_BC c M * U) := by
  induction h with
  | base c' M' hc' hM' =>
      intro c M hc hM; rw [kronA_BC_mul]
      exact .base _ _ (isUnitary2_mul hc hc') (isUnitary4_mul hM hM')
  | step hrest V hV c' M' hc' hM' ih =>
      intro c M hc hM; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
      exact .step (ih c M hc hM) V hV _ _ hc' hM'

/-! ## 2. Joint cut count for neighbour-gate circuits -/

/-- **Step 2.** Every neighbour gate increments EXACTLY ONE of the two cut
    counters: an AB gate crosses the A|BC cut and is absorbed by the AB|C cut,
    and a BC gate does the mirror.  Hence `i + j ≤ k`; with `k = 5` (odd) this
    forces `min(i,j) ≤ 2`. -/
theorem unitaryNeighbor_to_both_cutsU {k : ℕ} {U : Mat8} (h : UnitaryNeighborCircuit k U) :
    ∃ i j : ℕ, i + j ≤ k ∧ BCCutU i U ∧ ABCutU j U := by
  induction h with
  | product uA uB uC hA hB hC =>
      refine ⟨0, 0, by omega, ?_, ?_⟩
      · rw [singleQubitLayer_eq_kronABC]; exact .base _ _ (isUnitary4_kron2 hA hB) hC
      · rw [singleQubitLayer_eq_kronA_BC]; exact .base _ _ hA (isUnitary4_kron2 hB hC)
  | weaken _ ih => obtain ⟨i, j, hle, h1, h2⟩ := ih; exact ⟨i, j, by omega, h1, h2⟩
  | compose_AB V hV uA uB uC hA hB hC _ ih =>
      obtain ⟨i, j, hle, h1, h2⟩ := ih
      refine ⟨i, j + 1, by omega, ?_, ?_⟩
      · rw [embedAB_eq_kronABC, singleQubitLayer_eq_kronABC, Matrix.mul_assoc, kronABC_mul]
        exact BCCutU_mul_right h1 _ _
          (isUnitary4_mul hV (isUnitary4_kron2 hA hB)) (isUnitary2_mul isUnitary2_one hC)
      · rw [singleQubitLayer_eq_kronA_BC]
        exact .step h2 V hV _ _ hA (isUnitary4_kron2 hB hC)
  | compose_BC V hV uA uB uC hA hB hC _ ih =>
      obtain ⟨i, j, hle, h1, h2⟩ := ih
      refine ⟨i + 1, j, by omega, ?_, ?_⟩
      · rw [singleQubitLayer_eq_kronABC]
        exact .step h1 V hV _ _ (isUnitary4_kron2 hA hB) hC
      · rw [embedBC_eq_kronA_BC, singleQubitLayer_eq_kronA_BC, Matrix.mul_assoc, kronA_BC_mul]
        exact ABCutU_mul_right h2 _ _
          (isUnitary2_mul isUnitary2_one hA) (isUnitary4_mul hV (isUnitary4_kron2 hB hC))

/-- **The A↔C mirror**, verbatim from `CutMain.ABCut_to_BCCut`. -/
theorem ABCutU_to_BCCutU {m : ℕ} {U : Mat8} (h : ABCutU m U) :
    BCCutU m (swapMatAC * U * swapMatAC) := by
  induction h with
  | base c M hc hM => rw [swapMatAC_kronA_BC]; exact .base _ _ (isUnitary4_swap_conj hM) hc
  | step hrest V hV c M hc hM ih =>
      rw [swapMatAC_conj_triple, swapMatAC_embedAB, swapMatAC_kronA_BC]
      exact .step ih _ (isUnitary4_swap_conj hV) _ _ (isUnitary4_swap_conj hM) hc

/-! ## 3. `CutBoundU` and its consequences -/

/-- **The analytic input.**  True and TIGHT at `m = 2`, FALSE at `m = 3`. -/
def CutBoundU : Prop := ∀ {m : ℕ} {U : Mat8}, BCCutU m U → m ≤ 2 →
    Complex.normSq (Matrix.trace (CCZ8 * U)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2

/-- **Step 4.**  `Phi(k) ≤ 8cos(π/8)` for `k ≤ 5`, given `CutBoundU`.  Same
    assembly as `CutMain.achievable_trace_bound_cut`: absorb `H_C` on both sides,
    then take whichever cut is small, mirroring with `swapMatAC` if it is the
    A|BC one. -/
theorem phi_bound_of_cutBoundU (hcb : CutBoundU) {k : ℕ} (hk : k ≤ 5) {U : Mat8}
    (h : UnitaryNeighborCircuit k U) :
    Complex.normSq (Matrix.trace (Uᴴ * CCX)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2 := by
  rw [normSq_trace_ccx_eq]
  obtain ⟨i, j, hle, h1, h2⟩ := unitaryNeighbor_to_both_cutsU h
  by_cases hb : i ≤ 2
  · have hW : BCCutU i (kron3 1 1 Hgate * U * kron3 1 1 Hgate) := by
      rw [hC_eq_kronABC, Matrix.mul_assoc]
      exact BCCutU_mul_left (BCCutU_mul_right h1 1 Hgate isUnitary4_one hgate_unitary)
        1 Hgate isUnitary4_one hgate_unitary
    exact hcb hW hb
  · have hj : j ≤ 2 := by omega
    have hW : ABCutU j (kron3 1 1 Hgate * U * kron3 1 1 Hgate) := by
      rw [hC_eq_kronA_BC, Matrix.mul_assoc]
      exact ABCutU_mul_left
        (ABCutU_mul_right h2 1 (kron2 1 Hgate) isUnitary2_one isUnitary4_kron2_1_H)
        1 (kron2 1 Hgate) isUnitary2_one isUnitary4_kron2_1_H
    have hbd := hcb (ABCutU_to_BCCutU hW) hj
    rwa [trace_ccz_swapMatAC] at hbd

/-- **`Block.PhiFive`**, unfolded (`Block.PhiSqBound 5 (64cos²(π/8))` is this
    statement by `rfl`), hence `Block.achievable_seven_dichotomy` applies. -/
theorem phiFive_of_cutBoundU (hcb : CutBoundU) :
    ∀ U : Mat8, UnitaryNeighborCircuit 5 U →
      Complex.normSq (Matrix.trace (Uᴴ * CCX)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2 :=
  fun _ hU => phi_bound_of_cutBoundU hcb (le_refl 5) hU

/-! ## 4. `m = 0` -/

/-- `m = 0` is unchanged: a `BCCutU 0` circuit is literally a `BCCut 0` circuit. -/
theorem cutBoundU_zero {U : Mat8} (h : BCCutU 0 U) :
    Complex.normSq (Matrix.trace (CCZ8 * U)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2 := by
  cases h with
  | base M c hM hc => exact cut_trace_bound_zero (BCCut.base M c hM hc)

/-- So `CutBoundU` is exactly the conjunction of the `m = 1` and `m = 2` cases. -/
theorem cutBoundU_of_one_two
    (h1 : ∀ {U : Mat8}, BCCutU 1 U →
      Complex.normSq (Matrix.trace (CCZ8 * U)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2)
    (h2 : ∀ {U : Mat8}, BCCutU 2 U →
      Complex.normSq (Matrix.trace (CCZ8 * U)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2) :
    CutBoundU := by
  intro m U h hm
  interval_cases m
  · exact cutBoundU_zero h
  · exact h1 h
  · exact h2 h

/-! ## 5. The alternating normal form

Every C-side single-qubit layer can be pushed into a crossing (a C-local layer
IS a BC gate, `embedBC_kron2_one`, and it commutes with the AB blocks), so a
`BCCutU (m+1)` circuit is an alternating product of `m+2` pure AB gates and
`m+1` arbitrary BC gates.  This is what makes the trace expansion have only
`2^(m+1)` terms instead of `2^(2m+1)`. -/

inductive AltBC : ℕ → Mat8 → Prop where
  | base (M : Mat4) (hM : IsUnitary4 M) : AltBC 0 (kronABC M 1)
  | step {m : ℕ} {U : Mat8} (h : AltBC m U) (W : Mat4) (hW : IsUnitary4 W)
      (M : Mat4) (hM : IsUnitary4 M) : AltBC (m + 1) (U * embedBC W * kronABC M 1)

/-- A trailing C-local layer is absorbed by the last crossing. -/
lemma AltBC_mul_C {m : ℕ} {U : Mat8} (h : AltBC (m + 1) U) {c : Mat2} (hc : IsUnitary2 c) :
    AltBC (m + 1) (U * kronABC 1 c) := by
  cases h with
  | step hV W hW M hM =>
      have e : ∀ V : Mat8, V * embedBC W * kronABC M 1 * kronABC 1 c
          = V * embedBC (W * kron2 1 c) * kronABC M 1 := by
        intro V
        rw [← embedBC_mul, embedBC_kron2_one]
        calc V * embedBC W * kronABC M 1 * kronABC 1 c
            = V * embedBC W * (kronABC 1 c * kronABC M 1) := by
              rw [kronABC_comm]; noncomm_ring
          _ = V * (embedBC W * kronABC 1 c) * kronABC M 1 := by noncomm_ring
      rw [e]
      exact .step hV _ (isUnitary4_mul hW (isUnitary4_kron2 isUnitary2_one hc)) M hM

theorem BCCutU_altForm {m : ℕ} {U : Mat8} (h : BCCutU m U) :
    ∃ (V : Mat8) (c : Mat2), IsUnitary2 c ∧ AltBC m V ∧ U = V * kronABC 1 c := by
  induction h with
  | base M c hM hc => exact ⟨kronABC M 1, c, hc, .base M hM, kronABC_split M c⟩
  | step hrest W hW M c hM hc ih =>
      obtain ⟨V, c₀, hc₀, hV, rfl⟩ := ih
      refine ⟨V * embedBC (kron2 1 c₀ * W) * kronABC M 1, c, hc,
        .step hV _ (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hc₀) hW) M hM, ?_⟩
      rw [← embedBC_mul, embedBC_kron2_one, kronABC_split M c]
      noncomm_ring

/-- For at least one crossing the C-local tail disappears completely. -/
theorem BCCutU_alt {m : ℕ} {U : Mat8} (h : BCCutU (m + 1) U) : AltBC (m + 1) U := by
  obtain ⟨V, c, hc, hV, rfl⟩ := BCCutU_altForm h
  exact AltBC_mul_C hV hc

/-! ## 6. The Hilbert–Schmidt reduction

The middle AB block of an alternating circuit is a FREE unitary, and cyclicity
puts it last, so `Tr(CCZ8 · U) = Tr(Θ · M)` with `Θ = Tr_C Ξ` for an explicit
`Ξ` built from the remaining blocks.  Cauchy–Schwarz in the Hilbert–Schmidt
inner product (`‖M‖_HS = 2` for `M ∈ U(4)`) then gives
`|Tr(CCZ8 · U)|² ≤ 4‖Θ‖²_HS`, and `4(8+4√2) = 32+16√2 = 64cos²(π/8)` — so a
bound `‖Θ‖²_HS ≤ 8+4√2` is EXACTLY enough.  Numerically the maximum of
`‖Θ‖²_HS` is `12` at `m = 1` and `8+4√2` at `m = 2`, i.e. this step is tight and
loses nothing. -/

/-- Partial trace over qubit C (index `i = 2 * (AB index) + c`). -/
def trC (X : Mat8) : Mat4 :=
  Matrix.of fun x y =>
    X ⟨2 * x.val, by omega⟩ ⟨2 * y.val, by omega⟩
      + X ⟨2 * x.val + 1, by omega⟩ ⟨2 * y.val + 1, by omega⟩

set_option maxHeartbeats 1600000 in
-- 64-term `Fin 8` trace expansion against a 16-term `Fin 4` one.
/-- Tracing against a pure AB gate factors through the partial trace over C. -/
lemma trace_mul_kronABC_one (X : Mat8) (M : Mat4) :
    Matrix.trace (X * kronABC M 1) = Matrix.trace (trC X * M) := by
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, kronABC, trC,
    Matrix.of_apply, Matrix.one_apply, Fin.sum_univ_eight, Fin.sum_univ_four]
  ring

/-- **Hilbert–Schmidt Cauchy–Schwarz against the free middle block.**
    `|Tr(Θ M)|² ≤ 4‖Θ‖²_HS` for `M ∈ U(4)`, because `‖M‖²_HS = Tr(MᴴM) = 4`.
    TIGHT exactly when `Θ` is a scalar multiple of a unitary — which is what the
    `m = 2` optimum turns out to be (all four singular values `2cos(π/8)`). -/
theorem normSq_trace_mul_unitary_le (Θ : Mat4) {M : Mat4} (hM : IsUnitary4 M) :
    Complex.normSq (Matrix.trace (Θ * M)) ≤ 4 * RCLike.re (Matrix.trace (Θᴴ * Θ)) := by
  have hi : (inner ℂ (matToEuc Θᴴ) (matToEuc M) : ℂ) = Matrix.trace (Θ * M) := by
    rw [inner_matToEuc, Matrix.conjTranspose_conjTranspose]
  have nM : ‖matToEuc M‖ ^ 2 = 4 := by
    rw [norm_matToEuc_sq, (hM : Mᴴ * M = 1)]; simp
  have nT : ‖matToEuc Θᴴ‖ ^ 2 = RCLike.re (Matrix.trace (Θᴴ * Θ)) := by
    rw [norm_matToEuc_sq, Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm Θ Θᴴ]
  have hcs : ‖(inner ℂ (matToEuc Θᴴ) (matToEuc M) : ℂ)‖ ≤ ‖matToEuc Θᴴ‖ * ‖matToEuc M‖ :=
    norm_inner_le_norm _ _
  rw [hi] at hcs
  rw [← Complex.sq_norm]
  calc ‖Matrix.trace (Θ * M)‖ ^ 2 ≤ (‖matToEuc Θᴴ‖ * ‖matToEuc M‖) ^ 2 := by
        nlinarith [hcs, norm_nonneg (Matrix.trace (Θ * M)),
          mul_nonneg (norm_nonneg (matToEuc Θᴴ)) (norm_nonneg (matToEuc M))]
    _ = 4 * RCLike.re (Matrix.trace (Θᴴ * Θ)) := by rw [mul_pow, nM, nT]; ring

/-- `‖X‖²_HS ≤ 8 + 4√2`, written out. -/
def HSSmall (X : Mat4) : Prop :=
  RCLike.re (Matrix.trace (Xᴴ * X)) ≤ 8 + 4 * Real.sqrt 2

/-- **The `m = 1` residual.**  Numerically the maximum of the left-hand side is
    exactly `12 < 13.6568… = 8+4√2`, so this has genuine slack.  (A pen-and-paper
    proof is in the accompanying report: `Θ = M₀(X₀ + R X₁)` with `R = M₀ᴴ Z' M₀`
    a rank-1 reflection and `Xᵢ = I_A ⊗ ωᵢ` the C-diagonal blocks of `W`;
    `‖Θ‖²_HS = ‖X₀‖² + ‖X₁‖² + 2Re Tr(X₀ᴴ R X₁) ≤ 4 + 4 + 4 = 12`.) -/
def HS1 : Prop := ∀ (M0 W : Mat4), IsUnitary4 M0 → IsUnitary4 W →
    HSSmall (trC (CCZ8 * kronABC M0 1 * embedBC W))

/-- **The `m = 2` residual — the whole remaining analytic content.**
    Numerically TIGHT: the maximum of the left-hand side is exactly `8 + 4√2`. -/
def HS2 : Prop := ∀ (M0 M2 W1 W2 : Mat4), IsUnitary4 M0 → IsUnitary4 M2 →
    IsUnitary4 W1 → IsUnitary4 W2 →
    HSSmall (trC (embedBC W2 * kronABC M2 1 * CCZ8 * kronABC M0 1 * embedBC W1))

/-- The arithmetic of the reduction: `4(8+4√2) = 32+16√2 = 64cos²(π/8)`. -/
lemma four_mul_hs_budget : 4 * (8 + 4 * Real.sqrt 2) = 64 * Real.cos (Real.pi / 8) ^ 2 := by
  rw [sixtyfour_cos_sq]; ring

/-- **The reduction, `m = 1`.** -/
theorem cutBoundU_one_of_HS1 (hs : HS1) {U : Mat8} (h : BCCutU 1 U) :
    Complex.normSq (Matrix.trace (CCZ8 * U)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2 := by
  have h' : AltBC 1 U := BCCutU_alt h
  cases h' with
  | step h0 W hW M1 hM1 =>
    cases h0 with
    | base M0 hM0 =>
      have e : CCZ8 * (kronABC M0 1 * embedBC W * kronABC M1 1)
          = (CCZ8 * kronABC M0 1 * embedBC W) * kronABC M1 1 := by noncomm_ring
      rw [e, trace_mul_kronABC_one]
      refine le_trans (normSq_trace_mul_unitary_le _ hM1) ?_
      rw [← four_mul_hs_budget]
      exact mul_le_mul_of_nonneg_left (hs M0 W hM0 hW) (by norm_num)

/-- **The reduction, `m = 2`.** -/
theorem cutBoundU_two_of_HS2 (hs : HS2) {U : Mat8} (h : BCCutU 2 U) :
    Complex.normSq (Matrix.trace (CCZ8 * U)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2 := by
  have h' : AltBC 2 U := BCCutU_alt h
  cases h' with
  | step h1 W2 hW2 M2 hM2 =>
    cases h1 with
    | step h0 W1 hW1 M1 hM1 =>
      cases h0 with
      | base M0 hM0 =>
        have e : CCZ8 * (kronABC M0 1 * embedBC W1 * kronABC M1 1 * embedBC W2
              * kronABC M2 1)
            = (CCZ8 * kronABC M0 1 * embedBC W1 * kronABC M1 1)
              * (embedBC W2 * kronABC M2 1) := by noncomm_ring
        rw [e, Matrix.trace_mul_comm]
        have e2 : embedBC W2 * kronABC M2 1
              * (CCZ8 * kronABC M0 1 * embedBC W1 * kronABC M1 1)
            = (embedBC W2 * kronABC M2 1 * CCZ8 * kronABC M0 1 * embedBC W1)
              * kronABC M1 1 := by noncomm_ring
        rw [e2, trace_mul_kronABC_one]
        refine le_trans (normSq_trace_mul_unitary_le _ hM1) ?_
        rw [← four_mul_hs_budget]
        exact mul_le_mul_of_nonneg_left (hs M0 M2 W1 W2 hM0 hM2 hW1 hW2) (by norm_num)

/-- **The whole reduction.**  `CutBoundU` — and hence `Block.PhiFive`, and hence
    (with `Block.achievable_seven_dichotomy`) the `n = 6, 7` dichotomy — follows
    from the two circuit-free Hilbert–Schmidt inequalities `HS1` and `HS2`. -/
theorem cutBoundU_of_hs (h1 : HS1) (h2 : HS2) : CutBoundU :=
  cutBoundU_of_one_two (cutBoundU_one_of_HS1 h1) (cutBoundU_two_of_HS2 h2)

/-- The end-to-end statement: `HS1 ∧ HS2 → Phi(5) ≤ 8cos(π/8)`. -/
theorem phiFive_of_hs (h1 : HS1) (h2 : HS2) :
    ∀ U : Mat8, UnitaryNeighborCircuit 5 U →
      Complex.normSq (Matrix.trace (Uᴴ * CCX)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2 :=
  phiFive_of_cutBoundU (cutBoundU_of_hs h1 h2)

end BlockU

end
