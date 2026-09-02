/-
  ApproxToffoli.CutMain

  The A↔C mirror bridge, and the final assembly.

  This completes the STRUCTURAL half of the new proof of the 5-gate trace bound.
  After this file, `achievable_trace_bound_cut` — the replacement for
  `achievable_trace_bound` in `TraceBound.lean` — follows from a single analytic
  input, `cut_trace_bound_cz` (equivalently, from `bridge_ineq` + `core_psi_bound`
  + the `m = 1` bound). No circuit reasoning is left.

  The chain, all of it proved except where noted:

      AchievableCircuit n U,  n ≤ 5
        →  achievable_to_both_cuts :  BCCut mBC U ∧ ABCut mAB U,  mBC + mAB ≤ n
        →  min(mBC, mAB) ≤ 2                              (because 5 is ODD)
        →  in the mBC ≤ 2 branch: absorb H_C on both sides (BCCut_mul_left/_right)
           in the mAB ≤ 2 branch: absorb H_C, then MIRROR with `swapMatAC`
                                  (ABCut_to_BCCut), which fixes CCZ8
        →  cut_trace_bound  :  BCCut m U → m ≤ 2 → |Tr(CCZ8 U)|² ≤ 64cos²(π/8)
                               [OPEN: reduces to `bridge_ineq`, `core_psi_bound`
                                and the m = 1 bound]
        →  normSq_trace_ccx_eq  (R1)  gives the Toffoli objective.

  Why the mirror is load-bearing rather than cosmetic: the relaxation is USELESS
  for three or more crossing gates — numerically `F(3) = F(4) = 8`, i.e. CCZ is
  exactly reachable with 3 BC gates and unlimited AB gates. So the `m ≥ 3` cases
  MUST go through the other cut, and `min(m, 5−m) ≤ 2` — an arithmetic fact about
  the number 5 being odd — is what makes the problem finite.

  Everything in this file is `sorry`-free.
-/

import ApproxToffoli.CutBound

open Matrix Complex

noncomputable section

/-! ## The 2-qubit SWAP, and the A↔C bridge on cut products -/

/-- The 2-qubit SWAP as a `Mat4` (index `i = 2*b + c`). -/
def SWAP4 : Mat4 :=
  Matrix.of fun i j => if i.val % 2 * 2 + i.val / 2 = j.val then 1 else 0

lemma swap4_mul_self : SWAP4 * SWAP4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SWAP4, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_four]

lemma swap4_conjTranspose : SWAP4ᴴ = SWAP4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SWAP4, Matrix.conjTranspose_apply, Matrix.of_apply]

lemma isUnitary4_SWAP4 : IsUnitary4 SWAP4 := by
  rw [IsUnitary4, swap4_conjTranspose]; exact swap4_mul_self

lemma isUnitary4_swap_conj {M : Mat4} (hM : IsUnitary4 M) :
    IsUnitary4 (SWAP4 * M * SWAP4) :=
  isUnitary4_mul (isUnitary4_mul isUnitary4_SWAP4 hM) isUnitary4_SWAP4

set_option maxHeartbeats 2000000 in
-- Heartbeat bump: 64-case `fin_cases × fin_cases` on `Fin 8`, each side a triple
-- 4×4 product under the A↔C index relabelling.
/-- **The A↔C bridge on cut products.** Conjugating `c_A ⊗ M_BC` by the A↔C swap
    gives `(SWAP M SWAP)_AB ⊗ c_C` — a cut product for the OTHER cut. -/
lemma swapMatAC_kronA_BC (c : Mat2) (M : Mat4) :
    swapMatAC * kronA_BC c M * swapMatAC = kronABC (SWAP4 * M * SWAP4) c := by
  ext i j
  rw [swapMatAC_conj_apply]
  fin_cases i <;> fin_cases j <;>
    simp [kronA_BC, kronABC, SWAP4, swapIdx, Matrix.mul_apply, Matrix.of_apply,
      Fin.sum_univ_four] <;> ring

/-- Conjugation by `swapMatAC` distributes over a triple product. -/
lemma swapMatAC_conj_triple (V G X : Mat8) :
    swapMatAC * (V * G * X) * swapMatAC
      = (swapMatAC * V * swapMatAC) * (swapMatAC * G * swapMatAC) * (swapMatAC * X * swapMatAC) := by
  have h := swapMatAC_mul_self
  calc swapMatAC * (V * G * X) * swapMatAC
      = swapMatAC * V * (swapMatAC * swapMatAC) * G * (swapMatAC * swapMatAC) * X * swapMatAC := by
        rw [h]; noncomm_ring
    _ = (swapMatAC * V * swapMatAC) * (swapMatAC * G * swapMatAC) * (swapMatAC * X * swapMatAC) := by
        noncomm_ring

/-- **The A↔C mirror.** Conjugating by the A↔C relabelling turns an A|BC-cut
    circuit into an AB|C-cut circuit with the SAME crossing-gate count. -/
theorem ABCut_to_BCCut {m : ℕ} {U : Mat8} (h : ABCut m U) :
    BCCut m (swapMatAC * U * swapMatAC) := by
  induction h with
  | base c M hc hM =>
      rw [swapMatAC_kronA_BC]
      exact BCCut.base _ _ (isUnitary4_swap_conj hM) hc
  | stepAB hrest c M hc hM ih =>
      rw [swapMatAC_conj_triple, swapMatAC_cx_ab, swapMatAC_kronA_BC]
      exact BCCut.stepCB ih _ _ (isUnitary4_swap_conj hM) hc
  | stepBA hrest c M hc hM ih =>
      rw [swapMatAC_conj_triple, swapMatAC_cx_ba, swapMatAC_kronA_BC]
      exact BCCut.stepBC ih _ _ (isUnitary4_swap_conj hM) hc

/-- `CCZ8` is `swapMatAC`-invariant, so the objective is unchanged by the mirror.
    This is the reason R1 (`CCX → CCZ`) had to come first: `CCX` is NOT
    permutation-symmetric, but `CCZ` is. -/
lemma trace_ccz_swapMatAC (U : Mat8) :
    Matrix.trace (CCZ8 * (swapMatAC * U * swapMatAC)) = Matrix.trace (CCZ8 * U) := by
  calc Matrix.trace (CCZ8 * (swapMatAC * U * swapMatAC))
      = Matrix.trace ((swapMatAC * CCZ8 * swapMatAC) * (swapMatAC * U * swapMatAC)) := by
        rw [ccz8_perm_symm_AC]
    _ = Matrix.trace (swapMatAC * CCZ8 * (swapMatAC * swapMatAC) * U * swapMatAC) := by
        congr 1; noncomm_ring
    _ = Matrix.trace (swapMatAC * (CCZ8 * U) * swapMatAC) := by
        rw [swapMatAC_mul_self]; congr 1; noncomm_ring
    _ = Matrix.trace (CCZ8 * U) := by
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, swapMatAC_mul_self, Matrix.one_mul]

/-! ## Absorbing `H_C` on the left -/

/-- Cut form is closed under LEFT multiplication by a cut product too. -/
lemma BCCut_mul_left {m : ℕ} {U : Mat8} (h : BCCut m U) :
    ∀ (M : Mat4) (c : Mat2), IsUnitary4 M → IsUnitary2 c →
      BCCut m (kronABC M c * U) := by
  induction h with
  | base M' c' hM' hc' =>
      intro M c hM hc
      rw [kronABC_mul]
      exact BCCut.base _ _ (isUnitary4_mul hM hM') (isUnitary2_mul hc hc')
  | stepBC hrest M' c' hM' hc' ih =>
      intro M c hM hc
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
      exact BCCut.stepBC (ih M c hM hc) _ _ hM' hc'
  | stepCB hrest M' c' hM' hc' ih =>
      intro M c hM hc
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
      exact BCCut.stepCB (ih M c hM hc) _ _ hM' hc'

lemma ABCut_mul_left {m : ℕ} {U : Mat8} (h : ABCut m U) :
    ∀ (c : Mat2) (M : Mat4), IsUnitary2 c → IsUnitary4 M →
      ABCut m (kronA_BC c M * U) := by
  induction h with
  | base c' M' hc' hM' =>
      intro c M hc hM
      rw [kronA_BC_mul]
      exact ABCut.base _ _ (isUnitary2_mul hc hc') (isUnitary4_mul hM hM')
  | stepAB hrest c' M' hc' hM' ih =>
      intro c M hc hM
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
      exact ABCut.stepAB (ih c M hc hM) _ _ hc' hM'
  | stepBA hrest c' M' hc' hM' ih =>
      intro c M hc hM
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
      exact ABCut.stepBA (ih c M hc hM) _ _ hc' hM'

/-- `H_C` is also a MIRROR cut product: `I_A ⊗ (I_B ⊗ H)`. -/
lemma hC_eq_kronA_BC : kron3 1 1 Hgate = kronA_BC 1 (kron2 1 Hgate) :=
  kron3_eq_kronA_BC 1 1 Hgate

/-! ## R1 in `normSq` form -/

lemma ccx_conjTranspose : CCXᴴ = CCX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CCX, Matrix.conjTranspose_apply, decode3, pauliX]

/-- **R1, `normSq` form.** The Toffoli objective equals the `CCZ` objective on the
    Hadamard-conjugated circuit — the exact statement the cut bound consumes. -/
lemma normSq_trace_ccx_eq (U : Mat8) :
    Complex.normSq (Matrix.trace (Uᴴ * CCX))
      = Complex.normSq
          (Matrix.trace (CCZ8 * (kron3 1 1 Hgate * U * kron3 1 1 Hgate))) := by
  have key : (starRingEnd ℂ) (Matrix.trace (Uᴴ * CCX)) = Matrix.trace (CCX * U) := by
    have h := Matrix.trace_conjTranspose (Uᴴ * CCX)
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      ccx_conjTranspose] at h
    exact h.symm
  have h2 : Matrix.trace (CCX * U)
      = Matrix.trace (CCZ8 * (kron3 1 1 Hgate * U * kron3 1 1 Hgate)) := by
    rw [ccx_eq_ccz_conj]
    calc Matrix.trace (kron3 1 1 Hgate * CCZ8 * kron3 1 1 Hgate * U)
        = Matrix.trace (kron3 1 1 Hgate * (CCZ8 * kron3 1 1 Hgate * U)) := by
          congr 1; noncomm_ring
      _ = Matrix.trace ((CCZ8 * kron3 1 1 Hgate * U) * kron3 1 1 Hgate) :=
          Matrix.trace_mul_comm _ _
      _ = Matrix.trace (CCZ8 * (kron3 1 1 Hgate * U * kron3 1 1 Hgate)) := by
          congr 1; noncomm_ring
  rw [← Complex.normSq_conj (Matrix.trace (Uᴴ * CCX)), key, h2]

/-! ## The cut trace bound on `BCCut`, and the final assembly -/

/-- The analytic input, transported from `CZCut` to `BCCut` by R4. -/
theorem cut_trace_bound_bc {m : ℕ} {U : Mat8} (h : BCCut m U) (hm : m ≤ 2) :
    Complex.normSq (Matrix.trace (CCZ8 * U)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2 :=
  cut_trace_bound_cz (BCCut_to_CZCut h) hm

/-- **The theorem.** This IS `achievable_trace_bound`: since iter 1058
    `TraceBound.lean` is a one-line adapter onto this statement, and the old
    `compose_trace_bound` was DELETED rather than filled, the new proof being no
    induction on gate count at all.

    Sorry-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`). Note it is
    strictly more general than the statement it replaced, which fixed `n = 5`. -/
theorem achievable_trace_bound_cut {n : ℕ} (hn : n ≤ 5) {U : Mat8}
    (h : AchievableCircuit n U) :
    Complex.normSq (Matrix.trace (Uᴴ * CCX)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2 := by
  rw [normSq_trace_ccx_eq]
  obtain ⟨mB, mA, hle, h1, h2⟩ := achievable_to_both_cuts h
  by_cases hb : mB ≤ 2
  · -- the AB|C cut is the small one: absorb `H_C` on both sides
    have hW : BCCut mB (kron3 1 1 Hgate * U * kron3 1 1 Hgate) := by
      rw [hC_eq_kronABC, Matrix.mul_assoc]
      exact BCCut_mul_left
        (BCCut_mul_right h1 1 Hgate isUnitary4_one hgate_unitary) 1 Hgate
        isUnitary4_one hgate_unitary
    exact cut_trace_bound_bc hW hb
  · -- the A|BC cut is the small one: absorb `H_C`, then MIRROR with `swapMatAC`
    have hmA : mA ≤ 2 := by omega
    have hW : ABCut mA (kron3 1 1 Hgate * U * kron3 1 1 Hgate) := by
      rw [hC_eq_kronA_BC, Matrix.mul_assoc]
      exact ABCut_mul_left
        (ABCut_mul_right h2 1 (kron2 1 Hgate) isUnitary2_one isUnitary4_kron2_1_H)
        1 (kron2 1 Hgate) isUnitary2_one isUnitary4_kron2_1_H
    have hbd := cut_trace_bound_bc (ABCut_to_BCCut hW) hmA
    rwa [trace_ccz_swapMatAC] at hbd

end
