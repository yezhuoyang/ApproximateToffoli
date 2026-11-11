/-
  ApproxToffoli.CutPad

  **Padding to two crossing gates.**  A cut-form circuit with zero or one crossing
  gate is also a cut-form circuit with exactly two:

  * zero crossings: insert `CZ_BC · CZ_BC = 1`;
  * one crossing:   `CZ_BC = (SWAP_AB · CZ_BC · SWAP_AB) · (CX_AB · CZ_BC · CX_AB)`,
    i.e. `(-1)^{bc} = (-1)^{ac} · (-1)^{(a⊕b)c}`.

  So the cut bound for `m ≤ 2` follows from the two-crossing case ALONE
  (`cut_trace_bound_cz_of_two`).  This is the route the paper takes in Step 3 of its
  lower-bound proof.  `CutBound.cut_trace_bound_cz` proves the `m = 0` and `m = 1`
  cases by separate direct estimates instead; both routes give the same statement,
  and `cut_trace_bound_cz_pad` re-derives it through the padding.

  Everything here is `sorry`-free.
-/

import ApproxToffoli.CutMain

open Matrix Complex

noncomputable section

/-! ## Two small facts about `kronABC` and `CZ_BC` -/

private lemma kronABC_zero_right (M : Mat4) : kronABC M (0 : Mat2) = 0 := by
  ext i j; simp [kronABC]

private lemma kronABC_add_right (M : Mat4) (b c : Mat2) :
    kronABC M b + kronABC M c = kronABC M (b + c) := by
  ext i j
  simp [kronABC, Matrix.add_apply, Matrix.of_apply]; ring

/-- `CZ_BC` is an involution. -/
lemma czbc8_mul_self : CZBC8 * CZBC8 = 1 := by
  simp only [CZBC8, Matrix.mul_add, Matrix.add_mul, kronABC_mul, Matrix.one_mul,
    Matrix.mul_one, proj0_sq, proj1_sq, proj0_mul_proj1, proj1_mul_proj0,
    kronABC_zero_right, add_zero, zero_add, zhat4_mul_self]
  rw [kronABC_add_right, proj0_add_proj1, kronABC_one]

/-! ## One crossing gate is two crossing gates -/

/-- `Z_A = SWAP · Ẑ · SWAP` and `Z_A Z_B = CX · Ẑ · CX` multiply to `Ẑ = Z_B`. -/
lemma zhat4_split :
    SWAP4 * Zhat4 * (SWAP4 * cutCNOT_AB_4) * Zhat4 * cutCNOT_AB_4 = Zhat4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SWAP4, Zhat4, cutCNOT_AB_4, kron2, proj0, proj1, pauliX, I₂,
      Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_four, Matrix.diagonal_apply,
      Matrix.one_apply]

lemma swap_cx_cancel : SWAP4 * (SWAP4 * cutCNOT_AB_4) * cutCNOT_AB_4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SWAP4, cutCNOT_AB_4, kron2, proj0, proj1, pauliX, I₂,
      Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_four, Matrix.one_apply]

/-- **`CZ_BC = (SWAP_AB CZ_BC SWAP_AB)(CX_AB CZ_BC CX_AB)`**, written with the AB
    gates merged: one crossing gate equals two crossing gates separated by a gate on
    `AB`. -/
theorem czbc8_split :
    kronABC SWAP4 1 * CZBC8 * kronABC (SWAP4 * cutCNOT_AB_4) 1 * CZBC8
      * kronABC cutCNOT_AB_4 1 = CZBC8 := by
  simp only [CZBC8, Matrix.mul_add, Matrix.add_mul, kronABC_mul, Matrix.one_mul,
    Matrix.mul_one, proj0_sq, proj1_sq, proj0_mul_proj1, proj1_mul_proj0,
    kronABC_zero_right, add_zero, zero_add]
  rw [swap_cx_cancel, zhat4_split]

/-! ## Padding -/

/-- No crossing gate ⟹ two crossing gates (`CZ · CZ = 1`). -/
theorem CZCut.pad_zero {U : Mat8} (h : CZCut 0 U) : CZCut 2 U := by
  cases h with
  | base M c hM hc =>
    have e : kronABC M c
        = kronABC M c * CZBC8 * kronABC 1 1 * CZBC8 * kronABC 1 1 := by
      rw [kronABC_one, Matrix.mul_one, Matrix.mul_one, Matrix.mul_assoc, czbc8_mul_self,
        Matrix.mul_one]
    rw [e]
    exact CZCut.step
      (CZCut.step (CZCut.base M c hM hc) 1 1 isUnitary4_one isUnitary2_one)
      1 1 isUnitary4_one isUnitary2_one

/-- One crossing gate ⟹ two crossing gates (`czbc8_split`). -/
theorem CZCut.pad_one {U : Mat8} (h : CZCut 1 U) : CZCut 2 U := by
  cases h with
  | step h0 M1 c1 hM1 hc1 =>
    cases h0 with
    | base M0 c0 hM0 hc0 =>
      have e : kronABC M0 c0 * CZBC8 * kronABC M1 c1
          = kronABC (M0 * SWAP4) (c0 * 1) * CZBC8
              * kronABC (SWAP4 * cutCNOT_AB_4) 1 * CZBC8
              * kronABC (cutCNOT_AB_4 * M1) (1 * c1) := by
        calc kronABC M0 c0 * CZBC8 * kronABC M1 c1
            = kronABC M0 c0
                * (kronABC SWAP4 1 * CZBC8 * kronABC (SWAP4 * cutCNOT_AB_4) 1 * CZBC8
                    * kronABC cutCNOT_AB_4 1)
                * kronABC M1 c1 := by rw [czbc8_split]
          _ = (kronABC M0 c0 * kronABC SWAP4 1) * CZBC8
                * kronABC (SWAP4 * cutCNOT_AB_4) 1 * CZBC8
                * (kronABC cutCNOT_AB_4 1 * kronABC M1 c1) := by noncomm_ring
          _ = kronABC (M0 * SWAP4) (c0 * 1) * CZBC8
                * kronABC (SWAP4 * cutCNOT_AB_4) 1 * CZBC8
                * kronABC (cutCNOT_AB_4 * M1) (1 * c1) := by
              rw [kronABC_mul, kronABC_mul]
      rw [e]
      exact CZCut.step
        (CZCut.step
          (CZCut.base _ _ (isUnitary4_mul hM0 isUnitary4_SWAP4)
            (isUnitary2_mul hc0 isUnitary2_one))
          _ _ (isUnitary4_mul isUnitary4_SWAP4 isUnitary4_cutCNOT_AB_4) isUnitary2_one)
        _ _ (isUnitary4_mul isUnitary4_cutCNOT_AB_4 hM1)
        (isUnitary2_mul isUnitary2_one hc1)

/-- **Padding.** A cut-form circuit with at most two crossing gates is a cut-form
    circuit with exactly two. -/
theorem CZCut.pad {m : ℕ} {U : Mat8} (h : CZCut m U) (hm : m ≤ 2) : CZCut 2 U := by
  interval_cases m
  · exact h.pad_zero
  · exact h.pad_one
  · exact h

/-! ## The cut bound needs only the two-crossing case -/

/-- Any bound that holds for two crossing gates holds for at most two. -/
theorem cut_trace_bound_cz_of_two
    (h2 : ∀ U : Mat8, CZCut 2 U →
      Complex.normSq (Matrix.trace (CCZ8 * U)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2)
    {m : ℕ} {U : Mat8} (h : CZCut m U) (hm : m ≤ 2) :
    Complex.normSq (Matrix.trace (CCZ8 * U)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2 :=
  h2 U (h.pad hm)

/-- `cut_trace_bound_cz`, re-derived along the paper's route: only its `m = 2`
    instance is used, and zero or one crossing is handled by padding. -/
theorem cut_trace_bound_cz_pad {m : ℕ} {U : Mat8} (h : CZCut m U) (hm : m ≤ 2) :
    Complex.normSq (Matrix.trace (CCZ8 * U)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2 :=
  cut_trace_bound_cz_of_two (fun _ h2 => cut_trace_bound_cz h2 le_rfl) h hm

end
