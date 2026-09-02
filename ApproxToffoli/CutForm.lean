/-
  ApproxToffoli.CutForm

  The AB|C cut normal form, and the architecture of the new proof of the
  5-gate trace bound.

  This file replaces the induction-on-gate-count architecture of
  `TraceBound.lean` (whose `compose_trace_bound` is unprovable as an induction:
  no quantity is preserved by every CNOT, because tightness only appears at the
  fourth gate). The new route is described in full in
  `notes/trace_bound_reduction.md`; every step is machine-checked numerically in
  `PyScript/cut_*.py`. In outline:

  * **R1** `CCX = H_C · CCZ · H_C`, and `U ↦ H_C U H_C` is a bijection of the
    circuit family, so the objective becomes `|Tr W − 2 W₇₇|` and the target
    `CCZ` is invariant under all permutations of A, B, C.
  * **R2** `CX_BA = (H⊗H) CX_AB (H⊗H)`, so gate DIRECTION is free: all four
    `AllowedCX` generators reduce to `CX_AB` and `CX_BC` modulo layers.
  * **R3** Everything between two BC gates is a product `(AB part) ⊗ (C part)`,
    i.e. lies in the image of `kronABC`. Hence a circuit with `m` BC gates has
    the cut normal form `BCCut m`. Relaxing the AB blocks to arbitrary `U(4)`
    is LOSSLESS (numerically `F(0) = F(1) = √40`, `F(2) = 8cos(π/8)` exactly).
  * Since `min(m, 5−m) ≤ 2` for every `m ≤ 5`, and the A↔C swap exchanges the
    two cuts while fixing `CCZ`, the whole theorem follows from the three
    bounds `F(0), F(1), F(2) ≤ 8cos(π/8)`.

  Status of this file (iter 1058): `sorry`-free, and so is the rest of the chain.
  `F(0)`, `F(1)` and `F(2)` are all proved (`CutBound.lean`), the assembly is
  `CutMain.achievable_trace_bound_cut`, and `ApproxToffoli.lean` imports the chain.

  NAMING: this file's `cutCNOT_AB_4` and `CutAlgebra`'s `swapMatAC` carry the `cut`/
  `Mat` prefixes because `ApproxToffoli.HP.SetChar` and `ApproxToffoli.HP.Defs` define
  unrelated `CNOT_AB_4` and `swapAC`; the clash is only visible once both trees are
  imported together, which did not happen until iter 1058.
-/

import ApproxToffoli.BaseCase
import ApproxToffoli.Helpers
import ApproxToffoli.Kron2
import ApproxToffoli.CutAlgebra

open Matrix Complex

noncomputable section

/-! ## The AB|C cut product -/

/-- `M` acting on qubits A,B tensored with `c` acting on qubit C.
    Index encoding `i = 2*(ab) + c`, matching `kron3`. -/
def kronABC (M : Mat4) (c : Mat2) : Mat8 :=
  Matrix.of fun i j =>
    M ⟨i.val / 2, by omega⟩ ⟨j.val / 2, by omega⟩ *
    c ⟨i.val % 2, by omega⟩ ⟨j.val % 2, by omega⟩

/-- A single-qubit layer is a cut product: this is why the AB gates and the
    layers between two BC gates all collapse into one `U(4) ⊗ U(2)`. -/
lemma singleQubitLayer_eq_kronABC (a b c : Mat2) :
    singleQubitLayer a b c = kronABC (kron2 a b) c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [singleQubitLayer, kron3, kronABC, kron2, decode3, Matrix.of_apply]

set_option maxHeartbeats 1600000 in
-- Heartbeat bump: 64-case `fin_cases × fin_cases` on `Fin 8` with an
-- eight-term inner sum.
/-- Cut products multiply blockwise. This is the entire content of the cut
    normal form: a product of cut products is a cut product. -/
lemma kronABC_mul (M N : Mat4) (b c : Mat2) :
    kronABC M b * kronABC N c = kronABC (M * N) (b * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kronABC, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_eight,
          Fin.sum_univ_four, Fin.sum_univ_two] <;> ring

/-- The identity is a cut product. -/
lemma kronABC_one : kronABC (1 : Mat4) (1 : Mat2) = (1 : Mat8) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kronABC, Matrix.one_apply, Matrix.of_apply]

/-! ## The two AB-type gates are cut products -/

/-- `kronABC` is additive in the AB factor. -/
lemma kronABC_add_left (M N : Mat4) (c : Mat2) :
    kronABC M c + kronABC N c = kronABC (M + N) c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kronABC, Matrix.add_apply, Matrix.of_apply] <;> ring

/-- `kron3` factors through the cut. -/
lemma kron3_eq_kronABC (a b c : Mat2) : kron3 a b c = kronABC (kron2 a b) c :=
  singleQubitLayer_eq_kronABC a b c

/-- CNOT on the AB pair, as a `Mat4` (control = A, target = B). -/
def cutCNOT_AB_4 : Mat4 := kron2 proj0 I₂ + kron2 proj1 pauliX

/-- CNOT on the AB pair with control = B, target = A. -/
def CNOT_BA_4 : Mat4 := kron2 I₂ proj0 + kron2 pauliX proj1

lemma cx_ab_eq_kronABC : CX_AB = kronABC cutCNOT_AB_4 I₂ := by
  rw [CX_AB, kron3_eq_kronABC, kron3_eq_kronABC, kronABC_add_left, cutCNOT_AB_4]

lemma cx_ba_eq_kronABC : CX_BA = kronABC CNOT_BA_4 I₂ := by
  rw [CX_BA, kron3_eq_kronABC, kron3_eq_kronABC, kronABC_add_left, CNOT_BA_4]

/-! ## The cut normal form

`BCCut m U` says: `U` is a product of `m` `CX_BC` gates separated by `m+1`
arbitrary cut products `M ⊗ c` with `M ∈ U(4)`, `c ∈ U(2)`. The AB gates and
all single-qubit layers have been absorbed into the `M`s and `c`s — which is
exactly the relaxation that makes the problem finite, and which is lossless.
Gate order matches `AchievableCircuit`: new factors are appended on the right.
-/

inductive BCCut : ℕ → Mat8 → Prop where
  | base (M : Mat4) (c : Mat2) (hM : IsUnitary4 M) (hc : IsUnitary2 c) :
      BCCut 0 (kronABC M c)
  | stepBC {m : ℕ} {U : Mat8} (h : BCCut m U)
      (M : Mat4) (c : Mat2) (hM : IsUnitary4 M) (hc : IsUnitary2 c) :
      BCCut (m + 1) (U * CX_BC * kronABC M c)
  | stepCB {m : ℕ} {U : Mat8} (h : BCCut m U)
      (M : Mat4) (c : Mat2) (hM : IsUnitary4 M) (hc : IsUnitary2 c) :
      BCCut (m + 1) (U * CX_CB * kronABC M c)

lemma isUnitary2_I2 : IsUnitary2 I₂ := by
  unfold IsUnitary2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [I₂, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
          Fin.sum_univ_two]

lemma isUnitary4_cutCNOT_AB_4 : IsUnitary4 cutCNOT_AB_4 := by
  unfold IsUnitary4
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cutCNOT_AB_4, kron2, proj0, proj1, I₂, pauliX, Matrix.mul_apply,
          Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
          Matrix.one_apply, Fin.sum_univ_four]

lemma isUnitary4_CNOT_BA_4 : IsUnitary4 CNOT_BA_4 := by
  unfold IsUnitary4
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CNOT_BA_4, kron2, proj0, proj1, I₂, pauliX, Matrix.mul_apply,
          Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
          Matrix.one_apply, Fin.sum_univ_four]

/-- The cut form is closed under right multiplication by a cut product. This is
    the lemma that absorbs the AB gates and the single-qubit layers. -/
lemma BCCut_mul_right {m : ℕ} {U : Mat8} (h : BCCut m U) :
    ∀ (M : Mat4) (c : Mat2), IsUnitary4 M → IsUnitary2 c →
      BCCut m (U * kronABC M c) := by
  induction h with
  | base M' c' hM' hc' =>
      intro M c hM hc
      rw [kronABC_mul]
      exact BCCut.base _ _ (isUnitary4_mul hM' hM) (isUnitary2_mul hc' hc)
  | stepBC hrest M' c' hM' hc' _ =>
      intro M c hM hc
      rw [Matrix.mul_assoc, kronABC_mul]
      exact BCCut.stepBC hrest _ _ (isUnitary4_mul hM' hM) (isUnitary2_mul hc' hc)
  | stepCB hrest M' c' hM' hc' _ =>
      intro M c hM hc
      rw [Matrix.mul_assoc, kronABC_mul]
      exact BCCut.stepCB hrest _ _ (isUnitary4_mul hM' hM) (isUnitary2_mul hc' hc)

/-! ## The cut normal form

Everything below is PROVED (as is the whole chain that consumes it, since iter 1058).
The numerical companions in `notes/trace_bound_reduction.md` and `PyScript/cut_*.py`
are falsity-checks retained as documentation, not as evidence for anything unproved.
Listed in dependency order.
-/

/-- **R2/R3.** Every achievable circuit is in cut normal form, with the BC-gate
    count bounded by the gate count. The AB gates are absorbed by
    `cx_ab_eq_kronABC` and `kronABC_mul`; `CX_CB` is turned into `CX_BC` and
    `CX_BA` into `CX_AB` by Hadamard conjugation (R2), the Hadamards being
    absorbed into the adjacent layers. -/
theorem achievable_to_BCCut {n : ℕ} {U : Mat8} (h : AchievableCircuit n U) :
    ∃ m ≤ n, BCCut m U := by
  induction h with
  | single_layer uA uB uC hA hB hC =>
      refine ⟨0, le_refl 0, ?_⟩
      rw [singleQubitLayer_eq_kronABC]
      exact BCCut.base _ _ (isUnitary4_kron2 hA hB) hC
  | weaken _ ih =>
      obtain ⟨m, hm, hcut⟩ := ih
      exact ⟨m, by omega, hcut⟩
  | compose uA uB uC hA hB hC hCX _ ih =>
      obtain ⟨m, hm, hcut⟩ := ih
      rcases hCX with rfl | rfl | rfl | rfl
      · refine ⟨m, by omega, ?_⟩
        rw [cx_ab_eq_kronABC, singleQubitLayer_eq_kronABC, Matrix.mul_assoc,
            kronABC_mul]
        exact BCCut_mul_right hcut _ _
          (isUnitary4_mul isUnitary4_cutCNOT_AB_4 (isUnitary4_kron2 hA hB))
          (isUnitary2_mul isUnitary2_I2 hC)
      · refine ⟨m, by omega, ?_⟩
        rw [cx_ba_eq_kronABC, singleQubitLayer_eq_kronABC, Matrix.mul_assoc,
            kronABC_mul]
        exact BCCut_mul_right hcut _ _
          (isUnitary4_mul isUnitary4_CNOT_BA_4 (isUnitary4_kron2 hA hB))
          (isUnitary2_mul isUnitary2_I2 hC)
      · refine ⟨m + 1, by omega, ?_⟩
        rw [singleQubitLayer_eq_kronABC]
        exact BCCut.stepBC hcut _ _ (isUnitary4_kron2 hA hB) hC
      · refine ⟨m + 1, by omega, ?_⟩
        rw [singleQubitLayer_eq_kronABC]
        exact BCCut.stepCB hcut _ _ (isUnitary4_kron2 hA hB) hC

/-! ### The mirror cut A|BC

The A↔C swap exchanges the two cuts and fixes `CCZ8`. We need the mirror form
because the relaxation is USELESS for three or more crossing gates: numerically
`F(3) = F(4) = 8`, i.e. CCZ is exactly reachable with 3 BC gates and unlimited
AB gates. So the case `m ≥ 3` must be handled through the OTHER cut, and the
arithmetic fact `min(m, 5−m) ≤ 2` — which holds because 5 is odd — is genuinely
load-bearing rather than cosmetic. -/

/-- `c` on qubit A tensored with `M` on qubits B,C. Index `i = 4*a + (bc)`. -/
def kronA_BC (c : Mat2) (M : Mat4) : Mat8 :=
  Matrix.of fun i j =>
    c ⟨i.val / 4, by omega⟩ ⟨j.val / 4, by omega⟩ *
    M ⟨i.val % 4, by omega⟩ ⟨j.val % 4, by omega⟩

/-- The mirror cut normal form: crossing gates are the AB-type ones. -/
inductive ABCut : ℕ → Mat8 → Prop where
  | base (c : Mat2) (M : Mat4) (hc : IsUnitary2 c) (hM : IsUnitary4 M) :
      ABCut 0 (kronA_BC c M)
  | stepAB {m : ℕ} {U : Mat8} (h : ABCut m U)
      (c : Mat2) (M : Mat4) (hc : IsUnitary2 c) (hM : IsUnitary4 M) :
      ABCut (m + 1) (U * CX_AB * kronA_BC c M)
  | stepBA {m : ℕ} {U : Mat8} (h : ABCut m U)
      (c : Mat2) (M : Mat4) (hc : IsUnitary2 c) (hM : IsUnitary4 M) :
      ABCut (m + 1) (U * CX_BA * kronA_BC c M)

/-! ### The `kronA_BC` calculus (mirror of the `kronABC` lemmas) -/

set_option maxHeartbeats 1600000 in
-- Heartbeat bump: 64-case `fin_cases × fin_cases` on `Fin 8` with an
-- eight-term inner sum (mirror of `kronABC_mul`).
/-- Mirror cut products multiply blockwise. -/
lemma kronA_BC_mul (c b : Mat2) (M N : Mat4) :
    kronA_BC c M * kronA_BC b N = kronA_BC (c * b) (M * N) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kronA_BC, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_eight,
          Fin.sum_univ_four, Fin.sum_univ_two] <;> ring

/-- The identity is a mirror cut product. -/
lemma kronA_BC_one : kronA_BC (1 : Mat2) (1 : Mat4) = (1 : Mat8) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kronA_BC, Matrix.one_apply, Matrix.of_apply]

/-- `kronA_BC` is additive in the BC factor. Needed because `CX_BC` is a SUM
    of two `kron3`s, so the entrywise route does not apply directly. -/
lemma kronA_BC_add_right (c : Mat2) (M N : Mat4) :
    kronA_BC c M + kronA_BC c N = kronA_BC c (M + N) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kronA_BC, Matrix.add_apply, Matrix.of_apply] <;> ring

/-- `kron3` factors through the mirror cut. -/
lemma kron3_eq_kronA_BC (a b c : Mat2) : kron3 a b c = kronA_BC a (kron2 b c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kron3, kronA_BC, kron2, decode3, Matrix.of_apply] <;> ring

lemma singleQubitLayer_eq_kronA_BC (a b c : Mat2) :
    singleQubitLayer a b c = kronA_BC a (kron2 b c) :=
  kron3_eq_kronA_BC a b c

/-! ### The two BC-type gates are mirror cut products

Note the `Mat4` factors coincide with `cutCNOT_AB_4` / `CNOT_BA_4` — in both cuts the
4×4 factor is a CNOT on a qubit pair under the same "first argument = more
significant bit" convention. Only the cut they sit in differs. -/

lemma cx_bc_eq_kronA_BC : CX_BC = kronA_BC I₂ cutCNOT_AB_4 := by
  rw [CX_BC, kron3_eq_kronA_BC, kron3_eq_kronA_BC, kronA_BC_add_right, cutCNOT_AB_4]

lemma cx_cb_eq_kronA_BC : CX_CB = kronA_BC I₂ CNOT_BA_4 := by
  rw [CX_CB, kron3_eq_kronA_BC, kron3_eq_kronA_BC, kronA_BC_add_right, CNOT_BA_4]

/-- The mirror cut form is closed under right multiplication by a mirror cut
    product: this absorbs the BC gates and the single-qubit layers. As for
    `BCCut_mul_right`, the `∀ c M` must live INSIDE the induction. -/
lemma ABCut_mul_right {m : ℕ} {U : Mat8} (h : ABCut m U) :
    ∀ (c : Mat2) (M : Mat4), IsUnitary2 c → IsUnitary4 M →
      ABCut m (U * kronA_BC c M) := by
  induction h with
  | base c' M' hc' hM' =>
      intro c M hc hM
      rw [kronA_BC_mul]
      exact ABCut.base _ _ (isUnitary2_mul hc' hc) (isUnitary4_mul hM' hM)
  | stepAB hrest c' M' hc' hM' _ =>
      intro c M hc hM
      rw [Matrix.mul_assoc, kronA_BC_mul]
      exact ABCut.stepAB hrest _ _ (isUnitary2_mul hc' hc) (isUnitary4_mul hM' hM)
  | stepBA hrest c' M' hc' hM' _ =>
      intro c M hc hM
      rw [Matrix.mul_assoc, kronA_BC_mul]
      exact ABCut.stepBA hrest _ _ (isUnitary2_mul hc' hc) (isUnitary4_mul hM' hM)

/-- **Joint cut count.** Every gate of an `AchievableCircuit` increments EXACTLY
    ONE of the two cut counters: `CX_AB`/`CX_BA` are absorbed into the AB|C cut
    (leaving `mBC` fixed) while crossing the A|BC cut, and `CX_BC`/`CX_CB` do the
    mirror. Hence `mBC + mAB ≤ n`; with `n ≤ 5` this forces `min(mBC, mAB) ≤ 2`,
    which is exactly what `cut_trace_bound` consumes. -/
theorem achievable_to_both_cuts {n : ℕ} {U : Mat8} (h : AchievableCircuit n U) :
    ∃ mBC mAB : ℕ, mBC + mAB ≤ n ∧ BCCut mBC U ∧ ABCut mAB U := by
  induction h with
  | single_layer uA uB uC hA hB hC =>
      refine ⟨0, 0, by omega, ?_, ?_⟩
      · rw [singleQubitLayer_eq_kronABC]
        exact BCCut.base _ _ (isUnitary4_kron2 hA hB) hC
      · rw [singleQubitLayer_eq_kronA_BC]
        exact ABCut.base _ _ hA (isUnitary4_kron2 hB hC)
  | weaken _ ih =>
      obtain ⟨mB, mA, hle, h1, h2⟩ := ih
      exact ⟨mB, mA, by omega, h1, h2⟩
  | compose uA uB uC hA hB hC hCX _ ih =>
      obtain ⟨mB, mA, hle, h1, h2⟩ := ih
      rcases hCX with rfl | rfl | rfl | rfl
      · -- CX_AB : absorbed by the AB|C cut, crosses the A|BC cut
        refine ⟨mB, mA + 1, by omega, ?_, ?_⟩
        · rw [cx_ab_eq_kronABC, singleQubitLayer_eq_kronABC, Matrix.mul_assoc,
              kronABC_mul]
          exact BCCut_mul_right h1 _ _
            (isUnitary4_mul isUnitary4_cutCNOT_AB_4 (isUnitary4_kron2 hA hB))
            (isUnitary2_mul isUnitary2_I2 hC)
        · rw [singleQubitLayer_eq_kronA_BC]
          exact ABCut.stepAB h2 _ _ hA (isUnitary4_kron2 hB hC)
      · -- CX_BA : same side
        refine ⟨mB, mA + 1, by omega, ?_, ?_⟩
        · rw [cx_ba_eq_kronABC, singleQubitLayer_eq_kronABC, Matrix.mul_assoc,
              kronABC_mul]
          exact BCCut_mul_right h1 _ _
            (isUnitary4_mul isUnitary4_CNOT_BA_4 (isUnitary4_kron2 hA hB))
            (isUnitary2_mul isUnitary2_I2 hC)
        · rw [singleQubitLayer_eq_kronA_BC]
          exact ABCut.stepBA h2 _ _ hA (isUnitary4_kron2 hB hC)
      · -- CX_BC : crosses the AB|C cut, absorbed by the A|BC cut
        refine ⟨mB + 1, mA, by omega, ?_, ?_⟩
        · rw [singleQubitLayer_eq_kronABC]
          exact BCCut.stepBC h1 _ _ (isUnitary4_kron2 hA hB) hC
        · rw [cx_bc_eq_kronA_BC, singleQubitLayer_eq_kronA_BC, Matrix.mul_assoc,
              kronA_BC_mul]
          exact ABCut_mul_right h2 _ _
            (isUnitary2_mul isUnitary2_I2 hA)
            (isUnitary4_mul isUnitary4_cutCNOT_AB_4 (isUnitary4_kron2 hB hC))
      · -- CX_CB : same side
        refine ⟨mB + 1, mA, by omega, ?_, ?_⟩
        · rw [singleQubitLayer_eq_kronABC]
          exact BCCut.stepCB h1 _ _ (isUnitary4_kron2 hA hB) hC
        · rw [cx_cb_eq_kronA_BC, singleQubitLayer_eq_kronA_BC, Matrix.mul_assoc,
              kronA_BC_mul]
          exact ABCut_mul_right h2 _ _
            (isUnitary2_mul isUnitary2_I2 hA)
            (isUnitary4_mul isUnitary4_CNOT_BA_4 (isUnitary4_kron2 hB hC))

/-- Mirror of `achievable_to_BCCut`. -/
theorem achievable_to_ABCut {n : ℕ} {U : Mat8} (h : AchievableCircuit n U) :
    ∃ m ≤ n, ABCut m U := by
  obtain ⟨mB, mA, hle, _, h2⟩ := achievable_to_both_cuts h
  exact ⟨mA, by omega, h2⟩

/-- **`min(mBC, mAB) ≤ 2` for `n ≤ 5`.** The form the final assembly consumes:
    5 being odd is exactly what makes one of the two counters land at or below 2.

    Both disjuncts are consumable: the analytic bound is stated for `BCCut`, and the
    right disjunct is carried across by `CutMain.ABCut_to_BCCut`, the A↔C mirror
    `ABCut m U → BCCut m (swapMatAC * U * swapMatAC)`. (That bridge was the last
    structural prerequisite; it landed in iter 1055.) -/
theorem achievable_min_cut_le_two {n : ℕ} {U : Mat8} (hn : n ≤ 5)
    (h : AchievableCircuit n U) :
    (∃ m ≤ 2, BCCut m U) ∨ (∃ m ≤ 2, ABCut m U) := by
  obtain ⟨mB, mA, hle, h1, h2⟩ := achievable_to_both_cuts h
  by_cases hb : mB ≤ 2
  · exact Or.inl ⟨mB, hb, h1⟩
  · exact Or.inr ⟨mA, by omega, h2⟩

/-! ## Downstream

The analytic bound `cut_trace_bound` and the final theorem
`achievable_trace_bound_cut` used to be stated here as `sorry`'d stubs. They have
moved to the files that can actually state them properly:

* `ApproxToffoli.CutNormalForm` — R4/R5: `BCCut_to_CZCut` and the explicit
  `trace_ccz_cut0/1/2` formulas.
* `ApproxToffoli.CutBound` — the analytic half, all of it proved:
  `cut_trace_bound_zero` (F(0)), `cut_trace_bound_one` (F(1)),
  `cut2_bound_of_PQK` (F(2), from `bridge_ineq` + `core_psi_bound`), and the
  assembly `cut_trace_bound_cz` for `m ≤ 2`.
* `ApproxToffoli.CutMain` — the A↔C mirror (`ABCut_to_BCCut`) and
  `achievable_trace_bound_cut`, which is unconditional since iter 1058.
-/

end
