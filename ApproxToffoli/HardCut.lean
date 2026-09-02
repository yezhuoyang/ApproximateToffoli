/-
  ApproxToffoli.HardCut — the eight residual `n = 7` words (the four `HardProfile`
  cut lists), and TWO independent replacements for `Block.HardBound`.

  Development copy: compiled with `lean_run_code` against `ApproxToffoli.Budget3Interior`,
  0 errors / 0 warnings.  NOT installed in the tree.

  ==============================================================================
  WHAT THIS FILE DOES
  ==============================================================================
  `Block.HardBound` (Budget3Interior §1) is the leftover analytic input for `n = 7`:
  the four cut profiles `[0,1,2,1]`, `[0,2,1,1]`, `[1,1,2,0]`, `[1,2,1,0]` that
  `IntProfile` misses because they have an INTERIOR block of CNOT-cost two.

  §1–§4  the ADJOINT symmetry of the budgeted cut form:
            `CX2.dag`           `CX2 k M → CX2 k Mᴴ`
            `BCCutC.dag`        `BCCutC ks U → BCCutC ks.reverse Uᴴ`
            `CutSqBound.reverse`  `CutSqBound ks c → CutSqBound ks.reverse c`
         (`BCCutC.dag` needs `BCCutC.step_left`, a "glue a block on the LEFT, APPEND
          its cost" constructor, since the inductive only builds on the right).
         This halves `HardBound`: `[0,1,2,1] = [1,2,1,0].reverse` and
         `[0,2,1,1] = [1,1,2,0].reverse`.

  §5  **ROUTE A — `BLB`**, on the THREE-crossing cut the tree already uses.  One
      hypothesis for all four profiles; `BLB → HardBound`.

  §6  **ROUTE B — `ICB4`**, on the FOUR-crossing MIRROR cut.  Its boundary blocks are
      FREE `U(4)`, exactly like `ICB`, so it is the literal `m = 4` analogue of `ICB`.
      It replaces `HardBound` outright: `PhiFive + ICB + ICB4 ⊢ d(7) = sin(π/8)`.

  ==============================================================================
  THE NUMERICS THAT PICKED THESE TWO STATEMENTS
  ==============================================================================
  All 256 mode assignments `(m0,m1,m2,m3) ∈ {local, cost≤1, cost≤2, U(4)}^4` of the
  three-crossing family were maximised (Gauss–Seidel, exact nuclear-norm block
  updates, 220 restarts; 0 monotonicity violations, 0 reversal-symmetry violations;
  every load-bearing TRUE entry re-confirmed independently by L-BFGS over Euler
  angles with CZ instead of CNOT).  Only four values occur: `√40`, `4+2√2`,
  `8cos(π/8)`, `8`.  The MAXIMAL assignments of value `8cos(π/8)` are exactly

      u0uu , uu0u   one INTERIOR block LOCAL, the other three free U(4)
      u11u          both interiors cost ≤ 1, boundaries free       ( = `ICB` )
      0uu0          both BOUNDARIES local, interiors free
      01u1 , 1u10   boundaries (local, cost ≤ 1), interiors (cost ≤ 1, free)
      0u11 , 11u0   boundaries (local, cost ≤ 1), interiors (free, cost ≤ 1)

  (`m0` = the RIGHTMOST block `M0`; reversal is the adjoint symmetry of §4.)  The
  four hard profiles lie under the last two lines and NOWHERE else:

      [1,2,1,0] ≤ 1u10      [0,1,2,1] ≤ 01u1
      [1,1,2,0] ≤ 11u0      [0,2,1,1] ≤ 0u11

  so `BLB` = (`1u10` ∨ `11u0`) is the exact minimal three-crossing hypothesis.  Note
  what it says: THE COST-TWO INTERIOR BLOCK IS IRRELEVANT — it may be an arbitrary
  `U(4)`.  Only three budgets are load-bearing, and each is sharp (all `= 8`):

      1211 , 1121   relaxing the LOCAL boundary to one CNOT
      2210 , 2120   relaxing the cost-one boundary to two CNOTs
      1220 , 0221   relaxing the surviving interior budget to two CNOTs

  On the FOUR-crossing mirror cut (profiles `[0,1,0,1,1]`, `[0,1,1,0,1]`,
  `[1,1,0,1,0]`, `[1,0,1,1,0]`) a frontier climb gives the maximal true relaxations
  `u101u`, `u110u` (and `u011u` by reversal) — BOUNDARIES FREE.  Sharp:

      u011u , u101u , u110u   = 8cos(π/8) = 7.3910362600903   (500 restarts)
      u111u , u1u1u           = 8   (some interior must be LOCAL)
      u201u , u121u           = 8   (the other two interiors must cost ≤ 1)

  That is `ICB4`.  There is NO reduction of the interior-cost-2 case to `ICB`:
  `(u,2,1,u) = 8`, so the three-crossing form cannot have free boundaries, and the
  `CZ·CZ = 1` splitting of the cost-2 block into a five-crossing form gives
  `110110 = 101101 = 8`.  Both routes need genuinely new analytic input.

  EQUALITY CASE (the same for `ICB`, for all four hard profiles, and for `ICB4`):
  `CCZ8 · U` has four eigenvalues at `e^{-iπ/8}` and four at `e^{+iπ/8}`; at the
  three-crossing optimum it is literally the diagonal unitary with phases
  `exp(i(π/8)(2(a ⊕ c) − 1))`.  Attained to 15 digits
  (`7.391036260090298` vs `8cos(π/8) = 7.391036260090294`).  The eight residual
  words themselves also sit exactly at `8cos(π/8)` (±5e-15), so both cut relaxations
  are tight, with no slack to spend.
-/

import ApproxToffoli.Budget3Interior

open Matrix Complex

noncomputable section

namespace Block

/-! ## 1. Adjoints of the fixed gates -/

theorem i2_conjTranspose : (I₂ : Mat2).conjTranspose = I₂ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [I₂, Matrix.conjTranspose_apply]

theorem paulix_conjTranspose : (pauliX : Mat2).conjTranspose = pauliX := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.conjTranspose_apply, Matrix.of_apply]

theorem cx_bc_conjTranspose : CX_BC.conjTranspose = CX_BC := by
  rw [CX_BC, Matrix.conjTranspose_add, kron3_conjTranspose, kron3_conjTranspose,
    i2_conjTranspose, proj0_conjTranspose, proj1_conjTranspose, paulix_conjTranspose]

theorem cx_cb_conjTranspose : CX_CB.conjTranspose = CX_CB := by
  rw [CX_CB, Matrix.conjTranspose_add, kron3_conjTranspose, kron3_conjTranspose,
    i2_conjTranspose, proj0_conjTranspose, proj1_conjTranspose, paulix_conjTranspose]

theorem cutCNOT_AB_4_conjTranspose : cutCNOT_AB_4.conjTranspose = cutCNOT_AB_4 := by
  rw [cutCNOT_AB_4, Matrix.conjTranspose_add, kron2_conjTranspose, kron2_conjTranspose,
    i2_conjTranspose, proj0_conjTranspose, proj1_conjTranspose, paulix_conjTranspose]

theorem CNOT_BA_4_conjTranspose : CNOT_BA_4.conjTranspose = CNOT_BA_4 := by
  rw [CNOT_BA_4, Matrix.conjTranspose_add, kron2_conjTranspose, kron2_conjTranspose,
    i2_conjTranspose, proj0_conjTranspose, proj1_conjTranspose, paulix_conjTranspose]

theorem kronABC_conjTranspose (M : Mat4) (c : Mat2) :
    (kronABC M c).conjTranspose = kronABC M.conjTranspose c.conjTranspose := by
  ext i j
  simp [kronABC, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul']

/-! ## 2. `CX2` is closed under the adjoint -/

/-- A CNOT glued on the LEFT costs one, exactly as on the right.  (The inductive
    `CX2.step` only glues on the right, so this has to be derived.) -/
theorem CX2.step_left {k : ℕ} {M : Mat4} (h : CX2 k M) (G : Mat4)
    (hG : G = cutCNOT_AB_4 ∨ G = CNOT_BA_4) : CX2 (k + 1) (G * M) := by
  induction h with
  | layer a b ha hb =>
      have h0 : CX2 0 (kron2 (1 : Mat2) (1 : Mat2)) :=
        CX2.layer 1 1 isUnitary2_one isUnitary2_one
      simpa [kron2_one_one] using CX2.step h0 G hG a b ha hb
  | weaken _ ih => exact ih.weaken
  | @step k M h G' hG' a b ha hb ih =>
      have e : G * (M * G' * kron2 a b) = (G * M) * G' * kron2 a b := by noncomm_ring
      rw [e]; exact CX2.step ih G' hG' a b ha hb

/-- **`CX2` is adjoint-closed.**  Reversing a two-qubit circuit and daggering every
    layer uses the same number of CNOTs (both CNOTs are Hermitian). -/
theorem CX2.dag {k : ℕ} {M : Mat4} (h : CX2 k M) : CX2 k M.conjTranspose := by
  induction h with
  | layer a b ha hb =>
      rw [kron2_conjTranspose]
      exact CX2.layer _ _ (isUnitary2_conjTranspose ha) (isUnitary2_conjTranspose hb)
  | weaken _ ih => exact ih.weaken
  | @step k M h G hG a b ha hb ih =>
      have hGH : G.conjTranspose = G := by
        rcases hG with rfl | rfl
        · exact cutCNOT_AB_4_conjTranspose
        · exact CNOT_BA_4_conjTranspose
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hGH, kron2_conjTranspose]
      exact (ih.step_left G hG).mul_layer_left _ _
        (isUnitary2_conjTranspose ha) (isUnitary2_conjTranspose hb)

/-! ## 3. `BCCutC` is adjoint-closed, with the profile REVERSED -/

/-- A crossing and a far-side block glued on the LEFT, the block's cost APPENDED to
    the profile.  (`BCCutC.step` only glues on the right, PREPENDING the cost.) -/
theorem BCCutC.step_left {ks : List ℕ} {U : Mat8} (h : BCCutC ks U) (G : Mat8)
    (hG : G = CX_BC ∨ G = CX_CB) {k : ℕ} {M : Mat4} (hM : CX2 k M)
    (c : Mat2) (hc : IsUnitary2 c) :
    BCCutC (ks ++ [k]) (kronABC M c * G * U) := by
  induction h with
  | base hM0 c0 hc0 => exact BCCutC.step (BCCutC.base hM c hc) G hG hM0 c0 hc0
  | @step ks V h G' hG' k' M' hM' c' hc' ih =>
      have e : kronABC M c * G * (V * G' * kronABC M' c')
          = (kronABC M c * G * V) * G' * kronABC M' c' := by noncomm_ring
      rw [List.cons_append, e]
      exact BCCutC.step ih G' hG' hM' c' hc'

/-- **The budgeted cut form is adjoint-closed**, with the cost profile reversed.
    Every crossing (`CX_BC`, `CX_CB`) is Hermitian, so `Uᴴ` is the same circuit read
    backwards with every block daggered, and `CX2` preserves cost under daggering. -/
theorem BCCutC.dag {ks : List ℕ} {U : Mat8} (h : BCCutC ks U) :
    BCCutC ks.reverse U.conjTranspose := by
  induction h with
  | base hM c hc =>
      rw [List.reverse_singleton, kronABC_conjTranspose]
      exact BCCutC.base hM.dag _ (isUnitary2_conjTranspose hc)
  | @step ks V h G hG k M hM c hc ih =>
      have hGH : G.conjTranspose = G := by
        rcases hG with rfl | rfl
        · exact cx_bc_conjTranspose
        · exact cx_cb_conjTranspose
      rw [List.reverse_cons, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hGH,
        kronABC_conjTranspose, ← Matrix.mul_assoc]
      exact ih.step_left G hG hM.dag _ (isUnitary2_conjTranspose hc)

/-! ## 4. `CutSqBound` is invariant under reversing the profile -/

/-- `CCZ8` is real diagonal, hence Hermitian, so daggering conjugates the objective. -/
theorem trace_ccz8_conjTranspose (U : Mat8) :
    Matrix.trace (CCZ8 * U.conjTranspose) = star (Matrix.trace (CCZ8 * U)) := by
  have e : CCZ8 * U.conjTranspose = (U * CCZ8.conjTranspose).conjTranspose := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [e, Matrix.trace_conjTranspose, ccz8_conjTranspose, Matrix.trace_mul_comm]

/-- **Reversing a cut profile does not change its bound.**  `[0,1,2,1]` is the
    reverse of `[1,2,1,0]`, and `[0,2,1,1]` the reverse of `[1,1,2,0]`, so this
    symmetry halves `HardBound`. -/
theorem CutSqBound.reverse {ks : List ℕ} {c : ℝ} (h : CutSqBound ks c) :
    CutSqBound ks.reverse c := by
  intro U hU
  have h2 : BCCutC ks U.conjTranspose := by
    have := hU.dag; rwa [List.reverse_reverse] at this
  have hb := h _ h2
  rwa [trace_ccz8_conjTranspose, Complex.star_def, Complex.normSq_conj] at hb

/-! ## 5. ROUTE A — `BLB`, on the three-crossing cut -/

/-- **`BLB` — the boundary-local bound.**  Three crossings, four far-side blocks in
    the `BCCutC` build order (`M3` leftmost, `M0` rightmost):

    * boundary `M3` is LOCAL (cost 0);
    * boundary `M0` costs at most ONE CNOT;
    * ONE interior block costs at most ONE CNOT, the OTHER is an arbitrary `U(4)`.

    TRUE and TIGHT numerically (`8cos(π/8)`, attained).  Each of the three budgets is
    load-bearing — see the module note.  NOT PROVED here. -/
def BLB : Prop :=
  ∀ (M0 M1 M2 M3 : Mat4) (c0 c1 c2 c3 : Mat2) (G1 G2 G3 : Mat8),
    CX2 0 M3 → CX2 1 M0 →
    ((CX2 1 M1 ∧ IsUnitary4 M2) ∨ (IsUnitary4 M1 ∧ CX2 1 M2)) →
    IsUnitary2 c0 → IsUnitary2 c1 → IsUnitary2 c2 → IsUnitary2 c3 →
    (G1 = CX_BC ∨ G1 = CX_CB) → (G2 = CX_BC ∨ G2 = CX_CB) →
    (G3 = CX_BC ∨ G3 = CX_CB) →
    Complex.normSq (Matrix.trace (CCZ8 *
        (kronABC M3 c3 * G3 * kronABC M2 c2 * G2 * kronABC M1 c1 * G1
          * kronABC M0 c0)))
      ≤ 64 * Real.cos (Real.pi / 8) ^ 2

/-- **`HCB`** — the literal interior-cost-two statement, with the cost-2 interior
    block written as `CX2 2` rather than relaxed to `U(4)`.  Weaker than `BLB`. -/
def HCB : Prop :=
  ∀ (M0 M1 M2 M3 : Mat4) (c0 c1 c2 c3 : Mat2) (G1 G2 G3 : Mat8),
    CX2 0 M3 → CX2 1 M0 →
    ((CX2 2 M1 ∧ CX2 1 M2) ∨ (CX2 1 M1 ∧ CX2 2 M2)) →
    IsUnitary2 c0 → IsUnitary2 c1 → IsUnitary2 c2 → IsUnitary2 c3 →
    (G1 = CX_BC ∨ G1 = CX_CB) → (G2 = CX_BC ∨ G2 = CX_CB) →
    (G3 = CX_BC ∨ G3 = CX_CB) →
    Complex.normSq (Matrix.trace (CCZ8 *
        (kronABC M3 c3 * G3 * kronABC M2 c2 * G2 * kronABC M1 c1 * G1
          * kronABC M0 c0)))
      ≤ 64 * Real.cos (Real.pi / 8) ^ 2

/-- The cost-2 predicate is never needed: `BLB` already covers `HCB`. -/
theorem HCB_of_BLB (h : BLB) : HCB := by
  intro M0 M1 M2 M3 c0 c1 c2 c3 G1 G2 G3 h3 h0 hint hc0 hc1 hc2 hc3 hG1 hG2 hG3
  refine h M0 M1 M2 M3 c0 c1 c2 c3 G1 G2 G3 h3 h0 ?_ hc0 hc1 hc2 hc3 hG1 hG2 hG3
  rcases hint with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨h1.unitary, h2⟩
  · exact Or.inl ⟨h1, h2.unitary⟩

/-- The profile of `abaabab` (and, reversed, of `babaaba`). -/
theorem cutSq_1210_of_BLB (h : BLB) :
    CutSqBound [1, 2, 1, 0] (64 * Real.cos (Real.pi / 8) ^ 2) := by
  intro U hU
  cases hU with
  | @step _ _ h1 G1 hG1 _ M0 hM0 c0 hc0 =>
    cases h1 with
    | @step _ _ h2 G2 hG2 _ M1 hM1 c1 hc1 =>
      cases h2 with
      | @step _ _ h3 G3 hG3 _ M2 hM2 c2 hc2 =>
        cases h3 with
        | @base _ M3 hM3 c3 hc3 =>
            exact h M0 M1 M2 M3 c0 c1 c2 c3 G1 G2 G3 hM3 hM0
              (Or.inr ⟨hM1.unitary, hM2⟩) hc0 hc1 hc2 hc3 hG1 hG2 hG3
        | @step _ _ h4 _ _ _ _ _ _ _ => cases h4

/-- The profile of `ababaab` (and, reversed, of `baababa`). -/
theorem cutSq_1120_of_BLB (h : BLB) :
    CutSqBound [1, 1, 2, 0] (64 * Real.cos (Real.pi / 8) ^ 2) := by
  intro U hU
  cases hU with
  | @step _ _ h1 G1 hG1 _ M0 hM0 c0 hc0 =>
    cases h1 with
    | @step _ _ h2 G2 hG2 _ M1 hM1 c1 hc1 =>
      cases h2 with
      | @step _ _ h3 G3 hG3 _ M2 hM2 c2 hc2 =>
        cases h3 with
        | @base _ M3 hM3 c3 hc3 =>
            exact h M0 M1 M2 M3 c0 c1 c2 c3 G1 G2 G3 hM3 hM0
              (Or.inl ⟨hM1, hM2.unitary⟩) hc0 hc1 hc2 hc3 hG1 hG2 hG3
        | @step _ _ h4 _ _ _ _ _ _ _ => cases h4

/-- **`BLB` gives `HardBound`.**  Two profiles directly, the other two by
    `CutSqBound.reverse`. -/
theorem hardBound_of_BLB (h : BLB) : HardBound := by
  intro ks hk
  match ks, hk with
  | [0, 1, 2, 1], _ =>
      have e : ([1, 2, 1, 0] : List ℕ).reverse = [0, 1, 2, 1] := rfl
      have := (cutSq_1210_of_BLB h).reverse
      rwa [e] at this
  | [0, 2, 1, 1], _ =>
      have e : ([1, 1, 2, 0] : List ℕ).reverse = [0, 2, 1, 1] := rfl
      have := (cutSq_1120_of_BLB h).reverse
      rwa [e] at this
  | [1, 1, 2, 0], _ => exact cutSq_1120_of_BLB h
  | [1, 2, 1, 0], _ => exact cutSq_1210_of_BLB h

/-- **`d(7) = sin(π/8)`** on `PhiFive`, `ICB`, `BLB`. -/
theorem curve_seven_of_BLB (hphi : PhiFive) (hicb : ICB) (hblb : BLB) :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 7 U ∧ hsDistance U CCX = d}
      (Real.sin (Real.pi / 8)) :=
  curve_seven_of_ICB hphi hicb (hardBound_of_BLB hblb)

/-! ## 6. ROUTE B — `ICB4`, on the four-crossing MIRROR cut -/

/-- Five far-side blocks (four crossings) whose three INTERIOR costs are all at most
    one AND at least one of which is ZERO. -/
def Int4Profile : List ℕ → Bool
  | [_, k1, k2, k3, _] => k1 ≤ 1 && k2 ≤ 1 && k3 ≤ 1 && (k1 == 0 || k2 == 0 || k3 == 0)
  | _ => false

/-- **`ICB4`** — the literal `m = 4` analogue of `ICB`: four crossings, five far-side
    blocks, the two BOUNDARY blocks arbitrary `U(4)`, the three INTERIOR blocks of
    CNOT cost at most one with at least one of them LOCAL.

    TRUE and TIGHT numerically (`8cos(π/8)`, attained; 500 restarts).  Sharp in every
    coordinate: dropping the "one interior is local" clause, or raising either of the
    other two interior budgets to two CNOTs, gives `8`.  NOT PROVED here. -/
def ICB4 : Prop :=
  ∀ (M0 M1 M2 M3 M4 : Mat4) (c0 c1 c2 c3 c4 : Mat2) (G1 G2 G3 G4 : Mat8),
    IsUnitary4 M0 → IsUnitary4 M4 →
    ((CX2 0 M1 ∧ CX2 1 M2 ∧ CX2 1 M3) ∨ (CX2 1 M1 ∧ CX2 0 M2 ∧ CX2 1 M3) ∨
      (CX2 1 M1 ∧ CX2 1 M2 ∧ CX2 0 M3)) →
    IsUnitary2 c0 → IsUnitary2 c1 → IsUnitary2 c2 → IsUnitary2 c3 → IsUnitary2 c4 →
    (G1 = CX_BC ∨ G1 = CX_CB) → (G2 = CX_BC ∨ G2 = CX_CB) →
    (G3 = CX_BC ∨ G3 = CX_CB) → (G4 = CX_BC ∨ G4 = CX_CB) →
    Complex.normSq (Matrix.trace (CCZ8 *
        (kronABC M4 c4 * G4 * kronABC M3 c3 * G3 * kronABC M2 c2 * G2
          * kronABC M1 c1 * G1 * kronABC M0 c0)))
      ≤ 64 * Real.cos (Real.pi / 8) ^ 2

theorem cutSq_of_int4Profile (h : ICB4) {ks : List ℕ} (hk : Int4Profile ks = true) :
    CutSqBound ks (64 * Real.cos (Real.pi / 8) ^ 2) := by
  match ks, hk with
  | [k0, k1, k2, k3, k4], hk =>
    simp only [Int4Profile, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      beq_iff_eq] at hk
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, hz⟩ := hk
    intro U hU
    cases hU with
    | @step _ _ e1 G1 hG1 _ M0 hM0 c0 hc0 =>
      cases e1 with
      | @step _ _ e2 G2 hG2 _ M1 hM1 c1 hc1 =>
        cases e2 with
        | @step _ _ e3 G3 hG3 _ M2 hM2 c2 hc2 =>
          cases e3 with
          | @step _ _ e4 G4 hG4 _ M3 hM3 c3 hc3 =>
            cases e4 with
            | @base _ M4 hM4 c4 hc4 =>
                refine h M0 M1 M2 M3 M4 c0 c1 c2 c3 c4 G1 G2 G3 G4
                  hM0.unitary hM4.unitary ?_ hc0 hc1 hc2 hc3 hc4 hG1 hG2 hG3 hG4
                rcases hz with (hz | hz) | hz
                · exact Or.inl ⟨hz ▸ hM1, hM2.mono h2, hM3.mono h3⟩
                · exact Or.inr (Or.inl ⟨hM1.mono h1, hz ▸ hM2, hM3.mono h3⟩)
                · exact Or.inr (Or.inr ⟨hM1.mono h1, hM2.mono h2, hz ▸ hM3⟩)
            | @step _ _ e5 _ _ _ _ _ _ _ => cases e5

/-- **The `n = 7` enumeration, mirror-cut version.**  Every word of length ≤ 7 with
    ≥ 6 runs has, on one of its two cuts, either an `IntProfile` (three crossings) or
    an `Int4Profile` (four crossings).  The eight words `HardProfile` was invented for
    land in the SECOND class on their OTHER cut:

        abaabab → [0,1,0,1,1]     ababaab → [0,1,1,0,1]
        ababbab → [1,1,0,1,0]     abbabab → [1,0,1,1,0]      (+ the four mirrors) -/
theorem word_profile_seven_alt : ∀ w : List Bool, w.length ≤ 7 → 6 ≤ runs w →
    IntProfile (cutCosts true w) = true ∨ IntProfile (cutCosts false w) = true ∨
    Int4Profile (cutCosts true w) = true ∨ Int4Profile (cutCosts false w) = true := by
  intro w
  match w with
  | [] => intro _ h; simp [runs] at h
  | [a] => revert a; decide
  | [a, b] => revert a b; decide
  | [a, b, c] => revert a b c; decide
  | [a, b, c, d] => revert a b c d; decide
  | [a, b, c, d, e] => revert a b c d e; decide
  | [a, b, c, d, e, f] => revert a b c d e f; decide
  | [a, b, c, d, e, f, g] => revert a b c d e f g; decide
  | a :: b :: c :: d :: e :: f :: g :: h :: t =>
      intro hl; simp at hl; exfalso; omega

theorem word_residual_seven_alt {w : List Bool} {U : Mat8} (hw : CXWord w U)
    (hlen : w.length ≤ 7) (hr : 6 ≤ runs w) :
    ∃ (ks : List ℕ) (W : Mat8),
      (IntProfile ks = true ∨ Int4Profile ks = true) ∧ BCCutC ks W ∧
      Complex.normSq (Matrix.trace (Uᴴ * CCX))
        = Complex.normSq (Matrix.trace (CCZ8 * W)) := by
  have mk : ∀ p : Bool, ∃ W : Mat8, BCCutC (cutCosts p w) W ∧
      Complex.normSq (Matrix.trace (Uᴴ * CCX))
        = Complex.normSq (Matrix.trace (CCZ8 * W)) := by
    intro p
    cases p with
    | true =>
        exact ⟨kron3 1 1 Hgate * U * kron3 1 1 Hgate,
          ((cxWord_to_BCCutC hw).mul_layer_left 1 1 Hgate isUnitary2_one isUnitary2_one
              hgate_unitary).mul_layer_right 1 1 Hgate isUnitary2_one isUnitary2_one
              hgate_unitary,
          normSq_trace_ccx_eq U⟩
    | false =>
        refine ⟨kron3 Hgate 1 1 * (swapMatAC * U * swapMatAC) * kron3 Hgate 1 1, ?_, ?_⟩
        · have h1 := cxWord_to_BCCutC (cxWord_mirror hw)
          rw [cutCosts_map_not] at h1
          exact (h1.mul_layer_left Hgate 1 1 hgate_unitary isUnitary2_one
            isUnitary2_one).mul_layer_right Hgate 1 1 hgate_unitary isUnitary2_one
            isUnitary2_one
        · rw [normSq_trace_ccx_eq U, mirror_trace_eq]
  rcases word_profile_seven_alt w hlen hr with hg | hg | hg | hg
  · obtain ⟨W, hW, he⟩ := mk true; exact ⟨_, W, Or.inl hg, hW, he⟩
  · obtain ⟨W, hW, he⟩ := mk false; exact ⟨_, W, Or.inl hg, hW, he⟩
  · obtain ⟨W, hW, he⟩ := mk true; exact ⟨_, W, Or.inr hg, hW, he⟩
  · obtain ⟨W, hW, he⟩ := mk false; exact ⟨_, W, Or.inr hg, hW, he⟩

/-- **The `n ≤ 7` trace bound** on `PhiFive`, `ICB`, `ICB4` — `HardBound` is not
    used at all. -/
theorem achievable_trace_bound_seven_of_ICB4 (hphi : PhiFive) (hicb : ICB)
    (hicb4 : ICB4) {n : ℕ} (hn : n ≤ 7) {U : Mat8} (h : AchievableCircuit n U) :
    Complex.normSq (Matrix.trace (Uᴴ * CCX)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2 := by
  obtain ⟨w, hlen, hw⟩ := exists_cxWord h
  by_cases hr : runs w ≤ 5
  · exact trace_bound_of_runs_le_five hphi hw hr
  · obtain ⟨ks, W, hg, hcut, heq⟩ :=
      word_residual_seven_alt hw (le_trans hlen hn) (by omega)
    rw [heq]
    rcases hg with hg | hg
    · exact cutSq_of_intProfile hicb hg W hcut
    · exact cutSq_of_int4Profile hicb4 hg W hcut

/-- **`d(7) = sin(π/8)`** on `PhiFive`, `ICB`, `ICB4`. -/
theorem curve_seven_of_ICB4 (hphi : PhiFive) (hicb : ICB) (hicb4 : ICB4) :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 7 U ∧ hsDistance U CCX = d}
      (Real.sin (Real.pi / 8)) := by
  constructor
  · exact ⟨Curve.witness4,
      AchievableCircuit.weaken (AchievableCircuit.weaken
        (AchievableCircuit.weaken Curve.witness4_achievable)),
      Curve.witness4_distance⟩
  · rintro d ⟨U, hU, rfl⟩
    exact trace_bound_implies_distance U
      (achievable_trace_bound_seven_of_ICB4 hphi hicb hicb4 (by norm_num) hU)

/-- **`d(6)` and `d(7)`**, from `PhiFive` and `ICB` plus EITHER of the two new
    hypotheses. -/
theorem curve_six_seven_of_ICB4 (hphi : PhiFive) (hicb : ICB) (hicb4 : ICB4) :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 6 U ∧ hsDistance U CCX = d}
        (Real.sin (Real.pi / 8)) ∧
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 7 U ∧ hsDistance U CCX = d}
        (Real.sin (Real.pi / 8)) :=
  ⟨curve_six_of_ICB hphi hicb, curve_seven_of_ICB4 hphi hicb hicb4⟩

end Block

end
