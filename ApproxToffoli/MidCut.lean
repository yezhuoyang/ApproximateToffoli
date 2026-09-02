/-
  ApproxToffoli.MidCut

  **The `n = 6` residual, reduced to ONE circuit-free hypothesis on TWO blocks.**

  `BlockResidual` leaves `n = 6, 7` on two hypotheses, `PhiFive` and `Budget3`.
  This file replaces `Budget3` — for `n = 6` — by the strictly weaker `Mid3Bound`:

      three crossings, four far-side blocks, and a CNOT budget of at most one on
      the TWO MIDDLE blocks ONLY; the two outer blocks are arbitrary `U(4)`.

  Why the outer budgets can be dropped, and why the middle two cannot: the maximum
  of `|Tr(CCZ·U)|` over the four-block, three-crossing family is

      both middles budgeted, outers free   ->  8cos(pi/8) = 7.391036260090 3   (TIGHT)
      only ONE middle budgeted             ->  8                              (FALSE)
      only the outers budgeted             ->  8                              (FALSE)
      nothing budgeted                     ->  8                              (FALSE)

  (Gauss-Seidel with exact nuclear-norm block updates, cross-checked by an
  independent L-BFGS/Euler-angle optimiser; agreement to 5e-14.)  So `Mid3Bound` is
  sharp, and any proof of it that fails to consume BOTH middle budgets is wrong.

  The maximiser is EXACT and is a diagonal unitary:

      U* = CCZ . diag( exp( i (pi/4) (a XOR c) ) ),      Tr(CCZ U*) = 4 + 4 e^{i pi/4},

  i.e. `CCZ` composed with a pi/4 phase on the parity of the two END qubits — the
  non-adjacent pair.  `|4 + 4 e^{i pi/4}| = 8cos(pi/8)`.

  ## Contents

  1. `CZCutC` — the budgeted cut form with the C-block-diagonal crossing `CZBC8`,
     and `BCCutC.toCZCutC`: **R4 preserves the budget** (the Hadamards that
     diagonalise `CX_BC` / `CX_CB` are free single-qubit layers).
  2. `CX2.one_cost1` — the `BlockResidual` budget predicate at cost one IS the
     `OneGate` normal form `Cost1U4`, so `Cost1.phi_cost1` applies to far-side blocks.
  3. `CZCutC.unfold_four` — the explicit four-block normal form.
  4. `trace_ccz_cut3` — **R5 at m = 3**: the sixteen-term trace formula, derived by
     peeling one crossing onto the tree's `trace_ccz_cut2`.
  5. `Mid3Bound`, `cutSqBound_of_mid3` — the reduction.
  6. `MidProfile`, `word_profile_mid` — the `n = 6` enumeration.  This step is
     genuinely `n = 6` only: at length 7 the word `abaabab` has profile `[1,2,1,0]`,
     whose MIDDLE cost is 2.
  7. `achievable_trace_bound_six_mid`, `curve_six_mid` — the assembly.

  `Mid3Bound` itself is NOT proved here.  It is the whole remaining gap for `n = 6`.
-/

import ApproxToffoli.BlockResidual
import ApproxToffoli.OneGate

open Matrix Complex

noncomputable section

namespace Block

/-! ## 1. The budgeted CZ cut form (R4 with the budget) -/

/-- The budgeted cut form with the C-block-DIAGONAL crossing gate `CZBC8`. -/
inductive CZCutC : List ℕ → Mat8 → Prop where
  | base {k : ℕ} {M : Mat4} (hM : CX2 k M) (c : Mat2) (hc : IsUnitary2 c) :
      CZCutC [k] (kronABC M c)
  | step {ks : List ℕ} {U : Mat8} (h : CZCutC ks U) {k : ℕ} {M : Mat4}
      (hM : CX2 k M) (c : Mat2) (hc : IsUnitary2 c) :
      CZCutC (k :: ks) (U * CZBC8 * kronABC M c)

theorem CZCutC.cost_ne_nil {ks : List ℕ} {U : Mat8} (h : CZCutC ks U) : ks ≠ [] := by
  cases h <;> simp

/-- A free single-qubit layer on the right does not consume budget. -/
theorem CZCutC.mul_layer_right {ks : List ℕ} {U : Mat8} (h : CZCutC ks U) :
    ∀ (a b c : Mat2), IsUnitary2 a → IsUnitary2 b → IsUnitary2 c →
      CZCutC ks (U * kron3 a b c) := by
  induction h with
  | base hM c₀ hc₀ =>
      intro a b c ha hb hc
      rw [kron3_eq_kronABC, kronABC_mul]
      exact CZCutC.base (hM.mul_layer_right a b ha hb) _ (isUnitary2_mul hc₀ hc)
  | @step ks U h k M hM c₀ hc₀ ih =>
      intro a b c ha hb hc
      rw [show U * CZBC8 * kronABC M c₀ * kron3 a b c
            = U * CZBC8 * kronABC (M * kron2 a b) (c₀ * c) from by
        rw [kron3_eq_kronABC, Matrix.mul_assoc (U * CZBC8), kronABC_mul]]
      exact CZCutC.step h (hM.mul_layer_right a b ha hb) _ (isUnitary2_mul hc₀ hc)

/-- **R4, WITH the budget.**  The Hadamards that turn `CX_BC` / `CX_CB` into the
    C-block-diagonal `CZBC8` are free single-qubit layers, so they are absorbed into
    the far-side blocks without consuming any of the CNOT budget.  (The tree's
    `BCCut_to_CZCut` forgets the budget; this is the refinement that keeps it.) -/
theorem BCCutC.toCZCutC {ks : List ℕ} {U : Mat8} (h : BCCutC ks U) : CZCutC ks U := by
  induction h with
  | base hM c hc => exact CZCutC.base hM c hc
  | @step ks U hrest G hG k M hM c hc ih =>
      rcases hG with rfl | rfl
      · have e : U * CX_BC * kronABC M c
            = (U * kron3 1 1 Hgate) * CZBC8 * kronABC (1 * M) (Hgate * c) := by
          rw [hC_eq_kronABC, cx_bc_eq_cz_conj, ← kronABC_mul]; noncomm_ring
        rw [e]
        exact CZCutC.step
          (ih.mul_layer_right 1 1 Hgate isUnitary2_one isUnitary2_one hgate_unitary)
          (by rw [Matrix.one_mul]; exact hM) _ (isUnitary2_mul hgate_unitary hc)
      · have e : U * CX_CB * kronABC M c
            = (U * kron3 1 Hgate 1) * CZBC8 * kronABC (kron2 1 Hgate * M) (1 * c) := by
          rw [show kron3 1 Hgate 1 = kronABC (kron2 1 Hgate) 1 from
                kron3_eq_kronABC _ _ _,
            cx_cb_eq_cz_conj, ← kronABC_mul]
          noncomm_ring
        rw [e]
        exact CZCutC.step
          (ih.mul_layer_right 1 Hgate 1 isUnitary2_one hgate_unitary isUnitary2_one)
          (hM.mul_layer_left 1 Hgate isUnitary2_one hgate_unitary) _
          (isUnitary2_mul isUnitary2_one hc)

/-! ## 2. The budget predicate at cost 0 and 1 -/

/-- A zero-budget two-qubit circuit is a single-qubit layer. -/
theorem CX2.zero_local {M : Mat4} (h : CX2 0 M) :
    ∃ a b : Mat2, IsUnitary2 a ∧ IsUnitary2 b ∧ M = kron2 a b := by
  cases h with
  | layer a b ha hb => exact ⟨a, b, ha, hb, rfl⟩

/-- **Budget one IS `Cost1U4`.**  `BlockResidual`'s `CX2` and `OneGate`'s `Cost1U4`
    agree at cost one, so all the cost-one machinery of `OneGate` — in particular
    the sharp `Cost1.phi_cost1 : ‖Tr M‖ + ‖Tr(Z' M)‖ ≤ 6` — applies to the far-side
    blocks of a budgeted cut. -/
theorem CX2.one_cost1 {M : Mat4} (h : CX2 1 M) : Cost1.Cost1U4 M := by
  cases h with
  | weaken h0 =>
      obtain ⟨a, b, ha, hb, rfl⟩ := CX2.zero_local h0
      exact Cost1.Cost1U4.zero a b ha hb
  | step h0 G hG a b ha hb =>
      obtain ⟨x, y, hx, hy, rfl⟩ := CX2.zero_local h0
      rcases hG with rfl | rfl
      · exact Cost1.Cost1U4_mul_right
          (Cost1.Cost1U4_mul_left Cost1.cost1_cnotAB hx hy) ha hb
      · exact Cost1.Cost1U4_mul_right
          (Cost1.Cost1U4_mul_left Cost1.cost1_cnotBA hx hy) ha hb

theorem CX2.cost1_of_le_one {k : ℕ} {M : Mat4} (h : CX2 k M) (hk : k ≤ 1) :
    Cost1.Cost1U4 M := (h.mono hk (j := k) (k := 1)).one_cost1

/-! ## 3. The four-block normal form -/

/-- **The four-block normal form.**  `ks` is head-first, i.e. RIGHTMOST factor first,
    so `[k₃, k₂, k₁, k₀]` reads left to right as costs `k₀ k₁ k₂ k₃`. -/
theorem CZCutC.unfold_four {k0 k1 k2 k3 : ℕ} {U : Mat8}
    (h : CZCutC [k3, k2, k1, k0] U) :
    ∃ (M0 M1 M2 M3 : Mat4) (c0 c1 c2 c3 : Mat2),
      CX2 k0 M0 ∧ CX2 k1 M1 ∧ CX2 k2 M2 ∧ CX2 k3 M3 ∧
      IsUnitary2 c0 ∧ IsUnitary2 c1 ∧ IsUnitary2 c2 ∧ IsUnitary2 c3 ∧
      U = kronABC M0 c0 * CZBC8 * kronABC M1 c1 * CZBC8 * kronABC M2 c2
            * CZBC8 * kronABC M3 c3 := by
  cases h with
  | @step _ V h3 _ M3 hM3 c3 hc3 =>
    cases h3 with
    | @step _ W h2 _ M2 hM2 c2 hc2 =>
      cases h2 with
      | @step _ X h1 _ M1 hM1 c1 hc1 =>
        cases h1 with
        | base hM0 c0 hc0 =>
            exact ⟨_, M1, M2, M3, c0, c1, c2, c3, hM0, hM1, hM2, hM3,
              hc0, hc1, hc2, hc3, rfl⟩
        | @step _ Y hnil _ _ _ _ _ => exact absurd rfl hnil.cost_ne_nil

/-! ## 4. R5 at `m = 3` : the sixteen-term trace formula -/

/-- One crossing peeled off the right end.  `CZBC8` is a sum of two C-block terms,
    so a four-block cut form is a sum of two three-block cut forms — which is how the
    sixteen terms are obtained from the tree's eight. -/
lemma cut_peel (V : Mat8) (M2 M3 : Mat4) (c2 c3 : Mat2) :
    V * kronABC M2 c2 * CZBC8 * kronABC M3 c3
      = V * kronABC (M2 * M3) (c2 * proj0 * c3)
        + V * kronABC (M2 * Zhat4 * M3) (c2 * proj1 * c3) := by
  rw [CZBC8]
  simp only [Matrix.mul_add, Matrix.add_mul, kronABC_mul, Matrix.mul_one,
    Matrix.mul_assoc]

lemma p0_sandwich (a b : Mat2) (i j : Fin 2) : (a * proj0 * b) i j = a i 0 * b 0 j := by
  simp [proj0, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]

lemma p1_sandwich (a b : Mat2) (i j : Fin 2) : (a * proj1 * b) i j = a i 1 * b 1 j := by
  simp [proj1, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]

set_option maxHeartbeats 1000000 in
-- Heartbeat bump: sixteen products of four `Mat2` entries with a `Mat4` trace each,
-- closed by a single `ring` over the peeled `trace_ccz_cut2` pair.
/-- **R5, m = 3.**  Sixteen terms: the C-index traverses the closed path
    `i → α → β → γ → i`, contributing `c₀ i α · c₁ α β · c₂ β γ · c₃ γ i`, and the
    `Mat4` factor is `Z'ⁱ M₀ Ẑᵅ M₁ Ẑᵝ M₂ Ẑᵞ M₃`.  Setting
    `K = M₀M₁M₂M₃`, `Q₁ = M₀ Ẑ M₀ᴴ`, `Q₂ = M₀M₁ Ẑ M₁ᴴM₀ᴴ`, `P = M₃ᴴ Ẑ M₃` the
    sixteen `Mat4` traces are exactly `Tr(Z'ⁱ Q₁ᵅ Q₂ᵝ K Pᵞ)` — the `m = 3` analogue
    of the `Tr(Z'ⁱ Qᵃ K Pᵇ)` of `CutBound`. -/
lemma trace_ccz_cut3 (M0 M1 M2 M3 : Mat4) (c0 c1 c2 c3 : Mat2) :
    Matrix.trace (CCZ8 * kronABC M0 c0 * CZBC8 * kronABC M1 c1 * CZBC8
        * kronABC M2 c2 * CZBC8 * kronABC M3 c3)
      = c0 0 0 * c1 0 0 * c2 0 0 * c3 0 0 * (M0 * M1 * (M2 * M3)).trace
      + c0 0 0 * c1 0 1 * c2 1 0 * c3 0 0 * (M0 * M1 * Zhat4 * (M2 * M3)).trace
      + c0 0 1 * c1 1 0 * c2 0 0 * c3 0 0 * (M0 * Zhat4 * M1 * (M2 * M3)).trace
      + c0 0 1 * c1 1 1 * c2 1 0 * c3 0 0 * (M0 * Zhat4 * M1 * Zhat4 * (M2 * M3)).trace
      + c0 1 0 * c1 0 0 * c2 0 0 * c3 0 1 * (Zp4 * M0 * M1 * (M2 * M3)).trace
      + c0 1 0 * c1 0 1 * c2 1 0 * c3 0 1 * (Zp4 * M0 * M1 * Zhat4 * (M2 * M3)).trace
      + c0 1 1 * c1 1 0 * c2 0 0 * c3 0 1 * (Zp4 * M0 * Zhat4 * M1 * (M2 * M3)).trace
      + c0 1 1 * c1 1 1 * c2 1 0 * c3 0 1
          * (Zp4 * M0 * Zhat4 * M1 * Zhat4 * (M2 * M3)).trace
      + c0 0 0 * c1 0 0 * c2 0 1 * c3 1 0 * (M0 * M1 * (M2 * Zhat4 * M3)).trace
      + c0 0 0 * c1 0 1 * c2 1 1 * c3 1 0 * (M0 * M1 * Zhat4 * (M2 * Zhat4 * M3)).trace
      + c0 0 1 * c1 1 0 * c2 0 1 * c3 1 0 * (M0 * Zhat4 * M1 * (M2 * Zhat4 * M3)).trace
      + c0 0 1 * c1 1 1 * c2 1 1 * c3 1 0
          * (M0 * Zhat4 * M1 * Zhat4 * (M2 * Zhat4 * M3)).trace
      + c0 1 0 * c1 0 0 * c2 0 1 * c3 1 1 * (Zp4 * M0 * M1 * (M2 * Zhat4 * M3)).trace
      + c0 1 0 * c1 0 1 * c2 1 1 * c3 1 1
          * (Zp4 * M0 * M1 * Zhat4 * (M2 * Zhat4 * M3)).trace
      + c0 1 1 * c1 1 0 * c2 0 1 * c3 1 1
          * (Zp4 * M0 * Zhat4 * M1 * (M2 * Zhat4 * M3)).trace
      + c0 1 1 * c1 1 1 * c2 1 1 * c3 1 1
          * (Zp4 * M0 * Zhat4 * M1 * Zhat4 * (M2 * Zhat4 * M3)).trace := by
  rw [cut_peel, Matrix.trace_add, trace_ccz_cut2, trace_ccz_cut2]
  simp only [p0_sandwich, p1_sandwich]
  ring

/-! ## 5. The reduced analytic hypothesis -/

/-- **(MID3) — the reduced analytic input.**  Three crossings, four far-side blocks,
    and a CNOT budget on the TWO MIDDLE blocks ONLY; the two OUTER blocks are
    arbitrary `U(4)`.

    NOT PROVED here; this is the whole remaining gap for `n = 6`.

    TIGHT, and the budget is load-bearing: the maximum of `|Tr(CCZ·U)|` over this
    family is exactly `8cos(π/8)`, attained at the diagonal unitary
    `CCZ · diag(exp(i(π/4)(a ⊕ c)))`, whereas dropping EITHER of the two middle
    budgets raises it to `8` (so the statement becomes FALSE).  Any proof that does
    not consume BOTH `Cost1U4` hypotheses is therefore wrong. -/
def Mid3Bound (c : ℝ) : Prop :=
  ∀ (M0 M1 M2 M3 : Mat4) (c0 c1 c2 c3 : Mat2),
    IsUnitary4 M0 → Cost1.Cost1U4 M1 → Cost1.Cost1U4 M2 → IsUnitary4 M3 →
    IsUnitary2 c0 → IsUnitary2 c1 → IsUnitary2 c2 → IsUnitary2 c3 →
    Complex.normSq (Matrix.trace (CCZ8 * kronABC M0 c0 * CZBC8 * kronABC M1 c1
        * CZBC8 * kronABC M2 c2 * CZBC8 * kronABC M3 c3)) ≤ c

/-- **`Mid3Bound` gives the budgeted cut bound for every four-block profile whose two
    middle costs are at most one** — no constraint at all on the two outer blocks. -/
theorem cutSqBound_of_mid3 {c : ℝ} (h : Mid3Bound c) {k0 k1 k2 k3 : ℕ}
    (h1 : k1 ≤ 1) (h2 : k2 ≤ 1) : CutSqBound [k3, k2, k1, k0] c := by
  intro U hU
  obtain ⟨M0, M1, M2, M3, c0, c1, c2, c3, hM0, hM1, hM2, hM3,
    hc0, hc1, hc2, hc3, rfl⟩ := hU.toCZCutC.unfold_four
  simpa only [← Matrix.mul_assoc] using
    h M0 M1 M2 M3 c0 c1 c2 c3 hM0.unitary (hM1.cost1_of_le_one h1)
      (hM2.cost1_of_le_one h2) hM3.unitary hc0 hc1 hc2 hc3

/-- The profile of `ababab`, i.e. the ENTIRE residual of `n = 6`. -/
theorem cutSqBound_1110_of_mid3 {c : ℝ} (h : Mid3Bound c) :
    CutSqBound [1, 1, 1, 0] c := cutSqBound_of_mid3 h le_rfl le_rfl

/-- The profile of `bababa`, the mirror word. -/
theorem cutSqBound_0111_of_mid3 {c : ℝ} (h : Mid3Bound c) :
    CutSqBound [0, 1, 1, 1] c := cutSqBound_of_mid3 h le_rfl le_rfl

/-- `abababa`. -/
theorem cutSqBound_1111_of_mid3 {c : ℝ} (h : Mid3Bound c) :
    CutSqBound [1, 1, 1, 1] c := cutSqBound_of_mid3 h le_rfl le_rfl

/-- `aababab`. -/
theorem cutSqBound_2110_of_mid3 {c : ℝ} (h : Mid3Bound c) :
    CutSqBound [2, 1, 1, 0] c := cutSqBound_of_mid3 h le_rfl le_rfl

/-! ## 6. The `n = 6` enumeration -/

/-- Four far-side blocks whose two MIDDLE costs are at most one. -/
def MidProfile (ks : List ℕ) : Prop :=
  ks.length = 4 ∧ ks[1]! ≤ 1 ∧ ks[2]! ≤ 1

instance : DecidablePred MidProfile := by
  intro ks; unfold MidProfile; infer_instance

theorem midProfile_iff {ks : List ℕ} :
    MidProfile ks ↔ ∃ k0 k1 k2 k3 : ℕ, ks = [k3, k2, k1, k0] ∧ k1 ≤ 1 ∧ k2 ≤ 1 := by
  constructor
  · rintro ⟨hl, h1, h2⟩
    match ks with
    | [a, b, c, d] => exact ⟨d, c, b, a, rfl, by simpa using h2, by simpa using h1⟩
  · rintro ⟨k0, k1, k2, k3, rfl, h1, h2⟩
    exact ⟨rfl, by simpa using h2, by simpa using h1⟩

/-- **THE `n = 6` ENUMERATION.**  A word of length at most SIX with at least six runs
    is fully alternating (`ababab` or `bababa`), so on one of the two cuts it has four
    far-side blocks whose two MIDDLE costs are at most one — profiles `[1,1,1,0]`
    and `[0,1,1,1]`.

    This step is `n = 6` ONLY.  At length 7 it is FALSE: `abaabab` has cut profiles
    `[1,2,1,0]` and `[0,1,0,1,1]`, and `[1,2,1,0]` has middle cost 2.  (Seven distinct
    profiles occur at length 7, not the three named in `BlockResidual`'s docstring:
    `[0,1,1,2]`, `[0,1,2,1]`, `[0,2,1,1]`, `[1,1,1,1]`, `[1,1,2,0]`, `[1,2,1,0]`,
    `[2,1,1,0]`.  All are `GoodProfile`, so `word_profile` is unaffected.) -/
theorem word_profile_mid : ∀ w : List Bool, w.length ≤ 6 → 6 ≤ runs w →
    MidProfile (cutCosts true w) ∨ MidProfile (cutCosts false w) := by
  intro w
  match w with
  | [] => intro _ h; simp [runs] at h
  | [a] => revert a; decide
  | [a, b] => revert a b; decide
  | [a, b, c] => revert a b c; decide
  | [a, b, c, d] => revert a b c d; decide
  | [a, b, c, d, e] => revert a b c d e; decide
  | [a, b, c, d, e, f] => revert a b c d e f; decide
  | a :: b :: c :: d :: e :: f :: g :: t =>
      intro hl; simp at hl; exfalso; omega

/-- The `n = 6` residual, in the `MidProfile` form. -/
theorem word_residual_midc {w : List Bool} {U : Mat8} (hw : CXWord w U)
    (hlen : w.length ≤ 6) (hr : 6 ≤ runs w) :
    ∃ (ks : List ℕ) (W : Mat8), MidProfile ks ∧ BCCutC ks W ∧
      Complex.normSq (Matrix.trace (Uᴴ * CCX))
        = Complex.normSq (Matrix.trace (CCZ8 * W)) := by
  rcases word_profile_mid w hlen hr with hg | hg
  · exact ⟨cutCosts true w, kron3 1 1 Hgate * U * kron3 1 1 Hgate, hg,
      ((cxWord_to_BCCutC hw).mul_layer_left 1 1 Hgate isUnitary2_one isUnitary2_one
          hgate_unitary).mul_layer_right 1 1 Hgate isUnitary2_one isUnitary2_one
          hgate_unitary,
      normSq_trace_ccx_eq U⟩
  · refine ⟨cutCosts false w,
      kron3 Hgate 1 1 * (swapMatAC * U * swapMatAC) * kron3 Hgate 1 1, hg, ?_, ?_⟩
    · have h1 := cxWord_to_BCCutC (cxWord_mirror hw)
      rw [cutCosts_map_not] at h1
      exact (h1.mul_layer_left Hgate 1 1 hgate_unitary isUnitary2_one
        isUnitary2_one).mul_layer_right Hgate 1 1 hgate_unitary isUnitary2_one
        isUnitary2_one
    · rw [normSq_trace_ccx_eq U, mirror_trace_eq]

/-! ## 7. The assembly -/

/-- **The `n ≤ 6` trace bound**, on `PhiFive` and `Mid3Bound` — no `Budget3`. -/
theorem achievable_trace_bound_six_mid (hphi : PhiFive)
    (hmid : Mid3Bound (64 * Real.cos (Real.pi / 8) ^ 2))
    {n : ℕ} (hn : n ≤ 6) {U : Mat8} (h : AchievableCircuit n U) :
    Complex.normSq (Matrix.trace (Uᴴ * CCX)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2 := by
  obtain ⟨w, hlen, hw⟩ := exists_cxWord h
  by_cases hr : runs w ≤ 5
  · exact trace_bound_of_runs_le_five hphi hw hr
  · obtain ⟨ks, W, hg, hcut, heq⟩ := word_residual_midc hw (le_trans hlen hn) (by omega)
    obtain ⟨k0, k1, k2, k3, rfl, h1, h2⟩ := midProfile_iff.mp hg
    rw [heq]
    exact cutSqBound_of_mid3 hmid h1 h2 W hcut

/-- **`d(6) = sin(π/8)`**, on `PhiFive` and `Mid3Bound`.  Strictly weaker hypotheses
    than `Block.curve_six`, which needs the full `Budget3`. -/
theorem curve_six_mid (hphi : PhiFive)
    (hmid : Mid3Bound (64 * Real.cos (Real.pi / 8) ^ 2)) :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 6 U ∧ hsDistance U CCX = d}
      (Real.sin (Real.pi / 8)) := by
  constructor
  · exact ⟨Curve.witness4,
      AchievableCircuit.weaken (AchievableCircuit.weaken Curve.witness4_achievable),
      Curve.witness4_distance⟩
  · rintro d ⟨U, hU, rfl⟩
    exact trace_bound_implies_distance U
      (achievable_trace_bound_six_mid hphi hmid (by norm_num) hU)

/-- `Mid3Bound` also delivers `Budget3` on the three profiles of `BlockResidual`'s
    non-vacuity witnesses, so it subsumes that part of `Budget3` outright. -/
theorem budget3_on_named_profiles
    (hmid : Mid3Bound (64 * Real.cos (Real.pi / 8) ^ 2)) :
    CutSqBound [1, 1, 1, 0] (64 * Real.cos (Real.pi / 8) ^ 2) ∧
    CutSqBound [1, 1, 1, 1] (64 * Real.cos (Real.pi / 8) ^ 2) ∧
    CutSqBound [2, 1, 1, 0] (64 * Real.cos (Real.pi / 8) ^ 2) :=
  ⟨cutSqBound_1110_of_mid3 hmid, cutSqBound_1111_of_mid3 hmid,
    cutSqBound_2110_of_mid3 hmid⟩

/-! ## 8. The conjectured `m = 3` core

The structure of the maximiser says what a proof should aim at.  At the optimum ALL
FOUR `U(2)` layers `c₀ c₁ c₂ c₃` are permutation-like (each is diagonal or
antidiagonal with unit-modulus entries), so the C-index follows a SINGLE
deterministic path and the sixteen-term sum collapses to exactly TWO terms,

    tau(0, a, b, g)  and  tau(1, 1-a, 1-b, 1-g),

each of modulus `4cos(pi/8) = sqrt(8 + 4 sqrt 2) = 3.6955`, summing to `8cos(pi/8)`.
Absorbing the `Zhat`s into the neighbouring blocks normalises `(a,b,g)` to `(0,0,0)`,
which gives `Core3Bound` below.  Also observed at the optimum: `Phi(M_j)` is far from
its cost-one bound 6 (values 0.3 - 2.2), so `Cost1.phi_cost1` is NOT the tight
constraint — the budget acts structurally, not through `Phi`.
-/

lemma zhat4_eq_kron2 : Zhat4 = kron2 1 pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Zhat4, kron2, pauliZ, Matrix.one_apply, Matrix.of_apply]

lemma isUnitary2_pauliZ : IsUnitary2 pauliZ := by
  unfold IsUnitary2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]

/-- `Zhat4 = I ⊗ Z` is a free single-qubit layer, so it does not change CNOT cost. -/
lemma Cost1U4_zhat_right {M : Mat4} (h : Cost1.Cost1U4 M) :
    Cost1.Cost1U4 (M * Zhat4) := by
  rw [zhat4_eq_kron2]
  exact Cost1.Cost1U4_mul_right h isUnitary2_one isUnitary2_pauliZ

lemma Cost1U4_zhat_left {M : Mat4} (h : Cost1.Cost1U4 M) :
    Cost1.Cost1U4 (Zhat4 * M) := by
  rw [zhat4_eq_kron2]
  exact Cost1.Cost1U4_mul_left h isUnitary2_one isUnitary2_pauliZ

/-- **(CORE3)** — the conjectured `m = 3` core, the exact analogue of
    `Cost1.phi_cost1` (`m = 0`) and `CutBound.core_psi_bound` (`m = 2`) one crossing
    further out.

    NOT PROVED.  Numerically TIGHT — the maximum is exactly `8cos(π/8)`, attained —
    and FALSE without BOTH middle budgets: L-BFGS over Euler angles, 250 restarts,

        [u4, c1, c1, u4]  ->  7.391036260090   ( = 8cos(π/8) )
        [u4, c1, u4, u4]  ->  8
        [u4, u4, c1, c1]  ->  8
        [u4, u4, u4, u4]  ->  8

    WARNING.  `Core3Bound` does NOT obviously imply `Mid3Bound`: the naive bridge
    `|T| ≤ maxₐᵦᵧ (|τ(0,a,b,g)| + |τ(1,1-a,1-b,1-g)|)` is FALSE, violated by `+1.75`
    under adversarial search over `c₀..c₃ ∈ U(2)` and the four `U(4)` blocks.  A
    genuine `m = 3` analogue of `CutBound.bridge_ineq` — one that consumes
    `‖c₀₀‖ = ‖c₁₁‖`, `‖c₀₁‖ = ‖c₁₀‖` — is still missing. -/
def Core3Bound (c : ℝ) : Prop :=
  ∀ (M0 M1 M2 M3 : Mat4), IsUnitary4 M0 → Cost1.Cost1U4 M1 → Cost1.Cost1U4 M2 →
    IsUnitary4 M3 →
    ‖(M0 * M1 * M2 * M3).trace‖
      + ‖(Zp4 * M0 * Zhat4 * M1 * Zhat4 * M2 * Zhat4 * M3).trace‖ ≤ c

/-- **The two poles of `Core3Bound` are symmetric.**  Instantiating at
    `(M₀Ẑ, M₁Ẑ, M₂Ẑ, M₃)` and using `Ẑ² = 1` exchanges the two traces, so the
    `(α,β,γ) = (1,1,1)` pattern follows from the `(0,0,0)` one.  Combined with
    absorbing single `Ẑ`s into neighbouring blocks this covers all eight sign
    patterns of `trace_ccz_cut3`. -/
theorem core3_flip {c : ℝ} (h : Core3Bound c) {M0 M1 M2 M3 : Mat4}
    (h0 : IsUnitary4 M0) (h1 : Cost1.Cost1U4 M1) (h2 : Cost1.Cost1U4 M2)
    (h3 : IsUnitary4 M3) :
    ‖(M0 * Zhat4 * M1 * Zhat4 * M2 * Zhat4 * M3).trace‖
      + ‖(Zp4 * M0 * M1 * M2 * M3).trace‖ ≤ c := by
  have hz : IsUnitary4 Zhat4 := by
    rw [IsUnitary4, zhat4_conjTranspose]; exact zhat4_mul_self
  have key := h (M0 * Zhat4) (M1 * Zhat4) (M2 * Zhat4) M3
    (isUnitary4_mul h0 hz) (Cost1U4_zhat_right h1) (Cost1U4_zhat_right h2) h3
  have e1 : M0 * Zhat4 * (M1 * Zhat4) * (M2 * Zhat4) * M3
      = M0 * Zhat4 * M1 * Zhat4 * M2 * Zhat4 * M3 := by noncomm_ring
  have e2 : Zp4 * (M0 * Zhat4) * Zhat4 * (M1 * Zhat4) * Zhat4 * (M2 * Zhat4)
        * Zhat4 * M3 = Zp4 * M0 * M1 * M2 * M3 := by
    calc Zp4 * (M0 * Zhat4) * Zhat4 * (M1 * Zhat4) * Zhat4 * (M2 * Zhat4) * Zhat4 * M3
        = Zp4 * M0 * (Zhat4 * Zhat4) * M1 * (Zhat4 * Zhat4) * M2
            * (Zhat4 * Zhat4) * M3 := by noncomm_ring
      _ = Zp4 * M0 * M1 * M2 * M3 := by rw [zhat4_mul_self]; noncomm_ring
  rwa [e1, e2] at key

end Block

end
