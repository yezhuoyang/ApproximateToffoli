/-
  ApproxToffoli.Budget3Interior — splitting (BUDGET3) into its `n = 6` half and its
  `n = 7` half.

  Development copy: compiled with `lean_run_code` against `ApproxToffoli.BlockResidual`,
  0 errors / 0 warnings.  NOT installed in the tree.

  What this file does
  -------------------
  `Block.Budget3` (BlockResidual §6) is the single analytic gap left in the `n = 6, 7`
  lower bound.  It is stated over ALL `GoodProfile` cost lists.  This file replaces it
  by the two profile classes that words actually produce, and shows the `n = 6` half
  needs only the FIRST of them:

  * `IntProfile ks` — four far-side blocks whose two INTERIOR ones cost at most one
    CNOT.  The two boundary blocks are UNCONSTRAINED (arbitrary `U(4)`).
  * `HardProfile ks` — the four leftover lists `[0,1,2,1]`, `[0,2,1,1]`, `[1,1,2,0]`,
    `[1,2,1,0]`.

  `word_profile_six`  : length ≤ 6, ≥ 6 runs ⟹ one cut has an `IntProfile`.
  `word_profile_seven`: length ≤ 7, ≥ 6 runs ⟹ one cut has an `IntProfile` or a
                        `HardProfile`.
  Both by `decide` over all words.

  Consequently `curve_six` needs only `PhiFive` and `ICB`, and `curve_seven` needs
  `PhiFive`, `ICB` and `HardBound`.

  Why this is progress
  --------------------
  `ICB` is a much smaller statement than `Budget3`: the two boundary blocks are FREE,
  so only two budgeted blocks remain, and their budget is the sharpest one available —
  `CX2 1`, which by `Budget3.CXCostLE.one_shape` means "locally equivalent to an
  A-CONTROLLED gate".  Under that hypothesis the whole middle of the circuit becomes
  block diagonal in the A qubit, which is the structural fact the analytic proof has
  to exploit (see the module note at the end).

  Numerics (Gauss–Seidel with exact nuclear-norm block updates, 40 restarts, plus an
  independent L-BFGS optimiser):
    * interior costs (1,1), boundaries FREE  → max |Tr| = 7.3910362601 = 8cos(π/8).
      TIGHT — so `ICB` is true and cannot be weakened by relaxing the interior.
    * interior costs (1,2), boundaries FREE  → max |Tr| = 8.0000000000.  FALSE.
      So the `HardProfile` class genuinely needs its boundary budget: relaxing EITHER
      boundary of `[0,1,2,1]` to `U(4)` already reaches 8.
-/

import ApproxToffoli.BlockResidual

open Matrix Complex

noncomputable section

namespace Block

/-! ## 1. The interior-cost-one class -/

/-- **`ICB`** — the interior-cost-one three-crossing bound, written in the `BCCutC`
    build order (`M3` leftmost, `M0` rightmost).  The two BOUNDARY blocks `M3`, `M0`
    are arbitrary `U(4)`; only the two INTERIOR blocks carry a budget, and it is the
    sharpest one: a single CNOT.

    TRUE and TIGHT numerically (`8cos(π/8)`, attained).  NOT PROVED here. -/
def ICB : Prop :=
  ∀ (M0 M1 M2 M3 : Mat4) (c0 c1 c2 c3 : Mat2) (G1 G2 G3 : Mat8),
    IsUnitary4 M3 → CX2 1 M2 → CX2 1 M1 → IsUnitary4 M0 →
    IsUnitary2 c0 → IsUnitary2 c1 → IsUnitary2 c2 → IsUnitary2 c3 →
    (G1 = CX_BC ∨ G1 = CX_CB) → (G2 = CX_BC ∨ G2 = CX_CB) →
    (G3 = CX_BC ∨ G3 = CX_CB) →
    Complex.normSq (Matrix.trace (CCZ8 *
        (kronABC M3 c3 * G3 * kronABC M2 c2 * G2 * kronABC M1 c1 * G1
          * kronABC M0 c0)))
      ≤ 64 * Real.cos (Real.pi / 8) ^ 2

/-- Four far-side blocks whose two INTERIOR ones have CNOT cost at most one. -/
def IntProfile : List ℕ → Bool
  | [_, k1, k2, _] => k1 ≤ 1 && k2 ≤ 1
  | _ => false

/-- The four profiles of length ≤ 7 that `IntProfile` misses.  Each has a LOCAL
    boundary block and interior costs `{1,2}`. -/
def HardProfile : List ℕ → Bool
  | [0, 1, 2, 1] => true
  | [0, 2, 1, 1] => true
  | [1, 1, 2, 0] => true
  | [1, 2, 1, 0] => true
  | _ => false

/-- `HardBound` — the leftover analytic input for `n = 7`.  Unlike `ICB` it cannot
    drop either boundary budget: with `M0` or `M3` relaxed to `U(4)` the maximum is
    `8`, not `8cos(π/8)`. -/
def HardBound : Prop :=
  ∀ ks : List ℕ, HardProfile ks = true →
    CutSqBound ks (64 * Real.cos (Real.pi / 8) ^ 2)

/-! ## 2. `ICB` bounds every `IntProfile` cut class -/

/-- Unfolding a four-block budgeted cut form with interior costs ≤ 1 is exactly the
    hypothesis of `ICB`. -/
theorem cutSq_of_intProfile (h : ICB) {ks : List ℕ} (hk : IntProfile ks = true) :
    CutSqBound ks (64 * Real.cos (Real.pi / 8) ^ 2) := by
  match ks, hk with
  | [k0, k1, k2, k3], hk =>
    simp only [IntProfile, Bool.and_eq_true, decide_eq_true_eq] at hk
    intro U hU
    cases hU with
    | @step ks1 U1 h1 G1 hG1 j0 M0 hM0 c0 hc0 =>
      cases h1 with
      | @step ks2 U2 h2 G2 hG2 j1 M1 hM1 c1 hc1 =>
        cases h2 with
        | @step ks3 U3 h3 G3 hG3 j2 M2 hM2 c2 hc2 =>
          cases h3 with
          | @base j3 M3 hM3 c3 hc3 =>
            exact h M0 M1 M2 M3 c0 c1 c2 c3 G1 G2 G3 hM3.unitary
              (hM2.mono hk.2) (hM1.mono hk.1) hM0.unitary hc0 hc1 hc2 hc3
              hG1 hG2 hG3
          | @step ks4 U4 h4 _ _ _ _ _ _ _ => cases h4

/-! ## 3. The two enumerations -/

/-- **`n = 6`.**  A word of length at most 6 with at least 6 runs has, on one of the
    two cuts, four far-side blocks whose interior costs are at most one.  (The only
    such words are `ababab` and `bababa`, both with profile `[1,1,1,0]`.) -/
theorem word_profile_six : ∀ w : List Bool, w.length ≤ 6 → 6 ≤ runs w →
    IntProfile (cutCosts true w) = true ∨ IntProfile (cutCosts false w) = true := by
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

/-- **`n = 7`.**  Length ≤ 7 and ≥ 6 runs leaves exactly one extra class beyond
    `IntProfile`: the four `HardProfile` lists.  (8 of the 16 residual words land in
    `IntProfile`, the other 8 in `HardProfile`.) -/
theorem word_profile_seven : ∀ w : List Bool, w.length ≤ 7 → 6 ≤ runs w →
    IntProfile (cutCosts true w) = true ∨ IntProfile (cutCosts false w) = true ∨
    HardProfile (cutCosts true w) = true ∨ HardProfile (cutCosts false w) = true := by
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

/-! ## 4. The residual, refined -/

/-- The `IntProfile` version of `word_residual`: for `n = 6` the circuit lands in a
    cut class with interior costs ≤ 1, without changing the Toffoli objective. -/
theorem word_residual_int {w : List Bool} {U : Mat8} (hw : CXWord w U)
    (hlen : w.length ≤ 6) (hr : 6 ≤ runs w) :
    ∃ (ks : List ℕ) (W : Mat8), IntProfile ks = true ∧ BCCutC ks W ∧
      Complex.normSq (Matrix.trace (Uᴴ * CCX))
        = Complex.normSq (Matrix.trace (CCZ8 * W)) := by
  rcases word_profile_six w hlen hr with hg | hg
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

/-- The `n = 7` version: `IntProfile` or `HardProfile`. -/
theorem word_residual_seven {w : List Bool} {U : Mat8} (hw : CXWord w U)
    (hlen : w.length ≤ 7) (hr : 6 ≤ runs w) :
    ∃ (ks : List ℕ) (W : Mat8),
      (IntProfile ks = true ∨ HardProfile ks = true) ∧ BCCutC ks W ∧
      Complex.normSq (Matrix.trace (Uᴴ * CCX))
        = Complex.normSq (Matrix.trace (CCZ8 * W)) := by
  rcases word_profile_seven w hlen hr with hg | hg | hg | hg
  · exact ⟨cutCosts true w, kron3 1 1 Hgate * U * kron3 1 1 Hgate, Or.inl hg,
      ((cxWord_to_BCCutC hw).mul_layer_left 1 1 Hgate isUnitary2_one isUnitary2_one
          hgate_unitary).mul_layer_right 1 1 Hgate isUnitary2_one isUnitary2_one
          hgate_unitary,
      normSq_trace_ccx_eq U⟩
  · refine ⟨cutCosts false w,
      kron3 Hgate 1 1 * (swapMatAC * U * swapMatAC) * kron3 Hgate 1 1, Or.inl hg, ?_, ?_⟩
    · have h1 := cxWord_to_BCCutC (cxWord_mirror hw)
      rw [cutCosts_map_not] at h1
      exact (h1.mul_layer_left Hgate 1 1 hgate_unitary isUnitary2_one
        isUnitary2_one).mul_layer_right Hgate 1 1 hgate_unitary isUnitary2_one
        isUnitary2_one
    · rw [normSq_trace_ccx_eq U, mirror_trace_eq]
  · exact ⟨cutCosts true w, kron3 1 1 Hgate * U * kron3 1 1 Hgate, Or.inr hg,
      ((cxWord_to_BCCutC hw).mul_layer_left 1 1 Hgate isUnitary2_one isUnitary2_one
          hgate_unitary).mul_layer_right 1 1 Hgate isUnitary2_one isUnitary2_one
          hgate_unitary,
      normSq_trace_ccx_eq U⟩
  · refine ⟨cutCosts false w,
      kron3 Hgate 1 1 * (swapMatAC * U * swapMatAC) * kron3 Hgate 1 1, Or.inr hg, ?_, ?_⟩
    · have h1 := cxWord_to_BCCutC (cxWord_mirror hw)
      rw [cutCosts_map_not] at h1
      exact (h1.mul_layer_left Hgate 1 1 hgate_unitary isUnitary2_one
        isUnitary2_one).mul_layer_right Hgate 1 1 hgate_unitary isUnitary2_one
        isUnitary2_one
    · rw [normSq_trace_ccx_eq U, mirror_trace_eq]

/-! ## 5. Assembly -/

/-- **The `n ≤ 6` trace bound**, on `PhiFive` and `ICB` ONLY.  `Budget3` is not
    needed for `n = 6`: the two words of length 6 with 6 runs put the circuit in a
    cut class whose interior blocks cost one CNOT each. -/
theorem achievable_trace_bound_six (hphi : PhiFive) (hicb : ICB)
    {n : ℕ} (hn : n ≤ 6) {U : Mat8} (h : AchievableCircuit n U) :
    Complex.normSq (Matrix.trace (Uᴴ * CCX)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2 := by
  obtain ⟨w, hlen, hw⟩ := exists_cxWord h
  by_cases hr : runs w ≤ 5
  · exact trace_bound_of_runs_le_five hphi hw hr
  · obtain ⟨ks, W, hg, hcut, heq⟩ := word_residual_int hw (le_trans hlen hn) (by omega)
    rw [heq]
    exact cutSq_of_intProfile hicb hg W hcut

/-- **`d(6) = sin(π/8)`**, on `PhiFive` and `ICB`. -/
theorem curve_six_of_ICB (hphi : PhiFive) (hicb : ICB) :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 6 U ∧ hsDistance U CCX = d}
      (Real.sin (Real.pi / 8)) := by
  constructor
  · exact ⟨Curve.witness4,
      AchievableCircuit.weaken (AchievableCircuit.weaken Curve.witness4_achievable),
      Curve.witness4_distance⟩
  · rintro d ⟨U, hU, rfl⟩
    exact trace_bound_implies_distance U
      (achievable_trace_bound_six hphi hicb (by norm_num) hU)

/-- **The `n ≤ 7` trace bound**, on `PhiFive`, `ICB` and `HardBound`. -/
theorem achievable_trace_bound_seven' (hphi : PhiFive) (hicb : ICB) (hhard : HardBound)
    {n : ℕ} (hn : n ≤ 7) {U : Mat8} (h : AchievableCircuit n U) :
    Complex.normSq (Matrix.trace (Uᴴ * CCX)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2 := by
  obtain ⟨w, hlen, hw⟩ := exists_cxWord h
  by_cases hr : runs w ≤ 5
  · exact trace_bound_of_runs_le_five hphi hw hr
  · obtain ⟨ks, W, hg, hcut, heq⟩ := word_residual_seven hw (le_trans hlen hn) (by omega)
    rw [heq]
    rcases hg with hg | hg
    · exact cutSq_of_intProfile hicb hg W hcut
    · exact hhard ks hg W hcut

/-- **`d(7) = sin(π/8)`**, on `PhiFive`, `ICB` and `HardBound`. -/
theorem curve_seven_of_ICB (hphi : PhiFive) (hicb : ICB) (hhard : HardBound) :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 7 U ∧ hsDistance U CCX = d}
      (Real.sin (Real.pi / 8)) := by
  constructor
  · exact ⟨Curve.witness4,
      AchievableCircuit.weaken (AchievableCircuit.weaken
        (AchievableCircuit.weaken Curve.witness4_achievable)),
      Curve.witness4_distance⟩
  · rintro d ⟨U, hU, rfl⟩
    exact trace_bound_implies_distance U
      (achievable_trace_bound_seven' hphi hicb hhard (by norm_num) hU)

/-- `ICB` and `HardBound` together are enough for the tree's `Budget3` USES.  (They
    do not imply `Budget3` itself, which is stated over all `GoodProfile` lists —
    including ones no word produces.) -/
theorem curve_six_seven_of_ICB (hphi : PhiFive) (hicb : ICB) (hhard : HardBound) :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 6 U ∧ hsDistance U CCX = d}
        (Real.sin (Real.pi / 8)) ∧
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 7 U ∧ hsDistance U CCX = d}
        (Real.sin (Real.pi / 8)) :=
  ⟨curve_six_of_ICB hphi hicb, curve_seven_of_ICB hphi hicb hhard⟩

end Block

end
