/-
  ApproxToffoli.HardCutHS — the four `HardProfile` cut lists of `n = 7` reduced to
  TWO Hilbert–Schmidt inequalities of the `HS2`/`HS3` shape.

  Development copy: compiled with `lean_run_code` against `ApproxToffoli.HardCut`
  + `ApproxToffoli.MidCutHS`, 0 errors / 0 warnings.  NOT installed in the tree.

  ==============================================================================
  WHAT THIS FILE DOES
  ==============================================================================
  `HardCut.BLB` is the minimal three-crossing hypothesis for the four interior-cost-2
  profiles `[0,1,2,1]`, `[0,2,1,1]`, `[1,1,2,0]`, `[1,2,1,0]`.  Its content is that
  the cost-2 INTERIOR block may be relaxed to an arbitrary `U(4)`:

      BLB  =  (1u10)  ∨  (11u0)          (`m₀` = the RIGHTMOST block `M₀`)

  Because that block is FREE, the objective is LINEAR in it, so exactly the
  `Mid3Bound → HS3` manoeuvre of `MidCutHS` applies: cyclicity puts the free block
  last (`trace_peel_M1` / `trace_peel_M2` below), `BlockU.trace_mul_kronABC_one`
  factors it through the partial trace over C, and Hilbert–Schmidt Cauchy–Schwarz
  (`BlockU.normSq_trace_mul_unitary_le`, `‖M‖²_HS = 4`) gives

      |Tr(CCZ8 · U)|²  ≤  4‖Θ‖²_HS ,      4(8 + 4√2) = 64cos²(π/8).

  So `‖Θ‖²_HS ≤ 8 + 4√2` — `HS7a` / `HS7b` below — is EXACTLY enough, and

      HS7a ∧ HS7b  →  Block.HardBound          (`hardBound_of_HS7`)

  Combined with `BlockU.phiFive_of_HS2` and `MidCutHS.mid3Bound_of_HS3`, the whole
  `n ≤ 7` lower bound now rests on FOUR hypotheses of ONE shape,
  `‖Tr_C(·)‖²_HS ≤ 8 + 4√2`:

      curve_seven_of_HS : BlockU.HS2 → HS3 → HS7a → HS7b ⊢ d(7) = sin(π/8)

  The peeled block is in every case the unique cost-2 block, and it is always
  INTERIOR — which is why no boundary budget is lost.

  ==============================================================================
  NUMERICS: THE PEEL IS LOSS-FREE
  ==============================================================================
  Gauss–Seidel with exact nuclear-norm block updates for `|Tr|`, and Frank–Wolfe
  (monotone, `Θ` is linear in every variable) for `‖Θ‖²_HS`; cross-checked by
  L-BFGS-B over Hermitian generators.  Scratchpad `h7_hs.py`, `h7_peel.py`,
  `h7_hs_table.py`, `h7_hs_lbfgs.py`.  Encoding validated first against the three
  published `HS3` checkpoints (both interiors local → 12, `HS3` → 8+4√2, an interior
  freed → 16) and against `h7_table.json` (`h7_hs_self.py`: all pass).

  Writing `m₀m₁m₂m₃` for the CNOT modes of `M₀ … M₃` (`M₀` rightmost) and `?` for the
  peeled block:

      profile [1,2,1,0] = 1210, peel M₂ (my m₁)   1?10   max‖Θ‖²_HS = 13.656854249492
      profile [1,1,2,0] = 1120, peel M₁ (my m₂)   11?0   max‖Θ‖²_HS = 13.656854249492
      profile [0,1,2,1] = 0121, peel        …     01?1   max‖Θ‖²_HS = 13.656854249492
      profile [0,2,1,1] = 0211, peel        …     0?11   max‖Θ‖²_HS = 13.656854249492

  and `8 + 4√2 = 13.656854249492` exactly, with ALL FOUR singular values of `Θ` equal
  to `2cos(π/8) = 1.847759065` at the argmax — the signature of a saturated
  Cauchy–Schwarz.  So the step loses NOTHING.  (`HS7a → BLB`-case pointwise, not
  conversely; but the two families have the SAME maximum, `4·(8+4√2) = 64cos²(π/8)`,
  so passing to the HS form gives away no slack.)

  The full 4³ sweep of each peel position (`h7_hs_table.log`) shows the dichotomy is
  exact, with no exceptions in 128 configurations:

      relaxed |Tr| = 8cos(π/8)  ⟺  max‖Θ‖²_HS = 8+4√2   (loss-free, all σ equal)
      relaxed |Tr| = 8          ⟺  max‖Θ‖²_HS = 16       (FALSE)
      relaxed |Tr| = 4+2√2      ⟹  max‖Θ‖²_HS = 12       (true with slack)

  Each budget is load-bearing in HS form too.  For `HS7a` (`1?10`): `1?11` (local
  boundary → 1 CNOT), `2?10` (cost-1 boundary → 2), `1?20` (interior → 2) all give
  16.  For `HS7b` (`11?0`): `11?1`, `21?0`, `12?0` all give 16.
-/

import ApproxToffoli.HardCut
import ApproxToffoli.MidCutHS

open Matrix Complex

noncomputable section

namespace Block

/-! ## 1. Peeling an INTERIOR block off the four-block CZ normal form -/

/-- The C-factor and the AB-factor of a `kronABC` block commute, so the block also
    splits with the C-factor on the LEFT. -/
lemma kronABC_split' (M : Mat4) (c : Mat2) : kronABC M c = kronABC 1 c * kronABC M 1 := by
  rw [kronABC_mul]; simp

/-- **Peeling the THIRD block `M₂`.**  Cyclicity puts `M₂` last and
    `BlockU.trace_mul_kronABC_one` factors it through `Tr_C`.  `M₂` has DISAPPEARED
    from the right-hand side except as the free matrix argument. -/
theorem trace_peel_M2 (M0 M1 M2 M3 : Mat4) (c0 c1 c2 c3 : Mat2) :
    Matrix.trace (CCZ8 * (kronABC M0 c0 * CZBC8 * kronABC M1 c1 * CZBC8
        * kronABC M2 c2 * CZBC8 * kronABC M3 c3))
      = Matrix.trace (BlockU.trC (CZBC8 * kronABC M3 c3 * CCZ8 * kronABC M0 c0
          * CZBC8 * kronABC M1 c1 * CZBC8 * kronABC 1 c2) * M2) := by
  have e1 : CCZ8 * (kronABC M0 c0 * CZBC8 * kronABC M1 c1 * CZBC8
        * kronABC M2 c2 * CZBC8 * kronABC M3 c3)
      = (CCZ8 * kronABC M0 c0 * CZBC8 * kronABC M1 c1 * CZBC8 * kronABC 1 c2)
        * (kronABC M2 1 * (CZBC8 * kronABC M3 c3)) := by
    rw [kronABC_split' M2 c2]; simp only [Matrix.mul_assoc]
  rw [e1, Matrix.trace_mul_comm]
  have e2 : kronABC M2 1 * (CZBC8 * kronABC M3 c3)
        * (CCZ8 * kronABC M0 c0 * CZBC8 * kronABC M1 c1 * CZBC8 * kronABC 1 c2)
      = kronABC M2 1 * (CZBC8 * kronABC M3 c3 * CCZ8 * kronABC M0 c0
          * CZBC8 * kronABC M1 c1 * CZBC8 * kronABC 1 c2) := by
    simp only [Matrix.mul_assoc]
  rw [e2, Matrix.trace_mul_comm, BlockU.trace_mul_kronABC_one]

/-- **Peeling the SECOND block `M₁`.** -/
theorem trace_peel_M1 (M0 M1 M2 M3 : Mat4) (c0 c1 c2 c3 : Mat2) :
    Matrix.trace (CCZ8 * (kronABC M0 c0 * CZBC8 * kronABC M1 c1 * CZBC8
        * kronABC M2 c2 * CZBC8 * kronABC M3 c3))
      = Matrix.trace (BlockU.trC (CZBC8 * kronABC M2 c2 * CZBC8 * kronABC M3 c3
          * CCZ8 * kronABC M0 c0 * CZBC8 * kronABC 1 c1) * M1) := by
  have e1 : CCZ8 * (kronABC M0 c0 * CZBC8 * kronABC M1 c1 * CZBC8
        * kronABC M2 c2 * CZBC8 * kronABC M3 c3)
      = (CCZ8 * kronABC M0 c0 * CZBC8 * kronABC 1 c1)
        * (kronABC M1 1 * (CZBC8 * kronABC M2 c2 * CZBC8 * kronABC M3 c3)) := by
    rw [kronABC_split' M1 c1]; simp only [Matrix.mul_assoc]
  rw [e1, Matrix.trace_mul_comm]
  have e2 : kronABC M1 1 * (CZBC8 * kronABC M2 c2 * CZBC8 * kronABC M3 c3)
        * (CCZ8 * kronABC M0 c0 * CZBC8 * kronABC 1 c1)
      = kronABC M1 1 * (CZBC8 * kronABC M2 c2 * CZBC8 * kronABC M3 c3
          * CCZ8 * kronABC M0 c0 * CZBC8 * kronABC 1 c1) := by
    simp only [Matrix.mul_assoc]
  rw [e2, Matrix.trace_mul_comm, BlockU.trace_mul_kronABC_one]

/-! ## 2. The two Hilbert–Schmidt hypotheses -/

/-- **(HS7a)** — the peel of profile `[1,2,1,0]` (words `abaabab`, `babbaba`).
    `M₂`, the cost-2 interior block, is gone; the surviving budgets are the local
    boundary `M₀`, the cost-1 interior `M₁` and the cost-1 boundary `M₃`.

    Exactly the shape and the budget of `BlockU.HS1` / `BlockU.HS2` / `HS3`:
    `‖Θ‖²_HS ≤ 8 + 4√2`.  TIGHT — the maximum of the left-hand side is exactly
    `8 + 4√2 = 13.656854249492`, attained with all four singular values of `Θ` equal
    to `2cos(π/8)`, so the Cauchy–Schwarz step below loses NOTHING.  Each of the
    three budgets is load-bearing (raising any one gives 16). -/
def HS7a : Prop :=
  ∀ (M0 M1 M3 : Mat4) (c0 c1 c2 c3 : Mat2),
    CX2 0 M0 → CX2 1 M1 → CX2 1 M3 →
    IsUnitary2 c0 → IsUnitary2 c1 → IsUnitary2 c2 → IsUnitary2 c3 →
    BlockU.HSSmall (BlockU.trC (CZBC8 * kronABC M3 c3 * CCZ8 * kronABC M0 c0
        * CZBC8 * kronABC M1 c1 * CZBC8 * kronABC 1 c2))

/-- **(HS7b)** — the peel of profile `[1,1,2,0]` (words `ababaab`, `bababba`).
    Same statement with the cost-2 block one place to the left. -/
def HS7b : Prop :=
  ∀ (M0 M2 M3 : Mat4) (c0 c1 c2 c3 : Mat2),
    CX2 0 M0 → CX2 1 M2 → CX2 1 M3 →
    IsUnitary2 c0 → IsUnitary2 c1 → IsUnitary2 c2 → IsUnitary2 c3 →
    BlockU.HSSmall (BlockU.trC (CZBC8 * kronABC M2 c2 * CZBC8 * kronABC M3 c3
        * CCZ8 * kronABC M0 c0 * CZBC8 * kronABC 1 c1))

/-! ## 3. The reduction -/

/-- The profile of `abaabab` (and, reversed, of `babaaba`). -/
theorem cutSq_1210_of_HS7a (h : HS7a) :
    CutSqBound [1, 2, 1, 0] (64 * Real.cos (Real.pi / 8) ^ 2) := by
  intro U hU
  obtain ⟨M0, M1, M2, M3, c0, c1, c2, c3, hM0, hM1, hM2, hM3,
    hc0, hc1, hc2, hc3, rfl⟩ := hU.toCZCutC.unfold_four
  rw [trace_peel_M2]
  refine le_trans (BlockU.normSq_trace_mul_unitary_le _ hM2.unitary) ?_
  rw [← BlockU.four_mul_hs_budget]
  exact mul_le_mul_of_nonneg_left
    (h M0 M1 M3 c0 c1 c2 c3 hM0 hM1 hM3 hc0 hc1 hc2 hc3) (by norm_num)

/-- The profile of `ababaab` (and, reversed, of `baababa`). -/
theorem cutSq_1120_of_HS7b (h : HS7b) :
    CutSqBound [1, 1, 2, 0] (64 * Real.cos (Real.pi / 8) ^ 2) := by
  intro U hU
  obtain ⟨M0, M1, M2, M3, c0, c1, c2, c3, hM0, hM1, hM2, hM3,
    hc0, hc1, hc2, hc3, rfl⟩ := hU.toCZCutC.unfold_four
  rw [trace_peel_M1]
  refine le_trans (BlockU.normSq_trace_mul_unitary_le _ hM1.unitary) ?_
  rw [← BlockU.four_mul_hs_budget]
  exact mul_le_mul_of_nonneg_left
    (h M0 M2 M3 c0 c1 c2 c3 hM0 hM2 hM3 hc0 hc1 hc2 hc3) (by norm_num)

/-- **`HS7a ∧ HS7b → HardBound`.**  Two profiles directly, the other two by the
    adjoint symmetry `HardCut.CutSqBound.reverse`. -/
theorem hardBound_of_HS7 (ha : HS7a) (hb : HS7b) : HardBound := by
  intro ks hk
  match ks, hk with
  | [0, 1, 2, 1], _ =>
      have e : ([1, 2, 1, 0] : List ℕ).reverse = [0, 1, 2, 1] := rfl
      have := (cutSq_1210_of_HS7a ha).reverse
      rwa [e] at this
  | [0, 2, 1, 1], _ =>
      have e : ([1, 1, 2, 0] : List ℕ).reverse = [0, 2, 1, 1] := rfl
      have := (cutSq_1120_of_HS7b hb).reverse
      rwa [e] at this
  | [1, 1, 2, 0], _ => exact cutSq_1120_of_HS7b hb
  | [1, 2, 1, 0], _ => exact cutSq_1210_of_HS7a ha

/-- **`d(7) = sin(π/8)`** with `HardCut.BLB` replaced by the two HS inequalities. -/
theorem curve_seven_of_HS7 (hphi : PhiFive) (hicb : ICB) (ha : HS7a) (hb : HS7b) :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 7 U ∧ hsDistance U CCX = d}
      (Real.sin (Real.pi / 8)) :=
  curve_seven_of_ICB hphi hicb (hardBound_of_HS7 ha hb)

/-! ## 4. Dropping `ICB` as well: `n ≤ 7` on four hypotheses of ONE shape

`ICB` is only ever used through `cutSq_of_intProfile`, and `MidCut.cutSqBound_of_mid3`
delivers exactly the same conclusion — so `Mid3Bound`, hence `HS3`, replaces it. -/

/-- `Mid3Bound` covers every `IntProfile` cut class, just as `ICB` does. -/
theorem cutSq_of_intProfile_mid3 {c : ℝ} (h : Mid3Bound c) {ks : List ℕ}
    (hk : IntProfile ks = true) : CutSqBound ks c := by
  match ks, hk with
  | [_, _, _, _], hk =>
    simp only [IntProfile, Bool.and_eq_true, decide_eq_true_eq] at hk
    exact cutSqBound_of_mid3 h hk.2 hk.1

/-- **The `n ≤ 7` trace bound** on `PhiFive`, `Mid3Bound` and `HardBound` — `ICB` is
    no longer needed. -/
theorem achievable_trace_bound_seven_mid (hphi : PhiFive)
    (hmid : Mid3Bound (64 * Real.cos (Real.pi / 8) ^ 2)) (hhard : HardBound)
    {n : ℕ} (hn : n ≤ 7) {U : Mat8} (h : AchievableCircuit n U) :
    Complex.normSq (Matrix.trace (Uᴴ * CCX)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2 := by
  obtain ⟨w, hlen, hw⟩ := exists_cxWord h
  by_cases hr : runs w ≤ 5
  · exact trace_bound_of_runs_le_five hphi hw hr
  · obtain ⟨ks, W, hg, hcut, heq⟩ := word_residual_seven hw (le_trans hlen hn) (by omega)
    rw [heq]
    rcases hg with hg | hg
    · exact cutSq_of_intProfile_mid3 hmid hg W hcut
    · exact hhard ks hg W hcut

/-- **`d(7) = sin(π/8)`** on `PhiFive`, `Mid3Bound` and `HardBound`. -/
theorem curve_seven_mid (hphi : PhiFive)
    (hmid : Mid3Bound (64 * Real.cos (Real.pi / 8) ^ 2)) (hhard : HardBound) :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 7 U ∧ hsDistance U CCX = d}
      (Real.sin (Real.pi / 8)) := by
  constructor
  · exact ⟨Curve.witness4,
      AchievableCircuit.weaken (AchievableCircuit.weaken
        (AchievableCircuit.weaken Curve.witness4_achievable)),
      Curve.witness4_distance⟩
  · rintro d ⟨U, hU, rfl⟩
    exact trace_bound_implies_distance U
      (achievable_trace_bound_seven_mid hphi hmid hhard (by norm_num) hU)

/-- **`d(7) = sin(π/8)` on FOUR Hilbert–Schmidt inequalities and nothing else.**
    `BlockU.HS2`, `HS3`, `HS7a`, `HS7b` all read `‖Tr_C(X)‖²_HS ≤ 8 + 4√2` for an
    explicit unitary `X`; every one of them is TIGHT.  No circuit induction, no
    nuclear norms, no moduli — four polynomial sum-of-squares inequalities. -/
theorem curve_seven_of_HS (h2 : BlockU.HS2) (h3 : HS3) (ha : HS7a) (hb : HS7b) :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 7 U ∧ hsDistance U CCX = d}
      (Real.sin (Real.pi / 8)) :=
  curve_seven_mid (BlockU.phiFive_of_HS2 h2) (mid3Bound_of_HS3 h3)
    (hardBound_of_HS7 ha hb)

/-- **`d(6)` and `d(7)` together, on the same four hypotheses.** -/
theorem curve_six_seven_of_HS (h2 : BlockU.HS2) (h3 : HS3) (ha : HS7a) (hb : HS7b) :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 6 U ∧ hsDistance U CCX = d}
        (Real.sin (Real.pi / 8)) ∧
      IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 7 U ∧ hsDistance U CCX = d}
        (Real.sin (Real.pi / 8)) :=
  ⟨curve_six_of_HS2_HS3 h2 h3, curve_seven_of_HS h2 h3 ha hb⟩

end Block

end
