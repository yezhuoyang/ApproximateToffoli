/-
  ApproxToffoli.BlockResidual

  The COMBINATORIAL half of the `n = 6, 7` lower bound.

  `Block.achievable_seven_dichotomy` leaves, given `PhiFive`, exactly one case: a CNOT
  word `w` with `w.length ≤ 7` and `6 ≤ runs w`.  This file shows that every such word
  puts the circuit into a single, very small, BUDGETED cut class, and assembles the
  `n = 6, 7` entries of the curve from that class plus `PhiFive`.

  Contents
  --------
  1. `CX2 k M` — two-qubit circuits with at most `k` CNOTs (the far-side blocks).
  2. `BCCutC ks U` — the AB|C cut form REFINED by the list `ks` of far-side block
     costs (head = rightmost block).  `ks.length - 1` is the number of crossings, and
     `BCCutC.toBCCut` forgets the budget back onto the tree's `BCCut`.
  3. `cutProf` / `cutCosts` — the cut profile of a word, and the two counting
     identities `cutCosts_length` (#blocks = #crossings + 1) and `cutCosts_sum`
     (#crossings + Σ costs = word length).
  4. `cxWord_to_BCCutC : CXWord w U → BCCutC (cutCosts true w) U` — the profile is
     realised by the circuit: a maximal run of AB CNOTs is one far-side block of that
     exact cost.
  5. `cxWord_mirror : CXWord w U → CXWord (w.map not) (swapMatAC * U * swapMatAC)` —
     the A↔C mirror at the level of words, so only the BC-crossing cut is ever needed.
  6. `word_profile` — the finite enumeration: `w.length ≤ 7` and `6 ≤ runs w` force,
     on the letter with FEWER occurrences, exactly 3 crossings, 4 blocks, each of cost
     ≤ 2 and of total cost ≤ 4.  (There are NINE such ordered profiles; the three
     MULTISETS are `{1,1,1,0}`, `{1,1,1,1}`, `{2,1,1,0}`, but position matters and
     four of the nine have an INTERIOR cost-2 block.)
  7. `Budget3` — the one remaining analytic input, stated in the style of
     `Block.PhiSqBound`, together with `budget3_nonvacuous`: all three profiles are
     inhabited by genuine `AchievableCircuit` circuits.
  8. `achievable_trace_bound_seven`, `curve_six`, `curve_seven` — the assembly.

  THE BUDGET IS NOT OPTIONAL.  With the far side relaxed to arbitrary `U(4)` the bound
  is FALSE: `F(3) = F(4) = 8`, i.e. three crossings with unrestricted far-side layers
  build `CCZ` exactly (see the `CutForm` module docstring).  Any proof of `Budget3`
  that never uses `k ≤ 2` or `Σ k ≤ 4` is therefore wrong.
-/

import ApproxToffoli.Block
import ApproxToffoli.CurveMain

open Matrix Complex

noncomputable section

namespace Block

/-! ## 1. Two-qubit circuits with a CNOT budget

These are the far-side blocks of a cut: an AB-only stretch of the circuit, i.e. a
2-qubit circuit.  `cutCNOT_AB_4` and `CNOT_BA_4` are the two 4×4 CNOTs of `CutForm`. -/

/-- `CX2 k M` : the 4×4 unitary `M` is a two-qubit circuit using at most `k` CNOTs
    (either direction) and arbitrary single-qubit layers. -/
inductive CX2 : ℕ → Mat4 → Prop where
  | layer (a b : Mat2) (ha : IsUnitary2 a) (hb : IsUnitary2 b) : CX2 0 (kron2 a b)
  | weaken {k : ℕ} {M : Mat4} : CX2 k M → CX2 (k + 1) M
  | step {k : ℕ} {M : Mat4} (h : CX2 k M) (G : Mat4)
      (hG : G = cutCNOT_AB_4 ∨ G = CNOT_BA_4) (a b : Mat2)
      (ha : IsUnitary2 a) (hb : IsUnitary2 b) : CX2 (k + 1) (M * G * kron2 a b)

theorem CX2.unitary {k : ℕ} {M : Mat4} (h : CX2 k M) : IsUnitary4 M := by
  induction h with
  | layer a b ha hb => exact isUnitary4_kron2 ha hb
  | weaken _ ih => exact ih
  | step _ G hG a b ha hb ih =>
      rcases hG with rfl | rfl
      · exact isUnitary4_mul (isUnitary4_mul ih isUnitary4_cutCNOT_AB_4)
          (isUnitary4_kron2 ha hb)
      · exact isUnitary4_mul (isUnitary4_mul ih isUnitary4_CNOT_BA_4)
          (isUnitary4_kron2 ha hb)

theorem CX2.mono {j k : ℕ} (hjk : j ≤ k) {M : Mat4} (h : CX2 j M) : CX2 k M := by
  induction k, hjk using Nat.le_induction with
  | base => exact h
  | succ k _ ih => exact ih.weaken

/-- A free single-qubit layer on the right does not consume budget. -/
theorem CX2.mul_layer_right {k : ℕ} {M : Mat4} (h : CX2 k M) :
    ∀ (a b : Mat2), IsUnitary2 a → IsUnitary2 b → CX2 k (M * kron2 a b) := by
  induction h with
  | layer a₀ b₀ ha₀ hb₀ =>
      intro a b ha hb; rw [kron2_mul]
      exact CX2.layer _ _ (isUnitary2_mul ha₀ ha) (isUnitary2_mul hb₀ hb)
  | weaken _ ih => intro a b ha hb; exact (ih a b ha hb).weaken
  | step h G hG a₀ b₀ ha₀ hb₀ _ =>
      intro a b ha hb
      rw [Matrix.mul_assoc, kron2_mul]
      exact CX2.step h G hG _ _ (isUnitary2_mul ha₀ ha) (isUnitary2_mul hb₀ hb)

/-- A free single-qubit layer on the left does not consume budget. -/
theorem CX2.mul_layer_left {k : ℕ} {M : Mat4} (h : CX2 k M) :
    ∀ (a b : Mat2), IsUnitary2 a → IsUnitary2 b → CX2 k (kron2 a b * M) := by
  induction h with
  | layer a₀ b₀ ha₀ hb₀ =>
      intro a b ha hb; rw [kron2_mul]
      exact CX2.layer _ _ (isUnitary2_mul ha ha₀) (isUnitary2_mul hb hb₀)
  | weaken _ ih => intro a b ha hb; exact (ih a b ha hb).weaken
  | step h G hG a₀ b₀ ha₀ hb₀ ih =>
      intro a b ha hb
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
      exact CX2.step (ih a b ha hb) G hG _ _ ha₀ hb₀

/-! ## 2. The budgeted AB|C cut form

`BCCutC ks U` is `BCCut (ks.length - 1) U` with the far-side blocks constrained: the
`i`-th `U(4)` factor is not arbitrary but a two-qubit circuit of CNOT cost at most
`ks[i]`.  The head of `ks` is the RIGHTMOST block, matching the `CXWord` recursion
(whose head is the LAST gate applied). -/

/-- The AB|C cut normal form refined by the far-side CNOT budget `ks`. -/
inductive BCCutC : List ℕ → Mat8 → Prop where
  | base {k : ℕ} {M : Mat4} (hM : CX2 k M) (c : Mat2) (hc : IsUnitary2 c) :
      BCCutC [k] (kronABC M c)
  | step {ks : List ℕ} {U : Mat8} (h : BCCutC ks U) (G : Mat8)
      (hG : G = CX_BC ∨ G = CX_CB) {k : ℕ} {M : Mat4} (hM : CX2 k M)
      (c : Mat2) (hc : IsUnitary2 c) :
      BCCutC (k :: ks) (U * G * kronABC M c)

theorem BCCutC.cost_ne_nil {ks : List ℕ} {U : Mat8} (h : BCCutC ks U) : ks ≠ [] := by
  cases h <;> simp

/-- **Forgetting the budget.**  A budgeted cut form with `ks` costs is an ordinary
    `BCCut` with `ks.length - 1` crossings. -/
theorem BCCutC.toBCCut {ks : List ℕ} {U : Mat8} (h : BCCutC ks U) :
    BCCut (ks.length - 1) U := by
  induction h with
  | base hM c hc => exact BCCut.base _ _ hM.unitary hc
  | @step ks U h G hG k M hM c hc ih =>
      have hlen : (k :: ks).length - 1 = (ks.length - 1) + 1 := by
        cases ks with
        | nil => cases h
        | cons _ _ => simp
      rw [hlen]
      rcases hG with rfl | rfl
      · exact BCCut.stepBC ih _ _ hM.unitary hc
      · exact BCCut.stepCB ih _ _ hM.unitary hc

/-- A free single-qubit layer on the right does not consume budget. -/
theorem BCCutC.mul_layer_right {ks : List ℕ} {U : Mat8} (h : BCCutC ks U) :
    ∀ (a b c : Mat2), IsUnitary2 a → IsUnitary2 b → IsUnitary2 c →
      BCCutC ks (U * kron3 a b c) := by
  induction h with
  | base hM c₀ hc₀ =>
      intro a b c ha hb hc
      rw [kron3_eq_kronABC, kronABC_mul]
      exact BCCutC.base (hM.mul_layer_right a b ha hb) _ (isUnitary2_mul hc₀ hc)
  | @step ks U h G hG k M hM c₀ hc₀ ih =>
      intro a b c ha hb hc
      rw [show U * G * kronABC M c₀ * kron3 a b c
            = U * G * kronABC (M * kron2 a b) (c₀ * c) from by
        rw [kron3_eq_kronABC, Matrix.mul_assoc (U * G), kronABC_mul]]
      exact BCCutC.step h G hG (hM.mul_layer_right a b ha hb) _ (isUnitary2_mul hc₀ hc)

/-- A free single-qubit layer on the left does not consume budget. -/
theorem BCCutC.mul_layer_left {ks : List ℕ} {U : Mat8} (h : BCCutC ks U) :
    ∀ (a b c : Mat2), IsUnitary2 a → IsUnitary2 b → IsUnitary2 c →
      BCCutC ks (kron3 a b c * U) := by
  induction h with
  | base hM c₀ hc₀ =>
      intro a b c ha hb hc
      rw [kron3_eq_kronABC, kronABC_mul]
      exact BCCutC.base (hM.mul_layer_left a b ha hb) _ (isUnitary2_mul hc hc₀)
  | @step ks U h G hG k M hM c₀ hc₀ ih =>
      intro a b c ha hb hc
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
      exact BCCutC.step (ih a b c ha hb hc) G hG hM c₀ hc₀

/-- **One more AB CNOT joins the rightmost far-side block**, incrementing its cost by
    one.  This is the step that turns a maximal AB-run of the word into a single block
    whose budget is the run length. -/
theorem BCCutC.absorb_cx {k : ℕ} {ks : List ℕ} {U : Mat8} (h : BCCutC (k :: ks) U)
    (G : Mat4) (hG : G = cutCNOT_AB_4 ∨ G = CNOT_BA_4) (a b c : Mat2)
    (ha : IsUnitary2 a) (hb : IsUnitary2 b) (hc : IsUnitary2 c) :
    BCCutC ((k + 1) :: ks) (U * kronABC (G * kron2 a b) c) := by
  cases h with
  | base hM c₀ hc₀ =>
      rw [kronABC_mul]
      refine BCCutC.base ?_ _ (isUnitary2_mul hc₀ hc)
      rw [← Matrix.mul_assoc]
      exact CX2.step hM G hG a b ha hb
  | @step ks U h G' hG' k M hM c₀ hc₀ =>
      rw [show U * G' * kronABC M c₀ * kronABC (G * kron2 a b) c
            = U * G' * kronABC (M * (G * kron2 a b)) (c₀ * c) from by
        rw [Matrix.mul_assoc (U * G'), kronABC_mul]]
      refine BCCutC.step h G' hG' ?_ _ (isUnitary2_mul hc₀ hc)
      rw [← Matrix.mul_assoc]
      exact CX2.step hM G hG a b ha hb

/-! ## 3. The cut profile of a word

`cutProf p w` splits `w` at every occurrence of the CROSSING letter `p`; the far-side
blocks are the maximal runs of the other letter, INCLUDING the empty ones at the ends
and between two adjacent crossings.  The pair is `(rightmost block, the rest)`. -/

/-- The cut profile of `w` with respect to the crossing letter `p`. -/
def cutProf (p : Bool) : List Bool → ℕ × List ℕ
  | [] => (0, [])
  | q :: w => if q = p then (0, (cutProf p w).1 :: (cutProf p w).2)
              else ((cutProf p w).1 + 1, (cutProf p w).2)

/-- The far-side block costs, head = rightmost block. -/
def cutCosts (p : Bool) (w : List Bool) : List ℕ := (cutProf p w).1 :: (cutProf p w).2

/-- **Counting identity 1: #blocks = #crossings + 1.** -/
theorem cutCosts_length (p : Bool) (w : List Bool) :
    (cutCosts p w).length = w.count p + 1 := by
  induction w with
  | nil => simp [cutCosts, cutProf]
  | cons q w ih =>
    simp only [cutCosts, cutProf, List.count_cons] at *
    by_cases h : q = p <;> simp [h] at * <;> omega

/-- **Counting identity 2: #crossings + Σ (block costs) = word length.** -/
theorem cutCosts_sum (p : Bool) (w : List Bool) :
    (cutCosts p w).sum + w.count p = w.length := by
  induction w with
  | nil => simp [cutCosts, cutProf]
  | cons q w ih =>
    simp only [cutCosts, cutProf, List.count_cons, List.sum_cons, List.length_cons] at *
    by_cases h : q = p <;> simp [h] at * <;> omega

/-- Flipping every letter exchanges the two cuts. -/
theorem cutCosts_map_not (w : List Bool) :
    cutCosts true (w.map not) = cutCosts false w := by
  have h : ∀ v : List Bool, cutProf true (v.map not) = cutProf false v := by
    intro v
    induction v with
    | nil => rfl
    | cons q v ih => cases q <;> simp [cutProf, ih]
  simp [cutCosts, h]

/-! ## 4. The profile is realised by the circuit -/

/-- **The word-to-budgeted-cut reduction.**  A CNOT word `w` puts its circuit in the
    AB|C cut form whose far-side blocks have EXACTLY the CNOT costs `cutCosts true w`,
    i.e. the lengths of the maximal AB-runs of `w`. -/
theorem cxWord_to_BCCutC {w : List Bool} {U : Mat8} (h : CXWord w U) :
    BCCutC (cutCosts true w) U := by
  induction h with
  | nil uA uB uC hA hB hC =>
      rw [singleQubitLayer_eq_kronABC]
      exact BCCutC.base (CX2.layer uA uB hA hB) uC hC
  | @consAB w rest G uA uB uC hA hB hC hG hrest ih =>
      rcases hG with rfl | rfl
      · rw [cx_ab_eq_kronABC, singleQubitLayer_eq_kronABC, Matrix.mul_assoc,
          kronABC_mul]
        exact BCCutC.absorb_cx ih cutCNOT_AB_4 (Or.inl rfl) uA uB _ hA hB
          (isUnitary2_mul isUnitary2_I2 hC)
      · rw [cx_ba_eq_kronABC, singleQubitLayer_eq_kronABC, Matrix.mul_assoc,
          kronABC_mul]
        exact BCCutC.absorb_cx ih CNOT_BA_4 (Or.inr rfl) uA uB _ hA hB
          (isUnitary2_mul isUnitary2_I2 hC)
  | @consBC w rest G uA uB uC hA hB hC hG hrest ih =>
      rw [singleQubitLayer_eq_kronABC]
      exact BCCutC.step ih G hG (CX2.layer uA uB hA hB) uC hC

/-- **The A↔C mirror, at the level of words.**  Conjugating by the A↔C relabelling
    flips every letter, so the AB-crossing cut of `w` is the BC-crossing cut of the
    mirrored circuit; only `BCCutC` is ever needed. -/
theorem cxWord_mirror {w : List Bool} {U : Mat8} (h : CXWord w U) :
    CXWord (w.map not) (swapMatAC * U * swapMatAC) := by
  induction h with
  | nil uA uB uC hA hB hC =>
      have hL : swapMatAC * singleQubitLayer uA uB uC * swapMatAC
          = singleQubitLayer uC uB uA := swapMatAC_kron3 uA uB uC
      rw [List.map_nil, hL]
      exact CXWord.nil uC uB uA hC hB hA
  | @consAB w rest G uA uB uC hA hB hC hG hrest ih =>
      have hL : swapMatAC * singleQubitLayer uA uB uC * swapMatAC
          = singleQubitLayer uC uB uA := swapMatAC_kron3 uA uB uC
      rw [List.map_cons, swapMatAC_conj_triple, hL]
      rcases hG with rfl | rfl
      · rw [swapMatAC_cx_ab]; exact CXWord.consBC uC uB uA hC hB hA (Or.inr rfl) ih
      · rw [swapMatAC_cx_ba]; exact CXWord.consBC uC uB uA hC hB hA (Or.inl rfl) ih
  | @consBC w rest G uA uB uC hA hB hC hG hrest ih =>
      have hL : swapMatAC * singleQubitLayer uA uB uC * swapMatAC
          = singleQubitLayer uC uB uA := swapMatAC_kron3 uA uB uC
      rw [List.map_cons, swapMatAC_conj_triple, hL]
      rcases hG with rfl | rfl
      · rw [swapMatAC_cx_bc]; exact CXWord.consAB uC uB uA hC hB hA (Or.inr rfl) ih
      · rw [swapMatAC_cx_cb]; exact CXWord.consAB uC uB uA hC hB hA (Or.inl rfl) ih

/-- Every word is realised by some circuit (all layers trivial, all CNOTs forward);
    used only to show the budgeted class is non-empty. -/
theorem exists_cxWord_of_word (w : List Bool) : ∃ U : Mat8, CXWord w U := by
  induction w with
  | nil => exact ⟨_, CXWord.nil 1 1 1 isUnitary2_one isUnitary2_one isUnitary2_one⟩
  | cons q w ih =>
      obtain ⟨U, hU⟩ := ih
      cases q
      · exact ⟨_, CXWord.consAB 1 1 1 isUnitary2_one isUnitary2_one isUnitary2_one
          (Or.inl rfl) hU⟩
      · exact ⟨_, CXWord.consBC 1 1 1 isUnitary2_one isUnitary2_one isUnitary2_one
          (Or.inl rfl) hU⟩

/-- A `CXWord` circuit is an `AchievableCircuit` with exactly `w.length` CNOTs. -/
theorem achievable_of_cxWord {w : List Bool} {U : Mat8} (h : CXWord w U) :
    AchievableCircuit w.length U := by
  induction h with
  | nil uA uB uC hA hB hC => exact AchievableCircuit.single_layer uA uB uC hA hB hC
  | consAB uA uB uC hA hB hC hG hrest ih =>
      refine AchievableCircuit.compose uA uB uC hA hB hC ?_ ih
      rcases hG with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  | consBC uA uB uC hA hB hC hG hrest ih =>
      refine AchievableCircuit.compose uA uB uC hA hB hC ?_ ih
      rcases hG with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))

/-! ## 5. The finite enumeration -/

/-- The budget shape the residual lands in: **4 far-side blocks (so exactly 3
    crossings), each of CNOT cost at most 2, of total cost at most 4.** -/
def GoodProfile (ks : List ℕ) : Prop :=
  ks.length = 4 ∧ (∀ k ∈ ks, k ≤ 2) ∧ ks.sum ≤ 4

instance : DecidablePred GoodProfile := by
  intro ks; unfold GoodProfile; infer_instance

/-- A good profile has exactly 3 crossings. -/
theorem count_eq_three_of_good {p : Bool} {w : List Bool}
    (h : GoodProfile (cutCosts p w)) : w.count p = 3 := by
  have h1 := cutCosts_length p w
  have h2 := h.1
  omega

/-- **THE ENUMERATION.**  A word of length at most 7 with at least 6 runs has, on the
    letter with FEWER occurrences, exactly 3 crossings, 4 far-side blocks, each of
    cost at most 2 and of total cost at most 4.

    Proved by exhausting all 255 words of length ≤ 7.  The ORDERED profiles that
    occur are the NINE lists

      [0,1,1,1] bababa      [1,1,1,0] ababab       [1,1,1,1] abababa, bababab
      [0,1,1,2] abababb…    [2,1,1,0] aababab…     [0,1,2,1] ababbab…
      [1,1,2,0] ababaab…    [0,2,1,1] abbabab…     [1,2,1,0] abaabab…

    covering all 16 residual words.  They fall into only three MULTISETS, but the
    POSITION of a cost-2 block matters: four of the nine have it in the INTERIOR, and
    `[1,1,1,0]` does not occur at length 7 at all.  `GoodProfile` is position-agnostic,
    so this theorem is unaffected; the finer statement is `Budget3Interior.IntProfile`
    / `HardProfile`, which separate exactly those cases. -/
theorem word_profile : ∀ w : List Bool, w.length ≤ 7 → 6 ≤ runs w →
    GoodProfile (cutCosts true w) ∨ GoodProfile (cutCosts false w) := by
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

/-- The three profiles, explicitly. -/
example : cutCosts true [false, true, false, true, false, true] = [1, 1, 1, 0] := by
  decide

example :
    cutCosts true [false, true, false, true, false, true, false] = [1, 1, 1, 1] := by
  decide

example :
    cutCosts true [false, false, true, false, true, false, true] = [2, 1, 1, 0] := by
  decide

/-! ## 6. The residual, and the one remaining analytic input -/

/-- The A↔C mirror leaves the `CCZ` objective unchanged; on the mirrored side the
    Hadamard of R1 sits on qubit A instead of qubit C. -/
lemma mirror_trace_eq (U : Mat8) :
    Matrix.trace (CCZ8 *
        (kron3 Hgate 1 1 * (swapMatAC * U * swapMatAC) * kron3 Hgate 1 1))
      = Matrix.trace (CCZ8 * (kron3 1 1 Hgate * U * kron3 1 1 Hgate)) := by
  rw [show kron3 Hgate 1 1 = swapMatAC * kron3 1 1 Hgate * swapMatAC from
        (swapMatAC_kron3 1 1 Hgate).symm,
      ← swapMatAC_conj_triple]
  exact trace_ccz_swapMatAC _

/-- **THE RESIDUAL OF `n = 6, 7`.**  A CNOT word of length at most 7 with at least 6
    runs puts its circuit — after the R1 Hadamard and, if the AB cut is the cheaper
    one, the A↔C mirror — into a budgeted cut form with a `GoodProfile`, WITHOUT
    changing the Toffoli objective.  This is the exact hypothesis `Budget3` consumes. -/
theorem word_residual {w : List Bool} {U : Mat8} (hw : CXWord w U)
    (hlen : w.length ≤ 7) (hr : 6 ≤ runs w) :
    ∃ (ks : List ℕ) (W : Mat8), GoodProfile ks ∧ BCCutC ks W ∧
      Complex.normSq (Matrix.trace (Uᴴ * CCX))
        = Complex.normSq (Matrix.trace (CCZ8 * W)) := by
  rcases word_profile w hlen hr with hg | hg
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

/-- `CutSqBound ks c` : every budgeted cut circuit with far-side costs `ks` has
    `|Tr(CCZ · U)|² ≤ c`.  The `BCCutC` analogue of `Block.PhiSqBound`. -/
def CutSqBound (ks : List ℕ) (c : ℝ) : Prop :=
  ∀ U : Mat8, BCCutC ks U → Complex.normSq (Matrix.trace (CCZ8 * U)) ≤ c

/-- **(BUDGET3) — the one remaining analytic input.**  Three crossings of one cut and
    four far-side blocks of two-qubit CNOT-cost at most 2 and total cost at most 4
    cannot beat `8cos(π/8)`.  NOT PROVED here; this is the statement of the gap.

    Tight: numerically the maximum over each of the three profiles is exactly
    `8cos(π/8)`.  The budget is load-bearing — dropping it makes the statement FALSE,
    since `F(3) = 8`. -/
def Budget3 : Prop :=
  ∀ ks : List ℕ, GoodProfile ks → CutSqBound ks (64 * Real.cos (Real.pi / 8) ^ 2)

/-- `Budget3` really is a statement about 3 crossings: a `GoodProfile` budgeted cut
    form is a `BCCut 3`. -/
theorem BCCutC.bcCut_three {ks : List ℕ} {U : Mat8} (h : BCCutC ks U)
    (hg : GoodProfile ks) : BCCut 3 U := by
  have := h.toBCCut
  rwa [hg.1] at this

/-! ### Non-vacuity

All three profiles of the enumeration are inhabited by genuine `AchievableCircuit`
circuits, so `Budget3` is not vacuously true. -/

theorem budget3_nonvacuous_ababab :
    ∃ U : Mat8, AchievableCircuit 6 U ∧ GoodProfile [1, 1, 1, 0] ∧
      BCCutC [1, 1, 1, 0] U := by
  obtain ⟨U, hU⟩ := exists_cxWord_of_word [false, true, false, true, false, true]
  refine ⟨U, achievable_of_cxWord hU, by decide, ?_⟩
  have h := cxWord_to_BCCutC hU
  rwa [show cutCosts true [false, true, false, true, false, true] = [1, 1, 1, 0] from
    by decide] at h

theorem budget3_nonvacuous_abababa :
    ∃ U : Mat8, AchievableCircuit 7 U ∧ GoodProfile [1, 1, 1, 1] ∧
      BCCutC [1, 1, 1, 1] U := by
  obtain ⟨U, hU⟩ :=
    exists_cxWord_of_word [false, true, false, true, false, true, false]
  refine ⟨U, achievable_of_cxWord hU, by decide, ?_⟩
  have h := cxWord_to_BCCutC hU
  rwa [show cutCosts true [false, true, false, true, false, true, false]
      = [1, 1, 1, 1] from by decide] at h

theorem budget3_nonvacuous_aababab :
    ∃ U : Mat8, AchievableCircuit 7 U ∧ GoodProfile [2, 1, 1, 0] ∧
      BCCutC [2, 1, 1, 0] U := by
  obtain ⟨U, hU⟩ :=
    exists_cxWord_of_word [false, false, true, false, true, false, true]
  refine ⟨U, achievable_of_cxWord hU, by decide, ?_⟩
  have h := cxWord_to_BCCutC hU
  rwa [show cutCosts true [false, false, true, false, true, false, true]
      = [2, 1, 1, 0] from by decide] at h

/-! ## 7. The assembly -/

/-- **The `n ≤ 7` trace bound**, on the two hypotheses `PhiFive` and `Budget3`.
    Every circuit of at most 7 CNOTs either has at most 5 runs — and then `PhiFive`
    bounds it through the run/block reduction — or has at least 6 runs, and then
    `word_residual` puts it in the `GoodProfile` budgeted cut class. -/
theorem achievable_trace_bound_seven (hphi : PhiFive) (hb3 : Budget3)
    {n : ℕ} (hn : n ≤ 7) {U : Mat8} (h : AchievableCircuit n U) :
    Complex.normSq (Matrix.trace (Uᴴ * CCX)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2 := by
  obtain ⟨w, hlen, hw⟩ := exists_cxWord h
  by_cases hr : runs w ≤ 5
  · exact trace_bound_of_runs_le_five hphi hw hr
  · obtain ⟨ks, W, hg, hcut, heq⟩ := word_residual hw (le_trans hlen hn) (by omega)
    rw [heq]
    exact hb3 ks hg W hcut

/-- **`d(6) = sin(π/8)`**, on `PhiFive` and `Budget3`. -/
theorem curve_six (hphi : PhiFive) (hb3 : Budget3) :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 6 U ∧ hsDistance U CCX = d}
      (Real.sin (Real.pi / 8)) := by
  constructor
  · exact ⟨Curve.witness4,
      AchievableCircuit.weaken (AchievableCircuit.weaken Curve.witness4_achievable),
      Curve.witness4_distance⟩
  · rintro d ⟨U, hU, rfl⟩
    exact trace_bound_implies_distance U
      (achievable_trace_bound_seven hphi hb3 (by norm_num) hU)

/-- **`d(7) = sin(π/8)`**, on `PhiFive` and `Budget3`. -/
theorem curve_seven (hphi : PhiFive) (hb3 : Budget3) :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 7 U ∧ hsDistance U CCX = d}
      (Real.sin (Real.pi / 8)) := by
  constructor
  · exact ⟨Curve.witness4,
      AchievableCircuit.weaken (AchievableCircuit.weaken
        (AchievableCircuit.weaken Curve.witness4_achievable)),
      Curve.witness4_distance⟩
  · rintro d ⟨U, hU, rfl⟩
    exact trace_bound_implies_distance U
      (achievable_trace_bound_seven hphi hb3 (by norm_num) hU)

/-- **The two open entries of the curve, closed on `PhiFive` + `Budget3`.** -/
theorem curve_six_seven (hphi : PhiFive) (hb3 : Budget3) :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 6 U ∧ hsDistance U CCX = d}
        (Real.sin (Real.pi / 8)) ∧
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 7 U ∧ hsDistance U CCX = d}
        (Real.sin (Real.pi / 8)) :=
  ⟨curve_six hphi hb3, curve_seven hphi hb3⟩

end Block

end
