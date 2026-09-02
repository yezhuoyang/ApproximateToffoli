/-
  ApproxToffoli.HP.FiveToFour
  Theorem 4.5: For diagonal gates, 5 neighbor gates → 4 unrestricted gates.

  Key definitions:
  - UnrestrictedCircuit: circuits with k general 2-qubit gates on ANY pair (AB, BC, or AC)
  - DiagNeighborImpl: a diagonal gate implementable with k neighbor gates

  Key theorems:
  - five_neighbor_to_four_unrestricted: Theorem 4.5 from Huang & Palsberg

  Reference: Huang & Palsberg (2026), Section 4.
-/

import ApproxToffoli.HP.EmbedLemmas
import ApproxToffoli.HP.Trichotomy
import ApproxToffoli.HP.DiagBlocks
-- Iter 1042: `paper_lemma_4_4` (the paper's native BC-AC-BC-AC-BC → BC-AC-AB-BC
-- reduction) lives in Lemma44. It used to be downstream of this file; see the
-- note on `IsDiag8` below for how that cycle was broken.
import ApproxToffoli.HP.Lemma44

open Matrix Complex

noncomputable section

/-! ## Unrestricted 2-qubit gate circuits

Like NeighborCircuit but allows AC gates in addition to AB and BC.
This corresponds to "unrestricted" 2-qubit gates in the paper. -/

/-- A 3-qubit unitary implementable with at most k unrestricted 2-qubit gates.
    Unlike NeighborCircuit, this allows gates on any pair: AB, BC, or AC.
    Single-qubit gates (product layers) are free and don't count toward k. -/
inductive UnrestrictedCircuit : ℕ → Mat8 → Prop where
  | product (uA uB uC : Mat2)
      (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC) :
      UnrestrictedCircuit 0 (singleQubitLayer uA uB uC)
  | weaken {n : ℕ} {U : Mat8} :
      UnrestrictedCircuit n U → UnrestrictedCircuit (n + 1) U
  | compose_AB {n : ℕ} {rest : Mat8} (V : Mat4) (uA uB uC : Mat2)
      (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC) :
      UnrestrictedCircuit n rest →
      UnrestrictedCircuit (n + 1) (rest * embedAB V * singleQubitLayer uA uB uC)
  | compose_BC {n : ℕ} {rest : Mat8} (V : Mat4) (uA uB uC : Mat2)
      (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC) :
      UnrestrictedCircuit n rest →
      UnrestrictedCircuit (n + 1) (rest * embedBC V * singleQubitLayer uA uB uC)
  | compose_AC {n : ℕ} {rest : Mat8} (V : Mat4) (uA uB uC : Mat2)
      (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC) :
      UnrestrictedCircuit n rest →
      UnrestrictedCircuit (n + 1) (rest * embedAC V * singleQubitLayer uA uB uC)

/-! ## UnitaryUnrestrictedCircuit: V-unitarity tracked in the constructor

The constructors of `UnrestrictedCircuit` do NOT require the inner 2-qubit
gate `V` to be unitary. To rule out spurious circuits with non-unitary `V`,
we introduce a parallel inductive type `UnitaryUnrestrictedCircuit` that
bakes `IsUnitary4 V` into each `compose_*` constructor. This avoids the
dependent-elimination issues of an auxiliary `Prop` predicate over the
weaker type, while letting `cases` inside Lemma C.1 closure proofs
directly extract `hV : IsUnitary4 V`.

The downstream chain (`four_unrestricted_implies_S4_or_S5`,
`four_neighbor_implies_S4_or_S5`) takes `UnitaryUnrestrictedCircuit` going
forward; a separate lift `unitary_of_neighborCircuit` provides the bridge
when V's are constructed from explicit unitary primitives. -/

/-- Like `UnrestrictedCircuit` but with each compose constructor's inner gate
    `V : Mat4` carrying an `IsUnitary4 V` proof. This is the genuinely-physical
    class of 3-qubit circuits with arbitrary 2-qubit unitary gates. -/
inductive UnitaryUnrestrictedCircuit : ℕ → Mat8 → Prop where
  | product (uA uB uC : Mat2)
      (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC) :
      UnitaryUnrestrictedCircuit 0 (singleQubitLayer uA uB uC)
  | weaken {n : ℕ} {U : Mat8} :
      UnitaryUnrestrictedCircuit n U → UnitaryUnrestrictedCircuit (n + 1) U
  | compose_AB {n : ℕ} {rest : Mat8} (V : Mat4) (hV : IsUnitary4 V)
      (uA uB uC : Mat2)
      (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC) :
      UnitaryUnrestrictedCircuit n rest →
      UnitaryUnrestrictedCircuit (n + 1)
        (rest * embedAB V * singleQubitLayer uA uB uC)
  | compose_BC {n : ℕ} {rest : Mat8} (V : Mat4) (hV : IsUnitary4 V)
      (uA uB uC : Mat2)
      (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC) :
      UnitaryUnrestrictedCircuit n rest →
      UnitaryUnrestrictedCircuit (n + 1)
        (rest * embedBC V * singleQubitLayer uA uB uC)
  | compose_AC {n : ℕ} {rest : Mat8} (V : Mat4) (hV : IsUnitary4 V)
      (uA uB uC : Mat2)
      (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC) :
      UnitaryUnrestrictedCircuit n rest →
      UnitaryUnrestrictedCircuit (n + 1)
        (rest * embedAC V * singleQubitLayer uA uB uC)

/-- Forgetful map: `UnitaryUnrestrictedCircuit` is in particular an
    `UnrestrictedCircuit` (forgets the V-unitarity payload). -/
theorem unrestricted_of_unitary {n : ℕ} {U : Mat8}
    (h : UnitaryUnrestrictedCircuit n U) : UnrestrictedCircuit n U := by
  induction h with
  | product uA uB uC hA hB hC =>
    exact .product uA uB uC hA hB hC
  | weaken _ ih => exact .weaken ih
  | compose_AB V _ uA uB uC hA hB hC _ ih =>
    exact .compose_AB V uA uB uC hA hB hC ih
  | compose_BC V _ uA uB uC hA hB hC _ ih =>
    exact .compose_BC V uA uB uC hA hB hC ih
  | compose_AC V _ uA uB uC hA hB hC _ ih =>
    exact .compose_AC V uA uB uC hA hB hC ih

/-- Soundness: any `UnitaryUnrestrictedCircuit n U` has `U` unitary.
    Proof by induction; each constructor's matrix is a product of unitaries
    (singleQubitLayer of unitary 1-qubit gates, embedXY of unitary V, and
    the recursive `rest`). -/
theorem isUnitary8_of_unitaryUnrestricted {n : ℕ} {U : Mat8}
    (h : UnitaryUnrestrictedCircuit n U) :
    U.conjTranspose * U = (1 : Mat8) := by
  induction h with
  | product uA uB uC hA hB hC =>
    exact singleQubitLayer_unitary uA uB uC hA hB hC
  | weaken _ ih => exact ih
  | @compose_AB n rest V hV uA uB uC hA hB hC _ ih =>
    have hSQL := singleQubitLayer_unitary uA uB uC hA hB hC
    have hEmb := embedAB_unitary V hV
    have outer_strip : ∀ A B : Mat8, A.conjTranspose * A = 1 →
        (A * B).conjTranspose * (A * B) = B.conjTranspose * B := by
      intro A B hA
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
          ← Matrix.mul_assoc A.conjTranspose, hA, Matrix.one_mul]
    rw [Matrix.mul_assoc rest (embedAB V) (singleQubitLayer uA uB uC),
        outer_strip rest (embedAB V * singleQubitLayer uA uB uC) ih,
        outer_strip (embedAB V) (singleQubitLayer uA uB uC) hEmb]
    exact hSQL
  | @compose_BC n rest V hV uA uB uC hA hB hC _ ih =>
    have hSQL := singleQubitLayer_unitary uA uB uC hA hB hC
    have hEmb := embedBC_unitary V hV
    have outer_strip : ∀ A B : Mat8, A.conjTranspose * A = 1 →
        (A * B).conjTranspose * (A * B) = B.conjTranspose * B := by
      intro A B hA
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
          ← Matrix.mul_assoc A.conjTranspose, hA, Matrix.one_mul]
    rw [Matrix.mul_assoc rest (embedBC V) (singleQubitLayer uA uB uC),
        outer_strip rest (embedBC V * singleQubitLayer uA uB uC) ih,
        outer_strip (embedBC V) (singleQubitLayer uA uB uC) hEmb]
    exact hSQL
  | @compose_AC n rest V hV uA uB uC hA hB hC _ ih =>
    have hSQL := singleQubitLayer_unitary uA uB uC hA hB hC
    have hEmb := embedAC_unitary V hV
    have outer_strip : ∀ A B : Mat8, A.conjTranspose * A = 1 →
        (A * B).conjTranspose * (A * B) = B.conjTranspose * B := by
      intro A B hA
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
          ← Matrix.mul_assoc A.conjTranspose, hA, Matrix.one_mul]
    rw [Matrix.mul_assoc rest (embedAC V) (singleQubitLayer uA uB uC),
        outer_strip rest (embedAC V * singleQubitLayer uA uB uC) ih,
        outer_strip (embedAC V) (singleQubitLayer uA uB uC) hEmb]
    exact hSQL

/-! ## Neighbor circuits embed into unrestricted circuits -/

/-- Any neighbor circuit is also an unrestricted circuit (with the same gate count) -/
theorem neighborCircuit_to_unrestricted {n : ℕ} {U : Mat8}
    (h : NeighborCircuit n U) : UnrestrictedCircuit n U := by
  induction h with
  | product uA uB uC hA hB hC => exact .product uA uB uC hA hB hC
  | weaken _ ih => exact .weaken ih
  | compose_AB V uA uB uC hA hB hC _ ih => exact .compose_AB V uA uB uC hA hB hC ih
  | compose_BC V uA uB uC hA hB hC _ ih => exact .compose_BC V uA uB uC hA hB hC ih

/-- Forgetful map: a `UnitaryNeighborCircuit` is in particular a `NeighborCircuit`. -/
theorem neighborCircuit_of_unitaryNeighbor {n : ℕ} {U : Mat8}
    (h : UnitaryNeighborCircuit n U) : NeighborCircuit n U := by
  induction h with
  | product uA uB uC hA hB hC => exact .product uA uB uC hA hB hC
  | weaken _ ih => exact .weaken ih
  | compose_AB V _ uA uB uC hA hB hC _ ih =>
    exact .compose_AB V uA uB uC hA hB hC ih
  | compose_BC V _ uA uB uC hA hB hC _ ih =>
    exact .compose_BC V uA uB uC hA hB hC ih

/-- Lift: every `UnitaryNeighborCircuit` is also a `UnitaryUnrestrictedCircuit`
    (allowing AC gates in addition to AB and BC). V-unitarity payloads carry through. -/
theorem unitaryNeighborCircuit_to_unitaryUnrestricted {n : ℕ} {U : Mat8}
    (h : UnitaryNeighborCircuit n U) : UnitaryUnrestrictedCircuit n U := by
  induction h with
  | product uA uB uC hA hB hC => exact .product uA uB uC hA hB hC
  | weaken _ ih => exact .weaken ih
  | compose_AB V hV uA uB uC hA hB hC _ ih =>
    exact .compose_AB V hV uA uB uC hA hB hC ih
  | compose_BC V hV uA uB uC hA hB hC _ ih =>
    exact .compose_BC V hV uA uB uC hA hB hC ih

/-! ## NeighborCircuit absorbs product layers on the right

A NeighborCircuit n U multiplied by a product layer on the right
is still NeighborCircuit n (the product layer is free). -/

/-- Right-multiplying by a product layer preserves NeighborCircuit gate count -/
theorem neighborCircuit_mul_product {n : ℕ} {U : Mat8}
    (h : NeighborCircuit n U) (dA dB dC : Mat2)
    (hdA : IsUnitary2 dA) (hdB : IsUnitary2 dB) (hdC : IsUnitary2 dC) :
    NeighborCircuit n (U * singleQubitLayer dA dB dC) := by
  induction h with
  | product uA uB uC hA hB hC =>
    rw [singleQubitLayer_mul]
    exact .product _ _ _ (isUnitary2_mul hA hdA) (isUnitary2_mul hB hdB) (isUnitary2_mul hC hdC)
  | weaken _ ih =>
    exact .weaken ih
  | @compose_AB _ rest V uA uB uC hA hB hC hrest _ =>
    show NeighborCircuit _
      (rest * embedAB V * singleQubitLayer uA uB uC * singleQubitLayer dA dB dC)
    rw [mul_assoc (rest * embedAB V), singleQubitLayer_mul]
    exact .compose_AB V _ _ _ (isUnitary2_mul hA hdA) (isUnitary2_mul hB hdB)
      (isUnitary2_mul hC hdC) hrest
  | @compose_BC _ rest V uA uB uC hA hB hC hrest _ =>
    show NeighborCircuit _
      (rest * embedBC V * singleQubitLayer uA uB uC * singleQubitLayer dA dB dC)
    rw [mul_assoc (rest * embedBC V), singleQubitLayer_mul]
    exact .compose_BC V _ _ _ (isUnitary2_mul hA hdA) (isUnitary2_mul hB hdB)
      (isUnitary2_mul hC hdC) hrest

/-- Right-multiplying by a product layer preserves UnrestrictedCircuit gate count -/
theorem unrestrictedCircuit_mul_product {n : ℕ} {U : Mat8}
    (h : UnrestrictedCircuit n U) (dA dB dC : Mat2)
    (hdA : IsUnitary2 dA) (hdB : IsUnitary2 dB) (hdC : IsUnitary2 dC) :
    UnrestrictedCircuit n (U * singleQubitLayer dA dB dC) := by
  induction h with
  | product uA uB uC hA hB hC =>
    rw [singleQubitLayer_mul]
    exact .product _ _ _ (isUnitary2_mul hA hdA) (isUnitary2_mul hB hdB) (isUnitary2_mul hC hdC)
  | weaken _ ih =>
    exact .weaken ih
  | @compose_AB _ rest V uA uB uC hA hB hC hrest _ =>
    show UnrestrictedCircuit _
      (rest * embedAB V * singleQubitLayer uA uB uC * singleQubitLayer dA dB dC)
    rw [mul_assoc (rest * embedAB V), singleQubitLayer_mul]
    exact .compose_AB V _ _ _ (isUnitary2_mul hA hdA) (isUnitary2_mul hB hdB)
      (isUnitary2_mul hC hdC) hrest
  | @compose_BC _ rest V uA uB uC hA hB hC hrest _ =>
    show UnrestrictedCircuit _
      (rest * embedBC V * singleQubitLayer uA uB uC * singleQubitLayer dA dB dC)
    rw [mul_assoc (rest * embedBC V), singleQubitLayer_mul]
    exact .compose_BC V _ _ _ (isUnitary2_mul hA hdA) (isUnitary2_mul hB hdB)
      (isUnitary2_mul hC hdC) hrest
  | @compose_AC _ rest V uA uB uC hA hB hC hrest _ =>
    show UnrestrictedCircuit _
      (rest * embedAC V * singleQubitLayer uA uB uC * singleQubitLayer dA dB dC)
    rw [mul_assoc (rest * embedAC V), singleQubitLayer_mul]
    exact .compose_AC V _ _ _ (isUnitary2_mul hA hdA) (isUnitary2_mul hB hdB)
      (isUnitary2_mul hC hdC) hrest

/-- Stripping a product layer from an unrestricted circuit.
    If U * P is an n-gate unrestricted circuit, then so is U. -/
theorem unrestrictedCircuit_of_mul_product {n : ℕ} {U : Mat8}
    {dA dB dC : Mat2} (hdA : IsUnitary2 dA) (hdB : IsUnitary2 dB) (hdC : IsUnitary2 dC)
    (h : UnrestrictedCircuit n (U * singleQubitLayer dA dB dC)) :
    UnrestrictedCircuit n U := by
  have hAct : dA * dA.conjTranspose = 1 := by
    have := isUnitary2_conjTranspose hdA; unfold IsUnitary2 at this
    rwa [conjTranspose_conjTranspose] at this
  have hBct : dB * dB.conjTranspose = 1 := by
    have := isUnitary2_conjTranspose hdB; unfold IsUnitary2 at this
    rwa [conjTranspose_conjTranspose] at this
  have hCct : dC * dC.conjTranspose = 1 := by
    have := isUnitary2_conjTranspose hdC; unfold IsUnitary2 at this
    rwa [conjTranspose_conjTranspose] at this
  have key : U * singleQubitLayer dA dB dC *
      singleQubitLayer dA.conjTranspose dB.conjTranspose dC.conjTranspose = U := by
    rw [mul_assoc, singleQubitLayer_mul, hAct, hBct, hCct]
    show U * singleQubitLayer I₂ I₂ I₂ = U
    rw [singleQubitLayer_one, mul_one]
  rw [← key]
  exact unrestrictedCircuit_mul_product h _ _ _
    (isUnitary2_conjTranspose hdA) (isUnitary2_conjTranspose hdB) (isUnitary2_conjTranspose hdC)

/-! ## IsUnitary2 for identity (re-export from Kron2.lean for backward compat) -/

/-! ## Circuit-level gate merging

If the last two gates in a NeighborCircuit are the same type (both AB or both BC),
they can be merged, reducing the gate count by 1.
Uses embedAB_merge + neighborCircuit_mul_product. -/

/-- Consecutive AB-AB gates merge: reduces gate count by 1 -/
theorem neighborCircuit_merge_AB_AB {n : ℕ} {rest : Mat8}
    (V₁ V₂ : Mat4) (uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ : Mat2)
    (hA₁ : IsUnitary2 uA₁) (hB₁ : IsUnitary2 uB₁) (hC₁ : IsUnitary2 uC₁)
    (hA₂ : IsUnitary2 uA₂) (hB₂ : IsUnitary2 uB₂) (hC₂ : IsUnitary2 uC₂)
    (hrest : NeighborCircuit n rest) :
    NeighborCircuit (n + 1)
      (rest * embedAB V₁ * singleQubitLayer uA₁ uB₁ uC₁ *
       embedAB V₂ * singleQubitLayer uA₂ uB₂ uC₂) := by
  -- Re-associate to isolate the merge pattern
  have eq1 : rest * embedAB V₁ * singleQubitLayer uA₁ uB₁ uC₁ *
      embedAB V₂ * singleQubitLayer uA₂ uB₂ uC₂ =
      rest * (embedAB V₁ * singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂) *
      singleQubitLayer uA₂ uB₂ uC₂ := by simp only [mul_assoc]
  rw [eq1, embedAB_merge]
  -- Re-associate to expose (rest * P_C) * embedAB(...) * P₂
  have eq2 : rest * (singleQubitLayer I₂ I₂ uC₁ *
      embedAB (V₁ * (kron2 uA₁ uB₁ * V₂))) * singleQubitLayer uA₂ uB₂ uC₂ =
      (rest * singleQubitLayer I₂ I₂ uC₁) *
      embedAB (V₁ * (kron2 uA₁ uB₁ * V₂)) * singleQubitLayer uA₂ uB₂ uC₂ := by
    simp only [mul_assoc]
  rw [eq2]
  exact .compose_AB _ _ _ _ hA₂ hB₂ hC₂
    (neighborCircuit_mul_product hrest I₂ I₂ uC₁ isUnitary2_one isUnitary2_one hC₁)

/-- Consecutive BC-BC gates merge: reduces gate count by 1 -/
theorem neighborCircuit_merge_BC_BC {n : ℕ} {rest : Mat8}
    (V₁ V₂ : Mat4) (uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ : Mat2)
    (hA₁ : IsUnitary2 uA₁) (hB₁ : IsUnitary2 uB₁) (hC₁ : IsUnitary2 uC₁)
    (hA₂ : IsUnitary2 uA₂) (hB₂ : IsUnitary2 uB₂) (hC₂ : IsUnitary2 uC₂)
    (hrest : NeighborCircuit n rest) :
    NeighborCircuit (n + 1)
      (rest * embedBC V₁ * singleQubitLayer uA₁ uB₁ uC₁ *
       embedBC V₂ * singleQubitLayer uA₂ uB₂ uC₂) := by
  have eq1 : rest * embedBC V₁ * singleQubitLayer uA₁ uB₁ uC₁ *
      embedBC V₂ * singleQubitLayer uA₂ uB₂ uC₂ =
      rest * (embedBC V₁ * singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂) *
      singleQubitLayer uA₂ uB₂ uC₂ := by simp only [mul_assoc]
  rw [eq1, embedBC_merge]
  have eq2 : rest * (singleQubitLayer uA₁ I₂ I₂ *
      embedBC (V₁ * (kron2 uB₁ uC₁ * V₂))) * singleQubitLayer uA₂ uB₂ uC₂ =
      (rest * singleQubitLayer uA₁ I₂ I₂) *
      embedBC (V₁ * (kron2 uB₁ uC₁ * V₂)) * singleQubitLayer uA₂ uB₂ uC₂ := by
    simp only [mul_assoc]
  rw [eq2]
  exact .compose_BC _ _ _ _ hA₂ hB₂ hC₂
    (neighborCircuit_mul_product hrest uA₁ I₂ I₂ hA₁ isUnitary2_one isUnitary2_one)

/-! ## UnrestrictedCircuit gate merging

Same-type consecutive gates in UnrestrictedCircuit merge, reducing gate count by 1. -/

/-- Consecutive AB-AB gates merge in UnrestrictedCircuit -/
theorem unrestrictedCircuit_merge_AB_AB {n : ℕ} {rest : Mat8}
    (V₁ V₂ : Mat4) (uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ : Mat2)
    (hA₁ : IsUnitary2 uA₁) (hB₁ : IsUnitary2 uB₁) (hC₁ : IsUnitary2 uC₁)
    (hA₂ : IsUnitary2 uA₂) (hB₂ : IsUnitary2 uB₂) (hC₂ : IsUnitary2 uC₂)
    (hrest : UnrestrictedCircuit n rest) :
    UnrestrictedCircuit (n + 1)
      (rest * embedAB V₁ * singleQubitLayer uA₁ uB₁ uC₁ *
       embedAB V₂ * singleQubitLayer uA₂ uB₂ uC₂) := by
  have eq1 : rest * embedAB V₁ * singleQubitLayer uA₁ uB₁ uC₁ *
      embedAB V₂ * singleQubitLayer uA₂ uB₂ uC₂ =
      rest * (embedAB V₁ * singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂) *
      singleQubitLayer uA₂ uB₂ uC₂ := by simp only [mul_assoc]
  rw [eq1, embedAB_merge]
  have eq2 : rest * (singleQubitLayer I₂ I₂ uC₁ *
      embedAB (V₁ * (kron2 uA₁ uB₁ * V₂))) * singleQubitLayer uA₂ uB₂ uC₂ =
      (rest * singleQubitLayer I₂ I₂ uC₁) *
      embedAB (V₁ * (kron2 uA₁ uB₁ * V₂)) * singleQubitLayer uA₂ uB₂ uC₂ := by
    simp only [mul_assoc]
  rw [eq2]
  exact .compose_AB _ _ _ _ hA₂ hB₂ hC₂
    (unrestrictedCircuit_mul_product hrest I₂ I₂ uC₁ isUnitary2_one isUnitary2_one hC₁)

/-- Consecutive BC-BC gates merge in UnrestrictedCircuit -/
theorem unrestrictedCircuit_merge_BC_BC {n : ℕ} {rest : Mat8}
    (V₁ V₂ : Mat4) (uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ : Mat2)
    (hA₁ : IsUnitary2 uA₁) (hB₁ : IsUnitary2 uB₁) (hC₁ : IsUnitary2 uC₁)
    (hA₂ : IsUnitary2 uA₂) (hB₂ : IsUnitary2 uB₂) (hC₂ : IsUnitary2 uC₂)
    (hrest : UnrestrictedCircuit n rest) :
    UnrestrictedCircuit (n + 1)
      (rest * embedBC V₁ * singleQubitLayer uA₁ uB₁ uC₁ *
       embedBC V₂ * singleQubitLayer uA₂ uB₂ uC₂) := by
  have eq1 : rest * embedBC V₁ * singleQubitLayer uA₁ uB₁ uC₁ *
      embedBC V₂ * singleQubitLayer uA₂ uB₂ uC₂ =
      rest * (embedBC V₁ * singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂) *
      singleQubitLayer uA₂ uB₂ uC₂ := by simp only [mul_assoc]
  rw [eq1, embedBC_merge]
  have eq2 : rest * (singleQubitLayer uA₁ I₂ I₂ *
      embedBC (V₁ * (kron2 uB₁ uC₁ * V₂))) * singleQubitLayer uA₂ uB₂ uC₂ =
      (rest * singleQubitLayer uA₁ I₂ I₂) *
      embedBC (V₁ * (kron2 uB₁ uC₁ * V₂)) * singleQubitLayer uA₂ uB₂ uC₂ := by
    simp only [mul_assoc]
  rw [eq2]
  exact .compose_BC _ _ _ _ hA₂ hB₂ hC₂
    (unrestrictedCircuit_mul_product hrest uA₁ I₂ I₂ hA₁ isUnitary2_one isUnitary2_one)

/-- Consecutive AC-AC gates merge in UnrestrictedCircuit -/
theorem unrestrictedCircuit_merge_AC_AC {n : ℕ} {rest : Mat8}
    (V₁ V₂ : Mat4) (uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ : Mat2)
    (hA₁ : IsUnitary2 uA₁) (hB₁ : IsUnitary2 uB₁) (hC₁ : IsUnitary2 uC₁)
    (hA₂ : IsUnitary2 uA₂) (hB₂ : IsUnitary2 uB₂) (hC₂ : IsUnitary2 uC₂)
    (hrest : UnrestrictedCircuit n rest) :
    UnrestrictedCircuit (n + 1)
      (rest * embedAC V₁ * singleQubitLayer uA₁ uB₁ uC₁ *
       embedAC V₂ * singleQubitLayer uA₂ uB₂ uC₂) := by
  have eq1 : rest * embedAC V₁ * singleQubitLayer uA₁ uB₁ uC₁ *
      embedAC V₂ * singleQubitLayer uA₂ uB₂ uC₂ =
      rest * (embedAC V₁ * singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂) *
      singleQubitLayer uA₂ uB₂ uC₂ := by simp only [mul_assoc]
  rw [eq1, embedAC_merge]
  have eq2 : rest * (singleQubitLayer I₂ uB₁ I₂ *
      embedAC (V₁ * (kron2 uA₁ uC₁ * V₂))) * singleQubitLayer uA₂ uB₂ uC₂ =
      (rest * singleQubitLayer I₂ uB₁ I₂) *
      embedAC (V₁ * (kron2 uA₁ uC₁ * V₂)) * singleQubitLayer uA₂ uB₂ uC₂ := by
    simp only [mul_assoc]
  rw [eq2]
  exact .compose_AC _ _ _ _ hA₂ hB₂ hC₂
    (unrestrictedCircuit_mul_product hrest I₂ uB₁ I₂ isUnitary2_one hB₁ isUnitary2_one)

/-! ## SWAP conjugation distributes over matrix products -/

/-- SWAP_BC is a left involution: SWAP * (SWAP * X) = X -/
theorem swap_bc_cancel (X : Mat8) :
    SWAP_BC * (SWAP_BC * X) = X := by
  rw [← mul_assoc, SWAP_BC_sq, one_mul]

/-- SWAP conjugation distributes over products: SWAP(AB)SWAP = (SWAP·A·SWAP)(SWAP·B·SWAP) -/
theorem swap_bc_conj_distrib (A B : Mat8) :
    SWAP_BC * (A * B) * SWAP_BC =
    (SWAP_BC * A * SWAP_BC) * (SWAP_BC * B * SWAP_BC) := by
  simp only [mul_assoc, swap_bc_cancel]

/-- Local alias of `swap_bc_conj_distrib` for use within this file (where the
    historical name `swap_conj_distrib` was used; renamed to avoid clash with
    the private version in HP.EmbedLemmas). -/
private theorem swap_conj_distrib (A B : Mat8) :
    SWAP_BC * (A * B) * SWAP_BC =
    (SWAP_BC * A * SWAP_BC) * (SWAP_BC * B * SWAP_BC) :=
  swap_bc_conj_distrib A B

/-! ## SWAP conjugation of NeighborCircuit → UnrestrictedCircuit

Conjugating a neighbor circuit by SWAP_BC gives an unrestricted circuit:
AB gates become AC gates, BC gates stay BC (with conjugated argument). -/

/-- SWAP_BC conjugation of a NeighborCircuit gives an UnrestrictedCircuit
    with the same gate count -/
theorem swap_neighborCircuit_unrestricted {n : ℕ} {U : Mat8}
    (h : NeighborCircuit n U) :
    UnrestrictedCircuit n (SWAP_BC * U * SWAP_BC) := by
  induction h with
  | product uA uB uC hA hB hC =>
    rw [swap_bc_singleQubitLayer]
    exact .product uA uC uB hA hC hB
  | weaken _ ih =>
    exact .weaken ih
  | @compose_AB _ rest V uA uB uC hA hB hC _ ih =>
    show UnrestrictedCircuit _
      (SWAP_BC * (rest * embedAB V * singleQubitLayer uA uB uC) * SWAP_BC)
    rw [swap_conj_distrib, swap_conj_distrib, swap_bc_embedAB, swap_bc_singleQubitLayer]
    exact .compose_AC V uA uC uB hA hC hB ih
  | @compose_BC _ rest V uA uB uC hA hB hC _ ih =>
    show UnrestrictedCircuit _
      (SWAP_BC * (rest * embedBC V * singleQubitLayer uA uB uC) * SWAP_BC)
    rw [swap_conj_distrib, swap_conj_distrib, swap_bc_embedBC, swap_bc_singleQubitLayer]
    exact .compose_BC (SWAP_4 * V * SWAP_4) uA uC uB hA hC hB ih

/-! ## SWAP conjugation preserves UnrestrictedCircuit

Conjugating an unrestricted circuit by SWAP_BC gives another unrestricted circuit:
AB ↔ AC are swapped, BC stays (with conjugated argument). -/

/-- SWAP_BC conjugation preserves UnrestrictedCircuit gate count -/
theorem swap_unrestrictedCircuit {n : ℕ} {U : Mat8}
    (h : UnrestrictedCircuit n U) :
    UnrestrictedCircuit n (SWAP_BC * U * SWAP_BC) := by
  induction h with
  | product uA uB uC hA hB hC =>
    rw [swap_bc_singleQubitLayer]
    exact .product uA uC uB hA hC hB
  | weaken _ ih =>
    exact .weaken ih
  | @compose_AB _ rest V uA uB uC hA hB hC _ ih =>
    show UnrestrictedCircuit _
      (SWAP_BC * (rest * embedAB V * singleQubitLayer uA uB uC) * SWAP_BC)
    rw [swap_conj_distrib, swap_conj_distrib, swap_bc_embedAB, swap_bc_singleQubitLayer]
    exact .compose_AC V uA uC uB hA hC hB ih
  | @compose_BC _ rest V uA uB uC hA hB hC _ ih =>
    show UnrestrictedCircuit _
      (SWAP_BC * (rest * embedBC V * singleQubitLayer uA uB uC) * SWAP_BC)
    rw [swap_conj_distrib, swap_conj_distrib, swap_bc_embedBC, swap_bc_singleQubitLayer]
    exact .compose_BC (SWAP_4 * V * SWAP_4) uA uC uB hA hC hB ih
  | @compose_AC _ rest V uA uB uC hA hB hC _ ih =>
    show UnrestrictedCircuit _
      (SWAP_BC * (rest * embedAC V * singleQubitLayer uA uB uC) * SWAP_BC)
    rw [swap_conj_distrib, swap_conj_distrib, swap_bc_embedAC, swap_bc_singleQubitLayer]
    exact .compose_AB V uA uC uB hA hC hB ih

/-! ## `IsDiag8` and the A-block facts

Moved to `HP/DiagBlocks.lean` (iter 1042) so that `HP/Lemma44.lean` can depend
on them without depending on this file — which is what lets this file import
`Lemma44` and use `paper_lemma_4_4` in the 5→4 reduction below. -/

/-- block00 of a DiagGate3's matrix is the 4×4 diagonal whose entries are
    D.d 0, D.d 1, D.d 2, D.d 3. -/
theorem block00_diagGate3_toMatrix (D : DiagGate3) :
    block00 D.toMatrix =
      Matrix.diagonal (fun i : Fin 4 => D.d ⟨i.val, by omega⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block00, DiagGate3.toMatrix, Matrix.of_apply, Matrix.diagonal_apply]

/-- block11 of a DiagGate3's matrix is the 4×4 diagonal whose entries are
    D.d 4, D.d 5, D.d 6, D.d 7. -/
theorem block11_diagGate3_toMatrix (D : DiagGate3) :
    block11 D.toMatrix =
      Matrix.diagonal (fun i : Fin 4 => D.d ⟨i.val + 4, by omega⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block11, DiagGate3.toMatrix, Matrix.of_apply, Matrix.diagonal_apply]

/-- The "Eq 21" diagonal: `(block00 D.toMatrix)† · (block11 D.toMatrix)` is the
    4×4 diagonal whose entries are `conj(D.d i) · D.d (i+4)` for i : Fin 4.
    For unit-modulus D.d, this equals `D.d (i+4) / D.d i`. -/
theorem block00_conjTranspose_mul_block11_diagGate3 (D : DiagGate3) :
    (block00 D.toMatrix).conjTranspose * (block11 D.toMatrix) =
      Matrix.diagonal (fun i : Fin 4 =>
        starRingEnd ℂ (D.d ⟨i.val, by omega⟩) * D.d ⟨i.val + 4, by omega⟩) := by
  rw [block00_diagGate3_toMatrix, block11_diagGate3_toMatrix,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  rfl

/-- Conjugation form: when M is wrapped between embedBC factors with V₁ unitary,
    the diagonal-block product `(block00 ...)† · (block11 ...)` collapses the V₁
    factor (V₁†·V₁ = 1) and exposes V₄ on both sides as the similarity transform.
    This is the structural backbone for paper's Eq 21 in the BC-AC-AB-BC case. -/
theorem block00_conjTranspose_mul_block11_embedBC (V₁ V₄ : Mat4) (M : Mat8)
    (hV₁ : IsUnitary4 V₁) :
    (block00 (embedBC V₁ * M * embedBC V₄)).conjTranspose *
      (block11 (embedBC V₁ * M * embedBC V₄)) =
      V₄.conjTranspose * ((block00 M).conjTranspose * (block11 M)) * V₄ := by
  rw [block00_embedBC_mul_embedBC, block11_embedBC_mul_embedBC]
  have h_assoc : (V₁ * block00 M * V₄).conjTranspose * (V₁ * block11 M * V₄) =
      V₄.conjTranspose * (block00 M).conjTranspose *
        (V₁.conjTranspose * V₁) * block11 M * V₄ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    noncomm_ring
  rw [h_assoc, hV₁]
  noncomm_ring

/-- Eq 21 RHS for BC-AC-AB-BC: combining Steps 118 + 119, when the inner factor M
    has `block00 M = kron2 P₀ Q₀` and `block11 M = kron2 P₁ Q₁`, the diagonal-block
    product of `embedBC V₁ · M · embedBC V₄` reduces to a single tensor under
    unitary similarity by V₄: `V₄† · kron2 (P₀†·P₁) (Q₀†·Q₁) · V₄`. This matches
    paper's Eq 21 RHS. -/
theorem block00_conjTranspose_mul_block11_embedBC_kron2
    (V₁ V₄ : Mat4) (M : Mat8) (hV₁ : IsUnitary4 V₁)
    (P₀ P₁ Q₀ Q₁ : Mat2)
    (h00 : block00 M = kron2 P₀ Q₀) (h11 : block11 M = kron2 P₁ Q₁) :
    (block00 (embedBC V₁ * M * embedBC V₄)).conjTranspose *
      (block11 (embedBC V₁ * M * embedBC V₄)) =
      V₄.conjTranspose *
        kron2 (P₀.conjTranspose * P₁) (Q₀.conjTranspose * Q₁) * V₄ := by
  rw [block00_conjTranspose_mul_block11_embedBC V₁ V₄ M hV₁]
  rw [h00, h11, kron2_conjTranspose_mul_kron2]

/-- Helper: extract the middle factor from a BC-(...)-BC product using unitarity.
    If `D = embedBC V₁ · M · embedBC V₄` for unitary V₁, V₄, then
    `M = embedBC V₁† · D · embedBC V₄†`. Used in the BC-AC-AB-BC canonical case
    of Theorem 6.2 to reformulate a 4-gate factorization for `eq19_to_eq20`. -/
theorem extract_middle_from_embedBC (M D : Mat8) (V₁ V₄ : Mat4)
    (hV₁ : IsUnitary4 V₁) (hV₄ : IsUnitary4 V₄)
    (h : D = embedBC V₁ * M * embedBC V₄) :
    M = embedBC V₁.conjTranspose * D * embedBC V₄.conjTranspose := by
  have hV₁₁ : embedBC V₁.conjTranspose * embedBC V₁ = 1 := by
    rw [embedBC_mul, hV₁, embedBC_one]
  have hV₄_right : V₄ * V₄.conjTranspose = 1 := mul_eq_one_comm.mp hV₄
  have hV₄₁ : embedBC V₄ * embedBC V₄.conjTranspose = 1 := by
    rw [embedBC_mul, hV₄_right, embedBC_one]
  rw [h]
  rw [show embedBC V₁.conjTranspose * (embedBC V₁ * M * embedBC V₄) * embedBC V₄.conjTranspose
       = (embedBC V₁.conjTranspose * embedBC V₁) * M * (embedBC V₄ * embedBC V₄.conjTranspose)
       by noncomm_ring]
  rw [hV₁₁, hV₄₁, Matrix.one_mul, Matrix.mul_one]

/-! ## SWAP_BC conjugation of DiagGate3

SWAP_BC * D.toMatrix * SWAP_BC = D.swapBC.toMatrix.
This connects the algebraic swapBC on DiagGate3 to 8×8 matrix SWAP conjugation. -/

/-- SWAP_BC conjugation of a DiagGate3 gives the permuted DiagGate3 -/
theorem swapBC_toMatrix (D : DiagGate3) :
    SWAP_BC * D.toMatrix * SWAP_BC = D.swapBC.toMatrix := by
  ext i j
  simp only [DiagGate3.toMatrix, DiagGate3.swapBC, DiagGate3.swapBC_d]
  unfold SWAP_BC swap_bc_perm
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.diagonal_apply, Fin.sum_univ_eight]
  fin_cases i <;> fin_cases j <;> simp <;> try rfl

/-- IsDiag8 is preserved by SWAP_BC conjugation -/
theorem isDiag8_swap_bc (D : Mat8) (hD : IsDiag8 D) :
    IsDiag8 (SWAP_BC * D * SWAP_BC) := by
  obtain ⟨Dg, rfl⟩ := hD
  exact ⟨Dg.swapBC, swapBC_toMatrix Dg⟩

/-- SWAP_AC conjugation of a DiagGate3 gives the permuted DiagGate3 -/
theorem swapAC_toMatrix (D : DiagGate3) :
    SWAP_AC * D.toMatrix * SWAP_AC = D.swapAC.toMatrix := by
  ext i j
  simp only [DiagGate3.toMatrix, DiagGate3.swapAC, DiagGate3.swapAC_d]
  unfold SWAP_AC swap_ac_perm
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.diagonal_apply, Fin.sum_univ_eight]
  fin_cases i <;> fin_cases j <;> simp <;> try rfl

/-- SWAP_AB conjugation of a DiagGate3 gives the permuted DiagGate3 -/
theorem swapAB_toMatrix (D : DiagGate3) :
    SWAP_AB * D.toMatrix * SWAP_AB = D.swapAB.toMatrix := by
  ext i j
  simp only [DiagGate3.toMatrix, DiagGate3.swapAB, DiagGate3.swapAB_d]
  unfold SWAP_AB swap_ab_perm
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.diagonal_apply, Fin.sum_univ_eight]
  fin_cases i <;> fin_cases j <;> simp <;> try rfl

/-! ## SWAP_AC conjugation infrastructure

SWAP_AC swaps qubits A,C. Under this conjugation:
- embedAB(V) → embedBC(SWAP₄·V·SWAP₄)
- embedBC(V) → embedAB(SWAP₄·V·SWAP₄)
This converts BABAB patterns to ABABA patterns. -/

/-- SWAP_AC is a left involution: SWAP_AC * (SWAP_AC * X) = X -/
theorem swap_ac_cancel (X : Mat8) :
    SWAP_AC * (SWAP_AC * X) = X := by
  calc SWAP_AC * (SWAP_AC * X) = (SWAP_AC * SWAP_AC) * X := (mul_assoc _ _ _).symm
    _ = 1 * X := by rw [SWAP_AC_sq]
    _ = X := one_mul _

/-- SWAP_AC conjugation distributes over products -/
theorem swap_ac_conj_distrib (A B : Mat8) :
    SWAP_AC * (A * B) * SWAP_AC =
    (SWAP_AC * A * SWAP_AC) * (SWAP_AC * B * SWAP_AC) := by
  simp only [mul_assoc, swap_ac_cancel]

/-- SWAP_AC conjugation of a NeighborCircuit gives an UnrestrictedCircuit.
    AB gates become BC gates and vice versa (both neighbor), so
    it actually gives a NeighborCircuit, which embeds into UnrestrictedCircuit. -/
theorem swap_ac_neighborCircuit_unrestricted {n : ℕ} {U : Mat8}
    (h : NeighborCircuit n U) :
    UnrestrictedCircuit n (SWAP_AC * U * SWAP_AC) := by
  induction h with
  | product uA uB uC hA hB hC =>
    rw [swap_ac_singleQubitLayer]
    exact .product uC uB uA hC hB hA
  | weaken _ ih =>
    exact .weaken ih
  | @compose_AB _ rest V uA uB uC hA hB hC _ ih =>
    show UnrestrictedCircuit _
      (SWAP_AC * (rest * embedAB V * singleQubitLayer uA uB uC) * SWAP_AC)
    rw [swap_ac_conj_distrib, swap_ac_conj_distrib, swap_ac_embedAB, swap_ac_singleQubitLayer]
    exact .compose_BC (SWAP_4 * V * SWAP_4) uC uB uA hC hB hA ih
  | @compose_BC _ rest V uA uB uC hA hB hC _ ih =>
    show UnrestrictedCircuit _
      (SWAP_AC * (rest * embedBC V * singleQubitLayer uA uB uC) * SWAP_AC)
    rw [swap_ac_conj_distrib, swap_ac_conj_distrib, swap_ac_embedBC, swap_ac_singleQubitLayer]
    exact .compose_AB (SWAP_4 * V * SWAP_4) uC uB uA hC hB hA ih

/-- SWAP_AC conjugation preserves NeighborCircuit (AB↔BC, both neighbor pairs) -/
theorem swap_ac_neighborCircuit {n : ℕ} {U : Mat8}
    (h : NeighborCircuit n U) :
    NeighborCircuit n (SWAP_AC * U * SWAP_AC) := by
  induction h with
  | product uA uB uC hA hB hC =>
    rw [swap_ac_singleQubitLayer]
    exact .product uC uB uA hC hB hA
  | weaken _ ih =>
    exact .weaken ih
  | @compose_AB _ rest V uA uB uC hA hB hC _ ih =>
    show NeighborCircuit _
      (SWAP_AC * (rest * embedAB V * singleQubitLayer uA uB uC) * SWAP_AC)
    rw [swap_ac_conj_distrib, swap_ac_conj_distrib, swap_ac_embedAB, swap_ac_singleQubitLayer]
    exact .compose_BC (SWAP_4 * V * SWAP_4) uC uB uA hC hB hA ih
  | @compose_BC _ rest V uA uB uC hA hB hC _ ih =>
    show NeighborCircuit _
      (SWAP_AC * (rest * embedBC V * singleQubitLayer uA uB uC) * SWAP_AC)
    rw [swap_ac_conj_distrib, swap_ac_conj_distrib, swap_ac_embedBC, swap_ac_singleQubitLayer]
    exact .compose_AB (SWAP_4 * V * SWAP_4) uC uB uA hC hB hA ih

/-- IsDiag8 is preserved by SWAP_AC conjugation -/
theorem isDiag8_swap_ac (D : Mat8) (hD : IsDiag8 D) :
    IsDiag8 (SWAP_AC * D * SWAP_AC) := by
  obtain ⟨Dg, rfl⟩ := hD
  refine ⟨⟨fun i => Dg.d (swap_ac_perm i), fun i => Dg.unit (swap_ac_perm i)⟩, ?_⟩
  ext i j
  simp only [DiagGate3.toMatrix]
  unfold SWAP_AC swap_ac_perm
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.diagonal_apply, Fin.sum_univ_eight]
  fin_cases i <;> fin_cases j <;> simp <;> try rfl

/-- IsDiag8 is preserved by SWAP_AB conjugation -/
theorem isDiag8_swap_ab (D : Mat8) (hD : IsDiag8 D) :
    IsDiag8 (SWAP_AB * D * SWAP_AB) := by
  obtain ⟨Dg, rfl⟩ := hD
  refine ⟨⟨fun i => Dg.d (swap_ab_perm i), fun i => Dg.unit (swap_ab_perm i)⟩, ?_⟩
  ext i j
  simp only [DiagGate3.toMatrix]
  unfold SWAP_AB swap_ab_perm
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.diagonal_apply, Fin.sum_univ_eight]
  fin_cases i <;> fin_cases j <;> simp <;> try rfl

/-- SWAP_AB is a left involution: SWAP_AB * (SWAP_AB * X) = X -/
theorem swap_ab_cancel (X : Mat8) :
    SWAP_AB * (SWAP_AB * X) = X := by
  calc SWAP_AB * (SWAP_AB * X) = (SWAP_AB * SWAP_AB) * X := (mul_assoc _ _ _).symm
    _ = 1 * X := by rw [SWAP_AB_sq]
    _ = X := one_mul _

/-- SWAP_AB conjugation distributes over products -/
theorem swap_ab_conj_distrib (A B : Mat8) :
    SWAP_AB * (A * B) * SWAP_AB =
    (SWAP_AB * A * SWAP_AB) * (SWAP_AB * B * SWAP_AB) := by
  simp only [mul_assoc, swap_ab_cancel]

/-- **ABABA → BC-AC-BC-AC-BC conversion via SWAP_AB · SWAP_BC conjugation**.
    Maps the neighbor-only ABABA pattern to the paper's preferred BC-AC-BC-AC-BC
    pattern, with V₂, V₄ conjugated by SWAP_4 and V₁, V₃, V₅ unchanged in form. -/
theorem ABABA_to_BCACBCACBC_conjugation (V₁ V₂ V₃ V₄ V₅ : Mat4) :
    SWAP_AB * SWAP_BC *
    (embedAB V₁ * embedBC V₂ * embedAB V₃ * embedBC V₄ * embedAB V₅) *
    SWAP_BC * SWAP_AB =
    embedBC V₁ * embedAC (SWAP_4 * V₂ * SWAP_4) * embedBC V₃ *
      embedAC (SWAP_4 * V₄ * SWAP_4) * embedBC V₅ := by
  -- Step 1: associate SWAP_BC inward, then conjugate by SWAP_BC
  -- After SWAP_BC conjugation: AB → AC, BC → SUS_BC
  have h1 : SWAP_BC * (embedAB V₁ * embedBC V₂ * embedAB V₃ * embedBC V₄ * embedAB V₅) * SWAP_BC =
            embedAC V₁ * embedBC (SWAP_4 * V₂ * SWAP_4) * embedAC V₃ *
              embedBC (SWAP_4 * V₄ * SWAP_4) * embedAC V₅ := by
    rw [swap_conj_distrib, swap_conj_distrib, swap_conj_distrib, swap_conj_distrib,
        swap_bc_embedAB, swap_bc_embedBC, swap_bc_embedAB, swap_bc_embedBC, swap_bc_embedAB]
  -- Step 2: now apply SWAP_AB conjugation
  -- AC → BC, BC → AC
  rw [show SWAP_AB * SWAP_BC *
       (embedAB V₁ * embedBC V₂ * embedAB V₃ * embedBC V₄ * embedAB V₅) * SWAP_BC * SWAP_AB =
       SWAP_AB *
       (SWAP_BC * (embedAB V₁ * embedBC V₂ * embedAB V₃ * embedBC V₄ * embedAB V₅) * SWAP_BC) *
       SWAP_AB from by noncomm_ring]
  rw [h1]
  rw [swap_ab_conj_distrib, swap_ab_conj_distrib, swap_ab_conj_distrib, swap_ab_conj_distrib,
      swap_ab_embedAC, swap_ab_embedBC, swap_ab_embedAC, swap_ab_embedBC, swap_ab_embedAC]

/-- SWAP_AC conjugation preserves UnrestrictedCircuit gate count -/
theorem swap_ac_unrestrictedCircuit {n : ℕ} {U : Mat8}
    (h : UnrestrictedCircuit n U) :
    UnrestrictedCircuit n (SWAP_AC * U * SWAP_AC) := by
  induction h with
  | product uA uB uC hA hB hC =>
    rw [swap_ac_singleQubitLayer]
    exact .product uC uB uA hC hB hA
  | weaken _ ih =>
    exact .weaken ih
  | @compose_AB _ rest V uA uB uC hA hB hC _ ih =>
    show UnrestrictedCircuit _
      (SWAP_AC * (rest * embedAB V * singleQubitLayer uA uB uC) * SWAP_AC)
    rw [swap_ac_conj_distrib, swap_ac_conj_distrib, swap_ac_embedAB, swap_ac_singleQubitLayer]
    exact .compose_BC (SWAP_4 * V * SWAP_4) uC uB uA hC hB hA ih
  | @compose_BC _ rest V uA uB uC hA hB hC _ ih =>
    show UnrestrictedCircuit _
      (SWAP_AC * (rest * embedBC V * singleQubitLayer uA uB uC) * SWAP_AC)
    rw [swap_ac_conj_distrib, swap_ac_conj_distrib, swap_ac_embedBC, swap_ac_singleQubitLayer]
    exact .compose_AB (SWAP_4 * V * SWAP_4) uC uB uA hC hB hA ih
  | @compose_AC _ rest V uA uB uC hA hB hC _ ih =>
    show UnrestrictedCircuit _
      (SWAP_AC * (rest * embedAC V * singleQubitLayer uA uB uC) * SWAP_AC)
    rw [swap_ac_conj_distrib, swap_ac_conj_distrib, swap_ac_embedAC, swap_ac_singleQubitLayer]
    exact .compose_AC (SWAP_4 * V * SWAP_4) uC uB uA hC hB hA ih

/-- Inverse of swap_ac_unrestrictedCircuit: recover from SWAP_AC conjugation.
    If UnrestrictedCircuit n (SWAP_AC * D * SWAP_AC), then UnrestrictedCircuit n D. -/
theorem swap_ac_unrestrictedCircuit_inv {n : ℕ} {D : Mat8}
    (h : UnrestrictedCircuit n (SWAP_AC * D * SWAP_AC)) :
    UnrestrictedCircuit n D := by
  have h' := swap_ac_unrestrictedCircuit h
  -- h' : UnrestrictedCircuit n (SWAP_AC * (SWAP_AC * D * SWAP_AC) * SWAP_AC)
  -- SWAP_AC * (SWAP_AC * D * SWAP_AC) * SWAP_AC = D
  have heq : SWAP_AC * (SWAP_AC * D * SWAP_AC) * SWAP_AC = D := by
    simp only [mul_assoc, swap_ac_cancel, SWAP_AC_sq, mul_one]
  rwa [heq] at h'

/-- Iter 733: SWAP_AC conjugation preserves UnitaryUnrestrictedCircuit gate count.
    Adapts `swap_ac_unrestrictedCircuit` for the unitary type — additionally
    propagates `IsUnitary4 V → IsUnitary4 (SWAP_4 * V * SWAP_4)` per
    `isUnitary4_swap4_conj`. -/
theorem swap_ac_unitaryUnrestrictedCircuit {n : ℕ} {U : Mat8}
    (h : UnitaryUnrestrictedCircuit n U) :
    UnitaryUnrestrictedCircuit n (SWAP_AC * U * SWAP_AC) := by
  induction h with
  | product uA uB uC hA hB hC =>
    rw [swap_ac_singleQubitLayer]
    exact .product uC uB uA hC hB hA
  | weaken _ ih =>
    exact .weaken ih
  | @compose_AB _ rest V hV uA uB uC hA hB hC _ ih =>
    show UnitaryUnrestrictedCircuit _
      (SWAP_AC * (rest * embedAB V * singleQubitLayer uA uB uC) * SWAP_AC)
    rw [swap_ac_conj_distrib, swap_ac_conj_distrib, swap_ac_embedAB, swap_ac_singleQubitLayer]
    exact .compose_BC (SWAP_4 * V * SWAP_4) (isUnitary4_swap4_conj V hV)
      uC uB uA hC hB hA ih
  | @compose_BC _ rest V hV uA uB uC hA hB hC _ ih =>
    show UnitaryUnrestrictedCircuit _
      (SWAP_AC * (rest * embedBC V * singleQubitLayer uA uB uC) * SWAP_AC)
    rw [swap_ac_conj_distrib, swap_ac_conj_distrib, swap_ac_embedBC, swap_ac_singleQubitLayer]
    exact .compose_AB (SWAP_4 * V * SWAP_4) (isUnitary4_swap4_conj V hV)
      uC uB uA hC hB hA ih
  | @compose_AC _ rest V hV uA uB uC hA hB hC _ ih =>
    show UnitaryUnrestrictedCircuit _
      (SWAP_AC * (rest * embedAC V * singleQubitLayer uA uB uC) * SWAP_AC)
    rw [swap_ac_conj_distrib, swap_ac_conj_distrib, swap_ac_embedAC, swap_ac_singleQubitLayer]
    exact .compose_AC (SWAP_4 * V * SWAP_4) (isUnitary4_swap4_conj V hV)
      uC uB uA hC hB hA ih

/-- Inverse of `swap_ac_unitaryUnrestrictedCircuit`. -/
theorem swap_ac_unitaryUnrestrictedCircuit_inv {n : ℕ} {D : Mat8}
    (h : UnitaryUnrestrictedCircuit n (SWAP_AC * D * SWAP_AC)) :
    UnitaryUnrestrictedCircuit n D := by
  have h' := swap_ac_unitaryUnrestrictedCircuit h
  have heq : SWAP_AC * (SWAP_AC * D * SWAP_AC) * SWAP_AC = D := by
    simp only [mul_assoc, swap_ac_cancel, SWAP_AC_sq, mul_one]
  rwa [heq] at h'

/-- Iter 734: SWAP_AC of a DiagGate3 chain produces the swapAC(Dg) chain at
    the same depth. Bypass tool for missing-3-XY-ordering dispatcher cases:
    if Dg's chain is in a missing 3-XY ordering, swapAC(Dg)'s chain is in a
    covered 3-XY ordering (since SWAP_AC: embedAB ↔ embedBC, embedAC fixed).
    Use with `swapAC_inS4_or_S5_iff` (paper Lemma 5.1) to derive the original
    Dg's S₄∪S₅ membership from the swap-conjugated dispatcher result. -/
theorem swap_ac_unitaryUnrestricted_DiagGate3 (Dg : DiagGate3) {n : ℕ}
    (h : UnitaryUnrestrictedCircuit n Dg.toMatrix) :
    UnitaryUnrestrictedCircuit n Dg.swapAC.toMatrix := by
  rw [← swapAC_toMatrix]
  exact swap_ac_unitaryUnrestrictedCircuit h

/-- Iter 737: SWAP_BC variant of the unitary lifting. Adapts legacy
    `swap_unrestrictedCircuit` (line 450) for the unitary type. SWAP_BC
    permutes embedAB ↔ embedAC, with embedBC fixed (V conjugated by SWAP_4). -/
theorem swap_bc_unitaryUnrestrictedCircuit {n : ℕ} {U : Mat8}
    (h : UnitaryUnrestrictedCircuit n U) :
    UnitaryUnrestrictedCircuit n (SWAP_BC * U * SWAP_BC) := by
  induction h with
  | product uA uB uC hA hB hC =>
    rw [swap_bc_singleQubitLayer]
    exact .product uA uC uB hA hC hB
  | weaken _ ih =>
    exact .weaken ih
  | @compose_AB _ rest V hV uA uB uC hA hB hC _ ih =>
    show UnitaryUnrestrictedCircuit _
      (SWAP_BC * (rest * embedAB V * singleQubitLayer uA uB uC) * SWAP_BC)
    rw [swap_conj_distrib, swap_conj_distrib, swap_bc_embedAB, swap_bc_singleQubitLayer]
    exact .compose_AC V hV uA uC uB hA hC hB ih
  | @compose_BC _ rest V hV uA uB uC hA hB hC _ ih =>
    show UnitaryUnrestrictedCircuit _
      (SWAP_BC * (rest * embedBC V * singleQubitLayer uA uB uC) * SWAP_BC)
    rw [swap_conj_distrib, swap_conj_distrib, swap_bc_embedBC, swap_bc_singleQubitLayer]
    exact .compose_BC (SWAP_4 * V * SWAP_4) (isUnitary4_swap4_conj V hV)
      uA uC uB hA hC hB ih
  | @compose_AC _ rest V hV uA uB uC hA hB hC _ ih =>
    show UnitaryUnrestrictedCircuit _
      (SWAP_BC * (rest * embedAC V * singleQubitLayer uA uB uC) * SWAP_BC)
    rw [swap_conj_distrib, swap_conj_distrib, swap_bc_embedAC, swap_bc_singleQubitLayer]
    exact .compose_AB V hV uA uC uB hA hC hB ih

/-- DiagGate3-specific wrapper for SWAP_BC unitary lifting. -/
theorem swap_bc_unitaryUnrestricted_DiagGate3 (Dg : DiagGate3) {n : ℕ}
    (h : UnitaryUnrestrictedCircuit n Dg.toMatrix) :
    UnitaryUnrestrictedCircuit n Dg.swapBC.toMatrix := by
  rw [← swapBC_toMatrix]
  exact swap_bc_unitaryUnrestrictedCircuit h

/-- Iter 739: SWAP_AB variant of the unitary lifting. SWAP_AB permutes
    embedBC ↔ embedAC, with embedAB fixed (V conjugated by SWAP_4). Completes
    the SWAP_AC/BC/AB infrastructure trio for the unitary type. -/
theorem swap_ab_unitaryUnrestrictedCircuit {n : ℕ} {U : Mat8}
    (h : UnitaryUnrestrictedCircuit n U) :
    UnitaryUnrestrictedCircuit n (SWAP_AB * U * SWAP_AB) := by
  induction h with
  | product uA uB uC hA hB hC =>
    rw [swap_ab_singleQubitLayer]
    exact .product uB uA uC hB hA hC
  | weaken _ ih =>
    exact .weaken ih
  | @compose_AB _ rest V hV uA uB uC hA hB hC _ ih =>
    show UnitaryUnrestrictedCircuit _
      (SWAP_AB * (rest * embedAB V * singleQubitLayer uA uB uC) * SWAP_AB)
    rw [swap_ab_conj_distrib, swap_ab_conj_distrib, swap_ab_embedAB, swap_ab_singleQubitLayer]
    exact .compose_AB (SWAP_4 * V * SWAP_4) (isUnitary4_swap4_conj V hV)
      uB uA uC hB hA hC ih
  | @compose_BC _ rest V hV uA uB uC hA hB hC _ ih =>
    show UnitaryUnrestrictedCircuit _
      (SWAP_AB * (rest * embedBC V * singleQubitLayer uA uB uC) * SWAP_AB)
    rw [swap_ab_conj_distrib, swap_ab_conj_distrib, swap_ab_embedBC, swap_ab_singleQubitLayer]
    exact .compose_AC V hV uB uA uC hB hA hC ih
  | @compose_AC _ rest V hV uA uB uC hA hB hC _ ih =>
    show UnitaryUnrestrictedCircuit _
      (SWAP_AB * (rest * embedAC V * singleQubitLayer uA uB uC) * SWAP_AB)
    rw [swap_ab_conj_distrib, swap_ab_conj_distrib, swap_ab_embedAC, swap_ab_singleQubitLayer]
    exact .compose_BC V hV uB uA uC hB hA hC ih

/-- DiagGate3-specific wrapper for SWAP_AB unitary lifting. -/
theorem swap_ab_unitaryUnrestricted_DiagGate3 (Dg : DiagGate3) {n : ℕ}
    (h : UnitaryUnrestrictedCircuit n Dg.toMatrix) :
    UnitaryUnrestrictedCircuit n Dg.swapAB.toMatrix := by
  rw [← swapAB_toMatrix]
  exact swap_ab_unitaryUnrestrictedCircuit h

/-! ## Z-propagation infrastructure

For diagonal gates, Z⊗I⊗I and I⊗I⊗Z commute with everything in the circuit.
These lemmas support the key argument: propagating Pauli-Z through ABABA circuits
constrains the structure of the 2-qubit gates. -/

/-- embedAB(ZI) = Z⊗I⊗I commutes with any embedBC gate I⊗V.
    This holds because they act on disjoint qubit spaces (A vs BC). -/
theorem embedAB_ZI_comm_embedBC (V : Mat4) :
    embedAB ZI * embedBC V = embedBC V * embedAB ZI := by
  -- ZI = kron2 pauliZ I₂, so embedAB ZI = singleQubitLayer pauliZ I₂ I₂
  rw [show ZI = kron2 pauliZ I₂ from rfl,
      ← singleQubitLayer_eq_embedAB_kron2 pauliZ I₂]
  -- singleQubitLayer(Z, I, I) is an A-only product layer, commutes with embedBC
  exact (embedBC_comm_singleQubitLayer_A V pauliZ).symm

/-- embedBC(IZ) = I⊗I⊗Z commutes with any embedAB gate V⊗I.
    This holds because they act on disjoint qubit spaces (AB-A vs C). -/
theorem embedBC_IZ_comm_embedAB (V : Mat4) :
    embedBC IZ * embedAB V = embedAB V * embedBC IZ := by
  -- IZ = kron2 I₂ pauliZ, so embedBC IZ = singleQubitLayer I₂ I₂ pauliZ
  rw [show IZ = kron2 I₂ pauliZ from rfl,
      ← singleQubitLayer_eq_embedBC_kron2 I₂ pauliZ]
  -- singleQubitLayer(I, I, Z) is a C-only product layer, commutes with embedAB
  exact (embedAB_comm_singleQubitLayer_C V pauliZ).symm

/-- embedAB(ZI) is a diagonal matrix: diag(1,1,1,1,-1,-1,-1,-1) -/
private lemma embedAB_ZI_diagonal :
    embedAB ZI = Matrix.diagonal (fun i : Fin 8 => if i.val < 4 then (1 : ℂ) else -1) := by
  ext i j
  simp only [embedAB, ZI, kron2, pauliZ, I₂, Matrix.of_apply, Matrix.one_apply,
             Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;>
  · simp

/-- Diagonal 8×8 gates commute with embedAB(ZI) = Z⊗I⊗I.
    Key step in Z-propagation: since D is diagonal, D*(Z⊗I⊗I) = (Z⊗I⊗I)*D. -/
theorem isDiag8_comm_embedAB_ZI (D : Mat8) (hD : IsDiag8 D) :
    D * embedAB ZI = embedAB ZI * D := by
  obtain ⟨Dg, rfl⟩ := hD
  simp only [DiagGate3.toMatrix, embedAB_ZI_diagonal, diagonal_mul_diagonal']
  congr 1; ext i; exact mul_comm _ _

/-- Z-conjugation of product layers: conjugating by Z⊗I⊗I only affects the A-qubit.
    embedAB(ZI) * P(uA,uB,uC) * embedAB(ZI) = P(Z*uA*Z, uB, uC).
    Key step: allows Z-propagation through product layers in ABABA circuits. -/
theorem embedAB_ZI_conj_singleQubitLayer (uA uB uC : Mat2) :
    embedAB ZI * singleQubitLayer uA uB uC * embedAB ZI =
    singleQubitLayer (pauliZ * uA * pauliZ) uB uC := by
  have hZI : embedAB ZI = singleQubitLayer pauliZ I₂ I₂ :=
    (singleQubitLayer_eq_embedAB_kron2 pauliZ I₂).symm
  rw [hZI, mul_assoc, singleQubitLayer_mul, singleQubitLayer_mul]
  simp only [I₂, one_mul, mul_one, mul_assoc]

/-- ZI is an involution: ZI * ZI = 1 (i.e., (Z⊗I)² = I₄). -/
theorem ZI_sq : ZI * ZI = (1 : Mat4) := by
  show kron2 pauliZ I₂ * kron2 pauliZ I₂ = 1
  rw [kron2_mul, pauliZ_sq, I₂, mul_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [kron2, Matrix.of_apply, Matrix.one_apply]

/-- Block-diagonal in first qubit is invariant under Z⊗I conjugation.
    IsBlockDiagFirst V means V commutes with ZI, so ZI*V*ZI = V*ZI² = V. -/
theorem blockDiagFirst_conj_ZI (V : Mat4) (hV : IsBlockDiagFirst V) :
    ZI * V * ZI = V := by
  rw [(blockDiagFirst_commutes_ZI V hV).symm, mul_assoc, ZI_sq, mul_one]

/-- IZ is an involution: IZ * IZ = 1 (i.e., (I⊗Z)² = I₄). -/
theorem IZ_sq : IZ * IZ = (1 : Mat4) := by
  show kron2 I₂ pauliZ * kron2 I₂ pauliZ = 1
  rw [kron2_mul, pauliZ_sq, I₂, mul_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [kron2, Matrix.of_apply, Matrix.one_apply]

/-- Block-diagonal in second qubit is invariant under I⊗Z conjugation.
    IsBlockDiagSecond V means V commutes with IZ, so IZ*V*IZ = V*IZ² = V. -/
theorem blockDiagSecond_conj_IZ (V : Mat4) (hV : IsBlockDiagSecond V) :
    IZ * V * IZ = V := by
  rw [(blockDiagSecond_commutes_IZ V hV).symm, mul_assoc, IZ_sq, mul_one]

/-- ZI-conjugation invariance characterizes block-diagonal in first qubit (Lemma A.1, iff form).
    Reverse direction: ZI*V*ZI = V → V commutes with ZI → V is block-diagonal in A. -/
theorem blockDiagFirst_iff_conj_ZI (V : Mat4) :
    IsBlockDiagFirst V ↔ ZI * V * ZI = V := by
  refine ⟨blockDiagFirst_conj_ZI V, fun h => ?_⟩
  -- From ZI*V*ZI = V, multiply right by ZI: ZI*V*ZI*ZI = V*ZI; ZI_sq cancels.
  have h1 : ZI * V * ZI * ZI = V * ZI := by rw [h]
  rw [mul_assoc (ZI * V), ZI_sq, mul_one] at h1
  exact commutes_ZI_implies_blockDiagFirst V h1.symm

/-- IZ-conjugation invariance characterizes block-diagonal in second qubit (Lemma A.1, iff form).
    Symmetric counterpart of `blockDiagFirst_iff_conj_ZI`. -/
theorem blockDiagSecond_iff_conj_IZ (V : Mat4) :
    IsBlockDiagSecond V ↔ IZ * V * IZ = V := by
  refine ⟨blockDiagSecond_conj_IZ V, fun h => ?_⟩
  have h1 : IZ * V * IZ * IZ = V * IZ := by rw [h]
  rw [mul_assoc (IZ * V), IZ_sq, mul_one] at h1
  exact commutes_IZ_implies_blockDiagSecond V h1.symm

/-- ZI-conjugation distributes over block-diag-A factored products.
    For V block-diag-A and any M₁, M₂:
    `ZI * (M₁ * V * M₂) * ZI = (ZI * M₁ * ZI) * V * (ZI * M₂ * ZI)`.
    Insert ZI·ZI=1 around V; V is invariant under ZI-conjugation; result re-associates. -/
theorem ZI_conj_factored_blockDiagFirst (V M₁ M₂ : Mat4) (hV : IsBlockDiagFirst V) :
    ZI * (M₁ * V * M₂) * ZI = (ZI * M₁ * ZI) * V * (ZI * M₂ * ZI) := by
  have hV_inv : ZI * V * ZI = V := blockDiagFirst_conj_ZI V hV
  calc ZI * (M₁ * V * M₂) * ZI
      = ZI * M₁ * V * M₂ * ZI := by noncomm_ring
    _ = ZI * M₁ * (ZI * V * ZI) * M₂ * ZI := by rw [hV_inv]
    _ = (ZI * M₁ * ZI) * V * (ZI * M₂ * ZI) := by noncomm_ring

/-- IZ-conjugation distributes over block-diag-B factored products (symmetric to first qubit). -/
theorem IZ_conj_factored_blockDiagSecond (V M₁ M₂ : Mat4) (hV : IsBlockDiagSecond V) :
    IZ * (M₁ * V * M₂) * IZ = (IZ * M₁ * IZ) * V * (IZ * M₂ * IZ) := by
  have hV_inv : IZ * V * IZ = V := blockDiagSecond_conj_IZ V hV
  calc IZ * (M₁ * V * M₂) * IZ
      = IZ * M₁ * V * M₂ * IZ := by noncomm_ring
    _ = IZ * M₁ * (IZ * V * IZ) * M₂ * IZ := by rw [hV_inv]
    _ = (IZ * M₁ * IZ) * V * (IZ * M₂ * IZ) := by noncomm_ring

/-- Explicit form: ZI-conjugation of `kron2 A B` Z-conjugates the A-component, leaves B alone.
    `ZI · kron2(A,B) · ZI = kron2(Z·A·Z, B)`. -/
theorem kron2_ZI_conj (A B : Mat2) :
    ZI * kron2 A B * ZI = kron2 (pauliZ * A * pauliZ) B := by
  show kron2 pauliZ I₂ * kron2 A B * kron2 pauliZ I₂ = kron2 (pauliZ * A * pauliZ) B
  rw [kron2_mul, kron2_mul]
  show kron2 (pauliZ * A * pauliZ) (I₂ * B * I₂) = kron2 (pauliZ * A * pauliZ) B
  unfold I₂
  rw [Matrix.one_mul, Matrix.mul_one]

/-- Explicit form: IZ-conjugation of `kron2 A B` Z-conjugates the B-component, leaves A alone. -/
theorem kron2_IZ_conj (A B : Mat2) :
    IZ * kron2 A B * IZ = kron2 A (pauliZ * B * pauliZ) := by
  show kron2 I₂ pauliZ * kron2 A B * kron2 I₂ pauliZ = kron2 A (pauliZ * B * pauliZ)
  rw [kron2_mul, kron2_mul]
  show kron2 (I₂ * A * I₂) (pauliZ * B * pauliZ) = kron2 A (pauliZ * B * pauliZ)
  unfold I₂
  rw [Matrix.one_mul, Matrix.mul_one]

/-- ZI-conjugation of an absorbed AB embedding M₁·V·M₂ with V block-diag-A:
    `embedAB(ZI) · embedAB(M₁·V·M₂) · embedAB(ZI) = embedAB((ZI·M₁·ZI) · V · (ZI·M₂·ZI))`
    Combines `embedAB_mul` homomorphism with `ZI_conj_factored_blockDiagFirst`
    (V block-diag → V invariant inside the conjugation, surrounding M_i Z-conjugated). -/
theorem embedAB_ZI_conj_absorbed_blockDiagFirst (V M₁ M₂ : Mat4) (hV : IsBlockDiagFirst V) :
    embedAB ZI * embedAB (M₁ * V * M₂) * embedAB ZI =
    embedAB ((ZI * M₁ * ZI) * V * (ZI * M₂ * ZI)) := by
  have step1 : embedAB ZI * embedAB (M₁ * V * M₂) * embedAB ZI =
               embedAB (ZI * (M₁ * V * M₂) * ZI) := by
    rw [mul_assoc, embedAB_mul, embedAB_mul]
    congr 1
    noncomm_ring
  rw [step1, ZI_conj_factored_blockDiagFirst V M₁ M₂ hV]

/-- IZ-conjugation analog for the second qubit / IsBlockDiagSecond V. -/
theorem embedAB_IZ_conj_absorbed_blockDiagSecond (V M₁ M₂ : Mat4) (hV : IsBlockDiagSecond V) :
    embedAB IZ * embedAB (M₁ * V * M₂) * embedAB IZ =
    embedAB ((IZ * M₁ * IZ) * V * (IZ * M₂ * IZ)) := by
  have step1 : embedAB IZ * embedAB (M₁ * V * M₂) * embedAB IZ =
               embedAB (IZ * (M₁ * V * M₂) * IZ) := by
    rw [mul_assoc, embedAB_mul, embedAB_mul]
    congr 1
    noncomm_ring
  rw [step1, IZ_conj_factored_blockDiagSecond V M₁ M₂ hV]

/-- For V block-diag-A, embedAB(V) commutes with embedAB(ZI).
    This lifts `blockDiagFirst_commutes_ZI` through the embedAB homomorphism. -/
theorem embedAB_blockDiagFirst_commutes_embedAB_ZI (V : Mat4) (hV : IsBlockDiagFirst V) :
    embedAB V * embedAB ZI = embedAB ZI * embedAB V := by
  rw [embedAB_mul, blockDiagFirst_commutes_ZI V hV, ← embedAB_mul]

/-- For V block-diag-B, embedAB(V) commutes with embedAB(IZ). Symmetric version. -/
theorem embedAB_blockDiagSecond_commutes_embedAB_IZ (V : Mat4) (hV : IsBlockDiagSecond V) :
    embedAB V * embedAB IZ = embedAB IZ * embedAB V := by
  rw [embedAB_mul, blockDiagSecond_commutes_IZ V hV, ← embedAB_mul]

/-- For V block-diag-A, ZI-conjugation of embedAB(V) equals embedAB(V).
    This is the embedAB-lifted version of `blockDiagFirst_conj_ZI`. -/
theorem embedAB_ZI_conj_blockDiagFirst (V : Mat4) (hV : IsBlockDiagFirst V) :
    embedAB ZI * embedAB V * embedAB ZI = embedAB V := by
  rw [embedAB_mul, embedAB_mul, blockDiagFirst_conj_ZI V hV]

/-- For V block-diag-B, IZ-conjugation of embedAB(V) equals embedAB(V). Symmetric. -/
theorem embedAB_IZ_conj_blockDiagSecond (V : Mat4) (hV : IsBlockDiagSecond V) :
    embedAB IZ * embedAB V * embedAB IZ = embedAB V := by
  rw [embedAB_mul, embedAB_mul, blockDiagSecond_conj_IZ V hV]

/-- embedAB(ZI) is an involution: embedAB(ZI) * embedAB(ZI) = 1.
    Allows inserting embedAB(ZI)² = I between circuit elements. -/
theorem embedAB_ZI_sq : embedAB ZI * embedAB ZI = (1 : Mat8) := by
  rw [embedAB_mul, ZI_sq, embedAB_one]

/-- Z-conjugation of AB gates: embedAB(ZI) * embedAB(V) * embedAB(ZI) = embedAB(ZI*V*ZI).
    Follows from embedAB being a ring homomorphism and ZI² = I. -/
theorem embedAB_ZI_conj_embedAB (V : Mat4) :
    embedAB ZI * embedAB V * embedAB ZI = embedAB (ZI * V * ZI) := by
  rw [mul_assoc, embedAB_mul, embedAB_mul, mul_assoc]

/-- Z-conjugation of BC gates: embedAB(ZI) * embedBC(V) * embedAB(ZI) = embedBC(V).
    BC gates are invariant under Z⊗I⊗I conjugation. -/
theorem embedAB_ZI_conj_embedBC (V : Mat4) :
    embedAB ZI * embedBC V * embedAB ZI = embedBC V := by
  rw [mul_assoc, (embedAB_ZI_comm_embedBC V).symm, ← mul_assoc, embedAB_ZI_sq, one_mul]

/-- Z-conjugation invariance for diagonal gates:
    embedAB(ZI) * D * embedAB(ZI) = D when D is diagonal.
    Combines isDiag8_comm_embedAB_ZI with embedAB_ZI_sq. -/
theorem isDiag8_conj_embedAB_ZI (D : Mat8) (hD : IsDiag8 D) :
    embedAB ZI * D * embedAB ZI = D := by
  rw [(isDiag8_comm_embedAB_ZI D hD).symm, mul_assoc, embedAB_ZI_sq, mul_one]

/-- Helper: a C-only product layer with unitary uC has its conjugate-transpose as right-inverse. -/
private lemma singleQubitLayer_C_mul_conjTranspose (uC : Mat2) (huC : IsUnitary2 uC) :
    singleQubitLayer I₂ I₂ uC * singleQubitLayer I₂ I₂ uC.conjTranspose = (1 : Mat8) := by
  rw [singleQubitLayer_mul]
  have huC' : uC * uC.conjTranspose = 1 := by
    have := isUnitary2_conjTranspose huC
    unfold IsUnitary2 at this
    rwa [conjTranspose_conjTranspose] at this
  rw [huC']
  show singleQubitLayer (I₂ * I₂) (I₂ * I₂) 1 = 1
  unfold I₂
  rw [Matrix.one_mul]
  exact singleQubitLayer_one

/-- **Z-conjugation invariance with trailing C-only product**: if `D' · P_C(uC)` is
    diagonal (where uC is unitary), then `D'` itself is invariant under embedAB(ZI) conjugation.
    Proof: D' · P_C diagonal gives Z-conj invariance of D' · P_C; commute Z past P_C;
    then right-cancel P_C using its unitary inverse. -/
theorem embedAB_ZI_conj_eq_self_of_diag8_mul_C
    (D' : Mat8) (uC : Mat2) (huC : IsUnitary2 uC)
    (hD : IsDiag8 (D' * singleQubitLayer I₂ I₂ uC)) :
    embedAB ZI * D' * embedAB ZI = D' := by
  -- Step 1: ZI-conjugation invariance of D' · P_C (since it's diagonal)
  have h1 : embedAB ZI * (D' * singleQubitLayer I₂ I₂ uC) * embedAB ZI =
            D' * singleQubitLayer I₂ I₂ uC := isDiag8_conj_embedAB_ZI _ hD
  -- Step 2: embedAB(ZI) commutes with C-only product layer
  have h_comm : embedAB ZI * singleQubitLayer I₂ I₂ uC =
                singleQubitLayer I₂ I₂ uC * embedAB ZI :=
    embedAB_comm_singleQubitLayer_C ZI uC
  -- Step 3: re-associate using commute
  have h2 : (embedAB ZI * D' * embedAB ZI) * singleQubitLayer I₂ I₂ uC =
            D' * singleQubitLayer I₂ I₂ uC := by
    calc (embedAB ZI * D' * embedAB ZI) * singleQubitLayer I₂ I₂ uC
        = embedAB ZI * D' * (embedAB ZI * singleQubitLayer I₂ I₂ uC) := by noncomm_ring
      _ = embedAB ZI * D' * (singleQubitLayer I₂ I₂ uC * embedAB ZI) := by rw [h_comm]
      _ = embedAB ZI * (D' * singleQubitLayer I₂ I₂ uC) * embedAB ZI := by noncomm_ring
      _ = D' * singleQubitLayer I₂ I₂ uC := h1
  -- Step 4: right-cancel P_C using unitary inverse
  have h_inv := singleQubitLayer_C_mul_conjTranspose uC huC
  have h3 : (embedAB ZI * D' * embedAB ZI) * singleQubitLayer I₂ I₂ uC *
            singleQubitLayer I₂ I₂ uC.conjTranspose =
            D' * singleQubitLayer I₂ I₂ uC * singleQubitLayer I₂ I₂ uC.conjTranspose := by
    rw [h2]
  rw [mul_assoc (embedAB ZI * D' * embedAB ZI) (singleQubitLayer I₂ I₂ uC)
                (singleQubitLayer I₂ I₂ uC.conjTranspose),
      h_inv, mul_one,
      mul_assoc D' (singleQubitLayer I₂ I₂ uC) (singleQubitLayer I₂ I₂ uC.conjTranspose),
      h_inv, mul_one] at h3
  exact h3

/-- Helper: embedAB(ZI) is left-cancellable (since ZI² = I). -/
private theorem embedAB_ZI_cancel_left (B : Mat8) :
    embedAB ZI * (embedAB ZI * B) = B := by
  rw [← mul_assoc, embedAB_ZI_sq, one_mul]

/-- Z-conjugation of a product-free ABABA circuit:
    Replaces each AB gate V with ZI*V*ZI, leaves BC gates unchanged.
    This is the key structural lemma for the block-diagonal reduction. -/
theorem embedAB_ZI_conj_ABABA (V₁ V₂ V₃ V₄ V₅ : Mat4) :
    embedAB ZI *
    (embedAB V₁ * embedBC V₂ * embedAB V₃ * embedBC V₄ * embedAB V₅) *
    embedAB ZI =
    embedAB (ZI * V₁ * ZI) * embedBC V₂ * embedAB (ZI * V₃ * ZI) *
    embedBC V₄ * embedAB (ZI * V₅ * ZI) := by
  -- Expand RHS conjugations; use conv_rhs to avoid matching embedBC on the LHS
  conv_rhs =>
    rw [← embedAB_ZI_conj_embedAB V₁, ← embedAB_ZI_conj_embedAB V₃,
        ← embedAB_ZI_conj_embedAB V₅, ← embedAB_ZI_conj_embedBC V₂,
        ← embedAB_ZI_conj_embedBC V₄]
  -- Right-associate both sides, then cancel ZI*ZI pairs on the RHS
  simp only [mul_assoc]
  rw [embedAB_ZI_cancel_left, embedAB_ZI_cancel_left,
      embedAB_ZI_cancel_left, embedAB_ZI_cancel_left]

/-- Z-propagation with block-diagonal middle gate:
    In a product-free ABABA circuit computing a diagonal gate, if V₃ is block-diagonal
    in A, then the Z-conjugation identity simplifies: only V₁ and V₅ are conjugated. -/
theorem ABABA_zprop_blockDiagFirst_middle (V₁ V₂ V₃ V₄ V₅ : Mat4)
    (hD : IsDiag8 (embedAB V₁ * embedBC V₂ * embedAB V₃ * embedBC V₄ * embedAB V₅))
    (hBD : IsBlockDiagFirst V₃) :
    embedAB (ZI * V₁ * ZI) * embedBC V₂ * embedAB V₃ * embedBC V₄ * embedAB (ZI * V₅ * ZI) =
    embedAB V₁ * embedBC V₂ * embedAB V₃ * embedBC V₄ * embedAB V₅ := by
  -- Step 1: Z-conjugation of the full product equals itself (diagonal)
  have h1 := isDiag8_conj_embedAB_ZI _ hD
  -- Step 2: Z-conjugation expands via ABABA identity
  rw [embedAB_ZI_conj_ABABA] at h1
  -- Step 3: V₃ is invariant under ZI conjugation
  rw [blockDiagFirst_conj_ZI V₃ hBD] at h1
  exact h1

/-- **Z-invariance for absorbed ABABA with trailing P_C**: if a 5-gate product-free
    ABABA times a trailing C-only product is diagonal (with uC unitary), then the
    Z-conjugated ABABA equals itself, with each AB gate's W_i Z-conjugated and
    BC gates unchanged.

    This is the absorbed-form analog of `ABABA_zprop_blockDiagFirst_middle`'s setup,
    accommodating the trailing P_C residual. Combined with `ZI_conj_factored_blockDiagFirst`
    (when V₃ inside W₃ is block-diag-A), this gives the complete Z-propagation
    expansion for Case 1's absorbed form. -/
theorem absorbed_ABABA_Z_invariance_expanded
    (W₁ W₂ W₃ W₄ W₅ : Mat4) (uC : Mat2) (huC : IsUnitary2 uC)
    (hD : IsDiag8 (embedAB W₁ * embedBC W₂ * embedAB W₃ * embedBC W₄ * embedAB W₅ *
                    singleQubitLayer I₂ I₂ uC)) :
    embedAB (ZI * W₁ * ZI) * embedBC W₂ * embedAB (ZI * W₃ * ZI) *
      embedBC W₄ * embedAB (ZI * W₅ * ZI) =
    embedAB W₁ * embedBC W₂ * embedAB W₃ * embedBC W₄ * embedAB W₅ := by
  have hZinv := embedAB_ZI_conj_eq_self_of_diag8_mul_C _ uC huC hD
  rw [embedAB_ZI_conj_ABABA] at hZinv
  exact hZinv

set_option maxHeartbeats 1600000 in
-- Heartbeats raised: 12-step absorption cascade over an 11-factor 8×8 chain.
/-- **5-gate absorption**: a `BC-AC-BC-AC-BC` chain with six interleaved product
    layers collapses to exactly five embeds, with NO leftover layer.

    This is the input shape that `HP/Lemma44.lean`'s `paper_lemma_4_4` requires
    (`Dg.toMatrix = embedBC U₁ * embedAC U₂ * embedBC U₃ * embedAC U₄ * embedBC U₅`),
    so it is the adapter needed to feed a neighbor chain into that theorem.

    Cascade (each step is one primitive from `EmbedLemmas`): the leading layer's
    `(B,C)` part goes into `BC V₁` and its `A` part commutes right past `BC V₁`;
    thereafter the leftover alternates A-only (absorbed by the next `AC`) and
    B-only (absorbed by the next `BC`), which is exactly why the pattern closes
    with nothing left over. The final trailing `A`-only layer commutes back left
    past `BC V₅` and is absorbed into `AC V₄`. -/
theorem sandwich_BC_AC_BC_AC_BC_to_5embed (V₁ V₂ V₃ V₄ V₅ : Mat4)
    (a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ a₄ b₄ c₄ a₅ b₅ c₅ : Mat2) :
    singleQubitLayer a₀ b₀ c₀ * embedBC V₁ *
      singleQubitLayer a₁ b₁ c₁ * embedAC V₂ *
      singleQubitLayer a₂ b₂ c₂ * embedBC V₃ *
      singleQubitLayer a₃ b₃ c₃ * embedAC V₄ *
      singleQubitLayer a₄ b₄ c₄ * embedBC V₅ *
      singleQubitLayer a₅ b₅ c₅ =
    embedBC (kron2 b₀ c₀ * V₁ * kron2 b₁ c₁) *
      embedAC (kron2 (a₀ * a₁) 1 * V₂ * kron2 a₂ c₂) *
      embedBC (kron2 b₂ 1 * V₃ * kron2 b₃ c₃) *
      embedAC (kron2 a₃ 1 * V₄ * kron2 a₄ c₄ * kron2 a₅ 1) *
      embedBC (kron2 b₄ 1 * V₅ * kron2 b₅ c₅) := by
  -- Context-passing forms of the primitives, so the cascade is a plain `rw`
  -- sequence on the right-associated product (no giant `show` re-brackets).
  have sBCL : ∀ (uA uB uC : Mat2) (V : Mat4) (R : Mat8),
      singleQubitLayer uA uB uC * (embedBC V * R) =
      singleQubitLayer uA I₂ I₂ * (embedBC (kron2 uB uC * V) * R) := by
    intro uA uB uC V R; rw [← mul_assoc, singleQubitLayer_mul_embedBC, mul_assoc]
  have sBCR : ∀ (V : Mat4) (uA uB uC : Mat2) (R : Mat8),
      embedBC V * (singleQubitLayer uA uB uC * R) =
      embedBC (V * kron2 uB uC) * (singleQubitLayer uA I₂ I₂ * R) := by
    intro V uA uB uC R; rw [← mul_assoc, embedBC_mul_singleQubitLayer, mul_assoc]
  have sACL : ∀ (uA uB uC : Mat2) (V : Mat4) (R : Mat8),
      singleQubitLayer uA uB uC * (embedAC V * R) =
      singleQubitLayer I₂ uB I₂ * (embedAC (kron2 uA uC * V) * R) := by
    intro uA uB uC V R; rw [← mul_assoc, singleQubitLayer_mul_embedAC, mul_assoc]
  have sACR : ∀ (V : Mat4) (uA uB uC : Mat2) (R : Mat8),
      embedAC V * (singleQubitLayer uA uB uC * R) =
      embedAC (V * kron2 uA uC) * (singleQubitLayer I₂ uB I₂ * R) := by
    intro V uA uB uC R; rw [← mul_assoc, embedAC_mul_singleQubitLayer, mul_assoc]
  have cBC : ∀ (V : Mat4) (uA : Mat2) (R : Mat8),
      singleQubitLayer uA I₂ I₂ * (embedBC V * R) =
      embedBC V * (singleQubitLayer uA I₂ I₂ * R) := by
    intro V uA R; rw [← mul_assoc, ← embedBC_comm_singleQubitLayer_A, mul_assoc]
  have mSQL : ∀ (a b c a' b' c' : Mat2) (R : Mat8),
      singleQubitLayer a b c * (singleQubitLayer a' b' c' * R) =
      singleQubitLayer (a * a') (b * b') (c * c') * R := by
    intro a b c a' b' c' R; rw [← mul_assoc, singleQubitLayer_mul]
  have hone : (singleQubitLayer (1 : Mat2) 1 1 : Mat8) = 1 := singleQubitLayer_one
  have oneL : ∀ R : Mat8, singleQubitLayer (1 : Mat2) 1 1 * R = R := by
    intro R; rw [hone, one_mul]
  have sBCRt : ∀ (V : Mat4) (uA uB uC : Mat2),
      embedBC V * singleQubitLayer uA uB uC =
      embedBC (V * kron2 uB uC) * singleQubitLayer uA I₂ I₂ :=
    fun V uA uB uC => embedBC_mul_singleQubitLayer V uA uB uC
  have cBCt : ∀ (V : Mat4) (uA : Mat2),
      embedBC V * singleQubitLayer uA I₂ I₂ =
      singleQubitLayer uA I₂ I₂ * embedBC V :=
    fun V uA => embedBC_comm_singleQubitLayer_A V uA
  simp only [mul_assoc]
  rw [sBCL, sBCR, cBC, mSQL]
  simp only [I₂, mul_one, one_mul]
  rw [sACL]
  simp only [I₂, mul_one, one_mul]
  rw [oneL, sACR]
  simp only [I₂, mul_one, one_mul]
  rw [sBCL]
  simp only [I₂, mul_one, one_mul]
  rw [oneL, sBCR, sACL]
  simp only [I₂, mul_one, one_mul]
  rw [oneL, sACR, sBCL]
  simp only [I₂, mul_one, one_mul]
  rw [oneL, sBCRt, cBCt, sACR]
  simp only [I₂, mul_one, one_mul]
  rw [oneL]
  simp only [mul_assoc]

/-! ## The cyclic relabeling σ = (A→B→C→A)  (iter 1042)

The paper's Lemma 4.4 is stated for its native `BC-AC-BC-AC-BC` word, while a
5-gate NEIGHBOR circuit is `AB-BC-AB-BC-AB`. These are the same word up to
RELABELING the qubits: σ sends `AB ↦ BC`, `BC ↦ AC`, `AC ↦ AB`. So no new
algebra is needed — only transport. σ is realized by `CYC = SWAP_AB · SWAP_BC`. -/

/-- The cyclic relabeling σ = (A→B→C→A) as a `Mat8` permutation. -/
def CYC : Mat8 := SWAP_AB * SWAP_BC

/-- Its inverse σ⁻¹ = (A→C→B→A). -/
def CYCinv : Mat8 := SWAP_BC * SWAP_AB

theorem cycinv_mul : CYCinv * CYC = 1 := by
  unfold CYC CYCinv
  rw [show SWAP_BC * SWAP_AB * (SWAP_AB * SWAP_BC)
      = SWAP_BC * (SWAP_AB * SWAP_AB) * SWAP_BC from by noncomm_ring,
      SWAP_AB_sq, mul_one, SWAP_BC_sq]

theorem cyc_mul_inv : CYC * CYCinv = 1 := by
  unfold CYC CYCinv
  rw [show SWAP_AB * SWAP_BC * (SWAP_BC * SWAP_AB)
      = SWAP_AB * (SWAP_BC * SWAP_BC) * SWAP_AB from by noncomm_ring,
      SWAP_BC_sq, mul_one, SWAP_AB_sq]

theorem cyc_embedAB (V : Mat4) : CYC * embedAB V * CYCinv = embedBC V := by
  unfold CYC CYCinv
  rw [show SWAP_AB * SWAP_BC * embedAB V * (SWAP_BC * SWAP_AB)
      = SWAP_AB * (SWAP_BC * embedAB V * SWAP_BC) * SWAP_AB from by noncomm_ring,
      swap_bc_embedAB, swap_ab_embedAC]

theorem cyc_embedBC (V : Mat4) :
    CYC * embedBC V * CYCinv = embedAC (SWAP_4 * V * SWAP_4) := by
  unfold CYC CYCinv
  rw [show SWAP_AB * SWAP_BC * embedBC V * (SWAP_BC * SWAP_AB)
      = SWAP_AB * (SWAP_BC * embedBC V * SWAP_BC) * SWAP_AB from by noncomm_ring,
      swap_bc_embedBC, swap_ab_embedBC]

theorem cyc_embedAC (V : Mat4) :
    CYC * embedAC V * CYCinv = embedAB (SWAP_4 * V * SWAP_4) := by
  unfold CYC CYCinv
  rw [show SWAP_AB * SWAP_BC * embedAC V * (SWAP_BC * SWAP_AB)
      = SWAP_AB * (SWAP_BC * embedAC V * SWAP_BC) * SWAP_AB from by noncomm_ring,
      swap_bc_embedAC, swap_ab_embedAB]

theorem cyc_singleQubitLayer (a b c : Mat2) :
    CYC * singleQubitLayer a b c * CYCinv = singleQubitLayer c a b := by
  unfold CYC CYCinv
  rw [show SWAP_AB * SWAP_BC * singleQubitLayer a b c * (SWAP_BC * SWAP_AB)
      = SWAP_AB * (SWAP_BC * singleQubitLayer a b c * SWAP_BC) * SWAP_AB
      from by noncomm_ring, swap_bc_singleQubitLayer, swap_ab_singleQubitLayer]

theorem cyc_cancel (X : Mat8) : CYCinv * (CYC * X) = X := by
  rw [← mul_assoc, cycinv_mul, one_mul]

theorem cyc_cancel' (X : Mat8) : CYC * (CYCinv * X) = X := by
  rw [← mul_assoc, cyc_mul_inv, one_mul]

theorem cyc_conj_eq (M : Mat8) :
    CYC * M * CYCinv = SWAP_AB * (SWAP_BC * M * SWAP_BC) * SWAP_AB := by
  unfold CYC CYCinv; noncomm_ring

/-- σ is a permutation, so it preserves diagonality. -/
theorem isDiag8_cyc (M : Mat8) (hM : IsDiag8 M) : IsDiag8 (CYC * M * CYCinv) := by
  rw [cyc_conj_eq]; exact isDiag8_swap_ab _ (isDiag8_swap_bc M hM)

theorem cyc_conj_back (M : Mat8) : CYCinv * (CYC * M * CYCinv) * CYC = M := by
  rw [show CYCinv * (CYC * M * CYCinv) * CYC = (CYCinv * CYC) * M * (CYCinv * CYC)
      from by noncomm_ring, cycinv_mul, one_mul, mul_one]

theorem cycinv_embedBC (V : Mat4) : CYCinv * embedBC V * CYC = embedAB V := by
  calc CYCinv * embedBC V * CYC
      = CYCinv * (CYC * embedAB V * CYCinv) * CYC := by rw [cyc_embedAB]
    _ = embedAB V := cyc_conj_back _

theorem cycinv_embedAC (V : Mat4) :
    CYCinv * embedAC V * CYC = embedBC (SWAP_4 * V * SWAP_4) := by
  have h := cyc_embedBC (SWAP_4 * V * SWAP_4)
  rw [show SWAP_4 * (SWAP_4 * V * SWAP_4) * SWAP_4 = V from SWAP_4_double_conj V] at h
  calc CYCinv * embedAC V * CYC
      = CYCinv * (CYC * embedBC (SWAP_4 * V * SWAP_4) * CYCinv) * CYC := by rw [h]
    _ = embedBC (SWAP_4 * V * SWAP_4) := cyc_conj_back _

theorem cycinv_embedAB (V : Mat4) :
    CYCinv * embedAB V * CYC = embedAC (SWAP_4 * V * SWAP_4) := by
  have h := cyc_embedAC (SWAP_4 * V * SWAP_4)
  rw [show SWAP_4 * (SWAP_4 * V * SWAP_4) * SWAP_4 = V from SWAP_4_double_conj V] at h
  calc CYCinv * embedAB V * CYC
      = CYCinv * (CYC * embedAC (SWAP_4 * V * SWAP_4) * CYCinv) * CYC := by rw [h]
    _ = embedAC (SWAP_4 * V * SWAP_4) := cyc_conj_back _

set_option maxHeartbeats 1600000 in
-- Heartbeats raised: conjugation distributed over an 11-factor 8×8 chain.
/-- Conjugating a 5-gate ABABA NEIGHBOR word by σ gives the paper's native
    BC-AC-BC-AC-BC word (with each layer's entries cyclically permuted). -/
theorem cyc_conj_ababa (V₁ V₂ V₃ V₄ V₅ : Mat4)
    (a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ a₄ b₄ c₄ a₅ b₅ c₅ : Mat2) :
    CYC * (singleQubitLayer a₀ b₀ c₀ * embedAB V₁ *
      singleQubitLayer a₁ b₁ c₁ * embedBC V₂ *
      singleQubitLayer a₂ b₂ c₂ * embedAB V₃ *
      singleQubitLayer a₃ b₃ c₃ * embedBC V₄ *
      singleQubitLayer a₄ b₄ c₄ * embedAB V₅ *
      singleQubitLayer a₅ b₅ c₅) * CYCinv =
    singleQubitLayer c₀ a₀ b₀ * embedBC V₁ *
      singleQubitLayer c₁ a₁ b₁ * embedAC (SWAP_4 * V₂ * SWAP_4) *
      singleQubitLayer c₂ a₂ b₂ * embedBC V₃ *
      singleQubitLayer c₃ a₃ b₃ * embedAC (SWAP_4 * V₄ * SWAP_4) *
      singleQubitLayer c₄ a₄ b₄ * embedBC V₅ *
      singleQubitLayer c₅ a₅ b₅ := by
  conv_rhs => rw [← cyc_singleQubitLayer a₀ b₀ c₀, ← cyc_embedAB V₁,
                  ← cyc_singleQubitLayer a₁ b₁ c₁, ← cyc_embedBC V₂,
                  ← cyc_singleQubitLayer a₂ b₂ c₂, ← cyc_embedAB V₃,
                  ← cyc_singleQubitLayer a₃ b₃ c₃, ← cyc_embedBC V₄,
                  ← cyc_singleQubitLayer a₄ b₄ c₄, ← cyc_embedAB V₅,
                  ← cyc_singleQubitLayer a₅ b₅ c₅]
  simp only [mul_assoc, cyc_cancel]

set_option maxHeartbeats 2000000 in
-- Heartbeats raised: assembles a 5-gate chain, `paper_lemma_4_4`, and the
-- inverse relabeling in one declaration.
/-- **Unitary ABABA 5→4 reduction** (iter 1042).

    A 5-gate `AB-BC-AB-BC-AB` neighbor word with UNITARY 2-qubit gates whose
    product is diagonal is a `UnitaryUnrestrictedCircuit 4`.

    This is the theorem that the sorry'd `ababa_v3_trichotomy_assembly` below
    was scaffolding for, and it needs no V₃ trichotomy at all: relabel by σ onto
    the paper's `BC-AC-BC-AC-BC` word (`cyc_conj_ababa`), absorb the six product
    layers into the five gates (`sandwich_BC_AC_BC_AC_BC_to_5embed`), apply the
    proved `HP.paper_lemma_4_4`, then relabel the resulting 4-gate word back —
    `BC-AC-AB-BC` comes back as `AB-BC-AC-AB`, which is unrestricted.

    Unitarity of the five gates is what the old `NeighborCircuit`-typed
    statement could not supply (its `compose_*` carries no `IsUnitary4 V`), and
    is exactly why this version is provable and that one was not. -/
theorem ababa_unitary_five_to_four
    (V₁ V₂ V₃ V₄ V₅ : Mat4)
    (hV₁ : IsUnitary4 V₁) (hV₂ : IsUnitary4 V₂) (hV₃ : IsUnitary4 V₃)
    (hV₄ : IsUnitary4 V₄) (hV₅ : IsUnitary4 V₅)
    (a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ a₄ b₄ c₄ a₅ b₅ c₅ : Mat2)
    (ha₀ : IsUnitary2 a₀) (hb₀ : IsUnitary2 b₀) (hc₀ : IsUnitary2 c₀)
    (ha₁ : IsUnitary2 a₁) (hb₁ : IsUnitary2 b₁) (hc₁ : IsUnitary2 c₁)
    (ha₂ : IsUnitary2 a₂) (hb₂ : IsUnitary2 b₂) (hc₂ : IsUnitary2 c₂)
    (ha₃ : IsUnitary2 a₃) (hb₃ : IsUnitary2 b₃) (hc₃ : IsUnitary2 c₃)
    (ha₄ : IsUnitary2 a₄) (hb₄ : IsUnitary2 b₄) (hc₄ : IsUnitary2 c₄)
    (ha₅ : IsUnitary2 a₅) (hb₅ : IsUnitary2 b₅) (hc₅ : IsUnitary2 c₅)
    (hD : IsDiag8 (singleQubitLayer a₀ b₀ c₀ * embedAB V₁ *
      singleQubitLayer a₁ b₁ c₁ * embedBC V₂ * singleQubitLayer a₂ b₂ c₂ * embedAB V₃ *
      singleQubitLayer a₃ b₃ c₃ * embedBC V₄ * singleQubitLayer a₄ b₄ c₄ * embedAB V₅ *
      singleQubitLayer a₅ b₅ c₅)) :
    UnitaryUnrestrictedCircuit 4
      (singleQubitLayer a₀ b₀ c₀ * embedAB V₁ *
      singleQubitLayer a₁ b₁ c₁ * embedBC V₂ * singleQubitLayer a₂ b₂ c₂ * embedAB V₃ *
      singleQubitLayer a₃ b₃ c₃ * embedBC V₄ * singleQubitLayer a₄ b₄ c₄ * embedAB V₅ *
      singleQubitLayer a₅ b₅ c₅) := by
  obtain ⟨Dg, hDg⟩ := isDiag8_cyc _ hD
  have h5 := (cyc_conj_ababa V₁ V₂ V₃ V₄ V₅
      a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ a₄ b₄ c₄ a₅ b₅ c₅).trans
    (sandwich_BC_AC_BC_AC_BC_to_5embed V₁ (SWAP_4 * V₂ * SWAP_4) V₃ (SWAP_4 * V₄ * SWAP_4) V₅
      c₀ a₀ b₀ c₁ a₁ b₁ c₂ a₂ b₂ c₃ a₃ b₃ c₄ a₄ b₄ c₅ a₅ b₅)
  have h_chain : Dg.toMatrix =
      embedBC (kron2 a₀ b₀ * V₁ * kron2 a₁ b₁) *
      embedAC (kron2 (c₀ * c₁) 1 * (SWAP_4 * V₂ * SWAP_4) * kron2 c₂ b₂) *
      embedBC (kron2 a₂ 1 * V₃ * kron2 a₃ b₃) *
      embedAC (kron2 c₃ 1 * (SWAP_4 * V₄ * SWAP_4) * kron2 c₄ b₄ * kron2 c₅ 1) *
      embedBC (kron2 a₄ 1 * V₅ * kron2 a₅ b₅) := hDg.symm.trans h5
  obtain ⟨Z₁, Z₂, Z₃, Z₄, hZ₁, hZ₂, hZ₃, hZ₄, hZ⟩ :=
    HP.paper_lemma_4_4 Dg _ _ _ _ _
      (isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 ha₀ hb₀) hV₁)
        (isUnitary4_kron2 ha₁ hb₁))
      (isUnitary4_mul (isUnitary4_mul
        (isUnitary4_kron2 (isUnitary2_mul hc₀ hc₁) isUnitary2_one)
        (isUnitary4_swap4_conj V₂ hV₂)) (isUnitary4_kron2 hc₂ hb₂))
      (isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 ha₂ isUnitary2_one) hV₃)
        (isUnitary4_kron2 ha₃ hb₃))
      (isUnitary4_mul (isUnitary4_mul (isUnitary4_mul
        (isUnitary4_kron2 hc₃ isUnitary2_one)
        (isUnitary4_swap4_conj V₄ hV₄)) (isUnitary4_kron2 hc₄ hb₄))
        (isUnitary4_kron2 hc₅ isUnitary2_one))
      (isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 ha₄ isUnitary2_one) hV₅)
        (isUnitary4_kron2 ha₅ hb₅))
      h_chain
  have hback : CYCinv * Dg.toMatrix * CYC =
      embedAB Z₁ * embedBC (SWAP_4 * Z₂ * SWAP_4) *
        embedAC (SWAP_4 * Z₃ * SWAP_4) * embedAB Z₄ := by
    rw [hZ]
    conv_rhs => rw [← cycinv_embedBC Z₁, ← cycinv_embedAC Z₂, ← cycinv_embedAB Z₃,
                    ← cycinv_embedBC Z₄]
    simp only [mul_assoc, cyc_cancel']
  have hM : singleQubitLayer a₀ b₀ c₀ * embedAB V₁ *
      singleQubitLayer a₁ b₁ c₁ * embedBC V₂ * singleQubitLayer a₂ b₂ c₂ * embedAB V₃ *
      singleQubitLayer a₃ b₃ c₃ * embedBC V₄ * singleQubitLayer a₄ b₄ c₄ * embedAB V₅ *
      singleQubitLayer a₅ b₅ c₅ =
      embedAB Z₁ * embedBC (SWAP_4 * Z₂ * SWAP_4) *
        embedAC (SWAP_4 * Z₃ * SWAP_4) * embedAB Z₄ := by
    rw [← hback, ← hDg, cyc_conj_back]
  rw [hM]
  have h : UnitaryUnrestrictedCircuit 4
      ((((singleQubitLayer I₂ I₂ I₂ * embedAB Z₁ * singleQubitLayer I₂ I₂ I₂) *
        embedBC (SWAP_4 * Z₂ * SWAP_4) * singleQubitLayer I₂ I₂ I₂) *
        embedAC (SWAP_4 * Z₃ * SWAP_4) * singleQubitLayer I₂ I₂ I₂) *
        embedAB Z₄ * singleQubitLayer I₂ I₂ I₂) :=
    .compose_AB Z₄ hZ₄ I₂ I₂ I₂ isUnitary2_one isUnitary2_one isUnitary2_one
      (.compose_AC (SWAP_4 * Z₃ * SWAP_4) (isUnitary4_swap4_conj Z₃ hZ₃) I₂ I₂ I₂
        isUnitary2_one isUnitary2_one isUnitary2_one
        (.compose_BC (SWAP_4 * Z₂ * SWAP_4) (isUnitary4_swap4_conj Z₂ hZ₂) I₂ I₂ I₂
          isUnitary2_one isUnitary2_one isUnitary2_one
          (.compose_AB Z₁ hZ₁ I₂ I₂ I₂ isUnitary2_one isUnitary2_one isUnitary2_one
            (.product I₂ I₂ I₂ isUnitary2_one isUnitary2_one isUnitary2_one))))
  simp only [singleQubitLayer_one, mul_one, one_mul] at h
  exact h

/-! ## Theorem 4.5, unitary form (iter 1042)

The `NeighborCircuit`-typed 5→4 reduction below could never be closed: its
`compose_*` constructors carry no `IsUnitary4 V`, and the paper's Lemma 4.4 is
a spectral argument that needs it. These are the `UnitaryNeighborCircuit`
twins, for which the same case tree goes through and the ABABA leaf is closed
by `ababa_unitary_five_to_four`. -/

theorem unitaryNeighborCircuit_mul_product {n : ℕ} {U : Mat8}
    (h : UnitaryNeighborCircuit n U) (dA dB dC : Mat2)
    (hdA : IsUnitary2 dA) (hdB : IsUnitary2 dB) (hdC : IsUnitary2 dC) :
    UnitaryNeighborCircuit n (U * singleQubitLayer dA dB dC) := by
  induction h with
  | product uA uB uC hA hB hC =>
    rw [singleQubitLayer_mul]
    exact .product _ _ _ (isUnitary2_mul hA hdA) (isUnitary2_mul hB hdB)
      (isUnitary2_mul hC hdC)
  | weaken _ ih => exact .weaken ih
  | @compose_AB _ rest V hV uA uB uC hA hB hC hrest _ =>
    change UnitaryNeighborCircuit _
      (rest * embedAB V * singleQubitLayer uA uB uC * singleQubitLayer dA dB dC)
    rw [mul_assoc (rest * embedAB V), singleQubitLayer_mul]
    exact .compose_AB V hV _ _ _ (isUnitary2_mul hA hdA) (isUnitary2_mul hB hdB)
      (isUnitary2_mul hC hdC) hrest
  | @compose_BC _ rest V hV uA uB uC hA hB hC hrest _ =>
    change UnitaryNeighborCircuit _
      (rest * embedBC V * singleQubitLayer uA uB uC * singleQubitLayer dA dB dC)
    rw [mul_assoc (rest * embedBC V), singleQubitLayer_mul]
    exact .compose_BC V hV _ _ _ (isUnitary2_mul hA hdA) (isUnitary2_mul hB hdB)
      (isUnitary2_mul hC hdC) hrest

theorem unitaryNeighborCircuit_merge_AB_AB {n : ℕ} {rest : Mat8}
    (V₁ V₂ : Mat4) (hV₁ : IsUnitary4 V₁) (hV₂ : IsUnitary4 V₂)
    (uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ : Mat2)
    (hA₁ : IsUnitary2 uA₁) (hB₁ : IsUnitary2 uB₁) (hC₁ : IsUnitary2 uC₁)
    (hA₂ : IsUnitary2 uA₂) (hB₂ : IsUnitary2 uB₂) (hC₂ : IsUnitary2 uC₂)
    (hrest : UnitaryNeighborCircuit n rest) :
    UnitaryNeighborCircuit (n + 1)
      (rest * embedAB V₁ * singleQubitLayer uA₁ uB₁ uC₁ *
       embedAB V₂ * singleQubitLayer uA₂ uB₂ uC₂) := by
  rw [show rest * embedAB V₁ * singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
        singleQubitLayer uA₂ uB₂ uC₂ =
      rest * (embedAB V₁ * singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂) *
        singleQubitLayer uA₂ uB₂ uC₂ from by simp only [mul_assoc], embedAB_merge,
      show rest * (singleQubitLayer I₂ I₂ uC₁ *
          embedAB (V₁ * (kron2 uA₁ uB₁ * V₂))) * singleQubitLayer uA₂ uB₂ uC₂ =
        (rest * singleQubitLayer I₂ I₂ uC₁) *
          embedAB (V₁ * (kron2 uA₁ uB₁ * V₂)) * singleQubitLayer uA₂ uB₂ uC₂
      from by simp only [mul_assoc]]
  exact .compose_AB _
    (isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hB₁) hV₂))
    _ _ _ hA₂ hB₂ hC₂
    (unitaryNeighborCircuit_mul_product hrest I₂ I₂ uC₁ isUnitary2_one isUnitary2_one hC₁)

theorem unitaryNeighborCircuit_merge_BC_BC {n : ℕ} {rest : Mat8}
    (V₁ V₂ : Mat4) (hV₁ : IsUnitary4 V₁) (hV₂ : IsUnitary4 V₂)
    (uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ : Mat2)
    (hA₁ : IsUnitary2 uA₁) (hB₁ : IsUnitary2 uB₁) (hC₁ : IsUnitary2 uC₁)
    (hA₂ : IsUnitary2 uA₂) (hB₂ : IsUnitary2 uB₂) (hC₂ : IsUnitary2 uC₂)
    (hrest : UnitaryNeighborCircuit n rest) :
    UnitaryNeighborCircuit (n + 1)
      (rest * embedBC V₁ * singleQubitLayer uA₁ uB₁ uC₁ *
       embedBC V₂ * singleQubitLayer uA₂ uB₂ uC₂) := by
  rw [show rest * embedBC V₁ * singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
        singleQubitLayer uA₂ uB₂ uC₂ =
      rest * (embedBC V₁ * singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂) *
        singleQubitLayer uA₂ uB₂ uC₂ from by simp only [mul_assoc], embedBC_merge,
      show rest * (singleQubitLayer uA₁ I₂ I₂ *
          embedBC (V₁ * (kron2 uB₁ uC₁ * V₂))) * singleQubitLayer uA₂ uB₂ uC₂ =
        (rest * singleQubitLayer uA₁ I₂ I₂) *
          embedBC (V₁ * (kron2 uB₁ uC₁ * V₂)) * singleQubitLayer uA₂ uB₂ uC₂
      from by simp only [mul_assoc]]
  exact .compose_BC _
    (isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hB₁ hC₁) hV₂))
    _ _ _ hA₂ hB₂ hC₂
    (unitaryNeighborCircuit_mul_product hrest uA₁ I₂ I₂ hA₁ isUnitary2_one isUnitary2_one)

theorem swap_ac_unitaryNeighborCircuit {n : ℕ} {U : Mat8}
    (h : UnitaryNeighborCircuit n U) :
    UnitaryNeighborCircuit n (SWAP_AC * U * SWAP_AC) := by
  induction h with
  | product uA uB uC hA hB hC =>
    rw [swap_ac_singleQubitLayer]; exact .product uC uB uA hC hB hA
  | weaken _ ih => exact .weaken ih
  | @compose_AB _ rest V hV uA uB uC hA hB hC _ ih =>
    change UnitaryNeighborCircuit _
      (SWAP_AC * (rest * embedAB V * singleQubitLayer uA uB uC) * SWAP_AC)
    rw [swap_ac_conj_distrib, swap_ac_conj_distrib, swap_ac_embedAB,
        swap_ac_singleQubitLayer]
    exact .compose_BC _ (isUnitary4_swap4_conj V hV) uC uB uA hC hB hA ih
  | @compose_BC _ rest V hV uA uB uC hA hB hC _ ih =>
    change UnitaryNeighborCircuit _
      (SWAP_AC * (rest * embedBC V * singleQubitLayer uA uB uC) * SWAP_AC)
    rw [swap_ac_conj_distrib, swap_ac_conj_distrib, swap_ac_embedBC,
        swap_ac_singleQubitLayer]
    exact .compose_AB _ (isUnitary4_swap4_conj V hV) uC uB uA hC hB hA ih

set_option maxHeartbeats 1600000 in
-- Heartbeats raised: five nested `cases` over a 5-gate circuit.
/-- Unitary twin of `ababa_compose_AB_main`: outermost gate destructured as AB. -/
private lemma ababa_unitary_compose_AB_main
    (V₅ : Mat4) (hV₅ : IsUnitary4 V₅) (uA₅ uB₅ uC₅ : Mat2)
    (hA₅ : IsUnitary2 uA₅) (hB₅ : IsUnitary2 uB₅) (hC₅ : IsUnitary2 uC₅)
    {rest4 : Mat8} (h4 : UnitaryNeighborCircuit 4 rest4)
    (hD : IsDiag8 (rest4 * embedAB V₅ * singleQubitLayer uA₅ uB₅ uC₅)) :
    UnitaryUnrestrictedCircuit 4
      (rest4 * embedAB V₅ * singleQubitLayer uA₅ uB₅ uC₅) := by
  cases h4 with
  | weaken h3 =>
    exact .compose_AB V₅ hV₅ uA₅ uB₅ uC₅ hA₅ hB₅ hC₅
      (unitaryNeighborCircuit_to_unitaryUnrestricted h3)
  | compose_AB V₄ hV₄ uA₄ uB₄ uC₄ hA₄ hB₄ hC₄ h3 =>
    exact unitaryNeighborCircuit_to_unitaryUnrestricted
      (unitaryNeighborCircuit_merge_AB_AB V₄ V₅ hV₄ hV₅ uA₄ uB₄ uC₄ uA₅ uB₅ uC₅
        hA₄ hB₄ hC₄ hA₅ hB₅ hC₅ h3)
  | compose_BC V₄ hV₄ uA₄ uB₄ uC₄ hA₄ hB₄ hC₄ h3 =>
    cases h3 with
    | weaken h2 =>
      exact .compose_AB V₅ hV₅ uA₅ uB₅ uC₅ hA₅ hB₅ hC₅
        (.compose_BC V₄ hV₄ uA₄ uB₄ uC₄ hA₄ hB₄ hC₄
          (unitaryNeighborCircuit_to_unitaryUnrestricted h2))
    | compose_BC V₃ hV₃ uA₃ uB₃ uC₃ hA₃ hB₃ hC₃ h2 =>
      exact unitaryNeighborCircuit_to_unitaryUnrestricted
        (.compose_AB V₅ hV₅ uA₅ uB₅ uC₅ hA₅ hB₅ hC₅
          (unitaryNeighborCircuit_merge_BC_BC V₃ V₄ hV₃ hV₄ uA₃ uB₃ uC₃ uA₄ uB₄ uC₄
            hA₃ hB₃ hC₃ hA₄ hB₄ hC₄ h2))
    | compose_AB V₃ hV₃ uA₃ uB₃ uC₃ hA₃ hB₃ hC₃ h2 =>
      cases h2 with
      | weaken h1 =>
        exact .compose_AB V₅ hV₅ uA₅ uB₅ uC₅ hA₅ hB₅ hC₅
          (.compose_BC V₄ hV₄ uA₄ uB₄ uC₄ hA₄ hB₄ hC₄
            (.compose_AB V₃ hV₃ uA₃ uB₃ uC₃ hA₃ hB₃ hC₃
              (unitaryNeighborCircuit_to_unitaryUnrestricted h1)))
      | compose_AB V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        exact unitaryNeighborCircuit_to_unitaryUnrestricted
          (.compose_AB V₅ hV₅ uA₅ uB₅ uC₅ hA₅ hB₅ hC₅
            (.compose_BC V₄ hV₄ uA₄ uB₄ uC₄ hA₄ hB₄ hC₄
              (unitaryNeighborCircuit_merge_AB_AB V₂ V₃ hV₂ hV₃ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃
                hA₂ hB₂ hC₂ hA₃ hB₃ hC₃ h1)))
      | compose_BC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        cases h1 with
        | weaken h0 =>
          exact .compose_AB V₅ hV₅ uA₅ uB₅ uC₅ hA₅ hB₅ hC₅
            (.compose_BC V₄ hV₄ uA₄ uB₄ uC₄ hA₄ hB₄ hC₄
              (.compose_AB V₃ hV₃ uA₃ uB₃ uC₃ hA₃ hB₃ hC₃
                (.compose_BC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂
                  (unitaryNeighborCircuit_to_unitaryUnrestricted h0))))
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          exact unitaryNeighborCircuit_to_unitaryUnrestricted
            (.compose_AB V₅ hV₅ uA₅ uB₅ uC₅ hA₅ hB₅ hC₅
              (.compose_BC V₄ hV₄ uA₄ uB₄ uC₄ hA₄ hB₄ hC₄
                (.compose_AB V₃ hV₃ uA₃ uB₃ uC₃ hA₃ hB₃ hC₃
                  (unitaryNeighborCircuit_merge_BC_BC V₁ V₂ hV₁ hV₂
                    uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ hA₁ hB₁ hC₁ hA₂ hB₂ hC₂ h0))))
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- TRUE ABABA. No V₃ trichotomy: relabel onto the paper's word.
          cases h0 with
          | product a₀ b₀ c₀ ha₀ hb₀ hc₀ =>
            exact ababa_unitary_five_to_four V₁ V₂ V₃ V₄ V₅ hV₁ hV₂ hV₃ hV₄ hV₅
              a₀ b₀ c₀ uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA₄ uB₄ uC₄ uA₅ uB₅ uC₅
              ha₀ hb₀ hc₀ hA₁ hB₁ hC₁ hA₂ hB₂ hC₂ hA₃ hB₃ hC₃ hA₄ hB₄ hC₄
              hA₅ hB₅ hC₅ hD

set_option maxHeartbeats 800000 in
-- Heartbeats raised: three-way case split feeding a large auxiliary lemma.
/-- **Theorem 4.5 (Huang & Palsberg), unitary form.** A diagonal gate
    implementable with 5 neighbor gates whose 2-qubit gates are UNITARY is
    implementable with 4 unrestricted unitary gates. -/
theorem five_unitaryNeighbor_to_four_unitaryUnrestricted (D : Mat8) (hD : IsDiag8 D)
    (h5 : UnitaryNeighborCircuit 5 D) : UnitaryUnrestrictedCircuit 4 D := by
  cases h5 with
  | weaken h4 => exact unitaryNeighborCircuit_to_unitaryUnrestricted h4
  | compose_AB V₅ hV₅ uA₅ uB₅ uC₅ hA₅ hB₅ hC₅ h4 =>
    exact ababa_unitary_compose_AB_main V₅ hV₅ uA₅ uB₅ uC₅ hA₅ hB₅ hC₅ h4 hD
  | compose_BC V₅ hV₅ uA₅ uB₅ uC₅ hA₅ hB₅ hC₅ h4 =>
    apply swap_ac_unitaryUnrestrictedCircuit_inv
    rw [swap_ac_conj_distrib, swap_ac_conj_distrib, swap_ac_embedBC,
        swap_ac_singleQubitLayer]
    exact ababa_unitary_compose_AB_main (SWAP_4 * V₅ * SWAP_4)
      (isUnitary4_swap4_conj V₅ hV₅) uC₅ uB₅ uA₅ hC₅ hB₅ hA₅
      (swap_ac_unitaryNeighborCircuit h4)
      (by
        have hDswap := isDiag8_swap_ac _ hD
        rwa [swap_ac_conj_distrib, swap_ac_conj_distrib, swap_ac_embedBC,
             swap_ac_singleQubitLayer] at hDswap)

/-! ## Retired (iter 1043): the non-unitary 5-4 reduction

`ababa_v3_trichotomy_assembly`, `ababa_compose_AB_main`,
`alternating_five_to_four` and `five_neighbor_to_four_unrestricted` were
stated over `NeighborCircuit`, whose `compose_*` constructors carry no
`IsUnitary4 V`. The paper Lemma 4.4 argument is spectral and needs that
unitarity, and the forgetful lift from the unitary inductive is provably
false (`AB(V1) * SQL * AB(V2) = (V1 (a x b) V2) x c`; take `V1 = 2W`,
`V2 = W'/2`). They are replaced by
`five_unitaryNeighbor_to_four_unitaryUnrestricted` above. -/

end
