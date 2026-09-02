/-
  ApproxToffoli.HP.EmbedLemmas
  Algebraic properties of embedAB, embedBC, and SWAP_BC.

  Key lemmas (from Huang & Palsberg Appendix A):
  - embedAB_mul / embedBC_mul: embedding is a homomorphism
  - embedAB_conjTranspose / embedBC_conjTranspose: embedding commutes with dagger
  - SWAP conjugation lemmas

  Reference: Huang & Palsberg (2026), Appendix A.
-/

import ApproxToffoli.HP.Embedding
import ApproxToffoli.BlockDecomp

open Matrix Complex

noncomputable section

/-! ## Embedding is a ring homomorphism -/

/-- embedAB preserves multiplication: embedAB(V) * embedAB(W) = embedAB(V * W) -/
theorem embedAB_mul (V W : Mat4) : embedAB V * embedAB W = embedAB (V * W) := by
  ext i j
  simp only [embedAB, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_eight]
  fin_cases i <;> fin_cases j <;>
  · simp [Fin.sum_univ_four]

/-- embedBC preserves multiplication: embedBC(V) * embedBC(W) = embedBC(V * W) -/
theorem embedBC_mul (V W : Mat4) : embedBC V * embedBC W = embedBC (V * W) := by
  ext i j
  simp only [embedBC, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_eight]
  fin_cases i <;> fin_cases j <;>
  · simp [Fin.sum_univ_four]

/-! ## Embedding commutes with conjugate transpose -/

/-- embedAB commutes with †: (embedAB V)† = embedAB (V†) -/
theorem embedAB_conjTranspose (V : Mat4) :
    (embedAB V).conjTranspose = embedAB V.conjTranspose := by
  ext i j
  simp only [embedAB, Matrix.conjTranspose_apply, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;>
  · simp [star_zero]

/-- embedBC commutes with †: (embedBC V)† = embedBC (V†) -/
theorem embedBC_conjTranspose (V : Mat4) :
    (embedBC V).conjTranspose = embedBC V.conjTranspose := by
  ext i j
  simp only [embedBC, Matrix.conjTranspose_apply, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;>
  · simp [star_zero]

/-! ## Embedding on qubits A,C (non-neighbor)

embedAC(V) acts as V on qubits A,C with identity on qubit B.
In binary encoding i = 4a + 2b + c, the (A,C) index is 2a + c.
So embedAC(V)_{i,j} = δ_{b_i, b_j} · V_{2a_i+c_i, 2a_j+c_j}
where b = (i/2) mod 2.
-/

/-- Embed a 4×4 gate V on qubits A,C with identity on qubit B.
    (The non-neighbor embedding, obtained by SWAP conjugation.) -/
def embedAC (V : Mat4) : Mat8 :=
  Matrix.of fun (i j : Fin 8) =>
    if (i.val / 2) % 2 = (j.val / 2) % 2 then
      V ⟨2 * (i.val / 4) + i.val % 2, by omega⟩
        ⟨2 * (j.val / 4) + j.val % 2, by omega⟩
    else 0

/-- embedAC preserves multiplication: embedAC(V) * embedAC(W) = embedAC(V * W) -/
theorem embedAC_mul (V W : Mat4) : embedAC V * embedAC W = embedAC (V * W) := by
  ext i j
  simp only [embedAC, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_eight]
  fin_cases i <;> fin_cases j <;>
  · simp [Fin.sum_univ_four]

/-- embedAC commutes with †: (embedAC V)† = embedAC (V†) -/
theorem embedAC_conjTranspose (V : Mat4) :
    (embedAC V).conjTranspose = embedAC V.conjTranspose := by
  ext i j
  simp only [embedAC, Matrix.conjTranspose_apply, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;>
  · simp [star_zero]

/-- embedAC preserves identity: embedAC(1) = 1 -/
theorem embedAC_one : embedAC 1 = 1 := by
  ext i j
  simp only [embedAC, Matrix.of_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;>
  · simp

/-- A tensor-product gate `kron2 Ra Rb` embedded on (A,C) is a single-qubit layer
    with Ra on A, I on B, Rb on C. -/
theorem embedAC_kron2 (Ra Rb : Mat2) :
    embedAC (kron2 Ra Rb) = singleQubitLayer Ra I₂ Rb := by
  ext i j
  simp only [embedAC, singleQubitLayer, kron3, kron2, I₂, decode3,
             Matrix.of_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;>
  · simp

/-- A tensor-product gate `kron2 Rb Rc` embedded on (B,C) is a single-qubit layer
    with I on A, Rb on B, Rc on C. -/
theorem embedBC_kron2 (Rb Rc : Mat2) :
    embedBC (kron2 Rb Rc) = singleQubitLayer I₂ Rb Rc := by
  ext i j
  simp only [embedBC, singleQubitLayer, kron3, kron2, I₂, decode3,
             Matrix.of_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;>
  · simp

/-- A tensor-product gate `kron2 Ra Rb` embedded on (A,B) is a single-qubit layer
    with Ra on A, Rb on B, I on C. -/
theorem embedAB_kron2 (Ra Rb : Mat2) :
    embedAB (kron2 Ra Rb) = singleQubitLayer Ra Rb I₂ := by
  ext i j
  simp only [embedAB, singleQubitLayer, kron3, kron2, I₂, decode3,
             Matrix.of_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;>
  · simp

/-- Iter 770: tensor-structured embedAC decomposes into embedAB · embedBC.
    `embedAC(kron2 P Q) = embedAB(kron2 P 1) * embedBC(kron2 1 Q)`.
    Useful for paper Lemma C.1 when V₁ has tensor structure (a special-
    case stepping stone; general entangling V₁ doesn't decompose this way). -/
theorem embedAC_kron2_eq_embedAB_embedBC (P Q : Mat2) :
    embedAC (kron2 P Q) = embedAB (kron2 P 1) * embedBC (kron2 1 Q) := by
  rw [embedAC_kron2, embedAB_kron2, embedBC_kron2, singleQubitLayer_mul]
  simp [I₂]

/-- Iter 771: SQL with identity on qubit B splits into AB and BC embeds.
    Specialization of iter 770 via `embedAC_kron2`. Useful when SQL has
    trivial middle component (I on qubit 2). -/
theorem singleQubitLayer_I_middle_eq_embedAB_embedBC (P Q : Mat2) :
    singleQubitLayer P I₂ Q = embedAB (kron2 P 1) * embedBC (kron2 1 Q) := by
  rw [← embedAC_kron2, embedAC_kron2_eq_embedAB_embedBC]

/-- Iter 773: Commuted version of iter 770 — `embedBC(kron2 1 Q) ·
    embedAB(kron2 P 1) = embedAC(kron2 P Q)`. Disjoint qubit supports
    (qubit 1 vs qubit 3 of the kron2 inputs) make BC·AB and AB·BC
    interchangeable. Useful for chain rewrites where the BC factor
    appears first. -/
theorem embedBC_embedAB_eq_embedAC_kron2 (P Q : Mat2) :
    embedBC (kron2 1 Q) * embedAB (kron2 P 1) = embedAC (kron2 P Q) := by
  rw [embedBC_kron2, embedAB_kron2, singleQubitLayer_mul, embedAC_kron2]
  simp [I₂]

/-- **A.24 helper**: when X acts only on qubit A (i.e., `kron2 X 1`), embedding
    via embedAB or embedAC gives the same Mat8 (both are X⊗I⊗I). Used to
    convert `embedAC U · embedAB (kron2 p 1)` into `embedAC (U · kron2 p 1)`. -/
theorem embedAB_kron2_one_eq_embedAC_kron2_one (X : Mat2) :
    embedAB (kron2 X 1) = embedAC (kron2 X 1) := by
  rw [embedAB_kron2, embedAC_kron2]
  unfold I₂
  rfl

/-- Iter 777: dual of the above — when Y acts only on qubit C (i.e.,
    `kron2 1 Y`), embedding via embedBC or embedAC gives the same Mat8
    (both are I⊗I⊗Y). -/
theorem embedBC_kron2_one_eq_embedAC_kron2_one (Y : Mat2) :
    embedBC (kron2 1 Y) = embedAC (kron2 1 Y) := by
  rw [embedBC_kron2, embedAC_kron2]
  unfold I₂
  rfl

/-! ## Commutation: embedAB commutes with C-only product layers

embedAB(V) acts on qubits A,B while singleQubitLayer(I₂,I₂,uC) acts only on qubit C.
These commute because they act on disjoint qubit subspaces. -/

/-- AB embedding commutes with C-only product layers -/
theorem embedAB_comm_singleQubitLayer_C (V : Mat4) (uC : Mat2) :
    embedAB V * singleQubitLayer I₂ I₂ uC = singleQubitLayer I₂ I₂ uC * embedAB V := by
  ext i j
  simp only [singleQubitLayer, kron3, embedAB, I₂, decode3,
             Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply,
             Fin.sum_univ_eight]
  fin_cases i <;> fin_cases j <;>
    (simp; ring)

/-- BC embedding commutes with A-only product layers -/
theorem embedBC_comm_singleQubitLayer_A (V : Mat4) (uA : Mat2) :
    embedBC V * singleQubitLayer uA I₂ I₂ = singleQubitLayer uA I₂ I₂ * embedBC V := by
  ext i j
  simp only [singleQubitLayer, kron3, embedBC, I₂, decode3,
             Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply,
             Fin.sum_univ_eight]
  fin_cases i <;> fin_cases j <;>
    (simp; ring)

/-- AC embedding commutes with B-only product layers (B is outside AC's scope) -/
theorem embedAC_comm_singleQubitLayer_B (V : Mat4) (uB : Mat2) :
    embedAC V * singleQubitLayer I₂ uB I₂ = singleQubitLayer I₂ uB I₂ * embedAC V := by
  ext i j
  simp only [singleQubitLayer, kron3, embedAC, I₂, decode3,
             Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply,
             Fin.sum_univ_eight]
  fin_cases i <;> fin_cases j <;>
    (simp; ring)

/-! ## Absorption: product layers partially absorb into embeddings

singleQubitLayer(uA,uB,uC) * embedAB(V) = singleQubitLayer(I₂,I₂,uC) * embedAB(kron2(uA,uB) * V)
The AB part of the product layer is absorbed into the AB gate via kron2. -/

/-- Product layer absorption into AB embedding:
    the AB components of the product layer merge with the gate via kron2 -/
theorem singleQubitLayer_mul_embedAB (uA uB uC : Mat2) (V : Mat4) :
    singleQubitLayer uA uB uC * embedAB V =
    singleQubitLayer I₂ I₂ uC * embedAB (kron2 uA uB * V) := by
  ext i j
  simp only [singleQubitLayer, kron3, embedAB, I₂, kron2, decode3,
             Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply,
             Fin.sum_univ_eight, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
    (simp; ring)

/-- Product layer absorption into BC embedding:
    the BC components of the product layer merge with the gate via kron2 -/
theorem singleQubitLayer_mul_embedBC (uA uB uC : Mat2) (V : Mat4) :
    singleQubitLayer uA uB uC * embedBC V =
    singleQubitLayer uA I₂ I₂ * embedBC (kron2 uB uC * V) := by
  ext i j
  simp only [singleQubitLayer, kron3, embedBC, I₂, kron2, decode3,
             Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply,
             Fin.sum_univ_eight, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
    (simp; ring)

/-! ## Gate merging: two adjacent same-type gates combine into one

embedAB(V₁) * P(uA,uB,uC) * embedAB(V₂) = P(I₂,I₂,uC) * embedAB(V₁ * kron2(uA,uB) * V₂)
Two AB gates with a product layer between them merge into one AB gate
plus a residual C-only product layer. This is the key step for Theorem 4.5. -/

/-- Two adjacent AB gates with product layer merge into one AB gate -/
theorem embedAB_merge (V₁ V₂ : Mat4) (uA uB uC : Mat2) :
    embedAB V₁ * singleQubitLayer uA uB uC * embedAB V₂ =
    singleQubitLayer I₂ I₂ uC * embedAB (V₁ * (kron2 uA uB * V₂)) := by
  calc embedAB V₁ * singleQubitLayer uA uB uC * embedAB V₂
      = embedAB V₁ * (singleQubitLayer uA uB uC * embedAB V₂) := by
          rw [mul_assoc]
    _ = embedAB V₁ * (singleQubitLayer I₂ I₂ uC * embedAB (kron2 uA uB * V₂)) := by
          rw [singleQubitLayer_mul_embedAB]
    _ = (embedAB V₁ * singleQubitLayer I₂ I₂ uC) * embedAB (kron2 uA uB * V₂) := by
          rw [mul_assoc]
    _ = (singleQubitLayer I₂ I₂ uC * embedAB V₁) * embedAB (kron2 uA uB * V₂) := by
          rw [embedAB_comm_singleQubitLayer_C]
    _ = singleQubitLayer I₂ I₂ uC * (embedAB V₁ * embedAB (kron2 uA uB * V₂)) := by
          rw [mul_assoc]
    _ = singleQubitLayer I₂ I₂ uC * embedAB (V₁ * (kron2 uA uB * V₂)) := by
          rw [embedAB_mul]

/-- Two adjacent BC gates with product layer merge into one BC gate -/
theorem embedBC_merge (V₁ V₂ : Mat4) (uA uB uC : Mat2) :
    embedBC V₁ * singleQubitLayer uA uB uC * embedBC V₂ =
    singleQubitLayer uA I₂ I₂ * embedBC (V₁ * (kron2 uB uC * V₂)) := by
  calc embedBC V₁ * singleQubitLayer uA uB uC * embedBC V₂
      = embedBC V₁ * (singleQubitLayer uA uB uC * embedBC V₂) := by
          rw [mul_assoc]
    _ = embedBC V₁ * (singleQubitLayer uA I₂ I₂ * embedBC (kron2 uB uC * V₂)) := by
          rw [singleQubitLayer_mul_embedBC]
    _ = (embedBC V₁ * singleQubitLayer uA I₂ I₂) * embedBC (kron2 uB uC * V₂) := by
          rw [mul_assoc]
    _ = (singleQubitLayer uA I₂ I₂ * embedBC V₁) * embedBC (kron2 uB uC * V₂) := by
          rw [embedBC_comm_singleQubitLayer_A]
    _ = singleQubitLayer uA I₂ I₂ * (embedBC V₁ * embedBC (kron2 uB uC * V₂)) := by
          rw [mul_assoc]
    _ = singleQubitLayer uA I₂ I₂ * embedBC (V₁ * (kron2 uB uC * V₂)) := by
          rw [embedBC_mul]

/-! ## SWAP conjugation: converts AB gates to AC gates

Lemma 4.2 from Huang & Palsberg:
SWAP_BC · embedAB(V) · SWAP_BC = embedAC(V)
-/

/-- SWAP conjugation converts AB embedding to AC embedding -/
theorem swap_bc_embedAB (V : Mat4) :
    SWAP_BC * embedAB V * SWAP_BC = embedAC V := by
  ext i j
  unfold SWAP_BC swap_bc_perm embedAB embedAC
  simp only [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_eight]
  fin_cases i <;> fin_cases j <;>
  · simp

/-- SWAP conjugation converts AC embedding back to AB embedding -/
theorem swap_bc_embedAC (V : Mat4) :
    SWAP_BC * embedAC V * SWAP_BC = embedAB V := by
  have h := swap_bc_embedAB V
  -- From SWAP * embedAB(V) * SWAP = embedAC(V), multiply both sides by SWAP
  calc SWAP_BC * embedAC V * SWAP_BC
      = SWAP_BC * (SWAP_BC * embedAB V * SWAP_BC) * SWAP_BC := by rw [h]
    _ = (SWAP_BC * SWAP_BC) * embedAB V * (SWAP_BC * SWAP_BC) := by
        simp only [mul_assoc]
    _ = 1 * embedAB V * 1 := by rw [SWAP_BC_sq]
    _ = embedAB V := by rw [one_mul, mul_one]

/-! ## SWAP_BC as an embedding: SWAP_BC = embedBC(SWAP_4)

The 3-qubit SWAP_BC is just the 2-qubit SWAP embedded on the BC subspace.
This allows algebraic proofs of SWAP conjugation identities. -/

/-- The 2-qubit SWAP permutation: maps index (b,c) ↦ (c,b), i.e., 0↦0, 1↦2, 2↦1, 3↦3 -/
def swap4_perm : Fin 4 → Fin 4
  | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3

/-- The 2-qubit SWAP matrix on a 4×4 space -/
def SWAP_4 : Mat4 :=
  Matrix.of fun (i j : Fin 4) =>
    if swap4_perm i = j then 1 else 0

/-- SWAP_4 is an involution: SWAP_4 · SWAP_4 = 1. -/
theorem SWAP_4_sq : SWAP_4 * SWAP_4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SWAP_4, swap4_perm, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_four]

/-- SWAP_4 is self-adjoint: SWAP_4† = SWAP_4. -/
theorem SWAP_4_conjTranspose : SWAP_4.conjTranspose = SWAP_4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SWAP_4, swap4_perm, Matrix.conjTranspose_apply, Matrix.of_apply]

/-- SWAP_4 is unitary. -/
theorem isUnitary4_SWAP_4 : IsUnitary4 SWAP_4 := by
  unfold IsUnitary4
  rw [SWAP_4_conjTranspose, SWAP_4_sq]

/-- Conjugation by SWAP_4 preserves unitarity. -/
theorem isUnitary4_swap4_conj (V : Mat4) (hV : IsUnitary4 V) :
    IsUnitary4 (SWAP_4 * V * SWAP_4) := by
  unfold IsUnitary4
  have h_assoc : (SWAP_4 * V * SWAP_4).conjTranspose * (SWAP_4 * V * SWAP_4) =
      SWAP_4 * V.conjTranspose * (SWAP_4 * SWAP_4) * V * SWAP_4 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, SWAP_4_conjTranspose]
    noncomm_ring
  rw [h_assoc, SWAP_4_sq]
  have h_assoc2 : SWAP_4 * V.conjTranspose * 1 * V * SWAP_4 =
      SWAP_4 * (V.conjTranspose * V) * SWAP_4 := by noncomm_ring
  rw [h_assoc2, hV, Matrix.mul_one, SWAP_4_sq]

/-- Double SWAP_4 conjugation cancels: SWAP_4·(SWAP_4·V·SWAP_4)·SWAP_4 = V.
    Used when chained SWAP conjugations apply SWAP_4-conjugation twice on the
    same gate (the outer application cancels the inner). -/
theorem SWAP_4_double_conj (V : Mat4) :
    SWAP_4 * (SWAP_4 * V * SWAP_4) * SWAP_4 = V := by
  have h_assoc : SWAP_4 * (SWAP_4 * V * SWAP_4) * SWAP_4 =
      (SWAP_4 * SWAP_4) * V * (SWAP_4 * SWAP_4) := by noncomm_ring
  rw [h_assoc, SWAP_4_sq, Matrix.one_mul, Matrix.mul_one]

/-- SWAP_BC equals the 2-qubit SWAP embedded on qubits B,C -/
theorem SWAP_BC_eq_embedBC : SWAP_BC = embedBC SWAP_4 := by
  ext i j
  unfold SWAP_BC swap_bc_perm embedBC SWAP_4 swap4_perm
  simp only [Matrix.of_apply]
  fin_cases i <;> fin_cases j <;> simp

/-- SWAP conjugation of embedBC: reorders the gate's qubit inputs -/
theorem swap_bc_embedBC (V : Mat4) :
    SWAP_BC * embedBC V * SWAP_BC = embedBC (SWAP_4 * V * SWAP_4) := by
  rw [SWAP_BC_eq_embedBC, embedBC_mul, embedBC_mul]

/-! ## SWAP conjugation of product layers

SWAP_BC swaps qubits B and C, so it maps singleQubitLayer(uA,uB,uC) to
singleQubitLayer(uA,uC,uB). -/

/-- SWAP conjugation swaps B and C in product layers -/
theorem swap_bc_singleQubitLayer (uA uB uC : Mat2) :
    SWAP_BC * singleQubitLayer uA uB uC * SWAP_BC = singleQubitLayer uA uC uB := by
  ext i j
  simp only [SWAP_BC, swap_bc_perm, singleQubitLayer, kron3, decode3,
             Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_eight]
  fin_cases i <;> fin_cases j <;>
    (simp; ring)

/-! ## Product layers as embeddings

singleQubitLayer(uA, uB, I₂) = embedAB(kron2 uA uB): a product layer with identity
on qubit C is the same as embedding kron2(uA,uB) on the AB subspace.
Similarly for BC. -/

/-- Product layer with identity on C equals AB embedding of kron2 -/
theorem singleQubitLayer_eq_embedAB_kron2 (uA uB : Mat2) :
    singleQubitLayer uA uB I₂ = embedAB (kron2 uA uB) := by
  ext i j
  simp only [singleQubitLayer, kron3, decode3, embedAB, kron2, I₂,
             Matrix.of_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;>
  · simp

/-- Product layer with identity on A equals BC embedding of kron2 -/
theorem singleQubitLayer_eq_embedBC_kron2 (uB uC : Mat2) :
    singleQubitLayer I₂ uB uC = embedBC (kron2 uB uC) := by
  ext i j
  simp only [singleQubitLayer, kron3, decode3, embedBC, kron2, I₂,
             Matrix.of_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;>
  · simp

/-- Iter 724: General SQL splits as embedAB · embedBC. Useful for 3-XY
    chain decomposition (paper Lemma C.1 territory). Stepping stone
    toward future 3-real-embed canonical helpers. -/
theorem singleQubitLayer_eq_embedAB_mul_embedBC (uA uB uC : Mat2) :
    singleQubitLayer uA uB uC =
    embedAB (kron2 uA uB) * embedBC (kron2 I₂ uC) := by
  ext i j
  simp only [singleQubitLayer, kron3, decode3, embedAB, embedBC, kron2, I₂,
             Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply,
             Fin.sum_univ_eight]
  fin_cases i <;> fin_cases j <;>
  · simp

/-- Iter 725: Dual SQL splitting with uB on the BC side. Complements
    iter 724's lemma when 3-XY chain absorption needs uB folded into a
    BC-neighboring embed instead of an AB one. -/
theorem singleQubitLayer_eq_embedBC_mul_embedAB (uA uB uC : Mat2) :
    singleQubitLayer uA uB uC =
    embedBC (kron2 uB uC) * embedAB (kron2 uA I₂) := by
  ext i j
  simp only [singleQubitLayer, kron3, decode3, embedAB, embedBC, kron2, I₂,
             Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply,
             Fin.sum_univ_eight]
  fin_cases i <;> fin_cases j <;>
    (simp; ring)

/-- Iter 727: AC-side SQL decomposition. Since embedAC skips qubit B,
    the decomposition is 3-term: a B-only middle layer times an embedAC.
    Useful when 3-XY chain absorption needs an AC-flavored split. -/
theorem singleQubitLayer_eq_embedAC_mul_singleQubitLayer (uA uB uC : Mat2) :
    singleQubitLayer uA uB uC =
    singleQubitLayer I₂ uB I₂ * embedAC (kron2 uA uC) := by
  ext i j
  simp only [singleQubitLayer, kron3, decode3, embedAC, kron2, I₂,
             Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply,
             Fin.sum_univ_eight, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
  · simp <;> ring

/-! ## Right absorption: embedAB(V) * P(uA,uB,uC) = embedAB(V * kron2(uA,uB)) * P(I₂,I₂,uC)

The AB part of the product layer is absorbed into the AB gate from the right. -/

/-- Right absorption into AB embedding -/
theorem embedAB_mul_singleQubitLayer (V : Mat4) (uA uB uC : Mat2) :
    embedAB V * singleQubitLayer uA uB uC =
    embedAB (V * kron2 uA uB) * singleQubitLayer I₂ I₂ uC := by
  ext i j
  simp only [singleQubitLayer, kron3, embedAB, kron2, I₂, decode3,
             Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply,
             Fin.sum_univ_eight, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
  · simp <;> ring

/-- Right absorption into BC embedding -/
theorem embedBC_mul_singleQubitLayer (V : Mat4) (uA uB uC : Mat2) :
    embedBC V * singleQubitLayer uA uB uC =
    embedBC (V * kron2 uB uC) * singleQubitLayer uA I₂ I₂ := by
  ext i j
  simp only [singleQubitLayer, kron3, embedBC, kron2, I₂, decode3,
             Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply,
             Fin.sum_univ_eight, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
  · simp <;> ring

set_option maxHeartbeats 800000 in
-- Heartbeats raised: 8×8 matrix equality via `fin_cases × fin_cases` (64 leaves).
/-- Right absorption into AC embedding: the AC components of the product layer
    merge with the gate via kron2 (uA on first slot, uC on second slot). -/
theorem embedAC_mul_singleQubitLayer (V : Mat4) (uA uB uC : Mat2) :
    embedAC V * singleQubitLayer uA uB uC =
    embedAC (V * kron2 uA uC) * singleQubitLayer I₂ uB I₂ := by
  ext i j
  simp only [singleQubitLayer, kron3, embedAC, kron2, I₂, decode3,
             Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply,
             Fin.sum_univ_eight, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
  · simp <;> ring

set_option maxHeartbeats 800000 in
-- Heartbeats raised: 8×8 matrix equality via `fin_cases × fin_cases` (64 leaves).
/-- Left absorption into AC embedding (parallel to AB/BC versions). -/
theorem singleQubitLayer_mul_embedAC (uA uB uC : Mat2) (V : Mat4) :
    singleQubitLayer uA uB uC * embedAC V =
    singleQubitLayer I₂ uB I₂ * embedAC (kron2 uA uC * V) := by
  ext i j
  simp only [singleQubitLayer, kron3, embedAC, kron2, I₂, decode3,
             Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply,
             Fin.sum_univ_eight, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
  · simp <;> ring


/-! ## AC gate merging via SWAP conjugation -/

/-- Two adjacent AC gates with product layer merge into one AC gate.
    The AC embedding absorbs the A and C parts, leaving only the B part.
    Proved via SWAP conjugation of embedAB_merge. -/
private lemma swap_conj_distrib (A B : Mat8) :
    SWAP_BC * (A * B) * SWAP_BC =
    (SWAP_BC * A * SWAP_BC) * (SWAP_BC * B * SWAP_BC) := by
  symm
  calc (SWAP_BC * A * SWAP_BC) * (SWAP_BC * B * SWAP_BC)
      = SWAP_BC * (A * (SWAP_BC * (SWAP_BC * (B * SWAP_BC)))) := by simp only [mul_assoc]
    _ = SWAP_BC * (A * ((SWAP_BC * SWAP_BC) * (B * SWAP_BC))) := by
          congr 1; congr 1; exact (mul_assoc SWAP_BC SWAP_BC (B * SWAP_BC)).symm
    _ = SWAP_BC * (A * (B * SWAP_BC)) := by rw [SWAP_BC_sq, one_mul]
    _ = SWAP_BC * (A * B) * SWAP_BC := by simp only [mul_assoc]

theorem embedAC_merge (V₁ V₂ : Mat4) (uA uB uC : Mat2) :
    embedAC V₁ * singleQubitLayer uA uB uC * embedAC V₂ =
    singleQubitLayer I₂ uB I₂ * embedAC (V₁ * (kron2 uA uC * V₂)) := by
  calc embedAC V₁ * singleQubitLayer uA uB uC * embedAC V₂
      = (SWAP_BC * embedAB V₁ * SWAP_BC) * singleQubitLayer uA uB uC *
        (SWAP_BC * embedAB V₂ * SWAP_BC) := by
          rw [← swap_bc_embedAB, ← swap_bc_embedAB]
    _ = SWAP_BC * (embedAB V₁ * (SWAP_BC * singleQubitLayer uA uB uC * SWAP_BC) *
        embedAB V₂) * SWAP_BC := by
          simp only [mul_assoc]
    _ = SWAP_BC * (embedAB V₁ * singleQubitLayer uA uC uB * embedAB V₂) * SWAP_BC := by
          rw [swap_bc_singleQubitLayer]
    _ = SWAP_BC * (singleQubitLayer I₂ I₂ uB * embedAB (V₁ * (kron2 uA uC * V₂))) *
        SWAP_BC := by
          rw [embedAB_merge]
    _ = (SWAP_BC * singleQubitLayer I₂ I₂ uB * SWAP_BC) *
        (SWAP_BC * embedAB (V₁ * (kron2 uA uC * V₂)) * SWAP_BC) := by
          rw [swap_conj_distrib]
    _ = singleQubitLayer I₂ uB I₂ * embedAC (V₁ * (kron2 uA uC * V₂)) := by
          rw [swap_bc_singleQubitLayer, swap_bc_embedAB]

/-! ## SWAP_AC: swaps qubits A and C

Permutation on 3-qubit indices: (a,b,c) → (c,b,a), i.e., 4a+2b+c → 4c+2b+a.
Explicitly: 0→0, 1→4, 2→2, 3→6, 4→1, 5→5, 6→3, 7→7. -/

/-- The SWAP_AC permutation on indices: maps (a,b,c) to (c,b,a) -/
def swap_ac_perm : Fin 8 → Fin 8
  | 0 => 0  -- (0,0,0) → (0,0,0)
  | 1 => 4  -- (0,0,1) → (1,0,0)
  | 2 => 2  -- (0,1,0) → (0,1,0)
  | 3 => 6  -- (0,1,1) → (1,1,0)
  | 4 => 1  -- (1,0,0) → (0,0,1)
  | 5 => 5  -- (1,0,1) → (1,0,1)
  | 6 => 3  -- (1,1,0) → (0,1,1)
  | 7 => 7  -- (1,1,1) → (1,1,1)

/-- SWAP gate on qubits A,C: a permutation matrix -/
def SWAP_AC : Mat8 :=
  Matrix.of fun (i j : Fin 8) =>
    if swap_ac_perm i = j then 1 else 0

/-- SWAP_AC is an involution: SWAP_AC * SWAP_AC = I -/
theorem SWAP_AC_sq : SWAP_AC * SWAP_AC = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
  · simp [SWAP_AC, swap_ac_perm, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_eight]

/-- SWAP_AC conjugation converts AB embedding to BC embedding (with swapped gate) -/
theorem swap_ac_embedAB (V : Mat4) :
    SWAP_AC * embedAB V * SWAP_AC = embedBC (SWAP_4 * V * SWAP_4) := by
  ext i j
  unfold SWAP_AC swap_ac_perm embedAB embedBC SWAP_4 swap4_perm
  simp only [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_eight, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
  · simp

/-- SWAP_AC conjugation converts BC embedding to AB embedding (with swapped gate) -/
theorem swap_ac_embedBC (V : Mat4) :
    SWAP_AC * embedBC V * SWAP_AC = embedAB (SWAP_4 * V * SWAP_4) := by
  ext i j
  unfold SWAP_AC swap_ac_perm embedBC embedAB SWAP_4 swap4_perm
  simp only [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_eight, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
  · simp

/-- SWAP_AC conjugation swaps A and C in product layers -/
theorem swap_ac_singleQubitLayer (uA uB uC : Mat2) :
    SWAP_AC * singleQubitLayer uA uB uC * SWAP_AC = singleQubitLayer uC uB uA := by
  ext i j
  simp only [SWAP_AC, swap_ac_perm, singleQubitLayer, kron3, decode3,
             Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_eight]
  fin_cases i <;> fin_cases j <;>
    (simp; ring)

/-- SWAP_AC equals the AC embedding of the 2-qubit SWAP -/
theorem SWAP_AC_eq_embedAC : SWAP_AC = embedAC SWAP_4 := by
  ext i j
  unfold SWAP_AC swap_ac_perm embedAC SWAP_4 swap4_perm
  simp only [Matrix.of_apply]
  fin_cases i <;> fin_cases j <;> simp

/-- SWAP_AC conjugation preserves AC embedding (with swapped gate) -/
theorem swap_ac_embedAC (V : Mat4) :
    SWAP_AC * embedAC V * SWAP_AC = embedAC (SWAP_4 * V * SWAP_4) := by
  rw [SWAP_AC_eq_embedAC, embedAC_mul, embedAC_mul]

/-! ## SWAP_AB: swaps qubits A and B

Permutation on 3-qubit indices: (a,b,c) → (b,a,c), i.e., 4a+2b+c → 4b+2a+c.
Explicitly: 0→0, 1→1, 2→4, 3→5, 4→2, 5→3, 6→6, 7→7. -/

/-- The SWAP_AB permutation on indices: maps (a,b,c) to (b,a,c) -/
def swap_ab_perm : Fin 8 → Fin 8
  | 0 => 0  -- (0,0,0) → (0,0,0)
  | 1 => 1  -- (0,0,1) → (0,0,1)
  | 2 => 4  -- (0,1,0) → (1,0,0)
  | 3 => 5  -- (0,1,1) → (1,0,1)
  | 4 => 2  -- (1,0,0) → (0,1,0)
  | 5 => 3  -- (1,0,1) → (0,1,1)
  | 6 => 6  -- (1,1,0) → (1,1,0)
  | 7 => 7  -- (1,1,1) → (1,1,1)

/-- SWAP gate on qubits A,B: a permutation matrix -/
def SWAP_AB : Mat8 :=
  Matrix.of fun (i j : Fin 8) =>
    if swap_ab_perm i = j then 1 else 0

/-- **Iter 1035**: `SWAP_AB` is itself an AB-embedded gate — the missing third
    sibling of `SWAP_BC_eq_embedBC` and `SWAP_AC_eq_embedAC`.

    This is what makes SWAP conjugation FREE in gate count: conjugating a chain
    by `SWAP_AB` to convert a BC gate into an AC gate (`swap_ab_embedBC`) does
    not add gates, because each `SWAP_AB` is absorbed by a neighbouring AB
    factor. Needed for the pair-type rewriting that reduces arbitrary 4-gate
    chains to the 9 canonical patterns of
    `unitaryUnrestrictedCircuit_4_canonical_direct`. -/
theorem SWAP_AB_eq_embedAB : SWAP_AB = embedAB SWAP_4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SWAP_AB, embedAB, SWAP_4, swap_ab_perm, swap4_perm, Matrix.of_apply]

/-- SWAP_AB is an involution: SWAP_AB * SWAP_AB = I -/
theorem SWAP_AB_sq : SWAP_AB * SWAP_AB = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
  · simp [SWAP_AB, swap_ab_perm, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_eight]

set_option maxHeartbeats 800000 in
-- Heartbeats raised: 8×8 conjugation proof via `fin_cases × fin_cases` (64 leaves).
/-- SWAP_AB conjugation of AB embedding gives AB embedding with SWAP_4-conjugated gate -/
theorem swap_ab_embedAB (V : Mat4) :
    SWAP_AB * embedAB V * SWAP_AB = embedAB (SWAP_4 * V * SWAP_4) := by
  ext i j
  unfold SWAP_AB swap_ab_perm embedAB SWAP_4 swap4_perm
  simp only [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_eight, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
  · simp

set_option maxHeartbeats 800000 in
-- Heartbeats raised: 8×8 conjugation proof via `fin_cases × fin_cases` (64 leaves).
/-- SWAP_AB conjugation converts BC embedding to AC embedding -/
theorem swap_ab_embedBC (V : Mat4) :
    SWAP_AB * embedBC V * SWAP_AB = embedAC V := by
  ext i j
  unfold SWAP_AB swap_ab_perm embedBC embedAC
  simp only [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_eight]
  fin_cases i <;> fin_cases j <;>
  · simp

set_option maxHeartbeats 800000 in
-- Heartbeats raised: 8×8 conjugation proof via `fin_cases × fin_cases` (64 leaves).
/-- SWAP_AB conjugation converts AC embedding to BC embedding -/
theorem swap_ab_embedAC (V : Mat4) :
    SWAP_AB * embedAC V * SWAP_AB = embedBC V := by
  ext i j
  unfold SWAP_AB swap_ab_perm embedAC embedBC
  simp only [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_eight]
  fin_cases i <;> fin_cases j <;>
  · simp

set_option maxHeartbeats 800000 in
-- Heartbeats raised: 8×8 conjugation proof via `fin_cases × fin_cases` (64 leaves).
/-- SWAP_AB conjugation swaps A and B in product layers -/
theorem swap_ab_singleQubitLayer (uA uB uC : Mat2) :
    SWAP_AB * singleQubitLayer uA uB uC * SWAP_AB = singleQubitLayer uB uA uC := by
  ext i j
  simp only [SWAP_AB, swap_ab_perm, singleQubitLayer, kron3, decode3,
             Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_eight]
  fin_cases i <;> fin_cases j <;>
    (simp; try ring; try tauto)

/-! ## Linearity of embeddings

The embed functions are linear maps Mat4 → Mat8, which is needed
to decompose block-diagonal gates (IsBlockDiagFirst/IsBlockDiagSecond)
into sums of product-layer-like terms. -/

/-- embedAB is additive: embedAB(V + W) = embedAB(V) + embedAB(W) -/
theorem embedAB_add (V W : Mat4) : embedAB (V + W) = embedAB V + embedAB W := by
  ext i j
  simp only [embedAB, Matrix.of_apply, Matrix.add_apply]
  split <;> simp

/-- embedBC is additive: embedBC(V + W) = embedBC(V) + embedBC(W) -/
theorem embedBC_add (V W : Mat4) : embedBC (V + W) = embedBC V + embedBC W := by
  ext i j
  simp only [embedBC, Matrix.of_apply, Matrix.add_apply]
  split <;> simp

/-- embedAC is additive: embedAC(V + W) = embedAC(V) + embedAC(W) -/
theorem embedAC_add (V W : Mat4) : embedAC (V + W) = embedAC V + embedAC W := by
  ext i j
  simp only [embedAC, Matrix.of_apply, Matrix.add_apply]
  split <;> simp

/-- Block-diagonal gate decomposition: when V = kron2(proj0,P₀) + kron2(proj1,P₁),
    embedAB(V) = singleQubitLayer(proj0,P₀,I₂) + singleQubitLayer(proj1,P₁,I₂).
    This is the key decomposition for IsBlockDiagFirst gates. -/
theorem embedAB_blockDiagFirst (P₀ P₁ : Mat2) :
    embedAB (kron2 proj0 P₀ + kron2 proj1 P₁) =
    singleQubitLayer proj0 P₀ I₂ + singleQubitLayer proj1 P₁ I₂ := by
  rw [embedAB_add, singleQubitLayer_eq_embedAB_kron2, singleQubitLayer_eq_embedAB_kron2]

/-! ## singleQubitLayer identity

singleQubitLayer(I₂, I₂, I₂) = I₈: the all-identity product layer is the identity matrix. -/

/-- The all-identity product layer is the identity matrix -/
theorem singleQubitLayer_one : singleQubitLayer I₂ I₂ I₂ = (1 : Mat8) := by
  unfold singleQubitLayer I₂
  ext i j
  simp only [kron3, decode3, Matrix.of_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> simp

/-- A `singleQubitLayer` of unitary 1-qubit gates is itself unitary
    (in Mat8 sense): `(SQL u)† · SQL u = 1`. Combines
    `singleQubitLayer_conjTranspose`, `singleQubitLayer_mul`, and
    `singleQubitLayer_one`. -/
theorem singleQubitLayer_unitary (uA uB uC : Mat2)
    (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC) :
    (singleQubitLayer uA uB uC).conjTranspose * singleQubitLayer uA uB uC =
    (1 : Mat8) := by
  rw [singleQubitLayer_conjTranspose, singleQubitLayer_mul]
  rw [hA, hB, hC]
  exact singleQubitLayer_one

/-! ## Absorption chain for A.32 (PY24 V₃|00⟩=|00⟩ normalization)

After substituting `U₃ = kron2 Ra Rb · V · (kron2 1 Rψ)†`, expanding via
`embedAC_mul`, and converting `kron2`-embeds to `singleQubitLayer` via
`embedAC_kron2`, the chain
  `embedAC U₁ · embedBC U₂ · embedAC U₃ · embedBC U₄`
becomes
  `embedAC U₁ · embedBC U₂ · (sQL Ra I₂ Rb · embedAC V · sQL 1 I₂ Rψ.conjTranspose) · embedBC U₄`

This lemma absorbs the rotations into U₁, U₂, U₄. -/

theorem absorption_chain_AC_BC_AC_BC
    (U₁ U₂ U₄ V : Mat4) (Ra Rb Rψc : Mat2) :
    embedAC U₁ * embedBC U₂ *
    (singleQubitLayer Ra I₂ Rb * embedAC V * singleQubitLayer (1 : Mat2) I₂ Rψc) *
    embedBC U₄ =
    embedAC (U₁ * kron2 Ra I₂) * embedBC (U₂ * kron2 I₂ Rb) *
    embedAC V * embedBC (kron2 I₂ Rψc * U₄) := by
  have stepA : embedBC U₂ * singleQubitLayer Ra I₂ Rb =
               embedBC (U₂ * kron2 I₂ Rb) * singleQubitLayer Ra I₂ I₂ :=
    embedBC_mul_singleQubitLayer U₂ Ra I₂ Rb
  have stepB : singleQubitLayer (1 : Mat2) I₂ Rψc * embedBC U₄ =
               embedBC (kron2 I₂ Rψc * U₄) := by
    rw [singleQubitLayer_mul_embedBC]
    show singleQubitLayer (1 : Mat2) I₂ I₂ * embedBC (kron2 I₂ Rψc * U₄)
       = embedBC (kron2 I₂ Rψc * U₄)
    rw [show (singleQubitLayer (1 : Mat2) I₂ I₂ : Mat8) = 1 from singleQubitLayer_one,
        one_mul]
  have stepC : embedBC (U₂ * kron2 I₂ Rb) * singleQubitLayer Ra I₂ I₂ =
               singleQubitLayer Ra I₂ I₂ * embedBC (U₂ * kron2 I₂ Rb) :=
    embedBC_comm_singleQubitLayer_A (U₂ * kron2 I₂ Rb) Ra
  have stepD : embedAC U₁ * singleQubitLayer Ra I₂ I₂ = embedAC (U₁ * kron2 Ra I₂) := by
    rw [embedAC_mul_singleQubitLayer]
    show embedAC (U₁ * kron2 Ra I₂) * singleQubitLayer I₂ I₂ I₂ = embedAC (U₁ * kron2 Ra I₂)
    rw [singleQubitLayer_one, mul_one]
  calc embedAC U₁ * embedBC U₂ *
        (singleQubitLayer Ra I₂ Rb * embedAC V * singleQubitLayer (1 : Mat2) I₂ Rψc) *
        embedBC U₄
      = embedAC U₁ * (embedBC U₂ * singleQubitLayer Ra I₂ Rb) * embedAC V *
        (singleQubitLayer (1 : Mat2) I₂ Rψc * embedBC U₄) := by noncomm_ring
    _ = embedAC U₁ * (embedBC (U₂ * kron2 I₂ Rb) * singleQubitLayer Ra I₂ I₂) *
        embedAC V * embedBC (kron2 I₂ Rψc * U₄) := by rw [stepA, stepB]
    _ = embedAC U₁ * (singleQubitLayer Ra I₂ I₂ * embedBC (U₂ * kron2 I₂ Rb)) *
        embedAC V * embedBC (kron2 I₂ Rψc * U₄) := by rw [stepC]
    _ = (embedAC U₁ * singleQubitLayer Ra I₂ I₂) * embedBC (U₂ * kron2 I₂ Rb) *
        embedAC V * embedBC (kron2 I₂ Rψc * U₄) := by noncomm_ring
    _ = embedAC (U₁ * kron2 Ra I₂) * embedBC (U₂ * kron2 I₂ Rb) *
        embedAC V * embedBC (kron2 I₂ Rψc * U₄) := by rw [stepD]

/-! ## Injectivity of embeddings

The embeddings embedAB, embedBC are injective on 4×4 matrices: if embedAB V = embedAB W
then V = W. Proof: recover V's entry V[k,l] from embedAB(V)[2k, 2l] (i.e., reading
entries with the C-qubit fixed at 0). Useful for extracting equalities of 4×4 gates
from equalities of 8×8 embedded matrices. -/

/-- embedAB is injective: equal embeddings imply equal underlying gates. -/
theorem embedAB_injective : Function.Injective embedAB := by
  intro V W h
  ext k l
  have hentry := congrArg (fun M : Mat8 => M ⟨2 * k.val, by omega⟩ ⟨2 * l.val, by omega⟩) h
  simp only [embedAB, Matrix.of_apply,
             show (2 * k.val : ℕ) % 2 = (2 * l.val : ℕ) % 2 from by omega,
             if_true] at hentry
  have hk : (⟨(2 * k.val) / 2, by omega⟩ : Fin 4) = k := by
    apply Fin.ext; show (2 * k.val) / 2 = k.val; omega
  have hl : (⟨(2 * l.val) / 2, by omega⟩ : Fin 4) = l := by
    apply Fin.ext; show (2 * l.val) / 2 = l.val; omega
  rw [hk, hl] at hentry
  exact hentry

/-- embedBC is injective: equal embeddings imply equal underlying gates. -/
theorem embedBC_injective : Function.Injective embedBC := by
  intro V W h
  ext k l
  have hentry := congrArg (fun M : Mat8 => M ⟨k.val, by omega⟩ ⟨l.val, by omega⟩) h
  simp only [embedBC, Matrix.of_apply,
             show (k.val : ℕ) / 4 = (l.val : ℕ) / 4 from by omega,
             if_true] at hentry
  have hk : (⟨k.val % 4, by omega⟩ : Fin 4) = k := by
    apply Fin.ext; show k.val % 4 = k.val; omega
  have hl : (⟨l.val % 4, by omega⟩ : Fin 4) = l := by
    apply Fin.ext; show l.val % 4 = l.val; omega
  rw [hk, hl] at hentry
  exact hentry

/-- embedAC is injective: equal embeddings imply equal underlying gates.
    Recover V[k, l] from embedAC(V) at indices `4*(k/2) + k%2` (i.e., A-bit
    from k/2, B-bit fixed at 0, C-bit from k%2). -/
theorem embedAC_injective : Function.Injective embedAC := by
  intro V W h
  ext k l
  have hentry := congrArg (fun M : Mat8 =>
    M ⟨4 * (k.val / 2) + k.val % 2, by omega⟩
      ⟨4 * (l.val / 2) + l.val % 2, by omega⟩) h
  simp only [embedAC, Matrix.of_apply,
             show ((4 * (k.val / 2) + k.val % 2) / 2) % 2 =
                  ((4 * (l.val / 2) + l.val % 2) / 2) % 2 from by omega,
             if_true] at hentry
  have hk : (⟨2 * ((4 * (k.val / 2) + k.val % 2) / 4) +
              (4 * (k.val / 2) + k.val % 2) % 2, by omega⟩ : Fin 4) = k := by
    apply Fin.ext
    show 2 * ((4 * (k.val / 2) + k.val % 2) / 4) +
         (4 * (k.val / 2) + k.val % 2) % 2 = k.val
    omega
  have hl : (⟨2 * ((4 * (l.val / 2) + l.val % 2) / 4) +
              (4 * (l.val / 2) + l.val % 2) % 2, by omega⟩ : Fin 4) = l := by
    apply Fin.ext
    show 2 * ((4 * (l.val / 2) + l.val % 2) / 4) +
         (4 * (l.val / 2) + l.val % 2) % 2 = l.val
    omega
  rw [hk, hl] at hentry
  exact hentry

/-! ## Embedding preserves unitarity (forward and backward)

These bridge `IsUnitary4 V` with `(embedXY V)† · embedXY V = 1`, enabling
the chain-unitarity argument used in `unrestrictedCircuit_4_canonical`'s
proof: from a unitary 8×8 chain, extract unitary 4×4 components. -/

/-- Forward: V unitary ⇒ embedAB V unitary (in Mat8 sense). -/
theorem embedAB_unitary (V : Mat4) (hV : IsUnitary4 V) :
    (embedAB V).conjTranspose * embedAB V = (1 : Mat8) := by
  rw [embedAB_conjTranspose, embedAB_mul, hV]
  exact embedAB_one

/-- Backward: embedAB V unitary ⇒ V unitary. Uses `embedAB_injective`. -/
theorem isUnitary4_of_embedAB (V : Mat4)
    (h : (embedAB V).conjTranspose * embedAB V = (1 : Mat8)) : IsUnitary4 V := by
  rw [embedAB_conjTranspose, embedAB_mul] at h
  rw [show (1 : Mat8) = embedAB 1 from embedAB_one.symm] at h
  exact embedAB_injective h

/-- Forward: V unitary ⇒ embedBC V unitary. -/
theorem embedBC_unitary (V : Mat4) (hV : IsUnitary4 V) :
    (embedBC V).conjTranspose * embedBC V = (1 : Mat8) := by
  rw [embedBC_conjTranspose, embedBC_mul, hV]
  exact embedBC_one

/-- Backward: embedBC V unitary ⇒ V unitary. -/
theorem isUnitary4_of_embedBC (V : Mat4)
    (h : (embedBC V).conjTranspose * embedBC V = (1 : Mat8)) : IsUnitary4 V := by
  rw [embedBC_conjTranspose, embedBC_mul] at h
  rw [show (1 : Mat8) = embedBC 1 from embedBC_one.symm] at h
  exact embedBC_injective h

/-- Forward: V unitary ⇒ embedAC V unitary. -/
theorem embedAC_unitary (V : Mat4) (hV : IsUnitary4 V) :
    (embedAC V).conjTranspose * embedAC V = (1 : Mat8) := by
  rw [embedAC_conjTranspose, embedAC_mul, hV]
  exact embedAC_one

/-- Backward: embedAC V unitary ⇒ V unitary. Uses `embedAC_injective`. -/
theorem isUnitary4_of_embedAC (V : Mat4)
    (h : (embedAC V).conjTranspose * embedAC V = (1 : Mat8)) : IsUnitary4 V := by
  rw [embedAC_conjTranspose, embedAC_mul] at h
  rw [show (1 : Mat8) = embedAC 1 from embedAC_one.symm] at h
  exact embedAC_injective h

/-- Iter 712: bidirectional unitarity for embedAB. -/
theorem embedAB_unitary_iff (V : Mat4) :
    (embedAB V).conjTranspose * embedAB V = (1 : Mat8) ↔ IsUnitary4 V :=
  ⟨isUnitary4_of_embedAB V, embedAB_unitary V⟩

/-- Iter 712: bidirectional unitarity for embedBC. -/
theorem embedBC_unitary_iff (V : Mat4) :
    (embedBC V).conjTranspose * embedBC V = (1 : Mat8) ↔ IsUnitary4 V :=
  ⟨isUnitary4_of_embedBC V, embedBC_unitary V⟩

/-- Iter 712: bidirectional unitarity for embedAC. -/
theorem embedAC_unitary_iff (V : Mat4) :
    (embedAC V).conjTranspose * embedAC V = (1 : Mat8) ↔ IsUnitary4 V :=
  ⟨isUnitary4_of_embedAC V, embedAC_unitary V⟩

/-! ## Leading product absorption (P · AB → AB · P_C)

`singleQubitLayer uA uB uC * embedAB V` can be rewritten as `embedAB (kron2 uA uB * V) *
singleQubitLayer I₂ I₂ uC`: the AB-component of the product merges INTO the AB gate,
while the C-component slides PAST the AB gate to the right. This is the leading-product
analog of `embedAB_mul_singleQubitLayer` (which handles trailing products). -/

/-- Absorb a leading product layer into a following AB gate, leaving only a C-only
    product on the right. -/
theorem absorb_initial_product_AB (V : Mat4) (uA uB uC : Mat2) :
    singleQubitLayer uA uB uC * embedAB V =
    embedAB (kron2 uA uB * V) * singleQubitLayer I₂ I₂ uC := by
  rw [singleQubitLayer_mul_embedAB, ← embedAB_comm_singleQubitLayer_C]

/-- Absorb a leading product layer into a following BC gate, leaving only an A-only
    product on the right. -/
theorem absorb_initial_product_BC (V : Mat4) (uA uB uC : Mat2) :
    singleQubitLayer uA uB uC * embedBC V =
    embedBC (kron2 uB uC * V) * singleQubitLayer uA I₂ I₂ := by
  rw [singleQubitLayer_mul_embedBC, ← embedBC_comm_singleQubitLayer_A]

/-- Helper: combining a C-only layer with a general layer gives a layer with the
    C-component scaled. -/
private lemma singleQubitLayer_C_mul_general (uC₀ uA uB uC : Mat2) :
    singleQubitLayer I₂ I₂ uC₀ * singleQubitLayer uA uB uC =
    singleQubitLayer uA uB (uC₀ * uC) := by
  rw [singleQubitLayer_mul]
  unfold I₂
  rw [Matrix.one_mul, Matrix.one_mul]

/-- Helper: combining an A-only layer with a general layer gives a layer with the
    A-component scaled. -/
private lemma singleQubitLayer_A_mul_general (uA₀ uA uB uC : Mat2) :
    singleQubitLayer uA₀ I₂ I₂ * singleQubitLayer uA uB uC =
    singleQubitLayer (uA₀ * uA) uB uC := by
  rw [singleQubitLayer_mul]
  unfold I₂
  rw [Matrix.one_mul, Matrix.one_mul]

/-! ## Cross-type product absorption

These lemmas eliminate the product layer between two different-type gates,
absorbing it into the neighboring gates. This is the key step for converting
ABABA circuits with product layers into product-free form.

AB(V₁) * P(uA,uB,uC) * BC(V₂) = AB(V₁ * kron2(uA,uB)) * BC(kron2(I₂,uC) * V₂)
BC(V₁) * P(uA,uB,uC) * AB(V₂) = BC(V₁ * kron2(uB,uC)) * AB(kron2(uA,I₂) * V₂)

The AB part of the product merges left, the C part merges right (or vice versa). -/

/-- Absorb product layer between AB and BC gates.
    The AB components merge left, the C component merges right. -/
theorem ab_product_bc_absorb (V₁ V₂ : Mat4) (uA uB uC : Mat2) :
    embedAB V₁ * singleQubitLayer uA uB uC * embedBC V₂ =
    embedAB (V₁ * kron2 uA uB) * embedBC (kron2 I₂ uC * V₂) := by
  rw [embedAB_mul_singleQubitLayer, mul_assoc,
      singleQubitLayer_mul_embedBC, singleQubitLayer_one, one_mul]

/-- Absorb product layer between BC and AB gates.
    The BC components merge left, the A component merges right. -/
theorem bc_product_ab_absorb (V₁ V₂ : Mat4) (uA uB uC : Mat2) :
    embedBC V₁ * singleQubitLayer uA uB uC * embedAB V₂ =
    embedBC (V₁ * kron2 uB uC) * embedAB (kron2 uA I₂ * V₂) := by
  rw [embedBC_mul_singleQubitLayer, mul_assoc,
      singleQubitLayer_mul_embedAB, singleQubitLayer_one, one_mul]

/-! ## ABAB-prefix absorption: P · AB · P · BC pattern

Combines `absorb_initial_product_AB` (leading-product absorption) with
`ab_product_bc_absorb` (cross-type absorption) and the C-only product layer combine.
Eliminates the leading product P₀ AND the between-AB-and-BC product P₁,
producing a clean `AB · BC` form. -/

/-- Absorb the first three product layers of an ABABA chain (P₀, P₁ between AB and BC).
    Result: `AB(absorbed) · BC(absorbed)`. The C-components of P₀ and P₁ slide right
    and merge into the BC gate; the AB-components merge into the AB gate. -/
theorem absorb_initial_AB_product_BC
    (V₁ V₂ : Mat4) (uA₀ uB₀ uC₀ uA₁ uB₁ uC₁ : Mat2) :
    singleQubitLayer uA₀ uB₀ uC₀ * embedAB V₁ *
    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ =
    embedAB (kron2 uA₀ uB₀ * V₁ * kron2 uA₁ uB₁) *
    embedBC (kron2 I₂ (uC₀ * uC₁) * V₂) := by
  rw [absorb_initial_product_AB V₁ uA₀ uB₀ uC₀]
  rw [mul_assoc (embedAB _) (singleQubitLayer I₂ I₂ uC₀) _,
      singleQubitLayer_C_mul_general]
  rw [ab_product_bc_absorb]

/-- Middle BC-AB-BC chunk absorption: `BC(V₂)·P·AB(V₃)·P·BC(V₄)` collapses to
    `BC(absorbed) · AB(absorbed) · BC(absorbed)`. -/
theorem absorb_BC_product_AB_product_BC
    (V₂ V₃ V₄ : Mat4) (uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ : Mat2) :
    embedBC V₂ * singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
    singleQubitLayer uA₃ uB₃ uC₃ * embedBC V₄ =
    embedBC (V₂ * kron2 uB₂ uC₂) *
    embedAB (kron2 uA₂ I₂ * V₃ * kron2 uA₃ uB₃) *
    embedBC (kron2 I₂ uC₃ * V₄) := by
  rw [bc_product_ab_absorb]
  rw [mul_assoc (embedBC _) (embedAB _) (singleQubitLayer _ _ _)]
  rw [mul_assoc (embedBC _) _ (embedBC _)]
  rw [ab_product_bc_absorb]
  rw [← mul_assoc]

/-- End BC-AB chunk absorption: `BC(V₄)·P₄·AB(V₅)·P₅` collapses to
    `BC(absorbed) · AB(absorbed) · P_C(uC₅)`. -/
theorem absorb_BC_product_AB_product
    (V₄ V₅ : Mat4) (uA₄ uB₄ uC₄ uA₅ uB₅ uC₅ : Mat2) :
    embedBC V₄ * singleQubitLayer uA₄ uB₄ uC₄ * embedAB V₅ *
    singleQubitLayer uA₅ uB₅ uC₅ =
    embedBC (V₄ * kron2 uB₄ uC₄) *
    embedAB (kron2 uA₄ I₂ * V₅ * kron2 uA₅ uB₅) *
    singleQubitLayer I₂ I₂ uC₅ := by
  rw [bc_product_ab_absorb]
  rw [mul_assoc (embedBC _) (embedAB _) (singleQubitLayer _ _ _),
      embedAB_mul_singleQubitLayer, ← mul_assoc]

/-! ## Full ABABA absorption

The full 18-product-gate absorption: chains the three chunk lemmas via
associativity manipulations. -/

/-- **Full ABABA absorption**: a 5-gate ABABA circuit with 6 product layers
    (P₀ between empty-and-AB₁, ..., P₅ between AB₅-and-empty) collapses into
    a product-free 5-gate ABABA circuit followed by a C-only trailing product layer.
    All 18 single-qubit gates from the 6 product layers are absorbed into the
    5 two-qubit gates and the trailing C residual. -/
theorem ababa_absorb_product_layers
    (V₁ V₂ V₃ V₄ V₅ : Mat4)
    (uA₀ uB₀ uC₀ uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ : Mat2)
    (uA₄ uB₄ uC₄ uA₅ uB₅ uC₅ : Mat2) :
    singleQubitLayer uA₀ uB₀ uC₀ * embedAB V₁ *
    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
    singleQubitLayer uA₃ uB₃ uC₃ * embedBC V₄ *
    singleQubitLayer uA₄ uB₄ uC₄ * embedAB V₅ *
    singleQubitLayer uA₅ uB₅ uC₅ =
    embedAB (kron2 uA₀ uB₀ * V₁ * kron2 uA₁ uB₁) *
    embedBC (kron2 I₂ (uC₀ * uC₁) * V₂ * kron2 uB₂ uC₂) *
    embedAB (kron2 uA₂ I₂ * V₃ * kron2 uA₃ uB₃) *
    embedBC (kron2 I₂ uC₃ * V₄ * kron2 uB₄ uC₄) *
    embedAB (kron2 uA₄ I₂ * V₅ * kron2 uA₅ uB₅) *
    singleQubitLayer I₂ I₂ uC₅ := by
  calc singleQubitLayer uA₀ uB₀ uC₀ * embedAB V₁ *
       singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
       singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
       singleQubitLayer uA₃ uB₃ uC₃ * embedBC V₄ *
       singleQubitLayer uA₄ uB₄ uC₄ * embedAB V₅ *
       singleQubitLayer uA₅ uB₅ uC₅
      = (singleQubitLayer uA₀ uB₀ uC₀ * embedAB V₁ *
         singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂) *
        (singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
         singleQubitLayer uA₃ uB₃ uC₃ * embedBC V₄ *
         singleQubitLayer uA₄ uB₄ uC₄ * embedAB V₅ *
         singleQubitLayer uA₅ uB₅ uC₅) := by noncomm_ring
    _ = (embedAB (kron2 uA₀ uB₀ * V₁ * kron2 uA₁ uB₁) *
         embedBC (kron2 I₂ (uC₀ * uC₁) * V₂)) *
        (singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
         singleQubitLayer uA₃ uB₃ uC₃ * embedBC V₄ *
         singleQubitLayer uA₄ uB₄ uC₄ * embedAB V₅ *
         singleQubitLayer uA₅ uB₅ uC₅) := by
          rw [absorb_initial_AB_product_BC]
    _ = embedAB (kron2 uA₀ uB₀ * V₁ * kron2 uA₁ uB₁) *
        (embedBC (kron2 I₂ (uC₀ * uC₁) * V₂) *
         singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
         singleQubitLayer uA₃ uB₃ uC₃ * embedBC V₄) *
        (singleQubitLayer uA₄ uB₄ uC₄ * embedAB V₅ *
         singleQubitLayer uA₅ uB₅ uC₅) := by noncomm_ring
    _ = embedAB (kron2 uA₀ uB₀ * V₁ * kron2 uA₁ uB₁) *
        (embedBC (kron2 I₂ (uC₀ * uC₁) * V₂ * kron2 uB₂ uC₂) *
         embedAB (kron2 uA₂ I₂ * V₃ * kron2 uA₃ uB₃) *
         embedBC (kron2 I₂ uC₃ * V₄)) *
        (singleQubitLayer uA₄ uB₄ uC₄ * embedAB V₅ *
         singleQubitLayer uA₅ uB₅ uC₅) := by
          rw [absorb_BC_product_AB_product_BC]
    _ = (embedAB (kron2 uA₀ uB₀ * V₁ * kron2 uA₁ uB₁) *
         embedBC (kron2 I₂ (uC₀ * uC₁) * V₂ * kron2 uB₂ uC₂) *
         embedAB (kron2 uA₂ I₂ * V₃ * kron2 uA₃ uB₃)) *
        (embedBC (kron2 I₂ uC₃ * V₄) *
         singleQubitLayer uA₄ uB₄ uC₄ * embedAB V₅ *
         singleQubitLayer uA₅ uB₅ uC₅) := by noncomm_ring
    _ = (embedAB (kron2 uA₀ uB₀ * V₁ * kron2 uA₁ uB₁) *
         embedBC (kron2 I₂ (uC₀ * uC₁) * V₂ * kron2 uB₂ uC₂) *
         embedAB (kron2 uA₂ I₂ * V₃ * kron2 uA₃ uB₃)) *
        (embedBC (kron2 I₂ uC₃ * V₄ * kron2 uB₄ uC₄) *
         embedAB (kron2 uA₄ I₂ * V₅ * kron2 uA₅ uB₅) *
         singleQubitLayer I₂ I₂ uC₅) := by
          rw [absorb_BC_product_AB_product]
    _ = embedAB (kron2 uA₀ uB₀ * V₁ * kron2 uA₁ uB₁) *
        embedBC (kron2 I₂ (uC₀ * uC₁) * V₂ * kron2 uB₂ uC₂) *
        embedAB (kron2 uA₂ I₂ * V₃ * kron2 uA₃ uB₃) *
        embedBC (kron2 I₂ uC₃ * V₄ * kron2 uB₄ uC₄) *
        embedAB (kron2 uA₄ I₂ * V₅ * kron2 uA₅ uB₅) *
        singleQubitLayer I₂ I₂ uC₅ := by noncomm_ring

/-! ## A-qubit block decomposition of embedded gates

Since embedBC acts trivially on qubit A, embedBC(V) is block-diagonal in A
with both diagonal blocks equal to V. This is the foundational fact for
Lemmas A.13/A.14 (block-decomposition arguments in the paper). -/

/-- block00 of embedBC(V): the (A=0, A=0) block equals V itself. -/
theorem block00_embedBC (V : Mat4) :
    block00 (embedBC V) = V := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block00, embedBC, Matrix.of_apply]

/-- block11 of embedBC(V): the (A=1, A=1) block equals V itself. -/
theorem block11_embedBC (V : Mat4) :
    block11 (embedBC V) = V := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block11, embedBC, Matrix.of_apply]

/-- block01 of embedBC(V): the (A=0, A=1) off-diagonal block is zero. -/
theorem block01_embedBC (V : Mat4) :
    block01 (embedBC V) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block01, embedBC, Matrix.of_apply]

/-- block10 of embedBC(V): the (A=1, A=0) off-diagonal block is zero. -/
theorem block10_embedBC (V : Mat4) :
    block10 (embedBC V) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block10, embedBC, Matrix.of_apply]

/-! ## A-qubit block decomposition of embedAB

embedAB(V) acts as V on (A,B) with identity on C. So its A-block decomposition
along qubit A is determined by V's first-qubit block decomposition (`blockA_kk`),
tensored with I₂ on qubit C. -/

/-- block00 of embedAB(V) = (V's top-left A-block) ⊗ I₂ on C. -/
theorem block00_embedAB (V : Mat4) :
    block00 (embedAB V) = kron2 (blockA_00 V) I₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block00, embedAB, kron2, blockA_00, I₂, Matrix.of_apply, Matrix.one_apply]

/-- block11 of embedAB(V) = (V's bottom-right A-block) ⊗ I₂ on C. -/
theorem block11_embedAB (V : Mat4) :
    block11 (embedAB V) = kron2 (blockA_11 V) I₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block11, embedAB, kron2, blockA_11, I₂, Matrix.of_apply, Matrix.one_apply]

/-- block01 of embedAB(V) = (V's top-right A-block) ⊗ I₂ on C. -/
theorem block01_embedAB (V : Mat4) :
    block01 (embedAB V) = kron2 (blockA_01 V) I₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block01, embedAB, kron2, blockA_01, I₂, Matrix.of_apply, Matrix.one_apply]

/-- block10 of embedAB(V) = (V's bottom-left A-block) ⊗ I₂ on C. -/
theorem block10_embedAB (V : Mat4) :
    block10 (embedAB V) = kron2 (blockA_10 V) I₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block10, embedAB, kron2, blockA_10, I₂, Matrix.of_apply, Matrix.one_apply]

/-! ## A-qubit block decomposition of embedAC

embedAC(U) acts as U on (A,C) with identity on B. So its A-block decomposition
along qubit A puts I₂ on qubit B (outer) and U's first-qubit (A) sub-block on
qubit C (inner). -/

/-- block00 of embedAC(U) = I₂ on B ⊗ (U's top-left A-block) on C. -/
theorem block00_embedAC (U : Mat4) :
    block00 (embedAC U) = kron2 I₂ (blockA_00 U) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block00, embedAC, kron2, blockA_00, I₂, Matrix.of_apply, Matrix.one_apply]

/-- block11 of embedAC(U) = I₂ on B ⊗ (U's bottom-right A-block) on C. -/
theorem block11_embedAC (U : Mat4) :
    block11 (embedAC U) = kron2 I₂ (blockA_11 U) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block11, embedAC, kron2, blockA_11, I₂, Matrix.of_apply, Matrix.one_apply]

/-- block01 of embedAC(U) = I₂ on B ⊗ (U's top-right A-block) on C. -/
theorem block01_embedAC (U : Mat4) :
    block01 (embedAC U) = kron2 I₂ (blockA_01 U) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block01, embedAC, kron2, blockA_01, I₂, Matrix.of_apply, Matrix.one_apply]

/-- block10 of embedAC(U) = I₂ on B ⊗ (U's bottom-left A-block) on C. -/
theorem block10_embedAC (U : Mat4) :
    block10 (embedAC U) = kron2 I₂ (blockA_10 U) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block10, embedAC, kron2, blockA_10, I₂, Matrix.of_apply, Matrix.one_apply]

/-! ## A-block decomposition of the AC·AB product (paper's Lemma A.14 setup)

For 4×4 gates U, V, the matrix product `embedAC U * embedAB V` represents the
3-qubit gate "first apply embedAB(V), then embedAC(U)". Its A-block structure
is the structural backbone of paper's Lemma A.14 (page 19, Eq. 19-20). -/

/-- A-block (00) of the product `embedAC U * embedAB V`. The two terms come from
    the block-product formula: top-left = sum of (top-left)·(top-left) and
    (top-right)·(bottom-left). -/
theorem block00_embedAC_embedAB (U V : Mat4) :
    block00 (embedAC U * embedAB V) =
      kron2 (blockA_00 V) (blockA_00 U) + kron2 (blockA_10 V) (blockA_01 U) := by
  rw [block00_mul, block00_embedAC, block01_embedAC, block00_embedAB, block10_embedAB,
      kron2_mul, kron2_mul]
  simp [I₂]

/-- A-block (11) of the product `embedAC U * embedAB V`. -/
theorem block11_embedAC_embedAB (U V : Mat4) :
    block11 (embedAC U * embedAB V) =
      kron2 (blockA_01 V) (blockA_10 U) + kron2 (blockA_11 V) (blockA_11 U) := by
  rw [block11_mul, block10_embedAC, block11_embedAC, block01_embedAB, block11_embedAB,
      kron2_mul, kron2_mul]
  simp [I₂]

/-- A-block (01, off-diagonal) of the product `embedAC U * embedAB V`.
    The Lemma A.14 hypothesis "AC·AB product is block-diagonal in A" forces this = 0,
    yielding constraints on U's and V's first-qubit sub-blocks. -/
theorem block01_embedAC_embedAB (U V : Mat4) :
    block01 (embedAC U * embedAB V) =
      kron2 (blockA_01 V) (blockA_00 U) + kron2 (blockA_11 V) (blockA_01 U) := by
  rw [block01_mul, block00_embedAC, block01_embedAC, block01_embedAB, block11_embedAB,
      kron2_mul, kron2_mul]
  simp [I₂]

/-- A-block (10, off-diagonal) of the product `embedAC U * embedAB V`. -/
theorem block10_embedAC_embedAB (U V : Mat4) :
    block10 (embedAC U * embedAB V) =
      kron2 (blockA_00 V) (blockA_10 U) + kron2 (blockA_10 V) (blockA_11 U) := by
  rw [block10_mul, block10_embedAC, block11_embedAC, block00_embedAB, block10_embedAB,
      kron2_mul, kron2_mul]
  simp [I₂]

/-! ## A-block decomposition of `embedBC V * D * embedBC W`

When a Mat8 D is conjugated by embedBC factors on either side, each A-block of
the result is `V * (block_kk D) * W`. The off-diagonal A-block contributions
from D vanish naturally because embedBC has zero off-diagonal A-blocks
(Step 102). No hypothesis on D is needed — the embedBC structure does all the work.

This is the structural backbone of paper's Eq. 19 setup: for D diagonal,
combining with Step 110 (`isDiag8_block01/10`), the conjugated matrix
`embedBC V₁† · D · embedBC V₄†` is automatically block-diag in A. -/

/-- block00 of `embedBC V * D * embedBC W` = V · block00 D · W. -/
theorem block00_embedBC_mul_embedBC (V W : Mat4) (D : Mat8) :
    block00 (embedBC V * D * embedBC W) = V * block00 D * W := by
  rw [block00_mul, block00_embedBC, block10_embedBC, Matrix.mul_zero, add_zero,
      block00_mul, block00_embedBC, block01_embedBC, Matrix.zero_mul, add_zero]

/-- block11 of `embedBC V * D * embedBC W` = V · block11 D · W. -/
theorem block11_embedBC_mul_embedBC (V W : Mat4) (D : Mat8) :
    block11 (embedBC V * D * embedBC W) = V * block11 D * W := by
  rw [block11_mul, block01_embedBC, block11_embedBC, Matrix.mul_zero, zero_add,
      block11_mul, block10_embedBC, block11_embedBC, Matrix.zero_mul, zero_add]

/-- block01 of `embedBC V * D * embedBC W` = V · block01 D · W. -/
theorem block01_embedBC_mul_embedBC (V W : Mat4) (D : Mat8) :
    block01 (embedBC V * D * embedBC W) = V * block01 D * W := by
  rw [block01_mul, block01_embedBC, block11_embedBC, Matrix.mul_zero, zero_add,
      block01_mul, block00_embedBC, block01_embedBC, Matrix.zero_mul, add_zero]

/-- block10 of `embedBC V * D * embedBC W` = V · block10 D · W. -/
theorem block10_embedBC_mul_embedBC (V W : Mat4) (D : Mat8) :
    block10 (embedBC V * D * embedBC W) = V * block10 D * W := by
  rw [block10_mul, block00_embedBC, block10_embedBC, Matrix.mul_zero, add_zero,
      block10_mul, block10_embedBC, block11_embedBC, Matrix.zero_mul, zero_add]

/-- The product `embedAC U · embedAB V` is unitary as a Mat8 when U and V
    are unitary 4×4. Used in PY24 A.24 closure work. -/
theorem unitary_embedAC_mul_embedAB {U V : Mat4}
    (hU : U.conjTranspose * U = 1) (hV : V.conjTranspose * V = 1) :
    (embedAC U * embedAB V).conjTranspose * (embedAC U * embedAB V) = 1 := by
  rw [Matrix.conjTranspose_mul, embedAC_conjTranspose, embedAB_conjTranspose]
  rw [show (embedAB V.conjTranspose * embedAC U.conjTranspose) *
          (embedAC U * embedAB V) =
          embedAB V.conjTranspose *
            (embedAC U.conjTranspose * embedAC U) * embedAB V
          from by noncomm_ring,
      embedAC_mul, hU, embedAC_one, Matrix.mul_one,
      embedAB_mul, hV, embedAB_one]

end
