/-
  ApproxToffoli.HP.DiagBlocks

  `IsDiag8` and the A-block facts about diagonal 8×8 matrices.

  These were originally declared in `HP/FiveToFour.lean`. They live here so
  that `HP/Lemma44.lean` can depend on them WITHOUT depending on FiveToFour:
  that is what lets `FiveToFour.lean` import `Lemma44.lean` and use
  `paper_lemma_4_4` in the 5→4 reduction. (Measured iter 1041: Lemma44 used
  exactly these five declarations from FiveToFour, and nothing at all from
  SetChar.)
-/

import ApproxToffoli.HP.EmbedLemmas
import ApproxToffoli.BlockDecomp

open Matrix Complex

noncomputable section

/-- Predicate: U is a diagonal matrix with unit entries on the diagonal -/
def IsDiag8 (U : Mat8) : Prop :=
  ∃ D : DiagGate3, U = D.toMatrix

/-! ## A-block structure of diagonal matrices

A diagonal Mat8 is automatically block-diagonal in the A-qubit basis, since
all off-diagonal entries (in particular those crossing the A=0/A=1 split) are zero. -/

/-- A diagonal Mat8 has zero `block01` (top-right A-block). -/
theorem isDiag8_block01 (D : Mat8) (hD : IsDiag8 D) : block01 D = 0 := by
  obtain ⟨Dg, rfl⟩ := hD
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block01, DiagGate3.toMatrix, Matrix.of_apply, Matrix.diagonal_apply]

/-- A diagonal Mat8 has zero `block10` (bottom-left A-block). -/
theorem isDiag8_block10 (D : Mat8) (hD : IsDiag8 D) : block10 D = 0 := by
  obtain ⟨Dg, rfl⟩ := hD
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block10, DiagGate3.toMatrix, Matrix.of_apply, Matrix.diagonal_apply]

/-! ## Paper's Eq. 19: block-decomposition of `embedBC V · D · embedBC W` for diagonal D

For diagonal D : Mat8, the conjugated matrix is automatically block-diag in A
(off-diagonal A-blocks vanish), with diagonal blocks `V · block_kk D · W`. -/

/-- Off-diagonal A-block (01) of `embedBC V · D · embedBC W` vanishes when D is diagonal. -/
theorem isDiag8_block01_embedBC (V W : Mat4) (D : Mat8) (hD : IsDiag8 D) :
    block01 (embedBC V * D * embedBC W) = 0 := by
  rw [block01_embedBC_mul_embedBC, isDiag8_block01 D hD,
      Matrix.mul_zero, Matrix.zero_mul]

/-- Off-diagonal A-block (10) of `embedBC V · D · embedBC W` vanishes when D is diagonal. -/
theorem isDiag8_block10_embedBC (V W : Mat4) (D : Mat8) (hD : IsDiag8 D) :
    block10 (embedBC V * D * embedBC W) = 0 := by
  rw [block10_embedBC_mul_embedBC, isDiag8_block10 D hD,
      Matrix.mul_zero, Matrix.zero_mul]

end
