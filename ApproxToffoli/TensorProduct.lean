/-
  ApproxToffoli.TensorProduct
  Three-qubit tensor product infrastructure: encoding, decoding, kron3.
-/

import ApproxToffoli.Defs

open Matrix Complex

noncomputable section

/-! ## Three-qubit index encoding

We identify (Fin 2) × (Fin 2) × (Fin 2) with Fin 8
via the standard binary encoding: |abc⟩ ↦ |4a + 2b + c⟩.
-/

/-- Encode three binary indices into Fin 8 -/
def encode3 (a b c : Fin 2) : Fin 8 :=
  ⟨4 * a.val + 2 * b.val + c.val, by omega⟩

/-- Decode Fin 8 into three binary indices -/
def decode3 : Fin 8 → Fin 2 × Fin 2 × Fin 2
  | 0 => (0, 0, 0)
  | 1 => (0, 0, 1)
  | 2 => (0, 1, 0)
  | 3 => (0, 1, 1)
  | 4 => (1, 0, 0)
  | 5 => (1, 0, 1)
  | 6 => (1, 1, 0)
  | 7 => (1, 1, 1)

/-! ## Three-qubit tensor (Kronecker) product -/

/-- Tensor product of three 2×2 matrices, producing an 8×8 matrix.
    (A ⊗ B ⊗ C)_{(a₁b₁c₁),(a₂b₂c₂)} = A_{a₁a₂} · B_{b₁b₂} · C_{c₁c₂} -/
def kron3 (A B C : Mat2) : Mat8 :=
  Matrix.of fun i j =>
    let (a1, b1, c1) := decode3 i
    let (a2, b2, c2) := decode3 j
    A a1 a2 * B b1 b2 * C c1 c2

set_option maxHeartbeats 800000 in
-- Heartbeat bump: kron3 multiplication needs 64-case fin_cases × fin_cases
-- on Fin 8 × Fin 8 with Matrix.mul_apply expansion; exceeds default budget.
/-- Tensor product is multiplicative: (A⊗B⊗C)(D⊗E⊗F) = (AD)⊗(BE)⊗(CF) -/
lemma kron3_mul (A B C D E F : Mat2) :
    kron3 A B C * kron3 D E F = kron3 (A * D) (B * E) (C * F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [kron3, Matrix.of_apply, Matrix.mul_apply, decode3,
      Fin.sum_univ_eight, Fin.sum_univ_two, Fin.isValue] <;>
    ring

set_option maxHeartbeats 800000 in
-- conjTranspose distributes over kron3
/-- Conjugate transpose of a tensor product: (A⊗B⊗C)† = A†⊗B†⊗C† -/
lemma kron3_conjTranspose (A B C : Mat2) :
    (kron3 A B C).conjTranspose = kron3 A.conjTranspose B.conjTranspose C.conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [kron3, Matrix.of_apply, Matrix.conjTranspose_apply, decode3,
      Fin.isValue, star_mul']

end
