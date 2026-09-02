/-
  ApproxToffoli.PY24.Vectors
  Qubit vector infrastructure for formalizing Palsberg & Yu (2024).

  Defines:
  - 1-qubit, 2-qubit, 3-qubit vectors as functions Fin n → ℂ.
  - Computational basis |0⟩, |1⟩.
  - Matrix-vector action: Mat2 on Vec1, Mat4 on Vec2, Mat8 on Vec3.
  - Tensor product of vectors.
  - Inner product and norm.

  Reference: Palsberg & Yu (2024), "Optimal implementation of quantum gates
  with two controls", Linear Algebra and its Applications 694 (2024) 206-261.
-/

import ApproxToffoli.Defs
import ApproxToffoli.Kron2

open Matrix Complex

noncomputable section

/-! ## Qubit vector spaces -/

/-- A 1-qubit vector (state in ℂ²). Not necessarily unit-norm. -/
abbrev Vec1 := Fin 2 → ℂ

/-- A 2-qubit vector (state in ℂ⁴). -/
abbrev Vec2 := Fin 4 → ℂ

/-- A 3-qubit vector (state in ℂ⁸). -/
abbrev Vec3 := Fin 8 → ℂ

/-! ## Computational basis -/

/-- Computational basis state |0⟩ in Vec1: (1, 0). -/
def ket0_1 : Vec1 := fun i => if i.val = 0 then 1 else 0

/-- Computational basis state |1⟩ in Vec1: (0, 1). -/
def ket1_1 : Vec1 := fun i => if i.val = 1 then 1 else 0

/-! ## Matrix-vector action -/

/-- Action of a 2×2 matrix on a 1-qubit vector. -/
def Mat2.apply (M : Mat2) (v : Vec1) : Vec1 :=
  fun i => ∑ j : Fin 2, M i j * v j

/-- Action of a 4×4 matrix on a 2-qubit vector. -/
def Mat4.apply (M : Mat4) (v : Vec2) : Vec2 :=
  fun i => ∑ j : Fin 4, M i j * v j

/-- Action of an 8×8 matrix on a 3-qubit vector. -/
def Mat8.apply (M : Mat8) (v : Vec3) : Vec3 :=
  fun i => ∑ j : Fin 8, M i j * v j

/-! ## Tensor product of vectors -/

/-- Tensor product of two 1-qubit vectors: (|a⟩ ⊗ |b⟩)[2i+j] = a[i] · b[j]. -/
def tensor1_1 (a b : Vec1) : Vec2 :=
  fun k => a ⟨k.val / 2, by omega⟩ * b ⟨k.val % 2, by omega⟩

/-- Tensor product of a 1-qubit and a 2-qubit vector: 3-qubit result. -/
def tensor1_2 (a : Vec1) (b : Vec2) : Vec3 :=
  fun k => a ⟨k.val / 4, by omega⟩ * b ⟨k.val % 4, by omega⟩

/-- Tensor product of a 2-qubit and a 1-qubit vector: 3-qubit result. -/
def tensor2_1 (a : Vec2) (b : Vec1) : Vec3 :=
  fun k => a ⟨k.val / 2, by omega⟩ * b ⟨k.val % 2, by omega⟩

/-- **Tensor associativity in Vec3**: `a ⊗ (b ⊗ c) = (a ⊗ b) ⊗ c`. Both forms
    yield the same Vec3 with k-th entry `a[k/4]·b[(k/2)%2]·c[k%2]`. Used in
    A.24's Step 4 to bridge between input form `tensor1_2 ket0_1 (tensor1_1 ψ γ)`
    and the embedAB-friendly form `tensor2_1 (tensor1_1 ket0_1 ψ) γ`. -/
lemma tensor1_2_tensor1_1_eq_tensor2_1_tensor1_1 (a b c : Vec1) :
    tensor1_2 a (tensor1_1 b c) = tensor2_1 (tensor1_1 a b) c := by
  funext k
  fin_cases k <;>
    simp [tensor1_2, tensor1_1, tensor2_1, mul_assoc]

/-! ## Inner product and norm -/

/-- Hermitian inner product on Vec1: ⟨a|b⟩ = ∑ conj(a_i) · b_i. -/
def innerVec1 (a b : Vec1) : ℂ := ∑ i : Fin 2, starRingEnd ℂ (a i) * b i

/-- Hermitian inner product on Vec2: ⟨a|b⟩ = ∑ conj(a_i) · b_i. -/
def innerVec2 (a b : Vec2) : ℂ := ∑ i : Fin 4, starRingEnd ℂ (a i) * b i

/-- Squared norm of Vec1: ⟨a|a⟩. -/
def normSqVec1 (a : Vec1) : ℝ := ∑ i : Fin 2, Complex.normSq (a i)

/-- Squared norm of Vec2. -/
def normSqVec2 (a : Vec2) : ℝ := ∑ i : Fin 4, Complex.normSq (a i)

/-- A 1-qubit vector is a unit vector ("qubit") if its squared norm is 1. -/
def IsQubit1 (a : Vec1) : Prop := normSqVec1 a = 1

/-- A 2-qubit vector is a unit vector if its squared norm is 1. -/
def IsQubit2 (a : Vec2) : Prop := normSqVec2 a = 1

/-! ## Entangled vectors

A 2-qubit vector is entangled if it cannot be written as a tensor product
of two 1-qubit vectors. -/

/-- A 2-qubit vector is a tensor product of 1-qubit vectors. -/
def IsTensor (v : Vec2) : Prop := ∃ a b : Vec1, v = tensor1_1 a b

/-- A 2-qubit vector is entangled if it is NOT a tensor product. -/
def IsEntangled (v : Vec2) : Prop := ¬ IsTensor v

/-- A tensor product has zero "determinant": ϕ 0 · ϕ 3 = ϕ 1 · ϕ 2. -/
lemma isTensor_det_zero {ϕ : Vec2} (hT : IsTensor ϕ) :
    ϕ 0 * ϕ 3 = ϕ 1 * ϕ 2 := by
  obtain ⟨a, b, hϕ⟩ := hT
  rw [hϕ]
  show tensor1_1 a b 0 * tensor1_1 a b 3 = tensor1_1 a b 1 * tensor1_1 a b 2
  simp [tensor1_1]
  ring

/-- Contrapositive: nonzero "determinant" ⟹ entangled. -/
lemma isEntangled_of_det_ne_zero {ϕ : Vec2}
    (h : ϕ 0 * ϕ 3 ≠ ϕ 1 * ϕ 2) : IsEntangled ϕ := by
  intro hT
  exact h (isTensor_det_zero hT)

/-- Converse: zero "determinant" ⟹ tensor product (constructive). -/
lemma det_zero_implies_isTensor {ϕ : Vec2}
    (h : ϕ 0 * ϕ 3 = ϕ 1 * ϕ 2) : IsTensor ϕ := by
  by_cases h0 : ϕ 0 = 0
  · rw [h0, zero_mul] at h
    rcases (mul_eq_zero.mp h.symm) with h1 | h2
    · -- ϕ 0 = 0, ϕ 1 = 0 (top row zero). Take a = (0, 1), b = (ϕ 2, ϕ 3).
      refine ⟨![0, 1], ![ϕ 2, ϕ 3], ?_⟩
      funext k
      fin_cases k <;> simp [tensor1_1, h0, h1]
    · -- ϕ 0 = 0, ϕ 2 = 0 (left column zero).
      by_cases h1' : ϕ 1 = 0
      · -- ϕ 1 = 0 too. Take a = (0, 1), b = (0, ϕ 3).
        refine ⟨![0, 1], ![0, ϕ 3], ?_⟩
        funext k
        fin_cases k <;> simp [tensor1_1, h0, h1', h2]
      · -- ϕ 1 ≠ 0. Take a = (1, ϕ 3 / ϕ 1), b = (0, ϕ 1).
        refine ⟨![1, ϕ 3 / ϕ 1], ![0, ϕ 1], ?_⟩
        funext k
        fin_cases k <;> simp [tensor1_1, h0, h2]
        field_simp
  · -- ϕ 0 ≠ 0. Take a = (1, ϕ 2 / ϕ 0), b = (ϕ 0, ϕ 1).
    refine ⟨![1, ϕ 2 / ϕ 0], ![ϕ 0, ϕ 1], ?_⟩
    funext k
    fin_cases k
    · simp [tensor1_1]
    · simp [tensor1_1]
    · simp [tensor1_1]
      field_simp
    · simp [tensor1_1]
      field_simp
      linear_combination h

/-- Full characterization: ϕ is a tensor iff its "determinant" vanishes. -/
lemma isTensor_iff_det_zero (ϕ : Vec2) :
    IsTensor ϕ ↔ ϕ 0 * ϕ 3 = ϕ 1 * ϕ 2 :=
  ⟨isTensor_det_zero, det_zero_implies_isTensor⟩

/-- A Mat2 is zero iff all four entries are zero. -/
lemma mat2_eq_zero_iff (X : Mat2) :
    X = 0 ↔ X 0 0 = 0 ∧ X 0 1 = 0 ∧ X 1 0 = 0 ∧ X 1 1 = 0 := by
  refine ⟨fun h => ?_, fun ⟨h00, h01, h10, h11⟩ => ?_⟩
  · rw [h]; exact ⟨rfl, rfl, rfl, rfl⟩
  · ext i j; fin_cases i <;> fin_cases j <;> assumption

/-- Entrywise extraction: if `(kron2 1 X) · ϕ = 0`, then 4 entrywise products vanish.
    These are precisely the equations `X 0 0 ϕ_b + X 0 1 ϕ_b' = 0` and the
    `X 1 _` row, repeated for both top (b ∈ {0,1}) and bottom (b ∈ {2,3}) halves. -/
lemma kron2_one_apply_zero_entries {X : Mat2} {ϕ : Vec2}
    (h : Mat4.apply (kron2 1 X) ϕ = 0) :
    X 0 0 * ϕ 0 + X 0 1 * ϕ 1 = 0 ∧
    X 1 0 * ϕ 0 + X 1 1 * ϕ 1 = 0 ∧
    X 0 0 * ϕ 2 + X 0 1 * ϕ 3 = 0 ∧
    X 1 0 * ϕ 2 + X 1 1 * ϕ 3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := congr_fun h (0 : Fin 4)
    simpa [Mat4.apply, kron2, Matrix.of_apply, Matrix.one_apply, Fin.sum_univ_four]
      using this
  · have := congr_fun h (1 : Fin 4)
    simpa [Mat4.apply, kron2, Matrix.of_apply, Matrix.one_apply, Fin.sum_univ_four]
      using this
  · have := congr_fun h (2 : Fin 4)
    simpa [Mat4.apply, kron2, Matrix.of_apply, Matrix.one_apply, Fin.sum_univ_four]
      using this
  · have := congr_fun h (3 : Fin 4)
    simpa [Mat4.apply, kron2, Matrix.of_apply, Matrix.one_apply, Fin.sum_univ_four]
      using this

/-- A 2×2 matrix whose kernel contains two linearly independent vectors is zero. -/
lemma mat2_eq_zero_of_two_kernel
    (X : Mat2) (v w : Vec1)
    (h_indep : v 0 * w 1 ≠ v 1 * w 0)
    (hXv : Mat2.apply X v = 0)
    (hXw : Mat2.apply X w = 0) :
    X = 0 := by
  -- Extract 4 entrywise equations.
  have h00v : X 0 0 * v 0 + X 0 1 * v 1 = 0 := by
    have := congr_fun hXv 0
    simpa [Mat2.apply, Fin.sum_univ_two] using this
  have h10v : X 1 0 * v 0 + X 1 1 * v 1 = 0 := by
    have := congr_fun hXv 1
    simpa [Mat2.apply, Fin.sum_univ_two] using this
  have h00w : X 0 0 * w 0 + X 0 1 * w 1 = 0 := by
    have := congr_fun hXw 0
    simpa [Mat2.apply, Fin.sum_univ_two] using this
  have h10w : X 1 0 * w 0 + X 1 1 * w 1 = 0 := by
    have := congr_fun hXw 1
    simpa [Mat2.apply, Fin.sum_univ_two] using this
  have hdet : v 0 * w 1 - v 1 * w 0 ≠ 0 := sub_ne_zero.mpr h_indep
  -- Each X i j satisfies X i j · det = 0; det ≠ 0 implies X i j = 0.
  rw [mat2_eq_zero_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- X 0 0 = 0: combine h00v · w 1 - h00w · v 1.
    have key : X 0 0 * (v 0 * w 1 - v 1 * w 0) = 0 := by
      linear_combination w 1 * h00v - v 1 * h00w
    exact (mul_eq_zero.mp key).resolve_right hdet
  · -- X 0 1 = 0: combine h00w · v 0 - h00v · w 0.
    have key : X 0 1 * (v 0 * w 1 - v 1 * w 0) = 0 := by
      linear_combination v 0 * h00w - w 0 * h00v
    exact (mul_eq_zero.mp key).resolve_right hdet
  · -- X 1 0 = 0: combine h10v · w 1 - h10w · v 1.
    have key : X 1 0 * (v 0 * w 1 - v 1 * w 0) = 0 := by
      linear_combination w 1 * h10v - v 1 * h10w
    exact (mul_eq_zero.mp key).resolve_right hdet
  · -- X 1 1 = 0: combine h10w · v 0 - h10v · w 0.
    have key : X 1 1 * (v 0 * w 1 - v 1 * w 0) = 0 := by
      linear_combination v 0 * h10w - w 0 * h10v
    exact (mul_eq_zero.mp key).resolve_right hdet

/-- **A.17 helper**: two orthogonal Vec1 qubits are linearly independent.
    Concretely: ‖α‖ = ‖β‖ = 1 and ⟨α, β⟩ = 0 imply `α 0 · β 1 ≠ α 1 · β 0`
    (i.e., the 2×2 determinant of `(α; β)` is nonzero).
    Proof via the Lagrange/Gram identity:
    `(|a|² + |b|²)(|c|² + |d|²) = |ad - bc|² + |⟨α, β⟩|²`. -/
lemma orthogonal_qubits_indep {α β : Vec1}
    (hα : IsQubit1 α) (hβ : IsQubit1 β) (h_orth : innerVec1 α β = 0) :
    α 0 * β 1 ≠ α 1 * β 0 := by
  intro h_eq
  unfold IsQubit1 normSqVec1 at hα hβ
  unfold innerVec1 at h_orth
  rw [Fin.sum_univ_two] at hα hβ h_orth
  -- Promote norm equations to ℂ.
  have hα_ℂ : (Complex.normSq (α 0) : ℂ) + (Complex.normSq (α 1) : ℂ) = 1 := by
    exact_mod_cast hα
  have hβ_ℂ : (Complex.normSq (β 0) : ℂ) + (Complex.normSq (β 1) : ℂ) = 1 := by
    exact_mod_cast hβ
  -- z * conj(z) = (Complex.normSq z : ℂ).
  have ea0 : α 0 * starRingEnd ℂ (α 0) = (Complex.normSq (α 0) : ℂ) :=
    Complex.mul_conj _
  have ea1 : α 1 * starRingEnd ℂ (α 1) = (Complex.normSq (α 1) : ℂ) :=
    Complex.mul_conj _
  have eb0 : β 0 * starRingEnd ℂ (β 0) = (Complex.normSq (β 0) : ℂ) :=
    Complex.mul_conj _
  have eb1 : β 1 * starRingEnd ℂ (β 1) = (Complex.normSq (β 1) : ℂ) :=
    Complex.mul_conj _
  -- Lagrange/Gram identity (purely algebraic in ℂ; conjugates treated as
  -- independent atoms by ring).
  have lagrange :
      (α 0 * starRingEnd ℂ (α 0) + α 1 * starRingEnd ℂ (α 1)) *
      (β 0 * starRingEnd ℂ (β 0) + β 1 * starRingEnd ℂ (β 1)) =
      (α 0 * β 1 - α 1 * β 0) *
        (starRingEnd ℂ (α 0) * starRingEnd ℂ (β 1)
          - starRingEnd ℂ (α 1) * starRingEnd ℂ (β 0)) +
      (starRingEnd ℂ (α 0) * β 0 + starRingEnd ℂ (α 1) * β 1) *
        (α 0 * starRingEnd ℂ (β 0) + α 1 * starRingEnd ℂ (β 1)) := by ring
  rw [ea0, ea1, eb0, eb1, hα_ℂ, hβ_ℂ] at lagrange
  -- lagrange : 1 * 1 = (α 0·β 1 - α 1·β 0) * (...) + (innerVec1 α β factor) * (...)
  have h_diff_zero : α 0 * β 1 - α 1 * β 0 = 0 := by linear_combination h_eq
  rw [h_diff_zero, zero_mul, zero_add, h_orth, zero_mul] at lagrange
  -- lagrange : 1 * 1 = 0 → 1 = 0, contradiction.
  exact one_ne_zero (by linear_combination lagrange : (1 : ℂ) = 0)

/-- **A.24/A.30 helper**: orthogonal complement of a Vec1 unit qubit.
    `qubit_perp (a, b) = (-conj(b), conj(a))`. Used to construct unitary
    matrices with a prescribed first column via `matrixOfColumns α (qubit_perp α)`. -/
noncomputable def qubit_perp (α : Vec1) : Vec1 :=
  ![-starRingEnd ℂ (α 1), starRingEnd ℂ (α 0)]

/-- `qubit_perp` of a unit qubit is also a unit qubit. -/
lemma isQubit1_qubit_perp {α : Vec1} (hα : IsQubit1 α) :
    IsQubit1 (qubit_perp α) := by
  unfold IsQubit1 normSqVec1 at hα ⊢
  rw [Fin.sum_univ_two] at hα ⊢
  -- (qubit_perp α) 0 = -conj(α 1); (qubit_perp α) 1 = conj(α 0).
  simp only [qubit_perp, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Complex.normSq_neg, Complex.normSq_conj]
  -- |α 1|² + |α 0|² = |α 0|² + |α 1|² = 1.
  linarith [hα]

/-- A unit qubit is orthogonal to its `qubit_perp`. -/
lemma innerVec1_qubit_perp (α : Vec1) :
    innerVec1 α (qubit_perp α) = 0 := by
  unfold innerVec1 qubit_perp
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  -- conj(α 0) * (-conj(α 1)) + conj(α 1) * conj(α 0) = 0.
  ring

/-! ## A.30/A.24 helper: 2×2 matrix with prescribed columns

Note: `matrixOfColumns` and its lemmas were moved here from PY24/Lemmas.lean
to make them available to py24_lemma_A_24 via Vectors.lean. -/

/-- The 2×2 matrix with columns z₀, z₁. Used in A.30's T construction and
    in A.24's "unitary with prescribed first column" construction. -/
noncomputable def matrixOfColumns (z₀ z₁ : Vec1) : Mat2 :=
  Matrix.of ![![z₀ 0, z₁ 0], ![z₀ 1, z₁ 1]]

lemma matrixOfColumns_apply_ket0 (z₀ z₁ : Vec1) :
    Mat2.apply (matrixOfColumns z₀ z₁) ket0_1 = z₀ := by
  funext i
  fin_cases i <;>
    simp [Mat2.apply, matrixOfColumns, ket0_1, Fin.sum_univ_two,
          Matrix.of_apply]

lemma matrixOfColumns_apply_ket1 (z₀ z₁ : Vec1) :
    Mat2.apply (matrixOfColumns z₀ z₁) ket1_1 = z₁ := by
  funext i
  fin_cases i <;>
    simp [Mat2.apply, matrixOfColumns, ket1_1, Fin.sum_univ_two,
          Matrix.of_apply]

/-- For any x : Vec1, `T·x = x 0 • z₀ + x 1 • z₁` where T = matrixOfColumns z₀ z₁. -/
lemma matrixOfColumns_apply (z₀ z₁ x : Vec1) :
    Mat2.apply (matrixOfColumns z₀ z₁) x = x 0 • z₀ + x 1 • z₁ := by
  funext i
  fin_cases i <;>
    (simp [Mat2.apply, matrixOfColumns, Fin.sum_univ_two,
           Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring)

/-- **A.30 helper**: the matrix `matrixOfColumns z₀ z₁` is unitary if z₀, z₁ are
    orthonormal in Vec1 (i.e., ‖z₀‖ = ‖z₁‖ = 1, ⟨z₀, z₁⟩ = 0). -/
lemma matrixOfColumns_unitary {z₀ z₁ : Vec1}
    (h00 : normSqVec1 z₀ = 1) (h11 : normSqVec1 z₁ = 1)
    (h01 : innerVec1 z₀ z₁ = 0) :
    IsUnitary2 (matrixOfColumns z₀ z₁) := by
  unfold IsUnitary2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixOfColumns, Matrix.conjTranspose_apply, Matrix.mul_apply,
          Matrix.of_apply, Matrix.one_apply, Fin.sum_univ_two, Fin.isValue,
          Fin.cons_zero, Fin.cons_one]
  all_goals
    first
    | (-- (0,0): conj(z₀ 0)·z₀ 0 + conj(z₀ 1)·z₀ 1 = 1
       have : Complex.normSq (z₀ 0) + Complex.normSq (z₀ 1) = 1 := by
         have := h00; unfold normSqVec1 at this
         rw [Fin.sum_univ_two] at this; exact this
       have e0 : starRingEnd ℂ (z₀ 0) * z₀ 0 = (Complex.normSq (z₀ 0) : ℂ) := by
         rw [mul_comm]; exact Complex.mul_conj _
       have e1 : starRingEnd ℂ (z₀ 1) * z₀ 1 = (Complex.normSq (z₀ 1) : ℂ) := by
         rw [mul_comm]; exact Complex.mul_conj _
       have hC : (Complex.normSq (z₀ 0) : ℂ) + (Complex.normSq (z₀ 1) : ℂ) = 1 := by
         exact_mod_cast this
       linear_combination e0 + e1 + hC)
    | (have : Complex.normSq (z₁ 0) + Complex.normSq (z₁ 1) = 1 := by
         have := h11; unfold normSqVec1 at this
         rw [Fin.sum_univ_two] at this; exact this
       have e0 : starRingEnd ℂ (z₁ 0) * z₁ 0 = (Complex.normSq (z₁ 0) : ℂ) := by
         rw [mul_comm]; exact Complex.mul_conj _
       have e1 : starRingEnd ℂ (z₁ 1) * z₁ 1 = (Complex.normSq (z₁ 1) : ℂ) := by
         rw [mul_comm]; exact Complex.mul_conj _
       have hC : (Complex.normSq (z₁ 0) : ℂ) + (Complex.normSq (z₁ 1) : ℂ) = 1 := by
         exact_mod_cast this
       linear_combination e0 + e1 + hC)
    | (have hI : starRingEnd ℂ (z₀ 0) * z₁ 0 + starRingEnd ℂ (z₀ 1) * z₁ 1 = 0 := by
         have := h01; unfold innerVec1 at this
         rw [Fin.sum_univ_two] at this; exact this
       linear_combination hI)
    | (have h := h01
       unfold innerVec1 at h
       rw [Fin.sum_univ_two] at h
       have hconj := congrArg (starRingEnd ℂ) h
       simp [map_add, map_mul, Complex.conj_conj, map_zero] at hconj
       -- hconj : z₀ 0 * conj(z₁ 0) + z₀ 1 * conj(z₁ 1) = 0
       linear_combination hconj)

/-! ## A.24 helper: unitary with prescribed first column -/

/-- "Unitary with prescribed first column": for a unit qubit α, the matrix
    `matrixOfColumns α (qubit_perp α)` is unitary with first column α.
    Used in A.24's P construction to map α to ket0_1 via dagger. -/
noncomputable def unitary_first_column (α : Vec1) : Mat2 :=
  matrixOfColumns α (qubit_perp α)

lemma unitary_first_column_isUnitary {α : Vec1} (hα : IsQubit1 α) :
    IsUnitary2 (unitary_first_column α) :=
  matrixOfColumns_unitary hα (isQubit1_qubit_perp hα) (innerVec1_qubit_perp α)

lemma unitary_first_column_apply_ket0 (α : Vec1) :
    Mat2.apply (unitary_first_column α) ket0_1 = α :=
  matrixOfColumns_apply_ket0 _ _

/-- The dagger of `unitary_first_column α` maps α back to ket0_1.
    Direct component computation: P† has rows (conj(α 0), conj(α 1)) and
    (-α 1, α 0); applied to α gives (|α 0|² + |α 1|², 0) = (1, 0). -/
lemma unitary_first_column_dagger_apply {α : Vec1} (hα : IsQubit1 α) :
    Mat2.apply (unitary_first_column α).conjTranspose α = ket0_1 := by
  unfold IsQubit1 normSqVec1 at hα
  rw [Fin.sum_univ_two] at hα
  have hα_ℂ : (Complex.normSq (α 0) : ℂ) + (Complex.normSq (α 1) : ℂ) = 1 := by
    exact_mod_cast hα
  funext i
  fin_cases i
  · -- (P†·α) 0 = conj(α 0)·α 0 + conj(α 1)·α 1 = 1.
    simp [Mat2.apply, unitary_first_column, matrixOfColumns, qubit_perp,
          Matrix.conjTranspose_apply, Matrix.of_apply, ket0_1,
          Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
    have e0 : starRingEnd ℂ (α 0) * α 0 = (Complex.normSq (α 0) : ℂ) := by
      rw [mul_comm]; exact Complex.mul_conj _
    have e1 : starRingEnd ℂ (α 1) * α 1 = (Complex.normSq (α 1) : ℂ) := by
      rw [mul_comm]; exact Complex.mul_conj _
    linear_combination e0 + e1 + hα_ℂ
  · -- (P†·α) 1 = -α 1·α 0 + α 0·α 1 = 0.
    simp [Mat2.apply, unitary_first_column, matrixOfColumns, qubit_perp,
          Matrix.conjTranspose_apply, Matrix.of_apply, ket0_1,
          Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
    ring

set_option maxHeartbeats 800000 in
/-- Bridge: applying M : Mat8 to `tensor1_2 ket0 ϕ` and projecting to the
    upper half (a' = 1) gives `block10 M · ϕ` (since the Fin 8 sum reduces
    to the Fin 4 sum over the lower half of v). -/
lemma Mat8.apply_tensor1_2_ket0_upper (M : Mat8) (ϕ : Vec2) (i : Fin 4) :
    Mat8.apply M (tensor1_2 ket0_1 ϕ) ⟨i.val + 4, by omega⟩
      = Mat4.apply (block10 M) ϕ i := by
  show ∑ j : Fin 8, M ⟨i.val + 4, by omega⟩ j * tensor1_2 ket0_1 ϕ j
       = ∑ j : Fin 4, block10 M i j * ϕ j
  rw [Fin.sum_univ_eight, Fin.sum_univ_four]
  simp [tensor1_2, ket0_1, block10, Matrix.of_apply]

set_option maxHeartbeats 800000 in
/-- Bridge: applying M : Mat8 to `tensor1_2 ket0 ϕ` and projecting to the
    lower half (a' = 0) gives `block00 M · ϕ`. Symmetric to
    `Mat8.apply_tensor1_2_ket0_upper`. -/
lemma Mat8.apply_tensor1_2_ket0_lower (M : Mat8) (ϕ : Vec2) (i : Fin 4) :
    Mat8.apply M (tensor1_2 ket0_1 ϕ) ⟨i.val, by omega⟩
      = Mat4.apply (block00 M) ϕ i := by
  show ∑ j : Fin 8, M ⟨i.val, by omega⟩ j * tensor1_2 ket0_1 ϕ j
       = ∑ j : Fin 4, block00 M i j * ϕ j
  rw [Fin.sum_univ_eight, Fin.sum_univ_four]
  simp [tensor1_2, ket0_1, block00, Matrix.of_apply]

set_option maxHeartbeats 800000 in
/-- Bridge: applying M : Mat8 to `tensor1_2 ket1 ϕ` (concentrated in upper half)
    and projecting to the upper half (a' = 1) gives `block11 M · ϕ`. -/
lemma Mat8.apply_tensor1_2_ket1_upper (M : Mat8) (ϕ : Vec2) (i : Fin 4) :
    Mat8.apply M (tensor1_2 ket1_1 ϕ) ⟨i.val + 4, by omega⟩
      = Mat4.apply (block11 M) ϕ i := by
  show ∑ j : Fin 8, M ⟨i.val + 4, by omega⟩ j * tensor1_2 ket1_1 ϕ j
       = ∑ j : Fin 4, block11 M i j * ϕ j
  rw [Fin.sum_univ_eight, Fin.sum_univ_four]
  simp [tensor1_2, ket1_1, block11, Matrix.of_apply]

set_option maxHeartbeats 800000 in
/-- **A.24 Step 4 helper**: when M : Mat8 is block-diagonal in qubit A (i.e.,
    `block10 M = 0`), applying M to `tensor1_2 ket0_1 ϕ` gives
    `tensor1_2 ket0_1 (block00 M · ϕ)`. The lower half is direct; the upper
    half vanishes by `block10 M = 0`. -/
lemma Mat8.apply_block_diag_A_tensor1_2_ket0
    {M : Mat8} (h10 : block10 M = 0) (ϕ : Vec2) :
    Mat8.apply M (tensor1_2 ket0_1 ϕ) =
    tensor1_2 ket0_1 (Mat4.apply (block00 M) ϕ) := by
  funext k
  rcases Nat.lt_or_ge k.val 4 with hk | hk
  · -- Lower half: k.val < 4.
    have h_eq : k = (⟨k.val, by omega⟩ : Fin 8) := Fin.ext rfl
    rw [h_eq, Mat8.apply_tensor1_2_ket0_lower M ϕ ⟨k.val, hk⟩]
    -- Goal: block00 M · ϕ at i = tensor1_2 ket0_1 (block00 M · ϕ) ⟨k.val, _⟩
    -- For k.val < 4: tensor1_2 v_lo v at ⟨k.val, _⟩ = v_lo[0]·v[k.val] = v[k.val].
    show Mat4.apply (block00 M) ϕ ⟨k.val, hk⟩ =
         tensor1_2 ket0_1 (Mat4.apply (block00 M) ϕ) ⟨k.val, by omega⟩
    unfold tensor1_2
    have hdiv : k.val / 4 = 0 := Nat.div_eq_of_lt hk
    have hmod : k.val % 4 = k.val := Nat.mod_eq_of_lt hk
    rw [show (⟨k.val / 4, by omega⟩ : Fin 2) = ⟨0, by omega⟩ from Fin.ext hdiv,
        show (⟨k.val % 4, by omega⟩ : Fin 4) = ⟨k.val, hk⟩ from Fin.ext hmod]
    simp [ket0_1]
  · -- Upper half: k.val ≥ 4.
    have hk' : k.val - 4 < 4 := by omega
    have h_eq : k = (⟨(k.val - 4) + 4, by omega⟩ : Fin 8) :=
      Fin.ext (by show k.val = (k.val - 4) + 4; omega)
    rw [h_eq, Mat8.apply_tensor1_2_ket0_upper M ϕ ⟨k.val - 4, hk'⟩, h10]
    show Mat4.apply (0 : Mat4) ϕ ⟨k.val - 4, hk'⟩ =
         tensor1_2 ket0_1 (Mat4.apply (block00 M) ϕ) ⟨(k.val - 4) + 4, by omega⟩
    -- LHS: Mat4.apply 0 ϕ = 0.
    -- RHS: tensor1_2 ket0_1 v at idx ≥ 4 → ket0_1[1]=0 → result 0.
    have hdiv : ((k.val - 4) + 4) / 4 = 1 := by omega
    unfold tensor1_2
    rw [show (⟨((k.val - 4) + 4) / 4, by omega⟩ : Fin 2) = ⟨1, by omega⟩ from Fin.ext hdiv]
    simp [Mat4.apply, ket0_1]

set_option maxHeartbeats 800000 in
/-- Bridge: applying M : Mat8 to `tensor1_2 ket1 ϕ` and projecting to the
    lower half (a' = 0) gives `block01 M · ϕ`. -/
lemma Mat8.apply_tensor1_2_ket1_lower (M : Mat8) (ϕ : Vec2) (i : Fin 4) :
    Mat8.apply M (tensor1_2 ket1_1 ϕ) ⟨i.val, by omega⟩
      = Mat4.apply (block01 M) ϕ i := by
  show ∑ j : Fin 8, M ⟨i.val, by omega⟩ j * tensor1_2 ket1_1 ϕ j
       = ∑ j : Fin 4, block01 M i j * ϕ j
  rw [Fin.sum_univ_eight, Fin.sum_univ_four]
  simp [tensor1_2, ket1_1, block01, Matrix.of_apply]

/-- The 2-qubit identity factors as a tensor product of 1-qubit identities:
    `(1 : Mat4) = kron2 1 1`. -/
lemma kron2_one_one_eq_one : (kron2 (1 : Mat2) (1 : Mat2) : Mat4) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kron2, Matrix.one_apply]

/-- `kron2 1` is injective on Mat2: `kron2 1 X = kron2 1 Y ↔ X = Y`. -/
lemma kron2_one_eq_iff (X Y : Mat2) : kron2 1 X = kron2 1 Y ↔ X = Y := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  ext i j
  fin_cases i <;> fin_cases j
  · have := congr_fun (congr_fun h (0 : Fin 4)) (0 : Fin 4)
    simpa [kron2, Matrix.one_apply] using this
  · have := congr_fun (congr_fun h (0 : Fin 4)) (1 : Fin 4)
    simpa [kron2, Matrix.one_apply] using this
  · have := congr_fun (congr_fun h (1 : Fin 4)) (0 : Fin 4)
    simpa [kron2, Matrix.one_apply] using this
  · have := congr_fun (congr_fun h (1 : Fin 4)) (1 : Fin 4)
    simpa [kron2, Matrix.one_apply] using this

/-- A `kron2 1 X` matrix is zero iff X is zero. (`1 = I_2` so it's block-diagonal
    with X on each block.) -/
lemma kron2_one_eq_zero_iff (X : Mat2) :
    kron2 1 X = 0 ↔ X = 0 := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [mat2_eq_zero_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := congr_fun (congr_fun h (0 : Fin 4)) (0 : Fin 4)
      simpa [kron2, Matrix.one_apply] using this
    · have := congr_fun (congr_fun h (0 : Fin 4)) (1 : Fin 4)
      simpa [kron2, Matrix.one_apply] using this
    · have := congr_fun (congr_fun h (1 : Fin 4)) (0 : Fin 4)
      simpa [kron2, Matrix.one_apply] using this
    · have := congr_fun (congr_fun h (1 : Fin 4)) (1 : Fin 4)
      simpa [kron2, Matrix.one_apply] using this
  · rintro rfl
    ext i j
    simp [kron2]

/-- **Key lemma for py24_lemma_A_19**: if `(kron2 1 X) · ϕ = 0` for an entangled
    vector ϕ (i.e., ϕ 0 ϕ 3 ≠ ϕ 1 ϕ 2), then X = 0. -/
lemma mat2_eq_zero_of_kron2_one_apply_zero {X : Mat2} {ϕ : Vec2}
    (h_indep : ϕ 0 * ϕ 3 ≠ ϕ 1 * ϕ 2)
    (h : Mat4.apply (kron2 1 X) ϕ = 0) :
    X = 0 := by
  obtain ⟨h00v, h10v, h00w, h10w⟩ := kron2_one_apply_zero_entries h
  rw [mat2_eq_zero_iff]
  have hdet : ϕ 0 * ϕ 3 - ϕ 1 * ϕ 2 ≠ 0 := sub_ne_zero.mpr h_indep
  refine ⟨?_, ?_, ?_, ?_⟩
  · have key : X 0 0 * (ϕ 0 * ϕ 3 - ϕ 1 * ϕ 2) = 0 := by
      linear_combination ϕ 3 * h00v - ϕ 1 * h00w
    exact (mul_eq_zero.mp key).resolve_right hdet
  · have key : X 0 1 * (ϕ 0 * ϕ 3 - ϕ 1 * ϕ 2) = 0 := by
      linear_combination ϕ 0 * h00w - ϕ 2 * h00v
    exact (mul_eq_zero.mp key).resolve_right hdet
  · have key : X 1 0 * (ϕ 0 * ϕ 3 - ϕ 1 * ϕ 2) = 0 := by
      linear_combination ϕ 3 * h10v - ϕ 1 * h10w
    exact (mul_eq_zero.mp key).resolve_right hdet
  · have key : X 1 1 * (ϕ 0 * ϕ 3 - ϕ 1 * ϕ 2) = 0 := by
      linear_combination ϕ 0 * h10w - ϕ 2 * h10v
    exact (mul_eq_zero.mp key).resolve_right hdet

/-- Logical equivalence: ¬entangled ↔ tensor. -/
lemma not_isEntangled_iff_isTensor (v : Vec2) : ¬ IsEntangled v ↔ IsTensor v := by
  unfold IsEntangled
  exact Classical.not_not

/-! ## Linear dependence of two 1-qubit vectors

`linearDep1 a b` holds iff the 2×2 "column" matrix [a b] has zero determinant.
For non-zero vectors this is equivalent to "a is a scalar multiple of b". -/

/-- Two 1-qubit vectors are linearly dependent iff their cross-determinant is 0. -/
def linearDep1 (a b : Vec1) : Prop := a 0 * b 1 = a 1 * b 0

/-! ## Norm under scalar multiplication and normalization -/

/-- Squared norm scales by |c|² under complex scalar multiplication. -/
lemma normSqVec1_smul (c : ℂ) (v : Vec1) :
    normSqVec1 (c • v) = Complex.normSq c * normSqVec1 v := by
  unfold normSqVec1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul]

/-- A unit 1-qubit vector is nonzero. Direct corollary: `normSqVec1 v = 1 ≠ 0`. -/
lemma isQubit1_ne_zero {v : Vec1} (hv : IsQubit1 v) : v ≠ 0 := by
  intro h
  unfold IsQubit1 normSqVec1 at hv
  rw [h] at hv
  simp at hv

/-- A unit 2-qubit vector is nonzero. -/
lemma isQubit2_ne_zero {v : Vec2} (hv : IsQubit2 v) : v ≠ 0 := by
  intro h
  unfold IsQubit2 normSqVec2 at hv
  rw [h] at hv
  simp at hv

/-- A nonzero 1-qubit vector has strictly positive squared norm. -/
lemma normSqVec1_pos_of_ne_zero (v : Vec1) (hv : v ≠ 0) : 0 < normSqVec1 v := by
  unfold normSqVec1
  rw [Fin.sum_univ_two]
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h; apply hv; funext i; fin_cases i <;> assumption
    rw [h0, Complex.normSq_zero, zero_add]
    exact Complex.normSq_pos.mpr h1
  · linarith [Complex.normSq_pos.mpr h0, Complex.normSq_nonneg (v 1)]

/-- Unit normalization of a 1-qubit vector: divide by its real-valued norm. -/
noncomputable def unit_normalize_vec1 (v : Vec1) : Vec1 :=
  (((Real.sqrt (normSqVec1 v))⁻¹ : ℝ) : ℂ) • v

/-- The unit normalization of a nonzero vector is itself a unit vector. -/
lemma isQubit1_unit_normalize_vec1 (v : Vec1) (hv : v ≠ 0) :
    IsQubit1 (unit_normalize_vec1 v) := by
  unfold IsQubit1 unit_normalize_vec1
  rw [normSqVec1_smul, Complex.normSq_ofReal]
  have hnsq_pos : 0 < normSqVec1 v := normSqVec1_pos_of_ne_zero v hv
  have hsqrt_ne : Real.sqrt (normSqVec1 v) ≠ 0 :=
    (Real.sqrt_pos.mpr hnsq_pos).ne'
  rw [show ((Real.sqrt (normSqVec1 v))⁻¹ : ℝ) * ((Real.sqrt (normSqVec1 v))⁻¹ : ℝ)
        = (Real.sqrt (normSqVec1 v) * Real.sqrt (normSqVec1 v))⁻¹
        from (mul_inv _ _).symm]
  rw [Real.mul_self_sqrt hnsq_pos.le, inv_mul_cancel₀ hnsq_pos.ne']

/-- Recovery: scaling the unit normalization by ‖v‖ recovers v. -/
lemma smul_unit_normalize_vec1 (v : Vec1) (hv : v ≠ 0) :
    ((Real.sqrt (normSqVec1 v) : ℝ) : ℂ) • unit_normalize_vec1 v = v := by
  unfold unit_normalize_vec1
  rw [smul_smul]
  have hnsq_pos : 0 < normSqVec1 v := normSqVec1_pos_of_ne_zero v hv
  rw [show ((Real.sqrt (normSqVec1 v) : ℝ) : ℂ) *
          (((Real.sqrt (normSqVec1 v))⁻¹ : ℝ) : ℂ)
        = ((Real.sqrt (normSqVec1 v) * (Real.sqrt (normSqVec1 v))⁻¹ : ℝ) : ℂ) from by
       push_cast; ring]
  rw [show Real.sqrt (normSqVec1 v) * (Real.sqrt (normSqVec1 v))⁻¹ = 1 from
      mul_inv_cancel₀ (Real.sqrt_pos.mpr hnsq_pos).ne']
  simp

/-! ## Orthogonality -/

/-- Two 1-qubit vectors are orthogonal if their inner product is zero. -/
def IsOrthogonal1 (a b : Vec1) : Prop := innerVec1 a b = 0

/-! ## Basic action lemmas -/

/-- The identity matrix acts trivially on a 1-qubit vector. -/
lemma Mat2.apply_one (v : Vec1) : Mat2.apply 1 v = v := by
  funext i
  unfold Mat2.apply
  simp [Matrix.one_apply, Finset.sum_ite_eq']

/-- The identity matrix acts trivially on a 2-qubit vector. -/
lemma Mat4.apply_one (v : Vec2) : Mat4.apply 1 v = v := by
  funext i
  unfold Mat4.apply
  simp [Matrix.one_apply, Finset.sum_ite_eq']

/-- Matrix action distributes over multiplication: (M·N).apply v = M.apply (N.apply v). -/
lemma Mat2.apply_mul (M N : Mat2) (v : Vec1) :
    Mat2.apply (M * N) v = Mat2.apply M (Mat2.apply N v) := by
  funext i
  unfold Mat2.apply
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Matrix action distributes over multiplication: (M·N).apply v = M.apply (N.apply v). -/
lemma Mat4.apply_mul (M N : Mat4) (v : Vec2) :
    Mat4.apply (M * N) v = Mat4.apply M (Mat4.apply N v) := by
  funext i
  unfold Mat4.apply
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-! ## Computational basis is unit-norm -/

lemma IsQubit1_ket0 : IsQubit1 ket0_1 := by
  unfold IsQubit1 normSqVec1 ket0_1
  rw [Fin.sum_univ_two]
  simp

lemma IsQubit1_ket1 : IsQubit1 ket1_1 := by
  unfold IsQubit1 normSqVec1 ket1_1
  rw [Fin.sum_univ_two]
  simp

/-! ## tensor1_1 bilinearity -/

lemma tensor1_1_zero_left (b : Vec1) : tensor1_1 (0 : Vec1) b = 0 := by
  funext k
  unfold tensor1_1
  simp

lemma tensor1_1_zero_right (a : Vec1) : tensor1_1 a (0 : Vec1) = 0 := by
  funext k
  unfold tensor1_1
  simp

lemma tensor1_1_smul_left (s : ℂ) (a b : Vec1) :
    tensor1_1 (s • a) b = s • tensor1_1 a b := by
  funext k
  unfold tensor1_1
  simp [Pi.smul_apply, smul_eq_mul]
  ring

lemma tensor1_1_smul_right (s : ℂ) (a b : Vec1) :
    tensor1_1 a (s • b) = s • tensor1_1 a b := by
  funext k
  unfold tensor1_1
  simp [Pi.smul_apply, smul_eq_mul]
  ring

/-- **A.24 helper**: scalars on each tensor factor combine as `s · t`.
    Used in Step 4 normalization: `tensor1_1 ((1/r)•a_V) (r•b_V) = tensor1_1 a_V b_V`
    when `r ≠ 0`. -/
lemma tensor1_1_smul_smul (s t : ℂ) (a b : Vec1) :
    tensor1_1 (s • a) (t • b) = (s * t) • tensor1_1 a b := by
  rw [tensor1_1_smul_left, tensor1_1_smul_right, smul_smul]

lemma tensor1_1_add_left (a₁ a₂ b : Vec1) :
    tensor1_1 (a₁ + a₂) b = tensor1_1 a₁ b + tensor1_1 a₂ b := by
  funext k
  unfold tensor1_1
  simp [Pi.add_apply]
  ring

lemma tensor1_1_add_right (a b₁ b₂ : Vec1) :
    tensor1_1 a (b₁ + b₂) = tensor1_1 a b₁ + tensor1_1 a b₂ := by
  funext k
  unfold tensor1_1
  simp [Pi.add_apply]
  ring

/-- A 1-qubit vector is zero iff both components are zero. -/
lemma vec1_eq_zero_iff (v : Vec1) : v = 0 ↔ v 0 = 0 ∧ v 1 = 0 := by
  refine ⟨fun h => ?_, fun ⟨h0, h1⟩ => ?_⟩
  · rw [h]; exact ⟨rfl, rfl⟩
  · funext i; fin_cases i <;> assumption

/-- A 2-qubit vector is zero iff all four components are zero. -/
lemma vec2_eq_zero_iff (v : Vec2) :
    v = 0 ↔ v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0 := by
  refine ⟨fun h => ?_, fun ⟨h0, h1, h2, h3⟩ => ?_⟩
  · rw [h]; exact ⟨rfl, rfl, rfl, rfl⟩
  · funext i; fin_cases i <;> assumption

/-- A Vec1 ⊗ Vec2 tensor product is zero iff one factor is zero. -/
lemma tensor1_2_eq_zero_iff (a : Vec1) (b : Vec2) :
    tensor1_2 a b = 0 ↔ a = 0 ∨ b = 0 := by
  refine ⟨fun h => ?_, ?_⟩
  · -- 8 entrywise products = 0; combine via case analysis on a 0, a 1, b 0..3.
    have h0 : a 0 = 0 ∨ b 0 = 0 := by
      have := congr_fun h (0 : Fin 8); simpa [tensor1_2] using this
    have h1 : a 0 = 0 ∨ b 1 = 0 := by
      have := congr_fun h (1 : Fin 8); simpa [tensor1_2] using this
    have h2 : a 0 = 0 ∨ b 2 = 0 := by
      have := congr_fun h (2 : Fin 8); simpa [tensor1_2] using this
    have h3 : a 0 = 0 ∨ b 3 = 0 := by
      have := congr_fun h (3 : Fin 8); simpa [tensor1_2] using this
    have h4 : a 1 = 0 ∨ b 0 = 0 := by
      have := congr_fun h (4 : Fin 8); simpa [tensor1_2] using this
    have h5 : a 1 = 0 ∨ b 1 = 0 := by
      have := congr_fun h (5 : Fin 8); simpa [tensor1_2] using this
    have h6 : a 1 = 0 ∨ b 2 = 0 := by
      have := congr_fun h (6 : Fin 8); simpa [tensor1_2] using this
    have h7 : a 1 = 0 ∨ b 3 = 0 := by
      have := congr_fun h (7 : Fin 8); simpa [tensor1_2] using this
    rw [vec1_eq_zero_iff, vec2_eq_zero_iff]
    -- Goal: (a 0 = 0 ∧ a 1 = 0) ∨ (b 0 = 0 ∧ b 1 = 0 ∧ b 2 = 0 ∧ b 3 = 0)
    by_cases ha0 : a 0 = 0
    · by_cases ha1 : a 1 = 0
      · left; exact ⟨ha0, ha1⟩
      · right
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact h4.resolve_left ha1
        · exact h5.resolve_left ha1
        · exact h6.resolve_left ha1
        · exact h7.resolve_left ha1
    · right
      have hb0 : b 0 = 0 := h0.resolve_left ha0
      have hb1 : b 1 = 0 := h1.resolve_left ha0
      have hb2 : b 2 = 0 := h2.resolve_left ha0
      have hb3 : b 3 = 0 := h3.resolve_left ha0
      exact ⟨hb0, hb1, hb2, hb3⟩
  · rintro (rfl | rfl)
    · funext k; unfold tensor1_2; simp
    · funext k; unfold tensor1_2; simp

/-! ## tensor1_2 bilinearity (mirrors tensor1_1) -/

lemma tensor1_2_zero_left (b : Vec2) : tensor1_2 (0 : Vec1) b = 0 := by
  funext k
  unfold tensor1_2
  simp

lemma tensor1_2_zero_right (a : Vec1) : tensor1_2 a (0 : Vec2) = 0 := by
  funext k
  unfold tensor1_2
  simp

lemma tensor1_2_smul_left (s : ℂ) (a : Vec1) (b : Vec2) :
    tensor1_2 (s • a) b = s • tensor1_2 a b := by
  funext k
  unfold tensor1_2
  simp [Pi.smul_apply, smul_eq_mul]
  ring

lemma tensor1_2_smul_right (s : ℂ) (a : Vec1) (b : Vec2) :
    tensor1_2 a (s • b) = s • tensor1_2 a b := by
  funext k
  unfold tensor1_2
  simp [Pi.smul_apply, smul_eq_mul]
  ring

lemma tensor1_2_add_left (a₁ a₂ : Vec1) (b : Vec2) :
    tensor1_2 (a₁ + a₂) b = tensor1_2 a₁ b + tensor1_2 a₂ b := by
  funext k
  unfold tensor1_2
  simp [Pi.add_apply]
  ring

lemma tensor1_2_add_right (a : Vec1) (b₁ b₂ : Vec2) :
    tensor1_2 a (b₁ + b₂) = tensor1_2 a b₁ + tensor1_2 a b₂ := by
  funext k
  unfold tensor1_2
  simp [Pi.add_apply]
  ring

/-- A tensor product is zero iff one factor is zero. -/
lemma tensor1_1_eq_zero_iff (a b : Vec1) :
    tensor1_1 a b = 0 ↔ a = 0 ∨ b = 0 := by
  refine ⟨fun h => ?_, ?_⟩
  · -- Get the four entrywise products from h, in disjunctive form.
    have h00 : a 0 = 0 ∨ b 0 = 0 := by
      have := congr_fun h (0 : Fin 4); simpa [tensor1_1] using this
    have h01 : a 0 = 0 ∨ b 1 = 0 := by
      have := congr_fun h (1 : Fin 4); simpa [tensor1_1] using this
    have h10 : a 1 = 0 ∨ b 0 = 0 := by
      have := congr_fun h (2 : Fin 4); simpa [tensor1_1] using this
    have h11 : a 1 = 0 ∨ b 1 = 0 := by
      have := congr_fun h (3 : Fin 4); simpa [tensor1_1] using this
    rw [vec1_eq_zero_iff, vec1_eq_zero_iff]
    -- Goal: (a 0 = 0 ∧ a 1 = 0) ∨ (b 0 = 0 ∧ b 1 = 0)
    rcases h00 with ha0 | hb0
    · rcases h11 with ha1 | hb1
      · left; exact ⟨ha0, ha1⟩
      · rcases h10 with ha1 | hb0'
        · left; exact ⟨ha0, ha1⟩
        · right; exact ⟨hb0', hb1⟩
    · rcases h11 with ha1 | hb1
      · rcases h01 with ha0 | hb1'
        · left; exact ⟨ha0, ha1⟩
        · right; exact ⟨hb0, hb1'⟩
      · right; exact ⟨hb0, hb1⟩
  · rintro (rfl | rfl)
    · exact tensor1_1_zero_left b
    · exact tensor1_1_zero_right a

/-- The tensor product of two nonzero Vec1's is nonzero. Direct corollary
    of `tensor1_1_eq_zero_iff`. -/
lemma tensor1_1_ne_zero_of_factors_ne_zero {a b : Vec1}
    (ha : a ≠ 0) (hb : b ≠ 0) : tensor1_1 a b ≠ 0 := by
  rw [Ne, tensor1_1_eq_zero_iff, not_or]
  exact ⟨ha, hb⟩

/-- The Vec1 ⊗ Vec2 tensor product of two nonzero factors is nonzero. -/
lemma tensor1_2_ne_zero_of_factors_ne_zero {a : Vec1} {b : Vec2}
    (ha : a ≠ 0) (hb : b ≠ 0) : tensor1_2 a b ≠ 0 := by
  rw [Ne, tensor1_2_eq_zero_iff, not_or]
  exact ⟨ha, hb⟩


/-! ## Mat4.apply linearity -/

lemma Mat4.apply_zero (M : Mat4) : Mat4.apply M (0 : Vec2) = 0 := by
  funext i
  unfold Mat4.apply
  simp

lemma Mat4.apply_add (M : Mat4) (u v : Vec2) :
    Mat4.apply M (u + v) = Mat4.apply M u + Mat4.apply M v := by
  funext i
  unfold Mat4.apply
  simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma Mat4.apply_smul (s : ℂ) (M : Mat4) (v : Vec2) :
    Mat4.apply M (s • v) = s • Mat4.apply M v := by
  funext i
  unfold Mat4.apply
  simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

/-! ## Mat8.apply linearity (mirrors Mat4.apply) -/

lemma Mat8.apply_one (v : Vec3) : Mat8.apply 1 v = v := by
  funext i
  unfold Mat8.apply
  simp [Matrix.one_apply]

lemma Mat8.apply_zero (M : Mat8) : Mat8.apply M (0 : Vec3) = 0 := by
  funext i
  unfold Mat8.apply
  simp

lemma Mat8.apply_add (M : Mat8) (u v : Vec3) :
    Mat8.apply M (u + v) = Mat8.apply M u + Mat8.apply M v := by
  funext i
  unfold Mat8.apply
  simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma Mat8.apply_smul (s : ℂ) (M : Mat8) (v : Vec3) :
    Mat8.apply M (s • v) = s • Mat8.apply M v := by
  funext i
  unfold Mat8.apply
  simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

lemma Mat8.apply_mul (M N : Mat8) (v : Vec3) :
    Mat8.apply (M * N) v = Mat8.apply M (Mat8.apply N v) := by
  funext i
  unfold Mat8.apply
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-! ## Vec1 basis decomposition -/

/-- Any 1-qubit vector decomposes in the computational basis. -/
lemma vec1_basis_decomp (v : Vec1) : v = v 0 • ket0_1 + v 1 • ket1_1 := by
  funext i
  fin_cases i <;>
    simp [ket0_1, ket1_1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-! ## kron2 acts on tensor products as expected -/

/-- The tensor product of matrix actions equals the matrix action on the tensor:
    (V ⊗ W) · (a ⊗ b) = (V·a) ⊗ (W·b). -/
lemma kron2_apply_tensor1_1 (V W : Mat2) (a b : Vec1) :
    Mat4.apply (kron2 V W) (tensor1_1 a b) =
      tensor1_1 (Mat2.apply V a) (Mat2.apply W b) := by
  funext i
  fin_cases i <;>
    simp [Mat4.apply, Mat2.apply, kron2, tensor1_1, Matrix.of_apply,
          Fin.sum_univ_four, Fin.sum_univ_two] <;>
    ring

set_option maxHeartbeats 800000 in
/-- A 3-qubit tensor product gate acts on a tensor1_2 state by separately
    acting on each factor: (A⊗B⊗C)·(v⊗ϕ) = (A·v) ⊗ ((B⊗C)·ϕ). -/
lemma kron3_apply_tensor1_2 (A B C : Mat2) (v : Vec1) (ϕ : Vec2) :
    Mat8.apply (kron3 A B C) (tensor1_2 v ϕ) =
      tensor1_2 (Mat2.apply A v) (Mat4.apply (kron2 B C) ϕ) := by
  funext i
  fin_cases i <;>
    simp [Mat8.apply, Mat4.apply, Mat2.apply, kron3, kron2, tensor1_2,
          Matrix.of_apply, Fin.sum_univ_eight, Fin.sum_univ_four,
          Fin.sum_univ_two, decode3] <;>
    ring

/-! ## Tensor product norm

The squared norm of a tensor factors as the product of the factor norms. -/

/-- Squared norm of a tensor product equals the product of squared norms. -/
lemma normSqVec2_tensor1_1 (a b : Vec1) :
    normSqVec2 (tensor1_1 a b) = normSqVec1 a * normSqVec1 b := by
  unfold normSqVec2 normSqVec1 tensor1_1
  rw [Fin.sum_univ_four, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [Complex.normSq_mul]
  ring

/-- A tensor product of qubits is a 2-qubit state (unit-norm). -/
lemma IsQubit2_tensor1_1 {a b : Vec1} (ha : IsQubit1 a) (hb : IsQubit1 b) :
    IsQubit2 (tensor1_1 a b) := by
  unfold IsQubit2
  rw [normSqVec2_tensor1_1]
  unfold IsQubit1 at ha hb
  rw [ha, hb, mul_one]

/-! ## Computational basis tensors -/

/-- The 2-qubit basis state |00⟩ is a unit vector. -/
lemma IsQubit2_ket00 : IsQubit2 (tensor1_1 ket0_1 ket0_1) :=
  IsQubit2_tensor1_1 IsQubit1_ket0 IsQubit1_ket0

/-- The 2-qubit basis state |01⟩ is a unit vector. -/
lemma IsQubit2_ket01 : IsQubit2 (tensor1_1 ket0_1 ket1_1) :=
  IsQubit2_tensor1_1 IsQubit1_ket0 IsQubit1_ket1

/-- The 2-qubit basis state |10⟩ is a unit vector. -/
lemma IsQubit2_ket10 : IsQubit2 (tensor1_1 ket1_1 ket0_1) :=
  IsQubit2_tensor1_1 IsQubit1_ket1 IsQubit1_ket0

/-- The 2-qubit basis state |11⟩ is a unit vector. -/
lemma IsQubit2_ket11 : IsQubit2 (tensor1_1 ket1_1 ket1_1) :=
  IsQubit2_tensor1_1 IsQubit1_ket1 IsQubit1_ket1

/-! ## Inner product / norm correspondence

The inner product of a vector with itself equals its squared norm, viewed as
a complex number (the imaginary part is automatically zero). -/

/-- `⟨v|v⟩ = ‖v‖²` as a complex number. -/
lemma innerVec1_self (v : Vec1) :
    innerVec1 v v = (normSqVec1 v : ℂ) := by
  unfold innerVec1 normSqVec1
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm, Complex.mul_conj]

/-- `⟨v|v⟩ = ‖v‖²` as a complex number, for 2-qubit vectors. -/
lemma innerVec2_self (v : Vec2) :
    innerVec2 v v = (normSqVec2 v : ℂ) := by
  unfold innerVec2 normSqVec2
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm, Complex.mul_conj]

/-! ## Inner product linearity -/

/-- Inner product is conjugate-linear in the first argument (additive). -/
lemma innerVec1_add_left (u v w : Vec1) :
    innerVec1 (u + v) w = innerVec1 u w + innerVec1 v w := by
  unfold innerVec1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp [add_mul, map_add]

/-- Inner product is linear in the second argument (additive). -/
lemma innerVec1_add_right (u v w : Vec1) :
    innerVec1 u (v + w) = innerVec1 u v + innerVec1 u w := by
  unfold innerVec1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_add]

/-- Inner product factors through tensor product:
    `⟨a₁⊗a₂, b₁⊗b₂⟩ = ⟨a₁, b₁⟩ · ⟨a₂, b₂⟩`. -/
lemma innerVec2_tensor1_1 (a₁ a₂ b₁ b₂ : Vec1) :
    innerVec2 (tensor1_1 a₁ a₂) (tensor1_1 b₁ b₂) =
      innerVec1 a₁ b₁ * innerVec1 a₂ b₂ := by
  unfold innerVec2 innerVec1 tensor1_1
  rw [Fin.sum_univ_four, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [map_mul]
  ring

/-! ## Unitary action preserves inner product and norm

For unitary V, ⟨V·a | V·b⟩ = ⟨a | b⟩, hence ‖V·v‖² = ‖v‖². -/

/-- Column orthogonality of a 4×4 unitary in Σ-form:
    ∑_i conj(V i j) · V i k = δ_{jk}. -/
lemma unitary4_col_orthogonal_sum {V : Mat4} (hV : IsUnitary4 V) (j k : Fin 4) :
    ∑ i : Fin 4, starRingEnd ℂ (V i j) * V i k = if j = k then 1 else 0 := by
  unfold IsUnitary4 at hV
  have h := congr_fun (congr_fun hV j) k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
             RCLike.star_def] at h
  exact h

/-- Unitary action preserves the inner product: ⟨V·a | V·b⟩ = ⟨a | b⟩. -/
lemma innerVec2_apply_apply_unitary {V : Mat4} (hV : IsUnitary4 V) (a b : Vec2) :
    innerVec2 (Mat4.apply V a) (Mat4.apply V b) = innerVec2 a b := by
  unfold innerVec2 Mat4.apply
  -- Step 1: expand to a triple sum ∑ i ∑ j ∑ k.
  trans (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4,
            starRingEnd ℂ (V i j) * starRingEnd ℂ (a j) * (V i k * b k))
  · apply Finset.sum_congr rfl
    intro i _
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, Finset.mul_sum]
  -- Step 2: swap to ∑ j ∑ k ∑ i.
  trans (∑ j : Fin 4, ∑ k : Fin 4, ∑ i : Fin 4,
            starRingEnd ℂ (V i j) * starRingEnd ℂ (a j) * (V i k * b k))
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
  -- Step 3: factor out conj(a j) and b k from the inner sum.
  trans (∑ j : Fin 4, ∑ k : Fin 4,
            starRingEnd ℂ (a j) * b k *
              ∑ i : Fin 4, starRingEnd ℂ (V i j) * V i k)
  · apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  -- Step 4: apply unitarity (∑_i conj(V i j) · V i k = δ_{jk}).
  trans (∑ j : Fin 4, ∑ k : Fin 4,
            starRingEnd ℂ (a j) * b k * (if j = k then (1 : ℂ) else 0))
  · apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [unitary4_col_orthogonal_sum hV j k]
  -- Step 5: collapse the inner sum using sum_ite_eq.
  trans (∑ j : Fin 4, starRingEnd ℂ (a j) * b j)
  · apply Finset.sum_congr rfl
    intro j _
    trans (∑ k : Fin 4, if j = k then starRingEnd ℂ (a j) * b k else 0)
    · apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> ring
    rw [Finset.sum_ite_eq]
    simp
  rfl

/-- Unitary action preserves the squared norm: ‖V·v‖² = ‖v‖². -/
lemma unitary4_apply_normSqVec2 {V : Mat4} (hV : IsUnitary4 V) (v : Vec2) :
    normSqVec2 (Mat4.apply V v) = normSqVec2 v := by
  have h := innerVec2_apply_apply_unitary hV v v
  rw [innerVec2_self, innerVec2_self] at h
  exact_mod_cast h

/-- Unitary action sends qubit states to qubit states. -/
lemma IsQubit2_apply_unitary {V : Mat4} (hV : IsUnitary4 V) {v : Vec2}
    (hv : IsQubit2 v) : IsQubit2 (Mat4.apply V v) := by
  unfold IsQubit2 at *
  rw [unitary4_apply_normSqVec2 hV, hv]

/-- Mat2 column orthogonality in Σ-form (analog of `unitary4_col_orthogonal_sum`). -/
lemma unitary2_col_orthogonal_sum {V : Mat2} (hV : IsUnitary2 V) (j k : Fin 2) :
    ∑ i : Fin 2, starRingEnd ℂ (V i j) * V i k = if j = k then 1 else 0 := by
  unfold IsUnitary2 at hV
  have h := congr_fun (congr_fun hV j) k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
             RCLike.star_def] at h
  exact h

/-- Unitary 2×2 action preserves Vec1 inner product. -/
lemma innerVec1_apply_apply_unitary {V : Mat2} (hV : IsUnitary2 V) (a b : Vec1) :
    innerVec1 (Mat2.apply V a) (Mat2.apply V b) = innerVec1 a b := by
  unfold innerVec1 Mat2.apply
  trans (∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2,
            starRingEnd ℂ (V i j) * starRingEnd ℂ (a j) * (V i k * b k))
  · apply Finset.sum_congr rfl
    intro i _
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, Finset.mul_sum]
  trans (∑ j : Fin 2, ∑ k : Fin 2, ∑ i : Fin 2,
            starRingEnd ℂ (V i j) * starRingEnd ℂ (a j) * (V i k * b k))
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
  trans (∑ j : Fin 2, ∑ k : Fin 2,
            starRingEnd ℂ (a j) * b k *
              ∑ i : Fin 2, starRingEnd ℂ (V i j) * V i k)
  · apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  trans (∑ j : Fin 2, ∑ k : Fin 2,
            starRingEnd ℂ (a j) * b k * (if j = k then (1 : ℂ) else 0))
  · apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [unitary2_col_orthogonal_sum hV j k]
  trans (∑ j : Fin 2, starRingEnd ℂ (a j) * b j)
  · apply Finset.sum_congr rfl
    intro j _
    trans (∑ k : Fin 2, if j = k then starRingEnd ℂ (a j) * b k else 0)
    · apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> ring
    rw [Finset.sum_ite_eq]
    simp
  rfl

/-- Unitary 2×2 action preserves Vec1 squared norm. -/
lemma unitary2_apply_normSqVec1 {V : Mat2} (hV : IsUnitary2 V) (v : Vec1) :
    normSqVec1 (Mat2.apply V v) = normSqVec1 v := by
  have h := innerVec1_apply_apply_unitary hV v v
  rw [innerVec1_self, innerVec1_self] at h
  exact_mod_cast h

/-- Unitary 2×2 action sends qubit states to qubit states. -/
lemma IsQubit1_apply_unitary {V : Mat2} (hV : IsUnitary2 V) {v : Vec1}
    (hv : IsQubit1 v) : IsQubit1 (Mat2.apply V v) := by
  unfold IsQubit1 at *
  rw [unitary2_apply_normSqVec1 hV, hv]

/-- Mat2 applied to ket0 extracts the first column. -/
lemma Mat2.apply_ket0 (V : Mat2) :
    Mat2.apply V ket0_1 = fun i => V i 0 := by
  funext i
  unfold Mat2.apply
  rw [Fin.sum_univ_two]
  simp [ket0_1]

/-- Mat2 applied to ket1 extracts the second column. -/
lemma Mat2.apply_ket1 (V : Mat2) :
    Mat2.apply V ket1_1 = fun i => V i 1 := by
  funext i
  unfold Mat2.apply
  rw [Fin.sum_univ_two]
  simp [ket1_1]

/-- Inversion: if R·ψ = ket0, then R†·ket0 = ψ. (R unitary ⟹ R†·R = I.) -/
lemma Mat2_apply_conjTranspose_ket0_of_rotate {R : Mat2} (hR : IsUnitary2 R)
    {ψ : Vec1} (h : Mat2.apply R ψ = ket0_1) :
    Mat2.apply R.conjTranspose ket0_1 = ψ := by
  rw [← h, ← Mat2.apply_mul, hR, Mat2.apply_one]

end
