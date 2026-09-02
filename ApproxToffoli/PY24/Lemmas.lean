/-
  ApproxToffoli.PY24.Lemmas

  Full formalization of Palsberg & Yu (2024)'s "second main lemma"
  (Lemma 6.4) and supporting Appendix A lemmas.

  Source: Palsberg & Yu (2024), "Optimal implementation of quantum gates with
  two controls", Linear Algebra and its Applications 694 (2024) 206-261.

  STATUS: Sorry-free as of iter 358 (closure of py24_lemma_A_29). All
  PY24 lemmas referenced in HP / 6.4 / 6.3 / 6.2 / appendix are proved.

  HP→PY24 mapping (verified from HP page 28):
  - HP A.8  = PY24 Lemma 6.1  (case analysis of a unitary)
  - HP A.9  = PY24 Lemma 6.4  (CC(Diag) characterization, alternating AC-BC)
  - HP A.11 = PY24 Lemma A.5  (tensor product eigenvalues)
  - HP A.12 = PY24 Lemma A.6  (block-diagonal eigenvalues)
  - HP A.13 = PY24 Lemma A.19 (entangling implies controlled)
  - HP A.14 = PY24 Lemma A.24 (UAC VAB tensor decomposition)
  - HP A.15 = PY24 Lemma A.30 (tensor with second-factor-fixed)
  - HP A.16 = PY24 Lemma A.32 (V₃(|0⟩⊗|0⟩) = |0⟩⊗|0⟩ normalization)
  - HP A.17 = PY24 Lemma A.33 (V₁ controlled from middle gate's structure)
-/

import ApproxToffoli.PY24.Vectors
import ApproxToffoli.HP.Embedding
import ApproxToffoli.HP.EmbedLemmas
import ApproxToffoli.BlockDecomp
import Mathlib.Analysis.Complex.Polynomial.Basic

open Matrix Complex

noncomputable section

/-! ## PY24 Lemma 6.1 (HP A.8) — Case analysis of a unitary

For a 2-qubit unitary V, exactly one of three cases holds for its action on
states of the form |x⟩ ⊗ |0⟩:
1. V produces an entangled state for some |x⟩.
2. V always produces a tensor with the SECOND factor fixed (|z⟩ ⊗ |ψ⟩).
3. V always produces a tensor with the FIRST factor fixed (|ψ⟩ ⊗ |z⟩). -/

/-- Expansion of V·(x⊗|0⟩) given the action on basis states |0⊗0⟩, |1⊗0⟩.
    Combines `vec1_basis_decomp` with `tensor1_1` bilinearity and `Mat4.apply`
    linearity. -/
private lemma V_apply_xtensor0_decomp
    (V : Mat4) (a₀ b₀ a₁ b₁ : Vec1)
    (h₀ : Mat4.apply V (tensor1_1 ket0_1 ket0_1) = tensor1_1 a₀ b₀)
    (h₁ : Mat4.apply V (tensor1_1 ket1_1 ket0_1) = tensor1_1 a₁ b₁)
    (x : Vec1) :
    Mat4.apply V (tensor1_1 x ket0_1) =
      x 0 • tensor1_1 a₀ b₀ + x 1 • tensor1_1 a₁ b₁ := by
  conv_lhs => rw [vec1_basis_decomp x]
  rw [tensor1_1_add_left, tensor1_1_smul_left, tensor1_1_smul_left,
      Mat4.apply_add, Mat4.apply_smul, Mat4.apply_smul, h₀, h₁]

set_option maxHeartbeats 800000 in
-- fin_cases × 8 + heavy simp (Mat8.apply expansion over Fin 8 sums) exhausts default 200000.
/-- `embedBC V` acts on `tensor1_2 a ϕ` by applying V to the second factor:
    `(embedBC V) · (a ⊗ ϕ) = a ⊗ (V · ϕ)`. -/
lemma embedBC_apply_tensor1_2 (V : Mat4) (a : Vec1) (ϕ : Vec2) :
    Mat8.apply (embedBC V) (tensor1_2 a ϕ) = tensor1_2 a (Mat4.apply V ϕ) := by
  funext k
  fin_cases k <;>
    simp [Mat8.apply, Mat4.apply, embedBC, tensor1_2, Matrix.of_apply,
          Fin.sum_univ_eight, Fin.sum_univ_four] <;> ring

/-- For any V, `embedBC V` applied to a tensor1_2 ket0-state has zero upper
    half (since embedBC leaves qubit A fixed and the input has A=0). -/
lemma Mat8.apply_embedBC_tensor1_2_ket0_upper (V : Mat4) (ϕ : Vec2) (i : Fin 4) :
    Mat8.apply (embedBC V) (tensor1_2 ket0_1 ϕ) ⟨i.val + 4, by omega⟩ = 0 := by
  rw [Mat8.apply_tensor1_2_ket0_upper, block10_embedBC]
  show Mat4.apply 0 ϕ i = 0
  unfold Mat4.apply
  simp

/-- Bridge: if `(kron2 1 X)·(ψ⊗z) = 0` and ψ ≠ 0 (i.e., is a nonzero qubit-like
    vector), then `X·z = 0`. The factor ψ is "absorbed" via case analysis on
    its components. -/
private lemma X_apply_z_zero_of_kron2_apply_tensor_zero
    {X : Mat2} {ψ z : Vec1} (hψ : ψ ≠ 0)
    (h : Mat4.apply (kron2 1 X) (tensor1_1 ψ z) = 0) :
    Mat2.apply X z = 0 := by
  obtain ⟨h00, h10, h20, h30⟩ := kron2_one_apply_zero_entries h
  -- tensor1_1 ψ z indices: (ψ 0 z 0, ψ 0 z 1, ψ 1 z 0, ψ 1 z 1).
  have hϕ_def : ∀ k : Fin 4, tensor1_1 ψ z k =
      match k with | 0 => ψ 0 * z 0 | 1 => ψ 0 * z 1 | 2 => ψ 1 * z 0 | _ => ψ 1 * z 1 := by
    intro k; fin_cases k <;> rfl
  rw [hϕ_def 0] at h00
  rw [hϕ_def 1] at h00
  rw [hϕ_def 0] at h10
  rw [hϕ_def 1] at h10
  rw [hϕ_def 2] at h20
  rw [hϕ_def 3] at h20
  rw [hϕ_def 2] at h30
  rw [hϕ_def 3] at h30
  -- h00: X 0 0 * (ψ 0 * z 0) + X 0 1 * (ψ 0 * z 1) = 0
  --      ⟹ ψ 0 * (X 0 0 z 0 + X 0 1 z 1) = 0 (factor)
  -- Similar for h10, h20, h30.
  have hψ_split : ψ 0 ≠ 0 ∨ ψ 1 ≠ 0 := by
    by_contra hh; push_neg at hh
    exact hψ ((vec1_eq_zero_iff ψ).mpr ⟨hh.1, hh.2⟩)
  funext i
  fin_cases i
  · simp only [Mat2.apply, Fin.sum_univ_two, Pi.zero_apply, Fin.isValue]
    rcases hψ_split with hψ0 | hψ1
    · have key : ψ 0 * (X 0 0 * z 0 + X 0 1 * z 1) = 0 := by linear_combination h00
      exact (mul_eq_zero.mp key).resolve_left hψ0
    · have key : ψ 1 * (X 0 0 * z 0 + X 0 1 * z 1) = 0 := by linear_combination h20
      exact (mul_eq_zero.mp key).resolve_left hψ1
  · simp only [Mat2.apply, Fin.sum_univ_two, Pi.zero_apply, Fin.isValue]
    rcases hψ_split with hψ0 | hψ1
    · have key : ψ 0 * (X 1 0 * z 0 + X 1 1 * z 1) = 0 := by linear_combination h10
      exact (mul_eq_zero.mp key).resolve_left hψ0
    · have key : ψ 1 * (X 1 0 * z 0 + X 1 1 * z 1) = 0 := by linear_combination h30
      exact (mul_eq_zero.mp key).resolve_left hψ1

/-- Specialization of `V_apply_xtensor0_decomp` to the first-factor-fixed case:
    `V·(ket_k⊗|0⟩) = ψ⊗z_k` (same first factor ψ for k=0,1) gives
    `V·(x⊗|0⟩) = ψ⊗(x 0•z₀ + x 1•z₁)` for all x : Vec1. -/
private lemma V_apply_xtensor0_first_factor_fixed
    (V : Mat4) (ψ z₀ z₁ : Vec1)
    (h₀ : Mat4.apply V (tensor1_1 ket0_1 ket0_1) = tensor1_1 ψ z₀)
    (h₁ : Mat4.apply V (tensor1_1 ket1_1 ket0_1) = tensor1_1 ψ z₁)
    (x : Vec1) :
    Mat4.apply V (tensor1_1 x ket0_1) =
      tensor1_1 ψ (x 0 • z₀ + x 1 • z₁) := by
  rw [V_apply_xtensor0_decomp V ψ z₀ ψ z₁ h₀ h₁ x]
  rw [← tensor1_1_smul_right, ← tensor1_1_smul_right, ← tensor1_1_add_right]

/-! ## Block-diag-second algebra (mirrors block-diag-first in py24_lemma_A_6)

The form `kron2 A proj0 + kron2 B proj1` is "block-diagonal in qubit C": it
acts as A on qubit B when C=0, and as B when C=1. These helpers will be
used by A.30, A.32 to construct W₂-style controlled gates. -/

/-- Conjugate transpose of a "block-diag-second" form `kron2 A proj0 + kron2 B proj1`. -/
lemma block_diag_second_conjT (A B : Mat2) :
    (kron2 A proj0 + kron2 B proj1).conjTranspose
      = kron2 A.conjTranspose proj0 + kron2 B.conjTranspose proj1 := by
  rw [Matrix.conjTranspose_add, kron2_conjTranspose, kron2_conjTranspose,
      proj0_conjTranspose, proj1_conjTranspose]

/-- Multiplication of two "block-diag-second" forms collapses cross-terms
    via projector orthogonality. -/
lemma block_diag_second_mul (A B C D : Mat2) :
    (kron2 A proj0 + kron2 B proj1) * (kron2 C proj0 + kron2 D proj1) =
      kron2 (A * C) proj0 + kron2 (B * D) proj1 := by
  rw [add_mul, mul_add, mul_add,
      kron2_mul, kron2_mul, kron2_mul, kron2_mul,
      proj0_sq, proj0_mul_proj1, proj1_mul_proj0, proj1_sq,
      kron2_zero_right, kron2_zero_right, add_zero, zero_add]

/-- `kron2 1 proj0 + kron2 1 proj1 = 1` (dual of `kron2_proj0_one_add_kron2_proj1_one`). -/
lemma kron2_one_proj0_add_kron2_one_proj1 :
    kron2 (1 : Mat2) proj0 + kron2 (1 : Mat2) proj1 = (1 : Mat4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kron2, proj0, proj1, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]

/-- A "controlled-C" gate of the form `kron2 1 proj0 + kron2 P proj1` is
    unitary when P is. -/
lemma controlled_C_unitary {P : Mat2} (hP : IsUnitary2 P) :
    IsUnitary4 (kron2 1 proj0 + kron2 P proj1) := by
  unfold IsUnitary4
  rw [block_diag_second_conjT, block_diag_second_mul]
  rw [Matrix.conjTranspose_one]
  unfold IsUnitary2 at hP
  rw [hP, one_mul]
  exact kron2_one_proj0_add_kron2_one_proj1

set_option maxHeartbeats 400000 in
-- fin_cases × 4 + simp on 4-dim Vec2 state index pushes past default 200000.
/-- A "controlled-C" gate preserves states of the form `x ⊗ |0⟩` for any x.
    (When the C qubit is |0⟩, the gate acts as identity on the B qubit.) -/
lemma controlled_C_apply_xtensor0 (P : Mat2) (x : Vec1) :
    Mat4.apply (kron2 1 proj0 + kron2 P proj1) (tensor1_1 x ket0_1) =
      tensor1_1 x ket0_1 := by
  funext k
  fin_cases k <;>
    simp [Mat4.apply, kron2, proj0, proj1, tensor1_1, ket0_1,
          Matrix.add_apply, Matrix.of_apply, Matrix.one_apply,
          Fin.sum_univ_four]

/-- For any unit qubit ψ, there exists a 2×2 unitary R that rotates ψ to |0⟩.
    Construction: `R = !![conj(ψ_0), conj(ψ_1); -ψ_1, ψ_0]` is unitary by
    direct computation, and R·ψ = (|ψ_0|² + |ψ_1|², 0) = (1, 0) = ket0_1. -/
lemma exists_unitary_rotate_to_ket0 {ψ : Vec1} (hψ : IsQubit1 ψ) :
    ∃ R : Mat2, IsUnitary2 R ∧ Mat2.apply R ψ = ket0_1 := by
  refine ⟨Matrix.of !![starRingEnd ℂ (ψ 0), starRingEnd ℂ (ψ 1);
                       -ψ 1, ψ 0], ?_, ?_⟩
  · unfold IsUnitary2
    unfold IsQubit1 normSqVec1 at hψ
    rw [Fin.sum_univ_two] at hψ
    -- hψ : Complex.normSq (ψ 0) + Complex.normSq (ψ 1) = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.conjTranspose_apply, Matrix.mul_apply,
            Fin.sum_univ_two]
    · -- (0,0): conj(conj ψ_0) * conj ψ_0 + (-(- ψ 1)) * (-ψ 1)
      -- Trust simp + ring to handle the algebra.
      have : ψ 0 * starRingEnd ℂ (ψ 0) = (Complex.normSq (ψ 0) : ℂ) :=
        Complex.mul_conj _
      have h1 : ψ 1 * starRingEnd ℂ (ψ 1) = (Complex.normSq (ψ 1) : ℂ) :=
        Complex.mul_conj _
      have h_sum : (Complex.normSq (ψ 0) : ℂ) + (Complex.normSq (ψ 1) : ℂ) = 1 := by
        exact_mod_cast hψ
      linear_combination this + h1 + h_sum
    · -- (0,1) or similar
      ring
    · ring
    · have : ψ 0 * starRingEnd ℂ (ψ 0) = (Complex.normSq (ψ 0) : ℂ) :=
        Complex.mul_conj _
      have h1 : ψ 1 * starRingEnd ℂ (ψ 1) = (Complex.normSq (ψ 1) : ℂ) :=
        Complex.mul_conj _
      have h_sum : (Complex.normSq (ψ 0) : ℂ) + (Complex.normSq (ψ 1) : ℂ) = 1 := by
        exact_mod_cast hψ
      linear_combination this + h1 + h_sum
  · funext i
    fin_cases i <;>
      simp [Mat2.apply, Matrix.of_apply, ket0_1, Fin.sum_univ_two]
    · -- (0): conj(ψ 0) * ψ 0 + conj(ψ 1) * ψ 1 = 1
      unfold IsQubit1 normSqVec1 at hψ
      rw [Fin.sum_univ_two] at hψ
      have h0 : starRingEnd ℂ (ψ 0) * ψ 0 = (Complex.normSq (ψ 0) : ℂ) := by
        rw [mul_comm, Complex.mul_conj]
      have h1 : starRingEnd ℂ (ψ 1) * ψ 1 = (Complex.normSq (ψ 1) : ℂ) := by
        rw [mul_comm, Complex.mul_conj]
      have h_sum : (Complex.normSq (ψ 0) : ℂ) + (Complex.normSq (ψ 1) : ℂ) = 1 := by
        exact_mod_cast hψ
      linear_combination h0 + h1 + h_sum
    · ring

/-- Inverse rotation: for any unit qubit ψ, there exists a 2×2 unitary R that
    rotates `|0⟩` to ψ. (Dagger of `exists_unitary_rotate_to_ket0`.) -/
lemma exists_unitary_rotate_from_ket0 {ψ : Vec1} (hψ : IsQubit1 ψ) :
    ∃ R : Mat2, IsUnitary2 R ∧ Mat2.apply R ket0_1 = ψ := by
  obtain ⟨R, hR, hRψ⟩ := exists_unitary_rotate_to_ket0 hψ
  exact ⟨R.conjTranspose, isUnitary2_conjTranspose hR,
         Mat2_apply_conjTranspose_ket0_of_rotate hR hRψ⟩

/-- 2-qubit rotation: for unit qubits a, b, there exists a 4×4 unitary R that
    rotates `|0⟩⊗|0⟩` to `a⊗b`. Construction: `R = kron2 R_a R_b` where R_a, R_b
    are 1-qubit rotations from `|0⟩` to a, b. -/
lemma exists_unitary_kron2_rotate_from_ket00 {a b : Vec1}
    (ha : IsQubit1 a) (hb : IsQubit1 b) :
    ∃ R : Mat4, IsUnitary4 R ∧
      Mat4.apply R (tensor1_1 ket0_1 ket0_1) = tensor1_1 a b := by
  obtain ⟨Ra, hRa, hRaApp⟩ := exists_unitary_rotate_from_ket0 ha
  obtain ⟨Rb, hRb, hRbApp⟩ := exists_unitary_rotate_from_ket0 hb
  refine ⟨kron2 Ra Rb, isUnitary4_kron2 hRa hRb, ?_⟩
  rw [kron2_apply_tensor1_1, hRaApp, hRbApp]

/-- The complex scalar 1/√2 is nonzero with |s|² = 1/2.
    Used to construct a unit-qubit witness with both components nonzero. -/
lemma sqrt2_inv_ne_zero : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ≠ 0 := by
  rw [Complex.ofReal_ne_zero]
  exact inv_ne_zero (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'

/-- The complex norm squared of 1/√2 (cast to ℂ) equals 1/2. -/
lemma sqrt2_inv_normSq :
    Complex.normSq (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1/2 := by
  rw [Complex.normSq_ofReal]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
  rw [show ((Real.sqrt 2)⁻¹ : ℝ) * ((Real.sqrt 2)⁻¹ : ℝ)
          = (Real.sqrt 2 * Real.sqrt 2)⁻¹ from (mul_inv _ _).symm, h2]
  norm_num

/-- **Key linear-algebra fact**: if `a₀⊗b₀ + a₁⊗b₁ = c⊗d`, then either
    `a₀, a₁` are linearly dependent or `b₀, b₁` are linearly dependent.

    Proof: viewed as a 2×2 matrix `M[i,j] = a₀_i b₀_j + a₁_i b₁_j`, we have
    det(M) = (a₀_0 a₁_1 - a₀_1 a₁_0)(b₀_0 b₁_1 - b₀_1 b₁_0) (ring identity).
    But M = c⊗d has det zero (rank-1). Hence one of the two factors is zero,
    which is exactly `linearDep1` for that pair. -/
lemma tensor_sum_eq_tensor_linDep
    (a₀ b₀ a₁ b₁ c d : Vec1)
    (h : tensor1_1 a₀ b₀ + tensor1_1 a₁ b₁ = tensor1_1 c d) :
    linearDep1 a₀ a₁ ∨ linearDep1 b₀ b₁ := by
  -- Extract the four matrix entries by evaluating at indices 0..3.
  have h00 : a₀ 0 * b₀ 0 + a₁ 0 * b₁ 0 = c 0 * d 0 := by
    have := congr_fun h (0 : Fin 4)
    simpa [tensor1_1, Pi.add_apply] using this
  have h01 : a₀ 0 * b₀ 1 + a₁ 0 * b₁ 1 = c 0 * d 1 := by
    have := congr_fun h (1 : Fin 4)
    simpa [tensor1_1, Pi.add_apply] using this
  have h10 : a₀ 1 * b₀ 0 + a₁ 1 * b₁ 0 = c 1 * d 0 := by
    have := congr_fun h (2 : Fin 4)
    simpa [tensor1_1, Pi.add_apply] using this
  have h11 : a₀ 1 * b₀ 1 + a₁ 1 * b₁ 1 = c 1 * d 1 := by
    have := congr_fun h (3 : Fin 4)
    simpa [tensor1_1, Pi.add_apply] using this
  -- Determinant identity: M00·M11 - M01·M10 factors as
  -- (a₀_0 a₁_1 - a₀_1 a₁_0) * (b₀_0 b₁_1 - b₀_1 b₁_0).
  -- For c⊗d, this determinant is 0.
  have key : (a₀ 0 * a₁ 1 - a₀ 1 * a₁ 0) * (b₀ 0 * b₁ 1 - b₀ 1 * b₁ 0) = 0 := by
    have lhs_eq :
        (a₀ 0 * b₀ 0 + a₁ 0 * b₁ 0) * (a₀ 1 * b₀ 1 + a₁ 1 * b₁ 1)
        - (a₀ 0 * b₀ 1 + a₁ 0 * b₁ 1) * (a₀ 1 * b₀ 0 + a₁ 1 * b₁ 0)
        = (a₀ 0 * a₁ 1 - a₀ 1 * a₁ 0) * (b₀ 0 * b₁ 1 - b₀ 1 * b₁ 0) := by ring
    have rhs_zero : c 0 * d 0 * (c 1 * d 1) - c 0 * d 1 * (c 1 * d 0) = 0 := by ring
    rw [← lhs_eq, h00, h01, h10, h11]
    exact rhs_zero
  unfold linearDep1
  rcases mul_eq_zero.mp key with hL | hR
  · left; linear_combination hL
  · right; linear_combination hR

/-- If `linearDep1 a b` and `a ≠ 0`, then `b = λ • a` for some `λ : ℂ`.
    Concretely: `λ = b 0 / a 0` if `a 0 ≠ 0`; else `λ = b 1 / a 1`. -/
lemma linDep_to_scalar
    {a b : Vec1} (h_dep : linearDep1 a b) (ha : a ≠ 0) :
    ∃ lam : ℂ, b = lam • a := by
  unfold linearDep1 at h_dep
  by_cases ha0 : a 0 = 0
  · -- a 0 = 0 case: must have a 1 ≠ 0; from linDep, b 0 = 0; take λ = b 1 / a 1.
    have ha1 : a 1 ≠ 0 := by
      intro h
      apply ha
      funext i; fin_cases i <;> assumption
    have hb0 : b 0 = 0 := by
      rw [ha0, zero_mul, eq_comm, mul_eq_zero] at h_dep
      exact h_dep.resolve_left ha1
    refine ⟨b 1 / a 1, ?_⟩
    funext i
    fin_cases i
    · simp [Pi.smul_apply, smul_eq_mul, hb0, ha0]
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact (div_mul_cancel₀ _ ha1).symm
  · -- a 0 ≠ 0 case: take λ = b 0 / a 0; derive b 1 from linDep.
    refine ⟨b 0 / a 0, ?_⟩
    funext i
    fin_cases i
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact (div_mul_cancel₀ _ ha0).symm
    · simp [Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination h_dep

/-- For unitary V, if `V·(ket_k⊗|0⟩) = a⊗b` (k = 0 or 1), then both `a, b ≠ 0`.
    Proof: V preserves unit norm, so V·|k0⟩ ≠ 0; tensor product is zero iff
    one factor is zero. -/
lemma a_b_nonzero_of_unitary_ket0
    {V : Mat4} (hV : IsUnitary4 V) {a b : Vec1}
    (h : Mat4.apply V (tensor1_1 ket0_1 ket0_1) = tensor1_1 a b) :
    a ≠ 0 ∧ b ≠ 0 := by
  have h_unit : IsQubit2 (Mat4.apply V (tensor1_1 ket0_1 ket0_1)) :=
    IsQubit2_apply_unitary hV IsQubit2_ket00
  rw [h] at h_unit
  unfold IsQubit2 at h_unit
  rw [normSqVec2_tensor1_1] at h_unit
  -- h_unit : normSqVec1 a * normSqVec1 b = 1
  refine ⟨?_, ?_⟩
  · intro ha
    have : normSqVec1 a = 0 := by
      rw [ha]; unfold normSqVec1; simp
    rw [this, zero_mul] at h_unit
    exact one_ne_zero h_unit.symm
  · intro hb
    have : normSqVec1 b = 0 := by
      rw [hb]; unfold normSqVec1; simp
    rw [this, mul_zero] at h_unit
    exact one_ne_zero h_unit.symm

/-- Symmetric version for `V·(ket1⊗|0⟩)`. -/
private lemma a_b_nonzero_of_unitary_ket1
    {V : Mat4} (hV : IsUnitary4 V) {a b : Vec1}
    (h : Mat4.apply V (tensor1_1 ket1_1 ket0_1) = tensor1_1 a b) :
    a ≠ 0 ∧ b ≠ 0 := by
  have h_unit : IsQubit2 (Mat4.apply V (tensor1_1 ket1_1 ket0_1)) :=
    IsQubit2_apply_unitary hV IsQubit2_ket10
  rw [h] at h_unit
  unfold IsQubit2 at h_unit
  rw [normSqVec2_tensor1_1] at h_unit
  refine ⟨?_, ?_⟩
  · intro ha
    have : normSqVec1 a = 0 := by
      rw [ha]; unfold normSqVec1; simp
    rw [this, zero_mul] at h_unit
    exact one_ne_zero h_unit.symm
  · intro hb
    have : normSqVec1 b = 0 := by
      rw [hb]; unfold normSqVec1; simp
    rw [this, mul_zero] at h_unit
    exact one_ne_zero h_unit.symm

/-- If V·(x⊗|0⟩) is a tensor for every unit qubit x, then either (a₀, a₁) or
    (b₀, b₁) are linearly dependent (where a_k⊗b_k = V·(ket_k⊗|0⟩)). -/
lemma all_x_tensor_implies_linDep
    {V : Mat4} {a₀ b₀ a₁ b₁ : Vec1}
    (h₀ : Mat4.apply V (tensor1_1 ket0_1 ket0_1) = tensor1_1 a₀ b₀)
    (h₁ : Mat4.apply V (tensor1_1 ket1_1 ket0_1) = tensor1_1 a₁ b₁)
    (h_tensor : ∀ x : Vec1, IsQubit1 x →
        IsTensor (Mat4.apply V (tensor1_1 x ket0_1))) :
    linearDep1 a₀ a₁ ∨ linearDep1 b₀ b₁ := by
  -- Pick x : Vec1 with x 0 = x 1 = 1/√2 (unit qubit, both components nonzero).
  set s : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) with hs_def
  have hs_ne : s ≠ 0 := sqrt2_inv_ne_zero
  have hs_sq : Complex.normSq s = 1/2 := sqrt2_inv_normSq
  let x : Vec1 := fun _ => s
  have hx_qubit : IsQubit1 x := by
    unfold IsQubit1 normSqVec1
    rw [Fin.sum_univ_two]
    change Complex.normSq s + Complex.normSq s = 1
    rw [hs_sq]; norm_num
  -- Apply h_tensor to obtain (c, d) such that V·(x⊗|0⟩) = c⊗d.
  obtain ⟨c, d, hc⟩ := h_tensor x hx_qubit
  -- Expand V·(x⊗|0⟩) using the basis decomposition.
  -- Since x 0 = x 1 = s by definition, the result is s•(a₀⊗b₀) + s•(a₁⊗b₁).
  have hexpand : Mat4.apply V (tensor1_1 x ket0_1) =
      tensor1_1 (s • a₀) b₀ + tensor1_1 (s • a₁) b₁ := by
    have h := V_apply_xtensor0_decomp V a₀ b₀ a₁ b₁ h₀ h₁ x
    change Mat4.apply V (tensor1_1 x ket0_1) =
      tensor1_1 (s • a₀) b₀ + tensor1_1 (s • a₁) b₁
    rw [h, ← tensor1_1_smul_left, ← tensor1_1_smul_left]
  rw [hc] at hexpand
  -- hexpand : tensor1_1 c d = tensor1_1 (s • a₀) b₀ + tensor1_1 (s • a₁) b₁
  rcases tensor_sum_eq_tensor_linDep (s • a₀) b₀ (s • a₁) b₁ c d hexpand.symm with hL | hR
  · -- linearDep1 (s • a₀) (s • a₁) reduces to linearDep1 a₀ a₁ since s ≠ 0.
    left
    unfold linearDep1 at hL ⊢
    simp only [Pi.smul_apply, smul_eq_mul] at hL
    have hs2 : s * s ≠ 0 := mul_ne_zero hs_ne hs_ne
    have key : s * s * (a₀ 0 * a₁ 1 - a₀ 1 * a₁ 0) = 0 := by linear_combination hL
    have h0 : a₀ 0 * a₁ 1 - a₀ 1 * a₁ 0 = 0 :=
      (mul_eq_zero.mp key).resolve_left hs2
    linear_combination h0
  · right; exact hR

theorem py24_lemma_6_1 (V : Mat4) (hV : IsUnitary4 V) :
    (∃ x : Vec1, IsQubit1 x ∧ IsEntangled (Mat4.apply V (tensor1_1 x ket0_1))) ∨
    (∃ ψ : Vec1, IsQubit1 ψ ∧ ∀ x : Vec1, IsQubit1 x →
      ∃ z : Vec1, Mat4.apply V (tensor1_1 x ket0_1) = tensor1_1 z ψ) ∨
    (∃ ψ : Vec1, IsQubit1 ψ ∧ ∀ x : Vec1, IsQubit1 x →
      ∃ z : Vec1, Mat4.apply V (tensor1_1 x ket0_1) = tensor1_1 ψ z) := by
  by_cases h : ∃ x : Vec1, IsQubit1 x ∧ IsEntangled (Mat4.apply V (tensor1_1 x ket0_1))
  · -- Case 1: there exists an entangled output.
    left; exact h
  · right
    push_neg at h
    have h_tensor : ∀ x : Vec1, IsQubit1 x →
        IsTensor (Mat4.apply V (tensor1_1 x ket0_1)) := by
      intro x hx
      exact (not_isEntangled_iff_isTensor _).mp (h x hx)
    obtain ⟨a₀, b₀, h₀⟩ := h_tensor ket0_1 IsQubit1_ket0
    obtain ⟨a₁, b₁, h₁⟩ := h_tensor ket1_1 IsQubit1_ket1
    rcases all_x_tensor_implies_linDep h₀ h₁ h_tensor with hLin_a | hLin_b
    · -- linearDep1 a₀ a₁ → case 3 (first factor fixed): ψ = unit_normalize a₀.
      right
      obtain ⟨ha_ne, _⟩ := a_b_nonzero_of_unitary_ket0 hV h₀
      obtain ⟨lam, hlam⟩ := linDep_to_scalar hLin_a ha_ne
      refine ⟨unit_normalize_vec1 a₀, isQubit1_unit_normalize_vec1 a₀ ha_ne, ?_⟩
      intro x _hx
      refine ⟨((Real.sqrt (normSqVec1 a₀) : ℝ) : ℂ) •
                (x 0 • b₀ + (x 1 * lam) • b₁), ?_⟩
      rw [V_apply_xtensor0_decomp V a₀ b₀ a₁ b₁ h₀ h₁ x, hlam,
          tensor1_1_smul_left, smul_smul,
          ← tensor1_1_smul_right, ← tensor1_1_smul_right,
          ← tensor1_1_add_right]
      -- Now LHS: tensor1_1 a₀ (x 0 • b₀ + (x 1 * lam) • b₁)
      -- Rewrite the bare a₀ on LHS only (avoid cyclic re-write in RHS).
      conv_lhs => rw [← smul_unit_normalize_vec1 a₀ ha_ne]
      rw [tensor1_1_smul_left, ← tensor1_1_smul_right]
    · -- linearDep1 b₀ b₁ → case 2 (second factor fixed): ψ = unit_normalize b₀.
      left
      obtain ⟨_, hb_ne⟩ := a_b_nonzero_of_unitary_ket0 hV h₀
      obtain ⟨mu, hmu⟩ := linDep_to_scalar hLin_b hb_ne
      refine ⟨unit_normalize_vec1 b₀, isQubit1_unit_normalize_vec1 b₀ hb_ne, ?_⟩
      intro x _hx
      refine ⟨((Real.sqrt (normSqVec1 b₀) : ℝ) : ℂ) •
                (x 0 • a₀ + (x 1 * mu) • a₁), ?_⟩
      rw [V_apply_xtensor0_decomp V a₀ b₀ a₁ b₁ h₀ h₁ x, hmu,
          tensor1_1_smul_right, smul_smul,
          ← tensor1_1_smul_left, ← tensor1_1_smul_left,
          ← tensor1_1_add_left]
      conv_lhs => rw [← smul_unit_normalize_vec1 b₀ hb_ne]
      rw [tensor1_1_smul_right, ← tensor1_1_smul_left]

/-! ## PY24 Lemma 6.4 (HP A.9) — CC(Diag) characterization

For complex numbers u₀, u₁ with |u₀| = |u₁| = 1:
  ∃ U₁..U₄ 2-qubit unitaries: U₁_AC · U₂_BC · U₃_AC · U₄_BC = CC(Diag(u₀, u₁))
  ↔  u₀ = u₁  OR  u₀ · u₁ = 1.

Note: CC(Diag(u₀, u₁)) = Diag(1, 1, 1, 1, 1, 1, u₀, u₁) — a 3-qubit diagonal gate.
Cited by HP for fourGate_BC_AC_BC_AC_implies_S4_or_S5 (Step 130). -/

set_option maxHeartbeats 800000 in
-- ext + fin_cases × 8 × 8 = 64 cases × simp on embedAB / Matrix.diagonal definitions.
/-- Helper: `embedAB Diag(1,1,1,u)` equals the 8-dim diagonal Diag(1,1,1,1,1,1,u,u).
    The phase u appears at indices 6 and 7 (i.e., A=1, B=1, regardless of C). -/
lemma embedAB_diag_one_one_one_u (u : ℂ) :
    embedAB (Matrix.diagonal ![1, 1, 1, u]) =
    (Matrix.diagonal ![1, 1, 1, 1, 1, 1, u, u] : Mat8) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedAB, Matrix.diagonal, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Helper: `Matrix.diagonal ![1, u]` (2×2) is unitary when `|u|² = 1`.
    Used for 3.3 (⇐) Case 2 construction (P := Diag(1, u₀)). -/
lemma isUnitary2_diag_one_u (u : ℂ) (hu : Complex.normSq u = 1) :
    IsUnitary2 (Matrix.diagonal ![1, u]) := by
  unfold IsUnitary2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Matrix.diagonal, Matrix.mul_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show starRingEnd ℂ u * u = (Complex.normSq u : ℂ) from by
        rw [mul_comm]; exact Complex.mul_conj u]
  exact_mod_cast hu

/-- Helper: `Matrix.diagonal ![1,1,1,u]` is unitary when `|u|² = 1`. -/
lemma isUnitary4_diag_one_one_one_u (u : ℂ) (hu : Complex.normSq u = 1) :
    IsUnitary4 (Matrix.diagonal ![1, 1, 1, u]) := by
  unfold IsUnitary4
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Matrix.diagonal, Matrix.mul_apply,
          Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one]
  -- Remaining goal: starRingEnd ℂ u * u = 1.
  rw [show starRingEnd ℂ u * u = (Complex.normSq u : ℂ) from by
        rw [mul_comm]; exact Complex.mul_conj u]
  exact_mod_cast hu

/-- **6.4 constructive direction (case u₀ = u₁)**: explicit gate sequence
    achieving Diag(1,1,1,1,1,1,u,u). Construction: U₁=I, U₂=SWAP_4, U₃=Diag(1,1,1,u),
    U₄=SWAP_4. Then the chain conjugates `embedAC Diag(1,1,1,u)` by SWAP_BC twice
    yielding `embedAB Diag(1,1,1,u) = Diag(1,1,1,1,1,1,u,u)`. -/
lemma py24_lemma_6_4_construct_u_eq (u : ℂ) (hu : Complex.normSq u = 1) :
    ∃ U₁ U₂ U₃ U₄ : Mat4, IsUnitary4 U₁ ∧ IsUnitary4 U₂ ∧ IsUnitary4 U₃ ∧ IsUnitary4 U₄ ∧
      embedAC U₁ * embedBC U₂ * embedAC U₃ * embedBC U₄ =
      Matrix.diagonal ![1, 1, 1, 1, 1, 1, u, u] := by
  refine ⟨1, SWAP_4, Matrix.diagonal ![1, 1, 1, u], SWAP_4, ?_, ?_, ?_, ?_, ?_⟩
  · unfold IsUnitary4; rw [Matrix.conjTranspose_one, Matrix.one_mul]
  · exact isUnitary4_SWAP_4
  · exact isUnitary4_diag_one_one_one_u u hu
  · exact isUnitary4_SWAP_4
  · -- The chain identity.
    rw [embedAC_one, one_mul]
    rw [show embedBC SWAP_4 = SWAP_BC from SWAP_BC_eq_embedBC.symm]
    rw [swap_bc_embedAC]
    exact embedAB_diag_one_one_one_u u

/-- Local 4×4 CNOT (first qubit controls second). For 6.4's u₀·u₁=1 case. -/
def CNOT_4_local : Mat4 :=
  Matrix.of fun (i j : Fin 4) =>
    match i, j with
    | 0, 0 => (1 : ℂ) | 1, 1 => 1 | 2, 3 => 1 | 3, 2 => 1 | _, _ => 0

/-- Helper: CNOT_4_local is unitary. -/
lemma isUnitary4_CNOT_4_local : IsUnitary4 CNOT_4_local := by
  unfold IsUnitary4 CNOT_4_local
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Matrix.mul_apply, Matrix.of_apply,
          Fin.sum_univ_four]

set_option maxHeartbeats 1600000 in
-- 4-fold matrix product expansion via 64 fin_cases + simp on Matrix.mul_apply.
/-- Helper: chain product for u₀·u₁=1 case. Apply right-to-left:
    `CNOT_BC` permutes c↔c⊕b; `Diag(1,1,1,u₀)` on AC adds phase u₀ when (a,c)=(1,1);
    `CNOT_BC` permutes back; `Diag(1,1,1,u₁)` on AC adds phase u₁ when (a,c)=(1,1).
    Composition is diagonal Diag(1,1,1,1,1,u₀·u₁,u₀,u₁). -/
lemma chain_diag_CNOT_diag_CNOT (u₀ u₁ : ℂ) :
    embedAC (Matrix.diagonal ![1, 1, 1, u₁]) * embedBC CNOT_4_local *
      embedAC (Matrix.diagonal ![1, 1, 1, u₀]) * embedBC CNOT_4_local =
    (Matrix.diagonal ![1, 1, 1, 1, 1, u₀ * u₁, u₀, u₁] : Mat8) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [embedAC, embedBC, CNOT_4_local, Matrix.diagonal,
           Matrix.of_apply, Matrix.mul_apply,
           Fin.sum_univ_eight,
           Matrix.cons_val_zero, Matrix.cons_val_one]
     <;> ring)

/-- **6.4 constructive direction (case u₀·u₁ = 1)**: explicit gate sequence.
    Construction: U₁=Diag(1,1,1,u₁), U₂=CNOT, U₃=Diag(1,1,1,u₀), U₄=CNOT.
    Chain product = Diag(1,1,1,1,1, u₀·u₁, u₀, u₁); with u₀·u₁=1, this equals target. -/
lemma py24_lemma_6_4_construct_u_prod_inv (u₀ u₁ : ℂ)
    (hu₀ : Complex.normSq u₀ = 1) (hu₁ : Complex.normSq u₁ = 1) (h_prod : u₀ * u₁ = 1) :
    ∃ U₁ U₂ U₃ U₄ : Mat4, IsUnitary4 U₁ ∧ IsUnitary4 U₂ ∧ IsUnitary4 U₃ ∧ IsUnitary4 U₄ ∧
      embedAC U₁ * embedBC U₂ * embedAC U₃ * embedBC U₄ =
      Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] := by
  refine ⟨Matrix.diagonal ![1, 1, 1, u₁], CNOT_4_local,
          Matrix.diagonal ![1, 1, 1, u₀], CNOT_4_local, ?_, ?_, ?_, ?_, ?_⟩
  · exact isUnitary4_diag_one_one_one_u u₁ hu₁
  · exact isUnitary4_CNOT_4_local
  · exact isUnitary4_diag_one_one_one_u u₀ hu₀
  · exact isUnitary4_CNOT_4_local
  · rw [chain_diag_CNOT_diag_CNOT, h_prod]

set_option maxHeartbeats 800000 in
-- funext k + fin_cases × 8 + simp on Mat8.apply / embedAC / tensors.
/-- **Helper for A.28**: when V|00⟩=|00⟩, `embedAC V` acts as identity on
    states of the form `|0⟩_A ⊗ b_B ⊗ |0⟩_C`. The (A,C) part is preserved
    since V·(ket0⊗ket0) = ket0⊗ket0; B is a passive bystander. -/
lemma embedAC_apply_ket0_b_ket0_when_V_fixes_ket00
    (V : Mat4) (b : Vec1)
    (hV : Mat4.apply V (tensor1_1 ket0_1 ket0_1) = tensor1_1 ket0_1 ket0_1) :
    Mat8.apply (embedAC V) (tensor1_2 ket0_1 (tensor1_1 b ket0_1)) =
    tensor1_2 ket0_1 (tensor1_1 b ket0_1) := by
  -- Extract column 0 of V from hV: V·e_0 = e_0 means V's first column is (1,0,0,0).
  have hV00 : V 0 0 = 1 := by
    have h := congrFun hV 0
    simp [Mat4.apply, tensor1_1, ket0_1, Fin.sum_univ_four] at h; exact h
  have hV10 : V 1 0 = 0 := by
    have h := congrFun hV 1
    simp [Mat4.apply, tensor1_1, ket0_1, Fin.sum_univ_four] at h; exact h
  have hV20 : V 2 0 = 0 := by
    have h := congrFun hV 2
    simp [Mat4.apply, tensor1_1, ket0_1, Fin.sum_univ_four] at h; exact h
  have hV30 : V 3 0 = 0 := by
    have h := congrFun hV 3
    simp [Mat4.apply, tensor1_1, ket0_1, Fin.sum_univ_four] at h; exact h
  funext k
  fin_cases k <;>
    simp [Mat8.apply, embedAC, tensor1_2, tensor1_1, ket0_1,
          Matrix.of_apply, Fin.sum_univ_eight,
          hV00, hV10, hV20, hV30]

/-! ## PY24 Lemma A.28 — chain manipulation under V₃|00⟩=|00⟩

For V₁,V₂,V₃,V₄ unitaries and Mat8 D acting as identity on the |0⟩_A
subspace, if V₁_AC·V₂_BC·V₃_AC·V₄_BC = D and V₃|00⟩ = |00⟩, then for any
qubit x: V₁_AC · V₂_BC · (|0⟩_A ⊗ x_B ⊗ |0⟩_C) = V₄†_BC · (|0⟩_A ⊗ x_B ⊗ |0⟩_C). -/

/-- **Special case of Lemma 3.2 needed for Lemma 4.2's case 2**: if `kron2 P Q`
    equals the specific diagonal `Diag(1,1,1,u)`, then u = 1.

    This is a strict specialization of PY24 Lemma 3.2 (which is in terms of
    eigenvalue multisets). The matrix-level form is what 4.2's proof actually
    uses, and avoids needing the Spectral Theorem. -/
lemma kron2_eq_diag_three_ones_u_implies_u_eq_one
    {P Q : Mat2} {u : ℂ}
    (h : kron2 P Q = (Matrix.diagonal ![1, 1, 1, u] : Mat4)) :
    u = 1 := by
  have h00 : P 0 0 * Q 0 0 = 1 := by
    have := congrFun (congrFun h 0) 0
    simpa [kron2, Matrix.diagonal, Matrix.of_apply] using this
  have h01 : P 0 0 * Q 1 1 = 1 := by
    have := congrFun (congrFun h 1) 1
    simpa [kron2, Matrix.diagonal, Matrix.of_apply,
           Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using this
  have h10 : P 1 1 * Q 0 0 = 1 := by
    have := congrFun (congrFun h 2) 2
    simpa [kron2, Matrix.diagonal, Matrix.of_apply,
           Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using this
  have h11 : P 1 1 * Q 1 1 = u := by
    have := congrFun (congrFun h 3) 3
    simpa [kron2, Matrix.diagonal, Matrix.of_apply,
           Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using this
  have hP00_ne : P 0 0 ≠ 0 := by
    intro hP0; rw [hP0, zero_mul] at h00; exact zero_ne_one h00
  have hQ00_ne : Q 0 0 ≠ 0 := by
    intro hQ0; rw [hQ0, mul_zero] at h00; exact zero_ne_one h00
  have hQ_eq : Q 0 0 = Q 1 1 :=
    mul_left_cancel₀ hP00_ne (h00.trans h01.symm)
  have hP_eq : P 0 0 = P 1 1 :=
    mul_right_cancel₀ hQ00_ne (h00.trans h10.symm)
  rw [← hP_eq, ← hQ_eq, h00] at h11
  exact h11.symm

/-- **PY24 Lemma A.8**: For unitary Q : Mat2 with |φ⟩ = Q|0⟩ and |ψ⟩ = Q|1⟩,
    we have |φ⟩⟨φ| + |ψ⟩⟨ψ| = I.

    In matrix form: Q · proj0 · Q† + Q · proj1 · Q† = I, since |Q|0⟩⟩⟨Q|0⟩|
    equals Q · proj0 · Q† (and similarly for |1⟩). The proof factors out Q on
    both sides and uses proj0 + proj1 = I. -/
lemma py24_lemma_A_8 (Q : Mat2) (hQ : IsUnitary2 Q) :
    Q * proj0 * Q.conjTranspose + Q * proj1 * Q.conjTranspose = (1 : Mat2) := by
  have h_factor :
      Q * proj0 * Q.conjTranspose + Q * proj1 * Q.conjTranspose
      = Q * (proj0 + proj1) * Q.conjTranspose := by noncomm_ring
  rw [h_factor, proj0_add_proj1, mul_one]
  exact mul_eq_one_comm.mp hQ

/-- Helper: kron3 distributes over addition in the third argument. -/
lemma kron3_add_third (A B C₁ C₂ : Mat2) :
    kron3 A B (C₁ + C₂) = kron3 A B C₁ + kron3 A B C₂ := by
  ext i j
  simp [kron3, Matrix.add_apply, Matrix.of_apply]; ring

/-- Helper: the all-ones diagonal Mat8 equals the identity. -/
lemma diagonal_eight_ones_eq_one :
    (Matrix.diagonal ![1, 1, 1, 1, 1, 1, 1, 1] : Mat8) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **PY24 Lemma 4.2 (⇐) direction**: when u₀ = u₁ = 1, the equation
    `I⊗I⊗|φ⟩⟨φ| + P₀⊗P₁⊗|ψ⟩⟨ψ| = CC(Diag(u₀,u₁))` is solvable by
    P₀ = P₁ = I. -/
lemma py24_lemma_4_2_backward (Q : Mat2) (hQ : IsUnitary2 Q) :
    ∃ P₀ P₁ : Mat2, IsUnitary2 P₀ ∧ IsUnitary2 P₁ ∧
      kron3 1 1 (Q * proj0 * Q.conjTranspose) +
      kron3 P₀ P₁ (Q * proj1 * Q.conjTranspose) =
      (Matrix.diagonal ![1, 1, 1, 1, 1, 1, 1, 1] : Mat8) := by
  refine ⟨1, 1, isUnitary2_one, isUnitary2_one, ?_⟩
  rw [show kron3 (1:Mat2) (1:Mat2) (Q * proj0 * Q.conjTranspose) +
          kron3 1 1 (Q * proj1 * Q.conjTranspose) =
          kron3 1 1 (Q * proj0 * Q.conjTranspose + Q * proj1 * Q.conjTranspose)
      from (kron3_add_third _ _ _ _).symm]
  rw [py24_lemma_A_8 Q hQ]
  rw [show kron3 (1:Mat2) (1:Mat2) (1:Mat2) = (singleQubitLayer I₂ I₂ I₂ : Mat8) from rfl]
  rw [singleQubitLayer_one]
  exact diagonal_eight_ones_eq_one.symm

/- **PY24 Lemma 4.2 (⇒) — TODO**. Forward direction does case analysis on
    Q·|1⟩ = (a, b). Helpers below build toward Case 2 (a=0). -/

/-- Helper: when Q is unitary and Q's (0,1) entry is zero, then Q·proj1·Q† = proj1.
    (Q's column 1 is (0, Q_{1,1}) with |Q_{1,1}|² = 1, so the rank-1 projector
    onto Q's column 1 equals proj1.) -/
lemma Q_proj1_Q_dagger_eq_proj1_when_Q01_zero
    (Q : Mat2) (hQ : IsUnitary2 Q) (h_a_zero : Q 0 1 = 0) :
    Q * proj1 * Q.conjTranspose = proj1 := by
  unfold IsUnitary2 at hQ
  have h_Q11_norm : starRingEnd ℂ (Q 1 1) * Q 1 1 = 1 := by
    have h := congrFun (congrFun hQ 1) 1
    simp [Matrix.conjTranspose_apply, Matrix.mul_apply,
          Fin.sum_univ_two] at h
    rw [h_a_zero, map_zero, zero_mul, zero_add] at h
    exact h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [proj1, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
          Fin.sum_univ_two, h_a_zero]
  rw [mul_comm]; exact h_Q11_norm

/-- Corollary of A.8 + helper: when Q_{0,1}=0, also Q·proj0·Q† = proj0. -/
lemma Q_proj0_Q_dagger_eq_proj0_when_Q01_zero
    (Q : Mat2) (hQ : IsUnitary2 Q) (h_a_zero : Q 0 1 = 0) :
    Q * proj0 * Q.conjTranspose = proj0 := by
  have h_A8 := py24_lemma_A_8 Q hQ
  have h_proj1 := Q_proj1_Q_dagger_eq_proj1_when_Q01_zero Q hQ h_a_zero
  have h_decomp : Q * proj0 * Q.conjTranspose = 1 - Q * proj1 * Q.conjTranspose :=
    eq_sub_of_add_eq h_A8
  rw [h_decomp, h_proj1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [proj0, proj1, Matrix.sub_apply, Matrix.of_apply]

/- **PY24 Lemma 4.2 (⇒) Case 2 (Q_{0,1}=0)**: u₀ = u₁ = 1.
    Idea: substitute Q·proj0·Q†=proj0 and Q·proj1·Q†=proj1; entry (6,6) gives
    u₀=1; restriction to c=1 subspace gives kron2 P₀ P₁ = Diag(1,1,1,u₁); apply
    `kron2_eq_diag_three_ones_u_implies_u_eq_one` to get u₁=1.

    Below: u₀=1 part is proved (clean entry comparison). The u₁=1 part is TODO. -/

set_option maxHeartbeats 800000 in
-- 8×8 entry comparison via fin_cases × 8 × 8 + simp.
/-- **PY24 Lemma 4.2 (⇒) Case 2 — partial: u₀ = 1 alone**: from the equation
    + Q_{0,1}=0, derive u₀ = 1. -/
lemma py24_lemma_4_2_forward_case_Q01_zero_u0_eq_one
    (Q : Mat2) (hQ : IsUnitary2 Q) (u₀ u₁ : ℂ)
    (P₀ P₁ : Mat2)
    (h_Q01_zero : Q 0 1 = 0)
    (h : kron3 1 1 (Q * proj0 * Q.conjTranspose) +
         kron3 P₀ P₁ (Q * proj1 * Q.conjTranspose) =
         (Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] : Mat8)) :
    u₀ = 1 := by
  rw [Q_proj0_Q_dagger_eq_proj0_when_Q01_zero Q hQ h_Q01_zero,
      Q_proj1_Q_dagger_eq_proj1_when_Q01_zero Q hQ h_Q01_zero] at h
  have h66 := congrFun (congrFun h ⟨6, by omega⟩) ⟨6, by omega⟩
  simp [kron3, proj0, proj1, decode3, Matrix.add_apply, Matrix.diagonal,
        Matrix.of_apply, Matrix.cons_val_zero] at h66
  exact h66.symm

/-- Helper: Q_{1,1}=0 + Q unitary forces Q_{0,0}=0 (anti-diagonal Q). -/
lemma Q00_eq_zero_when_Q11_zero
    (Q : Mat2) (hQ : IsUnitary2 Q) (h_b_zero : Q 1 1 = 0) :
    Q 0 0 = 0 := by
  unfold IsUnitary2 at hQ
  -- |Q_{0,1}|² = 1 from column 1 unit (Q†Q)_{1,1}=1.
  have h_Q01_norm : starRingEnd ℂ (Q 0 1) * Q 0 1 = 1 := by
    have h := congrFun (congrFun hQ 1) 1
    simp [Matrix.conjTranspose_apply, Matrix.mul_apply,
          Fin.sum_univ_two] at h
    rw [h_b_zero, map_zero, zero_mul, add_zero] at h
    exact h
  have h_Q01_ne : Q 0 1 ≠ 0 := by
    intro h_zero
    rw [h_zero, map_zero, zero_mul] at h_Q01_norm
    exact zero_ne_one h_Q01_norm
  -- Cols orthogonal: (Q†Q)_{1,0} = 0.
  have h_off : starRingEnd ℂ (Q 0 1) * Q 0 0 + starRingEnd ℂ (Q 1 1) * Q 1 0 = 0 := by
    have h := congrFun (congrFun hQ 1) 0
    simp [Matrix.conjTranspose_apply, Matrix.mul_apply,
          Fin.sum_univ_two] at h
    exact h
  rw [h_b_zero, map_zero, zero_mul, add_zero] at h_off
  have h_conj_Q01_ne : starRingEnd ℂ (Q 0 1) ≠ 0 := by
    intro h_z
    have : Q 0 1 = 0 := by
      have := congrArg (starRingEnd ℂ) h_z
      simpa using this
    exact h_Q01_ne this
  -- conj(Q_{0,1}) * Q_{0,0} = 0 with conj(Q_{0,1}) ≠ 0 ⟹ Q_{0,0} = 0.
  exact (mul_eq_zero.mp h_off).resolve_left h_conj_Q01_ne

/-- Helper: when Q_{1,1}=0 (Case 3, b=0), Q·proj0·Q† = proj1. -/
lemma Q_proj0_Q_dagger_eq_proj1_when_Q11_zero
    (Q : Mat2) (hQ : IsUnitary2 Q) (h_b_zero : Q 1 1 = 0) :
    Q * proj0 * Q.conjTranspose = proj1 := by
  have hQ00 : Q 0 0 = 0 := Q00_eq_zero_when_Q11_zero Q hQ h_b_zero
  have hQ_unit := hQ
  unfold IsUnitary2 at hQ_unit
  have h_Q10_norm : starRingEnd ℂ (Q 1 0) * Q 1 0 = 1 := by
    have h := congrFun (congrFun hQ_unit 0) 0
    simp [Matrix.conjTranspose_apply, Matrix.mul_apply,
          Fin.sum_univ_two] at h
    rw [hQ00, map_zero, zero_mul, zero_add] at h
    exact h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [proj0, proj1, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
          Fin.sum_univ_two, hQ00]
  rw [mul_comm]; exact h_Q10_norm

/-- Helper: when Q_{1,1}=0, Q·proj1·Q† = proj0 (via A.8 + helper). -/
lemma Q_proj1_Q_dagger_eq_proj0_when_Q11_zero
    (Q : Mat2) (hQ : IsUnitary2 Q) (h_b_zero : Q 1 1 = 0) :
    Q * proj1 * Q.conjTranspose = proj0 := by
  have h_A8 := py24_lemma_A_8 Q hQ
  have h_proj0 := Q_proj0_Q_dagger_eq_proj1_when_Q11_zero Q hQ h_b_zero
  have h_decomp : Q * proj1 * Q.conjTranspose = 1 - Q * proj0 * Q.conjTranspose := by
    have h_A8' : Q * proj1 * Q.conjTranspose + Q * proj0 * Q.conjTranspose = 1 := by
      rw [add_comm]; exact h_A8
    exact eq_sub_of_add_eq h_A8'
  rw [h_decomp, h_proj0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [proj0, proj1, Matrix.sub_apply, Matrix.of_apply]

set_option maxHeartbeats 1600000 in
-- 8×8 entry comparison + sub-block extraction; 4-fold matrix product expansion.
/-- **PY24 Lemma 4.2 (⇒) Case 3 (Q_{1,1}=0, b=0)**: u₀ = u₁ = 1.
    Symmetric to Case 2: substitute Q·proj0·Q†=proj1 and Q·proj1·Q†=proj0;
    entry (7,7) gives u₁=1; c=0 sub-block extracts kron2 P₀ P₁ = Diag(1,1,1,u₀);
    apply specialized 3.2 to get u₀=1. -/
lemma py24_lemma_4_2_forward_case_Q11_zero
    (Q : Mat2) (hQ : IsUnitary2 Q) (u₀ u₁ : ℂ)
    (P₀ P₁ : Mat2)
    (h_b_zero : Q 1 1 = 0)
    (h : kron3 1 1 (Q * proj0 * Q.conjTranspose) +
         kron3 P₀ P₁ (Q * proj1 * Q.conjTranspose) =
         (Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] : Mat8)) :
    u₀ = 1 ∧ u₁ = 1 := by
  rw [Q_proj0_Q_dagger_eq_proj1_when_Q11_zero Q hQ h_b_zero,
      Q_proj1_Q_dagger_eq_proj0_when_Q11_zero Q hQ h_b_zero] at h
  refine ⟨?_, ?_⟩
  · -- u₀ = 1: prove kron2 P₀ P₁ = Diag(1,1,1,u₀) via c=0 sub-block.
    apply kron2_eq_diag_three_ones_u_implies_u_eq_one (P := P₀) (Q := P₁)
    ext i j
    have h_eq := congrFun (congrFun h ⟨2 * i.val, by omega⟩)
                          ⟨2 * j.val, by omega⟩
    fin_cases i <;> fin_cases j <;>
      (simp [kron3, kron2, proj0, proj1, decode3, Matrix.add_apply, Matrix.diagonal,
             Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h_eq ⊢
       exact h_eq)
  · -- u₁ = 1 from entry (7,7).
    have h77 := congrFun (congrFun h ⟨7, by omega⟩) ⟨7, by omega⟩
    simp [kron3, proj0, proj1, decode3, Matrix.add_apply, Matrix.diagonal,
          Matrix.of_apply, Matrix.cons_val_one] at h77
    exact h77.symm

set_option maxHeartbeats 1600000 in
-- 8×8 entry comparison + sub-block extraction via specialized 3.2.
/-- **PY24 Lemma 4.2 (⇒) Case 2 — u₁ = 1 part**: from equation + Q_{0,1}=0,
    derive u₁ = 1. Uses specialized 3.2 after showing kron2 P₀ P₁ = Diag(1,1,1,u₁). -/
lemma py24_lemma_4_2_forward_case_Q01_zero_u1_eq_one
    (Q : Mat2) (hQ : IsUnitary2 Q) (u₀ u₁ : ℂ)
    (P₀ P₁ : Mat2)
    (h_Q01_zero : Q 0 1 = 0)
    (h : kron3 1 1 (Q * proj0 * Q.conjTranspose) +
         kron3 P₀ P₁ (Q * proj1 * Q.conjTranspose) =
         (Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] : Mat8)) :
    u₁ = 1 := by
  rw [Q_proj0_Q_dagger_eq_proj0_when_Q01_zero Q hQ h_Q01_zero,
      Q_proj1_Q_dagger_eq_proj1_when_Q01_zero Q hQ h_Q01_zero] at h
  apply kron2_eq_diag_three_ones_u_implies_u_eq_one (P := P₀) (Q := P₁)
  ext i j
  have h_eq := congrFun (congrFun h ⟨2 * i.val + 1, by omega⟩)
                         ⟨2 * j.val + 1, by omega⟩
  fin_cases i <;> fin_cases j <;>
    (simp [kron3, kron2, proj0, proj1, decode3, Matrix.add_apply, Matrix.diagonal,
           Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h_eq ⊢
     exact h_eq)

/-- Helper: (Q·proj0·Q†)_{ij} = Q_{i,0} · conj(Q_{j,0}). -/
lemma Q_proj0_Q_dagger_apply (Q : Mat2) (i j : Fin 2) :
    (Q * proj0 * Q.conjTranspose) i j = Q i 0 * starRingEnd ℂ (Q j 0) := by
  fin_cases i <;> fin_cases j <;>
    simp [proj0, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
          Fin.sum_univ_two]

/-- Helper: (Q·proj1·Q†)_{ij} = Q_{i,1} · conj(Q_{j,1}). -/
lemma Q_proj1_Q_dagger_apply (Q : Mat2) (i j : Fin 2) :
    (Q * proj1 * Q.conjTranspose) i j = Q i 1 * starRingEnd ℂ (Q j 1) := by
  fin_cases i <;> fin_cases j <;>
    simp [proj1, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
          Fin.sum_univ_two]

set_option maxHeartbeats 1600000 in
-- Entry-wise extraction over Q's 4 components + complex algebra closure.
/-- **PY24 Lemma 4.2 (⇒) Case 1 (Q_{0,1}≠0 ∧ Q_{1,1}≠0)**: u₀ = u₁ = 1.
    Idea: extract entries (6,6), (7,7), (6,7) from h. Combined with row
    orthogonality of Q (from Q·Q† = I), entry (6,7) forces P₀_{1,1}·P₁_{1,1} = 1.
    Substituting back into (6,6) and (7,7) and using row unit norms yields
    u₀ = u₁ = 1. -/
lemma py24_lemma_4_2_forward_case_b_d_nonzero
    (Q : Mat2) (hQ : IsUnitary2 Q) (u₀ u₁ : ℂ)
    (P₀ P₁ : Mat2)
    (h_b_ne : Q 0 1 ≠ 0)
    (h_d_ne : Q 1 1 ≠ 0)
    (h : kron3 1 1 (Q * proj0 * Q.conjTranspose) +
         kron3 P₀ P₁ (Q * proj1 * Q.conjTranspose) =
         (Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] : Mat8)) :
    u₀ = 1 ∧ u₁ = 1 := by
  have hQQt : Q * Q.conjTranspose = 1 := mul_eq_one_comm.mp hQ
  -- Row identities from Q · Q† = 1.
  have h_row0_unit :
      Q 0 0 * starRingEnd ℂ (Q 0 0) + Q 0 1 * starRingEnd ℂ (Q 0 1) = 1 := by
    have hh := congrFun (congrFun hQQt 0) 0
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
           Fin.sum_univ_two] using hh
  have h_row1_unit :
      Q 1 0 * starRingEnd ℂ (Q 1 0) + Q 1 1 * starRingEnd ℂ (Q 1 1) = 1 := by
    have hh := congrFun (congrFun hQQt 1) 1
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
           Fin.sum_univ_two] using hh
  have h_row01_orth :
      Q 0 0 * starRingEnd ℂ (Q 1 0) + Q 0 1 * starRingEnd ℂ (Q 1 1) = 0 := by
    have hh := congrFun (congrFun hQQt 0) 1
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
           Fin.sum_univ_two] using hh
  -- Extract entries (6,6), (7,7), (6,7) from h.
  have h66 := congrFun (congrFun h ⟨6, by omega⟩) ⟨6, by omega⟩
  have h77 := congrFun (congrFun h ⟨7, by omega⟩) ⟨7, by omega⟩
  have h67 := congrFun (congrFun h ⟨6, by omega⟩) ⟨7, by omega⟩
  -- Convert each to a scalar identity. After kron3 + decode3 expansion:
  -- entry (i,j) of LHS picks (1)_{a₁a₂}(1)_{b₁b₂}M_{c₁c₂} + P₀_{a₁a₂}P₁_{b₁b₂}N_{c₁c₂}.
  -- We then substitute the entry helpers.
  simp [kron3, decode3, Matrix.add_apply, Matrix.diagonal,
        Matrix.of_apply, Matrix.one_apply,
        Q_proj0_Q_dagger_apply, Q_proj1_Q_dagger_apply] at h66 h77 h67
  -- Now:
  -- h66 : Q 0 0 * conj(Q 0 0) + P₀ 1 1 * P₁ 1 1 * (Q 0 1 * conj(Q 0 1)) = u₀
  -- h77 : Q 1 0 * conj(Q 1 0) + P₀ 1 1 * P₁ 1 1 * (Q 1 1 * conj(Q 1 1)) = u₁
  -- h67 : Q 0 0 * conj(Q 1 0) + P₀ 1 1 * P₁ 1 1 * (Q 0 1 * conj(Q 1 1)) = 0
  -- From h67 + h_row01_orth: (P₀ 1 1 · P₁ 1 1 - 1) · Q 0 1 · conj(Q 1 1) = 0.
  -- conj(Q 1 1) ≠ 0 since Q 1 1 ≠ 0.
  have h_conj_d_ne : starRingEnd ℂ (Q 1 1) ≠ 0 := by
    intro h_z
    have : Q 1 1 = 0 := by
      have := congrArg (starRingEnd ℂ) h_z
      simpa using this
    exact h_d_ne this
  -- Combine h67 with row orthogonality to derive (P₀_{11}·P₁_{11} - 1)·Q_{01}·conj(Q_{11}) = 0.
  have h_factor :
      (P₀ 1 1 * P₁ 1 1 - 1) * (Q 0 1 * starRingEnd ℂ (Q 1 1)) = 0 := by
    have h_off : Q 0 0 * starRingEnd ℂ (Q 1 0) =
                 -(Q 0 1 * starRingEnd ℂ (Q 1 1)) := by
      linear_combination h_row01_orth
    rw [h_off] at h67
    linear_combination h67
  -- Q_{01} · conj(Q_{11}) ≠ 0 in this case.
  have h_prod_ne : Q 0 1 * starRingEnd ℂ (Q 1 1) ≠ 0 :=
    mul_ne_zero h_b_ne h_conj_d_ne
  -- Hence P₀_{11}·P₁_{11} = 1.
  have h_PP : P₀ 1 1 * P₁ 1 1 = 1 := by
    have h_diff_zero : P₀ 1 1 * P₁ 1 1 - 1 = 0 :=
      (mul_eq_zero.mp h_factor).resolve_right h_prod_ne
    exact sub_eq_zero.mp h_diff_zero
  refine ⟨?_, ?_⟩
  · -- u₀ = 1: from h66 + h_PP + h_row0_unit.
    rw [h_PP, one_mul] at h66
    rw [h_row0_unit] at h66
    exact h66.symm
  · -- u₁ = 1: from h77 + h_PP + h_row1_unit.
    rw [h_PP, one_mul] at h77
    rw [h_row1_unit] at h77
    exact h77.symm

/-- **PY24 Lemma 4.2 (⇒)**: dispatch lemma combining Cases 1, 2, 3.
    If Q is unitary and kron3 1 1 (Q·proj0·Q†) + kron3 P₀ P₁ (Q·proj1·Q†)
    = Diag(1,1,1,1,1,1,u₀,u₁), then u₀ = 1 ∧ u₁ = 1. -/
lemma py24_lemma_4_2_forward
    (Q : Mat2) (hQ : IsUnitary2 Q) (u₀ u₁ : ℂ)
    (P₀ P₁ : Mat2)
    (h : kron3 1 1 (Q * proj0 * Q.conjTranspose) +
         kron3 P₀ P₁ (Q * proj1 * Q.conjTranspose) =
         (Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] : Mat8)) :
    u₀ = 1 ∧ u₁ = 1 := by
  by_cases h_b_zero : Q 0 1 = 0
  · -- Case 2: Q_{0,1} = 0.
    refine ⟨?_, ?_⟩
    · exact py24_lemma_4_2_forward_case_Q01_zero_u0_eq_one Q hQ u₀ u₁ P₀ P₁ h_b_zero h
    · exact py24_lemma_4_2_forward_case_Q01_zero_u1_eq_one Q hQ u₀ u₁ P₀ P₁ h_b_zero h
  · by_cases h_d_zero : Q 1 1 = 0
    · -- Case 3: Q_{1,1} = 0.
      exact py24_lemma_4_2_forward_case_Q11_zero Q hQ u₀ u₁ P₀ P₁ h_d_zero h
    · -- Case 1: Q_{0,1} ≠ 0 ∧ Q_{1,1} ≠ 0.
      exact py24_lemma_4_2_forward_case_b_d_nonzero Q hQ u₀ u₁ P₀ P₁ h_b_zero h_d_zero h

/-- **PY24 Lemma 4.2 (full iff)**: For Q unitary,
    `∃ P₀ P₁ : Mat2 unitary, kron3 1 1 (Q·proj0·Q†) + kron3 P₀ P₁ (Q·proj1·Q†)
      = Diag(1,1,1,1,1,1,u₀,u₁)` ↔ `u₀ = 1 ∧ u₁ = 1`. -/
theorem py24_lemma_4_2 (Q : Mat2) (hQ : IsUnitary2 Q) (u₀ u₁ : ℂ) :
    (∃ P₀ P₁ : Mat2, IsUnitary2 P₀ ∧ IsUnitary2 P₁ ∧
      kron3 1 1 (Q * proj0 * Q.conjTranspose) +
      kron3 P₀ P₁ (Q * proj1 * Q.conjTranspose) =
      (Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] : Mat8))
    ↔ (u₀ = 1 ∧ u₁ = 1) := by
  constructor
  · rintro ⟨P₀, P₁, _, _, h⟩
    exact py24_lemma_4_2_forward Q hQ u₀ u₁ P₀ P₁ h
  · rintro ⟨h₀, h₁⟩
    subst h₀
    subst h₁
    exact py24_lemma_4_2_backward Q hQ

/-- **PY24 Lemma A.28**. -/
lemma py24_lemma_A_28
    {V₁ V₂ V₃ V₄ : Mat4} (hV₄ : IsUnitary4 V₄)
    {D : Mat8}
    (h_chain : embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄ = D)
    (h_V3 : Mat4.apply V₃ (tensor1_1 ket0_1 ket0_1) = tensor1_1 ket0_1 ket0_1)
    (h_D : ∀ y : Vec2, Mat8.apply D (tensor1_2 ket0_1 y) = tensor1_2 ket0_1 y)
    (x : Vec1) :
    Mat8.apply (embedAC V₁ * embedBC V₂) (tensor1_2 ket0_1 (tensor1_1 x ket0_1)) =
    Mat8.apply (embedBC V₄.conjTranspose) (tensor1_2 ket0_1 (tensor1_1 x ket0_1)) := by
  -- Setup helpers.
  have h_V4_inv : V₄ * V₄.conjTranspose = 1 := mul_eq_one_comm.mp hV₄
  have h_V3_apply : Mat8.apply (embedAC V₃) (tensor1_2 ket0_1 (tensor1_1 x ket0_1)) =
                    tensor1_2 ket0_1 (tensor1_1 x ket0_1) :=
    embedAC_apply_ket0_b_ket0_when_V_fixes_ket00 V₃ x h_V3
  -- chain · V₄† simplifies to V₁_AC · V₂_BC · V₃_AC (via V₄·V₄†=1).
  have h_chain_simp :
      embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄ * embedBC V₄.conjTranspose
      = embedAC V₁ * embedBC V₂ * embedAC V₃ := by
    rw [mul_assoc (embedAC V₁ * embedBC V₂ * embedAC V₃) (embedBC V₄)]
    rw [embedBC_mul, h_V4_inv, embedBC_one, mul_one]
  -- chain·V₄†·(|0⟩|x⟩|0⟩) via h_chain_simp + h_V3_apply: equals V₁·V₂·(|0⟩|x⟩|0⟩).
  have step1 :
      Mat8.apply (embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄ * embedBC V₄.conjTranspose)
        (tensor1_2 ket0_1 (tensor1_1 x ket0_1)) =
      Mat8.apply (embedAC V₁ * embedBC V₂) (tensor1_2 ket0_1 (tensor1_1 x ket0_1)) := by
    rw [h_chain_simp, Mat8.apply_mul, h_V3_apply]
  -- chain·V₄†·(|0⟩|x⟩|0⟩) via h_chain (chain = D) + h_D: equals V₄†·(|0⟩|x⟩|0⟩).
  have step2 :
      Mat8.apply (embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄ * embedBC V₄.conjTranspose)
        (tensor1_2 ket0_1 (tensor1_1 x ket0_1)) =
      Mat8.apply (embedBC V₄.conjTranspose) (tensor1_2 ket0_1 (tensor1_1 x ket0_1)) := by
    rw [show embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄ * embedBC V₄.conjTranspose
          = D * embedBC V₄.conjTranspose by rw [h_chain]]
    rw [Mat8.apply_mul, embedBC_apply_tensor1_2]
    exact h_D _
  -- Combine.
  rw [← step1, step2]

-- (case1_v3dag_entangled_concludes, case3_v3dag_first_fixed_concludes,
-- py24_lemma_A_31, and py24_lemma_6_2 have all been relocated to the
-- end of the file (right before py24_lemma_A_29 and py24_lemma_6_3),
-- so that A.31's body can reference exists_T_second_factor_fixed and
-- other A.30 infrastructure.)

-- (py24_lemma_6_3 has been relocated to the end of the file alongside
-- py24_lemma_6_4, so that its body can reference py24_lemma_A_30 etc.)

-- (py24_lemma_6_4 has been relocated to the end of the file, after A.33,
-- so that its (⇒) direction can reference A.32, A.28, A.19, A.33 etc.)

/-! ## PY24 Lemma A.3 (Spectral Theorem for 2×2 unitary)

Every 2×2 unitary U is unitarily similar to a diagonal matrix:
  ∃ a b ∈ ℂ, ∃ V unitary, V† · U · V = Diag(a, b).

Proof outline:
  Case 1 (U 0 1 = 0): U is diagonal directly (unitarity forces U 1 0 = 0).
  Case 2 (U 0 1 ≠ 0): use eigenvector construction. Find one eigenvector v
    via FTA on char poly. Build V = [v/|v|, w] with w ⊥ v unit. Then V† · U · V
    is upper-triangular (since v is eigenvector). Normality of U + upper
    triangular ⟹ diagonal. -/

/-- Helper: 2×2 unitary U with `U 0 1 = 0` is diagonal. From column orthogonality
    and column-1 unit norm forcing U 1 1 ≠ 0, we get U 1 0 = 0. -/
private lemma unitary2_diagonal_of_upper_triangular_zero
    {U : Mat2} (hU : IsUnitary2 U) (h_b_zero : U 0 1 = 0) :
    U 1 0 = 0 := by
  unfold IsUnitary2 at hU
  -- Col 1 unit: |U 0 1|² + |U 1 1|² = 1.
  have h11_norm : starRingEnd ℂ (U 1 1) * U 1 1 = 1 := by
    have h := congrFun (congrFun hU 1) 1
    simp [Matrix.conjTranspose_apply, Matrix.mul_apply,
          Fin.sum_univ_two] at h
    rw [h_b_zero, map_zero, zero_mul, zero_add] at h
    exact h
  -- U 1 1 ≠ 0 from |U 1 1|² = 1.
  have h11_ne : U 1 1 ≠ 0 := by
    intro h_z
    rw [h_z, map_zero, zero_mul] at h11_norm
    exact zero_ne_one h11_norm
  have h_conj_11_ne : starRingEnd ℂ (U 1 1) ≠ 0 := by
    intro h_z
    have : U 1 1 = 0 := by
      have := congrArg (starRingEnd ℂ) h_z
      simpa using this
    exact h11_ne this
  -- (U†U)_{1,0} = conj(U 0 1)·U 0 0 + conj(U 1 1)·U 1 0 = 0.
  have h_off : starRingEnd ℂ (U 0 1) * U 0 0 + starRingEnd ℂ (U 1 1) * U 1 0 = 0 := by
    have h := congrFun (congrFun hU 1) 0
    simp [Matrix.conjTranspose_apply, Matrix.mul_apply,
          Fin.sum_univ_two] at h
    exact h
  rw [h_b_zero, map_zero, zero_mul, zero_add] at h_off
  exact (mul_eq_zero.mp h_off).resolve_left h_conj_11_ne

/-- Helper: existence of a square root in ℂ. -/
private lemma exists_complex_sqrt (z : ℂ) : ∃ s : ℂ, s * s = z := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self z
  exact ⟨s, hs.symm⟩

/-- The "spectral V" matrix from a vector (v0, v1) ∈ ℂ² with normalization r ∈ ℝ.
    Cols are (v0/r, v1/r) and (-conj(v1)/r, conj(v0)/r). -/
private noncomputable def spectralV (v0 v1 : ℂ) (r : ℝ) : Mat2 :=
  Matrix.of ![![v0 / (r : ℂ), -starRingEnd ℂ v1 / (r : ℂ)],
              ![v1 / (r : ℂ), starRingEnd ℂ v0 / (r : ℂ)]]

/-- Explicit values of spectralV's entries. -/
private lemma spectralV_apply_00 (v0 v1 : ℂ) (r : ℝ) :
    spectralV v0 v1 r 0 0 = v0 / (r : ℂ) := rfl
private lemma spectralV_apply_01 (v0 v1 : ℂ) (r : ℝ) :
    spectralV v0 v1 r 0 1 = -starRingEnd ℂ v1 / (r : ℂ) := rfl
private lemma spectralV_apply_10 (v0 v1 : ℂ) (r : ℝ) :
    spectralV v0 v1 r 1 0 = v1 / (r : ℂ) := rfl
private lemma spectralV_apply_11 (v0 v1 : ℂ) (r : ℝ) :
    spectralV v0 v1 r 1 1 = starRingEnd ℂ v0 / (r : ℂ) := rfl

/-- Each entry of (spectralV)† · spectralV. Computing these directly avoids
    interactions between fin_cases and the `(fun i ↦ i)` artifacts produced by
    Matrix.ext. -/
private lemma spectralV_dagger_mul_apply_00 (v0 v1 : ℂ) (r : ℝ) (hr_ne : (r : ℂ) ≠ 0)
    (hr_sq : (r : ℂ) * (r : ℂ) =
              starRingEnd ℂ v0 * v0 + starRingEnd ℂ v1 * v1) :
    ((spectralV v0 v1 r).conjTranspose * spectralV v0 v1 r) 0 0 = 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Matrix.conjTranspose_apply, spectralV_apply_00, spectralV_apply_10]
  rw [show star (v0 / (r : ℂ)) = starRingEnd ℂ v0 / (r : ℂ) by
        change starRingEnd ℂ (v0 / (r : ℂ)) = starRingEnd ℂ v0 / (r : ℂ)
        rw [map_div₀, Complex.conj_ofReal]]
  rw [show star (v1 / (r : ℂ)) = starRingEnd ℂ v1 / (r : ℂ) by
        change starRingEnd ℂ (v1 / (r : ℂ)) = starRingEnd ℂ v1 / (r : ℂ)
        rw [map_div₀, Complex.conj_ofReal]]
  field_simp
  linear_combination -hr_sq

private lemma spectralV_dagger_mul_apply_01 (v0 v1 : ℂ) (r : ℝ) (hr_ne : (r : ℂ) ≠ 0) :
    ((spectralV v0 v1 r).conjTranspose * spectralV v0 v1 r) 0 1 = 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Matrix.conjTranspose_apply, spectralV_apply_00, spectralV_apply_10,
      spectralV_apply_01, spectralV_apply_11]
  rw [show star (v0 / (r : ℂ)) = starRingEnd ℂ v0 / (r : ℂ) by
        change starRingEnd ℂ (v0 / (r : ℂ)) = starRingEnd ℂ v0 / (r : ℂ)
        rw [map_div₀, Complex.conj_ofReal]]
  rw [show star (v1 / (r : ℂ)) = starRingEnd ℂ v1 / (r : ℂ) by
        change starRingEnd ℂ (v1 / (r : ℂ)) = starRingEnd ℂ v1 / (r : ℂ)
        rw [map_div₀, Complex.conj_ofReal]]
  field_simp; ring

private lemma spectralV_dagger_mul_apply_10 (v0 v1 : ℂ) (r : ℝ) (hr_ne : (r : ℂ) ≠ 0) :
    ((spectralV v0 v1 r).conjTranspose * spectralV v0 v1 r) 1 0 = 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Matrix.conjTranspose_apply, spectralV_apply_01, spectralV_apply_11,
      spectralV_apply_00, spectralV_apply_10]
  rw [show star (-starRingEnd ℂ v1 / (r : ℂ)) = -v1 / (r : ℂ) by
        change starRingEnd ℂ (-starRingEnd ℂ v1 / (r : ℂ)) = -v1 / (r : ℂ)
        rw [map_div₀, map_neg, Complex.conj_conj, Complex.conj_ofReal]]
  rw [show star (starRingEnd ℂ v0 / (r : ℂ)) = v0 / (r : ℂ) by
        change starRingEnd ℂ (starRingEnd ℂ v0 / (r : ℂ)) = v0 / (r : ℂ)
        rw [map_div₀, Complex.conj_conj, Complex.conj_ofReal]]
  field_simp; ring

private lemma spectralV_dagger_mul_apply_11 (v0 v1 : ℂ) (r : ℝ) (hr_ne : (r : ℂ) ≠ 0)
    (hr_sq : (r : ℂ) * (r : ℂ) =
              starRingEnd ℂ v0 * v0 + starRingEnd ℂ v1 * v1) :
    ((spectralV v0 v1 r).conjTranspose * spectralV v0 v1 r) 1 1 = 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Matrix.conjTranspose_apply, spectralV_apply_01, spectralV_apply_11]
  rw [show star (-starRingEnd ℂ v1 / (r : ℂ)) = -v1 / (r : ℂ) by
        change starRingEnd ℂ (-starRingEnd ℂ v1 / (r : ℂ)) = -v1 / (r : ℂ)
        rw [map_div₀, map_neg, Complex.conj_conj, Complex.conj_ofReal]]
  rw [show star (starRingEnd ℂ v0 / (r : ℂ)) = v0 / (r : ℂ) by
        change starRingEnd ℂ (starRingEnd ℂ v0 / (r : ℂ)) = v0 / (r : ℂ)
        rw [map_div₀, Complex.conj_conj, Complex.conj_ofReal]]
  field_simp
  linear_combination -hr_sq

/-- spectralV is unitary when (r:ℂ)² = |v0|² + |v1|². -/
private lemma spectralV_isUnitary (v0 v1 : ℂ) (r : ℝ) (hr_ne : (r : ℂ) ≠ 0)
    (hr_sq : (r : ℂ) * (r : ℂ) =
              starRingEnd ℂ v0 * v0 + starRingEnd ℂ v1 * v1) :
    IsUnitary2 (spectralV v0 v1 r) := by
  change (spectralV v0 v1 r).conjTranspose * (spectralV v0 v1 r) = 1
  ext i j
  fin_cases i <;> fin_cases j
  · exact (spectralV_dagger_mul_apply_00 v0 v1 r hr_ne hr_sq).trans
            (Matrix.one_apply_eq _).symm
  · exact (spectralV_dagger_mul_apply_01 v0 v1 r hr_ne).trans
            (Matrix.one_apply_ne (by decide)).symm
  · exact (spectralV_dagger_mul_apply_10 v0 v1 r hr_ne).trans
            (Matrix.one_apply_ne (by decide)).symm
  · exact (spectralV_dagger_mul_apply_11 v0 v1 r hr_ne hr_sq).trans
            (Matrix.one_apply_eq _).symm

set_option maxHeartbeats 1600000 in
-- Spectral theorem: case split on tr/det + complex algebra closure (nlinarith).
/-- **PY24 Lemma A.3 (Spectral Theorem)**: Every 2×2 unitary U is unitarily
    similar to a diagonal matrix. -/
theorem py24_lemma_A_3 (U : Mat2) (hU : IsUnitary2 U) :
    ∃ a b : ℂ, ∃ V : Mat2, IsUnitary2 V ∧
      V.conjTranspose * U * V = Matrix.diagonal ![a, b] := by
  by_cases h_b_zero : U 0 1 = 0
  · -- Case 1: U is upper-triangular ⟹ U is diagonal.
    have h_lo_zero : U 1 0 = 0 :=
      unitary2_diagonal_of_upper_triangular_zero hU h_b_zero
    refine ⟨U 0 0, U 1 1, 1, isUnitary2_one, ?_⟩
    rw [Matrix.conjTranspose_one, one_mul, mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.of_apply, h_b_zero, h_lo_zero]
  · -- Case 2: U 0 1 ≠ 0. Eigenvector construction.
    -- Define char-poly-related scalars.
    set α := U 0 0
    set β := U 0 1
    set γ := U 1 0
    set η := U 1 1
    set τ := α + η
    set δ := α * η - β * γ
    -- Pick a root of X² - τX + δ = 0 via discriminant.
    obtain ⟨s, hs⟩ := exists_complex_sqrt (τ * τ - 4 * δ)
    set a := (τ + s) / 2
    -- a is a root of X² - τX + δ.
    have h_a_root : a * a - τ * a + δ = 0 := by
      change (τ + s) / 2 * ((τ + s) / 2) - τ * ((τ + s) / 2) + δ = 0
      field_simp
      linear_combination hs
    -- Eigenvector: v_a = (β, a - α). Nonzero since β ≠ 0.
    set v0 := β
    set v1 := a - α
    have h_v_norm_pos :
        starRingEnd ℂ v0 * v0 + starRingEnd ℂ v1 * v1 ≠ 0 := by
      intro h_zero
      have h_v0_norm : starRingEnd ℂ v0 * v0 = (Complex.normSq v0 : ℂ) := by
        rw [mul_comm]; exact (Complex.mul_conj v0).symm ▸ rfl
      have h_v1_norm : starRingEnd ℂ v1 * v1 = (Complex.normSq v1 : ℂ) := by
        rw [mul_comm]; exact (Complex.mul_conj v1).symm ▸ rfl
      rw [h_v0_norm, h_v1_norm, ← Complex.ofReal_add] at h_zero
      have h_real_zero : Complex.normSq v0 + Complex.normSq v1 = 0 := by
        exact_mod_cast h_zero
      have h_v0_nn : 0 ≤ Complex.normSq v0 := Complex.normSq_nonneg _
      have h_v1_nn : 0 ≤ Complex.normSq v1 := Complex.normSq_nonneg _
      have h_v0_zero : Complex.normSq v0 = 0 := by linarith
      exact h_b_zero (Complex.normSq_eq_zero.mp h_v0_zero)
    -- The norm |v_a|² is a positive real, so it's nonzero in ℂ and has a real sqrt.
    set N : ℂ := starRingEnd ℂ v0 * v0 + starRingEnd ℂ v1 * v1 with hN_def
    -- N is real: N = |v0|² + |v1|² as real ⟹ ℂ.
    have hN_real : N = ((Complex.normSq v0 + Complex.normSq v1 : ℝ) : ℂ) := by
      rw [hN_def]
      push_cast
      rw [show starRingEnd ℂ v0 * v0 = (Complex.normSq v0 : ℂ) by
            rw [mul_comm]; exact (Complex.mul_conj v0).symm ▸ rfl,
          show starRingEnd ℂ v1 * v1 = (Complex.normSq v1 : ℂ) by
            rw [mul_comm]; exact (Complex.mul_conj v1).symm ▸ rfl]
    have hN_pos_real : 0 < (Complex.normSq v0 + Complex.normSq v1 : ℝ) := by
      have h0 : 0 ≤ Complex.normSq v0 := Complex.normSq_nonneg _
      have h1 : 0 ≤ Complex.normSq v1 := Complex.normSq_nonneg _
      by_contra h_not
      push_neg at h_not
      have h_eq : Complex.normSq v0 + Complex.normSq v1 = 0 := le_antisymm h_not (by linarith)
      have h0_zero : Complex.normSq v0 = 0 := by linarith
      exact h_b_zero (Complex.normSq_eq_zero.mp h0_zero)
    -- Get the real square root r > 0.
    set r : ℝ := Real.sqrt (Complex.normSq v0 + Complex.normSq v1) with hr_def
    have hr_pos : 0 < r := Real.sqrt_pos.mpr hN_pos_real
    have hr_sq : r * r = Complex.normSq v0 + Complex.normSq v1 :=
      Real.mul_self_sqrt (le_of_lt hN_pos_real)
    have hr_ne : (r : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hr_pos)
    -- Use spectralV with v0 = β, v1 = a - α.
    -- (r:ℂ)² = N (lift hr_sq to ℂ).
    have hr_sq_C : (r : ℂ) * (r : ℂ) =
                   starRingEnd ℂ v0 * v0 + starRingEnd ℂ v1 * v1 := by
      have : (r : ℂ) * (r : ℂ) = N := by
        rw [hN_real]; push_cast; exact_mod_cast hr_sq
      rw [this, hN_def]
    -- V_mat is unitary by spectralV_isUnitary.
    have hV_unit : IsUnitary2 (spectralV v0 v1 r) :=
      spectralV_isUnitary v0 v1 r hr_ne hr_sq_C
    -- Algebraic eigenvalue identity from h_a_root:
    -- a²-τa+δ=0 ⟹ β·γ = (a-α)(a-η).
    -- Expand: a² - (α+η)a + (αη - βγ) = 0 ⟹ βγ = a² - (α+η)a + αη = (a-α)(a-η).
    have h_eig_factor : β * γ = (a - α) * (a - η) := by
      have h_τ : τ = α + η := rfl
      have h_δ : δ = α * η - β * γ := rfl
      have h := h_a_root
      rw [h_τ, h_δ] at h
      linear_combination -h
    -- Eigenvector property — top entry: (U · V) 0 0 = a · V 0 0.
    -- (U·V) 0 0 = α·(v0/r) + β·(v1/r) = α·β/r + β·(a-α)/r = β·a/r = a·(v0/r) ✓
    have h_UV_00 : (U * spectralV v0 v1 r) 0 0 = a * (spectralV v0 v1 r) 0 0 := by
      rw [Matrix.mul_apply, Fin.sum_univ_two,
          spectralV_apply_00, spectralV_apply_10]
      change α * (β / (r : ℂ)) + β * ((a - α) / (r : ℂ)) = a * (β / (r : ℂ))
      field_simp
      ring
    -- Eigenvector property — bottom entry: (U · V) 1 0 = a · V 1 0.
    -- (U·V) 1 0 = γ·(β/r) + η·((a-α)/r). Using β·γ = (a-α)(a-η):
    -- = ((a-α)(a-η) + η(a-α))/r = (a-α)·a/r = a·((a-α)/r) = a · V 1 0.
    have h_UV_10 : (U * spectralV v0 v1 r) 1 0 = a * (spectralV v0 v1 r) 1 0 := by
      rw [Matrix.mul_apply, Fin.sum_univ_two,
          spectralV_apply_00, spectralV_apply_10]
      change γ * (β / (r : ℂ)) + η * ((a - α) / (r : ℂ)) = a * ((a - α) / (r : ℂ))
      field_simp
      linear_combination h_eig_factor
    -- (V†UV) 0 0 = a, using h_UV_00, h_UV_10, and (V†V) 0 0 = 1.
    have h_VUV_00 :
        ((spectralV v0 v1 r).conjTranspose * (U * spectralV v0 v1 r)) 0 0 = a := by
      rw [Matrix.mul_apply, Fin.sum_univ_two, h_UV_00, h_UV_10]
      have h_VV_00 := spectralV_dagger_mul_apply_00 v0 v1 r hr_ne hr_sq_C
      rw [Matrix.mul_apply, Fin.sum_univ_two] at h_VV_00
      linear_combination a * h_VV_00
    -- (V†UV) 1 0 = 0, using h_UV_00, h_UV_10, and (V†V) 1 0 = 0.
    have h_VUV_10 :
        ((spectralV v0 v1 r).conjTranspose * (U * spectralV v0 v1 r)) 1 0 = 0 := by
      rw [Matrix.mul_apply, Fin.sum_univ_two, h_UV_00, h_UV_10]
      have h_VV_10 := spectralV_dagger_mul_apply_10 v0 v1 r hr_ne
      rw [Matrix.mul_apply, Fin.sum_univ_two] at h_VV_10
      linear_combination a * h_VV_10
    -- V†UV is unitary: sandwich of unitaries V, U, V.
    have hVUV_unit : IsUnitary2
        ((spectralV v0 v1 r).conjTranspose * U * (spectralV v0 v1 r)) := by
      change ((spectralV v0 v1 r).conjTranspose * U * spectralV v0 v1 r).conjTranspose *
           ((spectralV v0 v1 r).conjTranspose * U * spectralV v0 v1 r) = 1
      have h_VVdag : spectralV v0 v1 r * (spectralV v0 v1 r).conjTranspose = 1 :=
        mul_eq_one_comm.mp hV_unit
      have h_UdagU : U.conjTranspose * U = 1 := hU
      have h_VdagV : (spectralV v0 v1 r).conjTranspose * spectralV v0 v1 r = 1 := hV_unit
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose]
      calc (spectralV v0 v1 r).conjTranspose * (U.conjTranspose * spectralV v0 v1 r) *
            ((spectralV v0 v1 r).conjTranspose * U * spectralV v0 v1 r)
          = (spectralV v0 v1 r).conjTranspose * U.conjTranspose *
              (spectralV v0 v1 r * (spectralV v0 v1 r).conjTranspose) * U *
              spectralV v0 v1 r := by noncomm_ring
        _ = (spectralV v0 v1 r).conjTranspose * U.conjTranspose * 1 * U *
              spectralV v0 v1 r := by rw [h_VVdag]
        _ = (spectralV v0 v1 r).conjTranspose * (U.conjTranspose * U) *
              spectralV v0 v1 r := by noncomm_ring
        _ = (spectralV v0 v1 r).conjTranspose * 1 * spectralV v0 v1 r := by rw [h_UdagU]
        _ = (spectralV v0 v1 r).conjTranspose * spectralV v0 v1 r := by noncomm_ring
        _ = 1 := h_VdagV
    -- Variants of h_VUV_00, h_VUV_10 with left-associated multiplication.
    have h_VUV_00' :
        ((spectralV v0 v1 r).conjTranspose * U * spectralV v0 v1 r) 0 0 = a := by
      rw [mul_assoc]; exact h_VUV_00
    have h_VUV_10' :
        ((spectralV v0 v1 r).conjTranspose * U * spectralV v0 v1 r) 1 0 = 0 := by
      rw [mul_assoc]; exact h_VUV_10
    -- |a|² = 1 from col 0 unit norm of V†UV unitary.
    have h_a_norm : starRingEnd ℂ a * a = 1 := by
      have h := hVUV_unit
      unfold IsUnitary2 at h
      have h00 := congrFun (congrFun h 0) 0
      rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
          Matrix.conjTranspose_apply, Matrix.one_apply_eq, h_VUV_00', h_VUV_10'] at h00
      simpa using h00
    -- a ≠ 0 from |a|² = 1.
    have h_a_ne : a ≠ 0 := by
      intro h_zero
      rw [h_zero, map_zero, zero_mul] at h_a_norm
      exact zero_ne_one h_a_norm
    have h_star_a_ne : starRingEnd ℂ a ≠ 0 := by
      intro h_zero
      apply h_a_ne
      have := congrArg (starRingEnd ℂ) h_zero
      simpa using this
    -- (V†UV) 0 1 = 0 from col orthogonality of V†UV unitary.
    have h_VUV_01 :
        ((spectralV v0 v1 r).conjTranspose * U * spectralV v0 v1 r) 0 1 = 0 := by
      have h := hVUV_unit
      unfold IsUnitary2 at h
      have h01 := congrFun (congrFun h 0) 1
      rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
          Matrix.conjTranspose_apply, Matrix.one_apply_ne (by decide),
          h_VUV_00', h_VUV_10'] at h01
      simp at h01
      exact h01.resolve_left h_a_ne
    -- Define b := (V†UV) 1 1 and show V†UV = Diag(a, b).
    set b : ℂ := ((spectralV v0 v1 r).conjTranspose * U * spectralV v0 v1 r) 1 1
        with hb_def
    have h_diag_00 : (Matrix.diagonal ![a, b] : Mat2) 0 0 = a := by
      simp [Matrix.diagonal_apply_eq]
    have h_diag_11 : (Matrix.diagonal ![a, b] : Mat2) 1 1 = b := by
      simp [Matrix.diagonal_apply_eq]
    have h_diag_01 : (Matrix.diagonal ![a, b] : Mat2) 0 1 = 0 :=
      Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1)
    have h_diag_10 : (Matrix.diagonal ![a, b] : Mat2) 1 0 = 0 :=
      Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0)
    have h_VUV_diag :
        (spectralV v0 v1 r).conjTranspose * U * spectralV v0 v1 r =
        Matrix.diagonal ![a, b] := by
      ext i j
      fin_cases i <;> fin_cases j
      · exact h_VUV_00'.trans h_diag_00.symm
      · exact h_VUV_01.trans h_diag_01.symm
      · exact h_VUV_10'.trans h_diag_10.symm
      · exact (hb_def.symm).trans h_diag_11.symm
    -- Close A.3 with explicit witness.
    exact ⟨a, b, spectralV v0 v1 r, hV_unit, h_VUV_diag⟩

/-! ## PY24 Lemma A.5 (HP A.11) — Tensor product eigenvalues

For 1-qubit unitaries P, Q with eigenvalues [a, b] and [p, q]:
  Eigenvalues(P ⊗ Q) = [ap, aq, bp, bq]

In our framework, formulated via unitary similarity to diagonal form. -/

/-- Kronecker product of two 2×2 diagonal matrices is a 4×4 diagonal:
    `Diag(a,b) ⊗ Diag(p,q) = Diag(ap, aq, bp, bq)`. -/
lemma kron2_diag_diag (a b p q : ℂ) :
    kron2 (Matrix.diagonal ![a, b]) (Matrix.diagonal ![p, q])
      = Matrix.diagonal ![a * p, a * q, b * p, b * q] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kron2, Matrix.of_apply, Matrix.diagonal]

theorem py24_lemma_A_5 (P Q : Mat2) (_hP : IsUnitary2 P) (_hQ : IsUnitary2 Q)
    (a b p q : ℂ)
    (hPeig : ∃ V : Mat2, IsUnitary2 V ∧
      V.conjTranspose * P * V = Matrix.diagonal ![a, b])
    (hQeig : ∃ W : Mat2, IsUnitary2 W ∧
      W.conjTranspose * Q * W = Matrix.diagonal ![p, q]) :
    ∃ U : Mat4, IsUnitary4 U ∧
      U.conjTranspose * kron2 P Q * U =
      Matrix.diagonal ![a * p, a * q, b * p, b * q] := by
  obtain ⟨V, hV, hVPV⟩ := hPeig
  obtain ⟨W, hW, hWQW⟩ := hQeig
  refine ⟨kron2 V W, isUnitary4_kron2 hV hW, ?_⟩
  rw [kron2_conjTranspose, kron2_mul, kron2_mul, hVPV, hWQW, kron2_diag_diag]

/-! ## PY24 Lemma A.6 (HP A.12) — Block-diagonal eigenvalues

For 1-qubit unitaries P, Q:
  Eigenvalues(|0⟩⟨0| ⊗ P + |1⟩⟨1| ⊗ Q) = Eigenvalues(P) ⊔ Eigenvalues(Q). -/


lemma block_diag_first_conjT (A B : Mat2) :
    (kron2 proj0 A + kron2 proj1 B).conjTranspose
      = kron2 proj0 A.conjTranspose + kron2 proj1 B.conjTranspose := by
  rw [Matrix.conjTranspose_add, kron2_conjTranspose, kron2_conjTranspose,
      proj0_conjTranspose, proj1_conjTranspose]

lemma block_diag_first_mul (A B C D : Mat2) :
    (kron2 proj0 A + kron2 proj1 B) * (kron2 proj0 C + kron2 proj1 D) =
      kron2 proj0 (A * C) + kron2 proj1 (B * D) := by
  rw [add_mul, mul_add, mul_add,
      kron2_mul, kron2_mul, kron2_mul, kron2_mul,
      proj0_sq, proj0_mul_proj1, proj1_mul_proj0, proj1_sq,
      kron2_zero_left, kron2_zero_left, add_zero, zero_add]

/-- Trace of a block-diag-A 4×4 matrix: `tr(kron2 proj0 A + kron2 proj1 B)
    = tr(A) + tr(B)`. Used by 3.3 (⇒) to derive the e_2 (sum of squares)
    equation from `tr(M²) = tr(D²)`. -/
lemma trace_block_diag_first (A B : Mat2) :
    (kron2 proj0 A + kron2 proj1 B).trace = A.trace + B.trace := by
  simp [Matrix.trace, Matrix.diag, Matrix.add_apply, kron2, proj0, proj1,
        Matrix.of_apply, Fin.sum_univ_four, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Trace of a block-diag-B (second slot) 4×4 matrix:
    `tr(kron2 A proj0 + kron2 B proj1) = tr(A) + tr(B)`.
    Companion to `trace_block_diag_first`. Iter 241 infrastructure. -/
lemma trace_block_diag_second (A B : Mat2) :
    (kron2 A proj0 + kron2 B proj1).trace = A.trace + B.trace := by
  simp [Matrix.trace, Matrix.diag, Matrix.add_apply, kron2, proj0, proj1,
        Matrix.of_apply, Fin.sum_univ_four, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
  ring


/-- `kron2 proj0 1 + kron2 proj1 1 = 1` (the resolution of identity in qubit A). -/
lemma kron2_proj0_one_add_kron2_proj1_one :
    kron2 proj0 (1 : Mat2) + kron2 proj1 (1 : Mat2) = (1 : Mat4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kron2, proj0, proj1, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]

/-- `kron2 1 (Diag(1, u)) = Diag(1, u, 1, u)`. The 4×4 expansion of
    (I⊗Diag(1,u)) is the 4-diagonal that alternates 1 and u
    (each block of size 2). -/
lemma kron2_one_diag_one_u (u : ℂ) :
    kron2 (1 : Mat2) (Matrix.diagonal ![1, u]) =
    (Matrix.diagonal ![1, u, 1, u] : Mat4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kron2, Matrix.diagonal, Matrix.of_apply, Matrix.one_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Pointwise multiplication of two specific diagonal Mat4 matrices:
    `Diag(1,u₀,1,u₀) · Diag(1,1,u₀,u₁) = Diag(1,u₀,u₀,u₀·u₁)`. Used in
    PY24 Lemma 3.3 (⇐) Case 2 to compute `(kron2 1 P) · Diag(1,1,u₀,u₁)`. -/
lemma diag_one_u_one_u_mul_diag_one_one_u_u (u₀ u₁ : ℂ) :
    (Matrix.diagonal ![1, u₀, 1, u₀] : Mat4) * Matrix.diagonal ![1, 1, u₀, u₁] =
    Matrix.diagonal ![1, u₀, u₀, u₀ * u₁] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Matrix.mul_apply, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Helper for 3.3 (⇐) Case 2: V := `kron2 1 proj0 + kron2 pauliX proj1`
    (= CNOT_{B→A}, swap of positions 1 and 3) is unitary. -/
lemma isUnitary4_kron2_one_proj0_pauliX_proj1 :
    IsUnitary4 (kron2 (1 : Mat2) proj0 + kron2 pauliX proj1) := by
  unfold IsUnitary4
  rw [block_diag_second_conjT, Matrix.conjTranspose_one,
      block_diag_second_mul, Matrix.one_mul]
  have hX : pauliX.conjTranspose * pauliX = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliX, Matrix.conjTranspose_apply, Matrix.mul_apply,
            Matrix.of_apply, Fin.sum_univ_two]
  rw [hX, kron2_one_proj0_add_kron2_one_proj1]

/-- Block-diag-A diagonal decomposition: `kron2 proj0 Diag(a,b) + kron2 proj1
    Diag(p,q) = Diag(a, b, p, q)`. Used in PY24 A.6 / A.27. -/
lemma kron2_proj0_diag_add_kron2_proj1_diag (a b p q : ℂ) :
    kron2 proj0 (Matrix.diagonal ![a, b]) + kron2 proj1 (Matrix.diagonal ![p, q])
      = Matrix.diagonal ![a, b, p, q] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kron2, proj0, proj1, Matrix.add_apply, Matrix.of_apply, Matrix.diagonal]

/-- The Mat4 diagonal `Diag(1, 1, u₀, u₁) = C(Diag(u₀, u₁))` decomposes as
    block-diag-A `kron2 proj0 1 + kron2 proj1 (Diag u₀ u₁)`. Used by Lemma 3.3. -/
lemma diag_one_one_u_v_decomp (u₀ u₁ : ℂ) :
    (Matrix.diagonal ![1, 1, u₀, u₁] : Mat4) =
    kron2 proj0 (1 : Mat2) + kron2 proj1 (Matrix.diagonal ![u₀, u₁]) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kron2, proj0, proj1, Matrix.diagonal, Matrix.add_apply, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one]

/-- A unitary times a diagonal of unit-modulus complex numbers is unitary.
    Specialized to 2×2; used by Lemma 3.3 to apply A.3 to `P · Diag(u₀, u₁)`. -/
lemma isUnitary2_mul_diag_unit (P : Mat2) (hP : IsUnitary2 P)
    (u₀ u₁ : ℂ) (hu₀ : Complex.normSq u₀ = 1) (hu₁ : Complex.normSq u₁ = 1) :
    IsUnitary2 (P * Matrix.diagonal ![u₀, u₁]) := by
  change (P * Matrix.diagonal ![u₀, u₁]).conjTranspose *
       (P * Matrix.diagonal ![u₀, u₁]) = 1
  rw [Matrix.conjTranspose_mul, mul_assoc,
      ← mul_assoc P.conjTranspose, show P.conjTranspose * P = 1 from hP, one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal,
          Matrix.cons_val_zero, Matrix.cons_val_one]
  · -- (0,0): conj(u₀) * u₀ = 1
    rw [show starRingEnd ℂ u₀ * u₀ = (Complex.normSq u₀ : ℂ) by
          rw [mul_comm]; exact (Complex.mul_conj u₀).symm ▸ rfl]
    exact_mod_cast hu₀
  · -- (1,1): conj(u₁) * u₁ = 1
    rw [show starRingEnd ℂ u₁ * u₁ = (Complex.normSq u₁ : ℂ) by
          rw [mul_comm]; exact (Complex.mul_conj u₁).symm ▸ rfl]
    exact_mod_cast hu₁

/-- The determinant of a 2×2 unitary has unit modulus (`normSq = 1`).
    Proof: from `P†·P = 1`, take det → `conj(det P)·det P = 1`. Useful for
    deriving `det P ≠ 0` and field manipulations in 3.3 (⇒). -/
lemma normSq_det_of_isUnitary2 {P : Mat2} (hP : IsUnitary2 P) :
    Complex.normSq P.det = 1 := by
  have h1 : star P.det * P.det = 1 := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, hP, Matrix.det_one]
  have h2 : ((Complex.normSq P.det : ℝ) : ℂ) = (1 : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    exact h1
  exact_mod_cast h2

/-- The determinant of a 2×2 unitary is nonzero. Direct corollary of
    `normSq_det_of_isUnitary2 = 1 ≠ 0`. -/
lemma det_ne_zero_of_isUnitary2 {P : Mat2} (hP : IsUnitary2 P) :
    P.det ≠ 0 := by
  intro h
  have hns : Complex.normSq P.det = 1 := normSq_det_of_isUnitary2 hP
  rw [h, Complex.normSq_zero] at hns
  exact zero_ne_one hns

/-- The determinant of a 4×4 unitary has unit modulus (`normSq = 1`). -/
lemma normSq_det_of_isUnitary4 {V : Mat4} (hV : IsUnitary4 V) :
    Complex.normSq V.det = 1 := by
  have h1 : star V.det * V.det = 1 := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, hV, Matrix.det_one]
  have h2 : ((Complex.normSq V.det : ℝ) : ℂ) = (1 : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    exact h1
  exact_mod_cast h2

/-- The determinant of a 4×4 unitary is nonzero. -/
lemma det_ne_zero_of_isUnitary4 {V : Mat4} (hV : IsUnitary4 V) :
    V.det ≠ 0 := by
  intro h
  have hns : Complex.normSq V.det = 1 := normSq_det_of_isUnitary4 hV
  rw [h, Complex.normSq_zero] at hns
  exact zero_ne_one hns

/-- Determinant of a Mat2 diagonal: `det(Diag(a, b)) = a · b`. -/
lemma det_diagonal_Fin2 (a b : ℂ) :
    Matrix.det (Matrix.diagonal ![a, b] : Mat2) = a * b := by
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]


/-- Determinant of a Mat4 diagonal: `det(Diag(a,b,c,d)) = a · b · c · d`. -/
lemma det_diagonal_Fin4 (a b c d : ℂ) :
    Matrix.det (Matrix.diagonal ![a, b, c, d] : Mat4) = a * b * c * d := by
  rw [Matrix.det_diagonal, Fin.prod_univ_four]
  have e2 : (![a, b, c, d] : Fin 4 → ℂ) 2 = c := rfl
  have e3 : (![a, b, c, d] : Fin 4 → ℂ) 3 = d := rfl
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, e2, e3]

/-- Mat2 determinant formula: `det M = M[0,0]·M[1,1] - M[0,1]·M[1,0]`. -/
lemma Mat2.det_apply (M : Mat2) :
    M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := by
  rw [Matrix.det_fin_two]

/-- Mat2 trace formula: `tr M = M[0,0] + M[1,1]`. -/
lemma Mat2.trace_apply (M : Mat2) :
    M.trace = M 0 0 + M 1 1 := by
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- Mat4 trace formula: `tr M = M[0,0] + M[1,1] + M[2,2] + M[3,3]`. -/
lemma Mat4.trace_apply (M : Mat4) :
    M.trace = M 0 0 + M 1 1 + M 2 2 + M 3 3 := by
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_four]

/-- Mat2 variant of `trace_cube_eq_of_unitary_similar` — same proof. Used
    in 3.3 (⇒) M1/M2 case for the e_3 elementary symmetric polynomial eqn. -/
lemma trace_cube_eq_of_unitary_similar2 {V M D : Mat2} (hV : IsUnitary2 V)
    (hsim : V.conjTranspose * M * V = D) :
    (M * M * M).trace = (D * D * D).trace := by
  have hVVdag : V * V.conjTranspose = 1 := mul_eq_one_comm.mp hV
  have hD_cube : D * D * D = V.conjTranspose * (M * M * M) * V := by
    rw [← hsim]
    have e : V.conjTranspose * M * V * (V.conjTranspose * M * V) *
             (V.conjTranspose * M * V) =
             V.conjTranspose * M * (V * V.conjTranspose) * M *
             (V * V.conjTranspose) * M * V := by noncomm_ring
    rw [e]
    simp only [hVVdag, Matrix.mul_one]
    noncomm_ring
  rw [hD_cube, Matrix.trace_mul_comm (V.conjTranspose * (M * M * M)) V,
      ← mul_assoc V V.conjTranspose (M * M * M), hVVdag, Matrix.one_mul]

/-- A 2×2 matrix unitary-similar to a double-eigenvalue diagonal `Diag(a, a)`
    is the scalar matrix `a • 1`. Used in `py24_lemma_3_3` (⇒) M1/M2 case
    when P has degenerate spectrum (a = b), allowing one to conclude
    `P · Diag(u₀, u₁) = Diag(a·u₀, a·u₁)` and hence `u₀ = u₁` from the
    eigenvalue match `a·u₀ = a·u₁ = d`. Promoted to public (iter 218) since
    it's a clean general structural fact about 2×2 unitaries with degenerate
    spectrum. -/
lemma mat2_scalar_of_double_eigenvalue
    {P V : Mat2} (hV : IsUnitary2 V) {a : ℂ}
    (h_diag : V.conjTranspose * P * V = Matrix.diagonal ![a, a]) :
    P = a • (1 : Mat2) := by
  have hVVdag : V * V.conjTranspose = 1 := mul_eq_one_comm.mp hV
  have h_diag_eq_smul : (Matrix.diagonal ![a, a] : Mat2) = a • (1 : Mat2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal, Matrix.smul_apply, smul_eq_mul]
  -- Sandwich: P = V · (V† · P · V) · V†.
  have h_P_eq : P = V * (V.conjTranspose * P * V) * V.conjTranspose := by
    have e : V * (V.conjTranspose * P * V) * V.conjTranspose =
             V * V.conjTranspose * P * (V * V.conjTranspose) := by noncomm_ring
    rw [e, hVVdag, Matrix.one_mul, Matrix.mul_one]
  rw [h_P_eq, h_diag, h_diag_eq_smul]
  -- Goal: V · (a • 1) · V† = a • 1.
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hVVdag]

/-- Mat2 variant of `trace_sq_eq_of_unitary_similar` — same proof, used to
    apply trace-square-equality to hVP_diag and hVPD_diag in 3.3 (⇒). -/
lemma trace_sq_eq_of_unitary_similar2 {V M D : Mat2} (hV : IsUnitary2 V)
    (hsim : V.conjTranspose * M * V = D) :
    (M * M).trace = (D * D).trace := by
  have hVVdag : V * V.conjTranspose = 1 := mul_eq_one_comm.mp hV
  have hD_sq : D * D = V.conjTranspose * (M * M) * V := by
    rw [← hsim]
    rw [show V.conjTranspose * M * V * (V.conjTranspose * M * V) =
            V.conjTranspose * M * (V * V.conjTranspose) * M * V from by noncomm_ring,
        hVVdag, Matrix.mul_one]
    noncomm_ring
  rw [hD_sq, Matrix.trace_mul_comm (V.conjTranspose * (M * M)) V,
      ← mul_assoc V V.conjTranspose (M * M), hVVdag, Matrix.one_mul]

/-- For 4×4 matrices M, D, V with V unitary and V†·M·V = D:
    `trace(M³) = trace(D³)`. Same template as `trace_sq_eq_of_unitary_similar`,
    extended one product. Used in 3.3 (⇒) for the e_3 equation. -/
lemma trace_cube_eq_of_unitary_similar {V M D : Mat4} (hV : IsUnitary4 V)
    (hsim : V.conjTranspose * M * V = D) :
    (M * M * M).trace = (D * D * D).trace := by
  have hVVdag : V * V.conjTranspose = 1 := mul_eq_one_comm.mp hV
  have hD_cube : D * D * D = V.conjTranspose * (M * M * M) * V := by
    rw [← hsim]
    have e : V.conjTranspose * M * V * (V.conjTranspose * M * V) *
             (V.conjTranspose * M * V) =
             V.conjTranspose * M * (V * V.conjTranspose) * M *
             (V * V.conjTranspose) * M * V := by noncomm_ring
    rw [e]
    simp only [hVVdag, Matrix.mul_one]
    noncomm_ring
  rw [hD_cube, Matrix.trace_mul_comm (V.conjTranspose * (M * M * M)) V,
      ← mul_assoc V V.conjTranspose (M * M * M), hVVdag, Matrix.one_mul]

/-- For 4×4 matrices M, D, V with V unitary and V†·M·V = D:
    `trace(M²) = trace(D²)`. Proof: D² = V†·M²·V (cancel V·V†=1 in middle),
    then cyclic trace gives trace(D²) = trace(M²). Used in 3.3 (⇒) for the
    e_2 elementary symmetric polynomial equation. -/
lemma trace_sq_eq_of_unitary_similar {V M D : Mat4} (hV : IsUnitary4 V)
    (hsim : V.conjTranspose * M * V = D) :
    (M * M).trace = (D * D).trace := by
  have hVVdag : V * V.conjTranspose = 1 := mul_eq_one_comm.mp hV
  have hD_sq : D * D = V.conjTranspose * (M * M) * V := by
    rw [← hsim]
    rw [show V.conjTranspose * M * V * (V.conjTranspose * M * V) =
            V.conjTranspose * M * (V * V.conjTranspose) * M * V from by noncomm_ring,
        hVVdag, Matrix.mul_one]
    noncomm_ring
  rw [hD_sq, Matrix.trace_mul_comm (V.conjTranspose * (M * M)) V,
      ← mul_assoc V V.conjTranspose (M * M), hVVdag, Matrix.one_mul]

/-- `(I ⊗ P) · C(Diag(u₀, u₁))` absorbs into block-diag-A form
    `kron2 proj0 P + kron2 proj1 (P · Diag u₀ u₁)`. Used by Lemma 3.3. -/
lemma I_P_mul_C_Diag_decomp (P : Mat2) (u₀ u₁ : ℂ) :
    (kron2 (1 : Mat2) P) *
      (kron2 proj0 (1 : Mat2) + kron2 proj1 (Matrix.diagonal ![u₀, u₁])) =
    kron2 proj0 P + kron2 proj1 (P * Matrix.diagonal ![u₀, u₁]) := by
  rw [mul_add, kron2_mul, kron2_mul, one_mul, one_mul, mul_one]

theorem py24_lemma_A_6 (P Q : Mat2) (_hP : IsUnitary2 P) (_hQ : IsUnitary2 Q)
    (a b p q : ℂ)
    (hPeig : ∃ V : Mat2, IsUnitary2 V ∧
      V.conjTranspose * P * V = Matrix.diagonal ![a, b])
    (hQeig : ∃ W : Mat2, IsUnitary2 W ∧
      W.conjTranspose * Q * W = Matrix.diagonal ![p, q]) :
    ∃ U : Mat4, IsUnitary4 U ∧
      U.conjTranspose * (kron2 proj0 P + kron2 proj1 Q) * U =
      Matrix.diagonal ![a, b, p, q] := by
  obtain ⟨V, hV, hVPV⟩ := hPeig
  obtain ⟨W, hW, hWQW⟩ := hQeig
  refine ⟨kron2 proj0 V + kron2 proj1 W, ?_, ?_⟩
  · unfold IsUnitary4
    rw [block_diag_first_conjT, block_diag_first_mul]
    unfold IsUnitary2 at hV hW
    rw [hV, hW, kron2_proj0_one_add_kron2_proj1_one]
  · rw [block_diag_first_conjT, block_diag_first_mul, block_diag_first_mul,
        hVPV, hWQW, kron2_proj0_diag_add_kron2_proj1_diag]

/-- **Newton's identity** (4-variable, e_2 form): the e_2 elementary symmetric
    polynomial of `{a, b, p, q}` equals `(E² - T)/2` where E = e_1
    (sum) and T = p_2 (sum of squares). Pure algebraic identity over ℂ;
    used to derive Vieta e_2 from power-sum information. -/
lemma e2_vieta_from_power_sums (a b p q E T : ℂ)
    (h_e1 : a + b + p + q = E)
    (h_p2 : a ^ 2 + b ^ 2 + p ^ 2 + q ^ 2 = T) :
    a*b + a*p + a*q + b*p + b*q + p*q = (E^2 - T) / 2 := by
  linear_combination ((a + b + p + q + E) / 2) * h_e1 + (-1/2) * h_p2

/-- **Multiset matching via direct algebra** (general): if elementary
    symmetric polynomials e_1, e_2, e_3, e_4 of `{a, b, p, q}` match those
    of `{α, β, γ, δ}`, then each `x ∈ {a, b, p, q}` is a root of
    `(X-α)(X-β)(X-γ)(X-δ)`. Each consequence proven by single
    `linear_combination`. Companion to `multiset_match_4_eq_pair_pair`
    (which assumes the more specific {c, c, d, d} pair-pair structure
    and produces clean disjunctions); this version handles the
    4-distinct-values case but only yields the polynomial-root form. -/
lemma multiset_match_4_general
    {a b p q α β γ δ : ℂ}
    (h_e1 : a + b + p + q = α + β + γ + δ)
    (h_e2 : a * b + a * p + a * q + b * p + b * q + p * q
          = α * β + α * γ + α * δ + β * γ + β * δ + γ * δ)
    (h_e3 : a * b * p + a * b * q + a * p * q + b * p * q
          = α * β * γ + α * β * δ + α * γ * δ + β * γ * δ)
    (h_e4 : a * b * p * q = α * β * γ * δ) :
    ((a - α) * (a - β) * (a - γ) * (a - δ) = 0) ∧
    ((b - α) * (b - β) * (b - γ) * (b - δ) = 0) ∧
    ((p - α) * (p - β) * (p - γ) * (p - δ) = 0) ∧
    ((q - α) * (q - β) * (q - γ) * (q - δ) = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination a ^ 3 * h_e1 - a ^ 2 * h_e2 + a * h_e3 - h_e4
  · linear_combination b^3 * h_e1 - b^2 * h_e2 + b * h_e3 - h_e4
  · linear_combination p^3 * h_e1 - p^2 * h_e2 + p * h_e3 - h_e4
  · linear_combination q^3 * h_e1 - q^2 * h_e2 + q * h_e3 - h_e4

/-- **Multiset matching via direct algebra** (4-into-pair): if the elementary
    symmetric polynomials e_1 through e_4 of `{a, b, p, q}` match those of
    `{c, c, d, d}`, then each of `a, b, p, q` equals `c` or `d`. Avoids
    Mathlib's `Polynomial.roots` machinery — the polynomial identity
    `(X-a)(X-b)(X-p)(X-q) = (X-c)²(X-d)²` is encoded in the e_k equations,
    so plugging in any of `a, b, p, q` yields `(x-c)²·(x-d)² = 0`, hence
    `(x-c)·(x-d) = 0` over ℂ. Used in `py24_lemma_3_3` (⇒) M1/M2 case
    (iter 207). -/
lemma multiset_match_4_eq_pair_pair
    {a b p q c d : ℂ}
    (h_e1 : a + b + p + q = 2 * c + 2 * d)
    (h_e2 : a * b + a * p + a * q + b * p + b * q + p * q = c ^ 2 + 4 * c * d + d ^ 2)
    (h_e3 : a * b * p + a * b * q + a * p * q + b * p * q = 2 * c * d * (c + d))
    (h_e4 : a * b * p * q = c ^ 2 * d ^ 2) :
    (a = c ∨ a = d) ∧ (b = c ∨ b = d) ∧ (p = c ∨ p = d) ∧ (q = c ∨ q = d) := by
  have h_a : (a - c) * (a - d) = 0 := by
    have h_sq : (a - c) ^ 2 * (a - d) ^ 2 = 0 := by
      linear_combination a ^ 3 * h_e1 - a ^ 2 * h_e2 + a * h_e3 - h_e4
    have h : ((a - c) * (a - d)) ^ 2 = 0 := by linear_combination h_sq
    exact sq_eq_zero_iff.mp h
  have h_b : (b - c) * (b - d) = 0 := by
    have h_sq : (b - c)^2 * (b - d)^2 = 0 := by
      linear_combination b^3 * h_e1 - b^2 * h_e2 + b * h_e3 - h_e4
    have h : ((b - c) * (b - d))^2 = 0 := by linear_combination h_sq
    exact sq_eq_zero_iff.mp h
  have h_p : (p - c) * (p - d) = 0 := by
    have h_sq : (p - c)^2 * (p - d)^2 = 0 := by
      linear_combination p^3 * h_e1 - p^2 * h_e2 + p * h_e3 - h_e4
    have h : ((p - c) * (p - d))^2 = 0 := by linear_combination h_sq
    exact sq_eq_zero_iff.mp h
  have h_q : (q - c) * (q - d) = 0 := by
    have h_sq : (q - c)^2 * (q - d)^2 = 0 := by
      linear_combination q^3 * h_e1 - q^2 * h_e2 + q * h_e3 - h_e4
    have h : ((q - c) * (q - d))^2 = 0 := by linear_combination h_sq
    exact sq_eq_zero_iff.mp h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases mul_eq_zero.mp h_a with h | h
    · left; linear_combination h
    · right; linear_combination h
  · rcases mul_eq_zero.mp h_b with h | h
    · left; linear_combination h
    · right; linear_combination h
  · rcases mul_eq_zero.mp h_p with h | h
    · left; linear_combination h
    · right; linear_combination h
  · rcases mul_eq_zero.mp h_q with h | h
    · left; linear_combination h
    · right; linear_combination h

/-- **PY24 Lemma 3.3** (eigenvalue characterization for `(I⊗P)·C(Diag(u₀,u₁))`):
    There exist P unitary and complex numbers c, d such that
    `(I⊗P)·C(Diag(u₀,u₁))` is unitarily similar to `Diag(c,c,d,d)`
    if and only if `u₀ = u₁` or `u₀·u₁ = 1`.

    **Proof structure**:
    - (⇐) direction (constructive): two cases. u₀=u₁ uses P=I, V=I; u₀·u₁=1
      uses P=Diag(1,u₀), V = kron2 1 proj0 + kron2 pauliX proj1 (CNOT_{B→A}).
    - (⇒) direction (deductive): apply spectral theorem (A.3) to P and
      P·Diag(u₀,u₁) to extract eigenvalues a, b, p, q. From similarity to
      Diag(c,c,d,d), derive elementary symmetric polynomial matching:
      e_1, e_2, e_3, e_4 of `{a,b,p,q}` = those of `{c,c,d,d}`. Case-split
      on whether a+b = c+d:
        - **M3 case** (a+b = c+d): derive ab = cd and pq = cd, conclude
          u₀·u₁ = 1.
        - **M1/M2 case** (a+b ≠ c+d): use `multiset_match_4_eq_pair_pair`
          (iter 219) to conclude each x ∈ {a,b,p,q} ∈ {c, d}; case-split
          forces a = b (and similarly p = q via a²·(p-q)² = 0); apply
          `mat2_scalar_of_double_eigenvalue` (iter 203) to get P scalar,
          then `P · Diag(u₀,u₁) = Diag(a·u₀, a·u₁) = Diag(p, p)` gives
          a·u₀ = a·u₁, hence u₀ = u₁ (a ≠ 0 since unitary eigenvalue).

    The (⇒) direction's M1/M2 closure (iters 205-213) avoids Mathlib's
    `Polynomial.roots` machinery via direct `linear_combination` on the
    e_k equations (~6 iters of work). -/
theorem py24_lemma_3_3 (u₀ u₁ : ℂ)
    (hu₀ : Complex.normSq u₀ = 1) (hu₁ : Complex.normSq u₁ = 1) :
    (∃ P : Mat2, IsUnitary2 P ∧ ∃ c d : ℂ, ∃ V : Mat4, IsUnitary4 V ∧
      V.conjTranspose * (kron2 (1 : Mat2) P * Matrix.diagonal ![1, 1, u₀, u₁]) * V =
      Matrix.diagonal ![c, c, d, d])
    ↔ (u₀ = u₁ ∨ u₀ * u₁ = 1) := by
  constructor
  · -- (⇒) direction: from V†·((I⊗P)·C(Diag))·V = Diag(c,c,d,d), derive constraint.
    rintro ⟨P, hP, c, d, V, hV, hVP⟩
    -- Rewrite the chain to block-diag-A form.
    rw [diag_one_one_u_v_decomp, I_P_mul_C_Diag_decomp] at hVP
    -- hVP : V† · (kron2 proj0 P + kron2 proj1 (P · Diag(u₀,u₁))) · V = Diag(c,c,d,d).
    -- Apply A.3 to P → get eigenvalues a, b and diagonalization V_P.
    obtain ⟨a, b, V_P, hVP_unit, hVP_diag⟩ := py24_lemma_A_3 P hP
    -- hVP_diag : V_P.conjTranspose * P * V_P = Matrix.diagonal ![a, b]
    -- Apply A.3 to P · Diag(u₀, u₁) → get eigenvalues p, q and V_PD.
    have hPD : IsUnitary2 (P * Matrix.diagonal ![u₀, u₁]) :=
      isUnitary2_mul_diag_unit P hP u₀ u₁ hu₀ hu₁
    obtain ⟨p, q, V_PD, hVPD_unit, hVPD_diag⟩ :=
      py24_lemma_A_3 (P * Matrix.diagonal ![u₀, u₁]) hPD
    -- hVPD_diag : V_PD.conjTranspose * (P · Diag(u₀,u₁)) * V_PD = Diag ![p, q]
    -- Apply A.6 to combine into Mat4 diagonalization with eigenvalues [a,b,p,q].
    obtain ⟨V', hV'_unit, hV'_diag⟩ :=
      py24_lemma_A_6 P (P * Matrix.diagonal ![u₀, u₁]) hP hPD a b p q
        ⟨V_P, hVP_unit, hVP_diag⟩ ⟨V_PD, hVPD_unit, hVPD_diag⟩
    -- hV'_diag : V'† · (kron2 proj0 P + kron2 proj1 (P·Diag)) · V' = Diag ![a,b,p,q]
    -- We now have TWO diagonalizations of the same Mat4 M:
    --   hVP   : V† · M · V = Diag ![c, c, d, d]      (from hypothesis after rewrite)
    --   hV'_diag : V'† · M · V' = Diag ![a, b, p, q]  (from A.6)
    -- Trace equation: a + b + p + q = 2c + 2d via cyclic trace invariance.
    have h_trace_eq :
        (Matrix.diagonal ![a, b, p, q] : Mat4).trace =
        (Matrix.diagonal ![c, c, d, d] : Mat4).trace := by
      have hVVdag : V * V.conjTranspose = 1 := mul_eq_one_comm.mp hV
      have hV'V'dag : V' * V'.conjTranspose = 1 := mul_eq_one_comm.mp hV'_unit
      have key1 : (V.conjTranspose *
            (kron2 proj0 P + kron2 proj1 (P * Matrix.diagonal ![u₀, u₁])) * V).trace
          = (kron2 proj0 P + kron2 proj1 (P * Matrix.diagonal ![u₀, u₁])).trace := by
        rw [Matrix.trace_mul_comm, ← mul_assoc, hVVdag, Matrix.one_mul]
      have key2 : (V'.conjTranspose *
            (kron2 proj0 P + kron2 proj1 (P * Matrix.diagonal ![u₀, u₁])) * V').trace
          = (kron2 proj0 P + kron2 proj1 (P * Matrix.diagonal ![u₀, u₁])).trace := by
        rw [Matrix.trace_mul_comm, ← mul_assoc, hV'V'dag, Matrix.one_mul]
      rw [← hV'_diag, key2, ← key1, hVP]
    -- Arithmetic form: a + b + p + q = 2*c + 2*d.
    have h_trace_sum : a + b + p + q = 2 * c + 2 * d := by
      have h := h_trace_eq
      simp only [Matrix.trace_diagonal, Fin.sum_univ_four,
                 Matrix.cons_val_zero, Matrix.cons_val_one] at h
      have e3 : (![a, b, p, q] : Fin 4 → ℂ) 2 = p := rfl
      have e4 : (![a, b, p, q] : Fin 4 → ℂ) 3 = q := rfl
      have f3 : (![c, c, d, d] : Fin 4 → ℂ) 2 = d := rfl
      have f4 : (![c, c, d, d] : Fin 4 → ℂ) 3 = d := rfl
      rw [e3, e4, f3, f4] at h
      linear_combination h
    -- Determinant equation: a * b * p * q = c * c * d * d.
    have h_det_prod : a * b * p * q = c * c * d * d := by
      -- Helper: det(W† · M · W) = det(M) for unitary W.
      have det_invariant : ∀ (W : Mat4) (hW : IsUnitary4 W) (M : Mat4),
          (W.conjTranspose * M * W).det = M.det := by
        intros W hW M
        rw [Matrix.det_mul, Matrix.det_mul]
        have h : W.conjTranspose.det * W.det = 1 := by
          rw [← Matrix.det_mul, hW, Matrix.det_one]
        linear_combination M.det * h
      -- Apply to V' and V.
      have h_via_V' : Matrix.det (Matrix.diagonal ![a, b, p, q] : Mat4) =
                      Matrix.det (kron2 proj0 P + kron2 proj1 (P * Matrix.diagonal ![u₀, u₁])) := by
        rw [← hV'_diag]; exact det_invariant V' hV'_unit _
      have h_via_V : Matrix.det (Matrix.diagonal ![c, c, d, d] : Mat4) =
                     Matrix.det (kron2 proj0 P + kron2 proj1 (P * Matrix.diagonal ![u₀, u₁])) := by
        rw [← hVP]; exact det_invariant V hV _
      have h1 : Matrix.det (Matrix.diagonal ![a, b, p, q] : Mat4) =
                Matrix.det (Matrix.diagonal ![c, c, d, d] : Mat4) := h_via_V'.trans h_via_V.symm
      rw [Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_four,
          Fin.prod_univ_four] at h1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1
      have e3 : (![a, b, p, q] : Fin 4 → ℂ) 2 = p := rfl
      have e4 : (![a, b, p, q] : Fin 4 → ℂ) 3 = q := rfl
      have f3 : (![c, c, d, d] : Fin 4 → ℂ) 2 = d := rfl
      have f4 : (![c, c, d, d] : Fin 4 → ℂ) 3 = d := rfl
      rw [e3, e4, f3, f4] at h1
      linear_combination h1
    -- Vieta: a + b = tr(P) and a * b = det(P), from V_P†·P·V_P = Diag(a,b).
    have h_a_b_e0 : (![a, b] : Fin 2 → ℂ) 0 = a := rfl
    have h_a_b_e1 : (![a, b] : Fin 2 → ℂ) 1 = b := rfl
    have h_P_trace : a + b = P.trace := by
      have h := congrArg Matrix.trace hVP_diag
      rw [Matrix.trace_diagonal, Fin.sum_univ_two, h_a_b_e0, h_a_b_e1] at h
      rw [Matrix.trace_mul_comm, ← mul_assoc, mul_eq_one_comm.mp hVP_unit,
          Matrix.one_mul] at h
      exact h.symm
    have h_P_det : a * b = P.det := by
      have h := congrArg Matrix.det hVP_diag
      rw [Matrix.det_diagonal, Fin.prod_univ_two, h_a_b_e0, h_a_b_e1,
          Matrix.det_mul, Matrix.det_mul] at h
      have h_VPdag : V_P.conjTranspose.det * V_P.det = 1 := by
        rw [← Matrix.det_mul, hVP_unit, Matrix.det_one]
      linear_combination -h + P.det * h_VPdag
    -- Vieta for P · Diag(u₀,u₁): p + q = tr(P · Diag), p * q = det(P) * (u₀ * u₁).
    have h_p_q_e0 : (![p, q] : Fin 2 → ℂ) 0 = p := rfl
    have h_p_q_e1 : (![p, q] : Fin 2 → ℂ) 1 = q := rfl
    have h_u_e0 : (![u₀, u₁] : Fin 2 → ℂ) 0 = u₀ := rfl
    have h_u_e1 : (![u₀, u₁] : Fin 2 → ℂ) 1 = u₁ := rfl
    have h_PD_trace : p + q = (P * Matrix.diagonal ![u₀, u₁]).trace := by
      have h := congrArg Matrix.trace hVPD_diag
      rw [Matrix.trace_diagonal, Fin.sum_univ_two, h_p_q_e0, h_p_q_e1] at h
      rw [Matrix.trace_mul_comm, ← mul_assoc, mul_eq_one_comm.mp hVPD_unit,
          Matrix.one_mul] at h
      exact h.symm
    have h_PD_det : p * q = P.det * (u₀ * u₁) := by
      have h := congrArg Matrix.det hVPD_diag
      rw [Matrix.det_diagonal, Fin.prod_univ_two, h_p_q_e0, h_p_q_e1,
          Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
          Fin.prod_univ_two, h_u_e0, h_u_e1] at h
      have h_VPDdag : V_PD.conjTranspose.det * V_PD.det = 1 := by
        rw [← Matrix.det_mul, hVPD_unit, Matrix.det_one]
      linear_combination -h + (P.det * (u₀ * u₁)) * h_VPDdag
    -- Key combined equation: (det P)² · u₀ · u₁ = c² · d².
    -- Derived from a*b*p*q = c²d² (h_det_prod) and a*b = det P, p*q = det P · u₀u₁.
    have h_key : P.det * P.det * (u₀ * u₁) = c * c * d * d := by
      have h := h_det_prod
      rw [show a * b * p * q = (a * b) * (p * q) from by ring,
          h_P_det, h_PD_det] at h
      linear_combination h
    -- Trace-square equation: tr(M²) = tr(D²) (e_2 of multisets).
    -- M = kron2 proj0 P + kron2 proj1 (P · Diag(u₀,u₁)), D = Diag(c,c,d,d).
    have h_trace_sq_eq :
        ((kron2 proj0 P + kron2 proj1 (P * Matrix.diagonal ![u₀, u₁])) *
         (kron2 proj0 P + kron2 proj1 (P * Matrix.diagonal ![u₀, u₁]))).trace =
        ((Matrix.diagonal ![c, c, d, d] : Mat4) *
         Matrix.diagonal ![c, c, d, d]).trace :=
      trace_sq_eq_of_unitary_similar hV hVP
    -- Expand LHS: M² = block-diag-A with blocks P² and (P·Diag)². So
    -- tr(M²) = tr(P²) + tr((P·Diag)²).
    have h_trace_sq_lhs :
        ((kron2 proj0 P + kron2 proj1 (P * Matrix.diagonal ![u₀, u₁])) *
         (kron2 proj0 P + kron2 proj1 (P * Matrix.diagonal ![u₀, u₁]))).trace =
        (P * P).trace + (P * Matrix.diagonal ![u₀, u₁] *
                         (P * Matrix.diagonal ![u₀, u₁])).trace := by
      rw [block_diag_first_mul, trace_block_diag_first]
    -- Expand RHS: tr(Diag(c,c,d,d)²) = 2c² + 2d² via diagonal_mul_diagonal.
    have h_trace_sq_rhs :
        ((Matrix.diagonal ![c, c, d, d] : Mat4) *
         Matrix.diagonal ![c, c, d, d]).trace = 2 * c * c + 2 * d * d := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Fin.sum_univ_four]
      have e2 : (![c, c, d, d] : Fin 4 → ℂ) 2 = d := rfl
      have e3 : (![c, c, d, d] : Fin 4 → ℂ) 3 = d := rfl
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e2, e3]
      ring
    -- Derive tr(P²) = a² + b² via Mat2 trace-square-equality + diagonalization.
    have h_trace_P_sq : (P * P).trace = a * a + b * b := by
      have h := trace_sq_eq_of_unitary_similar2 hVP_unit hVP_diag
      rw [h, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Fin.sum_univ_two]
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    -- Symmetric: tr((P·Diag)²) = p² + q² from hVPD_diag.
    have h_trace_PD_sq :
        (P * Matrix.diagonal ![u₀, u₁] *
         (P * Matrix.diagonal ![u₀, u₁])).trace = p * p + q * q := by
      have h := trace_sq_eq_of_unitary_similar2 hVPD_unit hVPD_diag
      rw [h, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Fin.sum_univ_two]
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    -- Assemble the e_2 equation: a² + b² + p² + q² = 2c² + 2d².
    have h_e2 : a * a + b * b + p * p + q * q = 2 * c * c + 2 * d * d := by
      have h1 := h_trace_sq_eq
      rw [h_trace_sq_lhs, h_trace_sq_rhs, h_trace_P_sq, h_trace_PD_sq] at h1
      linear_combination h1
    -- Derive `(a*b) * (p*q) = (cd)²` from h_key + h_PD_det + h_P_det.
    have h_abpq : (a * b) * (p * q) = c * c * d * d := by
      have h_key' := h_key
      rw [← h_P_det] at h_key'
      -- h_key' : (a*b) * (a*b) * (u₀ * u₁) = c*c*d*d
      rw [h_PD_det, ← h_P_det]
      linear_combination h_key'
    -- Derive `ab + pq = (a+b-c-d)² + 2cd` from h_trace_sum + h_e2.
    -- Coefficients (computed): α = (-(a+b) + (p+q))/2 + (c+d), β = -1/2.
    have h_e_f_sum : a*b + p*q = (a + b - c - d)^2 + 2*c*d := by
      linear_combination
        ((-(a+b) + (p+q))/2 + (c+d)) * h_trace_sum + (-1/2) * h_e2
    -- Derive the key factoring identity: `(ab - cd)² = ab · (a+b-c-d)²`.
    -- Coefficients: α = -1 for h_abpq, β = a*b for h_e_f_sum.
    have h_factor : (a*b - c*d)^2 = a*b * (a + b - c - d)^2 := by
      linear_combination -h_abpq + (a*b) * h_e_f_sum
    -- Case-split on whether `a + b = c + d`.
    by_cases h_eq_sum : a + b = c + d
    · -- Case M3 (a+b = c+d): conclude u₀·u₁ = 1.
      right
      -- Step 1: ab = cd from h_factor.
      have h_zero : (a*b - c*d)^2 = 0 := by
        linear_combination h_factor + (a*b) * (a + b - c - d) * h_eq_sum
      have h_ab_eq_cd : a*b = c*d := by
        have h := sq_eq_zero_iff.mp h_zero
        linear_combination h
      -- Step 2: c*d ≠ 0 since c*d = ab = det P ≠ 0.
      have h_cd_ne : c * d ≠ 0 := by
        rw [← h_ab_eq_cd, h_P_det]
        exact det_ne_zero_of_isUnitary2 hP
      -- Step 3: pq = cd from h_det_prod.
      have h_pq_eq_cd : p * q = c * d := by
        have h := h_det_prod
        rw [show a * b * p * q = (a*b) * (p*q) from by ring, h_ab_eq_cd] at h
        -- h : c*d * (p*q) = c*c*d*d, factor out cd to derive pq = cd
        have h2 : c * d * (p * q - c * d) = 0 := by linear_combination h
        rcases mul_eq_zero.mp h2 with h_cd | h_pq
        · exact absurd h_cd h_cd_ne
        · linear_combination h_pq
      -- Step 4: u₀·u₁ = 1 from h_PD_det.
      have h := h_PD_det
      rw [h_pq_eq_cd, ← h_P_det, h_ab_eq_cd] at h
      -- h : c*d = c*d * (u₀ * u₁)
      have h_diff : c * d * (u₀ * u₁ - 1) = 0 := by linear_combination -h
      rcases mul_eq_zero.mp h_diff with h_cd | h_uu
      · exact absurd h_cd h_cd_ne
      · linear_combination h_uu
    · -- Case M1/M2 (a+b ≠ c+d): conclude u₀ = u₁.
      --
      -- **Strategy: multiset matching via direct algebra (no Polynomial.roots).**
      -- Given P(X) := (X-a)(X-b)(X-p)(X-q) shares all 4 elementary symmetric
      -- polynomials (e_1, e_2, e_3, e_4) with Q(X) := (X-c)²(X-d)², the
      -- multisets {a,b,p,q} and {c,c,d,d} are equal. Rather than use
      -- Mathlib's `Polynomial.roots` machinery (~20 iters of polynomial
      -- type wrangling), we prove the consequence directly:
      --   ∀ x ∈ {a,b,p,q}, (x-c)(x-d) = 0
      -- via a single `linear_combination` per element from the e_k equations
      -- (h_trace_sum, h_e2_vieta, h_e3_vieta, h_det_prod). The key polynomial
      -- identity `(X-a)(X-b)(X-p)(X-q) = (X-c)²(X-d)²` is encoded in those
      -- equations; plugging in any of a, b, p, q on the LHS makes it 0,
      -- so x must be a root of (X-c)²(X-d)².
      --
      -- After (x-c)(x-d) = 0 for each x:
      --   - Case-split a, b → a = b (M1/M2 hypothesis a+b ≠ c+d eliminates
      --     the (c, d) and (d, c) sub-cases).
      --   - a²·(p-q)² = 0 via single `linear_combination` from e_2 + e_4 +
      --     h_a_factor + h_ab_eq; with a ≠ 0 (det P = a·b ≠ 0), p = q.
      --   - mat2_scalar_of_double_eigenvalue gives P = a • 1 (from a = b
      --     in hVP_diag) and P·Diag(u₀,u₁) = p • 1 (from p = q in hVPD_diag).
      --   - Combining: a • Diag(u₀, u₁) = p • 1 ⟹ a·u₀ = a·u₁ = p ⟹ u₀ = u₁.
      --
      -- This technique (multiset matching via direct algebra) is reusable
      -- whenever the elementary symmetric polynomial system is fully
      -- determined and the conclusion is stated component-wise.
      -- (Earlier iters had `h_diff_squares` here as an intermediate algebraic
      -- identity, but it became unused after the multiset-matching approach
      -- replaced the pre-multiset M1/M2 proof. Removed in iter 229.)
      -- Trace-cube equation for full charpoly equality (e_3): tr(M³) = tr(D³).
      have h_trace_cube_eq :
          ((kron2 proj0 P + kron2 proj1 (P * Matrix.diagonal ![u₀, u₁])) *
           (kron2 proj0 P + kron2 proj1 (P * Matrix.diagonal ![u₀, u₁])) *
           (kron2 proj0 P + kron2 proj1 (P * Matrix.diagonal ![u₀, u₁]))).trace =
          ((Matrix.diagonal ![c, c, d, d] : Mat4) *
           Matrix.diagonal ![c, c, d, d] *
           Matrix.diagonal ![c, c, d, d]).trace :=
        trace_cube_eq_of_unitary_similar hV hVP
      -- Expand LHS: M³ = block-diag with blocks P³ and (P·Diag)³.
      have h_trace_cube_lhs :
          ((kron2 proj0 P + kron2 proj1 (P * Matrix.diagonal ![u₀, u₁])) *
           (kron2 proj0 P + kron2 proj1 (P * Matrix.diagonal ![u₀, u₁])) *
           (kron2 proj0 P + kron2 proj1 (P * Matrix.diagonal ![u₀, u₁]))).trace =
          (P * P * P).trace + (P * Matrix.diagonal ![u₀, u₁] *
                               (P * Matrix.diagonal ![u₀, u₁]) *
                               (P * Matrix.diagonal ![u₀, u₁])).trace := by
        rw [block_diag_first_mul, block_diag_first_mul, trace_block_diag_first]
      -- Expand RHS: tr(Diag(c,c,d,d)³) = 2c³ + 2d³.
      have h_trace_cube_rhs :
          ((Matrix.diagonal ![c, c, d, d] : Mat4) *
           Matrix.diagonal ![c, c, d, d] *
           Matrix.diagonal ![c, c, d, d]).trace = 2 * c^3 + 2 * d^3 := by
        rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
            Matrix.trace_diagonal, Fin.sum_univ_four]
        have e2 : (![c, c, d, d] : Fin 4 → ℂ) 2 = d := rfl
        have e3 : (![c, c, d, d] : Fin 4 → ℂ) 3 = d := rfl
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e2, e3]
        ring
      -- tr(P³) = a³ + b³ via Mat2 cube similarity.
      have h_trace_P_cube : (P * P * P).trace = a^3 + b^3 := by
        have h := trace_cube_eq_of_unitary_similar2 hVP_unit hVP_diag
        rw [h, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
            Matrix.trace_diagonal, Fin.sum_univ_two]
        simp [Matrix.cons_val_zero, Matrix.cons_val_one]
        ring
      -- tr((P·Diag)³) = p³ + q³ via Mat2 cube similarity.
      have h_trace_PD_cube :
          (P * Matrix.diagonal ![u₀, u₁] *
           (P * Matrix.diagonal ![u₀, u₁]) *
           (P * Matrix.diagonal ![u₀, u₁])).trace = p^3 + q^3 := by
        have h := trace_cube_eq_of_unitary_similar2 hVPD_unit hVPD_diag
        rw [h, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
            Matrix.trace_diagonal, Fin.sum_univ_two]
        simp [Matrix.cons_val_zero, Matrix.cons_val_one]
        ring
      -- Assemble the e_3 equation: a³ + b³ + p³ + q³ = 2c³ + 2d³.
      have h_e3 : a^3 + b^3 + p^3 + q^3 = 2 * c^3 + 2 * d^3 := by
        have h := h_trace_cube_eq
        rw [h_trace_cube_lhs, h_trace_cube_rhs, h_trace_P_cube,
            h_trace_PD_cube] at h
        linear_combination h
      -- **Vieta e_2** for {a, b, p, q}: from power sums to elementary symmetric.
      -- Identity: (a+b+p+q)² = (a²+b²+p²+q²) + 2·e_2({a,b,p,q}).
      -- Plug in values: e_2 = ((2c+2d)² - (2c²+2d²)) / 2 = c² + 4cd + d².
      -- (See `e2_vieta_from_power_sums` (iter 225) for the abstract Newton's
      -- identity; not used inline here because h_e2 uses `a*a` form rather
      -- than `a^2`, so a one-line `linear_combination` is cleaner.)
      have h_e2_vieta : a*b + a*p + a*q + b*p + b*q + p*q
                      = c^2 + 4*c*d + d^2 := by
        linear_combination ((a+b+p+q+2*c+2*d)/2) * h_trace_sum + (-1/2) * h_e2
      -- **Vieta e_3** for {a, b, p, q}: from Newton's identity
      -- p_3 = e_1·p_2 - e_2·p_1 + 3·e_3, so 3·e_3 = p_3 - e_1·p_2 + e_2·p_1.
      -- For {c,c,d,d}: e_3 = 2c²d + 2cd² = 2cd(c+d).
      have h_e3_vieta : a*b*p + a*b*q + a*p*q + b*p*q = 2*c*d*(c+d) := by
        linear_combination (1/3) * h_e3
          + (-(a+b+p+q)/3) * h_e2
          + ((a+b+p+q)/3) * h_e2_vieta
          + ((-c^2 + 4*c*d - d^2)/3) * h_trace_sum
      -- **Multiset matching**: apply `multiset_match_4_eq_pair_pair` (iter 219
      -- helper, defined just before this theorem) to derive disjunctions
      -- `x = c ∨ x = d` for x ∈ {a, b, p, q} directly from the e_k equations.
      -- This replaces ~45 lines of inline polynomial-root + sq_eq_zero proof.
      have h_e4 : a * b * p * q = c^2 * d^2 := by linear_combination h_det_prod
      obtain ⟨h_a_disj, h_b_disj, h_p_disj, h_q_disj⟩ :=
        multiset_match_4_eq_pair_pair h_trace_sum h_e2_vieta h_e3_vieta h_e4
      -- Derive `h_a_factor : (a - c) * (a - d) = 0` from h_a_disj for use in
      -- the iter 209 a²·(p-q)² = 0 algebraic argument below.
      have h_a_factor : (a - c) * (a - d) = 0 := by
        rcases h_a_disj with h | h <;> rw [h] <;> ring
      -- M1/M2 case (h_eq_sum : a + b ≠ c + d): conclude a = b.
      -- Cases (a, b) ∈ {(c,c), (c,d), (d,c), (d,d)}.
      -- (c,d) and (d,c) give a+b = c+d, contradicting h_eq_sum.
      -- (c,c) gives a=b=c; (d,d) gives a=b=d. Both have a = b.
      have h_ab_eq : a = b := by
        rcases h_a_disj with h_a | h_a
        · rcases h_b_disj with h_b | h_b
          · rw [h_a, h_b]
          · exfalso; apply h_eq_sum; rw [h_a, h_b]
        · rcases h_b_disj with h_b | h_b
          · exfalso; apply h_eq_sum; rw [h_a, h_b]; ring
          · rw [h_a, h_b]
      -- a ≠ 0: from h_P_det = a*b = det P ≠ 0, with a = b gives a² ≠ 0.
      have h_a_ne : a ≠ 0 := by
        intro h_zero
        have h_ab_ne : a * b ≠ 0 := by
          rw [h_P_det]; exact det_ne_zero_of_isUnitary2 hP
        apply h_ab_ne
        rw [h_zero, zero_mul]
      -- Derive a²·(p - q)² = 0 from the e_k equations + h_a_factor + h_ab_eq.
      -- Algebraic identity (a²-c²)(a²-d²) = (a²+(c+d)a+cd)·(a²-(c+d)a+cd) =
      -- (a²+(c+d)a+cd)·h_a_factor_diff. Combined with the e_2/e_4 equations
      -- substituted via b = a, the polynomial identity collapses.
      have h_a_sq_pq_sq : a^2 * (p - q)^2 = 0 := by
        linear_combination a^2 * h_e2 - 2 * h_det_prod
          - 2 * (a^2 + (c+d)*a + c*d) * h_a_factor
          + (a^2 * (a + b) - 2 * a * p * q) * h_ab_eq
      -- (p - q)² = 0 (since a² ≠ 0).
      have h_pq_sq : (p - q)^2 = 0 := by
        rcases mul_eq_zero.mp h_a_sq_pq_sq with h | h
        · exact absurd h (pow_ne_zero 2 h_a_ne)
        · exact h
      -- p = q (square root).
      have h_pq_eq : p = q := by
        have h_diff : p - q = 0 := sq_eq_zero_iff.mp h_pq_sq
        linear_combination h_diff
      -- Apply mat2_scalar_of_double_eigenvalue: P unitary similar to
      -- Diag(a, a) (after b = a substitution) ⟹ P = a • 1.
      have h_P_scalar : P = a • (1 : Mat2) := by
        have hVP_diag' : V_P.conjTranspose * P * V_P =
                         Matrix.diagonal ![a, a] := by
          rw [← h_ab_eq] at hVP_diag
          exact hVP_diag
        exact mat2_scalar_of_double_eigenvalue hVP_unit hVP_diag'
      -- Symmetric: P · Diag(u₀, u₁) is unitary similar to Diag(p, p), hence p • 1.
      have h_PD_scalar : P * Matrix.diagonal ![u₀, u₁] = p • (1 : Mat2) := by
        have hVPD_diag' : V_PD.conjTranspose * (P * Matrix.diagonal ![u₀, u₁]) *
                          V_PD = Matrix.diagonal ![p, p] := by
          rw [← h_pq_eq] at hVPD_diag
          exact hVPD_diag
        exact mat2_scalar_of_double_eigenvalue hVPD_unit hVPD_diag'
      -- Combine: a • Diag(u₀, u₁) = (a • 1) · Diag = P · Diag = p • 1.
      have h_combined : a • (Matrix.diagonal ![u₀, u₁] : Mat2) =
                        p • (1 : Mat2) := by
        rw [← h_PD_scalar, h_P_scalar, smul_mul_assoc, Matrix.one_mul]
      -- Read entries (0,0) and (1,1): a·u₀ = p, a·u₁ = p.
      have h_au0 : a * u₀ = p := by
        have h := congr_fun (congr_fun h_combined 0) 0
        simpa [Matrix.smul_apply, Matrix.diagonal, Matrix.one_apply,
               smul_eq_mul] using h
      have h_au1 : a * u₁ = p := by
        have h := congr_fun (congr_fun h_combined 1) 1
        simpa [Matrix.smul_apply, Matrix.diagonal, Matrix.one_apply,
               smul_eq_mul] using h
      -- u₀ = u₁ from a·u₀ = a·u₁ and a ≠ 0.
      left
      exact mul_left_cancel₀ h_a_ne (h_au0.trans h_au1.symm)
  · -- (⇐) direction: case-split.
    rintro (h_eq | h_prod)
    · -- Case 1: u₀ = u₁. Pick P = I, c = 1, d = u₀, V = 1.
      subst h_eq
      refine ⟨1, isUnitary2_one, 1, u₀, 1, ?_, ?_⟩
      · -- IsUnitary4 1
        change (1 : Mat4).conjTranspose * (1 : Mat4) = 1
        rw [Matrix.conjTranspose_one, Matrix.one_mul]
      · -- V† · ((kron2 1 1) · Diag(1,1,u₀,u₀)) · V = Diag(1, 1, u₀, u₀)
        rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
            kron2_one_one_eq_one, Matrix.one_mul]
    · -- Case 2: u₀ · u₁ = 1. P := Diag(1, u₀), c := 1, d := u₀,
      -- V := kron2 1 proj0 + kron2 pauliX proj1 (= CNOT_{B→A}, swap pos 1↔3).
      refine ⟨Matrix.diagonal ![1, u₀],
              isUnitary2_diag_one_u u₀ hu₀,
              1, u₀,
              kron2 (1 : Mat2) proj0 + kron2 pauliX proj1,
              isUnitary4_kron2_one_proj0_pauliX_proj1, ?_⟩
      -- Step (a): kron2 1 P = Diag(1, u₀, 1, u₀).
      rw [kron2_one_diag_one_u]
      -- Step (b): Diag(1,u₀,1,u₀) · Diag(1,1,u₀,u₁) = Diag(1,u₀,u₀,u₀·u₁).
      rw [diag_one_u_one_u_mul_diag_one_one_u_u]
      -- Step (c): substitute u₀·u₁ = 1.
      rw [h_prod]
      -- Step (d): V† · Diag(1,u₀,u₀,1) · V = Diag(1,1,u₀,u₀).
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [kron2, proj0, proj1, pauliX, Matrix.mul_apply,
              Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.of_apply,
              Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- From py24_lemma_A_19's hypothesis, derive `blockA_10 U = 0`.
    Proof: project hypothesis onto upper half indices ⟨i+4, _⟩ →
    block10 (embedAC U) · ϕ = 0 → kron2 1 (blockA_10 U) · ϕ = 0 → blockA_10 U = 0. -/
private lemma blockA_10_eq_zero_of_hAct
    {U : Mat4} {ϕ ω : Vec2}
    (hϕ_ent : ϕ 0 * ϕ 3 ≠ ϕ 1 * ϕ 2)
    (hAct : Mat8.apply (embedAC U) (tensor1_2 ket0_1 ϕ) = tensor1_2 ket0_1 ω) :
    blockA_10 U = 0 := by
  have h_block10 : Mat4.apply (block10 (embedAC U)) ϕ = 0 := by
    funext i
    rw [← Mat8.apply_tensor1_2_ket0_upper (embedAC U) ϕ i, hAct]
    change tensor1_2 ket0_1 ω ⟨i.val + 4, by omega⟩ = 0
    simp [tensor1_2, ket0_1]
  rw [block10_embedAC] at h_block10
  -- h_block10 : Mat4.apply (kron2 I₂ (blockA_10 U)) ϕ = 0; I₂ = 1.
  exact mat2_eq_zero_of_kron2_one_apply_zero hϕ_ent h_block10

/-- Helper: kron2 I₂ 0 = 0. -/
private lemma kron2_I₂_zero : (kron2 I₂ (0 : Mat2) : Mat4) = 0 := by
  ext i j; simp [kron2]

/-- Helper: when U is unitary and `blockA_10 U = 0`, then `blockA_00 U` is unitary.
    Derived from `embedAC U† · embedAC U = (1 : Mat8)` by extracting block00. -/
lemma blockA_00_unitary_of_blockA_10_zero
    {U : Mat4} (hU : IsUnitary4 U) (h10 : blockA_10 U = 0) :
    IsUnitary2 (blockA_00 U) := by
  unfold IsUnitary4 at hU
  -- embedAC U† * embedAC U = (1 : Mat8).
  have h_embed_id : (embedAC U).conjTranspose * embedAC U = (1 : Mat8) := by
    rw [embedAC_conjTranspose, embedAC_mul, hU, embedAC_one]
  -- block00 of both sides.
  have h_b00 := congr_arg block00 h_embed_id
  rw [block00_mul, block00_one, block00_conjTranspose, block01_conjTranspose,
      block00_embedAC, block10_embedAC, h10, kron2_I₂_zero,
      Matrix.conjTranspose_zero, Matrix.zero_mul, add_zero] at h_b00
  -- h_b00 : (kron2 I₂ (blockA_00 U))† · (kron2 I₂ (blockA_00 U)) = 1.
  change (blockA_00 U).conjTranspose * (blockA_00 U) = 1
  unfold I₂ at h_b00
  rw [kron2_conjTranspose, Matrix.conjTranspose_one, kron2_mul, one_mul] at h_b00
  -- h_b00 : kron2 1 ((blockA_00 U)† * (blockA_00 U)) = 1
  rw [← kron2_one_one_eq_one, kron2_one_eq_iff] at h_b00
  exact h_b00

/-- Helper: when U is unitary and `blockA_10 U = 0`, then `blockA_01 U = 0`.
    Uses `blockA_00 U` is unitary (Step 182) + `(blockA_00 U)† · blockA_01 U = 0`
    (extracted via block01 of `embedAC U† · embedAC U = (1 : Mat8)`). -/
private lemma blockA_01_zero_of_blockA_10_zero
    {U : Mat4} (hU : IsUnitary4 U) (h10 : blockA_10 U = 0) :
    blockA_01 U = 0 := by
  have h00_unit := blockA_00_unitary_of_blockA_10_zero hU h10
  unfold IsUnitary4 at hU
  have h_embed_id : (embedAC U).conjTranspose * embedAC U = (1 : Mat8) := by
    rw [embedAC_conjTranspose, embedAC_mul, hU, embedAC_one]
  have h_b01 := congr_arg block01 h_embed_id
  rw [block01_mul, block01_one, block00_conjTranspose, block01_conjTranspose,
      block00_embedAC, block01_embedAC, block10_embedAC, h10, kron2_I₂_zero,
      block11_embedAC,
      Matrix.conjTranspose_zero, Matrix.zero_mul, add_zero] at h_b01
  unfold I₂ at h_b01
  rw [kron2_conjTranspose, Matrix.conjTranspose_one, kron2_mul, one_mul] at h_b01
  rw [kron2_one_eq_zero_iff] at h_b01
  -- h_b01 : (blockA_00 U)† * blockA_01 U = 0
  have h00_unit_T : IsUnitary2 (blockA_00 U).conjTranspose :=
    isUnitary2_conjTranspose h00_unit
  unfold IsUnitary2 at h00_unit_T
  rw [Matrix.conjTranspose_conjTranspose] at h00_unit_T
  -- h00_unit_T : blockA_00 U * (blockA_00 U)† = 1
  have key : blockA_00 U * ((blockA_00 U).conjTranspose * blockA_01 U) = 0 := by
    rw [h_b01, Matrix.mul_zero]
  rw [← Matrix.mul_assoc, h00_unit_T, Matrix.one_mul] at key
  exact key

/-- Helper: when U is unitary and `blockA_10 U = 0` (so `blockA_01 U = 0` too),
    then `blockA_11 U` is unitary. Symmetric to `blockA_00_unitary_of_blockA_10_zero`. -/
lemma blockA_11_unitary_of_blockA_10_zero
    {U : Mat4} (hU : IsUnitary4 U) (h10 : blockA_10 U = 0) :
    IsUnitary2 (blockA_11 U) := by
  have h01 := blockA_01_zero_of_blockA_10_zero hU h10
  unfold IsUnitary4 at hU
  have h_embed_id : (embedAC U).conjTranspose * embedAC U = (1 : Mat8) := by
    rw [embedAC_conjTranspose, embedAC_mul, hU, embedAC_one]
  have h_b11 := congr_arg block11 h_embed_id
  rw [block11_mul, block11_one, block11_conjTranspose, block10_conjTranspose,
      block01_embedAC, block11_embedAC, h01, kron2_I₂_zero,
      Matrix.conjTranspose_zero, Matrix.zero_mul, zero_add] at h_b11
  change (blockA_11 U).conjTranspose * (blockA_11 U) = 1
  unfold I₂ at h_b11
  rw [kron2_conjTranspose, Matrix.conjTranspose_one, kron2_mul, one_mul] at h_b11
  rw [← kron2_one_one_eq_one, kron2_one_eq_iff] at h_b11
  exact h_b11

/-- Helper: U with `blockA_01 U = 0 ∧ blockA_10 U = 0` decomposes as
    `kron2 proj0 (blockA_00 U) + kron2 proj1 (blockA_11 U)`. -/
private lemma U_eq_kron2_proj_decomp
    {U : Mat4} (h01 : blockA_01 U = 0) (h10 : blockA_10 U = 0) :
    U = kron2 proj0 (blockA_00 U) + kron2 proj1 (blockA_11 U) := by
  -- Extract zero entries from h01 (rows {0,1}, cols {2,3}) and h10 (rows {2,3}, cols {0,1}).
  have hU02 : U 0 2 = 0 := by
    have := congr_fun (congr_fun h01 0) 0; simpa [blockA_01] using this
  have hU03 : U 0 3 = 0 := by
    have := congr_fun (congr_fun h01 0) 1; simpa [blockA_01] using this
  have hU12 : U 1 2 = 0 := by
    have := congr_fun (congr_fun h01 1) 0; simpa [blockA_01] using this
  have hU13 : U 1 3 = 0 := by
    have := congr_fun (congr_fun h01 1) 1; simpa [blockA_01] using this
  have hU20 : U 2 0 = 0 := by
    have := congr_fun (congr_fun h10 0) 0; simpa [blockA_10] using this
  have hU21 : U 2 1 = 0 := by
    have := congr_fun (congr_fun h10 0) 1; simpa [blockA_10] using this
  have hU30 : U 3 0 = 0 := by
    have := congr_fun (congr_fun h10 1) 0; simpa [blockA_10] using this
  have hU31 : U 3 1 = 0 := by
    have := congr_fun (congr_fun h10 1) 1; simpa [blockA_10] using this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kron2, proj0, proj1, blockA_00, blockA_11,
          Matrix.add_apply, Matrix.of_apply,
          hU02, hU03, hU12, hU13, hU20, hU21, hU30, hU31]

/-- **Common closing for A.19, A.33, etc.**: U unitary + blockA_10 U = 0 implies
    U has the controlled form `kron2 proj0 P₀ + kron2 proj1 P₁` with both
    P₀, P₁ unitary. -/
private lemma U_eq_controlled_of_blockA_10_zero
    {U : Mat4} (hU : IsUnitary4 U) (h10 : blockA_10 U = 0) :
    ∃ P₀ P₁ : Mat2, IsUnitary2 P₀ ∧ IsUnitary2 P₁ ∧
      U = kron2 proj0 P₀ + kron2 proj1 P₁ :=
  ⟨blockA_00 U, blockA_11 U,
    blockA_00_unitary_of_blockA_10_zero hU h10,
    blockA_11_unitary_of_blockA_10_zero hU h10,
    U_eq_kron2_proj_decomp (blockA_01_zero_of_blockA_10_zero hU h10) h10⟩

/-! ## PY24 Lemma A.17 — controlled-from-two-zero-images

If U is a 2-qubit unitary and there exist orthogonal qubits α, β such that
`U·(|0⟩⊗α) = |0⟩⊗γ` and `U·(|0⟩⊗β) = |0⟩⊗δ`, then U is controlled along
the first qubit. Used as a key step inside A.24's proof.
Reference: Palsberg & Yu (2024), Lemma A.17, page 242. -/

/-- Bridge: applying a Mat4 U to `tensor1_1 ket0_1 α` and reading the lower
    half (rows 2, 3) gives `Mat2.apply (blockA_10 U) α`. -/
private lemma Mat4.apply_tensor1_1_ket0_lower
    (U : Mat4) (α : Vec1) (i : Fin 2) :
    Mat4.apply U (tensor1_1 ket0_1 α) ⟨i.val + 2, by omega⟩
      = Mat2.apply (blockA_10 U) α i := by
  change ∑ j : Fin 4, U ⟨i.val + 2, by omega⟩ j * tensor1_1 ket0_1 α j
       = ∑ j : Fin 2, blockA_10 U i j * α j
  rw [Fin.sum_univ_four, Fin.sum_univ_two]
  simp [tensor1_1, ket0_1, blockA_10, Matrix.of_apply]

/-- From `U·(|0⟩⊗α) = |0⟩⊗γ`, conclude `(blockA_10 U)·α = 0`
    (the lower half of the LHS reads off `blockA_10 U · α`, and the
    lower half of the RHS `tensor1_1 ket0_1 γ` is identically 0). -/
private lemma blockA_10_apply_zero_of_apply_tensor_zero
    {U : Mat4} {α γ : Vec1}
    (h : Mat4.apply U (tensor1_1 ket0_1 α) = tensor1_1 ket0_1 γ) :
    Mat2.apply (blockA_10 U) α = 0 := by
  funext i
  rw [← Mat4.apply_tensor1_1_ket0_lower, h]
  -- Goal: tensor1_1 ket0_1 γ ⟨i.val + 2, _⟩ = 0
  show tensor1_1 ket0_1 γ ⟨i.val + 2, by omega⟩ = (0 : Vec1) i
  simp [tensor1_1, ket0_1]

/-- **PY24 Lemma A.17** (page 242). Controlled-from-two-zero-images.
    If U is a 2-qubit unitary and there exist orthogonal qubits α, β with
    `U·(|0⟩⊗α) = |0⟩⊗γ` and `U·(|0⟩⊗β) = |0⟩⊗δ`, then U is controlled along
    the first qubit: `U = kron2 proj0 P₀ + kron2 proj1 P₁` for some
    2×2 unitaries P₀, P₁. -/
theorem py24_lemma_A_17
    {U : Mat4} (hU : IsUnitary4 U)
    {α β γ δ : Vec1}
    (hα : IsQubit1 α) (hβ : IsQubit1 β) (h_orth : innerVec1 α β = 0)
    (hUα : Mat4.apply U (tensor1_1 ket0_1 α) = tensor1_1 ket0_1 γ)
    (hUβ : Mat4.apply U (tensor1_1 ket0_1 β) = tensor1_1 ket0_1 δ) :
    ∃ P₀ P₁ : Mat2, IsUnitary2 P₀ ∧ IsUnitary2 P₁ ∧
      U = kron2 proj0 P₀ + kron2 proj1 P₁ := by
  have hα_zero : Mat2.apply (blockA_10 U) α = 0 :=
    blockA_10_apply_zero_of_apply_tensor_zero hUα
  have hβ_zero : Mat2.apply (blockA_10 U) β = 0 :=
    blockA_10_apply_zero_of_apply_tensor_zero hUβ
  have h_indep : α 0 * β 1 ≠ α 1 * β 0 :=
    orthogonal_qubits_indep hα hβ h_orth
  have h10_zero : blockA_10 U = 0 :=
    mat2_eq_zero_of_two_kernel _ α β h_indep hα_zero hβ_zero
  exact U_eq_controlled_of_blockA_10_zero hU h10_zero

/-! ## PY24 Lemma A.21 (foundational for A.24, A.30, A.32)

For any 2-qubit unitary U, there exists a unit qubit ψ such that
`U(|0⟩ ⊗ ψ)` is a tensor product. This lemma is fundamental to PY24's
proof strategy for several subsequent lemmas. -/

/-- PY24 Lemma A.21. Existence of qubit ψ making U(|0⟩⊗ψ) a tensor.
    Used by A.24, A.30, A.32. -/
theorem py24_lemma_A_21 (U : Mat4) (_hU : IsUnitary4 U) :
    ∃ ψ : Vec1, IsQubit1 ψ ∧
      IsTensor (Mat4.apply U (tensor1_1 ket0_1 ψ)) := by
  -- Case analysis on whether U|00⟩ is already a tensor.
  by_cases h : IsTensor (Mat4.apply U (tensor1_1 ket0_1 ket0_1))
  · -- Easy case: U|00⟩ is tensor. Take ψ = ket0_1.
    exact ⟨ket0_1, IsQubit1_ket0, h⟩
  · -- Case B: U|00⟩ NOT tensor. Use quadratic formula over ℂ.
    rw [isTensor_iff_det_zero] at h
    set α : Vec2 := Mat4.apply U (tensor1_1 ket0_1 ket0_1) with hα_def
    set β : Vec2 := Mat4.apply U (tensor1_1 ket0_1 ket1_1) with hβ_def
    set A : ℂ := α 0 * α 3 - α 1 * α 2 with hA_def
    have hA_ne : A ≠ 0 := sub_ne_zero.mpr h
    set B : ℂ := α 0 * β 3 + β 0 * α 3 - α 1 * β 2 - β 1 * α 2 with hB_def
    set C : ℂ := β 0 * β 3 - β 1 * β 2 with hC_def
    -- Get a square root of B² - 4AC via ℂ algebraic closure.
    obtain ⟨y, hy⟩ : ∃ y : ℂ, y^2 = B^2 - 4*A*C :=
      IsAlgClosed.exists_pow_nat_eq (B^2 - 4*A*C) (by norm_num : 0 < 2)
    -- Quadratic formula: p₀ = (-B + y) / (2A).
    set p₀ : ℂ := (-B + y) / (2 * A) with hp₀_def
    have h2A_ne : (2 : ℂ) * A ≠ 0 := mul_ne_zero two_ne_zero hA_ne
    have h_root : A * p₀^2 + B * p₀ + C = 0 := by
      have h1 : 2 * A * p₀ + B = y := by
        rw [hp₀_def]
        field_simp
        ring
      have h4A_ne : (4 : ℂ) * A ≠ 0 := mul_ne_zero (by norm_num) hA_ne
      have h2 : 4 * A * (A * p₀^2 + B * p₀ + C) = 0 := by
        have eq : 4 * A * (A * p₀^2 + B * p₀ + C)
                = (2*A*p₀ + B)^2 - (B^2 - 4*A*C) := by ring
        rw [eq, h1, hy]; ring
      exact (mul_eq_zero.mp h2).resolve_left h4A_ne
    -- ψ_unnorm = ![p₀, 1] : Vec1. Nonzero since component 1 = 1.
    set ψ_unnorm : Vec1 := ![p₀, 1] with hψu_def
    have hψ_unnorm_ne : ψ_unnorm ≠ 0 := by
      intro heq
      have := congr_fun heq 1
      simp [hψu_def] at this
    refine ⟨unit_normalize_vec1 ψ_unnorm,
            isQubit1_unit_normalize_vec1 _ hψ_unnorm_ne, ?_⟩
    -- Show U(|0⟩ ⊗ ψ) is a tensor.
    -- Step 1: U(|0⟩ ⊗ ψ_unnorm) = p₀ • α + β.
    have h_apply_unnorm :
        Mat4.apply U (tensor1_1 ket0_1 ψ_unnorm) = p₀ • α + β := by
      have hψu_decomp : ψ_unnorm = p₀ • ket0_1 + ket1_1 := by
        funext i; fin_cases i <;>
          simp [hψu_def, ket0_1, ket1_1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hψu_decomp, tensor1_1_add_right, tensor1_1_smul_right,
          Mat4.apply_add, Mat4.apply_smul]
    -- Step 2: (p₀ • α + β) is a tensor (det = 0 from h_root).
    have h_p0_alpha_tensor : IsTensor (p₀ • α + β) := by
      rw [isTensor_iff_det_zero]
      show (p₀ • α + β) 0 * (p₀ • α + β) 3 = (p₀ • α + β) 1 * (p₀ • α + β) 2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      -- Expand: (p₀ α₀ + β₀)(p₀ α₃ + β₃) = (p₀ α₁ + β₁)(p₀ α₂ + β₂)
      -- = A·p₀² + B·p₀ + C = 0 (by h_root).
      linear_combination h_root
    -- Step 3: U(|0⟩ ⊗ ψ) = scalar • (p₀ • α + β); scalar of tensor is tensor.
    have h_apply_norm :
        Mat4.apply U (tensor1_1 ket0_1 (unit_normalize_vec1 ψ_unnorm)) =
          ((((Real.sqrt (normSqVec1 ψ_unnorm))⁻¹ : ℝ) : ℂ)) • (p₀ • α + β) := by
      unfold unit_normalize_vec1
      rw [tensor1_1_smul_right, Mat4.apply_smul, h_apply_unnorm]
    rw [h_apply_norm]
    -- (scalar) • tensor is tensor.
    obtain ⟨a, b, hab⟩ := h_p0_alpha_tensor
    refine ⟨((((Real.sqrt (normSqVec1 ψ_unnorm))⁻¹ : ℝ) : ℂ)) • a, b, ?_⟩
    rw [hab, ← tensor1_1_smul_left]

/-- Strengthened A.21: the tensor factors `a, b` can be assumed to be unit
    qubits. Used by A.30, A.32 to rotate the tensor decomposition to |0⟩⊗|0⟩.

    Construction: A.21 gives `U(|0⟩⊗ψ) = a⊗b`. Since U is unitary, the output
    has unit norm, so `‖a‖²·‖b‖² = 1` (both nonzero). Replace `(a, b)` by
    `(a/‖a‖, ‖a‖·b)` — both unit, same tensor. -/
lemma py24_lemma_A_21_unit_factors (U : Mat4) (hU : IsUnitary4 U) :
    ∃ ψ a b : Vec1, IsQubit1 ψ ∧ IsQubit1 a ∧ IsQubit1 b ∧
      Mat4.apply U (tensor1_1 ket0_1 ψ) = tensor1_1 a b := by
  obtain ⟨ψ, hψ_qubit, a, b, hab⟩ := py24_lemma_A_21 U hU
  -- |0⟩⊗ψ is unit; U preserves norm, so output is unit.
  have h_unit : IsQubit2 (Mat4.apply U (tensor1_1 ket0_1 ψ)) :=
    IsQubit2_apply_unitary hU (IsQubit2_tensor1_1 IsQubit1_ket0 hψ_qubit)
  rw [hab] at h_unit
  unfold IsQubit2 at h_unit
  rw [normSqVec2_tensor1_1] at h_unit
  -- h_unit : normSqVec1 a * normSqVec1 b = 1, so neither factor is 0.
  have ha_ne : a ≠ 0 := by
    intro ha
    have : normSqVec1 a = 0 := by rw [ha]; unfold normSqVec1; simp
    rw [this, zero_mul] at h_unit
    exact one_ne_zero h_unit.symm
  have hb_ne : b ≠ 0 := by
    intro hb
    have : normSqVec1 b = 0 := by rw [hb]; unfold normSqVec1; simp
    rw [this, mul_zero] at h_unit
    exact one_ne_zero h_unit.symm
  -- Unit factors: a' = a/‖a‖, b' = ‖a‖·b.
  refine ⟨ψ, unit_normalize_vec1 a,
          ((Real.sqrt (normSqVec1 a) : ℝ) : ℂ) • b, hψ_qubit,
          isQubit1_unit_normalize_vec1 a ha_ne, ?_, ?_⟩
  · -- IsQubit1 (‖a‖·b): ‖‖a‖·b‖² = ‖a‖² · ‖b‖² = 1.
    unfold IsQubit1
    rw [normSqVec1_smul, Complex.normSq_ofReal]
    have hns_pos : 0 < normSqVec1 a := normSqVec1_pos_of_ne_zero a ha_ne
    rw [Real.mul_self_sqrt hns_pos.le]
    exact h_unit
  · -- U·(|0⟩⊗ψ) = (a/‖a‖) ⊗ (‖a‖·b).
    rw [hab, tensor1_1_smul_right, ← tensor1_1_smul_left,
        smul_unit_normalize_vec1 a ha_ne]

/-- **Normalization at |00⟩**: any 2-qubit unitary U decomposes as
    `kron2 R_a R_b · V = U · (kron2 1 R_ψ)` where V·|00⟩ = |00⟩ and all factors
    are unitary. Equivalently: V := (kron2 R_a R_b)† · U · (kron2 1 R_ψ).
    Foundation for PY24 A.32 (V₃|00⟩=|00⟩ normalization). -/
lemma exists_unitary_normalize_at_ket00 (U : Mat4) (hU : IsUnitary4 U) :
    ∃ Ra Rb Rψ : Mat2, ∃ V : Mat4,
      IsUnitary2 Ra ∧ IsUnitary2 Rb ∧ IsUnitary2 Rψ ∧ IsUnitary4 V ∧
      Mat4.apply V (tensor1_1 ket0_1 ket0_1) = tensor1_1 ket0_1 ket0_1 ∧
      kron2 Ra Rb * V = U * kron2 1 Rψ := by
  obtain ⟨ψ, a, b, hψ, ha, hb, hUψ⟩ := py24_lemma_A_21_unit_factors U hU
  obtain ⟨Rψ, hRψ, hRψApp⟩ := exists_unitary_rotate_from_ket0 hψ
  obtain ⟨Ra, hRa, hRaApp⟩ := exists_unitary_rotate_from_ket0 ha
  obtain ⟨Rb, hRb, hRbApp⟩ := exists_unitary_rotate_from_ket0 hb
  -- V := (kron2 Ra Rb)† · U · kron2 1 Rψ
  refine ⟨Ra, Rb, Rψ, (kron2 Ra Rb).conjTranspose * U * kron2 1 Rψ,
          hRa, hRb, hRψ, ?_, ?_, ?_⟩
  · -- IsUnitary4 V
    exact isUnitary4_mul (isUnitary4_mul
            (isUnitary4_conjTranspose (isUnitary4_kron2 hRa hRb)) hU)
            (isUnitary4_kron2 isUnitary2_one hRψ)
  · -- V·|00⟩ = |00⟩
    rw [Mat4.apply_mul, Mat4.apply_mul, kron2_apply_tensor1_1,
        Mat2.apply_one, hRψApp, hUψ]
    -- Goal: Mat4.apply (kron2 Ra Rb)† (tensor1_1 a b) = tensor1_1 ket0_1 ket0_1
    have hRaRb : Mat4.apply (kron2 Ra Rb) (tensor1_1 ket0_1 ket0_1)
                  = tensor1_1 a b := by
      rw [kron2_apply_tensor1_1, hRaApp, hRbApp]
    rw [← hRaRb, ← Mat4.apply_mul]
    rw [show (kron2 Ra Rb).conjTranspose * kron2 Ra Rb = 1
        from isUnitary4_kron2 hRa hRb]
    exact Mat4.apply_one _
  · -- kron2 Ra Rb · V = U · kron2 1 Rψ
    change kron2 Ra Rb * ((kron2 Ra Rb).conjTranspose * U * kron2 1 Rψ)
        = U * kron2 1 Rψ
    rw [← mul_assoc, ← mul_assoc]
    rw [show kron2 Ra Rb * (kron2 Ra Rb).conjTranspose = 1
        from mul_eq_one_comm.mp (isUnitary4_kron2 hRa hRb)]
    rw [one_mul]

/-! ## PY24 Lemma A.19 (HP A.13) — Entangling implies controlled

If U is a 2-qubit unitary and |ϕ⟩, |ω⟩ are 4-dim unit vectors with
  U_AC (|0⟩_A ⊗ |ϕ⟩_BC) = |0⟩_A ⊗ |ω⟩_BC
and |ϕ⟩ is entangled, then U is of the form |0⟩⟨0| ⊗ P₀ + |1⟩⟨1| ⊗ P₁
for some 1-qubit unitaries P₀, P₁. -/
theorem py24_lemma_A_19 (U : Mat4) (hU : IsUnitary4 U)
    (ϕ ω : Vec2) (_hϕ : IsQubit2 ϕ) (_hω : IsQubit2 ω)
    (hAct : Mat8.apply (embedAC U) (tensor1_2 ket0_1 ϕ) = tensor1_2 ket0_1 ω)
    (hEnt : IsEntangled ϕ) :
    ∃ P₀ P₁ : Mat2, IsUnitary2 P₀ ∧ IsUnitary2 P₁ ∧
      U = kron2 proj0 P₀ + kron2 proj1 P₁ := by
  -- Convert IsEntangled to the algebraic form det ≠ 0.
  have hϕ_det : ϕ 0 * ϕ 3 ≠ ϕ 1 * ϕ 2 := fun h => hEnt (det_zero_implies_isTensor h)
  -- Chain of derivations:
  have h10 := blockA_10_eq_zero_of_hAct hϕ_det hAct
  have h00_unit := blockA_00_unitary_of_blockA_10_zero hU h10
  have h01 := blockA_01_zero_of_blockA_10_zero hU h10
  have h11_unit := blockA_11_unitary_of_blockA_10_zero hU h10
  have h_decomp := U_eq_kron2_proj_decomp h01 h10
  exact ⟨blockA_00 U, blockA_11 U, h00_unit, h11_unit, h_decomp⟩

/-! ## A.27 helpers: controlled-A form ↔ blockA off-diagonal vanishing -/

/-- For controlled-A 4×4 matrix `kron2 proj0 P₀ + kron2 proj1 P₁`:
    blockA_00 = P₀, blockA_11 = P₁, blockA_01 = 0, blockA_10 = 0. -/
lemma blockA_of_controlled (P₀ P₁ : Mat2) :
    blockA_00 (kron2 proj0 P₀ + kron2 proj1 P₁) = P₀ ∧
    blockA_01 (kron2 proj0 P₀ + kron2 proj1 P₁) = 0 ∧
    blockA_10 (kron2 proj0 P₀ + kron2 proj1 P₁) = 0 ∧
    blockA_11 (kron2 proj0 P₀ + kron2 proj1 P₁) = P₁ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blockA_00, blockA_01, blockA_10, blockA_11, kron2, proj0, proj1,
            Matrix.of_apply, Matrix.add_apply]

/-- If V is controlled, then block01 (embedAC V) = 0. -/
lemma block01_embedAC_of_controlled (P₀ P₁ : Mat2) :
    block01 (embedAC (kron2 proj0 P₀ + kron2 proj1 P₁)) = 0 := by
  rw [block01_embedAC, (blockA_of_controlled P₀ P₁).2.1, kron2_I₂_zero]

/-- If V is controlled, then block10 (embedAC V) = 0. -/
lemma block10_embedAC_of_controlled (P₀ P₁ : Mat2) :
    block10 (embedAC (kron2 proj0 P₀ + kron2 proj1 P₁)) = 0 := by
  rw [block10_embedAC, (blockA_of_controlled P₀ P₁).2.2.1, kron2_I₂_zero]

/-- block00 of (embedAC V) when V is controlled = kron2 1 P₀. -/
lemma block00_embedAC_of_controlled (P₀ P₁ : Mat2) :
    block00 (embedAC (kron2 proj0 P₀ + kron2 proj1 P₁)) = kron2 (1 : Mat2) P₀ := by
  rw [block00_embedAC, (blockA_of_controlled P₀ P₁).1]
  show kron2 I₂ P₀ = kron2 1 P₀
  rfl

/-- block11 of (embedAC V) when V is controlled = kron2 1 P₁. -/
lemma block11_embedAC_of_controlled (P₀ P₁ : Mat2) :
    block11 (embedAC (kron2 proj0 P₀ + kron2 proj1 P₁)) = kron2 (1 : Mat2) P₁ := by
  rw [block11_embedAC, (blockA_of_controlled P₀ P₁).2.2.2]
  show kron2 I₂ P₁ = kron2 1 P₁
  rfl

/-- The conjTranspose of a controlled gate is controlled. -/
lemma controlled_conjTranspose (P₀ P₁ : Mat2) :
    (kron2 proj0 P₀ + kron2 proj1 P₁).conjTranspose =
    kron2 proj0 P₀.conjTranspose + kron2 proj1 P₁.conjTranspose := by
  rw [Matrix.conjTranspose_add, kron2_conjTranspose, kron2_conjTranspose,
      proj0_conjTranspose, proj1_conjTranspose]

/-- Chain rearrangement: from `embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄ = D`,
    isolate `embedAC V₃` on the LHS using unitarity of V₁, V₂, V₄. -/
lemma embedAC_V3_isolated
    (V₁ V₂ V₃ V₄ : Mat4)
    (hV₁ : IsUnitary4 V₁) (hV₂ : IsUnitary4 V₂) (hV₄ : IsUnitary4 V₄)
    (D : Mat8)
    (h_chain : embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄ = D) :
    embedAC V₃ = embedBC V₂.conjTranspose * embedAC V₁.conjTranspose * D *
                  embedBC V₄.conjTranspose := by
  have hV₁_inv : V₁.conjTranspose * V₁ = 1 := hV₁
  have hV₂_inv : V₂.conjTranspose * V₂ = 1 := hV₂
  have hV₄_inv : V₄ * V₄.conjTranspose = 1 := mul_eq_one_comm.mp hV₄
  -- Show: RHS-with-chain = embedAC V₃, then transport via h_chain.
  have key : embedBC V₂.conjTranspose * embedAC V₁.conjTranspose *
             (embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄) *
             embedBC V₄.conjTranspose = embedAC V₃ := by
    calc embedBC V₂.conjTranspose * embedAC V₁.conjTranspose *
           (embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄) *
           embedBC V₄.conjTranspose
        = embedBC V₂.conjTranspose *
            (embedAC V₁.conjTranspose * embedAC V₁) *
            embedBC V₂ * embedAC V₃ *
            (embedBC V₄ * embedBC V₄.conjTranspose) := by noncomm_ring
      _ = embedBC V₂.conjTranspose *
            embedAC (V₁.conjTranspose * V₁) *
            embedBC V₂ * embedAC V₃ *
            embedBC (V₄ * V₄.conjTranspose) := by
              rw [embedAC_mul, embedBC_mul]
      _ = embedBC V₂.conjTranspose *
            embedAC 1 *
            embedBC V₂ * embedAC V₃ *
            embedBC 1 := by rw [hV₁_inv, hV₄_inv]
      _ = embedBC V₂.conjTranspose * 1 * embedBC V₂ * embedAC V₃ * 1 := by
              rw [embedAC_one, embedBC_one]
      _ = (embedBC V₂.conjTranspose * embedBC V₂) * embedAC V₃ := by noncomm_ring
      _ = embedBC (V₂.conjTranspose * V₂) * embedAC V₃ := by rw [embedBC_mul]
      _ = embedBC 1 * embedAC V₃ := by rw [hV₂_inv]
      _ = 1 * embedAC V₃ := by rw [embedBC_one]
      _ = embedAC V₃ := one_mul _
  rw [h_chain] at key
  exact key.symm

set_option maxHeartbeats 1600000 in
-- Block decomposition + 4-fold matrix product entry-wise analysis.
/-- **PY24 Lemma A.27**: For 2-qubit unitaries V₁..V₄ and 1-qubit unitaries
    P₀, P₁, if `V₁_AC · V₂_BC · V₃_AC · V₄_BC = D` for D block-diag-A
    (i.e., block01 D = 0 ∧ block10 D = 0), and V₁ = controlled, then
    V₃ is also controlled. -/
theorem py24_lemma_A_27
    (V₁ V₂ V₃ V₄ : Mat4)
    (hV₁ : IsUnitary4 V₁) (hV₂ : IsUnitary4 V₂)
    (hV₃ : IsUnitary4 V₃) (hV₄ : IsUnitary4 V₄)
    (P₀ P₁ : Mat2)
    (h_V₁ : V₁ = kron2 proj0 P₀ + kron2 proj1 P₁)
    (D : Mat8)
    (h_D_block01 : block01 D = 0) (h_D_block10 : block10 D = 0)
    (h_chain : embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄ = D) :
    ∃ Q₀ Q₁ : Mat2, IsUnitary2 Q₀ ∧ IsUnitary2 Q₁ ∧
      V₃ = kron2 proj0 Q₀ + kron2 proj1 Q₁ := by
  -- Step 1: Isolate embedAC V₃ via chain rearrangement.
  have h_iso := embedAC_V3_isolated V₁ V₂ V₃ V₄ hV₁ hV₂ hV₄ D h_chain
  -- Step 2: Show embedAC V₁† has block01 = 0 and block10 = 0.
  have h_V1dag_block01 : block01 (embedAC V₁.conjTranspose) = 0 := by
    rw [h_V₁, controlled_conjTranspose]
    exact block01_embedAC_of_controlled P₀.conjTranspose P₁.conjTranspose
  have h_V1dag_block10 : block10 (embedAC V₁.conjTranspose) = 0 := by
    rw [h_V₁, controlled_conjTranspose]
    exact block10_embedAC_of_controlled P₀.conjTranspose P₁.conjTranspose
  -- Step 3: Compute block01 of the rearranged RHS.
  -- RHS = ((embedBC V₂† · embedAC V₁†) · D) · embedBC V₄†.
  -- block01 (embedBC V₂† · embedAC V₁†) = 0 (both factors block-diag-A).
  have h_BV2_AV1_block01 :
      block01 (embedBC V₂.conjTranspose * embedAC V₁.conjTranspose) = 0 := by
    rw [block01_mul, block00_embedBC, block01_embedBC, h_V1dag_block01]
    simp
  have h_BV2_AV1_block10 :
      block10 (embedBC V₂.conjTranspose * embedAC V₁.conjTranspose) = 0 := by
    rw [block10_mul, block10_embedBC, block11_embedBC, h_V1dag_block10]
    simp
  -- block01 ((embedBC V₂† · embedAC V₁†) · D) = 0.
  have h_BV2_AV1_D_block01 :
      block01 (embedBC V₂.conjTranspose * embedAC V₁.conjTranspose * D) = 0 := by
    rw [block01_mul, h_BV2_AV1_block01, h_D_block01]
    simp
  have h_BV2_AV1_D_block10 :
      block10 (embedBC V₂.conjTranspose * embedAC V₁.conjTranspose * D) = 0 := by
    rw [block10_mul, h_BV2_AV1_block10, h_D_block10]
    simp
  -- block01 of full RHS = 0.
  have h_RHS_block01 :
      block01 (embedBC V₂.conjTranspose * embedAC V₁.conjTranspose * D *
               embedBC V₄.conjTranspose) = 0 := by
    rw [block01_mul, block01_embedBC, block11_embedBC, h_BV2_AV1_D_block01]
    simp
  have h_RHS_block10 :
      block10 (embedBC V₂.conjTranspose * embedAC V₁.conjTranspose * D *
               embedBC V₄.conjTranspose) = 0 := by
    rw [block10_mul, block00_embedBC, block10_embedBC, h_BV2_AV1_D_block10]
    simp
  -- Step 4: Translate to block01 (embedAC V₃) = 0 via h_iso.
  have h_V3_block01 : block01 (embedAC V₃) = 0 := by rw [h_iso]; exact h_RHS_block01
  have h_V3_block10 : block10 (embedAC V₃) = 0 := by rw [h_iso]; exact h_RHS_block10
  -- Step 5: Convert to blockA_01 V₃ = 0 and blockA_10 V₃ = 0.
  rw [block01_embedAC] at h_V3_block01
  rw [block10_embedAC] at h_V3_block10
  have hI₂ : (I₂ : Mat2) = 1 := rfl
  rw [hI₂, kron2_one_eq_zero_iff] at h_V3_block01 h_V3_block10
  -- Step 6: Apply U_eq_kron2_proj_decomp.
  have h_decomp := U_eq_kron2_proj_decomp h_V3_block01 h_V3_block10
  -- Step 7: blockA_00 V₃ and blockA_11 V₃ are unitary.
  have h_Q0_unit := blockA_00_unitary_of_blockA_10_zero hV₃ h_V3_block10
  have h_Q1_unit := blockA_11_unitary_of_blockA_10_zero hV₃ h_V3_block10
  exact ⟨blockA_00 V₃, blockA_11 V₃, h_Q0_unit, h_Q1_unit, h_decomp⟩

/-! ## Block-diag-A propagation helpers (preparation for chain block decomp) -/

/-- If block01 X = 0, then block00 (X · Y) = block00 X · block00 Y. -/
lemma block00_mul_of_block01_zero (X Y : Mat8) (h : block01 X = 0) :
    block00 (X * Y) = block00 X * block00 Y := by
  rw [block00_mul, h, Matrix.zero_mul, add_zero]

/-- If block10 X = 0, then block11 (X · Y) = block11 X · block11 Y. -/
lemma block11_mul_of_block10_zero (X Y : Mat8) (h : block10 X = 0) :
    block11 (X * Y) = block11 X * block11 Y := by
  rw [block11_mul, h, Matrix.zero_mul, zero_add]

/-- If block01 X = 0 and block01 Y = 0, then block01 (X · Y) = 0. -/
lemma block01_mul_of_both_zero (X Y : Mat8)
    (hX : block01 X = 0) (hY : block01 Y = 0) :
    block01 (X * Y) = 0 := by
  rw [block01_mul, hX, hY]; simp

/-- If block10 X = 0 and block10 Y = 0, then block10 (X · Y) = 0. -/
lemma block10_mul_of_both_zero (X Y : Mat8)
    (hX : block10 X = 0) (hY : block10 Y = 0) :
    block10 (X * Y) = 0 := by
  rw [block10_mul, hX, hY]; simp

/-- After applying A.27 (V₁ controlled + chain block-diag-A ⟹ V₃ controlled),
    the diagonal A-blocks of the chain factor cleanly. This is the algebraic
    setup for Lemma 4.3 (⇒).

    block00 (chain) = (I_B ⊗ P₀) · V₂ · (I_B ⊗ Q₀) · V₄.
    block11 (chain) = (I_B ⊗ P₁) · V₂ · (I_B ⊗ Q₁) · V₄. -/
lemma chain_block_decomp_under_controlled
    (V₁ V₂ V₃ V₄ : Mat4) (P₀ P₁ Q₀ Q₁ : Mat2)
    (h_V₁ : V₁ = kron2 proj0 P₀ + kron2 proj1 P₁)
    (h_V₃ : V₃ = kron2 proj0 Q₀ + kron2 proj1 Q₁) :
    block00 (embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄) =
      kron2 (1 : Mat2) P₀ * V₂ * kron2 (1 : Mat2) Q₀ * V₄ ∧
    block11 (embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄) =
      kron2 (1 : Mat2) P₁ * V₂ * kron2 (1 : Mat2) Q₁ * V₄ := by
  -- Shorthand: each factor is block-diag-A.
  have h01_AC1 : block01 (embedAC V₁) = 0 := by
    rw [h_V₁]; exact block01_embedAC_of_controlled P₀ P₁
  have h10_AC1 : block10 (embedAC V₁) = 0 := by
    rw [h_V₁]; exact block10_embedAC_of_controlled P₀ P₁
  have h01_AC3 : block01 (embedAC V₃) = 0 := by
    rw [h_V₃]; exact block01_embedAC_of_controlled Q₀ Q₁
  have h10_AC3 : block10 (embedAC V₃) = 0 := by
    rw [h_V₃]; exact block10_embedAC_of_controlled Q₀ Q₁
  have h01_BC2 : block01 (embedBC V₂) = 0 := block01_embedBC V₂
  have h10_BC2 : block10 (embedBC V₂) = 0 := block10_embedBC V₂
  have h01_BC4 : block01 (embedBC V₄) = 0 := block01_embedBC V₄
  have h10_BC4 : block10 (embedBC V₄) = 0 := block10_embedBC V₄
  -- block-diag propagation through products.
  have h01_12 : block01 (embedAC V₁ * embedBC V₂) = 0 :=
    block01_mul_of_both_zero _ _ h01_AC1 h01_BC2
  have h01_123 : block01 (embedAC V₁ * embedBC V₂ * embedAC V₃) = 0 :=
    block01_mul_of_both_zero _ _ h01_12 h01_AC3
  have h10_12 : block10 (embedAC V₁ * embedBC V₂) = 0 :=
    block10_mul_of_both_zero _ _ h10_AC1 h10_BC2
  have h10_123 : block10 (embedAC V₁ * embedBC V₂ * embedAC V₃) = 0 :=
    block10_mul_of_both_zero _ _ h10_12 h10_AC3
  -- Compute block00 and block11 via repeated propagation.
  have h_b00_AC1 : block00 (embedAC V₁) = kron2 1 P₀ := by
    rw [h_V₁]; exact block00_embedAC_of_controlled P₀ P₁
  have h_b00_AC3 : block00 (embedAC V₃) = kron2 1 Q₀ := by
    rw [h_V₃]; exact block00_embedAC_of_controlled Q₀ Q₁
  have h_b11_AC1 : block11 (embedAC V₁) = kron2 1 P₁ := by
    rw [h_V₁]; exact block11_embedAC_of_controlled P₀ P₁
  have h_b11_AC3 : block11 (embedAC V₃) = kron2 1 Q₁ := by
    rw [h_V₃]; exact block11_embedAC_of_controlled Q₀ Q₁
  refine ⟨?_, ?_⟩
  · -- block00 (chain) via repeated block00_mul_of_block01_zero.
    rw [block00_mul_of_block01_zero _ _ h01_123,
        block00_mul_of_block01_zero _ _ h01_12,
        block00_mul_of_block01_zero _ _ h01_AC1,
        h_b00_AC1, block00_embedBC, h_b00_AC3, block00_embedBC]
  · -- block11 (chain) via repeated block11_mul_of_block10_zero.
    rw [block11_mul_of_block10_zero _ _ h10_123,
        block11_mul_of_block10_zero _ _ h10_12,
        block11_mul_of_block10_zero _ _ h10_AC1,
        h_b11_AC1, block11_embedBC, h_b11_AC3, block11_embedBC]

/-! ## PY24 Lemma 4.3 — V₁ controlled chain ↔ u₀=u₁ ∨ u₀·u₁=1

PY24 page 396: For 2-qubit unitaries V₁..V₄ and 1-qubit unitaries P₀, P₁
where V₁ = controlled (V₁ = |0⟩⟨0|⊗P₀ + |1⟩⟨1|⊗P₁), the chain
`V₁_AC · V₂_BC · V₃_AC · V₄_BC = CC(Diag(u₀, u₁))` exists iff
`u₀ = u₁ ∨ u₀·u₁ = 1`.

Proof outline:
  (⇐) Constructive — same structure as py24_lemma_6_4 (⇐):
       Case u₀=u₁: use SWAP_BC + controlled-Diag.
       Case u₀·u₁=1: use CNOT-based construction.
  (⇒) Apply A.27 (V₁ controlled + chain block-diag-A ⟹ V₃ controlled).
       Use `chain_block_decomp_under_controlled` to get block equations.
       Apply Lemma 3.3 to extract `u₀=u₁ ∨ u₀·u₁=1`. -/
theorem py24_lemma_4_3 (u₀ u₁ : ℂ)
    (hu₀ : Complex.normSq u₀ = 1) (hu₁ : Complex.normSq u₁ = 1) :
    (∃ V₁ V₂ V₃ V₄ : Mat4, IsUnitary4 V₁ ∧ IsUnitary4 V₂ ∧ IsUnitary4 V₃ ∧
      IsUnitary4 V₄ ∧
      ∃ P₀ P₁ : Mat2, IsUnitary2 P₀ ∧ IsUnitary2 P₁ ∧
        V₁ = kron2 proj0 P₀ + kron2 proj1 P₁ ∧
        embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄ =
          Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁]) ↔
    (u₀ = u₁ ∨ u₀ * u₁ = 1) := by
  constructor
  · -- (⇒) direction: apply A.27 to extract V₃ controlled, then chain_block_decomp,
    -- finally Lemma 3.3 to conclude u₀=u₁ ∨ u₀·u₁=1.
    rintro ⟨V₁, V₂, V₃, V₄, hV₁_unit, hV₂_unit, hV₃_unit, hV₄_unit,
            P₀, P₁, hP₀_unit, hP₁_unit, h_V₁_form, h_chain⟩
    -- Diag(1,...,1,u₀,u₁) is block-diag-A.
    have h_D_block01 :
        block01 (Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] : Mat8) = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [block01, Matrix.diagonal_apply, Matrix.of_apply]
    have h_D_block10 :
        block10 (Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] : Mat8) = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [block10, Matrix.diagonal_apply, Matrix.of_apply]
    -- Apply A.27 to get V₃ controlled.
    obtain ⟨Q₀, Q₁, hQ₀_unit, hQ₁_unit, h_V₃_form⟩ :=
      py24_lemma_A_27 V₁ V₂ V₃ V₄ hV₁_unit hV₂_unit hV₃_unit hV₄_unit
        P₀ P₁ h_V₁_form _ h_D_block01 h_D_block10 h_chain
    -- Apply chain_block_decomp_under_controlled to get block equations.
    obtain ⟨h_block00, h_block11⟩ :=
      chain_block_decomp_under_controlled V₁ V₂ V₃ V₄ P₀ P₁ Q₀ Q₁
        h_V₁_form h_V₃_form
    -- Compute block00, block11 of Diag(1,...,1,u₀,u₁).
    have h_block00_chain :
        block00 (Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] : Mat8) = (1 : Mat4) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [block00, Matrix.diagonal_apply, Matrix.of_apply]
    have h_block11_chain :
        block11 (Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] : Mat8) =
        Matrix.diagonal ![1, 1, u₀, u₁] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [block11, Matrix.diagonal_apply, Matrix.of_apply,
              Matrix.cons_val_zero, Matrix.cons_val_one]
    -- Combine: (kron2 1 P₀) · V₂ · (kron2 1 Q₀) · V₄ = 1.
    have h_E0 : kron2 (1 : Mat2) P₀ * V₂ * kron2 (1 : Mat2) Q₀ * V₄ = 1 := by
      rw [← h_block00, h_chain, h_block00_chain]
    have h_E1 :
        kron2 (1 : Mat2) P₁ * V₂ * kron2 (1 : Mat2) Q₁ * V₄ =
        Matrix.diagonal ![1, 1, u₀, u₁] := by
      rw [← h_block11, h_chain, h_block11_chain]
    -- From h_E0, derive (kron2 1 P₀) · V₂ · (kron2 1 Q₀) = V₄†.
    have h_V4dag_eq :
        kron2 (1 : Mat2) P₀ * V₂ * kron2 (1 : Mat2) Q₀ = V₄.conjTranspose := by
      have h_V4_inv : V₄ * V₄.conjTranspose = 1 := mul_eq_one_comm.mp hV₄_unit
      have h := congrArg (· * V₄.conjTranspose) h_E0
      simp only at h
      rw [mul_assoc, h_V4_inv, mul_one, Matrix.one_mul] at h
      exact h
    -- From h_E1 by same manipulation: kron2 1 P₁·V₂·kron2 1 Q₁ = Diag · V₄†.
    have h_E1_alt :
        kron2 (1 : Mat2) P₁ * V₂ * kron2 (1 : Mat2) Q₁ =
        Matrix.diagonal ![1, 1, u₀, u₁] * V₄.conjTranspose := by
      have h_V4_inv : V₄ * V₄.conjTranspose = 1 := mul_eq_one_comm.mp hV₄_unit
      have h := congrArg (· * V₄.conjTranspose) h_E1
      simp only at h
      rw [mul_assoc, h_V4_inv, mul_one] at h
      exact h
    -- Substitute V₄† = kron2 1 P₀·V₂·kron2 1 Q₀ to relate the two factor forms.
    have h_combined :
        kron2 (1 : Mat2) P₁ * V₂ * kron2 (1 : Mat2) Q₁ =
        Matrix.diagonal ![1, 1, u₀, u₁] *
          (kron2 (1 : Mat2) P₀ * V₂ * kron2 (1 : Mat2) Q₀) := by
      rw [h_E1_alt, ← h_V4dag_eq]
    -- Helpers: products of unitaries are unitary (needed for applying 3.3 with P=P₀P₁†).
    have hP₀P₁dag_unit : IsUnitary2 (P₀ * P₁.conjTranspose) := by
      change (P₀ * P₁.conjTranspose).conjTranspose * (P₀ * P₁.conjTranspose) = 1
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          mul_assoc, ← mul_assoc P₀.conjTranspose, hP₀_unit, Matrix.one_mul]
      exact mul_eq_one_comm.mp hP₁_unit
    have hQ₁Q₀dag_unit : IsUnitary2 (Q₁ * Q₀.conjTranspose) := by
      change (Q₁ * Q₀.conjTranspose).conjTranspose * (Q₁ * Q₀.conjTranspose) = 1
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          mul_assoc, ← mul_assoc Q₁.conjTranspose, hQ₁_unit, Matrix.one_mul]
      exact mul_eq_one_comm.mp hQ₀_unit
    -- Multiply h_combined by X† (where X = kron2 1 P₀ · V₂ · kron2 1 Q₀) on right.
    -- X = V₄†, so X · X† = V₄† · V₄ = 1.
    have h_step1 :
        (kron2 (1 : Mat2) P₁ * V₂ * kron2 (1 : Mat2) Q₁) *
          (kron2 (1 : Mat2) P₀ * V₂ * kron2 (1 : Mat2) Q₀).conjTranspose =
        Matrix.diagonal ![1, 1, u₀, u₁] := by
      rw [h_combined, mul_assoc]
      rw [show (kron2 (1 : Mat2) P₀ * V₂ * kron2 (1 : Mat2) Q₀) *
                 (kron2 (1 : Mat2) P₀ * V₂ * kron2 (1 : Mat2) Q₀).conjTranspose = 1 by
              rw [h_V4dag_eq, Matrix.conjTranspose_conjTranspose]
              exact hV₄_unit]
      rw [mul_one]
    -- Helper kron2 identities for combining adjacent terms.
    have h_kron_Q : kron2 (1 : Mat2) Q₁ * kron2 (1 : Mat2) Q₀.conjTranspose =
                    kron2 (1 : Mat2) (Q₁ * Q₀.conjTranspose) := by
      rw [kron2_mul, one_mul]
    have h_kron_P_inv :
        kron2 (1 : Mat2) (P₀ * P₁.conjTranspose) * kron2 (1 : Mat2) P₁ =
        kron2 (1 : Mat2) P₀ := by
      rw [kron2_mul, one_mul, mul_assoc, hP₁_unit, mul_one]
    -- Helper: (kron2 1 X)† = kron2 1 X† (conjTranspose distributes over kron2).
    have h_kron_conjT : ∀ X : Mat2, (kron2 (1 : Mat2) X).conjTranspose =
                                     kron2 (1 : Mat2) X.conjTranspose := by
      intro X
      rw [kron2_conjTranspose, Matrix.conjTranspose_one]
    -- Expand h_step1's conjT factor.
    have h_step2 :
        kron2 (1 : Mat2) P₁ * V₂ * kron2 (1 : Mat2) Q₁ *
          (kron2 (1 : Mat2) Q₀.conjTranspose *
           (V₂.conjTranspose * kron2 (1 : Mat2) P₀.conjTranspose)) =
        Matrix.diagonal ![1, 1, u₀, u₁] := by
      have h := h_step1
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          h_kron_conjT, h_kron_conjT] at h
      exact h
    -- Re-associate and apply h_kron_Q to combine adjacent kron2 terms.
    have h_step3 :
        kron2 (1 : Mat2) P₁ * V₂ * kron2 (1 : Mat2) (Q₁ * Q₀.conjTranspose) *
          V₂.conjTranspose * kron2 (1 : Mat2) P₀.conjTranspose =
        Matrix.diagonal ![1, 1, u₀, u₁] := by
      rw [← h_kron_Q]
      calc kron2 (1 : Mat2) P₁ * V₂ *
            (kron2 (1 : Mat2) Q₁ * kron2 (1 : Mat2) Q₀.conjTranspose) *
            V₂.conjTranspose * kron2 (1 : Mat2) P₀.conjTranspose
          = kron2 (1 : Mat2) P₁ * V₂ * kron2 (1 : Mat2) Q₁ *
              (kron2 (1 : Mat2) Q₀.conjTranspose *
               (V₂.conjTranspose * kron2 (1 : Mat2) P₀.conjTranspose)) := by noncomm_ring
        _ = Matrix.diagonal ![1, 1, u₀, u₁] := h_step2
    -- Multiply by kron2 1 (P₀·P₁†) on left to insert the leading factor.
    have h_step4 :
        kron2 (1 : Mat2) P₀ * V₂ * kron2 (1 : Mat2) (Q₁ * Q₀.conjTranspose) *
          V₂.conjTranspose * kron2 (1 : Mat2) P₀.conjTranspose =
        kron2 (1 : Mat2) (P₀ * P₁.conjTranspose) * Matrix.diagonal ![1, 1, u₀, u₁] := by
      calc kron2 (1 : Mat2) P₀ * V₂ * kron2 (1 : Mat2) (Q₁ * Q₀.conjTranspose) *
              V₂.conjTranspose * kron2 (1 : Mat2) P₀.conjTranspose
          = kron2 (1 : Mat2) (P₀ * P₁.conjTranspose) * kron2 (1 : Mat2) P₁ * V₂ *
              kron2 (1 : Mat2) (Q₁ * Q₀.conjTranspose) * V₂.conjTranspose *
              kron2 (1 : Mat2) P₀.conjTranspose := by
                rw [show (kron2 (1 : Mat2) P₀ : Mat4) =
                        kron2 (1 : Mat2) (P₀ * P₁.conjTranspose) * kron2 (1 : Mat2) P₁
                      from h_kron_P_inv.symm]
        _ = kron2 (1 : Mat2) (P₀ * P₁.conjTranspose) *
              (kron2 (1 : Mat2) P₁ * V₂ * kron2 (1 : Mat2) (Q₁ * Q₀.conjTranspose) *
               V₂.conjTranspose * kron2 (1 : Mat2) P₀.conjTranspose) := by noncomm_ring
        _ = kron2 (1 : Mat2) (P₀ * P₁.conjTranspose) *
              Matrix.diagonal ![1, 1, u₀, u₁] := by rw [h_step3]
    -- Re-associate to expose W · M · W† similarity form (W = kron2 1 P₀ · V₂).
    have h_similarity :
        (kron2 (1 : Mat2) P₀ * V₂) * kron2 (1 : Mat2) (Q₁ * Q₀.conjTranspose) *
          (kron2 (1 : Mat2) P₀ * V₂).conjTranspose =
        kron2 (1 : Mat2) (P₀ * P₁.conjTranspose) *
          Matrix.diagonal ![1, 1, u₀, u₁] := by
      rw [Matrix.conjTranspose_mul, h_kron_conjT]
      calc (kron2 (1 : Mat2) P₀ * V₂) *
            kron2 (1 : Mat2) (Q₁ * Q₀.conjTranspose) *
            (V₂.conjTranspose * kron2 (1 : Mat2) P₀.conjTranspose)
          = kron2 (1 : Mat2) P₀ * V₂ *
              kron2 (1 : Mat2) (Q₁ * Q₀.conjTranspose) *
              V₂.conjTranspose * kron2 (1 : Mat2) P₀.conjTranspose := by noncomm_ring
        _ = kron2 (1 : Mat2) (P₀ * P₁.conjTranspose) *
              Matrix.diagonal ![1, 1, u₀, u₁] := h_step4
    -- Apply A.3 to Q₁·Q₀† to extract eigenvalues c, d and a Mat2 diagonalization.
    obtain ⟨c, d, V_QQ, hV_QQ_unit, hV_QQ_diag⟩ :=
      py24_lemma_A_3 (Q₁ * Q₀.conjTranspose) hQ₁Q₀dag_unit
    -- hV_QQ_diag : V_QQ.conjTranspose * (Q₁ · Q₀†) * V_QQ = Matrix.diagonal ![c, d]
    -- Helper: SWAP_4 conjugation maps Diag(c,d,c,d) to Diag(c,c,d,d).
    have h_SWAP4_diag :
        SWAP_4.conjTranspose * Matrix.diagonal ![c, d, c, d] * SWAP_4 =
        Matrix.diagonal ![c, c, d, d] := by
      rw [SWAP_4_conjTranspose]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [SWAP_4, swap4_perm, Matrix.mul_apply, Fin.sum_univ_four,
              Matrix.diagonal_apply, Matrix.of_apply,
              Matrix.cons_val_zero, Matrix.cons_val_one]
    -- Apply A.6 with P=Q=Q₁·Q₀† to diagonalize kron2 1 (Q₁·Q₀†).
    obtain ⟨V_6, hV_6_unit, hV_6_diag⟩ :=
      py24_lemma_A_6 (Q₁ * Q₀.conjTranspose) (Q₁ * Q₀.conjTranspose)
        hQ₁Q₀dag_unit hQ₁Q₀dag_unit c d c d
        ⟨V_QQ, hV_QQ_unit, hV_QQ_diag⟩ ⟨V_QQ, hV_QQ_unit, hV_QQ_diag⟩
    -- hV_6_diag : V_6† · (kron2 proj0 (Q₁·Q₀†) + kron2 proj1 (Q₁·Q₀†)) · V_6 = Diag ![c, d, c, d]
    -- Bridge: kron2 proj0 X + kron2 proj1 X = kron2 1 X (specialized to X = Q₁·Q₀†).
    have h_kron_proj_sum :
        kron2 proj0 (Q₁ * Q₀.conjTranspose) +
          kron2 proj1 (Q₁ * Q₀.conjTranspose) =
        kron2 (1 : Mat2) (Q₁ * Q₀.conjTranspose) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [kron2, proj0, proj1, Matrix.add_apply, Matrix.of_apply,
              Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    -- Convert hV_6_diag's LHS to use kron2 1 (Q₁·Q₀†).
    rw [h_kron_proj_sum] at hV_6_diag
    -- hV_6_diag: V_6† · (kron2 1 (Q₁·Q₀†)) · V_6 = Diag ![c, d, c, d]
    -- Define V_chain := (kron2 1 P₀·V₂) · V_6 · SWAP_4 and prove unitarity.
    set V_chain : Mat4 := kron2 (1 : Mat2) P₀ * V₂ * V_6 * SWAP_4 with hV_chain_def
    have hV_chain_unit : IsUnitary4 V_chain :=
      isUnitary4_mul (isUnitary4_mul (isUnitary4_mul
        (isUnitary4_kron2 isUnitary2_one hP₀_unit) hV₂_unit) hV_6_unit)
        isUnitary4_SWAP_4
    -- Inner cancellation: W† · M · W = kron2 1 (Q₁·Q₀†) where W = kron2 1 P₀·V₂.
    have hW_unit : IsUnitary4 (kron2 (1 : Mat2) P₀ * V₂) :=
      isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hP₀_unit) hV₂_unit
    have h_W_M_W :
        (kron2 (1 : Mat2) P₀ * V₂).conjTranspose *
          (kron2 (1 : Mat2) (P₀ * P₁.conjTranspose) *
             Matrix.diagonal ![1, 1, u₀, u₁]) *
          (kron2 (1 : Mat2) P₀ * V₂) =
        kron2 (1 : Mat2) (Q₁ * Q₀.conjTranspose) := by
      calc (kron2 (1 : Mat2) P₀ * V₂).conjTranspose *
            (kron2 (1 : Mat2) (P₀ * P₁.conjTranspose) *
               Matrix.diagonal ![1, 1, u₀, u₁]) *
            (kron2 (1 : Mat2) P₀ * V₂)
          = (kron2 (1 : Mat2) P₀ * V₂).conjTranspose *
              ((kron2 (1 : Mat2) P₀ * V₂) *
               kron2 (1 : Mat2) (Q₁ * Q₀.conjTranspose) *
               (kron2 (1 : Mat2) P₀ * V₂).conjTranspose) *
              (kron2 (1 : Mat2) P₀ * V₂) := by rw [← h_similarity]
        _ = ((kron2 (1 : Mat2) P₀ * V₂).conjTranspose *
              (kron2 (1 : Mat2) P₀ * V₂)) *
              kron2 (1 : Mat2) (Q₁ * Q₀.conjTranspose) *
              ((kron2 (1 : Mat2) P₀ * V₂).conjTranspose *
               (kron2 (1 : Mat2) P₀ * V₂)) := by noncomm_ring
        _ = 1 * kron2 (1 : Mat2) (Q₁ * Q₀.conjTranspose) * 1 := by
              rw [show (kron2 (1 : Mat2) P₀ * V₂).conjTranspose *
                       (kron2 (1 : Mat2) P₀ * V₂) = 1 from hW_unit]
        _ = kron2 (1 : Mat2) (Q₁ * Q₀.conjTranspose) := by
              rw [Matrix.one_mul, Matrix.mul_one]
    -- Final calc: V_chain† · M · V_chain = Diag(c,c,d,d).
    have h_VchainMVchain :
        V_chain.conjTranspose *
          (kron2 (1 : Mat2) (P₀ * P₁.conjTranspose) *
             Matrix.diagonal ![1, 1, u₀, u₁]) *
          V_chain =
        Matrix.diagonal ![c, c, d, d] := by
      rw [hV_chain_def]
      calc (kron2 (1 : Mat2) P₀ * V₂ * V_6 * SWAP_4).conjTranspose *
            (kron2 (1 : Mat2) (P₀ * P₁.conjTranspose) *
               Matrix.diagonal ![1, 1, u₀, u₁]) *
            (kron2 (1 : Mat2) P₀ * V₂ * V_6 * SWAP_4)
          = SWAP_4.conjTranspose * V_6.conjTranspose *
              ((kron2 (1 : Mat2) P₀ * V₂).conjTranspose *
                 (kron2 (1 : Mat2) (P₀ * P₁.conjTranspose) *
                    Matrix.diagonal ![1, 1, u₀, u₁]) *
                 (kron2 (1 : Mat2) P₀ * V₂)) * V_6 * SWAP_4 := by
                rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
                noncomm_ring
        _ = SWAP_4.conjTranspose * V_6.conjTranspose *
              kron2 (1 : Mat2) (Q₁ * Q₀.conjTranspose) * V_6 * SWAP_4 := by
                rw [h_W_M_W]
        _ = SWAP_4.conjTranspose *
              (V_6.conjTranspose *
               kron2 (1 : Mat2) (Q₁ * Q₀.conjTranspose) * V_6) * SWAP_4 := by
                noncomm_ring
        _ = SWAP_4.conjTranspose * Matrix.diagonal ![c, d, c, d] * SWAP_4 := by
                rw [hV_6_diag]
        _ = Matrix.diagonal ![c, c, d, d] := h_SWAP4_diag
    -- Apply Lemma 3.3 to conclude u₀ = u₁ ∨ u₀ · u₁ = 1.
    exact (py24_lemma_3_3 u₀ u₁ hu₀ hu₁).mp
      ⟨P₀ * P₁.conjTranspose, hP₀P₁dag_unit, c, d, V_chain,
       hV_chain_unit, h_VchainMVchain⟩
  · -- (⇐) direction: case-split.
    rintro (h_eq | h_prod)
    · -- Case 1: u₀ = u₁. V₁=1 (P₀=P₁=1), V₂=SWAP_4, V₃=Diag(1,1,1,u₀), V₄=SWAP_4.
      subst h_eq
      refine ⟨1, SWAP_4, Matrix.diagonal ![1, 1, 1, u₀], SWAP_4,
              ?_, ?_, ?_, ?_, 1, 1, isUnitary2_one, isUnitary2_one, ?_, ?_⟩
      · -- IsUnitary4 1
        change (1 : Mat4).conjTranspose * (1 : Mat4) = 1
        rw [Matrix.conjTranspose_one, Matrix.one_mul]
      · exact isUnitary4_SWAP_4
      · exact isUnitary4_diag_one_one_one_u u₀ hu₀
      · exact isUnitary4_SWAP_4
      · -- V₁ = kron2 proj0 1 + kron2 proj1 1 = 1.
        symm
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [kron2, proj0, proj1, Matrix.add_apply, Matrix.of_apply,
                Matrix.one_apply]
      · -- Chain identity: 1·SWAP_BC·embedAC(Diag(1,1,1,u₀))·SWAP_BC = Diag(1,...,1,u₀,u₀).
        rw [embedAC_one, one_mul]
        rw [show embedBC SWAP_4 = SWAP_BC from SWAP_BC_eq_embedBC.symm]
        rw [swap_bc_embedAC]
        exact embedAB_diag_one_one_one_u u₀
    · -- Case 2: u₀ · u₁ = 1. V₁ = Diag(1,1,1,u₁) = controlled with P₀=1, P₁=Diag(1,u₁).
      refine ⟨Matrix.diagonal ![1, 1, 1, u₁], CNOT_4_local,
              Matrix.diagonal ![1, 1, 1, u₀], CNOT_4_local,
              ?_, ?_, ?_, ?_,
              1, Matrix.diagonal ![1, u₁], isUnitary2_one, ?_, ?_, ?_⟩
      · exact isUnitary4_diag_one_one_one_u u₁ hu₁
      · exact isUnitary4_CNOT_4_local
      · exact isUnitary4_diag_one_one_one_u u₀ hu₀
      · exact isUnitary4_CNOT_4_local
      · -- IsUnitary2 (Diag ![1, u₁]).
        change (Matrix.diagonal ![1, u₁]).conjTranspose * Matrix.diagonal ![1, u₁] = 1
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.mul_apply,
                Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [show starRingEnd ℂ u₁ * u₁ = (Complex.normSq u₁ : ℂ) by
              rw [mul_comm]; exact (Complex.mul_conj u₁).symm ▸ rfl]
        exact_mod_cast hu₁
      · -- V₁ = Diag(1,1,1,u₁) = kron2 proj0 1 + kron2 proj1 (Diag ![1, u₁]).
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [kron2, proj0, proj1, Matrix.diagonal, Matrix.add_apply,
                Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
                Matrix.one_apply]
      · -- Chain identity: Diag·CNOT·Diag·CNOT = Diag(1,...,1,u₀,u₁) when u₀·u₁=1.
        rw [chain_diag_CNOT_diag_CNOT u₀ u₁, h_prod]

/-- Helper for 4.4 (⇒): controlled gate form (with projector on first qubit)
    is closed under conjTranspose, with the inner blocks daggered.
    `(proj0 ⊗ P₀ + proj1 ⊗ P₁)† = proj0 ⊗ P₀† + proj1 ⊗ P₁†` (proj0/1 are
    real symmetric so equal to their daggers). -/
lemma controlled_first_conjTranspose (P₀ P₁ : Mat2) :
    (kron2 proj0 P₀ + kron2 proj1 P₁).conjTranspose
      = kron2 proj0 P₀.conjTranspose + kron2 proj1 P₁.conjTranspose := by
  rw [Matrix.conjTranspose_add, kron2_conjTranspose, kron2_conjTranspose,
      proj0_conjTranspose, proj1_conjTranspose]

/-- Helper for 4.4 (⇒): SWAP_AB preserves the chain target diagonal.
    Reason: SWAP_AB fixes indices {0,1,6,7} (where a=b) and swaps {2,4}, {3,5}
    (where a≠b); since Diag(1,1,1,1,1,1,u₀,u₁) has equal entries at positions
    2,3,4,5 (all 1), the conjugation is a no-op. -/
lemma swap_ab_diag_chain_target (u₀ u₁ : ℂ) :
    SWAP_AB * (Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] : Mat8) * SWAP_AB =
    (Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] : Mat8) := by
  ext i j
  unfold SWAP_AB swap_ab_perm
  simp only [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_eight,
             Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;> simp

/-- Helper for 4.4 (⇒): SWAP_AB conjugation converts the AC-BC-AC-BC chain
    pattern to BC-AC-BC-AC. Inserts `SWAP_AB * SWAP_AB = 1` between factors,
    then re-associates so each gate gets its own conjugation pair. -/
lemma swap_ab_chain_AC_BC_AC_BC (V₁ V₂ V₃ V₄ : Mat4) :
    SWAP_AB * (embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄) * SWAP_AB =
    embedBC V₁ * embedAC V₂ * embedBC V₃ * embedAC V₄ := by
  have h_sq : SWAP_AB * SWAP_AB = 1 := SWAP_AB_sq
  have key : SWAP_AB * (embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄) * SWAP_AB =
             (SWAP_AB * embedAC V₁ * SWAP_AB) * (SWAP_AB * embedBC V₂ * SWAP_AB) *
             (SWAP_AB * embedAC V₃ * SWAP_AB) * (SWAP_AB * embedBC V₄ * SWAP_AB) := by
    have e : (SWAP_AB * embedAC V₁ * SWAP_AB) * (SWAP_AB * embedBC V₂ * SWAP_AB) *
             (SWAP_AB * embedAC V₃ * SWAP_AB) * (SWAP_AB * embedBC V₄ * SWAP_AB) =
             SWAP_AB * embedAC V₁ * (SWAP_AB * SWAP_AB) * embedBC V₂ *
             (SWAP_AB * SWAP_AB) * embedAC V₃ * (SWAP_AB * SWAP_AB) *
             embedBC V₄ * SWAP_AB := by noncomm_ring
    rw [e]
    simp only [h_sq, mul_one]
    noncomm_ring
  rw [key, swap_ab_embedAC, swap_ab_embedBC, swap_ab_embedAC, swap_ab_embedBC]

/-! ## PY24 Lemma 4.4 — V₄ controlled chain ↔ u₀=u₁ ∨ u₀·u₁=1

PY24 page 607: symmetric to Lemma 4.3 — the chain
`V₁_AC · V₂_BC · V₃_AC · V₄_BC = CC(Diag(u₀, u₁))` exists with V₄ controlled
(rather than V₁) iff `u₀ = u₁ ∨ u₀·u₁ = 1`.

Paper says: "follows easily from Lemma 4.3 by exchanging the roles of A and
B and considering the conjugate transpose of the product." -/
theorem py24_lemma_4_4 (u₀ u₁ : ℂ)
    (hu₀ : Complex.normSq u₀ = 1) (hu₁ : Complex.normSq u₁ = 1) :
    (∃ V₁ V₂ V₃ V₄ : Mat4, IsUnitary4 V₁ ∧ IsUnitary4 V₂ ∧ IsUnitary4 V₃ ∧
      IsUnitary4 V₄ ∧
      ∃ P₀ P₁ : Mat2, IsUnitary2 P₀ ∧ IsUnitary2 P₁ ∧
        V₄ = kron2 proj0 P₀ + kron2 proj1 P₁ ∧
        embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄ =
          Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁]) ↔
    (u₀ = u₁ ∨ u₀ * u₁ = 1) := by
  constructor
  · -- (⇒) direction: reduce to 4.3 via SWAP_AB conjugation + dagger.
    rintro ⟨V₁, V₂, V₃, V₄, hV₁_unit, hV₂_unit, hV₃_unit, hV₄_unit,
            P₀, P₁, hP₀_unit, hP₁_unit, h_V₄_form, h_chain⟩
    -- Step 1: SWAP_AB conjugation flips AC-BC-AC-BC to BC-AC-BC-AC pattern.
    -- Using `swap_ab_chain_AC_BC_AC_BC` (chain helper) +
    -- `swap_ab_diag_chain_target` (diagonal fixed under SWAP_AB conjugation).
    have h_swapped :
        embedBC V₁ * embedAC V₂ * embedBC V₃ * embedAC V₄ =
        Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] := by
      rw [← swap_ab_chain_AC_BC_AC_BC, h_chain, swap_ab_diag_chain_target]
    -- Step 2: take dagger of h_swapped to reach 4.3's hypothesis pattern.
    -- (X1·X2·X3·X4)† = X4†·X3†·X2†·X1†, and embedAC/BC commute with dagger.
    have h_dagger :
        embedAC V₄.conjTranspose * embedBC V₃.conjTranspose *
        embedAC V₂.conjTranspose * embedBC V₁.conjTranspose =
        Matrix.diagonal
          ![1, 1, 1, 1, 1, 1, starRingEnd ℂ u₀, starRingEnd ℂ u₁] := by
      calc embedAC V₄.conjTranspose * embedBC V₃.conjTranspose *
           embedAC V₂.conjTranspose * embedBC V₁.conjTranspose
          = (embedBC V₁ * embedAC V₂ * embedBC V₃ * embedAC V₄).conjTranspose := by
              simp only [Matrix.conjTranspose_mul, embedAC_conjTranspose,
                         embedBC_conjTranspose]
              noncomm_ring
        _ = (Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] : Mat8).conjTranspose := by
              rw [h_swapped]
        _ = Matrix.diagonal
              ![1, 1, 1, 1, 1, 1, starRingEnd ℂ u₀, starRingEnd ℂ u₁] := by
              ext i j
              simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
              fin_cases i <;> fin_cases j <;> simp
    -- Step 3: V_i† are unitary; V₄† is controlled with P₀†, P₁†ᵀ.
    have hV₁_dag_unit : IsUnitary4 V₁.conjTranspose :=
      isUnitary4_conjTranspose hV₁_unit
    have hV₂_dag_unit : IsUnitary4 V₂.conjTranspose :=
      isUnitary4_conjTranspose hV₂_unit
    have hV₃_dag_unit : IsUnitary4 V₃.conjTranspose :=
      isUnitary4_conjTranspose hV₃_unit
    have hV₄_dag_unit : IsUnitary4 V₄.conjTranspose :=
      isUnitary4_conjTranspose hV₄_unit
    have hP₀_dag_unit : IsUnitary2 P₀.conjTranspose :=
      isUnitary2_conjTranspose hP₀_unit
    have hP₁_dag_unit : IsUnitary2 P₁.conjTranspose :=
      isUnitary2_conjTranspose hP₁_unit
    have h_V₄_dag_form : V₄.conjTranspose =
        kron2 proj0 P₀.conjTranspose + kron2 proj1 P₁.conjTranspose := by
      rw [h_V₄_form, controlled_first_conjTranspose]
    -- Step 4: apply 4.3 to (V₄†, V₃†, V₂†, V₁†) with target Diag(...,conj u₀, conj u₁).
    have hcu₀ : Complex.normSq (starRingEnd ℂ u₀) = 1 := by
      rw [Complex.normSq_conj]; exact hu₀
    have hcu₁ : Complex.normSq (starRingEnd ℂ u₁) = 1 := by
      rw [Complex.normSq_conj]; exact hu₁
    have h_43 := (py24_lemma_4_3 (starRingEnd ℂ u₀) (starRingEnd ℂ u₁) hcu₀ hcu₁).mp
        ⟨V₄.conjTranspose, V₃.conjTranspose, V₂.conjTranspose, V₁.conjTranspose,
         hV₄_dag_unit, hV₃_dag_unit, hV₂_dag_unit, hV₁_dag_unit,
         P₀.conjTranspose, P₁.conjTranspose, hP₀_dag_unit, hP₁_dag_unit,
         h_V₄_dag_form, h_dagger⟩
    -- Step 5: convert conj u₀ = conj u₁ ∨ conj u₀ * conj u₁ = 1 → u₀ = u₁ ∨ u₀·u₁ = 1.
    rcases h_43 with h_eq | h_prod
    · left
      have h := congrArg (starRingEnd ℂ) h_eq
      rwa [Complex.conj_conj, Complex.conj_conj] at h
    · right
      have h := congrArg (starRingEnd ℂ) h_prod
      rw [map_mul, Complex.conj_conj, Complex.conj_conj, map_one] at h
      exact h
  · -- (⇐) direction: case-split.
    rintro (h_eq | h_prod)
    · -- Case 1: u₀ = u₁. V₁=SWAP_4, V₂=Diag(1,1,1,u₀), V₃=SWAP_4, V₄=1.
      subst h_eq
      refine ⟨SWAP_4, Matrix.diagonal ![1, 1, 1, u₀], SWAP_4, 1,
              isUnitary4_SWAP_4, isUnitary4_diag_one_one_one_u u₀ hu₀,
              isUnitary4_SWAP_4, ?_,
              1, 1, isUnitary2_one, isUnitary2_one, ?_, ?_⟩
      · -- IsUnitary4 1.
        change (1 : Mat4).conjTranspose * (1 : Mat4) = 1
        rw [Matrix.conjTranspose_one, Matrix.one_mul]
      · -- V₄ = 1 = kron2 proj0 1 + kron2 proj1 1.
        symm
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [kron2, proj0, proj1, Matrix.add_apply, Matrix.of_apply,
                Matrix.one_apply]
      · -- Chain identity.
        rw [embedBC_one, mul_one]
        rw [show embedAC SWAP_4 = SWAP_AC from SWAP_AC_eq_embedAC.symm]
        rw [swap_ac_embedBC]
        rw [show SWAP_4 * Matrix.diagonal ![1, 1, 1, u₀] * SWAP_4 =
                 Matrix.diagonal ![1, 1, 1, u₀] from ?_]
        · exact embedAB_diag_one_one_one_u u₀
        · -- SWAP_4 · Diag(1,1,1,u₀) · SWAP_4 = Diag(1,1,1,u₀).
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [SWAP_4, swap4_perm, Matrix.diagonal, Matrix.mul_apply,
                  Matrix.of_apply, Fin.sum_univ_four, Matrix.cons_val_zero,
                  Matrix.cons_val_one]
    · -- Case 2: u₀·u₁ = 1. V₁=Diag(1,1,1,u₁), V₂=CNOT, V₃=Diag(1,1,1,u₀), V₄=CNOT.
      -- V₄ = CNOT_4_local = kron2 proj0 1 + kron2 proj1 pauliX is controlled.
      refine ⟨Matrix.diagonal ![1, 1, 1, u₁], CNOT_4_local,
              Matrix.diagonal ![1, 1, 1, u₀], CNOT_4_local,
              isUnitary4_diag_one_one_one_u u₁ hu₁,
              isUnitary4_CNOT_4_local,
              isUnitary4_diag_one_one_one_u u₀ hu₀,
              isUnitary4_CNOT_4_local,
              1, pauliX, isUnitary2_one, ?_, ?_, ?_⟩
      · -- IsUnitary2 pauliX.
        change pauliX.conjTranspose * pauliX = 1
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [pauliX, Matrix.conjTranspose_apply, Matrix.mul_apply,
                Matrix.of_apply, Fin.sum_univ_two]
      · -- V₄ = CNOT_4_local = kron2 proj0 1 + kron2 proj1 pauliX.
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [CNOT_4_local, kron2, proj0, proj1, pauliX,
                Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
      · -- Chain identity from chain_diag_CNOT_diag_CNOT, then apply u₀·u₁=1.
        rw [chain_diag_CNOT_diag_CNOT, h_prod]

/-! ## A.24 Step 4 helpers: embedAB / embedAC actions on triple-tensor states -/

set_option maxHeartbeats 800000 in
-- funext k + fin_cases × 8 + simp on Mat8.apply / embedAB / tensor2_1.
/-- **A.24 Step 4 helper #2**: embedAB action on tensor2_1 form.
    `embedAB V` (V acts on (A,B), identity on C) applied to `tensor2_1 ϕ γ`
    (= ϕ on (A,B), γ on C) gives `tensor2_1 (V·ϕ) γ`. -/
lemma embedAB_apply_tensor2_1 (V : Mat4) (ϕ : Vec2) (γ : Vec1) :
    Mat8.apply (embedAB V) (tensor2_1 ϕ γ) =
    tensor2_1 (Mat4.apply V ϕ) γ := by
  funext k
  fin_cases k <;>
    simp [Mat8.apply, Mat4.apply, embedAB, tensor2_1, Matrix.of_apply,
          Fin.sum_univ_eight, Fin.sum_univ_four] <;>
    ring

/-- **A.24 Step 4 KEY equation**: under M block-diag-A and the A.21 hypothesis
    `tensor1_1 α β = V·(tensor1_1 ket0_1 ψ)`, the 3-qubit equation
    `embedAC (U · kron2 P† 1) · (|0⟩⊗β⊗γ) = |0⟩⊗(W₀·(ψ⊗γ))` holds for all γ.
    Proved by chained rewrites: factor `embedAC (U·kron2 p 1)` as
    `embedAC U · embedAB (kron2 p 1)` (via `embedAB_kron2_one_eq_embedAC_kron2_one`
    + `embedAC_mul`), apply embedAB-action helpers (iters 188/189) to reduce
    `embedAB (kron2 p 1) · (|0⟩⊗β⊗γ)` to `tensor2_1 (tensor1_1 α β) γ`,
    substitute via `hαβ` to convert this to `embedAB V · (|0⟩⊗ψ⊗γ)`, then
    apply `Mat8.apply_block_diag_A_tensor1_2_ket0` (iter 187). -/
private lemma A_24_step4_KEY
    {U V : Mat4} {α β ψ : Vec1}
    (hαβ : tensor1_1 α β = Mat4.apply V (tensor1_1 ket0_1 ψ))
    (h10 : block10 (embedAC U * embedAB V) = 0)
    (γ : Vec1) :
    Mat8.apply (embedAC (U * kron2 (unitary_first_column α) 1))
        (tensor1_2 ket0_1 (tensor1_1 β γ)) =
    tensor1_2 ket0_1 (Mat4.apply (block00 (embedAC U * embedAB V))
      (tensor1_1 ψ γ)) := by
  rw [← embedAC_mul, ← embedAB_kron2_one_eq_embedAC_kron2_one,
      Mat8.apply_mul,
      tensor1_2_tensor1_1_eq_tensor2_1_tensor1_1,
      embedAB_apply_tensor2_1,
      kron2_apply_tensor1_1, Mat2.apply_one,
      unitary_first_column_apply_ket0, hαβ,
      ← embedAB_apply_tensor2_1,
      ← tensor1_2_tensor1_1_eq_tensor2_1_tensor1_1,
      ← Mat8.apply_mul]
  exact Mat8.apply_block_diag_A_tensor1_2_ket0 h10 (tensor1_1 ψ γ)

/-- **A.24 Step 4 closure**: under the same hypotheses as `A_24_step4_KEY`,
    plus `IsQubit1 β` (so β ≠ 0), conclude
    `blockA_10 (U * kron2 (unitary_first_column α) 1) = 0`.
    Proof: extract upper-half components from the KEY 3-qubit equation.
    LHS upper half = `tensor1_1 β (Mat2.apply (blockA_10 X) γ)` via
    `Mat8.apply_tensor1_2_ket0_upper` + `block10_embedAC` + `kron2_apply_tensor1_1`.
    RHS upper half = 0 (since `tensor1_2 ket0_1 v` has zero upper half).
    Hence `tensor1_1 β (Mat2.apply (blockA_10 X) γ) = 0`; β ≠ 0 ⟹
    `Mat2.apply (blockA_10 X) γ = 0` for all γ; conclude `blockA_10 X = 0`. -/
private lemma A_24_blockA_10_zero
    {U V : Mat4} {α β ψ : Vec1}
    (hαβ : tensor1_1 α β = Mat4.apply V (tensor1_1 ket0_1 ψ))
    (hβ_unit : IsQubit1 β)
    (h10 : block10 (embedAC U * embedAB V) = 0) :
    blockA_10 (U * kron2 (unitary_first_column α) 1) = 0 := by
  set X := U * kron2 (unitary_first_column α) 1 with hX_def
  have hβ_ne : β ≠ 0 := isQubit1_ne_zero hβ_unit
  -- Universal kernel: ∀ γ, Mat2.apply (blockA_10 X) γ = 0.
  have h_kernel : ∀ γ : Vec1, Mat2.apply (blockA_10 X) γ = 0 := by
    intro γ
    have hKEY := A_24_step4_KEY hαβ h10 γ
    -- Show tensor1_1 β (Mat2.apply (blockA_10 X) γ) = 0 by Vec2 funext.
    have h_tensor_zero : tensor1_1 β (Mat2.apply (blockA_10 X) γ) = 0 := by
      funext i
      have h_at := congr_fun hKEY ⟨i.val + 4, by omega⟩
      -- LHS rewrite via apply_tensor1_2_ket0_upper + block10_embedAC + kron2_apply.
      rw [Mat8.apply_tensor1_2_ket0_upper, block10_embedAC,
          show (I₂ : Mat2) = 1 from rfl, kron2_apply_tensor1_1,
          Mat2.apply_one] at h_at
      -- h_at : tensor1_1 β (Mat2.apply (blockA_10 X) γ) i = tensor1_2 ket0_1 _ ⟨i+4, _⟩.
      -- Show RHS = 0: tensor1_2 ket0_1 v at upper-half index has ket0_1[1]=0 factor.
      rw [h_at]
      change tensor1_2 ket0_1 _ ⟨i.val + 4, by omega⟩ = (0 : Vec2) i
      unfold tensor1_2
      have h_div : (i.val + 4) / 4 = 1 := by omega
      rw [show (⟨(i.val + 4) / 4, by omega⟩ : Fin 2) = ⟨1, by omega⟩ from Fin.ext h_div]
      simp [ket0_1]
    rw [tensor1_1_eq_zero_iff] at h_tensor_zero
    exact h_tensor_zero.resolve_left hβ_ne
  -- Now conclude blockA_10 X = 0 by reading columns: γ = ket0_1, γ = ket1_1.
  ext c_out c_in
  fin_cases c_in
  · -- c_in = 0: column 0.
    have hh := congr_fun (h_kernel ket0_1) c_out
    simpa [Mat2.apply, ket0_1, blockA_10, Fin.sum_univ_two] using hh
  · -- c_in = 1: column 1.
    have hh := congr_fun (h_kernel ket1_1) c_out
    simpa [Mat2.apply, ket1_1, blockA_10, Fin.sum_univ_two] using hh

/-- **A.24 Step 4 → A.17 bridge**: when `blockA_10 X = 0`, applying X to
    `tensor1_1 ket0_1 γ` keeps the result in the `tensor1_1 ket0_1 (...)`
    form (with the `...` being `Mat2.apply (blockA_00 X) γ`). This is the
    Mat4 analog of `Mat8.apply_block_diag_A_tensor1_2_ket0` (iter 187),
    and feeds A.17's hypothesis pattern directly. -/
private lemma Mat4.apply_block_diag_A_tensor1_1_ket0
    {X : Mat4} (h10 : blockA_10 X = 0) (γ : Vec1) :
    Mat4.apply X (tensor1_1 ket0_1 γ) =
    tensor1_1 ket0_1 (Mat2.apply (blockA_00 X) γ) := by
  funext k
  -- Extract the four entrywise zeros from h10 (rows 2, 3).
  have h20 : X 2 0 = 0 := by
    have := congr_fun (congr_fun h10 0) 0; simpa [blockA_10] using this
  have h21 : X 2 1 = 0 := by
    have := congr_fun (congr_fun h10 0) 1; simpa [blockA_10] using this
  have h30 : X 3 0 = 0 := by
    have := congr_fun (congr_fun h10 1) 0; simpa [blockA_10] using this
  have h31 : X 3 1 = 0 := by
    have := congr_fun (congr_fun h10 1) 1; simpa [blockA_10] using this
  fin_cases k <;>
    simp [Mat4.apply, Mat2.apply, blockA_00, tensor1_1, ket0_1,
          Fin.sum_univ_four, Fin.sum_univ_two, Matrix.of_apply,
          h20, h21, h30, h31]

/-- **A.24 Step 5**: invoke `py24_lemma_A_17` to derive that
    `X = U · kron2 p 1` is "controlled along first qubit": `X = kron2 proj0 Q₀
    + kron2 proj1 Q₁`. Uses the iter 193/194 ingredients (blockA_10 X = 0
    via A_24_blockA_10_zero, then Mat4.apply X (tensor1_1 ket0_1 _) form
    via Mat4.apply_block_diag_A_tensor1_1_ket0) plus orthogonality of
    computational basis qubits. -/
private lemma A_24_step5_X_controlled
    {U V : Mat4} {α β ψ : Vec1}
    (hU : IsUnitary4 U)
    (hα_unit : IsQubit1 α)
    (hβ_unit : IsQubit1 β)
    (hαβ : tensor1_1 α β = Mat4.apply V (tensor1_1 ket0_1 ψ))
    (h10 : block10 (embedAC U * embedAB V) = 0) :
    ∃ Q₀ Q₁ : Mat2, IsUnitary2 Q₀ ∧ IsUnitary2 Q₁ ∧
      U * kron2 (unitary_first_column α) 1 =
        kron2 proj0 Q₀ + kron2 proj1 Q₁ := by
  set X := U * kron2 (unitary_first_column α) 1 with hX_def
  -- X is unitary.
  have hp_unit : IsUnitary2 (unitary_first_column α) :=
    unitary_first_column_isUnitary hα_unit
  have hkron_unit : IsUnitary4 (kron2 (unitary_first_column α) (1 : Mat2)) :=
    isUnitary4_kron2 hp_unit isUnitary2_one
  have hX_unit : IsUnitary4 X := isUnitary4_mul hU hkron_unit
  -- blockA_10 X = 0 (iter 193 result).
  have h_blockA10 : blockA_10 X = 0 := A_24_blockA_10_zero hαβ hβ_unit h10
  -- Mat4.apply X preserves the tensor1_1 ket0_1 (...) pattern (iter 194).
  have hX_ket0 := Mat4.apply_block_diag_A_tensor1_1_ket0 h_blockA10 ket0_1
  have hX_ket1 := Mat4.apply_block_diag_A_tensor1_1_ket0 h_blockA10 ket1_1
  -- ket0_1 ⊥ ket1_1 (computational basis).
  have h_orth : innerVec1 ket0_1 ket1_1 = (0 : ℂ) := by
    unfold innerVec1; rw [Fin.sum_univ_two]; simp [ket0_1, ket1_1]
  -- Apply A.17: X is controlled.
  exact py24_lemma_A_17 hX_unit IsQubit1_ket0 IsQubit1_ket1 h_orth hX_ket0 hX_ket1

/-! ## A.24 Step 6 helpers: block_kk of embedAC of controlled form -/

set_option maxHeartbeats 800000 in
-- ext + fin_cases × 4 × 4 + simp expanding block00 / embedAC / kron2 / proj definitions.
/-- block00 of `embedAC (kron2 proj0 Q₀ + kron2 proj1 Q₁)` = `kron2 1 Q₀`. -/
private lemma block00_embedAC_controlled (Q₀ Q₁ : Mat2) :
    block00 (embedAC (kron2 proj0 Q₀ + kron2 proj1 Q₁)) = kron2 1 Q₀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block00, embedAC, kron2, proj0, proj1,
          Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]

set_option maxHeartbeats 800000 in
-- ext + fin_cases × 4 × 4 + simp expanding block11 / embedAC / kron2 / proj definitions.
/-- block11 of `embedAC (kron2 proj0 Q₀ + kron2 proj1 Q₁)` = `kron2 1 Q₁`. -/
private lemma block11_embedAC_controlled (Q₀ Q₁ : Mat2) :
    block11 (embedAC (kron2 proj0 Q₀ + kron2 proj1 Q₁)) = kron2 1 Q₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block11, embedAC, kron2, proj0, proj1,
          Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]

set_option maxHeartbeats 800000 in
-- ext + fin_cases × 4 × 4 + simp expanding block01 / embedAC / kron2 / proj definitions.
/-- block01 of `embedAC (kron2 proj0 Q₀ + kron2 proj1 Q₁)` = `0`. -/
private lemma block01_embedAC_controlled (Q₀ Q₁ : Mat2) :
    block01 (embedAC (kron2 proj0 Q₀ + kron2 proj1 Q₁)) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block01, embedAC, kron2, proj0, proj1,
          Matrix.add_apply, Matrix.of_apply]

set_option maxHeartbeats 800000 in
-- ext + fin_cases × 4 × 4 + simp expanding block10 / embedAC / kron2 / proj definitions.
/-- block10 of `embedAC (kron2 proj0 Q₀ + kron2 proj1 Q₁)` = `0`. -/
private lemma block10_embedAC_controlled (Q₀ Q₁ : Mat2) :
    block10 (embedAC (kron2 proj0 Q₀ + kron2 proj1 Q₁)) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block10, embedAC, kron2, proj0, proj1,
          Matrix.add_apply, Matrix.of_apply]

/-- **A.24 substitution identity**: with `p := unitary_first_column α` (so
    `p · p† = 1`), inserting `kron2 p 1 · kron2 p† 1 = 1` into the M product
    factors as `embedAC (U · kron2 p 1) · embedAB (kron2 p† 1 · V)`. Used
    to convert M into the (X-controlled) · (Y-block-diag) form for the final
    block_kk extraction in A.24. -/
private lemma A_24_M_eq_substituted
    (U V : Mat4) {α : Vec1} (hα_unit : IsQubit1 α) :
    embedAC U * embedAB V =
    embedAC (U * kron2 (unitary_first_column α) 1) *
    embedAB (kron2 (unitary_first_column α).conjTranspose 1 * V) := by
  -- p · p† = 1 from IsUnitary2 (p†) which says (p†)† · p† = 1, i.e., p · p† = 1.
  have h_pp_dag : (unitary_first_column α) *
                  (unitary_first_column α).conjTranspose = 1 := by
    have h_dag_unit := isUnitary2_conjTranspose
      (unitary_first_column_isUnitary hα_unit)
    unfold IsUnitary2 at h_dag_unit
    rw [Matrix.conjTranspose_conjTranspose] at h_dag_unit
    exact h_dag_unit
  set p := unitary_first_column α with hp_def
  -- Calc proof: simplify RHS to LHS.
  symm
  calc embedAC (U * kron2 p 1) * embedAB (kron2 p.conjTranspose 1 * V)
      = (embedAC U * embedAC (kron2 p 1)) *
        (embedAB (kron2 p.conjTranspose 1) * embedAB V) := by
        rw [embedAC_mul, embedAB_mul]
    _ = embedAC U *
        ((embedAC (kron2 p 1) * embedAB (kron2 p.conjTranspose 1)) *
          embedAB V) := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc]
    _ = embedAC U *
        ((embedAB (kron2 p 1) * embedAB (kron2 p.conjTranspose 1)) *
          embedAB V) := by
        rw [← embedAB_kron2_one_eq_embedAC_kron2_one]
    _ = embedAC U *
        (embedAB (kron2 p 1 * kron2 p.conjTranspose 1) * embedAB V) := by
        rw [embedAB_mul]
    _ = embedAC U * (embedAB (1 : Mat4) * embedAB V) := by
        rw [kron2_mul, h_pp_dag, mul_one, kron2_one_one_eq_one]
    _ = embedAC U * embedAB V := by
        rw [embedAB_one, Matrix.one_mul]

/-! ## A.24 Step 6 part 2 prerequisites: unitary ≠ 0, kron2 cancellation -/

/-- A 2×2 unitary is nonzero (as 0·0 = 0 ≠ 1). -/
private lemma isUnitary2_ne_zero {Q : Mat2} (hQ : IsUnitary2 Q) : Q ≠ 0 := by
  intro h_zero
  unfold IsUnitary2 at hQ
  rw [h_zero, Matrix.conjTranspose_zero, Matrix.zero_mul] at hQ
  -- hQ : (0 : Mat2) = 1
  have h_entry := congr_fun (congr_fun hQ 0) 0
  simp at h_entry

/-- If `kron2 A B = 0` and `B ≠ 0`, then `A = 0`. -/
private lemma mat2_eq_zero_of_kron2_eq_zero_right
    {A B : Mat2} (h_zero : kron2 A B = 0) (hB_ne : B ≠ 0) : A = 0 := by
  obtain ⟨k, l, hB_kl⟩ : ∃ (k l : Fin 2), B k l ≠ 0 := by
    by_contra h_all
    push_neg at h_all
    exact hB_ne (by ext k l; exact h_all k l)
  ext i j
  have h_at : kron2 A B ⟨2 * i.val + k.val, by omega⟩
                       ⟨2 * j.val + l.val, by omega⟩ = 0 := by
    rw [h_zero]; rfl
  unfold kron2 at h_at
  rw [Matrix.of_apply] at h_at
  have h_di : (2 * i.val + k.val) / 2 = i.val := by omega
  have h_mi : (2 * i.val + k.val) % 2 = k.val := by omega
  have h_dj : (2 * j.val + l.val) / 2 = j.val := by omega
  have h_mj : (2 * j.val + l.val) % 2 = l.val := by omega
  rw [show (⟨(2 * i.val + k.val) / 2, by omega⟩ : Fin 2) = i from Fin.ext h_di,
      show (⟨(2 * j.val + l.val) / 2, by omega⟩ : Fin 2) = j from Fin.ext h_dj,
      show (⟨(2 * i.val + k.val) % 2, by omega⟩ : Fin 2) = k from Fin.ext h_mi,
      show (⟨(2 * j.val + l.val) % 2, by omega⟩ : Fin 2) = l from Fin.ext h_mj] at h_at
  exact (mul_eq_zero.mp h_at).resolve_right hB_kl

/-! ## A.24 Step 6 part 2: block_kk M factorization helpers -/

/-- block00 of `embedAC (controlled X) · embedAB Y` = `kron2 (blockA_00 Y) Q₀`. -/
private lemma block00_embedAC_controlled_mul_embedAB
    (Y : Mat4) (Q₀ Q₁ : Mat2) :
    block00 (embedAC (kron2 proj0 Q₀ + kron2 proj1 Q₁) * embedAB Y) =
    kron2 (blockA_00 Y) Q₀ := by
  rw [block00_mul, block01_embedAC_controlled, Matrix.zero_mul, add_zero,
      block00_embedAC_controlled, block00_embedAB,
      show (I₂ : Mat2) = 1 from rfl, kron2_mul, one_mul, mul_one]

/-- block01 of `embedAC (controlled X) · embedAB Y` = `kron2 (blockA_01 Y) Q₀`. -/
private lemma block01_embedAC_controlled_mul_embedAB
    (Y : Mat4) (Q₀ Q₁ : Mat2) :
    block01 (embedAC (kron2 proj0 Q₀ + kron2 proj1 Q₁) * embedAB Y) =
    kron2 (blockA_01 Y) Q₀ := by
  rw [block01_mul, block01_embedAC_controlled, Matrix.zero_mul, add_zero,
      block00_embedAC_controlled, block01_embedAB,
      show (I₂ : Mat2) = 1 from rfl, kron2_mul, one_mul, mul_one]

/-- block10 of `embedAC (controlled X) · embedAB Y` = `kron2 (blockA_10 Y) Q₁`. -/
private lemma block10_embedAC_controlled_mul_embedAB
    (Y : Mat4) (Q₀ Q₁ : Mat2) :
    block10 (embedAC (kron2 proj0 Q₀ + kron2 proj1 Q₁) * embedAB Y) =
    kron2 (blockA_10 Y) Q₁ := by
  rw [block10_mul, block10_embedAC_controlled, Matrix.zero_mul, zero_add,
      block11_embedAC_controlled, block10_embedAB,
      show (I₂ : Mat2) = 1 from rfl, kron2_mul, one_mul, mul_one]

/-- block11 of `embedAC (controlled X) · embedAB Y` = `kron2 (blockA_11 Y) Q₁`. -/
private lemma block11_embedAC_controlled_mul_embedAB
    (Y : Mat4) (Q₀ Q₁ : Mat2) :
    block11 (embedAC (kron2 proj0 Q₀ + kron2 proj1 Q₁) * embedAB Y) =
    kron2 (blockA_11 Y) Q₁ := by
  rw [block11_mul, block10_embedAC_controlled, Matrix.zero_mul, zero_add,
      block11_embedAC_controlled, block11_embedAB,
      show (I₂ : Mat2) = 1 from rfl, kron2_mul, one_mul, mul_one]

/-- **A.24 normalization**: from a tensor `tensor1_1 a_V b_V` of unit norm
    with both factors nonzero, extract unit qubits α, β with the same tensor.
    Used in A.24 to feed iter 195's Step 5 lemma which needs unit α, β. -/
private lemma A_24_normalize
    {a_V b_V : Vec1}
    (h_aV_ne : a_V ≠ 0)
    (h_norm : normSqVec1 a_V * normSqVec1 b_V = 1) :
    ∃ α β : Vec1, IsQubit1 α ∧ IsQubit1 β ∧
      tensor1_1 α β = tensor1_1 a_V b_V := by
  have hnsq_a_pos : 0 < normSqVec1 a_V := normSqVec1_pos_of_ne_zero a_V h_aV_ne
  have hsqrt_pos : 0 < Real.sqrt (normSqVec1 a_V) := Real.sqrt_pos.mpr hnsq_a_pos
  refine ⟨unit_normalize_vec1 a_V,
          ((Real.sqrt (normSqVec1 a_V) : ℝ) : ℂ) • b_V,
          isQubit1_unit_normalize_vec1 a_V h_aV_ne, ?_, ?_⟩
  · -- IsQubit1 (sqrt(‖a_V‖²) • b_V): ‖β‖² = ‖a_V‖² · ‖b_V‖² = 1.
    unfold IsQubit1
    rw [normSqVec1_smul, Complex.normSq_ofReal,
        Real.mul_self_sqrt hnsq_a_pos.le]
    exact h_norm
  · -- tensor1_1 (unit_normalize_vec1 a_V) (sqrt • b_V) = tensor1_1 a_V b_V.
    -- unit_normalize_vec1 a_V = (sqrt⁻¹) • a_V; tensor1_1 (s•a) (t•b) = (s*t) • (a⊗b).
    -- (sqrt⁻¹ * sqrt) = 1, so result is (1) • (a⊗b) = a⊗b.
    unfold unit_normalize_vec1
    rw [tensor1_1_smul_smul]
    have h_inv : (((Real.sqrt (normSqVec1 a_V))⁻¹ : ℝ) : ℂ) *
                 (((Real.sqrt (normSqVec1 a_V) : ℝ)) : ℂ) = 1 := by
      have h_real : (Real.sqrt (normSqVec1 a_V))⁻¹ * Real.sqrt (normSqVec1 a_V) = 1 :=
        inv_mul_cancel₀ hsqrt_pos.ne'
      exact_mod_cast h_real
    rw [h_inv, one_smul]

/-! ## PY24 Lemma A.24 (HP A.14) — UAC VAB tensor decomposition

For 2-qubit unitaries U, V, W₀, W₁, if
  U_AC · V_AB = |0⟩⟨0| ⊗ W₀ + |1⟩⟨1| ⊗ W₁
then
  U_AC · V_AB = |0⟩⟨0| ⊗ P₀ ⊗ Q₀ + |1⟩⟨1| ⊗ P₁ ⊗ Q₁
for 1-qubit unitaries P₀, Q₀, P₁, Q₁.

This is exactly our existing `paper_lemma_A14` (in HP/SetChar.lean), restated
using block_kk infrastructure. -/
theorem py24_lemma_A_24 (U V : Mat4) (hU : IsUnitary4 U) (hV : IsUnitary4 V)
    (h01 : block01 (embedAC U * embedAB V) = 0)
    (h10 : block10 (embedAC U * embedAB V) = 0) :
    ∃ P₀ Q₀ P₁ Q₁ : Mat2, IsUnitary2 P₀ ∧ IsUnitary2 Q₀ ∧
      IsUnitary2 P₁ ∧ IsUnitary2 Q₁ ∧
      block00 (embedAC U * embedAB V) = kron2 P₀ Q₀ ∧
      block11 (embedAC U * embedAB V) = kron2 P₁ Q₁ := by
  -- Step 1: A.21 on V → ψ_V, a_V, b_V with V·(ket0⊗ψ_V) = a_V⊗b_V.
  obtain ⟨ψ_V, hψ_V_unit, a_V, b_V, hab_V⟩ := py24_lemma_A_21 V hV
  -- Step 2: ‖a_V‖² · ‖b_V‖² = 1 (V unitary preserves norm).
  have h_Vapply_qubit : IsQubit2 (Mat4.apply V (tensor1_1 ket0_1 ψ_V)) :=
    IsQubit2_apply_unitary hV (IsQubit2_tensor1_1 IsQubit1_ket0 hψ_V_unit)
  have h_aV_bV_norm : normSqVec1 a_V * normSqVec1 b_V = 1 := by
    have h := h_Vapply_qubit
    rw [hab_V] at h
    unfold IsQubit2 at h
    rw [normSqVec2_tensor1_1] at h
    exact h
  -- Step 3: a_V ≠ 0 (else norm product = 0 ≠ 1).
  have h_aV_ne : a_V ≠ 0 := by
    intro h_zero
    rw [h_zero] at h_aV_bV_norm
    simp [normSqVec1] at h_aV_bV_norm
  -- Step 4: Normalize via A_24_normalize → unit α, β with α⊗β = a_V⊗b_V.
  obtain ⟨α, β, hα_unit, hβ_unit, h_αβ_eq⟩ :=
    A_24_normalize h_aV_ne h_aV_bV_norm
  have h_αβ_apply : tensor1_1 α β = Mat4.apply V (tensor1_1 ket0_1 ψ_V) :=
    h_αβ_eq.trans hab_V.symm
  -- Step 5: A_24_step5_X_controlled → ∃ Q₀, Q₁ unitary with X = U·kron2 p 1
  -- = kron2 proj0 Q₀ + kron2 proj1 Q₁ (controlled along first qubit).
  obtain ⟨Q₀, Q₁, hQ₀_unit, hQ₁_unit, hX_eq⟩ :=
    A_24_step5_X_controlled hU hα_unit hβ_unit h_αβ_apply h10
  -- Step 6: Substitute via A_24_M_eq_substituted to get
  --   M = embedAC (kron2 proj0 Q₀ + kron2 proj1 Q₁) · embedAB Y
  -- where Y := kron2 p† 1 · V.
  have h_M_sub := A_24_M_eq_substituted U V hα_unit
  rw [hX_eq] at h_M_sub
  set Y := kron2 (unitary_first_column α).conjTranspose 1 * V with hY_def
  -- Step 7: blockA_01 Y = 0 (from h01 + Q₀ unitary).
  have h_kron_01 : kron2 (blockA_01 Y) Q₀ = 0 := by
    rw [← block01_embedAC_controlled_mul_embedAB Y Q₀ Q₁, ← h_M_sub]
    exact h01
  have h_blockA_01_Y : blockA_01 Y = 0 :=
    mat2_eq_zero_of_kron2_eq_zero_right h_kron_01 (isUnitary2_ne_zero hQ₀_unit)
  -- Step 8: blockA_10 Y = 0 (from h10 + Q₁ unitary).
  have h_kron_10 : kron2 (blockA_10 Y) Q₁ = 0 := by
    rw [← block10_embedAC_controlled_mul_embedAB Y Q₀ Q₁, ← h_M_sub]
    exact h10
  have h_blockA_10_Y : blockA_10 Y = 0 :=
    mat2_eq_zero_of_kron2_eq_zero_right h_kron_10 (isUnitary2_ne_zero hQ₁_unit)
  -- Step 9: Y is unitary (product of unitaries).
  have hp_unit : IsUnitary2 (unitary_first_column α) :=
    unitary_first_column_isUnitary hα_unit
  have hp_dag_unit : IsUnitary2 (unitary_first_column α).conjTranspose :=
    isUnitary2_conjTranspose hp_unit
  have hY_unit : IsUnitary4 Y :=
    isUnitary4_mul (isUnitary4_kron2 hp_dag_unit isUnitary2_one) hV
  -- Step 10: blockA_00 Y, blockA_11 Y unitary (existing helpers).
  have hP₀_unit : IsUnitary2 (blockA_00 Y) :=
    blockA_00_unitary_of_blockA_10_zero hY_unit h_blockA_10_Y
  have hP₁_unit : IsUnitary2 (blockA_11 Y) :=
    blockA_11_unitary_of_blockA_10_zero hY_unit h_blockA_10_Y
  -- Step 11: assemble. P₀ := blockA_00 Y, Q₀, P₁ := blockA_11 Y, Q₁.
  refine ⟨blockA_00 Y, Q₀, blockA_11 Y, Q₁, hP₀_unit, hQ₀_unit,
          hP₁_unit, hQ₁_unit, ?_, ?_⟩
  · rw [h_M_sub]; exact block00_embedAC_controlled_mul_embedAB Y Q₀ Q₁
  · rw [h_M_sub]; exact block11_embedAC_controlled_mul_embedAB Y Q₀ Q₁

/-! ## A.30 helpers: extract 2×2 unitary T from second-factor-fixed hypothesis

Note: `matrixOfColumns` and its 4 helpers (`apply_ket0`, `apply_ket1`,
`apply`, `unitary`) were moved to `ApproxToffoli/PY24/Vectors.lean` in
iter 185 to make them available earlier (specifically inside
`py24_lemma_A_24` proof). They remain accessible here via the import. -/

/-- **A.30 main helper**: from V's second-factor-fixed hypothesis, extract a 2×2
    unitary T such that `V·(x⊗|0⟩) = (T·x)⊗ψ` for all x. -/
lemma exists_T_second_factor_fixed
    {V : Mat4} (hV : IsUnitary4 V) {ψ : Vec1} (hψ : IsQubit1 ψ)
    (h : ∀ x : Vec1, IsQubit1 x → ∃ z : Vec1,
      Mat4.apply V (tensor1_1 x ket0_1) = tensor1_1 z ψ) :
    ∃ T : Mat2, IsUnitary2 T ∧
      ∀ x : Vec1, Mat4.apply V (tensor1_1 x ket0_1) = tensor1_1 (Mat2.apply T x) ψ := by
  obtain ⟨z₀, h_z0⟩ := h ket0_1 IsQubit1_ket0
  obtain ⟨z₁, h_z1⟩ := h ket1_1 IsQubit1_ket1
  -- Orthonormality of z₀, z₁ from V's unitarity.
  have hψ_nsq : normSqVec1 ψ = 1 := hψ
  have h_z0_nsq : normSqVec1 z₀ = 1 := by
    have : IsQubit2 (tensor1_1 z₀ ψ) := by
      rw [← h_z0]; exact IsQubit2_apply_unitary hV IsQubit2_ket00
    unfold IsQubit2 at this
    rw [normSqVec2_tensor1_1, hψ_nsq, mul_one] at this
    exact this
  have h_z1_nsq : normSqVec1 z₁ = 1 := by
    have : IsQubit2 (tensor1_1 z₁ ψ) := by
      rw [← h_z1]; exact IsQubit2_apply_unitary hV IsQubit2_ket10
    unfold IsQubit2 at this
    rw [normSqVec2_tensor1_1, hψ_nsq, mul_one] at this
    exact this
  -- Orthogonality ⟨z₀, z₁⟩ = 0 from inner product preservation.
  have h_z01 : innerVec1 z₀ z₁ = 0 := by
    have h_inner : innerVec2 (Mat4.apply V (tensor1_1 ket0_1 ket0_1))
                            (Mat4.apply V (tensor1_1 ket1_1 ket0_1))
                  = innerVec2 (tensor1_1 ket0_1 ket0_1) (tensor1_1 ket1_1 ket0_1) :=
      innerVec2_apply_apply_unitary hV _ _
    rw [h_z0, h_z1, innerVec2_tensor1_1, innerVec2_tensor1_1] at h_inner
    -- h_inner : innerVec1 z₀ z₁ * innerVec1 ψ ψ = innerVec1 ket0_1 ket1_1 * innerVec1 ket0_1 ket0_1
    have h_psi_self : innerVec1 ψ ψ = (1 : ℂ) := by
      rw [innerVec1_self]; exact_mod_cast hψ
    have h_ket0_ket1 : innerVec1 ket0_1 ket1_1 = 0 := by
      unfold innerVec1
      rw [Fin.sum_univ_two]
      simp [ket0_1, ket1_1]
    rw [h_psi_self, h_ket0_ket1, zero_mul, mul_one] at h_inner
    exact h_inner
  refine ⟨matrixOfColumns z₀ z₁, matrixOfColumns_unitary h_z0_nsq h_z1_nsq h_z01, ?_⟩
  -- For all x, V·(x⊗|0⟩) = (T·x)⊗ψ.
  intro x
  -- V·(x⊗|0⟩) = V·((x 0)·ket0 + (x 1)·ket1)⊗|0⟩ = (x 0)·z₀⊗ψ + (x 1)·z₁⊗ψ
  have hx_decomp : x = x 0 • ket0_1 + x 1 • ket1_1 := vec1_basis_decomp x
  rw [hx_decomp]
  rw [tensor1_1_add_left, tensor1_1_smul_left, tensor1_1_smul_left,
      Mat4.apply_add, Mat4.apply_smul, Mat4.apply_smul, h_z0, h_z1]
  rw [matrixOfColumns_apply, ← tensor1_1_smul_left, ← tensor1_1_smul_left,
      ← tensor1_1_add_left]
  congr 1
  -- Need: x 0 • z₀ + x 1 • z₁ = (x 0 • ket0_1 + x 1 • ket1_1) 0 • z₀ + (...) 1 • z₁.
  -- (x 0 • ket0_1 + x 1 • ket1_1) 0 = x 0 * 1 + x 1 * 0 = x 0 (similar for 1).
  simp [ket0_1, ket1_1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- **A.30 W₂ candidate**: given T, R_ψ unitaries and V₂ with the second-factor-
    fixed structure, the matrix `W₂ := (kron2 T† R_ψ†) · V₂` satisfies
    `W₂(x⊗|0⟩) = x⊗|0⟩` for all x. -/
lemma W2_apply_x_ket0
    {T R : Mat2} {ψ : Vec1} {V₂ : Mat4}
    (hT : IsUnitary2 T) (hR : IsUnitary2 R) (hRψ : Mat2.apply R ket0_1 = ψ)
    (h : ∀ x : Vec1, Mat4.apply V₂ (tensor1_1 x ket0_1)
                    = tensor1_1 (Mat2.apply T x) ψ) :
    ∀ x : Vec1,
      Mat4.apply (kron2 T.conjTranspose R.conjTranspose * V₂) (tensor1_1 x ket0_1)
        = tensor1_1 x ket0_1 := by
  intro x
  rw [Mat4.apply_mul, h x, kron2_apply_tensor1_1]
  congr 1
  · -- T†·(T·x) = x.
    rw [← Mat2.apply_mul, hT, Mat2.apply_one]
  · -- R†·ψ = R†·R·ket0 = ket0.
    rw [← hRψ, ← Mat2.apply_mul, hR, Mat2.apply_one]

/-- **A.30 step 2**: V₂(y⊗|0⟩) and V₂(x⊗|1⟩) are orthogonal for any y, x
    (consequence of V₂ unitary preserving inner products + ket0/ket1 orthogonal). -/
lemma V2_image_ket0_orthogonal_ket1
    {V₂ : Mat4} (hV₂ : IsUnitary4 V₂) (x y : Vec1) :
    innerVec2 (Mat4.apply V₂ (tensor1_1 y ket0_1))
              (Mat4.apply V₂ (tensor1_1 x ket1_1)) = 0 := by
  rw [innerVec2_apply_apply_unitary hV₂, innerVec2_tensor1_1]
  have h_ket01 : innerVec1 ket0_1 ket1_1 = (0 : ℂ) := by
    unfold innerVec1; rw [Fin.sum_univ_two]; simp [ket0_1, ket1_1]
  rw [h_ket01, mul_zero]

/-- **A.30 step 3**: combining T-extraction with orthogonality gives
    `⟨(T·y)⊗ψ, V₂(x⊗|1⟩)⟩ = 0` for all y. -/
lemma V2_ket1_orthogonal_to_T_y_psi
    {V₂ : Mat4} (hV₂ : IsUnitary4 V₂) {T : Mat2} {ψ : Vec1}
    (hT : ∀ y : Vec1, Mat4.apply V₂ (tensor1_1 y ket0_1)
                    = tensor1_1 (Mat2.apply T y) ψ) :
    ∀ x y : Vec1, innerVec2 (tensor1_1 (Mat2.apply T y) ψ)
                            (Mat4.apply V₂ (tensor1_1 x ket1_1)) = 0 := by
  intro x y
  rw [← hT y]
  exact V2_image_ket0_orthogonal_ket1 hV₂ x y

/-- **innerVec2 adjoint identity**: ⟨a, V·b⟩ = ⟨V†·a, b⟩ for V unitary. -/
lemma innerVec2_apply_left {V : Mat4} (hV : IsUnitary4 V) (a b : Vec2) :
    innerVec2 a (Mat4.apply V b) = innerVec2 (Mat4.apply V.conjTranspose a) b := by
  have h_VV_one : V * V.conjTranspose = 1 := mul_eq_one_comm.mp hV
  have key := innerVec2_apply_apply_unitary hV (Mat4.apply V.conjTranspose a) b
  rw [← Mat4.apply_mul, h_VV_one, Mat4.apply_one] at key
  exact key

/-- Vec2 entry 0 (the |00⟩ component) equals innerVec2 with ket0⊗ket0. -/
lemma vec2_entry_0_eq_inner_ket00 (v : Vec2) :
    v 0 = innerVec2 (tensor1_1 ket0_1 ket0_1) v := by
  unfold innerVec2 tensor1_1 ket0_1
  rw [Fin.sum_univ_four]
  simp

/-- Vec2 entry 2 (the |10⟩ component) equals innerVec2 with ket1⊗ket0. -/
lemma vec2_entry_2_eq_inner_ket10 (v : Vec2) :
    v 2 = innerVec2 (tensor1_1 ket1_1 ket0_1) v := by
  unfold innerVec2 tensor1_1 ket1_1 ket0_1
  rw [Fin.sum_univ_four]
  simp

/-- **A.30 step 4**: W₂'s "ket0-second" entries vanish. -/
lemma W2_apply_x_ket1_entries_zero
    {V₂ : Mat4} (hV₂ : IsUnitary4 V₂) {T R : Mat2}
    (hT : IsUnitary2 T) (hR : IsUnitary2 R) {ψ : Vec1}
    (hRψ : Mat2.apply R ket0_1 = ψ)
    (hV : ∀ y : Vec1, Mat4.apply V₂ (tensor1_1 y ket0_1)
                    = tensor1_1 (Mat2.apply T y) ψ) (x : Vec1) :
    (Mat4.apply (kron2 T.conjTranspose R.conjTranspose * V₂)
        (tensor1_1 x ket1_1)) 0 = 0 ∧
    (Mat4.apply (kron2 T.conjTranspose R.conjTranspose * V₂)
        (tensor1_1 x ket1_1)) 2 = 0 := by
  have hKronT_unit : IsUnitary4 (kron2 T.conjTranspose R.conjTranspose) :=
    isUnitary4_kron2 (isUnitary2_conjTranspose hT) (isUnitary2_conjTranspose hR)
  have hKronT_dagger :
      (kron2 T.conjTranspose R.conjTranspose).conjTranspose = kron2 T R := by
    rw [kron2_conjTranspose, Matrix.conjTranspose_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
  refine ⟨?_, ?_⟩
  · -- Entry 0 = innerVec2 (ket0⊗ket0) W₂(x⊗ket1) = ⟨(T·ket0)⊗ψ, V₂(x⊗ket1)⟩ = 0.
    have h_entry := vec2_entry_0_eq_inner_ket00
      (Mat4.apply (kron2 T.conjTranspose R.conjTranspose * V₂) (tensor1_1 x ket1_1))
    rw [h_entry, Mat4.apply_mul,
        innerVec2_apply_left hKronT_unit, hKronT_dagger,
        kron2_apply_tensor1_1, hRψ]
    exact V2_ket1_orthogonal_to_T_y_psi hV₂ hV x ket0_1
  · -- Entry 2 = innerVec2 (ket1⊗ket0) W₂(x⊗ket1) = ⟨(T·ket1)⊗ψ, V₂(x⊗ket1)⟩ = 0.
    have h_entry := vec2_entry_2_eq_inner_ket10
      (Mat4.apply (kron2 T.conjTranspose R.conjTranspose * V₂) (tensor1_1 x ket1_1))
    rw [h_entry, Mat4.apply_mul,
        innerVec2_apply_left hKronT_unit, hKronT_dagger,
        kron2_apply_tensor1_1, hRψ]
    exact V2_ket1_orthogonal_to_T_y_psi hV₂ hV x ket1_1

/-- **A.30 step 5**: W₂(x⊗|1⟩) factors as `y⊗|1⟩` where y is the "|1⟩-second" entries. -/
lemma W2_apply_x_ket1_factors
    {V₂ : Mat4} (hV₂ : IsUnitary4 V₂) {T R : Mat2}
    (hT : IsUnitary2 T) (hR : IsUnitary2 R) {ψ : Vec1}
    (hRψ : Mat2.apply R ket0_1 = ψ)
    (hV : ∀ y : Vec1, Mat4.apply V₂ (tensor1_1 y ket0_1)
                    = tensor1_1 (Mat2.apply T y) ψ) (x : Vec1) :
    Mat4.apply (kron2 T.conjTranspose R.conjTranspose * V₂) (tensor1_1 x ket1_1) =
      tensor1_1
        ![(Mat4.apply (kron2 T.conjTranspose R.conjTranspose * V₂)
            (tensor1_1 x ket1_1)) 1,
          (Mat4.apply (kron2 T.conjTranspose R.conjTranspose * V₂)
            (tensor1_1 x ket1_1)) 3]
        ket1_1 := by
  obtain ⟨h0, h2⟩ := W2_apply_x_ket1_entries_zero hV₂ hT hR hRψ hV x
  funext k
  fin_cases k <;>
    simp [tensor1_1, ket1_1, h0, h2,
          Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **Mat4 entry as Mat4.apply on basis vector**: M i j = (M · e_j)_i. -/
lemma mat4_entry_eq_apply_basis (M : Mat4) (i j : Fin 4) :
    M i j = Mat4.apply M (fun k => if k = j then 1 else 0) i := by
  unfold Mat4.apply
  rw [Fin.sum_univ_four]
  fin_cases j <;> fin_cases i <;> simp

/-- The basis vector `e_0` equals `tensor1_1 ket0_1 ket0_1`. -/
lemma e_0_eq_tensor_ket0_ket0 :
    (fun k : Fin 4 => if k = 0 then (1 : ℂ) else 0) = tensor1_1 ket0_1 ket0_1 := by
  funext k; fin_cases k <;> simp [tensor1_1, ket0_1]

/-- The basis vector `e_1` equals `tensor1_1 ket0_1 ket1_1`. -/
lemma e_1_eq_tensor_ket0_ket1 :
    (fun k : Fin 4 => if k = 1 then (1 : ℂ) else 0) = tensor1_1 ket0_1 ket1_1 := by
  funext k; fin_cases k <;> simp [tensor1_1, ket0_1, ket1_1]

/-- The basis vector `e_2` equals `tensor1_1 ket1_1 ket0_1`. -/
lemma e_2_eq_tensor_ket1_ket0 :
    (fun k : Fin 4 => if k = 2 then (1 : ℂ) else 0) = tensor1_1 ket1_1 ket0_1 := by
  funext k; fin_cases k <;> simp [tensor1_1, ket0_1, ket1_1]

/-- The basis vector `e_3` equals `tensor1_1 ket1_1 ket1_1`. -/
lemma e_3_eq_tensor_ket1_ket1 :
    (fun k : Fin 4 => if k = 3 then (1 : ℂ) else 0) = tensor1_1 ket1_1 ket1_1 := by
  funext k; fin_cases k <;> simp [tensor1_1, ket1_1]

/-- Action of `kron2 1 proj0 + kron2 P₂ proj1` on `tensor1_1 x ket0_1`. -/
lemma kron_block_diag_second_apply_x_ket0 (P₂ : Mat2) (x : Vec1) :
    Mat4.apply (kron2 1 proj0 + kron2 P₂ proj1) (tensor1_1 x ket0_1) = tensor1_1 x ket0_1 := by
  funext k
  fin_cases k <;>
    simp [Mat4.apply, kron2, proj0, proj1, tensor1_1, ket0_1,
          Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, Fin.sum_univ_four]

/-- Action of `kron2 1 proj0 + kron2 P₂ proj1` on `tensor1_1 x ket1_1`. -/
lemma kron_block_diag_second_apply_x_ket1 (P₂ : Mat2) (x : Vec1) :
    Mat4.apply (kron2 1 proj0 + kron2 P₂ proj1) (tensor1_1 x ket1_1) =
    tensor1_1 (Mat2.apply P₂ x) ket1_1 := by
  funext k
  fin_cases k <;>
    simp [Mat4.apply, Mat2.apply, kron2, proj0, proj1, tensor1_1, ket1_1,
          Matrix.add_apply, Matrix.of_apply, Matrix.one_apply,
          Fin.sum_univ_four, Fin.sum_univ_two]

/-- Mat4 entry as a Vec2 entry of the matrix-vector product on a tensor basis. -/
lemma mat4_entry_via_tensor (M : Mat4) (i : Fin 4) :
    M i 0 = (Mat4.apply M (tensor1_1 ket0_1 ket0_1)) i ∧
    M i 1 = (Mat4.apply M (tensor1_1 ket0_1 ket1_1)) i ∧
    M i 2 = (Mat4.apply M (tensor1_1 ket1_1 ket0_1)) i ∧
    M i 3 = (Mat4.apply M (tensor1_1 ket1_1 ket1_1)) i := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [Mat4.apply, tensor1_1, ket0_1, ket1_1, Fin.sum_univ_four]

set_option maxHeartbeats 800000 in
-- ext + fin_cases × 2 × 2 + simp on Matrix.mul_apply (4×4 entries) + linear_combination.
/-- **A.30 P₂ unitarity**: if W = kron2 1 proj0 + kron2 P₂ proj1 is unitary,
    then P₂ is unitary. -/
lemma P2_unitary_from_W_unitary {P₂ : Mat2}
    (hW : IsUnitary4 (kron2 1 proj0 + kron2 P₂ proj1)) :
    IsUnitary2 P₂ := by
  unfold IsUnitary4 IsUnitary2 at *
  -- The (2k+1, 2l+1) entry of W†W gives (P₂†P₂)_{k,l}.
  ext k l
  have h11 := congrFun (congrFun hW ⟨2 * k.val + 1, by omega⟩) ⟨2 * l.val + 1, by omega⟩
  fin_cases k <;> fin_cases l <;>
    (simp [kron2, proj0, proj1, Matrix.mul_apply,
           Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
           Fin.sum_univ_four, Fin.sum_univ_two] at h11 ⊢;
     linear_combination h11)

/-- **A.30 conjugation invariance**: B-only conjugation of W₂ preserves the
    block-diag-second form, mapping P₂ to T·P₂·T†. -/
lemma kron2_T_conj_block_diag_second (T P₂ : Mat2) :
    kron2 T 1 * (kron2 1 proj0 + kron2 P₂ proj1) * kron2 T.conjTranspose 1 =
    kron2 (T * 1 * T.conjTranspose) proj0 + kron2 (T * P₂ * T.conjTranspose) proj1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kron2, proj0, proj1, Matrix.add_apply, Matrix.mul_apply,
          Matrix.of_apply, Matrix.one_apply, Matrix.conjTranspose_apply,
          Fin.sum_univ_two, Fin.sum_univ_four]

/-- **A.30 commutation through W₂**: B-only `singleQubitLayer I₂ T I₂` commutes
    through `embedBC W₂_old` by changing W₂'s P₂ to T·P₂·T†. -/
lemma sQL_T_through_embedBC_W2 (T P : Mat2) (hT : IsUnitary2 T) :
    singleQubitLayer I₂ T I₂ * embedBC (kron2 1 proj0 + kron2 P proj1) =
    embedBC (kron2 1 proj0 + kron2 (T * P * T.conjTranspose) proj1) *
      singleQubitLayer I₂ T I₂ := by
  rw [show (singleQubitLayer I₂ T I₂ : Mat8) = embedBC (kron2 T 1) from
      (embedBC_kron2 T 1).symm]
  rw [embedBC_mul, embedBC_mul]
  congr 1
  have hTT : T * 1 * T.conjTranspose = (1 : Mat2) := by
    rw [mul_one]; exact mul_eq_one_comm.mp hT
  have hW2_new_form :
      (kron2 (1 : Mat2) proj0 + kron2 (T * P * T.conjTranspose) proj1 : Mat4) =
      kron2 T 1 * (kron2 1 proj0 + kron2 P proj1) * kron2 T.conjTranspose 1 := by
    rw [kron2_T_conj_block_diag_second, hTT]
  rw [hW2_new_form]
  rw [mul_assoc, mul_assoc]
  rw [show kron2 T.conjTranspose (1 : Mat2) * kron2 T 1 = (1 : Mat4) from by
        rw [kron2_mul, hT, mul_one]; exact kron2_one_one_eq_one]
  rw [mul_one]

/-- **A.31 commutation through W₃**: A-only `singleQubitLayer T I₂ I₂` commutes
    through `embedAC W₃_old` by changing W₃'s P to T·P·T†. (AC analog of
    `sQL_T_through_embedBC_W2`.) -/
lemma sQL_T_through_embedAC_W (T P : Mat2) (hT : IsUnitary2 T) :
    singleQubitLayer T I₂ I₂ * embedAC (kron2 1 proj0 + kron2 P proj1) =
    embedAC (kron2 1 proj0 + kron2 (T * P * T.conjTranspose) proj1) *
      singleQubitLayer T I₂ I₂ := by
  rw [show (singleQubitLayer T I₂ I₂ : Mat8) = embedAC (kron2 T 1) from
      (embedAC_kron2 T 1).symm]
  rw [embedAC_mul, embedAC_mul]
  congr 1
  have hTT : T * 1 * T.conjTranspose = (1 : Mat2) := by
    rw [mul_one]; exact mul_eq_one_comm.mp hT
  have hW3_new_form :
      (kron2 (1 : Mat2) proj0 + kron2 (T * P * T.conjTranspose) proj1 : Mat4) =
      kron2 T 1 * (kron2 1 proj0 + kron2 P proj1) * kron2 T.conjTranspose 1 := by
    rw [kron2_T_conj_block_diag_second, hTT]
  rw [hW3_new_form]
  rw [mul_assoc, mul_assoc]
  rw [show kron2 T.conjTranspose (1 : Mat2) * kron2 T 1 = (1 : Mat4) from by
        rw [kron2_mul, hT, mul_one]; exact kron2_one_one_eq_one]
  rw [mul_one]

/-- **A.30 step 7**: W₂ has block-diag-second form. Construct P₂ and prove equality. -/
lemma exists_P2_W2_eq_block_diag_second
    {V₂ : Mat4} (hV₂ : IsUnitary4 V₂) {T R : Mat2}
    (hT : IsUnitary2 T) (hR : IsUnitary2 R) {ψ : Vec1}
    (hRψ : Mat2.apply R ket0_1 = ψ)
    (hV : ∀ y : Vec1, Mat4.apply V₂ (tensor1_1 y ket0_1)
                    = tensor1_1 (Mat2.apply T y) ψ) :
    ∃ P₂ : Mat2,
      kron2 T.conjTranspose R.conjTranspose * V₂ = kron2 1 proj0 + kron2 P₂ proj1 := by
  set W := kron2 T.conjTranspose R.conjTranspose * V₂
  refine ⟨!![W 1 1, W 1 3; W 3 1, W 3 3], ?_⟩
  set P₂ : Mat2 := !![W 1 1, W 1 3; W 3 1, W 3 3] with hP₂_def
  ext i j
  have hW0 := W2_apply_x_ket0 hT hR hRψ hV ket0_1
  have hW1 := W2_apply_x_ket1_factors hV₂ hT hR hRψ hV ket0_1
  have hW2 := W2_apply_x_ket0 hT hR hRψ hV ket1_1
  have hW3 := W2_apply_x_ket1_factors hV₂ hT hR hRψ hV ket1_1
  have hT0 := kron_block_diag_second_apply_x_ket0 P₂ ket0_1
  have hT1 := kron_block_diag_second_apply_x_ket1 P₂ ket0_1
  have hT2 := kron_block_diag_second_apply_x_ket0 P₂ ket1_1
  have hT3 := kron_block_diag_second_apply_x_ket1 P₂ ket1_1
  have hWentry := mat4_entry_via_tensor W i
  have hTentry := mat4_entry_via_tensor (kron2 1 proj0 + kron2 P₂ proj1) i
  fin_cases j <;> simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one]
  · -- j = 0
    change W i 0 = (kron2 1 proj0 + kron2 P₂ proj1) i 0
    rw [hWentry.1, hTentry.1, hW0, hT0]
  · -- j = 1
    change W i 1 = (kron2 1 proj0 + kron2 P₂ proj1) i 1
    rw [hWentry.2.1, hTentry.2.1, hW1, hT1]
    congr 1
    funext k
    fin_cases k <;>
      (simp [Mat2.apply, Mat4.apply, ket1_1, tensor1_1, hP₂_def,
            Fin.sum_univ_four,
            Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.of_apply]; rfl)
  · -- j = 2
    change W i 2 = (kron2 1 proj0 + kron2 P₂ proj1) i 2
    rw [hWentry.2.2.1, hTentry.2.2.1, hW2, hT2]
  · -- j = 3
    change W i 3 = (kron2 1 proj0 + kron2 P₂ proj1) i 3
    rw [hWentry.2.2.2, hTentry.2.2.2, hW3, hT3]
    congr 1
    funext k
    fin_cases k <;>
      (simp [Mat2.apply, Mat4.apply, ket1_1, tensor1_1, hP₂_def,
            Fin.sum_univ_four,
            Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.of_apply]; rfl)

/-! ## PY24 Lemma A.30 (HP A.15) — Tensor with second-factor-fixed

For 2-qubit unitaries V₁, V₂, V₃, V₄ with
  ∃|ψ⟩ : ∀|x⟩ : ∃|z⟩ : V₂(|x⟩ ⊗ |0⟩) = |z⟩ ⊗ |ψ⟩
there exist W₁, W₂, W₄ and 1-qubit P₂ such that:
  V₁_AC · V₂_BC · V₃_AC · V₄_BC = W₁_AC · W₂_BC · V₃_AC · W₄_BC
  W₂ = I ⊗ |0⟩⟨0| + P₂ ⊗ |1⟩⟨1|. -/
theorem py24_lemma_A_30 (V₁ V₂ V₃ V₄ : Mat4)
    (hV₁ : IsUnitary4 V₁) (hV₂ : IsUnitary4 V₂)
    (_hV₃ : IsUnitary4 V₃) (hV₄ : IsUnitary4 V₄)
    (h : ∃ ψ : Vec1, IsQubit1 ψ ∧ ∀ x : Vec1, IsQubit1 x →
      ∃ z : Vec1, Mat4.apply V₂ (tensor1_1 x ket0_1) = tensor1_1 z ψ) :
    ∃ W₁ W₂ W₄ : Mat4, ∃ P₂ : Mat2, IsUnitary4 W₁ ∧ IsUnitary4 W₂ ∧
      IsUnitary4 W₄ ∧ IsUnitary2 P₂ ∧
      embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄ =
      embedAC W₁ * embedBC W₂ * embedAC V₃ * embedBC W₄ ∧
      W₂ = kron2 1 proj0 + kron2 P₂ proj1 := by
  obtain ⟨ψ, hψ, h_factor⟩ := h
  -- Step 1: Extract T from V₂'s second-factor-fixed structure.
  obtain ⟨T, hT, hVT⟩ := exists_T_second_factor_fixed hV₂ hψ h_factor
  -- Step 2: Get rotation R with R·ket0 = ψ.
  obtain ⟨R, hR, hRψ⟩ := exists_unitary_rotate_from_ket0 hψ
  -- Step 3: Apply matrix equality to get P₂_old.
  obtain ⟨P₂_old, hP₂_eq⟩ := exists_P2_W2_eq_block_diag_second hV₂ hT hR hRψ hVT
  -- W₂_old = kron2 T† R† * V₂. Unitary as product of unitaries.
  have hW₂_old_unit : IsUnitary4 (kron2 1 proj0 + kron2 P₂_old proj1) := by
    rw [← hP₂_eq]
    exact isUnitary4_mul
      (isUnitary4_kron2 (isUnitary2_conjTranspose hT) (isUnitary2_conjTranspose hR)) hV₂
  -- P₂_old is unitary.
  have hP₂_old : IsUnitary2 P₂_old := P2_unitary_from_W_unitary hW₂_old_unit
  -- Define witnesses.
  let P₂_new : Mat2 := T * P₂_old * T.conjTranspose
  refine ⟨V₁ * kron2 I₂ R,
          kron2 1 proj0 + kron2 P₂_new proj1,
          kron2 T I₂ * V₄,
          P₂_new, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · -- W₁ = V₁ * kron2 I₂ R unitary.
    exact isUnitary4_mul hV₁ (isUnitary4_kron2 isUnitary2_one hR)
  · -- W₂_new unitary.
    -- W₂_new = kron2 T 1 * W₂_old * kron2 T† 1.
    have hW₂_new_eq : (kron2 1 proj0 + kron2 P₂_new proj1 : Mat4)
        = kron2 T 1 * (kron2 1 proj0 + kron2 P₂_old proj1) * kron2 T.conjTranspose 1 := by
      rw [kron2_T_conj_block_diag_second]
      have hTT : T * 1 * T.conjTranspose = (1 : Mat2) := by
        rw [mul_one]; exact mul_eq_one_comm.mp hT
      rw [hTT]
    rw [hW₂_new_eq]
    exact isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 hT isUnitary2_one) hW₂_old_unit)
      (isUnitary4_kron2 (isUnitary2_conjTranspose hT) isUnitary2_one)
  · -- W₄ = kron2 T I₂ * V₄ unitary.
    exact isUnitary4_mul (isUnitary4_kron2 hT isUnitary2_one) hV₄
  · -- P₂_new = T * P₂_old * T.conjTranspose unitary.
    exact isUnitary2_mul (isUnitary2_mul hT hP₂_old) (isUnitary2_conjTranspose hT)
  · -- Chain identity.
    -- Step 1: V₂ = kron2 T R * W₂_old.
    have hV₂_eq : V₂ = kron2 T R * (kron2 1 proj0 + kron2 P₂_old proj1) := by
      have h_TR_inv : kron2 T R * kron2 T.conjTranspose R.conjTranspose = (1 : Mat4) := by
        rw [kron2_mul, mul_eq_one_comm.mp hT, mul_eq_one_comm.mp hR]
        exact kron2_one_one_eq_one
      calc V₂ = 1 * V₂ := (one_mul V₂).symm
        _ = (kron2 T R * kron2 T.conjTranspose R.conjTranspose) * V₂ := by rw [h_TR_inv]
        _ = kron2 T R * (kron2 T.conjTranspose R.conjTranspose * V₂) := by rw [mul_assoc]
        _ = kron2 T R * (kron2 1 proj0 + kron2 P₂_old proj1) := by rw [hP₂_eq]
    -- Step 2: split singleQubitLayer I₂ T R into C-part and B-part.
    have h_split : (singleQubitLayer I₂ T R : Mat8)
                 = singleQubitLayer I₂ I₂ R * singleQubitLayer I₂ T I₂ := by
      rw [singleQubitLayer_mul]
      congr 1 <;> simp [I₂]
    -- Now do the chain rewrite via calc.
    calc embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄
        = embedAC V₁ * embedBC (kron2 T R * (kron2 1 proj0 + kron2 P₂_old proj1)) *
          embedAC V₃ * embedBC V₄ := by rw [hV₂_eq]
      _ = embedAC V₁ * (embedBC (kron2 T R) *
            embedBC (kron2 1 proj0 + kron2 P₂_old proj1)) *
          embedAC V₃ * embedBC V₄ := by rw [← embedBC_mul]
      _ = embedAC V₁ * (singleQubitLayer I₂ T R *
            embedBC (kron2 1 proj0 + kron2 P₂_old proj1)) *
          embedAC V₃ * embedBC V₄ := by rw [embedBC_kron2]
      _ = embedAC V₁ * ((singleQubitLayer I₂ I₂ R * singleQubitLayer I₂ T I₂) *
            embedBC (kron2 1 proj0 + kron2 P₂_old proj1)) *
          embedAC V₃ * embedBC V₄ := by rw [h_split]
      -- Reassociate: pull C-part out, leave B-part before W₂.
      _ = (embedAC V₁ * singleQubitLayer I₂ I₂ R) *
          (singleQubitLayer I₂ T I₂ * embedBC (kron2 1 proj0 + kron2 P₂_old proj1)) *
          embedAC V₃ * embedBC V₄ := by noncomm_ring
      -- Step 3: absorb C-part into V₁.
      _ = embedAC (V₁ * kron2 I₂ R) *
          (singleQubitLayer I₂ T I₂ * embedBC (kron2 1 proj0 + kron2 P₂_old proj1)) *
          embedAC V₃ * embedBC V₄ := by
            rw [embedAC_mul_singleQubitLayer, singleQubitLayer_one, mul_one]
      -- Step 4: move B-part through W₂_old (P₂_old → T·P₂_old·T†).
      _ = embedAC (V₁ * kron2 I₂ R) *
          (embedBC (kron2 1 proj0 + kron2 (T * P₂_old * T.conjTranspose) proj1) *
           singleQubitLayer I₂ T I₂) *
          embedAC V₃ * embedBC V₄ := by rw [sQL_T_through_embedBC_W2 _ _ hT]
      -- Reassociate.
      _ = embedAC (V₁ * kron2 I₂ R) *
          embedBC (kron2 1 proj0 + kron2 (T * P₂_old * T.conjTranspose) proj1) *
          (singleQubitLayer I₂ T I₂ * embedAC V₃) * embedBC V₄ := by noncomm_ring
      -- Step 5: move B-part past V₃ (commutes).
      _ = embedAC (V₁ * kron2 I₂ R) *
          embedBC (kron2 1 proj0 + kron2 (T * P₂_old * T.conjTranspose) proj1) *
          (embedAC V₃ * singleQubitLayer I₂ T I₂) * embedBC V₄ := by
            rw [← embedAC_comm_singleQubitLayer_B]
      -- Reassociate.
      _ = embedAC (V₁ * kron2 I₂ R) *
          embedBC (kron2 1 proj0 + kron2 (T * P₂_old * T.conjTranspose) proj1) *
          embedAC V₃ * (singleQubitLayer I₂ T I₂ * embedBC V₄) := by noncomm_ring
      -- Step 6: absorb B-part into V₄.
      _ = embedAC (V₁ * kron2 I₂ R) *
          embedBC (kron2 1 proj0 + kron2 (T * P₂_old * T.conjTranspose) proj1) *
          embedAC V₃ * embedBC (kron2 T I₂ * V₄) := by
            rw [singleQubitLayer_mul_embedBC, singleQubitLayer_one, one_mul]

/-! ## PY24 Lemma A.32 (HP A.16) — Normalization V₃(|0⟩⊗|0⟩) = |0⟩⊗|0⟩

For 2-qubit unitaries U₁, U₂, U₃, U₄, there exist V₁, V₂, V₃, V₄ such that:
  U₁_AC · U₂_BC · U₃_AC · U₄_BC = V₁_AC · V₂_BC · V₃_AC · V₄_BC
  V₃(|0⟩ ⊗ |0⟩) = |0⟩ ⊗ |0⟩. -/
theorem py24_lemma_A_32 (U₁ U₂ U₃ U₄ : Mat4)
    (hU₁ : IsUnitary4 U₁) (hU₂ : IsUnitary4 U₂)
    (hU₃ : IsUnitary4 U₃) (hU₄ : IsUnitary4 U₄) :
    ∃ V₁ V₂ V₃ V₄ : Mat4, IsUnitary4 V₁ ∧ IsUnitary4 V₂ ∧
      IsUnitary4 V₃ ∧ IsUnitary4 V₄ ∧
      embedAC U₁ * embedBC U₂ * embedAC U₃ * embedBC U₄ =
      embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄ ∧
      Mat4.apply V₃ (tensor1_1 ket0_1 ket0_1) = tensor1_1 ket0_1 ket0_1 := by
  -- Apply the normalization lemma to U₃.
  obtain ⟨Ra, Rb, Rψ, V, hRa, hRb, hRψ, hV_unit, hV_ket00, hEq⟩ :=
    exists_unitary_normalize_at_ket00 U₃ hU₃
  refine ⟨U₁ * kron2 Ra I₂, U₂ * kron2 I₂ Rb, V,
          kron2 I₂ Rψ.conjTranspose * U₄, ?_, ?_, hV_unit, ?_, ?_, hV_ket00⟩
  · exact isUnitary4_mul hU₁ (isUnitary4_kron2 hRa isUnitary2_one)
  · exact isUnitary4_mul hU₂ (isUnitary4_kron2 isUnitary2_one hRb)
  · exact isUnitary4_mul
      (isUnitary4_kron2 isUnitary2_one (isUnitary2_conjTranspose hRψ)) hU₄
  · -- Chain identity: substitute U₃, expand embedAC, apply absorption helper.
    have hM_unit : IsUnitary4 (kron2 (1 : Mat2) Rψ) :=
      isUnitary4_kron2 isUnitary2_one hRψ
    have hM_right : kron2 (1 : Mat2) Rψ * (kron2 (1 : Mat2) Rψ).conjTranspose = 1 :=
      mul_eq_one_comm.mp hM_unit
    have hCT : (kron2 (1 : Mat2) Rψ).conjTranspose = kron2 (1 : Mat2) Rψ.conjTranspose := by
      rw [kron2_conjTranspose, Matrix.conjTranspose_one]
    have hU₃_eq : U₃ = kron2 Ra Rb * V * kron2 (1 : Mat2) Rψ.conjTranspose := by
      calc U₃ = U₃ * 1 := (mul_one U₃).symm
        _ = U₃ * (kron2 (1 : Mat2) Rψ * (kron2 (1 : Mat2) Rψ).conjTranspose) := by
            rw [hM_right]
        _ = U₃ * kron2 (1 : Mat2) Rψ * (kron2 (1 : Mat2) Rψ).conjTranspose := by
            rw [mul_assoc]
        _ = kron2 Ra Rb * V * (kron2 (1 : Mat2) Rψ).conjTranspose := by rw [← hEq]
        _ = kron2 Ra Rb * V * kron2 (1 : Mat2) Rψ.conjTranspose := by rw [hCT]
    rw [hU₃_eq]
    rw [show embedAC (kron2 Ra Rb * V * kron2 (1 : Mat2) Rψ.conjTranspose)
            = singleQubitLayer Ra I₂ Rb * embedAC V *
              singleQubitLayer (1 : Mat2) I₂ Rψ.conjTranspose
        from by rw [← embedAC_mul, ← embedAC_mul,
                    embedAC_kron2, embedAC_kron2]]
    exact absorption_chain_AC_BC_AC_BC U₁ U₂ U₄ V Ra Rb Rψ.conjTranspose

/-! ## PY24 Lemma A.33 (HP A.17) — V₁ controlled from middle gate's structure

For 2-qubit unitaries V₁, V₂, V₄, if:
  ∀|x⟩_C : V₁_AC · V₂_BC (|0⟩_A ⊗ |x⟩_B ⊗ |0⟩_C) = V₄†_BC (|0⟩_A ⊗ |x⟩_B ⊗ |0⟩_C)
  ∃|ψ⟩ : ∀|x⟩ : ∃|z⟩ : V₂(|x⟩ ⊗ |0⟩) = |ψ⟩ ⊗ |z⟩
then V₁ = |0⟩⟨0| ⊗ P₀ + |1⟩⟨1| ⊗ P₁ for 1-qubit unitaries P₀, P₁. -/
theorem py24_lemma_A_33 (V₁ V₂ V₄ : Mat4)
    (hV₁ : IsUnitary4 V₁) (_hV₂ : IsUnitary4 V₂) (_hV₄ : IsUnitary4 V₄)
    (h₁ : ∀ x : Vec1, IsQubit1 x →
      Mat8.apply (embedAC V₁ * embedBC V₂)
        (tensor1_2 ket0_1 (tensor1_1 x ket0_1)) =
      Mat8.apply (embedBC V₄.conjTranspose)
        (tensor1_2 ket0_1 (tensor1_1 x ket0_1)))
    (h₂ : ∃ ψ : Vec1, IsQubit1 ψ ∧ ∀ x : Vec1, IsQubit1 x →
      ∃ z : Vec1, Mat4.apply V₂ (tensor1_1 x ket0_1) = tensor1_1 ψ z) :
    ∃ P₀ P₁ : Mat2, IsUnitary2 P₀ ∧ IsUnitary2 P₁ ∧
      V₁ = kron2 proj0 P₀ + kron2 proj1 P₁ := by
  obtain ⟨ψ, hψ, h_factored⟩ := h₂
  obtain ⟨z₀, h_z0⟩ := h_factored ket0_1 IsQubit1_ket0
  obtain ⟨z₁, h_z1⟩ := h_factored ket1_1 IsQubit1_ket1
  -- ψ ≠ 0 since unit qubit.
  have hψ_ne : ψ ≠ 0 := by
    intro h
    have := hψ
    unfold IsQubit1 normSqVec1 at this
    rw [h] at this
    simp at this
  -- For each unit qubit x, derive Mat2.apply (blockA_10 V₁) (x 0 • z₀ + x 1 • z₁) = 0.
  have h_X_z : ∀ x : Vec1, IsQubit1 x →
      Mat2.apply (blockA_10 V₁) (x 0 • z₀ + x 1 • z₁) = 0 := by
    intro x hx
    apply X_apply_z_zero_of_kron2_apply_tensor_zero hψ_ne
    funext i
    -- Goal: Mat4.apply (kron2 1 (blockA_10 V₁)) (tensor1_1 ψ (x 0 • z₀ + x 1 • z₁)) i = 0
    have hkr : kron2 (1 : Mat2) (blockA_10 V₁) = block10 (embedAC V₁) := by
      rw [block10_embedAC]; rfl
    rw [hkr, ← Mat8.apply_tensor1_2_ket0_upper,
        ← V_apply_xtensor0_first_factor_fixed V₂ ψ z₀ z₁ h_z0 h_z1 x,
        ← embedBC_apply_tensor1_2, ← Mat8.apply_mul, h₁ x hx]
    exact Mat8.apply_embedBC_tensor1_2_ket0_upper V₄.conjTranspose _ i
  have hX_z0 : Mat2.apply (blockA_10 V₁) z₀ = 0 := by
    have hh := h_X_z ket0_1 IsQubit1_ket0
    have h_simp : (ket0_1 0 • z₀ + ket0_1 1 • z₁) = z₀ := by
      funext i
      simp [ket0_1, Pi.add_apply]
    rw [h_simp] at hh
    exact hh
  have hX_z1 : Mat2.apply (blockA_10 V₁) z₁ = 0 := by
    have hh := h_X_z ket1_1 IsQubit1_ket1
    have h_simp : (ket1_1 0 • z₀ + ket1_1 1 • z₁) = z₁ := by
      funext i
      simp [ket1_1, Pi.add_apply]
    rw [h_simp] at hh
    exact hh
  -- z₀, z₁ are linearly independent (orthonormal from V₂ unitary).
  have hz_indep : z₀ 0 * z₁ 1 ≠ z₀ 1 * z₁ 0 := by
    -- Step 1: ⟨z₀, z₁⟩ = 0 from V₂ unitary preserving inner product.
    have h_basis_ortho :
        innerVec2 (tensor1_1 ket0_1 ket0_1) (tensor1_1 ket1_1 ket0_1) = 0 := by
      rw [innerVec2_tensor1_1]
      simp [innerVec1, ket0_1, ket1_1, Fin.sum_univ_two]
    have h_z_ortho_full :
        innerVec2 (Mat4.apply V₂ (tensor1_1 ket0_1 ket0_1))
                  (Mat4.apply V₂ (tensor1_1 ket1_1 ket0_1)) = 0 := by
      rw [innerVec2_apply_apply_unitary _hV₂]
      exact h_basis_ortho
    rw [h_z0, h_z1, innerVec2_tensor1_1, innerVec1_self] at h_z_ortho_full
    unfold IsQubit1 at hψ
    rw [hψ] at h_z_ortho_full
    push_cast at h_z_ortho_full
    rw [one_mul] at h_z_ortho_full
    -- h_z_ortho_full : innerVec1 z₀ z₁ = 0
    -- Step 2: ‖z₀‖ = 1.
    have hz₀_unit : IsQubit1 z₀ := by
      have hh := innerVec2_apply_apply_unitary _hV₂
        (tensor1_1 ket0_1 ket0_1) (tensor1_1 ket0_1 ket0_1)
      rw [h_z0, innerVec2_tensor1_1, innerVec1_self, innerVec1_self] at hh
      rw [hψ] at hh
      have h_basis_norm :
          innerVec2 (tensor1_1 ket0_1 ket0_1) (tensor1_1 ket0_1 ket0_1) = 1 := by
        rw [innerVec2_tensor1_1, innerVec1_self]
        rw [show normSqVec1 ket0_1 = 1 from IsQubit1_ket0]
        push_cast; ring
      rw [h_basis_norm] at hh
      push_cast at hh
      rw [one_mul] at hh
      unfold IsQubit1
      exact_mod_cast hh
    have hz₀_ne : z₀ ≠ 0 := by
      intro h
      have hu := hz₀_unit
      unfold IsQubit1 normSqVec1 at hu
      rw [h] at hu
      simp at hu
    -- Step 3: contradiction via linDep_to_scalar.
    intro hcontra
    have h_dep : linearDep1 z₀ z₁ := hcontra
    obtain ⟨lam, hlam⟩ := linDep_to_scalar h_dep hz₀_ne
    -- innerVec1 z₀ (lam • z₀) = lam * normSqVec1 z₀.
    have h_inner_smul : innerVec1 z₀ (lam • z₀) = lam * (normSqVec1 z₀ : ℂ) := by
      unfold innerVec1 normSqVec1
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [show starRingEnd ℂ (z₀ i) * (lam * z₀ i) = lam * (starRingEnd ℂ (z₀ i) * z₀ i)
            from by ring,
          mul_comm (starRingEnd ℂ (z₀ i)), Complex.mul_conj]
    rw [hlam, h_inner_smul] at h_z_ortho_full
    unfold IsQubit1 at hz₀_unit
    rw [hz₀_unit] at h_z_ortho_full
    push_cast at h_z_ortho_full
    rw [mul_one] at h_z_ortho_full
    -- h_z_ortho_full : lam = 0
    -- So z₁ = 0 • z₀ = 0, contradicting IsQubit1 z₁.
    have hz₁_unit : IsQubit1 z₁ := by
      have hh := innerVec2_apply_apply_unitary _hV₂
        (tensor1_1 ket1_1 ket0_1) (tensor1_1 ket1_1 ket0_1)
      rw [h_z1, innerVec2_tensor1_1, innerVec1_self, innerVec1_self] at hh
      rw [hψ] at hh
      have h_basis_norm :
          innerVec2 (tensor1_1 ket1_1 ket0_1) (tensor1_1 ket1_1 ket0_1) = 1 := by
        rw [innerVec2_tensor1_1, innerVec1_self, innerVec1_self]
        rw [show normSqVec1 ket1_1 = 1 from IsQubit1_ket1,
            show normSqVec1 ket0_1 = 1 from IsQubit1_ket0]
        push_cast; ring
      rw [h_basis_norm] at hh
      push_cast at hh
      rw [one_mul] at hh
      unfold IsQubit1
      exact_mod_cast hh
    have hz₁_ne : z₁ ≠ 0 := by
      intro h
      have hu := hz₁_unit
      unfold IsQubit1 normSqVec1 at hu
      rw [h] at hu
      simp at hu
    apply hz₁_ne
    rw [hlam, h_z_ortho_full]
    funext i; simp [Pi.smul_apply, smul_eq_mul]
  have h10 : blockA_10 V₁ = 0 :=
    mat2_eq_zero_of_two_kernel _ z₀ z₁ hz_indep hX_z0 hX_z1
  exact U_eq_controlled_of_blockA_10_zero hV₁ h10

/-- Helper: kron3 of A, B, and the zero matrix is zero. Used by the
    chain_expansion_Q_rotated proof to vanish 14 of 16 cross-terms
    whose C-component is `proj_i · proj_j` with i ≠ j (which equals 0). -/
private lemma kron3_zero_right (A B : Mat2) : kron3 A B (0 : Mat2) = 0 := by
  ext i j
  simp [kron3]

/-- Right-associated projector absorption: `proj0 * (proj0 * X) = proj0 * X`. -/
private lemma proj0_proj0_assoc (X : Mat2) : proj0 * (proj0 * X) = proj0 * X := by
  rw [← mul_assoc, proj0_sq]

/-- Right-associated projector absorption: `proj1 * (proj1 * X) = proj1 * X`. -/
private lemma proj1_proj1_assoc (X : Mat2) : proj1 * (proj1 * X) = proj1 * X := by
  rw [← mul_assoc, proj1_sq]

/-- Right-associated projector orthogonality: `proj0 * (proj1 * X) = 0`. -/
private lemma proj0_proj1_assoc (X : Mat2) : proj0 * (proj1 * X) = 0 := by
  rw [← mul_assoc, proj0_mul_proj1, zero_mul]

/-- Right-associated projector orthogonality: `proj1 * (proj0 * X) = 0`. -/
private lemma proj1_proj0_assoc (X : Mat2) : proj1 * (proj0 * X) = 0 := by
  rw [← mul_assoc, proj1_mul_proj0, zero_mul]

/-- Helper: expansion of the Q-rotated W₁W₂W₃W₄ chain into the kron3 form
    needed by `py24_lemma_4_2`. Paper p.229 tracks third-qubit projector
    sequences: only `(0,0,0,0)` and `(1,1,1,1)` survive (others vanish
    via projector orthogonality). The (0,0,0,0) term yields
    I⊗I⊗(Q·proj0·Q†); the (1,1,1,1) term yields
    (P₁P₃)⊗(P₂P₄)⊗(Q·proj1·Q†). Proof: 5-step decomposition (substitute
    W_i, distribute embedAC/BC over addition, embedAC/BC of kron2 →
    singleQubitLayer, unfold to kron3, then a single `simp only` with
    add_mul/mul_add/kron3_mul/mul_assoc + projector lemmas to fully
    close the 16-term expansion). -/
private lemma chain_expansion_Q_rotated
    (P₁ P₂ P₃ P₄ Q : Mat2)
    (W₁ W₂ W₃ W₄ : Mat4)
    (hW₁ : W₁ = kron2 1 (Q * proj0) + kron2 P₁ (Q * proj1))
    (hW₂ : W₂ = kron2 1 proj0 + kron2 P₂ proj1)
    (hW₃ : W₃ = kron2 1 proj0 + kron2 P₃ proj1)
    (hW₄ : W₄ = kron2 1 (proj0 * Q.conjTranspose) +
                kron2 P₄ (proj1 * Q.conjTranspose)) :
    embedAC W₁ * embedBC W₂ * embedAC W₃ * embedBC W₄ =
    kron3 1 1 (Q * proj0 * Q.conjTranspose) +
    kron3 (P₁ * P₃) (P₂ * P₄) (Q * proj1 * Q.conjTranspose) := by
  -- Step 1: substitute the W_i forms.
  subst hW₁ hW₂ hW₃ hW₄
  -- Step 2: distribute embedAC/embedBC over additions.
  rw [embedAC_add, embedBC_add, embedAC_add, embedBC_add]
  -- Step 3: convert each embedAC/embedBC of a kron2 to a singleQubitLayer.
  simp only [embedAC_kron2, embedBC_kron2]
  -- Step 4: unfold singleQubitLayer and I₂ to kron3 with explicit 1's.
  unfold singleQubitLayer I₂
  -- Step 5: distribute (16 cross-terms via add_mul/mul_add), combine pairs
  -- via kron3_mul, then projector simplifications for both left- and
  -- right-associated forms (mul_assoc + proj_*_assoc helpers + projector
  -- orthogonality + kron3_zero_right) close all 16 terms — surviving
  -- (0,0,0,0) and (1,1,1,1) match RHS, the other 14 vanish.
  simp only [add_mul, mul_add, kron3_mul, mul_one, one_mul, mul_zero,
             mul_assoc, proj0_sq, proj1_sq, proj0_mul_proj1, proj1_mul_proj0,
             proj0_proj0_assoc, proj1_proj1_assoc,
             proj0_proj1_assoc, proj1_proj0_assoc,
             kron3_zero_right, add_zero, zero_add]

/-- SWAP_AB applied to `(x ⊗ |0⟩ ⊗ |0⟩)` gives `(|0⟩ ⊗ x ⊗ |0⟩)`.
    Building block for case1 closure (Lemma 6.2 Case 1) and A.29 closure
    via SWAP_AB role swap. -/
private lemma swap_ab_apply_xtensor_00 (x : Vec1) :
    Mat8.apply SWAP_AB (tensor1_2 x (tensor1_1 ket0_1 ket0_1)) =
    tensor1_2 ket0_1 (tensor1_1 x ket0_1) := by
  funext i
  fin_cases i <;>
    simp [Mat8.apply, SWAP_AB, swap_ab_perm, tensor1_2, tensor1_1, ket0_1,
          Matrix.of_apply, Fin.sum_univ_eight]

/-! ## Helper: 6.2 Case 1 closure (V₃†(x⊗|0⟩) entangled → u₀=u₁ ∨ u₀u₁=1)

Paper p.224 Case 1 of Lemma 6.2. Proof structure (5 steps, ~70 Lean
lines): Step A applies SWAP_AB conjugation to h_U1_eq (using
swap_ab_embedAC, swap_ab_embedBC, swap_ab_apply_xtensor_00) to derive
the role-swapped chain action equation. Step B specializes to xEnt and
reduces via embedBC_apply_tensor1_2 to A.19's hAct form. Step C applies
A.19 to U₄† (with V₃†(xEnt⊗|0⟩) entangled) to extract U₄† = kron2 proj0
P₀ + kron2 proj1 P₁. Step D takes conjTranspose via block_diag_first_conjT
to get U₄ controlled. Step E applies 4.4 with V₄ = U₄'s controlled form
+ h_prod to conclude u₀=u₁ ∨ u₀u₁=1. -/
private lemma case1_v3dag_entangled_concludes
    (u₀ u₁ : ℂ) (hu₀ : Complex.normSq u₀ = 1) (hu₁ : Complex.normSq u₁ = 1)
    (U₁ W₂ V₃ U₄ : Mat4)
    (hU₁ : IsUnitary4 U₁) (hW₂ : IsUnitary4 W₂)
    (hV₃ : IsUnitary4 V₃) (hU₄ : IsUnitary4 U₄)
    (h_prod : embedAC U₁ * embedBC W₂ * embedAC V₃ * embedBC U₄ =
              Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁])
    (h_U1_eq : ∀ x : Vec1, IsQubit1 x →
      Mat8.apply (embedAC U₁) (tensor1_2 x (tensor1_1 ket0_1 ket0_1)) =
      Mat8.apply (embedBC U₄.conjTranspose * embedAC V₃.conjTranspose)
        (tensor1_2 x (tensor1_1 ket0_1 ket0_1)))
    (xEnt : Vec1) (hxEnt_qubit : IsQubit1 xEnt)
    (h_V3dag_ent : IsEntangled (Mat4.apply V₃.conjTranspose (tensor1_1 xEnt ket0_1))) :
    u₀ = u₁ ∨ u₀ * u₁ = 1 := by
  -- Foundational facts: U₄†, V₃† unitary; ϕ := V₃†(xEnt⊗|0⟩) is unit-norm.
  have _hU₄_dag : IsUnitary4 U₄.conjTranspose := isUnitary4_conjTranspose hU₄
  have _hV₃_dag : IsUnitary4 V₃.conjTranspose := isUnitary4_conjTranspose hV₃
  have _h_xEnt_ket0_qubit : IsQubit2 (tensor1_1 xEnt ket0_1) :=
    IsQubit2_tensor1_1 hxEnt_qubit IsQubit1_ket0
  -- ϕ := V₃†(xEnt⊗|0⟩) is a Vec2 unit qubit by V₃† unitary.
  have _hϕ_qubit : IsQubit2 (Mat4.apply V₃.conjTranspose (tensor1_1 xEnt ket0_1)) :=
    IsQubit2_apply_unitary _hV₃_dag _h_xEnt_ket0_qubit
  -- ω := U₁(xEnt⊗|0⟩) is also a Vec2 unit qubit.
  have _hω_qubit : IsQubit2 (Mat4.apply U₁ (tensor1_1 xEnt ket0_1)) :=
    IsQubit2_apply_unitary hU₁ _h_xEnt_ket0_qubit
  -- Step A: SWAP_AB conjugation rewrites: SWAP_AB · embedAC V = embedBC V · SWAP_AB
  -- and SWAP_AB · embedBC V = embedAC V · SWAP_AB. From swap_ab_embedAC + SWAP_AB_sq.
  have h_swap_AC : ∀ V : Mat4, SWAP_AB * embedAC V = embedBC V * SWAP_AB := fun V => by
    calc SWAP_AB * embedAC V
        = SWAP_AB * embedAC V * (SWAP_AB * SWAP_AB) := by rw [SWAP_AB_sq, mul_one]
      _ = (SWAP_AB * embedAC V * SWAP_AB) * SWAP_AB := by noncomm_ring
      _ = embedBC V * SWAP_AB := by rw [swap_ab_embedAC]
  have h_swap_BC : ∀ V : Mat4, SWAP_AB * embedBC V = embedAC V * SWAP_AB := fun V => by
    calc SWAP_AB * embedBC V
        = SWAP_AB * embedBC V * (SWAP_AB * SWAP_AB) := by rw [SWAP_AB_sq, mul_one]
      _ = (SWAP_AB * embedBC V * SWAP_AB) * SWAP_AB := by noncomm_ring
      _ = embedAC V * SWAP_AB := by rw [swap_ab_embedBC]
  -- Derive h_role_swapped from h_U1_eq via SWAP_AB conjugation.
  have h_role_swapped : ∀ x : Vec1, IsQubit1 x →
      Mat8.apply (embedBC U₁) (tensor1_2 ket0_1 (tensor1_1 x ket0_1)) =
      Mat8.apply (embedAC U₄.conjTranspose * embedBC V₃.conjTranspose)
        (tensor1_2 ket0_1 (tensor1_1 x ket0_1)) := by
    intro x hx
    have h := h_U1_eq x hx
    have h_lhs_simp :
        Mat8.apply SWAP_AB (Mat8.apply (embedAC U₁)
          (tensor1_2 x (tensor1_1 ket0_1 ket0_1))) =
        Mat8.apply (embedBC U₁) (tensor1_2 ket0_1 (tensor1_1 x ket0_1)) := by
      rw [← Mat8.apply_mul, h_swap_AC, Mat8.apply_mul, swap_ab_apply_xtensor_00]
    have h_rhs_simp :
        Mat8.apply SWAP_AB
          (Mat8.apply (embedBC U₄.conjTranspose * embedAC V₃.conjTranspose)
            (tensor1_2 x (tensor1_1 ket0_1 ket0_1))) =
        Mat8.apply (embedAC U₄.conjTranspose * embedBC V₃.conjTranspose)
          (tensor1_2 ket0_1 (tensor1_1 x ket0_1)) := by
      rw [← Mat8.apply_mul]
      rw [show SWAP_AB * (embedBC U₄.conjTranspose * embedAC V₃.conjTranspose) =
           (embedAC U₄.conjTranspose * embedBC V₃.conjTranspose) * SWAP_AB from by
           rw [← mul_assoc, h_swap_BC, mul_assoc, h_swap_AC, ← mul_assoc]]
      rw [Mat8.apply_mul, swap_ab_apply_xtensor_00]
    rw [← h_lhs_simp, ← h_rhs_simp]
    exact congrArg (Mat8.apply SWAP_AB) h
  -- Step B: Specialize h_role_swapped to xEnt; reduce both sides via
  -- embedBC_apply_tensor1_2 + Mat8.apply_mul. Result is A.19's hAct form.
  have hAct :
      Mat8.apply (embedAC U₄.conjTranspose)
        (tensor1_2 ket0_1 (Mat4.apply V₃.conjTranspose (tensor1_1 xEnt ket0_1))) =
      tensor1_2 ket0_1 (Mat4.apply U₁ (tensor1_1 xEnt ket0_1)) := by
    have h_specialized := h_role_swapped xEnt hxEnt_qubit
    rw [embedBC_apply_tensor1_2] at h_specialized
    rw [Mat8.apply_mul, embedBC_apply_tensor1_2] at h_specialized
    exact h_specialized.symm
  -- Step C: Apply A.19 to U₄† to extract controlled form.
  obtain ⟨P₀, P₁, hP₀, hP₁, hU₄_dag_form⟩ :=
    py24_lemma_A_19 U₄.conjTranspose _hU₄_dag
      (Mat4.apply V₃.conjTranspose (tensor1_1 xEnt ket0_1))
      (Mat4.apply U₁ (tensor1_1 xEnt ket0_1))
      _hϕ_qubit _hω_qubit hAct h_V3dag_ent
  -- Step D: Take conjTranspose to get U₄'s controlled form.
  have hU₄_form : U₄ = kron2 proj0 P₀.conjTranspose + kron2 proj1 P₁.conjTranspose := by
    have h := congrArg Matrix.conjTranspose hU₄_dag_form
    rw [Matrix.conjTranspose_conjTranspose, block_diag_first_conjT] at h
    exact h
  -- Step E: Apply 4.4 with U₄'s controlled form + h_prod to conclude.
  exact (py24_lemma_4_4 u₀ u₁ hu₀ hu₁).mp
    ⟨U₁, W₂, V₃, U₄, hU₁, hW₂, hV₃, hU₄,
     P₀.conjTranspose, P₁.conjTranspose,
     isUnitary2_conjTranspose hP₀, isUnitary2_conjTranspose hP₁,
     hU₄_form, h_prod⟩

/-- **A.22 helper**: entry-wise computation of `embedAC U (α⊗β⊗γ)`.
    The (4a+2b+c)-th entry equals `β_b · (U·(α⊗γ))_{2a+c}`.
    Used by `py24_lemma_A_22` to convert the Mat8 equation into 8
    scalar equations over (a,b,c) ∈ Fin 2³. -/
lemma embedAC_apply_tensor1_2_tensor1_1_entry
    (U : Mat4) (α β γ : Vec1) :
    ∀ a b c : Fin 2,
      Mat8.apply (embedAC U) (tensor1_2 α (tensor1_1 β γ))
        ⟨4 * a.val + 2 * b.val + c.val, by omega⟩ =
      β b * Mat4.apply U (tensor1_1 α γ)
        ⟨2 * a.val + c.val, by omega⟩ := by
  intro a b c
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    (simp [Mat8.apply, embedAC, tensor1_2, tensor1_1, Mat4.apply,
           Matrix.of_apply, Fin.sum_univ_eight, Fin.sum_univ_four];
     ring)

/-- Converse extraction: from `embedAC M (α ⊗ |0⟩ ⊗ γ) = a ⊗ |0⟩ ⊗ c`,
    derive `M(α⊗γ) = a⊗c` by reading the b=0 slice of the Vec3 equation.
    Direct entry-by-entry computation via funext + fin_cases + simp +
    linear_combination on each of 4 Fin 4 indices. -/
lemma Mat4_apply_eq_of_embedAC_apply_with_ket0_middle
    (M : Mat4) (α γ a c : Vec1)
    (h : Mat8.apply (embedAC M) (tensor1_2 α (tensor1_1 ket0_1 γ)) =
         tensor1_2 a (tensor1_1 ket0_1 c)) :
    Mat4.apply M (tensor1_1 α γ) = tensor1_1 a c := by
  funext k
  fin_cases k
  · have h' := congrFun h 0
    simp [Mat8.apply, embedAC, tensor1_2, tensor1_1, ket0_1,
          Matrix.of_apply, Fin.sum_univ_eight] at h'
    simp [Mat4.apply, tensor1_1, Fin.sum_univ_four]
    linear_combination h'
  · have h' := congrFun h 1
    simp [Mat8.apply, embedAC, tensor1_2, tensor1_1, ket0_1,
          Matrix.of_apply, Fin.sum_univ_eight] at h'
    simp [Mat4.apply, tensor1_1, Fin.sum_univ_four]
    linear_combination h'
  · have h' := congrFun h 4
    simp [Mat8.apply, embedAC, tensor1_2, tensor1_1, ket0_1,
          Matrix.of_apply, Fin.sum_univ_eight] at h'
    simp [Mat4.apply, tensor1_1, Fin.sum_univ_four]
    linear_combination h'
  · have h' := congrFun h 5
    simp [Mat8.apply, embedAC, tensor1_2, tensor1_1, ket0_1,
          Matrix.of_apply, Fin.sum_univ_eight] at h'
    simp [Mat4.apply, tensor1_1, Fin.sum_univ_four]
    linear_combination h'

/-- **case3 helper**: when `V·(α⊗γ) = a⊗c` factors, applying `embedAC V` to
    `α⊗β⊗γ` (with B-bystander β) yields `a⊗β⊗c`. Threads the entry-wise
    helper `embedAC_apply_tensor1_2_tensor1_1_entry` through Fin 8
    decomposition + congrFun on the Mat4 equation `h`. -/
lemma embedAC_apply_via_factored_action
    (V : Mat4) (α β γ a c : Vec1)
    (h : Mat4.apply V (tensor1_1 α γ) = tensor1_1 a c) :
    Mat8.apply (embedAC V) (tensor1_2 α (tensor1_1 β γ)) =
    tensor1_2 a (tensor1_1 β c) := by
  funext k
  obtain ⟨a', b', c', hk_eq⟩ : ∃ a' b' c' : Fin 2,
      k = ⟨4 * a'.val + 2 * b'.val + c'.val, by omega⟩ := by
    refine ⟨⟨k.val / 4, by omega⟩, ⟨(k.val / 2) % 2, by omega⟩,
            ⟨k.val % 2, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [Fin.val_mk]
    omega
  rw [hk_eq, embedAC_apply_tensor1_2_tensor1_1_entry V α β γ a' b' c']
  rw [show Mat4.apply V (tensor1_1 α γ) ⟨2 * a'.val + c'.val, by omega⟩ =
       tensor1_1 a c ⟨2 * a'.val + c'.val, by omega⟩ from congrFun h _]
  fin_cases a' <;> fin_cases b' <;> fin_cases c' <;>
    simp [tensor1_1, tensor1_2] <;> ring

/-! ## PY24 Lemma A.22 — Tensor structure preservation through U_AC

Paper p.248. For a 2-qubit unitary U and qubits |α⟩, |β⟩, |γ⟩, |ψ⟩ and a
4-dim unit vector |φ⟩_BC, if `U_AC (|α⟩_A ⊗ |β⟩_B ⊗ |γ⟩_C) = |ψ⟩_A ⊗ |φ⟩_BC`,
then ∃ qubit |w⟩ such that |φ⟩_BC = |β⟩_B ⊗ |w⟩_C.

Used by Lemma 6.2 Case 3 (via `case3_v3dag_first_fixed_concludes`) to
derive `W₄†(|z⟩⊗|0⟩) = |z⟩⊗β` (B factor preserved through W₄† action).

Paper proof (p.248): form outer product on each side, trace out A and C
to get |β⟩⟨β| = tr_C(|φ⟩⟨φ|). Pick |β⊥⟩ ⊥ |β⟩; from A.15 (Schmidt-like
decomp), |φ⟩ = |β⟩⊗|w⟩ + |β⊥⟩⊗|z⟩. Compute tr_C(|φ⟩⟨φ|) and equate;
get ⟨z|z⟩ = 0, so |z⟩ = 0.

Direct proof avoiding partial trace: from the hypothesis, the (4a+2b+c)-th
entry of the LHS is `β_b · (U·(α⊗γ))_{2a+c}` (since embedAC preserves the
B coordinate), while the RHS entry is `ψ_a · φ_{2b+c}`. Eliminating the
ξ := U·(α⊗γ) variable across (a,0,c) vs (a,1,c) yields the constraint
`β_1 · φ_c = β_0 · φ_{2+c}` for c ∈ {0,1}. Constructive: when β 0 ≠ 0,
pick w_c := φ_c / β_0; otherwise (β 1 ≠ 0) pick w_c := φ_{2+c} / β_1.

Uses helper `embedAC_apply_tensor1_2_tensor1_1_entry` (defined below)
to extract 8 scalar equations. -/
lemma py24_lemma_A_22 {U : Mat4} (_hU : IsUnitary4 U)
    {α β γ ψ : Vec1} (_hα : IsQubit1 α) (hβ : IsQubit1 β)
    (_hγ : IsQubit1 γ) (hψ : IsQubit1 ψ)
    {φ : Vec2} (_hφ : IsQubit2 φ)
    (h : Mat8.apply (embedAC U) (tensor1_2 α (tensor1_1 β γ)) =
          tensor1_2 ψ φ) :
    ∃ w : Vec1, φ = tensor1_1 β w := by
  -- Step 1: 8 entry equations β_b · U·αγ_{2a+c} = ψ_a · φ_{2b+c}.
  have h_e : ∀ a b c : Fin 2,
      β b * Mat4.apply U (tensor1_1 α γ)
            ⟨2 * a.val + c.val, by omega⟩ =
      ψ a * φ ⟨2 * b.val + c.val, by omega⟩ := by
    intro a b c
    have hE := embedAC_apply_tensor1_2_tensor1_1_entry U α β γ a b c
    have hH := congrFun h ⟨4 * a.val + 2 * b.val + c.val, by omega⟩
    rw [hE] at hH
    rw [hH]
    -- show tensor1_2 ψ φ ⟨4a+2b+c⟩ = ψ a * φ ⟨2b+c⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [tensor1_2]
  -- Specialize to 8 facts (defeq Fin reductions).
  have e000 : β 0 * Mat4.apply U (tensor1_1 α γ) 0 = ψ 0 * φ 0 := h_e 0 0 0
  have e001 : β 0 * Mat4.apply U (tensor1_1 α γ) 1 = ψ 0 * φ 1 := h_e 0 0 1
  have e010 : β 1 * Mat4.apply U (tensor1_1 α γ) 0 = ψ 0 * φ 2 := h_e 0 1 0
  have e011 : β 1 * Mat4.apply U (tensor1_1 α γ) 1 = ψ 0 * φ 3 := h_e 0 1 1
  have e100 : β 0 * Mat4.apply U (tensor1_1 α γ) 2 = ψ 1 * φ 0 := h_e 1 0 0
  have e101 : β 0 * Mat4.apply U (tensor1_1 α γ) 3 = ψ 1 * φ 1 := h_e 1 0 1
  have e110 : β 1 * Mat4.apply U (tensor1_1 α γ) 2 = ψ 1 * φ 2 := h_e 1 1 0
  have e111 : β 1 * Mat4.apply U (tensor1_1 α γ) 3 = ψ 1 * φ 3 := h_e 1 1 1
  -- Step 2: ψ unit qubit gives ψ 0 ≠ 0 ∨ ψ 1 ≠ 0.
  have hψ_ne : ψ 0 ≠ 0 ∨ ψ 1 ≠ 0 := by
    by_contra hne; push_neg at hne
    have : normSqVec1 ψ = 0 := by
      unfold normSqVec1; rw [Fin.sum_univ_two, hne.1, hne.2]; simp
    rw [hψ] at this; norm_num at this
  -- Step 3: derive β_1·φ_0 = β_0·φ_2 and β_1·φ_1 = β_0·φ_3.
  have h_phi_02 : β 1 * φ 0 = β 0 * φ 2 := by
    rcases hψ_ne with hψ0 | hψ1
    · have key : ψ 0 * (β 1 * φ 0 - β 0 * φ 2) = 0 := by
        linear_combination β 0 * e010 - β 1 * e000
      have := (mul_eq_zero.mp key).resolve_left hψ0
      linear_combination this
    · have key : ψ 1 * (β 1 * φ 0 - β 0 * φ 2) = 0 := by
        linear_combination β 0 * e110 - β 1 * e100
      have := (mul_eq_zero.mp key).resolve_left hψ1
      linear_combination this
  have h_phi_13 : β 1 * φ 1 = β 0 * φ 3 := by
    rcases hψ_ne with hψ0 | hψ1
    · have key : ψ 0 * (β 1 * φ 1 - β 0 * φ 3) = 0 := by
        linear_combination β 0 * e011 - β 1 * e001
      have := (mul_eq_zero.mp key).resolve_left hψ0
      linear_combination this
    · have key : ψ 1 * (β 1 * φ 1 - β 0 * φ 3) = 0 := by
        linear_combination β 0 * e111 - β 1 * e101
      have := (mul_eq_zero.mp key).resolve_left hψ1
      linear_combination this
  -- Step 4: case split β 0 = 0 vs ≠ 0; construct w.
  by_cases hβ0 : β 0 = 0
  · have hβ1 : β 1 ≠ 0 := by
      intro h1
      have : normSqVec1 β = 0 := by
        unfold normSqVec1; rw [Fin.sum_univ_two, hβ0, h1]; simp
      rw [hβ] at this; norm_num at this
    have hφ0 : φ 0 = 0 := by
      have hk := h_phi_02; rw [hβ0, zero_mul] at hk
      exact (mul_eq_zero.mp hk).resolve_left hβ1
    have hφ1 : φ 1 = 0 := by
      have hk := h_phi_13; rw [hβ0, zero_mul] at hk
      exact (mul_eq_zero.mp hk).resolve_left hβ1
    refine ⟨![φ 2 / β 1, φ 3 / β 1], ?_⟩
    funext k
    fin_cases k <;> simp [tensor1_1, hβ0, hφ0, hφ1] <;> field_simp
  · refine ⟨![φ 0 / β 0, φ 1 / β 0], ?_⟩
    funext k
    fin_cases k <;> simp [tensor1_1]
    · field_simp
    · field_simp
    · field_simp; linear_combination -h_phi_02
    · field_simp; linear_combination -h_phi_13

/-! ## PY24 Lemma A.25 — First-factor-fixed → linear via 1-qubit unitary

Paper p.226. If a 2-qubit unitary V is "first-factor-fixed" — i.e.,
∃ ψ ∀ x ∃ z : V(x⊗|0⟩) = ψ⊗z (z varies with x but first factor is
fixed at ψ) — then there exists a 1-qubit unitary P such that, for
any qubit x, `V(x⊗|0⟩) = ψ⊗(P·x)`. So z(x) = P·x. Used by case3
helper to convert V₃†'s factored output into a P₀-linear form.

Proof mirrors `exists_T_second_factor_fixed` (line 3822) with the
tensor positions swapped (ψ on left of z instead of right). Pick z₀ = z(ket0),
z₁ = z(ket1); derive z₀, z₁ unit-norm and orthogonal from V unitary
preserving inner products; build P = matrixOfColumns z₀ z₁; show
∀ x, V(x⊗|0⟩) = ψ⊗(P·x) via vec1_basis_decomp x + Mat4.apply linearity. -/
lemma py24_lemma_A_25 (V : Mat4) (hV : IsUnitary4 V) (ψ : Vec1) (hψ : IsQubit1 ψ)
    (h : ∀ x : Vec1, IsQubit1 x →
      ∃ z : Vec1, Mat4.apply V (tensor1_1 x ket0_1) = tensor1_1 ψ z) :
    ∃ P : Mat2, IsUnitary2 P ∧
      ∀ x : Vec1, IsQubit1 x →
        Mat4.apply V (tensor1_1 x ket0_1) = tensor1_1 ψ (Mat2.apply P x) := by
  obtain ⟨z₀, h_z0⟩ := h ket0_1 IsQubit1_ket0
  obtain ⟨z₁, h_z1⟩ := h ket1_1 IsQubit1_ket1
  -- Orthonormality of z₀, z₁ from V's unitarity.
  have hψ_nsq : normSqVec1 ψ = 1 := hψ
  have h_z0_nsq : normSqVec1 z₀ = 1 := by
    have : IsQubit2 (tensor1_1 ψ z₀) := by
      rw [← h_z0]; exact IsQubit2_apply_unitary hV IsQubit2_ket00
    unfold IsQubit2 at this
    rw [normSqVec2_tensor1_1, hψ_nsq, one_mul] at this
    exact this
  have h_z1_nsq : normSqVec1 z₁ = 1 := by
    have : IsQubit2 (tensor1_1 ψ z₁) := by
      rw [← h_z1]; exact IsQubit2_apply_unitary hV IsQubit2_ket10
    unfold IsQubit2 at this
    rw [normSqVec2_tensor1_1, hψ_nsq, one_mul] at this
    exact this
  -- Orthogonality ⟨z₀, z₁⟩ = 0 from inner product preservation.
  have h_z01 : innerVec1 z₀ z₁ = 0 := by
    have h_inner : innerVec2 (Mat4.apply V (tensor1_1 ket0_1 ket0_1))
                            (Mat4.apply V (tensor1_1 ket1_1 ket0_1))
                  = innerVec2 (tensor1_1 ket0_1 ket0_1) (tensor1_1 ket1_1 ket0_1) :=
      innerVec2_apply_apply_unitary hV _ _
    rw [h_z0, h_z1, innerVec2_tensor1_1, innerVec2_tensor1_1] at h_inner
    have h_psi_self : innerVec1 ψ ψ = (1 : ℂ) := by
      rw [innerVec1_self]; exact_mod_cast hψ
    have h_ket0_ket1 : innerVec1 ket0_1 ket1_1 = 0 := by
      unfold innerVec1
      rw [Fin.sum_univ_two]
      simp [ket0_1, ket1_1]
    rw [h_psi_self, h_ket0_ket1, zero_mul, one_mul] at h_inner
    exact h_inner
  refine ⟨matrixOfColumns z₀ z₁, matrixOfColumns_unitary h_z0_nsq h_z1_nsq h_z01, ?_⟩
  -- For all x, V·(x⊗|0⟩) = ψ⊗(P·x).
  intro x _hx
  have hx_decomp : x = x 0 • ket0_1 + x 1 • ket1_1 := vec1_basis_decomp x
  rw [hx_decomp]
  rw [tensor1_1_add_left, tensor1_1_smul_left, tensor1_1_smul_left,
      Mat4.apply_add, Mat4.apply_smul, Mat4.apply_smul, h_z0, h_z1]
  rw [matrixOfColumns_apply, ← tensor1_1_smul_right, ← tensor1_1_smul_right,
      ← tensor1_1_add_right]
  congr 1
  simp [ket0_1, ket1_1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-! ## Helper: 6.2 Case 3 closure (V₃† first-factor-fixed → u₀=u₁ ∨ u₀u₁=1)

Paper p.226 Case 3 of Lemma 6.2 chain: from V₃†(x⊗|0⟩) = |ψ⟩⊗z(x)
(first-factor fixed) plus the chain action hypothesis, paper applies
**A.25** (z(x) = P₀|x⟩ for some unitary P₀), then **A.22** (a `|0⟩-fixed
mapping for U₄†` corollary), then **A.17** (have ✓; gives U₄†
controlled), then **4.4** (have ✓; controlled-V₄ ⇒ disjunct). Body:
`sorry` — this black-box helper packages the full chain. Tractable
in ~80-150 Lean lines once A.25, A.22 are formalized (missing). -/
private lemma case3_v3dag_first_fixed_concludes
    (u₀ u₁ : ℂ) (_hu₀ : Complex.normSq u₀ = 1) (_hu₁ : Complex.normSq u₁ = 1)
    (U₁ W₂ V₃ U₄ : Mat4)
    (hU₁ : IsUnitary4 U₁) (_hW₂ : IsUnitary4 W₂)
    (hV₃ : IsUnitary4 V₃) (hU₄ : IsUnitary4 U₄)
    (_h_prod : embedAC U₁ * embedBC W₂ * embedAC V₃ * embedBC U₄ =
              Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁])
    (h_U1_eq : ∀ x : Vec1, IsQubit1 x →
      Mat8.apply (embedAC U₁) (tensor1_2 x (tensor1_1 ket0_1 ket0_1)) =
      Mat8.apply (embedBC U₄.conjTranspose * embedAC V₃.conjTranspose)
        (tensor1_2 x (tensor1_1 ket0_1 ket0_1)))
    (ψ : Vec1) (hψ : IsQubit1 ψ)
    (h_V3dag_first_fixed : ∀ x : Vec1, IsQubit1 x →
      ∃ z : Vec1, Mat4.apply V₃.conjTranspose (tensor1_1 x ket0_1) = tensor1_1 ψ z) :
    u₀ = u₁ ∨ u₀ * u₁ = 1 := by
  -- Step 1: extract P₀ via A.25.
  obtain ⟨P₀, hP₀_unit, hP₀_eq⟩ :=
    py24_lemma_A_25 V₃.conjTranspose (isUnitary4_conjTranspose hV₃)
      ψ hψ h_V3dag_first_fixed
  -- Step 2: derive
  --   embedAC U₁ (x⊗|0⟩⊗|0⟩) = ψ ⊗ U₄†(|0⟩⊗(P₀·x))     for x : qubit.
  -- Chain: h_U1_eq → Mat8.apply_mul → embedAC_apply_via_factored_action
  --                → embedBC_apply_tensor1_2.
  have h_chain_action : ∀ x : Vec1, IsQubit1 x →
      Mat8.apply (embedAC U₁) (tensor1_2 x (tensor1_1 ket0_1 ket0_1)) =
      tensor1_2 ψ
        (Mat4.apply U₄.conjTranspose (tensor1_1 ket0_1 (Mat2.apply P₀ x))) := by
    intro x hx
    rw [h_U1_eq x hx, Mat8.apply_mul,
        embedAC_apply_via_factored_action V₃.conjTranspose x ket0_1 ket0_1
          ψ (Mat2.apply P₀ x) (hP₀_eq x hx),
        embedBC_apply_tensor1_2]
  -- Step 3: apply A.22 to extract w_x with U₄†(|0⟩⊗(P₀·x)) = |0⟩⊗w_x.
  have h_U4dag_factors : ∀ x : Vec1, IsQubit1 x →
      ∃ w : Vec1, Mat4.apply U₄.conjTranspose
                    (tensor1_1 ket0_1 (Mat2.apply P₀ x)) = tensor1_1 ket0_1 w := by
    intro x hx
    have hP0x : IsQubit1 (Mat2.apply P₀ x) := IsQubit1_apply_unitary hP₀_unit hx
    have h_ket0_P0x : IsQubit2 (tensor1_1 ket0_1 (Mat2.apply P₀ x)) :=
      IsQubit2_tensor1_1 IsQubit1_ket0 hP0x
    have hU4dag_unit : IsUnitary4 U₄.conjTranspose := isUnitary4_conjTranspose hU₄
    have hφ : IsQubit2 (Mat4.apply U₄.conjTranspose
                         (tensor1_1 ket0_1 (Mat2.apply P₀ x))) :=
      IsQubit2_apply_unitary hU4dag_unit h_ket0_P0x
    exact py24_lemma_A_22 hU₁ hx IsQubit1_ket0 IsQubit1_ket0 hψ hφ
      (h_chain_action x hx)
  -- Step 4: specialize to ket0_1, ket1_1; apply A.17 to U₄†.
  obtain ⟨w₀, hw₀⟩ := h_U4dag_factors ket0_1 IsQubit1_ket0
  obtain ⟨w₁, hw₁⟩ := h_U4dag_factors ket1_1 IsQubit1_ket1
  have hP0_ket0_qubit : IsQubit1 (Mat2.apply P₀ ket0_1) :=
    IsQubit1_apply_unitary hP₀_unit IsQubit1_ket0
  have hP0_ket1_qubit : IsQubit1 (Mat2.apply P₀ ket1_1) :=
    IsQubit1_apply_unitary hP₀_unit IsQubit1_ket1
  have h_orth : innerVec1 (Mat2.apply P₀ ket0_1) (Mat2.apply P₀ ket1_1) = 0 := by
    rw [innerVec1_apply_apply_unitary hP₀_unit]
    unfold innerVec1; rw [Fin.sum_univ_two]; simp [ket0_1, ket1_1]
  obtain ⟨Q₀, Q₁, hQ₀, hQ₁, hU₄dag_form⟩ :=
    py24_lemma_A_17 (isUnitary4_conjTranspose hU₄)
      hP0_ket0_qubit hP0_ket1_qubit h_orth hw₀ hw₁
  -- Step 5: take conjTranspose to get U₄ in block_diag_first form; apply 4.4.
  have hU₄_form : U₄ = kron2 proj0 Q₀.conjTranspose + kron2 proj1 Q₁.conjTranspose := by
    have h := congrArg Matrix.conjTranspose hU₄dag_form
    rw [Matrix.conjTranspose_conjTranspose, block_diag_first_conjT] at h
    exact h
  exact (py24_lemma_4_4 u₀ u₁ _hu₀ _hu₁).mp
    ⟨U₁, W₂, V₃, U₄, hU₁, _hW₂, hV₃, hU₄,
     Q₀.conjTranspose, Q₁.conjTranspose,
     isUnitary2_conjTranspose hQ₀, isUnitary2_conjTranspose hQ₁,
     hU₄_form, _h_prod⟩

/-! ## PY24 Lemma A.31 — Tensor with first-factor V₃† extracts W₃ controlled

Paper p.225. Analog of A.30 with the third position rather than the second:
for 2-qubit unitaries V₁..V₄, if V₃†(x⊗|0⟩) is second-factor-fixed
(∃ψ ∀x ∃z, V₃†(x⊗|0⟩) = z⊗ψ), then ∃ W₁, W₃, W₄ and 1-qubit P₃ such that:
  · V_{1AC} V_{2BC} V_{3AC} V_{4BC} = W_{1AC} V_{2BC} W_{3AC} W_{4BC}
  · W₃ = I ⊗ |0⟩⟨0| + P₃ ⊗ |1⟩⟨1|

Proof: mirrors A.30 (extract T from V₃†'s second-factor-fixed structure,
build rotation R_ψ, define W₃ via the T-conjugation P₃_new = T·P₃_old†·T†,
verify the chain identity via sQL_T_through_embedAC_W). -/
lemma py24_lemma_A_31 (V₁ V₂ V₃ V₄ : Mat4)
    (hV₁ : IsUnitary4 V₁) (_hV₂ : IsUnitary4 V₂)
    (hV₃ : IsUnitary4 V₃) (hV₄ : IsUnitary4 V₄)
    (h : ∃ ψ : Vec1, IsQubit1 ψ ∧ ∀ x : Vec1, IsQubit1 x →
      ∃ z : Vec1, Mat4.apply V₃.conjTranspose (tensor1_1 x ket0_1) = tensor1_1 z ψ) :
    ∃ W₁ W₃ W₄ : Mat4, ∃ P₃ : Mat2, IsUnitary4 W₁ ∧ IsUnitary4 W₃ ∧
      IsUnitary4 W₄ ∧ IsUnitary2 P₃ ∧
      embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄ =
      embedAC W₁ * embedBC V₂ * embedAC W₃ * embedBC W₄ ∧
      W₃ = kron2 1 proj0 + kron2 P₃ proj1 := by
  obtain ⟨ψ, hψ, h_factor⟩ := h
  -- Step 1: Extract T from V₃†'s second-factor-fixed structure.
  obtain ⟨T, hT, hVT⟩ := exists_T_second_factor_fixed
    (isUnitary4_conjTranspose hV₃) hψ h_factor
  -- Step 2: Get rotation R with R · ket0 = ψ.
  obtain ⟨R, hR, hRψ⟩ := exists_unitary_rotate_from_ket0 hψ
  -- Step 3: Extract P₃_old with kron2 T† R† · V₃† = kron2 1 proj0 + kron2 P₃_old proj1.
  obtain ⟨P₃_old, hP₃_eq⟩ := exists_P2_W2_eq_block_diag_second
    (isUnitary4_conjTranspose hV₃) hT hR hRψ hVT
  -- Step 4a: W₃_old (the LHS of hP₃_eq) is unitary as a product of unitaries.
  have hW₃_old_unit : IsUnitary4 (kron2 1 proj0 + kron2 P₃_old proj1) := by
    rw [← hP₃_eq]
    exact isUnitary4_mul
      (isUnitary4_kron2 (isUnitary2_conjTranspose hT) (isUnitary2_conjTranspose hR))
      (isUnitary4_conjTranspose hV₃)
  -- Step 4b: P₃_old is unitary (extract from W₃_old's controlled form).
  have hP₃_old : IsUnitary2 P₃_old := P2_unitary_from_W_unitary hW₃_old_unit
  -- Step 5: Define P₃_new := T · P₃_old† · T† (the conjugated form needed
  -- for the chain identity to work in the AC position). Refine the
  -- existential with explicit witnesses:
  --   W₁_new = V₁ · kron2 T† I₂  (V₁ absorbs T† on A)
  --   W₃_new = kron2 1 proj0 + kron2 P₃_new proj1  (controlled form)
  --   W₄_new = kron2 I₂ R† · V₄  (V₄ absorbs R† on C)
  -- These come from the analysis: V₃ = W₃_old† · kron2 T† R†, where
  -- W₃_old† is conjugated by kron2 T 1 to put it in controlled form.
  let P₃_new : Mat2 := T * P₃_old.conjTranspose * T.conjTranspose
  refine ⟨V₁ * kron2 T.conjTranspose I₂,
          kron2 1 proj0 + kron2 P₃_new proj1,
          kron2 I₂ R.conjTranspose * V₄,
          P₃_new, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · -- IsUnitary4 W₁_new = V₁ · kron2 T† I₂
    exact isUnitary4_mul hV₁
      (isUnitary4_kron2 (isUnitary2_conjTranspose hT) isUnitary2_one)
  · -- IsUnitary4 W₃_new = kron2 1 proj0 + kron2 P₃_new proj1.
    -- Strategy: rewrite W₃_new = kron2 T 1 · W₃_old† · kron2 T† 1 via
    -- kron2_T_conj_block_diag_second, then use unitarity of all factors.
    have hTT : T * 1 * T.conjTranspose = (1 : Mat2) := by
      rw [mul_one]; exact mul_eq_one_comm.mp hT
    have hW₃_old_dag_unit :
        IsUnitary4 (kron2 1 proj0 + kron2 P₃_old.conjTranspose proj1) := by
      have h_eq : (kron2 1 proj0 + kron2 P₃_old.conjTranspose proj1 : Mat4)
                = (kron2 1 proj0 + kron2 P₃_old proj1 : Mat4).conjTranspose := by
        rw [block_diag_second_conjT, Matrix.conjTranspose_one]
      rw [h_eq]
      exact isUnitary4_conjTranspose hW₃_old_unit
    have hW₃_new_eq : (kron2 1 proj0 + kron2 P₃_new proj1 : Mat4)
        = kron2 T 1 * (kron2 1 proj0 + kron2 P₃_old.conjTranspose proj1)
            * kron2 T.conjTranspose 1 := by
      rw [kron2_T_conj_block_diag_second, hTT]
    rw [hW₃_new_eq]
    exact isUnitary4_mul
      (isUnitary4_mul (isUnitary4_kron2 hT isUnitary2_one) hW₃_old_dag_unit)
      (isUnitary4_kron2 (isUnitary2_conjTranspose hT) isUnitary2_one)
  · -- IsUnitary4 W₄_new = kron2 I₂ R† · V₄
    exact isUnitary4_mul
      (isUnitary4_kron2 isUnitary2_one (isUnitary2_conjTranspose hR)) hV₄
  · -- IsUnitary2 P₃_new = T · P₃_old† · T†
    exact isUnitary2_mul
      (isUnitary2_mul hT (isUnitary2_conjTranspose hP₃_old))
      (isUnitary2_conjTranspose hT)
  · -- chain identity. Foundation: V₃ = W₃_old† · kron2 T† R†.
    have hV₃dag_eq : V₃.conjTranspose = kron2 T R *
        (kron2 1 proj0 + kron2 P₃_old proj1) := by
      have h_TR_inv : kron2 T R * kron2 T.conjTranspose R.conjTranspose = (1 : Mat4) := by
        rw [kron2_mul, mul_eq_one_comm.mp hT, mul_eq_one_comm.mp hR]
        exact kron2_one_one_eq_one
      calc V₃.conjTranspose
          = 1 * V₃.conjTranspose := (one_mul _).symm
        _ = (kron2 T R * kron2 T.conjTranspose R.conjTranspose) *
              V₃.conjTranspose := by rw [h_TR_inv]
        _ = kron2 T R * (kron2 T.conjTranspose R.conjTranspose *
              V₃.conjTranspose) := by rw [mul_assoc]
        _ = kron2 T R * (kron2 1 proj0 + kron2 P₃_old proj1) := by rw [hP₃_eq]
    have hV₃_eq : V₃ = (kron2 1 proj0 + kron2 P₃_old.conjTranspose proj1) *
                       kron2 T.conjTranspose R.conjTranspose := by
      have h := congrArg Matrix.conjTranspose hV₃dag_eq
      rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul,
          block_diag_second_conjT, Matrix.conjTranspose_one,
          kron2_conjTranspose] at h
      exact h
    -- Calc block: substitute V₃, split embedAC into singleQubitLayer + W₃_old†,
    -- thread sQL T† through W₃_old† via the helper, absorb pieces into V₁ and V₄.
    have hTinv : T.conjTranspose * T = (1 : Mat2) := hT
    have h_conj_simplify :
        T.conjTranspose * (T * P₃_old.conjTranspose * T.conjTranspose) * T =
        P₃_old.conjTranspose := by
      rw [show T.conjTranspose * (T * P₃_old.conjTranspose * T.conjTranspose) * T
           = (T.conjTranspose * T) * P₃_old.conjTranspose * (T.conjTranspose * T)
           by noncomm_ring]
      rw [hTinv, one_mul, mul_one]
    -- Split sQL T† I R† = sQL T† I I · sQL I I R†.
    have h_split : (singleQubitLayer T.conjTranspose I₂ R.conjTranspose : Mat8) =
        singleQubitLayer T.conjTranspose I₂ I₂ * singleQubitLayer I₂ I₂ R.conjTranspose := by
      rw [singleQubitLayer_mul]
      congr 1 <;> simp [I₂]
    -- Threading lemma: embedAC W₃_old† · sQL T† = sQL T† · embedAC W₃_new.
    have h_thread :
        embedAC (kron2 1 proj0 + kron2 P₃_old.conjTranspose proj1) *
          singleQubitLayer T.conjTranspose I₂ I₂ =
        singleQubitLayer T.conjTranspose I₂ I₂ *
          embedAC (kron2 1 proj0 + kron2 P₃_new proj1) := by
      have h_helper :=
        sQL_T_through_embedAC_W T.conjTranspose P₃_new (isUnitary2_conjTranspose hT)
      rw [Matrix.conjTranspose_conjTranspose, h_conj_simplify] at h_helper
      exact h_helper.symm
    -- Calc block:
    calc embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄
        = embedAC V₁ * embedBC V₂ *
            embedAC ((kron2 1 proj0 + kron2 P₃_old.conjTranspose proj1) *
                     kron2 T.conjTranspose R.conjTranspose) * embedBC V₄ := by
            rw [hV₃_eq]
      _ = embedAC V₁ * embedBC V₂ *
            (embedAC (kron2 1 proj0 + kron2 P₃_old.conjTranspose proj1) *
             embedAC (kron2 T.conjTranspose R.conjTranspose)) * embedBC V₄ := by
            rw [embedAC_mul]
      _ = embedAC V₁ * embedBC V₂ *
            (embedAC (kron2 1 proj0 + kron2 P₃_old.conjTranspose proj1) *
             singleQubitLayer T.conjTranspose I₂ R.conjTranspose) * embedBC V₄ := by
            rw [embedAC_kron2]
      _ = embedAC V₁ * embedBC V₂ *
            (embedAC (kron2 1 proj0 + kron2 P₃_old.conjTranspose proj1) *
             (singleQubitLayer T.conjTranspose I₂ I₂ *
              singleQubitLayer I₂ I₂ R.conjTranspose)) * embedBC V₄ := by
            rw [h_split]
      -- Step 5: reassociate the inner triple, then apply h_thread.
      _ = embedAC V₁ * embedBC V₂ *
            (singleQubitLayer T.conjTranspose I₂ I₂ *
             embedAC (kron2 1 proj0 + kron2 P₃_new proj1) *
             singleQubitLayer I₂ I₂ R.conjTranspose) * embedBC V₄ := by
            rw [show embedAC (kron2 1 proj0 + kron2 P₃_old.conjTranspose proj1) *
                  (singleQubitLayer T.conjTranspose I₂ I₂ *
                   singleQubitLayer I₂ I₂ R.conjTranspose) =
                (embedAC (kron2 1 proj0 + kron2 P₃_old.conjTranspose proj1) *
                  singleQubitLayer T.conjTranspose I₂ I₂) *
                  singleQubitLayer I₂ I₂ R.conjTranspose from by noncomm_ring,
                h_thread]
      -- Step 6: reassociate to expose sQL T† at the front of the inner block.
      _ = embedAC V₁ * (embedBC V₂ * singleQubitLayer T.conjTranspose I₂ I₂) *
            embedAC (kron2 1 proj0 + kron2 P₃_new proj1) *
            (singleQubitLayer I₂ I₂ R.conjTranspose * embedBC V₄) := by noncomm_ring
      -- Step 7: commute embedBC V₂ and sQL T† I I (different qubits A vs BC).
      _ = embedAC V₁ * (singleQubitLayer T.conjTranspose I₂ I₂ * embedBC V₂) *
            embedAC (kron2 1 proj0 + kron2 P₃_new proj1) *
            (singleQubitLayer I₂ I₂ R.conjTranspose * embedBC V₄) := by
            rw [embedBC_comm_singleQubitLayer_A]
      -- Step 8: reassociate to absorb sQL T† I I into V₁ on the left.
      _ = (embedAC V₁ * singleQubitLayer T.conjTranspose I₂ I₂) * embedBC V₂ *
            embedAC (kron2 1 proj0 + kron2 P₃_new proj1) *
            (singleQubitLayer I₂ I₂ R.conjTranspose * embedBC V₄) := by noncomm_ring
      -- Step 9: absorb sQL T† I I into V₁; absorb sQL I I R† into V₄.
      _ = embedAC (V₁ * kron2 T.conjTranspose I₂) * embedBC V₂ *
            embedAC (kron2 1 proj0 + kron2 P₃_new proj1) *
            embedBC (kron2 I₂ R.conjTranspose * V₄) := by
            rw [embedAC_mul_singleQubitLayer, singleQubitLayer_one, mul_one,
                singleQubitLayer_mul_embedBC, singleQubitLayer_one, one_mul]

/-! ## PY24 Lemma 6.2 — Inner step for 6.3 / 6.4 Case 3

Paper p.224. Suppose |u₀| = |u₁| = 1. For 2-qubit unitaries U₁, W₂, V₃, U₄, if:
  · U_{1AC} · W_{2BC} · V_{3AC} · U_{4BC} = CC(Diag(u₀, u₁))
  · V₃ (|0⟩ ⊗ |0⟩) = |0⟩ ⊗ |0⟩
  · ∀ |x⟩_A: U_{1AC} (|x⟩ ⊗ |0⟩ ⊗ |0⟩) =
             U†_{4BC} V†_{3AC} (|x⟩ ⊗ |0⟩ ⊗ |0⟩)

then either u₀ = u₁, or u₀·u₁ = 1, or there exist 2-qubit unitaries
W₁, W₃, W₄ and a 1-qubit unitary P₃ such that:
  · U_{1AC} · W_{2BC} · V_{3AC} · U_{4BC}
        = W_{1AC} · W_{2BC} · W_{3AC} · W_{4BC}
  · W₃ = I ⊗ |0⟩⟨0| + P₃ ⊗ |1⟩⟨1|

(Paper proof: case analysis on V†_3 via Lemma 6.1; Case 1 uses A.10/A.12/A.19/4.4
and concludes u₀=u₁ ∨ u₀u₁=1 directly; Case 2 uses A.31; Case 3 uses A.25/A.17/4.4.) -/
theorem py24_lemma_6_2 (u₀ u₁ : ℂ) (hu₀ : Complex.normSq u₀ = 1) (hu₁ : Complex.normSq u₁ = 1)
    (U₁ W₂ V₃ U₄ : Mat4)
    (hU₁ : IsUnitary4 U₁) (hW₂ : IsUnitary4 W₂)
    (hV₃ : IsUnitary4 V₃) (hU₄ : IsUnitary4 U₄)
    (h_prod : embedAC U₁ * embedBC W₂ * embedAC V₃ * embedBC U₄ =
              Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁])
    (_h_V3_ket00 : Mat4.apply V₃ (tensor1_1 ket0_1 ket0_1) = tensor1_1 ket0_1 ket0_1)
    (h_U1_eq : ∀ x : Vec1, IsQubit1 x →
      Mat8.apply (embedAC U₁) (tensor1_2 x (tensor1_1 ket0_1 ket0_1)) =
      Mat8.apply (embedBC U₄.conjTranspose * embedAC V₃.conjTranspose)
        (tensor1_2 x (tensor1_1 ket0_1 ket0_1))) :
    u₀ = u₁ ∨ u₀ * u₁ = 1 ∨
    (∃ W₁ W₃ W₄ : Mat4, ∃ P₃ : Mat2,
      IsUnitary4 W₁ ∧ IsUnitary4 W₃ ∧ IsUnitary4 W₄ ∧ IsUnitary2 P₃ ∧
      embedAC U₁ * embedBC W₂ * embedAC V₃ * embedBC U₄ =
      embedAC W₁ * embedBC W₂ * embedAC W₃ * embedBC W₄ ∧
      W₃ = kron2 1 proj0 + kron2 P₃ proj1) := by
  -- Paper p.224 strategy: apply 6.1 to V₃† for trichotomic case analysis.
  rcases py24_lemma_6_1 V₃.conjTranspose (isUnitary4_conjTranspose hV₃) with
    ⟨xEnt, hxEnt_qubit, hV3dag_ent⟩ |
    ⟨ψ_r, hψ_r, h_V3dag_second_fixed⟩ |
    ⟨ψ_l, hψ_l, h_V3dag_first_fixed⟩
  · -- Case 1 (paper Case 1): ∃ xEnt with V₃†(xEnt⊗|0⟩) entangled.
    -- Black-box helper packages the A.10 + A.12 + A.19 + 4.4 chain.
    rcases case1_v3dag_entangled_concludes u₀ u₁ hu₀ hu₁ U₁ W₂ V₃ U₄
        hU₁ hW₂ hV₃ hU₄ h_prod h_U1_eq xEnt hxEnt_qubit hV3dag_ent with
      h_eq | h_prod_uu
    · exact Or.inl h_eq
    · exact Or.inr (Or.inl h_prod_uu)
  · -- Case 2 (Lean) = paper Case 2: V₃†(x⊗|0⟩) = z⊗ψ_r (second-factor fixed).
    -- A.31 directly gives W₁, W₃, W₄, P₃ with chain rewrite + W₃ controlled.
    obtain ⟨W₁, W₃, W₄, P₃, hW₁, hW₃, hW₄, hP₃, h_chain_W, hW₃_form⟩ :=
      py24_lemma_A_31 U₁ W₂ V₃ U₄ hU₁ hW₂ hV₃ hU₄
        ⟨ψ_r, hψ_r, h_V3dag_second_fixed⟩
    exact Or.inr (Or.inr ⟨W₁, W₃, W₄, P₃, hW₁, hW₃, hW₄, hP₃, h_chain_W, hW₃_form⟩)
  · -- Case 3 (Lean) = paper Case 3: V₃†(x⊗|0⟩) = ψ_l⊗z (first-factor fixed).
    -- Black-box helper packages the A.25 + A.22 + A.17 + 4.4 chain.
    rcases case3_v3dag_first_fixed_concludes u₀ u₁ hu₀ hu₁ U₁ W₂ V₃ U₄
        hU₁ hW₂ hV₃ hU₄ h_prod h_U1_eq ψ_l hψ_l h_V3dag_first_fixed with
      h_eq | h_prod_uu
    · exact Or.inl h_eq
    · exact Or.inr (Or.inl h_prod_uu)

/-! ## PY24 Lemma A.29 — Chain action analog of A.28 with V₂ fixing |0⟩⊗|0⟩

Paper p.255-256. Symmetric to A.28: instead of V₃ fixing |0⟩⊗|0⟩ (BC),
here V₂ fixes |0⟩⊗|0⟩ (BC). Conclusion: ∀ x : Vec1, the chain's "front
half" (V₁_AC) and "back half" (V₃†_AC · V₄†_BC) agree on (x⊗|0⟩⊗|0⟩).

**Strategy** (from PY24 paper p.256): use S_AB conjugation + dagger
to reduce A.29 to A.28. Specifically:
1. From V₂(|0⟩|0⟩)=|0⟩|0⟩ + V₂ unitary → V₂†(|0⟩|0⟩)=|0⟩|0⟩.
2. Take dagger of chain: V₄†_BC V₃†_AC V₂†_BC V₁†_AC = D†.
3. S_AB-conjugate all factors: V₄†_AC V₃†_BC V₂†_AC V₁†_BC = S_AB·D†·S_AB.
4. Apply A.28 to this chain with V₃' = V₂† fixing |0⟩|0⟩ + h_D' fix.
   Get eq (A.7): V₄†_AC V₃†_BC (|0⟩⊗x⊗|0⟩) = V₁_BC (|0⟩⊗x⊗|0⟩).
5. S_AB-conjugate eq (A.7) to recover A.29's form.

The h_D' (4-dim ket0_A subspace fix for S_AB·D†·S_AB) requires D to
have a structure compatible with both subspace fixes. For our caller
(6.3 + assemble_Q_rotated), D = Matrix.diagonal ![1,1,1,1,1,1,u₀,u₁]
has both 2-dim {x⊗|0⟩⊗|0⟩} fix AND 4-dim {ket0_A ⊗ y} fix automatically
(since first 6 diagonal entries are 1 and the form is S_AB-symmetric).

Body: ~110 Lean lines implementing the 5-step paper proof above
(closed iter 358). -/
lemma py24_lemma_A_29
    {V₁ V₂ V₃ V₄ : Mat4}
    (_hV₁ : IsUnitary4 V₁) (hV₂ : IsUnitary4 V₂)
    (_hV₃ : IsUnitary4 V₃) (_hV₄ : IsUnitary4 V₄)
    {u₀ u₁ : ℂ}
    (_h_chain : embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄ =
                Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁])
    (h_V2_ket00 : Mat4.apply V₂ (tensor1_1 ket0_1 ket0_1) = tensor1_1 ket0_1 ket0_1)
    (_x : Vec1) :
    Mat8.apply (embedAC V₁)
      (tensor1_2 _x (tensor1_1 ket0_1 ket0_1)) =
    Mat8.apply (embedBC V₄.conjTranspose * embedAC V₃.conjTranspose)
      (tensor1_2 _x (tensor1_1 ket0_1 ket0_1)) := by
  -- Local abbreviation: D := Matrix.diagonal ![1,1,1,1,1,1,u₀,u₁].
  set D : Mat8 := Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] with _hD_def
  -- Step 1: derive V₂†(|0⟩⊗|0⟩) = |0⟩⊗|0⟩.
  -- From V₂(|0⟩|0⟩)=|0⟩|0⟩ + V₂† V₂ = 1 (hV₂):
  --   V₂† V₂ (|0⟩|0⟩) = V₂† (|0⟩|0⟩)  ← apply V₂† to both sides
  --   1 · (|0⟩|0⟩)    = V₂† (|0⟩|0⟩)  ← V₂† V₂ = 1
  --   |0⟩|0⟩          = V₂† (|0⟩|0⟩)
  have hV2_dag_ket00 :
      Mat4.apply V₂.conjTranspose (tensor1_1 ket0_1 ket0_1) =
      tensor1_1 ket0_1 ket0_1 := by
    have step : Mat4.apply (V₂.conjTranspose * V₂) (tensor1_1 ket0_1 ket0_1) =
                Mat4.apply V₂.conjTranspose (tensor1_1 ket0_1 ket0_1) := by
      rw [Mat4.apply_mul, h_V2_ket00]
    rw [hV₂, Mat4.apply_one] at step
    exact step.symm
  -- Step 2: take dagger of chain.
  -- (V₁_AC V₂_BC V₃_AC V₄_BC)† = V₄†_BC V₃†_AC V₂†_BC V₁†_AC = D†.
  have h_chain_dag :
      embedBC V₄.conjTranspose * embedAC V₃.conjTranspose *
      embedBC V₂.conjTranspose * embedAC V₁.conjTranspose = D.conjTranspose := by
    have h := congrArg Matrix.conjTranspose _h_chain
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        embedBC_conjTranspose, embedAC_conjTranspose, embedBC_conjTranspose,
        embedAC_conjTranspose] at h
    rw [← h]; noncomm_ring
  -- Step 3: SWAP_AB conjugate the dagger chain. This swaps embedBC ↔ embedAC.
  have h_chain_swap :
      embedAC V₄.conjTranspose * embedBC V₃.conjTranspose *
      embedAC V₂.conjTranspose * embedBC V₁.conjTranspose =
      SWAP_AB * D.conjTranspose * SWAP_AB := by
    -- Rewrite each embedAC/BC factor as SWAP_AB-conjugated version of opposite type.
    rw [show embedAC V₄.conjTranspose =
         SWAP_AB * embedBC V₄.conjTranspose * SWAP_AB
         from (swap_ab_embedBC (V := V₄.conjTranspose)).symm,
        show embedBC V₃.conjTranspose =
         SWAP_AB * embedAC V₃.conjTranspose * SWAP_AB
         from (swap_ab_embedAC (V := V₃.conjTranspose)).symm,
        show embedAC V₂.conjTranspose =
         SWAP_AB * embedBC V₂.conjTranspose * SWAP_AB
         from (swap_ab_embedBC (V := V₂.conjTranspose)).symm,
        show embedBC V₁.conjTranspose =
         SWAP_AB * embedAC V₁.conjTranspose * SWAP_AB
         from (swap_ab_embedAC (V := V₁.conjTranspose)).symm]
    -- Telescope: (SWAP_AB·A·SWAP_AB)·(SWAP_AB·B·SWAP_AB)·... = SWAP_AB·A·B·...·SWAP_AB.
    have telescope :
        (SWAP_AB * embedBC V₄.conjTranspose * SWAP_AB) *
        (SWAP_AB * embedAC V₃.conjTranspose * SWAP_AB) *
        (SWAP_AB * embedBC V₂.conjTranspose * SWAP_AB) *
        (SWAP_AB * embedAC V₁.conjTranspose * SWAP_AB) =
        SWAP_AB *
          (embedBC V₄.conjTranspose * embedAC V₃.conjTranspose *
           embedBC V₂.conjTranspose * embedAC V₁.conjTranspose) * SWAP_AB := by
      calc (SWAP_AB * embedBC V₄.conjTranspose * SWAP_AB) *
           (SWAP_AB * embedAC V₃.conjTranspose * SWAP_AB) *
           (SWAP_AB * embedBC V₂.conjTranspose * SWAP_AB) *
           (SWAP_AB * embedAC V₁.conjTranspose * SWAP_AB)
          = SWAP_AB * embedBC V₄.conjTranspose * (SWAP_AB * SWAP_AB) *
              embedAC V₃.conjTranspose * (SWAP_AB * SWAP_AB) *
              embedBC V₂.conjTranspose * (SWAP_AB * SWAP_AB) *
              embedAC V₁.conjTranspose * SWAP_AB := by noncomm_ring
        _ = SWAP_AB * embedBC V₄.conjTranspose * 1 *
              embedAC V₃.conjTranspose * 1 *
              embedBC V₂.conjTranspose * 1 *
              embedAC V₁.conjTranspose * SWAP_AB := by simp only [SWAP_AB_sq]
        _ = SWAP_AB *
              (embedBC V₄.conjTranspose * embedAC V₃.conjTranspose *
               embedBC V₂.conjTranspose * embedAC V₁.conjTranspose) * SWAP_AB := by
            noncomm_ring
    rw [telescope, h_chain_dag]
  -- Step 4 prep: D.conjTranspose fixes the 4-dim {ket0_A ⊗ y} subspace.
  -- D = Matrix.diagonal ![1,1,1,1,1,1,u₀,u₁], so
  -- D† = Matrix.diagonal ![1,1,1,1,1,1,star u₀, star u₁].
  -- For y ∈ Vec2, tensor1_2 ket0_1 y has support only on indices 0-3 (where D†'s
  -- diagonal entries are 1), so D† fixes (ket0⊗y).
  have hD_conj_fixes_ket0 : ∀ y : Vec2,
      Mat8.apply D.conjTranspose (tensor1_2 ket0_1 y) = tensor1_2 ket0_1 y := by
    intro y
    funext i
    fin_cases i <;>
      simp [Mat8.apply, _hD_def, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
            tensor1_2, ket0_1, Fin.sum_univ_eight]
  -- Show: SWAP_AB · D† · SWAP_AB = D† (D† commutes with S_AB conjugation since
  -- D's diagonal is S_AB-permutation-invariant: π fixes 6, 7 and the first 6
  -- entries are all 1).
  have hD_dag_swap : SWAP_AB * D.conjTranspose * SWAP_AB = D.conjTranspose := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SWAP_AB, swap_ab_perm, _hD_def, Matrix.conjTranspose_apply,
            Matrix.diagonal_apply, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_eight]
  -- Combine: h_D' : ∀ y, (SWAP_AB · D† · SWAP_AB)(ket0⊗y) = ket0⊗y.
  have h_D' : ∀ y : Vec2,
      Mat8.apply (SWAP_AB * D.conjTranspose * SWAP_AB) (tensor1_2 ket0_1 y) =
      tensor1_2 ket0_1 y := by
    intro y
    rw [hD_dag_swap]
    exact hD_conj_fixes_ket0 y
  -- Step 4: apply A.28 to the SWAP-conjugated chain (V₁'=V₄†, V₂'=V₃†, V₃'=V₂†, V₄'=V₁†).
  -- Returns: V₁'_AC · V₂'_BC (ket0⊗x⊗ket0) = (V₄')†_BC (ket0⊗x⊗ket0).
  -- I.e., embedAC V₄† · embedBC V₃† (ket0⊗x⊗ket0) = embedBC V₁ (ket0⊗x⊗ket0).
  have h_eq_A7 : ∀ x : Vec1,
      Mat8.apply (embedAC V₄.conjTranspose * embedBC V₃.conjTranspose)
        (tensor1_2 ket0_1 (tensor1_1 x ket0_1)) =
      Mat8.apply (embedBC V₁) (tensor1_2 ket0_1 (tensor1_1 x ket0_1)) := by
    intro x
    have h := py24_lemma_A_28
      (V₁ := V₄.conjTranspose) (V₂ := V₃.conjTranspose)
      (V₃ := V₂.conjTranspose) (V₄ := V₁.conjTranspose)
      (D := SWAP_AB * D.conjTranspose * SWAP_AB)
      (isUnitary4_conjTranspose _hV₁) h_chain_swap hV2_dag_ket00 h_D' x
    rw [Matrix.conjTranspose_conjTranspose] at h
    exact h
  -- Step 5: SWAP_AB-conjugate eq A.7 to recover A.29's form.
  -- Strategy: use suffices to reduce goal to: SWAP_AB · LHS = SWAP_AB · RHS.
  suffices h : Mat8.apply SWAP_AB
                  (Mat8.apply (embedAC V₁) (tensor1_2 _x (tensor1_1 ket0_1 ket0_1))) =
               Mat8.apply SWAP_AB
                  (Mat8.apply (embedBC V₄.conjTranspose * embedAC V₃.conjTranspose)
                    (tensor1_2 _x (tensor1_1 ket0_1 ket0_1))) by
    have key : ∀ v : Vec3, Mat8.apply SWAP_AB (Mat8.apply SWAP_AB v) = v := fun v => by
      rw [← Mat8.apply_mul, SWAP_AB_sq, Mat8.apply_one]
    have := congrArg (Mat8.apply SWAP_AB) h
    rw [key, key] at this
    exact this
  -- Now reduce SWAP_AB · LHS and SWAP_AB · RHS using commutation lemmas.
  have h_swap_AC_V1 : SWAP_AB * embedAC V₁ = embedBC V₁ * SWAP_AB := by
    calc SWAP_AB * embedAC V₁
        = SWAP_AB * embedAC V₁ * (SWAP_AB * SWAP_AB) := by rw [SWAP_AB_sq, mul_one]
      _ = (SWAP_AB * embedAC V₁ * SWAP_AB) * SWAP_AB := by noncomm_ring
      _ = embedBC V₁ * SWAP_AB := by rw [swap_ab_embedAC]
  have h_swap_BC_V4 : SWAP_AB * embedBC V₄.conjTranspose =
                      embedAC V₄.conjTranspose * SWAP_AB := by
    calc SWAP_AB * embedBC V₄.conjTranspose
        = SWAP_AB * embedBC V₄.conjTranspose * (SWAP_AB * SWAP_AB) := by
            rw [SWAP_AB_sq, mul_one]
      _ = (SWAP_AB * embedBC V₄.conjTranspose * SWAP_AB) * SWAP_AB := by noncomm_ring
      _ = embedAC V₄.conjTranspose * SWAP_AB := by rw [swap_ab_embedBC]
  have h_swap_AC_V3 : SWAP_AB * embedAC V₃.conjTranspose =
                      embedBC V₃.conjTranspose * SWAP_AB := by
    calc SWAP_AB * embedAC V₃.conjTranspose
        = SWAP_AB * embedAC V₃.conjTranspose * (SWAP_AB * SWAP_AB) := by
            rw [SWAP_AB_sq, mul_one]
      _ = (SWAP_AB * embedAC V₃.conjTranspose * SWAP_AB) * SWAP_AB := by noncomm_ring
      _ = embedBC V₃.conjTranspose * SWAP_AB := by rw [swap_ab_embedAC]
  have h_swap_chain : SWAP_AB * (embedBC V₄.conjTranspose * embedAC V₃.conjTranspose) =
                      (embedAC V₄.conjTranspose * embedBC V₃.conjTranspose) * SWAP_AB := by
    rw [← mul_assoc, h_swap_BC_V4, mul_assoc, h_swap_AC_V3, ← mul_assoc]
  -- Reduce LHS: SWAP_AB · embedAC V₁ · v = embedBC V₁ · SWAP_AB · v = embedBC V₁ · (|0⟩⊗x⊗|0⟩).
  rw [← Mat8.apply_mul, h_swap_AC_V1, Mat8.apply_mul, swap_ab_apply_xtensor_00]
  -- Reduce RHS: similar with h_swap_chain.
  rw [← Mat8.apply_mul, h_swap_chain, Mat8.apply_mul, swap_ab_apply_xtensor_00]
  -- Now: LHS = embedBC V₁ (|0⟩⊗x⊗|0⟩), RHS = (embedAC V₄† · embedBC V₃†)(|0⟩⊗x⊗|0⟩).
  -- By h_eq_A7 _x reversed.
  exact (h_eq_A7 _x).symm

/-! ## PY24 Lemma A.26 — Constant second-factor extraction

Paper p.227. If a 2-qubit unitary V satisfies `∀ z : ∃ w : V(z⊗|0⟩) = z⊗w(z)`
(every input z⊗|0⟩ maps to a state with first factor z), then there
exists a FIXED β such that `∀ z : V(z⊗|0⟩) = z⊗β`. So w(z) is constant
in z. Used by `assemble_Q_rotated` to construct the |β⟩ for Q.

Proof: take w₀ = w(ket0), w₁ = w(ket1). Apply h to the |+⟩ superposition
state z_plus = (1/√2)(ket0+ket1) to get w_z. By V's linearity,
V(z_plus⊗|0⟩) = (1/√2)·(ket0⊗w₀) + (1/√2)·(ket1⊗w₁), but also
= z_plus⊗w_z. Component-wise comparison gives w₀ = w_z = w₁.
Final witness: β = w₀, with `IsQubit1 w₀` from V unitary preserving
norms; the universal-z property follows from V's linearity expanded
in the {ket0, ket1} basis. -/
lemma py24_lemma_A_26 (V : Mat4) (hV : IsUnitary4 V)
    (h : ∀ z : Vec1, IsQubit1 z →
      ∃ w : Vec1, Mat4.apply V (tensor1_1 z ket0_1) = tensor1_1 z w) :
    ∃ β : Vec1, IsQubit1 β ∧ ∀ z : Vec1, IsQubit1 z →
      Mat4.apply V (tensor1_1 z ket0_1) = tensor1_1 z β := by
  -- Pick β := w₀ where w₀ = w(ket0_1).
  obtain ⟨w₀, h_w0⟩ := h ket0_1 IsQubit1_ket0
  obtain ⟨w₁, h_w1⟩ := h ket1_1 IsQubit1_ket1
  -- Define the superposition state z_+ = (1/√2)(ket0 + ket1).
  let z_plus : Vec1 := fun i => ((Real.sqrt 2)⁻¹ : ℝ)
  have hz_plus_qubit : IsQubit1 z_plus := by
    -- normSqVec1 z_plus = |1/√2|² + |1/√2|² = 1/2 + 1/2 = 1.
    change ∑ i : Fin 2, Complex.normSq (z_plus i) = 1
    simp [z_plus]
  -- Apply h to z_plus to get w_z.
  obtain ⟨w_z, h_wz⟩ := h z_plus hz_plus_qubit
  -- Decompose tensor1_1 z_plus ket0_1 as a sum of scaled basis tensors.
  have h_z_decomp : tensor1_1 z_plus ket0_1
                  = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • tensor1_1 ket0_1 ket0_1 +
                    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • tensor1_1 ket1_1 ket0_1 := by
    funext k
    fin_cases k <;>
      simp [tensor1_1, z_plus, ket0_1, ket1_1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  -- Apply V's linearity to expand Mat4.apply V (tensor1_1 z_plus ket0_1).
  have h_apply_z : Mat4.apply V (tensor1_1 z_plus ket0_1) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • tensor1_1 ket0_1 w₀ +
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • tensor1_1 ket1_1 w₁ := by
    rw [h_z_decomp, Mat4.apply_add, Mat4.apply_smul, Mat4.apply_smul, h_w0, h_w1]
  -- Combine with h_wz to get the key identity.
  have h_eq : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • tensor1_1 ket0_1 w₀ +
              (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • tensor1_1 ket1_1 w₁ =
              tensor1_1 z_plus w_z := by
    rw [← h_apply_z]; exact h_wz
  -- Extract w₀ = w_z component-wise from h_eq evaluated at indices 0, 1.
  have h_w0_eq_wz : w₀ = w_z := by
    funext i
    fin_cases i
    · -- i = 0: use h_eq at Fin 4 index 0; simp cancels the (1/√2) prefactor.
      have h0 := congrFun h_eq 0
      simp [tensor1_1, z_plus, ket0_1, ket1_1, Pi.add_apply, Pi.smul_apply,
            smul_eq_mul] at h0
      exact h0
    · -- i = 1: use h_eq at Fin 4 index 1.
      have h1 := congrFun h_eq 1
      simp [tensor1_1, z_plus, ket0_1, ket1_1, Pi.add_apply, Pi.smul_apply,
            smul_eq_mul] at h1
      exact h1
  -- Extract w₁ = w_z component-wise from h_eq evaluated at indices 2, 3.
  have h_w1_eq_wz : w₁ = w_z := by
    funext i
    fin_cases i
    · -- i = 0: use h_eq at Fin 4 index 2.
      have h2 := congrFun h_eq 2
      simp [tensor1_1, z_plus, ket0_1, ket1_1, Pi.add_apply, Pi.smul_apply,
            smul_eq_mul] at h2
      exact h2
    · -- i = 1: use h_eq at Fin 4 index 3.
      have h3 := congrFun h_eq 3
      simp [tensor1_1, z_plus, ket0_1, ket1_1, Pi.add_apply, Pi.smul_apply,
            smul_eq_mul] at h3
      exact h3
  have h_w0_eq_w1 : w₀ = w₁ := h_w0_eq_wz.trans h_w1_eq_wz.symm
  -- Build IsQubit1 w₀ from V unitary preserving normSq.
  have hw0_qubit : IsQubit1 w₀ := by
    have h_qubit2 : IsQubit2 (Mat4.apply V (tensor1_1 ket0_1 ket0_1)) :=
      IsQubit2_apply_unitary hV (IsQubit2_tensor1_1 IsQubit1_ket0 IsQubit1_ket0)
    rw [h_w0] at h_qubit2
    -- h_qubit2 : IsQubit2 (tensor1_1 ket0_1 w₀)
    -- normSqVec2 (tensor1_1 ket0_1 w₀) = normSqVec1 ket0 · normSqVec1 w₀ = 1 · normSqVec1 w₀
    unfold IsQubit2 at h_qubit2
    rw [normSqVec2_tensor1_1] at h_qubit2
    have hk0 : normSqVec1 ket0_1 = 1 := IsQubit1_ket0
    rw [hk0, one_mul] at h_qubit2
    exact h_qubit2
  -- Final witness: β = w₀; the universal-z property uses linearity + w₀ = w₁.
  refine ⟨w₀, hw0_qubit, ?_⟩
  intro z _hz
  obtain ⟨w_y, h_wy⟩ := h z _hz
  -- By the same argument: w_y = w₀.
  -- Compute V(z⊗|0⟩) two ways: via h_wy gives z⊗w_y; via linearity gives
  -- z[0]·ket0⊗w₀ + z[1]·ket1⊗w₁ = z[0]·ket0⊗w₀ + z[1]·ket1⊗w₀ [w₁=w₀]
  -- = z⊗w₀. So z⊗w_y = z⊗w₀; if z ≠ 0, w_y = w₀.
  -- Direct: prove V(z⊗|0⟩) = z⊗w₀ via linearity, then equate with h_wy.
  have h_z_decomp_gen : tensor1_1 z ket0_1 = z 0 • tensor1_1 ket0_1 ket0_1 +
                       z 1 • tensor1_1 ket1_1 ket0_1 := by
    funext k
    fin_cases k <;>
      simp [tensor1_1, ket0_1, ket1_1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h_apply_gen : Mat4.apply V (tensor1_1 z ket0_1) = tensor1_1 z w₀ := by
    rw [h_z_decomp_gen, Mat4.apply_add, Mat4.apply_smul, Mat4.apply_smul,
        h_w0, h_w1, h_w0_eq_w1]
    -- Now: z[0]·ket0⊗w₁ + z[1]·ket1⊗w₁ = tensor1_1 z w₁? With w₁ = w₀.
    funext k
    fin_cases k <;>
      simp [tensor1_1, ket0_1, ket1_1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [h_apply_gen]

/-! ## PY24 Lemma A.18 — Reverse of `controlled_C_apply_xtensor0`

Paper p.227-228 invokes A.18 to derive `W` controlled from `W·(x⊗|0⟩) = x⊗|0⟩`.
If a 2-qubit unitary U satisfies `U(x⊗|0⟩) = x⊗|0⟩` for all unit qubits x,
then `U = I⊗|0⟩⟨0| + P⊗|1⟩⟨1|` for some 1-qubit unitary P (= block-diag-
second form). Note: this is the converse of `controlled_C_apply_xtensor0`
(which is the forward direction: controlled form ⇒ fixes states).

Proof: take T = 1, R = 1, ψ = ket0_1 in `exists_P2_W2_eq_block_diag_second`.
The hypothesis `_hAct` (only on qubits) is extended to all of Vec1 via
linearity in the first factor (`vec1_basis_decomp` + `Mat4.apply_smul`/
`Mat4.apply_add`), then the helper directly delivers P satisfying
`U = kron2 1 proj0 + kron2 P proj1`. P unitary follows from
`P2_unitary_from_W_unitary`. -/
lemma py24_lemma_A_18 (U : Mat4) (hU : IsUnitary4 U)
    (hAct : ∀ x : Vec1, IsQubit1 x →
      Mat4.apply U (tensor1_1 x ket0_1) = tensor1_1 x ket0_1) :
    ∃ P : Mat2, IsUnitary2 P ∧ U = kron2 1 proj0 + kron2 P proj1 := by
  -- Step 1: extend hAct from qubits to all of Vec1 via linearity.
  have hAll : ∀ y : Vec1, Mat4.apply U (tensor1_1 y ket0_1) = tensor1_1 y ket0_1 := by
    intro y
    have hy_decomp : y = y 0 • ket0_1 + y 1 • ket1_1 := vec1_basis_decomp y
    rw [hy_decomp]
    rw [tensor1_1_add_left, tensor1_1_smul_left, tensor1_1_smul_left,
        Mat4.apply_add, Mat4.apply_smul, Mat4.apply_smul,
        hAct ket0_1 IsQubit1_ket0, hAct ket1_1 IsQubit1_ket1]
  -- Step 2: massage hAll into form expected by `exists_P2_W2_eq_block_diag_second`
  -- (with T = 1, ψ = ket0_1).
  have hV : ∀ y : Vec1, Mat4.apply U (tensor1_1 y ket0_1)
                      = tensor1_1 (Mat2.apply 1 y) ket0_1 := by
    intro y; rw [Mat2.apply_one]; exact hAll y
  -- Step 3: invoke the helper with T = R = 1, ψ = ket0_1.
  obtain ⟨P, hP_eq⟩ := exists_P2_W2_eq_block_diag_second
    (V₂ := U) (T := 1) (R := 1) (ψ := ket0_1)
    hU isUnitary2_one isUnitary2_one (Mat2.apply_one ket0_1) hV
  -- Step 4: simplify LHS `kron2 1† 1† * U = U`.
  rw [Matrix.conjTranspose_one, kron2_one_one_eq_one, one_mul] at hP_eq
  -- Step 5: P is unitary because U is unitary and U = kron2 1 proj0 + kron2 P proj1.
  have hUnit : IsUnitary4 (kron2 1 proj0 + kron2 P proj1) := hP_eq ▸ hU
  exact ⟨P, P2_unitary_from_W_unitary hUnit, hP_eq⟩

/-! ## Helper: assemble 6.3's Q-rotated W_i forms from 6.2's W_i form output

Paper p.227-228. After 6.3 invokes A.30 + A.29 + 6.2 and reaches 6.2's
third disjunct (chain rewrite to W₁_b, W₂_a, W₃_b, W₄_b with W₃_b
controlled), paper assembles 6.3's third disjunct (W_i in Q-rotated
forms) via the chain:
  - From W₃_b W₄_b's action on (|0⟩⊗|z⟩⊗|0⟩) and the chain identity,
    derive `∀ |z⟩: W₃_b W₄_b (|0⟩⊗|z⟩⊗|0⟩) = (|0⟩⊗Q|z⟩⊗|0⟩)` for some
    1-qubit Q (via Lemma A.18 missing).
  - Use Lemma A.22 (missing) to derive `W₄†(|z⟩⊗|0⟩) = |z⟩⊗β` for
    some β = Q|0⟩.
  - Use Lemma A.26 (missing) to build Q as a unitary.
  - Propagate Q backward through W₁_b, W₂_a to obtain final
    Q-rotated W_i forms.
Body: `sorry` — captures the entire ~150-line construction. -/
private lemma assemble_Q_rotated_from_6_2_W_i_form
    (u₀ u₁ : ℂ) (_hu₀ : Complex.normSq u₀ = 1) (_hu₁ : Complex.normSq u₁ = 1)
    (U₁_a W₂_a V₃ U₄_a : Mat4)
    (_hU₁_a : IsUnitary4 U₁_a) (hW₂_a : IsUnitary4 W₂_a)
    (_hV₃ : IsUnitary4 V₃) (_hU₄_a : IsUnitary4 U₄_a)
    (P₂_a : Mat2) (hP₂_a : IsUnitary2 P₂_a)
    (hW₂_a_form : W₂_a = kron2 1 proj0 + kron2 P₂_a proj1)
    (h_chain_a : embedAC U₁_a * embedBC W₂_a * embedAC V₃ * embedBC U₄_a =
                 Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁])
    (_h_V3_ket00 : Mat4.apply V₃ (tensor1_1 ket0_1 ket0_1) = tensor1_1 ket0_1 ket0_1)
    (W₁_b W₃_b W₄_b : Mat4) (P₃_b : Mat2)
    (hW₁_b : IsUnitary4 W₁_b) (hW₃_b : IsUnitary4 W₃_b)
    (hW₄_b : IsUnitary4 W₄_b) (hP₃_b : IsUnitary2 P₃_b)
    (h_chain_b : embedAC U₁_a * embedBC W₂_a * embedAC V₃ * embedBC U₄_a =
                 embedAC W₁_b * embedBC W₂_a * embedAC W₃_b * embedBC W₄_b)
    (hW₃_b_form : W₃_b = kron2 1 proj0 + kron2 P₃_b proj1) :
    ∃ W₁ W₂ W₃ W₄ : Mat4, ∃ P₁ P₂ P₃ P₄ Q : Mat2,
      IsUnitary4 W₁ ∧ IsUnitary4 W₂ ∧ IsUnitary4 W₃ ∧ IsUnitary4 W₄ ∧
      IsUnitary2 P₁ ∧ IsUnitary2 P₂ ∧ IsUnitary2 P₃ ∧ IsUnitary2 P₄ ∧ IsUnitary2 Q ∧
      embedAC W₁ * embedBC W₂ * embedAC W₃ * embedBC W₄ =
        Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] ∧
      W₁ = kron2 1 (Q * proj0) + kron2 P₁ (Q * proj1) ∧
      W₂ = kron2 1 proj0 + kron2 P₂ proj1 ∧
      W₃ = kron2 1 proj0 + kron2 P₃ proj1 ∧
      W₄ = kron2 1 (proj0 * Q.conjTranspose) + kron2 P₄ (proj1 * Q.conjTranspose) := by
  -- Step 1: derive eq 12 via A.28 applied to chain_b.
  -- Need: chain_b_eq_D, W₃_b|00⟩=|00⟩, D fixes ket0⊗y.
  have h_chain_b_eq_D :
      embedAC W₁_b * embedBC W₂_a * embedAC W₃_b * embedBC W₄_b =
      Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] := h_chain_b ▸ h_chain_a
  have h_W3_b_ket00 :
      Mat4.apply W₃_b (tensor1_1 ket0_1 ket0_1) = tensor1_1 ket0_1 ket0_1 := by
    rw [hW₃_b_form]; exact controlled_C_apply_xtensor0 P₃_b ket0_1
  have h_D_fixes_ket0_y : ∀ y : Vec2,
      Mat8.apply (Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] : Mat8)
        (tensor1_2 ket0_1 y) = tensor1_2 ket0_1 y := by
    intro y
    funext i
    change ∑ j : Fin 8, (Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] : Mat8) i j *
          tensor1_2 ket0_1 y j = tensor1_2 ket0_1 y i
    rw [Finset.sum_eq_single i]
    · rw [Matrix.diagonal_apply_eq]
      fin_cases i <;> simp [tensor1_2, ket0_1]
    · intro j _ hj_ne
      rw [Matrix.diagonal_apply_ne _ hj_ne.symm, zero_mul]
    · intro h_in; exact (h_in (Finset.mem_univ i)).elim
  -- Apply A.28 to (W₁_b, W₂_a, W₃_b, W₄_b): get eq 12.
  have h_eq12 : ∀ z : Vec1,
      Mat8.apply (embedAC W₁_b * embedBC W₂_a)
        (tensor1_2 ket0_1 (tensor1_1 z ket0_1)) =
      Mat8.apply (embedBC W₄_b.conjTranspose)
        (tensor1_2 ket0_1 (tensor1_1 z ket0_1)) :=
    fun z => py24_lemma_A_28 hW₄_b h_chain_b_eq_D h_W3_b_ket00 h_D_fixes_ket0_y z
  -- Step 2: combine eq 12 with W₂_a controlled (W₂_a fixes z⊗ket0) to drop W₂_a.
  have h_W2a_apply : ∀ z : Vec1,
      Mat4.apply W₂_a (tensor1_1 z ket0_1) = tensor1_1 z ket0_1 := by
    intro z
    rw [hW₂_a_form]
    exact kron_block_diag_second_apply_x_ket0 P₂_a z
  have h_eq_W1b : ∀ z : Vec1,
      Mat8.apply (embedAC W₁_b) (tensor1_2 ket0_1 (tensor1_1 z ket0_1)) =
      Mat8.apply (embedBC W₄_b.conjTranspose) (tensor1_2 ket0_1 (tensor1_1 z ket0_1)) := by
    intro z
    have h12 := h_eq12 z
    rw [Mat8.apply_mul, embedBC_apply_tensor1_2, h_W2a_apply z] at h12
    exact h12
  -- Step 3: apply A.22 to extract w_z with W₄_b†(z⊗ket0) = z⊗w_z.
  have h_W4b_dag_factors : ∀ z : Vec1, IsQubit1 z →
      ∃ w : Vec1, Mat4.apply W₄_b.conjTranspose (tensor1_1 z ket0_1) = tensor1_1 z w := by
    intro z hz
    -- Phrase h_eq_W1b z in A.22's form: LHS = ψ_A ⊗ φ_BC where ψ=ket0, φ=W₄†(z⊗ket0).
    have h_apply : Mat8.apply (embedAC W₁_b) (tensor1_2 ket0_1 (tensor1_1 z ket0_1)) =
                   tensor1_2 ket0_1
                     (Mat4.apply W₄_b.conjTranspose (tensor1_1 z ket0_1)) := by
      rw [h_eq_W1b z, embedBC_apply_tensor1_2]
    have hzket0 : IsQubit2 (tensor1_1 z ket0_1) :=
      IsQubit2_tensor1_1 hz IsQubit1_ket0
    have hW4dag_unit : IsUnitary4 W₄_b.conjTranspose :=
      isUnitary4_conjTranspose hW₄_b
    have hφ : IsQubit2 (Mat4.apply W₄_b.conjTranspose (tensor1_1 z ket0_1)) :=
      IsQubit2_apply_unitary hW4dag_unit hzket0
    exact py24_lemma_A_22 hW₁_b IsQubit1_ket0 hz IsQubit1_ket0 IsQubit1_ket0
      hφ h_apply
  -- Step 4: apply A.26 to get fixed β with ∀z qubit: W₄_b†(z⊗|0⟩) = z⊗β.
  obtain ⟨β, hβ_qubit, h_eq13⟩ :=
    py24_lemma_A_26 W₄_b.conjTranspose (isUnitary4_conjTranspose hW₄_b)
      h_W4b_dag_factors
  -- Step 5: construct Q = unitary_first_column β. Q unitary, Q|0⟩ = β.
  let Q : Mat2 := unitary_first_column β
  have hQ_unit : IsUnitary2 Q := unitary_first_column_isUnitary hβ_qubit
  have hQ_ket0 : Mat2.apply Q ket0_1 = β := unitary_first_column_apply_ket0 β
  -- Step 6: derive (W₄_b * kron2 1 Q)(z⊗|0⟩) = z⊗|0⟩ for all z qubit.
  -- Bridge: kron2 1 Q (z⊗|0⟩) = z⊗β; then W₄_b(z⊗β) = z⊗|0⟩ via h_eq13 inverted.
  have hW4b_W4bdag : W₄_b * W₄_b.conjTranspose = (1 : Mat4) := mul_eq_one_comm.mp hW₄_b
  have h_W4Q_fixes : ∀ z : Vec1, IsQubit1 z →
      Mat4.apply (W₄_b * kron2 1 Q) (tensor1_1 z ket0_1) = tensor1_1 z ket0_1 := by
    intro z hz
    rw [Mat4.apply_mul, kron2_apply_tensor1_1, Mat2.apply_one, hQ_ket0]
    -- goal: Mat4.apply W₄_b (tensor1_1 z β) = tensor1_1 z ket0_1
    rw [show tensor1_1 z β = Mat4.apply W₄_b.conjTranspose (tensor1_1 z ket0_1) from
         (h_eq13 z hz).symm,
        ← Mat4.apply_mul, hW4b_W4bdag, Mat4.apply_one]
  -- Step 7: apply A.18 to (W₄_b * kron2 1 Q) → P₄ + form; recover W₄_b form.
  have hkron2_1Q_unit : IsUnitary4 (kron2 1 Q) :=
    isUnitary4_kron2 isUnitary2_one hQ_unit
  have hW4Q_unit : IsUnitary4 (W₄_b * kron2 1 Q) :=
    isUnitary4_mul hW₄_b hkron2_1Q_unit
  obtain ⟨P₄, hP₄_unit, hW4Q_form⟩ :=
    py24_lemma_A_18 (W₄_b * kron2 1 Q) hW4Q_unit h_W4Q_fixes
  -- Recover W₄_b form by right-multiplying by (kron2 1 Q)†.
  have hkron2_1Q_inv : kron2 (1 : Mat2) Q * kron2 1 Q.conjTranspose = (1 : Mat4) := by
    rw [kron2_mul, mul_one, mul_eq_one_comm.mp hQ_unit]
    exact kron2_one_one_eq_one
  have hW4_b_form :
      W₄_b = kron2 1 (proj0 * Q.conjTranspose) + kron2 P₄ (proj1 * Q.conjTranspose) := by
    have step1 : W₄_b = W₄_b * kron2 1 Q * kron2 1 Q.conjTranspose := by
      rw [mul_assoc, hkron2_1Q_inv, mul_one]
    rw [step1, hW4Q_form, add_mul, kron2_mul, kron2_mul, one_mul, mul_one]
  -- Step 8: invoke A.29 to derive eq 14:
  --   ∀ x : W₁_b(x⊗|0⟩⊗|0⟩) = W₄_b†W₃_b†(x⊗|0⟩⊗|0⟩).
  have h_W2a_ket00 :
      Mat4.apply W₂_a (tensor1_1 ket0_1 ket0_1) = tensor1_1 ket0_1 ket0_1 :=
    h_W2a_apply ket0_1
  have h_D_fixes_x00 : ∀ x : Vec1,
      Mat8.apply (Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] : Mat8)
        (tensor1_2 x (tensor1_1 ket0_1 ket0_1)) =
      tensor1_2 x (tensor1_1 ket0_1 ket0_1) := by
    intro x
    funext i
    change ∑ j : Fin 8, (Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] : Mat8) i j *
          tensor1_2 x (tensor1_1 ket0_1 ket0_1) j =
          tensor1_2 x (tensor1_1 ket0_1 ket0_1) i
    rw [Finset.sum_eq_single i]
    · rw [Matrix.diagonal_apply_eq]
      fin_cases i <;> simp [tensor1_2, tensor1_1, ket0_1]
    · intro j _ hj_ne
      rw [Matrix.diagonal_apply_ne _ hj_ne.symm, zero_mul]
    · intro h_in; exact (h_in (Finset.mem_univ i)).elim
  have h_eq14 : ∀ x : Vec1,
      Mat8.apply (embedAC W₁_b) (tensor1_2 x (tensor1_1 ket0_1 ket0_1)) =
      Mat8.apply (embedBC W₄_b.conjTranspose * embedAC W₃_b.conjTranspose)
        (tensor1_2 x (tensor1_1 ket0_1 ket0_1)) :=
    fun x => py24_lemma_A_29 hW₁_b hW₂_a hW₃_b hW₄_b h_chain_b_eq_D h_W2a_ket00 x
  -- Step 9 prep: W₃_b† is controlled, so embedAC W₃_b† fixes (x⊗|0⟩⊗|0⟩).
  have hW3_b_dag_form :
      W₃_b.conjTranspose = kron2 1 proj0 + kron2 P₃_b.conjTranspose proj1 := by
    rw [hW₃_b_form, block_diag_second_conjT, Matrix.conjTranspose_one]
  have h_W3_b_dag_apply : ∀ x : Vec1,
      Mat4.apply W₃_b.conjTranspose (tensor1_1 x ket0_1) = tensor1_1 x ket0_1 := by
    intro x
    rw [hW3_b_dag_form]
    exact kron_block_diag_second_apply_x_ket0 P₃_b.conjTranspose x
  have h_embedAC_W3b_dag_fixes : ∀ x : Vec1,
      Mat8.apply (embedAC W₃_b.conjTranspose)
        (tensor1_2 x (tensor1_1 ket0_1 ket0_1)) =
      tensor1_2 x (tensor1_1 ket0_1 ket0_1) := fun x =>
    embedAC_apply_via_factored_action W₃_b.conjTranspose x ket0_1 ket0_1
      x ket0_1 (h_W3_b_dag_apply x)
  -- Step 9 main: derive Mat8-level chain identity for W₁_b's action.
  -- embedAC W₁_b (x⊗|0⟩⊗|0⟩)
  -- = (embedBC W₄_b† * embedAC W₃_b†)(x⊗|0⟩⊗|0⟩)   [eq 14]
  -- = embedBC W₄_b† (embedAC W₃_b†(x⊗|0⟩⊗|0⟩))    [Mat8.apply_mul]
  -- = embedBC W₄_b† (x⊗|0⟩⊗|0⟩)                    [W₃_b† fixes]
  -- = tensor1_2 x (W₄_b†(|0⟩⊗|0⟩))                 [embedBC_apply_tensor1_2]
  -- = tensor1_2 x (tensor1_1 |0⟩ β)                [h_eq13 ket0]
  have h_W1b_Mat8 : ∀ x : Vec1,
      Mat8.apply (embedAC W₁_b) (tensor1_2 x (tensor1_1 ket0_1 ket0_1)) =
      tensor1_2 x (tensor1_1 ket0_1 β) := by
    intro x
    rw [h_eq14 x, Mat8.apply_mul, h_embedAC_W3b_dag_fixes x,
        embedBC_apply_tensor1_2, h_eq13 ket0_1 IsQubit1_ket0]
  -- Step 9 conversion: extract Mat4 form via the converse helper.
  have h_W1b_apply : ∀ x : Vec1,
      Mat4.apply W₁_b (tensor1_1 x ket0_1) = tensor1_1 x β := fun x =>
    Mat4_apply_eq_of_embedAC_apply_with_ket0_middle W₁_b x ket0_1 x β (h_W1b_Mat8 x)
  -- Step 9 final: derive (kron2 1 Q† * W₁_b) fixes (x⊗|0⟩) for all x.
  have hQdag_β : Mat2.apply Q.conjTranspose β = ket0_1 := by
    rw [← hQ_ket0, ← Mat2.apply_mul, hQ_unit, Mat2.apply_one]
  have h_Q_W1_fixes : ∀ x : Vec1,
      Mat4.apply (kron2 1 Q.conjTranspose * W₁_b) (tensor1_1 x ket0_1) =
      tensor1_1 x ket0_1 := by
    intro x
    rw [Mat4.apply_mul, h_W1b_apply x, kron2_apply_tensor1_1, Mat2.apply_one, hQdag_β]
  -- Step 10: apply A.18 to (kron2 1 Q† * W₁_b) → extract P₁ + form; recover W₁_b form.
  have hkron2_1Qdag_unit : IsUnitary4 (kron2 1 Q.conjTranspose) :=
    isUnitary4_kron2 isUnitary2_one (isUnitary2_conjTranspose hQ_unit)
  have hQW1_unit : IsUnitary4 (kron2 1 Q.conjTranspose * W₁_b) :=
    isUnitary4_mul hkron2_1Qdag_unit hW₁_b
  obtain ⟨P₁, hP₁_unit, hQW1_form⟩ :=
    py24_lemma_A_18 (kron2 1 Q.conjTranspose * W₁_b) hQW1_unit
      (fun x _hx => h_Q_W1_fixes x)
  -- Recover W₁_b form by left-multiplying by (kron2 1 Q).
  have hkron2_1Q_mul_inv :
      kron2 (1 : Mat2) Q * kron2 1 Q.conjTranspose = (1 : Mat4) := by
    rw [kron2_mul, mul_one, mul_eq_one_comm.mp hQ_unit]
    exact kron2_one_one_eq_one
  have hW1_b_form :
      W₁_b = kron2 1 (Q * proj0) + kron2 P₁ (Q * proj1) := by
    have step1 : W₁_b = kron2 1 Q * (kron2 1 Q.conjTranspose * W₁_b) := by
      rw [← mul_assoc, hkron2_1Q_mul_inv, one_mul]
    rw [step1, hQW1_form, mul_add, kron2_mul, kron2_mul, mul_one, one_mul]
  -- Step 11 (final): assemble all witnesses.
  -- W₁ = W₁_b, W₂ = W₂_a, W₃ = W₃_b, W₄ = W₄_b
  -- P₁ = P₁, P₂ = P₂_a, P₃ = P₃_b, P₄ = P₄, Q = Q
  exact ⟨W₁_b, W₂_a, W₃_b, W₄_b, P₁, P₂_a, P₃_b, P₄, Q,
         hW₁_b, hW₂_a, hW₃_b, hW₄_b,
         hP₁_unit, hP₂_a, hP₃_b, hP₄_unit, hQ_unit,
         h_chain_b_eq_D, hW1_b_form, hW₂_a_form, hW₃_b_form, hW4_b_form⟩

/-! ## PY24 Lemma 6.3 — Trichotomic structural conclusion under V₂ second-factor-fixed

Paper p.226. Suppose |u₀| = |u₁| = 1. For 2-qubit unitaries V₁, V₂, V₃, V₄, if:
  · V_{1AC} V_{2BC} V_{3AC} V_{4BC} = CC(Diag(u₀, u₁))                         (eq 2)
  · ∃ |ψ⟩ : ∀ |x⟩ : ∃ |z⟩ : V₂ (|x⟩ ⊗ |0⟩) = |z⟩ ⊗ |ψ⟩  (V₂ second-factor-fixed) (eq 3)
  · V₃ (|0⟩ ⊗ |0⟩) = |0⟩ ⊗ |0⟩                                                   (eq 4)

then either u₀ = u₁, or u₀·u₁ = 1, or there exist 2-qubit unitaries
W₁, W₂, W₃, W₄ and 1-qubit unitaries P₁, P₂, P₃, P₄, Q such that:
  · W_{1AC} W_{2BC} W_{3AC} W_{4BC} = CC(Diag(u₀, u₁))
  · W₁ = I ⊗ |β⟩⟨0| + P₁ ⊗ |β⊥⟩⟨1|         (= kron2 1 (Q·proj0) + kron2 P₁ (Q·proj1))
  · W₂ = I ⊗ |0⟩⟨0| + P₂ ⊗ |1⟩⟨1|          (= kron2 1 proj0 + kron2 P₂ proj1)
  · W₃ = I ⊗ |0⟩⟨0| + P₃ ⊗ |1⟩⟨1|          (= kron2 1 proj0 + kron2 P₃ proj1)
  · W₄ = I ⊗ |0⟩⟨β| + P₄ ⊗ |1⟩⟨β⊥|         (= kron2 1 (proj0·Q†) + kron2 P₄ (proj1·Q†))

where |β⟩ = Q|0⟩, |β⊥⟩ = Q|1⟩.

Paper proof p.226-228: from eq (3) + A.30 derive ∃ U₁,W₂_a,U₄,P₂_a with
W₂_a = controlled and chain U₁ W₂_a V₃ U₄ = CC(Diag); apply Lemma 6.2;
first two disjuncts close; in the third (W_i form), expand and propagate
Q to recover W₁,W₄ structure via A.18, A.22, A.26 (missing helpers). -/
theorem py24_lemma_6_3 (u₀ u₁ : ℂ) (hu₀ : Complex.normSq u₀ = 1) (hu₁ : Complex.normSq u₁ = 1)
    (V₁ V₂ V₃ V₄ : Mat4)
    (hV₁ : IsUnitary4 V₁) (hV₂ : IsUnitary4 V₂)
    (hV₃ : IsUnitary4 V₃) (hV₄ : IsUnitary4 V₄)
    (h_prod : embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄ =
              Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁])
    (h_V2_factor : ∃ ψ : Vec1, IsQubit1 ψ ∧ ∀ x : Vec1, IsQubit1 x →
      ∃ z : Vec1, Mat4.apply V₂ (tensor1_1 x ket0_1) = tensor1_1 z ψ)
    (h_V3_ket00 : Mat4.apply V₃ (tensor1_1 ket0_1 ket0_1) = tensor1_1 ket0_1 ket0_1) :
    u₀ = u₁ ∨ u₀ * u₁ = 1 ∨
    (∃ W₁ W₂ W₃ W₄ : Mat4, ∃ P₁ P₂ P₃ P₄ Q : Mat2,
      IsUnitary4 W₁ ∧ IsUnitary4 W₂ ∧ IsUnitary4 W₃ ∧ IsUnitary4 W₄ ∧
      IsUnitary2 P₁ ∧ IsUnitary2 P₂ ∧ IsUnitary2 P₃ ∧ IsUnitary2 P₄ ∧ IsUnitary2 Q ∧
      embedAC W₁ * embedBC W₂ * embedAC W₃ * embedBC W₄ =
        Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] ∧
      W₁ = kron2 1 (Q * proj0) + kron2 P₁ (Q * proj1) ∧
      W₂ = kron2 1 proj0 + kron2 P₂ proj1 ∧
      W₃ = kron2 1 proj0 + kron2 P₃ proj1 ∧
      W₄ = kron2 1 (proj0 * Q.conjTranspose) + kron2 P₄ (proj1 * Q.conjTranspose)) := by
  -- Step 1: Apply A.30 to V₂'s second-factor-fixed hypothesis to extract
  -- U₁_a, W₂_a, U₄_a, P₂_a with W₂_a controlled and chain rewritten.
  obtain ⟨U₁_a, W₂_a, U₄_a, P₂_a, hU₁_a_unit, _hW₂_a_unit, hU₄_a_unit, _hP₂_a_unit,
          h_chain_eq, hW₂_a_form⟩ :=
    py24_lemma_A_30 V₁ V₂ V₃ V₄ hV₁ hV₂ hV₃ hV₄ h_V2_factor
  -- chain: embedAC U₁_a * embedBC W₂_a * embedAC V₃ * embedBC U₄_a = CC(Diag(u₀,u₁)).
  have h_chain_a : embedAC U₁_a * embedBC W₂_a * embedAC V₃ * embedBC U₄_a =
                    Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] := by
    rw [← h_chain_eq]; exact h_prod
  -- Step 2: W₂_a (|0⟩⊗|0⟩) = |0⟩⊗|0⟩ via the controlled-C action lemma
  -- (specialized to x = ket0_1).
  have h_W2_a_ket00 :
      Mat4.apply W₂_a (tensor1_1 ket0_1 ket0_1) = tensor1_1 ket0_1 ket0_1 := by
    rw [hW₂_a_form]
    exact controlled_C_apply_xtensor0 P₂_a ket0_1
  -- Step 3: D fixes the (x ⊗ |0⟩ ⊗ |0⟩) subspace because the first 4
  -- and entries 4-5 of D are 1, and tensor1_2 x (tensor1_1 ket0_1 ket0_1)
  -- vanishes at indices 1,2,3,5,6,7 (since one of B or C is in |1⟩).
  have h_D : ∀ x : Vec1,
      Mat8.apply (Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] : Mat8)
        (tensor1_2 x (tensor1_1 ket0_1 ket0_1)) =
      tensor1_2 x (tensor1_1 ket0_1 ket0_1) := by
    intro x
    funext i
    change ∑ j : Fin 8, (Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] : Mat8) i j *
        tensor1_2 x (tensor1_1 ket0_1 ket0_1) j =
      tensor1_2 x (tensor1_1 ket0_1 ket0_1) i
    rw [Finset.sum_eq_single i]
    · rw [Matrix.diagonal_apply_eq]
      fin_cases i <;> simp [tensor1_2, tensor1_1, ket0_1]
    · intro j _ hj_ne
      rw [Matrix.diagonal_apply_ne _ hj_ne.symm, zero_mul]
    · intro h_in; exact (h_in (Finset.mem_univ i)).elim
  -- Step 4: Apply A.29 to derive eq (8): ∀ x : Vec1,
  -- U₁_a (x⊗|0⟩⊗|0⟩) = U†_{4_a,BC} V†_{3,AC} (x⊗|0⟩⊗|0⟩).
  have h_eq8 : ∀ x : Vec1,
      Mat8.apply (embedAC U₁_a)
        (tensor1_2 x (tensor1_1 ket0_1 ket0_1)) =
      Mat8.apply (embedBC U₄_a.conjTranspose * embedAC V₃.conjTranspose)
        (tensor1_2 x (tensor1_1 ket0_1 ket0_1)) :=
    fun x => py24_lemma_A_29 hU₁_a_unit _hW₂_a_unit hV₃ hU₄_a_unit
      h_chain_a h_W2_a_ket00 x
  -- Step 5: Apply 6.2 to U₁_a, W₂_a, V₃, U₄_a using h_chain_a, h_V3_ket00, h_eq8.
  -- 6.2 returns a trichotomic disjunction.
  rcases py24_lemma_6_2 u₀ u₁ hu₀ hu₁ U₁_a W₂_a V₃ U₄_a
      hU₁_a_unit _hW₂_a_unit hV₃ hU₄_a_unit h_chain_a h_V3_ket00
      (fun x _hx => h_eq8 x) with
    h_eq | h_prod_uu |
    ⟨W₁_b, W₃_b, W₄_b, P₃_b, _hW₁_b, _hW₃_b, _hW₄_b, _hP₃_b,
     _h_chain_b, _hW₃_b_form⟩
  · -- 6.2 Disjunct 1: u₀ = u₁ ⇒ 6.3 disjunct 1 directly.
    exact Or.inl h_eq
  · -- 6.2 Disjunct 2: u₀·u₁ = 1 ⇒ 6.3 disjunct 2 directly.
    exact Or.inr (Or.inl h_prod_uu)
  · -- 6.2 Disjunct 3: ∃ W₁_b, W₃_b, W₄_b, P₃_b with chain rewrite + W₃_b
    -- controlled. Delegate to helper which packages the A.18 + A.22 +
    -- A.26 chain (all missing) to assemble the Q-rotated W_i forms.
    exact Or.inr (Or.inr (assemble_Q_rotated_from_6_2_W_i_form
      u₀ u₁ hu₀ hu₁ U₁_a W₂_a V₃ U₄_a
      hU₁_a_unit _hW₂_a_unit hV₃ hU₄_a_unit
      P₂_a _hP₂_a_unit hW₂_a_form h_chain_a h_V3_ket00
      W₁_b W₃_b W₄_b P₃_b _hW₁_b _hW₃_b _hW₄_b _hP₃_b
      _h_chain_b _hW₃_b_form))

/-- The PY24 Lemma 6.4 main statement. (⇐) direction is proved via the
    `py24_lemma_6_4_construct_u_eq` and `py24_lemma_6_4_construct_u_prod_inv`
    helpers. (⇒) direction remains as `sorry` — **blocked on missing
    `py24_lemma_6_2` and `py24_lemma_6_3`** (paper Lemmas 6.2/6.3 from
    Section 6, "the second main lemma"). The dependency chain per paper
    p.229 is: A.32 (V₃ similar structure), A.28 (chain → V₁V₂ on
    (|0⟩|x⟩|0⟩)), 6.1 (case analysis on V₂), then per case:
      Case 1 (V₂(·|0⟩) entangled): A.19 + 4.3.
      Case 2 (V₂(|x⟩|0⟩)=|ψ⟩⊗|z⟩): A.33 + 4.3.
      Case 3 (V₂(|x⟩|0⟩)=|z⟩⊗|ψ⟩): 6.3 + 4.2. -/
theorem py24_lemma_6_4 (u₀ u₁ : ℂ) (hu₀ : Complex.normSq u₀ = 1) (hu₁ : Complex.normSq u₁ = 1) :
    (∃ U₁ U₂ U₃ U₄ : Mat4, IsUnitary4 U₁ ∧ IsUnitary4 U₂ ∧ IsUnitary4 U₃ ∧ IsUnitary4 U₄ ∧
      embedAC U₁ * embedBC U₂ * embedAC U₃ * embedBC U₄ =
      Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁]) ↔
    (u₀ = u₁ ∨ u₀ * u₁ = 1) := by
  constructor
  · -- (⇒) direction. Paper p.229: A.32 → A.28 → 6.1 case-split → {A.19+4.3,
    -- A.33+4.3, 6.3+4.2}. Skeleton in progress; remaining via 6.3 (also stub).
    rintro ⟨U₁, U₂, U₃, U₄, hU₁, hU₂, hU₃, hU₄, h_prod⟩
    -- Step 1: A.32 normalizes V₃ to fix |00⟩, preserving the chain.
    obtain ⟨V₁, V₂, V₃, V₄, hV₁, hV₂, hV₃, hV₄, h_chain_eq, h_V3_ket00⟩ :=
      py24_lemma_A_32 U₁ U₂ U₃ U₄ hU₁ hU₂ hU₃ hU₄
    have h_chain : embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄ =
                   Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] := by
      rw [← h_chain_eq]; exact h_prod
    -- Step 2: D = diag(1,1,1,1,1,1,u₀,u₁) fixes the |0⟩_A subspace because
    -- the first 6 diagonal entries are 1 and tensor1_2 ket0_1 y vanishes on
    -- indices 4..7 (where ket0_1's high half is 0).
    have h_D : ∀ y : Vec2,
        Mat8.apply (Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] : Mat8)
          (tensor1_2 ket0_1 y) = tensor1_2 ket0_1 y := by
      intro y
      funext i
      change ∑ j : Fin 8, (Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] : Mat8) i j *
                        tensor1_2 ket0_1 y j = tensor1_2 ket0_1 y i
      rw [Finset.sum_eq_single i]
      · rw [Matrix.diagonal_apply_eq]
        fin_cases i <;> simp [tensor1_2, ket0_1]
      · intro j _ hj_ne
        rw [Matrix.diagonal_apply_ne _ hj_ne.symm, zero_mul]
      · intro h_in; exact (h_in (Finset.mem_univ i)).elim
    -- Step 3: Apply A.28 to derive ∀x : Vec1, V₁_AC V₂_BC (|0⟩|x⟩|0⟩) =
    -- V₄†_BC (|0⟩|x⟩|0⟩).
    have h_chain_action : ∀ x : Vec1,
        Mat8.apply (embedAC V₁ * embedBC V₂)
          (tensor1_2 ket0_1 (tensor1_1 x ket0_1)) =
        Mat8.apply (embedBC V₄.conjTranspose)
          (tensor1_2 ket0_1 (tensor1_1 x ket0_1)) :=
      fun x => py24_lemma_A_28 hV₄ h_chain h_V3_ket00 h_D x
    -- Step 4: Apply 6.1 to V₂ for trichotomic case analysis. Note: our 6.1
    -- has Case 2 = (V₂(x⊗|0⟩) = z⊗ψ, second-factor fixed) and Case 3 =
    -- (V₂(x⊗|0⟩) = ψ⊗z, first-factor fixed). Paper p.229 has these in
    -- swapped order (paper Case 2 = first-factor, paper Case 3 = second-
    -- factor), so paper Case 2 ↔ our Case 3 and paper Case 3 ↔ our Case 2.
    rcases py24_lemma_6_1 V₂ hV₂ with
      ⟨xEnt, hxEnt_qubit, hV₂_ent⟩ |
      ⟨ψ_r, hψ_r, h_V2_second_fixed⟩ |
      ⟨ψ_l, hψ_l, h_V2_first_fixed⟩
    · -- Case 1 (paper Case 1): ∃ xEnt with V₂(xEnt⊗|0⟩) entangled.
      -- ϕ := V₂(xEnt⊗|0⟩) and ω := V₄†(xEnt⊗|0⟩) are 2-qubit unit vectors.
      have h_xEnt_ket0_qubit : IsQubit2 (tensor1_1 xEnt ket0_1) :=
        IsQubit2_tensor1_1 hxEnt_qubit IsQubit1_ket0
      have hϕ_qubit : IsQubit2 (Mat4.apply V₂ (tensor1_1 xEnt ket0_1)) :=
        IsQubit2_apply_unitary hV₂ h_xEnt_ket0_qubit
      have hω_qubit :
          IsQubit2 (Mat4.apply V₄.conjTranspose (tensor1_1 xEnt ket0_1)) :=
        IsQubit2_apply_unitary (isUnitary4_conjTranspose hV₄) h_xEnt_ket0_qubit
      -- Derive hAct: embedAC V₁ (|0⟩ ⊗ ϕ) = |0⟩ ⊗ ω from h_chain_action.
      have hAct :
          Mat8.apply (embedAC V₁)
            (tensor1_2 ket0_1 (Mat4.apply V₂ (tensor1_1 xEnt ket0_1))) =
          tensor1_2 ket0_1 (Mat4.apply V₄.conjTranspose (tensor1_1 xEnt ket0_1)) := by
        have h_use := h_chain_action xEnt
        rw [Mat8.apply_mul, embedBC_apply_tensor1_2,
            embedBC_apply_tensor1_2] at h_use
        exact h_use
      -- Apply A.19 to extract V₁'s controlled form.
      obtain ⟨P₀, P₁, hP₀, hP₁, hV₁_ctrl⟩ :=
        py24_lemma_A_19 V₁ hV₁
          (Mat4.apply V₂ (tensor1_1 xEnt ket0_1))
          (Mat4.apply V₄.conjTranspose (tensor1_1 xEnt ket0_1))
          hϕ_qubit hω_qubit hAct hV₂_ent
      -- Apply 4.3 (⇒) using V₁ controlled + h_chain.
      exact (py24_lemma_4_3 u₀ u₁ hu₀ hu₁).mp
        ⟨V₁, V₂, V₃, V₄, hV₁, hV₂, hV₃, hV₄, P₀, P₁, hP₀, hP₁,
         hV₁_ctrl, h_chain⟩
    · -- Lean Case 2 = Paper Case 3: V₂(x⊗|0⟩) = z ⊗ ψ_r (second-factor fixed).
      -- Invoke 6.3 to get a 3-way disjunction; first two disjuncts close
      -- directly, third gives the structured W_i form (handled below).
      rcases py24_lemma_6_3 u₀ u₁ hu₀ hu₁ V₁ V₂ V₃ V₄ hV₁ hV₂ hV₃ hV₄
          h_chain ⟨ψ_r, hψ_r, h_V2_second_fixed⟩ h_V3_ket00 with
        h_ueq | h_uprod | ⟨W₁, W₂, W₃, W₄, P₁, P₂, P₃, P₄, Q,
                          _hW₁_unit, _hW₂_unit, _hW₃_unit, _hW₄_unit,
                          hP₁, hP₂, hP₃, hP₄, hQ,
                          h_chain_W, hW₁_form, hW₂_form, hW₃_form, hW₄_form⟩
      · exact Or.inl h_ueq
      · exact Or.inr h_uprod
      · -- Disjunct (c): W_i in structured Q-rotated form.
        -- Use chain_expansion_Q_rotated helper to convert chain to kron3 form.
        have h_kron3 :
            kron3 1 1 (Q * proj0 * Q.conjTranspose) +
            kron3 (P₁ * P₃) (P₂ * P₄) (Q * proj1 * Q.conjTranspose) =
            (Matrix.diagonal ![1, 1, 1, 1, 1, 1, u₀, u₁] : Mat8) := by
          rw [← chain_expansion_Q_rotated P₁ P₂ P₃ P₄ Q W₁ W₂ W₃ W₄
                hW₁_form hW₂_form hW₃_form hW₄_form]
          exact h_chain_W
        -- Apply 4.2 (⇒) with (P₀, P₁) := (P₁·P₃, P₂·P₄).
        obtain ⟨h_u0_eq_one, h_u1_eq_one⟩ := (py24_lemma_4_2 Q hQ u₀ u₁).mp
          ⟨P₁ * P₃, P₂ * P₄,
           isUnitary2_mul hP₁ hP₃, isUnitary2_mul hP₂ hP₄, h_kron3⟩
        -- u₀ = 1 ∧ u₁ = 1 ⟹ u₀ = u₁.
        exact Or.inl (h_u0_eq_one.trans h_u1_eq_one.symm)
    · -- Lean Case 3 = Paper Case 2: V₂(x⊗|0⟩) = ψ_l ⊗ z (first-factor fixed).
      -- A.33 takes the universal-x chain action (with IsQubit1 precondition)
      -- and the first-factor-fixed hypothesis to give V₁ controlled.
      obtain ⟨P₀, P₁, hP₀, hP₁, hV₁_ctrl⟩ :=
        py24_lemma_A_33 V₁ V₂ V₄ hV₁ hV₂ hV₄
          (fun x _hx => h_chain_action x)
          ⟨ψ_l, hψ_l, h_V2_first_fixed⟩
      exact (py24_lemma_4_3 u₀ u₁ hu₀ hu₁).mp
        ⟨V₁, V₂, V₃, V₄, hV₁, hV₂, hV₃, hV₄, P₀, P₁, hP₀, hP₁,
         hV₁_ctrl, h_chain⟩
  · -- (⇐) direction: case-split on u₀=u₁ vs u₀·u₁=1.
    rintro (h_eq | h_prod)
    · -- Case u₀ = u₁: SWAP-based construction.
      subst h_eq
      exact py24_lemma_6_4_construct_u_eq u₀ hu₀
    · -- Case u₀·u₁ = 1: CNOT-based construction.
      exact py24_lemma_6_4_construct_u_prod_inv u₀ u₁ hu₀ hu₁ h_prod

end
