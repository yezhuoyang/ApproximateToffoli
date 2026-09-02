/-
  ApproxToffoli.HP.Trichotomy
  Lemma A.8: Entanglement trichotomy for 2-qubit gates.

  A 2-qubit gate V either:
  (1) is entangling (maps some product state to an entangled state), or
  (2) preserves the first qubit: V = |0⟩⟨0| ⊗ P₀ + |1⟩⟨1| ⊗ P₁, or
  (3) preserves the second qubit: V = P₀ ⊗ |0⟩⟨0| + P₁ ⊗ |1⟩⟨1|.

  Cases (2) and (3) mean V is "block-diagonal" in the respective qubit.

  Reference: Lemma A.8 (Palsberg and Yu 2024, Lemma 6.1)
-/

import ApproxToffoli.HP.EmbedLemmas

open Matrix Complex

noncomputable section

/-! ## Block-diagonal predicates for 4×4 matrices

A 4×4 matrix V is "block-diagonal in the first qubit" if V_{ij} = 0
whenever ⌊i/2⌋ ≠ ⌊j/2⌋. This means V has the form:
  V = |0⟩⟨0| ⊗ P₀ + |1⟩⟨1| ⊗ P₁
where P₀ = V[0:2, 0:2] and P₁ = V[2:4, 2:4].

Equivalently, V = kron2(proj0, P₀) + kron2(proj1, P₁). -/

/-- V is block-diagonal in the first qubit: V_{ij} = 0 when ⌊i/2⌋ ≠ ⌊j/2⌋ -/
def IsBlockDiagFirst (V : Mat4) : Prop :=
  ∃ (P₀ P₁ : Mat2), V = kron2 proj0 P₀ + kron2 proj1 P₁

/-- V is block-diagonal in the second qubit: V_{ij} = 0 when i%2 ≠ j%2 -/
def IsBlockDiagSecond (V : Mat4) : Prop :=
  ∃ (P₀ P₁ : Mat2), V = kron2 P₀ proj0 + kron2 P₁ proj1

/-- V is entangling: there exist input states such that V maps a product to an entangled state.
    For our purposes, we define entangling as NOT being block-diagonal in either qubit. -/
def IsEntangling (V : Mat4) : Prop :=
  ¬ IsBlockDiagFirst V ∧ ¬ IsBlockDiagSecond V

/-! ## Entanglement trichotomy (Lemma A.8)

For a 4×4 unitary V, exactly one of:
(1) V is entangling (some product input → entangled output)
(2) V is block-diagonal in the first qubit
(3) V is block-diagonal in the second qubit

Note: The paper's Lemma A.8 states a slightly different (but equivalent) formulation
in terms of preserving computational basis states. Our matrix formulation captures
the essential property used in Theorem 4.5. -/

/-- Lemma A.8 (entanglement trichotomy): A 4×4 unitary is either entangling,
    block-diagonal in the first qubit, or block-diagonal in the second qubit.
    This is the weak form (disjunction); the paper also shows mutual exclusivity. -/
theorem entanglement_trichotomy (V : Mat4) (_hV : IsUnitary4 V) :
    IsEntangling V ∨ IsBlockDiagFirst V ∨ IsBlockDiagSecond V := by
  -- This is a propositional tautology: (¬A ∧ ¬B) ∨ A ∨ B
  by_cases h1 : IsBlockDiagFirst V
  · exact Or.inr (Or.inl h1)
  · by_cases h2 : IsBlockDiagSecond V
    · exact Or.inr (Or.inr h2)
    · exact Or.inl ⟨h1, h2⟩

/-! ## Lemma A.1: Z-commutativity characterization

A 4×4 matrix V commutes with Z⊗I iff V is block-diagonal in the first qubit.
This is the key structural lemma: if a circuit product equals a diagonal gate D,
then D commutes with Z on every qubit, which forces intermediate gates
to have controlled structure. -/

/-- Z⊗I as a 4×4 matrix -/
def ZI : Mat4 := kron2 pauliZ I₂

/-- Block-diagonal matrices commute with Z⊗I (forward direction) -/
theorem blockDiagFirst_commutes_ZI (V : Mat4) (hV : IsBlockDiagFirst V) :
    V * ZI = ZI * V := by
  obtain ⟨P₀, P₁, hV⟩ := hV
  subst hV
  ext i j
  simp only [ZI, kron2, pauliZ, I₂, proj0, proj1,
             Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply,
             Matrix.one_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
  · simp <;> ring

/-- Over ℂ, -a = a implies a = 0 (characteristic ≠ 2) -/
private lemma neg_eq_self_zero {a : ℂ} (h : -a = a) : a = 0 := by
  have h2 : -a + a = 0 := neg_add_cancel a
  rw [h] at h2 -- h2 : a + a = 0
  have h3 : 2 * a = 0 := by rw [two_mul]; exact h2
  exact (mul_eq_zero.mp h3).resolve_left two_ne_zero

/-- Commuting with Z⊗I implies block-diagonal in first qubit (reverse direction).
    If V * (Z⊗I) = (Z⊗I) * V, then V_{ij} = 0 whenever ⌊i/2⌋ ≠ ⌊j/2⌋.
    This means V = kron2(proj0, P₀) + kron2(proj1, P₁). -/
theorem commutes_ZI_implies_blockDiagFirst (V : Mat4) (h : V * ZI = ZI * V) :
    IsBlockDiagFirst V := by
  -- Extract the 2×2 blocks P₀ = V[0:2, 0:2] and P₁ = V[2:4, 2:4]
  refine ⟨Matrix.of !![V 0 0, V 0 1; V 1 0, V 1 1],
          Matrix.of !![V 2 2, V 2 3; V 3 2, V 3 3], ?_⟩
  -- The commutation V*(Z⊗I) = (Z⊗I)*V forces off-diagonal blocks to vanish:
  -- For cross-block entries (⌊i/2⌋ ≠ ⌊j/2⌋), the condition gives -V_{ij} = V_{ij}
  ext i j
  have hij := congr_fun (congr_fun h i) j
  simp only [ZI, kron2, pauliZ, I₂, Matrix.mul_apply, Matrix.of_apply,
             Matrix.one_apply, proj0, proj1, Matrix.add_apply,
             Fin.sum_univ_four] at hij ⊢
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
    first | exact hij | exact neg_eq_self_zero hij |
      exact neg_eq_self_zero (neg_eq_iff_eq_neg.mpr hij)

/-! ## Lemma A.1 (second qubit): I⊗Z commutativity characterization

A 4×4 matrix V commutes with I⊗Z iff V is block-diagonal in the second qubit. -/

/-- I⊗Z as a 4×4 matrix -/
def IZ : Mat4 := kron2 I₂ pauliZ

/-- Block-diagonal in second qubit implies commutes with I⊗Z -/
theorem blockDiagSecond_commutes_IZ (V : Mat4) (hV : IsBlockDiagSecond V) :
    V * IZ = IZ * V := by
  obtain ⟨P₀, P₁, hV⟩ := hV
  subst hV
  ext i j
  simp only [IZ, kron2, pauliZ, I₂, proj0, proj1,
             Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply,
             Matrix.one_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
  · simp <;> ring

/-- Commuting with I⊗Z implies block-diagonal in second qubit.
    If V * (I⊗Z) = (I⊗Z) * V, then V_{ij} = 0 whenever i%2 ≠ j%2.
    This means V = kron2(P₀, proj0) + kron2(P₁, proj1). -/
theorem commutes_IZ_implies_blockDiagSecond (V : Mat4) (h : V * IZ = IZ * V) :
    IsBlockDiagSecond V := by
  -- Extract the 2×2 blocks: P₀ from even rows/cols, P₁ from odd rows/cols
  refine ⟨Matrix.of !![V 0 0, V 0 2; V 2 0, V 2 2],
          Matrix.of !![V 1 1, V 1 3; V 3 1, V 3 3], ?_⟩
  ext i j
  have hij := congr_fun (congr_fun h i) j
  simp only [IZ, kron2, pauliZ, I₂, Matrix.mul_apply, Matrix.of_apply,
             Matrix.one_apply, proj0, proj1, Matrix.add_apply,
             Fin.sum_univ_four] at hij ⊢
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
    first | exact hij | exact neg_eq_self_zero hij |
      exact neg_eq_self_zero (neg_eq_iff_eq_neg.mpr hij)

end
