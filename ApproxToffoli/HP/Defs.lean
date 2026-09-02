/-
  ApproxToffoli.HP.Defs
  Core definitions for formalizing Huang & Palsberg (2026):
  "Toffoli Requires Six Quantum Neighbor Gates"

  Defines 3-qubit diagonal gates and the classification sets S₁-S₆.
  These sets characterize exactly which diagonal gates can be implemented
  with k neighbor (AB/BC) 2-qubit gates.
-/

import ApproxToffoli.Defs

open Matrix Complex

noncomputable section

/-! ## 3-qubit diagonal gates

A 3-qubit diagonal gate D = Diag(d₀, d₁, ..., d₇) where each |dᵢ| = 1.
Indices use binary encoding: i = 4a + 2b + c for qubits A, B, C.
  0=(000), 1=(001), 2=(010), 3=(011),
  4=(100), 5=(101), 6=(110), 7=(111)
-/

/-- A 3-qubit diagonal gate: 8 diagonal entries, each with unit modulus -/
structure DiagGate3 where
  d : Fin 8 → ℂ
  unit : ∀ i, Complex.normSq (d i) = 1

namespace DiagGate3

/-- A diagonal entry with unit normSq is nonzero -/
theorem d_ne_zero (D : DiagGate3) (i : Fin 8) : D.d i ≠ 0 := by
  intro h
  have := D.unit i
  rw [h, map_zero] at this
  exact zero_ne_one this

/-- A diagonal entry has norm 1: d * conj(d) = 1 -/
theorem d_mul_conj (D : DiagGate3) (i : Fin 8) :
    D.d i * starRingEnd ℂ (D.d i) = 1 := by
  rw [Complex.mul_conj]
  exact_mod_cast D.unit i

/-- conj(d) * d = 1 -/
theorem conj_mul_d (D : DiagGate3) (i : Fin 8) :
    starRingEnd ℂ (D.d i) * D.d i = 1 := by
  rw [mul_comm, d_mul_conj]

/-- Convert a DiagGate3 to an 8×8 diagonal matrix -/
def toMatrix (D : DiagGate3) : Mat8 :=
  Matrix.diagonal D.d

/-- A DiagGate3's matrix is unitary in Mat8 sense: `D.toMatrix† · D.toMatrix = 1`.
    Follows from each entry `D.d i` having `|D.d i|² = 1` (`D.conj_mul_d`). -/
theorem toMatrix_unitary (D : DiagGate3) :
    D.toMatrix.conjTranspose * D.toMatrix = (1 : Mat8) := by
  unfold toMatrix
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  -- Goal: Matrix.diagonal (fun i => star (D.d i) * D.d i) = 1.
  -- Each diagonal entry equals 1 via D.conj_mul_d (modulo star = starRingEnd ℂ).
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    change star (D.d i) * D.d i = 1
    have : starRingEnd ℂ (D.d i) * D.d i = 1 := D.conj_mul_d i
    exact this
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

end DiagGate3

/-! ## The controlled-controlled-Z (CCZ) gate as a diagonal gate -/

/-- Helper: the CCZ diagonal entries defined by pattern match for clean reduction -/
private def ccz_entries : Fin 8 → ℂ := fun i =>
  match i.val with
  | 7 => -1
  | _ => 1

/-- CCZ = Diag(1,1,1,1,1,1,1,-1): flips the phase of |111⟩.
    This is the diagonal form of CCX (Toffoli), related by
    CCX = (I ⊗ I ⊗ H) · CCZ · (I ⊗ I ⊗ H). -/
def CCZ_diag : DiagGate3 where
  d := ccz_entries
  unit := by
    intro i; fin_cases i <;> simp [ccz_entries, normSq_apply]

-- Concrete entry values for CCZ, used in classification proofs
@[simp] theorem ccz_d_0 : CCZ_diag.d 0 = 1 := rfl
@[simp] theorem ccz_d_1 : CCZ_diag.d 1 = 1 := rfl
@[simp] theorem ccz_d_2 : CCZ_diag.d 2 = 1 := rfl
@[simp] theorem ccz_d_3 : CCZ_diag.d 3 = 1 := rfl
@[simp] theorem ccz_d_4 : CCZ_diag.d 4 = 1 := rfl
@[simp] theorem ccz_d_5 : CCZ_diag.d 5 = 1 := rfl
@[simp] theorem ccz_d_6 : CCZ_diag.d 6 = 1 := rfl
@[simp] theorem ccz_d_7 : CCZ_diag.d 7 = -1 := rfl

/-! ## Classification sets S₁ through S₆

From Huang & Palsberg, Section 5.
Each set captures the algebraic constraints on diagonal entries
that characterize implementability with a given number of neighbor gates.
-/

namespace DiagGate3

/-- Set S₁: implementable with exactly 1 neighbor gate.
    Equivalent to D factoring as a tensor product of three single-qubit phases:
    dᵢ = αₐ · βᵦ · γ꜀ where i = 4a + 2b + c. -/
def inS1 (D : DiagGate3) : Prop :=
  D.d 0 * D.d 5 = D.d 1 * D.d 4 ∧
  D.d 0 * D.d 6 = D.d 2 * D.d 4 ∧
  D.d 0 * D.d 7 = D.d 3 * D.d 4

/-- Set S₂: implementable with exactly 2 neighbor gates.
    Two factorization conditions on the AC bipartition. -/
def inS2 (D : DiagGate3) : Prop :=
  D.d 0 * D.d 6 = D.d 2 * D.d 4 ∧
  D.d 1 * D.d 7 = D.d 3 * D.d 5

/-- Set S₃: additional diagonal gates in the 3-gate class beyond S₂.
    The full 3-gate implementable set is S₂ ∪ S₃. -/
def inS3 (D : DiagGate3) : Prop :=
  D.d 0 * D.d 7 = D.d 3 * D.d 4 ∧
  D.d 1 * D.d 6 = D.d 2 * D.d 5

/-- Set S₄: implementable with 4 neighbor gates (first component).
    KEY parity condition: the product of entries at even-parity indices
    equals the product at odd-parity indices.
    Even parity (even number of 1-bits): {0=000, 3=011, 5=101, 6=110}
    Odd parity (odd number of 1-bits):   {1=001, 2=010, 4=100, 7=111} -/
def inS4 (D : DiagGate3) : Prop :=
  D.d 0 * D.d 3 * D.d 5 * D.d 6 = D.d 1 * D.d 2 * D.d 4 * D.d 7

/-- Set S₅: further diagonal gates reachable with 4 neighbor gates beyond S₄.
    From Definition 5.8: S₅ = S₅¹ ∪ S₅² ∪ S₅³ where
    S₅ᵏ = { D | ξ(D) = λᵢ(D)·λⱼ(D)/λₖ(D) } for {i,j} = {1,2,3}\{k}.
    Expressed as product-of-four conditions (matching the paper exactly). -/
def inS5 (D : DiagGate3) : Prop :=
  -- S₅¹: d₀d₃d₄d₇ = d₁d₂d₅d₆  (ξ = λ₂λ₃/λ₁)
  D.d 0 * D.d 3 * D.d 4 * D.d 7 = D.d 1 * D.d 2 * D.d 5 * D.d 6 ∨
  -- S₅²: d₀d₂d₅d₇ = d₁d₃d₄d₆  (ξ = λ₁λ₃/λ₂)
  D.d 0 * D.d 2 * D.d 5 * D.d 7 = D.d 1 * D.d 3 * D.d 4 * D.d 6 ∨
  -- S₅³: d₀d₁d₆d₇ = d₂d₃d₄d₅  (ξ = λ₁λ₂/λ₃)
  D.d 0 * D.d 1 * D.d 6 * D.d 7 = D.d 2 * D.d 3 * D.d 4 * D.d 5

/-- Set S₆: all 3-qubit diagonal gates. Every diagonal gate with unit entries
    can be implemented with 6 neighbor gates. -/
def inS6 (_D : DiagGate3) : Prop := True

end DiagGate3

/-! ## CCZ classification: not in S₄ ∪ S₅

This is the key algebraic fact that drives the 6-gate lower bound.
-/

/-- CCZ violates the S₄ parity condition.
    d₀d₃d₅d₆ = 1·1·1·1 = 1, but d₁d₂d₄d₇ = 1·1·1·(-1) = -1. -/
private lemma complex_one_ne_neg_one : (1 : ℂ) ≠ -1 := by
  exact_mod_cast (show (1 : ℤ) ≠ -1 from by decide)

theorem CCZ_not_inS4 : ¬ CCZ_diag.inS4 := by
  simp only [DiagGate3.inS4, ccz_d_0, ccz_d_1, ccz_d_2, ccz_d_3,
             ccz_d_4, ccz_d_5, ccz_d_6, ccz_d_7, mul_one, one_mul]
  exact complex_one_ne_neg_one

/-- CCZ violates all three S₅ product conditions.
    Each S₅ᵏ condition evaluates to -1 = 1 for CCZ
    (since d₇ = -1 and all other entries are 1). -/
theorem CCZ_not_inS5 : ¬ CCZ_diag.inS5 := by
  simp only [DiagGate3.inS5, ccz_d_0, ccz_d_1, ccz_d_2, ccz_d_3,
             ccz_d_4, ccz_d_5, ccz_d_6, ccz_d_7]
  -- Each disjunct reduces to -1 = 1 (over ℂ)
  simp only [mul_one, one_mul]
  rintro (h | h | h) <;> exact complex_one_ne_neg_one h.symm

/-- CCZ is not in S₄ ∪ S₅.
    Combined with the fact that ≤5 neighbor gates can only produce
    diagonal gates in S₄ ∪ S₅ (Theorem 4.5 + Theorem 6.2),
    this means CCZ requires at least 6 neighbor gates. -/
theorem CCZ_not_inS4_or_S5 : ¬ (CCZ_diag.inS4 ∨ CCZ_diag.inS5) := by
  push_neg
  exact ⟨CCZ_not_inS4, CCZ_not_inS5⟩

/-- CCZ is trivially in S₆ (all diagonal gates are). -/
theorem CCZ_inS6 : CCZ_diag.inS6 := trivial

/-! ## SWAP_BC conjugation for DiagGate3 (Lemma A.18)

Swapping qubits B and C permutes the diagonal entries and
permutes the S₅ᵏ components while preserving S₄ ∪ S₅ as a whole. -/

namespace DiagGate3

/-- Permutation of Fin 8 indices induced by swapping qubits B and C.
    Index i = 4a+2b+c maps to j = 4a+2c+b. Explicitly:
    0→0, 1→2, 2→1, 3→3, 4→4, 5→6, 6→5, 7→7 -/
private def swapBC_index : Fin 8 → Fin 8 := fun i =>
  match i.val with
  | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3
  | 4 => 4 | 5 => 6 | 6 => 5 | _ => 7

/-- SWAP_BC permutation is an involution -/
private theorem swapBC_index_invol (i : Fin 8) :
    swapBC_index (swapBC_index i) = i := by
  fin_cases i <;> rfl

/-- Conjugation by SWAP_BC: swap qubits B and C in a diagonal gate.
    D' = SWAP_BC · D · SWAP_BC has entries d'_i = d_{swap(i)}. -/
def swapBC (D : DiagGate3) : DiagGate3 where
  d := D.d ∘ swapBC_index
  unit := by
    intro i; simp only [Function.comp_apply]; exact D.unit (swapBC_index i)

-- Simp lemmas for swapBC entries
@[simp] theorem swapBC_d (D : DiagGate3) (i : Fin 8) :
    D.swapBC.d i = D.d (swapBC_index i) := rfl

/-- swapBC is an involution: swapBC (swapBC D) = D -/
theorem swapBC_invol (D : DiagGate3) : D.swapBC.swapBC = D := by
  cases D with | mk d hu =>
  simp only [swapBC]
  congr 1
  funext i
  exact congr_arg d (swapBC_index_invol i)

/-- S₄ is preserved by swapBC: swapping B,C doesn't change the parity condition. -/
theorem swapBC_inS4_iff (D : DiagGate3) :
    D.swapBC.inS4 ↔ D.inS4 := by
  simp only [inS4, swapBC_d, swapBC_index]
  -- Both sides are: d 0 * d 3 * d 5 * d 6 = d 1 * d 2 * d 4 * d 7
  -- after swapBC: d 0 * d 3 * d 6 * d 5 = d 2 * d 1 * d 4 * d 7
  constructor <;> intro h <;> ring_nf at h ⊢ <;> exact h

/-- S₅ is preserved by swapBC: S₅¹ ↔ S₅¹, S₅² ↔ S₅³. -/
theorem swapBC_inS5_iff (D : DiagGate3) :
    D.swapBC.inS5 ↔ D.inS5 := by
  simp only [inS5, swapBC_d, swapBC_index]
  -- swapBC fixes indices 0,3,4,7 and swaps 1↔2, 5↔6
  -- S₅¹ ↔ S₅¹ (by commutativity), S₅² ↔ S₅³, S₅³ ↔ S₅²
  constructor <;> intro h <;> rcases h with h | h | h
  · exact Or.inl (by ring_nf at h ⊢; exact h)
  · exact Or.inr (Or.inr (by ring_nf at h ⊢; exact h))
  · exact Or.inr (Or.inl (by ring_nf at h ⊢; exact h))
  · exact Or.inl (by ring_nf at h ⊢; exact h)
  · exact Or.inr (Or.inr (by ring_nf at h ⊢; exact h))
  · exact Or.inr (Or.inl (by ring_nf at h ⊢; exact h))

/-- Combined: S₄ ∨ S₅ is preserved by swapBC -/
theorem swapBC_inS4_or_S5_iff (D : DiagGate3) :
    (D.swapBC.inS4 ∨ D.swapBC.inS5) ↔ (D.inS4 ∨ D.inS5) := by
  rw [swapBC_inS4_iff, swapBC_inS5_iff]

/-! ## SWAP_AC and SWAP_AB conjugation on DiagGate3 (basic) -/

/-- Permutation of Fin 8 indices induced by swapping qubits A and C.
    Index 4a+2b+c maps to 4c+2b+a. -/
private def swapAC_index : Fin 8 → Fin 8 := fun i =>
  match i.val with
  | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 6
  | 4 => 1 | 5 => 5 | 6 => 3 | _ => 7

private theorem swapAC_index_invol (i : Fin 8) :
    swapAC_index (swapAC_index i) = i := by
  fin_cases i <;> rfl

/-- Conjugation by SWAP_AC: swap qubits A and C in a diagonal gate. -/
def swapAC (D : DiagGate3) : DiagGate3 where
  d := D.d ∘ swapAC_index
  unit := by
    intro i; simp only [Function.comp_apply]; exact D.unit (swapAC_index i)

@[simp] theorem swapAC_d (D : DiagGate3) (i : Fin 8) :
    D.swapAC.d i = D.d (swapAC_index i) := rfl

theorem swapAC_invol (D : DiagGate3) : D.swapAC.swapAC = D := by
  cases D with | mk d hu =>
  simp only [swapAC]
  congr 1
  funext i
  exact congr_arg d (swapAC_index_invol i)

/-- Permutation of Fin 8 indices induced by swapping qubits A and B.
    Index 4a+2b+c maps to 4b+2a+c. -/
private def swapAB_index : Fin 8 → Fin 8 := fun i =>
  match i.val with
  | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 5
  | 4 => 2 | 5 => 3 | 6 => 6 | _ => 7

private theorem swapAB_index_invol (i : Fin 8) :
    swapAB_index (swapAB_index i) = i := by
  fin_cases i <;> rfl

/-- Conjugation by SWAP_AB: swap qubits A and B in a diagonal gate. -/
def swapAB (D : DiagGate3) : DiagGate3 where
  d := D.d ∘ swapAB_index
  unit := by
    intro i; simp only [Function.comp_apply]; exact D.unit (swapAB_index i)

@[simp] theorem swapAB_d (D : DiagGate3) (i : Fin 8) :
    D.swapAB.d i = D.d (swapAB_index i) := rfl

theorem swapAB_invol (D : DiagGate3) : D.swapAB.swapAB = D := by
  cases D with | mk d hu =>
  simp only [swapAB]
  congr 1
  funext i
  exact congr_arg d (swapAB_index_invol i)

/-- S₄ is preserved by swapAC: S₄ indices {0,3,5,6} permute among themselves,
    likewise {1,2,4,7}. -/
theorem swapAC_inS4_iff (D : DiagGate3) :
    D.swapAC.inS4 ↔ D.inS4 := by
  simp only [inS4, swapAC_d, swapAC_index]
  -- LHS: d 0 * d 6 * d 5 * d 3 = d 4 * d 2 * d 1 * d 7
  -- RHS: d 0 * d 3 * d 5 * d 6 = d 1 * d 2 * d 4 * d 7
  constructor <;> intro h <;> ring_nf at h ⊢ <;> exact h

/-- S₄ is preserved by swapAB: S₄ indices {0,3,5,6} permute among themselves,
    likewise {1,2,4,7}. -/
theorem swapAB_inS4_iff (D : DiagGate3) :
    D.swapAB.inS4 ↔ D.inS4 := by
  simp only [inS4, swapAB_d, swapAB_index]
  -- LHS: d 0 * d 5 * d 3 * d 6 = d 1 * d 4 * d 2 * d 7
  -- RHS: d 0 * d 3 * d 5 * d 6 = d 1 * d 2 * d 4 * d 7
  constructor <;> intro h <;> ring_nf at h ⊢ <;> exact h

/-- S₅ is preserved by swapAC: S₅¹ ↔ S₅³ and S₅² fixed.
    Index map 0→0, 1→4, 2→2, 3→6, 4→1, 5→5, 6→3, 7→7 sends:
    S₅¹ LHS {0,3,4,7}→{0,6,1,7}=S₅³ LHS; RHS {1,2,5,6}→{4,2,5,3}=S₅³ RHS.
    S₅² LHS {0,2,5,7} fixed; RHS {1,3,4,6}→{4,6,1,3}=same set. -/
theorem swapAC_inS5_iff (D : DiagGate3) :
    D.swapAC.inS5 ↔ D.inS5 := by
  simp only [inS5, swapAC_d, swapAC_index]
  constructor <;> intro h <;> rcases h with h | h | h
  · exact Or.inr (Or.inr (by ring_nf at h ⊢; exact h))     -- swapAC.S₅¹ → S₅³
  · exact Or.inr (Or.inl (by ring_nf at h ⊢; exact h))     -- swapAC.S₅² → S₅²
  · exact Or.inl (by ring_nf at h ⊢; exact h)              -- swapAC.S₅³ → S₅¹
  · exact Or.inr (Or.inr (by ring_nf at h ⊢; exact h))     -- S₅¹ → swapAC.S₅³
  · exact Or.inr (Or.inl (by ring_nf at h ⊢; exact h))     -- S₅² → swapAC.S₅²
  · exact Or.inl (by ring_nf at h ⊢; exact h)              -- S₅³ → swapAC.S₅¹

/-- S₅ is preserved by swapAB: S₅¹ ↔ S₅² and S₅³ fixed.
    Index map 0→0, 1→1, 2→4, 3→5, 4→2, 5→3, 6→6, 7→7 sends:
    S₅¹ LHS {0,3,4,7}→{0,5,2,7}=S₅² LHS; RHS {1,2,5,6}→{1,4,3,6}=S₅² RHS.
    S₅³ LHS {0,1,6,7} fixed; RHS {2,3,4,5}→{4,5,2,3}=same set. -/
theorem swapAB_inS5_iff (D : DiagGate3) :
    D.swapAB.inS5 ↔ D.inS5 := by
  simp only [inS5, swapAB_d, swapAB_index]
  constructor <;> intro h <;> rcases h with h | h | h
  · exact Or.inr (Or.inl (by ring_nf at h ⊢; exact h))     -- swapAB.S₅¹ → S₅²
  · exact Or.inl (by ring_nf at h ⊢; exact h)              -- swapAB.S₅² → S₅¹
  · exact Or.inr (Or.inr (by ring_nf at h ⊢; exact h))     -- swapAB.S₅³ → S₅³
  · exact Or.inr (Or.inl (by ring_nf at h ⊢; exact h))     -- S₅¹ → swapAB.S₅²
  · exact Or.inl (by ring_nf at h ⊢; exact h)              -- S₅² → swapAB.S₅¹
  · exact Or.inr (Or.inr (by ring_nf at h ⊢; exact h))     -- S₅³ → swapAB.S₅³

/-- Combined: S₄ ∨ S₅ is preserved by swapAC. -/
theorem swapAC_inS4_or_S5_iff (D : DiagGate3) :
    (D.swapAC.inS4 ∨ D.swapAC.inS5) ↔ (D.inS4 ∨ D.inS5) := by
  rw [swapAC_inS4_iff, swapAC_inS5_iff]

/-- Combined: S₄ ∨ S₅ is preserved by swapAB. -/
theorem swapAB_inS4_or_S5_iff (D : DiagGate3) :
    (D.swapAB.inS4 ∨ D.swapAB.inS5) ↔ (D.inS4 ∨ D.inS5) := by
  rw [swapAB_inS4_iff, swapAB_inS5_iff]

/-! ## Dagger of DiagGate3 (Lemma 5.3 of Huang & Palsberg 2026)

The dagger of a DiagGate3 is obtained by conjugating all diagonal entries.
This corresponds to the conjugate transpose of the matrix representation.
The S₄ and S₅ sets are preserved under dagger (the algebraic conditions are
invariant under taking complex conjugates). -/

/-- The dagger of a DiagGate3: conjugate all diagonal entries. -/
def dagger (D : DiagGate3) : DiagGate3 where
  d := fun i => starRingEnd ℂ (D.d i)
  unit := by
    intro i
    rw [Complex.normSq_conj]
    exact D.unit i

@[simp] theorem dagger_d (D : DiagGate3) (i : Fin 8) :
    D.dagger.d i = starRingEnd ℂ (D.d i) := rfl

/-- The dagger is an involution. -/
theorem dagger_invol (D : DiagGate3) : D.dagger.dagger = D := by
  cases D with | mk d hu =>
  simp only [dagger]
  congr 1
  funext i
  exact Complex.conj_conj _

/-- **Paper's Lemma 5.3** (S₄ part): D ∈ S₄ ↔ D† ∈ S₄. -/
theorem dagger_inS4_iff (D : DiagGate3) : D.dagger.inS4 ↔ D.inS4 := by
  simp only [inS4, dagger_d]
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
  exact star_injective.eq_iff

/-- **Paper's Lemma 5.3** (S₅ part): D ∈ S₅ ↔ D† ∈ S₅. -/
theorem dagger_inS5_iff (D : DiagGate3) : D.dagger.inS5 ↔ D.inS5 := by
  simp only [inS5, dagger_d]
  constructor
  · rintro (h | h | h)
    · refine Or.inl ?_
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul] at h
      exact star_injective h
    · refine Or.inr (Or.inl ?_)
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul] at h
      exact star_injective h
    · refine Or.inr (Or.inr ?_)
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul] at h
      exact star_injective h
  · rintro (h | h | h)
    · refine Or.inl ?_
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
      exact congrArg _ h
    · refine Or.inr (Or.inl ?_)
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
      exact congrArg _ h
    · refine Or.inr (Or.inr ?_)
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
      exact congrArg _ h

/-- Combined: S₄ ∨ S₅ is preserved by dagger. -/
theorem dagger_inS4_or_S5_iff (D : DiagGate3) :
    (D.dagger.inS4 ∨ D.dagger.inS5) ↔ (D.inS4 ∨ D.inS5) := by
  rw [dagger_inS4_iff, dagger_inS5_iff]

/-- The DiagGate3 dagger's matrix equals the matrix conjugate transpose. -/
theorem dagger_toMatrix (D : DiagGate3) :
    D.dagger.toMatrix = D.toMatrix.conjTranspose := by
  unfold DiagGate3.toMatrix DiagGate3.dagger
  rw [Matrix.diagonal_conjTranspose]
  rfl

/-! ## Set inclusion lemmas

The paper's classification hierarchy (Section 5):
S₁ ⊂ S₂ ⊂ S₄, and S₁ ⊂ S₃ ⊂ S₄ ∪ S₅.
These algebraic inclusions are proved by ring manipulations. -/

/-- S₁ ⊂ S₄: product gates satisfy the S₄ parity condition. -/
theorem inS1_implies_inS4 (D : DiagGate3) (h : D.inS1) : D.inS4 := by
  obtain ⟨h05, h06, h07⟩ := h
  unfold inS4
  have hd0 := D.d_ne_zero 0
  -- Multiply both sides of the goal by d₀, then use h05/h06/h07 to simplify
  apply mul_left_cancel₀ hd0
  calc D.d 0 * (D.d 0 * D.d 3 * D.d 5 * D.d 6)
      = D.d 3 * (D.d 0 * D.d 5) * (D.d 0 * D.d 6) := by ring
    _ = D.d 3 * (D.d 1 * D.d 4) * (D.d 2 * D.d 4) := by rw [h05, h06]
    _ = D.d 1 * D.d 2 * D.d 4 * (D.d 3 * D.d 4) := by ring
    _ = D.d 1 * D.d 2 * D.d 4 * (D.d 0 * D.d 7) := by rw [h07]
    _ = D.d 0 * (D.d 1 * D.d 2 * D.d 4 * D.d 7) := by ring

/-- S₂ ⊂ S₄: the S₂ conditions imply the S₄ parity condition. -/
theorem inS2_implies_inS4 (D : DiagGate3) (h : D.inS2) : D.inS4 := by
  obtain ⟨h06, h17⟩ := h
  unfold inS4
  -- h06 : d₀ * d₆ = d₂ * d₄
  -- h17 : d₁ * d₇ = d₃ * d₅
  -- Goal : d₀ * d₃ * d₅ * d₆ = d₁ * d₂ * d₄ * d₇
  -- Direct: d₀d₃d₅d₆ = d₃d₅ · d₀d₆ = d₃d₅ · d₂d₄ = d₂d₄ · d₃d₅
  --                    = d₂d₄ · d₁d₇ = d₁d₂d₄d₇ ✓
  calc D.d 0 * D.d 3 * D.d 5 * D.d 6
      = D.d 3 * D.d 5 * (D.d 0 * D.d 6) := by ring
    _ = D.d 3 * D.d 5 * (D.d 2 * D.d 4) := by rw [h06]
    _ = D.d 2 * D.d 4 * (D.d 1 * D.d 7) := by rw [← h17]; ring
    _ = D.d 1 * D.d 2 * D.d 4 * D.d 7 := by ring

/-- S₃ ⊂ S₄ ∪ S₅: the S₃ conditions imply S₅³ (hence S₅).
    Proof: d₀d₁d₆d₇ = (d₀d₇)(d₁d₆) = (d₃d₄)(d₂d₅) = d₂d₃d₄d₅. -/
theorem inS3_implies_inS4_or_S5 (D : DiagGate3) (h : D.inS3) : D.inS4 ∨ D.inS5 := by
  obtain ⟨h07, h16⟩ := h
  -- S₃ implies S₅³: d₀d₁d₆d₇ = d₂d₃d₄d₅
  exact Or.inr (Or.inr (Or.inr (
    calc D.d 0 * D.d 1 * D.d 6 * D.d 7
        = (D.d 0 * D.d 7) * (D.d 1 * D.d 6) := by ring
      _ = (D.d 3 * D.d 4) * (D.d 2 * D.d 5) := by rw [h07, h16]
      _ = D.d 2 * D.d 3 * D.d 4 * D.d 5 := by ring)))

end DiagGate3

end
