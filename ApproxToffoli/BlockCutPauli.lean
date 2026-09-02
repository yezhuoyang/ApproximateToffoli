/-
  ApproxToffoli.BlockCutPauli

  **`HS2` ⟺ a C-Pauli LOWER bound.**

  `BlockU.HS2` — the last analytic input of `CutBoundU`, hence of `Block.PhiFive`
  and of the `n = 6, 7` lower bounds — asks for an UPPER bound

      ‖Tr_C X‖²_HS ≤ 8 + 4√2 ,   X = (1⊗W₂)(M₂⊗1)·CCZ8·(M₀⊗1)(1⊗W₁) ∈ U(8).

  Every term-by-term magnitude estimate on `Tr_C X` caps at `16` and so overshoots
  the budget by exactly `16 - (8+4√2) = 8 - 4√2`; closing that gap needs the phases.
  This file removes the phases from the statement.

  Since `{1, σx, σy, σz}/√2` is an orthonormal basis of `Mat2`, for EVERY 8×8 `X`

      ‖Tr_C X‖² + ‖Tr_C((1⊗σx)X)‖² + ‖Tr_C((1⊗σy)X)‖² + ‖Tr_C((1⊗σz)X)‖²
        = 2‖X‖²_HS                                          (`pauli_identity`)

  — a pointwise 2×2 parallelogram law; no unitarity is used.  For `X` unitary the
  right-hand side is `16`, so `HS2` is EQUIVALENT to the LOWER bound

      (PAULI)  ‖Tr_C((1⊗σx)X)‖² + ‖Tr_C((1⊗σy)X)‖² + ‖Tr_C((1⊗σz)X)‖²
                 ≥ 8 - 4√2 = 2.3431457…                     (`hs2_iff_pauliLB`)

  i.e. "the circuit must carry a certain minimum amount of NON-identity C-Pauli
  content, and `CCZ8` is what forces it".  The quantity now being bounded is a sum
  of squares of a positive quantity: no cancellation, no phases.

  Equivalently, `pauliContent X = 2·min over A of ‖X - A ⊗ 1_C‖²_HS`, so (PAULI)
  says the circuit stays HS-distance `2√2 sin(π/8)` away from every C-trivial
  operator: `min_A ‖X - A⊗1‖² ≥ 4 - 2√2 = 8 sin²(π/8)` (`budget_sin`).

  NUMERICS (independent re-derivation; `scratchpad/p1_derive.py`, `p2_opt.py`,
  `p7_geo.py`, `p8_survey.py`): the identity holds to `2.5e-14` over 2000 random
  instances.  The maximum of `‖Tr_C X‖²` over the `HS2` family is
  `13.656854249492 = 8 + 4√2` to `3e-14`, reached from 14/14 random restarts by
  monotone Gauss–Seidel with exact nuclear-norm block updates (the objective is a
  squared norm, hence convex in each block, so linearised nuclear-norm updates
  ascend).  At every maximiser all four singular values of `Tr_C X` equal
  `2cos(π/8)` and the 3×3 C-Pauli Gram matrix has rank ≤ 2.  So (PAULI) is TIGHT:
  its minimum is exactly `2.343145750508 = 8 - 4√2`.

  (PAULI) itself is NOT proved here.  This file is the reduction only.
-/

import ApproxToffoli.BlockCutHS1

open Matrix Complex

noncomputable section

namespace PauliHS

/-! ## 0. Setup -/

/-- `‖A‖²_HS` for an 8×8 (the `Mat4` version is `HSBound.hs4`). -/
def hs8 (A : Mat8) : ℝ := RCLike.re (Matrix.trace (Aᴴ * A))

/-- `σy`.  (`pauliX`/`pauliZ` are in `Defs`; `pauliY` lives in `CartanCut`, which
    is not on this import path, so it is re-declared here.) -/
def pY : Mat2 := Matrix.of !![0, -Complex.I; Complex.I, 0]

/-- The two `Fin 8` indices sitting above the AB index `x`. -/
def e0 (x : Fin 4) : Fin 8 := ⟨2 * x.val, by omega⟩
def e1 (x : Fin 4) : Fin 8 := ⟨2 * x.val + 1, by omega⟩

lemma hs4_eq_sum (A : Mat4) :
    HSBound.hs4 A = ∑ i : Fin 4, ∑ j : Fin 4, Complex.normSq (A i j) := by
  simp [HSBound.hs4, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_four, Complex.normSq_apply,
    Complex.add_re, Complex.mul_re]
  ring

lemma hs8_eq_sum (A : Mat8) :
    hs8 A = ∑ i : Fin 8, ∑ j : Fin 8, Complex.normSq (A i j) := by
  simp [hs8, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_eight, Complex.normSq_apply,
    Complex.add_re, Complex.mul_re]
  ring

lemma hs4_nonneg (A : Mat4) : 0 ≤ HSBound.hs4 A := by
  rw [hs4_eq_sum]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

/-! ## 1. The C-Pauli identity -/

lemma trC_apply (X : Mat8) (x y : Fin 4) :
    BlockU.trC X x y = X (e0 x) (e0 y) + X (e1 x) (e1 y) := rfl

set_option maxHeartbeats 1600000 in
-- 16-case `fin_cases × fin_cases` with an 8-term `Fin 8` sum inside each case.
/-- Left-multiplying by a C-local layer `1 ⊗ c` mixes the four C-blocks of `X`
    exactly as `c` prescribes. -/
lemma trC_kron_apply (c : Mat2) (X : Mat8) (x y : Fin 4) :
    BlockU.trC (kronABC 1 c * X) x y =
      c 0 0 * X (e0 x) (e0 y) + c 0 1 * X (e1 x) (e0 y)
      + c 1 0 * X (e0 x) (e1 y) + c 1 1 * X (e1 x) (e1 y) := by
  rw [trC_apply]
  fin_cases x <;> fin_cases y <;>
    simp [Matrix.mul_apply, kronABC, Matrix.of_apply, Matrix.one_apply, e0, e1,
      Fin.sum_univ_eight] <;> ring

lemma trC_X_apply (X : Mat8) (x y : Fin 4) :
    BlockU.trC (kronABC 1 pauliX * X) x y = X (e1 x) (e0 y) + X (e0 x) (e1 y) := by
  rw [trC_kron_apply]; simp [pauliX]

lemma trC_Y_apply (X : Mat8) (x y : Fin 4) :
    BlockU.trC (kronABC 1 pY * X) x y =
      -Complex.I * X (e1 x) (e0 y) + Complex.I * X (e0 x) (e1 y) := by
  rw [trC_kron_apply]; simp [pY]

lemma trC_Z_apply (X : Mat8) (x y : Fin 4) :
    BlockU.trC (kronABC 1 pauliZ * X) x y = X (e0 x) (e0 y) - X (e1 x) (e1 y) := by
  rw [trC_kron_apply]; simp [pauliZ]; ring

/-- Re-indexing `Fin 8 × Fin 8` as `(Fin 4 × Fin 2)²`. -/
lemma sum_split (f : Fin 8 → Fin 8 → ℝ) :
    ∑ x : Fin 4, ∑ y : Fin 4,
        (f (e0 x) (e0 y) + f (e0 x) (e1 y) + f (e1 x) (e0 y) + f (e1 x) (e1 y))
      = ∑ i : Fin 8, ∑ j : Fin 8, f i j := by
  simp [Fin.sum_univ_four, Fin.sum_univ_eight, e0, e1]
  ring

/-- The 2×2 parallelogram law behind the identity: `{1,σx,σy,σz}/√2` is an ONB of
    `Mat2`, so the four C-Pauli coefficients of a 2×2 block carry twice its
    squared norm. -/
lemma ptwise (a b p d : ℂ) :
    Complex.normSq (a + d) + Complex.normSq (p + b)
      + Complex.normSq (-Complex.I * p + Complex.I * b) + Complex.normSq (a - d)
    = 2 * (Complex.normSq a + Complex.normSq b + Complex.normSq p + Complex.normSq d) := by
  simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  ring

lemma key (X : Mat8) (x y : Fin 4) :
    Complex.normSq (BlockU.trC X x y)
      + Complex.normSq (BlockU.trC (kronABC 1 pauliX * X) x y)
      + Complex.normSq (BlockU.trC (kronABC 1 pY * X) x y)
      + Complex.normSq (BlockU.trC (kronABC 1 pauliZ * X) x y)
    = 2 * (Complex.normSq (X (e0 x) (e0 y)) + Complex.normSq (X (e0 x) (e1 y))
        + Complex.normSq (X (e1 x) (e0 y)) + Complex.normSq (X (e1 x) (e1 y))) := by
  rw [trC_X_apply, trC_Y_apply, trC_Z_apply, trC_apply]
  exact ptwise _ _ _ _

/-- The NON-identity C-Pauli content of `X`. -/
def pauliContent (X : Mat8) : ℝ :=
  HSBound.hs4 (BlockU.trC (kronABC 1 pauliX * X))
    + HSBound.hs4 (BlockU.trC (kronABC 1 pY * X))
    + HSBound.hs4 (BlockU.trC (kronABC 1 pauliZ * X))

lemma pauliContent_nonneg (X : Mat8) : 0 ≤ pauliContent X := by
  have h1 := hs4_nonneg (BlockU.trC (kronABC 1 pauliX * X))
  have h2 := hs4_nonneg (BlockU.trC (kronABC 1 pY * X))
  have h3 := hs4_nonneg (BlockU.trC (kronABC 1 pauliZ * X))
  unfold pauliContent; linarith

/-- **The C-Pauli identity.**  Purely algebraic — no unitarity is used. -/
theorem pauli_identity (X : Mat8) :
    HSBound.hs4 (BlockU.trC X) + pauliContent X = 2 * hs8 X := by
  rw [pauliContent,
    show ∀ a b c d : ℝ, a + (b + c + d) = a + b + c + d from fun _ _ _ _ => by ring,
    hs4_eq_sum, hs4_eq_sum, hs4_eq_sum, hs4_eq_sum, hs8_eq_sum,
    ← sum_split (fun i j => Complex.normSq (X i j))]
  simp only [← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => key X x y

/-! ## 2. The `HS2` configuration is a unitary -/

set_option maxHeartbeats 1600000 in
-- 64-case `fin_cases × fin_cases` on `Fin 8`.
lemma kronABC_conjTranspose (M : Mat4) (c : Mat2) : (kronABC M c)ᴴ = kronABC Mᴴ cᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kronABC, Matrix.conjTranspose_apply, Matrix.of_apply]

lemma kronABC_one_unitary {M : Mat4} (hM : IsUnitary4 M) :
    (kronABC M 1)ᴴ * kronABC M 1 = (1 : Mat8) := by
  rw [kronABC_conjTranspose, kronABC_mul, hM, Matrix.conjTranspose_one, Matrix.one_mul,
    kronABC_one]

lemma ccz8_left_unitary : (CCZ8)ᴴ * CCZ8 = (1 : Mat8) := by
  rw [ccz8_conjTranspose]; exact ccz8_mul_self

lemma mul_left_unitary {A B : Mat8} (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) :
    (A * B)ᴴ * (A * B) = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, hA,
    Matrix.one_mul, hB]

theorem cfg_unitary {M0 M2 W1 W2 : Mat4} (hM0 : IsUnitary4 M0) (hM2 : IsUnitary4 M2)
    (hW1 : IsUnitary4 W1) (hW2 : IsUnitary4 W2) :
    (embedBC W2 * kronABC M2 1 * CCZ8 * kronABC M0 1 * embedBC W1)ᴴ
      * (embedBC W2 * kronABC M2 1 * CCZ8 * kronABC M0 1 * embedBC W1) = 1 :=
  mul_left_unitary (mul_left_unitary (mul_left_unitary
    (mul_left_unitary (embedBC_unitary W2 hW2) (kronABC_one_unitary hM2)) ccz8_left_unitary)
    (kronABC_one_unitary hM0)) (embedBC_unitary W1 hW1)

lemma hs8_of_unitary {X : Mat8} (hX : Xᴴ * X = 1) : hs8 X = 8 := by
  rw [hs8, hX]; simp [Matrix.trace_one]

/-! ## 3. `HS2` ⟺ the C-Pauli lower bound -/

/-- For a unitary `X` the four C-Pauli pieces of `2‖X‖²_HS = 16` add up to `16`. -/
theorem hs4_add_pauliContent {X : Mat8} (hX : Xᴴ * X = 1) :
    HSBound.hs4 (BlockU.trC X) + pauliContent X = 16 := by
  rw [pauli_identity, hs8_of_unitary hX]; norm_num

/-- **The pointwise equivalence.**  `HSSmall (Tr_C X)` ⟺ a LOWER bound on the
    non-identity C-Pauli content; note `16 - (8+4√2) = 8-4√2`. -/
theorem hsSmall_iff_pauli {X : Mat8} (hX : Xᴴ * X = 1) :
    BlockU.HSSmall (BlockU.trC X) ↔ 8 - 4 * Real.sqrt 2 ≤ pauliContent X := by
  have h := hs4_add_pauliContent hX
  have e : BlockU.HSSmall (BlockU.trC X) ↔ HSBound.hs4 (BlockU.trC X) ≤ 8 + 4 * Real.sqrt 2 :=
    Iff.rfl
  rw [e]; constructor <;> intro hh <;> linarith

/-- **(PAULI)** — the C-Pauli lower bound, over the whole `HS2` family. -/
def PauliLB : Prop := ∀ (M0 M2 W1 W2 : Mat4), IsUnitary4 M0 → IsUnitary4 M2 →
    IsUnitary4 W1 → IsUnitary4 W2 →
    8 - 4 * Real.sqrt 2 ≤
      pauliContent (embedBC W2 * kronABC M2 1 * CCZ8 * kronABC M0 1 * embedBC W1)

/-- **`HS2` is EQUIVALENT to (PAULI).** -/
theorem hs2_iff_pauliLB : BlockU.HS2 ↔ PauliLB :=
  ⟨fun h M0 M2 W1 W2 h0 h2 h1 hw =>
      (hsSmall_iff_pauli (cfg_unitary h0 h2 h1 hw)).1 (h M0 M2 W1 W2 h0 h2 h1 hw),
   fun h M0 M2 W1 W2 h0 h2 h1 hw =>
      (hsSmall_iff_pauli (cfg_unitary h0 h2 h1 hw)).2 (h M0 M2 W1 W2 h0 h2 h1 hw)⟩

/-- (PAULI) ⇒ `Φ(5) ≤ 8cos(π/8)`, using the already-proved `HS1`. -/
theorem phiFive_of_pauliLB (h : PauliLB) :
    ∀ U : Mat8, UnitaryNeighborCircuit 5 U →
      Complex.normSq (Matrix.trace (Uᴴ * CCX)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2 :=
  BlockU.phiFive_of_HS2 (hs2_iff_pauliLB.2 h)

/-- The budget in distance form: `(8 - 4√2)/2 = 4 - 2√2 = 8 sin²(π/8)`. -/
lemma budget_sin : 4 - 2 * Real.sqrt 2 = 8 * Real.sin (Real.pi / 8) ^ 2 := by
  have hs : Real.sin (Real.pi / 8) ^ 2 = 1 / 2 - Real.cos (2 * (Real.pi / 8)) / 2 :=
    Real.sin_sq_eq_half_sub (Real.pi / 8)
  rw [hs, show 2 * (Real.pi / 8) = Real.pi / 4 by ring, Real.cos_pi_div_four]
  ring

end PauliHS

end
