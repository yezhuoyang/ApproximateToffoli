/-
  Candidate new module: ApproxToffoli/CtrlObstruct.lean
  NOT added to the tree (the task forbade editing it).  Verified verbatim by
  lean_run_code against the built `ApproxToffoli.BlockFree`:
      {"success": true, "timed_out": false, "diagnostics": []}
  i.e. 0 errors, 0 warnings, 0 sorries.
-/
import ApproxToffoli.BlockFree

open Matrix Complex

noncomputable section

/-! ## 1. The obstruction identity -/

namespace HSObstruct
open PauliHS

/-! The four C-blocks of an 8×8, as `Mat4`s (`e0 x = 2x`, `e1 x = 2x+1`). -/
def B00 (X : Mat8) : Mat4 := Matrix.of fun x y => X (e0 x) (e0 y)
def B01 (X : Mat8) : Mat4 := Matrix.of fun x y => X (e0 x) (e1 y)
def B10 (X : Mat8) : Mat4 := Matrix.of fun x y => X (e1 x) (e0 y)
def B11 (X : Mat8) : Mat4 := Matrix.of fun x y => X (e1 x) (e1 y)

lemma trC_eq_B00_add_B11 (X : Mat8) : BlockU.trC X = B00 X + B11 X := by
  ext x y; simp [BlockU.trC, B00, B11, e0, e1, Matrix.of_apply]

lemma ptwise2 (p b : ℂ) :
    Complex.normSq (p + b) + Complex.normSq (-Complex.I * p + Complex.I * b)
      = 2 * (Complex.normSq p + Complex.normSq b) := by
  simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  ring

lemma xy_slots (X : Mat8) :
    HSBound.hs4 (BlockU.trC (kronABC 1 pauliX * X))
      + HSBound.hs4 (BlockU.trC (kronABC 1 pY * X))
      = 2 * HSBound.hs4 (B01 X) + 2 * HSBound.hs4 (B10 X) := by
  rw [hs4_eq_sum, hs4_eq_sum, hs4_eq_sum, hs4_eq_sum,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [trC_X_apply, trC_Y_apply]
  have h := ptwise2 (X (e1 x) (e0 y)) (X (e0 x) (e1 y))
  simp only [B01, B10, Matrix.of_apply]
  linarith [h]

lemma pauliContent_eq (X : Mat8) :
    PauliHS.pauliContent X
      = 2 * HSBound.hs4 (B01 X) + 2 * HSBound.hs4 (B10 X)
        + HSBound.hs4 (B00 X - B11 X) := by
  have hz : BlockU.trC (kronABC 1 pauliZ * X) = B00 X - B11 X := by
    ext x y; rw [trC_Z_apply]; simp [B00, B11, Matrix.of_apply]
  rw [PauliHS.pauliContent, hz]
  linarith [xy_slots X]

/-- **THE OBSTRUCTION IDENTITY.**  No unitarity is used. -/
theorem obstruction_identity (X : Mat8) :
    HSBound.hs4 (BlockU.trC X)
      + (2 * HSBound.hs4 (B01 X) + 2 * HSBound.hs4 (B10 X)
          + HSBound.hs4 (B00 X - B11 X))
      = 2 * PauliHS.hs8 X := by
  rw [← pauliContent_eq]; exact PauliHS.pauli_identity X

lemma sum8_split (f : Fin 8 → ℝ) : ∑ j : Fin 8, f j = ∑ y : Fin 4, (f (e0 y) + f (e1 y)) := by
  simp [Fin.sum_univ_eight, Fin.sum_univ_four, e0, e1]; ring

lemma row_sum {X : Mat8} (h : X * Xᴴ = 1) (i : Fin 8) :
    ∑ j : Fin 8, Complex.normSq (X i j) = 1 := by
  have h2 : (X * Xᴴ) i i = 1 := by rw [h]; simp
  rw [Matrix.mul_apply] at h2
  have h1 : ∑ j : Fin 8, ((Complex.normSq (X i j) : ℝ) : ℂ) = 1 := by
    simpa [Matrix.conjTranspose_apply, Complex.mul_conj] using h2
  simpa using congrArg Complex.re h1

lemma col_sum {X : Mat8} (h : Xᴴ * X = 1) (j : Fin 8) :
    ∑ i : Fin 8, Complex.normSq (X i j) = 1 := by
  have h2 : (Xᴴ * X) j j = 1 := by rw [h]; simp
  rw [Matrix.mul_apply] at h2
  have h1 : ∑ i : Fin 8, ((Complex.normSq (X i j) : ℝ) : ℂ) = 1 := by
    have e : ∀ i : Fin 8, Xᴴ j i * X i j = ((Complex.normSq (X i j) : ℝ) : ℂ) := fun i => by
      rw [Matrix.conjTranspose_apply, show star (X i j) = (starRingEnd ℂ) (X i j) from rfl,
        mul_comm, Complex.mul_conj]
    rw [← h2]; exact (Finset.sum_congr rfl fun i _ => (e i)).symm
  simpa using congrArg Complex.re h1

lemma rows0 {X : Mat8} (h : X * Xᴴ = 1) :
    HSBound.hs4 (B00 X) + HSBound.hs4 (B01 X) = 4 := by
  rw [hs4_eq_sum, hs4_eq_sum, ← Finset.sum_add_distrib]
  have key : ∀ x : Fin 4, (∑ y : Fin 4, Complex.normSq (B00 X x y))
        + ∑ y : Fin 4, Complex.normSq (B01 X x y) = 1 := by
    intro x
    have e : (∑ y : Fin 4, Complex.normSq (B00 X x y))
        + ∑ y : Fin 4, Complex.normSq (B01 X x y)
        = ∑ j : Fin 8, Complex.normSq (X (e0 x) j) := by
      rw [sum8_split (fun j => Complex.normSq (X (e0 x) j)), ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun y _ => by simp [B00, B01, Matrix.of_apply]
    rw [e]; exact row_sum h (e0 x)
  rw [Finset.sum_congr rfl fun x _ => key x]; simp

lemma cols0 {X : Mat8} (h : Xᴴ * X = 1) :
    HSBound.hs4 (B00 X) + HSBound.hs4 (B10 X) = 4 := by
  rw [hs4_eq_sum, hs4_eq_sum,
    Finset.sum_comm (γ := Fin 4) (f := fun x y => Complex.normSq (B00 X x y)),
    Finset.sum_comm (γ := Fin 4) (f := fun x y => Complex.normSq (B10 X x y)),
    ← Finset.sum_add_distrib]
  have key : ∀ y : Fin 4, (∑ x : Fin 4, Complex.normSq (B00 X x y))
        + ∑ x : Fin 4, Complex.normSq (B10 X x y) = 1 := by
    intro y
    have e : (∑ x : Fin 4, Complex.normSq (B00 X x y))
        + ∑ x : Fin 4, Complex.normSq (B10 X x y)
        = ∑ i : Fin 8, Complex.normSq (X i (e0 y)) := by
      rw [sum8_split (fun i => Complex.normSq (X i (e0 y))), ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by simp [B00, B10, Matrix.of_apply]
    rw [e]; exact col_sum h (e0 y)
  rw [Finset.sum_congr rfl fun y _ => key y]; simp

theorem hs4_B01_eq_B10 {X : Mat8} (h : Xᴴ * X = 1) :
    HSBound.hs4 (B01 X) = HSBound.hs4 (B10 X) := by
  have h' : X * Xᴴ = 1 := mul_eq_one_comm.mp h
  linarith [rows0 h', cols0 h]

/-- **`‖tr_C X‖² = 16 − 4‖X₀₁‖² − ‖X₀₀−X₁₁‖²`** for unitary `X`. -/
theorem obstruction_unitary {X : Mat8} (h : Xᴴ * X = 1) :
    HSBound.hs4 (BlockU.trC X)
      = 16 - 4 * HSBound.hs4 (B01 X) - HSBound.hs4 (B00 X - B11 X) := by
  have hid := obstruction_identity X
  rw [PauliHS.hs8_of_unitary h] at hid
  linarith [hs4_B01_eq_B10 h]

theorem hsSmall_iff_defect {X : Mat8} (h : Xᴴ * X = 1) :
    BlockU.HSSmall (BlockU.trC X) ↔
      8 - 4 * Real.sqrt 2 ≤ 4 * HSBound.hs4 (B01 X) + HSBound.hs4 (B00 X - B11 X) := by
  have e : BlockU.HSSmall (BlockU.trC X)
      ↔ HSBound.hs4 (BlockU.trC X) ≤ 8 + 4 * Real.sqrt 2 := Iff.rfl
  rw [e, obstruction_unitary h]
  constructor <;> intro hh <;> linarith

/-- **The easy regime is discharged.** -/
theorem hsSmall_of_offdiag_large {X : Mat8} (h : Xᴴ * X = 1)
    (hs : 2 - Real.sqrt 2 ≤ HSBound.hs4 (B01 X)) : BlockU.HSSmall (BlockU.trC X) := by
  rw [hsSmall_iff_defect h]
  linarith [PauliHS.hs4_nonneg (B00 X - B11 X)]

/-- **The regime split.**  Only the NEARLY C-BLOCK-DIAGONAL case is left. -/
theorem hsSmall_of_near {X : Mat8} (h : Xᴴ * X = 1)
    (hnear : HSBound.hs4 (B01 X) < 2 - Real.sqrt 2 →
      8 - 4 * Real.sqrt 2 ≤ 4 * HSBound.hs4 (B01 X) + HSBound.hs4 (B00 X - B11 X)) :
    BlockU.HSSmall (BlockU.trC X) := by
  by_cases hc : 2 - Real.sqrt 2 ≤ HSBound.hs4 (B01 X)
  · exact hsSmall_of_offdiag_large h hc
  · exact (hsSmall_iff_defect h).2 (hnear (lt_of_not_ge hc))

end HSObstruct

/-! ## 2. The controlled closed form -/

namespace HSCtrlForm

/-- `|11⟩⟨11|` on the AB factor — the rank-one projection `CCZ8` reflects about. -/
def E33 : Mat4 := Matrix.of fun i j => if i = 3 ∧ j = 3 then (1 : ℂ) else 0

/-- `P` is a rank-one orthogonal projection on `Mat4`. -/
def IsRank1Proj4 (P : Mat4) : Prop := Pᴴ = P ∧ P * P = P ∧ Matrix.trace P = 1

lemma E33_conjTranspose : E33ᴴ = E33 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [E33, Matrix.conjTranspose_apply, Matrix.of_apply]
lemma E33_mul_self : E33 * E33 = E33 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [E33, Matrix.mul_apply, Matrix.of_apply]
lemma E33_trace : Matrix.trace E33 = 1 := by
  simp [E33, Matrix.trace, Matrix.diag_apply, Matrix.of_apply]

lemma isRank1Proj4_conj {V : Mat4} (hV : V * Vᴴ = 1) : IsRank1Proj4 (Vᴴ * E33 * V) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      E33_conjTranspose, Matrix.mul_assoc]
  · calc Vᴴ * E33 * V * (Vᴴ * E33 * V)
        = Vᴴ * E33 * (V * Vᴴ) * E33 * V := by noncomm_ring
      _ = Vᴴ * (E33 * E33) * V := by rw [hV, Matrix.mul_one]; noncomm_ring
      _ = Vᴴ * E33 * V := by rw [E33_mul_self]
  · calc Matrix.trace (Vᴴ * E33 * V)
        = Matrix.trace (Vᴴ * (E33 * V)) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace (E33 * V * Vᴴ) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace E33 := by rw [Matrix.mul_assoc, hV, Matrix.mul_one]
      _ = 1 := E33_trace

/-- **`CCZ8` is a C-CONTROLLED AB gate.** -/
lemma ccz8_eq_ctrl : CCZ8 = kronABC 1 proj0 + kronABC (1 - E33 - E33) proj1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CCZ8, kronABC, proj0, proj1, E33, Matrix.of_apply, Matrix.one_apply]

/-- **THE CLOSED FORM: the middle of the `HS2` word is a C-controlled AB gate whose
    two branches differ by a rank-one reflection.** -/
theorem middle_eq_ctrl (M0 M2 : Mat4) :
    kronABC M2 1 * CCZ8 * kronABC M0 1
      = kronABC (M2 * M0) proj0
        + kronABC (M2 * M0 - M2 * E33 * M0 - M2 * E33 * M0) proj1 := by
  calc kronABC M2 1 * CCZ8 * kronABC M0 1
      = kronABC M2 1 * kronABC 1 proj0 * kronABC M0 1
        + kronABC M2 1 * kronABC (1 - E33 - E33) proj1 * kronABC M0 1 := by
        rw [ccz8_eq_ctrl]; noncomm_ring
    _ = kronABC (M2 * 1 * M0) (1 * proj0 * 1)
        + kronABC (M2 * (1 - E33 - E33) * M0) (1 * proj1 * 1) := by
        rw [kronABC_mul, kronABC_mul, kronABC_mul, kronABC_mul]
    _ = kronABC (M2 * M0) proj0
        + kronABC (M2 * M0 - M2 * E33 * M0 - M2 * E33 * M0) proj1 := by
        rw [show M2 * 1 * M0 = M2 * M0 from by noncomm_ring,
          show (1 : Mat2) * proj0 * 1 = proj0 from by noncomm_ring,
          show M2 * (1 - E33 - E33) * M0
              = M2 * M0 - M2 * E33 * M0 - M2 * E33 * M0 from by noncomm_ring,
          show (1 : Mat2) * proj1 * 1 = proj1 from by noncomm_ring]

/-- **(HSCTRL)** — `HS2` in CONTROLLED form: `CCZ8`, `M₀`, `M₂` eliminated. -/
def HSCtrl : Prop := ∀ (G P W1 W2 : Mat4), IsUnitary4 G → IsRank1Proj4 P →
    IsUnitary4 W1 → IsUnitary4 W2 →
    BlockU.HSSmall (BlockU.trC (embedBC W2 *
      (kronABC G proj0 + kronABC (G * (1 - P - P)) proj1) * embedBC W1))

theorem HS2_of_HSCtrl (h : HSCtrl) : BlockU.HS2 := by
  intro M0 M2 W1 W2 hM0 hM2 hW1 hW2
  have hM0' : M0 * M0ᴴ = 1 := mul_eq_one_comm.mp hM0
  set Q : Mat4 := M0ᴴ * E33 * M0 with hQ
  have hgq : (M2 * M0) * (1 - Q - Q)
      = M2 * M0 - M2 * E33 * M0 - M2 * E33 * M0 := by
    have e : (M2 * M0) * Q = M2 * E33 * M0 := by
      rw [hQ]
      calc (M2 * M0) * (M0ᴴ * E33 * M0) = M2 * (M0 * M0ᴴ) * E33 * M0 := by noncomm_ring
        _ = M2 * E33 * M0 := by rw [hM0']; noncomm_ring
    calc (M2 * M0) * (1 - Q - Q) = M2 * M0 - (M2 * M0) * Q - (M2 * M0) * Q := by noncomm_ring
      _ = M2 * M0 - M2 * E33 * M0 - M2 * E33 * M0 := by rw [e]
  have key : embedBC W2 * kronABC M2 1 * CCZ8 * kronABC M0 1 * embedBC W1
      = embedBC W2 * (kronABC (M2 * M0) proj0
          + kronABC ((M2 * M0) * (1 - Q - Q)) proj1) * embedBC W1 := by
    rw [hgq, ← middle_eq_ctrl]; noncomm_ring
  rw [key]
  exact h (M2 * M0) Q W1 W2 (isUnitary4_mul hM2 hM0) (isRank1Proj4_conj hM0') hW1 hW2

/-! ### The controlled word is unitary, so the obstruction identity applies to it -/

lemma kronABC_zero_right (M : Mat4) : kronABC M (0 : Mat2) = 0 := by
  ext i j; simp [kronABC, Matrix.of_apply]
lemma kronABC_add_right (M : Mat4) (b c : Mat2) :
    kronABC M b + kronABC M c = kronABC M (b + c) := by
  ext i j; simp [kronABC, Matrix.of_apply, mul_add]
lemma proj0_add_proj1 : proj0 + proj1 = (1 : Mat2) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj0, proj1]
lemma p00 : proj0 * proj0 = proj0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj0, Matrix.mul_apply, Fin.sum_univ_two]
lemma p11 : proj1 * proj1 = proj1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj1, Matrix.mul_apply, Fin.sum_univ_two]
lemma p01 : proj0 * proj1 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj0, proj1, Matrix.mul_apply, Fin.sum_univ_two]
lemma p10 : proj1 * proj0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj0, proj1, Matrix.mul_apply, Fin.sum_univ_two]
lemma p0h : proj0ᴴ = proj0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj0, Matrix.conjTranspose_apply]
lemma p1h : proj1ᴴ = proj1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj1, Matrix.conjTranspose_apply]

/-- A rank-one reflection is a Hermitian involution, hence unitary. -/
lemma refl_unitary {P : Mat4} (hP : IsRank1Proj4 P) : IsUnitary4 ((1 : Mat4) - P - P) := by
  obtain ⟨hPh, hPp, -⟩ := hP
  have e : ((1 : Mat4) - P - P)ᴴ = 1 - P - P := by simp [Matrix.conjTranspose_sub, hPh]
  change ((1 : Mat4) - P - P)ᴴ * (1 - P - P) = 1
  rw [e]
  calc ((1 : Mat4) - P - P) * (1 - P - P)
      = 1 - P - P - P - P + (P * P + P * P + P * P + P * P) := by noncomm_ring
    _ = 1 := by rw [hPp]; noncomm_ring

lemma ctrlMid_unitary {G P : Mat4} (hG : IsUnitary4 G) (hP : IsRank1Proj4 P) :
    (kronABC G proj0 + kronABC (G * (1 - P - P)) proj1)ᴴ
      * (kronABC G proj0 + kronABC (G * (1 - P - P)) proj1) = 1 := by
  have hGG : Gᴴ * G = 1 := hG
  have hGR : (G * (1 - P - P))ᴴ * (G * (1 - P - P)) = 1 := isUnitary4_mul hG (refl_unitary hP)
  set A : Mat8 := kronABC G proj0 with hA
  set B : Mat8 := kronABC (G * (1 - P - P)) proj1 with hB
  have expand : (A + B)ᴴ * (A + B) = Aᴴ * A + Aᴴ * B + (Bᴴ * A + Bᴴ * B) := by
    rw [Matrix.conjTranspose_add]; noncomm_ring
  have eAA : Aᴴ * A = kronABC 1 proj0 := by
    rw [hA, PauliHS.kronABC_conjTranspose, kronABC_mul, p0h, p00, hGG]
  have eBB : Bᴴ * B = kronABC 1 proj1 := by
    rw [hB, PauliHS.kronABC_conjTranspose, kronABC_mul, p1h, p11, hGR]
  have eAB : Aᴴ * B = 0 := by
    rw [hA, hB, PauliHS.kronABC_conjTranspose, kronABC_mul, p0h, p01, kronABC_zero_right]
  have eBA : Bᴴ * A = 0 := by
    rw [hA, hB, PauliHS.kronABC_conjTranspose, kronABC_mul, p1h, p10, kronABC_zero_right]
  rw [expand, eAA, eBB, eAB, eBA, add_zero, zero_add, kronABC_add_right, proj0_add_proj1,
    kronABC_one]

theorem ctrlWord_unitary {G P W1 W2 : Mat4} (hG : IsUnitary4 G) (hP : IsRank1Proj4 P)
    (hW1 : IsUnitary4 W1) (hW2 : IsUnitary4 W2) :
    (embedBC W2 * (kronABC G proj0 + kronABC (G * (1 - P - P)) proj1) * embedBC W1)ᴴ
      * (embedBC W2 * (kronABC G proj0 + kronABC (G * (1 - P - P)) proj1) * embedBC W1) = 1 :=
  PauliHS.mul_left_unitary
    (PauliHS.mul_left_unitary (embedBC_unitary W2 hW2) (ctrlMid_unitary hG hP))
    (embedBC_unitary W1 hW1)

/-! ## 3. The two reductions, composed -/

def ctrlWord (G P W1 W2 : Mat4) : Mat8 :=
  embedBC W2 * (kronABC G proj0 + kronABC (G * (1 - P - P)) proj1) * embedBC W1

/-- **(HSCTRLNEAR)** — `HS2` reduced to the NEARLY C-BLOCK-DIAGONAL regime of the
    CONTROLLED family: the smallest statement `n = 6, 7` is known to rest on. -/
def HSCtrlNear : Prop := ∀ (G P W1 W2 : Mat4), IsUnitary4 G → IsRank1Proj4 P →
    IsUnitary4 W1 → IsUnitary4 W2 →
    HSBound.hs4 (HSObstruct.B01 (ctrlWord G P W1 W2)) < 2 - Real.sqrt 2 →
    8 - 4 * Real.sqrt 2
      ≤ 4 * HSBound.hs4 (HSObstruct.B01 (ctrlWord G P W1 W2))
        + HSBound.hs4 (HSObstruct.B00 (ctrlWord G P W1 W2)
            - HSObstruct.B11 (ctrlWord G P W1 W2))

theorem HSCtrl_of_HSCtrlNear (h : HSCtrlNear) : HSCtrl := by
  intro G P W1 W2 hG hP hW1 hW2
  exact HSObstruct.hsSmall_of_near (ctrlWord_unitary hG hP hW1 hW2) (h G P W1 W2 hG hP hW1 hW2)

theorem HS2_of_HSCtrlNear (h : HSCtrlNear) : BlockU.HS2 :=
  HS2_of_HSCtrl (HSCtrl_of_HSCtrlNear h)

end HSCtrlForm
