import ApproxToffoli.BlockCutPauli

open Matrix Complex

noncomputable section

namespace BlockFree

/-! `E₇₇`, the rank-one projection onto `|111⟩ = |11⟩_AB ⊗ |1⟩_C`. -/
def E77 : Mat8 := Matrix.of fun i j => if i = 7 ∧ j = 7 then (1 : ℂ) else 0

lemma E77_conjTranspose : E77ᴴ = E77 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E77, Matrix.conjTranspose_apply, Matrix.of_apply]

lemma E77_mul_self : E77 * E77 = E77 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E77, Matrix.mul_apply, Matrix.of_apply]

lemma E77_trace : Matrix.trace E77 = 1 := by
  simp [E77, Matrix.trace, Matrix.diag_apply, Matrix.of_apply]

lemma ccz8_eq_refl : CCZ8 = 1 - E77 - E77 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CCZ8, E77, Matrix.of_apply]

/-- `P` is a rank-one orthogonal projection on `Mat8`. -/
def IsRank1Proj (P : Mat8) : Prop := Pᴴ = P ∧ P * P = P ∧ Matrix.trace P = 1

lemma isRank1Proj_conj {V : Mat8} (hV : V * Vᴴ = 1) : IsRank1Proj (Vᴴ * E77 * V) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      E77_conjTranspose, Matrix.mul_assoc]
  · calc Vᴴ * E77 * V * (Vᴴ * E77 * V)
        = Vᴴ * E77 * (V * Vᴴ) * E77 * V := by noncomm_ring
      _ = Vᴴ * (E77 * E77) * V := by rw [hV, Matrix.mul_one]; noncomm_ring
      _ = Vᴴ * E77 * V := by rw [E77_mul_self]
  · calc Matrix.trace (Vᴴ * E77 * V)
        = Matrix.trace (Vᴴ * (E77 * V)) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace (E77 * V * Vᴴ) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace E77 := by rw [Matrix.mul_assoc, hV, Matrix.mul_one]
      _ = 1 := E77_trace

/-- **Reflection peeling.**  `A · CCZ8 · V = (A·V)·(1 − 2P)` with `P = Vᴴ E₇₇ V` a
    rank-one projection, for any unitary `V`.  This is what eliminates `M₀`. -/
lemma peel (A V : Mat8) (hV : V * Vᴴ = 1) :
    A * CCZ8 * V = A * V * (1 - (Vᴴ * E77 * V) - (Vᴴ * E77 * V)) := by
  have h1 : A * V * (Vᴴ * E77 * V) = A * E77 * V := by
    calc A * V * (Vᴴ * E77 * V) = A * (V * Vᴴ) * E77 * V := by noncomm_ring
      _ = A * E77 * V := by rw [hV, Matrix.mul_one]
  have e1 : A * CCZ8 * V = A * V - A * E77 * V - A * E77 * V := by
    rw [ccz8_eq_refl]; noncomm_ring
  have e2 : A * V * (1 - (Vᴴ * E77 * V) - (Vᴴ * E77 * V))
      = A * V - A * V * (Vᴴ * E77 * V) - A * V * (Vᴴ * E77 * V) := by noncomm_ring
  rw [e1, e2, h1]

/-- **(HSFREE)** — `HS2` with the boundary block `M₀` ELIMINATED and the rank-one
    reflection FREED: the projection no longer has to be a PRODUCT across the AB|C cut.

    Numerically TRUE and exactly TIGHT: the maximum of the left-hand side over this
    LARGER family is still exactly `8 + 4√2 = 13.6568542494924` (300 cold + 60 warm
    L-BFGS restarts, overshoot `+2.3e-14`).  Compared with `HS2` this drops the 16
    real parameters of `M₀` and replaces the constraint "the reflection vector is
    `v ⊗ e₁`" by "the reflection vector is arbitrary". -/
def HSFree : Prop := ∀ (Z0 W1 W2 : Mat4) (P : Mat8), IsUnitary4 Z0 → IsUnitary4 W1 →
    IsUnitary4 W2 → IsRank1Proj P →
    BlockU.HSSmall (BlockU.trC (embedBC W2 * kronABC Z0 1 * embedBC W1 * (1 - P - P)))

/-- **`HSFree → HS2`.** -/
theorem HS2_of_HSFree (h : HSFree) : BlockU.HS2 := by
  intro M0 M2 W1 W2 hM0 hM2 hW1 hW2
  set V : Mat8 := kronABC M0 1 * embedBC W1 with hVdef
  have hVu : Vᴴ * V = 1 :=
    PauliHS.mul_left_unitary (PauliHS.kronABC_one_unitary hM0) (embedBC_unitary W1 hW1)
  have hVu' : V * Vᴴ = 1 := mul_eq_one_comm.mp hVu
  have hk : kronABC M2 1 * kronABC M0 1 = kronABC (M2 * M0) 1 := by
    rw [kronABC_mul]; simp
  have key : embedBC W2 * kronABC M2 1 * CCZ8 * kronABC M0 1 * embedBC W1
      = embedBC W2 * kronABC (M2 * M0) 1 * embedBC W1
          * (1 - (Vᴴ * E77 * V) - (Vᴴ * E77 * V)) := by
    have e0 : embedBC W2 * kronABC M2 1 * CCZ8 * kronABC M0 1 * embedBC W1
        = (embedBC W2 * kronABC M2 1) * CCZ8 * V := by rw [hVdef]; noncomm_ring
    have e1 : embedBC W2 * kronABC (M2 * M0) 1 * embedBC W1
        = (embedBC W2 * kronABC M2 1) * V := by rw [hVdef, ← hk]; noncomm_ring
    rw [e0, e1, peel _ _ hVu']
  rw [key]
  exact h (M2 * M0) W1 W2 _ (isUnitary4_mul hM2 hM0) hW1 hW2 (isRank1Proj_conj hVu')

end BlockFree
