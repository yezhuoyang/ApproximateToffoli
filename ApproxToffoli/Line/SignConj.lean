/-
The conditional sign between two Hadamards is the conditional.

`hGate_sign_hGate`: `H_q · T_N · H_q = condMat q`, where `T_N = signMat N` is minus one
on the all-ones basis state.
-/
import Mathlib
import ApproxToffoli.Line.Toggle

namespace Line

open Matrix ExactLine

variable {N : ℕ}

theorem hGate_diag_hGate (p : Bool) :
    hGate * Matrix.diagonal (fun b => if p && b then (-1 : ℂ) else 1) * hGate
      = if p then xGate else 1 := by
  rw [diagonal_eq_m2, hGate_mul_mul]
  cases p
  · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, one_eq_m2]
    congr 1 <;> norm_num
  · simp only [Bool.true_and, ↓reduceIte, Bool.false_eq_true, xGate_eq_m2]
    congr 1 <;> norm_num

/-- The conditional sign is a controlled `Z` on any qubit `q`. -/
theorem signMat_eq_ctrlMat (q : Fin N) :
    signMat N = ctrlMat q (fun x =>
      Matrix.diagonal (fun b => if allOthers q x && b then (-1 : ℂ) else 1)) := by
  rw [ctrlMat_diagonal, mono_one_eq_diagonal]
  unfold signMat
  congr 1
  funext x
  have h : (∀ r, x r = true) ↔ (allOthers q x && x q) = true := by
    simp only [allOthers, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · intro H
      exact ⟨fun r _ => H r, H q⟩
    · rintro ⟨H1, H2⟩ r
      by_cases hr : r = q
      · rw [hr]
        exact H2
      · exact H1 r hr
  exact if_congr h rfl rfl

/-- **`H · T_N · H` is the conditional.** -/
theorem hGate_sign_hGate (q : Fin N) :
    oneMat q hGate * signMat N * oneMat q hGate = condMat q := by
  have h1 := ctrlMat_mul q (fun _ => hGate)
    (fun x => Matrix.diagonal (fun b => if allOthers q x && b then (-1 : ℂ) else 1))
    (fun _ _ => rfl)
  have h2 := ctrlMat_mul q
    (fun x => hGate * Matrix.diagonal (fun b => if allOthers q x && b then (-1 : ℂ) else 1))
    (fun _ => hGate) (fun x b => by simp only [allOthers_update])
  rw [signMat_eq_ctrlMat q, oneMat_eq_ctrlMat, h1, h2]
  simp only [hGate_diag_hGate]
  rw [← flip_eq_ctrlMat q (allOthers q) (fun x b => allOthers_update q x b)]
  rfl

end Line
