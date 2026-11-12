/-
T-gate counts of the building blocks of the increment: the relative-phase Toffoli
cells (4 T gates each), the ripple (`8 k`), and the toggle (`8 a - 12`).
-/
import Mathlib
import ApproxToffoli.Line.TCount
import ApproxToffoli.Line.RippleAdd

namespace Line

open Matrix ExactLine

variable {N : ℕ}

theorem trle_rccx (top mid bot : Fin N)
    (h1 : top.val + 1 = mid.val ∨ mid.val + 1 = top.val)
    (h2 : bot.val + 1 = mid.val ∨ mid.val + 1 = bot.val) :
    TRle (rccx top mid bot h1 h2) 4 0 :=
  trle_h _ (trle_one _ tcost_pGate_neg_quarter' (trle_cx _ _ _
    (trle_one _ tcost_pGate_quarter (trle_cx _ _ _ (trle_one _ tcost_pGate_neg_quarter'
      (trle_cx _ _ _ (trle_one _ tcost_pGate_quarter (trle_h _ trle_nil))))))))

theorem trle_rtof5 (c1 c2 t : Fin N) (h1 : c1.val + 1 = c2.val ∨ c2.val + 1 = c1.val)
    (h2 : c2.val + 1 = t.val ∨ t.val + 1 = c2.val) : TRle (rtof5 c1 c2 t h1 h2) 4 0 :=
  trle_h _ (trle_one _ tcost_pGate_quarter (trle_cx _ _ _
    (trle_one _ tcost_pGate_neg_quarter' (trle_cx _ _ _ (trle_cx _ _ _
      (trle_one _ tcost_pGate_neg_quarter' (trle_cx _ _ _ (trle_cx _ _ _
        (trle_one _ tcost_pGate_quarter (trle_h _ trle_nil))))))))))

theorem trle_fwdCell (q0 q1 q2 : Fin N) (h01 : q0.val + 1 = q1.val)
    (h12 : q1.val + 1 = q2.val) : TRle (fwdCell q0 q1 q2 h01 h12) 4 0 :=
  trle_append (trle_append (trle_cx _ _ _ (trle_cx _ _ _ (trle_x _ trle_nil)))
    (trle_rccx _ _ _ _ _)) (trle_cx _ _ _ (trle_x _ trle_nil))

theorem trle_revCell (q0 q1 q2 : Fin N) (h01 : q0.val + 1 = q1.val)
    (h12 : q1.val + 1 = q2.val) : TRle (revCell q0 q1 q2 h01 h12) 4 0 :=
  trle_append (trle_append (trle_cx _ _ _ (trle_x _ (trle_x _ trle_nil)))
    (trle_rccx _ _ _ _ _)) (trle_cx _ _ _ (trle_cx _ _ _ (trle_cx _ _ _ (trle_x _ trle_nil))))

theorem trle_fwdAt (N o : ℕ) : TRle (fwdAt N o) 4 0 := by
  unfold fwdAt
  split_ifs
  · exact trle_fwdCell _ _ _ _ _
  · exact trle_mono trle_nil (by omega) le_rfl

theorem trle_revAt (N o : ℕ) : TRle (revAt N o) 4 0 := by
  unfold revAt
  split_ifs
  · exact trle_revCell _ _ _ _ _
  · exact trle_mono trle_nil (by omega) le_rfl

theorem trle_copyAt (N o : ℕ) (gap : Bool) : TRle (copyAt N o gap) 0 0 := by
  cases gap <;> rw [copyAt] <;> split_ifs <;>
    repeat first
      | exact trle_nil
      | apply trle_cx

theorem trle_rippleAt (N o k : ℕ) (gap : Bool) : TRle (rippleAt N o k gap) (8 * k) 0 := by
  induction k generalizing o with
  | zero => exact trle_copyAt N o gap
  | succ k ih =>
    exact trle_mono (trle_append (trle_append (trle_fwdAt N o) (ih (o + 2)))
      (trle_revAt N o)) (by omega) le_rfl

theorem trle_ripple (N k : ℕ) (gap : Bool) : TRle (ripple N k gap) (8 * k) 0 :=
  trle_rippleAt N 0 k gap

/-! ### The toggle -/

theorem trle_stepGate (N s : ℕ) : TRle (stepGate N s) (4 * (s % 2)) 0 := by
  unfold stepGate
  split_ifs with h h2
  · exact trle_mono (trle_cx _ _ _ trle_nil) (by omega) le_rfl
  · exact trle_mono (trle_rccx _ _ _ _ _) (by omega) le_rfl
  · exact trle_mono trle_nil (by omega) le_rfl

theorem trle_steps (N n : ℕ) : TRle (steps N n) (4 * (n / 2)) 0 := by
  induction n with
  | zero => exact trle_nil
  | succ n ih =>
    exact trle_mono (trle_append ih (trle_stepGate N n)) (by omega) le_rfl

theorem trle_chCirc (q0 q1 : Fin N) (h : q0.val + 1 = q1.val) : TRle (chCirc q0 q1 h) 2 0 :=
  trle_one _ tcost_rGate (trle_cx _ _ _ (trle_one _ tcost_rGate_transpose trle_nil))

theorem trle_baseCirc (q3 q2 q1 : Fin N) (h32 : q3.val + 1 = q2.val)
    (h21 : q2.val + 1 = q1.val) : TRle (baseCirc q3 q2 q1 h32 h21) 0 0 :=
  trle_h _ (trle_cx _ _ _ (trle_cx _ _ _ (trle_cx _ _ _ (trle_h _ trle_nil))))

/-- The toggle has at most `8 a - 12` T gates. -/
theorem trle_mark (a : ℕ) (hN : 2 * a ≤ N) (ha : 2 ≤ a) :
    TRle (mark a hN ha) (8 * a - 12) 0 := by
  unfold mark
  exact trle_mono (trle_append (trle_append (trle_append (trle_append (trle_chCirc _ _ _)
    (trle_steps N _)) (trle_baseCirc _ _ _ _ _)) (trle_invCirc (trle_steps N _)))
    (trle_chCirc _ _ _)) (by omega) le_rfl

end Line
