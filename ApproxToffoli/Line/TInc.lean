/-
T-gate counts of the low incrementer (`12 a - 8`), of the increment circuit and of the
phase operator (no T gate, `2 m + 1` rotations).
-/
import Mathlib
import ApproxToffoli.Line.TBlocks
import ApproxToffoli.Line.IncCirc
import ApproxToffoli.Line.PhaseOp

namespace Line

open Matrix ExactLine

variable {N : ℕ}

/-! ### The centre -/

theorem trle_jHalf (a b c : Fin N) (h1 : a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (h2 : c.val + 1 = b.val ∨ b.val + 1 = c.val) : TRle (jHalf a b c h1 h2) 2 0 :=
  trle_one _ tcost_ryGate_quarter (trle_cx _ _ _ (trle_cx _ _ _
    (trle_one _ tcost_ryGate_quarter (trle_cx _ _ _ trle_nil))))

theorem trle_jHalfAt (N o : ℕ) : TRle (jHalfAt N o) 2 0 := by
  unfold jHalfAt
  split_ifs
  · exact trle_jHalf _ _ _ _ _
  · exact trle_mono trle_nil (by omega) le_rfl

theorem trle_halvesAt (N o n : ℕ) : TRle (halvesAt N o n) (2 * n) 0 := by
  induction n generalizing o with
  | zero => exact trle_nil
  | succ n ih =>
    exact trle_mono (trle_append (trle_jHalfAt N o) (ih (o + 2))) (by omega) le_rfl

/-- The seven-CNOT cell has four T gates (`P(±π/4)`) and two Hadamard gates. -/
theorem trle_gap7 (q s t u : Fin N) (hqs : q.val + 1 = s.val ∨ s.val + 1 = q.val)
    (hst : s.val + 1 = t.val ∨ t.val + 1 = s.val)
    (htu : t.val + 1 = u.val ∨ u.val + 1 = t.val) : TRle (gap7 q s t u hqs hst htu) 4 0 :=
  trle_h _ (trle_one _ tcost_pGate_quarter (trle_cx _ _ _
    (trle_one _ tcost_pGate_neg_quarter' (trle_cx _ _ _ (trle_cx _ _ _ (trle_cx _ _ _
      (trle_cx _ _ _ (trle_one _ tcost_pGate_quarter (trle_cx _ _ _
        (trle_one _ tcost_pGate_neg_quarter' (trle_cx _ _ _ (trle_h _ trle_nil))))))))))))

theorem trle_coreAt (N o : ℕ) : TRle (coreAt N o) 4 0 := by
  unfold coreAt
  split_ifs
  · exact trle_gap7 _ _ _ _ _ _ _
  · exact trle_mono trle_nil (by omega) le_rfl

/-- The centre has at most `4 a` T gates. -/
theorem trle_centre (N a : ℕ) : TRle (centre N a) (4 * a) 0 := by
  unfold centre
  split_ifs with h
  · exact trle_mono (trle_append (trle_append (trle_append (trle_append
      (trle_x _ (trle_x _ (trle_cx _ _ _ trle_nil))) (trle_halvesAt N 0 (a - 2)))
      (trle_coreAt N _)) (trle_invCirc (trle_halvesAt N 0 (a - 2))))
      (trle_cx _ _ _ (trle_x _ trle_nil))) (by omega) le_rfl
  · exact trle_mono trle_nil (by omega) le_rfl

/-! ### The low incrementer -/

theorem trle_incCellAt (N o : ℕ) : TRle (incCellAt N o) 4 0 := by
  unfold incCellAt
  split_ifs
  · exact trle_cx _ _ _ (trle_rtof5 _ _ _ _ _)
  · exact trle_mono trle_nil (by omega) le_rfl

theorem trle_incLoop (N m : ℕ) : TRle (incLoop N m) (4 * m) 0 := by
  induction m with
  | zero => exact trle_nil
  | succ m ih =>
    exact trle_mono (trle_append ih (trle_incCellAt N _)) (by omega) le_rfl

theorem trle_fanAt (N o : ℕ) : TRle (fanAt N o) 0 0 := by
  unfold fanAt
  split_ifs
  · exact trle_cx _ _ _ (trle_cx _ _ _ (trle_cx _ _ _ trle_nil))
  · exact trle_nil

theorem trle_fanLoop (N m : ℕ) : TRle (fanLoop N m) 0 0 := by
  induction m with
  | zero => exact trle_nil
  | succ m ih => exact trle_append (trle_fanAt N _) ih

theorem trle_xAt (N q : ℕ) : TRle (xAt N q) 0 0 := by
  unfold xAt
  split_ifs
  · exact trle_x _ trle_nil
  · exact trle_nil

theorem trle_xsAt (N n : ℕ) : TRle (xsAt N n) 0 0 := by
  induction n with
  | zero => exact trle_nil
  | succ n ih => exact trle_append ih (trle_xAt N n)

theorem trle_rest (N a : ℕ) : TRle (rest N a) (4 * (a - 1)) 0 := by
  unfold rest
  split_ifs
  · exact trle_append (trle_append (trle_incLoop N _) (trle_fanLoop N _))
      (trle_cx _ _ _ (trle_cx _ _ _ trle_nil))
  · exact trle_mono trle_nil (by omega) le_rfl

/-- The low incrementer has at most `12 a - 8` T gates. -/
theorem trle_lowInc (N a : ℕ) (ha : 1 ≤ a) : TRle (lowInc N a) (12 * a - 8) 0 := by
  unfold lowInc terminal
  exact trle_mono (trle_append (trle_append (trle_append (trle_invCirc (trle_rest N a))
    (trle_centre N a)) (trle_rest N a)) (trle_xsAt N _)) (by omega) le_rfl

/-! ### The increment -/

theorem trle_incOf {K M R : List (Gate N)} {TK TM TL : ℕ} (hK : TRle K TK 0)
    (hM : TRle M TM 0) (hR : TRle R TL 0) : TRle (incOf K M R) (2 * TK + TM + TL) 0 := by
  unfold incOf
  exact trle_mono (trle_append (trle_append (trle_append hK hM) (trle_invCirc hK)) hR)
    (by omega) le_rfl

theorem trle_markS (h : 1 < N) : TRle (markS h) 0 0 := trle_cx _ _ _ trle_nil

theorem trle_lowIncS (h : 1 < N) : TRle (lowIncS h) 0 0 :=
  trle_cx _ _ _ (trle_x _ trle_nil)

/-- The increment for `a ≥ 2` has at most `16 k + 20 a - 20` T gates. -/
theorem trle_inc_general (N a k : ℕ) (gap : Bool) (hN : 2 * a ≤ N) (ha : 2 ≤ a) :
    TRle (incOf (ripple N k gap) (mark a hN ha) (lowInc N a)) (16 * k + 20 * a - 20) 0 :=
  trle_mono (trle_incOf (trle_ripple N k gap) (trle_mark a hN ha) (trle_lowInc N a (by omega)))
    (by omega) le_rfl

/-- The increment for `a = 1` has at most `16 k` T gates. -/
theorem trle_inc_small (N k : ℕ) (gap : Bool) (h : 1 < N) :
    TRle (incOf (ripple N k gap) (markS h) (lowIncS h)) (16 * k) 0 :=
  trle_mono (trle_incOf (trle_ripple N k gap) (trle_markS h) (trle_lowIncS h))
    (by omega) le_rfl

/-! ### The phase operator -/

theorem trle_pOne (N j : ℕ) (t : ℝ) : TRle (pOne N j t) 0 1 := by
  unfold pOne
  split_ifs
  · exact trle_rot _ _ trle_nil
  · exact trle_mono trle_nil le_rfl (by omega)

theorem trle_pLayer (N : ℕ) (f : ℕ → ℝ) (n : ℕ) : TRle (pLayer N f n) 0 n := by
  induction n with
  | zero => exact trle_nil
  | succ n ih => exact trle_append ih (trle_pOne N _ _)

theorem trle_cxUp (N j : ℕ) : TRle (cxUp N j) 0 0 := by
  unfold cxUp
  split_ifs
  · exact trle_cx _ _ _ trle_nil
  · exact trle_nil

theorem trle_fanAux (N k : ℕ) : TRle (fanAux N k) 0 0 := by
  induction k with
  | zero => exact trle_cxUp N 0
  | succ k ih => exact trle_append (trle_append (trle_cxUp N _) ih) (trle_cxUp N _)

/-- The phase operator has no T gate and at most `2 m + 1` rotations. -/
theorem trle_phaseOp (N m : ℕ) (ang : ℕ → ℝ) : TRle (phaseOp N m ang) 0 (2 * m + 1) := by
  unfold phaseOp fan
  exact trle_mono (trle_append (trle_append (trle_append (trle_append (trle_pOne N 0 _)
    (trle_pLayer N _ m)) (trle_fanAux N _)) (trle_pLayer N _ m)) (trle_fanAux N _))
    le_rfl (by omega)

end Line
