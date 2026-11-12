/-
Exact synthesis on a line with CNOT, T and rotation counts.

The circuit of `exactLine_66` (`Line/Main.lean`) is `H · F · inc · F⁻¹ · inc⁻¹ · P(θ) · H`.
Its one-qubit gates split into Clifford+T gates with at most `36 (N - 1)` T gates (all
of them in `inc` and `inc⁻¹`) and at most `4 N - 1` phase gates of arbitrary angle
(`2 (N - 1) + 1` in `F`, as many in `F⁻¹`, and `P(θ)`).
-/
import Mathlib
import ApproxToffoli.Line.TInc
import ApproxToffoli.Line.Main

namespace Line

open Matrix ExactLine

variable {N : ℕ}

/-- The T count of the whole circuit: twice that of the increment; the rotations are
those of `F`, of `F⁻¹`, and `P(θ)`. -/
theorem trle_exactCirc {F inc : List (Gate N)} {TI RF : ℕ} (hF : TRle F 0 RF)
    (hI : TRle inc TI 0) (q : Fin N) (θ : ℝ) :
    TRle (exactCirc F inc q θ) (2 * TI) (2 * RF + 1) := by
  unfold exactCirc
  exact trle_mono (trle_append (trle_append (trle_append (trle_append (trle_append
    (trle_h q trle_nil) hF) hI) (trle_invCirc hF)) (trle_invCirc hI))
    (trle_rot q θ (trle_h q trle_nil))) (by omega) (by omega)

theorem exists_increment_T_aux {a k : ℕ} {gap : Bool} (ha : 2 ≤ a) (hka : k ≤ a)
    (hat : 2 * a ≤ rippleTop k gap) (ht : rippleTop k gap = N - 1) (hN : 4 ≤ N)
    (hs : a + (k + 1) = N - 1)
    (hc : 2 * (13 * k + (if gap then 4 else 1)) + (8 * a - 9) + (24 * a - 19)
      ≤ 29 * (N - 1))
    (hT : 16 * k + 20 * a - 20 ≤ 18 * (N - 1)) :
    ∃ (a k : ℕ) (gap : Bool) (inc : List (Gate N)) (ι : Equiv.Perm (St N)),
      k ≤ a ∧ 2 * a ≤ rippleTop k gap ∧ rippleTop k gap = N - 1 ∧ a + (k + 1) = N - 1 ∧
      UnitaryGates inc ∧ cnots inc ≤ 29 * (N - 1) ∧ UMono (circMat inc) ι ∧
      (∀ x : St N, wire (ι x) 0 = wire x 0 ∧ (wire x 0 = true →
        val a k gap (ι x) = (val a k gap x + 1) % 2 ^ (N - 1))) ∧
      TRle inc (18 * (N - 1)) 0 := by
  have hN' : rippleTop k gap < N := by omega
  have h2a : 2 * a < N := by omega
  obtain ⟨ι, hι, hs'⟩ := inc_general (N := N) ha hka hat hN'
  refine ⟨a, k, gap, _, ι, hka, hat, ht, hs,
    unitaryGates_incOf (unitaryGates_ripple N k gap) (unitaryGates_mark a _ ha)
      (lowInc_spec (N := N) ⟨ha, h2a⟩).2.1, ?_, hι, ?_,
    trle_mono (trle_inc_general N a k gap _ ha) hT le_rfl⟩
  · rw [cnots_incOf, cnots_ripple k gap hN', cnots_mark,
      (lowInc_spec (N := N) ⟨ha, h2a⟩).1]
    exact hc
  · rw [← hs]
    exact hs'

/-- **The increment on a line, with its T count.**  The increment of
`exists_increment` has at most `18 (N - 1)` T gates and no rotation. -/
theorem exists_increment_T (hN : 4 ≤ N) :
    ∃ (a k : ℕ) (gap : Bool) (inc : List (Gate N)) (ι : Equiv.Perm (St N)),
      k ≤ a ∧ 2 * a ≤ rippleTop k gap ∧ rippleTop k gap = N - 1 ∧ a + (k + 1) = N - 1 ∧
      UnitaryGates inc ∧ cnots inc ≤ 29 * (N - 1) ∧ UMono (circMat inc) ι ∧
      (∀ x : St N, wire (ι x) 0 = wire x 0 ∧ (wire x 0 = true →
        val a k gap (ι x) = (val a k gap x + 1) % 2 ^ (N - 1))) ∧
      TRle inc (18 * (N - 1)) 0 := by
  rcases Nat.lt_or_ge N 5 with h5 | h5
  · have h4 : N = 4 := by omega
    subst h4
    obtain ⟨ι, hι, hs⟩ := inc_small (N := 4) (k := 1) (gap := false) le_rfl
      (by decide) (by decide)
    refine ⟨1, 1, false, _, ι, le_rfl, by decide, rfl, rfl,
      unitaryGates_incOf (unitaryGates_ripple 4 1 false)
        (unitaryGates_cons_cx _ _ _ unitaryGates_nil)
        (unitaryGates_cons_cx _ _ _ (unitaryGates_cons_one _ xGate_unitary
          unitaryGates_nil)), ?_, hι, hs,
      trle_mono (trle_inc_small 4 1 false _) (by decide) le_rfl⟩
    rw [cnots_incOf, cnots_ripple 1 false (by decide)]
    exact (by decide : 2 * (13 * 1 + 1) + 1 + 1 ≤ 29 * (4 - 1))
  · rcases Nat.even_or_odd' (N - 1) with ⟨a, ha | ha⟩
    · refine exists_increment_T_aux (a := a) (k := a - 1) (gap := true) (by omega) (by omega)
        ?_ ?_ hN (by omega) ?_ (by omega)
      · rw [rippleTop_true]
        omega
      · rw [rippleTop_true]
        omega
      · simp only [↓reduceIte]
        omega
    · refine exists_increment_T_aux (a := a) (k := a) (gap := false) (by omega) le_rfl
        ?_ ?_ hN (by omega) ?_ (by omega)
      · rw [rippleTop_false]
        omega
      · rw [rippleTop_false]
        omega
      · simp only [Bool.false_eq_true, ↓reduceIte]
        omega

/-- **Exact synthesis on a line with CNOT, T and rotation counts.**  For every `N ≥ 4`
the conditional is exactly a circuit of adjacent CNOTs and unitary one-qubit gates with
at most `66 (N - 1)` CNOTs, whose one-qubit gates split into Clifford+T gates with at
most `36 (N - 1)` T gates and at most `4 N - 1` phase gates of arbitrary angle. -/
theorem exactLine_66_T : ExactLineTGoal := by
  intro N hN
  have h0 : 0 < N := by omega
  obtain ⟨a, k, gap, inc, ι, hka, hat, ht, hs, hU, hc, ⟨φ, hφ, hA⟩, hι, hT⟩ :=
    exists_increment_T hN
  have hm1 : 1 ≤ N - 1 := by omega
  have hmN : N - 1 + 1 ≤ N := by omega
  have hF : circMat (phaseOp N (N - 1)
        (fun j => Real.pi / 2 ^ (N - 1) * (wt a k (rippleTop k gap) j : ℝ)))
      = Matrix.diagonal (fun x : St N =>
          if wire x 0 then e (Real.pi / 2 ^ (N - 1) * (val a k gap x : ℝ)) else 1) := by
    rw [circMat_phaseOp (N - 1) hm1 hmN]
    congr 1
    funext x
    rw [ang_sum, sum_wt a k gap (N - 1) (by omega) (by omega) (by omega)]
  have hS : ∀ D : St N → ℂ, (∀ x, D x = if (∀ r, x r = true) then (-1 : ℂ) else 1) →
      Matrix.diagonal D = signMat N := fun D hD => by
    unfold signMat
    congr 1
    funext x
    exact hD x
  refine ⟨exactCirc (phaseOp N (N - 1)
      (fun j => Real.pi / 2 ^ (N - 1) * (wt a k (rippleTop k gap) j : ℝ))) inc ⟨0, h0⟩
      (Real.pi / 2 ^ (N - 1)),
    unitaryGates_exactCirc (unitaryGates_phaseOp N _ _) hU _ _, ?_, ?_, ?_⟩
  · rw [cnots_exactCirc, cnots_phaseOp (N - 1) hm1 hmN]
    omega
  · rw [circMat_exactCirc, hF, hA, commutator_eq_diagonal ι φ _ hφ, oneMat_pGate,
      mono_one_eq_diagonal, Matrix.diagonal_mul_diagonal,
      hS _ (sign_entry hka hat ht hs h0 ι hι)]
    exact hGate_sign_hGate _
  · exact trle_mono (trle_exactCirc (trle_phaseOp N (N - 1) _) hT _ _) (by omega) (by omega)

/-- **The resource estimate.**  With at most `36 (N - 1)` T gates and at most `4 N - 1`
rotations, the estimate is at most `36 (N - 1) + 3 (4 N - 1) log2 ((4 N - 1) / ε)`. -/
theorem tEstimate_le (N : ℕ) (hN : 4 ≤ N) (t r : ℕ) (ht : t ≤ 36 * (N - 1))
    (hr : r ≤ 4 * N - 1) (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    tEstimate t r ε ≤ 36 * ((N : ℝ) - 1)
      + 3 * (4 * (N : ℝ) - 1) * Real.logb 2 ((4 * (N : ℝ) - 1) / ε) := by
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have htr : (t : ℝ) ≤ 36 * ((N : ℝ) - 1) := by
    have h : ((t : ℕ) : ℝ) ≤ ((36 * (N - 1) : ℕ) : ℝ) := by exact_mod_cast ht
    rw [Nat.cast_mul, Nat.cast_sub (by omega)] at h
    simpa using h
  have hrr : (r : ℝ) ≤ 4 * (N : ℝ) - 1 := by
    have h : ((r : ℕ) : ℝ) ≤ ((4 * N - 1 : ℕ) : ℝ) := by exact_mod_cast hr
    rw [Nat.cast_sub (by omega), Nat.cast_mul] at h
    simpa using h
  have hR1 : (1 : ℝ) ≤ 4 * (N : ℝ) - 1 := by linarith
  have hlogR : 0 ≤ Real.logb 2 ((4 * (N : ℝ) - 1) / ε) := by
    refine Real.logb_nonneg one_lt_two ?_
    rw [le_div_iff₀ h0]
    linarith
  unfold tEstimate
  split_ifs with hz
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * (N : ℝ) - 1) hlogR]
  · have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hz
    have hlogr : 0 ≤ Real.logb 2 ((r : ℝ) / ε) := by
      refine Real.logb_nonneg one_lt_two ?_
      rw [le_div_iff₀ h0]
      linarith
    have hmono : Real.logb 2 ((r : ℝ) / ε) ≤ Real.logb 2 ((4 * (N : ℝ) - 1) / ε) :=
      Real.logb_le_logb_of_le one_lt_two (div_pos (by linarith) h0)
        (div_le_div_of_nonneg_right hrr h0.le)
    have hprod : (r : ℝ) * Real.logb 2 ((r : ℝ) / ε)
        ≤ (4 * (N : ℝ) - 1) * Real.logb 2 ((4 * (N : ℝ) - 1) / ε) :=
      mul_le_mul hrr hmono hlogr (by linarith)
    linarith

end Line
