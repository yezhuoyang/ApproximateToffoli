/-
Exact synthesis of the conditional on a line with at most `66 (N - 1)` CNOTs.

The circuit is `H · F · inc · F⁻¹ · inc⁻¹ · P(θ) · H` on wire `0`, with `θ = π / 2^(N-1)`,
`F = phaseOp` the phase `e^{iθ·b·val}` and `inc` the increment of `Line/IncCirc.lean`.
The commutator `inc⁻¹ F⁻¹ inc F` is diagonal (`commutator_eq_diagonal`); every address
receives `e^{-iθ}` and the address that wraps around an extra minus sign, so with `P(θ)`
it is the conditional sign `signMat N`, and `H · signMat N · H` is the conditional.
-/
import Mathlib
import ApproxToffoli.Line.IncCirc
import ApproxToffoli.Line.AddrWeight
import ApproxToffoli.Line.SignConj
import ApproxToffoli.Line.PhaseOpNs

namespace Line

open Matrix ExactLine

variable {N : ℕ}

/-! ### The phase of one step -/

/-- One step of the increment on natural numbers: every address receives `e^{-iθ}` and
the address that wraps around receives an extra minus sign (`θ = π / 2^m`). -/
theorem step_phase_nat (m v : ℕ) (hv : v < 2 ^ m) :
    star (e (Real.pi / 2 ^ m * (((v + 1) % 2 ^ m : ℕ) : ℝ))) * e (Real.pi / 2 ^ m * (v : ℝ))
      = (if v + 1 = 2 ^ m then (-1 : ℂ) else 1) * e (-(Real.pi / 2 ^ m)) := by
  rw [star_e, ← e_add]
  by_cases h : v + 1 = 2 ^ m
  · rw [if_pos h, h, Nat.mod_self]
    have hc : (v : ℝ) + 1 = 2 ^ m := by exact_mod_cast h
    have hv' : (v : ℝ) = 2 ^ m - 1 := by linarith
    have hne : (2 : ℝ) ^ m ≠ 0 := by positivity
    have : -(Real.pi / 2 ^ m * ((0 : ℕ) : ℝ)) + Real.pi / 2 ^ m * (v : ℝ)
        = Real.pi + -(Real.pi / 2 ^ m) := by
      rw [hv']
      push_cast
      field_simp
      ring
    rw [this, e_add, e_pi]
  · rw [if_neg h, Nat.mod_eq_of_lt (by omega), one_mul]
    congr 1
    push_cast
    ring

theorem val_lt (a k : ℕ) (gap : Bool) (x : St N) : val a k gap x < 2 ^ (a + (k + 1)) := by
  have h1 := Tval_lt a x
  have h2 : 2 ^ a * (targetVal k gap x + 1) ≤ 2 ^ a * 2 ^ (k + 1) :=
    Nat.mul_le_mul_left _ (targetVal_lt k gap x)
  rw [Nat.mul_add, Nat.mul_one] at h2
  unfold val
  rw [pow_add]
  omega

/-- The diagonal entry of `P(θ) · inc⁻¹ F⁻¹ inc F`: minus one on the all-ones state. -/
theorem sign_entry {a k : ℕ} {gap : Bool} (hka : k ≤ a) (hat : 2 * a ≤ rippleTop k gap)
    (ht : rippleTop k gap = N - 1) (hs : a + (k + 1) = N - 1) (hN : 0 < N)
    (ι : Equiv.Perm (St N))
    (hι : ∀ x : St N, wire (ι x) 0 = wire x 0 ∧ (wire x 0 = true →
      val a k gap (ι x) = (val a k gap x + 1) % 2 ^ (N - 1))) (x : St N) :
    (if x ⟨0, hN⟩ then e (Real.pi / 2 ^ (N - 1)) else 1)
        * (star (if wire (ι x) 0 then e (Real.pi / 2 ^ (N - 1) * (val a k gap (ι x) : ℝ))
            else 1)
          * (if wire x 0 then e (Real.pi / 2 ^ (N - 1) * (val a k gap x : ℝ)) else 1))
      = if (∀ r, x r = true) then (-1 : ℂ) else 1 := by
  rw [(hι x).1, ← wire_mk x 0 hN]
  by_cases h0 : wire x 0 = true
  · have hv : val a k gap x < 2 ^ (N - 1) := by
      rw [← hs]
      exact val_lt a k gap x
    rw [if_pos h0, if_pos h0, if_pos h0, (hι x).2 h0, step_phase_nat _ _ hv,
      if_congr (val_top hka hat ht hs hN x h0) rfl rfl, mul_comm, mul_assoc, ← e_add,
      neg_add_cancel, e_zero, mul_one]
  · have hno : ¬ ∀ r, x r = true := fun H => h0 (by rw [wire_mk x 0 hN]; exact H _)
    rw [if_neg h0, if_neg h0, if_neg h0, if_neg hno, star_one, mul_one, mul_one]

/-- The angles: `θ` times the weight of the wire. -/
theorem ang_sum (θ : ℝ) (w : ℕ → ℕ) (m : ℕ) (x : St N) :
    ∑ j ∈ Finset.Icc 1 m, (if wire x j then θ * (w j : ℝ) else 0)
      = θ * ((∑ j ∈ Finset.Icc 1 m, (if wire x j then w j else 0) : ℕ) : ℝ) := by
  rw [Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs <;> simp

/-! ### The circuit -/

/-- `H · F · inc · F⁻¹ · inc⁻¹ · P(θ) · H` on qubit `q`. -/
noncomputable def exactCirc (F inc : List (Gate N)) (q : Fin N) (θ : ℝ) : List (Gate N) :=
  [.one q hGate] ++ F ++ inc ++ invCirc F ++ invCirc inc ++ [.one q (pGate θ), .one q hGate]

theorem circMat_exactCirc (F inc : List (Gate N)) (q : Fin N) (θ : ℝ) :
    circMat (exactCirc F inc q θ)
      = oneMat q hGate * (oneMat q (pGate θ)
          * ((circMat inc)ᴴ * (circMat F)ᴴ * circMat inc * circMat F)) * oneMat q hGate := by
  simp only [exactCirc, circMat_append, circMat_invCirc, circMat, Gate.mat, Matrix.one_mul,
    Matrix.mul_assoc]

theorem cnots_exactCirc (F inc : List (Gate N)) (q : Fin N) (θ : ℝ) :
    cnots (exactCirc F inc q θ) = 2 * cnots F + 2 * cnots inc := by
  simp only [exactCirc, cnots_append, cnots_invCirc, cnots]
  omega

theorem unitaryGates_exactCirc {F inc : List (Gate N)} (hF : UnitaryGates F)
    (hI : UnitaryGates inc) (q : Fin N) (θ : ℝ) : UnitaryGates (exactCirc F inc q θ) :=
  unitaryGates_append (unitaryGates_append (unitaryGates_append (unitaryGates_append
    (unitaryGates_append (unitaryGates_cons_one q hGate_unitary unitaryGates_nil) hF) hI)
    (unitaryGates_invCirc hF)) (unitaryGates_invCirc hI))
    (unitaryGates_cons_one q (pGate_unitary θ)
      (unitaryGates_cons_one q hGate_unitary unitaryGates_nil))

/-! ### The theorem -/

/-- **Exact synthesis on a line with at most `66 (N - 1)` CNOTs.**  For every `N ≥ 4`
there is a circuit of adjacent CNOTs and unitary one-qubit gates, with at most
`66 (N - 1)` CNOTs, whose matrix is exactly the conditional with target qubit `0`. -/
theorem exactLine_66 : ExactLineGoal (fun N => 66 * (N - 1)) := by
  intro N hN
  have h0 : 0 < N := by omega
  obtain ⟨a, k, gap, inc, ι, hka, hat, ht, hs, hU, hc, ⟨φ, hφ, hA⟩, hι⟩ :=
    exists_increment hN
  have hm1 : 1 ≤ N - 1 := by omega
  have hmN : N - 1 + 1 ≤ N := by omega
  have hF : circMat (Ph.phaseOp N (N - 1)
        (fun j => Real.pi / 2 ^ (N - 1) * (wt a k (rippleTop k gap) j : ℝ)))
      = Matrix.diagonal (fun x : St N =>
          if wire x 0 then e (Real.pi / 2 ^ (N - 1) * (val a k gap x : ℝ)) else 1) := by
    rw [Ph.circMat_phaseOp (N - 1) hm1 hmN]
    congr 1
    funext x
    rw [ang_sum, sum_wt a k gap (N - 1) (by omega) (by omega) (by omega)]
  have hS : ∀ D : St N → ℂ, (∀ x, D x = if (∀ r, x r = true) then (-1 : ℂ) else 1) →
      Matrix.diagonal D = signMat N := fun D hD => by
    unfold signMat
    congr 1
    funext x
    exact hD x
  refine ⟨exactCirc (Ph.phaseOp N (N - 1)
      (fun j => Real.pi / 2 ^ (N - 1) * (wt a k (rippleTop k gap) j : ℝ))) inc ⟨0, h0⟩
      (Real.pi / 2 ^ (N - 1)),
    unitaryGates_exactCirc (Ph.unitaryGates_phaseOp N _ _) hU _ _, ?_, ?_⟩
  · show cnots _ ≤ 66 * (N - 1)
    rw [cnots_exactCirc, Ph.cnots_phaseOp (N - 1) hm1 hmN]
    omega
  · rw [circMat_exactCirc, hF, hA, commutator_eq_diagonal ι φ _ hφ, oneMat_pGate,
      mono_one_eq_diagonal, Matrix.diagonal_mul_diagonal,
      hS _ (sign_entry hka hat ht hs h0 ι hι)]
    exact hGate_sign_hGate _

end Line
