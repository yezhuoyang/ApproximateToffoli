/-
The recursion of Cirq's circuit (`CirqMcx.step`, `CirqMcx.recur`, cells 9, 10 and 11 of
the reference; Barenco et al., Lemma 7.5) and the whole circuit.

Every cell here is a block on the target qubit `N - 1` chosen by the other bits
(`ctrlMat`), and the blocks are powers of `X` (`Dsp.blk true`), so products of cells
add their angles.  `recur N k` is `X^(2^-(N-1-k))` when the qubits `0 .. k-1` are all
one, and `recur N (N-1)` is the conditional.
-/
import Mathlib
import ApproxToffoli.Free.CirqSplit

namespace CirqMcx

open Matrix Free ExactLine
open Line (St hGate pGate xGate ryGate condMat cxFun cxPerm oneMat ctrlMat m2)
open Qulin (qb cx marg fmono pc)

variable {N : ℕ}

/-! ### Cell 9. One step of the recursion -/

/-- The 2×2 fact of cell 9: `X^-s` if the control was flipped to one, after `X^s` if it
was one before. -/
theorem step_block (θ : ℝ) (p q : Bool) :
    (if xor q p then Dsp.blk true (-θ) else 1) * (if q then Dsp.blk true θ else 1)
      = Dsp.blk true (if p then (if q then θ else -θ) else 0) := by
  cases p <;> cases q <;>
    simp only [Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, Matrix.one_mul, Matrix.mul_one, Dsp.blk_zero]
  rw [← Dsp.blk_add, neg_add_cancel, Dsp.blk_zero]

/-- `pc (qb N hN) n` does not read the qubit `r` if `n ≤ r`. -/
theorem pc_qb_update (hN : 0 < N) {n r : ℕ} (hr : r < N) (hn : n ≤ r) (x : St N) (b : Bool) :
    pc (qb N hN) n (Function.update x (qb N hN r) b) = pc (qb N hN) n x :=
  Qulin.pc_update _ n _ (fun i hi => Qulin.qb_ne hN hr (by omega) (by omega)) x b

/-- **Cell 9.**  `step N k` is the block `X^s` (`s = 2^-(N-k)`) on the target when the
qubits `0 .. k-1` are all one, `X^-s` when the qubits `0 .. k-2` are all one and qubit
`k - 1` is zero, and the identity otherwise. -/
theorem circMat_step (hN : 0 < N) {k : ℕ} (hk2 : 2 ≤ k) (hkN : k + 1 ≤ N) :
    circMat (step N hN k)
      = ctrlMat (qb N hN (N - 1)) (fun x => Dsp.blk true
          (if pc (qb N hN) (k - 1) x then
            (if x (qb N hN (k - 1)) then Real.pi * (1 / 2 ^ (N - k))
              else -(Real.pi * (1 / 2 ^ (N - k))))
          else 0)) := by
  have hne : qb N hN (k - 1) ≠ qb N hN (N - 1) := Qulin.qb_ne hN (by omega) (by omega) (by omega)
  have hf : ∀ (x : St N) (b : Bool),
      pc (qb N hN) (k - 1) (Function.update x (qb N hN (k - 1)) b) = pc (qb N hN) (k - 1) x :=
    fun x b => pc_qb_update hN (by omega) le_rfl x b
  have hM : circMat (mcxK N hN k)
      = mono (Line.flipPerm (qb N hN (k - 1)) (pc (qb N hN) (k - 1)) hf) (fun _ => 1) :=
    acts_mcxK hN hk2 hkN
  have hσ : ∀ (x : St N) (b : Bool),
      Line.flipPerm (qb N hN (k - 1)) (pc (qb N hN) (k - 1)) hf
          (Function.update x (qb N hN (N - 1)) b)
        = Function.update (Line.flipPerm (qb N hN (k - 1)) (pc (qb N hN) (k - 1)) hf x)
            (qb N hN (N - 1)) b := by
    intro x b
    rw [Line.flipPerm_apply, Line.flipPerm_apply, Function.update_of_ne hne,
      pc_qb_update hN (by omega) (by omega), Function.update_comm hne]
  have hMM : mono (Line.flipPerm (qb N hN (k - 1)) (pc (qb N hN) (k - 1)) hf) (fun _ => (1 : ℂ))
      * mono (Line.flipPerm (qb N hN (k - 1)) (pc (qb N hN) (k - 1)) hf) (fun _ => (1 : ℂ))
      = 1 := by
    rw [Line.mono_mul, mul_one]
    have h1 : Line.flipPerm (qb N hN (k - 1)) (pc (qb N hN) (k - 1)) hf
        * Line.flipPerm (qb N hN (k - 1)) (pc (qb N hN) (k - 1)) hf = 1 :=
      Equiv.ext fun x => Line.flipFun_involutive _ _ hf x
    rw [h1]
    exact Line.mono_one
  unfold step
  rw [circMat_append, circMat_append, circMat_append, circMat_croot hne, circMat_croot hne, hM,
    ← Matrix.mul_assoc (ctrlMat _ _) (mono _ _),
    Dsp.ctrlMat_mul_mono _ _ _ _ hσ (fun _ _ => rfl), Matrix.mul_assoc (mono _ _),
    ← Matrix.mul_assoc (mono _ _) (mono _ _), hMM, Matrix.one_mul,
    Line.ctrlMat_mul _ _ _ (fun x b => by rw [hσ, Function.update_of_ne hne])]
  congr 1
  funext x
  rw [Line.flipPerm_apply, Function.update_self, mul_neg]
  exact step_block _ _ _

/-! ### Cell 10. The recursion -/

/-- The angles of `recur N (j+1)` and `step N (j+2)` add up to the angle of
`recur N (j+2)`. -/
theorem recur_angle (d : ℕ) (p q : Bool) :
    (if p then Real.pi * (1 / 2 ^ (d + 1)) else 0)
        + (if p then (if q then Real.pi * (1 / 2 ^ (d + 1)) else -(Real.pi * (1 / 2 ^ (d + 1))))
          else 0)
      = if p && q then Real.pi * (1 / 2 ^ d) else 0 := by
  cases p <;> cases q
  · simp
  · simp
  · simp
  · simp only [↓reduceIte, Bool.and_self]
    rw [pow_succ]
    field_simp
    ring

/-- **Cell 10.**  `recur N k` (`1 ≤ k ≤ N - 1`) is the block `X^(2^-(N-1-k))` on the
target when the qubits `0 .. k-1` are all one, and the identity otherwise. -/
theorem circMat_recur (hN : 0 < N) (j : ℕ) (hj : j + 2 ≤ N) :
    circMat (recur N hN (j + 1))
      = ctrlMat (qb N hN (N - 1)) (fun x => Dsp.blk true
          (if pc (qb N hN) (j + 1) x then Real.pi * (1 / 2 ^ (N - 1 - (j + 1))) else 0)) := by
  induction j with
  | zero =>
    rw [recur, circMat_croot (Qulin.qb_ne hN (by omega) (by omega) (by omega))]
    congr 1
    funext x
    rw [Dsp.ite_blk, show N - 1 - (0 + 1) = N - 2 by omega]
    simp [pc]
  | succ j ih =>
    obtain ⟨d, hd⟩ : ∃ d, N = d + (j + 3) := ⟨N - (j + 3), by omega⟩
    have e1 : N - 1 - (j + 1) = d + 1 := by omega
    have e2 : N - (j + 2) = d + 1 := by omega
    have e3 : N - 1 - (j + 1 + 1) = d := by omega
    rw [recur, circMat_append, ih (by omega), circMat_step hN (by omega) (by omega),
      Line.ctrlMat_mul _ _ _ (fun x b => by rw [pc_qb_update hN (by omega) (by omega)])]
    congr 1
    funext x
    rw [← Dsp.blk_add, show j + 2 - 1 = j + 1 by omega, e1, e2, e3, recur_angle]
    rfl

/-! ### Cell 11. The whole circuit -/

/-- "The first `N - 1` qubits are all one" is "all qubits other than the target are
one". -/
theorem pc_allOthers (hN : 0 < N) (x : St N) :
    pc (qb N hN) (N - 1) x = Line.allOthers (qb N hN (N - 1)) x := by
  rw [Qulin.pc_eq_decide]
  unfold Line.allOthers
  congr 1
  apply propext
  constructor
  · intro h r hr
    have hlt := r.isLt
    have h1 : r.val ≠ N - 1 := fun e => hr (by rw [← Qulin.qb_self hN r, e])
    have h2 := h r.val (by omega)
    rwa [Qulin.qb_self] at h2
  · intro h i hi
    exact h _ (Qulin.qb_ne hN (by omega) (by omega) (by omega))

/-- **Cell 11.  Cirq's circuit is the conditional**, exactly. -/
theorem circMat_cirqMcx (hN : 0 < N) (h4 : 4 ≤ N) :
    circMat (cirqMcx N hN) = condMat (qb N hN (N - 1)) := by
  obtain ⟨j, hj⟩ : ∃ j, N - 1 = j + 1 := ⟨N - 2, by omega⟩
  have hf : ∀ (x : St N) (b : Bool),
      pc (qb N hN) (N - 1) (Function.update x (qb N hN (N - 1)) b) = pc (qb N hN) (N - 1) x :=
    fun x b => pc_qb_update hN (by omega) le_rfl x b
  have h := Dsp.ctrlMat_flip (qb N hN (N - 1)) true false (pc (qb N hN) (N - 1)) hf
  have hc := circMat_recur hN j (by omega)
  rw [← hj] at hc
  unfold cirqMcx
  rw [hc]
  have hang : (fun x : St N => Dsp.blk true
        (if pc (qb N hN) (N - 1) x then Real.pi * (1 / 2 ^ (N - 1 - (N - 1))) else 0))
      = fun x => Dsp.blk true
        (if pc (qb N hN) (N - 1) x then (if false then -1 else 1) * Real.pi else 0) := by
    funext x
    rw [Nat.sub_self]
    simp
  rw [hang, h]
  have hperm : Line.flipPerm (qb N hN (N - 1)) (pc (qb N hN) (N - 1)) hf
      = Line.condPerm (qb N hN (N - 1)) := by
    apply Equiv.ext
    intro x
    rw [Line.flipPerm_apply, pc_allOthers]
    rfl
  rw [hperm]
  unfold Line.condMat
  congr 1
  funext x
  simp [Dsp.kap]

/-! ### Unitary gates -/

theorem unitaryGates_step (hN : 0 < N) (k : ℕ) : UnitaryGates (step N hN k) :=
  unitaryGates_append (unitaryGates_append (unitaryGates_append (unitaryGates_croot _ _ _)
    (unitaryGates_mcxK hN k)) (unitaryGates_croot _ _ _)) (unitaryGates_mcxK hN k)

theorem unitaryGates_recur (hN : 0 < N) (k : ℕ) : UnitaryGates (recur N hN k) := by
  induction k using recur.induct with
  | case1 => exact unitaryGates_nil
  | case2 => exact unitaryGates_croot _ _ _
  | case3 k ih => exact unitaryGates_append (unitaryGates_step hN _) ih

theorem unitaryGates_cirqMcx (hN : 0 < N) : UnitaryGates (cirqMcx N hN) :=
  unitaryGates_recur hN _

end CirqMcx
