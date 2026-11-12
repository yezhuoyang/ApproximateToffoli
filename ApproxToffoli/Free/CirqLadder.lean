/-
The multi-controlled X with borrowed qubits of Cirq's circuit (`CirqMcx.ladder`, cells 4
and 5 of the reference; Barenco et al., Lemma 7.2): it flips the target iff all `m`
controls are one, exactly (no phase, borrowed qubits restored), with `12m - 14` CNOTs.

The chain is a palindrome of relative-phase Toffolis (`Qulin.marg`).  Its function on
basis states is the one of the ladder of the Huang–Palsberg circuit (`Qulin.wF`); its
sign is `cS`.  Each `marg` is its own inverse, so the chain is its own inverse, which
gives that the sign before the chain times the sign after it is one (`cS_wF_mul`).
-/
import Mathlib
import ApproxToffoli.Free.CirqCells

namespace CirqMcx

open Matrix Free ExactLine
open Line (St hGate pGate xGate ryGate condMat cxFun cxPerm oneMat ctrlMat m2)
open Qulin (qb cx marg fmono pc wF wSgn)

variable {N : ℕ}

/-! ### Cell 3. The relative-phase Toffoli is its own inverse -/

theorem marg_sq {u v s : Fin N} (hu : u ≠ s) (hv : v ≠ s) :
    circMat (marg u v s) * circMat (marg u v s) = 1 := by
  rw [Qulin.circMat_marg hu hv, Qulin.fmono_mul, ← Qulin.fmono_id_one]
  apply Qulin.fmono_congr
  · intro x
    simp only [Function.comp_apply, id]
    rw [Function.update_self, Function.update_of_ne hu, Function.update_of_ne hv]
    exact Qulin.flip_flip x s (x u && x v)
  · intro x
    simp only [Function.update_self, Function.update_of_ne hu, Function.update_of_ne hv]
    rw [Qulin.wSgn_flip, Qulin.wSgn_sq]

/-! ### Cell 4. The chain -/

/-- The sign of one further level of the chain: `-1` iff the controls so far are all
one and the two borrowed qubits of the level are equal. -/
def lvSgn (p u v : Bool) : ℂ := if p && (u == v) then -1 else 1

/-- The sign of `chain c a j`: `-1` iff `c 0 = 1`, `c 1 = 0`, `a 0 = 0`, times, for every
level `1 ≤ i ≤ j`, `-1` iff `c 0 .. c (i+1)` are all one and `a (i-1) = a i`. -/
def cS (c a : ℕ → Fin N) : ℕ → St N → ℂ
  | 0, x => wSgn (x (c 0)) (x (c 1)) (x (a 0))
  | j + 1, x => cS c a j x * lvSgn (pc c (j + 3) x) (x (a j)) (x (a (j + 1)))

/-- The sign of the chain does not read a qubit that is neither one of `a 0 .. a j` nor
one of `c 0 .. c (j+1)`. -/
theorem cS_update (c a : ℕ → Fin N) (j : ℕ) (s : Fin N) (hsa : ∀ i ≤ j, s ≠ a i)
    (hsc : ∀ i < j + 2, s ≠ c i) (x : St N) (b : Bool) :
    cS c a j (Function.update x s b) = cS c a j x := by
  induction j with
  | zero =>
    rw [cS, cS, Function.update_of_ne (hsa 0 le_rfl).symm,
      Function.update_of_ne (hsc 0 (by omega)).symm, Function.update_of_ne (hsc 1 (by omega)).symm]
  | succ j ih =>
    rw [cS, cS, Function.update_of_ne (hsa (j + 1) le_rfl).symm,
      Function.update_of_ne (hsa j (by omega)).symm, Qulin.pc_update c (j + 3) s hsc,
      ih (fun i hi => hsa i (Nat.le_succ_of_le hi)) (fun i hi => hsc i (Nat.lt_succ_of_lt hi))]

theorem chain_bit (s u v p : Bool) :
    xor (xor s (u && v)) (u && xor v p) = xor s (p && u) := by
  cases s <;> cases u <;> cases v <;> cases p <;> rfl

theorem chain_sgn (u v s p : Bool) (K : ℂ) :
    wSgn u (xor v p) (xor s (u && v)) * (K * wSgn u v s) = K * lvSgn (p && u) v s := by
  cases u <;> cases v <;> cases s <;> cases p <;> simp [wSgn, lvSgn]

/-- **Cell 4.  The chain** is a function up to signs: `Qulin.wF` with the sign `cS`. -/
theorem circMat_chain {k : ℕ} {c a : ℕ → Fin N} (ha : Inj (k - 2) a)
    (hca : Disj k c (k - 2) a) (j : ℕ) (hj : j < k - 2) :
    circMat (chain c a j) = fmono (wF c a j) (cS c a j) := by
  induction j with
  | zero =>
    rw [chain, Qulin.circMat_marg (hca 0 (by omega) 0 hj) (hca 1 (by omega) 0 hj)]
    apply Qulin.fmono_congr
    · intro x
      simp [wF, pc]
    · intro x
      rfl
  | succ j ih =>
    have hu : c (j + 2) ≠ a (j + 1) := hca (j + 2) (by omega) (j + 1) hj
    have hv : a j ≠ a (j + 1) := fun h => by
      have := ha j (by omega) (j + 1) hj h
      omega
    have hsa : ∀ i ≤ j, a (j + 1) ≠ a i := fun i hi h => by
      have := ha (j + 1) hj i (by omega) h
      omega
    have hsc : ∀ i < j + 2, a (j + 1) ≠ c i := fun i hi => (hca i (by omega) (j + 1) hj).symm
    rw [chain, circMat_append, circMat_append, Qulin.circMat_marg hu hv, ih (by omega),
      Qulin.fmono_mul, Qulin.fmono_mul]
    apply Qulin.fmono_congr
    · intro x
      simp only [Function.comp_apply]
      rw [Qulin.wF_update c a j _ hsa hsc, Function.update_self, Function.update_of_ne hu,
        Function.update_of_ne hv, Function.update_idem,
        Qulin.wF_of_ne c a j (c (j + 2)) (fun i hi => hca (j + 2) (by omega) i (by omega)),
        Qulin.wF_last, chain_bit]
      rfl
    · intro x
      simp only [Function.comp_apply]
      rw [Qulin.wF_update c a j _ hsa hsc, Function.update_self, Function.update_of_ne hu,
        Function.update_of_ne hv, cS_update c a j _ hsa hsc,
        Qulin.wF_of_ne c a j (c (j + 2)) (fun i hi => hca (j + 2) (by omega) i (by omega)),
        Qulin.wF_last, chain_sgn]
      rfl

/-- The chain is its own inverse. -/
theorem chain_sq {k : ℕ} {c a : ℕ → Fin N} (ha : Inj (k - 2) a) (hca : Disj k c (k - 2) a)
    (j : ℕ) (hj : j < k - 2) : circMat (chain c a j) * circMat (chain c a j) = 1 := by
  induction j with
  | zero => exact marg_sq (hca 0 (by omega) 0 hj) (hca 1 (by omega) 0 hj)
  | succ j ih =>
    have hu : c (j + 2) ≠ a (j + 1) := hca (j + 2) (by omega) (j + 1) hj
    have hv : a j ≠ a (j + 1) := fun h => by
      have := ha j (by omega) (j + 1) hj h
      omega
    have hM := marg_sq hu hv
    have hC := ih (by omega)
    rw [chain, circMat_append, circMat_append]
    calc circMat (marg (c (j + 2)) (a j) (a (j + 1)))
            * (circMat (chain c a j) * circMat (marg (c (j + 2)) (a j) (a (j + 1))))
          * (circMat (marg (c (j + 2)) (a j) (a (j + 1)))
            * (circMat (chain c a j) * circMat (marg (c (j + 2)) (a j) (a (j + 1)))))
        = circMat (marg (c (j + 2)) (a j) (a (j + 1)))
            * (circMat (chain c a j) * (circMat (marg (c (j + 2)) (a j) (a (j + 1)))
              * circMat (marg (c (j + 2)) (a j) (a (j + 1))))
            * (circMat (chain c a j) * circMat (marg (c (j + 2)) (a j) (a (j + 1))))) := by
          simp only [Matrix.mul_assoc]
      _ = circMat (marg (c (j + 2)) (a j) (a (j + 1)))
            * (circMat (chain c a j) * circMat (chain c a j)
              * circMat (marg (c (j + 2)) (a j) (a (j + 1)))) := by
          rw [hM, Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hC, Matrix.one_mul, hM]

/-- The sign of the chain after the chain times the sign before it is one. -/
theorem cS_wF_mul {k : ℕ} {c a : ℕ → Fin N} (ha : Inj (k - 2) a) (hca : Disj k c (k - 2) a)
    (j : ℕ) (hj : j < k - 2) (x : St N) : cS c a j (wF c a j x) * cS c a j x = 1 := by
  have h := chain_sq ha hca j hj
  rw [circMat_chain ha hca j hj, Qulin.fmono_mul] at h
  have h1 := congrFun (congrFun h x) x
  simpa [fmono, Qulin.wF_wF ha hca j hj] using h1

/-! ### Cell 5. The ladder -/

/-- Half of the ladder is a function up to the sign of the chain. -/
theorem circMat_ladderHalf {m : ℕ} {c a : ℕ → Fin N} {t : Fin N} (hm : 3 ≤ m)
    (ha : Inj (m - 2) a) (hca : Disj m c (m - 2) a) (htc : ∀ i < m, t ≠ c i)
    (hta : ∀ i < m - 2, t ≠ a i) :
    circMat (ladderHalf m c a t)
      = fmono (fun x => Function.update (wF c a (m - 3) x) t
            (xor (x t) (x (c (m - 1)) && x (a (m - 3)))))
          (cS c a (m - 3)) := by
  have hj : m - 3 < m - 2 := by omega
  have hab : c (m - 1) ≠ a (m - 3) := hca (m - 1) (by omega) (m - 3) hj
  have hat : c (m - 1) ≠ t := (htc (m - 1) (by omega)).symm
  have hbt : a (m - 3) ≠ t := (hta (m - 3) hj).symm
  have h1 : circMat (ccx (c (m - 1)) (a (m - 3)) t) = permMat _ := acts_ccx hab hat hbt
  have hsa : ∀ i ≤ m - 3, t ≠ a i := fun i hi => hta i (by omega)
  have hsc : ∀ i < m - 3 + 2, t ≠ c i := fun i hi => htc i (by omega)
  unfold ladderHalf
  rw [circMat_append, circMat_chain ha hca _ hj, h1, Qulin.permMat_eq_fmono, Qulin.fmono_mul]
  apply Qulin.fmono_congr
  · intro x
    exact Qulin.wF_update c a (m - 3) t hsa hsc x _
  · intro x
    rw [mul_one]
    exact cS_update c a (m - 3) t hsa hsc x _

/-- **Cell 5.  The ladder** flips `t` iff all `m` controls are one; the borrowed qubits
come back unchanged and there is no phase. -/
theorem acts_ladder {m : ℕ} {c a : ℕ → Fin N} {t : Fin N} (hm : 3 ≤ m)
    (ha : Inj (m - 2) a) (hca : Disj m c (m - 2) a) (htc : ∀ i < m, t ≠ c i)
    (hta : ∀ i < m - 2, t ≠ a i) :
    Acts (ladder m c a t) (fun x => Function.update x t (xor (x t) (pc c m x))) := by
  have hj : m - 3 < m - 2 := by omega
  have hat : c (m - 1) ≠ t := (htc (m - 1) (by omega)).symm
  have hbt : a (m - 3) ≠ t := (hta (m - 3) hj).symm
  have hsa : ∀ i ≤ m - 3, t ≠ a i := fun i hi => hta i (by omega)
  have hsc : ∀ i < m - 3 + 2, t ≠ c i := fun i hi => htc i (by omega)
  unfold Acts ladder
  rw [circMat_append, circMat_ladderHalf hm ha hca htc hta, Qulin.fmono_mul,
    Qulin.permMat_eq_fmono]
  apply Qulin.fmono_congr
  · intro x
    have e : pc c m x = (pc c (m - 3 + 2) x && x (c (m - 1))) := by
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
      rfl
    simp only [Function.comp_apply]
    rw [Qulin.wF_update c a (m - 3) t hsa hsc, Qulin.wF_wF ha hca _ hj, Function.update_self,
      Function.update_of_ne hat, Function.update_of_ne hbt, Qulin.wF_last,
      Qulin.wF_ctrl hca _ hj (m - 1) (by omega), Function.update_idem, e, Vale.mcx_bit]
  · intro x
    change cS c a (m - 3) (Function.update (wF c a (m - 3) x) t _) * cS c a (m - 3) x = 1
    rw [cS_update c a (m - 3) t hsa hsc, cS_wF_mul ha hca _ hj]

/-! ### Counting -/

theorem cnots_chain {k : ℕ} {c a : ℕ → Fin N} (ha : Inj (k - 2) a)
    (hca : Disj k c (k - 2) a) (j : ℕ) (hj : j < k - 2) :
    cnots (chain c a j) = 6 * j + 3 := by
  induction j with
  | zero => exact Qulin.cnots_marg (hca 0 (by omega) 0 hj) (hca 1 (by omega) 0 hj)
  | succ j ih =>
    have hu : c (j + 2) ≠ a (j + 1) := hca (j + 2) (by omega) (j + 1) hj
    have hv : a j ≠ a (j + 1) := fun h => by
      have := ha j (by omega) (j + 1) hj h
      omega
    rw [chain, cnots_append, cnots_append, Qulin.cnots_marg hu hv, ih (by omega)]
    omega

theorem unitaryGates_chain (c a : ℕ → Fin N) (j : ℕ) : UnitaryGates (chain c a j) := by
  induction j with
  | zero => exact Qulin.unitaryGates_marg _ _ _
  | succ j ih =>
    exact unitaryGates_append (unitaryGates_append (Qulin.unitaryGates_marg _ _ _) ih)
      (Qulin.unitaryGates_marg _ _ _)

theorem cnots_ladder {m : ℕ} {c a : ℕ → Fin N} {t : Fin N} (hm : 3 ≤ m)
    (ha : Inj (m - 2) a) (hca : Disj m c (m - 2) a) (htc : ∀ i < m, t ≠ c i)
    (hta : ∀ i < m - 2, t ≠ a i) : cnots (ladder m c a t) = 12 * m - 14 := by
  have hj : m - 3 < m - 2 := by omega
  have hab : c (m - 1) ≠ a (m - 3) := hca (m - 1) (by omega) (m - 3) hj
  have hat : c (m - 1) ≠ t := (htc (m - 1) (by omega)).symm
  have hbt : a (m - 3) ≠ t := (hta (m - 3) hj).symm
  unfold ladder ladderHalf
  rw [cnots_append, cnots_append, cnots_ccx hab hat hbt, cnots_chain ha hca _ hj]
  omega

theorem unitaryGates_ladder (m : ℕ) (c a : ℕ → Fin N) (t : Fin N) :
    UnitaryGates (ladder m c a t) :=
  unitaryGates_append
    (unitaryGates_append (unitaryGates_ccx _ _ _) (unitaryGates_chain c a (m - 3)))
    (unitaryGates_append (unitaryGates_ccx _ _ _) (unitaryGates_chain c a (m - 3)))

end CirqMcx
