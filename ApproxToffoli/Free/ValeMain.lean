/-
The circuit of Vale et al., as Qiskit emits it, is the conditional, exactly, for every
`N ≥ 2`, and has exactly `8N² - 32N - 36` CNOTs for every `N ≥ 8` (`Vale.vale_goal`).

This file counts the CNOTs.  `mcx` has `1, 6, 14` CNOTs for `k = 1, 2, 3` and `8k - 6`
for `k ≥ 4`; `mcrz m` has `2` for `m = 1` and twice the two `mcx` counts otherwise, which
is `16m - 24` for `m ≥ 8`; the chain through `m = 1 .. 7` has `220`.
-/
import Mathlib
import ApproxToffoli.Free.ValeMcrz

namespace Vale

open Matrix Free ExactLine
open Line (St hGate pGate xGate condMat)
open Qulin (qb cx ccx pc)

variable {N : ℕ}

/-! ### Counting -/

/-- The CNOT count of `mcrz lam m`. -/
def mcrzCount (m : ℕ) : ℕ :=
  if m = 1 then 2 else 2 * (mcxCount ((m + 1) / 2) + mcxCount (m / 2))

/-- The CNOT count of `phaseChain m lam`: the sum of the counts of `mcrz 1 .. mcrz m`. -/
def pcCount : ℕ → ℕ
  | 0 => 0
  | m + 1 => mcrzCount (m + 1) + pcCount m

theorem cnots_mcrz (hN : 0 < N) {m : ℕ} (hm1 : 1 ≤ m) (hm : m < N) (lam : ℝ) :
    cnots (mcrz N hN lam m) = mcrzCount m := by
  unfold mcrzCount
  by_cases h1 : m = 1
  · subst h1
    rw [mcrz, if_pos rfl, if_pos rfl]
    exact cnots_crz (Qulin.qb_ne hN (by omega) hm (by omega)) lam
  · rw [mcrz, if_neg h1, if_neg h1]
    simp only [cnots_append, cnots_pG, cnots_mcx hN (mcxOk_first (by omega) hm),
      cnots_mcx hN (mcxOk_second (by omega) hm)]
    omega

theorem cnots_phaseChain (hN : 0 < N) (m : ℕ) (hm : m < N) (lam : ℝ) :
    cnots (phaseChain N hN m lam) = pcCount m := by
  induction m generalizing lam with
  | zero => rfl
  | succ m ih =>
    rw [phaseChain, cnots_append, cnots_mcrz hN (by omega) hm, ih (by omega), pcCount]

theorem mcxCount_of_ge {k : ℕ} (hk : 4 ≤ k) : mcxCount k = 8 * k - 6 := by
  unfold mcxCount
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem mcrzCount_of_ge {m : ℕ} (hm : 8 ≤ m) : mcrzCount m = 16 * m - 24 := by
  unfold mcrzCount
  rw [if_neg (by omega), mcxCount_of_ge (by omega), mcxCount_of_ge (by omega)]
  omega

/-- The chain through `mcrz 1 .. mcrz 7` has 220 CNOTs. -/
theorem pcCount_seven : pcCount 7 = 220 := by decide

/-- The closed form of the count of the chain, from `m = 7` on. -/
theorem pcCount_closed (m : ℕ) (hm : 7 ≤ m) : pcCount m + 16 * m + 60 = 8 * m ^ 2 := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [pcCount_seven]
    norm_num
  | succ m hm ih =>
    have h2 : 8 * (m + 1) ^ 2 = 8 * m ^ 2 + 16 * m + 8 := by ring
    rw [pcCount, mcrzCount_of_ge (by omega), h2]
    omega

theorem cnots_vale (hN : 0 < N) (h8 : 8 ≤ N) :
    cnots (vale N hN) = 8 * N ^ 2 - 32 * N - 36 := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hc := pcCount_closed m (by omega)
  have h2 : 8 * (m + 1) ^ 2 = 8 * m ^ 2 + 16 * m + 8 := by ring
  unfold vale
  rw [cnots_append, cnots_append, cnots_hG, Nat.add_sub_cancel,
    cnots_phaseChain hN m (by omega), h2]
  omega

/-! ### The theorem -/

/-- **The scheme of Vale et al., formalized.**  For every `N ≥ 2` the circuit that
Qiskit emits has unitary one-qubit gates and equals the conditional with target qubit
`N - 1` exactly, with no global phase; for every `N ≥ 8` it has exactly
`8N² - 32N - 36` CNOTs. -/
theorem vale_goal : ValeGoal := by
  refine ⟨fun N hN => ⟨unitaryGates_vale _, ?_⟩, fun N hN => cnots_vale _ hN⟩
  have h0 : 0 < N := by omega
  have ht : (⟨N - 1, by omega⟩ : Fin N) = qb N h0 (N - 1) :=
    Fin.ext (Qulin.qb_val h0 (by omega)).symm
  rw [ht]
  exact circMat_vale h0

end Vale
