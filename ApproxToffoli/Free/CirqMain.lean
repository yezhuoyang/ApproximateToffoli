/-
Cirq's decomposition of the conditional without helper qubits is the conditional,
exactly, for every `N ≥ 4`, and has exactly `21N² - 120N + 164` (even `N`) or
`21N² - 126N + 181` (odd `N`) CNOTs for every `N ≥ 5` (`CirqMcx.cirq_goal`).

This file counts the CNOTs.  `step N k` has `4 + 2 M(N, k)` CNOTs, where
`M(N, k) = mcxKCount N k` is `1`, `8` for `k = 2, 3`, then `12k - 26` while one ladder
is used (`2k ≤ N + 3`), then `24k - 56` (two ladders, each twice), except `24 (N/2) - 12`
at `k = N/2 + 2` for even `N` (a ladder and a Toffoli, each twice).  The partial sums
`recCount N k` are quadratic in `k` on each range.
-/
import Mathlib
import ApproxToffoli.Free.CirqRec

namespace CirqMcx

open Matrix Free ExactLine
open Line (St hGate pGate xGate condMat)
open Qulin (qb cx pc)

variable {N : ℕ}

/-! ### The count of the circuit is a recurrence -/

theorem cnots_step (hN : 0 < N) {k : ℕ} (hk2 : 2 ≤ k) (hkN : k + 1 ≤ N) :
    cnots (step N hN k) = 4 + 2 * mcxKCount N k := by
  have hne : qb N hN (k - 1) ≠ qb N hN (N - 1) := Qulin.qb_ne hN (by omega) (by omega) (by omega)
  unfold step
  rw [cnots_append, cnots_append, cnots_append, cnots_croot hne, cnots_croot hne,
    cnots_mcxK hN hk2 hkN]
  omega

/-- The CNOT count of `recur N k`: `2 + Σ_{j = 2 .. k} (4 + 2 M(N, j))`. -/
def recCount (N : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | k + 2 => 4 + 2 * mcxKCount N (k + 2) + recCount N (k + 1)

/-- **The recurrence of the count**, for every `k ≤ N - 1`. -/
theorem cnots_recur (hN : 0 < N) (k : ℕ) (hk : k + 1 ≤ N) :
    cnots (recur N hN k) = recCount N k := by
  induction k using recur.induct with
  | case1 => rfl
  | case2 => exact cnots_croot (Qulin.qb_ne hN (by omega) (by omega) (by omega)) _
  | case3 k ih =>
    rw [recur, cnots_append, cnots_step hN (by omega) hk, ih (by omega), recCount]

/-! ### The closed forms -/

theorem recCount_succ (N : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    recCount N (k + 1) = 4 + 2 * mcxKCount N (k + 1) + recCount N k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rfl

/-- One ladder: `M(N, k) = 12k - 26`. -/
theorem mcxKCount_ladder {N k : ℕ} (hk4 : 4 ≤ k) (hk : 2 * k ≤ N + 3) :
    mcxKCount N k + 26 = 12 * k := by
  unfold mcxKCount
  rw [if_neg (by omega), if_neg (by omega), if_pos hk]
  omega

/-- A ladder and a Toffoli, each twice: `M(N, k) = 24 (N/2) - 12`. -/
theorem mcxKCount_mid {N k : ℕ} (h4 : 4 ≤ N) (hk : N + 3 < 2 * k) (h2 : k - N / 2 = 2) :
    mcxKCount N k + 12 = 24 * (N / 2) := by
  unfold mcxKCount
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2]
  omega

/-- Two ladders, each twice: `M(N, k) = 24k - 56`. -/
theorem mcxKCount_split {N k : ℕ} (h4 : 4 ≤ N) (hk : N + 3 < 2 * k) (h2 : k - N / 2 ≠ 2) :
    mcxKCount N k + 56 = 24 * k := by
  unfold mcxKCount
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg h2]
  omega

/-- While one ladder is used, the count is `12k² - 36k + 28`. -/
theorem recCount_ladder (N : ℕ) (k : ℕ) (hk3 : 3 ≤ k) (hk : 2 * k ≤ N + 3) :
    (recCount N k : ℤ) = 12 * (k : ℤ) ^ 2 - 36 * (k : ℤ) + 28 := by
  induction k, hk3 using Nat.le_induction with
  | base =>
    have h : recCount N 3 = 28 := by simp [recCount, mcxKCount]
    rw [h]
    norm_num
  | succ k hk3 ih =>
    have h1 : (mcxKCount N (k + 1) : ℤ) + 26 = 12 * ((k : ℤ) + 1) := by
      exact_mod_cast mcxKCount_ladder (N := N) (k := k + 1) (by omega) hk
    rw [recCount_succ N (by omega)]
    push_cast
    linear_combination 2 * h1 + ih (by omega)

/-- Even `N = 2h`: from `k = h + 2` on, the count is `24k² - 84k - 12h² + 24h + 56`. -/
theorem recCount_even {N h : ℕ} (hN : N = 2 * h) (h3 : 3 ≤ h) (k : ℕ) (hk : h + 2 ≤ k) :
    (recCount N k : ℤ)
      = 24 * (k : ℤ) ^ 2 - 84 * (k : ℤ) - 12 * (h : ℤ) ^ 2 + 24 * (h : ℤ) + 56 := by
  induction k, hk using Nat.le_induction with
  | base =>
    have h1 : (mcxKCount N (h + 1 + 1) : ℤ) + 12 = 24 * (h : ℤ) := by
      have := mcxKCount_mid (N := N) (k := h + 1 + 1) (by omega) (by omega) (by omega)
      rw [show N / 2 = h by omega] at this
      exact_mod_cast this
    have h2 := recCount_ladder N (h + 1) (by omega) (by omega)
    rw [show h + 2 = h + 1 + 1 from rfl, recCount_succ N (by omega)]
    push_cast at h2 ⊢
    linear_combination 2 * h1 + h2
  | succ k hk ih =>
    have h1 : (mcxKCount N (k + 1) : ℤ) + 56 = 24 * ((k : ℤ) + 1) := by
      exact_mod_cast mcxKCount_split (N := N) (k := k + 1) (by omega) (by omega) (by omega)
    rw [recCount_succ N (by omega)]
    push_cast
    linear_combination 2 * h1 + ih

/-- Odd `N = 2h + 1`: from `k = h + 2` on, the count is `24k² - 84k - 12h² + 76`. -/
theorem recCount_odd {N h : ℕ} (hN : N = 2 * h + 1) (h2 : 2 ≤ h) (k : ℕ) (hk : h + 2 ≤ k) :
    (recCount N k : ℤ) = 24 * (k : ℤ) ^ 2 - 84 * (k : ℤ) - 12 * (h : ℤ) ^ 2 + 76 := by
  induction k, hk using Nat.le_induction with
  | base =>
    have h1 := recCount_ladder N (h + 2) (by omega) (by omega)
    push_cast at h1 ⊢
    linear_combination h1
  | succ k hk ih =>
    have h1 : (mcxKCount N (k + 1) : ℤ) + 56 = 24 * ((k : ℤ) + 1) := by
      exact_mod_cast mcxKCount_split (N := N) (k := k + 1) (by omega) (by omega) (by omega)
    rw [recCount_succ N (by omega)]
    push_cast
    linear_combination 2 * h1 + ih

/-- **The CNOT count of Cirq's circuit**, for every `N ≥ 5`. -/
theorem cnots_cirqMcx (hN : 0 < N) (h5 : 5 ≤ N) :
    (cnots (cirqMcx N hN) : ℤ) =
      if N % 2 = 0 then 21 * (N : ℤ) ^ 2 - 120 * (N : ℤ) + 164
      else 21 * (N : ℤ) ^ 2 - 126 * (N : ℤ) + 181 := by
  unfold cirqMcx
  rw [cnots_recur hN (N - 1) (by omega)]
  split_ifs with he
  · obtain ⟨h, rfl⟩ : ∃ h, N = 2 * h := ⟨N / 2, by omega⟩
    have hk : ((2 * h - 1 : ℕ) : ℤ) = 2 * (h : ℤ) - 1 := by omega
    rw [recCount_even rfl (by omega) (2 * h - 1) (by omega), hk]
    push_cast
    ring
  · obtain ⟨h, rfl⟩ : ∃ h, N = 2 * h + 1 := ⟨N / 2, by omega⟩
    rw [Nat.add_sub_cancel, recCount_odd rfl (by omega) (2 * h) (by omega)]
    push_cast
    ring

/-- At `N = 4` (where the closed form does not apply) the circuit has 28 CNOTs. -/
theorem cnots_cirqMcx_four : cnots (cirqMcx 4 (by omega)) = 28 := by
  unfold cirqMcx
  rw [cnots_recur (by omega) (4 - 1) (by omega)]
  simp [recCount, mcxKCount]

/-! ### The theorem -/

/-- **Cirq's decomposition of the conditional without helper qubits, formalized.**  For
every `N ≥ 4` the circuit has unitary one-qubit gates and equals the conditional with
target qubit `N - 1` exactly, with no global phase; for every `N ≥ 5` it has exactly
`21N² - 120N + 164` CNOTs if `N` is even and `21N² - 126N + 181` CNOTs if `N` is odd. -/
theorem cirq_goal : CirqGoal := by
  refine ⟨fun N hN => ⟨unitaryGates_cirqMcx _, ?_⟩, fun N hN => cnots_cirqMcx _ hN⟩
  have h0 : 0 < N := by omega
  have ht : (⟨N - 1, by omega⟩ : Fin N) = qb N h0 (N - 1) :=
    Fin.ext (Qulin.qb_val h0 (by omega)).symm
  rw [ht]
  exact circMat_cirqMcx h0 hN

end CirqMcx
