/-
The multi-controlled X gates inside Cirq's recursion (`CirqMcx.split`, `CirqMcx.mcxK`,
cells 6 and 7 of the reference): `mcxK N k` flips qubit `k - 1` iff the qubits
`0 .. k-2` are all one, exactly (no phase, every other qubit restored), for every
`2 ≤ k ≤ N - 1`, in each of its four cases (`k = 2`, `k = 3`, one ladder, two ladders
each used twice), and its CNOT count is `mcxKCount N k`.
-/
import Mathlib
import ApproxToffoli.Free.CirqLadder

namespace CirqMcx

open Matrix Free ExactLine
open Line (St hGate pGate xGate ryGate condMat cxFun cxPerm oneMat ctrlMat m2)
open Qulin (qb cx marg fmono pc wF wSgn)

variable {N : ℕ}

/-! ### The side conditions of a ladder -/

/-- The side conditions of `ladder m c a t`: at least three controls, the borrowed
qubits are distinct, no borrowed qubit is a control, and the target is neither a control
nor a borrowed qubit. -/
def LadderOk (m : ℕ) (c a : ℕ → Fin N) (t : Fin N) : Prop :=
  3 ≤ m ∧ Inj (m - 2) a ∧ Disj m c (m - 2) a ∧ (∀ i < m, t ≠ c i) ∧ (∀ i < m - 2, t ≠ a i)

theorem LadderOk.acts {m : ℕ} {c a : ℕ → Fin N} {t : Fin N} (h : LadderOk m c a t) :
    Acts (ladder m c a t) (fun x => Function.update x t (xor (x t) (pc c m x))) :=
  acts_ladder h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

theorem LadderOk.cnots {m : ℕ} {c a : ℕ → Fin N} {t : Fin N} (h : LadderOk m c a t) :
    cnots (ladder m c a t) = 12 * m - 14 :=
  cnots_ladder h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

theorem skip_inj {j i i' : ℕ} (h : skip j i = skip j i') : i = i' := by
  unfold skip at h
  split_ifs at h <;> omega

theorem skip_ne (j i : ℕ) : skip j i ≠ j := by
  unfold skip
  split_ifs <;> omega

theorem skip_le (j i : ℕ) : skip j i ≤ i + 1 := by
  unfold skip
  split_ifs <;> omega

theorem le_skip (j i : ℕ) : i ≤ skip j i := by
  unfold skip
  split_ifs <;> omega

theorem skip_of_lt {j i : ℕ} (h : i < j) : skip j i = i := by
  unfold skip
  rw [if_pos h]

/-- The ladder of `mcxK` (`4 ≤ k`, `2k ≤ N + 3`). -/
theorem ladderOk_mcxK (hN : 0 < N) {k : ℕ} (hk4 : 4 ≤ k) (hk : 2 * k ≤ N + 3) :
    LadderOk (k - 1) (fun i => qb N hN i) (fun i => qb N hN (k + i)) (qb N hN (k - 1)) := by
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj e
    have := Qulin.qb_inj hN (by omega) (by omega) e
    omega
  · intro i hi j hj
    exact Qulin.qb_ne hN (by omega) (by omega) (by omega)
  · intro i hi
    exact Qulin.qb_ne hN (by omega) (by omega) (by omega)
  · intro i hi
    exact Qulin.qb_ne hN (by omega) (by omega) (by omega)

/-- The first ladder of `split` (`2k > N + 3`, `k ≤ N - 1`). -/
theorem ladderOk_part1 (hN : 0 < N) {k : ℕ} (hk : N + 3 < 2 * k) (hkN : k + 1 ≤ N) :
    LadderOk (N / 2) (fun i => qb N hN i) (fun i => qb N hN (skip k (N / 2 + i)))
      (qb N hN k) := by
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj e
    have h1 := skip_le k (N / 2 + i)
    have h2 := skip_le k (N / 2 + j)
    have := skip_inj (Qulin.qb_inj hN (by omega) (by omega) e)
    omega
  · intro i hi j hj
    have h1 := skip_le k (N / 2 + j)
    have h2 := le_skip k (N / 2 + j)
    exact Qulin.qb_ne hN (by omega) (by omega) (by omega)
  · intro i hi
    exact Qulin.qb_ne hN (by omega) (by omega) (by omega)
  · intro i hi
    have h1 := skip_le k (N / 2 + i)
    exact Qulin.qb_ne hN (by omega) (by omega) (skip_ne k _).symm

/-- The second ladder of `split` (`2k > N + 3`, `k ≤ N - 1`, `k - N / 2 ≥ 3`). -/
theorem ladderOk_part2 (hN : 0 < N) {k : ℕ} (hk : N + 3 < 2 * k) (hkN : k + 1 ≤ N)
    (h2 : k - N / 2 ≠ 2) :
    LadderOk (k - N / 2) (fun i => qb N hN (skip (k - 1) (N / 2 + i))) (fun i => qb N hN i)
      (qb N hN (k - 1)) := by
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj e
    exact Qulin.qb_inj hN (by omega) (by omega) e
  · intro i hi j hj
    have h1 := skip_le (k - 1) (N / 2 + i)
    have h3 := le_skip (k - 1) (N / 2 + i)
    exact Qulin.qb_ne hN (by omega) (by omega) (by omega)
  · intro i hi
    have h1 := skip_le (k - 1) (N / 2 + i)
    exact Qulin.qb_ne hN (by omega) (by omega) (skip_ne (k - 1) _).symm
  · intro i hi
    exact Qulin.qb_ne hN (by omega) (by omega) (by omega)

/-! ### Cell 6. Two conditional flips, each used twice -/

/-- If `A` flips `p` iff `fa` and `B` flips `q` iff `fb` and bit `p`, then
`A ; B ; A ; B` flips `q` iff `fa` and `fb`, and restores `p`. -/
theorem acts_split_core {p q : Fin N} (hpq : p ≠ q) (fa fb : St N → Bool)
    (hap : ∀ x s, fa (Function.update x p s) = fa x)
    (haq : ∀ x s, fa (Function.update x q s) = fa x)
    (hbp : ∀ x s, fb (Function.update x p s) = fb x)
    (hbq : ∀ x s, fb (Function.update x q s) = fb x) {A B : List (Gate N)}
    (hA : Acts A (fun x => Function.update x p (xor (x p) (fa x))))
    (hB : Acts B (fun x => Function.update x q (xor (x q) (fb x && x p)))) :
    Acts (A ++ B ++ A ++ B) (fun x => Function.update x q (xor (x q) (fa x && fb x))) := by
  refine (acts_append (acts_append (acts_append hA hB) hA) hB).congr (fun x => ?_)
  funext r
  simp only [Function.comp_apply, hap, haq, hbp, hbq, Function.update_self,
    Function.update_of_ne hpq, Function.update_of_ne hpq.symm]
  by_cases hrq : r = q
  · subst hrq
    simp only [Function.update_self]
    cases x r <;> cases x p <;> cases fa x <;> cases fb x <;> rfl
  · by_cases hrp : r = p
    · subst hrp
      simp only [Function.update_self, Function.update_of_ne hrq]
      cases x r <;> cases fa x <;> rfl
    · simp only [Function.update_of_ne hrq, Function.update_of_ne hrp]

theorem pc_congr_fun {c c' : ℕ → Fin N} (n : ℕ) (h : ∀ i < n, c i = c' i) (x : St N) :
    pc c n x = pc c' n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pc, pc, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

/-- The second part of `split` flips qubit `k - 1` iff the qubits `N/2 .. k-2` and the
qubit `k` are all one, in both of its cases. -/
theorem acts_splitPart2 (hN : 0 < N) {k : ℕ} (hk : N + 3 < 2 * k) (hkN : k + 1 ≤ N) :
    Acts (splitPart2 N hN k)
      (fun x => Function.update x (qb N hN (k - 1)) (xor (x (qb N hN (k - 1)))
        (pc (fun i => qb N hN (N / 2 + i)) (k - 1 - N / 2) x && x (qb N hN k)))) := by
  unfold splitPart2
  split_ifs with h2
  · refine (acts_ccx (Qulin.qb_ne hN (by omega) (by omega) (by omega))
      (Qulin.qb_ne hN (by omega) (by omega) (by omega))
      (Qulin.qb_ne hN (by omega) (by omega) (by omega))).congr (fun x => ?_)
    have e1 : k - 1 - N / 2 = 1 := by omega
    rw [e1]
    simp [pc]
  · refine (ladderOk_part2 hN hk hkN h2).acts.congr (fun x => ?_)
    obtain ⟨n, hn⟩ : ∃ n, k - N / 2 = n + 1 := ⟨k - N / 2 - 1, by omega⟩
    have e1 : k - 1 - N / 2 = n := by omega
    have e2 : skip (k - 1) (N / 2 + n) = k := by
      unfold skip
      rw [if_neg (by omega)]
      omega
    rw [hn, e1, pc, pc_congr_fun n (c' := fun i => qb N hN (N / 2 + i))
      (fun i hi => by rw [skip_of_lt (by omega)]), e2]

/-- **Cell 6.**  `split N k` flips qubit `k - 1` iff the qubits `0 .. k-2` are all one;
every other qubit is restored and there is no phase. -/
theorem acts_split (hN : 0 < N) {k : ℕ} (hk : N + 3 < 2 * k) (hkN : k + 1 ≤ N) :
    Acts (split N hN k)
      (fun x => Function.update x (qb N hN (k - 1))
        (xor (x (qb N hN (k - 1))) (pc (qb N hN) (k - 1) x))) := by
  have hpq : qb N hN k ≠ qb N hN (k - 1) := Qulin.qb_ne hN (by omega) (by omega) (by omega)
  have hfa : ∀ r, N / 2 ≤ r → r < N → ∀ (x : St N) (s : Bool),
      pc (qb N hN) (N / 2) (Function.update x (qb N hN r) s) = pc (qb N hN) (N / 2) x :=
    fun r hr hrN x s => Qulin.pc_update _ _ _
      (fun i hi => Qulin.qb_ne hN hrN (by omega) (by omega)) x s
  have hfb : ∀ r, k - 1 ≤ r → r < N → ∀ (x : St N) (s : Bool),
      pc (fun i => qb N hN (N / 2 + i)) (k - 1 - N / 2) (Function.update x (qb N hN r) s)
        = pc (fun i => qb N hN (N / 2 + i)) (k - 1 - N / 2) x :=
    fun r hr hrN x s => Qulin.pc_update _ _ _
      (fun i hi => Qulin.qb_ne hN hrN (by omega) (by omega)) x s
  have h := acts_split_core hpq (pc (qb N hN) (N / 2))
    (pc (fun i => qb N hN (N / 2 + i)) (k - 1 - N / 2))
    (hfa k (by omega) (by omega)) (hfa (k - 1) (by omega) (by omega))
    (hfb k (by omega) (by omega)) (hfb (k - 1) (by omega) (by omega))
    (ladderOk_part1 hN hk hkN).acts (acts_splitPart2 hN hk hkN)
  refine h.congr (fun x => ?_)
  have hs := Vale.pc_add (qb N hN) (N / 2) (k - 1 - N / 2) x
  rw [show N / 2 + (k - 1 - N / 2) = k - 1 by omega] at hs
  rw [hs]

/-! ### Cell 7. `mcxK` -/

/-- **Cell 7.**  `mcxK N k` flips qubit `k - 1` iff the qubits `0 .. k-2` are all one,
exactly, for every `2 ≤ k ≤ N - 1`; every other qubit is restored. -/
theorem acts_mcxK (hN : 0 < N) {k : ℕ} (hk2 : 2 ≤ k) (hkN : k + 1 ≤ N) :
    Acts (mcxK N hN k)
      (fun x => Function.update x (qb N hN (k - 1))
        (xor (x (qb N hN (k - 1))) (pc (qb N hN) (k - 1) x))) := by
  unfold mcxK
  split_ifs with h2 h3 hl
  · subst h2
    exact (Qulin.acts_cx (Qulin.qb_ne hN (by omega) (by omega) (by omega))).congr
      (fun x => by simp [cxFun, pc])
  · subst h3
    exact (acts_ccx (Qulin.qb_ne hN (by omega) (by omega) (by omega))
      (Qulin.qb_ne hN (by omega) (by omega) (by omega))
      (Qulin.qb_ne hN (by omega) (by omega) (by omega))).congr (fun x => by simp [pc])
  · exact (ladderOk_mcxK hN (by omega) hl).acts
  · exact acts_split hN (by omega) hkN

/-- The CNOT count of `mcxK N k`. -/
def mcxKCount (N k : ℕ) : ℕ :=
  if k = 2 then 1
  else if k = 3 then 8
  else if 2 * k ≤ N + 3 then 12 * (k - 1) - 14
  else if k - N / 2 = 2 then 2 * (12 * (N / 2) - 14 + 8)
  else 2 * (12 * (N / 2) - 14 + (12 * (k - N / 2) - 14))

theorem cnots_mcxK (hN : 0 < N) {k : ℕ} (hk2 : 2 ≤ k) (hkN : k + 1 ≤ N) :
    cnots (mcxK N hN k) = mcxKCount N k := by
  unfold mcxK mcxKCount
  split_ifs with h2 h3 hl hs
  · subst h2
    exact Qulin.cnots_cx (Qulin.qb_ne hN (by omega) (by omega) (by omega))
  · subst h3
    exact cnots_ccx (Qulin.qb_ne hN (by omega) (by omega) (by omega))
      (Qulin.qb_ne hN (by omega) (by omega) (by omega))
      (Qulin.qb_ne hN (by omega) (by omega) (by omega))
  · exact (ladderOk_mcxK hN (by omega) hl).cnots
  · unfold split splitPart2
    rw [if_pos hs]
    simp only [cnots_append, (ladderOk_part1 hN (by omega) hkN).cnots, splitPart1,
      cnots_ccx (Qulin.qb_ne hN (show N / 2 < N by omega) (show k < N by omega) (by omega))
        (Qulin.qb_ne hN (show N / 2 < N by omega) (show k - 1 < N by omega) (by omega))
        (Qulin.qb_ne hN (show k < N by omega) (show k - 1 < N by omega) (by omega))]
    omega
  · unfold split splitPart2
    rw [if_neg hs]
    simp only [cnots_append, (ladderOk_part1 hN (by omega) hkN).cnots, splitPart1,
      (ladderOk_part2 hN (by omega) hkN hs).cnots]
    omega

theorem unitaryGates_mcxK (hN : 0 < N) (k : ℕ) : UnitaryGates (mcxK N hN k) := by
  have h2 : UnitaryGates (splitPart2 N hN k) := by
    unfold splitPart2
    split_ifs
    · exact unitaryGates_ccx _ _ _
    · exact unitaryGates_ladder _ _ _ _
  unfold mcxK
  split_ifs
  · exact Qulin.unitaryGates_cx _ _
  · exact unitaryGates_ccx _ _ _
  · exact unitaryGates_ladder _ _ _ _
  · exact unitaryGates_append (unitaryGates_append (unitaryGates_append
      (unitaryGates_ladder _ _ _ _) h2) (unitaryGates_ladder _ _ _ _)) h2

end CirqMcx
