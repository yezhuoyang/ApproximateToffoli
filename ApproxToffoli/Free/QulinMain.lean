/-
The Huang–Palsberg circuit `qulin N`: the counts, and the main theorem `qulin_goal`.

CNOTs: `124N - 214` (even `N`), `132N - 358` (odd `N`).  One-qubit gates: `100N - 170`
T gates and `6N - 15` rotations (even `N`), `100N - 276` T gates and `14N - 35`
rotations (odd `N`).
-/
import Mathlib
import ApproxToffoli.Free.QulinMat

namespace Qulin

open Matrix Free ExactLine
open Line (St hGate pGate xGate condMat oneMat signMat)

variable {N : ℕ}

/-! ### Unitary gates -/

theorem unitaryGates_root (hN : 0 < N) (θ : ℝ) (c : Fin N) : UnitaryGates (root N hN θ c) := by
  unfold root
  split_ifs
  · exact unitaryGates_cphase _ _ _
  · exact unitaryGates_ccphase _ _ _ _

theorem unitaryGates_roots (hN : 0 < N) (s : ℝ) : UnitaryGates (roots N hN s) :=
  unitaryGates_forUp _ _ (fun _ _ => unitaryGates_root hN _ _)

/-- Every one-qubit gate of the circuit is unitary. -/
theorem unitaryGates_qulin (N : ℕ) (hN : 6 ≤ N) : UnitaryGates (qulin N (by omega)) := by
  have h0 : 0 < N := by omega
  have hH : UnitaryGates [Gate.one (qb N h0 (N - 1)) hGate] :=
    unitaryGates_singleton_one _ Line.hGate_unitary
  unfold qulin
  exact unitaryGates_append (unitaryGates_append (unitaryGates_append (unitaryGates_append
    (unitaryGates_append (unitaryGates_append hH (unitaryGates_root h0 _ _))
    (unitaryGates_roots h0 _)) (unitaryGates_inc _ _ _)) (unitaryGates_roots h0 _))
    (unitaryGates_dec _ _ _)) hH

/-! ### CNOTs -/

theorem cnots_singleton_one (q : Fin N) (g : Matrix Bool Bool ℂ) : cnots [Gate.one q g] = 0 :=
  rfl

theorem cnots_root (hN : 0 < N) (θ : ℝ) {i : ℕ} (hi : i < regW N) :
    cnots (root N hN θ (qb N hN i)) = if N % 2 = 0 then 2 else 6 := by
  rw [regW_eq] at hi
  unfold root
  by_cases hp : N % 2 = 0
  · rw [if_pos hp, if_pos hp, cnots_cphase (tgt_ne_qb hN i hi).symm]
  · rw [if_neg hp, if_neg hp, cnots_ccphase (ext_ne_qb hN hp i hi).symm
      (tgt_ne_qb hN i hi).symm (qb_ne hN (by omega) (by omega) (by omega))]

theorem cnots_roots (hN : 0 < N) (h6 : 6 ≤ N) (s : ℝ) :
    cnots (roots N hN s) = (regW N - 1) * (if N % 2 = 0 then 2 else 6) :=
  cnots_forUp _ _ _ (fun i hi => cnots_root hN _ (by rw [regW_eq] at hi ⊢; omega))

/-- The CNOT count of the circuit: exactly the count of the paper. -/
theorem cnots_qulin (N : ℕ) (hN : 6 ≤ N) : cnots (qulin N (by omega)) = qulinCnots N := by
  have h0 : 0 < N := by omega
  have hk : 3 ≤ N / 2 := by omega
  unfold qulin qulinCnots
  rw [cnots_append, cnots_append, cnots_append, cnots_append, cnots_append, cnots_append,
    cnots_singleton_one, cnots_root h0 _ (i := 0) (by rw [regW_eq]; omega),
    cnots_roots h0 hN, cnots_roots h0 hN, cnots_inc hk (inj_qb h0) (tgt_ne_qb h0),
    cnots_dec hk (inj_qb h0) (tgt_ne_qb h0), regW_eq]
  split_ifs <;> omega

/-! ### T gates and rotations -/

theorem tr_root_even (hN : 0 < N) (hp : N % 2 = 0) (θ : ℝ) (c : Fin N) :
    TR (root N hN θ c) 0 3 := by
  unfold root
  rw [if_pos hp]
  exact tr_cphase_rot _ _ _

theorem tr_root_odd (hN : 0 < N) (hp : ¬ N % 2 = 0) (θ : ℝ) (c : Fin N) :
    TR (root N hN θ c) 0 7 := by
  unfold root
  rw [if_neg hp]
  exact tr_ccphase_rot _ _ _ _

/-- The largest root angle is a quarter turn. -/
theorem θ0_mul_pow {m : ℕ} (hm : regW N - 1 = m + 1) : θ0 N * 2 ^ m = Real.pi / 2 := by
  unfold θ0
  rw [hm, pow_succ]
  field_simp

/-- Even `N`: the last root of the chain has angle `± π / 2`, so its three phase gates
are T gates; every other root is three rotations. -/
theorem tr_roots_even (hN : 0 < N) (h6 : 6 ≤ N) (hp : N % 2 = 0) (s : ℝ)
    (hs : ∀ c t : Fin N, TR (cphase (s * (Real.pi / 2)) c t) 3 0) :
    TR (roots N hN s) 3 ((regW N - 2) * 3) := by
  obtain ⟨m, hm⟩ : ∃ m, regW N - 1 = m + 1 := ⟨regW N - 2, by rw [regW_eq]; omega⟩
  have hm2 : regW N - 2 = m := by omega
  have hlast : root N hN (s * θ0 N * 2 ^ m) (qb N hN (1 + m))
      = cphase (s * (Real.pi / 2)) (qb N hN (1 + m)) (qb N hN (N - 1)) := by
    unfold root
    rw [if_pos hp, mul_assoc, θ0_mul_pow hm]
  unfold roots
  rw [hm, forUp_succ, hm2, hlast]
  exact (tr_append (tr_forUp m _ 0 3 (fun j _ => tr_root_even hN hp _ _)) (hs _ _)).congr
    (by omega) (by omega)

theorem tr_roots_odd (hN : 0 < N) (hp : ¬ N % 2 = 0) (s : ℝ) :
    TR (roots N hN s) 0 ((regW N - 1) * 7) :=
  (tr_forUp _ _ 0 7 (fun _ _ => tr_root_odd hN hp _ _)).congr (Nat.mul_zero _) rfl

/-- The one-qubit gates of the circuit: `qulinT N` T gates and `qulinR N` rotations. -/
theorem tr_qulin (N : ℕ) (hN : 6 ≤ N) : TR (qulin N (by omega)) (qulinT N) (qulinR N) := by
  have h0 : 0 < N := by omega
  have hk : 3 ≤ N / 2 := by omega
  have hH : TR [Gate.one (qb N h0 (N - 1)) hGate] 0 0 := tr_one _ Line.TCost.h
  unfold qulin qulinT qulinR
  by_cases hp : N % 2 = 0
  · rw [if_pos hp, if_pos hp]
    have hpos : TR (roots N h0 1) 3 ((regW N - 2) * 3) :=
      tr_roots_even h0 hN hp 1 (fun c t => by rw [one_mul]; exact tr_cphase_T c t)
    have hneg : TR (roots N h0 (-1)) 3 ((regW N - 2) * 3) :=
      tr_roots_even h0 hN hp (-1) (fun c t => by rw [neg_one_mul]; exact tr_cphase_T_neg c t)
    refine (tr_append (tr_append (tr_append (tr_append (tr_append (tr_append hH
      (tr_root_even h0 hp _ _)) hpos) (tr_inc _ hk _ _)) hneg) (tr_dec _ hk _ _)) hH).congr
      ?_ ?_
    · omega
    · rw [regW_eq]
      omega
  · rw [if_neg hp, if_neg hp]
    refine (tr_append (tr_append (tr_append (tr_append (tr_append (tr_append hH
      (tr_root_odd h0 hp _ _)) (tr_roots_odd h0 hp _)) (tr_inc _ hk _ _))
      (tr_roots_odd h0 hp _)) (tr_dec _ hk _ _)) hH).congr ?_ ?_
    · omega
    · rw [regW_eq]
      omega

/-- **The Huang–Palsberg scheme, formalized.**  For every `N ≥ 6` the circuit `qulin N`
has unitary one-qubit gates, equals the conditional with target qubit `N - 1`, has
`124N - 214` (even `N`) or `132N - 358` (odd `N`) CNOTs, and its one-qubit gates are
`100N - 170` T gates and `6N - 15` rotations (even `N`), or `100N - 276` T gates and
`14N - 35` rotations (odd `N`). -/
theorem qulin_goal : QulinGoal :=
  fun N hN => ⟨unitaryGates_qulin N hN, circMat_qulin N hN, cnots_qulin N hN, tr_qulin N hN⟩

end Qulin
