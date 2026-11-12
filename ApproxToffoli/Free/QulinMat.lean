/-
The Huang–Palsberg circuit `qulin N` equals the conditional `C^{N-1}(X)`.

The roots are diagonal matrices, the increment and the decrement are inverse
permutations; together the five middle blocks are the sign matrix (`circMat_mid`),
and the two Hadamards turn it into the conditional (`circMat_qulin`).
-/
import Mathlib
import ApproxToffoli.Free.QulinTop

namespace Qulin

open Matrix Free ExactLine
open Line (St hGate pGate xGate condMat oneMat signMat)

variable {N : ℕ}

/-- One root: the phase `e θ` when the register qubit `i` and the outside controls are one. -/
theorem circMat_root (hN : 0 < N) (θ : ℝ) {i : ℕ} (hi : i < regW N) :
    circMat (root N hN θ (qb N hN i))
      = Matrix.diagonal (fun x => if x (qb N hN i) = true ∧ ctl N hN x then e θ else 1) := by
  rw [regW_eq] at hi
  unfold root
  by_cases hp : N % 2 = 0
  · rw [if_pos hp, circMat_cphase (tgt_ne_qb hN i hi).symm]
    congr 1
    funext x
    exact if_congr (by simp [ctl, hp]) rfl rfl
  · rw [if_neg hp, circMat_ccphase (ext_ne_qb hN hp i hi).symm (tgt_ne_qb hN i hi).symm
      (qb_ne hN (by omega) (by omega) (by omega))]
    congr 1
    funext x
    exact if_congr (by simp [ctl, hp]) rfl rfl

/-- All roots but the first: the phase `e (s θ0 ⌊z / 2⌋)`, where `z` is the register. -/
theorem circMat_roots (hN : 0 < N) (h6 : 6 ≤ N) (s : ℝ) :
    circMat (roots N hN s) = Matrix.diagonal (fun x =>
      if ctl N hN x then e (s * θ0 N * ((regVal (regW N) (qb N hN) x / 2 : ℕ) : ℝ)) else 1) := by
  obtain ⟨m, hm⟩ : ∃ m, regW N = m + 1 := ⟨regW N - 1, by rw [regW_eq]; omega⟩
  unfold roots
  rw [hm, Nat.add_sub_cancel, circMat_forUp_diagonal m _
    (fun j x => if x (qb N hN (1 + j)) = true ∧ ctl N hN x then e (s * θ0 N * 2 ^ j) else 1)
    (fun j hj => circMat_root hN _ (by omega))]
  congr 1
  funext x
  rw [prod_phase m (fun j => qb N hN (1 + j)) x (ctl N hN x) (s * θ0 N),
    regVal_tail m (qb N hN) x]

/-- The phase of the five middle blocks on the basis state `x`; `y` is `x` after the
increment. -/
theorem mid_phase (hN : 0 < N) (h6 : 6 ≤ N) (x y : St N) (hc : ctl N hN y ↔ ctl N hN x)
    (hy : regVal (regW N) (qb N hN) y = (regVal (regW N) (qb N hN) x + 1) % 2 ^ regW N) :
    (if ctl N hN x then e (1 * θ0 N * ((regVal (regW N) (qb N hN) x / 2 : ℕ) : ℝ)) else 1)
        * (if x (qb N hN 0) = true ∧ ctl N hN x then e (θ0 N) else 1)
        * (if ctl N hN y then e (-1 * θ0 N * ((regVal (regW N) (qb N hN) y / 2 : ℕ) : ℝ))
            else 1)
      = if (∀ r, x r = true) then -1 else 1 := by
  have hw : 1 ≤ regW N := by rw [regW_eq]; omega
  by_cases hcx : ctl N hN x
  · have hlow : x (qb N hN 0) = true ↔ regVal (regW N) (qb N hN) x % 2 = 1 := by
      obtain ⟨m, hm⟩ : ∃ m, regW N = m + 1 := ⟨regW N - 1, by omega⟩
      rw [hm]
      exact regVal_low m (qb N hN) x
    rw [if_pos hcx, if_pos (hc.2 hcx), hy,
      if_congr (and_iff_left_of_imp (fun _ => hcx) |>.trans hlow) rfl rfl,
      phase_arith (regW N) hw _ (regVal_lt _ _ _) (θ0 N) rfl]
    refine if_congr ?_ rfl rfl
    rw [all_one_iff hN x]
    exact (and_iff_right hcx).symm
  · rw [if_neg hcx, if_neg (fun h => hcx h.2), if_neg (fun h => hcx (hc.1 h)),
      if_neg (fun h => hcx ((all_one_iff hN x).1 h).1), mul_one, mul_one]

/-- Adding `1` and then `M - 1` modulo `M` gives back the number. -/
theorem inc_dec_arith {M z : ℕ} (hz : z < M) : ((z + 1) % M + (M - 1)) % M = z := by
  rw [Nat.mod_add_mod, show z + 1 + (M - 1) = z + M by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt hz]

/-- The five middle blocks of the circuit are the sign matrix: `-1` on the basis state
with all qubits one, and `1` on every other basis state. -/
theorem circMat_mid (hN : 0 < N) (h6 : 6 ≤ N) :
    circMat (root N hN (θ0 N) (qb N hN 0) ++ roots N hN 1 ++
        inc (N / 2) (qb N hN) (qb N hN (N - 1)) ++ roots N hN (-1) ++
        dec (N / 2) (qb N hN) (qb N hN (N - 1))) = signMat N := by
  have hk : 3 ≤ N / 2 := by omega
  obtain ⟨f, hf, hf'⟩ := acts_inc hk (inj_qb hN) (tgt_ne_qb hN)
  obtain ⟨g, hg, hg'⟩ := acts_dec hk (inj_qb hN) (tgt_ne_qb hN)
  have hgf : ∀ x, g (f x) = x := by
    intro x
    obtain ⟨h1, h2⟩ := hf' x
    obtain ⟨h3, h4⟩ := hg' (f x)
    beta_reduce at h1 h3
    refine eq_of_regVal_eq (m := 2 * (N / 2) - 1) (q := qb N hN) ?_
      (fun r hr => (h4 r hr).trans (h2 r hr))
    rw [h3, h1]
    exact inc_dec_arith (regVal_lt _ _ _)
  unfold Acts at hf hg
  rw [circMat_append, circMat_append, circMat_append, circMat_append, hf, hg,
    circMat_roots hN h6, circMat_roots hN h6,
    circMat_root hN _ (i := 0) (by rw [regW_eq]; omega), Matrix.diagonal_mul_diagonal,
    permMat_diagonal_permMat_diagonal f g hgf]
  unfold signMat
  congr 1
  funext x
  exact mid_phase hN h6 x (f x) (ctl_congr hN (hf' x).2) (hf' x).1

/-- **The Huang–Palsberg circuit equals the conditional** with target qubit `N - 1`. -/
theorem circMat_qulin (N : ℕ) (hN : 6 ≤ N) :
    circMat (qulin N (by omega)) = condMat (⟨N - 1, by omega⟩ : Fin N) := by
  have h0 : 0 < N := by omega
  have ht : qb N h0 (N - 1) = (⟨N - 1, by omega⟩ : Fin N) :=
    Fin.ext (Nat.mod_eq_of_lt (by omega))
  have hsplit : qulin N h0 = [Gate.one (qb N h0 (N - 1)) hGate] ++
      (root N h0 (θ0 N) (qb N h0 0) ++ roots N h0 1 ++
        inc (N / 2) (qb N h0) (qb N h0 (N - 1)) ++ roots N h0 (-1) ++
        dec (N / 2) (qb N h0) (qb N h0 (N - 1))) ++ [Gate.one (qb N h0 (N - 1)) hGate] := by
    unfold qulin
    simp only [List.append_assoc]
  rw [hsplit, circMat_append, circMat_append, circMat_mid h0 hN, circMat_singleton, ← ht]
  exact (Matrix.mul_assoc _ _ _).symm.trans (Line.hGate_sign_hGate _)

end Qulin
