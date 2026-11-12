/-
The multi-controlled X with dirty qubits of the circuit of Vale et al. (`Vale.mcx`,
S3–S7): it flips the target iff all `k` controls are one, exactly (no phase, dirty
qubits restored), with `1, 6, 14` CNOTs for `k = 1, 2, 3` and `8k - 6` for `k ≥ 4`.

The ladder has the shape of the one of the Huang–Palsberg circuit (`QulinMcx.lean`):
the function on basis states is the same (`Qulin.wF`), the 2×2 blocks are built from
`H` and `T` instead of `R_y`, and the phases are fourth roots of unity (`wPh`), so the
phase of the chain is not invariant under the chain but is inverted by it.
-/
import Mathlib
import ApproxToffoli.Free.ValeCells

namespace Vale

open Matrix Free ExactLine
open Line (St hGate pGate xGate condMat cxFun cxPerm oneMat ctrlMat m2)
open Qulin (qb cx ccx fmono pc wF)

variable {N : ℕ}

/-! ### S4. The 2×2 blocks of the ladder -/

/-- The block of `ladAct` on its target, for the bits `u`, `v` of its controls:
`X^u T⁻¹ X^v T H`. -/
noncomputable def aBlk (u v : Bool) : Matrix Bool Bool ℂ :=
  (if u then xGate else 1) * pGate (-(Real.pi / 4)) * (if v then xGate else 1)
    * pGate (Real.pi / 4) * hGate

/-- The block of `ladRst` on its target: `H T⁻¹ X^v T X^u`. -/
noncomputable def aInvBlk (u v : Bool) : Matrix Bool Bool ℂ :=
  hGate * pGate (-(Real.pi / 4)) * (if v then xGate else 1) * pGate (Real.pi / 4)
    * (if u then xGate else 1)

/-- The block of the relative-phase Toffoli: `1` if `d` is zero, `Z` if `d = 1`, `v = 0`,
and `Y` if `d = v = 1`. -/
def wBlk (d v : Bool) : Matrix Bool Bool ℂ :=
  if d then (if v then m2 0 (-Complex.I) Complex.I 0 else m2 1 0 0 (-1)) else m2 1 0 0 1

theorem e_neg_quarter_sq : e (-(Real.pi / 4)) * e (-(Real.pi / 4)) = -Complex.I := by
  rw [← e_add, show -(Real.pi / 4) + -(Real.pi / 4) = -(Real.pi / 2) by ring,
    Dsp.e_neg_pi_div_two]

theorem lad_mid (u u' v : Bool) :
    pGate (-(Real.pi / 4)) * (if v then xGate else 1) * pGate (Real.pi / 4)
        * (if u' then xGate else 1) * (if u then xGate else 1)
        * pGate (-(Real.pi / 4)) * (if v then xGate else 1) * pGate (Real.pi / 4)
      = if xor u u' then (if v then m2 0 Complex.I (-Complex.I) 0 else m2 0 1 1 0)
        else m2 1 0 0 1 := by
  cases u <;> cases u' <;> cases v <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Line.pGate_eq_m2, Line.xGate_eq_m2,
      Line.one_eq_m2, Line.m2_mul, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add,
      Qulin.e_neg_mul_self, Qulin.e_mul_neg_self, Line.e_quarter_sq, e_neg_quarter_sq,
      Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true]

/-- **The key 2×2 fact (S4)**: `ladAct` with first control `u` followed by `ladRst` with
first control `u'` is the relative-phase Toffoli block controlled by `u xor u'`. -/
theorem aInv_mul_a (u u' v : Bool) : aInvBlk u' v * aBlk u v = wBlk (xor u u') v := by
  have hre : aInvBlk u' v * aBlk u v
      = hGate * (pGate (-(Real.pi / 4)) * (if v then xGate else 1) * pGate (Real.pi / 4)
        * (if u' then xGate else 1) * (if u then xGate else 1)
        * pGate (-(Real.pi / 4)) * (if v then xGate else 1) * pGate (Real.pi / 4)) * hGate := by
    simp only [aBlk, aInvBlk, Matrix.mul_assoc]
  rw [hre, lad_mid]
  cases xor u u' <;> cases v <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Line.hGate_mul_mul, wBlk] <;>
    congr 1 <;> ring

/-- The phase of one level of the chain: `(i^v (-1)^s)^p`. -/
noncomputable def wPh (p v s : Bool) : ℂ :=
  if p then (if v then (if s then -Complex.I else Complex.I) else (if s then -1 else 1)) else 1

theorem wBlk_support (d v p q : Bool) (h : p ≠ xor q (d && v)) : wBlk d v p q = 0 := by
  revert h
  cases d <;> cases v <;> cases p <;> cases q <;> simp [wBlk, m2]

theorem wBlk_entry (d v q : Bool) : wBlk d v (xor q (d && v)) q = wPh d v q := by
  cases d <;> cases v <;> cases q <;> simp [wBlk, m2, wPh]

/-- The phase of one level before the flip times the phase after it is one. -/
theorem wPh_flip_mul (p v s : Bool) : wPh p v (xor s (p && v)) * wPh p v s = 1 := by
  cases p <;> cases v <;> cases s <;> simp [wPh]

/-! ### The matrices of `ladAct`, `ladRst` and `rtof` -/

theorem circMat_ladAct {u v s : Fin N} (hu : u ≠ s) (hv : v ≠ s) :
    circMat (ladAct u v s) = ctrlMat s (fun x => aBlk (x u) (x v)) := by
  unfold ladAct hG pG
  rw [Qulin.cx_eq u s hu, Qulin.cx_eq v s hv]
  simp only [List.cons_append, List.nil_append, circMat, one_mul, Qulin.one_mat_eq_ctrl2 u s v,
    Qulin.cx_top_mat_eq_ctrl2 u s v, Qulin.cx_bot_mat_eq_ctrl2 u s v, Line.ctrl2_mul u s v hu hv]
  rfl

theorem circMat_ladRst {u v s : Fin N} (hu : u ≠ s) (hv : v ≠ s) :
    circMat (ladRst u v s) = ctrlMat s (fun x => aInvBlk (x u) (x v)) := by
  unfold ladRst hG pG
  rw [Qulin.cx_eq u s hu, Qulin.cx_eq v s hv]
  simp only [List.cons_append, List.nil_append, circMat, one_mul, Qulin.one_mat_eq_ctrl2 u s v,
    Qulin.cx_top_mat_eq_ctrl2 u s v, Qulin.cx_bot_mat_eq_ctrl2 u s v, Line.ctrl2_mul u s v hu hv]
  rfl

/-- The last four gates of `rtof` are `ladRst` with its first control switched off. -/
theorem circMat_rtofTail {u v s : Fin N} (hu : u ≠ s) (hv : v ≠ s) :
    circMat (pG (Real.pi / 4) s ++ cx v s ++ pG (-(Real.pi / 4)) s ++ hG s)
      = ctrlMat s (fun x => aInvBlk false (x v)) := by
  unfold hG pG
  rw [Qulin.cx_eq v s hv]
  simp only [List.cons_append, List.nil_append, circMat, one_mul, Qulin.one_mat_eq_ctrl2 u s v,
    Qulin.cx_bot_mat_eq_ctrl2 u s v, Line.ctrl2_mul u s v hu hv]
  unfold Line.ctrl2
  congr 1
  funext x
  simp [aInvBlk]

/-- **S3. The relative-phase Toffoli**: flip `s` iff `u` and `v` are one, with the phase
`(i^(x_v) (-1)^(x_s))^(x_u)`. -/
theorem circMat_rtof {u v s : Fin N} (hu : u ≠ s) (hv : v ≠ s) :
    circMat (rtof u v s)
      = fmono (fun x => Function.update x s (xor (x s) (x u && x v)))
          (fun x => wPh (x u) (x v) (x s)) := by
  have hl : rtof u v s = ladAct u v s ++ (pG (Real.pi / 4) s ++ cx v s ++
      pG (-(Real.pi / 4)) s ++ hG s) := by
    simp only [rtof, List.append_assoc]
  have hprod : ∀ x : St N, aInvBlk false (x v) * aBlk (x u) (x v) = wBlk (x u) (x v) := by
    intro x
    rw [aInv_mul_a, Bool.xor_false]
  rw [hl, circMat_append, circMat_rtofTail hu hv, circMat_ladAct hu hv,
    ← Matrix.mul_one (ctrlMat s fun x => aInvBlk false (x v)), ← Qulin.fmono_id_one,
    Qulin.ctrl_fmono_ctrl s id (fun _ => 1) _ _ (fun x => x u && x v) (fun _ _ => rfl)
      (fun _ _ => rfl)]
  · apply Qulin.fmono_congr
    · intro x
      rfl
    · intro x
      simp only [id, one_mul]
      rw [hprod, wBlk_entry]
  · intro x b
    simp only [Function.update_of_ne hv]
  · intro x p q h
    simp only [id]
    rw [hprod]
    exact wBlk_support _ _ _ _ h

/-! ### S5. The chain -/

/-- The chain on the controls `c 0, c 1, ...` and the dirty qubits `a 0, a 1, ...`:
level `j` writes into `a j` and is controlled by `a (j-1)` and `c (j+1)`. -/
noncomputable def gChain (c a : ℕ → Fin N) : ℕ → List (Gate N)
  | 0 => rtof (c 0) (c 1) (a 0)
  | j + 1 =>
    ladAct (a j) (c (j + 2)) (a (j + 1)) ++ gChain c a j ++ ladRst (a j) (c (j + 2)) (a (j + 1))

/-- The phase of `gChain c a j`: the product over the levels `i ≤ j` of
`(i^(x_{c (i+1)}) (-1)^(x_{a i}))^(P_i)`, `P_i` the product of the bits `c 0 .. c i`. -/
noncomputable def wS (c a : ℕ → Fin N) : ℕ → St N → ℂ
  | 0, x => wPh (x (c 0)) (x (c 1)) (x (a 0))
  | j + 1, x => wS c a j x * wPh (pc c (j + 2) x) (x (c (j + 2))) (x (a (j + 1)))

theorem wS_update (c a : ℕ → Fin N) (j : ℕ) (s : Fin N) (hsa : ∀ i ≤ j, s ≠ a i)
    (hsc : ∀ i < j + 2, s ≠ c i) (x : St N) (b : Bool) :
    wS c a j (Function.update x s b) = wS c a j x := by
  induction j with
  | zero =>
    rw [wS, wS, Function.update_of_ne (hsa 0 le_rfl).symm,
      Function.update_of_ne (hsc 0 (by omega)).symm, Function.update_of_ne (hsc 1 (by omega)).symm]
  | succ j ih =>
    rw [wS, wS, Function.update_of_ne (hsa (j + 1) le_rfl).symm,
      Function.update_of_ne (hsc (j + 2) (by omega)).symm,
      Qulin.pc_update c (j + 2) s (fun i hi => hsc i (Nat.lt_succ_of_lt hi)),
      ih (fun i hi => hsa i (Nat.le_succ_of_le hi)) (fun i hi => hsc i (Nat.lt_succ_of_lt hi))]

/-- **S5. The chain** is a function up to phases: `Qulin.wF` with the phase `wS`. -/
theorem circMat_gChain {k : ℕ} {c a : ℕ → Fin N} (ha : Inj (k - 2) a)
    (hca : Disj k c (k - 2) a) (j : ℕ) (hj : j < k - 2) :
    circMat (gChain c a j) = fmono (wF c a j) (wS c a j) := by
  induction j with
  | zero =>
    rw [gChain, circMat_rtof (hca 0 (by omega) 0 hj) (hca 1 (by omega) 0 hj)]
    apply Qulin.fmono_congr
    · intro x
      simp [wF, pc]
    · intro x
      rfl
  | succ j ih =>
    have hu : a j ≠ a (j + 1) := fun h => by
      have := ha j (by omega) (j + 1) hj h
      omega
    have hv : c (j + 2) ≠ a (j + 1) := hca (j + 2) (by omega) (j + 1) hj
    have hsa : ∀ i ≤ j, a (j + 1) ≠ a i := fun i hi h => by
      have := ha (j + 1) hj i (by omega) h
      omega
    have hsc : ∀ i < j + 2, a (j + 1) ≠ c i := fun i hi => (hca i (by omega) (j + 1) hj).symm
    have hprod : ∀ x : St N,
        aInvBlk (wF c a j x (a j)) (wF c a j x (c (j + 2))) * aBlk (x (a j)) (x (c (j + 2)))
          = wBlk (pc c (j + 2) x) (x (c (j + 2))) := by
      intro x
      rw [Qulin.wF_last,
        Qulin.wF_of_ne c a j (c (j + 2)) (fun i hi => hca (j + 2) (by omega) i (by omega)),
        aInv_mul_a, Qulin.xor_xor_self_left]
    rw [gChain, circMat_append, circMat_append, circMat_ladAct hu hv, circMat_ladRst hu hv,
      ih (by omega), ← Matrix.mul_assoc,
      Qulin.ctrl_fmono_ctrl (a (j + 1)) (wF c a j) (wS c a j) _ _ (pc c (j + 3))
        (Qulin.wF_update c a j _ hsa hsc) (wS_update c a j _ hsa hsc)]
    · apply Qulin.fmono_congr
      · intro x
        rfl
      · intro x
        rw [hprod]
        exact congrArg _ (wBlk_entry _ _ _)
    · intro x b
      simp only [Function.update_of_ne hu, Function.update_of_ne hv]
    · intro x p q h
      rw [hprod]
      exact wBlk_support _ _ _ _ h

/-- **The chain inverts its own phase**: the phase after the chain times the phase
before it is one. -/
theorem wS_wF_mul {k : ℕ} {c a : ℕ → Fin N} (ha : Inj (k - 2) a) (hca : Disj k c (k - 2) a)
    (j : ℕ) (hj : j < k - 2) (x : St N) : wS c a j (wF c a j x) * wS c a j x = 1 := by
  induction j with
  | zero =>
    rw [wS, wS, Qulin.wF_ctrl hca 0 hj 0 (by omega), Qulin.wF_ctrl hca 0 hj 1 (by omega),
      Qulin.wF_last]
    change wPh (x (c 0)) (x (c 1)) (xor (x (a 0)) ((true && x (c 0)) && x (c 1))) * _ = 1
    rw [Bool.true_and]
    exact wPh_flip_mul _ _ _
  | succ j ih =>
    have hsa : ∀ i ≤ j, a (j + 1) ≠ a i := fun i hi h => by
      have := ha (j + 1) hj i (by omega) h
      omega
    have hsc : ∀ i < j + 2, a (j + 1) ≠ c i := fun i hi => (hca i (by omega) (j + 1) hj).symm
    have h1 : wS c a j (wF c a (j + 1) x) = wS c a j (wF c a j x) := by
      rw [wF, wS_update c a j _ hsa hsc]
    have h2 : wPh (pc c (j + 2) (wF c a (j + 1) x)) (wF c a (j + 1) x (c (j + 2)))
          (wF c a (j + 1) x (a (j + 1)))
        = wPh (pc c (j + 2) x) (x (c (j + 2)))
          (xor (x (a (j + 1))) (pc c (j + 2) x && x (c (j + 2)))) := by
      rw [Qulin.pc_wF hca (j + 1) hj (j + 2) (by omega),
        Qulin.wF_ctrl hca (j + 1) hj (j + 2) (by omega), Qulin.wF_last]
      rfl
    rw [wS, wS, h1, h2, mul_mul_mul_comm, ih (by omega), wPh_flip_mul, one_mul]

/-! ### S6, S7. The multi-controlled gate on any qubits -/

/-- Half of the multi-controlled gate: the Toffoli onto the target, then the chain. -/
noncomputable def gHalf (k : ℕ) (c a : ℕ → Fin N) (t : Fin N) : List (Gate N) :=
  ccx (c (k - 1)) (a (k - 3)) t ++ gChain c a (k - 3)

/-- **S6.**  Half of the gate is a function up to the phase of the chain. -/
theorem circMat_gHalf {k : ℕ} {c a : ℕ → Fin N} {t : Fin N} (hk : 3 ≤ k)
    (ha : Inj (k - 2) a) (hca : Disj k c (k - 2) a) (htc : ∀ i < k, t ≠ c i)
    (hta : ∀ i < k - 2, t ≠ a i) :
    circMat (gHalf k c a t)
      = fmono (fun x => Function.update (wF c a (k - 3) x) t
            (xor (x t) (x (c (k - 1)) && x (a (k - 3)))))
          (wS c a (k - 3)) := by
  have hj : k - 3 < k - 2 := by omega
  have hab : c (k - 1) ≠ a (k - 3) := hca (k - 1) (by omega) (k - 3) hj
  have hat : c (k - 1) ≠ t := (htc (k - 1) (by omega)).symm
  have hbt : a (k - 3) ≠ t := (hta (k - 3) hj).symm
  have h1 : circMat (ccx (c (k - 1)) (a (k - 3)) t) = permMat _ := Qulin.acts_ccx hab hat hbt
  have hsa : ∀ i ≤ k - 3, t ≠ a i := fun i hi => hta i (by omega)
  have hsc : ∀ i < k - 3 + 2, t ≠ c i := fun i hi => htc i (by omega)
  unfold gHalf
  rw [circMat_append, circMat_gChain ha hca _ hj, h1, Qulin.permMat_eq_fmono, Qulin.fmono_mul]
  apply Qulin.fmono_congr
  · intro x
    exact Qulin.wF_update c a (k - 3) t hsa hsc x _
  · intro x
    rw [mul_one]
    exact wS_update c a (k - 3) t hsa hsc x _

theorem mcx_bit (s u v p : Bool) : xor (xor s (v && u)) (v && xor u p) = xor s (p && v) := by
  cases s <;> cases u <;> cases v <;> cases p <;> rfl

/-- **S7 on any qubits.**  Two halves flip `t` iff all `k` controls are one; the dirty
qubits come back unchanged and there is no phase. -/
theorem acts_gmcx {k : ℕ} {c a : ℕ → Fin N} {t : Fin N} (hk : 3 ≤ k)
    (ha : Inj (k - 2) a) (hca : Disj k c (k - 2) a) (htc : ∀ i < k, t ≠ c i)
    (hta : ∀ i < k - 2, t ≠ a i) :
    Acts (gHalf k c a t ++ gHalf k c a t)
      (fun x => Function.update x t (xor (x t) (pc c k x))) := by
  have hj : k - 3 < k - 2 := by omega
  have hat : c (k - 1) ≠ t := (htc (k - 1) (by omega)).symm
  have hbt : a (k - 3) ≠ t := (hta (k - 3) hj).symm
  have hsa : ∀ i ≤ k - 3, t ≠ a i := fun i hi => hta i (by omega)
  have hsc : ∀ i < k - 3 + 2, t ≠ c i := fun i hi => htc i (by omega)
  unfold Acts
  rw [circMat_append, circMat_gHalf hk ha hca htc hta, Qulin.fmono_mul, Qulin.permMat_eq_fmono]
  apply Qulin.fmono_congr
  · intro x
    have e : pc c k x = (pc c (k - 3 + 2) x && x (c (k - 1))) := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
      rfl
    simp only [Function.comp_apply]
    rw [Qulin.wF_update c a (k - 3) t hsa hsc, Qulin.wF_wF ha hca _ hj, Function.update_self,
      Function.update_of_ne hat, Function.update_of_ne hbt, Qulin.wF_last,
      Qulin.wF_ctrl hca _ hj (k - 1) (by omega), Function.update_idem, e, mcx_bit]
  · intro x
    change wS c a (k - 3) (Function.update (wF c a (k - 3) x) t _) * wS c a (k - 3) x = 1
    rw [wS_update c a (k - 3) t hsa hsc, wS_wF_mul ha hca _ hj]

/-! ### Counting on any qubits -/

theorem cnots_ladAct {u v s : Fin N} (hu : u ≠ s) (hv : v ≠ s) : cnots (ladAct u v s) = 2 := by
  unfold ladAct
  simp only [cnots_append, Qulin.cnots_cx hu, Qulin.cnots_cx hv, cnots_pG, cnots_hG]

theorem cnots_ladRst {u v s : Fin N} (hu : u ≠ s) (hv : v ≠ s) : cnots (ladRst u v s) = 2 := by
  unfold ladRst
  simp only [cnots_append, Qulin.cnots_cx hu, Qulin.cnots_cx hv, cnots_pG, cnots_hG]

theorem cnots_rtof {u v s : Fin N} (hu : u ≠ s) (hv : v ≠ s) : cnots (rtof u v s) = 3 := by
  unfold rtof
  simp only [cnots_append, cnots_ladAct hu hv, Qulin.cnots_cx hv, cnots_pG, cnots_hG]

theorem unitaryGates_ladAct (u v s : Fin N) : UnitaryGates (ladAct u v s) := by
  unfold ladAct
  simp only [unitaryGates_append_iff, unitaryGates_pG, unitaryGates_hG, Qulin.unitaryGates_cx,
    and_self]

theorem unitaryGates_ladRst (u v s : Fin N) : UnitaryGates (ladRst u v s) := by
  unfold ladRst
  simp only [unitaryGates_append_iff, unitaryGates_pG, unitaryGates_hG, Qulin.unitaryGates_cx,
    and_self]

theorem unitaryGates_rtof (u v s : Fin N) : UnitaryGates (rtof u v s) := by
  unfold rtof
  simp only [unitaryGates_append_iff, unitaryGates_pG, unitaryGates_hG, Qulin.unitaryGates_cx,
    unitaryGates_ladAct, and_self]

theorem cnots_gChain {k : ℕ} {c a : ℕ → Fin N} (ha : Inj (k - 2) a)
    (hca : Disj k c (k - 2) a) (j : ℕ) (hj : j < k - 2) :
    cnots (gChain c a j) = 4 * j + 3 := by
  induction j with
  | zero => exact cnots_rtof (hca 0 (by omega) 0 hj) (hca 1 (by omega) 0 hj)
  | succ j ih =>
    have hu : a j ≠ a (j + 1) := fun h => by
      have := ha j (by omega) (j + 1) hj h
      omega
    have hv : c (j + 2) ≠ a (j + 1) := hca (j + 2) (by omega) (j + 1) hj
    rw [gChain, cnots_append, cnots_append, cnots_ladAct hu hv, cnots_ladRst hu hv,
      ih (by omega)]
    omega

theorem unitaryGates_gChain (c a : ℕ → Fin N) (j : ℕ) : UnitaryGates (gChain c a j) := by
  induction j with
  | zero => exact unitaryGates_rtof _ _ _
  | succ j ih =>
    exact unitaryGates_append (unitaryGates_append (unitaryGates_ladAct _ _ _) ih)
      (unitaryGates_ladRst _ _ _)

theorem cnots_gHalf {k : ℕ} {c a : ℕ → Fin N} {t : Fin N} (hk : 3 ≤ k)
    (ha : Inj (k - 2) a) (hca : Disj k c (k - 2) a) (htc : ∀ i < k, t ≠ c i)
    (hta : ∀ i < k - 2, t ≠ a i) : cnots (gHalf k c a t) = 4 * k - 3 := by
  have hj : k - 3 < k - 2 := by omega
  have hab : c (k - 1) ≠ a (k - 3) := hca (k - 1) (by omega) (k - 3) hj
  have hat : c (k - 1) ≠ t := (htc (k - 1) (by omega)).symm
  have hbt : a (k - 3) ≠ t := (hta (k - 3) hj).symm
  unfold gHalf
  rw [cnots_append, Qulin.cnots_ccx hab hat hbt, cnots_gChain ha hca _ hj]
  omega

theorem unitaryGates_gHalf (k : ℕ) (c a : ℕ → Fin N) (t : Fin N) :
    UnitaryGates (gHalf k c a t) :=
  unitaryGates_append (Qulin.unitaryGates_ccx _ _ _) (unitaryGates_gChain c a (k - 3))

/-! ### S7. `mcx k c0 a0 t` on the qubits `c0 + i`, `a0 + i` -/

theorem chain_eq (hN : 0 < N) (c0 a0 j : ℕ) :
    chain N hN c0 a0 j
      = gChain (fun i => qb N hN (c0 + i)) (fun i => qb N hN (a0 + i)) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [chain, gChain, ih]
    rfl

theorem mcxHalf_eq (hN : 0 < N) {k : ℕ} (hk : 3 ≤ k) (c0 a0 t : ℕ) :
    mcxHalf N hN k c0 a0 t
      = gHalf k (fun i => qb N hN (c0 + i)) (fun i => qb N hN (a0 + i)) (qb N hN t) := by
  unfold mcxHalf gHalf
  rw [chain_eq, show c0 + k - 1 = c0 + (k - 1) by omega,
    show a0 + k - 3 = a0 + (k - 3) by omega]

/-- The side conditions of `mcx k c0 a0 t` on `N` qubits: the controls `c0 .. c0+k-1`
exist and the target is none of them; for `k ≥ 4` the dirty qubits `a0 .. a0+k-3` exist,
and are neither the target nor controls. -/
def McxOk (N k c0 a0 t : ℕ) : Prop :=
  1 ≤ k ∧ c0 + k ≤ N ∧ t < N ∧ (t < c0 ∨ c0 + k ≤ t) ∧
  (4 ≤ k → a0 + (k - 2) ≤ N ∧ (t < a0 ∨ a0 + (k - 2) ≤ t) ∧
    (a0 + (k - 2) ≤ c0 ∨ c0 + k ≤ a0))

/-- **S7.**  `mcx k c0 a0 t` flips `t` iff the controls `c0 .. c0+k-1` are all one,
exactly, for every `k ≥ 1`. -/
theorem acts_mcx (hN : 0 < N) {k c0 a0 t : ℕ} (h : McxOk N k c0 a0 t) :
    Acts (mcx N hN k c0 a0 t)
      (fun x => Function.update x (qb N hN t)
        (xor (x (qb N hN t)) (pc (fun i => qb N hN (c0 + i)) k x))) := by
  obtain ⟨hk, hc, ht, htc, hd⟩ := h
  by_cases h1 : k = 1
  · subst h1
    rw [mcx, if_pos rfl]
    exact (Qulin.acts_cx (Qulin.qb_ne hN (by omega) ht (by omega))).congr
      (fun x => by simp [cxFun, pc])
  by_cases h2 : k = 2
  · subst h2
    rw [mcx, if_neg (by omega), if_pos rfl]
    exact (Qulin.acts_ccx (Qulin.qb_ne hN (by omega) (by omega) (by omega))
      (Qulin.qb_ne hN (by omega) ht (by omega)) (Qulin.qb_ne hN (by omega) ht (by omega))).congr
      (fun x => by simp [pc])
  by_cases h3 : k = 3
  · subst h3
    rw [mcx, if_neg (by omega), if_neg (by omega), if_pos rfl]
    exact (acts_c3x (Qulin.qb_ne hN (by omega) (by omega) (by omega))
      (Qulin.qb_ne hN (by omega) (by omega) (by omega))
      (Qulin.qb_ne hN (by omega) (by omega) (by omega))
      (Qulin.qb_ne hN (by omega) ht (by omega)) (Qulin.qb_ne hN (by omega) ht (by omega))
      (Qulin.qb_ne hN (by omega) ht (by omega))).congr
      (fun x => by simp [pc])
  · obtain ⟨hd1, hd2, hd3⟩ := hd (by omega)
    rw [mcx, if_neg h1, if_neg h2, if_neg h3, mcxHalf_eq hN (by omega)]
    exact acts_gmcx (by omega)
      (fun i hi j hj e => by
        have := Qulin.qb_inj hN (by omega) (by omega) e
        omega)
      (fun i hi j hj => Qulin.qb_ne hN (by omega) (by omega) (by omega))
      (fun i hi => Qulin.qb_ne hN ht (by omega) (by omega))
      (fun i hi => Qulin.qb_ne hN ht (by omega) (by omega))

/-- The CNOT count of `mcx`. -/
def mcxCount (k : ℕ) : ℕ :=
  if k = 1 then 1 else if k = 2 then 6 else if k = 3 then 14 else 8 * k - 6

theorem cnots_mcx (hN : 0 < N) {k c0 a0 t : ℕ} (h : McxOk N k c0 a0 t) :
    cnots (mcx N hN k c0 a0 t) = mcxCount k := by
  obtain ⟨hk, hc, ht, htc, hd⟩ := h
  unfold mcxCount
  by_cases h1 : k = 1
  · subst h1
    rw [mcx, if_pos rfl, if_pos rfl]
    exact Qulin.cnots_cx (Qulin.qb_ne hN (by omega) ht (by omega))
  by_cases h2 : k = 2
  · subst h2
    rw [mcx, if_neg (by omega), if_pos rfl, if_neg (by omega), if_pos rfl]
    exact Qulin.cnots_ccx (Qulin.qb_ne hN (by omega) (by omega) (by omega))
      (Qulin.qb_ne hN (by omega) ht (by omega)) (Qulin.qb_ne hN (by omega) ht (by omega))
  by_cases h3 : k = 3
  · subst h3
    rw [mcx, if_neg (by omega), if_neg (by omega), if_pos rfl, if_neg (by omega),
      if_neg (by omega), if_pos rfl]
    exact cnots_c3x (Qulin.qb_ne hN (by omega) (by omega) (by omega))
      (Qulin.qb_ne hN (by omega) (by omega) (by omega))
      (Qulin.qb_ne hN (by omega) (by omega) (by omega))
      (Qulin.qb_ne hN (by omega) ht (by omega)) (Qulin.qb_ne hN (by omega) ht (by omega))
      (Qulin.qb_ne hN (by omega) ht (by omega))
  · obtain ⟨hd1, hd2, hd3⟩ := hd (by omega)
    rw [mcx, if_neg h1, if_neg h2, if_neg h3, if_neg h1, if_neg h2, if_neg h3,
      mcxHalf_eq hN (by omega), cnots_append,
      cnots_gHalf (by omega)
        (fun i hi j hj e => by
          have := Qulin.qb_inj hN (by omega) (by omega) e
          omega)
        (fun i hi j hj => Qulin.qb_ne hN (by omega) (by omega) (by omega))
        (fun i hi => Qulin.qb_ne hN ht (by omega) (by omega))
        (fun i hi => Qulin.qb_ne hN ht (by omega) (by omega))]
    omega

theorem unitaryGates_mcx (hN : 0 < N) (k c0 a0 t : ℕ) :
    UnitaryGates (mcx N hN k c0 a0 t) := by
  have hh : UnitaryGates (mcxHalf N hN k c0 a0 t) := by
    unfold mcxHalf
    rw [chain_eq]
    exact unitaryGates_append (Qulin.unitaryGates_ccx _ _ _) (unitaryGates_gChain _ _ _)
  unfold mcx
  split_ifs
  · exact Qulin.unitaryGates_cx _ _
  · exact Qulin.unitaryGates_ccx _ _ _
  · exact unitaryGates_c3x _ _ _ _
  · exact unitaryGates_append hh hh

end Vale
