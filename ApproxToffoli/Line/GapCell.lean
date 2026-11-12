/-
The seven-CNOT cell on four neighbouring wires `q, s, t, u` of a line.

`gap7 q s t u` (13 gates, 7 CNOTs) has the basis action `s ^= q`, `u ^= q ∧ t`, up to
phases of modulus one.  Its matrix is the CNOT from `q` to `s` times a 2×2 block on `u`
controlled classically by `q` and `t`: the block is `1` if `q = 0`, `Z` if `q = 1` and
`t = 0`, and `Y` if `q = t = 1`.
-/
import Mathlib
import ApproxToffoli.Line.Cells2

namespace Line

open Matrix ExactLine

variable {N : ℕ}

/-- The seven-CNOT cell on neighbouring wires `q, s, t, u`. -/
noncomputable def gap7 (q s t u : Fin N)
    (hqs : q.val + 1 = s.val ∨ s.val + 1 = q.val)
    (hst : s.val + 1 = t.val ∨ t.val + 1 = s.val)
    (htu : t.val + 1 = u.val ∨ u.val + 1 = t.val) : List (Gate N) :=
  [.one u hGate, .one u (pGate (Real.pi / 4)), .cx u t htu.symm,
   .one t (pGate (-Real.pi / 4)), .cx t u htu, .cx s t hst, .cx q s hqs, .cx s t hst,
   .one t (pGate (Real.pi / 4)), .cx t u htu, .one u (pGate (-Real.pi / 4)),
   .cx u t htu.symm, .one u hGate]

theorem cnots_gap7 (q s t u : Fin N) (hqs : q.val + 1 = s.val ∨ s.val + 1 = q.val)
    (hst : s.val + 1 = t.val ∨ t.val + 1 = s.val)
    (htu : t.val + 1 = u.val ∨ u.val + 1 = t.val) : cnots (gap7 q s t u hqs hst htu) = 7 := rfl

theorem unitaryGates_gap7 (q s t u : Fin N) (hqs : q.val + 1 = s.val ∨ s.val + 1 = q.val)
    (hst : s.val + 1 = t.val ∨ t.val + 1 = s.val)
    (htu : t.val + 1 = u.val ∨ u.val + 1 = t.val) :
    UnitaryGates (gap7 q s t u hqs hst htu) := by
  unfold gap7
  repeat first
    | exact unitaryGates_nil
    | apply unitaryGates_cons_cx
    | apply unitaryGates_cons_one _ hGate_unitary
    | apply unitaryGates_cons_one _ (pGate_unitary _)

/-- Every gate of `gap7 q s t u` touches only the wires `q, s, t, u`. -/
theorem circOn_gap7 (q s t u : Fin N) (hqs : q.val + 1 = s.val ∨ s.val + 1 = q.val)
    (hst : s.val + 1 = t.val ∨ t.val + 1 = s.val)
    (htu : t.val + 1 = u.val ∨ u.val + 1 = t.val) (P : Fin N → Prop) (pq : P q) (ps : P s)
    (pt : P t) (pu : P u) : CircOn P (gap7 q s t u hqs hst htu) := by
  intro g hg
  simp only [gap7, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact pu
    | exact pt
    | exact ⟨pu, pt⟩
    | exact ⟨pt, pu⟩
    | exact ⟨ps, pt⟩
    | exact ⟨pq, ps⟩

/-! ### The middle eleven gates: a permutation up to phases -/

/-- The phases of the middle eleven gates. -/
noncomputable def gapMidPhase (q t u : Fin N) (x : St N) : ℂ :=
  if x q && x t then (if x u then Complex.I else -Complex.I) else 1

/-- The basis permutation of the middle eleven gates: `s ^= q`, `u ^= q`. -/
theorem gap7_mid_perm (q s t u : Fin N) (hqs : q ≠ s) (hst : s ≠ t) (htu : t ≠ u)
    (hqt : q ≠ t) (hqu : q ≠ u) (hsu : s ≠ u) :
    cxPerm u t htu.symm * cxPerm t u htu * cxPerm s t hst * cxPerm q s hqs * cxPerm s t hst
        * cxPerm t u htu * cxPerm u t htu.symm
      = cxPerm q s hqs * cxPerm q u hqu := by
  apply Equiv.ext
  intro x
  funext r
  simp only [Equiv.Perm.mul_apply, cxPerm_apply]
  by_cases hr : r = u
  · rw [hr]
    simp [hst, htu, hqt, hqu, hsu, hst.symm, htu.symm, hsu.symm]
    cases x q <;> cases x s <;> cases x t <;> cases x u <;> rfl
  · by_cases hr' : r = t
    · rw [hr']
      simp [hst, htu, hqt, hqu, hsu, hst.symm, htu.symm, hsu.symm]
      cases x q <;> cases x s <;> cases x t <;> cases x u <;> rfl
    · by_cases hr'' : r = s
      · rw [hr'']
        simp [hst, htu, hqt, hqu, hsu, hst.symm, htu.symm, hsu.symm]
      · simp [Function.update_apply, hr, hr', hr'']

/-- The middle eleven gates are the permutation `s ^= q`, `u ^= q` up to the phases
`gapMidPhase`. -/
theorem gap7_mid (q s t u : Fin N) (hqs : q.val + 1 = s.val ∨ s.val + 1 = q.val)
    (hst : s.val + 1 = t.val ∨ t.val + 1 = s.val)
    (htu : t.val + 1 = u.val ∨ u.val + 1 = t.val) (hqt : q ≠ t) (hqu : q ≠ u) (hsu : s ≠ u) :
    (Gate.cx u t htu.symm).mat * (Gate.one u (pGate (-Real.pi / 4))).mat
        * (Gate.cx t u htu).mat * (Gate.one t (pGate (Real.pi / 4))).mat
        * (Gate.cx s t hst).mat * (Gate.cx q s hqs).mat * (Gate.cx s t hst).mat
        * (Gate.cx t u htu).mat * (Gate.one t (pGate (-Real.pi / 4))).mat
        * (Gate.cx u t htu.symm).mat * (Gate.one u (pGate (Real.pi / 4))).mat
      = mono (cxPerm q s (adj_ne hqs) * cxPerm q u hqu) (gapMidPhase q t u) := by
  have nqs : q ≠ s := adj_ne hqs
  have nst : s ≠ t := adj_ne hst
  have ntu : t ≠ u := adj_ne htu
  have h1 := e_quarter_sq
  have h2 := e_neg_quarter_sq
  have h3 := e_quarter_mul_neg
  have h4 := e_neg_mul_quarter
  simp only [Gate.mat, oneMat_pGate, mono_mul, mul_one, one_mul]
  rw [gap7_mid_perm q s t u nqs nst ntu hqt hqu hsu]
  congr 1
  funext x
  simp only [Equiv.Perm.one_apply, cxPerm_apply, gapMidPhase]
  generalize e (Real.pi / 4) = A at *
  generalize e (-Real.pi / 4) = B at *
  simp only [Function.update_self, Function.update_of_ne nst, Function.update_of_ne ntu,
    Function.update_of_ne hqt, Function.update_of_ne hqu, Function.update_of_ne hsu,
    Function.update_of_ne nst.symm, Function.update_of_ne ntu.symm,
    Function.update_of_ne hsu.symm]
  cases x q <;> cases x s <;> cases x t <;> cases x u <;> simp [h1, h2, h3, h4]

/-- The block of the middle eleven gates on `u`, for the bits `a` on `q` and `b` on `t`:
`1`, `X`, `-Y`. -/
def gapMidBlock (a b : Bool) : Matrix Bool Bool ℂ :=
  if a then (if b then m2 0 Complex.I (-Complex.I) 0 else m2 0 1 1 0) else m2 1 0 0 1

/-- The middle eleven gates as a CNOT from `q` to `s` and a block on `u` controlled
classically by `q` and `t`. -/
theorem ctrl2_gapMidBlock (q s t u : Fin N) (hqs : q ≠ s) (hqu : q ≠ u) :
    mono (cxPerm q s hqs) (fun _ => (1 : ℂ)) * ctrl2 q u t gapMidBlock
      = mono (cxPerm q s hqs * cxPerm q u hqu) (gapMidPhase q t u) := by
  have hf : ∀ (x : St N) (b : Bool), (Function.update x u b) q = x q :=
    fun x b => Function.update_of_ne hqu _ _
  have hg : ∀ (x : St N) (a b : Bool), a ≠ xor b (x q) →
      gapMidBlock (x q) (x t) a b = 0 := by
    intro x a b
    unfold gapMidBlock
    cases x q <;> cases x t <;> cases a <;> cases b <;> simp [m2]
  have hp : cxPerm q u hqu = flipPerm u (fun x => x q) hf := Equiv.ext fun _ => rfl
  rw [ctrl2, ctrlMat_eq_mono u (fun x => x q) hf _ hg, mono_mul, hp]
  congr 1
  funext x
  unfold gapMidPhase gapMidBlock
  cases x q <;> cases x t <;> cases x u <;> simp [m2]

/-! ### The whole cell -/

/-- The block of the whole cell on `u`, for the bits `a` on `q` and `b` on `t`:
`1`, `Z`, `Y`. -/
def gapBlock (a b : Bool) : Matrix Bool Bool ℂ :=
  if a then (if b then m2 0 (-Complex.I) Complex.I 0 else m2 1 0 0 (-1)) else m2 1 0 0 1

theorem gap_block (a b : Bool) : hGate * gapMidBlock a b * hGate = gapBlock a b := by
  cases a <;> cases b <;>
    simp only [↓reduceIte, Bool.false_eq_true, hGate_mul_mul, gapMidBlock, gapBlock] <;>
    congr 1 <;> ring

/-- **The seven-CNOT cell** is the CNOT from `q` to `s` times a block on `u` controlled
classically by `q` and `t`: `1` if `q = 0`, `Z` if `q = 1` and `t = 0`, `Y` if
`q = t = 1`. -/
theorem circMat_gap7 (q s t u : Fin N) (hqs : q.val + 1 = s.val ∨ s.val + 1 = q.val)
    (hst : s.val + 1 = t.val ∨ t.val + 1 = s.val)
    (htu : t.val + 1 = u.val ∨ u.val + 1 = t.val) (hqt : q ≠ t) (hqu : q ≠ u) (hsu : s ≠ u) :
    circMat (gap7 q s t u hqs hst htu)
      = mono (cxPerm q s (adj_ne hqs)) (fun _ => (1 : ℂ)) * ctrl2 q u t gapBlock := by
  have hre : circMat (gap7 q s t u hqs hst htu)
      = (Gate.one u hGate).mat
        * ((Gate.cx u t htu.symm).mat * (Gate.one u (pGate (-Real.pi / 4))).mat
          * (Gate.cx t u htu).mat * (Gate.one t (pGate (Real.pi / 4))).mat
          * (Gate.cx s t hst).mat * (Gate.cx q s hqs).mat * (Gate.cx s t hst).mat
          * (Gate.cx t u htu).mat * (Gate.one t (pGate (-Real.pi / 4))).mat
          * (Gate.cx u t htu.symm).mat * (Gate.one u (pGate (Real.pi / 4))).mat)
        * (Gate.one u hGate).mat := by
    simp only [gap7, circMat, one_mul, Matrix.mul_assoc]
  rw [hre, gap7_mid q s t u hqs hst htu hqt hqu hsu,
    ← ctrl2_gapMidBlock q s t u (adj_ne hqs) hqu]
  change oneMat u hGate * (mono (cxPerm q s (adj_ne hqs)) (fun _ => (1 : ℂ))
      * ctrl2 q u t gapMidBlock) * oneMat u hGate = _
  rw [← Matrix.mul_assoc, oneMat_mul_cx_comm u q s (adj_ne hqs) hqu.symm hsu.symm hGate,
    Matrix.mul_assoc, Matrix.mul_assoc]
  congr 1
  change ctrl2 q u t (fun _ _ => hGate)
      * (ctrl2 q u t gapMidBlock * ctrl2 q u t (fun _ _ => hGate)) = _
  rw [ctrl2_mul q u t hqu (adj_ne htu), ctrl2_mul q u t hqu (adj_ne htu)]
  congr 1
  funext a b
  change hGate * (gapMidBlock a b * hGate) = gapBlock a b
  rw [← Matrix.mul_assoc]
  exact gap_block a b

/-- The phases of the cell. -/
noncomputable def gapPhase (q t u : Fin N) (x : St N) : ℂ :=
  if x q then
    (if x t then (if x u then -Complex.I else Complex.I) else (if x u then -1 else 1))
  else 1

theorem gapPhase_unit (q t u : Fin N) (x : St N) :
    star (gapPhase q t u x) * gapPhase q t u x = 1 := by
  unfold gapPhase
  cases x q <;> cases x t <;> cases x u <;> simp

theorem ctrl2_gapBlock (q t u : Fin N) (hqu : q ≠ u) (htu : t ≠ u) :
    ctrl2 q u t gapBlock = mono (ccPerm q u t hqu htu) (gapPhase q t u) := by
  have hg : ∀ (x : St N) (a b : Bool), a ≠ xor b (x q && x t) →
      gapBlock (x q) (x t) a b = 0 := by
    intro x a b
    unfold gapBlock
    cases x q <;> cases x t <;> cases a <;> cases b <;> simp [m2]
  rw [ctrl2, ccPerm, ctrlMat_eq_mono u (fun x => x q && x t) _ _ hg]
  · congr 1
    funext x
    unfold gapPhase gapBlock
    cases x q <;> cases x t <;> cases x u <;> simp [m2]
  · intro x b
    change (Function.update x u b q && Function.update x u b t) = (x q && x t)
    rw [Function.update_of_ne hqu, Function.update_of_ne htu]

/-- **The seven-CNOT cell is a permutation up to phases**: the CNOT from `q` to `s`
and the Toffoli with controls `q`, `t` and target `u`. -/
theorem umono_gap7 (q s t u : Fin N) (hqs : q.val + 1 = s.val ∨ s.val + 1 = q.val)
    (hst : s.val + 1 = t.val ∨ t.val + 1 = s.val)
    (htu : t.val + 1 = u.val ∨ u.val + 1 = t.val) (hqt : q ≠ t) (hqu : q ≠ u) (hsu : s ≠ u) :
    UMono (circMat (gap7 q s t u hqs hst htu))
      (cxPerm q s (adj_ne hqs) * ccPerm q u t hqu (adj_ne htu)) := by
  rw [circMat_gap7 q s t u hqs hst htu hqt hqu hsu, ctrl2_gapBlock q t u hqu (adj_ne htu)]
  exact UMono.mul ⟨fun _ => 1, fun _ => by simp, rfl⟩
    ⟨gapPhase q t u, gapPhase_unit q t u, rfl⟩

/-- **Basis action of the seven-CNOT cell**: `s ^= q`, `u ^= q ∧ t`; all other wires
are unchanged. -/
theorem gapPerm_apply (q s t u : Fin N) (hqs : q ≠ s) (hqu : q ≠ u) (htu : t ≠ u)
    (hsu : s ≠ u) (x : St N) :
    (cxPerm q s hqs * ccPerm q u t hqu htu) x
      = Function.update (Function.update x s (xor (x s) (x q))) u
          (xor (x u) (x q && x t)) := by
  funext r
  simp only [Equiv.Perm.mul_apply, ccPerm_apply, cxPerm_apply]
  by_cases hr : r = u
  · rw [hr]
    simp only [Function.update_self, Function.update_of_ne hsu.symm]
  · by_cases hr' : r = s
    · rw [hr']
      simp only [Function.update_self, Function.update_of_ne hsu, Function.update_of_ne hqu]
    · simp only [Function.update_of_ne hr, Function.update_of_ne hr']

/-- **The phases of the seven-CNOT cell**, entry by entry. -/
theorem circMat_gap7_mono (q s t u : Fin N) (hqs : q.val + 1 = s.val ∨ s.val + 1 = q.val)
    (hst : s.val + 1 = t.val ∨ t.val + 1 = s.val)
    (htu : t.val + 1 = u.val ∨ u.val + 1 = t.val) (hqt : q ≠ t) (hqu : q ≠ u) (hsu : s ≠ u) :
    circMat (gap7 q s t u hqs hst htu)
      = mono (cxPerm q s (adj_ne hqs) * ccPerm q u t hqu (adj_ne htu)) (gapPhase q t u) := by
  rw [circMat_gap7 q s t u hqs hst htu hqt hqu hsu, ctrl2_gapBlock q t u hqu (adj_ne htu),
    mono_mul]
  congr 1
  funext x
  rw [one_mul]

end Line
