/-
The two carry cells of the ripple-carry adder on three neighbouring wires of a line.

* `UMono M σ`: the matrix `M` is the permutation `σ` up to phases of modulus one.
* `wire x i`: the bit of the basis state `x` on wire `i`, indexed by a natural number.
* `fwdCell` (6 CNOTs) sends the bits `(c, u, t)` to `(c ⊕ u, u ⊕ t ⊕ v, v)` with
  `v = maj c u t`; `revCell` (7 CNOTs) sends that triple to `(c, u, c ⊕ u ⊕ t)`.
-/
import Mathlib
import ApproxToffoli.Line.Toggle

namespace Line

open Matrix ExactLine

variable {N : ℕ}

/-! ### Permutations up to unit phases -/

/-- `UMono M σ`: `M` is the permutation `σ` up to phases of modulus one. -/
def UMono {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (σ : Equiv.Perm ι) :
    Prop :=
  ∃ φ : ι → ℂ, (∀ x, star (φ x) * φ x = 1) ∧ M = mono σ φ

theorem UMono.mul {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    {σ τ : Equiv.Perm ι} (hA : UMono A σ) (hB : UMono B τ) : UMono (A * B) (σ * τ) := by
  obtain ⟨φ, hφ, rfl⟩ := hA
  obtain ⟨ψ, hψ, rfl⟩ := hB
  exact mono_mul_unit σ τ φ ψ hφ hψ

theorem umono_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    UMono (1 : Matrix ι ι ℂ) (1 : Equiv.Perm ι) :=
  ⟨fun _ => 1, fun _ => by simp, mono_one.symm⟩

/-- The conjugate transpose of a permutation up to phases. -/
theorem conjTranspose_mono {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι)
    (φ : ι → ℂ) : (mono σ φ)ᴴ = mono σ⁻¹ (fun j => star (φ (σ⁻¹ j))) := by
  ext i j
  simp only [conjTranspose_apply, mono, of_apply]
  by_cases h : j = σ i
  · have h' : i = σ⁻¹ j := by rw [h]; simp
    rw [if_pos h, if_pos h', ← h']
  · have h' : ¬ i = σ⁻¹ j := fun h' => h (by rw [h']; simp)
    rw [if_neg h, if_neg h', star_zero]

theorem UMono.conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    {σ : Equiv.Perm ι} (hA : UMono A σ) : UMono Aᴴ σ⁻¹ := by
  obtain ⟨φ, hφ, rfl⟩ := hA
  refine ⟨fun j => star (φ (σ⁻¹ j)), fun x => ?_, conjTranspose_mono σ φ⟩
  change star (star (φ (σ⁻¹ x))) * star (φ (σ⁻¹ x)) = 1
  rw [star_star, mul_comm]
  exact hφ _

/-! ### Circuits that are permutations up to phases -/

theorem umono_single {g : Gate N} {σ : Equiv.Perm (St N)} (hg : UMono g.mat σ) :
    UMono (circMat [g]) σ := by
  simpa only [circMat, Matrix.one_mul] using hg

theorem umono_cons {g : Gate N} {c : List (Gate N)} {σ τ : Equiv.Perm (St N)}
    (hg : UMono g.mat σ) (hc : UMono (circMat c) τ) : UMono (circMat (g :: c)) (τ * σ) :=
  hc.mul hg

theorem umono_nil : UMono (circMat ([] : List (Gate N))) 1 := umono_one

theorem umono_append {c d : List (Gate N)} {σ τ : Equiv.Perm (St N)}
    (hc : UMono (circMat c) σ) (hd : UMono (circMat d) τ) :
    UMono (circMat (c ++ d)) (τ * σ) := by
  rw [circMat_append]
  exact hd.mul hc

theorem umono_cx (c t : Fin N) (adj : c.val + 1 = t.val ∨ t.val + 1 = c.val) :
    UMono (Gate.cx c t adj).mat (cxPerm c t (adj_ne adj)) :=
  ⟨fun _ => 1, fun _ => by simp, rfl⟩

/-- The basis permutation of a NOT on wire `q`. -/
def xPerm (q : Fin N) : Equiv.Perm (St N) := flipPerm q (fun _ => true) (fun _ _ => rfl)

theorem xPerm_apply (q : Fin N) (x : St N) : xPerm q x = Function.update x q (!x q) := by
  rw [xPerm, flipPerm_apply]
  simp

theorem oneMat_xGate (q : Fin N) : oneMat q xGate = mono (xPerm q) (fun _ => (1 : ℂ)) := by
  rw [xPerm, flip_eq_ctrlMat]
  rfl

theorem umono_x (q : Fin N) : UMono (Gate.one q xGate).mat (xPerm q) :=
  ⟨fun _ => 1, fun _ => by simp, oneMat_xGate q⟩

theorem umono_rccx (top mid bot : Fin N)
    (h1 : top.val + 1 = mid.val ∨ mid.val + 1 = top.val)
    (h2 : bot.val + 1 = mid.val ∨ mid.val + 1 = bot.val) :
    UMono (circMat (rccx top mid bot h1 h2)) (ccPerm top mid bot (adj_ne h1) (adj_ne h2)) :=
  ⟨rccxPhase top mid bot, rccxPhase_unit top mid bot, circMat_rccx top mid bot h1 h2⟩

/-! ### Bits indexed by natural numbers -/

/-- The bit of `x` on wire `i` (`false` if there is no such wire). -/
def wire (x : St N) (i : ℕ) : Bool := if h : i < N then x ⟨i, h⟩ else false

theorem wire_mk (x : St N) (i : ℕ) (h : i < N) : wire x i = x ⟨i, h⟩ := dif_pos h

theorem wire_val (x : St N) (q : Fin N) : wire x q.val = x q := dif_pos q.isLt

theorem wire_ext {x y : St N} (h : ∀ i, wire x i = wire y i) : x = y := by
  funext r
  rw [← wire_val x r, ← wire_val y r]
  exact h _

theorem wire_update (x : St N) (q : Fin N) (b : Bool) (i : ℕ) :
    wire (Function.update x q b) i = if i = q.val then b else wire x i := by
  unfold wire
  by_cases h : i < N
  · rw [dif_pos h, dif_pos h]
    by_cases hq : i = q.val
    · have hq' : (⟨i, h⟩ : Fin N) = q := Fin.ext hq
      rw [if_pos hq, hq', Function.update_self]
    · rw [if_neg hq, Function.update_of_ne]
      intro hh
      exact hq (congrArg Fin.val hh)
  · rw [dif_neg h, dif_neg h, if_neg]
    intro hh
    exact h (hh ▸ q.isLt)

/-! ### States with three bits replaced -/

/-- Replace the bits on wires `q0, q1, q2` by `a, b, c`. -/
def upd3 (q0 q1 q2 : Fin N) (x : St N) (a b c : Bool) : St N :=
  Function.update (Function.update (Function.update x q0 a) q1 b) q2 c

section upd3

variable {q0 q1 q2 : Fin N}

theorem upd3_get2 (x : St N) (a b c : Bool) : upd3 q0 q1 q2 x a b c q2 = c :=
  Function.update_self _ _ _

theorem upd3_get1 (n12 : q1 ≠ q2) (x : St N) (a b c : Bool) :
    upd3 q0 q1 q2 x a b c q1 = b := by
  rw [upd3, Function.update_of_ne n12, Function.update_self]

theorem upd3_get0 (n01 : q0 ≠ q1) (n02 : q0 ≠ q2) (x : St N) (a b c : Bool) :
    upd3 q0 q1 q2 x a b c q0 = a := by
  rw [upd3, Function.update_of_ne n02, Function.update_of_ne n01, Function.update_self]

theorem upd3_set2 (x : St N) (a b c c' : Bool) :
    Function.update (upd3 q0 q1 q2 x a b c) q2 c' = upd3 q0 q1 q2 x a b c' :=
  Function.update_idem _ _ _

theorem upd3_set1 (n12 : q1 ≠ q2) (x : St N) (a b c b' : Bool) :
    Function.update (upd3 q0 q1 q2 x a b c) q1 b' = upd3 q0 q1 q2 x a b' c := by
  rw [upd3, upd3, Function.update_comm n12.symm, Function.update_idem]

theorem upd3_set0 (n01 : q0 ≠ q1) (n02 : q0 ≠ q2) (x : St N) (a b c a' : Bool) :
    Function.update (upd3 q0 q1 q2 x a b c) q0 a' = upd3 q0 q1 q2 x a' b c := by
  rw [upd3, upd3, Function.update_comm n02.symm, Function.update_comm n01.symm,
    Function.update_idem]

theorem upd3_self (x : St N) : upd3 q0 q1 q2 x (x q0) (x q1) (x q2) = x := by
  simp [upd3]

theorem upd3_eq_update (x : St N) (c : Bool) :
    upd3 q0 q1 q2 x (x q0) (x q1) c = Function.update x q2 c := by
  simp [upd3]

theorem wire_upd3 (x : St N) (a b c : Bool) (j : ℕ) :
    wire (upd3 q0 q1 q2 x a b c) j
      = if j = q2.val then c else if j = q1.val then b else if j = q0.val then a
        else wire x j := by
  rw [upd3, wire_update, wire_update, wire_update]

end upd3

/-! ### The forward carry cell -/

/-- Majority of three bits. -/
def maj (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

theorem fin_ne2 {q0 q1 q2 : Fin N} (h01 : q0.val + 1 = q1.val) (h12 : q1.val + 1 = q2.val) :
    q0 ≠ q2 := by
  intro h
  rw [h] at h01
  omega

/-- The forward carry cell on wires `q0, q1 = q0 + 1, q2 = q0 + 2` (6 CNOTs). -/
noncomputable def fwdCell (q0 q1 q2 : Fin N) (h01 : q0.val + 1 = q1.val)
    (h12 : q1.val + 1 = q2.val) : List (Gate N) :=
  [.cx q1 q2 (Or.inl h12), .cx q1 q0 (Or.inr h01), .one q0 xGate]
    ++ rccx q0 q1 q2 (Or.inl h01) (Or.inr h12)
    ++ [.cx q1 q2 (Or.inl h12), .one q0 xGate]

/-- The basis permutation of the forward cell, as the product of its gates. -/
def fwdPerm (q0 q1 q2 : Fin N) (h01 : q0.val + 1 = q1.val) (h12 : q1.val + 1 = q2.val) :
    Equiv.Perm (St N) :=
  (xPerm q0 * cxPerm q1 q2 (adj_ne (Or.inl h12)))
    * (ccPerm q0 q1 q2 (adj_ne (Or.inl h01)) (adj_ne (Or.inr h12))
      * ((xPerm q0 * cxPerm q1 q0 (adj_ne (Or.inr h01))) * cxPerm q1 q2 (adj_ne (Or.inl h12))))

theorem cnots_fwdCell (q0 q1 q2 : Fin N) (h01 : q0.val + 1 = q1.val)
    (h12 : q1.val + 1 = q2.val) : cnots (fwdCell q0 q1 q2 h01 h12) = 6 := rfl

theorem unitaryGates_fwdCell (q0 q1 q2 : Fin N) (h01 : q0.val + 1 = q1.val)
    (h12 : q1.val + 1 = q2.val) : UnitaryGates (fwdCell q0 q1 q2 h01 h12) :=
  unitaryGates_append (unitaryGates_append
    (unitaryGates_cons_cx _ _ _ (unitaryGates_cons_cx _ _ _
      (unitaryGates_cons_one _ xGate_unitary unitaryGates_nil)))
    (unitaryGates_rccx _ _ _ _ _))
    (unitaryGates_cons_cx _ _ _ (unitaryGates_cons_one _ xGate_unitary unitaryGates_nil))

/-- The forward cell is a permutation up to phases. -/
theorem umono_fwdCell (q0 q1 q2 : Fin N) (h01 : q0.val + 1 = q1.val)
    (h12 : q1.val + 1 = q2.val) :
    UMono (circMat (fwdCell q0 q1 q2 h01 h12)) (fwdPerm q0 q1 q2 h01 h12) :=
  umono_append (umono_append
    (umono_cons (umono_cx _ _ _) (umono_cons (umono_cx _ _ _) (umono_single (umono_x _))))
    (umono_rccx _ _ _ _ _))
    (umono_cons (umono_cx _ _ _) (umono_single (umono_x _)))

theorem fwdPerm_upd3 (q0 q1 q2 : Fin N) (h01 : q0.val + 1 = q1.val)
    (h12 : q1.val + 1 = q2.val) (x : St N) (a b c : Bool) :
    fwdPerm q0 q1 q2 h01 h12 (upd3 q0 q1 q2 x a b c)
      = upd3 q0 q1 q2 x (xor a b) (xor (xor b c) (maj a b c)) (maj a b c) := by
  have n01 : q0 ≠ q1 := adj_ne (Or.inl h01)
  have n12 : q1 ≠ q2 := adj_ne (Or.inl h12)
  have n02 : q0 ≠ q2 := fin_ne2 h01 h12
  simp only [fwdPerm, Equiv.Perm.mul_apply, cxPerm_apply, ccPerm_apply, xPerm_apply,
    upd3_get0 n01 n02, upd3_get1 n12, upd3_get2, upd3_set0 n01 n02, upd3_set1 n12, upd3_set2]
  cases a <;> cases b <;> cases c <;> rfl

/-- **Basis action of the forward cell**: `(c, u, t) ↦ (c ⊕ u, u ⊕ t ⊕ v, v)` with
`v = maj c u t`; all other wires are unchanged. -/
theorem fwdPerm_apply (q0 q1 q2 : Fin N) (h01 : q0.val + 1 = q1.val)
    (h12 : q1.val + 1 = q2.val) (x : St N) :
    fwdPerm q0 q1 q2 h01 h12 x
      = upd3 q0 q1 q2 x (xor (x q0) (x q1)) (xor (xor (x q1) (x q2)) (maj (x q0) (x q1) (x q2)))
          (maj (x q0) (x q1) (x q2)) := by
  have h := fwdPerm_upd3 q0 q1 q2 h01 h12 x (x q0) (x q1) (x q2)
  rwa [upd3_self] at h

/-! ### The reverse carry cell -/

/-- Output bit of the reverse cell on wire `q0`, for input bits `(a, b, c)`. -/
def rev0 (a b c : Bool) : Bool := !(xor b (!a && !(xor c b)))

/-- Output bit of the reverse cell on wire `q1`. -/
def rev1 (a b c : Bool) : Bool := xor (xor b (!a && !(xor c b))) (!a)

/-- Output bit of the reverse cell on wire `q2`. -/
def rev2 (a b c : Bool) : Bool := !(xor c (!a && !(xor c b)))

theorem rev0_fwd (c u t : Bool) :
    rev0 (xor c u) (xor (xor u t) (maj c u t)) (maj c u t) = c := by
  cases c <;> cases u <;> cases t <;> rfl

theorem rev1_fwd (c u t : Bool) :
    rev1 (xor c u) (xor (xor u t) (maj c u t)) (maj c u t) = u := by
  cases c <;> cases u <;> cases t <;> rfl

theorem rev2_fwd (c u t : Bool) :
    rev2 (xor c u) (xor (xor u t) (maj c u t)) (maj c u t) = xor (xor c u) t := by
  cases c <;> cases u <;> cases t <;> rfl

/-- The reverse carry cell on wires `q0, q1 = q0 + 1, q2 = q0 + 2` (7 CNOTs). -/
noncomputable def revCell (q0 q1 q2 : Fin N) (h01 : q0.val + 1 = q1.val)
    (h12 : q1.val + 1 = q2.val) : List (Gate N) :=
  [.cx q1 q2 (Or.inl h12), .one q0 xGate, .one q2 xGate]
    ++ rccx q0 q1 q2 (Or.inl h01) (Or.inr h12)
    ++ [.cx q1 q2 (Or.inl h12), .cx q0 q1 (Or.inl h01), .cx q1 q0 (Or.inr h01), .one q0 xGate]

/-- The basis permutation of the reverse cell, as the product of its gates. -/
def revPerm (q0 q1 q2 : Fin N) (h01 : q0.val + 1 = q1.val) (h12 : q1.val + 1 = q2.val) :
    Equiv.Perm (St N) :=
  (((xPerm q0 * cxPerm q1 q0 (adj_ne (Or.inr h01))) * cxPerm q0 q1 (adj_ne (Or.inl h01)))
      * cxPerm q1 q2 (adj_ne (Or.inl h12)))
    * (ccPerm q0 q1 q2 (adj_ne (Or.inl h01)) (adj_ne (Or.inr h12))
      * ((xPerm q2 * xPerm q0) * cxPerm q1 q2 (adj_ne (Or.inl h12))))

theorem cnots_revCell (q0 q1 q2 : Fin N) (h01 : q0.val + 1 = q1.val)
    (h12 : q1.val + 1 = q2.val) : cnots (revCell q0 q1 q2 h01 h12) = 7 := rfl

theorem unitaryGates_revCell (q0 q1 q2 : Fin N) (h01 : q0.val + 1 = q1.val)
    (h12 : q1.val + 1 = q2.val) : UnitaryGates (revCell q0 q1 q2 h01 h12) :=
  unitaryGates_append (unitaryGates_append
    (unitaryGates_cons_cx _ _ _ (unitaryGates_cons_one _ xGate_unitary
      (unitaryGates_cons_one _ xGate_unitary unitaryGates_nil)))
    (unitaryGates_rccx _ _ _ _ _))
    (unitaryGates_cons_cx _ _ _ (unitaryGates_cons_cx _ _ _ (unitaryGates_cons_cx _ _ _
      (unitaryGates_cons_one _ xGate_unitary unitaryGates_nil))))

/-- The reverse cell is a permutation up to phases. -/
theorem umono_revCell (q0 q1 q2 : Fin N) (h01 : q0.val + 1 = q1.val)
    (h12 : q1.val + 1 = q2.val) :
    UMono (circMat (revCell q0 q1 q2 h01 h12)) (revPerm q0 q1 q2 h01 h12) :=
  umono_append (umono_append
    (umono_cons (umono_cx _ _ _) (umono_cons (umono_x _) (umono_single (umono_x _))))
    (umono_rccx _ _ _ _ _))
    (umono_cons (umono_cx _ _ _) (umono_cons (umono_cx _ _ _)
      (umono_cons (umono_cx _ _ _) (umono_single (umono_x _)))))

theorem revPerm_upd3 (q0 q1 q2 : Fin N) (h01 : q0.val + 1 = q1.val)
    (h12 : q1.val + 1 = q2.val) (x : St N) (a b c : Bool) :
    revPerm q0 q1 q2 h01 h12 (upd3 q0 q1 q2 x a b c)
      = upd3 q0 q1 q2 x (rev0 a b c) (rev1 a b c) (rev2 a b c) := by
  have n01 : q0 ≠ q1 := adj_ne (Or.inl h01)
  have n12 : q1 ≠ q2 := adj_ne (Or.inl h12)
  have n02 : q0 ≠ q2 := fin_ne2 h01 h12
  simp only [revPerm, Equiv.Perm.mul_apply, cxPerm_apply, ccPerm_apply, xPerm_apply,
    upd3_get0 n01 n02, upd3_get1 n12, upd3_get2, upd3_set0 n01 n02, upd3_set1 n12, upd3_set2]
  cases a <;> cases b <;> cases c <;> rfl

/-- **Basis action of the reverse cell** on arbitrary input bits. -/
theorem revPerm_apply (q0 q1 q2 : Fin N) (h01 : q0.val + 1 = q1.val)
    (h12 : q1.val + 1 = q2.val) (x : St N) :
    revPerm q0 q1 q2 h01 h12 x
      = upd3 q0 q1 q2 x (rev0 (x q0) (x q1) (x q2)) (rev1 (x q0) (x q1) (x q2))
          (rev2 (x q0) (x q1) (x q2)) := by
  have h := revPerm_upd3 q0 q1 q2 h01 h12 x (x q0) (x q1) (x q2)
  rwa [upd3_self] at h

/-- **The reverse cell undoes the forward cell** up to the sum bit: it sends the
forward cell's output for input `(c, u, t)` to `(c, u, c ⊕ u ⊕ t)`. -/
theorem revPerm_fwdPerm (q0 q1 q2 : Fin N) (h01 : q0.val + 1 = q1.val)
    (h12 : q1.val + 1 = q2.val) (x : St N) :
    revPerm q0 q1 q2 h01 h12 (fwdPerm q0 q1 q2 h01 h12 x)
      = Function.update x q2 (xor (xor (x q0) (x q1)) (x q2)) := by
  rw [fwdPerm_apply, revPerm_upd3, rev0_fwd, rev1_fwd, rev2_fwd, upd3_eq_update]

end Line
