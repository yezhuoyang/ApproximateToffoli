/-
Circuits on disjoint parts of the line commute.

* `Gate.On P g`: every wire touched by the gate `g` satisfies `P`.
* `CircOn P c`: every gate of the circuit `c` is on `P`.
* `circMat_comm_of_disjoint`: circuits on disjoint sets of wires commute.
* `circMat_comm_below_above`: the special case "wires `< w`" against "wires `≥ w`".
-/
import Mathlib
import ApproxToffoli.Line.Carry

namespace Line

open Matrix ExactLine

variable {N : ℕ}

/-! ### Which wires a gate touches -/

/-- Every wire touched by the gate satisfies `P`. -/
def Gate.On (P : Fin N → Prop) : Gate N → Prop
  | .cx c t _ => P c ∧ P t
  | .one q _ => P q

/-- Every gate of the circuit touches only wires that satisfy `P`. -/
def CircOn (P : Fin N → Prop) (c : List (Gate N)) : Prop := ∀ g ∈ c, g.On P

/-- The circuit touches only wires `< w`. -/
def Below (w : ℕ) (c : List (Gate N)) : Prop := CircOn (fun r => r.val < w) c

/-- The circuit touches only wires `≥ w`. -/
def Above (w : ℕ) (c : List (Gate N)) : Prop := CircOn (fun r => w ≤ r.val) c

theorem Gate.On.mono {P Q : Fin N → Prop} (h : ∀ r, P r → Q r) {g : Gate N} (hg : g.On P) :
    g.On Q := by
  cases g with
  | cx c t adj => exact ⟨h _ hg.1, h _ hg.2⟩
  | one q m => exact h _ hg

theorem CircOn.mono {P Q : Fin N → Prop} (h : ∀ r, P r → Q r) {c : List (Gate N)}
    (hc : CircOn P c) : CircOn Q c := fun g hg => (hc g hg).mono h

theorem circOn_nil (P : Fin N → Prop) : CircOn P ([] : List (Gate N)) := by
  intro g hg
  simp at hg

theorem circOn_cons {P : Fin N → Prop} {g : Gate N} {c : List (Gate N)} :
    CircOn P (g :: c) ↔ g.On P ∧ CircOn P c := by
  simp [CircOn]

theorem circOn_append {P : Fin N → Prop} {c d : List (Gate N)} :
    CircOn P (c ++ d) ↔ CircOn P c ∧ CircOn P d := by
  simp only [CircOn, List.mem_append]
  constructor
  · intro h
    exact ⟨fun g hg => h g (Or.inl hg), fun g hg => h g (Or.inr hg)⟩
  · rintro ⟨h1, h2⟩ g (hg | hg)
    · exact h1 g hg
    · exact h2 g hg

theorem circOn_invCirc {P : Fin N → Prop} {c : List (Gate N)} (hc : CircOn P c) :
    CircOn P (invCirc c) := by
  intro g hg
  unfold invCirc at hg
  rw [List.mem_reverse, List.mem_map] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  have := hc g' hg'
  cases g' with
  | cx c' t adj => exact this
  | one q m => exact this

/-! ### Pairwise commutation of gates on different wires -/

/-- The product of two one-qubit gates on different wires, entry by entry. -/
theorem oneMat_mul_oneMat_apply (q q' : Fin N) (hne : q ≠ q') (g h : Matrix Bool Bool ℂ)
    (y x : St N) :
    (oneMat q g * oneMat q' h) y x
      = if (∀ r, r ≠ q → r ≠ q' → y r = x r) then g (y q) (x q) * h (y q') (x q') else 0 := by
  rw [Matrix.mul_apply, sum_agree q' x]
  · have h2 : ∀ b, (∀ r, r ≠ q' → Function.update x q' b r = x r) :=
      fun b r hr => Function.update_of_ne hr _ _
    have key : ∀ b, (∀ r, r ≠ q → y r = Function.update x q' b r)
        ↔ (y q' = b ∧ ∀ r, r ≠ q → r ≠ q' → y r = x r) := by
      intro b
      constructor
      · intro H
        refine ⟨?_, fun r hr hr' => ?_⟩
        · have := H q' (Ne.symm hne)
          rwa [Function.update_self] at this
        · have := H r hr
          rwa [Function.update_of_ne hr'] at this
      · rintro ⟨H1, H2⟩ r hr
        by_cases hr' : r = q'
        · rw [hr', Function.update_self, H1]
        · rw [Function.update_of_ne hr']
          exact H2 r hr hr'
    simp only [oneMat, of_apply, if_pos (h2 _), Function.update_self,
      Function.update_of_ne hne, key]
    by_cases hA : ∀ r, r ≠ q → r ≠ q' → y r = x r
    · cases hy : y q' <;> simp
    · simp [hA]
  · intro z hz
    simp [oneMat, hz]

/-- One-qubit gates on different wires commute. -/
theorem oneMat_mul_oneMat_comm (q q' : Fin N) (hne : q ≠ q') (g h : Matrix Bool Bool ℂ) :
    oneMat q g * oneMat q' h = oneMat q' h * oneMat q g := by
  ext y x
  rw [oneMat_mul_oneMat_apply q q' hne, oneMat_mul_oneMat_apply q' q (Ne.symm hne)]
  have key : (∀ r, r ≠ q → r ≠ q' → y r = x r) ↔ (∀ r, r ≠ q' → r ≠ q → y r = x r) :=
    ⟨fun H r h1 h2 => H r h2 h1, fun H r h1 h2 => H r h2 h1⟩
  by_cases hA : ∀ r, r ≠ q → r ≠ q' → y r = x r
  · rw [if_pos hA, if_pos (key.1 hA), mul_comm]
  · rw [if_neg hA, if_neg (fun H => hA (key.2 H))]

/-- CNOTs on disjoint pairs of wires commute, as basis permutations. -/
theorem cxPerm_comm (c t c' t' : Fin N) (h : c ≠ t) (h' : c' ≠ t') (htt : t ≠ t')
    (htc : t ≠ c') (hct : c ≠ t') :
    cxPerm c t h * cxPerm c' t' h' = cxPerm c' t' h' * cxPerm c t h := by
  apply Equiv.ext
  intro x
  funext r
  simp only [Equiv.Perm.mul_apply, cxPerm_apply]
  by_cases hr : r = t
  · rw [hr]
    simp [htt, hct, Ne.symm htc]
  · by_cases hr' : r = t'
    · rw [hr']
      simp [htt, hct, Ne.symm htt, Ne.symm htc]
    · simp [Function.update_apply, hr, hr']

/-- Two gates on disjoint sets of wires commute. -/
theorem gate_mat_comm {P Q : Fin N → Prop} (hPQ : ∀ r, P r → Q r → False) {g h : Gate N}
    (hg : g.On P) (hh : h.On Q) : g.mat * h.mat = h.mat * g.mat := by
  have ne : ∀ {r s : Fin N}, P r → Q s → r ≠ s := by
    intro r s hr hs hrs
    rw [hrs] at hr
    exact hPQ s hr hs
  cases g with
  | cx c t adj =>
    cases h with
    | cx c' t' adj' =>
      change mono _ _ * mono _ _ = mono _ _ * mono _ _
      rw [mono_mul, mono_mul,
        cxPerm_comm c t c' t' (adj_ne adj) (adj_ne adj') (ne hg.2 hh.2) (ne hg.2 hh.1)
          (ne hg.1 hh.2)]
    | one q m =>
      exact (one_mat_mul_cx_mat_comm q c t adj (ne hg.1 hh).symm (ne hg.2 hh).symm m).symm
  | one q m =>
    cases h with
    | cx c' t' adj' => exact one_mat_mul_cx_mat_comm q c' t' adj' (ne hg hh.1) (ne hg hh.2) m
    | one q' m' => exact oneMat_mul_oneMat_comm q q' (ne hg hh) m m'

/-! ### Circuits on disjoint sets of wires commute -/

theorem gate_mat_comm_circMat {P Q : Fin N → Prop} (hPQ : ∀ r, P r → Q r → False)
    {g : Gate N} (hg : g.On P) {d : List (Gate N)} (hd : CircOn Q d) :
    g.mat * circMat d = circMat d * g.mat := by
  induction d with
  | nil => simp [circMat]
  | cons h d ih =>
    have hh := circOn_cons.1 hd
    simp only [circMat]
    rw [← Matrix.mul_assoc, ih hh.2, Matrix.mul_assoc, gate_mat_comm hPQ hg hh.1,
      Matrix.mul_assoc]

/-- **Circuits on disjoint sets of wires commute.** -/
theorem circMat_comm_of_disjoint {P Q : Fin N → Prop} (hPQ : ∀ r, P r → Q r → False)
    {c d : List (Gate N)} (hc : CircOn P c) (hd : CircOn Q d) :
    circMat c * circMat d = circMat d * circMat c := by
  induction c with
  | nil => simp [circMat]
  | cons g c ih =>
    have hg := circOn_cons.1 hc
    simp only [circMat]
    rw [Matrix.mul_assoc, gate_mat_comm_circMat hPQ hg.1 hd, ← Matrix.mul_assoc, ih hg.2,
      Matrix.mul_assoc]

/-- **A circuit on the wires `< w` commutes with a circuit on the wires `≥ w`.** -/
theorem circMat_comm_below_above (w : ℕ) {c d : List (Gate N)} (hc : Below w c)
    (hd : Above w d) : circMat c * circMat d = circMat d * circMat c :=
  circMat_comm_of_disjoint (fun r (h1 : r.val < w) (h2 : w ≤ r.val) => by omega) hc hd

/-- The two circuits may be appended in either order. -/
theorem circMat_append_comm {P Q : Fin N → Prop} (hPQ : ∀ r, P r → Q r → False)
    {c d : List (Gate N)} (hc : CircOn P c) (hd : CircOn Q d) :
    circMat (c ++ d) = circMat (d ++ c) := by
  rw [circMat_append, circMat_append, circMat_comm_of_disjoint hPQ hc hd]

end Line
