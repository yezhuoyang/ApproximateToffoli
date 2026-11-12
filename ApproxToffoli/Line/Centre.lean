/-
The centre circuit on a line: `6 a - 3` CNOTs.

Wires (natural-number positions): `S_i = 2a - 2i` (`0 ≤ i ≤ a`), `T_i = 2a - 2i - 1`
(`0 ≤ i < a`).  The circuit

    centre a = [X S_0, X T_0, cx S_0 T_0] ++ halves ++ core ++ invCirc halves
                 ++ [cx S_0 T_0, X S_a]

is, up to phases of modulus one, the basis permutation that flips `S_0` and `T_0`, adds
`p = x(S_0) ⊕ x(T_0)` to `S_1`, adds `p ∧ x(T_1) ∧ … ∧ x(T_j)` to `S_{j+1}`, and flips
`S_a` (wire `0`) once more.

This file: the building blocks at a natural-number offset, the nested circuit `nest`,
and the proof that it is a permutation up to phases.  The basis action is computed in
`CentreSpec.lean`.
-/
import Mathlib
import ApproxToffoli.Line.GapCell

namespace Line

open Matrix ExactLine

variable {N : ℕ}

/-! ### A circuit of unitary gates has a unitary matrix -/

theorem gate_mat_unitary (g : Gate N)
    (hg : ∀ q m, g = Gate.one q m → m ∈ Matrix.unitaryGroup Bool ℂ) :
    g.matᴴ * g.mat = 1 := by
  cases g with
  | cx c t adj =>
    rw [conjTranspose_gate_mat]
    change mono _ _ * mono _ _ = 1
    rw [mono_mul]
    have h : cxPerm c t (adj_ne adj) * cxPerm c t (adj_ne adj) = 1 := by
      apply Equiv.ext
      intro x
      exact cxPerm_cxPerm c t (adj_ne adj) x
    rw [h]
    simp only [mul_one]
    exact mono_one
  | one q m =>
    have hm := hg q m rfl
    rw [conjTranspose_gate_mat]
    change oneMat q mᴴ * oneMat q m = 1
    rw [oneMat_mul, ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.1 hm,
      oneMat_one]

/-- **A circuit of unitary gates has a unitary matrix.** -/
theorem circMat_unitary {c : List (Gate N)} (hc : UnitaryGates c) :
    (circMat c)ᴴ * circMat c = 1 := by
  induction c with
  | nil => simp [circMat]
  | cons g c ih =>
    have hg : g.matᴴ * g.mat = 1 :=
      gate_mat_unitary g (fun q m h => hc g List.mem_cons_self q m h)
    have hc' : UnitaryGates c := fun g' hg' => hc g' (List.mem_cons_of_mem _ hg')
    simp only [circMat, conjTranspose_mul]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (circMat c), ih hc', Matrix.one_mul, hg]

/-! ### Conjugation by a circuit -/

theorem invCirc_append (c d : List (Gate N)) : invCirc (c ++ d) = invCirc d ++ invCirc c := by
  simp [invCirc]

/-- **Half-to-cell replacement.**  In a conjugation `c ++ d ++ invCirc c` the circuit
`c` may be extended by any circuit `t` of unitary gates that commutes with `d`. -/
theorem circMat_conj_append {c t d : List (Gate N)} (ht : UnitaryGates t)
    (hcomm : circMat t * circMat d = circMat d * circMat t) :
    circMat (c ++ d ++ invCirc c) = circMat ((c ++ t) ++ d ++ invCirc (c ++ t)) := by
  have h : (circMat t)ᴴ * (circMat d * (circMat t * circMat c)) = circMat d * circMat c := by
    rw [← Matrix.mul_assoc (circMat d), ← hcomm, Matrix.mul_assoc (circMat t),
      ← Matrix.mul_assoc (circMat t)ᴴ, circMat_unitary ht, Matrix.one_mul]
  simp only [circMat_append, circMat_invCirc, conjTranspose_mul]
  rw [Matrix.mul_assoc, h]

/-- Conjugating a permutation up to phases by a permutation up to phases. -/
theorem umono_conj {c d : List (Gate N)} {σ τ : Equiv.Perm (St N)}
    (hc : UMono (circMat c) σ) (hd : UMono (circMat d) τ) :
    UMono (circMat (c ++ d ++ invCirc c)) (σ⁻¹ * (τ * σ)) := by
  rw [circMat_append, circMat_invCirc]
  exact hc.conjTranspose.mul (umono_append hc hd)

/-! ### The inverse of the moving cell on basis states -/

/-- The inverse moving cell: `(ya, yb, yc) ↦ (ya, yc, yb ⊕ (ya ∧ yc))`. -/
theorem jPerm_inv_apply (a b c : Fin N) (hab : a ≠ b) (hcb : c ≠ b) (hac : a ≠ c) (y : St N) :
    (jPerm a b c hab hcb)⁻¹ y = upd3 a b c y (y a) (y c) (xor (y b) (y a && y c)) := by
  have hbc : b ≠ c := hcb.symm
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, jPerm_apply a b c hab hcb hac,
    upd3_get0 hab hac, upd3_get1 hbc, upd3_get2]
  funext r
  by_cases h1 : r = c
  · rw [h1, upd3_get2]
  · by_cases h2 : r = b
    · rw [h2, upd3_get1 hbc]
      cases y b <;> cases y a <;> cases y c <;> rfl
    · by_cases h3 : r = a
      · rw [h3, upd3_get0 hab hac]
      · simp only [upd3, Function.update_of_ne h1, Function.update_of_ne h2,
          Function.update_of_ne h3]

/-- The inverse moving cell on basis states, wire by wire. -/
theorem jPerm_inv_wire (a b c : Fin N) (hab : a ≠ b) (hcb : c ≠ b) (hac : a ≠ c) (y : St N)
    (j : ℕ) :
    wire ((jPerm a b c hab hcb)⁻¹ y) j
      = if j = c.val then xor (y b) (y a && y c) else if j = b.val then y c
        else wire y j := by
  rw [jPerm_inv_apply a b c hab hcb hac, wire_upd3]
  by_cases h1 : j = c.val
  · rw [if_pos h1, if_pos h1]
  · by_cases h2 : j = b.val
    · rw [if_neg h1, if_neg h1, if_pos h2, if_pos h2]
    · rw [if_neg h1, if_neg h1, if_neg h2, if_neg h2]
      by_cases h3 : j = a.val
      · rw [if_pos h3, h3, wire_val]
      · rw [if_neg h3]

/-! ### The cells at a natural-number offset

The moving cell at offset `o` has its control on wire `o + 2`, its middle on `o + 1`
and its target on `o`. -/

/-- The first five gates of the moving cell on wires `o + 2, o + 1, o`. -/
noncomputable def jHalfAt (N o : ℕ) : List (Gate N) :=
  if h : o + 2 < N then
    jHalf ⟨o + 2, h⟩ ⟨o + 1, by omega⟩ ⟨o, by omega⟩ (Or.inr rfl) (Or.inl rfl)
  else []

/-- The last three gates of the moving cell; they touch only wires `o + 1` and `o`. -/
noncomputable def jTailAt (N o : ℕ) : List (Gate N) :=
  if h : o + 2 < N then jTail ⟨o + 1, by omega⟩ ⟨o, by omega⟩ (Or.inl rfl) else []

/-- The basis permutation of the moving cell on wires `o + 2, o + 1, o`. -/
def jPermAt (N o : ℕ) : Equiv.Perm (St N) :=
  if h : o + 2 < N then
    jPerm ⟨o + 2, h⟩ ⟨o + 1, by omega⟩ ⟨o, by omega⟩ (adj_ne (Or.inr rfl)) (adj_ne (Or.inl rfl))
  else 1

theorem cnots_jHalfAt (o : ℕ) (h : o + 2 < N) : cnots (jHalfAt N o) = 3 := by
  rw [jHalfAt, dif_pos h]
  rfl

theorem unitaryGates_jHalfAt (N o : ℕ) : UnitaryGates (jHalfAt N o) := by
  unfold jHalfAt
  split_ifs
  · exact unitaryGates_jHalf _ _ _ _ _
  · exact unitaryGates_nil

theorem unitaryGates_jTailAt (N o : ℕ) : UnitaryGates (jTailAt N o) := by
  unfold jTailAt
  split_ifs
  · exact unitaryGates_jTail _ _ _
  · exact unitaryGates_nil

/-- `jHalfAt o ++ jTailAt o` is the moving cell: a permutation up to phases. -/
theorem umono_jCellAt (N o : ℕ) :
    UMono (circMat (jHalfAt N o ++ jTailAt N o)) (jPermAt N o) := by
  by_cases h : o + 2 < N
  · rw [jHalfAt, dif_pos h, jTailAt, dif_pos h, jPermAt, dif_pos h]
    exact umono_jCell _ _ _ _ _
  · rw [jHalfAt, dif_neg h, jTailAt, dif_neg h, jPermAt, dif_neg h]
    exact umono_nil

/-- `jTailAt o` touches only wires `< o + 2`. -/
theorem below_jTailAt (N o : ℕ) : Below (o + 2) (jTailAt N o) := by
  unfold jTailAt
  split_ifs
  · exact circOn_jTail' _ _ _ _ (by simp) (by simp)
  · exact circOn_nil _

/-- `jHalfAt o` touches only wires `≥ o`. -/
theorem above_jHalfAt (N o : ℕ) : Above o (jHalfAt N o) := by
  unfold jHalfAt
  split_ifs
  · exact circOn_jHalf _ _ _ _ _ _ (by simp) (by simp) (by simp)
  · exact circOn_nil _

/-! ### The core -/

theorem circOn_rtof5 (c1 c2 t : Fin N) (h1 : c1.val + 1 = c2.val ∨ c2.val + 1 = c1.val)
    (h2 : c2.val + 1 = t.val ∨ t.val + 1 = c2.val) (P : Fin N → Prop) (p1 : P c1) (p2 : P c2)
    (pt : P t) : CircOn P (rtof5 c1 c2 t h1 h2) := by
  intro g hg
  simp only [rtof5, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact pt
    | exact ⟨p2, pt⟩
    | exact ⟨p1, p2⟩

/-- The core on wires `o, …, o + 3`: the seven-CNOT cell `gap7` with `q = o + 3`,
`s = o + 2`, `t = o + 1`, `u = o`.  Its basis action is `(o + 2) ^= (o + 3)` and
`o ^= (o + 3) ∧ (o + 1)`.  Seven CNOTs. -/
noncomputable def coreAt (N o : ℕ) : List (Gate N) :=
  if h : o + 3 < N then
    gap7 ⟨o + 3, h⟩ ⟨o + 2, by omega⟩ ⟨o + 1, by omega⟩ ⟨o, by omega⟩ (Or.inr rfl)
      (Or.inr rfl) (Or.inr rfl)
  else []

/-- The basis permutation of the core: the CNOT from `o + 3` to `o + 2` and the Toffoli
with controls `o + 3`, `o + 1` and target `o`. -/
def corePermAt (N o : ℕ) : Equiv.Perm (St N) :=
  if h : o + 3 < N then
    cxPerm ⟨o + 3, h⟩ ⟨o + 2, by omega⟩ (by simp)
      * ccPerm ⟨o + 3, h⟩ ⟨o, by omega⟩ ⟨o + 1, by omega⟩ (by simp) (by simp)
  else 1

theorem cnots_coreAt (o : ℕ) (h : o + 3 < N) : cnots (coreAt N o) = 7 := by
  rw [coreAt, dif_pos h]
  rfl

theorem unitaryGates_coreAt (N o : ℕ) : UnitaryGates (coreAt N o) := by
  unfold coreAt
  split_ifs
  · exact unitaryGates_gap7 _ _ _ _ _ _ _
  · exact unitaryGates_nil

theorem umono_coreAt (N o : ℕ) : UMono (circMat (coreAt N o)) (corePermAt N o) := by
  by_cases h : o + 3 < N
  · rw [coreAt, dif_pos h, corePermAt, dif_pos h]
    exact umono_gap7 _ _ _ _ _ _ _ (by simp) (by simp) (by simp)
  · rw [coreAt, dif_neg h, corePermAt, dif_neg h]
    exact umono_nil

theorem above_coreAt (N o : ℕ) : Above o (coreAt N o) := by
  unfold coreAt
  split_ifs
  · exact circOn_gap7 _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp)
  · exact circOn_nil _

/-! ### The nested circuit -/

/-- `nest o n`: the core at offset `o + 2 n`, conjugated by the half cells at offsets
`o + 2 n - 2, …, o + 2, o` (innermost first). -/
noncomputable def nest (N : ℕ) : ℕ → ℕ → List (Gate N)
  | o, 0 => coreAt N o
  | o, n + 1 => jHalfAt N o ++ nest N (o + 2) n ++ invCirc (jHalfAt N o)

/-- The basis permutation of `nest`: the core conjugated by the moving cells. -/
def nestPerm (N : ℕ) : ℕ → ℕ → Equiv.Perm (St N)
  | o, 0 => corePermAt N o
  | o, n + 1 => (jPermAt N o)⁻¹ * (nestPerm N (o + 2) n * jPermAt N o)

/-- The half cells at offsets `o, o + 2, …, o + 2 n - 2`, in this order. -/
noncomputable def halvesAt (N : ℕ) : ℕ → ℕ → List (Gate N)
  | _, 0 => []
  | o, n + 1 => jHalfAt N o ++ halvesAt N (o + 2) n

theorem halves_core_eq_nest (N o n : ℕ) :
    halvesAt N o n ++ coreAt N (o + 2 * n) ++ invCirc (halvesAt N o n) = nest N o n := by
  induction n generalizing o with
  | zero => simp [halvesAt, nest, invCirc_nil]
  | succ n ih =>
    have e : o + 2 * (n + 1) = o + 2 + 2 * n := by ring
    simp only [halvesAt, nest, invCirc_append, e, ← ih (o + 2), List.append_assoc]

theorem above_nest (N o n : ℕ) : Above o (nest N o n) := by
  induction n generalizing o with
  | zero => exact above_coreAt N o
  | succ n ih =>
    refine circOn_append.2 ⟨circOn_append.2 ⟨above_jHalfAt N o, ?_⟩,
      circOn_invCirc (above_jHalfAt N o)⟩
    exact (ih (o + 2)).mono (fun r (hr : o + 2 ≤ r.val) => show o ≤ r.val by omega)

theorem unitaryGates_nest (N o n : ℕ) : UnitaryGates (nest N o n) := by
  induction n generalizing o with
  | zero => exact unitaryGates_coreAt N o
  | succ n ih =>
    exact unitaryGates_append (unitaryGates_append (unitaryGates_jHalfAt N o) (ih (o + 2)))
      (unitaryGates_invCirc (unitaryGates_jHalfAt N o))

theorem cnots_nest (o n : ℕ) (h : o + 2 * n + 3 < N) : cnots (nest N o n) = 6 * n + 7 := by
  induction n generalizing o with
  | zero => exact cnots_coreAt o (by omega)
  | succ n ih =>
    change cnots (jHalfAt N o ++ nest N (o + 2) n ++ invCirc (jHalfAt N o)) = _
    rw [cnots_append, cnots_append, cnots_invCirc, cnots_jHalfAt o (by omega),
      ih (o + 2) (by omega)]
    ring

/-- **The nested circuit is a permutation up to phases.**  Each pair of half cells is
replaced by a pair of full moving cells: the missing tail commutes with the inner
circuit and cancels against its inverse. -/
theorem umono_nest (N o n : ℕ) : UMono (circMat (nest N o n)) (nestPerm N o n) := by
  induction n generalizing o with
  | zero => exact umono_coreAt N o
  | succ n ih =>
    change UMono (circMat (jHalfAt N o ++ nest N (o + 2) n ++ invCirc (jHalfAt N o)))
      ((jPermAt N o)⁻¹ * (nestPerm N (o + 2) n * jPermAt N o))
    rw [circMat_conj_append (t := jTailAt N o) (unitaryGates_jTailAt N o)
      (circMat_comm_below_above (o + 2) (below_jTailAt N o) (above_nest N (o + 2) n))]
    exact umono_conj (umono_jCellAt N o) (ih (o + 2))

end Line
