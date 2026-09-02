/-
  ApproxToffoli.HP.Main
  Main result: The Toffoli gate (CCX) requires exactly 6 neighbor gates.

  This file combines:
  1. CCZ ∉ S₄ ∪ S₅ (from HP.Defs)
  2. 5 neighbor gates → S₄ ∪ S₅ for diagonal gates (from HP.SetChar)
  3. CCX ~ CCZ up to single-qubit gates (free)

  Reference: Huang & Palsberg (2026), Corollary 7.3.
-/

import ApproxToffoli.HP.SetChar
import ApproxToffoli.HP.SixGate
-- for R1 (`ccx_eq_ccz_conj`), `Hgate` and `h8_mul_self`: the CCZ → CCX transfer.
-- No cycle: the cut chain's import closure never reaches `ApproxToffoli.HP`.
import ApproxToffoli.CutAlgebra

open Matrix Complex

noncomputable section

/-! ## CCZ is a diagonal gate -/

/-- CCZ as a Mat8 diagonal matrix -/
def CCZ_matrix : Mat8 := CCZ_diag.toMatrix

/-! ## CCZ cannot be implemented with 5 neighbor gates

The key argument:
1. Suppose CCZ = NeighborCircuit 5.
2. By five_neighbor_implies_S4_or_S5, CCZ_diag ∈ S₄ ∪ S₅.
3. But CCZ_not_inS4_or_S5 says CCZ_diag ∉ S₄ ∪ S₅.
4. Contradiction.
-/

/-- CCZ cannot be implemented with 5 or fewer neighbor gates.

    Iter 1043: stated over `UnitaryNeighborCircuit` — i.e. 2-qubit gates that
    are actually unitary, which is what the paper means and what makes the
    statement physically meaningful. The non-unitary `NeighborCircuit` version
    was retired because the paper's spectral arguments (Lemmas 4.4, C.1) need
    gate unitarity and no forgetful lift can supply it. -/
theorem CCZ_not_five_neighbor :
    ¬ UnitaryNeighborCircuit 5 CCZ_matrix := by
  intro h5
  have hS := five_unitaryNeighbor_implies_S4_or_S5 CCZ_diag h5
  exact CCZ_not_inS4_or_S5 hS

/-- CCZ requires exactly 6 neighbor gates:
    - 6 gates suffice (by `ccz_six_neighbor` from HP/SixGate.lean — specific
      CCZ construction; the general `six_neighbor_suffice` is NOT on the
      critical path for this main theorem).
    - 5 gates do not suffice (by `CCZ_not_five_neighbor`).

    **Remaining sorries: NONE.** This docstring previously listed three
    (`unrestrictedCircuit_4_canonical`, the `five_neighbor_to_four_unrestricted`
    V₃ trichotomy cases, and `six_neighbor_suffice`); all were resolved by iter 1046 —
    two of them RETIRED in iter 1043 as not provable over the non-unitary
    `NeighborCircuit`, which is why this theorem is stated over
    `UnitaryNeighborCircuit`. `#print axioms` on this declaration returns exactly
    `[propext, Classical.choice, Quot.sound]`. -/
theorem CCZ_requires_six_neighbor :
    UnitaryNeighborCircuit 6 CCZ_matrix ∧ ¬ UnitaryNeighborCircuit 5 CCZ_matrix :=
  ⟨ccz_six_unitaryNeighbor, CCZ_not_five_neighbor⟩

/-! ## Extension to CCX (Toffoli gate)

`CCX = (I ⊗ I ⊗ H) · CCZ · (I ⊗ I ⊗ H)`, and single-qubit layers are free in the
neighbor-circuit model, so CCX and CCZ have the same neighbor-gate complexity.

**Iter 1059: this is now PROVED, not asserted.** Until then this section said "For now,
we state the result directly" and `CCX_requires_six_neighbor_gates` was literally
`CCZ_not_five_neighbor` renamed — its statement mentioned `CCZ_matrix`, not `CCX`, so
the name promised more than the statement delivered. The three ingredients the old
comment listed as missing all exist now:

* the Hadamard gate and **R1** `ccx_eq_ccz_conj` (`CutAlgebra.lean`, iter 1054);
* `unitaryNeighborCircuit_mul_product` (right layers, `FiveToFour.lean`) and
  `unitaryNeighborCircuit_product_mul` (left layers, below).

Everything below is about `CCX` itself. -/

/-- `CCZ_matrix` (a `DiagGate3`) and `CCZ8` (a literal diagonal matrix) agree. -/
lemma cczMatrix_eq_ccz8 : CCZ_matrix = CCZ8 := by
  have hd : CCZ_diag.d = ![1, 1, 1, 1, 1, 1, 1, -1] := by
    funext i; fin_cases i <;> simp
  rw [CCZ_matrix, DiagGate3.toMatrix, hd, CCZ8]

/-- Left multiplication by a product layer is free, the mirror of
    `unitaryNeighborCircuit_mul_product`. As there, the `∀ dA dB dC` must be INSIDE the
    induction, or the `compose_*` cases cannot apply the hypothesis to `rest`. -/
theorem unitaryNeighborCircuit_product_mul {n : ℕ} {U : Mat8}
    (h : UnitaryNeighborCircuit n U) :
    ∀ (dA dB dC : Mat2), IsUnitary2 dA → IsUnitary2 dB → IsUnitary2 dC →
      UnitaryNeighborCircuit n (singleQubitLayer dA dB dC * U) := by
  induction h with
  | product uA uB uC hA hB hC =>
    intro dA dB dC hdA hdB hdC
    rw [singleQubitLayer_mul]
    exact .product _ _ _ (isUnitary2_mul hdA hA) (isUnitary2_mul hdB hB)
      (isUnitary2_mul hdC hC)
  | weaken _ ih => intro dA dB dC hdA hdB hdC; exact .weaken (ih dA dB dC hdA hdB hdC)
  | @compose_AB _ rest V hV uA uB uC hA hB hC hrest ih =>
    intro dA dB dC hdA hdB hdC
    rw [show singleQubitLayer dA dB dC * (rest * embedAB V * singleQubitLayer uA uB uC)
        = (singleQubitLayer dA dB dC * rest) * embedAB V * singleQubitLayer uA uB uC by
      noncomm_ring]
    exact .compose_AB V hV _ _ _ hA hB hC (ih dA dB dC hdA hdB hdC)
  | @compose_BC _ rest V hV uA uB uC hA hB hC hrest ih =>
    intro dA dB dC hdA hdB hdC
    rw [show singleQubitLayer dA dB dC * (rest * embedBC V * singleQubitLayer uA uB uC)
        = (singleQubitLayer dA dB dC * rest) * embedBC V * singleQubitLayer uA uB uC by
      noncomm_ring]
    exact .compose_BC V hV _ _ _ hA hB hC (ih dA dB dC hdA hdB hdC)

/-- **R1 in circuit form.** Conjugating by the free layer `H_C` turns `CCX` into `CCZ`. -/
lemma hC_conj_ccx :
    singleQubitLayer 1 1 Hgate * CCX * singleQubitLayer 1 1 Hgate = CCZ_matrix := by
  rw [cczMatrix_eq_ccz8]
  change kron3 1 1 Hgate * CCX * kron3 1 1 Hgate = CCZ8
  rw [ccx_eq_ccz_conj]
  calc kron3 1 1 Hgate * (kron3 1 1 Hgate * CCZ8 * kron3 1 1 Hgate) * kron3 1 1 Hgate
      = (kron3 1 1 Hgate * kron3 1 1 Hgate) * CCZ8
        * (kron3 1 1 Hgate * kron3 1 1 Hgate) := by noncomm_ring
    _ = CCZ8 := by rw [h8_mul_self, Matrix.one_mul, Matrix.mul_one]

/-- …and back. -/
lemma hC_conj_ccz :
    singleQubitLayer 1 1 Hgate * CCZ_matrix * singleQubitLayer 1 1 Hgate = CCX := by
  rw [cczMatrix_eq_ccz8]
  change kron3 1 1 Hgate * CCZ8 * kron3 1 1 Hgate = CCX
  rw [ccx_eq_ccz_conj]

/-- Conjugation by `H_C` preserves the neighbor-gate count. -/
private lemma unc_conj_hC {n : ℕ} {U : Mat8} (h : UnitaryNeighborCircuit n U) :
    UnitaryNeighborCircuit n
      (singleQubitLayer 1 1 Hgate * U * singleQubitLayer 1 1 Hgate) :=
  unitaryNeighborCircuit_mul_product
    (unitaryNeighborCircuit_product_mul h 1 1 Hgate isUnitary2_one isUnitary2_one
      hgate_unitary) 1 1 Hgate isUnitary2_one isUnitary2_one hgate_unitary

/-- **The Toffoli gate cannot be built from five neighbor gates.** A statement about
    `CCX` itself, not about `CCZ`. -/
theorem CCX_not_five_neighbor : ¬ UnitaryNeighborCircuit 5 CCX := fun h =>
  CCZ_not_five_neighbor (hC_conj_ccx ▸ unc_conj_hC h)

/-- **Toffoli requires exactly six quantum neighbor gates** — the paper's title result,
    stated about `CCX`: six suffice, five do not. -/
theorem CCX_requires_six_neighbor :
    UnitaryNeighborCircuit 6 CCX ∧ ¬ UnitaryNeighborCircuit 5 CCX :=
  ⟨hC_conj_ccz ▸ unc_conj_hC ccz_six_unitaryNeighbor, CCX_not_five_neighbor⟩

/-- Retained under its historical name; it is now genuinely about `CCX`. -/
theorem CCX_requires_six_neighbor_gates : ¬ UnitaryNeighborCircuit 5 CCX :=
  CCX_not_five_neighbor

end
