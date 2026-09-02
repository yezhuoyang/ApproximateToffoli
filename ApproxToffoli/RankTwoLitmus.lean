import ApproxToffoli.BlockClean
import ApproxToffoli.HSObstruct

/-!
# The rank-two litmus: `HS2` is FALSE for a rank-two reflection

`BlockU.HS2` — and its cleaner equivalents `BlockClean.HS2clean`, `HSObstruct.HSCtrl`,
`BlockFree.HSFree` — all bound `‖trC X‖²_HS` by `8 + 4√2` for a word built around the
`CCZ` reflection `1 - 2Π` with `Π` of **rank one**.  This file proves that the same
statement with a **rank-two** projection is false, with an explicit witness.

## Why this matters

The numerics (`notes/lemmas.md`, iter 1081 / 1081b, and `PyScript/refl/step4_rank_litmus.py`)
give, for `Z_r = 1 - 2(Π_AB ⊗ |1⟩⟨1|_C)` with `Π_AB` of rank `r`:

| `r` | `max ‖trC X‖²_HS` | `max ‖trC X‖_*` |
| --- | --- | --- |
| 1 (`= HS2`) | `8 + 4√2 = 13.657` | `8cos(π/8) = 7.391` |
| **2** | **`16` (ceiling)** | **`8` (ceiling)** |
| 3 | `8 + 4√2` | `8cos(π/8)` |

so the truth is **non-monotone in `r`**.  Consequently:

> **Any bound whose only use of the reflection is a property shared by all ranks —
> `P = P² = Pᴴ`, `1 - 2P` a self-adjoint unitary, `‖P‖_op = 1`, or any estimate monotone
> in `rank P` — is `≥ 16`, and therefore cannot prove `HS2`.  The only usable input is
> minimality, `rank P = 1`.**

`hs2clean_rank2_false` and `hsFree_rank2_false` below turn that from a numerical observation
into two theorems, so a candidate argument can be checked against them mechanically: if the
argument never uses `trace Q = 1` in a way that fails at `trace Q = 2`, it proves a false
statement too.  The two cover the two forms a proof attempt is likely to target —
`BlockClean.HS2clean` (four `Mat4` parameters, rank-one projection of the `AB` factor) and
`BlockFree.HSFree` (three `Mat4` parameters, rank-one projection of `C^8`, `M₀` eliminated;
recall `BlockFree.HS2_of_HSFree : HSFree → BlockU.HS2`).

Two further theorems cover the other two load-bearing hypotheses in iter 1080's table, each
catching a **disjoint** class of wrong arguments (both witnesses keep `rank P = 1`, so they
are independent of the rank litmus):

* `hsFree_nonlocal_W2_false` — relaxing the outer gate `embedBC W₂` to an arbitrary element
  of `U(8)` is false;
* `hsCtrl_free_branches_false` — letting the two `C`-branches of the controlled form be
  independent unitaries is false.

> **Together: a proof of `HSFree` / `HSCtrl` must use ALL THREE of `rank P = 1`, the
> `A`-triviality of `W₂`, and the fact that the two `C`-branches differ by that reflection.
> An argument missing any one of the three is refuted by the corresponding theorem.**

## The witness

At rank two the projection may be taken to be `1_A ⊗ |1⟩⟨1|_B`, and then the reflection
degenerates to a **neighbour** two-body gate,

`1 - 2(1_A ⊗ |1⟩⟨1|_B ⊗ |1⟩⟨1|_C) = CZ_BC = embedBC czBC`,

which is a legal `BC` crossing and is therefore cancelled by a single further `BC` gate.
Taking `G = W₁ = 1` and `W₂ = czBC` makes the whole word the identity, whose partial trace
`2 · 1₄` has `‖·‖²_HS = 16 > 8 + 4√2`.

(A second, less degenerate witness — `Π_AB = |1⟩⟨1|_A ⊗ 1_B`, which makes the reflection the
*non-adjacent* `CZ_AC`, routed to `CZ_AB ⊗ 1_C` by one `SWAP_BC` — is verified numerically to
`0.0` in `PyScript/refl/step5_rank2_witness.py`.  It gives the same ceiling `16` and shows the
phenomenon is not an artefact of the degenerate choice below.  It is not formalised here
because the conjugation costs a 64-case `Fin 8` expansion, whereas the witness below stays
inside `Fin 4`.)

See `notes/OPEN_PROBLEM.md` §7.48 for the surrounding discussion.
-/

open Matrix Complex

namespace RankTwoLitmus

/-- `1_A ⊗ |1⟩⟨1|_B`: a **rank-two** projection of the `AB` factor. -/
def qBC : Mat4 := kron2 1 proj1

/-- `CZ` on the **neighbour** pair `B,C`. -/
def czBC : Mat4 := 1 - kron2 proj1 proj1 - kron2 proj1 proj1

/-- Rank-two analogue of `BlockClean.IsRank1Proj4`. -/
def IsRank2Proj4 (Q : Mat4) : Prop := Qᴴ = Q ∧ Q * Q = Q ∧ Matrix.trace Q = 2

lemma qBC_rank2 : IsRank2Proj4 qBC := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [qBC, kron2, proj1, Matrix.conjTranspose_apply, Matrix.of_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [qBC, kron2, proj1, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply]
  · simp [qBC, kron2, proj1, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_four,
      Matrix.of_apply]
    norm_num

lemma czBC_sq : czBC * czBC = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [czBC, kron2, proj1, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.one_apply, Matrix.of_apply, Matrix.sub_apply]

lemma czBC_unitary : IsUnitary4 czBC := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [czBC, kron2, proj1, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.of_apply, Matrix.sub_apply]

lemma one_unitary4 : IsUnitary4 (1 : Mat4) := by simp [IsUnitary4]

lemma embedBC_sub (V W : Mat4) : embedBC (V - W) = embedBC V - embedBC W := by
  ext i j
  simp only [embedBC, Matrix.of_apply, Matrix.sub_apply]
  split <;> simp

/-- **The rank-two reflection degenerates to the neighbour gate `CZ_BC`.**
    This is the whole content of the counterexample: at rank one the corresponding
    object is `CCZ`, a genuine three-body gate. -/
lemma refl_eq_embedBC :
    (1 : Mat8) - kronABC qBC proj1 - kronABC qBC proj1 = embedBC czBC := by
  have h : kronABC qBC proj1 = embedBC (kron2 proj1 proj1) := by
    rw [embedBC_kron2, singleQubitLayer_eq_kronABC]; rfl
  rw [h, czBC, embedBC_sub, embedBC_sub, embedBC_one]

/-- With `G = W₁ = 1` and `W₂ = czBC` the whole word collapses to the identity. -/
lemma witness_eq :
    embedBC czBC * kronABC (1 : Mat4) 1 *
      ((1 : Mat8) - kronABC qBC proj1 - kronABC qBC proj1) * embedBC 1 = 1 := by
  rw [refl_eq_embedBC, embedBC_one, kronABC_one, Matrix.mul_one, Matrix.mul_one,
    embedBC_mul, czBC_sq, embedBC_one]

lemma trC_one : BlockU.trC (1 : Mat8) = Matrix.of !![2,0,0,0; 0,2,0,0; 0,0,2,0; 0,0,0,2] := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [BlockU.trC, Matrix.one_apply, Matrix.of_apply] <;> norm_num

/-- `‖2 · 1₄‖²_HS = 16 > 8 + 4√2`. -/
lemma sixteen_not_small : ¬ BlockU.HSSmall (BlockU.trC (1 : Mat8)) := by
  have hv : RCLike.re (Matrix.trace ((BlockU.trC (1:Mat8))ᴴ * BlockU.trC (1:Mat8))) = 16 := by
    rw [trC_one]
    simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.conjTranspose_apply, Matrix.of_apply]
    norm_num
  rw [BlockU.HSSmall, hv]
  have h2 : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]
  linarith

/-- **The rank-TWO analogue of `HS2` is FALSE.**

    Compare `BlockClean.HS2clean`, which is the same statement with `IsRank1Proj4 Q`
    in place of `IsRank2Proj4 Q` and is believed true and exactly tight.  So no proof of
    `HS2clean` can avoid using `trace Q = 1`: any argument that goes through verbatim for
    `trace Q = 2` proves this false statement as well. -/
theorem hs2clean_rank2_false :
    ¬ (∀ (G W1 W2 Q : Mat4), IsUnitary4 G → IsUnitary4 W1 → IsUnitary4 W2 →
        IsRank2Proj4 Q →
        BlockU.HSSmall (BlockU.trC (embedBC W2 * kronABC G 1 *
          ((1 : Mat8) - kronABC Q proj1 - kronABC Q proj1) * embedBC W1))) := by
  intro h
  have hw := h 1 1 czBC qBC one_unitary4 one_unitary4 czBC_unitary qBC_rank2
  rw [witness_eq] at hw
  exact sixteen_not_small hw

/-! ## The same litmus for `BlockFree.HSFree`

`HSFree` is the cleanest form of the open problem — three unitaries and one rank-one
projection of `C^8`, with `M₀` eliminated — so it is the form a proof attempt is most likely
to target.  The litmus applies there verbatim, with the rank-two projection
`1_A ⊗ |11⟩⟨11|_BC`, which is again just `CZ_BC` in disguise. -/

/-- `1_A ⊗ |11⟩⟨11|_BC`: a **rank-two** projection of `C^8`. -/
def pBC : Mat8 := embedBC (kron2 proj1 proj1)

/-- Rank-two analogue of `BlockFree.IsRank1Proj`. -/
def IsRank2Proj (P : Mat8) : Prop := Pᴴ = P ∧ P * P = P ∧ Matrix.trace P = 2

lemma proj1_sq : proj1 * proj1 = proj1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [proj1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]

lemma kron2_pp_herm : (kron2 proj1 proj1)ᴴ = kron2 proj1 proj1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [kron2, proj1, Matrix.conjTranspose_apply, Matrix.of_apply]

lemma pBC_rank2 : IsRank2Proj pBC := by
  refine ⟨?_, ?_, ?_⟩
  · rw [pBC, embedBC_conjTranspose, kron2_pp_herm]
  · rw [pBC, embedBC_mul, kron2_mul, proj1_sq]
  · simp [pBC, embedBC, kron2, proj1, Matrix.trace, Matrix.diag_apply,
      Fin.sum_univ_eight, Matrix.of_apply]
    norm_num

lemma refl_pBC : (1 : Mat8) - pBC - pBC = embedBC czBC := by
  rw [pBC, czBC, embedBC_sub, embedBC_sub, embedBC_one]

lemma witnessFree_eq :
    embedBC czBC * kronABC (1 : Mat4) 1 * embedBC 1 * ((1 : Mat8) - pBC - pBC) = 1 := by
  rw [refl_pBC, embedBC_one, kronABC_one, Matrix.mul_one, Matrix.mul_one,
    embedBC_mul, czBC_sq, embedBC_one]

/-- **The rank-TWO analogue of `BlockFree.HSFree` is FALSE.**

    Compare `BlockFree.HSFree`, which carries `IsRank1Proj P` and is believed true and
    exactly tight.  Since `BlockFree.HS2_of_HSFree : HSFree → BlockU.HS2`, `HSFree` is the
    natural target; this says any proof of it must use `trace P = 1`. -/
theorem hsFree_rank2_false :
    ¬ (∀ (Z0 W1 W2 : Mat4) (P : Mat8), IsUnitary4 Z0 → IsUnitary4 W1 → IsUnitary4 W2 →
        IsRank2Proj P →
        BlockU.HSSmall (BlockU.trC (embedBC W2 * kronABC Z0 1 * embedBC W1 * (1 - P - P)))) := by
  intro h
  have hw := h 1 1 czBC pBC one_unitary4 one_unitary4 czBC_unitary pBC_rank2
  rw [witnessFree_eq] at hw
  exact sixteen_not_small hw

/-! ## A complementary litmus: the LOCALITY of the outer gate is load-bearing

The rank litmus catches arguments that ignore `rank P = 1`.  `notes/lemmas.md` iter 1080
records a second load-bearing hypothesis in the same table — "`W2` relaxed to `U(8)` → 16
← A-triviality of `W2` is essential" — and it catches a disjoint class of wrong arguments:
those that use only `W₂ᴴW₂ = 1` and never that `W₂` acts trivially on `A`.

Here the witness is even simpler, and it is a genuine **rank-one** one, so the two litmus
tests are independent: taking the outer gate to be `CCZ8` itself lets it cancel the
reflection, because `CCZ8 = 1 - 2E₇₇` is *itself* a reflection about a rank-one projection.

Together the two say: a proof of `HSFree` must use **both** minimality of `P` **and** the
`A`-triviality of `W₂`.  An argument using only one of them is refuted by the other. -/

/-- **`HSFree` with the outer `BC` gate relaxed to an arbitrary element of `U(8)` is FALSE.**

    This is a genuine relaxation of `BlockFree.HSFree`: `embedBC_unitary` says every
    `embedBC W₂` with `W₂` unitary satisfies the hypothesis `U₂ᴴ * U₂ = 1` used here, so the
    statement below is implied by (a suitably re-typed) `HSFree`.  It is nonetheless false,
    with `Z₀ = W₁ = 1`, `U₂ = CCZ8` and `P = E₇₇`: since `CCZ8 = 1 - E₇₇ - E₇₇` is itself the
    reflection about `P`, the word is `CCZ8 * CCZ8 = 1`, whose partial trace `2·1₄` has
    `‖·‖²_HS = 16 > 8 + 4√2`.  Note `P` here has rank ONE, so this refutation is independent
    of the rank litmus above. -/
theorem hsFree_nonlocal_W2_false :
    ¬ (∀ (Z0 W1 : Mat4) (U2 P : Mat8), IsUnitary4 Z0 → IsUnitary4 W1 → U2ᴴ * U2 = 1 →
        BlockFree.IsRank1Proj P →
        BlockU.HSSmall (BlockU.trC (U2 * kronABC Z0 1 * embedBC W1 * (1 - P - P)))) := by
  intro h
  have hE : BlockFree.IsRank1Proj BlockFree.E77 :=
    ⟨BlockFree.E77_conjTranspose, BlockFree.E77_mul_self, BlockFree.E77_trace⟩
  have hU : CCZ8ᴴ * CCZ8 = 1 := by rw [ccz8_conjTranspose]; exact ccz8_mul_self
  have hw := h 1 1 CCZ8 BlockFree.E77 one_unitary4 one_unitary4 hU hE
  rw [kronABC_one, embedBC_one, Matrix.mul_one, Matrix.mul_one,
    ← BlockFree.ccz8_eq_refl, ccz8_mul_self] at hw
  exact sixteen_not_small hw

/-! ## A third litmus: the two `C`-branches must be LINKED

`HSCtrlForm.HSCtrl` writes the middle of the word in controlled form,
`kronABC G proj0 + kronABC (G * (1 - P - P)) proj1` — the two `C`-branches are `G` and
`G(1-2P)`, which differ by a rank-one reflection.  iter 1080's table has the corresponding
row, "`Z0, Z1` independent unitaries → 16".

This catches a third disjoint class of wrong arguments: those that use only "each branch is
unitary" and never that the two branches are *related*.  The witness is as degenerate as
possible — take the branches EQUAL, `Z₀ = Z₁ = 1` — because then the controlled gate collapses
to `kronABC 1 (proj0 + proj1) = 1`, which is exactly what `G` vs `G(1-2P)` can never do. -/

lemma kronABC_add_right (M : Mat4) (c d : Mat2) :
    kronABC M c + kronABC M d = kronABC M (c + d) := by
  ext i j
  simp [kronABC, Matrix.add_apply, Matrix.of_apply, mul_add]

lemma proj0_add_proj1 : (proj0 : Mat2) + proj1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj0, proj1, Matrix.of_apply]

/-- **`HSCtrl` with the two `C`-branches taken INDEPENDENT is FALSE.**

    Compare `HSCtrlForm.HSCtrl`, where the branches are `G` and `G * (1 - P - P)` with `P` a
    rank-one projection.  Since `1 - P - P ≠ 1`, the branches there always differ; the
    relaxation below permits `Z₀ = Z₁`, and that alone reaches the ceiling `16`. -/
theorem hsCtrl_free_branches_false :
    ¬ (∀ (Z0 Z1 W1 W2 : Mat4), IsUnitary4 Z0 → IsUnitary4 Z1 → IsUnitary4 W1 → IsUnitary4 W2 →
        BlockU.HSSmall (BlockU.trC (embedBC W2 *
          (kronABC Z0 proj0 + kronABC Z1 proj1) * embedBC W1))) := by
  intro h
  have hw := h 1 1 1 1 one_unitary4 one_unitary4 one_unitary4 one_unitary4
  rw [kronABC_add_right, proj0_add_proj1, kronABC_one, embedBC_one,
    Matrix.mul_one, Matrix.one_mul] at hw
  exact sixteen_not_small hw

end RankTwoLitmus
