/-
  ApproxToffoli.BlockRoute
  The RUN / BLOCK reduction: the bridge between the CNOT-counting half of this
  repository (`AchievableCircuit`) and the Huang-Palsberg neighbour-gate half
  (`UnitaryNeighborCircuit`, `ApproxToffoli/HP/`).

  Contents
  --------
  1. Every allowed CNOT is a *unitary* 2-qubit neighbour gate
     (`cnotFwd4`, `cnotRev4` and the four `embed*` identities).
  2. `CXWord w U` — an `AchievableCircuit` refined by the WORD `w : List Bool`
     of pair labels it uses (`false` = AB, `true` = BC).  No `weaken`, so
     `w.length` is the exact CNOT count.
  3. `runs w` — the number of maximal constant blocks of `w`.
  4. **`cxWord_run_form`** : `CXWord w U → UnitaryNeighborCircuit (runs w) U`.
     A whole RUN of consecutive CNOTs on one pair, with all its interleaved
     free single-qubit layers, costs ONE neighbour gate.
  5. `unitaryNeighborCircuit_of_achievable` : the crude bridge `n ↦ n`.
  6. `achievable_five_not_CCX` : an immediate new consequence — five CNOTs on
     the line A–B–C cannot realise the Toffoli gate EXACTLY.  (Quantitatively
     this is far weaker than `approxToffoli_lower_bound`; it is recorded
     because it is the first result flowing from HP to the CNOT side.)
  7. `PhiSqBound` — the quantitative object `Phi(k)`, and the statement
     `PhiFive` of the missing lemma `Phi(5) ≤ 8 cos(π/8)`, together with the
     consequences that would follow from it at n = 5, 6, 7.
-/

import ApproxToffoli.HP.Main
import ApproxToffoli.CutMain

open Matrix Complex

noncomputable section

namespace Block

/-! ## 1. The four allowed CNOTs are unitary neighbour gates -/

/-- CNOT on a pair with the FIRST wire of the pair as control: `0→0, 1→1, 2→3, 3→2`. -/
def cnotFwd4 : Mat4 :=
  Matrix.of fun (i j : Fin 4) =>
    match i, j with
    | 0, 0 => (1 : ℂ) | 1, 1 => 1 | 2, 3 => 1 | 3, 2 => 1 | _, _ => 0

/-- CNOT on a pair with the SECOND wire of the pair as control: `0→0, 1→3, 2→2, 3→1`. -/
def cnotRev4 : Mat4 :=
  Matrix.of fun (i j : Fin 4) =>
    match i, j with
    | 0, 0 => (1 : ℂ) | 1, 3 => 1 | 2, 2 => 1 | 3, 1 => 1 | _, _ => 0

set_option maxHeartbeats 1600000 in
-- 16-case `fin_cases × fin_cases` over `Fin 4` with `Fin.sum_univ_four`.
theorem cnotFwd4_unitary : IsUnitary4 cnotFwd4 := by
  unfold IsUnitary4
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cnotFwd4, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four,
      Matrix.of_apply]

set_option maxHeartbeats 1600000 in
-- 16-case `fin_cases × fin_cases` over `Fin 4` with `Fin.sum_univ_four`.
theorem cnotRev4_unitary : IsUnitary4 cnotRev4 := by
  unfold IsUnitary4
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cnotRev4, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four,
      Matrix.of_apply]

set_option maxHeartbeats 1600000 in
-- 64-case `fin_cases × fin_cases` over `Fin 8`.
theorem embedAB_cnotFwd4 : embedAB cnotFwd4 = CX_AB := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedAB, cnotFwd4, CX_AB, kron3, proj0, proj1, pauliX, I₂, decode3,
      Matrix.of_apply, Matrix.add_apply, Matrix.one_apply]

set_option maxHeartbeats 1600000 in
-- 64-case `fin_cases × fin_cases` over `Fin 8`.
theorem embedAB_cnotRev4 : embedAB cnotRev4 = CX_BA := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedAB, cnotRev4, CX_BA, kron3, proj0, proj1, pauliX, I₂, decode3,
      Matrix.of_apply, Matrix.add_apply, Matrix.one_apply]

set_option maxHeartbeats 1600000 in
-- 64-case `fin_cases × fin_cases` over `Fin 8`.
theorem embedBC_cnotFwd4 : embedBC cnotFwd4 = CX_BC := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedBC, cnotFwd4, CX_BC, kron3, proj0, proj1, pauliX, I₂, decode3,
      Matrix.of_apply, Matrix.add_apply, Matrix.one_apply]

set_option maxHeartbeats 1600000 in
-- 64-case `fin_cases × fin_cases` over `Fin 8`.
theorem embedBC_cnotRev4 : embedBC cnotRev4 = CX_CB := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedBC, cnotRev4, CX_CB, kron3, proj0, proj1, pauliX, I₂, decode3,
      Matrix.of_apply, Matrix.add_apply, Matrix.one_apply]

theorem exists_embedAB_of_allowedAB {G : Mat8} (hG : G = CX_AB ∨ G = CX_BA) :
    ∃ V : Mat4, IsUnitary4 V ∧ G = embedAB V := by
  rcases hG with rfl | rfl
  · exact ⟨cnotFwd4, cnotFwd4_unitary, embedAB_cnotFwd4.symm⟩
  · exact ⟨cnotRev4, cnotRev4_unitary, embedAB_cnotRev4.symm⟩

theorem exists_embedBC_of_allowedBC {G : Mat8} (hG : G = CX_BC ∨ G = CX_CB) :
    ∃ V : Mat4, IsUnitary4 V ∧ G = embedBC V := by
  rcases hG with rfl | rfl
  · exact ⟨cnotFwd4, cnotFwd4_unitary, embedBC_cnotFwd4.symm⟩
  · exact ⟨cnotRev4, cnotRev4_unitary, embedBC_cnotRev4.symm⟩

/-! ## 2. Word-indexed achievable circuits -/

/-- `CXWord w U`: `U` is built from the CNOT word `w`, read right-to-left
    (`w.head` is the LAST gate applied), with free unitary single-qubit layers.
    `false` labels a gate on the pair AB (either direction), `true` a gate on BC.
    Unlike `AchievableCircuit` there is no `weaken`, so `w.length` is the exact
    number of CNOTs. -/
inductive CXWord : List Bool → Mat8 → Prop where
  | nil (uA uB uC : Mat2) (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC) :
      CXWord [] (singleQubitLayer uA uB uC)
  | consAB {w : List Bool} {rest G : Mat8} (uA uB uC : Mat2)
      (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC)
      (hG : G = CX_AB ∨ G = CX_BA) (hrest : CXWord w rest) :
      CXWord (false :: w) (rest * G * singleQubitLayer uA uB uC)
  | consBC {w : List Bool} {rest G : Mat8} (uA uB uC : Mat2)
      (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC)
      (hG : G = CX_BC ∨ G = CX_CB) (hrest : CXWord w rest) :
      CXWord (true :: w) (rest * G * singleQubitLayer uA uB uC)

/-- Every `AchievableCircuit n` carries a pair-word of length at most `n`. -/
theorem exists_cxWord {n : ℕ} {U : Mat8} (h : AchievableCircuit n U) :
    ∃ w : List Bool, w.length ≤ n ∧ CXWord w U := by
  induction h with
  | single_layer uA uB uC hA hB hC => exact ⟨[], by simp, .nil uA uB uC hA hB hC⟩
  | weaken _ ih => obtain ⟨w, hlen, hw⟩ := ih; exact ⟨w, by omega, hw⟩
  | @compose n G rest uA uB uC hA hB hC hG _ ih =>
    obtain ⟨w, hlen, hw⟩ := ih
    rcases hG with h1 | h1 | h1 | h1
    · exact ⟨false :: w, by simpa using hlen, .consAB uA uB uC hA hB hC (Or.inl h1) hw⟩
    · exact ⟨false :: w, by simpa using hlen, .consAB uA uB uC hA hB hC (Or.inr h1) hw⟩
    · exact ⟨true :: w, by simpa using hlen, .consBC uA uB uC hA hB hC (Or.inl h1) hw⟩
    · exact ⟨true :: w, by simpa using hlen, .consBC uA uB uC hA hB hC (Or.inr h1) hw⟩

/-! ## 3. Runs -/

/-- The number of maximal runs of equal labels in a word. -/
def runs : List Bool → ℕ
  | [] => 0
  | [_] => 1
  | p :: q :: t => if p = q then runs (q :: t) else runs (q :: t) + 1

theorem runs_nil : runs [] = 0 := rfl

theorem runs_singleton (p : Bool) : runs [p] = 1 := rfl

theorem runs_cons_cons (p q : Bool) (t : List Bool) :
    runs (p :: q :: t) = if p = q then runs (q :: t) else runs (q :: t) + 1 := rfl

theorem runs_pos {w : List Bool} (h : w ≠ []) : 0 < runs w := by
  match w with
  | [] => exact absurd rfl h
  | [_] => simp [runs]
  | p :: q :: t =>
    simp only [runs]
    split
    · exact runs_pos (by simp)
    · omega

theorem runs_le_length (w : List Bool) : runs w ≤ w.length := by
  match w with
  | [] => simp [runs]
  | [_] => simp [runs]
  | p :: q :: t =>
    have ih := runs_le_length (q :: t)
    simp only [runs, List.length_cons]
    split <;> simp only [List.length_cons] at ih ⊢ <;> omega

/-! ## 4. The run/block reduction -/

/-- `NCLast p k U`: `U` is a neighbour-gate circuit whose outermost (last-applied)
    block sits on pair `p` (`false` = AB, `true` = BC) and which uses `k` further
    blocks before it — so `U` costs `k + 1` blocks in total. -/
def NCLast : Bool → ℕ → Mat8 → Prop
  | false, k, U => ∃ (rest : Mat8) (V : Mat4) (uA uB uC : Mat2),
      IsUnitary4 V ∧ IsUnitary2 uA ∧ IsUnitary2 uB ∧ IsUnitary2 uC ∧
      UnitaryNeighborCircuit k rest ∧ U = rest * embedAB V * singleQubitLayer uA uB uC
  | true, k, U => ∃ (rest : Mat8) (V : Mat4) (uA uB uC : Mat2),
      IsUnitary4 V ∧ IsUnitary2 uA ∧ IsUnitary2 uB ∧ IsUnitary2 uC ∧
      UnitaryNeighborCircuit k rest ∧ U = rest * embedBC V * singleQubitLayer uA uB uC

theorem unitaryNeighborCircuit_of_NCLast {p : Bool} {k : ℕ} {U : Mat8}
    (h : NCLast p k U) : UnitaryNeighborCircuit (k + 1) U := by
  cases p with
  | false =>
    obtain ⟨rest, V, uA, uB, uC, hV, hA, hB, hC, hrest, rfl⟩ := h
    exact .compose_AB V hV uA uB uC hA hB hC hrest
  | true =>
    obtain ⟨rest, V, uA, uB, uC, hV, hA, hB, hC, hrest, rfl⟩ := h
    exact .compose_BC V hV uA uB uC hA hB hC hrest

/-- **Run merging, AB side.** Appending one more AB block to a circuit whose last
    block is already AB does NOT increase the block count: the two AB gates and the
    single-qubit layer between them fuse into one AB gate (`embedAB_merge`), the
    left-over C-only layer being absorbed by `unitaryNeighborCircuit_mul_product`. -/
theorem NCLast_merge_AB {k : ℕ} {rest : Mat8} (hrest : NCLast false k rest)
    (V₂ : Mat4) (hV₂ : IsUnitary4 V₂) (uA uB uC : Mat2)
    (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC) :
    NCLast false k (rest * embedAB V₂ * singleQubitLayer uA uB uC) := by
  obtain ⟨rest₀, V₁, uA₁, uB₁, uC₁, hV₁, hA₁, hB₁, hC₁, hrest₀, rfl⟩ := hrest
  refine ⟨rest₀ * singleQubitLayer I₂ I₂ uC₁, V₁ * (kron2 uA₁ uB₁ * V₂), uA, uB, uC,
    isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hB₁) hV₂), hA, hB, hC,
    unitaryNeighborCircuit_mul_product hrest₀ I₂ I₂ uC₁ isUnitary2_one isUnitary2_one hC₁,
    ?_⟩
  have key : rest₀ * embedAB V₁ * singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂
      = (rest₀ * singleQubitLayer I₂ I₂ uC₁) * embedAB (V₁ * (kron2 uA₁ uB₁ * V₂)) := by
    rw [show rest₀ * embedAB V₁ * singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂
        = rest₀ * (embedAB V₁ * singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂) from by
      noncomm_ring, embedAB_merge]
    noncomm_ring
  rw [key]

/-- **Run merging, BC side.** -/
theorem NCLast_merge_BC {k : ℕ} {rest : Mat8} (hrest : NCLast true k rest)
    (V₂ : Mat4) (hV₂ : IsUnitary4 V₂) (uA uB uC : Mat2)
    (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC) :
    NCLast true k (rest * embedBC V₂ * singleQubitLayer uA uB uC) := by
  obtain ⟨rest₀, V₁, uA₁, uB₁, uC₁, hV₁, hA₁, hB₁, hC₁, hrest₀, rfl⟩ := hrest
  refine ⟨rest₀ * singleQubitLayer uA₁ I₂ I₂, V₁ * (kron2 uB₁ uC₁ * V₂), uA, uB, uC,
    isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hB₁ hC₁) hV₂), hA, hB, hC,
    unitaryNeighborCircuit_mul_product hrest₀ uA₁ I₂ I₂ hA₁ isUnitary2_one isUnitary2_one,
    ?_⟩
  have key : rest₀ * embedBC V₁ * singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂
      = (rest₀ * singleQubitLayer uA₁ I₂ I₂) * embedBC (V₁ * (kron2 uB₁ uC₁ * V₂)) := by
    rw [show rest₀ * embedBC V₁ * singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂
        = rest₀ * (embedBC V₁ * singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂) from by
      noncomm_ring, embedBC_merge]
    noncomm_ring
  rw [key]

/-- **THE RUN / BLOCK REDUCTION.**  A CNOT word `w` on the line A–B–C is realised
    by only `runs w` general two-qubit neighbour gates — one per maximal run of
    consecutive CNOTs on the same pair.  The second conjunct is the strengthening
    that makes the induction go through: it records WHICH pair the outermost block
    sits on, so that the next gate can be merged into it when the pair repeats. -/
theorem cxWord_run_form : ∀ {w : List Bool} {U : Mat8}, CXWord w U →
    UnitaryNeighborCircuit (runs w) U ∧
    ∀ (p : Bool) (w' : List Bool) (k : ℕ), w = p :: w' → runs w = k + 1 → NCLast p k U := by
  intro w U h
  induction h with
  | nil uA uB uC hA hB hC =>
    exact ⟨.product uA uB uC hA hB hC, by intro p w' k hw; exact absurd hw (by simp)⟩
  | @consAB w rest G uA uB uC hA hB hC hG hrest ih =>
    obtain ⟨V₂, hV₂, hGV⟩ := exists_embedAB_of_allowedAB hG
    subst hGV
    have main : ∀ k : ℕ, runs (false :: w) = k + 1 → NCLast false k
        (rest * embedAB V₂ * singleQubitLayer uA uB uC) := by
      cases w with
      | nil =>
        intro k hk
        have hk0 : k = 0 := by simpa [runs] using hk.symm
        subst hk0
        exact ⟨rest, V₂, uA, uB, uC, hV₂, hA, hB, hC, ih.1, rfl⟩
      | cons q t =>
        intro k hk
        by_cases hq : (false : Bool) = q
        · subst hq
          rw [runs_cons_cons] at hk
          simp only [if_pos rfl] at hk
          exact NCLast_merge_AB (ih.2 false t k rfl hk) V₂ hV₂ uA uB uC hA hB hC
        · rw [runs_cons_cons, if_neg hq] at hk
          have hk' : runs (q :: t) = k := by omega
          exact ⟨rest, V₂, uA, uB, uC, hV₂, hA, hB, hC, hk' ▸ ih.1, rfl⟩
    obtain ⟨k, hk⟩ : ∃ k, runs (false :: w) = k + 1 :=
      ⟨runs (false :: w) - 1, by have := runs_pos (w := false :: w) (by simp); omega⟩
    refine ⟨?_, ?_⟩
    · rw [hk]; exact unitaryNeighborCircuit_of_NCLast (main k hk)
    · intro p w' k' hw hk'
      obtain ⟨rfl, rfl⟩ : p = false ∧ w' = w := by simpa using hw.symm
      exact main k' hk'
  | @consBC w rest G uA uB uC hA hB hC hG hrest ih =>
    obtain ⟨V₂, hV₂, hGV⟩ := exists_embedBC_of_allowedBC hG
    subst hGV
    have main : ∀ k : ℕ, runs (true :: w) = k + 1 → NCLast true k
        (rest * embedBC V₂ * singleQubitLayer uA uB uC) := by
      cases w with
      | nil =>
        intro k hk
        have hk0 : k = 0 := by simpa [runs] using hk.symm
        subst hk0
        exact ⟨rest, V₂, uA, uB, uC, hV₂, hA, hB, hC, ih.1, rfl⟩
      | cons q t =>
        intro k hk
        by_cases hq : (true : Bool) = q
        · subst hq
          rw [runs_cons_cons] at hk
          simp only [if_pos rfl] at hk
          exact NCLast_merge_BC (ih.2 true t k rfl hk) V₂ hV₂ uA uB uC hA hB hC
        · rw [runs_cons_cons, if_neg hq] at hk
          have hk' : runs (q :: t) = k := by omega
          exact ⟨rest, V₂, uA, uB, uC, hV₂, hA, hB, hC, hk' ▸ ih.1, rfl⟩
    obtain ⟨k, hk⟩ : ∃ k, runs (true :: w) = k + 1 :=
      ⟨runs (true :: w) - 1, by have := runs_pos (w := true :: w) (by simp); omega⟩
    refine ⟨?_, ?_⟩
    · rw [hk]; exact unitaryNeighborCircuit_of_NCLast (main k hk)
    · intro p w' k' hw hk'
      obtain ⟨rfl, rfl⟩ : p = true ∧ w' = w := by simpa using hw.symm
      exact main k' hk'

/-- Block count is monotone. -/
theorem unitaryNeighborCircuit_mono {m n : ℕ} (hmn : m ≤ n) {U : Mat8}
    (h : UnitaryNeighborCircuit m U) : UnitaryNeighborCircuit n U := by
  induction n, hmn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact .weaken ih

/-! ## 5. The bridge -/

/-- **The run/block bridge, packaged.**  Every `AchievableCircuit n` circuit is a
    neighbour-gate circuit with only `runs w ≤ n` gates, `w` its CNOT word. -/
theorem achievable_run_block {n : ℕ} {U : Mat8} (h : AchievableCircuit n U) :
    ∃ w : List Bool, w.length ≤ n ∧ CXWord w U ∧ UnitaryNeighborCircuit (runs w) U := by
  obtain ⟨w, hlen, hw⟩ := exists_cxWord h
  exact ⟨w, hlen, hw, (cxWord_run_form hw).1⟩

/-- **The crude bridge** (`n ↦ n`): `n` CNOTs on the line are in particular `n`
    general two-qubit neighbour gates.  Everything Huang–Palsberg prove about
    `UnitaryNeighborCircuit` now applies to `AchievableCircuit`. -/
theorem unitaryNeighborCircuit_of_achievable {n : ℕ} {U : Mat8}
    (h : AchievableCircuit n U) : UnitaryNeighborCircuit n U := by
  obtain ⟨w, hlen, _, hnc⟩ := achievable_run_block h
  exact unitaryNeighborCircuit_mono (le_trans (runs_le_length w) hlen) hnc

/-! ## 6. First consequence: five CNOTs cannot realise Toffoli exactly -/

/-- **New.**  Five CNOTs on the line A–B–C (with unlimited single-qubit gates)
    cannot implement the Toffoli gate exactly.  Immediate from Huang–Palsberg's
    `CCX_not_five_neighbor` through the bridge.  (This is qualitative; the
    quantitative statement `hsDistance U CCX ≥ sin(π/8)` is
    `approxToffoli_lower_bound`, proved by the independent cut route.) -/
theorem achievable_five_not_CCX : ¬ AchievableCircuit 5 CCX := fun h =>
  CCX_not_five_neighbor (unitaryNeighborCircuit_of_achievable h)

/-- …and hence for any budget below 6. -/
theorem achievable_not_CCX_of_le_five {n : ℕ} (hn : n ≤ 5) : ¬ AchievableCircuit n CCX :=
  fun h => CCX_not_five_neighbor
    (unitaryNeighborCircuit_mono hn (unitaryNeighborCircuit_of_achievable h))

/-! ## 7. `Phi(k)` and the missing quantitative lemma

`Phi(k) := max { |Tr(U† · CCX)| : U built from at most k two-qubit neighbour gates }`
is precisely the Huang–Palsberg object, measured quantitatively instead of
exactly.  Numerically (two independent optimisers, exact nuclear-norm block
updates and L-BFGS over `exp(iH)` parametrisations, with the free outer
single-qubit layer included):

| k        | 0 | 1   | 2       | 3       | 4          | 5          | 6 | 7 |
|----------|---|-----|---------|---------|------------|------------|---|---|
| `Phi(k)` | 6 | √40 | 4+2√2   | 4+2√2   | 8cos(π/8)  | 8cos(π/8)  | 8 | 8 |

Huang–Palsberg prove only `Phi(5) < 8` (their `CCZ_not_five_neighbor`, an
exact-synthesis statement).  `Phi(5) ≤ 8 cos(π/8)` — `PhiFive` below — is the
quantitative strengthening, and is NOT available from the HP machinery: every
step of that chain (`five_unitaryNeighbor_to_four_unitaryUnrestricted`,
`fourGate_*_implies_S4_or_S5`) is conditioned on the circuit's product being
EXACTLY a diagonal gate, and its conclusion `S₄ ∪ S₅` is a codimension-1
algebraic condition on the diagonal entries with no metric content. -/

/-- `PhiSqBound k c` : `Phi(k)² ≤ c`, in the `normSq`-of-trace units used by
    `achievable_trace_bound_cut`. -/
def PhiSqBound (k : ℕ) (c : ℝ) : Prop :=
  ∀ U : Mat8, UnitaryNeighborCircuit k U →
    Complex.normSq (Matrix.trace (Uᴴ * CCX)) ≤ c

theorem PhiSqBound.mono {j k : ℕ} {c : ℝ} (h : j ≤ k) (hb : PhiSqBound k c) :
    PhiSqBound j c :=
  fun U hU => hb U (unitaryNeighborCircuit_mono h hU)

/-- **The missing lemma.** `Phi(5) ≤ 8 cos(π/8)`.  NOT PROVED here — this is the
    statement of the gap. -/
def PhiFive : Prop := PhiSqBound 5 (64 * Real.cos (Real.pi / 8) ^ 2)

/-- Any CNOT word with at most five runs is bounded, given `PhiFive`. -/
theorem trace_bound_of_runs_le_five (hphi : PhiFive) {w : List Bool} {U : Mat8}
    (hw : CXWord w U) (hr : runs w ≤ 5) :
    Complex.normSq (Matrix.trace (Uᴴ * CCX)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2 :=
  hphi U (unitaryNeighborCircuit_mono hr (cxWord_run_form hw).1)

/-- `PhiFive` re-proves the existing main bound for `n ≤ 5` — with no min-cut,
    no `F(2)` computation and no use of the parity of 5.  (Compare
    `achievable_trace_bound_cut`, which is unconditional but uses all three.) -/
theorem achievable_trace_bound_of_phiFive (hphi : PhiFive) {n : ℕ} (hn : n ≤ 5)
    {U : Mat8} (h : AchievableCircuit n U) :
    Complex.normSq (Matrix.trace (Uᴴ * CCX)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2 := by
  obtain ⟨w, hlen, hw, _⟩ := achievable_run_block h
  exact trace_bound_of_runs_le_five hphi hw (le_trans (runs_le_length w) (by omega))

/-- **What the run reduction leaves at n = 6 and n = 7.**  Given `PhiFive`, every
    circuit of at most 7 CNOTs either already meets the `8cos(π/8)` bound, or its
    CNOT word has at least SIX runs.  Words of length ≤ 7 with ≥ 6 runs are, up to
    the A↔C mirror and reversal, only four: `1111111`, `211111`, `121111`,
    `112111`.  Those four profiles are the entire residual content of n = 6, 7. -/
theorem achievable_seven_dichotomy (hphi : PhiFive) {n : ℕ} (hn : n ≤ 7) {U : Mat8}
    (h : AchievableCircuit n U) :
    Complex.normSq (Matrix.trace (Uᴴ * CCX)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2 ∨
    ∃ w : List Bool, CXWord w U ∧ w.length ≤ 7 ∧ 6 ≤ runs w := by
  obtain ⟨w, hlen, hw, _⟩ := achievable_run_block h
  by_cases hr : runs w ≤ 5
  · exact Or.inl (trace_bound_of_runs_le_five hphi hw hr)
  · exact Or.inr ⟨w, hw, by omega, by omega⟩

end Block

end
