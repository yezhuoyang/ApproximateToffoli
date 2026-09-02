/-
  ApproxToffoli.HP.SetChar
  Set characterization theorems for diagonal gates.

  Theorem 7.1: D ∈ S_k ↔ D implementable with k neighbor gates
  Theorem 6.2: D ∈ S₄ ∪ S₅ ↔ conditions on neighbor/unrestricted gates

  We state the key direction needed for the main result:
  If a diagonal gate D is implementable with ≤5 neighbor gates, then D ∈ S₄ ∪ S₅.

  Reference: Huang & Palsberg (2026), Sections 6-7.
-/

import ApproxToffoli.HP.FiveToFour
import ApproxToffoli.PY24.Lemmas
-- `Complex.exp`/`Complex.log`: used only to extract the two square roots that
-- the paper's Section-3 six-gate construction needs (`six_neighbor_suffice`).
import Mathlib.Analysis.SpecialFunctions.Complex.Log

open Matrix Complex

noncomputable section

/-! ## Key theorem: 5 neighbor gates implies S₄ ∪ S₅

This combines:
- Theorem 4.5: 5 neighbor → 4 unrestricted (for diagonal gates)
- Theorem 6.2/7.2: 4 unrestricted → S₄ ∪ S₅
- Theorem 7.1(4): 4 neighbor → S₄ ∪ S₅

The full proof requires extensive infrastructure from Appendices C-E.
-/

/-- Extract the DiagGate3 from a diagonal matrix -/
def diagGateOf (D : Mat8) (hD : IsDiag8 D) : DiagGate3 := hD.choose

/-! ## Paper's Lemma A.14: Tensor structure of block-diagonal AC·AB products

Key structural lemma from Huang & Palsberg (2026), citing Palsberg & Yu (2024)
Lemma A.24. We have built the foundational infrastructure (Steps 102-108):
the 4-block A-decomposition of `embedAC U * embedAB V` is fully computed in
terms of U's and V's first-qubit sub-blocks (blockA_kk).

What remains is the deep algebraic content of A.14: under unitarity and the
block-diagonal-in-A hypothesis, the 2-term sums comprising each diagonal A-block
collapse to a single tensor term. This relies on prior published work
[Palsberg & Yu 2024, Lemma A.24], which is non-trivial. We state Lemma A.14
here as a black-box and use it downstream in Theorem 6.2. -/

/-- **Paper's Lemma A.14** [Huang & Palsberg 2026, citing Palsberg & Yu 2024 Lemma A.24]:
    For 4×4 unitary gates U, V (interpreted as 2-qubit gates), if the embedded
    product `embedAC U * embedAB V` is block-diagonal in qubit A (off-diagonal
    A-blocks vanish), then both diagonal A-blocks have a tensor product structure
    as 1-qubit ⊗ 1-qubit gates. -/
theorem paper_lemma_A14 (U V : Mat4) (hU : IsUnitary4 U) (hV : IsUnitary4 V)
    (h01 : block01 (embedAC U * embedAB V) = 0)
    (h10 : block10 (embedAC U * embedAB V) = 0) :
    ∃ (P₀ P₁ Q₀ Q₁ : Mat2),
      IsUnitary2 P₀ ∧ IsUnitary2 P₁ ∧ IsUnitary2 Q₀ ∧ IsUnitary2 Q₁ ∧
      block00 (embedAC U * embedAB V) = kron2 P₀ Q₀ ∧
      block11 (embedAC U * embedAB V) = kron2 P₁ Q₁ := by
  -- Direct call to PY24 Lemma A.24 (variable order P₀,Q₀,P₁,Q₁ vs P₀,P₁,Q₀,Q₁)
  obtain ⟨P₀, Q₀, P₁, Q₁, hP₀, hQ₀, hP₁, hQ₁, h00, h11⟩ :=
    py24_lemma_A_24 U V hU hV h01 h10
  exact ⟨P₀, P₁, Q₀, Q₁, hP₀, hP₁, hQ₀, hQ₁, h00, h11⟩

/-- Paper's Eq 19 → Eq 20: if `embedAC V₂ · embedAB V₃ = embedBC V₁ · D · embedBC V₄`
    for some Mat4 V₁, V₄ and *diagonal* D, with V₂, V₃ unitary, then the diagonal
    A-blocks of the AC·AB middle factor have tensor-product structure.

    This is the immediate consequence of paper_lemma_A14 (Step 109) combined with
    the Eq 19 packaging (Step 112): the RHS is block-diag-in-A automatically, and
    the LHS = RHS inherits this property, so Lemma A.14 applies to the LHS. -/
theorem eq19_to_eq20 (V₂ V₃ : Mat4)
    (hV₂ : IsUnitary4 V₂) (hV₃ : IsUnitary4 V₃)
    (V₁ V₄ : Mat4) (D : Mat8) (hD : IsDiag8 D)
    (h : embedAC V₂ * embedAB V₃ = embedBC V₁ * D * embedBC V₄) :
    ∃ (P₀ P₁ Q₀ Q₁ : Mat2),
      IsUnitary2 P₀ ∧ IsUnitary2 P₁ ∧ IsUnitary2 Q₀ ∧ IsUnitary2 Q₁ ∧
      block00 (embedAC V₂ * embedAB V₃) = kron2 P₀ Q₀ ∧
      block11 (embedAC V₂ * embedAB V₃) = kron2 P₁ Q₁ := by
  apply paper_lemma_A14 V₂ V₃ hV₂ hV₃
  · rw [h]; exact isDiag8_block01_embedBC V₁ V₄ D hD
  · rw [h]; exact isDiag8_block10_embedBC V₁ V₄ D hD

/-! ## Algebraic building blocks for the S₄/S₅ classification

The key algebraic fact: if eigenvalue ratios come from a tensor product P⊗Q,
then they satisfy one of the three S₄/S₅ product conditions.
This is because the tensor product eigenvalues (ap, bp, aq, bq) satisfy
ap·bq = bp·aq (both equal abpq).
-/

/-- The S₄/S₅ discriminant: product of the three possible pairwise differences.
    This is zero iff at least one of S₄, S₅², S₅³ holds. -/
def s45Discriminant (D : DiagGate3) : ℂ :=
  (D.d 0 * D.d 3 * D.d 5 * D.d 6 - D.d 1 * D.d 2 * D.d 4 * D.d 7) *
  (D.d 0 * D.d 2 * D.d 5 * D.d 7 - D.d 1 * D.d 3 * D.d 4 * D.d 6) *
  (D.d 0 * D.d 1 * D.d 6 * D.d 7 - D.d 2 * D.d 3 * D.d 4 * D.d 5)

/-- If the discriminant is zero, then D ∈ S₄ ∨ S₅.
    This reduces the classification to showing the discriminant vanishes
    for any diagonal gate produced by 4 unrestricted gates. -/
theorem S4_or_S5_of_discriminant_zero (D : DiagGate3)
    (h : s45Discriminant D = 0) : D.inS4 ∨ D.inS5 := by
  unfold s45Discriminant at h
  -- Factors are: (S₄ condition) * (S₅² condition) * (S₅³ condition)
  rcases mul_eq_zero.mp h with h12 | h3
  · rcases mul_eq_zero.mp h12 with h1 | h2
    · -- Factor 1 = 0 → S₄
      exact Or.inl (sub_eq_zero.mp h1)
    · -- Factor 2 = 0 → S₅²
      exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h2)))
  · -- Factor 3 = 0 → S₅³
    exact Or.inr (Or.inr (Or.inr (sub_eq_zero.mp h3)))

/-- The abstract discriminant for four complex numbers.
    Zero iff one of the three pair-product conditions holds. -/
def abstractDiscriminant (r₀ r₁ r₂ r₃ : ℂ) : ℂ :=
  (r₀ * r₃ - r₁ * r₂) * (r₀ * r₂ - r₁ * r₃) * (r₀ * r₁ - r₂ * r₃)

/-- The abstract discriminant vanishes for tensor product eigenvalues.
    This is the core identity: ap·bq = bp·aq. -/
theorem abstractDiscriminant_tensor (a b p q : ℂ) :
    abstractDiscriminant (a * p) (b * p) (a * q) (b * q) = 0 := by
  unfold abstractDiscriminant; ring

/-- The abstract discriminant is symmetric: invariant under transposition of first two args -/
theorem abstractDiscriminant_swap01 (r₀ r₁ r₂ r₃ : ℂ) :
    abstractDiscriminant r₁ r₀ r₂ r₃ = abstractDiscriminant r₀ r₁ r₂ r₃ := by
  unfold abstractDiscriminant; ring

/-- The abstract discriminant is symmetric: invariant under transposition of middle two args -/
theorem abstractDiscriminant_swap12 (r₀ r₁ r₂ r₃ : ℂ) :
    abstractDiscriminant r₀ r₂ r₁ r₃ = abstractDiscriminant r₀ r₁ r₂ r₃ := by
  unfold abstractDiscriminant; ring

/-- The abstract discriminant is symmetric: invariant under transposition of last two args -/
theorem abstractDiscriminant_swap23 (r₀ r₁ r₂ r₃ : ℂ) :
    abstractDiscriminant r₀ r₁ r₃ r₂ = abstractDiscriminant r₀ r₁ r₂ r₃ := by
  unfold abstractDiscriminant; ring

/-- **Paper's Lemma A.11** [Huang & Palsberg 2026, citing Palsberg & Yu 2024 Lemma A.5]
    + similarity invariance, packaged for our discriminant-vanishing reduction:
    If a diagonal Mat4 M is unitarily similar to a tensor product `kron2 P Q` of
    two 2×2 matrices, then the abstract discriminant of M's diagonal entries vanishes.

    Proof sketch (deferred — relies on Palsberg & Yu 2024 Lemma A.5):
    By Lemma A.11, eigenvalues(P⊗Q) = (ap, aq, bp, bq) as a multiset, where (a,b) =
    eigenvalues(P) and (p,q) = eigenvalues(Q). Similarity invariance:
    eigenvalues(V†·(P⊗Q)·V) = eigenvalues(P⊗Q). For diagonal M, eigenvalues(M) =
    diagonal entries (with multiplicity). Hence the diagonal entries are
    {ap, aq, bp, bq} up to permutation. The abstract discriminant is permutation-
    invariant (proven via `abstractDiscriminant_swap01/12/23`), and on the canonical
    tensor tuple (ap, aq, bp, bq) it vanishes (`abstractDiscriminant_tensor`).

    **Proof gap analysis (iter 223)**: The recently-extracted multiset-matching
    helper `multiset_match_4_eq_pair_pair` in PY24/Lemmas.lean (iter 219) uses
    direct algebra to show {a,b,p,q} = {c,c,d,d}. That setup has the pair-pair
    structure with 2 distinct values {c, d}. The current lemma needs
    {M_ii} = {ap, bp, aq, bq}, which has up to 4 distinct values. A direct-algebra
    analog would require deriving the polynomial equality
    `(X-M_00)(X-M_11)(X-M_22)(X-M_33) = (X-ap)(X-bp)(X-aq)(X-bq)` via 4 e_k
    equations, then plugging in each M_ii. The e_k of {ap, bp, aq, bq} in terms
    of (a, b, p, q):
      e_1 = (a + b)·(p + q),
      e_2 = ab·(p² + q²) + (a² + 2ab + b²)·pq = ab·(p+q)² + (a-b)²·pq + 2ab·pq,
      e_3 = abpq·(a + b)·(p + q) / (?), -- needs careful Vieta computation
      e_4 = a²·b²·p²·q².
    For the diagonal M, e_k(M_ii) = coefficients of charpoly(M) = symmetric in M_ii.
    For kron2 P Q, e_k of eigenvalues = coefficients of charpoly(kron2 P Q),
    which can be computed as products of charpolys of P and Q. The e_k matching
    requires `Matrix.charpoly` / `Polynomial.aeval` machinery from Mathlib, which
    would take 5-10 iters to set up. Alternative: invoke spectral theorem
    (`py24_lemma_A_3`) twice to extract a, b, p, q explicitly, then match
    coefficients directly via `linear_combination` (paralleling iter 207 logic).
    The 4-distinct-values multiset structure may need a generalization of
    `multiset_match_4_eq_pair_pair` (or a `multiset_match_4_general` variant). -/
theorem similar_diag_kron2_discriminant_zero
    (M : Mat4) (_hM : ∀ i j, i ≠ j → M i j = 0)
    (P Q : Mat2) (hP : IsUnitary2 P) (hQ : IsUnitary2 Q)
    (V : Mat4) (_hV : IsUnitary4 V)
    (_h : M = V.conjTranspose * kron2 P Q * V) :
    abstractDiscriminant (M 0 0) (M 1 1) (M 2 2) (M 3 3) = 0 := by
  -- Step 1: extract eigenvalues a, b, p, q via spectral theorem (PY24 A.3).
  obtain ⟨a, b, V_P, hV_P, hV_P_diag⟩ := py24_lemma_A_3 P hP
  obtain ⟨p, q, V_Q, hV_Q, hV_Q_diag⟩ := py24_lemma_A_3 Q hQ
  -- Step (iii): kron2 of two diagonals is diagonal with product entries.
  have h_kron_diag : kron2 (Matrix.diagonal ![a, b]) (Matrix.diagonal ![p, q])
                   = (Matrix.diagonal ![a * p, a * q, b * p, b * q] : Mat4) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [kron2, Matrix.diagonal_apply, Matrix.of_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  -- Step (iv-a): rearrange spectral theorem to express P, Q in terms of diagonals.
  -- From V_P† · P · V_P = Diag(a, b) and V_P unitary: P = V_P · Diag(a, b) · V_P†.
  have hVP_VPdag : V_P * V_P.conjTranspose = (1 : Mat2) := mul_eq_one_comm.mp hV_P
  have hVQ_VQdag : V_Q * V_Q.conjTranspose = (1 : Mat2) := mul_eq_one_comm.mp hV_Q
  have hP_spec : P = V_P * Matrix.diagonal ![a, b] * V_P.conjTranspose := by
    calc P = (V_P * V_P.conjTranspose) * P * (V_P * V_P.conjTranspose) := by
            rw [hVP_VPdag, one_mul, mul_one]
      _ = V_P * (V_P.conjTranspose * P * V_P) * V_P.conjTranspose := by noncomm_ring
      _ = V_P * Matrix.diagonal ![a, b] * V_P.conjTranspose := by rw [hV_P_diag]
  have hQ_spec : Q = V_Q * Matrix.diagonal ![p, q] * V_Q.conjTranspose := by
    calc Q = (V_Q * V_Q.conjTranspose) * Q * (V_Q * V_Q.conjTranspose) := by
            rw [hVQ_VQdag, one_mul, mul_one]
      _ = V_Q * (V_Q.conjTranspose * Q * V_Q) * V_Q.conjTranspose := by noncomm_ring
      _ = V_Q * Matrix.diagonal ![p, q] * V_Q.conjTranspose := by rw [hV_Q_diag]
  -- Step (iv-b): substitute hP_spec/hQ_spec into M, factor via kron2_mul.
  -- Result: M = (V† · kron2 V_P V_Q) · Diag(ap,aq,bp,bq) · (kron2 V_P V_Q)† · V.
  have hM_spec : M = V.conjTranspose * kron2 V_P V_Q *
                       (Matrix.diagonal ![a*p, a*q, b*p, b*q] : Mat4) *
                       (kron2 V_P V_Q).conjTranspose * V := by
    rw [_h, hP_spec, hQ_spec]
    rw [show kron2 (V_P * Matrix.diagonal ![a, b] * V_P.conjTranspose)
                    (V_Q * Matrix.diagonal ![p, q] * V_Q.conjTranspose) =
            kron2 V_P V_Q *
              kron2 (Matrix.diagonal ![a, b]) (Matrix.diagonal ![p, q]) *
              kron2 V_P.conjTranspose V_Q.conjTranspose from by
          rw [← kron2_mul, ← kron2_mul]]
    rw [h_kron_diag, ← kron2_conjTranspose]
    noncomm_ring
  -- Step (v) prep: kron2 V_P V_Q is unitary (product of two unitaries).
  have hKron_unit : IsUnitary4 (kron2 V_P V_Q) :=
    isUnitary4_kron2 hV_P hV_Q
  have hVV : V * V.conjTranspose = (1 : Mat4) := mul_eq_one_comm.mp _hV
  -- e_1: Tr(M) = ap + aq + bp + bq via similarity invariance.
  -- Tr(V† · K · D · K† · V) = Tr(V · V† · K · D · K†) [trace cyclic]
  -- = Tr(K · D · K†) [V·V† = 1]
  -- = Tr(D · K† · K) [trace cyclic]
  -- = Tr(D) [K† · K = 1].
  have h_trace_M : M.trace =
      (Matrix.diagonal ![a*p, a*q, b*p, b*q] : Mat4).trace := by
    rw [hM_spec]
    set K := kron2 V_P V_Q
    set D' := (Matrix.diagonal ![a*p, a*q, b*p, b*q] : Mat4)
    -- Goal: Tr(V† · K · D' · K† · V) = Tr(D').
    rw [show V.conjTranspose * K * D' * K.conjTranspose * V =
          V.conjTranspose * (K * D' * K.conjTranspose * V) from by noncomm_ring]
    rw [Matrix.trace_mul_comm]
    -- Goal: Tr(K · D' · K† · V · V†) = Tr(D').
    rw [show K * D' * K.conjTranspose * V * V.conjTranspose =
          K * D' * K.conjTranspose * (V * V.conjTranspose) from by noncomm_ring,
        hVV, mul_one]
    -- Goal: Tr(K · D' · K†) = Tr(D').
    rw [show K * D' * K.conjTranspose = K * (D' * K.conjTranspose) from by
          noncomm_ring]
    rw [Matrix.trace_mul_comm]
    -- Goal: Tr(D' · K† · K) = Tr(D').
    rw [show D' * K.conjTranspose * K = D' * (K.conjTranspose * K) from by
          noncomm_ring,
        hKron_unit, mul_one]
  -- Extract explicit e_1 equation: M_00 + M_11 + M_22 + M_33 = a*p + a*q + b*p + b*q.
  have h_e1 : M 0 0 + M 1 1 + M 2 2 + M 3 3 = a*p + a*q + b*p + b*q := by
    have hh := h_trace_M
    simp [Matrix.trace, Matrix.diagonal_apply_eq, Fin.sum_univ_four,
          Matrix.cons_val_zero, Matrix.cons_val_one] at hh
    linear_combination hh
  -- e_4: det(M) = det(D') via det multiplicativity + unitarity.
  -- det(V† · K · D' · K† · V) = det(V†)·det(K)·det(D')·det(K†)·det(V), and
  -- det(V†)·det(V) = det(V†·V) = 1, det(K)·det(K†) = det(K·K†) = 1.
  have h_det_M : M.det =
      (Matrix.diagonal ![a*p, a*q, b*p, b*q] : Mat4).det := by
    rw [hM_spec]
    set K := kron2 V_P V_Q
    set D' := (Matrix.diagonal ![a*p, a*q, b*p, b*q] : Mat4)
    have h_KK : K * K.conjTranspose = (1 : Mat4) := mul_eq_one_comm.mp hKron_unit
    have h_det_VV : V.conjTranspose.det * V.det = 1 := by
      rw [← Matrix.det_mul, _hV, Matrix.det_one]
    have h_det_KK : K.det * K.conjTranspose.det = 1 := by
      rw [← Matrix.det_mul, h_KK, Matrix.det_one]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
    linear_combination D'.det * K.det * K.conjTranspose.det * h_det_VV +
      D'.det * h_det_KK
  -- Extract explicit e_4 equation: M_00 · M_11 · M_22 · M_33 = ap·aq·bp·bq.
  -- Use _hM (off-diagonal entries are zero) to express M as Matrix.diagonal,
  -- then det of diagonal = product of diagonal entries.
  have h_M_diag : M = Matrix.diagonal (fun i => M i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; rw [Matrix.diagonal_apply_eq]
    · rw [_hM i j hij, Matrix.diagonal_apply_ne _ hij]
  have h_e4 : M 0 0 * M 1 1 * M 2 2 * M 3 3 =
      (a*p) * (a*q) * (b*p) * (b*q) := by
    have hh := h_det_M
    rw [h_M_diag] at hh
    rw [Matrix.det_diagonal, Matrix.det_diagonal] at hh
    simp [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one] at hh
    linear_combination hh
  -- Step (v) p_2 prep: M*M = V† · K · (D' · D') · K† · V.
  -- Derivation: (V†·K·D'·K†·V)·(V†·K·D'·K†·V)
  --   = V†·K·D'·K†·(V·V†)·K·D'·K†·V       [reassoc]
  --   = V†·K·D'·(K†·K)·D'·K†·V             [V·V† = 1]
  --   = V†·K·D'·D'·K†·V                    [K†·K = 1]
  have h_M_sq : M * M = V.conjTranspose * kron2 V_P V_Q *
                          ((Matrix.diagonal ![a*p, a*q, b*p, b*q] : Mat4) *
                           (Matrix.diagonal ![a*p, a*q, b*p, b*q] : Mat4)) *
                          (kron2 V_P V_Q).conjTranspose * V := by
    conv_lhs => rw [hM_spec]
    set K := kron2 V_P V_Q
    set D' := (Matrix.diagonal ![a*p, a*q, b*p, b*q] : Mat4)
    rw [show V.conjTranspose * K * D' * K.conjTranspose * V *
            (V.conjTranspose * K * D' * K.conjTranspose * V) =
          V.conjTranspose * K * D' * K.conjTranspose * (V * V.conjTranspose) *
            K * D' * K.conjTranspose * V from by noncomm_ring]
    rw [hVV, mul_one]
    rw [show V.conjTranspose * K * D' * K.conjTranspose * K * D' *
            K.conjTranspose * V =
          V.conjTranspose * K * D' * (K.conjTranspose * K) * D' *
            K.conjTranspose * V from by noncomm_ring]
    rw [hKron_unit, mul_one]
    noncomm_ring
  -- Step (v) p_2: Tr(M*M) = Tr(D'·D') via similarity invariance.
  -- Same trace-cycling chain as h_trace_M, applied to M*M = V†·K·(D'·D')·K†·V.
  have h_trace_M2 : (M * M).trace =
      ((Matrix.diagonal ![a*p, a*q, b*p, b*q] : Mat4) *
       (Matrix.diagonal ![a*p, a*q, b*p, b*q] : Mat4)).trace := by
    rw [h_M_sq]
    set K := kron2 V_P V_Q
    set D2 := (Matrix.diagonal ![a*p, a*q, b*p, b*q] : Mat4) *
              (Matrix.diagonal ![a*p, a*q, b*p, b*q] : Mat4)
    rw [show V.conjTranspose * K * D2 * K.conjTranspose * V =
          V.conjTranspose * (K * D2 * K.conjTranspose * V) from by noncomm_ring]
    rw [Matrix.trace_mul_comm]
    rw [show K * D2 * K.conjTranspose * V * V.conjTranspose =
          K * D2 * K.conjTranspose * (V * V.conjTranspose) from by noncomm_ring,
        hVV, mul_one]
    rw [show K * D2 * K.conjTranspose = K * (D2 * K.conjTranspose) from by
          noncomm_ring]
    rw [Matrix.trace_mul_comm]
    rw [show D2 * K.conjTranspose * K = D2 * (K.conjTranspose * K) from by
          noncomm_ring,
        hKron_unit, mul_one]
  -- Extract explicit p_2 equation: Σ M_ii² = Σ (D'_ii)².
  -- Strategy: collapse (diag d) * (diag d) = diag (d²) via diagonal_mul_diagonal,
  -- then expand both sides as Fin.sum_univ_four.
  have h_p2 : M 0 0 * M 0 0 + M 1 1 * M 1 1 + M 2 2 * M 2 2 + M 3 3 * M 3 3 =
      (a*p) * (a*p) + (a*q) * (a*q) + (b*p) * (b*p) + (b*q) * (b*q) := by
    have hh := h_trace_M2
    rw [h_M_diag] at hh
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal] at hh
    simp [Matrix.trace, Fin.sum_univ_four, Matrix.diagonal_apply_eq,
          Matrix.cons_val_zero, Matrix.cons_val_one] at hh
    linear_combination hh
  -- Newton's identity: 2·e_2 = e_1² - p_2.
  -- (Σ M_i)² - Σ M_i² = 2·Σ_{i<j} M_i·M_j, and similarly for D' diag entries.
  have h_e2 :
      M 0 0 * M 1 1 + M 0 0 * M 2 2 + M 0 0 * M 3 3 +
        M 1 1 * M 2 2 + M 1 1 * M 3 3 + M 2 2 * M 3 3 =
      (a*p) * (a*q) + (a*p) * (b*p) + (a*p) * (b*q) +
        (a*q) * (b*p) + (a*q) * (b*q) + (b*p) * (b*q) := by
    linear_combination
      ((M 0 0 + M 1 1 + M 2 2 + M 3 3) + (a*p + a*q + b*p + b*q)) / 2 * h_e1 -
        (1/2 : ℂ) * h_p2
  -- Step (v) p_3 prep: M*M*M = V† · K · (D'·D'·D') · K† · V.
  -- Use h_M_sq for the first M*M, then collapse K†·V·V†·K = K†·K = 1.
  have h_M_cube : M * M * M = V.conjTranspose * kron2 V_P V_Q *
                    ((Matrix.diagonal ![a*p, a*q, b*p, b*q] : Mat4) *
                     (Matrix.diagonal ![a*p, a*q, b*p, b*q] : Mat4) *
                     (Matrix.diagonal ![a*p, a*q, b*p, b*q] : Mat4)) *
                    (kron2 V_P V_Q).conjTranspose * V := by
    rw [h_M_sq, hM_spec]
    set K := kron2 V_P V_Q
    set D' := (Matrix.diagonal ![a*p, a*q, b*p, b*q] : Mat4)
    rw [show V.conjTranspose * K * (D' * D') * K.conjTranspose * V *
            (V.conjTranspose * K * D' * K.conjTranspose * V) =
          V.conjTranspose * K * (D' * D') * K.conjTranspose * (V * V.conjTranspose) *
            K * D' * K.conjTranspose * V from by noncomm_ring]
    rw [hVV, mul_one]
    rw [show V.conjTranspose * K * (D' * D') * K.conjTranspose * K * D' *
            K.conjTranspose * V =
          V.conjTranspose * K * (D' * D') * (K.conjTranspose * K) * D' *
            K.conjTranspose * V from by noncomm_ring]
    rw [hKron_unit, mul_one]
    noncomm_ring
  -- Step (v) p_3: Tr(M·M·M) = Tr(D'·D'·D') via similarity invariance.
  -- Same trace-cycling chain as h_trace_M, applied to M·M·M = V†·K·D'^3·K†·V.
  have h_trace_M3 : (M * M * M).trace =
      ((Matrix.diagonal ![a*p, a*q, b*p, b*q] : Mat4) *
       (Matrix.diagonal ![a*p, a*q, b*p, b*q] : Mat4) *
       (Matrix.diagonal ![a*p, a*q, b*p, b*q] : Mat4)).trace := by
    rw [h_M_cube]
    set K := kron2 V_P V_Q
    set D3 := (Matrix.diagonal ![a*p, a*q, b*p, b*q] : Mat4) *
              (Matrix.diagonal ![a*p, a*q, b*p, b*q] : Mat4) *
              (Matrix.diagonal ![a*p, a*q, b*p, b*q] : Mat4)
    rw [show V.conjTranspose * K * D3 * K.conjTranspose * V =
          V.conjTranspose * (K * D3 * K.conjTranspose * V) from by noncomm_ring]
    rw [Matrix.trace_mul_comm]
    rw [show K * D3 * K.conjTranspose * V * V.conjTranspose =
          K * D3 * K.conjTranspose * (V * V.conjTranspose) from by noncomm_ring,
        hVV, mul_one]
    rw [show K * D3 * K.conjTranspose = K * (D3 * K.conjTranspose) from by
          noncomm_ring]
    rw [Matrix.trace_mul_comm]
    rw [show D3 * K.conjTranspose * K = D3 * (K.conjTranspose * K) from by
          noncomm_ring,
        hKron_unit, mul_one]
  -- Extract explicit p_3 equation: Σ M_ii³ = Σ (D'_ii)³.
  -- Strategy: collapse triple-product diagonals via diagonal_mul_diagonal (×4 total),
  -- then expand both sides via Fin.sum_univ_four.
  have h_p3 :
      M 0 0 * M 0 0 * M 0 0 + M 1 1 * M 1 1 * M 1 1 +
        M 2 2 * M 2 2 * M 2 2 + M 3 3 * M 3 3 * M 3 3 =
      (a*p) * (a*p) * (a*p) + (a*q) * (a*q) * (a*q) +
        (b*p) * (b*p) * (b*p) + (b*q) * (b*q) * (b*q) := by
    have hh := h_trace_M3
    rw [h_M_diag] at hh
    simp only [Matrix.diagonal_mul_diagonal] at hh
    simp [Matrix.trace, Fin.sum_univ_four, Matrix.diagonal_apply_eq,
          Matrix.cons_val_zero, Matrix.cons_val_one] at hh
    linear_combination hh
  -- Newton's identity (k=3): 3·e_3 = p_3 - e_1·p_2 + e_2·e_1.
  -- Decomposition: 3·(diff_e3) = h_p3 - S_m·h_p2 + (E2_m - P_α)·h_e1 + S_α·h_e2.
  have h_e3 :
      M 0 0 * M 1 1 * M 2 2 + M 0 0 * M 1 1 * M 3 3 +
        M 0 0 * M 2 2 * M 3 3 + M 1 1 * M 2 2 * M 3 3 =
      (a*p) * (a*q) * (b*p) + (a*p) * (a*q) * (b*q) +
        (a*p) * (b*p) * (b*q) + (a*q) * (b*p) * (b*q) := by
    linear_combination
      (1/3 : ℂ) * h_p3 -
        (M 0 0 + M 1 1 + M 2 2 + M 3 3) / 3 * h_p2 +
        ((M 0 0 * M 1 1 + M 0 0 * M 2 2 + M 0 0 * M 3 3 +
            M 1 1 * M 2 2 + M 1 1 * M 3 3 + M 2 2 * M 3 3) -
          ((a*p)*(a*p) + (a*q)*(a*q) + (b*p)*(b*p) + (b*q)*(b*q))) / 3 * h_e1 +
        (a*p + a*q + b*p + b*q) / 3 * h_e2
  -- Step (v) closing: multiset_match_4_general gives polynomial-root condition for each M_ii.
  -- (Not strictly needed for Step (vi) via Strategy C, but kept for completeness.)
  obtain ⟨_h_root_0, _h_root_1, _h_root_2, _h_root_3⟩ :=
    multiset_match_4_general h_e1 h_e2 h_e3 h_e4
  -- Step (vi): abstractDiscriminant zero via symmetric polynomial identity.
  -- KEY IDENTITY (verified by ring): abstractDiscriminant r₀ r₁ r₂ r₃ =
  --   (r₀+r₁+r₂+r₃)²·(r₀·r₁·r₂·r₃) - (r₀r₁r₂+r₀r₁r₃+r₀r₂r₃+r₁r₂r₃)²
  --   = e_1²·e_4 - e_3².
  -- Since abstractDiscriminant(α) = 0 (polynomial identity for our specific
  -- α := (a*p, a*q, b*p, b*q)), and h_e1, h_e3, h_e4 give matching e_k's,
  -- abstractDiscriminant(M) = abstractDiscriminant(α) = 0.
  unfold abstractDiscriminant
  linear_combination
    (M 0 0 + M 1 1 + M 2 2 + M 3 3)^2 * h_e4 +
    ((a*p) * (a*q) * (b*p) * (b*q)) *
      ((M 0 0 + M 1 1 + M 2 2 + M 3 3) + (a*p + a*q + b*p + b*q)) * h_e1 -
    ((M 0 0 * M 1 1 * M 2 2 + M 0 0 * M 1 1 * M 3 3 +
      M 0 0 * M 2 2 * M 3 3 + M 1 1 * M 2 2 * M 3 3) +
     ((a*p)*(a*q)*(b*p) + (a*p)*(a*q)*(b*q) +
      (a*p)*(b*p)*(b*q) + (a*q)*(b*p)*(b*q))) * h_e3

/-! ## Connecting entry discriminant to abstract discriminant via eigenvalue ratios

If the diagonal entries satisfy d_{i+4} = rᵢ · dᵢ (eigenvalue ratio decomposition),
then s45Discriminant(D) = -(d₀d₁d₂d₃)³ · abstractDiscriminant(r₀,r₁,r₂,r₃).
This is a pure ring identity. -/

/-- The entry discriminant factors through eigenvalue ratios.
    Key identity: s45Disc = -(d₀d₁d₂d₃)³ · abstractDisc(ratios). -/
theorem s45Discriminant_eq_ratio_discriminant (D : DiagGate3) (r₀ r₁ r₂ r₃ : ℂ)
    (h₀ : D.d 4 = r₀ * D.d 0) (h₁ : D.d 5 = r₁ * D.d 1)
    (h₂ : D.d 6 = r₂ * D.d 2) (h₃ : D.d 7 = r₃ * D.d 3) :
    s45Discriminant D = -(D.d 0 * D.d 1 * D.d 2 * D.d 3) ^ 3 *
      abstractDiscriminant r₀ r₁ r₂ r₃ := by
  unfold s45Discriminant abstractDiscriminant
  rw [h₀, h₁, h₂, h₃]
  ring

/-- If eigenvalue ratios have vanishing abstract discriminant,
    the entry discriminant also vanishes. -/
theorem s45Discriminant_zero_of_ratio (D : DiagGate3) (r₀ r₁ r₂ r₃ : ℂ)
    (h₀ : D.d 4 = r₀ * D.d 0) (h₁ : D.d 5 = r₁ * D.d 1)
    (h₂ : D.d 6 = r₂ * D.d 2) (h₃ : D.d 7 = r₃ * D.d 3)
    (hdisc : abstractDiscriminant r₀ r₁ r₂ r₃ = 0) :
    s45Discriminant D = 0 := by
  rw [s45Discriminant_eq_ratio_discriminant D r₀ r₁ r₂ r₃ h₀ h₁ h₂ h₃, hdisc, mul_zero]

/-- Conversion: from `abstractDiscriminant (conj(D.d i) · D.d (i+4))_{i=0..3} = 0`
    derive `D ∈ S₄ ∪ S₅`. Uses the unit-modulus property `D.d i · conj(D.d i) = 1`
    to rewrite r_i = conj(D.d i) · D.d (i+4) so that D.d (i+4) = r_i · D.d i,
    then applies `s45Discriminant_zero_of_ratio` and `S4_or_S5_of_discriminant_zero`. -/
theorem inS4_or_S5_from_abstractDiscriminant (D : DiagGate3)
    (h : abstractDiscriminant
          (starRingEnd ℂ (D.d 0) * D.d 4)
          (starRingEnd ℂ (D.d 1) * D.d 5)
          (starRingEnd ℂ (D.d 2) * D.d 6)
          (starRingEnd ℂ (D.d 3) * D.d 7) = 0) :
    D.inS4 ∨ D.inS5 := by
  apply S4_or_S5_of_discriminant_zero
  refine s45Discriminant_zero_of_ratio D _ _ _ _ ?_ ?_ ?_ ?_ h
  all_goals
    first
      | (show D.d 4 = starRingEnd ℂ (D.d 0) * D.d 4 * D.d 0
         rw [mul_assoc, mul_comm (D.d 4) (D.d 0), ← mul_assoc, D.conj_mul_d 0, one_mul])
      | (show D.d 5 = starRingEnd ℂ (D.d 1) * D.d 5 * D.d 1
         rw [mul_assoc, mul_comm (D.d 5) (D.d 1), ← mul_assoc, D.conj_mul_d 1, one_mul])
      | (show D.d 6 = starRingEnd ℂ (D.d 2) * D.d 6 * D.d 2
         rw [mul_assoc, mul_comm (D.d 6) (D.d 2), ← mul_assoc, D.conj_mul_d 2, one_mul])
      | (show D.d 7 = starRingEnd ℂ (D.d 3) * D.d 7 * D.d 3
         rw [mul_assoc, mul_comm (D.d 7) (D.d 3), ← mul_assoc, D.conj_mul_d 3, one_mul])

/-! ## Theorem 6.2: BC-AC-AB-BC canonical case

This is one of the 9 canonical 4-gate patterns from Lemma C.1. Combining all the
infrastructure built in Steps 102-121, we can now prove this case directly. -/

/-- **Theorem 6.2, BC-AC-AB-BC canonical case** (1 of 9 from paper's Lemma C.1):
    if a diagonal D : DiagGate3 equals the product of 4 unrestricted unitaries with
    the BC-AC-AB-BC pattern, then D ∈ S₄ ∪ S₅. -/
theorem fourGate_BC_AC_AB_BC_implies_S4_or_S5 (D : DiagGate3)
    (V₁ V₂ V₃ V₄ : Mat4)
    (hV₁ : IsUnitary4 V₁) (hV₂ : IsUnitary4 V₂)
    (hV₃ : IsUnitary4 V₃) (hV₄ : IsUnitary4 V₄)
    (h : D.toMatrix = embedBC V₁ * embedAC V₂ * embedAB V₃ * embedBC V₄) :
    D.inS4 ∨ D.inS5 := by
  -- Step 1: Reassociate so the inner factor groups as (embedAC V₂ * embedAB V₃)
  have h' : D.toMatrix = embedBC V₁ * (embedAC V₂ * embedAB V₃) * embedBC V₄ := by
    rw [h]; noncomm_ring
  -- Step 2: Extract middle factor (Step 115) using V₁, V₄ unitarity
  have h_middle : embedAC V₂ * embedAB V₃ =
      embedBC V₁.conjTranspose * D.toMatrix * embedBC V₄.conjTranspose :=
    extract_middle_from_embedBC _ _ V₁ V₄ hV₁ hV₄ h'
  -- Step 3: Apply Lemma A.14 via eq19_to_eq20 (Step 113)
  obtain ⟨P₀, P₁, Q₀, Q₁, hP₀, hP₁, hQ₀, hQ₁, h00, h11⟩ :=
    eq19_to_eq20 V₂ V₃ hV₂ hV₃ V₁.conjTranspose V₄.conjTranspose D.toMatrix
      ⟨D, rfl⟩ h_middle
  -- Step 4: Compute (block00 D.toMatrix)† · (block11 D.toMatrix) two ways
  -- Form 1 (RHS): V₄† · kron2(P₀†P₁, Q₀†Q₁) · V₄ via Step 120
  have h_eq21_rhs : (block00 D.toMatrix).conjTranspose * (block11 D.toMatrix) =
      V₄.conjTranspose *
        kron2 (P₀.conjTranspose * P₁) (Q₀.conjTranspose * Q₁) * V₄ := by
    conv_lhs => rw [h']
    exact block00_conjTranspose_mul_block11_embedBC_kron2
            V₁ V₄ _ hV₁ P₀ P₁ Q₀ Q₁ h00 h11
  -- Form 2 (LHS): Matrix.diagonal (i ↦ conj(D.d i) · D.d (i+4)) via Step 117
  have h_eq21_lhs := block00_conjTranspose_mul_block11_diagGate3 D
  -- Combining: the diagonal matrix equals V₄† · kron2 · V₄
  have h_diag_eq : Matrix.diagonal (fun i : Fin 4 =>
        starRingEnd ℂ (D.d ⟨i.val, by omega⟩) * D.d ⟨i.val + 4, by omega⟩) =
      V₄.conjTranspose *
        kron2 (P₀.conjTranspose * P₁) (Q₀.conjTranspose * Q₁) * V₄ := by
    rw [← h_eq21_lhs, h_eq21_rhs]
  -- Step 5: Apply Lemma A.11 (Step 114) to get discriminant zero on diagonal entries
  have hM_diag : ∀ i j : Fin 4, i ≠ j →
      (Matrix.diagonal (fun i : Fin 4 =>
        starRingEnd ℂ (D.d ⟨i.val, by omega⟩) * D.d ⟨i.val + 4, by omega⟩)) i j = 0 := by
    intro i j hij
    simp [Matrix.diagonal_apply, hij]
  have hP : IsUnitary2 (P₀.conjTranspose * P₁) :=
    isUnitary2_mul (isUnitary2_conjTranspose hP₀) hP₁
  have hQ : IsUnitary2 (Q₀.conjTranspose * Q₁) :=
    isUnitary2_mul (isUnitary2_conjTranspose hQ₀) hQ₁
  have h_disc :=
    similar_diag_kron2_discriminant_zero _ hM_diag _ _ hP hQ V₄ hV₄ h_diag_eq
  -- Step 6: Reduce diagonal entries M_ii via Matrix.diagonal_apply_eq
  -- Each M i i = starRingEnd ℂ (D.d ⟨i.val, _⟩) * D.d ⟨i.val + 4, _⟩
  -- Need: this matches conj(D.d i) * D.d (i+4) for the call to Step 121.
  simp only [Matrix.diagonal_apply_eq] at h_disc
  -- Step 7: Apply Step 121 to conclude D ∈ S₄ ∪ S₅
  exact inS4_or_S5_from_abstractDiscriminant D h_disc

/-- Helper lemma: applying SWAP_AC then SWAP_BC conjugation to an AB-BC-AC-AB
    4-gate product produces a BC-AC-AB-BC pattern (with V₂, V₃ replaced by their
    SWAP_4-conjugates; V₁, V₄ unchanged due to the double SWAP_4 cancellation). -/
private lemma swap_bc_swap_ac_AB_BC_AC_AB (V₁ V₂ V₃ V₄ : Mat4) :
    SWAP_BC * (SWAP_AC * (embedAB V₁ * embedBC V₂ * embedAC V₃ * embedAB V₄) *
        SWAP_AC) * SWAP_BC =
      embedBC V₁ * embedAC (SWAP_4 * V₂ * SWAP_4) *
        embedAB (SWAP_4 * V₃ * SWAP_4) * embedBC V₄ := by
  rw [swap_ac_conj_distrib, swap_ac_conj_distrib, swap_ac_conj_distrib]
  rw [swap_ac_embedAB, swap_ac_embedBC, swap_ac_embedAC, swap_ac_embedAB]
  rw [swap_bc_conj_distrib, swap_bc_conj_distrib, swap_bc_conj_distrib]
  rw [swap_bc_embedBC, swap_bc_embedAB, swap_bc_embedAC, swap_bc_embedBC]
  rw [SWAP_4_double_conj, SWAP_4_double_conj]

/-- **Theorem 6.2, AB-BC-AC-AB canonical case** (2 of 9 from paper's Lemma C.1):
    proved by SWAP_AC + SWAP_BC double-conjugation reduction to the BC-AC-AB-BC
    case (Step 122) followed by Lemma 5.1 invariance. -/
theorem fourGate_AB_BC_AC_AB_implies_S4_or_S5 (D : DiagGate3)
    (V₁ V₂ V₃ V₄ : Mat4)
    (hV₁ : IsUnitary4 V₁) (hV₂ : IsUnitary4 V₂)
    (hV₃ : IsUnitary4 V₃) (hV₄ : IsUnitary4 V₄)
    (h : D.toMatrix = embedAB V₁ * embedBC V₂ * embedAC V₃ * embedAB V₄) :
    D.inS4 ∨ D.inS5 := by
  rw [← DiagGate3.swapAC_inS4_or_S5_iff D, ← DiagGate3.swapBC_inS4_or_S5_iff D.swapAC]
  have hD' : D.swapAC.swapBC.toMatrix =
      embedBC V₁ * embedAC (SWAP_4 * V₂ * SWAP_4) *
        embedAB (SWAP_4 * V₃ * SWAP_4) * embedBC V₄ := by
    rw [← swapBC_toMatrix, ← swapAC_toMatrix, h]
    exact swap_bc_swap_ac_AB_BC_AC_AB V₁ V₂ V₃ V₄
  exact fourGate_BC_AC_AB_BC_implies_S4_or_S5 D.swapAC.swapBC
    V₁ (SWAP_4 * V₂ * SWAP_4) (SWAP_4 * V₃ * SWAP_4) V₄
    hV₁ (isUnitary4_swap4_conj V₂ hV₂) (isUnitary4_swap4_conj V₃ hV₃) hV₄ hD'

/-- Helper lemma: SWAP_AB conjugation of an AC-BC-AB-AC 4-gate product yields
    a BC-AC-AB-BC pattern with V₃ replaced by SWAP_4·V₃·SWAP_4; V₁, V₂, V₄ unchanged. -/
private lemma swap_ab_AC_BC_AB_AC (V₁ V₂ V₃ V₄ : Mat4) :
    SWAP_AB * (embedAC V₁ * embedBC V₂ * embedAB V₃ * embedAC V₄) * SWAP_AB =
      embedBC V₁ * embedAC V₂ * embedAB (SWAP_4 * V₃ * SWAP_4) * embedBC V₄ := by
  rw [swap_ab_conj_distrib, swap_ab_conj_distrib, swap_ab_conj_distrib]
  rw [swap_ab_embedAC, swap_ab_embedBC, swap_ab_embedAB, swap_ab_embedAC]

/-- **Theorem 6.2, AC-BC-AB-AC canonical case** (3 of 9 from paper's Lemma C.1):
    proved by single SWAP_AB conjugation reduction to the BC-AC-AB-BC case (Step 122)
    followed by Lemma 5.1 invariance. (Paper page 20: simpler than Step 127 because
    only one SWAP suffices.) -/
theorem fourGate_AC_BC_AB_AC_implies_S4_or_S5 (D : DiagGate3)
    (V₁ V₂ V₃ V₄ : Mat4)
    (hV₁ : IsUnitary4 V₁) (hV₂ : IsUnitary4 V₂)
    (hV₃ : IsUnitary4 V₃) (hV₄ : IsUnitary4 V₄)
    (h : D.toMatrix = embedAC V₁ * embedBC V₂ * embedAB V₃ * embedAC V₄) :
    D.inS4 ∨ D.inS5 := by
  rw [← DiagGate3.swapAB_inS4_or_S5_iff D]
  have hD' : D.swapAB.toMatrix =
      embedBC V₁ * embedAC V₂ * embedAB (SWAP_4 * V₃ * SWAP_4) * embedBC V₄ := by
    rw [← swapAB_toMatrix, h]
    exact swap_ab_AC_BC_AB_AC V₁ V₂ V₃ V₄
  exact fourGate_BC_AC_AB_BC_implies_S4_or_S5 D.swapAB
    V₁ V₂ (SWAP_4 * V₃ * SWAP_4) V₄
    hV₁ hV₂ (isUnitary4_swap4_conj V₃ hV₃) hV₄ hD'

/-- Helper: `embedBC` of a diagonal Mat4 with entries `[c₀, c₁, c₂, c₃]`
    equals a diagonal Mat8 with entries `[c₀, c₁, c₂, c₃, c₀, c₁, c₂, c₃]`.
    (embedBC = I₂ ⊗ V, so the 4-vector is repeated twice.) -/
private lemma embedBC_diag_eq (c0 c1 c2 c3 : ℂ) :
    embedBC (Matrix.diagonal ![c0, c1, c2, c3]) =
    (Matrix.diagonal ![c0, c1, c2, c3, c0, c1, c2, c3] : Mat8) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedBC, Matrix.diagonal, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Helper: `embedAC` of a diagonal Mat4 with entries `[c₀, c₁, c₂, c₃]`
    equals a diagonal Mat8 with entries `[c₀, c₁, c₀, c₁, c₂, c₃, c₂, c₃]`.
    (embedAC acts on (A,C) with identity on B.) -/
private lemma embedAC_diag_eq (c0 c1 c2 c3 : ℂ) :
    embedAC (Matrix.diagonal ![c0, c1, c2, c3]) =
    (Matrix.diagonal ![c0, c1, c0, c1, c2, c3, c2, c3] : Mat8) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedAC, Matrix.diagonal, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Helper: `Matrix.diagonal ![c0, c1, c2, c3]` is unitary when each
    `cᵢ` has `|cᵢ|² = 1`. Mirrors `isUnitary4_diag_one_one_one_u` but
    for fully arbitrary unit-modulus diagonal entries. -/
private lemma isUnitary4_diag4_unit_modulus
    (c0 c1 c2 c3 : ℂ)
    (h0 : Complex.normSq c0 = 1) (h1 : Complex.normSq c1 = 1)
    (h2 : Complex.normSq c2 = 1) (h3 : Complex.normSq c3 = 1) :
    IsUnitary4 (Matrix.diagonal ![c0, c1, c2, c3]) := by
  unfold IsUnitary4
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Matrix.diagonal, Matrix.mul_apply,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  · rw [show starRingEnd ℂ c0 * c0 = (Complex.normSq c0 : ℂ) from by
          rw [mul_comm]; exact Complex.mul_conj c0]
    exact_mod_cast h0
  · rw [show starRingEnd ℂ c1 * c1 = (Complex.normSq c1 : ℂ) from by
          rw [mul_comm]; exact Complex.mul_conj c1]
    exact_mod_cast h1
  · rw [show starRingEnd ℂ c2 * c2 = (Complex.normSq c2 : ℂ) from by
          rw [mul_comm]; exact Complex.mul_conj c2]
    exact_mod_cast h2
  · rw [show starRingEnd ℂ c3 * c3 = (Complex.normSq c3 : ℂ) from by
          rw [mul_comm]; exact Complex.mul_conj c3]
    exact_mod_cast h3

/-- Helper: SWAP_AB conjugation of BC-AC-BC-AC pattern → AC-BC-AC-BC pattern.
    Used in `fourGate_BC_AC_BC_AC_implies_S4_or_S5` Step 3. The cleanness of
    BC↔AC swap (no SWAP_4 conjugation needed) follows from
    `swap_ab_embedBC` and `swap_ab_embedAC`. -/
private lemma swap_ab_BC_AC_BC_AC (V₁ V₂ V₃ V₄ : Mat4) :
    SWAP_AB * (embedBC V₁ * embedAC V₂ * embedBC V₃ * embedAC V₄) * SWAP_AB =
      embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄ := by
  rw [swap_ab_conj_distrib, swap_ab_conj_distrib, swap_ab_conj_distrib]
  rw [swap_ab_embedBC, swap_ab_embedAC, swap_ab_embedBC, swap_ab_embedAC]

/-- Helper: SWAP_AB conjugation fixes the target diagonal
    `Diag(![1,1,1,1,1,1,a,b])` because the only non-trivial entries are at
    indices 6, 7 (binary 110, 111), which have qubit a = qubit b = 1, hence
    are fixed by the A↔B swap. -/
private lemma swap_ab_target_diag (a b : ℂ) :
    SWAP_AB * (Matrix.diagonal ![1, 1, 1, 1, 1, 1, a, b] : Mat8) * SWAP_AB =
    Matrix.diagonal ![1, 1, 1, 1, 1, 1, a, b] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SWAP_AB, swap_ab_perm, Matrix.diagonal, Matrix.mul_apply,
          Matrix.of_apply, Fin.sum_univ_eight,
          Matrix.cons_val_zero, Matrix.cons_val_one]

/-! ## Theorem 6.1: alternating 4-gate patterns

Paper's Theorem 6.1 [Huang & Palsberg 2026, page 18, citing Palsberg & Yu 2024 Lemma A.9]
states 3 alternating 4-gate patterns each characterize one S₅ᵏ subset:
  - Property (1): D ∈ S₄ ∪ S₅¹ ↔ ∃ U₁..U₄: Ū_{1AC} Ū_{2AB} Ū_{3AC} Ū_{4AB} = D.
  - Property (2): D ∈ S₄ ∪ S₅² ↔ ∃ U₁..U₄: Ū_{1BC} Ū_{2AB} Ū_{3BC} Ū_{4AB} = D.
  - Property (3): D ∈ S₄ ∪ S₅³ ↔ ∃ U₁..U₄: Ū_{1BC} Ū_{2AC} Ū_{3BC} Ū_{4AC} = D.

The proof uses Lemma A.9 (eigenvalue characterization for 2-qubit unitary product),
which is from prior published work. We state Theorem 6.1 case (3) as a black-box;
cases (1) and (2) follow by SWAP conjugation. -/

/-- **Theorem 6.2, BC-AC-BC-AC canonical case (#6)** = paper's Theorem 6.1(3) forward.

PY24 dependency `py24_lemma_6_4` is now proved (PY24 closure iter 358),
so this theorem becomes tractable. The proof follows HP paper p.17
Property (3), reading the iff chain from the bottom up:

Step 1. Define ratios a := d₆·d₀/(d₂·d₄), b := d₇·d₁/(d₃·d₅).
        (Need d₂, d₃, d₄, d₅ ≠ 0; D is unitary so all dᵢ are unit-modulus
        complex, hence nonzero.)

Step 2. From `D.toMatrix = embedBC V₁ * embedAC V₂ * embedBC V₃ * embedAC V₄`,
        construct V'₁..V'₄ such that
        `embedBC V'₁ * embedAC V'₂ * embedBC V'₃ * embedAC V'₄ = CC(Diag(a, b))`.
        Specifically: define W₁ := Diag(d₀, d₁, d₂, d₃),
        W₄ := Diag(1, 1, d₄/d₀, d₅/d₁); then V'₁ := W₁⁻¹ * V₁, V'₂ := V₂,
        V'₃ := V₃, V'₄ := V₄ * W₄⁻¹ should work (paper's W₁, W₄ inversion).

Step 3. SWAP_AB conjugate Step 2's chain to swap embedBC ↔ embedAC:
        get `embedAC V''₁ * embedBC V''₂ * embedAC V''₃ * embedBC V''₄ = CC(Diag(a, b))`.

Step 4. Apply `py24_lemma_6_4` (⇒) to Step 3's chain → conclude
        a = b ∨ a · b = 1.

Step 5. Translate to d-products:
        a = b ⟺ d₆d₀d₃d₅ = d₇d₁d₂d₄ ⟺ d₀d₃d₅d₆ = d₁d₂d₄d₇ = D.inS4.
        a · b = 1 ⟺ d₆d₀d₇d₁ = d₂d₄d₃d₅ ⟺ d₀d₁d₆d₇ = d₂d₃d₄d₅ = D.inS5³.
        Combining: D.inS4 ∨ D.inS5³ → D.inS4 ∨ D.inS5.

Estimated effort: ~150-300 Lean lines. The remaining 5 alternating
patterns (#4, #5, #7, #8, #9) reduce to this via SWAP conjugations +
Lemma 5.1 + dagger + Lemma 5.3.

Body: `sorry` — closure tracked across multiple iters. -/
theorem fourGate_BC_AC_BC_AC_implies_S4_or_S5 (D : DiagGate3)
    (V₁ V₂ V₃ V₄ : Mat4)
    (_hV₁ : IsUnitary4 V₁) (_hV₂ : IsUnitary4 V₂)
    (_hV₃ : IsUnitary4 V₃) (_hV₄ : IsUnitary4 V₄)
    (_h : D.toMatrix = embedBC V₁ * embedAC V₂ * embedBC V₃ * embedAC V₄) :
    D.inS4 ∨ D.inS5 := by
  -- Step 1: each d_i ≠ 0 (from |d_i| = 1) and define ratios a, b.
  have hd0 : D.d 0 ≠ 0 := D.d_ne_zero 0
  have hd1 : D.d 1 ≠ 0 := D.d_ne_zero 1
  have hd2 : D.d 2 ≠ 0 := D.d_ne_zero 2
  have hd3 : D.d 3 ≠ 0 := D.d_ne_zero 3
  have hd4 : D.d 4 ≠ 0 := D.d_ne_zero 4
  have hd5 : D.d 5 ≠ 0 := D.d_ne_zero 5
  have hd6 : D.d 6 ≠ 0 := D.d_ne_zero 6
  have hd7 : D.d 7 ≠ 0 := D.d_ne_zero 7
  -- Define eigenvalue ratios a := d₆·d₀/(d₂·d₄), b := d₇·d₁/(d₃·d₅).
  set a := D.d 6 * D.d 0 / (D.d 2 * D.d 4) with ha_def
  set b := D.d 7 * D.d 1 / (D.d 3 * D.d 5) with hb_def
  -- a, b have normSq = 1 (unit-modulus, ratio of unit-modulus complex numbers).
  have h_normSq_a : Complex.normSq a = 1 := by
    rw [ha_def]
    rw [map_div₀, map_mul, map_mul, D.unit 6, D.unit 0, D.unit 2, D.unit 4]
    norm_num
  have h_normSq_b : Complex.normSq b = 1 := by
    rw [hb_def]
    rw [map_div₀, map_mul, map_mul, D.unit 7, D.unit 1, D.unit 3, D.unit 5]
    norm_num
  -- Step 2 setup: W₁, W₄ unitary diagonal matrices for chain absorption.
  -- W₁ = Diag(d₀, d₁, d₂, d₃), W₄ = Diag(1, 1, d₄/d₀, d₅/d₁).
  set W₁ : Mat4 := Matrix.diagonal ![D.d 0, D.d 1, D.d 2, D.d 3] with hW₁_def
  set W₄ : Mat4 := Matrix.diagonal ![1, 1, D.d 4 / D.d 0, D.d 5 / D.d 1] with hW₄_def
  -- Ratios d_k/d_l have unit modulus (normSq = 1).
  have h_ratio_normSq : ∀ k l : Fin 8,
      Complex.normSq (D.d k / D.d l) = 1 := by
    intro k l
    rw [map_div₀, D.unit k, D.unit l]; norm_num
  -- Use the local helper isUnitary4_diag4_unit_modulus (defined just before this theorem).
  have hW₁_unit : IsUnitary4 W₁ := by
    rw [hW₁_def]
    exact isUnitary4_diag4_unit_modulus _ _ _ _
      (D.unit 0) (D.unit 1) (D.unit 2) (D.unit 3)
  have hW₄_unit : IsUnitary4 W₄ := by
    rw [hW₄_def]
    refine isUnitary4_diag4_unit_modulus _ _ _ _ ?_ ?_ ?_ ?_
    · simp
    · simp
    · exact h_ratio_normSq 4 0
    · exact h_ratio_normSq 5 1
  -- Step 2 absorption: define V₁' := W₁† * V₁, V₄' := V₄ * W₄†.
  -- These are V'₁, V'₄ in the docstring (W₁⁻¹ = W₁† for unitary W₁).
  set V₁' := W₁.conjTranspose * V₁ with hV₁'_def
  set V₄' := V₄ * W₄.conjTranspose with hV₄'_def
  have _hV₁'_unit : IsUnitary4 V₁' :=
    isUnitary4_mul (isUnitary4_conjTranspose hW₁_unit) _hV₁
  have _hV₄'_unit : IsUnitary4 V₄' :=
    isUnitary4_mul _hV₄ (isUnitary4_conjTranspose hW₄_unit)
  -- Algebraic factoring: chain product splits via embedBC_mul / embedAC_mul.
  -- embedBC V₁' = embedBC W₁† · embedBC V₁; embedAC V₄' = embedAC V₄ · embedAC W₄†.
  -- Reassociate and substitute _h to get
  -- embedBC W₁† · D.toMatrix · embedAC W₄†.
  have h_chain_factor :
      embedBC V₁' * embedAC V₂ * embedBC V₃ * embedAC V₄' =
      embedBC W₁.conjTranspose * D.toMatrix * embedAC W₄.conjTranspose := by
    rw [hV₁'_def, hV₄'_def]
    rw [← embedBC_mul W₁.conjTranspose V₁,
        ← embedAC_mul V₄ W₄.conjTranspose]
    rw [show
      embedBC W₁.conjTranspose * embedBC V₁ * embedAC V₂ * embedBC V₃ *
        (embedAC V₄ * embedAC W₄.conjTranspose) =
      embedBC W₁.conjTranspose *
        (embedBC V₁ * embedAC V₂ * embedBC V₃ * embedAC V₄) *
        embedAC W₄.conjTranspose from by noncomm_ring]
    rw [← _h]
  -- Step 2c prep: convert W₁†, W₄† to explicit Matrix.diagonal ![star ...] forms.
  have hW₁_conjT_form : W₁.conjTranspose =
      Matrix.diagonal ![star (D.d 0), star (D.d 1), star (D.d 2), star (D.d 3)] := by
    rw [hW₁_def, Matrix.diagonal_conjTranspose]
    congr 1
    funext i; fin_cases i <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hW₄_conjT_form : W₄.conjTranspose =
      Matrix.diagonal ![1, 1, star (D.d 4 / D.d 0), star (D.d 5 / D.d 1)] := by
    rw [hW₄_def, Matrix.diagonal_conjTranspose]
    congr 1
    funext i; fin_cases i <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  -- For each unitary d_i, star(d_i) = 1/d_i (since d_i * star(d_i) = 1).
  have h_star_d : ∀ k : Fin 8, star (D.d k) = 1 / D.d k := by
    intro k
    have h1 : D.d k * star (D.d k) = 1 := D.d_mul_conj k
    have hk : D.d k ≠ 0 := D.d_ne_zero k
    field_simp
    linear_combination h1
  -- Step 2c: full diagonal calc.
  -- After applying embedBC_diag_eq, embedAC_diag_eq, Matrix.diagonal_mul_diagonal ×2,
  -- we get LHS = Matrix.diagonal of an explicit 8-vector matching
  -- ![1, 1, 1, 1, 1, 1, a, b]. Each entry verified algebraically:
  -- - i=0..3: star(d_k)·d_k·1 = 1 (via D.d_mul_conj k after star→inverse).
  -- - i=4: (1/d_0)·d_4·(d_0/d_4) = 1.
  -- - i=5: (1/d_1)·d_5·(d_1/d_5) = 1.
  -- - i=6: (1/d_2)·d_6·(d_0/d_4) = d_6·d_0/(d_2·d_4) = a.
  -- - i=7: (1/d_3)·d_7·(d_1/d_5) = d_7·d_1/(d_3·d_5) = b.
  -- Per-case closure via field_simp + ring is standard but combinator
  -- orchestration on 8 subgoals (some trivial, some needing field_simp)
  -- requires careful tactic structure; deferred to iter 432+.
  have h_chain_eq_target :
      embedBC W₁.conjTranspose * D.toMatrix * embedAC W₄.conjTranspose =
      (Matrix.diagonal ![1, 1, 1, 1, 1, 1, a, b] : Mat8) := by
    rw [hW₁_conjT_form, hW₄_conjT_form,
        embedBC_diag_eq, embedAC_diag_eq]
    unfold DiagGate3.toMatrix
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [ha_def, hb_def]
    simp only [star_div₀, h_star_d]
    fin_cases i <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.mul_apply] <;>
      field_simp <;> ring
  -- Step 2 closure: combine h_chain_factor + h_chain_eq_target.
  have h_chain_combined :
      embedBC V₁' * embedAC V₂ * embedBC V₃ * embedAC V₄' =
      (Matrix.diagonal ![1, 1, 1, 1, 1, 1, a, b] : Mat8) := by
    rw [h_chain_factor]; exact h_chain_eq_target
  -- Step 3: SWAP_AB conjugate to AC-BC-AC-BC pattern.
  have h_chain_swapped :
      embedAC V₁' * embedBC V₂ * embedAC V₃ * embedBC V₄' =
      (Matrix.diagonal ![1, 1, 1, 1, 1, 1, a, b] : Mat8) := by
    have h := congrArg (fun X => SWAP_AB * X * SWAP_AB) h_chain_combined
    simp only at h
    rw [swap_ab_BC_AC_BC_AC, swap_ab_target_diag] at h
    exact h
  -- Step 4: invoke py24_lemma_6_4.
  have h_a_or_b : a = b ∨ a * b = 1 :=
    (py24_lemma_6_4 a b h_normSq_a h_normSq_b).mp
      ⟨V₁', V₂, V₃, V₄', _hV₁'_unit, _hV₂, _hV₃, _hV₄'_unit, h_chain_swapped⟩
  -- Step 5: case split → S4 ∨ S5.
  rcases h_a_or_b with hab | hab
  · -- a = b → D.inS4 (entry-product equality).
    left
    rw [ha_def, hb_def] at hab
    unfold DiagGate3.inS4
    have := hab
    field_simp at this
    linear_combination this
  · -- a * b = 1 → D.inS5³ → D.inS5.
    right
    right; right
    rw [ha_def, hb_def] at hab
    have := hab
    field_simp at this
    linear_combination this

/-- Helper: SWAP_BC conjugation of BC-AB-BC-AB → BC-AC-BC-AC pattern. -/
private lemma swap_bc_BC_AB_BC_AB (V₁ V₂ V₃ V₄ : Mat4) :
    SWAP_BC * (embedBC V₁ * embedAB V₂ * embedBC V₃ * embedAB V₄) * SWAP_BC =
      embedBC (SWAP_4 * V₁ * SWAP_4) * embedAC V₂ *
        embedBC (SWAP_4 * V₃ * SWAP_4) * embedAC V₄ := by
  rw [swap_bc_conj_distrib, swap_bc_conj_distrib, swap_bc_conj_distrib]
  rw [swap_bc_embedBC, swap_bc_embedAB, swap_bc_embedBC, swap_bc_embedAB]

/-- **Theorem 6.2, BC-AB-BC-AB canonical case (#5)**: reduces to #6 via SWAP_BC. -/
theorem fourGate_BC_AB_BC_AB_implies_S4_or_S5 (D : DiagGate3)
    (V₁ V₂ V₃ V₄ : Mat4)
    (hV₁ : IsUnitary4 V₁) (hV₂ : IsUnitary4 V₂)
    (hV₃ : IsUnitary4 V₃) (hV₄ : IsUnitary4 V₄)
    (h : D.toMatrix = embedBC V₁ * embedAB V₂ * embedBC V₃ * embedAB V₄) :
    D.inS4 ∨ D.inS5 := by
  rw [← DiagGate3.swapBC_inS4_or_S5_iff D]
  have hD' : D.swapBC.toMatrix =
      embedBC (SWAP_4 * V₁ * SWAP_4) * embedAC V₂ *
        embedBC (SWAP_4 * V₃ * SWAP_4) * embedAC V₄ := by
    rw [← swapBC_toMatrix, h]
    exact swap_bc_BC_AB_BC_AB V₁ V₂ V₃ V₄
  exact fourGate_BC_AC_BC_AC_implies_S4_or_S5 D.swapBC
    (SWAP_4 * V₁ * SWAP_4) V₂ (SWAP_4 * V₃ * SWAP_4) V₄
    (isUnitary4_swap4_conj V₁ hV₁) hV₂
    (isUnitary4_swap4_conj V₃ hV₃) hV₄ hD'

/-- Helper: SWAP_AB conjugation of AC-AB-AC-AB → BC-AB-BC-AB pattern. -/
private lemma swap_ab_AC_AB_AC_AB (V₁ V₂ V₃ V₄ : Mat4) :
    SWAP_AB * (embedAC V₁ * embedAB V₂ * embedAC V₃ * embedAB V₄) * SWAP_AB =
      embedBC V₁ * embedAB (SWAP_4 * V₂ * SWAP_4) *
        embedBC V₃ * embedAB (SWAP_4 * V₄ * SWAP_4) := by
  rw [swap_ab_conj_distrib, swap_ab_conj_distrib, swap_ab_conj_distrib]
  rw [swap_ab_embedAC, swap_ab_embedAB, swap_ab_embedAC, swap_ab_embedAB]

/-- **Theorem 6.2, AC-AB-AC-AB canonical case (#4)**: reduces to #5 via SWAP_AB. -/
theorem fourGate_AC_AB_AC_AB_implies_S4_or_S5 (D : DiagGate3)
    (V₁ V₂ V₃ V₄ : Mat4)
    (hV₁ : IsUnitary4 V₁) (hV₂ : IsUnitary4 V₂)
    (hV₃ : IsUnitary4 V₃) (hV₄ : IsUnitary4 V₄)
    (h : D.toMatrix = embedAC V₁ * embedAB V₂ * embedAC V₃ * embedAB V₄) :
    D.inS4 ∨ D.inS5 := by
  rw [← DiagGate3.swapAB_inS4_or_S5_iff D]
  have hD' : D.swapAB.toMatrix =
      embedBC V₁ * embedAB (SWAP_4 * V₂ * SWAP_4) *
        embedBC V₃ * embedAB (SWAP_4 * V₄ * SWAP_4) := by
    rw [← swapAB_toMatrix, h]
    exact swap_ab_AC_AB_AC_AB V₁ V₂ V₃ V₄
  exact fourGate_BC_AB_BC_AB_implies_S4_or_S5 D.swapAB
    V₁ (SWAP_4 * V₂ * SWAP_4) V₃ (SWAP_4 * V₄ * SWAP_4)
    hV₁ (isUnitary4_swap4_conj V₂ hV₂)
    hV₃ (isUnitary4_swap4_conj V₄ hV₄) hD'

/-- (Re-export alias for backward compat; underlying `isUnitary4_conjTranspose`
    is in Kron2.lean.) -/
private lemma isUnitary4_conjTranspose' {V : Mat4} (hV : IsUnitary4 V) :
    IsUnitary4 V.conjTranspose := isUnitary4_conjTranspose hV

/-- **Theorem 6.2, AB-AC-AB-AC canonical case (#7)**: reduces to #4 (AC-AB-AC-AB) via
    dagger of the DiagGate3 + Matrix conjTranspose of the 4-gate product. -/
theorem fourGate_AB_AC_AB_AC_implies_S4_or_S5 (D : DiagGate3)
    (V₁ V₂ V₃ V₄ : Mat4)
    (hV₁ : IsUnitary4 V₁) (hV₂ : IsUnitary4 V₂)
    (hV₃ : IsUnitary4 V₃) (hV₄ : IsUnitary4 V₄)
    (h : D.toMatrix = embedAB V₁ * embedAC V₂ * embedAB V₃ * embedAC V₄) :
    D.inS4 ∨ D.inS5 := by
  rw [← DiagGate3.dagger_inS4_or_S5_iff D]
  have hD' : D.dagger.toMatrix =
      embedAC V₄.conjTranspose * embedAB V₃.conjTranspose *
        embedAC V₂.conjTranspose * embedAB V₁.conjTranspose := by
    rw [DiagGate3.dagger_toMatrix, h]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    rw [embedAB_conjTranspose, embedAC_conjTranspose,
        embedAB_conjTranspose, embedAC_conjTranspose]
    noncomm_ring
  exact fourGate_AC_AB_AC_AB_implies_S4_or_S5 D.dagger
    V₄.conjTranspose V₃.conjTranspose V₂.conjTranspose V₁.conjTranspose
    (isUnitary4_conjTranspose' hV₄) (isUnitary4_conjTranspose' hV₃)
    (isUnitary4_conjTranspose' hV₂) (isUnitary4_conjTranspose' hV₁) hD'

/-- **Theorem 6.2, AB-BC-AB-BC canonical case (#8)**: reduces to #5 (BC-AB-BC-AB) via
    dagger. -/
theorem fourGate_AB_BC_AB_BC_implies_S4_or_S5 (D : DiagGate3)
    (V₁ V₂ V₃ V₄ : Mat4)
    (hV₁ : IsUnitary4 V₁) (hV₂ : IsUnitary4 V₂)
    (hV₃ : IsUnitary4 V₃) (hV₄ : IsUnitary4 V₄)
    (h : D.toMatrix = embedAB V₁ * embedBC V₂ * embedAB V₃ * embedBC V₄) :
    D.inS4 ∨ D.inS5 := by
  rw [← DiagGate3.dagger_inS4_or_S5_iff D]
  have hD' : D.dagger.toMatrix =
      embedBC V₄.conjTranspose * embedAB V₃.conjTranspose *
        embedBC V₂.conjTranspose * embedAB V₁.conjTranspose := by
    rw [DiagGate3.dagger_toMatrix, h]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    rw [embedAB_conjTranspose, embedBC_conjTranspose,
        embedAB_conjTranspose, embedBC_conjTranspose]
    noncomm_ring
  exact fourGate_BC_AB_BC_AB_implies_S4_or_S5 D.dagger
    V₄.conjTranspose V₃.conjTranspose V₂.conjTranspose V₁.conjTranspose
    (isUnitary4_conjTranspose' hV₄) (isUnitary4_conjTranspose' hV₃)
    (isUnitary4_conjTranspose' hV₂) (isUnitary4_conjTranspose' hV₁) hD'

/-- **Theorem 6.2, AC-BC-AC-BC canonical case (#9)**: reduces to #6 (BC-AC-BC-AC) via
    dagger. **All 9 canonical cases now proved!** -/
theorem fourGate_AC_BC_AC_BC_implies_S4_or_S5 (D : DiagGate3)
    (V₁ V₂ V₃ V₄ : Mat4)
    (hV₁ : IsUnitary4 V₁) (hV₂ : IsUnitary4 V₂)
    (hV₃ : IsUnitary4 V₃) (hV₄ : IsUnitary4 V₄)
    (h : D.toMatrix = embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄) :
    D.inS4 ∨ D.inS5 := by
  rw [← DiagGate3.dagger_inS4_or_S5_iff D]
  have hD' : D.dagger.toMatrix =
      embedBC V₄.conjTranspose * embedAC V₃.conjTranspose *
        embedBC V₂.conjTranspose * embedAC V₁.conjTranspose := by
    rw [DiagGate3.dagger_toMatrix, h]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    rw [embedAC_conjTranspose, embedBC_conjTranspose,
        embedAC_conjTranspose, embedBC_conjTranspose]
    noncomm_ring
  exact fourGate_BC_AC_BC_AC_implies_S4_or_S5 D.dagger
    V₄.conjTranspose V₃.conjTranspose V₂.conjTranspose V₁.conjTranspose
    (isUnitary4_conjTranspose' hV₄) (isUnitary4_conjTranspose' hV₃)
    (isUnitary4_conjTranspose' hV₂) (isUnitary4_conjTranspose' hV₁) hD'

/-- Combined: if eigenvalue ratios are tensor product eigenvalues (a,b,p,q),
    then D ∈ S₄ ∨ S₅. This is the core algebraic reduction. -/
theorem S4_or_S5_of_tensor_ratios (D : DiagGate3) (a b p q : ℂ)
    (h₀ : D.d 4 = a * p * D.d 0) (h₁ : D.d 5 = b * p * D.d 1)
    (h₂ : D.d 6 = a * q * D.d 2) (h₃ : D.d 7 = b * q * D.d 3) :
    D.inS4 ∨ D.inS5 := by
  apply S4_or_S5_of_discriminant_zero
  exact s45Discriminant_zero_of_ratio D (a * p) (b * p) (a * q) (b * q) h₀ h₁ h₂ h₃
    (abstractDiscriminant_tensor a b p q)

/-! ## Lemma C.1: Reduction of 4-unrestricted to 9 canonical patterns

Paper's Lemma C.1 (Appendix C, page 29) reduces arbitrary 4-gate products to 9
canonical forms. Our enumeration matches the paper's Theorem 6.2 proof structure
(Theorem 6.1 alternating patterns + 3 detail cases + 3 dagger reverses), differing
slightly from Lemma C.1's exact enumeration on page 29-30 but capturing the same
content modulo SWAP equivalences.

**Proof outline for `unrestrictedCircuit_4_canonical`** (substantial structural
case analysis, currently a black-box):

1. **Inductive structure of `UnrestrictedCircuit 4 Dg.toMatrix`**:
   - Either `weaken : UnrestrictedCircuit 3 → UnrestrictedCircuit 4` (3-gate case
     padded with identity), OR
   - `compose_XY rest V uA uB uC : UnrestrictedCircuit 4 (rest * embedXY V * P)`
     where `XY ∈ {AB, BC, AC}` and `rest : UnrestrictedCircuit 3`.

2. **Recursive decomposition**: each `compose_XY` requires further case-splitting
   on the inner `UnrestrictedCircuit 3`, giving 3⁴ = 81 leaf cases (modulo
   `weaken` collapse).

3. **For each (k₁, k₂, k₃, k₄) ∈ {AB, BC, AC}⁴**, the 4-gate product
   `embed_{k₁} V₁ · P₁ · embed_{k₂} V₂ · P₂ · embed_{k₃} V₃ · P₃ · embed_{k₄} V₄ · P₄`
   is reduced to one of the 9 canonical patterns by:
   - Absorbing product layers Pᵢ into adjacent V's (using existing absorption lemmas).
   - Applying SWAP_BC, SWAP_AC, or SWAP_AB conjugations to permute gate types.

4. **For consecutive same-type gates** (e.g., AB-AB), use `embedAB_mul` to merge,
   reducing to a 3-gate pattern; then handle as a degenerate canonical pattern by
   identity padding.

This requires significant case-by-case work; deferring as a documented black-box. -/

/-- Helper for Lemma C.1: a pure single-qubit layer `singleQubitLayer uA uB uC`
    decomposes into the 4-gate canonical pattern #8 (AB-BC-AB-BC) with
    `V₁ = kron2 uA uB`, `V₂ = kron2 1 uC`, `V₃ = V₄ = 1`. Used by the
    inner-most `weaken` chain (M = product, all gates trivial) of Lemma C.1's
    case analysis. -/
private lemma unrestrictedCircuit_singleQubitLayer_canonical
    (uA uB uC : Mat2) (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC) :
    ∃ V₁ V₂ V₃ V₄ : Mat4,
      IsUnitary4 V₁ ∧ IsUnitary4 V₂ ∧ IsUnitary4 V₃ ∧ IsUnitary4 V₄ ∧
      singleQubitLayer uA uB uC =
        embedAB V₁ * embedBC V₂ * embedAB V₃ * embedBC V₄ := by
  refine ⟨kron2 uA uB, kron2 1 uC, 1, 1,
    isUnitary4_kron2 hA hB,
    isUnitary4_kron2 isUnitary2_one hC,
    isUnitary4_one, isUnitary4_one, ?_⟩
  rw [embedAB_one, embedBC_one, Matrix.mul_one, Matrix.mul_one,
      embedAB_kron2, embedBC_kron2]
  -- Goal: singleQubitLayer uA uB uC = singleQubitLayer uA uB I₂ * singleQubitLayer I₂ I₂ uC
  -- (= kron3 uA uB uC = kron3 (uA·I₂) (uB·I₂) (I₂·uC) by kron3_mul.)
  show kron3 uA uB uC = kron3 uA uB I₂ * kron3 I₂ I₂ uC
  rw [kron3_mul]
  simp [I₂]

/-- Helper for Lemma C.1: a circuit `singleQubitLayer u'A u'B u'C * embedAB V *
    singleQubitLayer uA uB uC` (1 AB gate sandwiched by single-qubit layers)
    decomposes into pattern #8 (AB-BC-AB-BC) with V₃ = V * kron2 uA uB.
    Requires V unitary as explicit hypothesis (NOT given directly by
    `UnrestrictedCircuit`'s compose_AB constructor; would need to be derived
    from Dg.toMatrix being unitary in a future iter). -/
private lemma unrestrictedCircuit_singleAB_canonical
    (V : Mat4) (hV : IsUnitary4 V)
    (u'A u'B u'C : Mat2) (h'A : IsUnitary2 u'A) (h'B : IsUnitary2 u'B) (h'C : IsUnitary2 u'C)
    (uA uB uC : Mat2) (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC) :
    ∃ V₁ V₂ V₃ V₄ : Mat4,
      IsUnitary4 V₁ ∧ IsUnitary4 V₂ ∧ IsUnitary4 V₃ ∧ IsUnitary4 V₄ ∧
      singleQubitLayer u'A u'B u'C * embedAB V * singleQubitLayer uA uB uC =
        embedAB V₁ * embedBC V₂ * embedAB V₃ * embedBC V₄ := by
  refine ⟨kron2 u'A u'B, kron2 1 u'C, V * kron2 uA uB, kron2 1 uC,
    isUnitary4_kron2 h'A h'B,
    isUnitary4_kron2 isUnitary2_one h'C,
    isUnitary4_mul hV (isUnitary4_kron2 hA hB),
    isUnitary4_kron2 isUnitary2_one hC, ?_⟩
  -- Expand both singleQubitLayer factors as embedAB · embedBC.
  have h_left : singleQubitLayer u'A u'B u'C =
      embedAB (kron2 u'A u'B) * embedBC (kron2 1 u'C) := by
    rw [embedAB_kron2, embedBC_kron2]
    show kron3 u'A u'B u'C = kron3 u'A u'B I₂ * kron3 I₂ I₂ u'C
    rw [kron3_mul]; simp [I₂]
  have h_right : singleQubitLayer uA uB uC =
      embedAB (kron2 uA uB) * embedBC (kron2 1 uC) := by
    rw [embedAB_kron2, embedBC_kron2]
    show kron3 uA uB uC = kron3 uA uB I₂ * kron3 I₂ I₂ uC
    rw [kron3_mul]; simp [I₂]
  rw [h_left, h_right]
  -- Goal: (embedAB (kron2 u'A u'B) * embedBC (kron2 1 u'C)) * embedAB V *
  --       (embedAB (kron2 uA uB) * embedBC (kron2 1 uC))
  --       = embedAB (kron2 u'A u'B) * embedBC (kron2 1 u'C) *
  --         embedAB (V * kron2 uA uB) * embedBC (kron2 1 uC)
  rw [show
    embedAB (kron2 u'A u'B) * embedBC (kron2 1 u'C) * embedAB V *
      (embedAB (kron2 uA uB) * embedBC (kron2 1 uC)) =
    embedAB (kron2 u'A u'B) * embedBC (kron2 1 u'C) *
      (embedAB V * embedAB (kron2 uA uB)) * embedBC (kron2 1 uC) from by noncomm_ring]
  rw [embedAB_mul]

/-- Helper for Lemma C.1: 1-BC-gate sandwiched between single-qubit layers
    decomposes into pattern #9 (AC-BC-AC-BC). -/
private lemma unrestrictedCircuit_singleBC_canonical
    (V : Mat4) (hV : IsUnitary4 V)
    (u'A u'B u'C : Mat2) (h'A : IsUnitary2 u'A) (h'B : IsUnitary2 u'B) (h'C : IsUnitary2 u'C)
    (uA uB uC : Mat2) (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC) :
    ∃ V₁ V₂ V₃ V₄ : Mat4,
      IsUnitary4 V₁ ∧ IsUnitary4 V₂ ∧ IsUnitary4 V₃ ∧ IsUnitary4 V₄ ∧
      singleQubitLayer u'A u'B u'C * embedBC V * singleQubitLayer uA uB uC =
        embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄ := by
  refine ⟨kron2 u'A u'C, kron2 u'B 1 * V, kron2 uA uC, kron2 uB 1,
    isUnitary4_kron2 h'A h'C,
    isUnitary4_mul (isUnitary4_kron2 h'B isUnitary2_one) hV,
    isUnitary4_kron2 hA hC,
    isUnitary4_kron2 hB isUnitary2_one, ?_⟩
  -- singleQubitLayer u'A u'B u'C = embedAC (kron2 u'A u'C) · embedBC (kron2 u'B 1).
  have h_left : singleQubitLayer u'A u'B u'C =
      embedAC (kron2 u'A u'C) * embedBC (kron2 u'B 1) := by
    rw [embedAC_kron2, embedBC_kron2]
    show kron3 u'A u'B u'C = kron3 u'A I₂ u'C * kron3 I₂ u'B I₂
    rw [kron3_mul]; simp [I₂]
  have h_right : singleQubitLayer uA uB uC =
      embedAC (kron2 uA uC) * embedBC (kron2 uB 1) := by
    rw [embedAC_kron2, embedBC_kron2]
    show kron3 uA uB uC = kron3 uA I₂ uC * kron3 I₂ uB I₂
    rw [kron3_mul]; simp [I₂]
  rw [h_left, h_right]
  rw [show
    embedAC (kron2 u'A u'C) * embedBC (kron2 u'B 1) * embedBC V *
      (embedAC (kron2 uA uC) * embedBC (kron2 uB 1)) =
    embedAC (kron2 u'A u'C) *
      (embedBC (kron2 u'B 1) * embedBC V) *
      embedAC (kron2 uA uC) * embedBC (kron2 uB 1) from by noncomm_ring]
  rw [embedBC_mul]

/-- Helper for Lemma C.1: 1-AC-gate sandwiched between single-qubit layers
    decomposes into pattern #7 (AB-AC-AB-AC). -/
private lemma unrestrictedCircuit_singleAC_canonical
    (V : Mat4) (hV : IsUnitary4 V)
    (u'A u'B u'C : Mat2) (h'A : IsUnitary2 u'A) (h'B : IsUnitary2 u'B) (h'C : IsUnitary2 u'C)
    (uA uB uC : Mat2) (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC) :
    ∃ V₁ V₂ V₃ V₄ : Mat4,
      IsUnitary4 V₁ ∧ IsUnitary4 V₂ ∧ IsUnitary4 V₃ ∧ IsUnitary4 V₄ ∧
      singleQubitLayer u'A u'B u'C * embedAC V * singleQubitLayer uA uB uC =
        embedAB V₁ * embedAC V₂ * embedAB V₃ * embedAC V₄ := by
  refine ⟨kron2 u'A u'B, kron2 1 u'C * V, kron2 uA uB, kron2 1 uC,
    isUnitary4_kron2 h'A h'B,
    isUnitary4_mul (isUnitary4_kron2 isUnitary2_one h'C) hV,
    isUnitary4_kron2 hA hB,
    isUnitary4_kron2 isUnitary2_one hC, ?_⟩
  -- singleQubitLayer u'A u'B u'C = embedAB (kron2 u'A u'B) · embedAC (kron2 1 u'C).
  have h_left : singleQubitLayer u'A u'B u'C =
      embedAB (kron2 u'A u'B) * embedAC (kron2 1 u'C) := by
    rw [embedAB_kron2, embedAC_kron2]
    show kron3 u'A u'B u'C = kron3 u'A u'B I₂ * kron3 I₂ I₂ u'C
    rw [kron3_mul]; simp [I₂]
  have h_right : singleQubitLayer uA uB uC =
      embedAB (kron2 uA uB) * embedAC (kron2 1 uC) := by
    rw [embedAB_kron2, embedAC_kron2]
    show kron3 uA uB uC = kron3 uA uB I₂ * kron3 I₂ I₂ uC
    rw [kron3_mul]; simp [I₂]
  rw [h_left, h_right]
  rw [show
    embedAB (kron2 u'A u'B) * embedAC (kron2 1 u'C) * embedAC V *
      (embedAB (kron2 uA uB) * embedAC (kron2 1 uC)) =
    embedAB (kron2 u'A u'B) *
      (embedAC (kron2 1 u'C) * embedAC V) *
      embedAB (kron2 uA uB) * embedAC (kron2 1 uC) from by noncomm_ring]
  rw [embedAC_mul]

/-- Algebraic sandwich identity for mixed BC-AB chain. The 5-factor
    chain `SQL u' · embedBC V_BC · SQL u_b · embedAB V_AB · SQL u_t`
    equals the 3-embed form `embedBC V₁' · embedAB V₂' · embedBC V₃'`
    matching pattern #5 (BC-AB-BC-AB) with V₄ = 1.

    Components:
    - V₁' = kron2 u'B u'C · V_BC · kron2 uB_b uC_b
    - V₂' = kron2 (u'A · uA_b) 1 · V_AB · kron2 uA_t uB_t
    - V₃' = kron2 1 uC_t -/
private lemma sandwich_BC_AB_to_BC_AB_BC
    (V_BC V_AB : Mat4)
    (u'A u'B u'C uA_b uB_b uC_b uA_t uB_t uC_t : Mat2) :
    singleQubitLayer u'A u'B u'C * embedBC V_BC *
      singleQubitLayer uA_b uB_b uC_b * embedAB V_AB *
      singleQubitLayer uA_t uB_t uC_t =
    embedBC (kron2 u'B u'C * V_BC * kron2 uB_b uC_b) *
      embedAB (kron2 (u'A * uA_b) 1 * V_AB * kron2 uA_t uB_t) *
      embedBC (kron2 1 uC_t) := by
  -- Step 1: SQL u' · embedBC V_BC = SQL (u'A, I, I) · embedBC (kron2 u'B u'C · V_BC).
  rw [show singleQubitLayer u'A u'B u'C * embedBC V_BC *
            singleQubitLayer uA_b uB_b uC_b * embedAB V_AB *
            singleQubitLayer uA_t uB_t uC_t =
        (singleQubitLayer u'A u'B u'C * embedBC V_BC) *
          singleQubitLayer uA_b uB_b uC_b * embedAB V_AB *
          singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [singleQubitLayer_mul_embedBC]
  -- Goal now has SQL (u'A, I, I) · embedBC (kron2 u'B u'C · V_BC) · SQL u_b · ...
  -- Step 2: absorb SQL u_b into embedBC via embedBC_mul_singleQubitLayer.
  rw [show singleQubitLayer u'A I₂ I₂ * embedBC (kron2 u'B u'C * V_BC) *
            singleQubitLayer uA_b uB_b uC_b * embedAB V_AB *
            singleQubitLayer uA_t uB_t uC_t =
        singleQubitLayer u'A I₂ I₂ *
          (embedBC (kron2 u'B u'C * V_BC) * singleQubitLayer uA_b uB_b uC_b) *
          embedAB V_AB * singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [embedBC_mul_singleQubitLayer]
  -- After Step 2: SQL (u'A, I, I) · embedBC (kron2 u'B u'C · V_BC · kron2 uB_b uC_b)
  --                · SQL (uA_b, I, I) · embedAB V_AB · SQL u_t.
  -- Step 3: commute SQL_A past embedBC.
  rw [show singleQubitLayer u'A I₂ I₂ *
            (embedBC ((kron2 u'B u'C * V_BC) * kron2 uB_b uC_b) *
              singleQubitLayer uA_b I₂ I₂) *
            embedAB V_AB * singleQubitLayer uA_t uB_t uC_t =
        singleQubitLayer u'A I₂ I₂ *
          embedBC ((kron2 u'B u'C * V_BC) * kron2 uB_b uC_b) *
          singleQubitLayer uA_b I₂ I₂ *
          embedAB V_AB * singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [show singleQubitLayer u'A I₂ I₂ *
            embedBC ((kron2 u'B u'C * V_BC) * kron2 uB_b uC_b) =
        embedBC ((kron2 u'B u'C * V_BC) * kron2 uB_b uC_b) *
          singleQubitLayer u'A I₂ I₂ from
      (embedBC_comm_singleQubitLayer_A
        ((kron2 u'B u'C * V_BC) * kron2 uB_b uC_b) u'A).symm]
  -- After Step 3: embedBC X' · SQL (u'A, I, I) · SQL (uA_b, I, I) · embedAB V_AB · SQL u_t.
  rw [show embedBC ((kron2 u'B u'C * V_BC) * kron2 uB_b uC_b) *
            singleQubitLayer u'A I₂ I₂ *
            singleQubitLayer uA_b I₂ I₂ *
            embedAB V_AB * singleQubitLayer uA_t uB_t uC_t =
        embedBC ((kron2 u'B u'C * V_BC) * kron2 uB_b uC_b) *
          (singleQubitLayer u'A I₂ I₂ * singleQubitLayer uA_b I₂ I₂) *
          embedAB V_AB * singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [singleQubitLayer_mul]
  -- After: SQL (u'A · uA_b, I·I, I·I) = SQL (u'A · uA_b, I, I).
  -- Step 4: absorb SQL_A into embedAB.
  rw [show embedBC ((kron2 u'B u'C * V_BC) * kron2 uB_b uC_b) *
            singleQubitLayer (u'A * uA_b) (I₂ * I₂) (I₂ * I₂) *
            embedAB V_AB * singleQubitLayer uA_t uB_t uC_t =
        embedBC ((kron2 u'B u'C * V_BC) * kron2 uB_b uC_b) *
          (singleQubitLayer (u'A * uA_b) (I₂ * I₂) (I₂ * I₂) * embedAB V_AB) *
          singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAB]
  -- After: embedBC X' · (SQL I I (I·I) · embedAB Y) · SQL u_t. Note SQL I I (I·I) = 1.
  -- Step 5: absorb SQL u_t into embedAB via embedAB_mul_singleQubitLayer.
  rw [show embedBC ((kron2 u'B u'C * V_BC) * kron2 uB_b uC_b) *
            (singleQubitLayer I₂ I₂ (I₂ * I₂) *
              embedAB (kron2 (u'A * uA_b) (I₂ * I₂) * V_AB)) *
            singleQubitLayer uA_t uB_t uC_t =
        embedBC ((kron2 u'B u'C * V_BC) * kron2 uB_b uC_b) *
          singleQubitLayer I₂ I₂ (I₂ * I₂) *
          (embedAB (kron2 (u'A * uA_b) (I₂ * I₂) * V_AB) *
            singleQubitLayer uA_t uB_t uC_t) from by noncomm_ring]
  rw [embedAB_mul_singleQubitLayer]
  -- After: ... · SQL I I (I·I) · embedAB ... · SQL (I, I, uC_t).
  -- Step 6: SQL I I (I·I) = 1 (since I·I = I); collapse and replace trailing SQL_C with embedBC.
  rw [show embedBC ((kron2 u'B u'C * V_BC) * kron2 uB_b uC_b) *
            singleQubitLayer I₂ I₂ (I₂ * I₂) *
            (embedAB (kron2 (u'A * uA_b) (I₂ * I₂) * V_AB * kron2 uA_t uB_t) *
              singleQubitLayer I₂ I₂ uC_t) =
        embedBC ((kron2 u'B u'C * V_BC) * kron2 uB_b uC_b) *
          (singleQubitLayer I₂ I₂ (I₂ * I₂)) *
          embedAB (kron2 (u'A * uA_b) (I₂ * I₂) * V_AB * kron2 uA_t uB_t) *
          singleQubitLayer I₂ I₂ uC_t from by noncomm_ring]
  -- Replace SQL (I, I, uC_t) with embedBC (kron2 1 uC_t).
  rw [show singleQubitLayer I₂ I₂ uC_t = embedBC (kron2 1 uC_t) from by
        rw [embedBC_kron2]; rfl]
  -- Replace SQL I I (I·I) with 1 (since I·I = I = 1).
  -- Need to simplify the I₂ * I₂ terms and collapse singleQubitLayer 1 1 1.
  have hSQL_one : (singleQubitLayer (1 : Mat2) 1 1 : Mat8) = 1 := singleQubitLayer_one
  simp only [I₂, mul_one] at *
  rw [hSQL_one]
  noncomm_ring

/-- Mirror of `sandwich_BC_AB_to_BC_AB_BC` for AB-BC chains. Given the 5-factor
    sandwich `SQL u' · embedAB V_AB · SQL u_b · embedBC V_BC · SQL u_t`, derive
    the form `embedAB V₁' · embedBC V₂' · embedAB V₃'` (3-embed AB-BC-AB).

    Strategy mirrors iter-470: absorb SQL components into adjacent embeds,
    using C-only/A-only commutation past mismatched embeds. -/
private lemma sandwich_AB_BC_to_AB_BC_AB
    (V_AB V_BC : Mat4)
    (u'A u'B u'C uA_b uB_b uC_b uA_t uB_t uC_t : Mat2) :
    singleQubitLayer u'A u'B u'C * embedAB V_AB *
      singleQubitLayer uA_b uB_b uC_b * embedBC V_BC *
      singleQubitLayer uA_t uB_t uC_t =
    embedAB (kron2 u'A u'B * V_AB * kron2 uA_b uB_b) *
      embedBC (kron2 1 (u'C * uC_b) * V_BC * kron2 uB_t uC_t) *
      embedAB (kron2 uA_t 1) := by
  -- Step 1: SQL u' · embedAB V_AB → SQL (I, I, u'C) · embedAB (kron2 u'A u'B · V_AB).
  rw [show singleQubitLayer u'A u'B u'C * embedAB V_AB *
            singleQubitLayer uA_b uB_b uC_b * embedBC V_BC *
            singleQubitLayer uA_t uB_t uC_t =
        (singleQubitLayer u'A u'B u'C * embedAB V_AB) *
          singleQubitLayer uA_b uB_b uC_b * embedBC V_BC *
          singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAB]
  -- Step 2: embedAB (kron2 u'A u'B · V_AB) · SQL u_b →
  -- embedAB(...· kron2 uA_b uB_b) · SQL(I, I, uC_b).
  rw [show singleQubitLayer I₂ I₂ u'C * embedAB (kron2 u'A u'B * V_AB) *
            singleQubitLayer uA_b uB_b uC_b * embedBC V_BC *
            singleQubitLayer uA_t uB_t uC_t =
        singleQubitLayer I₂ I₂ u'C *
          (embedAB (kron2 u'A u'B * V_AB) * singleQubitLayer uA_b uB_b uC_b) *
          embedBC V_BC * singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [embedAB_mul_singleQubitLayer]
  -- Step 3: commute SQL(I, I, u'C) past embedAB (C-only commutes with AB).
  rw [show singleQubitLayer I₂ I₂ u'C *
            (embedAB ((kron2 u'A u'B * V_AB) * kron2 uA_b uB_b) *
              singleQubitLayer I₂ I₂ uC_b) *
            embedBC V_BC * singleQubitLayer uA_t uB_t uC_t =
        singleQubitLayer I₂ I₂ u'C *
          embedAB ((kron2 u'A u'B * V_AB) * kron2 uA_b uB_b) *
          singleQubitLayer I₂ I₂ uC_b *
          embedBC V_BC * singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [show singleQubitLayer I₂ I₂ u'C *
            embedAB ((kron2 u'A u'B * V_AB) * kron2 uA_b uB_b) =
        embedAB ((kron2 u'A u'B * V_AB) * kron2 uA_b uB_b) *
          singleQubitLayer I₂ I₂ u'C from
      (embedAB_comm_singleQubitLayer_C
        ((kron2 u'A u'B * V_AB) * kron2 uA_b uB_b) u'C).symm]
  -- Step 4: SQL(I, I, u'C) · SQL(I, I, uC_b) → SQL(I, I, u'C·uC_b). Absorb into embedBC.
  rw [show embedAB ((kron2 u'A u'B * V_AB) * kron2 uA_b uB_b) *
            singleQubitLayer I₂ I₂ u'C *
            singleQubitLayer I₂ I₂ uC_b *
            embedBC V_BC * singleQubitLayer uA_t uB_t uC_t =
        embedAB ((kron2 u'A u'B * V_AB) * kron2 uA_b uB_b) *
          (singleQubitLayer I₂ I₂ u'C * singleQubitLayer I₂ I₂ uC_b) *
          embedBC V_BC * singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [singleQubitLayer_mul]
  -- After: SQL(I·I, I·I, u'C·uC_b). Absorb into embedBC via singleQubitLayer_mul_embedBC.
  rw [show embedAB ((kron2 u'A u'B * V_AB) * kron2 uA_b uB_b) *
            singleQubitLayer (I₂ * I₂) (I₂ * I₂) (u'C * uC_b) *
            embedBC V_BC * singleQubitLayer uA_t uB_t uC_t =
        embedAB ((kron2 u'A u'B * V_AB) * kron2 uA_b uB_b) *
          (singleQubitLayer (I₂ * I₂) (I₂ * I₂) (u'C * uC_b) * embedBC V_BC) *
          singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [singleQubitLayer_mul_embedBC]
  -- Step 5: embedBC(...) · SQL u_t → embedBC(... · kron2 uB_t uC_t) · SQL(uA_t, I, I).
  rw [show embedAB ((kron2 u'A u'B * V_AB) * kron2 uA_b uB_b) *
            (singleQubitLayer (I₂ * I₂) I₂ I₂ *
              embedBC (kron2 (I₂ * I₂) (u'C * uC_b) * V_BC)) *
            singleQubitLayer uA_t uB_t uC_t =
        embedAB ((kron2 u'A u'B * V_AB) * kron2 uA_b uB_b) *
          singleQubitLayer (I₂ * I₂) I₂ I₂ *
          (embedBC (kron2 (I₂ * I₂) (u'C * uC_b) * V_BC) *
            singleQubitLayer uA_t uB_t uC_t) from by noncomm_ring]
  rw [embedBC_mul_singleQubitLayer]
  -- Step 6: SQL(uA_t, I, I) → embedAB(kron2 uA_t 1).
  rw [show singleQubitLayer uA_t I₂ I₂ = embedAB (kron2 uA_t 1) from by
        rw [embedAB_kron2]
        show kron3 uA_t I₂ I₂ = kron3 uA_t (1 : Mat2) I₂
        rw [show (1 : Mat2) = I₂ from rfl]]
  -- Step 7: clean up I₂ * I₂ → 1, collapse SQL 1 1 1 → 1.
  have hSQL_one : (singleQubitLayer (1 : Mat2) 1 1 : Mat8) = 1 := singleQubitLayer_one
  simp only [I₂, mul_one] at *
  rw [hSQL_one]
  noncomm_ring

/-- Sandwich identity for AB-AC mixed chains. Given the 5-factor chain
    `SQL u' · embedAB V_AB · SQL u_b · embedAC V_AC · SQL u_t`, derive the
    3-embed form `embedAB V₁' · embedAC V₂' · embedAB V₃'`.

    Strategy: AB and AC share qubit A. SQL absorption flows through embedAB
    (A,B parts), then C-only commutes past embedAB, combines with C-from-u_b,
    absorbs into embedAC (A,C parts), then B-only trailing → new embedAB. -/
private lemma sandwich_AB_AC_to_AB_AC_AB
    (V_AB V_AC : Mat4)
    (u'A u'B u'C uA_b uB_b uC_b uA_t uB_t uC_t : Mat2) :
    singleQubitLayer u'A u'B u'C * embedAB V_AB *
      singleQubitLayer uA_b uB_b uC_b * embedAC V_AC *
      singleQubitLayer uA_t uB_t uC_t =
    embedAB (kron2 u'A u'B * V_AB * kron2 uA_b uB_b) *
      embedAC (kron2 1 (u'C * uC_b) * V_AC * kron2 uA_t uC_t) *
      embedAB (kron2 1 uB_t) := by
  -- Step 1: SQL u' · embedAB V_AB → SQL(I, I, u'C) · embedAB(kron2 u'A u'B · V_AB).
  rw [show singleQubitLayer u'A u'B u'C * embedAB V_AB *
            singleQubitLayer uA_b uB_b uC_b * embedAC V_AC *
            singleQubitLayer uA_t uB_t uC_t =
        (singleQubitLayer u'A u'B u'C * embedAB V_AB) *
          singleQubitLayer uA_b uB_b uC_b * embedAC V_AC *
          singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAB]
  -- Step 2: embedAB(...) · SQL u_b → embedAB(... · kron2 uA_b uB_b) · SQL(I, I, uC_b).
  rw [show singleQubitLayer I₂ I₂ u'C * embedAB (kron2 u'A u'B * V_AB) *
            singleQubitLayer uA_b uB_b uC_b * embedAC V_AC *
            singleQubitLayer uA_t uB_t uC_t =
        singleQubitLayer I₂ I₂ u'C *
          (embedAB (kron2 u'A u'B * V_AB) * singleQubitLayer uA_b uB_b uC_b) *
          embedAC V_AC * singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [embedAB_mul_singleQubitLayer]
  -- Step 3: commute SQL(I, I, u'C) past embedAB (C-only commutes with AB).
  rw [show singleQubitLayer I₂ I₂ u'C *
            (embedAB ((kron2 u'A u'B * V_AB) * kron2 uA_b uB_b) *
              singleQubitLayer I₂ I₂ uC_b) *
            embedAC V_AC * singleQubitLayer uA_t uB_t uC_t =
        singleQubitLayer I₂ I₂ u'C *
          embedAB ((kron2 u'A u'B * V_AB) * kron2 uA_b uB_b) *
          singleQubitLayer I₂ I₂ uC_b *
          embedAC V_AC * singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [show singleQubitLayer I₂ I₂ u'C *
            embedAB ((kron2 u'A u'B * V_AB) * kron2 uA_b uB_b) =
        embedAB ((kron2 u'A u'B * V_AB) * kron2 uA_b uB_b) *
          singleQubitLayer I₂ I₂ u'C from
      (embedAB_comm_singleQubitLayer_C
        ((kron2 u'A u'B * V_AB) * kron2 uA_b uB_b) u'C).symm]
  -- Step 4: SQL(I, I, u'C) · SQL(I, I, uC_b) → SQL(I, I, u'C·uC_b). Absorb into embedAC.
  rw [show embedAB ((kron2 u'A u'B * V_AB) * kron2 uA_b uB_b) *
            singleQubitLayer I₂ I₂ u'C *
            singleQubitLayer I₂ I₂ uC_b *
            embedAC V_AC * singleQubitLayer uA_t uB_t uC_t =
        embedAB ((kron2 u'A u'B * V_AB) * kron2 uA_b uB_b) *
          (singleQubitLayer I₂ I₂ u'C * singleQubitLayer I₂ I₂ uC_b) *
          embedAC V_AC * singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [singleQubitLayer_mul]
  -- After: SQL(I·I, I·I, u'C·uC_b). Absorb into embedAC via singleQubitLayer_mul_embedAC.
  rw [show embedAB ((kron2 u'A u'B * V_AB) * kron2 uA_b uB_b) *
            singleQubitLayer (I₂ * I₂) (I₂ * I₂) (u'C * uC_b) *
            embedAC V_AC * singleQubitLayer uA_t uB_t uC_t =
        embedAB ((kron2 u'A u'B * V_AB) * kron2 uA_b uB_b) *
          (singleQubitLayer (I₂ * I₂) (I₂ * I₂) (u'C * uC_b) * embedAC V_AC) *
          singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAC]
  -- Step 5: embedAC(...) · SQL u_t → embedAC(... · kron2 uA_t uC_t) · SQL(I, uB_t, I).
  rw [show embedAB ((kron2 u'A u'B * V_AB) * kron2 uA_b uB_b) *
            (singleQubitLayer I₂ (I₂ * I₂) I₂ *
              embedAC (kron2 (I₂ * I₂) (u'C * uC_b) * V_AC)) *
            singleQubitLayer uA_t uB_t uC_t =
        embedAB ((kron2 u'A u'B * V_AB) * kron2 uA_b uB_b) *
          singleQubitLayer I₂ (I₂ * I₂) I₂ *
          (embedAC (kron2 (I₂ * I₂) (u'C * uC_b) * V_AC) *
            singleQubitLayer uA_t uB_t uC_t) from by noncomm_ring]
  rw [embedAC_mul_singleQubitLayer]
  -- Step 6: SQL(I, uB_t, I) → embedAB(kron2 1 uB_t).
  rw [show singleQubitLayer I₂ uB_t I₂ = embedAB (kron2 1 uB_t) from by
        rw [embedAB_kron2]
        show kron3 I₂ uB_t I₂ = kron3 (1 : Mat2) uB_t I₂
        rw [show (1 : Mat2) = I₂ from rfl]]
  -- Step 7: clean up I₂ * I₂ → 1, collapse SQL 1 1 1 → 1.
  have hSQL_one : (singleQubitLayer (1 : Mat2) 1 1 : Mat8) = 1 := singleQubitLayer_one
  simp only [I₂, mul_one] at *
  rw [hSQL_one]
  noncomm_ring

/-- V₂-unitarity extractor for 3-embed BC-AB-BC chain. Given that
    `embedBC V₁ · embedAB V₂ · embedBC V₃` is unitary AND V₁, V₃ are
    unitary, V₂ is unitary. Uses the same "conjugation by unitary
    cancels" pattern as iter-448's `isUnitary4_V_from_chain_AB`,
    but with embedXY factors instead of singleQubitLayer. -/
private lemma isUnitary4_V₂_from_chain_BC_AB_BC
    {V₁ V₂ V₃ : Mat4} (hV₁ : IsUnitary4 V₁) (hV₃ : IsUnitary4 V₃)
    (hM : (embedBC V₁ * embedAB V₂ * embedBC V₃).conjTranspose *
          (embedBC V₁ * embedAB V₂ * embedBC V₃) = (1 : Mat8)) :
    IsUnitary4 V₂ := by
  -- Step 1: surrounding embedXY are unitary.
  have hBC₁_unit : (embedBC V₁).conjTranspose * embedBC V₁ = (1 : Mat8) :=
    embedBC_unitary V₁ hV₁
  have hBC₃_unit : (embedBC V₃).conjTranspose * embedBC V₃ = (1 : Mat8) :=
    embedBC_unitary V₃ hV₃
  have hBC₃_unit_right : embedBC V₃ * (embedBC V₃).conjTranspose = (1 : Mat8) :=
    mul_eq_one_comm.mp hBC₃_unit
  -- Step 2: from hM, derive (embedBC V₃)† · (embedAB V₂)† · embedAB V₂ · embedBC V₃ = 1.
  have hInner : (embedBC V₃).conjTranspose *
                ((embedAB V₂).conjTranspose * embedAB V₂) *
                embedBC V₃ = (1 : Mat8) := by
    have h := hM
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul] at h
    have h_reassoc :
      (embedBC V₃).conjTranspose * ((embedAB V₂).conjTranspose * (embedBC V₁).conjTranspose) *
        (embedBC V₁ * embedAB V₂ * embedBC V₃) =
      (embedBC V₃).conjTranspose *
        ((embedAB V₂).conjTranspose * embedAB V₂) *
        embedBC V₃ +
      (embedBC V₃).conjTranspose * (embedAB V₂).conjTranspose *
        ((embedBC V₁).conjTranspose * embedBC V₁ - 1) *
        embedAB V₂ * embedBC V₃ := by
      noncomm_ring
    rw [h_reassoc, hBC₁_unit, sub_self] at h
    simp at h
    exact h
  -- Step 3: multiply hInner by embedBC V₃ on left, (embedBC V₃)† on right.
  have hEmbed : (embedAB V₂).conjTranspose * embedAB V₂ = (1 : Mat8) := by
    have h := congrArg (fun X => embedBC V₃ * X * (embedBC V₃).conjTranspose) hInner
    simp only at h
    rw [show
      embedBC V₃ *
        ((embedBC V₃).conjTranspose *
          ((embedAB V₂).conjTranspose * embedAB V₂) *
          embedBC V₃) *
        (embedBC V₃).conjTranspose =
      (embedBC V₃ * (embedBC V₃).conjTranspose) *
        ((embedAB V₂).conjTranspose * embedAB V₂) *
        (embedBC V₃ * (embedBC V₃).conjTranspose)
      from by noncomm_ring] at h
    rw [hBC₃_unit_right, one_mul, mul_one] at h
    rw [show
      embedBC V₃ * 1 * (embedBC V₃).conjTranspose =
      embedBC V₃ * (embedBC V₃).conjTranspose
      from by rw [mul_one]] at h
    rw [hBC₃_unit_right] at h
    exact h
  exact isUnitary4_of_embedAB V₂ hEmbed

/-! ## Mixed-XY 2-real-gate closure strategy (DOCUMENTATION for iters 470+)

For mixed-XY chains like `SQL u' · embedBC V_BC · SQL u_b · embedAB V_AB · SQL u_t`,
embedXY_merge does NOT apply (different XYs). Closure strategy:

1. **Cascading absorption**: use `singleQubitLayer_mul_embedBC` /
   `embedBC_mul_singleQubitLayer` (and AB analogs) to migrate SQL
   components into adjacent embed gates, leaving only A-only or
   C-only SQL leftover.
2. **Commutation**: use `embedBC_comm_singleQubitLayer_A` /
   `embedAB_comm_singleQubitLayer_C` to slide the leftover SQL
   components past compatible embed gates.
3. **Trailing absorption**: leftover SQL_C absorbs into a NEW
   embedBC factor via `embedBC_kron2 : embedBC (kron2 Rb Rc) = SQL I Rb Rc`.
   Leftover SQL_A absorbs into a NEW embedBC factor (since BC commutes
   with A-only SQL and embedBC of `kron2 X I` represents A-component).
4. **Final form** for BC-AB chain: `embedBC V₁ · embedAB V₂ · embedBC V₃ · 1`
   matching pattern #5 (BC-AB-BC-AB) with V₄ = 1.

For the unitarity derivation: the V_AB and V_BC components are
INDIVIDUALLY unitary (provably from M unitary + their disjoint
qubit support — embedAB on (A, B), embedBC on (B, C); the only
shared qubit B can't allow non-unitary cancellation in the chain
context). The proof requires a multi-step chain helper analogous
to `isUnitary4_V_from_chain_AB` but for mixed-XY.

**Status**: substantial work (~80-100 Lean lines per leaf, 36 mixed-XY
leaves total). Each (XY₁, XY₂) pair has its specific canonical pattern
target. Iters 470+ tackle this incrementally.
-/

/-- Mixed-XY (3,2) BC-AB leaf canonical-form helper. Given the 5-factor
    sandwich `SQL u' · embedBC V_BC · SQL u_b · embedAB V_AB · SQL u_t`
    with `V_BC, V_AB` BOTH unitary (provided EXPLICITLY — chain unitarity
    alone is insufficient, see iter 472's α-scaling counter-example), produce
    a canonical 4-gate decomposition matching pattern #5 (BC-AB-BC-AB) with
    `V₄ = 1`. Uses iter-470's `sandwich_BC_AB_to_BC_AB_BC` for the algebraic
    identity; unitarity of the V's follows directly from kron2 of unitaries.

    Intended for downstream integration into the direct-proof body of
    `unitaryUnrestrictedCircuit_4_canonical` (mixed-XY (3,2) BC-AB branch). -/
private lemma unitaryCircuit_4_BC_AB_at_3_2_canonical
    (V_BC V_AB : Mat4) (hV_BC : IsUnitary4 V_BC) (hV_AB : IsUnitary4 V_AB)
    (u'A u'B u'C uA_b uB_b uC_b uA_t uB_t uC_t : Mat2)
    (h'A : IsUnitary2 u'A) (h'B : IsUnitary2 u'B) (h'C : IsUnitary2 u'C)
    (hA_b : IsUnitary2 uA_b) (hB_b : IsUnitary2 uB_b) (hC_b : IsUnitary2 uC_b)
    (hA_t : IsUnitary2 uA_t) (hB_t : IsUnitary2 uB_t) (hC_t : IsUnitary2 uC_t) :
    ∃ V₁ V₂ V₃ V₄ : Mat4,
      IsUnitary4 V₁ ∧ IsUnitary4 V₂ ∧ IsUnitary4 V₃ ∧ IsUnitary4 V₄ ∧
      singleQubitLayer u'A u'B u'C * embedBC V_BC *
        singleQubitLayer uA_b uB_b uC_b * embedAB V_AB *
        singleQubitLayer uA_t uB_t uC_t =
      embedBC V₁ * embedAB V₂ * embedBC V₃ * embedAB V₄ := by
  refine ⟨kron2 u'B u'C * V_BC * kron2 uB_b uC_b,
          kron2 (u'A * uA_b) 1 * V_AB * kron2 uA_t uB_t,
          kron2 1 uC_t,
          1, ?_, ?_, ?_, ?_, ?_⟩
  · exact isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h'B h'C) hV_BC)
            (isUnitary4_kron2 hB_b hC_b)
  · exact isUnitary4_mul
            (isUnitary4_mul
              (isUnitary4_kron2 (isUnitary2_mul h'A hA_b) isUnitary2_one) hV_AB)
            (isUnitary4_kron2 hA_t hB_t)
  · exact isUnitary4_kron2 isUnitary2_one hC_t
  · exact isUnitary4_one
  · rw [sandwich_BC_AB_to_BC_AB_BC V_BC V_AB
          u'A u'B u'C uA_b uB_b uC_b uA_t uB_t uC_t,
        embedAB_one, mul_one]

/-- Mirror of `unitaryCircuit_4_BC_AB_at_3_2_canonical` for AB-BC mixed pair.
    Given the 5-factor sandwich `SQL u' · embedAB V_AB · SQL u_b · embedBC V_BC · SQL u_t`
    with V_AB, V_BC both unitary, produce a canonical 4-gate decomposition matching
    pattern #8 (AB-BC-AB-BC) with V₄ = 1.

    Uses `sandwich_AB_BC_to_AB_BC_AB` for the algebraic identity. -/
private lemma unitaryCircuit_4_AB_BC_at_3_2_canonical
    (V_AB V_BC : Mat4) (hV_AB : IsUnitary4 V_AB) (hV_BC : IsUnitary4 V_BC)
    (u'A u'B u'C uA_b uB_b uC_b uA_t uB_t uC_t : Mat2)
    (h'A : IsUnitary2 u'A) (h'B : IsUnitary2 u'B) (h'C : IsUnitary2 u'C)
    (hA_b : IsUnitary2 uA_b) (hB_b : IsUnitary2 uB_b) (hC_b : IsUnitary2 uC_b)
    (hA_t : IsUnitary2 uA_t) (_hB_t : IsUnitary2 uB_t) (_hC_t : IsUnitary2 uC_t) :
    ∃ V₁ V₂ V₃ V₄ : Mat4,
      IsUnitary4 V₁ ∧ IsUnitary4 V₂ ∧ IsUnitary4 V₃ ∧ IsUnitary4 V₄ ∧
      singleQubitLayer u'A u'B u'C * embedAB V_AB *
        singleQubitLayer uA_b uB_b uC_b * embedBC V_BC *
        singleQubitLayer uA_t uB_t uC_t =
      embedAB V₁ * embedBC V₂ * embedAB V₃ * embedBC V₄ := by
  refine ⟨kron2 u'A u'B * V_AB * kron2 uA_b uB_b,
          kron2 1 (u'C * uC_b) * V_BC * kron2 uB_t uC_t,
          kron2 uA_t 1,
          1, ?_, ?_, ?_, ?_, ?_⟩
  · exact isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h'A h'B) hV_AB)
            (isUnitary4_kron2 hA_b hB_b)
  · exact isUnitary4_mul
            (isUnitary4_mul
              (isUnitary4_kron2 isUnitary2_one (isUnitary2_mul h'C hC_b)) hV_BC)
            (isUnitary4_kron2 _hB_t _hC_t)
  · exact isUnitary4_kron2 hA_t isUnitary2_one
  · exact isUnitary4_one
  · rw [sandwich_AB_BC_to_AB_BC_AB V_AB V_BC
          u'A u'B u'C uA_b uB_b uC_b uA_t uB_t uC_t,
        embedBC_one, mul_one]

/-- Mixed-XY (3,2) AB-AC leaf canonical-form helper. Produces canonical 4-gate
    decomposition matching pattern #7 (AB-AC-AB-AC) with V₄ = 1. Uses
    `sandwich_AB_AC_to_AB_AC_AB`. -/
private lemma unitaryCircuit_4_AB_AC_at_3_2_canonical
    (V_AB V_AC : Mat4) (hV_AB : IsUnitary4 V_AB) (hV_AC : IsUnitary4 V_AC)
    (u'A u'B u'C uA_b uB_b uC_b uA_t uB_t uC_t : Mat2)
    (h'A : IsUnitary2 u'A) (h'B : IsUnitary2 u'B) (h'C : IsUnitary2 u'C)
    (hA_b : IsUnitary2 uA_b) (hB_b : IsUnitary2 uB_b) (hC_b : IsUnitary2 uC_b)
    (hA_t : IsUnitary2 uA_t) (hB_t : IsUnitary2 uB_t) (hC_t : IsUnitary2 uC_t) :
    ∃ V₁ V₂ V₃ V₄ : Mat4,
      IsUnitary4 V₁ ∧ IsUnitary4 V₂ ∧ IsUnitary4 V₃ ∧ IsUnitary4 V₄ ∧
      singleQubitLayer u'A u'B u'C * embedAB V_AB *
        singleQubitLayer uA_b uB_b uC_b * embedAC V_AC *
        singleQubitLayer uA_t uB_t uC_t =
      embedAB V₁ * embedAC V₂ * embedAB V₃ * embedAC V₄ := by
  refine ⟨kron2 u'A u'B * V_AB * kron2 uA_b uB_b,
          kron2 1 (u'C * uC_b) * V_AC * kron2 uA_t uC_t,
          kron2 1 uB_t,
          1, ?_, ?_, ?_, ?_, ?_⟩
  · exact isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h'A h'B) hV_AB)
            (isUnitary4_kron2 hA_b hB_b)
  · exact isUnitary4_mul
            (isUnitary4_mul
              (isUnitary4_kron2 isUnitary2_one (isUnitary2_mul h'C hC_b)) hV_AC)
            (isUnitary4_kron2 hA_t hC_t)
  · exact isUnitary4_kron2 isUnitary2_one hB_t
  · exact isUnitary4_one
  · rw [sandwich_AB_AC_to_AB_AC_AB V_AB V_AC
          u'A u'B u'C uA_b uB_b uC_b uA_t uB_t uC_t,
        embedAC_one, mul_one]

/-- Sandwich identity for AC-AB mixed chains. Given the 5-factor chain
    `SQL u' · embedAC V_AC · SQL u_b · embedAB V_AB · SQL u_t`, derive the
    3-embed form `embedAC V₁' · embedAB V₂' · embedAC V₃'`.

    Strategy: AC and AB share qubit A. SQL absorption flows through embedAC
    (A,C parts), then B-only commutes past embedAC, combines with B-from-u_b,
    absorbs into embedAB (A,B parts), then C-only trailing → new embedAC. -/
private lemma sandwich_AC_AB_to_AC_AB_AC
    (V_AC V_AB : Mat4)
    (u'A u'B u'C uA_b uB_b uC_b uA_t uB_t uC_t : Mat2) :
    singleQubitLayer u'A u'B u'C * embedAC V_AC *
      singleQubitLayer uA_b uB_b uC_b * embedAB V_AB *
      singleQubitLayer uA_t uB_t uC_t =
    embedAC (kron2 u'A u'C * V_AC * kron2 uA_b uC_b) *
      embedAB (kron2 1 (u'B * uB_b) * V_AB * kron2 uA_t uB_t) *
      embedAC (kron2 1 uC_t) := by
  -- Step 1: SQL u' · embedAC V_AC → SQL(I, u'B, I) · embedAC(kron2 u'A u'C · V_AC).
  rw [show singleQubitLayer u'A u'B u'C * embedAC V_AC *
            singleQubitLayer uA_b uB_b uC_b * embedAB V_AB *
            singleQubitLayer uA_t uB_t uC_t =
        (singleQubitLayer u'A u'B u'C * embedAC V_AC) *
          singleQubitLayer uA_b uB_b uC_b * embedAB V_AB *
          singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAC]
  -- Step 2: embedAC(...) · SQL u_b → embedAC(... · kron2 uA_b uC_b) · SQL(I, uB_b, I).
  rw [show singleQubitLayer I₂ u'B I₂ * embedAC (kron2 u'A u'C * V_AC) *
            singleQubitLayer uA_b uB_b uC_b * embedAB V_AB *
            singleQubitLayer uA_t uB_t uC_t =
        singleQubitLayer I₂ u'B I₂ *
          (embedAC (kron2 u'A u'C * V_AC) * singleQubitLayer uA_b uB_b uC_b) *
          embedAB V_AB * singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [embedAC_mul_singleQubitLayer]
  -- Step 3: commute SQL(I, u'B, I) past embedAC (B-only commutes with AC).
  rw [show singleQubitLayer I₂ u'B I₂ *
            (embedAC ((kron2 u'A u'C * V_AC) * kron2 uA_b uC_b) *
              singleQubitLayer I₂ uB_b I₂) *
            embedAB V_AB * singleQubitLayer uA_t uB_t uC_t =
        singleQubitLayer I₂ u'B I₂ *
          embedAC ((kron2 u'A u'C * V_AC) * kron2 uA_b uC_b) *
          singleQubitLayer I₂ uB_b I₂ *
          embedAB V_AB * singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [show singleQubitLayer I₂ u'B I₂ *
            embedAC ((kron2 u'A u'C * V_AC) * kron2 uA_b uC_b) =
        embedAC ((kron2 u'A u'C * V_AC) * kron2 uA_b uC_b) *
          singleQubitLayer I₂ u'B I₂ from
      (embedAC_comm_singleQubitLayer_B
        ((kron2 u'A u'C * V_AC) * kron2 uA_b uC_b) u'B).symm]
  -- Step 4: SQL(I, u'B, I) · SQL(I, uB_b, I) → SQL(I, u'B·uB_b, I). Absorb into embedAB.
  rw [show embedAC ((kron2 u'A u'C * V_AC) * kron2 uA_b uC_b) *
            singleQubitLayer I₂ u'B I₂ *
            singleQubitLayer I₂ uB_b I₂ *
            embedAB V_AB * singleQubitLayer uA_t uB_t uC_t =
        embedAC ((kron2 u'A u'C * V_AC) * kron2 uA_b uC_b) *
          (singleQubitLayer I₂ u'B I₂ * singleQubitLayer I₂ uB_b I₂) *
          embedAB V_AB * singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [singleQubitLayer_mul]
  -- After: SQL(I·I, u'B·uB_b, I·I). Absorb into embedAB via singleQubitLayer_mul_embedAB.
  rw [show embedAC ((kron2 u'A u'C * V_AC) * kron2 uA_b uC_b) *
            singleQubitLayer (I₂ * I₂) (u'B * uB_b) (I₂ * I₂) *
            embedAB V_AB * singleQubitLayer uA_t uB_t uC_t =
        embedAC ((kron2 u'A u'C * V_AC) * kron2 uA_b uC_b) *
          (singleQubitLayer (I₂ * I₂) (u'B * uB_b) (I₂ * I₂) * embedAB V_AB) *
          singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAB]
  -- Step 5: embedAB(...) · SQL u_t → embedAB(... · kron2 uA_t uB_t) · SQL(I, I, uC_t).
  rw [show embedAC ((kron2 u'A u'C * V_AC) * kron2 uA_b uC_b) *
            (singleQubitLayer I₂ I₂ (I₂ * I₂) *
              embedAB (kron2 (I₂ * I₂) (u'B * uB_b) * V_AB)) *
            singleQubitLayer uA_t uB_t uC_t =
        embedAC ((kron2 u'A u'C * V_AC) * kron2 uA_b uC_b) *
          singleQubitLayer I₂ I₂ (I₂ * I₂) *
          (embedAB (kron2 (I₂ * I₂) (u'B * uB_b) * V_AB) *
            singleQubitLayer uA_t uB_t uC_t) from by noncomm_ring]
  rw [embedAB_mul_singleQubitLayer]
  -- Step 6: SQL(I, I, uC_t) → embedAC(kron2 1 uC_t).
  rw [show singleQubitLayer I₂ I₂ uC_t = embedAC (kron2 1 uC_t) from by
        rw [embedAC_kron2]
        show kron3 I₂ I₂ uC_t = kron3 (1 : Mat2) I₂ uC_t
        rw [show (1 : Mat2) = I₂ from rfl]]
  -- Step 7: clean up I₂ * I₂ → 1, collapse SQL 1 1 1 → 1.
  have hSQL_one : (singleQubitLayer (1 : Mat2) 1 1 : Mat8) = 1 := singleQubitLayer_one
  simp only [I₂, mul_one] at *
  rw [hSQL_one]
  noncomm_ring

/-- Mixed-XY (3,2) AC-AB leaf canonical-form helper. Produces canonical 4-gate
    decomposition matching pattern #4 (AC-AB-AC-AB) with V₄ = 1. Uses
    `sandwich_AC_AB_to_AC_AB_AC`. -/
private lemma unitaryCircuit_4_AC_AB_at_3_2_canonical
    (V_AC V_AB : Mat4) (hV_AC : IsUnitary4 V_AC) (hV_AB : IsUnitary4 V_AB)
    (u'A u'B u'C uA_b uB_b uC_b uA_t uB_t uC_t : Mat2)
    (h'A : IsUnitary2 u'A) (h'B : IsUnitary2 u'B) (h'C : IsUnitary2 u'C)
    (hA_b : IsUnitary2 uA_b) (hB_b : IsUnitary2 uB_b) (hC_b : IsUnitary2 uC_b)
    (hA_t : IsUnitary2 uA_t) (hB_t : IsUnitary2 uB_t) (hC_t : IsUnitary2 uC_t) :
    ∃ V₁ V₂ V₃ V₄ : Mat4,
      IsUnitary4 V₁ ∧ IsUnitary4 V₂ ∧ IsUnitary4 V₃ ∧ IsUnitary4 V₄ ∧
      singleQubitLayer u'A u'B u'C * embedAC V_AC *
        singleQubitLayer uA_b uB_b uC_b * embedAB V_AB *
        singleQubitLayer uA_t uB_t uC_t =
      embedAC V₁ * embedAB V₂ * embedAC V₃ * embedAB V₄ := by
  refine ⟨kron2 u'A u'C * V_AC * kron2 uA_b uC_b,
          kron2 1 (u'B * uB_b) * V_AB * kron2 uA_t uB_t,
          kron2 1 uC_t,
          1, ?_, ?_, ?_, ?_, ?_⟩
  · exact isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h'A h'C) hV_AC)
            (isUnitary4_kron2 hA_b hC_b)
  · exact isUnitary4_mul
            (isUnitary4_mul
              (isUnitary4_kron2 isUnitary2_one (isUnitary2_mul h'B hB_b)) hV_AB)
            (isUnitary4_kron2 hA_t hB_t)
  · exact isUnitary4_kron2 isUnitary2_one hC_t
  · exact isUnitary4_one
  · rw [sandwich_AC_AB_to_AC_AB_AC V_AC V_AB
          u'A u'B u'C uA_b uB_b uC_b uA_t uB_t uC_t,
        embedAB_one, mul_one]

/-- Sandwich identity for BC-AC mixed chains. Given the 5-factor chain
    `SQL u' · embedBC V_BC · SQL u_b · embedAC V_AC · SQL u_t`, derive the
    3-embed form `embedBC V₁' · embedAC V₂' · embedBC V₃'`. BC and AC share
    qubit C; A-only commutes past embedBC, then absorbs into embedAC. -/
private lemma sandwich_BC_AC_to_BC_AC_BC
    (V_BC V_AC : Mat4)
    (u'A u'B u'C uA_b uB_b uC_b uA_t uB_t uC_t : Mat2) :
    singleQubitLayer u'A u'B u'C * embedBC V_BC *
      singleQubitLayer uA_b uB_b uC_b * embedAC V_AC *
      singleQubitLayer uA_t uB_t uC_t =
    embedBC (kron2 u'B u'C * V_BC * kron2 uB_b uC_b) *
      embedAC (kron2 (u'A * uA_b) 1 * V_AC * kron2 uA_t uC_t) *
      embedBC (kron2 uB_t 1) := by
  rw [show singleQubitLayer u'A u'B u'C * embedBC V_BC *
            singleQubitLayer uA_b uB_b uC_b * embedAC V_AC *
            singleQubitLayer uA_t uB_t uC_t =
        (singleQubitLayer u'A u'B u'C * embedBC V_BC) *
          singleQubitLayer uA_b uB_b uC_b * embedAC V_AC *
          singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [singleQubitLayer_mul_embedBC]
  rw [show singleQubitLayer u'A I₂ I₂ * embedBC (kron2 u'B u'C * V_BC) *
            singleQubitLayer uA_b uB_b uC_b * embedAC V_AC *
            singleQubitLayer uA_t uB_t uC_t =
        singleQubitLayer u'A I₂ I₂ *
          (embedBC (kron2 u'B u'C * V_BC) * singleQubitLayer uA_b uB_b uC_b) *
          embedAC V_AC * singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [embedBC_mul_singleQubitLayer]
  rw [show singleQubitLayer u'A I₂ I₂ *
            (embedBC ((kron2 u'B u'C * V_BC) * kron2 uB_b uC_b) *
              singleQubitLayer uA_b I₂ I₂) *
            embedAC V_AC * singleQubitLayer uA_t uB_t uC_t =
        singleQubitLayer u'A I₂ I₂ *
          embedBC ((kron2 u'B u'C * V_BC) * kron2 uB_b uC_b) *
          singleQubitLayer uA_b I₂ I₂ *
          embedAC V_AC * singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [show singleQubitLayer u'A I₂ I₂ *
            embedBC ((kron2 u'B u'C * V_BC) * kron2 uB_b uC_b) =
        embedBC ((kron2 u'B u'C * V_BC) * kron2 uB_b uC_b) *
          singleQubitLayer u'A I₂ I₂ from
      (embedBC_comm_singleQubitLayer_A
        ((kron2 u'B u'C * V_BC) * kron2 uB_b uC_b) u'A).symm]
  rw [show embedBC ((kron2 u'B u'C * V_BC) * kron2 uB_b uC_b) *
            singleQubitLayer u'A I₂ I₂ *
            singleQubitLayer uA_b I₂ I₂ *
            embedAC V_AC * singleQubitLayer uA_t uB_t uC_t =
        embedBC ((kron2 u'B u'C * V_BC) * kron2 uB_b uC_b) *
          (singleQubitLayer u'A I₂ I₂ * singleQubitLayer uA_b I₂ I₂) *
          embedAC V_AC * singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [singleQubitLayer_mul]
  rw [show embedBC ((kron2 u'B u'C * V_BC) * kron2 uB_b uC_b) *
            singleQubitLayer (u'A * uA_b) (I₂ * I₂) (I₂ * I₂) *
            embedAC V_AC * singleQubitLayer uA_t uB_t uC_t =
        embedBC ((kron2 u'B u'C * V_BC) * kron2 uB_b uC_b) *
          (singleQubitLayer (u'A * uA_b) (I₂ * I₂) (I₂ * I₂) * embedAC V_AC) *
          singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAC]
  rw [show embedBC ((kron2 u'B u'C * V_BC) * kron2 uB_b uC_b) *
            (singleQubitLayer I₂ (I₂ * I₂) I₂ *
              embedAC (kron2 (u'A * uA_b) (I₂ * I₂) * V_AC)) *
            singleQubitLayer uA_t uB_t uC_t =
        embedBC ((kron2 u'B u'C * V_BC) * kron2 uB_b uC_b) *
          singleQubitLayer I₂ (I₂ * I₂) I₂ *
          (embedAC (kron2 (u'A * uA_b) (I₂ * I₂) * V_AC) *
            singleQubitLayer uA_t uB_t uC_t) from by noncomm_ring]
  rw [embedAC_mul_singleQubitLayer]
  rw [show singleQubitLayer I₂ uB_t I₂ = embedBC (kron2 uB_t 1) from by
        rw [embedBC_kron2]
        show kron3 I₂ uB_t I₂ = kron3 I₂ uB_t (1 : Mat2)
        rw [show (1 : Mat2) = I₂ from rfl]]
  have hSQL_one : (singleQubitLayer (1 : Mat2) 1 1 : Mat8) = 1 := singleQubitLayer_one
  simp only [I₂, mul_one] at *
  rw [hSQL_one]
  noncomm_ring

/-- Mixed-XY (3,2) BC-AC leaf canonical-form helper. Pattern #6 (BC-AC-BC-AC)
    with V₄ = 1. Uses `sandwich_BC_AC_to_BC_AC_BC`. -/
private lemma unitaryCircuit_4_BC_AC_at_3_2_canonical
    (V_BC V_AC : Mat4) (hV_BC : IsUnitary4 V_BC) (hV_AC : IsUnitary4 V_AC)
    (u'A u'B u'C uA_b uB_b uC_b uA_t uB_t uC_t : Mat2)
    (h'A : IsUnitary2 u'A) (h'B : IsUnitary2 u'B) (h'C : IsUnitary2 u'C)
    (hA_b : IsUnitary2 uA_b) (hB_b : IsUnitary2 uB_b) (hC_b : IsUnitary2 uC_b)
    (hA_t : IsUnitary2 uA_t) (hB_t : IsUnitary2 uB_t) (hC_t : IsUnitary2 uC_t) :
    ∃ V₁ V₂ V₃ V₄ : Mat4,
      IsUnitary4 V₁ ∧ IsUnitary4 V₂ ∧ IsUnitary4 V₃ ∧ IsUnitary4 V₄ ∧
      singleQubitLayer u'A u'B u'C * embedBC V_BC *
        singleQubitLayer uA_b uB_b uC_b * embedAC V_AC *
        singleQubitLayer uA_t uB_t uC_t =
      embedBC V₁ * embedAC V₂ * embedBC V₃ * embedAC V₄ := by
  refine ⟨kron2 u'B u'C * V_BC * kron2 uB_b uC_b,
          kron2 (u'A * uA_b) 1 * V_AC * kron2 uA_t uC_t,
          kron2 uB_t 1,
          1, ?_, ?_, ?_, ?_, ?_⟩
  · exact isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h'B h'C) hV_BC)
            (isUnitary4_kron2 hB_b hC_b)
  · exact isUnitary4_mul
            (isUnitary4_mul
              (isUnitary4_kron2 (isUnitary2_mul h'A hA_b) isUnitary2_one) hV_AC)
            (isUnitary4_kron2 hA_t hC_t)
  · exact isUnitary4_kron2 hB_t isUnitary2_one
  · exact isUnitary4_one
  · rw [sandwich_BC_AC_to_BC_AC_BC V_BC V_AC
          u'A u'B u'C uA_b uB_b uC_b uA_t uB_t uC_t,
        embedAC_one, mul_one]

set_option maxHeartbeats 800000 in
/-- Sandwich identity for AC-BC mixed chains. Given the 5-factor chain
    `SQL u' · embedAC V_AC · SQL u_b · embedBC V_BC · SQL u_t`, derive the
    3-embed form `embedAC V₁' · embedBC V₂' · embedAC V₃'`. AC and BC share
    qubit C; B-only commutes past embedAC, then absorbs into embedBC. -/
private lemma sandwich_AC_BC_to_AC_BC_AC
    (V_AC V_BC : Mat4)
    (u'A u'B u'C uA_b uB_b uC_b uA_t uB_t uC_t : Mat2) :
    singleQubitLayer u'A u'B u'C * embedAC V_AC *
      singleQubitLayer uA_b uB_b uC_b * embedBC V_BC *
      singleQubitLayer uA_t uB_t uC_t =
    embedAC (kron2 u'A u'C * V_AC * kron2 uA_b uC_b) *
      embedBC (kron2 (u'B * uB_b) 1 * V_BC * kron2 uB_t uC_t) *
      embedAC (kron2 uA_t 1) := by
  rw [show singleQubitLayer u'A u'B u'C * embedAC V_AC *
            singleQubitLayer uA_b uB_b uC_b * embedBC V_BC *
            singleQubitLayer uA_t uB_t uC_t =
        (singleQubitLayer u'A u'B u'C * embedAC V_AC) *
          singleQubitLayer uA_b uB_b uC_b * embedBC V_BC *
          singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAC]
  rw [show singleQubitLayer I₂ u'B I₂ * embedAC (kron2 u'A u'C * V_AC) *
            singleQubitLayer uA_b uB_b uC_b * embedBC V_BC *
            singleQubitLayer uA_t uB_t uC_t =
        singleQubitLayer I₂ u'B I₂ *
          (embedAC (kron2 u'A u'C * V_AC) * singleQubitLayer uA_b uB_b uC_b) *
          embedBC V_BC * singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [embedAC_mul_singleQubitLayer]
  rw [show singleQubitLayer I₂ u'B I₂ *
            (embedAC ((kron2 u'A u'C * V_AC) * kron2 uA_b uC_b) *
              singleQubitLayer I₂ uB_b I₂) *
            embedBC V_BC * singleQubitLayer uA_t uB_t uC_t =
        singleQubitLayer I₂ u'B I₂ *
          embedAC ((kron2 u'A u'C * V_AC) * kron2 uA_b uC_b) *
          singleQubitLayer I₂ uB_b I₂ *
          embedBC V_BC * singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [show singleQubitLayer I₂ u'B I₂ *
            embedAC ((kron2 u'A u'C * V_AC) * kron2 uA_b uC_b) =
        embedAC ((kron2 u'A u'C * V_AC) * kron2 uA_b uC_b) *
          singleQubitLayer I₂ u'B I₂ from
      (embedAC_comm_singleQubitLayer_B
        ((kron2 u'A u'C * V_AC) * kron2 uA_b uC_b) u'B).symm]
  rw [show embedAC ((kron2 u'A u'C * V_AC) * kron2 uA_b uC_b) *
            singleQubitLayer I₂ u'B I₂ *
            singleQubitLayer I₂ uB_b I₂ *
            embedBC V_BC * singleQubitLayer uA_t uB_t uC_t =
        embedAC ((kron2 u'A u'C * V_AC) * kron2 uA_b uC_b) *
          (singleQubitLayer I₂ u'B I₂ * singleQubitLayer I₂ uB_b I₂) *
          embedBC V_BC * singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [singleQubitLayer_mul]
  rw [show embedAC ((kron2 u'A u'C * V_AC) * kron2 uA_b uC_b) *
            singleQubitLayer (I₂ * I₂) (u'B * uB_b) (I₂ * I₂) *
            embedBC V_BC * singleQubitLayer uA_t uB_t uC_t =
        embedAC ((kron2 u'A u'C * V_AC) * kron2 uA_b uC_b) *
          (singleQubitLayer (I₂ * I₂) (u'B * uB_b) (I₂ * I₂) * embedBC V_BC) *
          singleQubitLayer uA_t uB_t uC_t from by noncomm_ring]
  rw [singleQubitLayer_mul_embedBC]
  rw [show embedAC ((kron2 u'A u'C * V_AC) * kron2 uA_b uC_b) *
            (singleQubitLayer (I₂ * I₂) I₂ I₂ *
              embedBC (kron2 (u'B * uB_b) (I₂ * I₂) * V_BC)) *
            singleQubitLayer uA_t uB_t uC_t =
        embedAC ((kron2 u'A u'C * V_AC) * kron2 uA_b uC_b) *
          singleQubitLayer (I₂ * I₂) I₂ I₂ *
          (embedBC (kron2 (u'B * uB_b) (I₂ * I₂) * V_BC) *
            singleQubitLayer uA_t uB_t uC_t) from by noncomm_ring]
  rw [embedBC_mul_singleQubitLayer]
  rw [show singleQubitLayer uA_t I₂ I₂ = embedAC (kron2 uA_t 1) from by
        rw [embedAC_kron2]
        show kron3 uA_t I₂ I₂ = kron3 uA_t I₂ (1 : Mat2)
        rw [show (1 : Mat2) = I₂ from rfl]]
  have hSQL_one : (singleQubitLayer (1 : Mat2) 1 1 : Mat8) = 1 := singleQubitLayer_one
  simp only [I₂, mul_one] at *
  rw [hSQL_one]
  noncomm_ring

/-- Mixed-XY (3,2) AC-BC leaf canonical-form helper. Pattern #9 (AC-BC-AC-BC)
    with V₄ = 1. Uses `sandwich_AC_BC_to_AC_BC_AC`. -/
private lemma unitaryCircuit_4_AC_BC_at_3_2_canonical
    (V_AC V_BC : Mat4) (hV_AC : IsUnitary4 V_AC) (hV_BC : IsUnitary4 V_BC)
    (u'A u'B u'C uA_b uB_b uC_b uA_t uB_t uC_t : Mat2)
    (h'A : IsUnitary2 u'A) (h'B : IsUnitary2 u'B) (h'C : IsUnitary2 u'C)
    (hA_b : IsUnitary2 uA_b) (hB_b : IsUnitary2 uB_b) (hC_b : IsUnitary2 uC_b)
    (hA_t : IsUnitary2 uA_t) (hB_t : IsUnitary2 uB_t) (hC_t : IsUnitary2 uC_t) :
    ∃ V₁ V₂ V₃ V₄ : Mat4,
      IsUnitary4 V₁ ∧ IsUnitary4 V₂ ∧ IsUnitary4 V₃ ∧ IsUnitary4 V₄ ∧
      singleQubitLayer u'A u'B u'C * embedAC V_AC *
        singleQubitLayer uA_b uB_b uC_b * embedBC V_BC *
        singleQubitLayer uA_t uB_t uC_t =
      embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄ := by
  refine ⟨kron2 u'A u'C * V_AC * kron2 uA_b uC_b,
          kron2 (u'B * uB_b) 1 * V_BC * kron2 uB_t uC_t,
          kron2 uA_t 1,
          1, ?_, ?_, ?_, ?_, ?_⟩
  · exact isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h'A h'C) hV_AC)
            (isUnitary4_kron2 hA_b hC_b)
  · exact isUnitary4_mul
            (isUnitary4_mul
              (isUnitary4_kron2 (isUnitary2_mul h'B hB_b) isUnitary2_one) hV_BC)
            (isUnitary4_kron2 hB_t hC_t)
  · exact isUnitary4_kron2 hA_t isUnitary2_one
  · exact isUnitary4_one
  · rw [sandwich_AC_BC_to_AC_BC_AC V_AC V_BC
          u'A u'B u'C uA_b uB_b uC_b uA_t uB_t uC_t,
        embedBC_one, mul_one]

/-! ## 3-XY 3-real-embed dispatcher gap (iter 729-731 finding)

The 31 remaining sorries in `unitaryUnrestrictedCircuit_4_canonical_direct`
are 3-XY 3-real-embed chains. Existing 3-XY sandwiches handle 3 of 6
{AB,BC,AC} orderings:
- `sandwich_AB_BC_AC_to_4embed` → pattern #2 (AB-BC-AC-AB).
- `sandwich_BC_AC_AB_to_4embed` → pattern #1 (BC-AC-AB-BC).
- `sandwich_AC_BC_AB_to_4embed` → pattern #3 (AC-BC-AB-AC).

In each, output's leading XY equals trailing XY (the chain extension
lies in a canonical pattern). The 3 missing orderings — AC-AB-BC,
BC-AB-AC, AB-AC-BC — extend to AC-AB-BC-AC etc., but NONE of the 9
canonical patterns has form XY₁-XY₂-XY₃-XY₁ for those XY₁/XY₃
combinations. Cataloging extensions:
- AC-AB-BC-AC: not a pattern (#3 is AC-BC-AB-AC, #4 is AC-AB-AC-AB).
- BC-AB-AC-BC: not a pattern (#1 is BC-AC-AB-BC, #5 is BC-AB-BC-AB).
- AB-AC-BC-AB: not a pattern (#2 is AB-BC-AC-AB, #7 is AB-AC-AB-AC).

So a direct sandwich → canonical-pattern path doesn't exist for these
chains. **Iter 731 hypothesized** that SWAP_AC conjugation maps the 3
missing orderings to the 3 covered orderings (since SWAP_AC: embedAB
↔ embedBC, embedAC fixed):
- AC-AB-BC →(SWAP_AC)→ AC-BC-AB.
- BC-AB-AC →(SWAP_AC)→ AB-BC-AC.
- AB-AC-BC →(SWAP_AC)→ BC-AC-AB.

This led to building SWAP_AC infrastructure (iters 733-735):
`swap_ac_unitaryUnrestrictedCircuit`, `swap_ac_unitaryUnrestricted_DiagGate3`,
and `four_unitaryUnrestricted_implies_S4_or_S5_via_swap_AC`.

**Iter 736 finding**: the bypass DOES NOT close canonical_direct's
sorries. canonical_direct's signature returns a 4-V canonical form,
and SWAP-back of canonical patterns yields non-canonical chains
(e.g., SWAP-back of pattern #3 = AC-AB-BC-AC, which is not one of
the 9 patterns). So even with the SWAP infrastructure, canonical_direct
still has the same 31 sorries.

The iter 735 `_via_swap_AC` entry point routes through the same
dispatcher (with the 31 sorries propagating); calling it on a
missing-ordering Dg internally calls `four_unitaryUnrestricted_implies_S4_or_S5
Dg.swapAC` which calls canonical_direct on swapAC(Dg) — and even
though the case tree for swapAC(Dg) hits a covered leaf at runtime,
the sorries elsewhere in canonical_direct's case tree still mean the
theorem propositionally has those sorries propagated.

**Closure path remains**: paper Lemma C.1's full case analysis (multi-
week, ~600-900 lines) or accept the 31 sorries as paper-cited
black-boxes. The SWAP infrastructure (iters 733-735) is useful only
if a different dispatcher returning S₄∪S₅ directly (without 4-V
canonical) is later written.

The SQL-decomposition primitives added iters 724-727 remain
foundational infrastructure (useful when the multi-week work is
undertaken). They are NOT used in any current proof — saved for the
future. -/

/-! ## Triple-merge sandwich identities for 3-real-gate same-XY chains

For a 7-factor chain `SQL · embedXY V₁ · SQL · embedXY V₂ · SQL · embedXY V₃ · SQL`,
two applications of `embedXY_merge` collapse the three embeds into a single
`embedXY` of `V₁ · (kron2 a b · V₂) · (kron2 a' b' · V₃)`. The merged outer
SQL absorbs the inter-gate SQL contributions on the appropriate qubit
(C for AB, A for BC, B for AC). -/

private lemma sandwich_AB_AB_AB_to_AB
    (V₁ V₂ V₃ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA u_pB ((u_pC * u₁C) * u₂C) *
      embedAB (V₁ * (kron2 u₁A u₁B * V₂) * (kron2 u₂A u₂B * V₃)) *
      singleQubitLayer u'A u'B u'C := by
  rw [show singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
            singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
            singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
            singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA u_pB u_pC *
          (embedAB V₁ * singleQubitLayer u₁A u₁B u₁C * embedAB V₂) *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAB_merge]
  rw [show singleQubitLayer u_pA u_pB u_pC *
            (singleQubitLayer I₂ I₂ u₁C *
              embedAB (V₁ * (kron2 u₁A u₁B * V₂))) *
            singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
            singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC *
           singleQubitLayer I₂ I₂ u₁C) *
          (embedAB (V₁ * (kron2 u₁A u₁B * V₂)) *
            singleQubitLayer u₂A u₂B u₂C * embedAB V₃) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul]
  rw [embedAB_merge]
  rw [show singleQubitLayer (u_pA * I₂) (u_pB * I₂) (u_pC * u₁C) *
            (singleQubitLayer I₂ I₂ u₂C *
              embedAB (V₁ * (kron2 u₁A u₁B * V₂) * (kron2 u₂A u₂B * V₃))) *
            singleQubitLayer u'A u'B u'C =
        (singleQubitLayer (u_pA * I₂) (u_pB * I₂) (u_pC * u₁C) *
           singleQubitLayer I₂ I₂ u₂C) *
          embedAB (V₁ * (kron2 u₁A u₁B * V₂) * (kron2 u₂A u₂B * V₃)) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul]
  simp [I₂]

private lemma sandwich_BC_BC_BC_to_BC
    (V₁ V₂ V₃ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer ((u_pA * u₁A) * u₂A) u_pB u_pC *
      embedBC (V₁ * (kron2 u₁B u₁C * V₂) * (kron2 u₂B u₂C * V₃)) *
      singleQubitLayer u'A u'B u'C := by
  rw [show singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
            singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
            singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
            singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA u_pB u_pC *
          (embedBC V₁ * singleQubitLayer u₁A u₁B u₁C * embedBC V₂) *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedBC_merge]
  rw [show singleQubitLayer u_pA u_pB u_pC *
            (singleQubitLayer u₁A I₂ I₂ *
              embedBC (V₁ * (kron2 u₁B u₁C * V₂))) *
            singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
            singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC *
           singleQubitLayer u₁A I₂ I₂) *
          (embedBC (V₁ * (kron2 u₁B u₁C * V₂)) *
            singleQubitLayer u₂A u₂B u₂C * embedBC V₃) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul]
  rw [embedBC_merge]
  rw [show singleQubitLayer (u_pA * u₁A) (u_pB * I₂) (u_pC * I₂) *
            (singleQubitLayer u₂A I₂ I₂ *
              embedBC (V₁ * (kron2 u₁B u₁C * V₂) * (kron2 u₂B u₂C * V₃))) *
            singleQubitLayer u'A u'B u'C =
        (singleQubitLayer (u_pA * u₁A) (u_pB * I₂) (u_pC * I₂) *
           singleQubitLayer u₂A I₂ I₂) *
          embedBC (V₁ * (kron2 u₁B u₁C * V₂) * (kron2 u₂B u₂C * V₃)) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul]
  simp [I₂]

/-- 4-BC triple-merge sandwich: 4 consecutive BC gates with 5 SQLs collapse
    to a single embedBC sandwich. Proved iter 580 via sandwich_BC_BC_BC_to_BC
    + embedBC_merge composition. -/
private lemma sandwich_BC_BC_BC_BC_to_BC
    (V₁ V₂ V₃ V₄ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
      singleQubitLayer u₃A u₃B u₃C * embedBC V₄ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer (((u_pA * u₁A) * u₂A) * u₃A) u_pB u_pC *
      embedBC (V₁ * (kron2 u₁B u₁C * V₂) * (kron2 u₂B u₂C * V₃) *
        (kron2 u₃B u₃C * V₄)) *
      singleQubitLayer u'A u'B u'C := by
  -- Step 1: Re-bracket so first 7 factors form a 3-BC chain.
  rw [show
        singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u₃A u₃B u₃C * embedBC V₄ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u₃A u₃B u₃C) *
          embedBC V₄ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [sandwich_BC_BC_BC_to_BC V₁ V₂ V₃
        u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C]
  -- Step 2: Apply embedBC_merge to combine the resulting embedBC with V₄.
  rw [show
        singleQubitLayer ((u_pA * u₁A) * u₂A) u_pB u_pC *
          embedBC (V₁ * (kron2 u₁B u₁C * V₂) * (kron2 u₂B u₂C * V₃)) *
          singleQubitLayer u₃A u₃B u₃C *
          embedBC V₄ *
          singleQubitLayer u'A u'B u'C =
        singleQubitLayer ((u_pA * u₁A) * u₂A) u_pB u_pC *
          (embedBC (V₁ * (kron2 u₁B u₁C * V₂) * (kron2 u₂B u₂C * V₃)) *
            singleQubitLayer u₃A u₃B u₃C *
            embedBC V₄) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedBC_merge (V₁ * (kron2 u₁B u₁C * V₂) * (kron2 u₂B u₂C * V₃)) V₄
        u₃A u₃B u₃C]
  -- Step 3: Combine the two SQLs at the front.
  rw [show
        singleQubitLayer ((u_pA * u₁A) * u₂A) u_pB u_pC *
          (singleQubitLayer u₃A I₂ I₂ *
            embedBC ((V₁ * (kron2 u₁B u₁C * V₂) * (kron2 u₂B u₂C * V₃)) *
              (kron2 u₃B u₃C * V₄))) *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer ((u_pA * u₁A) * u₂A) u_pB u_pC *
          singleQubitLayer u₃A I₂ I₂) *
          embedBC ((V₁ * (kron2 u₁B u₁C * V₂) * (kron2 u₂B u₂C * V₃)) *
            (kron2 u₃B u₃C * V₄)) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul ((u_pA * u₁A) * u₂A) u_pB u_pC u₃A I₂ I₂]
  -- Final: simplify u_pB*I → u_pB, u_pC*I → u_pC.
  show _ = _
  simp only [I₂, mul_one]

/-- 4-AB triple-merge sandwich: 4 consecutive AB gates with 5 SQLs collapse
    to a single embedAB sandwich. Proved iter 578 via sandwich_AB_AB_AB_to_AB
    + embedAB_merge composition. -/
private lemma sandwich_AB_AB_AB_AB_to_AB
    (V₁ V₂ V₃ V₄ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
      singleQubitLayer u₃A u₃B u₃C * embedAB V₄ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA u_pB (((u_pC * u₁C) * u₂C) * u₃C) *
      embedAB (V₁ * (kron2 u₁A u₁B * V₂) * (kron2 u₂A u₂B * V₃) *
        (kron2 u₃A u₃B * V₄)) *
      singleQubitLayer u'A u'B u'C := by
  -- Step 1: Re-bracket so first 7 factors form a 3-AB chain.
  rw [show
        singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u₃A u₃B u₃C * embedAB V₄ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u₃A u₃B u₃C) *
          embedAB V₄ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [sandwich_AB_AB_AB_to_AB V₁ V₂ V₃
        u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C]
  -- Now LHS = SQL u_pA u_pB ((u_pC*u₁C)*u₂C) * embedAB(V₁ * (kron2 u₁A u₁B * V₂) *
  --   (kron2 u₂A u₂B * V₃)) * SQL u₃A u₃B u₃C * embedAB V₄ * SQL u'A u'B u'C.
  -- Step 2: Apply embedAB_merge to combine the resulting embedAB with V₄.
  rw [show
        singleQubitLayer u_pA u_pB ((u_pC * u₁C) * u₂C) *
          embedAB (V₁ * (kron2 u₁A u₁B * V₂) * (kron2 u₂A u₂B * V₃)) *
          singleQubitLayer u₃A u₃B u₃C *
          embedAB V₄ *
          singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA u_pB ((u_pC * u₁C) * u₂C) *
          (embedAB (V₁ * (kron2 u₁A u₁B * V₂) * (kron2 u₂A u₂B * V₃)) *
            singleQubitLayer u₃A u₃B u₃C *
            embedAB V₄) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAB_merge (V₁ * (kron2 u₁A u₁B * V₂) * (kron2 u₂A u₂B * V₃)) V₄
        u₃A u₃B u₃C]
  -- Now LHS = SQL u_pA u_pB ((u_pC*u₁C)*u₂C) * (SQL I I u₃C * embedAB(merged_4)) * SQL u'.
  -- Step 3: Combine the two SQLs at the front.
  rw [show
        singleQubitLayer u_pA u_pB ((u_pC * u₁C) * u₂C) *
          (singleQubitLayer I₂ I₂ u₃C *
            embedAB ((V₁ * (kron2 u₁A u₁B * V₂) * (kron2 u₂A u₂B * V₃)) *
              (kron2 u₃A u₃B * V₄))) *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB ((u_pC * u₁C) * u₂C) *
          singleQubitLayer I₂ I₂ u₃C) *
          embedAB ((V₁ * (kron2 u₁A u₁B * V₂) * (kron2 u₂A u₂B * V₃)) *
            (kron2 u₃A u₃B * V₄)) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul u_pA u_pB ((u_pC * u₁C) * u₂C) I₂ I₂ u₃C]
  -- Final: simplify u_pA*I → u_pA, u_pB*I → u_pB.
  show _ = _
  simp only [I₂, mul_one]

/-! ### Non-adjacent-same sandwich identities

For a 7-factor 3-real-gate chain `SQL · embedX V₁ · SQL · embedY V₂ · SQL · embedX V₃ · SQL`
where V₁ and V₃ are X but V₂ is Y (different), the chain CANNOT be merged
via a single `embedXY_merge`. Instead, all SQLs are absorbed into the V's,
producing a 4-embed canonical form `embedX W₁ · embedY W₂ · embedX W₃ · embedY W₄`. -/

set_option maxHeartbeats 400000 in
/-- Non-adjacent-same sandwich identity for AB-BC-AB pattern.
    Proved iter 566 via 8-step cascading absorption. -/
private lemma sandwich_AB_BC_AB_to_4embed
    (V₁ V₂ V₃ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
      singleQubitLayer u'A u'B u'C =
    embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
      embedBC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
      embedAB (kron2 u₂A 1 * V₃ * kron2 u'A u'B) *
      embedBC (kron2 1 u'C) := by
  -- Step 1: absorb leading SQL into embedAB V₁ from left.
  rw [show
        singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC * embedAB V₁) *
          singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAB u_pA u_pB u_pC V₁]
  -- Step 2: absorb SQL₁ into embedAB(...) from right.
  rw [show
        singleQubitLayer I₂ I₂ u_pC * embedAB (kron2 u_pA u_pB * V₁) *
          singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        singleQubitLayer I₂ I₂ u_pC *
          (embedAB (kron2 u_pA u_pB * V₁) * singleQubitLayer u₁A u₁B u₁C) *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAB_mul_singleQubitLayer (kron2 u_pA u_pB * V₁) u₁A u₁B u₁C]
  -- Step 3: commute SQL(I,I,u_pC) past embedAB then merge two C-only SQLs.
  rw [show
        singleQubitLayer I₂ I₂ u_pC *
          (embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
            singleQubitLayer I₂ I₂ u₁C) *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer I₂ I₂ u_pC *
          embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B)) *
          singleQubitLayer I₂ I₂ u₁C *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [← embedAB_comm_singleQubitLayer_C
        (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) u_pC]
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          singleQubitLayer I₂ I₂ u_pC *
          singleQubitLayer I₂ I₂ u₁C *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          (singleQubitLayer I₂ I₂ u_pC * singleQubitLayer I₂ I₂ u₁C) *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul I₂ I₂ u_pC I₂ I₂ u₁C]
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          singleQubitLayer (I₂ * I₂) (I₂ * I₂) (u_pC * u₁C) *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          singleQubitLayer I₂ I₂ (u_pC * u₁C) *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by simp [I₂]]
  -- Step 4: absorb SQL(I,I, u_pC*u₁C) into embedBC V₂.
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          singleQubitLayer I₂ I₂ (u_pC * u₁C) *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          (singleQubitLayer I₂ I₂ (u_pC * u₁C) * embedBC V₂) *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedBC I₂ I₂ (u_pC * u₁C) V₂]
  rw [show (singleQubitLayer I₂ I₂ I₂ : Mat8) = 1 from singleQubitLayer_one]
  -- Step 5: absorb SQL_2 into embedBC from right.
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          (1 * embedBC (kron2 I₂ (u_pC * u₁C) * V₂)) *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          (embedBC (kron2 I₂ (u_pC * u₁C) * V₂) *
            singleQubitLayer u₂A u₂B u₂C) *
          embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedBC_mul_singleQubitLayer
        (kron2 I₂ (u_pC * u₁C) * V₂) u₂A u₂B u₂C]
  -- Step 6: absorb SQL(u₂A,I,I) into embedAB V₃ from left.
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          (embedBC (kron2 I₂ (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
            singleQubitLayer u₂A I₂ I₂) *
          embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedBC (kron2 I₂ (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
          (singleQubitLayer u₂A I₂ I₂ * embedAB V₃) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAB u₂A I₂ I₂ V₃]
  rw [show (singleQubitLayer I₂ I₂ I₂ : Mat8) = 1 from singleQubitLayer_one]
  -- Step 7: absorb SQL_' into embedAB from right.
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedBC (kron2 I₂ (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
          (1 * embedAB (kron2 u₂A I₂ * V₃)) *
          singleQubitLayer u'A u'B u'C =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedBC (kron2 I₂ (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
          (embedAB (kron2 u₂A I₂ * V₃) * singleQubitLayer u'A u'B u'C)
        from by noncomm_ring]
  rw [embedAB_mul_singleQubitLayer (kron2 u₂A I₂ * V₃) u'A u'B u'C]
  -- Step 8: convert trailing SQL(I,I,u'C) to embedBC.
  rw [singleQubitLayer_eq_embedBC_kron2 I₂ u'C]
  -- Final: I₂ → 1 normalization and re-association.
  show _ = _
  simp only [I₂]
  noncomm_ring

set_option maxHeartbeats 400000 in
/-- AB-AC-AB non-adjacent-same sandwich. Pattern #7 (AB-AC-AB-AC).
    Proved iter 567 via 8-step cascading absorption. -/
private lemma sandwich_AB_AC_AB_to_4embed
    (V₁ V₂ V₃ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
      singleQubitLayer u'A u'B u'C =
    embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
      embedAC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂A u₂C) *
      embedAB (kron2 1 u₂B * V₃ * kron2 u'A u'B) *
      embedAC (kron2 1 u'C) := by
  -- Step 1: absorb leading SQL into V₁ from left.
  rw [show
        singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC * embedAB V₁) *
          singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAB u_pA u_pB u_pC V₁]
  -- Step 2: absorb SQL₁ into AB(...) from right.
  rw [show
        singleQubitLayer I₂ I₂ u_pC * embedAB (kron2 u_pA u_pB * V₁) *
          singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        singleQubitLayer I₂ I₂ u_pC *
          (embedAB (kron2 u_pA u_pB * V₁) * singleQubitLayer u₁A u₁B u₁C) *
          embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAB_mul_singleQubitLayer (kron2 u_pA u_pB * V₁) u₁A u₁B u₁C]
  -- Step 3: commute SQL(I,I,u_pC) past AB; merge two C-only SQLs.
  rw [show
        singleQubitLayer I₂ I₂ u_pC *
          (embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
            singleQubitLayer I₂ I₂ u₁C) *
          embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer I₂ I₂ u_pC *
          embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B)) *
          singleQubitLayer I₂ I₂ u₁C *
          embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [← embedAB_comm_singleQubitLayer_C
        (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) u_pC]
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          singleQubitLayer I₂ I₂ u_pC *
          singleQubitLayer I₂ I₂ u₁C *
          embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          (singleQubitLayer I₂ I₂ u_pC * singleQubitLayer I₂ I₂ u₁C) *
          embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul I₂ I₂ u_pC I₂ I₂ u₁C]
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          singleQubitLayer (I₂ * I₂) (I₂ * I₂) (u_pC * u₁C) *
          embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          singleQubitLayer I₂ I₂ (u_pC * u₁C) *
          embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by simp [I₂]]
  -- Step 4: absorb SQL(I,I, u_pC*u₁C) into V₂ via AC absorption.
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          singleQubitLayer I₂ I₂ (u_pC * u₁C) *
          embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          (singleQubitLayer I₂ I₂ (u_pC * u₁C) * embedAC V₂) *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAC I₂ I₂ (u_pC * u₁C) V₂]
  rw [show (singleQubitLayer I₂ I₂ I₂ : Mat8) = 1 from singleQubitLayer_one]
  -- Step 5: absorb SQL_2 into AC(...) from right.
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          (1 * embedAC (kron2 I₂ (u_pC * u₁C) * V₂)) *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          (embedAC (kron2 I₂ (u_pC * u₁C) * V₂) *
            singleQubitLayer u₂A u₂B u₂C) *
          embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAC_mul_singleQubitLayer
        (kron2 I₂ (u_pC * u₁C) * V₂) u₂A u₂B u₂C]
  -- Step 6: absorb SQL(I, u₂B, I) into V₃ from left.
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          (embedAC (kron2 I₂ (u_pC * u₁C) * V₂ * kron2 u₂A u₂C) *
            singleQubitLayer I₂ u₂B I₂) *
          embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedAC (kron2 I₂ (u_pC * u₁C) * V₂ * kron2 u₂A u₂C) *
          (singleQubitLayer I₂ u₂B I₂ * embedAB V₃) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAB I₂ u₂B I₂ V₃]
  rw [show (singleQubitLayer I₂ I₂ I₂ : Mat8) = 1 from singleQubitLayer_one]
  -- Step 7: absorb SQL_' into AB(...) from right.
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedAC (kron2 I₂ (u_pC * u₁C) * V₂ * kron2 u₂A u₂C) *
          (1 * embedAB (kron2 I₂ u₂B * V₃)) *
          singleQubitLayer u'A u'B u'C =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedAC (kron2 I₂ (u_pC * u₁C) * V₂ * kron2 u₂A u₂C) *
          (embedAB (kron2 I₂ u₂B * V₃) * singleQubitLayer u'A u'B u'C)
        from by noncomm_ring]
  rw [embedAB_mul_singleQubitLayer (kron2 I₂ u₂B * V₃) u'A u'B u'C]
  -- Step 8: convert trailing SQL(I,I,u'C) to embedAC(kron2 1 u'C).
  rw [show singleQubitLayer I₂ I₂ u'C = embedAC (kron2 1 u'C) from by
        rw [embedAC_kron2]
        show kron3 I₂ I₂ u'C = kron3 (1 : Mat2) I₂ u'C
        rw [show (1 : Mat2) = I₂ from rfl]]
  -- Final: I₂ → 1 normalization and re-association.
  show _ = _
  simp only [I₂]
  noncomm_ring

set_option maxHeartbeats 400000 in
/-- BC-AB-BC non-adjacent-same sandwich. Pattern #5 (BC-AB-BC-AB).
    Proved iter 568 via 8-step cascading absorption (SWAP_BC mirror of iter 566). -/
private lemma sandwich_BC_AB_BC_to_4embed
    (V₁ V₂ V₃ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
      singleQubitLayer u'A u'B u'C =
    embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
      embedAB (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂B) *
      embedBC (kron2 1 u₂C * V₃ * kron2 u'B u'C) *
      embedAB (kron2 u'A 1) := by
  -- Step 1: absorb leading SQL into V₁ from left.
  rw [show
        singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC * embedBC V₁) *
          singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedBC u_pA u_pB u_pC V₁]
  -- Step 2: absorb SQL₁ into BC(...) from right.
  rw [show
        singleQubitLayer u_pA I₂ I₂ * embedBC (kron2 u_pB u_pC * V₁) *
          singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA I₂ I₂ *
          (embedBC (kron2 u_pB u_pC * V₁) * singleQubitLayer u₁A u₁B u₁C) *
          embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedBC_mul_singleQubitLayer (kron2 u_pB u_pC * V₁) u₁A u₁B u₁C]
  -- Step 3: commute SQL(u_pA, I, I) past BC; merge two A-only SQLs.
  rw [show
        singleQubitLayer u_pA I₂ I₂ *
          (embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
            singleQubitLayer u₁A I₂ I₂) *
          embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA I₂ I₂ *
          embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C)) *
          singleQubitLayer u₁A I₂ I₂ *
          embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [← embedBC_comm_singleQubitLayer_A
        (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) u_pA]
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          singleQubitLayer u_pA I₂ I₂ *
          singleQubitLayer u₁A I₂ I₂ *
          embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          (singleQubitLayer u_pA I₂ I₂ * singleQubitLayer u₁A I₂ I₂) *
          embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul u_pA I₂ I₂ u₁A I₂ I₂]
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          singleQubitLayer (u_pA * u₁A) (I₂ * I₂) (I₂ * I₂) *
          embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          singleQubitLayer (u_pA * u₁A) I₂ I₂ *
          embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C from by simp [I₂]]
  -- Step 4: absorb SQL(u_pA*u₁A, I, I) into V₂ via AB absorption from left.
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          singleQubitLayer (u_pA * u₁A) I₂ I₂ *
          embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          (singleQubitLayer (u_pA * u₁A) I₂ I₂ * embedAB V₂) *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAB (u_pA * u₁A) I₂ I₂ V₂]
  rw [show (singleQubitLayer I₂ I₂ I₂ : Mat8) = 1 from singleQubitLayer_one]
  -- Step 5: absorb SQL_2 into AB(...) from right.
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          (1 * embedAB (kron2 (u_pA * u₁A) I₂ * V₂)) *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          (embedAB (kron2 (u_pA * u₁A) I₂ * V₂) *
            singleQubitLayer u₂A u₂B u₂C) *
          embedBC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAB_mul_singleQubitLayer
        (kron2 (u_pA * u₁A) I₂ * V₂) u₂A u₂B u₂C]
  -- Step 6: absorb SQL(I, I, u₂C) into V₃ via BC absorption from left.
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          (embedAB (kron2 (u_pA * u₁A) I₂ * V₂ * kron2 u₂A u₂B) *
            singleQubitLayer I₂ I₂ u₂C) *
          embedBC V₃ *
          singleQubitLayer u'A u'B u'C =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAB (kron2 (u_pA * u₁A) I₂ * V₂ * kron2 u₂A u₂B) *
          (singleQubitLayer I₂ I₂ u₂C * embedBC V₃) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedBC I₂ I₂ u₂C V₃]
  rw [show (singleQubitLayer I₂ I₂ I₂ : Mat8) = 1 from singleQubitLayer_one]
  -- Step 7: absorb SQL_' into BC(...) from right.
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAB (kron2 (u_pA * u₁A) I₂ * V₂ * kron2 u₂A u₂B) *
          (1 * embedBC (kron2 I₂ u₂C * V₃)) *
          singleQubitLayer u'A u'B u'C =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAB (kron2 (u_pA * u₁A) I₂ * V₂ * kron2 u₂A u₂B) *
          (embedBC (kron2 I₂ u₂C * V₃) * singleQubitLayer u'A u'B u'C)
        from by noncomm_ring]
  rw [embedBC_mul_singleQubitLayer (kron2 I₂ u₂C * V₃) u'A u'B u'C]
  -- Step 8: convert trailing SQL(u'A, I, I) to embedAB(kron2 u'A 1).
  rw [singleQubitLayer_eq_embedAB_kron2 u'A I₂]
  -- Final: I₂ → 1 normalization and re-association.
  show _ = _
  simp only [I₂]
  noncomm_ring

set_option maxHeartbeats 400000 in
/-- BC-AC-BC non-adjacent-same sandwich. Pattern #6 (BC-AC-BC-AC).
    Proved iter 569 via 8-step cascading absorption. -/
private lemma sandwich_BC_AC_BC_to_4embed
    (V₁ V₂ V₃ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
      singleQubitLayer u'A u'B u'C =
    embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
      embedAC (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂C) *
      embedBC (kron2 u₂B 1 * V₃ * kron2 u'B u'C) *
      embedAC (kron2 u'A 1) := by
  -- Step 1: absorb leading SQL into V₁ from left.
  rw [show
        singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC * embedBC V₁) *
          singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedBC u_pA u_pB u_pC V₁]
  -- Step 2: absorb SQL₁ into BC(...) from right.
  rw [show
        singleQubitLayer u_pA I₂ I₂ * embedBC (kron2 u_pB u_pC * V₁) *
          singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA I₂ I₂ *
          (embedBC (kron2 u_pB u_pC * V₁) * singleQubitLayer u₁A u₁B u₁C) *
          embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedBC_mul_singleQubitLayer (kron2 u_pB u_pC * V₁) u₁A u₁B u₁C]
  -- Step 3: commute SQL(u_pA, I, I) past BC; merge two A-only SQLs.
  rw [show
        singleQubitLayer u_pA I₂ I₂ *
          (embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
            singleQubitLayer u₁A I₂ I₂) *
          embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA I₂ I₂ *
          embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C)) *
          singleQubitLayer u₁A I₂ I₂ *
          embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [← embedBC_comm_singleQubitLayer_A
        (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) u_pA]
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          singleQubitLayer u_pA I₂ I₂ *
          singleQubitLayer u₁A I₂ I₂ *
          embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          (singleQubitLayer u_pA I₂ I₂ * singleQubitLayer u₁A I₂ I₂) *
          embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul u_pA I₂ I₂ u₁A I₂ I₂]
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          singleQubitLayer (u_pA * u₁A) (I₂ * I₂) (I₂ * I₂) *
          embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          singleQubitLayer (u_pA * u₁A) I₂ I₂ *
          embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C from by simp [I₂]]
  -- Step 4: absorb SQL(u_pA*u₁A, I, I) into V₂ via AC absorption from left.
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          singleQubitLayer (u_pA * u₁A) I₂ I₂ *
          embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          (singleQubitLayer (u_pA * u₁A) I₂ I₂ * embedAC V₂) *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAC (u_pA * u₁A) I₂ I₂ V₂]
  rw [show (singleQubitLayer I₂ I₂ I₂ : Mat8) = 1 from singleQubitLayer_one]
  -- Step 5: absorb SQL_2 into AC(...) from right.
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          (1 * embedAC (kron2 (u_pA * u₁A) I₂ * V₂)) *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          (embedAC (kron2 (u_pA * u₁A) I₂ * V₂) *
            singleQubitLayer u₂A u₂B u₂C) *
          embedBC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAC_mul_singleQubitLayer
        (kron2 (u_pA * u₁A) I₂ * V₂) u₂A u₂B u₂C]
  -- Step 6: absorb SQL(I, u₂B, I) into V₃ via BC absorption from left.
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          (embedAC (kron2 (u_pA * u₁A) I₂ * V₂ * kron2 u₂A u₂C) *
            singleQubitLayer I₂ u₂B I₂) *
          embedBC V₃ *
          singleQubitLayer u'A u'B u'C =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAC (kron2 (u_pA * u₁A) I₂ * V₂ * kron2 u₂A u₂C) *
          (singleQubitLayer I₂ u₂B I₂ * embedBC V₃) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedBC I₂ u₂B I₂ V₃]
  rw [show (singleQubitLayer I₂ I₂ I₂ : Mat8) = 1 from singleQubitLayer_one]
  -- Step 7: absorb SQL_' into BC(...) from right.
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAC (kron2 (u_pA * u₁A) I₂ * V₂ * kron2 u₂A u₂C) *
          (1 * embedBC (kron2 u₂B I₂ * V₃)) *
          singleQubitLayer u'A u'B u'C =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAC (kron2 (u_pA * u₁A) I₂ * V₂ * kron2 u₂A u₂C) *
          (embedBC (kron2 u₂B I₂ * V₃) * singleQubitLayer u'A u'B u'C)
        from by noncomm_ring]
  rw [embedBC_mul_singleQubitLayer (kron2 u₂B I₂ * V₃) u'A u'B u'C]
  -- Step 8: convert trailing SQL(u'A, I, I) to embedAC(kron2 u'A 1).
  rw [show singleQubitLayer u'A I₂ I₂ = embedAC (kron2 u'A 1) from by
        rw [embedAC_kron2]
        show kron3 u'A I₂ I₂ = kron3 u'A I₂ (1 : Mat2)
        rw [show (1 : Mat2) = I₂ from rfl]]
  -- Final: I₂ → 1 normalization.
  show _ = _
  simp only [I₂]
  noncomm_ring

set_option maxHeartbeats 400000 in
/-- AC-AB-AC non-adjacent-same sandwich. Pattern #4 (AC-AB-AC-AB).
    Proved iter 571 via 8-step cascading absorption. -/
private lemma sandwich_AC_AB_AC_to_4embed
    (V₁ V₂ V₃ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
      singleQubitLayer u'A u'B u'C =
    embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
      embedAB (kron2 1 (u_pB * u₁B) * V₂ * kron2 u₂A u₂B) *
      embedAC (kron2 1 u₂C * V₃ * kron2 u'A u'C) *
      embedAB (kron2 1 u'B) := by
  -- Step 1: absorb leading SQL into V₁ from left.
  rw [show
        singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC * embedAC V₁) *
          singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAC u_pA u_pB u_pC V₁]
  -- Step 2: absorb SQL₁ into AC(...) from right.
  rw [show
        singleQubitLayer I₂ u_pB I₂ * embedAC (kron2 u_pA u_pC * V₁) *
          singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C =
        singleQubitLayer I₂ u_pB I₂ *
          (embedAC (kron2 u_pA u_pC * V₁) * singleQubitLayer u₁A u₁B u₁C) *
          embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAC_mul_singleQubitLayer (kron2 u_pA u_pC * V₁) u₁A u₁B u₁C]
  -- Step 3: commute SQL(I, u_pB, I) past AC; merge two B-only SQLs.
  rw [show
        singleQubitLayer I₂ u_pB I₂ *
          (embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
            singleQubitLayer I₂ u₁B I₂) *
          embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer I₂ u_pB I₂ *
          embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C)) *
          singleQubitLayer I₂ u₁B I₂ *
          embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [← embedAC_comm_singleQubitLayer_B
        (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) u_pB]
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          singleQubitLayer I₂ u_pB I₂ *
          singleQubitLayer I₂ u₁B I₂ *
          embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          (singleQubitLayer I₂ u_pB I₂ * singleQubitLayer I₂ u₁B I₂) *
          embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul I₂ u_pB I₂ I₂ u₁B I₂]
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          singleQubitLayer (I₂ * I₂) (u_pB * u₁B) (I₂ * I₂) *
          embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          singleQubitLayer I₂ (u_pB * u₁B) I₂ *
          embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C from by simp [I₂]]
  -- Step 4: absorb SQL(I, u_pB*u₁B, I) into V₂=AB from left.
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          singleQubitLayer I₂ (u_pB * u₁B) I₂ *
          embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          (singleQubitLayer I₂ (u_pB * u₁B) I₂ * embedAB V₂) *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAB I₂ (u_pB * u₁B) I₂ V₂]
  rw [show (singleQubitLayer I₂ I₂ I₂ : Mat8) = 1 from singleQubitLayer_one]
  -- Step 5: absorb SQL_2 into AB(...) from right.
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          (1 * embedAB (kron2 I₂ (u_pB * u₁B) * V₂)) *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          (embedAB (kron2 I₂ (u_pB * u₁B) * V₂) *
            singleQubitLayer u₂A u₂B u₂C) *
          embedAC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAB_mul_singleQubitLayer
        (kron2 I₂ (u_pB * u₁B) * V₂) u₂A u₂B u₂C]
  -- Step 6: absorb SQL(I, I, u₂C) into V₃=AC from left.
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          (embedAB (kron2 I₂ (u_pB * u₁B) * V₂ * kron2 u₂A u₂B) *
            singleQubitLayer I₂ I₂ u₂C) *
          embedAC V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedAB (kron2 I₂ (u_pB * u₁B) * V₂ * kron2 u₂A u₂B) *
          (singleQubitLayer I₂ I₂ u₂C * embedAC V₃) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAC I₂ I₂ u₂C V₃]
  rw [show (singleQubitLayer I₂ I₂ I₂ : Mat8) = 1 from singleQubitLayer_one]
  -- Step 7: absorb SQL_' into AC(...) from right.
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedAB (kron2 I₂ (u_pB * u₁B) * V₂ * kron2 u₂A u₂B) *
          (1 * embedAC (kron2 I₂ u₂C * V₃)) *
          singleQubitLayer u'A u'B u'C =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedAB (kron2 I₂ (u_pB * u₁B) * V₂ * kron2 u₂A u₂B) *
          (embedAC (kron2 I₂ u₂C * V₃) * singleQubitLayer u'A u'B u'C)
        from by noncomm_ring]
  rw [embedAC_mul_singleQubitLayer (kron2 I₂ u₂C * V₃) u'A u'B u'C]
  -- Step 8: convert trailing SQL(I, u'B, I) to embedAB(kron2 1 u'B).
  rw [singleQubitLayer_eq_embedAB_kron2 I₂ u'B]
  -- Final: I₂ → 1 normalization.
  show _ = _
  simp only [I₂]
  noncomm_ring

set_option maxHeartbeats 400000 in
/-- AC-BC-AC non-adjacent-same sandwich. Pattern #9 (AC-BC-AC-BC).
    Proved iter 572 via 8-step cascading absorption. -/
private lemma sandwich_AC_BC_AC_to_4embed
    (V₁ V₂ V₃ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
      singleQubitLayer u'A u'B u'C =
    embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
      embedBC (kron2 (u_pB * u₁B) 1 * V₂ * kron2 u₂B u₂C) *
      embedAC (kron2 u₂A 1 * V₃ * kron2 u'A u'C) *
      embedBC (kron2 u'B 1) := by
  -- Step 1: absorb leading SQL into V₁ from left.
  rw [show
        singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC * embedAC V₁) *
          singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAC u_pA u_pB u_pC V₁]
  -- Step 2: absorb SQL₁ into AC(...) from right.
  rw [show
        singleQubitLayer I₂ u_pB I₂ * embedAC (kron2 u_pA u_pC * V₁) *
          singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C =
        singleQubitLayer I₂ u_pB I₂ *
          (embedAC (kron2 u_pA u_pC * V₁) * singleQubitLayer u₁A u₁B u₁C) *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAC_mul_singleQubitLayer (kron2 u_pA u_pC * V₁) u₁A u₁B u₁C]
  -- Step 3: commute SQL(I, u_pB, I) past AC; merge two B-only SQLs.
  rw [show
        singleQubitLayer I₂ u_pB I₂ *
          (embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
            singleQubitLayer I₂ u₁B I₂) *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer I₂ u_pB I₂ *
          embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C)) *
          singleQubitLayer I₂ u₁B I₂ *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [← embedAC_comm_singleQubitLayer_B
        (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) u_pB]
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          singleQubitLayer I₂ u_pB I₂ *
          singleQubitLayer I₂ u₁B I₂ *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          (singleQubitLayer I₂ u_pB I₂ * singleQubitLayer I₂ u₁B I₂) *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul I₂ u_pB I₂ I₂ u₁B I₂]
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          singleQubitLayer (I₂ * I₂) (u_pB * u₁B) (I₂ * I₂) *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          singleQubitLayer I₂ (u_pB * u₁B) I₂ *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C from by simp [I₂]]
  -- Step 4: absorb SQL(I, u_pB*u₁B, I) into V₂=BC from left.
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          singleQubitLayer I₂ (u_pB * u₁B) I₂ *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          (singleQubitLayer I₂ (u_pB * u₁B) I₂ * embedBC V₂) *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedBC I₂ (u_pB * u₁B) I₂ V₂]
  rw [show (singleQubitLayer I₂ I₂ I₂ : Mat8) = 1 from singleQubitLayer_one]
  -- Step 5: absorb SQL_2 into BC(...) from right.
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          (1 * embedBC (kron2 (u_pB * u₁B) I₂ * V₂)) *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          (embedBC (kron2 (u_pB * u₁B) I₂ * V₂) *
            singleQubitLayer u₂A u₂B u₂C) *
          embedAC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedBC_mul_singleQubitLayer
        (kron2 (u_pB * u₁B) I₂ * V₂) u₂A u₂B u₂C]
  -- Step 6: absorb SQL(u₂A, I, I) into V₃=AC from left.
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          (embedBC (kron2 (u_pB * u₁B) I₂ * V₂ * kron2 u₂B u₂C) *
            singleQubitLayer u₂A I₂ I₂) *
          embedAC V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedBC (kron2 (u_pB * u₁B) I₂ * V₂ * kron2 u₂B u₂C) *
          (singleQubitLayer u₂A I₂ I₂ * embedAC V₃) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAC u₂A I₂ I₂ V₃]
  rw [show (singleQubitLayer I₂ I₂ I₂ : Mat8) = 1 from singleQubitLayer_one]
  -- Step 7: absorb SQL_' into AC(...) from right.
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedBC (kron2 (u_pB * u₁B) I₂ * V₂ * kron2 u₂B u₂C) *
          (1 * embedAC (kron2 u₂A I₂ * V₃)) *
          singleQubitLayer u'A u'B u'C =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedBC (kron2 (u_pB * u₁B) I₂ * V₂ * kron2 u₂B u₂C) *
          (embedAC (kron2 u₂A I₂ * V₃) * singleQubitLayer u'A u'B u'C)
        from by noncomm_ring]
  rw [embedAC_mul_singleQubitLayer (kron2 u₂A I₂ * V₃) u'A u'B u'C]
  -- Step 8: convert trailing SQL(I, u'B, I) to embedBC(kron2 u'B 1).
  rw [singleQubitLayer_eq_embedBC_kron2 u'B I₂]
  -- Final: I₂ → 1 normalization.
  show _ = _
  simp only [I₂]
  noncomm_ring

set_option maxHeartbeats 400000 in
/-- AB-BC-AC all-different sandwich. Pattern #2 (AB-BC-AC-AB).
    Proved iter 573 via 8-step cascading absorption. -/
private lemma sandwich_AB_BC_AC_to_4embed
    (V₁ V₂ V₃ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
      singleQubitLayer u'A u'B u'C =
    embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
      embedBC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
      embedAC (kron2 u₂A 1 * V₃ * kron2 u'A u'C) *
      embedAB (kron2 1 u'B) := by
  -- Step 1: absorb leading SQL into V₁=AB from left.
  rw [show
        singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC * embedAB V₁) *
          singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAB u_pA u_pB u_pC V₁]
  -- Step 2: absorb SQL₁ into AB(...) from right.
  rw [show
        singleQubitLayer I₂ I₂ u_pC * embedAB (kron2 u_pA u_pB * V₁) *
          singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C =
        singleQubitLayer I₂ I₂ u_pC *
          (embedAB (kron2 u_pA u_pB * V₁) * singleQubitLayer u₁A u₁B u₁C) *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAB_mul_singleQubitLayer (kron2 u_pA u_pB * V₁) u₁A u₁B u₁C]
  -- Step 3: commute SQL(I,I,u_pC) past AB; merge two C-only SQLs.
  rw [show
        singleQubitLayer I₂ I₂ u_pC *
          (embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
            singleQubitLayer I₂ I₂ u₁C) *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer I₂ I₂ u_pC *
          embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B)) *
          singleQubitLayer I₂ I₂ u₁C *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [← embedAB_comm_singleQubitLayer_C
        (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) u_pC]
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          singleQubitLayer I₂ I₂ u_pC *
          singleQubitLayer I₂ I₂ u₁C *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          (singleQubitLayer I₂ I₂ u_pC * singleQubitLayer I₂ I₂ u₁C) *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul I₂ I₂ u_pC I₂ I₂ u₁C]
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          singleQubitLayer (I₂ * I₂) (I₂ * I₂) (u_pC * u₁C) *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          singleQubitLayer I₂ I₂ (u_pC * u₁C) *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C from by simp [I₂]]
  -- Step 4: absorb SQL(I,I, u_pC*u₁C) into V₂=BC from left.
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          singleQubitLayer I₂ I₂ (u_pC * u₁C) *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          (singleQubitLayer I₂ I₂ (u_pC * u₁C) * embedBC V₂) *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedBC I₂ I₂ (u_pC * u₁C) V₂]
  rw [show (singleQubitLayer I₂ I₂ I₂ : Mat8) = 1 from singleQubitLayer_one]
  -- Step 5: absorb SQL_2 into BC(...) from right.
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          (1 * embedBC (kron2 I₂ (u_pC * u₁C) * V₂)) *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          (embedBC (kron2 I₂ (u_pC * u₁C) * V₂) *
            singleQubitLayer u₂A u₂B u₂C) *
          embedAC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedBC_mul_singleQubitLayer
        (kron2 I₂ (u_pC * u₁C) * V₂) u₂A u₂B u₂C]
  -- Step 6: absorb SQL(u₂A, I, I) into V₃=AC from left.
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          (embedBC (kron2 I₂ (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
            singleQubitLayer u₂A I₂ I₂) *
          embedAC V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedBC (kron2 I₂ (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
          (singleQubitLayer u₂A I₂ I₂ * embedAC V₃) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAC u₂A I₂ I₂ V₃]
  rw [show (singleQubitLayer I₂ I₂ I₂ : Mat8) = 1 from singleQubitLayer_one]
  -- Step 7: absorb SQL_' into AC(...) from right.
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedBC (kron2 I₂ (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
          (1 * embedAC (kron2 u₂A I₂ * V₃)) *
          singleQubitLayer u'A u'B u'C =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedBC (kron2 I₂ (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
          (embedAC (kron2 u₂A I₂ * V₃) * singleQubitLayer u'A u'B u'C)
        from by noncomm_ring]
  rw [embedAC_mul_singleQubitLayer (kron2 u₂A I₂ * V₃) u'A u'B u'C]
  -- Step 8: convert trailing SQL(I, u'B, I) to embedAB(kron2 1 u'B).
  rw [singleQubitLayer_eq_embedAB_kron2 I₂ u'B]
  -- Final: I₂ → 1 normalization.
  show _ = _
  simp only [I₂]
  noncomm_ring

set_option maxHeartbeats 400000 in
/-- BC-AC-AB all-different sandwich. Pattern #1 (BC-AC-AB-BC).
    Proved iter 574 via 8-step cascading absorption. -/
private lemma sandwich_BC_AC_AB_to_4embed
    (V₁ V₂ V₃ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
      singleQubitLayer u'A u'B u'C =
    embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
      embedAC (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂C) *
      embedAB (kron2 1 u₂B * V₃ * kron2 u'A u'B) *
      embedBC (kron2 1 u'C) := by
  -- Step 1: absorb leading SQL into V₁=BC from left.
  rw [show
        singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC * embedBC V₁) *
          singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedBC u_pA u_pB u_pC V₁]
  -- Step 2: absorb SQL₁ into BC(...) from right.
  rw [show
        singleQubitLayer u_pA I₂ I₂ * embedBC (kron2 u_pB u_pC * V₁) *
          singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA I₂ I₂ *
          (embedBC (kron2 u_pB u_pC * V₁) * singleQubitLayer u₁A u₁B u₁C) *
          embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedBC_mul_singleQubitLayer (kron2 u_pB u_pC * V₁) u₁A u₁B u₁C]
  -- Step 3: commute SQL(u_pA, I, I) past BC; merge two A-only SQLs.
  rw [show
        singleQubitLayer u_pA I₂ I₂ *
          (embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
            singleQubitLayer u₁A I₂ I₂) *
          embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA I₂ I₂ *
          embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C)) *
          singleQubitLayer u₁A I₂ I₂ *
          embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [← embedBC_comm_singleQubitLayer_A
        (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) u_pA]
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          singleQubitLayer u_pA I₂ I₂ *
          singleQubitLayer u₁A I₂ I₂ *
          embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          (singleQubitLayer u_pA I₂ I₂ * singleQubitLayer u₁A I₂ I₂) *
          embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul u_pA I₂ I₂ u₁A I₂ I₂]
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          singleQubitLayer (u_pA * u₁A) (I₂ * I₂) (I₂ * I₂) *
          embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          singleQubitLayer (u_pA * u₁A) I₂ I₂ *
          embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by simp [I₂]]
  -- Step 4: absorb SQL(u_pA*u₁A, I, I) into V₂=AC from left.
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          singleQubitLayer (u_pA * u₁A) I₂ I₂ *
          embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          (singleQubitLayer (u_pA * u₁A) I₂ I₂ * embedAC V₂) *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAC (u_pA * u₁A) I₂ I₂ V₂]
  rw [show (singleQubitLayer I₂ I₂ I₂ : Mat8) = 1 from singleQubitLayer_one]
  -- Step 5: absorb SQL_2 into AC(...) from right.
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          (1 * embedAC (kron2 (u_pA * u₁A) I₂ * V₂)) *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          (embedAC (kron2 (u_pA * u₁A) I₂ * V₂) *
            singleQubitLayer u₂A u₂B u₂C) *
          embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAC_mul_singleQubitLayer
        (kron2 (u_pA * u₁A) I₂ * V₂) u₂A u₂B u₂C]
  -- Step 6: absorb SQL(I, u₂B, I) into V₃=AB from left.
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          (embedAC (kron2 (u_pA * u₁A) I₂ * V₂ * kron2 u₂A u₂C) *
            singleQubitLayer I₂ u₂B I₂) *
          embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAC (kron2 (u_pA * u₁A) I₂ * V₂ * kron2 u₂A u₂C) *
          (singleQubitLayer I₂ u₂B I₂ * embedAB V₃) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAB I₂ u₂B I₂ V₃]
  rw [show (singleQubitLayer I₂ I₂ I₂ : Mat8) = 1 from singleQubitLayer_one]
  -- Step 7: absorb SQL_' into AB(...) from right.
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAC (kron2 (u_pA * u₁A) I₂ * V₂ * kron2 u₂A u₂C) *
          (1 * embedAB (kron2 I₂ u₂B * V₃)) *
          singleQubitLayer u'A u'B u'C =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAC (kron2 (u_pA * u₁A) I₂ * V₂ * kron2 u₂A u₂C) *
          (embedAB (kron2 I₂ u₂B * V₃) * singleQubitLayer u'A u'B u'C)
        from by noncomm_ring]
  rw [embedAB_mul_singleQubitLayer (kron2 I₂ u₂B * V₃) u'A u'B u'C]
  -- Step 8: convert trailing SQL(I, I, u'C) to embedBC(kron2 1 u'C).
  rw [singleQubitLayer_eq_embedBC_kron2 I₂ u'C]
  -- Final: I₂ → 1 normalization.
  show _ = _
  simp only [I₂]
  noncomm_ring

set_option maxHeartbeats 400000 in
/-- AC-BC-AB all-different sandwich. Pattern #3 (AC-BC-AB-AC).
    Proved iter 575 via 8-step cascading absorption.
    LAST of 9 sandwich helpers — completes natural-class infrastructure. -/
private lemma sandwich_AC_BC_AB_to_4embed
    (V₁ V₂ V₃ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
      singleQubitLayer u'A u'B u'C =
    embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
      embedBC (kron2 (u_pB * u₁B) 1 * V₂ * kron2 u₂B u₂C) *
      embedAB (kron2 u₂A 1 * V₃ * kron2 u'A u'B) *
      embedAC (kron2 1 u'C) := by
  -- Step 1: absorb leading SQL into V₁=AC from left.
  rw [show
        singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC * embedAC V₁) *
          singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAC u_pA u_pB u_pC V₁]
  -- Step 2: absorb SQL₁ into AC(...) from right.
  rw [show
        singleQubitLayer I₂ u_pB I₂ * embedAC (kron2 u_pA u_pC * V₁) *
          singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        singleQubitLayer I₂ u_pB I₂ *
          (embedAC (kron2 u_pA u_pC * V₁) * singleQubitLayer u₁A u₁B u₁C) *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAC_mul_singleQubitLayer (kron2 u_pA u_pC * V₁) u₁A u₁B u₁C]
  -- Step 3: commute SQL(I, u_pB, I) past AC; merge two B-only SQLs.
  rw [show
        singleQubitLayer I₂ u_pB I₂ *
          (embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
            singleQubitLayer I₂ u₁B I₂) *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer I₂ u_pB I₂ *
          embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C)) *
          singleQubitLayer I₂ u₁B I₂ *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [← embedAC_comm_singleQubitLayer_B
        (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) u_pB]
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          singleQubitLayer I₂ u_pB I₂ *
          singleQubitLayer I₂ u₁B I₂ *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          (singleQubitLayer I₂ u_pB I₂ * singleQubitLayer I₂ u₁B I₂) *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul I₂ u_pB I₂ I₂ u₁B I₂]
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          singleQubitLayer (I₂ * I₂) (u_pB * u₁B) (I₂ * I₂) *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          singleQubitLayer I₂ (u_pB * u₁B) I₂ *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by simp [I₂]]
  -- Step 4: absorb SQL(I, u_pB*u₁B, I) into V₂=BC from left.
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          singleQubitLayer I₂ (u_pB * u₁B) I₂ *
          embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          (singleQubitLayer I₂ (u_pB * u₁B) I₂ * embedBC V₂) *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedBC I₂ (u_pB * u₁B) I₂ V₂]
  rw [show (singleQubitLayer I₂ I₂ I₂ : Mat8) = 1 from singleQubitLayer_one]
  -- Step 5: absorb SQL_2 into BC(...) from right.
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          (1 * embedBC (kron2 (u_pB * u₁B) I₂ * V₂)) *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          (embedBC (kron2 (u_pB * u₁B) I₂ * V₂) *
            singleQubitLayer u₂A u₂B u₂C) *
          embedAB V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedBC_mul_singleQubitLayer
        (kron2 (u_pB * u₁B) I₂ * V₂) u₂A u₂B u₂C]
  -- Step 6: absorb SQL(u₂A, I, I) into V₃=AB from left.
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          (embedBC (kron2 (u_pB * u₁B) I₂ * V₂ * kron2 u₂B u₂C) *
            singleQubitLayer u₂A I₂ I₂) *
          embedAB V₃ *
          singleQubitLayer u'A u'B u'C =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedBC (kron2 (u_pB * u₁B) I₂ * V₂ * kron2 u₂B u₂C) *
          (singleQubitLayer u₂A I₂ I₂ * embedAB V₃) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAB u₂A I₂ I₂ V₃]
  rw [show (singleQubitLayer I₂ I₂ I₂ : Mat8) = 1 from singleQubitLayer_one]
  -- Step 7: absorb SQL_' into AB(...) from right.
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedBC (kron2 (u_pB * u₁B) I₂ * V₂ * kron2 u₂B u₂C) *
          (1 * embedAB (kron2 u₂A I₂ * V₃)) *
          singleQubitLayer u'A u'B u'C =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedBC (kron2 (u_pB * u₁B) I₂ * V₂ * kron2 u₂B u₂C) *
          (embedAB (kron2 u₂A I₂ * V₃) * singleQubitLayer u'A u'B u'C)
        from by noncomm_ring]
  rw [embedAB_mul_singleQubitLayer (kron2 u₂A I₂ * V₃) u'A u'B u'C]
  -- Step 8: convert trailing SQL(I, I, u'C) to embedAC(kron2 1 u'C).
  rw [show singleQubitLayer I₂ I₂ u'C = embedAC (kron2 1 u'C) from by
        rw [embedAC_kron2]
        show kron3 I₂ I₂ u'C = kron3 (1 : Mat2) I₂ u'C
        rw [show (1 : Mat2) = I₂ from rfl]]
  -- Final: I₂ → 1 normalization.
  show _ = _
  simp only [I₂]
  noncomm_ring

set_option maxHeartbeats 400000 in
-- Heartbeats raised: 9-step absorption cascade over a 7-factor 8×8 product.
/-- **BC-AB-AC all-different sandwich** (iter 1038). Pattern #3 (AC-BC-AB-AC)
    with `V₁ = 1`. Mirror of `sandwich_AC_AB_BC_to_4embed`: here the trailing
    leftover is **B-only**, so it commutes past `embedAC`
    (`embedAC_comm_singleQubitLayer_B`) and absorbs into the AB gate. Again no
    fourth real embed is created, so the iter-729 "3-XY gap" does not arise. -/
private lemma sandwich_BC_AB_AC_to_4embed (V₁ V₂ V₃ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
      singleQubitLayer u'A u'B u'C =
    embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
      embedAB (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂B * kron2 1 u'B) *
      embedAC (kron2 1 u₂C * V₃ * kron2 u'A u'C) := by
  rw [singleQubitLayer_mul_embedBC u_pA u_pB u_pC V₁]
  rw [show singleQubitLayer u_pA I₂ I₂ * embedBC (kron2 u_pB u_pC * V₁) *
        singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
        singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
        singleQubitLayer u'A u'B u'C =
      singleQubitLayer u_pA I₂ I₂ *
        (embedBC (kron2 u_pB u_pC * V₁) * singleQubitLayer u₁A u₁B u₁C) *
        embedAB V₂ * singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
        singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedBC_mul_singleQubitLayer (kron2 u_pB u_pC * V₁) u₁A u₁B u₁C]
  rw [show singleQubitLayer u_pA I₂ I₂ *
        (embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          singleQubitLayer u₁A I₂ I₂) *
        embedAB V₂ * singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
        singleQubitLayer u'A u'B u'C =
      (singleQubitLayer u_pA I₂ I₂ *
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C)) *
        singleQubitLayer u₁A I₂ I₂ *
        embedAB V₂ * singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
        singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [← embedBC_comm_singleQubitLayer_A
        (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) u_pA]
  rw [show embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
        singleQubitLayer u_pA I₂ I₂ * singleQubitLayer u₁A I₂ I₂ *
        embedAB V₂ * singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
        singleQubitLayer u'A u'B u'C =
      embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
        (singleQubitLayer u_pA I₂ I₂ * singleQubitLayer u₁A I₂ I₂) *
        embedAB V₂ * singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
        singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul]
  rw [show embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
        singleQubitLayer (u_pA * u₁A) (I₂ * I₂) (I₂ * I₂) *
        embedAB V₂ * singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
        singleQubitLayer u'A u'B u'C =
      embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
        (singleQubitLayer (u_pA * u₁A) (I₂ * I₂) (I₂ * I₂) * embedAB V₂) *
        singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
        singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAB (u_pA * u₁A) (I₂ * I₂) (I₂ * I₂) V₂]
  rw [show embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
        (singleQubitLayer I₂ I₂ (I₂ * I₂) *
          embedAB (kron2 (u_pA * u₁A) (I₂ * I₂) * V₂)) *
        singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
        singleQubitLayer u'A u'B u'C =
      embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
        singleQubitLayer I₂ I₂ (I₂ * I₂) *
        (embedAB (kron2 (u_pA * u₁A) (I₂ * I₂) * V₂) *
          singleQubitLayer u₂A u₂B u₂C) *
        embedAC V₃ * singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAB_mul_singleQubitLayer
        (kron2 (u_pA * u₁A) (I₂ * I₂) * V₂) u₂A u₂B u₂C]
  rw [show embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
        singleQubitLayer I₂ I₂ (I₂ * I₂) *
        (embedAB (kron2 (u_pA * u₁A) (I₂ * I₂) * V₂ * kron2 u₂A u₂B) *
          singleQubitLayer I₂ I₂ u₂C) *
        embedAC V₃ * singleQubitLayer u'A u'B u'C =
      embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
        singleQubitLayer I₂ I₂ (I₂ * I₂) *
        embedAB (kron2 (u_pA * u₁A) (I₂ * I₂) * V₂ * kron2 u₂A u₂B) *
        (singleQubitLayer I₂ I₂ u₂C * embedAC V₃) *
        singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAC I₂ I₂ u₂C V₃]
  rw [show embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
        singleQubitLayer I₂ I₂ (I₂ * I₂) *
        embedAB (kron2 (u_pA * u₁A) (I₂ * I₂) * V₂ * kron2 u₂A u₂B) *
        (singleQubitLayer I₂ I₂ I₂ * embedAC (kron2 I₂ u₂C * V₃)) *
        singleQubitLayer u'A u'B u'C =
      embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
        singleQubitLayer I₂ I₂ (I₂ * I₂) *
        embedAB (kron2 (u_pA * u₁A) (I₂ * I₂) * V₂ * kron2 u₂A u₂B) *
        singleQubitLayer I₂ I₂ I₂ *
        (embedAC (kron2 I₂ u₂C * V₃) * singleQubitLayer u'A u'B u'C)
      from by noncomm_ring]
  rw [embedAC_mul_singleQubitLayer (kron2 I₂ u₂C * V₃) u'A u'B u'C]
  rw [embedAC_comm_singleQubitLayer_B
        (kron2 I₂ u₂C * V₃ * kron2 u'A u'C) u'B]
  rw [show embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
        singleQubitLayer I₂ I₂ (I₂ * I₂) *
        embedAB (kron2 (u_pA * u₁A) (I₂ * I₂) * V₂ * kron2 u₂A u₂B) *
        singleQubitLayer I₂ I₂ I₂ *
        (singleQubitLayer I₂ u'B I₂ *
          embedAC (kron2 I₂ u₂C * V₃ * kron2 u'A u'C)) =
      embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
        singleQubitLayer I₂ I₂ (I₂ * I₂) *
        embedAB (kron2 (u_pA * u₁A) (I₂ * I₂) * V₂ * kron2 u₂A u₂B) *
        (singleQubitLayer I₂ I₂ I₂ * singleQubitLayer I₂ u'B I₂) *
        embedAC (kron2 I₂ u₂C * V₃ * kron2 u'A u'C) from by noncomm_ring]
  rw [singleQubitLayer_mul]
  rw [show embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
        singleQubitLayer I₂ I₂ (I₂ * I₂) *
        embedAB (kron2 (u_pA * u₁A) (I₂ * I₂) * V₂ * kron2 u₂A u₂B) *
        singleQubitLayer (I₂ * I₂) (I₂ * u'B) (I₂ * I₂) *
        embedAC (kron2 I₂ u₂C * V₃ * kron2 u'A u'C) =
      embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
        singleQubitLayer I₂ I₂ (I₂ * I₂) *
        (embedAB (kron2 (u_pA * u₁A) (I₂ * I₂) * V₂ * kron2 u₂A u₂B) *
          singleQubitLayer (I₂ * I₂) (I₂ * u'B) (I₂ * I₂)) *
        embedAC (kron2 I₂ u₂C * V₃ * kron2 u'A u'C) from by noncomm_ring]
  rw [embedAB_mul_singleQubitLayer
        (kron2 (u_pA * u₁A) (I₂ * I₂) * V₂ * kron2 u₂A u₂B)
        (I₂ * I₂) (I₂ * u'B) (I₂ * I₂)]
  have hSQL_one : (singleQubitLayer (1 : Mat2) 1 1 : Mat8) = 1 := singleQubitLayer_one
  simp only [I₂, mul_one, one_mul]
  rw [hSQL_one]
  noncomm_ring
set_option maxHeartbeats 400000 in
-- Heartbeats raised: 9-step absorption cascade over a 7-factor 8×8 product.
/-- **AC-AB-BC all-different sandwich** (iter 1036). Pattern #1 (BC-AC-AB-BC)
    with `V₁ = 1`.

    This is the lemma the iter-729/731 note declared impossible. That note
    assumed the trailing leftover single-qubit gate must be parked in a fresh
    TRAILING slot — which would need the word AC-AB-BC-AC, indeed not one of
    the 9 canonical patterns. But for this word the leftover is **A-only**, and
    an A-only layer COMMUTES past `embedBC` (`embedBC_comm_singleQubitLayer_A`),
    so it travels left and absorbs into the **AB** gate instead. No fourth real
    embed is created; the spare slot goes at the FRONT as `embedBC 1`, and the
    word is disjunct #1.

    Cascade (9 steps, mirroring `sandwich_AC_BC_AB_to_4embed`'s idiom):
    leading SQL → AC; SQL₁'s (A,C) → AC, its B-part merges with the leading
    B-residual and → AB; SQL₂'s (A,B) → AB, its C-part → BC; the trailing SQL's
    (B,C) → BC, and its A-part commutes back left into AB. -/
private lemma sandwich_AC_AB_BC_to_4embed (V₁ V₂ V₃ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
      singleQubitLayer u'A u'B u'C =
    embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
      embedAB (kron2 1 (u_pB * u₁B) * V₂ * kron2 u₂A u₂B * kron2 u'A 1) *
      embedBC (kron2 1 u₂C * V₃ * kron2 u'B u'C) := by
  -- Step 1: leading SQL into AC from the left.
  rw [singleQubitLayer_mul_embedAC u_pA u_pB u_pC V₁]
  -- Step 2: SQL₁'s (A,C) into AC from the right.
  rw [show singleQubitLayer I₂ u_pB I₂ * embedAC (kron2 u_pA u_pC * V₁) *
        singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
        singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
        singleQubitLayer u'A u'B u'C =
      singleQubitLayer I₂ u_pB I₂ *
        (embedAC (kron2 u_pA u_pC * V₁) * singleQubitLayer u₁A u₁B u₁C) *
        embedAB V₂ * singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
        singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAC_mul_singleQubitLayer (kron2 u_pA u_pC * V₁) u₁A u₁B u₁C]
  -- Step 3: move the leading B-only layer right past AC.
  rw [show singleQubitLayer I₂ u_pB I₂ *
        (embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          singleQubitLayer I₂ u₁B I₂) *
        embedAB V₂ * singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
        singleQubitLayer u'A u'B u'C =
      (singleQubitLayer I₂ u_pB I₂ *
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C)) *
        singleQubitLayer I₂ u₁B I₂ *
        embedAB V₂ * singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
        singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [← embedAC_comm_singleQubitLayer_B
        (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) u_pB]
  -- Step 4: merge the two B-only layers.
  rw [show embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
        singleQubitLayer I₂ u_pB I₂ * singleQubitLayer I₂ u₁B I₂ *
        embedAB V₂ * singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
        singleQubitLayer u'A u'B u'C =
      embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
        (singleQubitLayer I₂ u_pB I₂ * singleQubitLayer I₂ u₁B I₂) *
        embedAB V₂ * singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
        singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul]
  -- Step 5: merged B-layer into AB from the left.
  rw [show embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
        singleQubitLayer (I₂ * I₂) (u_pB * u₁B) (I₂ * I₂) *
        embedAB V₂ * singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
        singleQubitLayer u'A u'B u'C =
      embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
        (singleQubitLayer (I₂ * I₂) (u_pB * u₁B) (I₂ * I₂) * embedAB V₂) *
        singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
        singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedAB (I₂ * I₂) (u_pB * u₁B) (I₂ * I₂) V₂]
  -- Step 6: SQL₂'s (A,B) into AB from the right.
  rw [show embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
        (singleQubitLayer I₂ I₂ (I₂ * I₂) *
          embedAB (kron2 (I₂ * I₂) (u_pB * u₁B) * V₂)) *
        singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
        singleQubitLayer u'A u'B u'C =
      embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
        singleQubitLayer I₂ I₂ (I₂ * I₂) *
        (embedAB (kron2 (I₂ * I₂) (u_pB * u₁B) * V₂) *
          singleQubitLayer u₂A u₂B u₂C) *
        embedBC V₃ * singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAB_mul_singleQubitLayer
        (kron2 (I₂ * I₂) (u_pB * u₁B) * V₂) u₂A u₂B u₂C]
  -- Step 7: leftover C-only layer into BC from the left.
  rw [show embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
        singleQubitLayer I₂ I₂ (I₂ * I₂) *
        (embedAB (kron2 (I₂ * I₂) (u_pB * u₁B) * V₂ * kron2 u₂A u₂B) *
          singleQubitLayer I₂ I₂ u₂C) *
        embedBC V₃ * singleQubitLayer u'A u'B u'C =
      embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
        singleQubitLayer I₂ I₂ (I₂ * I₂) *
        embedAB (kron2 (I₂ * I₂) (u_pB * u₁B) * V₂ * kron2 u₂A u₂B) *
        (singleQubitLayer I₂ I₂ u₂C * embedBC V₃) *
        singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul_embedBC I₂ I₂ u₂C V₃]
  -- Step 8: trailing SQL's (B,C) into BC from the right.
  rw [show embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
        singleQubitLayer I₂ I₂ (I₂ * I₂) *
        embedAB (kron2 (I₂ * I₂) (u_pB * u₁B) * V₂ * kron2 u₂A u₂B) *
        (singleQubitLayer I₂ I₂ I₂ * embedBC (kron2 I₂ u₂C * V₃)) *
        singleQubitLayer u'A u'B u'C =
      embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
        singleQubitLayer I₂ I₂ (I₂ * I₂) *
        embedAB (kron2 (I₂ * I₂) (u_pB * u₁B) * V₂ * kron2 u₂A u₂B) *
        singleQubitLayer I₂ I₂ I₂ *
        (embedBC (kron2 I₂ u₂C * V₃) * singleQubitLayer u'A u'B u'C)
      from by noncomm_ring]
  rw [embedBC_mul_singleQubitLayer (kron2 I₂ u₂C * V₃) u'A u'B u'C]
  -- Step 9 (THE KEY STEP): the leftover A-only layer commutes LEFT past BC,
  -- then absorbs into the AB gate — no fourth real embed is needed.
  rw [embedBC_comm_singleQubitLayer_A
        (kron2 I₂ u₂C * V₃ * kron2 u'B u'C) u'A]
  rw [show embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
        singleQubitLayer I₂ I₂ (I₂ * I₂) *
        embedAB (kron2 (I₂ * I₂) (u_pB * u₁B) * V₂ * kron2 u₂A u₂B) *
        singleQubitLayer I₂ I₂ I₂ *
        (singleQubitLayer u'A I₂ I₂ *
          embedBC (kron2 I₂ u₂C * V₃ * kron2 u'B u'C)) =
      embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
        singleQubitLayer I₂ I₂ (I₂ * I₂) *
        embedAB (kron2 (I₂ * I₂) (u_pB * u₁B) * V₂ * kron2 u₂A u₂B) *
        (singleQubitLayer I₂ I₂ I₂ * singleQubitLayer u'A I₂ I₂) *
        embedBC (kron2 I₂ u₂C * V₃ * kron2 u'B u'C) from by noncomm_ring]
  rw [singleQubitLayer_mul]
  rw [show embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
        singleQubitLayer I₂ I₂ (I₂ * I₂) *
        embedAB (kron2 (I₂ * I₂) (u_pB * u₁B) * V₂ * kron2 u₂A u₂B) *
        singleQubitLayer (I₂ * u'A) (I₂ * I₂) (I₂ * I₂) *
        embedBC (kron2 I₂ u₂C * V₃ * kron2 u'B u'C) =
      embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
        singleQubitLayer I₂ I₂ (I₂ * I₂) *
        (embedAB (kron2 (I₂ * I₂) (u_pB * u₁B) * V₂ * kron2 u₂A u₂B) *
          singleQubitLayer (I₂ * u'A) (I₂ * I₂) (I₂ * I₂)) *
        embedBC (kron2 I₂ u₂C * V₃ * kron2 u'B u'C) from by noncomm_ring]
  rw [embedAB_mul_singleQubitLayer
        (kron2 (I₂ * I₂) (u_pB * u₁B) * V₂ * kron2 u₂A u₂B)
        (I₂ * u'A) (I₂ * I₂) (I₂ * I₂)]
  -- Final: normalize I₂ = 1 and kill the two identity layers.
  have hSQL_one : (singleQubitLayer (1 : Mat2) 1 1 : Mat8) = 1 := singleQubitLayer_one
  simp only [I₂, mul_one, one_mul]
  rw [hSQL_one]
  noncomm_ring

/-- 3-gate sandwich, word `AB-AC-BC` → pattern #1 (BC-AC-AB-BC) with
    `V₁ = SWAP_4`.

    `AB-AC-BC` is the one 3-gate all-different ordering that fits NO canonical
    pattern by padding (all six of `X-AB-AC-BC` / `AB-AC-BC-X` were checked
    against the nine patterns). It is closed instead by the paper's own device
    (Appendix C, Lemma C.1, move 2): *insert SWAP gates that cancel out*.

    Write `S = SWAP_BC`. Then `M = S · (S·M·S) · S`, and conjugating the word
    factor-by-factor with `swap_bc_embedAB / swap_bc_embedAC / swap_bc_embedBC /
    swap_bc_singleQubitLayer` turns `AB-AC-BC` into `AC-AB-BC` with every
    layer's B and C entries swapped. That word is exactly
    `sandwich_AC_AB_BC_to_4embed` (iter 1038). Conjugating back, the leading `S`
    IS the pattern's leading BC slot (`SWAP_BC = embedBC SWAP_4`) and the
    trailing `S` merges into the trailing BC gate — so the two inserted SWAPs
    cost zero extra gates, precisely as in the paper. -/
private lemma sandwich_AB_AC_BC_to_4embed (V₁ V₂ V₃ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
      singleQubitLayer u'A u'B u'C =
    embedBC SWAP_4 *
      embedAC (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
      embedAB (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂A u₂C * kron2 u'A 1) *
      embedBC (kron2 1 u₂B * (SWAP_4 * V₃ * SWAP_4) * kron2 u'C u'B * SWAP_4) := by
  have hSS : ∀ X : Mat8, SWAP_BC * (SWAP_BC * X) = X := fun X => by
    rw [← mul_assoc, SWAP_BC_sq, one_mul]
  have hdc : ∀ X : Mat8, SWAP_BC * (SWAP_BC * X * SWAP_BC) * SWAP_BC = X := fun X => by
    rw [show SWAP_BC * (SWAP_BC * X * SWAP_BC) * SWAP_BC
          = (SWAP_BC * SWAP_BC) * X * (SWAP_BC * SWAP_BC) from by noncomm_ring,
       SWAP_BC_sq, one_mul, mul_one]
  -- The conjugated word is `AC-AB-BC` with B/C entries of every layer swapped.
  have key := sandwich_AC_AB_BC_to_4embed V₁ V₂ (SWAP_4 * V₃ * SWAP_4)
    u_pA u_pC u_pB u₁A u₁C u₁B u₂A u₂C u₂B u'A u'C u'B
  have hconj :
      SWAP_BC * (singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
        singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
        singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
        singleQubitLayer u'A u'B u'C) * SWAP_BC =
      singleQubitLayer u_pA u_pC u_pB * embedAC V₁ *
        singleQubitLayer u₁A u₁C u₁B * embedAB V₂ *
        singleQubitLayer u₂A u₂C u₂B * embedBC (SWAP_4 * V₃ * SWAP_4) *
        singleQubitLayer u'A u'C u'B := by
    conv_rhs => rw [← swap_bc_singleQubitLayer u_pA u_pB u_pC,
                    ← swap_bc_embedAB V₁,
                    ← swap_bc_singleQubitLayer u₁A u₁B u₁C,
                    ← swap_bc_embedAC V₂,
                    ← swap_bc_singleQubitLayer u₂A u₂B u₂C,
                    ← swap_bc_embedBC V₃,
                    ← swap_bc_singleQubitLayer u'A u'B u'C]
    simp only [mul_assoc, hSS]
  calc singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
        singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
        singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
        singleQubitLayer u'A u'B u'C
      = SWAP_BC * (SWAP_BC * (singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u'A u'B u'C) * SWAP_BC) * SWAP_BC := (hdc _).symm
    _ = SWAP_BC * (embedAC (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedAB (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂A u₂C * kron2 u'A 1) *
          embedBC (kron2 1 u₂B * (SWAP_4 * V₃ * SWAP_4) * kron2 u'C u'B)) * SWAP_BC := by
        rw [hconj, key]
    _ = embedBC SWAP_4 *
          embedAC (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedAB (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂A u₂C * kron2 u'A 1) *
          embedBC (kron2 1 u₂B * (SWAP_4 * V₃ * SWAP_4) * kron2 u'C u'B * SWAP_4) := by
        rw [show embedBC (kron2 1 u₂B * (SWAP_4 * V₃ * SWAP_4) * kron2 u'C u'B * SWAP_4)
              = embedBC (kron2 1 u₂B * (SWAP_4 * V₃ * SWAP_4) * kron2 u'C u'B) *
                embedBC SWAP_4 from (embedBC_mul _ _).symm]
        rw [SWAP_BC_eq_embedBC]
        noncomm_ring

/-! ## Paper Appendix C, Table 4: SWAP insertion that cancels out (iter 1040)

Huang & Palsberg's proof of Lemma C.1 turns a non-canonical 4-gate word into a
canonical one by *"inserting SWAP gates that cancel out and by using
associativity"*. The device is always the same: if a contiguous block of gates
is flanked on BOTH sides by gates of one type `Y`, then inserting `S_Y · S_Y = 1`
on each side of the block costs nothing — each inserted `S_Y` is itself a
`Y`-gate (`SWAP_Y = embedY SWAP_4`) and is absorbed into the flanking `Y` gate.
Conjugation by `S_Y` fixes type `Y` and TRANSPOSES the other two types, so the
block is re-typed for free.

The lemmas below package the three flanking positions that occur in
`unitaryUnrestrictedCircuit_4_canonical_direct`:
* `retype3_*` — gates 2 and 4 share type `Y`, gate 3 is re-typed;
* `retype2_*` — gates 1 and 3 share type `Y`, gate 2 is re-typed;
* `retype23_*` — gates 1 and 4 share type `Y`, gates 2 and 3 are both re-typed.
The remaining gate stays abstract as a `Mat8`, so one lemma serves every leaf
with that (position, type) signature. -/

private lemma embedAB_swap4_right (V : Mat4) :
    embedAB (V * SWAP_4) = embedAB V * SWAP_AB := by
  rw [SWAP_AB_eq_embedAB, embedAB_mul]

private lemma embedAB_swap4_left (V : Mat4) :
    embedAB (SWAP_4 * V) = SWAP_AB * embedAB V := by
  rw [SWAP_AB_eq_embedAB, embedAB_mul]

private lemma embedAC_swap4_right (V : Mat4) :
    embedAC (V * SWAP_4) = embedAC V * SWAP_AC := by
  rw [SWAP_AC_eq_embedAC, embedAC_mul]

private lemma embedAC_swap4_left (V : Mat4) :
    embedAC (SWAP_4 * V) = SWAP_AC * embedAC V := by
  rw [SWAP_AC_eq_embedAC, embedAC_mul]

private lemma embedBC_swap4_right (V : Mat4) :
    embedBC (V * SWAP_4) = embedBC V * SWAP_BC := by
  rw [SWAP_BC_eq_embedBC, embedBC_mul]

private lemma embedBC_swap4_left (V : Mat4) :
    embedBC (SWAP_4 * V) = SWAP_BC * embedBC V := by
  rw [SWAP_BC_eq_embedBC, embedBC_mul]

/-- Gates 2,4 are AB; gate 3 (AC) is re-typed to BC. Table 4 row 1. -/
private lemma retype3_AB_AC_to_BC (M₁ : Mat8) (V₂ V₃ V₄ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * M₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
      singleQubitLayer u₃A u₃B u₃C * embedAB V₄ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA u_pB u_pC * M₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAB (V₂ * SWAP_4) *
      singleQubitLayer u₂B u₂A u₂C * embedBC V₃ *
      singleQubitLayer u₃B u₃A u₃C * embedAB (SWAP_4 * V₄) *
      singleQubitLayer u'A u'B u'C := by
  conv_rhs => rw [embedAB_swap4_right, ← swap_ab_singleQubitLayer u₂A u₂B u₂C,
                  ← swap_ab_embedAC V₃, ← swap_ab_singleQubitLayer u₃A u₃B u₃C,
                  embedAB_swap4_left]
  simp only [mul_assoc, swap_ab_cancel]

/-- Gates 2,4 are AB; gate 3 (BC) is re-typed to AC. -/
private lemma retype3_AB_BC_to_AC (M₁ : Mat8) (V₂ V₃ V₄ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * M₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
      singleQubitLayer u₃A u₃B u₃C * embedAB V₄ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA u_pB u_pC * M₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAB (V₂ * SWAP_4) *
      singleQubitLayer u₂B u₂A u₂C * embedAC V₃ *
      singleQubitLayer u₃B u₃A u₃C * embedAB (SWAP_4 * V₄) *
      singleQubitLayer u'A u'B u'C := by
  conv_rhs => rw [embedAB_swap4_right, ← swap_ab_singleQubitLayer u₂A u₂B u₂C,
                  ← swap_ab_embedBC V₃, ← swap_ab_singleQubitLayer u₃A u₃B u₃C,
                  embedAB_swap4_left]
  simp only [mul_assoc, swap_ab_cancel]

/-- Gates 2,4 are BC; gate 3 (AB) is re-typed to AC. -/
private lemma retype3_BC_AB_to_AC (M₁ : Mat8) (V₂ V₃ V₄ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * M₁ *
      singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
      singleQubitLayer u₃A u₃B u₃C * embedBC V₄ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA u_pB u_pC * M₁ *
      singleQubitLayer u₁A u₁B u₁C * embedBC (V₂ * SWAP_4) *
      singleQubitLayer u₂A u₂C u₂B * embedAC V₃ *
      singleQubitLayer u₃A u₃C u₃B * embedBC (SWAP_4 * V₄) *
      singleQubitLayer u'A u'B u'C := by
  conv_rhs => rw [embedBC_swap4_right, ← swap_bc_singleQubitLayer u₂A u₂B u₂C,
                  ← swap_bc_embedAB V₃, ← swap_bc_singleQubitLayer u₃A u₃B u₃C,
                  embedBC_swap4_left]
  simp only [mul_assoc, swap_bc_cancel]

/-- Gates 2,4 are BC; gate 3 (AC) is re-typed to AB. -/
private lemma retype3_BC_AC_to_AB (M₁ : Mat8) (V₂ V₃ V₄ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * M₁ *
      singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
      singleQubitLayer u₃A u₃B u₃C * embedBC V₄ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA u_pB u_pC * M₁ *
      singleQubitLayer u₁A u₁B u₁C * embedBC (V₂ * SWAP_4) *
      singleQubitLayer u₂A u₂C u₂B * embedAB V₃ *
      singleQubitLayer u₃A u₃C u₃B * embedBC (SWAP_4 * V₄) *
      singleQubitLayer u'A u'B u'C := by
  conv_rhs => rw [embedBC_swap4_right, ← swap_bc_singleQubitLayer u₂A u₂B u₂C,
                  ← swap_bc_embedAC V₃, ← swap_bc_singleQubitLayer u₃A u₃B u₃C,
                  embedBC_swap4_left]
  simp only [mul_assoc, swap_bc_cancel]

/-- Gates 2,4 are AC; gate 3 (AB) is re-typed to BC (SWAP_4-conjugated). -/
private lemma retype3_AC_AB_to_BC (M₁ : Mat8) (V₂ V₃ V₄ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * M₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
      singleQubitLayer u₃A u₃B u₃C * embedAC V₄ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA u_pB u_pC * M₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAC (V₂ * SWAP_4) *
      singleQubitLayer u₂C u₂B u₂A * embedBC (SWAP_4 * V₃ * SWAP_4) *
      singleQubitLayer u₃C u₃B u₃A * embedAC (SWAP_4 * V₄) *
      singleQubitLayer u'A u'B u'C := by
  conv_rhs => rw [embedAC_swap4_right, ← swap_ac_singleQubitLayer u₂A u₂B u₂C,
                  ← swap_ac_embedAB V₃, ← swap_ac_singleQubitLayer u₃A u₃B u₃C,
                  embedAC_swap4_left]
  simp only [mul_assoc, swap_ac_cancel]

/-- Gates 2,4 are AC; gate 3 (BC) is re-typed to AB (SWAP_4-conjugated). -/
private lemma retype3_AC_BC_to_AB (M₁ : Mat8) (V₂ V₃ V₄ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * M₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
      singleQubitLayer u₃A u₃B u₃C * embedAC V₄ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA u_pB u_pC * M₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAC (V₂ * SWAP_4) *
      singleQubitLayer u₂C u₂B u₂A * embedAB (SWAP_4 * V₃ * SWAP_4) *
      singleQubitLayer u₃C u₃B u₃A * embedAC (SWAP_4 * V₄) *
      singleQubitLayer u'A u'B u'C := by
  conv_rhs => rw [embedAC_swap4_right, ← swap_ac_singleQubitLayer u₂A u₂B u₂C,
                  ← swap_ac_embedBC V₃, ← swap_ac_singleQubitLayer u₃A u₃B u₃C,
                  embedAC_swap4_left]
  simp only [mul_assoc, swap_ac_cancel]

/-- Gates 1,3 are BC; gate 2 (AC) is re-typed to AB. Table 4 row 7. -/
private lemma retype2_BC_AC_to_AB (M₄ : Mat8) (V₁ V₂ V₃ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
      singleQubitLayer u₃A u₃B u₃C * M₄ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA u_pB u_pC * embedBC (V₁ * SWAP_4) *
      singleQubitLayer u₁A u₁C u₁B * embedAB V₂ *
      singleQubitLayer u₂A u₂C u₂B * embedBC (SWAP_4 * V₃) *
      singleQubitLayer u₃A u₃B u₃C * M₄ *
      singleQubitLayer u'A u'B u'C := by
  conv_rhs => rw [embedBC_swap4_right, ← swap_bc_singleQubitLayer u₁A u₁B u₁C,
                  ← swap_bc_embedAC V₂, ← swap_bc_singleQubitLayer u₂A u₂B u₂C,
                  embedBC_swap4_left]
  simp only [mul_assoc, swap_bc_cancel]

/-- Gates 1,3 are BC; gate 2 (AB) is re-typed to AC. Table 4 row 4. -/
private lemma retype2_BC_AB_to_AC (M₄ : Mat8) (V₁ V₂ V₃ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
      singleQubitLayer u₃A u₃B u₃C * M₄ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA u_pB u_pC * embedBC (V₁ * SWAP_4) *
      singleQubitLayer u₁A u₁C u₁B * embedAC V₂ *
      singleQubitLayer u₂A u₂C u₂B * embedBC (SWAP_4 * V₃) *
      singleQubitLayer u₃A u₃B u₃C * M₄ *
      singleQubitLayer u'A u'B u'C := by
  conv_rhs => rw [embedBC_swap4_right, ← swap_bc_singleQubitLayer u₁A u₁B u₁C,
                  ← swap_bc_embedAB V₂, ← swap_bc_singleQubitLayer u₂A u₂B u₂C,
                  embedBC_swap4_left]
  simp only [mul_assoc, swap_bc_cancel]

/-- Gates 1,3 are AC; gate 2 (BC) is re-typed to AB (SWAP_4-conjugated). -/
private lemma retype2_AC_BC_to_AB (M₄ : Mat8) (V₁ V₂ V₃ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
      singleQubitLayer u₃A u₃B u₃C * M₄ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA u_pB u_pC * embedAC (V₁ * SWAP_4) *
      singleQubitLayer u₁C u₁B u₁A * embedAB (SWAP_4 * V₂ * SWAP_4) *
      singleQubitLayer u₂C u₂B u₂A * embedAC (SWAP_4 * V₃) *
      singleQubitLayer u₃A u₃B u₃C * M₄ *
      singleQubitLayer u'A u'B u'C := by
  conv_rhs => rw [embedAC_swap4_right, ← swap_ac_singleQubitLayer u₁A u₁B u₁C,
                  ← swap_ac_embedBC V₂, ← swap_ac_singleQubitLayer u₂A u₂B u₂C,
                  embedAC_swap4_left]
  simp only [mul_assoc, swap_ac_cancel]

/-- Gates 1,4 are AB; gates 2 (AC) and 3 (BC) swap types. Table 4 row 2. -/
private lemma retype23_AB (V₁ V₂ V₃ V₄ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
      singleQubitLayer u₃A u₃B u₃C * embedAB V₄ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA u_pB u_pC * embedAB (V₁ * SWAP_4) *
      singleQubitLayer u₁B u₁A u₁C * embedBC V₂ *
      singleQubitLayer u₂B u₂A u₂C * embedAC V₃ *
      singleQubitLayer u₃B u₃A u₃C * embedAB (SWAP_4 * V₄) *
      singleQubitLayer u'A u'B u'C := by
  conv_rhs => rw [embedAB_swap4_right, ← swap_ab_singleQubitLayer u₁A u₁B u₁C,
                  ← swap_ab_embedAC V₂, ← swap_ab_singleQubitLayer u₂A u₂B u₂C,
                  ← swap_ab_embedBC V₃, ← swap_ab_singleQubitLayer u₃A u₃B u₃C,
                  embedAB_swap4_left]
  simp only [mul_assoc, swap_ab_cancel]

/-- Gates 1,4 are AC; gates 2 (AB) and 3 (BC) swap types (SWAP_4-conjugated). -/
private lemma retype23_AC (V₁ V₂ V₃ V₄ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
      singleQubitLayer u₃A u₃B u₃C * embedAC V₄ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA u_pB u_pC * embedAC (V₁ * SWAP_4) *
      singleQubitLayer u₁C u₁B u₁A * embedBC (SWAP_4 * V₂ * SWAP_4) *
      singleQubitLayer u₂C u₂B u₂A * embedAB (SWAP_4 * V₃ * SWAP_4) *
      singleQubitLayer u₃C u₃B u₃A * embedAC (SWAP_4 * V₄) *
      singleQubitLayer u'A u'B u'C := by
  conv_rhs => rw [embedAC_swap4_right, ← swap_ac_singleQubitLayer u₁A u₁B u₁C,
                  ← swap_ac_embedAB V₂, ← swap_ac_singleQubitLayer u₂A u₂B u₂C,
                  ← swap_ac_embedBC V₃, ← swap_ac_singleQubitLayer u₃A u₃B u₃C,
                  embedAC_swap4_left]
  simp only [mul_assoc, swap_ac_cancel]

/-- Gates 1,3 are AB; gate 2 (AC) is re-typed to BC. -/
private lemma retype2_AB_AC_to_BC (M₄ : Mat8) (V₁ V₂ V₃ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
      singleQubitLayer u₃A u₃B u₃C * M₄ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA u_pB u_pC * embedAB (V₁ * SWAP_4) *
      singleQubitLayer u₁B u₁A u₁C * embedBC V₂ *
      singleQubitLayer u₂B u₂A u₂C * embedAB (SWAP_4 * V₃) *
      singleQubitLayer u₃A u₃B u₃C * M₄ *
      singleQubitLayer u'A u'B u'C := by
  conv_rhs => rw [embedAB_swap4_right, ← swap_ab_singleQubitLayer u₁A u₁B u₁C,
                  ← swap_ab_embedAC V₂, ← swap_ab_singleQubitLayer u₂A u₂B u₂C,
                  embedAB_swap4_left]
  simp only [mul_assoc, swap_ab_cancel]

/-- Gates 1,3 are AB; gate 2 (BC) is re-typed to AC. -/
private lemma retype2_AB_BC_to_AC (M₄ : Mat8) (V₁ V₂ V₃ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
      singleQubitLayer u₃A u₃B u₃C * M₄ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA u_pB u_pC * embedAB (V₁ * SWAP_4) *
      singleQubitLayer u₁B u₁A u₁C * embedAC V₂ *
      singleQubitLayer u₂B u₂A u₂C * embedAB (SWAP_4 * V₃) *
      singleQubitLayer u₃A u₃B u₃C * M₄ *
      singleQubitLayer u'A u'B u'C := by
  conv_rhs => rw [embedAB_swap4_right, ← swap_ab_singleQubitLayer u₁A u₁B u₁C,
                  ← swap_ab_embedBC V₂, ← swap_ab_singleQubitLayer u₂A u₂B u₂C,
                  embedAB_swap4_left]
  simp only [mul_assoc, swap_ab_cancel]

/-- Gates 1,3 are AC; gate 2 (AB) is re-typed to BC (SWAP_4-conjugated). -/
private lemma retype2_AC_AB_to_BC (M₄ : Mat8) (V₁ V₂ V₃ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
      singleQubitLayer u₃A u₃B u₃C * M₄ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA u_pB u_pC * embedAC (V₁ * SWAP_4) *
      singleQubitLayer u₁C u₁B u₁A * embedBC (SWAP_4 * V₂ * SWAP_4) *
      singleQubitLayer u₂C u₂B u₂A * embedAC (SWAP_4 * V₃) *
      singleQubitLayer u₃A u₃B u₃C * M₄ *
      singleQubitLayer u'A u'B u'C := by
  conv_rhs => rw [embedAC_swap4_right, ← swap_ac_singleQubitLayer u₁A u₁B u₁C,
                  ← swap_ac_embedAB V₂, ← swap_ac_singleQubitLayer u₂A u₂B u₂C,
                  embedAC_swap4_left]
  simp only [mul_assoc, swap_ac_cancel]

/-- Gates 1,4 are BC; gates 2 (AB) and 3 (AC) swap types. -/
private lemma retype23_BC (V₁ V₂ V₃ V₄ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
      singleQubitLayer u₃A u₃B u₃C * embedBC V₄ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA u_pB u_pC * embedBC (V₁ * SWAP_4) *
      singleQubitLayer u₁A u₁C u₁B * embedAC V₂ *
      singleQubitLayer u₂A u₂C u₂B * embedAB V₃ *
      singleQubitLayer u₃A u₃C u₃B * embedBC (SWAP_4 * V₄) *
      singleQubitLayer u'A u'B u'C := by
  conv_rhs => rw [embedBC_swap4_right, ← swap_bc_singleQubitLayer u₁A u₁B u₁C,
                  ← swap_bc_embedAB V₂, ← swap_bc_singleQubitLayer u₂A u₂B u₂C,
                  ← swap_bc_embedAC V₃, ← swap_bc_singleQubitLayer u₃A u₃B u₃C,
                  embedBC_swap4_left]
  simp only [mul_assoc, swap_bc_cancel]

/-! ### 4-gate adjacent-pair merge at slots (1,2) -/

private lemma merge12_AB (V₁ V₂ : Mat4) (M₃ M₄ : Mat8)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
      singleQubitLayer u₂A u₂B u₂C * M₃ *
      singleQubitLayer u₃A u₃B u₃C * M₄ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA u_pB (u_pC * u₁C) *
      embedAB (V₁ * (kron2 u₁A u₁B * V₂)) *
      singleQubitLayer u₂A u₂B u₂C * M₃ *
      singleQubitLayer u₃A u₃B u₃C * M₄ *
      singleQubitLayer u'A u'B u'C := by
  rw [show singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
            singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
            singleQubitLayer u₂A u₂B u₂C * M₃ *
            singleQubitLayer u₃A u₃B u₃C * M₄ *
            singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA u_pB u_pC *
          (embedAB V₁ * singleQubitLayer u₁A u₁B u₁C * embedAB V₂) *
          singleQubitLayer u₂A u₂B u₂C * M₃ *
          singleQubitLayer u₃A u₃B u₃C * M₄ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAB_merge]
  rw [show singleQubitLayer u_pA u_pB u_pC *
            (singleQubitLayer I₂ I₂ u₁C * embedAB (V₁ * (kron2 u₁A u₁B * V₂))) *
            singleQubitLayer u₂A u₂B u₂C * M₃ *
            singleQubitLayer u₃A u₃B u₃C * M₄ *
            singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC * singleQubitLayer I₂ I₂ u₁C) *
          embedAB (V₁ * (kron2 u₁A u₁B * V₂)) *
          singleQubitLayer u₂A u₂B u₂C * M₃ *
          singleQubitLayer u₃A u₃B u₃C * M₄ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul]
  simp [I₂]

private lemma merge12_AC (V₁ V₂ : Mat4) (M₃ M₄ : Mat8)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
      singleQubitLayer u₂A u₂B u₂C * M₃ *
      singleQubitLayer u₃A u₃B u₃C * M₄ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA (u_pB * u₁B) u_pC *
      embedAC (V₁ * (kron2 u₁A u₁C * V₂)) *
      singleQubitLayer u₂A u₂B u₂C * M₃ *
      singleQubitLayer u₃A u₃B u₃C * M₄ *
      singleQubitLayer u'A u'B u'C := by
  rw [show singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
            singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
            singleQubitLayer u₂A u₂B u₂C * M₃ *
            singleQubitLayer u₃A u₃B u₃C * M₄ *
            singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA u_pB u_pC *
          (embedAC V₁ * singleQubitLayer u₁A u₁B u₁C * embedAC V₂) *
          singleQubitLayer u₂A u₂B u₂C * M₃ *
          singleQubitLayer u₃A u₃B u₃C * M₄ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAC_merge]
  rw [show singleQubitLayer u_pA u_pB u_pC *
            (singleQubitLayer I₂ u₁B I₂ * embedAC (V₁ * (kron2 u₁A u₁C * V₂))) *
            singleQubitLayer u₂A u₂B u₂C * M₃ *
            singleQubitLayer u₃A u₃B u₃C * M₄ *
            singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC * singleQubitLayer I₂ u₁B I₂) *
          embedAC (V₁ * (kron2 u₁A u₁C * V₂)) *
          singleQubitLayer u₂A u₂B u₂C * M₃ *
          singleQubitLayer u₃A u₃B u₃C * M₄ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul]
  simp [I₂]

private lemma merge12_BC (V₁ V₂ : Mat4) (M₃ M₄ : Mat8)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
      singleQubitLayer u₂A u₂B u₂C * M₃ *
      singleQubitLayer u₃A u₃B u₃C * M₄ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer (u_pA * u₁A) u_pB u_pC *
      embedBC (V₁ * (kron2 u₁B u₁C * V₂)) *
      singleQubitLayer u₂A u₂B u₂C * M₃ *
      singleQubitLayer u₃A u₃B u₃C * M₄ *
      singleQubitLayer u'A u'B u'C := by
  rw [show singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
            singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
            singleQubitLayer u₂A u₂B u₂C * M₃ *
            singleQubitLayer u₃A u₃B u₃C * M₄ *
            singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA u_pB u_pC *
          (embedBC V₁ * singleQubitLayer u₁A u₁B u₁C * embedBC V₂) *
          singleQubitLayer u₂A u₂B u₂C * M₃ *
          singleQubitLayer u₃A u₃B u₃C * M₄ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedBC_merge]
  rw [show singleQubitLayer u_pA u_pB u_pC *
            (singleQubitLayer u₁A I₂ I₂ * embedBC (V₁ * (kron2 u₁B u₁C * V₂))) *
            singleQubitLayer u₂A u₂B u₂C * M₃ *
            singleQubitLayer u₃A u₃B u₃C * M₄ *
            singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC * singleQubitLayer u₁A I₂ I₂) *
          embedBC (V₁ * (kron2 u₁B u₁C * V₂)) *
          singleQubitLayer u₂A u₂B u₂C * M₃ *
          singleQubitLayer u₃A u₃B u₃C * M₄ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul]
  simp [I₂]

/-- Pads a 3-gate `AC-AB-BC` canonical form with a leading `embedBC 1`, turning
    it into disjunct #1 (`BC-AC-AB-BC`). -/
private lemma pad_BC_one (A B C : Mat4) (M : Mat8)
    (h : M = embedAC A * embedAB B * embedBC C) :
    M = embedBC 1 * embedAC A * embedAB B * embedBC C := by
  rw [h, embedBC_one, one_mul]

/-- Pads a 3-gate `BC-AB-AC` canonical form with a leading `embedAC 1`, turning
    it into disjunct #3 (`AC-BC-AB-AC`). -/
private lemma pad_AC_one (A B C : Mat4) (M : Mat8)
    (h : M = embedBC A * embedAB B * embedAC C) :
    M = embedAC 1 * embedBC A * embedAB B * embedAC C := by
  rw [h, embedAC_one, one_mul]

set_option maxHeartbeats 800000 in
-- Heartbeats raised: 9-factor chain with six sequential `noncomm_ring` re-brackets.
/-- 4-gate sandwich for pattern #1 (BC-AC-AB-BC). Extends
    `sandwich_BC_AC_AB_to_4embed` by one trailing BC gate; the leftover layer is
    A-only, commutes back past the BC gate and absorbs into the AB gate. -/
private lemma sandwich_BC_AC_AB_BC_to_4embed
    (V₁ V₂ V₃ V₄ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
      singleQubitLayer u₃A u₃B u₃C * embedBC V₄ *
      singleQubitLayer u'A u'B u'C =
    embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
      embedAC (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂C) *
      embedAB (kron2 1 u₂B * V₃ * kron2 u₃A u₃B * kron2 u'A 1) *
      embedBC (kron2 1 u₃C * V₄ * kron2 u'B u'C) := by
  rw [show
        singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u₃A u₃B u₃C * embedBC V₄ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u₃A u₃B u₃C) *
          embedBC V₄ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [sandwich_BC_AC_AB_to_4embed V₁ V₂ V₃
        u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C]
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAC (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂C) *
          embedAB (kron2 1 u₂B * V₃ * kron2 u₃A u₃B) *
          embedBC (kron2 1 u₃C) *
          embedBC V₄ *
          singleQubitLayer u'A u'B u'C =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAC (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂C) *
          embedAB (kron2 1 u₂B * V₃ * kron2 u₃A u₃B) *
          (embedBC (kron2 1 u₃C) * embedBC V₄) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedBC_mul]
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAC (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂C) *
          embedAB (kron2 1 u₂B * V₃ * kron2 u₃A u₃B) *
          embedBC (kron2 1 u₃C * V₄) *
          singleQubitLayer u'A u'B u'C =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAC (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂C) *
          embedAB (kron2 1 u₂B * V₃ * kron2 u₃A u₃B) *
          (embedBC (kron2 1 u₃C * V₄) *
            singleQubitLayer u'A u'B u'C) from by noncomm_ring]
  rw [embedBC_mul_singleQubitLayer]
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAC (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂C) *
          embedAB (kron2 1 u₂B * V₃ * kron2 u₃A u₃B) *
          (embedBC (kron2 1 u₃C * V₄ * kron2 u'B u'C) *
            singleQubitLayer u'A I₂ I₂) =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAC (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂C) *
          embedAB (kron2 1 u₂B * V₃ * kron2 u₃A u₃B) *
          singleQubitLayer u'A I₂ I₂ *
          embedBC (kron2 1 u₃C * V₄ * kron2 u'B u'C) from by
        rw [embedBC_comm_singleQubitLayer_A]; noncomm_ring]
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAC (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂C) *
          embedAB (kron2 1 u₂B * V₃ * kron2 u₃A u₃B) *
          singleQubitLayer u'A I₂ I₂ *
          embedBC (kron2 1 u₃C * V₄ * kron2 u'B u'C) =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAC (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂C) *
          (embedAB (kron2 1 u₂B * V₃ * kron2 u₃A u₃B) *
            singleQubitLayer u'A I₂ I₂) *
          embedBC (kron2 1 u₃C * V₄ * kron2 u'B u'C) from by noncomm_ring]
  rw [embedAB_mul_singleQubitLayer]
  rw [show singleQubitLayer I₂ I₂ I₂ = (1 : Mat8) from singleQubitLayer_one]
  show _ = _
  simp only [I₂]
  noncomm_ring

set_option maxHeartbeats 800000 in
-- Heartbeats raised: 9-factor chain with six sequential `noncomm_ring` re-brackets.
/-- 4-gate sandwich for pattern #2 (AB-BC-AC-AB). Extends
    `sandwich_AB_BC_AC_to_4embed` by one trailing AB gate: merge the two AB
    embeds, absorb the trailing SQL's (A,B) part, commute the leftover C-only
    layer back past the AB gate and absorb it into the preceding AC gate. -/
private lemma sandwich_AB_BC_AC_AB_to_4embed
    (V₁ V₂ V₃ V₄ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
      singleQubitLayer u₃A u₃B u₃C * embedAB V₄ *
      singleQubitLayer u'A u'B u'C =
    embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
      embedBC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
      embedAC ((kron2 u₂A 1 * V₃ * kron2 u₃A u₃C) * kron2 1 u'C) *
      embedAB (kron2 1 u₃B * V₄ * kron2 u'A u'B) := by
  rw [show
        singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u₃A u₃B u₃C * embedAB V₄ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u₃A u₃B u₃C) *
          embedAB V₄ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [sandwich_AB_BC_AC_to_4embed V₁ V₂ V₃
        u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C]
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedBC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
          embedAC (kron2 u₂A 1 * V₃ * kron2 u₃A u₃C) *
          embedAB (kron2 1 u₃B) *
          embedAB V₄ *
          singleQubitLayer u'A u'B u'C =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedBC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
          embedAC (kron2 u₂A 1 * V₃ * kron2 u₃A u₃C) *
          (embedAB (kron2 1 u₃B) * embedAB V₄) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAB_mul]
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedBC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
          embedAC (kron2 u₂A 1 * V₃ * kron2 u₃A u₃C) *
          embedAB (kron2 1 u₃B * V₄) *
          singleQubitLayer u'A u'B u'C =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedBC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
          embedAC (kron2 u₂A 1 * V₃ * kron2 u₃A u₃C) *
          (embedAB (kron2 1 u₃B * V₄) *
            singleQubitLayer u'A u'B u'C) from by noncomm_ring]
  rw [embedAB_mul_singleQubitLayer]
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedBC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
          embedAC (kron2 u₂A 1 * V₃ * kron2 u₃A u₃C) *
          (embedAB (kron2 1 u₃B * V₄ * kron2 u'A u'B) *
            singleQubitLayer I₂ I₂ u'C) =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedBC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
          embedAC (kron2 u₂A 1 * V₃ * kron2 u₃A u₃C) *
          singleQubitLayer I₂ I₂ u'C *
          embedAB (kron2 1 u₃B * V₄ * kron2 u'A u'B) from by
        rw [embedAB_comm_singleQubitLayer_C]; noncomm_ring]
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedBC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
          embedAC (kron2 u₂A 1 * V₃ * kron2 u₃A u₃C) *
          singleQubitLayer I₂ I₂ u'C *
          embedAB (kron2 1 u₃B * V₄ * kron2 u'A u'B) =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedBC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
          (embedAC (kron2 u₂A 1 * V₃ * kron2 u₃A u₃C) *
            singleQubitLayer I₂ I₂ u'C) *
          embedAB (kron2 1 u₃B * V₄ * kron2 u'A u'B) from by noncomm_ring]
  rw [embedAC_mul_singleQubitLayer]
  rw [show singleQubitLayer I₂ I₂ I₂ = (1 : Mat8) from singleQubitLayer_one]
  show _ = _
  simp only [I₂]
  noncomm_ring

set_option maxHeartbeats 800000 in
-- Heartbeats raised: 9-factor chain with six sequential `noncomm_ring` re-brackets.
/-- 4-gate sandwich for pattern #3 (AC-BC-AB-AC). Extends
    `sandwich_AC_BC_AB_to_4embed` by one trailing AC gate; the leftover layer
    is B-only, commutes back past the AC gate and absorbs into the AB gate. -/
private lemma sandwich_AC_BC_AB_AC_to_4embed
    (V₁ V₂ V₃ V₄ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
      singleQubitLayer u₃A u₃B u₃C * embedAC V₄ *
      singleQubitLayer u'A u'B u'C =
    embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
      embedBC (kron2 (u_pB * u₁B) 1 * V₂ * kron2 u₂B u₂C) *
      embedAB ((kron2 u₂A 1 * V₃ * kron2 u₃A u₃B) * kron2 1 u'B) *
      embedAC (kron2 1 u₃C * V₄ * kron2 u'A u'C) := by
  rw [show
        singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u₃A u₃B u₃C * embedAC V₄ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u₃A u₃B u₃C) *
          embedAC V₄ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [sandwich_AC_BC_AB_to_4embed V₁ V₂ V₃
        u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C]
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedBC (kron2 (u_pB * u₁B) 1 * V₂ * kron2 u₂B u₂C) *
          embedAB (kron2 u₂A 1 * V₃ * kron2 u₃A u₃B) *
          embedAC (kron2 1 u₃C) *
          embedAC V₄ *
          singleQubitLayer u'A u'B u'C =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedBC (kron2 (u_pB * u₁B) 1 * V₂ * kron2 u₂B u₂C) *
          embedAB (kron2 u₂A 1 * V₃ * kron2 u₃A u₃B) *
          (embedAC (kron2 1 u₃C) * embedAC V₄) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAC_mul]
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedBC (kron2 (u_pB * u₁B) 1 * V₂ * kron2 u₂B u₂C) *
          embedAB (kron2 u₂A 1 * V₃ * kron2 u₃A u₃B) *
          embedAC (kron2 1 u₃C * V₄) *
          singleQubitLayer u'A u'B u'C =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedBC (kron2 (u_pB * u₁B) 1 * V₂ * kron2 u₂B u₂C) *
          embedAB (kron2 u₂A 1 * V₃ * kron2 u₃A u₃B) *
          (embedAC (kron2 1 u₃C * V₄) *
            singleQubitLayer u'A u'B u'C) from by noncomm_ring]
  rw [embedAC_mul_singleQubitLayer]
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedBC (kron2 (u_pB * u₁B) 1 * V₂ * kron2 u₂B u₂C) *
          embedAB (kron2 u₂A 1 * V₃ * kron2 u₃A u₃B) *
          (embedAC (kron2 1 u₃C * V₄ * kron2 u'A u'C) *
            singleQubitLayer I₂ u'B I₂) =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedBC (kron2 (u_pB * u₁B) 1 * V₂ * kron2 u₂B u₂C) *
          embedAB (kron2 u₂A 1 * V₃ * kron2 u₃A u₃B) *
          singleQubitLayer I₂ u'B I₂ *
          embedAC (kron2 1 u₃C * V₄ * kron2 u'A u'C) from by
        rw [embedAC_comm_singleQubitLayer_B]; noncomm_ring]
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedBC (kron2 (u_pB * u₁B) 1 * V₂ * kron2 u₂B u₂C) *
          embedAB (kron2 u₂A 1 * V₃ * kron2 u₃A u₃B) *
          singleQubitLayer I₂ u'B I₂ *
          embedAC (kron2 1 u₃C * V₄ * kron2 u'A u'C) =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedBC (kron2 (u_pB * u₁B) 1 * V₂ * kron2 u₂B u₂C) *
          (embedAB (kron2 u₂A 1 * V₃ * kron2 u₃A u₃B) *
            singleQubitLayer I₂ u'B I₂) *
          embedAC (kron2 1 u₃C * V₄ * kron2 u'A u'C) from by noncomm_ring]
  rw [embedAB_mul_singleQubitLayer]
  rw [show singleQubitLayer I₂ I₂ I₂ = (1 : Mat8) from singleQubitLayer_one]
  show _ = _
  simp only [I₂]
  noncomm_ring

set_option maxHeartbeats 800000 in
/-- 4-gate Pattern E sandwich: AC-AB-AC-AB chain with 5 SQLs collapses to
    4 embeds matching pattern #4 (AC-AB-AC-AB). Proved iter 659 by extending
    `sandwich_AC_AB_AC_to_4embed` via embedAB merge + SQL absorption +
    SQL/embedAB commutation + SQL absorption into preceding embedAC. -/
private lemma sandwich_AC_AB_AC_AB_to_4embed
    (V₁ V₂ V₃ V₄ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
      singleQubitLayer u₃A u₃B u₃C * embedAB V₄ *
      singleQubitLayer u'A u'B u'C =
    embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
      embedAB (kron2 1 (u_pB * u₁B) * V₂ * kron2 u₂A u₂B) *
      embedAC ((kron2 1 u₂C * V₃ * kron2 u₃A u₃C) * kron2 1 u'C) *
      embedAB (kron2 1 u₃B * V₄ * kron2 u'A u'B) := by
  -- Step 1: Re-bracket so first 7 factors are the AC-AB-AC sandwich input.
  rw [show
        singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u₃A u₃B u₃C * embedAB V₄ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u₃A u₃B u₃C) *
          embedAB V₄ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  -- Step 2: Apply sandwich_AC_AB_AC_to_4embed to first 7 factors.
  rw [sandwich_AC_AB_AC_to_4embed V₁ V₂ V₃
        u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C]
  -- Step 3: Re-bracket so the two consecutive embedAB factors are adjacent.
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedAB (kron2 1 (u_pB * u₁B) * V₂ * kron2 u₂A u₂B) *
          embedAC (kron2 1 u₂C * V₃ * kron2 u₃A u₃C) *
          embedAB (kron2 1 u₃B) *
          embedAB V₄ *
          singleQubitLayer u'A u'B u'C =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedAB (kron2 1 (u_pB * u₁B) * V₂ * kron2 u₂A u₂B) *
          embedAC (kron2 1 u₂C * V₃ * kron2 u₃A u₃C) *
          (embedAB (kron2 1 u₃B) * embedAB V₄) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAB_mul]
  -- Step 4: Re-bracket and absorb trailing SQL into the merged embedAB via
  --         embedAB_mul_singleQubitLayer (absorbs u'A, u'B, leaves SQL I I u'C).
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedAB (kron2 1 (u_pB * u₁B) * V₂ * kron2 u₂A u₂B) *
          embedAC (kron2 1 u₂C * V₃ * kron2 u₃A u₃C) *
          embedAB (kron2 1 u₃B * V₄) *
          singleQubitLayer u'A u'B u'C =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedAB (kron2 1 (u_pB * u₁B) * V₂ * kron2 u₂A u₂B) *
          embedAC (kron2 1 u₂C * V₃ * kron2 u₃A u₃C) *
          (embedAB (kron2 1 u₃B * V₄) *
            singleQubitLayer u'A u'B u'C) from by noncomm_ring]
  rw [embedAB_mul_singleQubitLayer]
  -- Step 5: Commute SQL I I u'C past trailing embedAB (disjoint qubits).
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedAB (kron2 1 (u_pB * u₁B) * V₂ * kron2 u₂A u₂B) *
          embedAC (kron2 1 u₂C * V₃ * kron2 u₃A u₃C) *
          (embedAB (kron2 1 u₃B * V₄ * kron2 u'A u'B) *
            singleQubitLayer I₂ I₂ u'C) =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedAB (kron2 1 (u_pB * u₁B) * V₂ * kron2 u₂A u₂B) *
          embedAC (kron2 1 u₂C * V₃ * kron2 u₃A u₃C) *
          singleQubitLayer I₂ I₂ u'C *
          embedAB (kron2 1 u₃B * V₄ * kron2 u'A u'B) from by
        rw [embedAB_comm_singleQubitLayer_C]; noncomm_ring]
  -- Step 6: Re-bracket and absorb SQL I I u'C into preceding embedAC.
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedAB (kron2 1 (u_pB * u₁B) * V₂ * kron2 u₂A u₂B) *
          embedAC (kron2 1 u₂C * V₃ * kron2 u₃A u₃C) *
          singleQubitLayer I₂ I₂ u'C *
          embedAB (kron2 1 u₃B * V₄ * kron2 u'A u'B) =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedAB (kron2 1 (u_pB * u₁B) * V₂ * kron2 u₂A u₂B) *
          (embedAC (kron2 1 u₂C * V₃ * kron2 u₃A u₃C) *
            singleQubitLayer I₂ I₂ u'C) *
          embedAB (kron2 1 u₃B * V₄ * kron2 u'A u'B) from by noncomm_ring]
  rw [embedAC_mul_singleQubitLayer]
  -- Trailing SQL I₂ I₂ I₂ = 1; final I₂ → 1 normalization.
  rw [show singleQubitLayer I₂ I₂ I₂ = (1 : Mat8) from singleQubitLayer_one]
  show _ = _
  simp only [I₂]
  noncomm_ring

set_option maxHeartbeats 800000 in
/-- 4-gate Pattern E sandwich: AB-AC-AB-AC chain with 5 SQLs collapses to
    4 embeds matching pattern #7 (AB-AC-AB-AC). Proved iter 662 by extending
    `sandwich_AB_AC_AB_to_4embed` via embedAC merge + SQL absorption +
    SQL/embedAC commutation + SQL absorption into preceding embedAB. -/
private lemma sandwich_AB_AC_AB_AC_to_4embed
    (V₁ V₂ V₃ V₄ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
      singleQubitLayer u₃A u₃B u₃C * embedAC V₄ *
      singleQubitLayer u'A u'B u'C =
    embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
      embedAC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂A u₂C) *
      embedAB (kron2 1 u₂B * V₃ * kron2 u₃A u₃B * kron2 1 u'B) *
      embedAC (kron2 1 u₃C * V₄ * kron2 u'A u'C) := by
  rw [show
        singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u₃A u₃B u₃C * embedAC V₄ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u₃A u₃B u₃C) *
          embedAC V₄ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [sandwich_AB_AC_AB_to_4embed V₁ V₂ V₃
        u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C]
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedAC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂A u₂C) *
          embedAB (kron2 1 u₂B * V₃ * kron2 u₃A u₃B) *
          embedAC (kron2 1 u₃C) *
          embedAC V₄ *
          singleQubitLayer u'A u'B u'C =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedAC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂A u₂C) *
          embedAB (kron2 1 u₂B * V₃ * kron2 u₃A u₃B) *
          (embedAC (kron2 1 u₃C) * embedAC V₄) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAC_mul]
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedAC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂A u₂C) *
          embedAB (kron2 1 u₂B * V₃ * kron2 u₃A u₃B) *
          embedAC (kron2 1 u₃C * V₄) *
          singleQubitLayer u'A u'B u'C =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedAC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂A u₂C) *
          embedAB (kron2 1 u₂B * V₃ * kron2 u₃A u₃B) *
          (embedAC (kron2 1 u₃C * V₄) *
            singleQubitLayer u'A u'B u'C) from by noncomm_ring]
  rw [embedAC_mul_singleQubitLayer]
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedAC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂A u₂C) *
          embedAB (kron2 1 u₂B * V₃ * kron2 u₃A u₃B) *
          (embedAC (kron2 1 u₃C * V₄ * kron2 u'A u'C) *
            singleQubitLayer I₂ u'B I₂) =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedAC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂A u₂C) *
          embedAB (kron2 1 u₂B * V₃ * kron2 u₃A u₃B) *
          singleQubitLayer I₂ u'B I₂ *
          embedAC (kron2 1 u₃C * V₄ * kron2 u'A u'C) from by
        rw [embedAC_comm_singleQubitLayer_B]; noncomm_ring]
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedAC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂A u₂C) *
          embedAB (kron2 1 u₂B * V₃ * kron2 u₃A u₃B) *
          singleQubitLayer I₂ u'B I₂ *
          embedAC (kron2 1 u₃C * V₄ * kron2 u'A u'C) =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedAC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂A u₂C) *
          (embedAB (kron2 1 u₂B * V₃ * kron2 u₃A u₃B) *
            singleQubitLayer I₂ u'B I₂) *
          embedAC (kron2 1 u₃C * V₄ * kron2 u'A u'C) from by noncomm_ring]
  rw [embedAB_mul_singleQubitLayer]
  rw [show singleQubitLayer I₂ I₂ I₂ = (1 : Mat8) from singleQubitLayer_one]
  show _ = _
  simp only [I₂]
  noncomm_ring

set_option maxHeartbeats 800000 in
/-- 4-gate Pattern E sandwich: BC-AC-BC-AC chain with 5 SQLs collapses to
    4 embeds matching pattern #6 (BC-AC-BC-AC). Proved iter 664 by extending
    `sandwich_BC_AC_BC_to_4embed` via embedAC merge + SQL absorption +
    SQL/embedAC commutation + SQL absorption into preceding embedBC. -/
private lemma sandwich_BC_AC_BC_AC_to_4embed
    (V₁ V₂ V₃ V₄ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
      singleQubitLayer u₃A u₃B u₃C * embedAC V₄ *
      singleQubitLayer u'A u'B u'C =
    embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
      embedAC (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂C) *
      embedBC (kron2 u₂B 1 * V₃ * kron2 u₃B u₃C * kron2 u'B 1) *
      embedAC (kron2 u₃A 1 * V₄ * kron2 u'A u'C) := by
  rw [show
        singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u₃A u₃B u₃C * embedAC V₄ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u₃A u₃B u₃C) *
          embedAC V₄ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [sandwich_BC_AC_BC_to_4embed V₁ V₂ V₃
        u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C]
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAC (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂C) *
          embedBC (kron2 u₂B 1 * V₃ * kron2 u₃B u₃C) *
          embedAC (kron2 u₃A 1) *
          embedAC V₄ *
          singleQubitLayer u'A u'B u'C =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAC (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂C) *
          embedBC (kron2 u₂B 1 * V₃ * kron2 u₃B u₃C) *
          (embedAC (kron2 u₃A 1) * embedAC V₄) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAC_mul]
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAC (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂C) *
          embedBC (kron2 u₂B 1 * V₃ * kron2 u₃B u₃C) *
          embedAC (kron2 u₃A 1 * V₄) *
          singleQubitLayer u'A u'B u'C =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAC (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂C) *
          embedBC (kron2 u₂B 1 * V₃ * kron2 u₃B u₃C) *
          (embedAC (kron2 u₃A 1 * V₄) *
            singleQubitLayer u'A u'B u'C) from by noncomm_ring]
  rw [embedAC_mul_singleQubitLayer]
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAC (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂C) *
          embedBC (kron2 u₂B 1 * V₃ * kron2 u₃B u₃C) *
          (embedAC (kron2 u₃A 1 * V₄ * kron2 u'A u'C) *
            singleQubitLayer I₂ u'B I₂) =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAC (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂C) *
          embedBC (kron2 u₂B 1 * V₃ * kron2 u₃B u₃C) *
          singleQubitLayer I₂ u'B I₂ *
          embedAC (kron2 u₃A 1 * V₄ * kron2 u'A u'C) from by
        rw [embedAC_comm_singleQubitLayer_B]; noncomm_ring]
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAC (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂C) *
          embedBC (kron2 u₂B 1 * V₃ * kron2 u₃B u₃C) *
          singleQubitLayer I₂ u'B I₂ *
          embedAC (kron2 u₃A 1 * V₄ * kron2 u'A u'C) =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAC (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂C) *
          (embedBC (kron2 u₂B 1 * V₃ * kron2 u₃B u₃C) *
            singleQubitLayer I₂ u'B I₂) *
          embedAC (kron2 u₃A 1 * V₄ * kron2 u'A u'C) from by noncomm_ring]
  rw [embedBC_mul_singleQubitLayer]
  rw [show singleQubitLayer I₂ I₂ I₂ = (1 : Mat8) from singleQubitLayer_one]
  show _ = _
  simp only [I₂]
  noncomm_ring

set_option maxHeartbeats 800000 in
/-- 4-gate Pattern E sandwich: BC-AB-BC-AB chain with 5 SQLs collapses to
    4 embeds matching pattern #5 (BC-AB-BC-AB). Proved iter 667 by extending
    `sandwich_BC_AB_BC_to_4embed` via embedAB merge + SQL absorption +
    SQL/embedAB commutation + SQL absorption into preceding embedBC. -/
private lemma sandwich_BC_AB_BC_AB_to_4embed
    (V₁ V₂ V₃ V₄ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
      singleQubitLayer u₃A u₃B u₃C * embedAB V₄ *
      singleQubitLayer u'A u'B u'C =
    embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
      embedAB (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂B) *
      embedBC (kron2 1 u₂C * V₃ * kron2 u₃B u₃C * kron2 1 u'C) *
      embedAB (kron2 u₃A 1 * V₄ * kron2 u'A u'B) := by
  rw [show
        singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u₃A u₃B u₃C * embedAB V₄ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
          singleQubitLayer u₃A u₃B u₃C) *
          embedAB V₄ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [sandwich_BC_AB_BC_to_4embed V₁ V₂ V₃
        u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C]
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAB (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂B) *
          embedBC (kron2 1 u₂C * V₃ * kron2 u₃B u₃C) *
          embedAB (kron2 u₃A 1) *
          embedAB V₄ *
          singleQubitLayer u'A u'B u'C =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAB (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂B) *
          embedBC (kron2 1 u₂C * V₃ * kron2 u₃B u₃C) *
          (embedAB (kron2 u₃A 1) * embedAB V₄) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAB_mul]
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAB (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂B) *
          embedBC (kron2 1 u₂C * V₃ * kron2 u₃B u₃C) *
          embedAB (kron2 u₃A 1 * V₄) *
          singleQubitLayer u'A u'B u'C =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAB (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂B) *
          embedBC (kron2 1 u₂C * V₃ * kron2 u₃B u₃C) *
          (embedAB (kron2 u₃A 1 * V₄) *
            singleQubitLayer u'A u'B u'C) from by noncomm_ring]
  rw [embedAB_mul_singleQubitLayer]
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAB (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂B) *
          embedBC (kron2 1 u₂C * V₃ * kron2 u₃B u₃C) *
          (embedAB (kron2 u₃A 1 * V₄ * kron2 u'A u'B) *
            singleQubitLayer I₂ I₂ u'C) =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAB (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂B) *
          embedBC (kron2 1 u₂C * V₃ * kron2 u₃B u₃C) *
          singleQubitLayer I₂ I₂ u'C *
          embedAB (kron2 u₃A 1 * V₄ * kron2 u'A u'B) from by
        rw [embedAB_comm_singleQubitLayer_C]; noncomm_ring]
  rw [show
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAB (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂B) *
          embedBC (kron2 1 u₂C * V₃ * kron2 u₃B u₃C) *
          singleQubitLayer I₂ I₂ u'C *
          embedAB (kron2 u₃A 1 * V₄ * kron2 u'A u'B) =
        embedBC (kron2 u_pB u_pC * V₁ * kron2 u₁B u₁C) *
          embedAB (kron2 (u_pA * u₁A) 1 * V₂ * kron2 u₂A u₂B) *
          (embedBC (kron2 1 u₂C * V₃ * kron2 u₃B u₃C) *
            singleQubitLayer I₂ I₂ u'C) *
          embedAB (kron2 u₃A 1 * V₄ * kron2 u'A u'B) from by noncomm_ring]
  rw [embedBC_mul_singleQubitLayer]
  rw [show singleQubitLayer I₂ I₂ I₂ = (1 : Mat8) from singleQubitLayer_one]
  show _ = _
  simp only [I₂]
  noncomm_ring

set_option maxHeartbeats 800000 in
/-- 4-gate Pattern E sandwich: AB-BC-AB-BC chain with 5 SQLs collapses to
    4 embeds matching pattern #8 (AB-BC-AB-BC). Proved iter 669 by extending
    `sandwich_AB_BC_AB_to_4embed` via embedBC merge + SQL absorption +
    SQL/embedBC commutation + SQL absorption into preceding embedAB. -/
private lemma sandwich_AB_BC_AB_BC_to_4embed
    (V₁ V₂ V₃ V₄ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
      singleQubitLayer u₃A u₃B u₃C * embedBC V₄ *
      singleQubitLayer u'A u'B u'C =
    embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
      embedBC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
      embedAB (kron2 u₂A 1 * V₃ * kron2 u₃A u₃B * kron2 u'A 1) *
      embedBC (kron2 1 u₃C * V₄ * kron2 u'B u'C) := by
  rw [show
        singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u₃A u₃B u₃C * embedBC V₄ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
          singleQubitLayer u₃A u₃B u₃C) *
          embedBC V₄ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [sandwich_AB_BC_AB_to_4embed V₁ V₂ V₃
        u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C]
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedBC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
          embedAB (kron2 u₂A 1 * V₃ * kron2 u₃A u₃B) *
          embedBC (kron2 1 u₃C) *
          embedBC V₄ *
          singleQubitLayer u'A u'B u'C =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedBC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
          embedAB (kron2 u₂A 1 * V₃ * kron2 u₃A u₃B) *
          (embedBC (kron2 1 u₃C) * embedBC V₄) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedBC_mul]
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedBC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
          embedAB (kron2 u₂A 1 * V₃ * kron2 u₃A u₃B) *
          embedBC (kron2 1 u₃C * V₄) *
          singleQubitLayer u'A u'B u'C =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedBC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
          embedAB (kron2 u₂A 1 * V₃ * kron2 u₃A u₃B) *
          (embedBC (kron2 1 u₃C * V₄) *
            singleQubitLayer u'A u'B u'C) from by noncomm_ring]
  rw [embedBC_mul_singleQubitLayer]
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedBC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
          embedAB (kron2 u₂A 1 * V₃ * kron2 u₃A u₃B) *
          (embedBC (kron2 1 u₃C * V₄ * kron2 u'B u'C) *
            singleQubitLayer u'A I₂ I₂) =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedBC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
          embedAB (kron2 u₂A 1 * V₃ * kron2 u₃A u₃B) *
          singleQubitLayer u'A I₂ I₂ *
          embedBC (kron2 1 u₃C * V₄ * kron2 u'B u'C) from by
        rw [embedBC_comm_singleQubitLayer_A]; noncomm_ring]
  rw [show
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedBC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
          embedAB (kron2 u₂A 1 * V₃ * kron2 u₃A u₃B) *
          singleQubitLayer u'A I₂ I₂ *
          embedBC (kron2 1 u₃C * V₄ * kron2 u'B u'C) =
        embedAB (kron2 u_pA u_pB * V₁ * kron2 u₁A u₁B) *
          embedBC (kron2 1 (u_pC * u₁C) * V₂ * kron2 u₂B u₂C) *
          (embedAB (kron2 u₂A 1 * V₃ * kron2 u₃A u₃B) *
            singleQubitLayer u'A I₂ I₂) *
          embedBC (kron2 1 u₃C * V₄ * kron2 u'B u'C) from by noncomm_ring]
  rw [embedAB_mul_singleQubitLayer]
  rw [show singleQubitLayer I₂ I₂ I₂ = (1 : Mat8) from singleQubitLayer_one]
  show _ = _
  simp only [I₂]
  noncomm_ring

set_option maxHeartbeats 800000 in
/-- 4-gate Pattern E sandwich: AC-BC-AC-BC chain with 5 SQLs collapses to
    4 embeds matching pattern #9 (AC-BC-AC-BC). Proved iter 671 by extending
    `sandwich_AC_BC_AC_to_4embed` via embedBC merge + SQL absorption +
    SQL/embedBC commutation + SQL absorption into preceding embedAC.
    Final Pattern E helper — all 6 alternating patterns now have 4-gate
    sandwich infrastructure. -/
private lemma sandwich_AC_BC_AC_BC_to_4embed
    (V₁ V₂ V₃ V₄ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
      singleQubitLayer u₃A u₃B u₃C * embedBC V₄ *
      singleQubitLayer u'A u'B u'C =
    embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
      embedBC (kron2 (u_pB * u₁B) 1 * V₂ * kron2 u₂B u₂C) *
      embedAC (kron2 u₂A 1 * V₃ * kron2 u₃A u₃C * kron2 u'A 1) *
      embedBC (kron2 u₃B 1 * V₄ * kron2 u'B u'C) := by
  rw [show
        singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u₃A u₃B u₃C * embedBC V₄ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u₃A u₃B u₃C) *
          embedBC V₄ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [sandwich_AC_BC_AC_to_4embed V₁ V₂ V₃
        u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C]
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedBC (kron2 (u_pB * u₁B) 1 * V₂ * kron2 u₂B u₂C) *
          embedAC (kron2 u₂A 1 * V₃ * kron2 u₃A u₃C) *
          embedBC (kron2 u₃B 1) *
          embedBC V₄ *
          singleQubitLayer u'A u'B u'C =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedBC (kron2 (u_pB * u₁B) 1 * V₂ * kron2 u₂B u₂C) *
          embedAC (kron2 u₂A 1 * V₃ * kron2 u₃A u₃C) *
          (embedBC (kron2 u₃B 1) * embedBC V₄) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedBC_mul]
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedBC (kron2 (u_pB * u₁B) 1 * V₂ * kron2 u₂B u₂C) *
          embedAC (kron2 u₂A 1 * V₃ * kron2 u₃A u₃C) *
          embedBC (kron2 u₃B 1 * V₄) *
          singleQubitLayer u'A u'B u'C =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedBC (kron2 (u_pB * u₁B) 1 * V₂ * kron2 u₂B u₂C) *
          embedAC (kron2 u₂A 1 * V₃ * kron2 u₃A u₃C) *
          (embedBC (kron2 u₃B 1 * V₄) *
            singleQubitLayer u'A u'B u'C) from by noncomm_ring]
  rw [embedBC_mul_singleQubitLayer]
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedBC (kron2 (u_pB * u₁B) 1 * V₂ * kron2 u₂B u₂C) *
          embedAC (kron2 u₂A 1 * V₃ * kron2 u₃A u₃C) *
          (embedBC (kron2 u₃B 1 * V₄ * kron2 u'B u'C) *
            singleQubitLayer u'A I₂ I₂) =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedBC (kron2 (u_pB * u₁B) 1 * V₂ * kron2 u₂B u₂C) *
          embedAC (kron2 u₂A 1 * V₃ * kron2 u₃A u₃C) *
          singleQubitLayer u'A I₂ I₂ *
          embedBC (kron2 u₃B 1 * V₄ * kron2 u'B u'C) from by
        rw [embedBC_comm_singleQubitLayer_A]; noncomm_ring]
  rw [show
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedBC (kron2 (u_pB * u₁B) 1 * V₂ * kron2 u₂B u₂C) *
          embedAC (kron2 u₂A 1 * V₃ * kron2 u₃A u₃C) *
          singleQubitLayer u'A I₂ I₂ *
          embedBC (kron2 u₃B 1 * V₄ * kron2 u'B u'C) =
        embedAC (kron2 u_pA u_pC * V₁ * kron2 u₁A u₁C) *
          embedBC (kron2 (u_pB * u₁B) 1 * V₂ * kron2 u₂B u₂C) *
          (embedAC (kron2 u₂A 1 * V₃ * kron2 u₃A u₃C) *
            singleQubitLayer u'A I₂ I₂) *
          embedBC (kron2 u₃B 1 * V₄ * kron2 u'B u'C) from by noncomm_ring]
  rw [embedAC_mul_singleQubitLayer]
  rw [show singleQubitLayer I₂ I₂ I₂ = (1 : Mat8) from singleQubitLayer_one]
  show _ = _
  simp only [I₂]
  noncomm_ring

private lemma sandwich_AC_AC_AC_to_AC
    (V₁ V₂ V₃ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA ((u_pB * u₁B) * u₂B) u_pC *
      embedAC (V₁ * (kron2 u₁A u₁C * V₂) * (kron2 u₂A u₂C * V₃)) *
      singleQubitLayer u'A u'B u'C := by
  rw [show singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
            singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
            singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
            singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA u_pB u_pC *
          (embedAC V₁ * singleQubitLayer u₁A u₁B u₁C * embedAC V₂) *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAC_merge]
  rw [show singleQubitLayer u_pA u_pB u_pC *
            (singleQubitLayer I₂ u₁B I₂ *
              embedAC (V₁ * (kron2 u₁A u₁C * V₂))) *
            singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
            singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC *
           singleQubitLayer I₂ u₁B I₂) *
          (embedAC (V₁ * (kron2 u₁A u₁C * V₂)) *
            singleQubitLayer u₂A u₂B u₂C * embedAC V₃) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul]
  rw [embedAC_merge]
  rw [show singleQubitLayer (u_pA * I₂) (u_pB * u₁B) (u_pC * I₂) *
            (singleQubitLayer I₂ u₂B I₂ *
              embedAC (V₁ * (kron2 u₁A u₁C * V₂) * (kron2 u₂A u₂C * V₃))) *
            singleQubitLayer u'A u'B u'C =
        (singleQubitLayer (u_pA * I₂) (u_pB * u₁B) (u_pC * I₂) *
           singleQubitLayer I₂ u₂B I₂) *
          embedAC (V₁ * (kron2 u₁A u₁C * V₂) * (kron2 u₂A u₂C * V₃)) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul]
  simp [I₂]

/-- 4-AC triple-merge sandwich: 4 consecutive AC gates with 5 SQLs collapse
    to a single embedAC sandwich. Proved iter 583 via sandwich_AC_AC_AC_to_AC
    + embedAC_merge composition. -/
private lemma sandwich_AC_AC_AC_AC_to_AC
    (V₁ V₂ V₃ V₄ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
      singleQubitLayer u₃A u₃B u₃C * embedAC V₄ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA (((u_pB * u₁B) * u₂B) * u₃B) u_pC *
      embedAC (V₁ * (kron2 u₁A u₁C * V₂) * (kron2 u₂A u₂C * V₃) *
        (kron2 u₃A u₃C * V₄)) *
      singleQubitLayer u'A u'B u'C := by
  -- Step 1: Re-bracket so first 7 factors form a 3-AC chain.
  rw [show
        singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u₃A u₃B u₃C * embedAC V₄ *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
          singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
          singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
          singleQubitLayer u₃A u₃B u₃C) *
          embedAC V₄ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [sandwich_AC_AC_AC_to_AC V₁ V₂ V₃
        u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C]
  -- Step 2: Apply embedAC_merge to combine the resulting embedAC with V₄.
  rw [show
        singleQubitLayer u_pA ((u_pB * u₁B) * u₂B) u_pC *
          embedAC (V₁ * (kron2 u₁A u₁C * V₂) * (kron2 u₂A u₂C * V₃)) *
          singleQubitLayer u₃A u₃B u₃C *
          embedAC V₄ *
          singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA ((u_pB * u₁B) * u₂B) u_pC *
          (embedAC (V₁ * (kron2 u₁A u₁C * V₂) * (kron2 u₂A u₂C * V₃)) *
            singleQubitLayer u₃A u₃B u₃C *
            embedAC V₄) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAC_merge (V₁ * (kron2 u₁A u₁C * V₂) * (kron2 u₂A u₂C * V₃)) V₄
        u₃A u₃B u₃C]
  -- Step 3: Combine the two SQLs at the front.
  rw [show
        singleQubitLayer u_pA ((u_pB * u₁B) * u₂B) u_pC *
          (singleQubitLayer I₂ u₃B I₂ *
            embedAC ((V₁ * (kron2 u₁A u₁C * V₂) * (kron2 u₂A u₂C * V₃)) *
              (kron2 u₃A u₃C * V₄))) *
          singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA ((u_pB * u₁B) * u₂B) u_pC *
          singleQubitLayer I₂ u₃B I₂) *
          embedAC ((V₁ * (kron2 u₁A u₁C * V₂) * (kron2 u₂A u₂C * V₃)) *
            (kron2 u₃A u₃C * V₄)) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul u_pA ((u_pB * u₁B) * u₂B) u_pC I₂ u₃B I₂]
  -- Final: simplify u_pA*I → u_pA, u_pC*I → u_pC.
  show _ = _
  simp only [I₂, mul_one]

/-! ## Outer-pair adjacent-merge sandwich identities

For a 7-factor 3-real-gate chain where the OUTER two embeds are same-XY
(V₂ and V₃, both XY=Y), this collapses to a 5-factor 2-real-gate chain
with the original V₁ untouched and V₂, V₃ merged via `embedY_merge`.

The helper is parameterized over `M₁ : Mat8` (typically `embedX V₁` in
the caller, but the helper is generic — V₁'s position is innermost). -/

private lemma outer_AB_pair_merge_sandwich
    (M₁ : Mat8) (V₂ V₃ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * M₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA u_pB u_pC * M₁ *
      singleQubitLayer u₁A u₁B (u₁C * u₂C) *
      embedAB (V₂ * (kron2 u₂A u₂B * V₃)) *
      singleQubitLayer u'A u'B u'C := by
  rw [show singleQubitLayer u_pA u_pB u_pC * M₁ *
            singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
            singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
            singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA u_pB u_pC * M₁ *
          singleQubitLayer u₁A u₁B u₁C *
          (embedAB V₂ * singleQubitLayer u₂A u₂B u₂C * embedAB V₃) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAB_merge]
  rw [show singleQubitLayer u_pA u_pB u_pC * M₁ *
            singleQubitLayer u₁A u₁B u₁C *
            (singleQubitLayer I₂ I₂ u₂C *
              embedAB (V₂ * (kron2 u₂A u₂B * V₃))) *
            singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA u_pB u_pC * M₁ *
          (singleQubitLayer u₁A u₁B u₁C * singleQubitLayer I₂ I₂ u₂C) *
          embedAB (V₂ * (kron2 u₂A u₂B * V₃)) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul]
  simp [I₂]

private lemma outer_BC_pair_merge_sandwich
    (M₁ : Mat8) (V₂ V₃ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * M₁ *
      singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA u_pB u_pC * M₁ *
      singleQubitLayer (u₁A * u₂A) u₁B u₁C *
      embedBC (V₂ * (kron2 u₂B u₂C * V₃)) *
      singleQubitLayer u'A u'B u'C := by
  rw [show singleQubitLayer u_pA u_pB u_pC * M₁ *
            singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
            singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
            singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA u_pB u_pC * M₁ *
          singleQubitLayer u₁A u₁B u₁C *
          (embedBC V₂ * singleQubitLayer u₂A u₂B u₂C * embedBC V₃) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedBC_merge]
  rw [show singleQubitLayer u_pA u_pB u_pC * M₁ *
            singleQubitLayer u₁A u₁B u₁C *
            (singleQubitLayer u₂A I₂ I₂ *
              embedBC (V₂ * (kron2 u₂B u₂C * V₃))) *
            singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA u_pB u_pC * M₁ *
          (singleQubitLayer u₁A u₁B u₁C * singleQubitLayer u₂A I₂ I₂) *
          embedBC (V₂ * (kron2 u₂B u₂C * V₃)) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul]
  simp [I₂]

/-! ### Inner-pair-merge sandwich identities

For a 7-factor 3-real-gate chain where the INNER two embeds are same-XY
(V₁ and V₂, both XY=Y), this collapses to a 5-factor 2-real-gate chain
with V₁, V₂ merged via `embedY_merge` and V₃ untouched. Parameterized
over `M₃ : Mat8` (typically `embedX V₃` in the caller). -/

private lemma inner_AB_pair_merge_sandwich
    (V₁ V₂ : Mat4) (M₃ : Mat8)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
      singleQubitLayer u₂A u₂B u₂C * M₃ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA u_pB (u_pC * u₁C) *
      embedAB (V₁ * (kron2 u₁A u₁B * V₂)) *
      singleQubitLayer u₂A u₂B u₂C * M₃ *
      singleQubitLayer u'A u'B u'C := by
  rw [show singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
            singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
            singleQubitLayer u₂A u₂B u₂C * M₃ *
            singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA u_pB u_pC *
          (embedAB V₁ * singleQubitLayer u₁A u₁B u₁C * embedAB V₂) *
          singleQubitLayer u₂A u₂B u₂C * M₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAB_merge]
  rw [show singleQubitLayer u_pA u_pB u_pC *
            (singleQubitLayer I₂ I₂ u₁C *
              embedAB (V₁ * (kron2 u₁A u₁B * V₂))) *
            singleQubitLayer u₂A u₂B u₂C * M₃ *
            singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC *
           singleQubitLayer I₂ I₂ u₁C) *
          embedAB (V₁ * (kron2 u₁A u₁B * V₂)) *
          singleQubitLayer u₂A u₂B u₂C * M₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul]
  simp [I₂]

private lemma inner_BC_pair_merge_sandwich
    (V₁ V₂ : Mat4) (M₃ : Mat8)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
      singleQubitLayer u₂A u₂B u₂C * M₃ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer (u_pA * u₁A) u_pB u_pC *
      embedBC (V₁ * (kron2 u₁B u₁C * V₂)) *
      singleQubitLayer u₂A u₂B u₂C * M₃ *
      singleQubitLayer u'A u'B u'C := by
  rw [show singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
            singleQubitLayer u₁A u₁B u₁C * embedBC V₂ *
            singleQubitLayer u₂A u₂B u₂C * M₃ *
            singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA u_pB u_pC *
          (embedBC V₁ * singleQubitLayer u₁A u₁B u₁C * embedBC V₂) *
          singleQubitLayer u₂A u₂B u₂C * M₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedBC_merge]
  rw [show singleQubitLayer u_pA u_pB u_pC *
            (singleQubitLayer u₁A I₂ I₂ *
              embedBC (V₁ * (kron2 u₁B u₁C * V₂))) *
            singleQubitLayer u₂A u₂B u₂C * M₃ *
            singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC *
           singleQubitLayer u₁A I₂ I₂) *
          embedBC (V₁ * (kron2 u₁B u₁C * V₂)) *
          singleQubitLayer u₂A u₂B u₂C * M₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul]
  simp [I₂]

private lemma inner_AC_pair_merge_sandwich
    (V₁ V₂ : Mat4) (M₃ : Mat8)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
      singleQubitLayer u₂A u₂B u₂C * M₃ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA (u_pB * u₁B) u_pC *
      embedAC (V₁ * (kron2 u₁A u₁C * V₂)) *
      singleQubitLayer u₂A u₂B u₂C * M₃ *
      singleQubitLayer u'A u'B u'C := by
  rw [show singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
            singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
            singleQubitLayer u₂A u₂B u₂C * M₃ *
            singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA u_pB u_pC *
          (embedAC V₁ * singleQubitLayer u₁A u₁B u₁C * embedAC V₂) *
          singleQubitLayer u₂A u₂B u₂C * M₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAC_merge]
  rw [show singleQubitLayer u_pA u_pB u_pC *
            (singleQubitLayer I₂ u₁B I₂ *
              embedAC (V₁ * (kron2 u₁A u₁C * V₂))) *
            singleQubitLayer u₂A u₂B u₂C * M₃ *
            singleQubitLayer u'A u'B u'C =
        (singleQubitLayer u_pA u_pB u_pC *
           singleQubitLayer I₂ u₁B I₂) *
          embedAC (V₁ * (kron2 u₁A u₁C * V₂)) *
          singleQubitLayer u₂A u₂B u₂C * M₃ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul]
  simp [I₂]

private lemma outer_AC_pair_merge_sandwich
    (M₁ : Mat8) (V₂ V₃ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * M₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA u_pB u_pC * M₁ *
      singleQubitLayer u₁A (u₁B * u₂B) u₁C *
      embedAC (V₂ * (kron2 u₂A u₂C * V₃)) *
      singleQubitLayer u'A u'B u'C := by
  rw [show singleQubitLayer u_pA u_pB u_pC * M₁ *
            singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
            singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
            singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA u_pB u_pC * M₁ *
          singleQubitLayer u₁A u₁B u₁C *
          (embedAC V₂ * singleQubitLayer u₂A u₂B u₂C * embedAC V₃) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAC_merge]
  rw [show singleQubitLayer u_pA u_pB u_pC * M₁ *
            singleQubitLayer u₁A u₁B u₁C *
            (singleQubitLayer I₂ u₂B I₂ *
              embedAC (V₂ * (kron2 u₂A u₂C * V₃))) *
            singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA u_pB u_pC * M₁ *
          (singleQubitLayer u₁A u₁B u₁C * singleQubitLayer I₂ u₂B I₂) *
          embedAC (V₂ * (kron2 u₂A u₂C * V₃)) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul]
  simp [I₂]

/-! ### 4-gate adjacent-pair merges (iter 1040)

For a 9-factor 4-real-gate chain in which two ADJACENT gates share the same
XY type, the pair merges via `embedXY_merge` and the residual product layer
is absorbed into the neighbouring SQL, leaving an 7-factor 3-real-gate chain
handled by the existing 3-gate sandwiches. Two position classes occur in
`unitaryUnrestrictedCircuit_4_canonical_direct`: the pair at slots (2,3) and
the pair at slots (3,4). The non-merging gates stay abstract as `Mat8`, so
each lemma serves every leaf with that (position, type). -/

private lemma merge23_AB (M₁ M₄ : Mat8) (V₂ V₃ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * M₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
      singleQubitLayer u₃A u₃B u₃C * M₄ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA u_pB u_pC * M₁ *
      singleQubitLayer u₁A u₁B (u₁C * u₂C) *
      embedAB (V₂ * (kron2 u₂A u₂B * V₃)) *
      singleQubitLayer u₃A u₃B u₃C * M₄ *
      singleQubitLayer u'A u'B u'C := by
  rw [show singleQubitLayer u_pA u_pB u_pC * M₁ *
            singleQubitLayer u₁A u₁B u₁C * embedAB V₂ *
            singleQubitLayer u₂A u₂B u₂C * embedAB V₃ *
            singleQubitLayer u₃A u₃B u₃C * M₄ *
            singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA u_pB u_pC * M₁ *
          singleQubitLayer u₁A u₁B u₁C *
          (embedAB V₂ * singleQubitLayer u₂A u₂B u₂C * embedAB V₃) *
          singleQubitLayer u₃A u₃B u₃C * M₄ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAB_merge]
  rw [show singleQubitLayer u_pA u_pB u_pC * M₁ *
            singleQubitLayer u₁A u₁B u₁C *
            (singleQubitLayer I₂ I₂ u₂C * embedAB (V₂ * (kron2 u₂A u₂B * V₃))) *
            singleQubitLayer u₃A u₃B u₃C * M₄ *
            singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA u_pB u_pC * M₁ *
          (singleQubitLayer u₁A u₁B u₁C * singleQubitLayer I₂ I₂ u₂C) *
          embedAB (V₂ * (kron2 u₂A u₂B * V₃)) *
          singleQubitLayer u₃A u₃B u₃C * M₄ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul]
  simp [I₂]

private lemma merge23_AC (M₁ M₄ : Mat8) (V₂ V₃ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * M₁ *
      singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
      singleQubitLayer u₃A u₃B u₃C * M₄ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA u_pB u_pC * M₁ *
      singleQubitLayer u₁A (u₁B * u₂B) u₁C *
      embedAC (V₂ * (kron2 u₂A u₂C * V₃)) *
      singleQubitLayer u₃A u₃B u₃C * M₄ *
      singleQubitLayer u'A u'B u'C := by
  rw [show singleQubitLayer u_pA u_pB u_pC * M₁ *
            singleQubitLayer u₁A u₁B u₁C * embedAC V₂ *
            singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
            singleQubitLayer u₃A u₃B u₃C * M₄ *
            singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA u_pB u_pC * M₁ *
          singleQubitLayer u₁A u₁B u₁C *
          (embedAC V₂ * singleQubitLayer u₂A u₂B u₂C * embedAC V₃) *
          singleQubitLayer u₃A u₃B u₃C * M₄ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAC_merge]
  rw [show singleQubitLayer u_pA u_pB u_pC * M₁ *
            singleQubitLayer u₁A u₁B u₁C *
            (singleQubitLayer I₂ u₂B I₂ * embedAC (V₂ * (kron2 u₂A u₂C * V₃))) *
            singleQubitLayer u₃A u₃B u₃C * M₄ *
            singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA u_pB u_pC * M₁ *
          (singleQubitLayer u₁A u₁B u₁C * singleQubitLayer I₂ u₂B I₂) *
          embedAC (V₂ * (kron2 u₂A u₂C * V₃)) *
          singleQubitLayer u₃A u₃B u₃C * M₄ *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul]
  simp [I₂]

private lemma merge34_BC (M₁ M₂ : Mat8) (V₃ V₄ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * M₁ *
      singleQubitLayer u₁A u₁B u₁C * M₂ *
      singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
      singleQubitLayer u₃A u₃B u₃C * embedBC V₄ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA u_pB u_pC * M₁ *
      singleQubitLayer u₁A u₁B u₁C * M₂ *
      singleQubitLayer (u₂A * u₃A) u₂B u₂C *
      embedBC (V₃ * (kron2 u₃B u₃C * V₄)) *
      singleQubitLayer u'A u'B u'C := by
  rw [show singleQubitLayer u_pA u_pB u_pC * M₁ *
            singleQubitLayer u₁A u₁B u₁C * M₂ *
            singleQubitLayer u₂A u₂B u₂C * embedBC V₃ *
            singleQubitLayer u₃A u₃B u₃C * embedBC V₄ *
            singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA u_pB u_pC * M₁ *
          singleQubitLayer u₁A u₁B u₁C * M₂ *
          singleQubitLayer u₂A u₂B u₂C *
          (embedBC V₃ * singleQubitLayer u₃A u₃B u₃C * embedBC V₄) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedBC_merge]
  rw [show singleQubitLayer u_pA u_pB u_pC * M₁ *
            singleQubitLayer u₁A u₁B u₁C * M₂ *
            singleQubitLayer u₂A u₂B u₂C *
            (singleQubitLayer u₃A I₂ I₂ * embedBC (V₃ * (kron2 u₃B u₃C * V₄))) *
            singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA u_pB u_pC * M₁ *
          singleQubitLayer u₁A u₁B u₁C * M₂ *
          (singleQubitLayer u₂A u₂B u₂C * singleQubitLayer u₃A I₂ I₂) *
          embedBC (V₃ * (kron2 u₃B u₃C * V₄)) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul]
  simp [I₂]

private lemma merge34_AC (M₁ M₂ : Mat8) (V₃ V₄ : Mat4)
    (u_pA u_pB u_pC u₁A u₁B u₁C u₂A u₂B u₂C u₃A u₃B u₃C u'A u'B u'C : Mat2) :
    singleQubitLayer u_pA u_pB u_pC * M₁ *
      singleQubitLayer u₁A u₁B u₁C * M₂ *
      singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
      singleQubitLayer u₃A u₃B u₃C * embedAC V₄ *
      singleQubitLayer u'A u'B u'C =
    singleQubitLayer u_pA u_pB u_pC * M₁ *
      singleQubitLayer u₁A u₁B u₁C * M₂ *
      singleQubitLayer u₂A (u₂B * u₃B) u₂C *
      embedAC (V₃ * (kron2 u₃A u₃C * V₄)) *
      singleQubitLayer u'A u'B u'C := by
  rw [show singleQubitLayer u_pA u_pB u_pC * M₁ *
            singleQubitLayer u₁A u₁B u₁C * M₂ *
            singleQubitLayer u₂A u₂B u₂C * embedAC V₃ *
            singleQubitLayer u₃A u₃B u₃C * embedAC V₄ *
            singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA u_pB u_pC * M₁ *
          singleQubitLayer u₁A u₁B u₁C * M₂ *
          singleQubitLayer u₂A u₂B u₂C *
          (embedAC V₃ * singleQubitLayer u₃A u₃B u₃C * embedAC V₄) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [embedAC_merge]
  rw [show singleQubitLayer u_pA u_pB u_pC * M₁ *
            singleQubitLayer u₁A u₁B u₁C * M₂ *
            singleQubitLayer u₂A u₂B u₂C *
            (singleQubitLayer I₂ u₃B I₂ * embedAC (V₃ * (kron2 u₃A u₃C * V₄))) *
            singleQubitLayer u'A u'B u'C =
        singleQubitLayer u_pA u_pB u_pC * M₁ *
          singleQubitLayer u₁A u₁B u₁C * M₂ *
          (singleQubitLayer u₂A u₂B u₂C * singleQubitLayer I₂ u₃B I₂) *
          embedAC (V₃ * (kron2 u₃A u₃C * V₄)) *
          singleQubitLayer u'A u'B u'C from by noncomm_ring]
  rw [singleQubitLayer_mul]
  simp [I₂]

/-- General V-unitarity recovery (iter 701): if `Pre · embedAB V · Post` is
    unitary and Pre, Post are unitary 8x8 matrices, then V is unitary.
    Generalizes `isUnitary4_V_from_chain_AB` from SQL pre/post to arbitrary
    unitary 8x8 pre/post. Building block for closing dispatcher sorries
    in `unrestrictedCircuit_4_canonical` where "rest" of chain is non-SQL. -/
private lemma isUnitary4_V_from_unitary_sandwich_AB
    {V : Mat4} {Pre Post : Mat8}
    (hPre : Pre.conjTranspose * Pre = (1 : Mat8))
    (hPost : Post.conjTranspose * Post = (1 : Mat8))
    (hM : (Pre * embedAB V * Post).conjTranspose *
          (Pre * embedAB V * Post) = (1 : Mat8)) :
    IsUnitary4 V := by
  have hPost_right : Post * Post.conjTranspose = (1 : Mat8) :=
    mul_eq_one_comm.mp hPost
  have hInner : Post.conjTranspose *
                ((embedAB V).conjTranspose * embedAB V) *
                Post = (1 : Mat8) := by
    have h := hM
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul] at h
    have h_reassoc :
      Post.conjTranspose *
        ((embedAB V).conjTranspose * Pre.conjTranspose) *
        (Pre * embedAB V * Post) =
      Post.conjTranspose *
        ((embedAB V).conjTranspose * embedAB V) *
        Post +
      Post.conjTranspose * (embedAB V).conjTranspose *
        (Pre.conjTranspose * Pre - 1) *
        embedAB V * Post := by
      noncomm_ring
    rw [h_reassoc, hPre, sub_self] at h
    simp at h
    exact h
  have hEmbed : (embedAB V).conjTranspose * embedAB V = (1 : Mat8) := by
    have h := congrArg (fun X => Post * X * Post.conjTranspose) hInner
    simp only at h
    rw [show
      Post * (Post.conjTranspose *
        ((embedAB V).conjTranspose * embedAB V) *
        Post) * Post.conjTranspose =
      (Post * Post.conjTranspose) *
        ((embedAB V).conjTranspose * embedAB V) *
        (Post * Post.conjTranspose)
      from by noncomm_ring] at h
    rw [hPost_right, one_mul, mul_one] at h
    rw [show Post * 1 * Post.conjTranspose =
      Post * Post.conjTranspose from by rw [mul_one]] at h
    rw [hPost_right] at h
    exact h
  exact isUnitary4_of_embedAB V hEmbed

/-- AC variant of `isUnitary4_V_from_unitary_sandwich_AB` (iter 704). -/
private lemma isUnitary4_V_from_unitary_sandwich_AC
    {V : Mat4} {Pre Post : Mat8}
    (hPre : Pre.conjTranspose * Pre = (1 : Mat8))
    (hPost : Post.conjTranspose * Post = (1 : Mat8))
    (hM : (Pre * embedAC V * Post).conjTranspose *
          (Pre * embedAC V * Post) = (1 : Mat8)) :
    IsUnitary4 V := by
  have hPost_right : Post * Post.conjTranspose = (1 : Mat8) :=
    mul_eq_one_comm.mp hPost
  have hInner : Post.conjTranspose *
                ((embedAC V).conjTranspose * embedAC V) *
                Post = (1 : Mat8) := by
    have h := hM
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul] at h
    have h_reassoc :
      Post.conjTranspose *
        ((embedAC V).conjTranspose * Pre.conjTranspose) *
        (Pre * embedAC V * Post) =
      Post.conjTranspose *
        ((embedAC V).conjTranspose * embedAC V) *
        Post +
      Post.conjTranspose * (embedAC V).conjTranspose *
        (Pre.conjTranspose * Pre - 1) *
        embedAC V * Post := by
      noncomm_ring
    rw [h_reassoc, hPre, sub_self] at h
    simp at h
    exact h
  have hEmbed : (embedAC V).conjTranspose * embedAC V = (1 : Mat8) := by
    have h := congrArg (fun X => Post * X * Post.conjTranspose) hInner
    simp only at h
    rw [show
      Post * (Post.conjTranspose *
        ((embedAC V).conjTranspose * embedAC V) *
        Post) * Post.conjTranspose =
      (Post * Post.conjTranspose) *
        ((embedAC V).conjTranspose * embedAC V) *
        (Post * Post.conjTranspose)
      from by noncomm_ring] at h
    rw [hPost_right, one_mul, mul_one] at h
    rw [show Post * 1 * Post.conjTranspose =
      Post * Post.conjTranspose from by rw [mul_one]] at h
    rw [hPost_right] at h
    exact h
  exact isUnitary4_of_embedAC V hEmbed

/-- BC variant of `isUnitary4_V_from_unitary_sandwich_AB` (iter 703). -/
private lemma isUnitary4_V_from_unitary_sandwich_BC
    {V : Mat4} {Pre Post : Mat8}
    (hPre : Pre.conjTranspose * Pre = (1 : Mat8))
    (hPost : Post.conjTranspose * Post = (1 : Mat8))
    (hM : (Pre * embedBC V * Post).conjTranspose *
          (Pre * embedBC V * Post) = (1 : Mat8)) :
    IsUnitary4 V := by
  have hPost_right : Post * Post.conjTranspose = (1 : Mat8) :=
    mul_eq_one_comm.mp hPost
  have hInner : Post.conjTranspose *
                ((embedBC V).conjTranspose * embedBC V) *
                Post = (1 : Mat8) := by
    have h := hM
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul] at h
    have h_reassoc :
      Post.conjTranspose *
        ((embedBC V).conjTranspose * Pre.conjTranspose) *
        (Pre * embedBC V * Post) =
      Post.conjTranspose *
        ((embedBC V).conjTranspose * embedBC V) *
        Post +
      Post.conjTranspose * (embedBC V).conjTranspose *
        (Pre.conjTranspose * Pre - 1) *
        embedBC V * Post := by
      noncomm_ring
    rw [h_reassoc, hPre, sub_self] at h
    simp at h
    exact h
  have hEmbed : (embedBC V).conjTranspose * embedBC V = (1 : Mat8) := by
    have h := congrArg (fun X => Post * X * Post.conjTranspose) hInner
    simp only at h
    rw [show
      Post * (Post.conjTranspose *
        ((embedBC V).conjTranspose * embedBC V) *
        Post) * Post.conjTranspose =
      (Post * Post.conjTranspose) *
        ((embedBC V).conjTranspose * embedBC V) *
        (Post * Post.conjTranspose)
      from by noncomm_ring] at h
    rw [hPost_right, one_mul, mul_one] at h
    rw [show Post * 1 * Post.conjTranspose =
      Post * Post.conjTranspose from by rw [mul_one]] at h
    rw [hPost_right] at h
    exact h
  exact isUnitary4_of_embedBC V hEmbed

/-- Iter 721: AC-BC analog. Given chain `SQL · embedAC V₁ · SQL · embedBC V₂
    · SQL` unitary AND V₁ unitary, derive V₂ unitary. Final 2-V helper
    (6/6) — all chain orderings between distinct embeds covered. -/
private lemma isUnitary4_V₂_from_chain_AC_BC_known_V₁
    {V₁ V₂ : Mat4} (hV₁ : IsUnitary4 V₁)
    {u_pA u_pB u_pC u_mA u_mB u_mC u_qA u_qB u_qC : Mat2}
    (h_pA : IsUnitary2 u_pA) (h_pB : IsUnitary2 u_pB) (h_pC : IsUnitary2 u_pC)
    (h_mA : IsUnitary2 u_mA) (h_mB : IsUnitary2 u_mB) (h_mC : IsUnitary2 u_mC)
    (h_qA : IsUnitary2 u_qA) (h_qB : IsUnitary2 u_qB) (h_qC : IsUnitary2 u_qC)
    (hM : (singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
           singleQubitLayer u_mA u_mB u_mC * embedBC V₂ *
           singleQubitLayer u_qA u_qB u_qC).conjTranspose *
          (singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
           singleQubitLayer u_mA u_mB u_mC * embedBC V₂ *
           singleQubitLayer u_qA u_qB u_qC) = (1 : Mat8)) :
    IsUnitary4 V₂ := by
  set Pre := singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
              singleQubitLayer u_mA u_mB u_mC with hPre_def
  set Post := singleQubitLayer u_qA u_qB u_qC with hPost_def
  have hPre_unit : Pre.conjTranspose * Pre = (1 : Mat8) := by
    rw [hPre_def]
    have h1 : (singleQubitLayer u_pA u_pB u_pC).conjTranspose *
              singleQubitLayer u_pA u_pB u_pC = (1 : Mat8) :=
      singleQubitLayer_unitary u_pA u_pB u_pC h_pA h_pB h_pC
    have h2 : (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
              singleQubitLayer u_mA u_mB u_mC = (1 : Mat8) :=
      singleQubitLayer_unitary u_mA u_mB u_mC h_mA h_mB h_mC
    have hAC : (embedAC V₁).conjTranspose * embedAC V₁ = (1 : Mat8) :=
      embedAC_unitary V₁ hV₁
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    have h_reassoc :
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        ((embedAC V₁).conjTranspose * (singleQubitLayer u_pA u_pB u_pC).conjTranspose) *
        (singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
          singleQubitLayer u_mA u_mB u_mC) =
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        ((embedAC V₁).conjTranspose *
          ((singleQubitLayer u_pA u_pB u_pC).conjTranspose *
            singleQubitLayer u_pA u_pB u_pC) *
          embedAC V₁) *
        singleQubitLayer u_mA u_mB u_mC := by noncomm_ring
    rw [h_reassoc, h1, mul_one]
    rw [show
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        ((embedAC V₁).conjTranspose * embedAC V₁) *
        singleQubitLayer u_mA u_mB u_mC =
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        ((embedAC V₁).conjTranspose * embedAC V₁ - 1) *
        singleQubitLayer u_mA u_mB u_mC +
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        singleQubitLayer u_mA u_mB u_mC from by noncomm_ring]
    rw [hAC, sub_self]
    simp [h2]
  have hPost_unit : Post.conjTranspose * Post = (1 : Mat8) := by
    rw [hPost_def]
    exact singleQubitLayer_unitary u_qA u_qB u_qC h_qA h_qB h_qC
  have hM_reformulated :
      (Pre * embedBC V₂ * Post).conjTranspose *
      (Pre * embedBC V₂ * Post) = (1 : Mat8) := by
    rw [hPre_def, hPost_def]
    convert hM using 2 <;> noncomm_ring
  exact isUnitary4_V_from_unitary_sandwich_BC hPre_unit hPost_unit
    hM_reformulated

/-- Iter 719: BC-AC analog. Given chain `SQL · embedBC V₁ · SQL · embedAC V₂
    · SQL` unitary AND V₁ unitary, derive V₂ unitary. -/
private lemma isUnitary4_V₂_from_chain_BC_AC_known_V₁
    {V₁ V₂ : Mat4} (hV₁ : IsUnitary4 V₁)
    {u_pA u_pB u_pC u_mA u_mB u_mC u_qA u_qB u_qC : Mat2}
    (h_pA : IsUnitary2 u_pA) (h_pB : IsUnitary2 u_pB) (h_pC : IsUnitary2 u_pC)
    (h_mA : IsUnitary2 u_mA) (h_mB : IsUnitary2 u_mB) (h_mC : IsUnitary2 u_mC)
    (h_qA : IsUnitary2 u_qA) (h_qB : IsUnitary2 u_qB) (h_qC : IsUnitary2 u_qC)
    (hM : (singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
           singleQubitLayer u_mA u_mB u_mC * embedAC V₂ *
           singleQubitLayer u_qA u_qB u_qC).conjTranspose *
          (singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
           singleQubitLayer u_mA u_mB u_mC * embedAC V₂ *
           singleQubitLayer u_qA u_qB u_qC) = (1 : Mat8)) :
    IsUnitary4 V₂ := by
  set Pre := singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
              singleQubitLayer u_mA u_mB u_mC with hPre_def
  set Post := singleQubitLayer u_qA u_qB u_qC with hPost_def
  have hPre_unit : Pre.conjTranspose * Pre = (1 : Mat8) := by
    rw [hPre_def]
    have h1 : (singleQubitLayer u_pA u_pB u_pC).conjTranspose *
              singleQubitLayer u_pA u_pB u_pC = (1 : Mat8) :=
      singleQubitLayer_unitary u_pA u_pB u_pC h_pA h_pB h_pC
    have h2 : (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
              singleQubitLayer u_mA u_mB u_mC = (1 : Mat8) :=
      singleQubitLayer_unitary u_mA u_mB u_mC h_mA h_mB h_mC
    have hBC : (embedBC V₁).conjTranspose * embedBC V₁ = (1 : Mat8) :=
      embedBC_unitary V₁ hV₁
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    have h_reassoc :
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        ((embedBC V₁).conjTranspose * (singleQubitLayer u_pA u_pB u_pC).conjTranspose) *
        (singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
          singleQubitLayer u_mA u_mB u_mC) =
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        ((embedBC V₁).conjTranspose *
          ((singleQubitLayer u_pA u_pB u_pC).conjTranspose *
            singleQubitLayer u_pA u_pB u_pC) *
          embedBC V₁) *
        singleQubitLayer u_mA u_mB u_mC := by noncomm_ring
    rw [h_reassoc, h1, mul_one]
    rw [show
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        ((embedBC V₁).conjTranspose * embedBC V₁) *
        singleQubitLayer u_mA u_mB u_mC =
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        ((embedBC V₁).conjTranspose * embedBC V₁ - 1) *
        singleQubitLayer u_mA u_mB u_mC +
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        singleQubitLayer u_mA u_mB u_mC from by noncomm_ring]
    rw [hBC, sub_self]
    simp [h2]
  have hPost_unit : Post.conjTranspose * Post = (1 : Mat8) := by
    rw [hPost_def]
    exact singleQubitLayer_unitary u_qA u_qB u_qC h_qA h_qB h_qC
  have hM_reformulated :
      (Pre * embedAC V₂ * Post).conjTranspose *
      (Pre * embedAC V₂ * Post) = (1 : Mat8) := by
    rw [hPre_def, hPost_def]
    convert hM using 2 <;> noncomm_ring
  exact isUnitary4_V_from_unitary_sandwich_AC hPre_unit hPost_unit
    hM_reformulated

/-- Iter 718: AB-AC analog. Given chain `SQL · embedAB V₁ · SQL · embedAC V₂
    · SQL` unitary AND V₁ unitary, derive V₂ unitary. -/
private lemma isUnitary4_V₂_from_chain_AB_AC_known_V₁
    {V₁ V₂ : Mat4} (hV₁ : IsUnitary4 V₁)
    {u_pA u_pB u_pC u_mA u_mB u_mC u_qA u_qB u_qC : Mat2}
    (h_pA : IsUnitary2 u_pA) (h_pB : IsUnitary2 u_pB) (h_pC : IsUnitary2 u_pC)
    (h_mA : IsUnitary2 u_mA) (h_mB : IsUnitary2 u_mB) (h_mC : IsUnitary2 u_mC)
    (h_qA : IsUnitary2 u_qA) (h_qB : IsUnitary2 u_qB) (h_qC : IsUnitary2 u_qC)
    (hM : (singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
           singleQubitLayer u_mA u_mB u_mC * embedAC V₂ *
           singleQubitLayer u_qA u_qB u_qC).conjTranspose *
          (singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
           singleQubitLayer u_mA u_mB u_mC * embedAC V₂ *
           singleQubitLayer u_qA u_qB u_qC) = (1 : Mat8)) :
    IsUnitary4 V₂ := by
  set Pre := singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
              singleQubitLayer u_mA u_mB u_mC with hPre_def
  set Post := singleQubitLayer u_qA u_qB u_qC with hPost_def
  have hPre_unit : Pre.conjTranspose * Pre = (1 : Mat8) := by
    rw [hPre_def]
    have h1 : (singleQubitLayer u_pA u_pB u_pC).conjTranspose *
              singleQubitLayer u_pA u_pB u_pC = (1 : Mat8) :=
      singleQubitLayer_unitary u_pA u_pB u_pC h_pA h_pB h_pC
    have h2 : (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
              singleQubitLayer u_mA u_mB u_mC = (1 : Mat8) :=
      singleQubitLayer_unitary u_mA u_mB u_mC h_mA h_mB h_mC
    have hAB : (embedAB V₁).conjTranspose * embedAB V₁ = (1 : Mat8) :=
      embedAB_unitary V₁ hV₁
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    have h_reassoc :
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        ((embedAB V₁).conjTranspose * (singleQubitLayer u_pA u_pB u_pC).conjTranspose) *
        (singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
          singleQubitLayer u_mA u_mB u_mC) =
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        ((embedAB V₁).conjTranspose *
          ((singleQubitLayer u_pA u_pB u_pC).conjTranspose *
            singleQubitLayer u_pA u_pB u_pC) *
          embedAB V₁) *
        singleQubitLayer u_mA u_mB u_mC := by noncomm_ring
    rw [h_reassoc, h1, mul_one]
    rw [show
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        ((embedAB V₁).conjTranspose * embedAB V₁) *
        singleQubitLayer u_mA u_mB u_mC =
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        ((embedAB V₁).conjTranspose * embedAB V₁ - 1) *
        singleQubitLayer u_mA u_mB u_mC +
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        singleQubitLayer u_mA u_mB u_mC from by noncomm_ring]
    rw [hAB, sub_self]
    simp [h2]
  have hPost_unit : Post.conjTranspose * Post = (1 : Mat8) := by
    rw [hPost_def]
    exact singleQubitLayer_unitary u_qA u_qB u_qC h_qA h_qB h_qC
  have hM_reformulated :
      (Pre * embedAC V₂ * Post).conjTranspose *
      (Pre * embedAC V₂ * Post) = (1 : Mat8) := by
    rw [hPre_def, hPost_def]
    convert hM using 2 <;> noncomm_ring
  exact isUnitary4_V_from_unitary_sandwich_AC hPre_unit hPost_unit
    hM_reformulated

/-- Iter 717: AC-AB analog. Given chain `SQL · embedAC V₁ · SQL · embedAB V₂
    · SQL` unitary AND V₁ unitary, derive V₂ unitary. -/
private lemma isUnitary4_V₂_from_chain_AC_AB_known_V₁
    {V₁ V₂ : Mat4} (hV₁ : IsUnitary4 V₁)
    {u_pA u_pB u_pC u_mA u_mB u_mC u_qA u_qB u_qC : Mat2}
    (h_pA : IsUnitary2 u_pA) (h_pB : IsUnitary2 u_pB) (h_pC : IsUnitary2 u_pC)
    (h_mA : IsUnitary2 u_mA) (h_mB : IsUnitary2 u_mB) (h_mC : IsUnitary2 u_mC)
    (h_qA : IsUnitary2 u_qA) (h_qB : IsUnitary2 u_qB) (h_qC : IsUnitary2 u_qC)
    (hM : (singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
           singleQubitLayer u_mA u_mB u_mC * embedAB V₂ *
           singleQubitLayer u_qA u_qB u_qC).conjTranspose *
          (singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
           singleQubitLayer u_mA u_mB u_mC * embedAB V₂ *
           singleQubitLayer u_qA u_qB u_qC) = (1 : Mat8)) :
    IsUnitary4 V₂ := by
  set Pre := singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
              singleQubitLayer u_mA u_mB u_mC with hPre_def
  set Post := singleQubitLayer u_qA u_qB u_qC with hPost_def
  have hPre_unit : Pre.conjTranspose * Pre = (1 : Mat8) := by
    rw [hPre_def]
    have h1 : (singleQubitLayer u_pA u_pB u_pC).conjTranspose *
              singleQubitLayer u_pA u_pB u_pC = (1 : Mat8) :=
      singleQubitLayer_unitary u_pA u_pB u_pC h_pA h_pB h_pC
    have h2 : (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
              singleQubitLayer u_mA u_mB u_mC = (1 : Mat8) :=
      singleQubitLayer_unitary u_mA u_mB u_mC h_mA h_mB h_mC
    have hAC : (embedAC V₁).conjTranspose * embedAC V₁ = (1 : Mat8) :=
      embedAC_unitary V₁ hV₁
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    have h_reassoc :
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        ((embedAC V₁).conjTranspose * (singleQubitLayer u_pA u_pB u_pC).conjTranspose) *
        (singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
          singleQubitLayer u_mA u_mB u_mC) =
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        ((embedAC V₁).conjTranspose *
          ((singleQubitLayer u_pA u_pB u_pC).conjTranspose *
            singleQubitLayer u_pA u_pB u_pC) *
          embedAC V₁) *
        singleQubitLayer u_mA u_mB u_mC := by noncomm_ring
    rw [h_reassoc, h1, mul_one]
    rw [show
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        ((embedAC V₁).conjTranspose * embedAC V₁) *
        singleQubitLayer u_mA u_mB u_mC =
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        ((embedAC V₁).conjTranspose * embedAC V₁ - 1) *
        singleQubitLayer u_mA u_mB u_mC +
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        singleQubitLayer u_mA u_mB u_mC from by noncomm_ring]
    rw [hAC, sub_self]
    simp [h2]
  have hPost_unit : Post.conjTranspose * Post = (1 : Mat8) := by
    rw [hPost_def]
    exact singleQubitLayer_unitary u_qA u_qB u_qC h_qA h_qB h_qC
  have hM_reformulated :
      (Pre * embedAB V₂ * Post).conjTranspose *
      (Pre * embedAB V₂ * Post) = (1 : Mat8) := by
    rw [hPre_def, hPost_def]
    convert hM using 2 <;> noncomm_ring
  exact isUnitary4_V_from_unitary_sandwich_AB hPre_unit hPost_unit
    hM_reformulated

/-- Iter 716: BC-AB analog of `isUnitary4_V₂_from_chain_AB_BC_known_V₁`.
    Given chain `SQL · embedBC V₁ · SQL · embedAB V₂ · SQL` unitary AND
    V₁ unitary, derive V₂ unitary. -/
private lemma isUnitary4_V₂_from_chain_BC_AB_known_V₁
    {V₁ V₂ : Mat4} (hV₁ : IsUnitary4 V₁)
    {u_pA u_pB u_pC u_mA u_mB u_mC u_qA u_qB u_qC : Mat2}
    (h_pA : IsUnitary2 u_pA) (h_pB : IsUnitary2 u_pB) (h_pC : IsUnitary2 u_pC)
    (h_mA : IsUnitary2 u_mA) (h_mB : IsUnitary2 u_mB) (h_mC : IsUnitary2 u_mC)
    (h_qA : IsUnitary2 u_qA) (h_qB : IsUnitary2 u_qB) (h_qC : IsUnitary2 u_qC)
    (hM : (singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
           singleQubitLayer u_mA u_mB u_mC * embedAB V₂ *
           singleQubitLayer u_qA u_qB u_qC).conjTranspose *
          (singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
           singleQubitLayer u_mA u_mB u_mC * embedAB V₂ *
           singleQubitLayer u_qA u_qB u_qC) = (1 : Mat8)) :
    IsUnitary4 V₂ := by
  set Pre := singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
              singleQubitLayer u_mA u_mB u_mC with hPre_def
  set Post := singleQubitLayer u_qA u_qB u_qC with hPost_def
  have hPre_unit : Pre.conjTranspose * Pre = (1 : Mat8) := by
    rw [hPre_def]
    have h1 : (singleQubitLayer u_pA u_pB u_pC).conjTranspose *
              singleQubitLayer u_pA u_pB u_pC = (1 : Mat8) :=
      singleQubitLayer_unitary u_pA u_pB u_pC h_pA h_pB h_pC
    have h2 : (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
              singleQubitLayer u_mA u_mB u_mC = (1 : Mat8) :=
      singleQubitLayer_unitary u_mA u_mB u_mC h_mA h_mB h_mC
    have hBC : (embedBC V₁).conjTranspose * embedBC V₁ = (1 : Mat8) :=
      embedBC_unitary V₁ hV₁
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    have h_reassoc :
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        ((embedBC V₁).conjTranspose * (singleQubitLayer u_pA u_pB u_pC).conjTranspose) *
        (singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
          singleQubitLayer u_mA u_mB u_mC) =
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        ((embedBC V₁).conjTranspose *
          ((singleQubitLayer u_pA u_pB u_pC).conjTranspose *
            singleQubitLayer u_pA u_pB u_pC) *
          embedBC V₁) *
        singleQubitLayer u_mA u_mB u_mC := by noncomm_ring
    rw [h_reassoc, h1, mul_one]
    rw [show
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        ((embedBC V₁).conjTranspose * embedBC V₁) *
        singleQubitLayer u_mA u_mB u_mC =
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        ((embedBC V₁).conjTranspose * embedBC V₁ - 1) *
        singleQubitLayer u_mA u_mB u_mC +
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        singleQubitLayer u_mA u_mB u_mC from by noncomm_ring]
    rw [hBC, sub_self]
    simp [h2]
  have hPost_unit : Post.conjTranspose * Post = (1 : Mat8) := by
    rw [hPost_def]
    exact singleQubitLayer_unitary u_qA u_qB u_qC h_qA h_qB h_qC
  have hM_reformulated :
      (Pre * embedAB V₂ * Post).conjTranspose *
      (Pre * embedAB V₂ * Post) = (1 : Mat8) := by
    rw [hPre_def, hPost_def]
    convert hM using 2 <;> noncomm_ring
  exact isUnitary4_V_from_unitary_sandwich_AB hPre_unit hPost_unit
    hM_reformulated

/-- Iter 715: 2-V chain helper. Given chain `SQL_pre · embedAB V₁ · SQL_mid
    · embedBC V₂ · SQL_post` unitary, with V₁ unitary, derive V₂ unitary.
    Uses `isUnitary4_V_from_unitary_sandwich_BC` with Pre := SQL_pre ·
    embedAB V₁ · SQL_mid (unitary since SQLs and V₁ are unitary).
    Building block for "bootstrap+peel" approach to dispatcher closure. -/
private lemma isUnitary4_V₂_from_chain_AB_BC_known_V₁
    {V₁ V₂ : Mat4} (hV₁ : IsUnitary4 V₁)
    {u_pA u_pB u_pC u_mA u_mB u_mC u_qA u_qB u_qC : Mat2}
    (h_pA : IsUnitary2 u_pA) (h_pB : IsUnitary2 u_pB) (h_pC : IsUnitary2 u_pC)
    (h_mA : IsUnitary2 u_mA) (h_mB : IsUnitary2 u_mB) (h_mC : IsUnitary2 u_mC)
    (h_qA : IsUnitary2 u_qA) (h_qB : IsUnitary2 u_qB) (h_qC : IsUnitary2 u_qC)
    (hM : (singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
           singleQubitLayer u_mA u_mB u_mC * embedBC V₂ *
           singleQubitLayer u_qA u_qB u_qC).conjTranspose *
          (singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
           singleQubitLayer u_mA u_mB u_mC * embedBC V₂ *
           singleQubitLayer u_qA u_qB u_qC) = (1 : Mat8)) :
    IsUnitary4 V₂ := by
  set Pre := singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
              singleQubitLayer u_mA u_mB u_mC with hPre_def
  set Post := singleQubitLayer u_qA u_qB u_qC with hPost_def
  have hPre_unit : Pre.conjTranspose * Pre = (1 : Mat8) := by
    rw [hPre_def]
    have h1 : (singleQubitLayer u_pA u_pB u_pC).conjTranspose *
              singleQubitLayer u_pA u_pB u_pC = (1 : Mat8) :=
      singleQubitLayer_unitary u_pA u_pB u_pC h_pA h_pB h_pC
    have h2 : (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
              singleQubitLayer u_mA u_mB u_mC = (1 : Mat8) :=
      singleQubitLayer_unitary u_mA u_mB u_mC h_mA h_mB h_mC
    have hAB : (embedAB V₁).conjTranspose * embedAB V₁ = (1 : Mat8) :=
      embedAB_unitary V₁ hV₁
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    have h_reassoc :
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        ((embedAB V₁).conjTranspose * (singleQubitLayer u_pA u_pB u_pC).conjTranspose) *
        (singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
          singleQubitLayer u_mA u_mB u_mC) =
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        ((embedAB V₁).conjTranspose *
          ((singleQubitLayer u_pA u_pB u_pC).conjTranspose *
            singleQubitLayer u_pA u_pB u_pC) *
          embedAB V₁) *
        singleQubitLayer u_mA u_mB u_mC := by noncomm_ring
    rw [h_reassoc, h1, mul_one]
    rw [show
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        ((embedAB V₁).conjTranspose * embedAB V₁) *
        singleQubitLayer u_mA u_mB u_mC =
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        ((embedAB V₁).conjTranspose * embedAB V₁ - 1) *
        singleQubitLayer u_mA u_mB u_mC +
      (singleQubitLayer u_mA u_mB u_mC).conjTranspose *
        singleQubitLayer u_mA u_mB u_mC from by noncomm_ring]
    rw [hAB, sub_self]
    simp [h2]
  have hPost_unit : Post.conjTranspose * Post = (1 : Mat8) := by
    rw [hPost_def]
    exact singleQubitLayer_unitary u_qA u_qB u_qC h_qA h_qB h_qC
  have hM_reformulated :
      (Pre * embedBC V₂ * Post).conjTranspose *
      (Pre * embedBC V₂ * Post) = (1 : Mat8) := by
    rw [hPre_def, hPost_def]
    convert hM using 2 <;> noncomm_ring
  exact isUnitary4_V_from_unitary_sandwich_BC hPre_unit hPost_unit
    hM_reformulated

/-- V-unitarity from chain unitarity (AB sandwich case). Given that
    `singleQubitLayer u' · embedAB V · singleQubitLayer u` is unitary
    (with all u, u' unitary), V is unitary. Used in
    `unrestrictedCircuit_4_canonical`'s compose_AB outer case. -/
private lemma isUnitary4_V_from_chain_AB
    {V : Mat4} {u'A u'B u'C uA uB uC : Mat2}
    (h'A : IsUnitary2 u'A) (h'B : IsUnitary2 u'B) (h'C : IsUnitary2 u'C)
    (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC)
    (hM : (singleQubitLayer u'A u'B u'C * embedAB V * singleQubitLayer uA uB uC).conjTranspose *
          (singleQubitLayer u'A u'B u'C * embedAB V * singleQubitLayer uA uB uC) = 1) :
    IsUnitary4 V := by
  -- Setup unitarity facts for surrounding singleQubitLayer factors.
  have hSQL_u'_left : (singleQubitLayer u'A u'B u'C).conjTranspose *
                      singleQubitLayer u'A u'B u'C = (1 : Mat8) :=
    singleQubitLayer_unitary u'A u'B u'C h'A h'B h'C
  have hSQL_u_left : (singleQubitLayer uA uB uC).conjTranspose *
                     singleQubitLayer uA uB uC = (1 : Mat8) :=
    singleQubitLayer_unitary uA uB uC hA hB hC
  have hSQL_u_right : singleQubitLayer uA uB uC *
                      (singleQubitLayer uA uB uC).conjTranspose = (1 : Mat8) :=
    mul_eq_one_comm.mp hSQL_u_left
  -- Step 1: from hM, derive SQL_u† · ((embedAB V)† · embedAB V) · SQL_u = 1.
  -- (Conjtranspose distributes; SQL_u' factor cancels via its unitarity.)
  have hInner : (singleQubitLayer uA uB uC).conjTranspose *
                ((embedAB V).conjTranspose * embedAB V) *
                singleQubitLayer uA uB uC = (1 : Mat8) := by
    have h := hM
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul] at h
    -- After conjT distribution, h has form:
    -- SQL_u† · ((embedAB V)† · SQL_u'†) · (SQL_u' · embedAB V · SQL_u) = 1.
    -- Reassociate inside h to bracket SQL_u'† · SQL_u' = 1:
    have h_reassoc :
      (singleQubitLayer uA uB uC).conjTranspose *
        ((embedAB V).conjTranspose * (singleQubitLayer u'A u'B u'C).conjTranspose) *
        (singleQubitLayer u'A u'B u'C * embedAB V * singleQubitLayer uA uB uC) =
      (singleQubitLayer uA uB uC).conjTranspose *
        ((embedAB V).conjTranspose * embedAB V) *
        singleQubitLayer uA uB uC +
      (singleQubitLayer uA uB uC).conjTranspose * (embedAB V).conjTranspose *
        ((singleQubitLayer u'A u'B u'C).conjTranspose *
          singleQubitLayer u'A u'B u'C - 1) *
        embedAB V * singleQubitLayer uA uB uC := by
      noncomm_ring
    rw [h_reassoc, hSQL_u'_left, sub_self] at h
    simp at h
    exact h
  -- Step 2: multiply hInner on left by SQL_u, right by SQL_u†, simplify.
  have hEmbed : (embedAB V).conjTranspose * embedAB V = (1 : Mat8) := by
    have h := congrArg (fun X => singleQubitLayer uA uB uC * X *
                                  (singleQubitLayer uA uB uC).conjTranspose) hInner
    simp only at h
    -- h: SQL_u · (SQL_u† · X · SQL_u) · SQL_u† = SQL_u · 1 · SQL_u†
    --   where X = (embedAB V)† · embedAB V.
    rw [show
      singleQubitLayer uA uB uC *
        ((singleQubitLayer uA uB uC).conjTranspose *
          ((embedAB V).conjTranspose * embedAB V) *
          singleQubitLayer uA uB uC) *
        (singleQubitLayer uA uB uC).conjTranspose =
      (singleQubitLayer uA uB uC * (singleQubitLayer uA uB uC).conjTranspose) *
        ((embedAB V).conjTranspose * embedAB V) *
        (singleQubitLayer uA uB uC * (singleQubitLayer uA uB uC).conjTranspose)
      from by noncomm_ring] at h
    rw [hSQL_u_right, one_mul, mul_one] at h
    rw [show
      singleQubitLayer uA uB uC * 1 * (singleQubitLayer uA uB uC).conjTranspose =
      singleQubitLayer uA uB uC * (singleQubitLayer uA uB uC).conjTranspose
      from by rw [mul_one]] at h
    rw [hSQL_u_right] at h
    exact h
  exact isUnitary4_of_embedAB V hEmbed

/-- V-unitarity from chain unitarity (BC sandwich case). Mirror of
    `isUnitary4_V_from_chain_AB` for embedBC. -/
private lemma isUnitary4_V_from_chain_BC
    {V : Mat4} {u'A u'B u'C uA uB uC : Mat2}
    (h'A : IsUnitary2 u'A) (h'B : IsUnitary2 u'B) (h'C : IsUnitary2 u'C)
    (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC)
    (hM : (singleQubitLayer u'A u'B u'C * embedBC V * singleQubitLayer uA uB uC).conjTranspose *
          (singleQubitLayer u'A u'B u'C * embedBC V * singleQubitLayer uA uB uC) = 1) :
    IsUnitary4 V := by
  have hSQL_u'_left : (singleQubitLayer u'A u'B u'C).conjTranspose *
                      singleQubitLayer u'A u'B u'C = (1 : Mat8) :=
    singleQubitLayer_unitary u'A u'B u'C h'A h'B h'C
  have hSQL_u_left : (singleQubitLayer uA uB uC).conjTranspose *
                     singleQubitLayer uA uB uC = (1 : Mat8) :=
    singleQubitLayer_unitary uA uB uC hA hB hC
  have hSQL_u_right : singleQubitLayer uA uB uC *
                      (singleQubitLayer uA uB uC).conjTranspose = (1 : Mat8) :=
    mul_eq_one_comm.mp hSQL_u_left
  have hInner : (singleQubitLayer uA uB uC).conjTranspose *
                ((embedBC V).conjTranspose * embedBC V) *
                singleQubitLayer uA uB uC = (1 : Mat8) := by
    have h := hM
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul] at h
    have h_reassoc :
      (singleQubitLayer uA uB uC).conjTranspose *
        ((embedBC V).conjTranspose * (singleQubitLayer u'A u'B u'C).conjTranspose) *
        (singleQubitLayer u'A u'B u'C * embedBC V * singleQubitLayer uA uB uC) =
      (singleQubitLayer uA uB uC).conjTranspose *
        ((embedBC V).conjTranspose * embedBC V) *
        singleQubitLayer uA uB uC +
      (singleQubitLayer uA uB uC).conjTranspose * (embedBC V).conjTranspose *
        ((singleQubitLayer u'A u'B u'C).conjTranspose *
          singleQubitLayer u'A u'B u'C - 1) *
        embedBC V * singleQubitLayer uA uB uC := by
      noncomm_ring
    rw [h_reassoc, hSQL_u'_left, sub_self] at h
    simp at h
    exact h
  have hEmbed : (embedBC V).conjTranspose * embedBC V = (1 : Mat8) := by
    have h := congrArg (fun X => singleQubitLayer uA uB uC * X *
                                  (singleQubitLayer uA uB uC).conjTranspose) hInner
    simp only at h
    rw [show
      singleQubitLayer uA uB uC *
        ((singleQubitLayer uA uB uC).conjTranspose *
          ((embedBC V).conjTranspose * embedBC V) *
          singleQubitLayer uA uB uC) *
        (singleQubitLayer uA uB uC).conjTranspose =
      (singleQubitLayer uA uB uC * (singleQubitLayer uA uB uC).conjTranspose) *
        ((embedBC V).conjTranspose * embedBC V) *
        (singleQubitLayer uA uB uC * (singleQubitLayer uA uB uC).conjTranspose)
      from by noncomm_ring] at h
    rw [hSQL_u_right, one_mul, mul_one] at h
    rw [show
      singleQubitLayer uA uB uC * 1 * (singleQubitLayer uA uB uC).conjTranspose =
      singleQubitLayer uA uB uC * (singleQubitLayer uA uB uC).conjTranspose
      from by rw [mul_one]] at h
    rw [hSQL_u_right] at h
    exact h
  exact isUnitary4_of_embedBC V hEmbed

/-- V-unitarity from chain unitarity (AC sandwich case). Mirror of
    `isUnitary4_V_from_chain_AB` for embedAC. -/
private lemma isUnitary4_V_from_chain_AC
    {V : Mat4} {u'A u'B u'C uA uB uC : Mat2}
    (h'A : IsUnitary2 u'A) (h'B : IsUnitary2 u'B) (h'C : IsUnitary2 u'C)
    (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC)
    (hM : (singleQubitLayer u'A u'B u'C * embedAC V * singleQubitLayer uA uB uC).conjTranspose *
          (singleQubitLayer u'A u'B u'C * embedAC V * singleQubitLayer uA uB uC) = 1) :
    IsUnitary4 V := by
  have hSQL_u'_left : (singleQubitLayer u'A u'B u'C).conjTranspose *
                      singleQubitLayer u'A u'B u'C = (1 : Mat8) :=
    singleQubitLayer_unitary u'A u'B u'C h'A h'B h'C
  have hSQL_u_left : (singleQubitLayer uA uB uC).conjTranspose *
                     singleQubitLayer uA uB uC = (1 : Mat8) :=
    singleQubitLayer_unitary uA uB uC hA hB hC
  have hSQL_u_right : singleQubitLayer uA uB uC *
                      (singleQubitLayer uA uB uC).conjTranspose = (1 : Mat8) :=
    mul_eq_one_comm.mp hSQL_u_left
  have hInner : (singleQubitLayer uA uB uC).conjTranspose *
                ((embedAC V).conjTranspose * embedAC V) *
                singleQubitLayer uA uB uC = (1 : Mat8) := by
    have h := hM
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul] at h
    have h_reassoc :
      (singleQubitLayer uA uB uC).conjTranspose *
        ((embedAC V).conjTranspose * (singleQubitLayer u'A u'B u'C).conjTranspose) *
        (singleQubitLayer u'A u'B u'C * embedAC V * singleQubitLayer uA uB uC) =
      (singleQubitLayer uA uB uC).conjTranspose *
        ((embedAC V).conjTranspose * embedAC V) *
        singleQubitLayer uA uB uC +
      (singleQubitLayer uA uB uC).conjTranspose * (embedAC V).conjTranspose *
        ((singleQubitLayer u'A u'B u'C).conjTranspose *
          singleQubitLayer u'A u'B u'C - 1) *
        embedAC V * singleQubitLayer uA uB uC := by
      noncomm_ring
    rw [h_reassoc, hSQL_u'_left, sub_self] at h
    simp at h
    exact h
  have hEmbed : (embedAC V).conjTranspose * embedAC V = (1 : Mat8) := by
    have h := congrArg (fun X => singleQubitLayer uA uB uC * X *
                                  (singleQubitLayer uA uB uC).conjTranspose) hInner
    simp only at h
    rw [show
      singleQubitLayer uA uB uC *
        ((singleQubitLayer uA uB uC).conjTranspose *
          ((embedAC V).conjTranspose * embedAC V) *
          singleQubitLayer uA uB uC) *
        (singleQubitLayer uA uB uC).conjTranspose =
      (singleQubitLayer uA uB uC * (singleQubitLayer uA uB uC).conjTranspose) *
        ((embedAC V).conjTranspose * embedAC V) *
        (singleQubitLayer uA uB uC * (singleQubitLayer uA uB uC).conjTranspose)
      from by noncomm_ring] at h
    rw [hSQL_u_right, one_mul, mul_one] at h
    rw [show
      singleQubitLayer uA uB uC * 1 * (singleQubitLayer uA uB uC).conjTranspose =
      singleQubitLayer uA uB uC * (singleQubitLayer uA uB uC).conjTranspose
      from by rw [mul_one]] at h
    rw [hSQL_u_right] at h
    exact h
  exact isUnitary4_of_embedAC V hEmbed

/-! Retired iter 1043: `unrestrictedCircuit_4_canonical` (16 dispatcher
sorries) and `four_unrestricted_implies_S4_or_S5`. Both were stated over the
non-unitary `UnrestrictedCircuit`, whose `compose_*` carries no
`IsUnitary4 V`; the paper Lemma C.1 argument needs it, and the forgetful lift
from `UnitaryUnrestrictedCircuit` is provably false. The unitary versions,
`unitaryUnrestrictedCircuit_4_canonical_direct` (closed iter 1040) and
`four_unitaryUnrestricted_implies_S4_or_S5`, are sorryAx-free. -/


/- Iter 689: removed `unitaryUnrestrictedCircuit_4_canonical` wrapper that
   was kept only for backward compatibility. It delegated to the legacy
   `unrestrictedCircuit_4_canonical` (which has 16 dispatcher sorries).
   Direct callers should use `unitaryUnrestrictedCircuit_4_canonical_direct`
   (defined below) which uses per-constructor `hV` payloads and avoids
   the dispatcher sorries entirely. See refactor iter 677:
   `four_unitaryUnrestricted_implies_S4_or_S5`. -/

/-- Discharges an `IsUnitary4` / `IsUnitary2` goal whose subject is built from
    `*`, `kron2`, `1` and `SWAP_4` over unitarity hypotheses in context.
    `with_reducible` is essential: at default transparency the unifier unfolds
    `kron2` / `SWAP_4` into their `Matrix.of` bodies and times out. -/
syntax "unitary_auto" : tactic
macro_rules
  | `(tactic| unitary_auto) =>
    `(tactic| repeat' with_reducible first
        | apply isUnitary4_mul
        | apply isUnitary2_mul
        | apply isUnitary4_kron2
        | assumption
        | exact isUnitary4_SWAP_4
        | exact isUnitary4_one
        | exact isUnitary2_one)

set_option maxHeartbeats 8000000 in
/-- Direct-proof variant of `unitaryUnrestrictedCircuit_4_canonical`. Uses
    the `UnitaryUnrestrictedCircuit` type's `cases h` to access each
    constructor's `hV` payload in mixed-XY branches (where chain-extraction
    fails — see iter 472).

    **Status (iter 723)**: ~215 / ~240 leaves closed (~89%). 31 remaining
    sorries are all **3-XY 3-real-embed chains** — chains where the 3
    real embeds use 3 DIFFERENT XY types (e.g., AC at position 1, AB at
    position 2, BC at position 3, possibly with a 4th XY embed wrapping).
    At each sorry site V₁, V₂, V (and V₃ if present) unitarities ARE
    available via constructor `hV` payloads — bootstrapping is NOT the
    blocker.

    ⚠️ **RETRACTED (iter 1035, 2026-08-14)**. The iter-722/729 "genuine
    blocker" recorded here — *"each of the 9 canonical disjuncts alternates
    between exactly 2 XY types, so a 3-XY chain cannot collapse to a 2-XY
    canonical pattern"* — is **FALSE**, and the ~600-900-line/multi-week
    estimate derived from it is a large over-estimate.

    Read the disjunction below (lines ~6219-6227): disjuncts **#1, #2 and #3
    each use ALL THREE pair types** —
      #1 `BC-AC-AB-BC`,  #2 `AB-BC-AC-AB`,  #3 `AC-BC-AB-AC`.
    Only #4-#9 are 2-type alternating. The nine patterns are exactly the three
    families `{X-Y-Z-X, X-Y-X-Y, X-Z-X-Z}` for `X ∈ {AB, BC, AC}`, i.e. #1-#3
    exist PRECISELY to host 3-XY chains. So no embed needs decomposing, and no
    new "XY-decomposition identity" is required.

    Actual remaining work (bookkeeping, not structure): each of the 31 sorries
    is a length-≤4 pair-type word that reduces to one of the 9 patterns by
    three moves already in the codebase — (a) MERGE adjacent same-type gates
    (`embedXY_mul` + SQL absorption), (b) PAD with `embedXY 1 = 1`, and
    (c) SWAP CONJUGATION to relabel a pair type (`swap_ab_embedBC`,
    `swap_bc_embedAC`, `swap_ac_embedAB`, …). Move (c) costs ZERO gates
    because each SWAP is itself an embed of its own pair type and is absorbed
    by a neighbour: `SWAP_BC_eq_embedBC`, `SWAP_AC_eq_embedAC`, and — added
    iter 1035 to complete the trio — `SWAP_AB_eq_embedAB`.

    Audit estimate (reported, not yet verified leaf-by-leaf): ~13 of the 31
    need NO swap at all (e.g. the 3-gate chain `AC-AB-BC` is disjunct #1 with
    `V₁ = 1`), and ~18 need exactly ONE swap conjugation. Fallback remains:
    accept as paper-cited Lemma C.1 black-boxes (Huang & Palsberg 2026,
    Appendix C, pages 29-30 of 3787463). See the iter-1035 entry in
    notes/scratch.md; the iter-722 investigation there is superseded.

    Structure mirrors `unrestrictedCircuit_4_canonical`'s suffices+cases
    tree; the difference is each `compose_XY` constructor pattern now
    also binds `hV : IsUnitary4 V`, available in scope for the matching
    mixed-XY helper. Heartbeats increased to 1600000 for large
    declaration size. -/
private theorem unitaryUnrestrictedCircuit_4_canonical_direct (Dg : DiagGate3)
    (h : UnitaryUnrestrictedCircuit 4 Dg.toMatrix) :
    ∃ V₁ V₂ V₃ V₄ : Mat4,
      IsUnitary4 V₁ ∧ IsUnitary4 V₂ ∧ IsUnitary4 V₃ ∧ IsUnitary4 V₄ ∧
      (Dg.toMatrix = embedBC V₁ * embedAC V₂ * embedAB V₃ * embedBC V₄ ∨
       Dg.toMatrix = embedAB V₁ * embedBC V₂ * embedAC V₃ * embedAB V₄ ∨
       Dg.toMatrix = embedAC V₁ * embedBC V₂ * embedAB V₃ * embedAC V₄ ∨
       Dg.toMatrix = embedAC V₁ * embedAB V₂ * embedAC V₃ * embedAB V₄ ∨
       Dg.toMatrix = embedBC V₁ * embedAB V₂ * embedBC V₃ * embedAB V₄ ∨
       Dg.toMatrix = embedBC V₁ * embedAC V₂ * embedBC V₃ * embedAC V₄ ∨
       Dg.toMatrix = embedAB V₁ * embedAC V₂ * embedAB V₃ * embedAC V₄ ∨
       Dg.toMatrix = embedAB V₁ * embedBC V₂ * embedAB V₃ * embedBC V₄ ∨
       Dg.toMatrix = embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄) := by
  suffices aux : ∀ (M : Mat8), UnitaryUnrestrictedCircuit 4 M →
      M.conjTranspose * M = (1 : Mat8) →
      ∃ V₁ V₂ V₃ V₄ : Mat4,
        IsUnitary4 V₁ ∧ IsUnitary4 V₂ ∧ IsUnitary4 V₃ ∧ IsUnitary4 V₄ ∧
        (M = embedBC V₁ * embedAC V₂ * embedAB V₃ * embedBC V₄ ∨
         M = embedAB V₁ * embedBC V₂ * embedAC V₃ * embedAB V₄ ∨
         M = embedAC V₁ * embedBC V₂ * embedAB V₃ * embedAC V₄ ∨
         M = embedAC V₁ * embedAB V₂ * embedAC V₃ * embedAB V₄ ∨
         M = embedBC V₁ * embedAB V₂ * embedBC V₃ * embedAB V₄ ∨
         M = embedBC V₁ * embedAC V₂ * embedBC V₃ * embedAC V₄ ∨
         M = embedAB V₁ * embedAC V₂ * embedAB V₃ * embedAC V₄ ∨
         M = embedAB V₁ * embedBC V₂ * embedAB V₃ * embedBC V₄ ∨
         M = embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄) by
    exact aux Dg.toMatrix h Dg.toMatrix_unitary
  intro M h hM_unit
  cases h with
  | weaken h3 =>
    -- depth 3 sub-circuit. Recurse on h3.
    cases h3 with
    | weaken h2 =>
      cases h2 with
      | weaken h1 =>
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product uA uB uC hA hB hC =>
            -- Deepest leaf: M = singleQubitLayer uA uB uC. Pattern #8.
            obtain ⟨V₁, V₂, V₃, V₄, hV₁, hV₂, hV₃, hV₄, h_eq⟩ :=
              unrestrictedCircuit_singleQubitLayer_canonical uA uB uC hA hB hC
            refine ⟨V₁, V₂, V₃, V₄, hV₁, hV₂, hV₃, hV₄, ?_⟩
            right; right; right; right; right; right; right; left
            exact h_eq
        | compose_AB V hV uA' uB' uC' hA' hB' hC' h0 =>
          -- Position-1 AB: M = SQL u_p · embedAB V · SQL u_1.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁, V₂, V₃, V₄, hV₁, hV₂, hV₃, hV₄, h_eq⟩ :=
              unrestrictedCircuit_singleAB_canonical V hV
                u_pA u_pB u_pC h_pA h_pB h_pC uA' uB' uC' hA' hB' hC'
            refine ⟨V₁, V₂, V₃, V₄, hV₁, hV₂, hV₃, hV₄, ?_⟩
            right; right; right; right; right; right; right; left
            exact h_eq
        | compose_BC V hV uA' uB' uC' hA' hB' hC' h0 =>
          -- Position-1 BC.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁, V₂, V₃, V₄, hV₁, hV₂, hV₃, hV₄, h_eq⟩ :=
              unrestrictedCircuit_singleBC_canonical V hV
                u_pA u_pB u_pC h_pA h_pB h_pC uA' uB' uC' hA' hB' hC'
            refine ⟨V₁, V₂, V₃, V₄, hV₁, hV₂, hV₃, hV₄, ?_⟩
            right; right; right; right; right; right; right; right
            exact h_eq
        | compose_AC V hV uA' uB' uC' hA' hB' hC' h0 =>
          -- Position-1 AC.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁, V₂, V₃, V₄, hV₁, hV₂, hV₃, hV₄, h_eq⟩ :=
              unrestrictedCircuit_singleAC_canonical V hV
                u_pA u_pB u_pC h_pA h_pB h_pC uA' uB' uC' hA' hB' hC'
            refine ⟨V₁, V₂, V₃, V₄, hV₁, hV₂, hV₃, hV₄, ?_⟩
            right; right; right; right; right; right; left
            exact h_eq
      | compose_AB V hV uA' uB' uC' hA' hB' hC' h1 =>
        -- Position-2 AB: M = SQL u_p · embedAB V · SQL u_2.
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁, V₂', V₃, V₄, hV₁, hV₂', hV₃, hV₄, h_eq⟩ :=
              unrestrictedCircuit_singleAB_canonical V hV
                u_pA u_pB u_pC h_pA h_pB h_pC uA' uB' uC' hA' hB' hC'
            refine ⟨V₁, V₂', V₃, V₄, hV₁, hV₂', hV₃, hV₄, ?_⟩
            right; right; right; right; right; right; right; left
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (2,1) AB-AB consecutive same-XY merge. Pattern #8.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge :
              singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                singleQubitLayer uA₁ uB₁ uC₁ * embedAB V *
                singleQubitLayer uA' uB' uC' =
              singleQubitLayer u_pA u_pB (u_pC * uC₁) *
                embedAB (V₁ * (kron2 uA₁ uB₁ * V)) *
                singleQubitLayer uA' uB' uC' := by
              rw [show singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                        singleQubitLayer uA₁ uB₁ uC₁ * embedAB V *
                        singleQubitLayer uA' uB' uC' =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAB V₁ * singleQubitLayer uA₁ uB₁ uC₁ * embedAB V) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [embedAB_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                        (singleQubitLayer I₂ I₂ uC₁ *
                          embedAB (V₁ * (kron2 uA₁ uB₁ * V))) *
                        singleQubitLayer uA' uB' uC' =
                    (singleQubitLayer u_pA u_pB u_pC *
                       singleQubitLayer I₂ I₂ uC₁) *
                      embedAB (V₁ * (kron2 uA₁ uB₁ * V)) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₁ * (kron2 uA₁ uB₁ * V)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hB₁) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleAB_canonical (V₁ * (kron2 uA₁ uB₁ * V))
                hV_merged
                u_pA u_pB (u_pC * uC₁) h_pA h_pB (isUnitary2_mul h_pC hC₁)
                uA' uB' uC' hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (2,1) outer AB, inner BC. Pattern #5 (BC-AB-BC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AB_at_3_2_canonical V₁ V hV₁ hV
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA' uB' uC'
                h_pA h_pB h_pC hA₁ hB₁ hC₁ hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; left
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (2,1) outer AB, inner AC. Pattern #4 (AC-AB-AC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_AB_at_3_2_canonical V₁ V hV₁ hV
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA' uB' uC'
                h_pA h_pB h_pC hA₁ hB₁ hC₁ hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; left
            exact h_eq
      | compose_BC V hV uA' uB' uC' hA' hB' hC' h1 =>
        -- Position-2 BC.
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁, V₂', V₃, V₄, hV₁, hV₂', hV₃, hV₄, h_eq⟩ :=
              unrestrictedCircuit_singleBC_canonical V hV
                u_pA u_pB u_pC h_pA h_pB h_pC uA' uB' uC' hA' hB' hC'
            refine ⟨V₁, V₂', V₃, V₄, hV₁, hV₂', hV₃, hV₄, ?_⟩
            right; right; right; right; right; right; right; right
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (2,1) outer BC, inner AB. Pattern #8 (AB-BC-AB-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_BC_at_3_2_canonical V₁ V hV₁ hV
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA' uB' uC'
                h_pA h_pB h_pC hA₁ hB₁ hC₁ hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (2,1) BC-BC consecutive same-XY merge. Pattern #9.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge :
              singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                singleQubitLayer uA₁ uB₁ uC₁ * embedBC V *
                singleQubitLayer uA' uB' uC' =
              singleQubitLayer (u_pA * uA₁) u_pB u_pC *
                embedBC (V₁ * (kron2 uB₁ uC₁ * V)) *
                singleQubitLayer uA' uB' uC' := by
              rw [show singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                        singleQubitLayer uA₁ uB₁ uC₁ * embedBC V *
                        singleQubitLayer uA' uB' uC' =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedBC V₁ * singleQubitLayer uA₁ uB₁ uC₁ * embedBC V) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [embedBC_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                        (singleQubitLayer uA₁ I₂ I₂ *
                          embedBC (V₁ * (kron2 uB₁ uC₁ * V))) *
                        singleQubitLayer uA' uB' uC' =
                    (singleQubitLayer u_pA u_pB u_pC *
                       singleQubitLayer uA₁ I₂ I₂) *
                      embedBC (V₁ * (kron2 uB₁ uC₁ * V)) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₁ * (kron2 uB₁ uC₁ * V)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hB₁ hC₁) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleBC_canonical (V₁ * (kron2 uB₁ uC₁ * V))
                hV_merged
                (u_pA * uA₁) u_pB u_pC (isUnitary2_mul h_pA hA₁) h_pB h_pC
                uA' uB' uC' hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            rw [h_merge]
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (2,1) outer BC, inner AC. Pattern #9 (AC-BC-AC-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_BC_at_3_2_canonical V₁ V hV₁ hV
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA' uB' uC'
                h_pA h_pB h_pC hA₁ hB₁ hC₁ hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            exact h_eq
      | compose_AC V hV uA' uB' uC' hA' hB' hC' h1 =>
        -- Position-2 AC.
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁, V₂', V₃, V₄, hV₁, hV₂', hV₃, hV₄, h_eq⟩ :=
              unrestrictedCircuit_singleAC_canonical V hV
                u_pA u_pB u_pC h_pA h_pB h_pC uA' uB' uC' hA' hB' hC'
            refine ⟨V₁, V₂', V₃, V₄, hV₁, hV₂', hV₃, hV₄, ?_⟩
            right; right; right; right; right; right; left
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (2,1) outer AC, inner AB. Pattern #7 (AB-AC-AB-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_AC_at_3_2_canonical V₁ V hV₁ hV
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA' uB' uC'
                h_pA h_pB h_pC hA₁ hB₁ hC₁ hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (2,1) outer AC, inner BC. Pattern #6 (BC-AC-BC-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AC_at_3_2_canonical V₁ V hV₁ hV
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA' uB' uC'
                h_pA h_pB h_pC hA₁ hB₁ hC₁ hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; left
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (2,1) AC-AC consecutive same-XY merge. Pattern #7.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge :
              singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                singleQubitLayer uA₁ uB₁ uC₁ * embedAC V *
                singleQubitLayer uA' uB' uC' =
              singleQubitLayer u_pA (u_pB * uB₁) u_pC *
                embedAC (V₁ * (kron2 uA₁ uC₁ * V)) *
                singleQubitLayer uA' uB' uC' := by
              rw [show singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                        singleQubitLayer uA₁ uB₁ uC₁ * embedAC V *
                        singleQubitLayer uA' uB' uC' =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAC V₁ * singleQubitLayer uA₁ uB₁ uC₁ * embedAC V) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [embedAC_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                        (singleQubitLayer I₂ uB₁ I₂ *
                          embedAC (V₁ * (kron2 uA₁ uC₁ * V))) *
                        singleQubitLayer uA' uB' uC' =
                    (singleQubitLayer u_pA u_pB u_pC *
                       singleQubitLayer I₂ uB₁ I₂) *
                      embedAC (V₁ * (kron2 uA₁ uC₁ * V)) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₁ * (kron2 uA₁ uC₁ * V)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hC₁) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleAC_canonical (V₁ * (kron2 uA₁ uC₁ * V))
                hV_merged
                u_pA (u_pB * uB₁) u_pC h_pA (isUnitary2_mul h_pB hB₁) h_pC
                uA' uB' uC' hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
    | compose_AB V hV uA' uB' uC' hA' hB' hC' h2 =>
      -- Position-3 AB.
      cases h2 with
      | weaken h1 =>
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁, V₂, V₃', V₄, hV₁, hV₂, hV₃', hV₄, h_eq⟩ :=
              unrestrictedCircuit_singleAB_canonical V hV
                u_pA u_pB u_pC h_pA h_pB h_pC uA' uB' uC' hA' hB' hC'
            refine ⟨V₁, V₂, V₃', V₄, hV₁, hV₂, hV₃', hV₄, ?_⟩
            right; right; right; right; right; right; right; left
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,1) AB-AB consecutive same-XY merge. Pattern #8.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge :
              singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                singleQubitLayer uA₁ uB₁ uC₁ * embedAB V *
                singleQubitLayer uA' uB' uC' =
              singleQubitLayer u_pA u_pB (u_pC * uC₁) *
                embedAB (V₁ * (kron2 uA₁ uB₁ * V)) *
                singleQubitLayer uA' uB' uC' := by
              rw [show singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                        singleQubitLayer uA₁ uB₁ uC₁ * embedAB V *
                        singleQubitLayer uA' uB' uC' =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAB V₁ * singleQubitLayer uA₁ uB₁ uC₁ * embedAB V) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [embedAB_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                        (singleQubitLayer I₂ I₂ uC₁ *
                          embedAB (V₁ * (kron2 uA₁ uB₁ * V))) *
                        singleQubitLayer uA' uB' uC' =
                    (singleQubitLayer u_pA u_pB u_pC *
                       singleQubitLayer I₂ I₂ uC₁) *
                      embedAB (V₁ * (kron2 uA₁ uB₁ * V)) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₁ * (kron2 uA₁ uB₁ * V)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hB₁) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleAB_canonical (V₁ * (kron2 uA₁ uB₁ * V))
                hV_merged
                u_pA u_pB (u_pC * uC₁) h_pA h_pB (isUnitary2_mul h_pC hC₁)
                uA' uB' uC' hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,1) outer AB inner BC. Pattern #5 (BC-AB-BC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AB_at_3_2_canonical V₁ V hV₁ hV
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA' uB' uC'
                h_pA h_pB h_pC hA₁ hB₁ hC₁ hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; left
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,1) outer AB inner AC. Pattern #4 (AC-AB-AC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_AB_at_3_2_canonical V₁ V hV₁ hV
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA' uB' uC'
                h_pA h_pB h_pC hA₁ hB₁ hC₁ hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; left
            exact h_eq
      | compose_AB V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (3,2) AB-AB consecutive same-XY merge. Pattern #8.
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge :
              singleQubitLayer u_pA u_pB u_pC * embedAB V₂ *
                singleQubitLayer uA₂ uB₂ uC₂ * embedAB V *
                singleQubitLayer uA' uB' uC' =
              singleQubitLayer u_pA u_pB (u_pC * uC₂) *
                embedAB (V₂ * (kron2 uA₂ uB₂ * V)) *
                singleQubitLayer uA' uB' uC' := by
              rw [show singleQubitLayer u_pA u_pB u_pC * embedAB V₂ *
                        singleQubitLayer uA₂ uB₂ uC₂ * embedAB V *
                        singleQubitLayer uA' uB' uC' =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAB V₂ * singleQubitLayer uA₂ uB₂ uC₂ * embedAB V) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [embedAB_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                        (singleQubitLayer I₂ I₂ uC₂ *
                          embedAB (V₂ * (kron2 uA₂ uB₂ * V))) *
                        singleQubitLayer uA' uB' uC' =
                    (singleQubitLayer u_pA u_pB u_pC *
                       singleQubitLayer I₂ I₂ uC₂) *
                      embedAB (V₂ * (kron2 uA₂ uB₂ * V)) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₂ * (kron2 uA₂ uB₂ * V)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hA₂ hB₂) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleAB_canonical (V₂ * (kron2 uA₂ uB₂ * V))
                hV_merged
                u_pA u_pB (u_pC * uC₂) h_pA h_pB (isUnitary2_mul h_pC hC₂)
                uA' uB' uC' hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) AB-AB-AB triple same-XY merge. Pattern #8.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            -- Strategy: apply embedAB_merge twice to collapse 3 embeds → 1.
            have h_merge :
              singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                singleQubitLayer uA₂ uB₂ uC₂ * embedAB V *
                singleQubitLayer uA' uB' uC' =
              singleQubitLayer u_pA u_pB ((u_pC * uC₁) * uC₂) *
                embedAB (V₁ * (kron2 uA₁ uB₁ * V₂) *
                          (kron2 uA₂ uB₂ * V)) *
                singleQubitLayer uA' uB' uC' := by
              -- First merge: V₁ * SQL · V₂.
              rw [show singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                        singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                        singleQubitLayer uA₂ uB₂ uC₂ * embedAB V *
                        singleQubitLayer uA' uB' uC' =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAB V₁ * singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂) *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedAB V *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [embedAB_merge]
              -- After first merge: SQL u_p · SQL I I uC₁ · embedAB(V₁₂) ·
              -- SQL u₂ · embedAB V · SQL u'.
              rw [show singleQubitLayer u_pA u_pB u_pC *
                        (singleQubitLayer I₂ I₂ uC₁ *
                          embedAB (V₁ * (kron2 uA₁ uB₁ * V₂))) *
                        singleQubitLayer uA₂ uB₂ uC₂ * embedAB V *
                        singleQubitLayer uA' uB' uC' =
                    (singleQubitLayer u_pA u_pB u_pC *
                       singleQubitLayer I₂ I₂ uC₁) *
                      (embedAB (V₁ * (kron2 uA₁ uB₁ * V₂)) *
                        singleQubitLayer uA₂ uB₂ uC₂ * embedAB V) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [singleQubitLayer_mul]
              -- Second merge: V₁₂ * SQL · V.
              rw [embedAB_merge]
              -- Combine outer SQL with middle SQL.
              rw [show singleQubitLayer (u_pA * I₂) (u_pB * I₂) (u_pC * uC₁) *
                        (singleQubitLayer I₂ I₂ uC₂ *
                          embedAB (V₁ * (kron2 uA₁ uB₁ * V₂) *
                                    (kron2 uA₂ uB₂ * V))) *
                        singleQubitLayer uA' uB' uC' =
                    (singleQubitLayer (u_pA * I₂) (u_pB * I₂) (u_pC * uC₁) *
                       singleQubitLayer I₂ I₂ uC₂) *
                      embedAB (V₁ * (kron2 uA₁ uB₁ * V₂) *
                                (kron2 uA₂ uB₂ * V)) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4
                (V₁ * (kron2 uA₁ uB₁ * V₂) * (kron2 uA₂ uB₂ * V)) :=
              isUnitary4_mul
                (isUnitary4_mul hV₁
                  (isUnitary4_mul (isUnitary4_kron2 hA₁ hB₁) hV₂))
                (isUnitary4_mul (isUnitary4_kron2 hA₂ hB₂) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleAB_canonical
                (V₁ * (kron2 uA₁ uB₁ * V₂) * (kron2 uA₂ uB₂ * V))
                hV_merged
                u_pA u_pB ((u_pC * uC₁) * uC₂) h_pA h_pB
                (isUnitary2_mul (isUnitary2_mul h_pC hC₁) hC₂)
                uA' uB' uC' hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) BC-AB-AB adjacent-same: V₂ and V outer merge (both AB).
          -- Pattern #5 (BC-AB-BC-AB) with V₃ = (merged) and V₄ = 1.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge :
              singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                singleQubitLayer uA₂ uB₂ uC₂ * embedAB V *
                singleQubitLayer uA' uB' uC' =
              singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                singleQubitLayer uA₁ uB₁ (uC₁ * uC₂) *
                embedAB (V₂ * (kron2 uA₂ uB₂ * V)) *
                singleQubitLayer uA' uB' uC' := by
              rw [show singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                        singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                        singleQubitLayer uA₂ uB₂ uC₂ * embedAB V *
                        singleQubitLayer uA' uB' uC' =
                    singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                      singleQubitLayer uA₁ uB₁ uC₁ *
                      (embedAB V₂ * singleQubitLayer uA₂ uB₂ uC₂ * embedAB V) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [embedAB_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                        singleQubitLayer uA₁ uB₁ uC₁ *
                        (singleQubitLayer I₂ I₂ uC₂ *
                          embedAB (V₂ * (kron2 uA₂ uB₂ * V))) *
                        singleQubitLayer uA' uB' uC' =
                    singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                      (singleQubitLayer uA₁ uB₁ uC₁ * singleQubitLayer I₂ I₂ uC₂) *
                      embedAB (V₂ * (kron2 uA₂ uB₂ * V)) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₂ * (kron2 uA₂ uB₂ * V)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hA₂ hB₂) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AB_at_3_2_canonical V₁
                (V₂ * (kron2 uA₂ uB₂ * V)) hV₁ hV_merged
                u_pA u_pB u_pC uA₁ uB₁ (uC₁ * uC₂) uA' uB' uC'
                h_pA h_pB h_pC hA₁ hB₁ (isUnitary2_mul hC₁ hC₂)
                hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) AC-AB-AB adjacent-same: V₂ and V outer merge (both AB).
          -- Pattern #4 (AC-AB-AC-AB) with V₂ from helper, V₄ = 1.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge :
              singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                singleQubitLayer uA₂ uB₂ uC₂ * embedAB V *
                singleQubitLayer uA' uB' uC' =
              singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                singleQubitLayer uA₁ uB₁ (uC₁ * uC₂) *
                embedAB (V₂ * (kron2 uA₂ uB₂ * V)) *
                singleQubitLayer uA' uB' uC' := by
              rw [show singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                        singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                        singleQubitLayer uA₂ uB₂ uC₂ * embedAB V *
                        singleQubitLayer uA' uB' uC' =
                    singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                      singleQubitLayer uA₁ uB₁ uC₁ *
                      (embedAB V₂ * singleQubitLayer uA₂ uB₂ uC₂ * embedAB V) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [embedAB_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                        singleQubitLayer uA₁ uB₁ uC₁ *
                        (singleQubitLayer I₂ I₂ uC₂ *
                          embedAB (V₂ * (kron2 uA₂ uB₂ * V))) *
                        singleQubitLayer uA' uB' uC' =
                    singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                      (singleQubitLayer uA₁ uB₁ uC₁ * singleQubitLayer I₂ I₂ uC₂) *
                      embedAB (V₂ * (kron2 uA₂ uB₂ * V)) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₂ * (kron2 uA₂ uB₂ * V)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hA₂ hB₂) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_AB_at_3_2_canonical V₁
                (V₂ * (kron2 uA₂ uB₂ * V)) hV₁ hV_merged
                u_pA u_pB u_pC uA₁ uB₁ (uC₁ * uC₂) uA' uB' uC'
                h_pA h_pB h_pC hA₁ hB₁ (isUnitary2_mul hC₁ hC₂)
                hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; left
            rw [h_merge]
            exact h_eq
      | compose_BC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (3,2) outer AB inner BC. Pattern #5 (BC-AB-BC-AB).
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AB_at_3_2_canonical V₂ V hV₂ hV
                u_pA u_pB u_pC uA₂ uB₂ uC₂ uA' uB' uC'
                h_pA h_pB h_pC hA₂ hB₂ hC₂ hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; left
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) AB-BC-AB non-adjacent-same: V₁ and V outer both AB.
          -- Pattern #8 (AB-BC-AB-BC). Uses stubbed sandwich helper.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AB_BC_AB_to_4embed V₁ V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA' uB' uC'
            have hV₁_unit : IsUnitary4
                (kron2 u_pA u_pB * V₁ * kron2 uA₁ uB₁) :=
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV₁)
                (isUnitary4_kron2 hA₁ hB₁)
            have hV₂_unit : IsUnitary4
                (kron2 1 (u_pC * uC₁) * V₂ * kron2 uB₂ uC₂) :=
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_kron2 isUnitary2_one
                    (isUnitary2_mul h_pC hC₁)) hV₂)
                (isUnitary4_kron2 hB₂ hC₂)
            have hV₃_unit : IsUnitary4
                (kron2 uA₂ 1 * V * kron2 uA' uB') :=
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₂ isUnitary2_one) hV)
                (isUnitary4_kron2 hA' hB')
            have hV₄_unit : IsUnitary4 (kron2 (1 : Mat2) uC') :=
              isUnitary4_kron2 isUnitary2_one hC'
            refine ⟨_, _, _, _, hV₁_unit, hV₂_unit, hV₃_unit, hV₄_unit, ?_⟩
            right; right; right; right; right; right; right; left
            exact h_chain
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) BC-BC-AB inner-pair-merge: V₁ and V₂ both BC.
          -- Pattern #5 (BC-AB-BC-AB) with merged V replaces V₁,V₂.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := inner_BC_pair_merge_sandwich V₁ V₂ (embedAB V)
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA' uB' uC'
            have hV_merged : IsUnitary4 (V₁ * (kron2 uB₁ uC₁ * V₂)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hB₁ hC₁) hV₂)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AB_at_3_2_canonical
                (V₁ * (kron2 uB₁ uC₁ * V₂)) V hV_merged hV
                (u_pA * uA₁) u_pB u_pC uA₂ uB₂ uC₂ uA' uB' uC'
                (isUnitary2_mul h_pA hA₁) h_pB h_pC hA₂ hB₂ hC₂
                hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) AC-BC-AB all-different: V₁=AC, V₂=BC, V outer=AB.
          -- Pattern #3 (AC-BC-AB-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AC_BC_AB_to_4embed V₁ V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA' uB' uC'
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV₁)
                (isUnitary4_kron2 hA₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pB hB₁) isUnitary2_one) hV₂)
                (isUnitary4_kron2 hB₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₂ isUnitary2_one) hV)
                (isUnitary4_kron2 hA' hB'),
              isUnitary4_kron2 isUnitary2_one hC', ?_⟩
            right; right; left
            exact h_chain
      | compose_AC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (3,2) outer AB inner AC. Pattern #4 (AC-AB-AC-AB).
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_AB_at_3_2_canonical V₂ V hV₂ hV
                u_pA u_pB u_pC uA₂ uB₂ uC₂ uA' uB' uC'
                h_pA h_pB h_pC hA₂ hB₂ hC₂ hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; left
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) AB-AC-AB non-adjacent-same: V₁ and V outer both AB.
          -- Pattern #7 (AB-AC-AB-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AB_AC_AB_to_4embed V₁ V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA' uB' uC'
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV₁)
                (isUnitary4_kron2 hA₁ hB₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul h_pC hC₁)) hV₂)
                (isUnitary4_kron2 hA₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hB₂) hV)
                (isUnitary4_kron2 hA' hB'),
              isUnitary4_kron2 isUnitary2_one hC', ?_⟩
            right; right; right; right; right; right; left
            exact h_chain
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) BC-AC-AB all-different: V₁=BC, V₂=AC, V outer=AB.
          -- Pattern #1 (BC-AC-AB-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_BC_AC_AB_to_4embed V₁ V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA' uB' uC'
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV₁)
                (isUnitary4_kron2 hB₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pA hA₁) isUnitary2_one) hV₂)
                (isUnitary4_kron2 hA₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hB₂) hV)
                (isUnitary4_kron2 hA' hB'),
              isUnitary4_kron2 isUnitary2_one hC', ?_⟩
            left
            exact h_chain
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) AC-AC-AB inner-pair-merge: V₁ and V₂ both AC.
          -- Pattern #4 (AC-AB-AC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := inner_AC_pair_merge_sandwich V₁ V₂ (embedAB V)
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA' uB' uC'
            have hV_merged : IsUnitary4 (V₁ * (kron2 uA₁ uC₁ * V₂)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hC₁) hV₂)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_AB_at_3_2_canonical
                (V₁ * (kron2 uA₁ uC₁ * V₂)) V hV_merged hV
                u_pA (u_pB * uB₁) u_pC uA₂ uB₂ uC₂ uA' uB' uC'
                h_pA (isUnitary2_mul h_pB hB₁) h_pC hA₂ hB₂ hC₂
                hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; left
            rw [h_merge]
            exact h_eq
    | compose_BC V hV uA' uB' uC' hA' hB' hC' h2 =>
      -- Position-3 BC.
      cases h2 with
      | weaken h1 =>
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁, V₂, V₃', V₄, hV₁, hV₂, hV₃', hV₄, h_eq⟩ :=
              unrestrictedCircuit_singleBC_canonical V hV
                u_pA u_pB u_pC h_pA h_pB h_pC uA' uB' uC' hA' hB' hC'
            refine ⟨V₁, V₂, V₃', V₄, hV₁, hV₂, hV₃', hV₄, ?_⟩
            right; right; right; right; right; right; right; right
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,1) outer BC inner AB. Pattern #8 (AB-BC-AB-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_BC_at_3_2_canonical V₁ V hV₁ hV
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA' uB' uC'
                h_pA h_pB h_pC hA₁ hB₁ hC₁ hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,1) BC-BC consecutive same-XY merge. Pattern #9.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge :
              singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                singleQubitLayer uA₁ uB₁ uC₁ * embedBC V *
                singleQubitLayer uA' uB' uC' =
              singleQubitLayer (u_pA * uA₁) u_pB u_pC *
                embedBC (V₁ * (kron2 uB₁ uC₁ * V)) *
                singleQubitLayer uA' uB' uC' := by
              rw [show singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                        singleQubitLayer uA₁ uB₁ uC₁ * embedBC V *
                        singleQubitLayer uA' uB' uC' =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedBC V₁ * singleQubitLayer uA₁ uB₁ uC₁ * embedBC V) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [embedBC_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                        (singleQubitLayer uA₁ I₂ I₂ *
                          embedBC (V₁ * (kron2 uB₁ uC₁ * V))) *
                        singleQubitLayer uA' uB' uC' =
                    (singleQubitLayer u_pA u_pB u_pC *
                       singleQubitLayer uA₁ I₂ I₂) *
                      embedBC (V₁ * (kron2 uB₁ uC₁ * V)) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₁ * (kron2 uB₁ uC₁ * V)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hB₁ hC₁) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleBC_canonical (V₁ * (kron2 uB₁ uC₁ * V))
                hV_merged
                (u_pA * uA₁) u_pB u_pC (isUnitary2_mul h_pA hA₁) h_pB h_pC
                uA' uB' uC' hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            rw [h_merge]
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,1) outer BC inner AC. Pattern #9 (AC-BC-AC-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_BC_at_3_2_canonical V₁ V hV₁ hV
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA' uB' uC'
                h_pA h_pB h_pC hA₁ hB₁ hC₁ hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            exact h_eq
      | compose_AB V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (3,2) outer BC inner AB. Pattern #8 (AB-BC-AB-BC).
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_BC_at_3_2_canonical V₂ V hV₂ hV
                u_pA u_pB u_pC uA₂ uB₂ uC₂ uA' uB' uC'
                h_pA h_pB h_pC hA₂ hB₂ hC₂ hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) AB-AB-BC inner-pair-merge: V₁ and V₂ both AB.
          -- Pattern #8 (AB-BC-AB-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := inner_AB_pair_merge_sandwich V₁ V₂ (embedBC V)
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA' uB' uC'
            have hV_merged : IsUnitary4 (V₁ * (kron2 uA₁ uB₁ * V₂)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hB₁) hV₂)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_BC_at_3_2_canonical
                (V₁ * (kron2 uA₁ uB₁ * V₂)) V hV_merged hV
                u_pA u_pB (u_pC * uC₁) uA₂ uB₂ uC₂ uA' uB' uC'
                h_pA h_pB (isUnitary2_mul h_pC hC₁) hA₂ hB₂ hC₂
                hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) BC-AB-BC non-adjacent-same: V₁ and V outer both BC.
          -- Pattern #5 (BC-AB-BC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_BC_AB_BC_to_4embed V₁ V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA' uB' uC'
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV₁)
                (isUnitary4_kron2 hB₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pA hA₁) isUnitary2_one) hV₂)
                (isUnitary4_kron2 hA₂ hB₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₂) hV)
                (isUnitary4_kron2 hB' hC'),
              isUnitary4_kron2 hA' isUnitary2_one, ?_⟩
            right; right; right; right; left
            exact h_chain
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) AC-AB-BC all-different. Pattern #1 (BC-AC-AB-BC), V₁ = 1.
          -- **Iter 1036**: one of the 31 leaves blocked by the iter-729 "3-XY
          -- gap", which is RETRACTED (see the declaration docstring). The
          -- trailing A-only leftover commutes past `embedBC`
          -- (`embedBC_comm_singleQubitLayer_A`) and absorbs into the AB gate, so
          -- no fourth real embed is needed and the word IS disjunct #1 with the
          -- leading BC slot set to 1. Bookkeeping: `sandwich_AC_AB_BC_to_4embed`.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AC_AB_BC_to_4embed V₁ V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA' uB' uC'
            refine ⟨1,
              kron2 u_pA u_pC * V₁ * kron2 uA₁ uC₁,
              kron2 1 (u_pB * uB₁) * V₂ * kron2 uA₂ uB₂ * kron2 uA' 1,
              kron2 1 uC₂ * V * kron2 uB' uC',
              isUnitary4_one,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV₁)
                (isUnitary4_kron2 hA₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul
                    (isUnitary4_kron2 isUnitary2_one (isUnitary2_mul h_pB hB₁))
                    hV₂)
                  (isUnitary4_kron2 hA₂ hB₂))
                (isUnitary4_kron2 hA' isUnitary2_one),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₂) hV)
                (isUnitary4_kron2 hB' hC'), ?_⟩
            left
            rw [embedBC_one, one_mul]
            exact h_chain
      | compose_BC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (3,2) BC-BC consecutive same-XY merge. Pattern #9.
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge :
              singleQubitLayer u_pA u_pB u_pC * embedBC V₂ *
                singleQubitLayer uA₂ uB₂ uC₂ * embedBC V *
                singleQubitLayer uA' uB' uC' =
              singleQubitLayer (u_pA * uA₂) u_pB u_pC *
                embedBC (V₂ * (kron2 uB₂ uC₂ * V)) *
                singleQubitLayer uA' uB' uC' := by
              rw [show singleQubitLayer u_pA u_pB u_pC * embedBC V₂ *
                        singleQubitLayer uA₂ uB₂ uC₂ * embedBC V *
                        singleQubitLayer uA' uB' uC' =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedBC V₂ * singleQubitLayer uA₂ uB₂ uC₂ * embedBC V) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [embedBC_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                        (singleQubitLayer uA₂ I₂ I₂ *
                          embedBC (V₂ * (kron2 uB₂ uC₂ * V))) *
                        singleQubitLayer uA' uB' uC' =
                    (singleQubitLayer u_pA u_pB u_pC *
                       singleQubitLayer uA₂ I₂ I₂) *
                      embedBC (V₂ * (kron2 uB₂ uC₂ * V)) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₂ * (kron2 uB₂ uC₂ * V)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hB₂ hC₂) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleBC_canonical (V₂ * (kron2 uB₂ uC₂ * V))
                hV_merged
                (u_pA * uA₂) u_pB u_pC (isUnitary2_mul h_pA hA₂) h_pB h_pC
                uA' uB' uC' hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            rw [h_merge]
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) AB-BC-BC adjacent-same: V₂ and V outer merge (both BC).
          -- Pattern #8 (AB-BC-AB-BC) with V₂ from helper, V₃ = V_merged, V₄ = 1.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := outer_BC_pair_merge_sandwich (embedAB V₁) V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA' uB' uC'
            have hV_merged : IsUnitary4 (V₂ * (kron2 uB₂ uC₂ * V)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hB₂ hC₂) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_BC_at_3_2_canonical V₁
                (V₂ * (kron2 uB₂ uC₂ * V)) hV₁ hV_merged
                u_pA u_pB u_pC (uA₁ * uA₂) uB₁ uC₁ uA' uB' uC'
                h_pA h_pB h_pC (isUnitary2_mul hA₁ hA₂) hB₁ hC₁
                hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) BC-BC-BC triple same-XY merge. Pattern #9.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge :
              singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                singleQubitLayer uA₂ uB₂ uC₂ * embedBC V *
                singleQubitLayer uA' uB' uC' =
              singleQubitLayer ((u_pA * uA₁) * uA₂) u_pB u_pC *
                embedBC (V₁ * (kron2 uB₁ uC₁ * V₂) *
                          (kron2 uB₂ uC₂ * V)) *
                singleQubitLayer uA' uB' uC' := by
              rw [show singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                        singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                        singleQubitLayer uA₂ uB₂ uC₂ * embedBC V *
                        singleQubitLayer uA' uB' uC' =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedBC V₁ * singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂) *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedBC V *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [embedBC_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                        (singleQubitLayer uA₁ I₂ I₂ *
                          embedBC (V₁ * (kron2 uB₁ uC₁ * V₂))) *
                        singleQubitLayer uA₂ uB₂ uC₂ * embedBC V *
                        singleQubitLayer uA' uB' uC' =
                    (singleQubitLayer u_pA u_pB u_pC *
                       singleQubitLayer uA₁ I₂ I₂) *
                      (embedBC (V₁ * (kron2 uB₁ uC₁ * V₂)) *
                        singleQubitLayer uA₂ uB₂ uC₂ * embedBC V) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [singleQubitLayer_mul]
              rw [embedBC_merge]
              rw [show singleQubitLayer (u_pA * uA₁) (u_pB * I₂) (u_pC * I₂) *
                        (singleQubitLayer uA₂ I₂ I₂ *
                          embedBC (V₁ * (kron2 uB₁ uC₁ * V₂) *
                                    (kron2 uB₂ uC₂ * V))) *
                        singleQubitLayer uA' uB' uC' =
                    (singleQubitLayer (u_pA * uA₁) (u_pB * I₂) (u_pC * I₂) *
                       singleQubitLayer uA₂ I₂ I₂) *
                      embedBC (V₁ * (kron2 uB₁ uC₁ * V₂) *
                                (kron2 uB₂ uC₂ * V)) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4
                (V₁ * (kron2 uB₁ uC₁ * V₂) * (kron2 uB₂ uC₂ * V)) :=
              isUnitary4_mul
                (isUnitary4_mul hV₁
                  (isUnitary4_mul (isUnitary4_kron2 hB₁ hC₁) hV₂))
                (isUnitary4_mul (isUnitary4_kron2 hB₂ hC₂) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleBC_canonical
                (V₁ * (kron2 uB₁ uC₁ * V₂) * (kron2 uB₂ uC₂ * V))
                hV_merged
                ((u_pA * uA₁) * uA₂) u_pB u_pC
                (isUnitary2_mul (isUnitary2_mul h_pA hA₁) hA₂) h_pB h_pC
                uA' uB' uC' hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            rw [h_merge]
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) AC-BC-BC adjacent-same: V₂ and V outer merge (both BC).
          -- Pattern #9 (AC-BC-AC-BC) with V₂ from helper, V₃ = V_merged, V₄ = 1.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := outer_BC_pair_merge_sandwich (embedAC V₁) V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA' uB' uC'
            have hV_merged : IsUnitary4 (V₂ * (kron2 uB₂ uC₂ * V)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hB₂ hC₂) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_BC_at_3_2_canonical V₁
                (V₂ * (kron2 uB₂ uC₂ * V)) hV₁ hV_merged
                u_pA u_pB u_pC (uA₁ * uA₂) uB₁ uC₁ uA' uB' uC'
                h_pA h_pB h_pC (isUnitary2_mul hA₁ hA₂) hB₁ hC₁
                hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            rw [h_merge]
            exact h_eq
      | compose_AC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (3,2) outer BC inner AC. Pattern #9 (AC-BC-AC-BC).
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_BC_at_3_2_canonical V₂ V hV₂ hV
                u_pA u_pB u_pC uA₂ uB₂ uC₂ uA' uB' uC'
                h_pA h_pB h_pC hA₂ hB₂ hC₂ hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) AB-AC-BC all-different. Pattern #1 (BC-AC-AB-BC) with
          -- V₁ = SWAP_4. Iter 1040: closed via `sandwich_AB_AC_BC_to_4embed`,
          -- the SWAP_BC transport of `sandwich_AC_AB_BC_to_4embed` (paper
          -- Appendix C move 2: insert SWAP gates that cancel out).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AB_AC_BC_to_4embed V₁ V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA' uB' uC'
            refine ⟨_, _, _, _,
              isUnitary4_SWAP_4,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV₁)
                (isUnitary4_kron2 hA₁ hB₁),
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul
                    (isUnitary4_kron2 isUnitary2_one (isUnitary2_mul h_pC hC₁))
                    hV₂)
                  (isUnitary4_kron2 hA₂ hC₂))
                (isUnitary4_kron2 hA' isUnitary2_one),
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hB₂)
                    (isUnitary4_swap4_conj V hV))
                  (isUnitary4_kron2 hC' hB'))
                isUnitary4_SWAP_4, ?_⟩
            left
            exact h_chain
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) BC-AC-BC non-adjacent-same: V₁ and V outer both BC.
          -- Pattern #6 (BC-AC-BC-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_BC_AC_BC_to_4embed V₁ V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA' uB' uC'
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV₁)
                (isUnitary4_kron2 hB₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pA hA₁) isUnitary2_one) hV₂)
                (isUnitary4_kron2 hA₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hB₂ isUnitary2_one) hV)
                (isUnitary4_kron2 hB' hC'),
              isUnitary4_kron2 hA' isUnitary2_one, ?_⟩
            right; right; right; right; right; left
            exact h_chain
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) AC-AC-BC inner-pair-merge: V₁ and V₂ both AC.
          -- Pattern #9 (AC-BC-AC-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := inner_AC_pair_merge_sandwich V₁ V₂ (embedBC V)
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA' uB' uC'
            have hV_merged : IsUnitary4 (V₁ * (kron2 uA₁ uC₁ * V₂)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hC₁) hV₂)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_BC_at_3_2_canonical
                (V₁ * (kron2 uA₁ uC₁ * V₂)) V hV_merged hV
                u_pA (u_pB * uB₁) u_pC uA₂ uB₂ uC₂ uA' uB' uC'
                h_pA (isUnitary2_mul h_pB hB₁) h_pC hA₂ hB₂ hC₂
                hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            rw [h_merge]
            exact h_eq
    | compose_AC V hV uA' uB' uC' hA' hB' hC' h2 =>
      -- Position-3 AC.
      cases h2 with
      | weaken h1 =>
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁, V₂, V₃', V₄, hV₁, hV₂, hV₃', hV₄, h_eq⟩ :=
              unrestrictedCircuit_singleAC_canonical V hV
                u_pA u_pB u_pC h_pA h_pB h_pC uA' uB' uC' hA' hB' hC'
            refine ⟨V₁, V₂, V₃', V₄, hV₁, hV₂, hV₃', hV₄, ?_⟩
            right; right; right; right; right; right; left
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,1) outer AC inner AB. Pattern #7 (AB-AC-AB-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_AC_at_3_2_canonical V₁ V hV₁ hV
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA' uB' uC'
                h_pA h_pB h_pC hA₁ hB₁ hC₁ hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,1) outer AC inner BC. Pattern #6 (BC-AC-BC-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AC_at_3_2_canonical V₁ V hV₁ hV
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA' uB' uC'
                h_pA h_pB h_pC hA₁ hB₁ hC₁ hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; left
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,1) AC-AC consecutive same-XY merge. Pattern #7.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge :
              singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                singleQubitLayer uA₁ uB₁ uC₁ * embedAC V *
                singleQubitLayer uA' uB' uC' =
              singleQubitLayer u_pA (u_pB * uB₁) u_pC *
                embedAC (V₁ * (kron2 uA₁ uC₁ * V)) *
                singleQubitLayer uA' uB' uC' := by
              rw [show singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                        singleQubitLayer uA₁ uB₁ uC₁ * embedAC V *
                        singleQubitLayer uA' uB' uC' =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAC V₁ * singleQubitLayer uA₁ uB₁ uC₁ * embedAC V) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [embedAC_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                        (singleQubitLayer I₂ uB₁ I₂ *
                          embedAC (V₁ * (kron2 uA₁ uC₁ * V))) *
                        singleQubitLayer uA' uB' uC' =
                    (singleQubitLayer u_pA u_pB u_pC *
                       singleQubitLayer I₂ uB₁ I₂) *
                      embedAC (V₁ * (kron2 uA₁ uC₁ * V)) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₁ * (kron2 uA₁ uC₁ * V)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hC₁) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleAC_canonical (V₁ * (kron2 uA₁ uC₁ * V))
                hV_merged
                u_pA (u_pB * uB₁) u_pC h_pA (isUnitary2_mul h_pB hB₁) h_pC
                uA' uB' uC' hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
      | compose_AB V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (3,2) outer AC inner AB. Pattern #7 (AB-AC-AB-AC).
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_AC_at_3_2_canonical V₂ V hV₂ hV
                u_pA u_pB u_pC uA₂ uB₂ uC₂ uA' uB' uC'
                h_pA h_pB h_pC hA₂ hB₂ hC₂ hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) AB-AB-AC inner-pair-merge: V₁ and V₂ both AB.
          -- Pattern #7 (AB-AC-AB-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := inner_AB_pair_merge_sandwich V₁ V₂ (embedAC V)
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA' uB' uC'
            have hV_merged : IsUnitary4 (V₁ * (kron2 uA₁ uB₁ * V₂)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hB₁) hV₂)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_AC_at_3_2_canonical
                (V₁ * (kron2 uA₁ uB₁ * V₂)) V hV_merged hV
                u_pA u_pB (u_pC * uC₁) uA₂ uB₂ uC₂ uA' uB' uC'
                h_pA h_pB (isUnitary2_mul h_pC hC₁) hA₂ hB₂ hC₂
                hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) BC-AB-AC all-different. Pattern #3 (AC-BC-AB-AC), V₁ = 1.
          -- Iter 1038: mirror of the AC-AB-BC closure — the trailing leftover
          -- is B-only, commutes past `embedAC` and absorbs into the AB gate,
          -- so no fourth real embed is needed.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_BC_AB_AC_to_4embed V₁ V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA' uB' uC'
            refine ⟨1,
              kron2 u_pB u_pC * V₁ * kron2 uB₁ uC₁,
              kron2 (u_pA * uA₁) 1 * V₂ * kron2 uA₂ uB₂ * kron2 1 uB',
              kron2 1 uC₂ * V * kron2 uA' uC',
              isUnitary4_one,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV₁)
                (isUnitary4_kron2 hB₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul
                    (isUnitary4_kron2 (isUnitary2_mul h_pA hA₁) isUnitary2_one)
                    hV₂)
                  (isUnitary4_kron2 hA₂ hB₂))
                (isUnitary4_kron2 isUnitary2_one hB'),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₂) hV)
                (isUnitary4_kron2 hA' hC'), ?_⟩
            right; right; left
            rw [embedAC_one, one_mul]
            exact h_chain
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) AC-AB-AC non-adjacent-same: V₁ and V outer both AC.
          -- Pattern #4 (AC-AB-AC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AC_AB_AC_to_4embed V₁ V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA' uB' uC'
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV₁)
                (isUnitary4_kron2 hA₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul h_pB hB₁)) hV₂)
                (isUnitary4_kron2 hA₂ hB₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₂) hV)
                (isUnitary4_kron2 hA' hC'),
              isUnitary4_kron2 isUnitary2_one hB', ?_⟩
            right; right; right; left
            exact h_chain
      | compose_BC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (3,2) outer AC inner BC. Pattern #6 (BC-AC-BC-AC).
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AC_at_3_2_canonical V₂ V hV₂ hV
                u_pA u_pB u_pC uA₂ uB₂ uC₂ uA' uB' uC'
                h_pA h_pB h_pC hA₂ hB₂ hC₂ hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; left
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) AB-BC-AC all-different: V₁=AB, V₂=BC, V outer=AC.
          -- Pattern #2 (AB-BC-AC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AB_BC_AC_to_4embed V₁ V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA' uB' uC'
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV₁)
                (isUnitary4_kron2 hA₁ hB₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul h_pC hC₁)) hV₂)
                (isUnitary4_kron2 hB₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₂ isUnitary2_one) hV)
                (isUnitary4_kron2 hA' hC'),
              isUnitary4_kron2 isUnitary2_one hB', ?_⟩
            right; left
            exact h_chain
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) BC-BC-AC inner-pair-merge: V₁ and V₂ both BC.
          -- Pattern #6 (BC-AC-BC-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := inner_BC_pair_merge_sandwich V₁ V₂ (embedAC V)
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA' uB' uC'
            have hV_merged : IsUnitary4 (V₁ * (kron2 uB₁ uC₁ * V₂)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hB₁ hC₁) hV₂)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AC_at_3_2_canonical
                (V₁ * (kron2 uB₁ uC₁ * V₂)) V hV_merged hV
                (u_pA * uA₁) u_pB u_pC uA₂ uB₂ uC₂ uA' uB' uC'
                (isUnitary2_mul h_pA hA₁) h_pB h_pC hA₂ hB₂ hC₂
                hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) AC-BC-AC non-adjacent-same: V₁ and V outer both AC.
          -- Pattern #9 (AC-BC-AC-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AC_BC_AC_to_4embed V₁ V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA' uB' uC'
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV₁)
                (isUnitary4_kron2 hA₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pB hB₁) isUnitary2_one) hV₂)
                (isUnitary4_kron2 hB₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₂ isUnitary2_one) hV)
                (isUnitary4_kron2 hA' hC'),
              isUnitary4_kron2 hB' isUnitary2_one, ?_⟩
            right; right; right; right; right; right; right; right
            exact h_chain
      | compose_AC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (3,2) AC-AC consecutive same-XY merge. Pattern #7.
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge :
              singleQubitLayer u_pA u_pB u_pC * embedAC V₂ *
                singleQubitLayer uA₂ uB₂ uC₂ * embedAC V *
                singleQubitLayer uA' uB' uC' =
              singleQubitLayer u_pA (u_pB * uB₂) u_pC *
                embedAC (V₂ * (kron2 uA₂ uC₂ * V)) *
                singleQubitLayer uA' uB' uC' := by
              rw [show singleQubitLayer u_pA u_pB u_pC * embedAC V₂ *
                        singleQubitLayer uA₂ uB₂ uC₂ * embedAC V *
                        singleQubitLayer uA' uB' uC' =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAC V₂ * singleQubitLayer uA₂ uB₂ uC₂ * embedAC V) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [embedAC_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                        (singleQubitLayer I₂ uB₂ I₂ *
                          embedAC (V₂ * (kron2 uA₂ uC₂ * V))) *
                        singleQubitLayer uA' uB' uC' =
                    (singleQubitLayer u_pA u_pB u_pC *
                       singleQubitLayer I₂ uB₂ I₂) *
                      embedAC (V₂ * (kron2 uA₂ uC₂ * V)) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₂ * (kron2 uA₂ uC₂ * V)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hA₂ hC₂) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleAC_canonical (V₂ * (kron2 uA₂ uC₂ * V))
                hV_merged
                u_pA (u_pB * uB₂) u_pC h_pA (isUnitary2_mul h_pB hB₂) h_pC
                uA' uB' uC' hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) AB-AC-AC adjacent-same: V₂ and V outer merge (both AC).
          -- Pattern #7 (AB-AC-AB-AC) with V₂ from helper, V₄ = 1.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := outer_AC_pair_merge_sandwich (embedAB V₁) V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA' uB' uC'
            have hV_merged : IsUnitary4 (V₂ * (kron2 uA₂ uC₂ * V)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hA₂ hC₂) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_AC_at_3_2_canonical V₁
                (V₂ * (kron2 uA₂ uC₂ * V)) hV₁ hV_merged
                u_pA u_pB u_pC uA₁ (uB₁ * uB₂) uC₁ uA' uB' uC'
                h_pA h_pB h_pC hA₁ (isUnitary2_mul hB₁ hB₂) hC₁
                hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) BC-AC-AC adjacent-same: V₂ and V outer merge (both AC).
          -- Pattern #6 (BC-AC-BC-AC) with V₂ from helper, V₄ = 1.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := outer_AC_pair_merge_sandwich (embedBC V₁) V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA' uB' uC'
            have hV_merged : IsUnitary4 (V₂ * (kron2 uA₂ uC₂ * V)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hA₂ hC₂) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AC_at_3_2_canonical V₁
                (V₂ * (kron2 uA₂ uC₂ * V)) hV₁ hV_merged
                u_pA u_pB u_pC uA₁ (uB₁ * uB₂) uC₁ uA' uB' uC'
                h_pA h_pB h_pC hA₁ (isUnitary2_mul hB₁ hB₂) hC₁
                hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) AC-AC-AC triple same-XY merge. Pattern #7.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge :
              singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                singleQubitLayer uA₂ uB₂ uC₂ * embedAC V *
                singleQubitLayer uA' uB' uC' =
              singleQubitLayer u_pA ((u_pB * uB₁) * uB₂) u_pC *
                embedAC (V₁ * (kron2 uA₁ uC₁ * V₂) *
                          (kron2 uA₂ uC₂ * V)) *
                singleQubitLayer uA' uB' uC' := by
              rw [show singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                        singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                        singleQubitLayer uA₂ uB₂ uC₂ * embedAC V *
                        singleQubitLayer uA' uB' uC' =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAC V₁ * singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂) *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedAC V *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [embedAC_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                        (singleQubitLayer I₂ uB₁ I₂ *
                          embedAC (V₁ * (kron2 uA₁ uC₁ * V₂))) *
                        singleQubitLayer uA₂ uB₂ uC₂ * embedAC V *
                        singleQubitLayer uA' uB' uC' =
                    (singleQubitLayer u_pA u_pB u_pC *
                       singleQubitLayer I₂ uB₁ I₂) *
                      (embedAC (V₁ * (kron2 uA₁ uC₁ * V₂)) *
                        singleQubitLayer uA₂ uB₂ uC₂ * embedAC V) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [singleQubitLayer_mul]
              rw [embedAC_merge]
              rw [show singleQubitLayer (u_pA * I₂) (u_pB * uB₁) (u_pC * I₂) *
                        (singleQubitLayer I₂ uB₂ I₂ *
                          embedAC (V₁ * (kron2 uA₁ uC₁ * V₂) *
                                    (kron2 uA₂ uC₂ * V))) *
                        singleQubitLayer uA' uB' uC' =
                    (singleQubitLayer (u_pA * I₂) (u_pB * uB₁) (u_pC * I₂) *
                       singleQubitLayer I₂ uB₂ I₂) *
                      embedAC (V₁ * (kron2 uA₁ uC₁ * V₂) *
                                (kron2 uA₂ uC₂ * V)) *
                      singleQubitLayer uA' uB' uC' from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4
                (V₁ * (kron2 uA₁ uC₁ * V₂) * (kron2 uA₂ uC₂ * V)) :=
              isUnitary4_mul
                (isUnitary4_mul hV₁
                  (isUnitary4_mul (isUnitary4_kron2 hA₁ hC₁) hV₂))
                (isUnitary4_mul (isUnitary4_kron2 hA₂ hC₂) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleAC_canonical
                (V₁ * (kron2 uA₁ uC₁ * V₂) * (kron2 uA₂ uC₂ * V))
                hV_merged
                u_pA ((u_pB * uB₁) * uB₂) u_pC h_pA
                (isUnitary2_mul (isUnitary2_mul h_pB hB₁) hB₂) h_pC
                uA' uB' uC' hA' hB' hC'
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
  | compose_AB V hV uA uB uC hA hB hC h3 =>
    -- Position-4 AB outer.
    cases h3 with
    | weaken h2 =>
      cases h2 with
      | weaken h1 =>
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁, V₂, V₃, V₄', hV₁, hV₂, hV₃, hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleAB_canonical V hV
                u_pA u_pB u_pC h_pA h_pB h_pC uA uB uC hA hB hC
            refine ⟨V₁, V₂, V₃, V₄', hV₁, hV₂, hV₃, hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,1) AB-AB consecutive same-XY merge. Pattern #8.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge :
              singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                singleQubitLayer uA₁ uB₁ uC₁ * embedAB V *
                singleQubitLayer uA uB uC =
              singleQubitLayer u_pA u_pB (u_pC * uC₁) *
                embedAB (V₁ * (kron2 uA₁ uB₁ * V)) *
                singleQubitLayer uA uB uC := by
              rw [show singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                        singleQubitLayer uA₁ uB₁ uC₁ * embedAB V *
                        singleQubitLayer uA uB uC =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAB V₁ * singleQubitLayer uA₁ uB₁ uC₁ * embedAB V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedAB_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                        (singleQubitLayer I₂ I₂ uC₁ *
                          embedAB (V₁ * (kron2 uA₁ uB₁ * V))) *
                        singleQubitLayer uA uB uC =
                    (singleQubitLayer u_pA u_pB u_pC *
                       singleQubitLayer I₂ I₂ uC₁) *
                      embedAB (V₁ * (kron2 uA₁ uB₁ * V)) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₁ * (kron2 uA₁ uB₁ * V)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hB₁) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleAB_canonical (V₁ * (kron2 uA₁ uB₁ * V))
                hV_merged
                u_pA u_pB (u_pC * uC₁) h_pA h_pB (isUnitary2_mul h_pC hC₁)
                uA uB uC hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,1) outer AB inner BC. Pattern #5 (BC-AB-BC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AB_at_3_2_canonical V₁ V hV₁ hV
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA uB uC
                h_pA h_pB h_pC hA₁ hB₁ hC₁ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; left
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,1) outer AB inner AC. Pattern #4 (AC-AB-AC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_AB_at_3_2_canonical V₁ V hV₁ hV
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA uB uC
                h_pA h_pB h_pC hA₁ hB₁ hC₁ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; left
            exact h_eq
      | compose_AB V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,2) AB-AB consecutive same-XY merge. Pattern #8.
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge :
              singleQubitLayer u_pA u_pB u_pC * embedAB V₂ *
                singleQubitLayer uA₂ uB₂ uC₂ * embedAB V *
                singleQubitLayer uA uB uC =
              singleQubitLayer u_pA u_pB (u_pC * uC₂) *
                embedAB (V₂ * (kron2 uA₂ uB₂ * V)) *
                singleQubitLayer uA uB uC := by
              rw [show singleQubitLayer u_pA u_pB u_pC * embedAB V₂ *
                        singleQubitLayer uA₂ uB₂ uC₂ * embedAB V *
                        singleQubitLayer uA uB uC =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAB V₂ * singleQubitLayer uA₂ uB₂ uC₂ * embedAB V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedAB_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                        (singleQubitLayer I₂ I₂ uC₂ *
                          embedAB (V₂ * (kron2 uA₂ uB₂ * V))) *
                        singleQubitLayer uA uB uC =
                    (singleQubitLayer u_pA u_pB u_pC *
                       singleQubitLayer I₂ I₂ uC₂) *
                      embedAB (V₂ * (kron2 uA₂ uB₂ * V)) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₂ * (kron2 uA₂ uB₂ * V)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hA₂ hB₂) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleAB_canonical (V₂ * (kron2 uA₂ uB₂ * V))
                hV_merged
                u_pA u_pB (u_pC * uC₂) h_pA h_pB (isUnitary2_mul h_pC hC₂)
                uA uB uC hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,2,1) AB-AB-AB triple same-XY merge. Pattern #8.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have hV_merged : IsUnitary4
                (V₁ * (kron2 uA₁ uB₁ * V₂) * (kron2 uA₂ uB₂ * V)) :=
              isUnitary4_mul
                (isUnitary4_mul hV₁
                  (isUnitary4_mul (isUnitary4_kron2 hA₁ hB₁) hV₂))
                (isUnitary4_mul (isUnitary4_kron2 hA₂ hB₂) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleAB_canonical
                (V₁ * (kron2 uA₁ uB₁ * V₂) * (kron2 uA₂ uB₂ * V))
                hV_merged
                u_pA u_pB ((u_pC * uC₁) * uC₂) h_pA h_pB
                (isUnitary2_mul (isUnitary2_mul h_pC hC₁) hC₂)
                uA uB uC hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            rw [sandwich_AB_AB_AB_to_AB V₁ V₂ V
                  u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA uB uC]
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,2,1) BC-AB-AB outer-pair-AB-merge: V₂ and V outer both AB.
          -- Pattern #5 (BC-AB-BC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := outer_AB_pair_merge_sandwich (embedBC V₁) V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA uB uC
            have hV_merged : IsUnitary4 (V₂ * (kron2 uA₂ uB₂ * V)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hA₂ hB₂) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AB_at_3_2_canonical V₁
                (V₂ * (kron2 uA₂ uB₂ * V)) hV₁ hV_merged
                u_pA u_pB u_pC uA₁ uB₁ (uC₁ * uC₂) uA uB uC
                h_pA h_pB h_pC hA₁ hB₁ (isUnitary2_mul hC₁ hC₂) hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,2,1) AC-AB-AB outer-pair-AB-merge: V₂ and V outer both AB.
          -- Pattern #4 (AC-AB-AC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := outer_AB_pair_merge_sandwich (embedAC V₁) V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA uB uC
            have hV_merged : IsUnitary4 (V₂ * (kron2 uA₂ uB₂ * V)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hA₂ hB₂) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_AB_at_3_2_canonical V₁
                (V₂ * (kron2 uA₂ uB₂ * V)) hV₁ hV_merged
                u_pA u_pB u_pC uA₁ uB₁ (uC₁ * uC₂) uA uB uC
                h_pA h_pB h_pC hA₁ hB₁ (isUnitary2_mul hC₁ hC₂) hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; left
            rw [h_merge]
            exact h_eq
      | compose_BC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,2) outer AB inner BC. Pattern #5 (BC-AB-BC-AB).
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AB_at_3_2_canonical V₂ V hV₂ hV
                u_pA u_pB u_pC uA₂ uB₂ uC₂ uA uB uC
                h_pA h_pB h_pC hA₂ hB₂ hC₂ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; left
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,2,1) AB-BC-AB non-adjacent-same: V₁ and V outer both AB.
          -- Pattern #8 (AB-BC-AB-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AB_BC_AB_to_4embed V₁ V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV₁)
                (isUnitary4_kron2 hA₁ hB₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul h_pC hC₁)) hV₂)
                (isUnitary4_kron2 hB₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₂ isUnitary2_one) hV)
                (isUnitary4_kron2 hA hB),
              isUnitary4_kron2 isUnitary2_one hC, ?_⟩
            right; right; right; right; right; right; right; left
            exact h_chain
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,2,1) BC-BC-AB inner-pair-merge: V₁ and V₂ both BC.
          -- Pattern #5 (BC-AB-BC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := inner_BC_pair_merge_sandwich V₁ V₂ (embedAB V)
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA uB uC
            have hV_merged : IsUnitary4 (V₁ * (kron2 uB₁ uC₁ * V₂)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hB₁ hC₁) hV₂)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AB_at_3_2_canonical
                (V₁ * (kron2 uB₁ uC₁ * V₂)) V hV_merged hV
                (u_pA * uA₁) u_pB u_pC uA₂ uB₂ uC₂ uA uB uC
                (isUnitary2_mul h_pA hA₁) h_pB h_pC hA₂ hB₂ hC₂ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,2,1) AC-BC-AB all-different: V₁=AC, V₂=BC, V outer=AB.
          -- Pattern #3 (AC-BC-AB-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AC_BC_AB_to_4embed V₁ V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV₁)
                (isUnitary4_kron2 hA₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pB hB₁) isUnitary2_one) hV₂)
                (isUnitary4_kron2 hB₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₂ isUnitary2_one) hV)
                (isUnitary4_kron2 hA hB),
              isUnitary4_kron2 isUnitary2_one hC, ?_⟩
            right; right; left
            exact h_chain
      | compose_AC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,2) outer AB inner AC. Pattern #4 (AC-AB-AC-AB).
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_AB_at_3_2_canonical V₂ V hV₂ hV
                u_pA u_pB u_pC uA₂ uB₂ uC₂ uA uB uC
                h_pA h_pB h_pC hA₂ hB₂ hC₂ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; left
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,2,1) AB-AC-AB non-adjacent-same: V₁ and V outer both AB.
          -- Pattern #7 (AB-AC-AB-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AB_AC_AB_to_4embed V₁ V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV₁)
                (isUnitary4_kron2 hA₁ hB₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul h_pC hC₁)) hV₂)
                (isUnitary4_kron2 hA₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hB₂) hV)
                (isUnitary4_kron2 hA hB),
              isUnitary4_kron2 isUnitary2_one hC, ?_⟩
            right; right; right; right; right; right; left
            exact h_chain
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,2,1) BC-AC-AB all-different: V₁=BC, V₂=AC, V outer=AB.
          -- Pattern #1 (BC-AC-AB-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_BC_AC_AB_to_4embed V₁ V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV₁)
                (isUnitary4_kron2 hB₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pA hA₁) isUnitary2_one) hV₂)
                (isUnitary4_kron2 hA₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hB₂) hV)
                (isUnitary4_kron2 hA hB),
              isUnitary4_kron2 isUnitary2_one hC, ?_⟩
            left
            exact h_chain
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,2,1) AC-AC-AB inner-pair-merge: V₁ and V₂ both AC.
          -- Pattern #4 (AC-AB-AC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := inner_AC_pair_merge_sandwich V₁ V₂ (embedAB V)
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA uB uC
            have hV_merged : IsUnitary4 (V₁ * (kron2 uA₁ uC₁ * V₂)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hC₁) hV₂)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_AB_at_3_2_canonical
                (V₁ * (kron2 uA₁ uC₁ * V₂)) V hV_merged hV
                u_pA (u_pB * uB₁) u_pC uA₂ uB₂ uC₂ uA uB uC
                h_pA (isUnitary2_mul h_pB hB₁) h_pC hA₂ hB₂ hC₂ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; left
            rw [h_merge]
            exact h_eq
    | compose_AB V₃ hV₃ uA₃ uB₃ uC₃ hA₃ hB₃ hC₃ h2 =>
      -- (4,3) AB-AB consecutive same-XY merge. Pattern #8.
      cases h2 with
      | weaken h1 =>
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge :
              singleQubitLayer u_pA u_pB u_pC * embedAB V₃ *
                singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                singleQubitLayer uA uB uC =
              singleQubitLayer u_pA u_pB (u_pC * uC₃) *
                embedAB (V₃ * (kron2 uA₃ uB₃ * V)) *
                singleQubitLayer uA uB uC := by
              rw [show singleQubitLayer u_pA u_pB u_pC * embedAB V₃ *
                        singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                        singleQubitLayer uA uB uC =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAB V₃ * singleQubitLayer uA₃ uB₃ uC₃ * embedAB V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedAB_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                        (singleQubitLayer I₂ I₂ uC₃ *
                          embedAB (V₃ * (kron2 uA₃ uB₃ * V))) *
                        singleQubitLayer uA uB uC =
                    (singleQubitLayer u_pA u_pB u_pC *
                       singleQubitLayer I₂ I₂ uC₃) *
                      embedAB (V₃ * (kron2 uA₃ uB₃ * V)) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₃ * (kron2 uA₃ uB₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hA₃ hB₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleAB_canonical (V₃ * (kron2 uA₃ uB₃ * V))
                hV_merged
                u_pA u_pB (u_pC * uC₃) h_pA h_pB (isUnitary2_mul h_pC hC₃)
                uA uB uC hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,1) AB-AB-AB triple same-XY merge. Pattern #8.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have hV_merged : IsUnitary4
                (V₁ * (kron2 uA₁ uB₁ * V₃) * (kron2 uA₃ uB₃ * V)) :=
              isUnitary4_mul
                (isUnitary4_mul hV₁
                  (isUnitary4_mul (isUnitary4_kron2 hA₁ hB₁) hV₃))
                (isUnitary4_mul (isUnitary4_kron2 hA₃ hB₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleAB_canonical
                (V₁ * (kron2 uA₁ uB₁ * V₃) * (kron2 uA₃ uB₃ * V))
                hV_merged
                u_pA u_pB ((u_pC * uC₁) * uC₃) h_pA h_pB
                (isUnitary2_mul (isUnitary2_mul h_pC hC₁) hC₃)
                uA uB uC hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            rw [sandwich_AB_AB_AB_to_AB V₁ V₃ V
                  u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC]
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,1) BC-AB-AB adjacent-same: V₃ and V outer merge (both AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := outer_AB_pair_merge_sandwich (embedBC V₁) V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            have hV_merged : IsUnitary4 (V₃ * (kron2 uA₃ uB₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hA₃ hB₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AB_at_3_2_canonical V₁
                (V₃ * (kron2 uA₃ uB₃ * V)) hV₁ hV_merged
                u_pA u_pB u_pC uA₁ uB₁ (uC₁ * uC₃) uA uB uC
                h_pA h_pB h_pC hA₁ hB₁ (isUnitary2_mul hC₁ hC₃) hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,1) AC-AB-AB adjacent-same: V₃ and V outer merge (both AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := outer_AB_pair_merge_sandwich (embedAC V₁) V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            have hV_merged : IsUnitary4 (V₃ * (kron2 uA₃ uB₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hA₃ hB₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_AB_at_3_2_canonical V₁
                (V₃ * (kron2 uA₃ uB₃ * V)) hV₁ hV_merged
                u_pA u_pB u_pC uA₁ uB₁ (uC₁ * uC₃) uA uB uC
                h_pA h_pB h_pC hA₁ hB₁ (isUnitary2_mul hC₁ hC₃) hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; left
            rw [h_merge]
            exact h_eq
      | compose_AB V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,3,2) AB-AB-AB triple same-XY merge. Pattern #8.
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have hV_merged : IsUnitary4
                (V₂ * (kron2 uA₂ uB₂ * V₃) * (kron2 uA₃ uB₃ * V)) :=
              isUnitary4_mul
                (isUnitary4_mul hV₂
                  (isUnitary4_mul (isUnitary4_kron2 hA₂ hB₂) hV₃))
                (isUnitary4_mul (isUnitary4_kron2 hA₃ hB₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleAB_canonical
                (V₂ * (kron2 uA₂ uB₂ * V₃) * (kron2 uA₃ uB₃ * V))
                hV_merged
                u_pA u_pB ((u_pC * uC₂) * uC₃) h_pA h_pB
                (isUnitary2_mul (isUnitary2_mul h_pC hC₂) hC₃)
                uA uB uC hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            rw [sandwich_AB_AB_AB_to_AB V₂ V₃ V
                  u_pA u_pB u_pC uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC]
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AB-AB-AB-AB: all 4 gates AB, full 4-way merge.
          -- Pattern #8 (AB-BC-AB-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have hV_merged : IsUnitary4
                (V₁ * (kron2 uA₁ uB₁ * V₂) * (kron2 uA₂ uB₂ * V₃) *
                  (kron2 uA₃ uB₃ * V)) :=
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul hV₁
                    (isUnitary4_mul (isUnitary4_kron2 hA₁ hB₁) hV₂))
                  (isUnitary4_mul (isUnitary4_kron2 hA₂ hB₂) hV₃))
                (isUnitary4_mul (isUnitary4_kron2 hA₃ hB₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleAB_canonical
                (V₁ * (kron2 uA₁ uB₁ * V₂) * (kron2 uA₂ uB₂ * V₃) *
                  (kron2 uA₃ uB₃ * V))
                hV_merged
                u_pA u_pB (((u_pC * uC₁) * uC₂) * uC₃) h_pA h_pB
                (isUnitary2_mul
                  (isUnitary2_mul (isUnitary2_mul h_pC hC₁) hC₂) hC₃)
                uA uB uC hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            rw [sandwich_AB_AB_AB_AB_to_AB V₁ V₂ V₃ V
                  u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃
                  uA uB uC]
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) BC-AB-AB-AB: V₁=BC, V₂=V₃=V=AB. Merge outer 3 ABs.
          -- Pattern #5 (BC-AB-BC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge_inner :
                singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                  singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                  singleQubitLayer uA uB uC =
                singleQubitLayer uA₁ uB₁ ((uC₁ * uC₂) * uC₃) *
                  embedAB (V₂ * (kron2 uA₂ uB₂ * V₃) *
                    (kron2 uA₃ uB₃ * V)) *
                  singleQubitLayer uA uB uC :=
              sandwich_AB_AB_AB_to_AB V₂ V₃ V
                uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    (singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                      singleQubitLayer uA uB uC) from by noncomm_ring]
            rw [h_merge_inner]
            have hV_merged : IsUnitary4
                (V₂ * (kron2 uA₂ uB₂ * V₃) * (kron2 uA₃ uB₃ * V)) :=
              isUnitary4_mul
                (isUnitary4_mul hV₂
                  (isUnitary4_mul (isUnitary4_kron2 hA₂ hB₂) hV₃))
                (isUnitary4_mul (isUnitary4_kron2 hA₃ hB₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AB_at_3_2_canonical V₁
                (V₂ * (kron2 uA₂ uB₂ * V₃) * (kron2 uA₃ uB₃ * V))
                hV₁ hV_merged
                u_pA u_pB u_pC uA₁ uB₁ ((uC₁ * uC₂) * uC₃) uA uB uC
                h_pA h_pB h_pC hA₁ hB₁
                (isUnitary2_mul (isUnitary2_mul hC₁ hC₂) hC₃) hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; left
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    (singleQubitLayer uA₁ uB₁ ((uC₁ * uC₂) * uC₃) *
                      embedAB (V₂ * (kron2 uA₂ uB₂ * V₃) *
                        (kron2 uA₃ uB₃ * V)) *
                      singleQubitLayer uA uB uC) =
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ ((uC₁ * uC₂) * uC₃) *
                    embedAB (V₂ * (kron2 uA₂ uB₂ * V₃) *
                      (kron2 uA₃ uB₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AC-AB-AB-AB: V₁=AC, V₂=V₃=V=AB. Merge outer 3 ABs.
          -- Pattern #4 (AC-AB-AC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge_inner :
                singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                  singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                  singleQubitLayer uA uB uC =
                singleQubitLayer uA₁ uB₁ ((uC₁ * uC₂) * uC₃) *
                  embedAB (V₂ * (kron2 uA₂ uB₂ * V₃) *
                    (kron2 uA₃ uB₃ * V)) *
                  singleQubitLayer uA uB uC :=
              sandwich_AB_AB_AB_to_AB V₂ V₃ V
                uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    (singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                      singleQubitLayer uA uB uC) from by noncomm_ring]
            rw [h_merge_inner]
            have hV_merged : IsUnitary4
                (V₂ * (kron2 uA₂ uB₂ * V₃) * (kron2 uA₃ uB₃ * V)) :=
              isUnitary4_mul
                (isUnitary4_mul hV₂
                  (isUnitary4_mul (isUnitary4_kron2 hA₂ hB₂) hV₃))
                (isUnitary4_mul (isUnitary4_kron2 hA₃ hB₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_AB_at_3_2_canonical V₁
                (V₂ * (kron2 uA₂ uB₂ * V₃) * (kron2 uA₃ uB₃ * V))
                hV₁ hV_merged
                u_pA u_pB u_pC uA₁ uB₁ ((uC₁ * uC₂) * uC₃) uA uB uC
                h_pA h_pB h_pC hA₁ hB₁
                (isUnitary2_mul (isUnitary2_mul hC₁ hC₂) hC₃) hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; left
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    (singleQubitLayer uA₁ uB₁ ((uC₁ * uC₂) * uC₃) *
                      embedAB (V₂ * (kron2 uA₂ uB₂ * V₃) *
                        (kron2 uA₃ uB₃ * V)) *
                      singleQubitLayer uA uB uC) =
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ ((uC₁ * uC₂) * uC₃) *
                    embedAB (V₂ * (kron2 uA₂ uB₂ * V₃) *
                      (kron2 uA₃ uB₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_eq
      | compose_BC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,3,2) BC-AB-AB adjacent-same: V₃ and V outer merge (both AB).
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := outer_AB_pair_merge_sandwich (embedBC V₂) V₃ V
              u_pA u_pB u_pC uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            have hV_merged : IsUnitary4 (V₃ * (kron2 uA₃ uB₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hA₃ hB₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AB_at_3_2_canonical V₂
                (V₃ * (kron2 uA₃ uB₃ * V)) hV₂ hV_merged
                u_pA u_pB u_pC uA₂ uB₂ (uC₂ * uC₃) uA uB uC
                h_pA h_pB h_pC hA₂ hB₂ (isUnitary2_mul hC₂ hC₃) hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AB-BC-AB-AB: V₁=AB, V₂=BC, V₃=V=AB. Merge outer
          -- pair V₃,V (both AB), reduce to (3,2,1) AB-BC-AB chain.
          -- Pattern #8 (AB-BC-AB-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_outer_merge :
                singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                  singleQubitLayer uA uB uC =
                singleQubitLayer uA₂ uB₂ (uC₂ * uC₃) *
                  embedAB (V₃ * (kron2 uA₃ uB₃ * V)) *
                  singleQubitLayer uA uB uC := by
              rw [show
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                      singleQubitLayer uA uB uC =
                    singleQubitLayer uA₂ uB₂ uC₂ *
                      (embedAB V₃ * singleQubitLayer uA₃ uB₃ uC₃ *
                        embedAB V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedAB_merge]
              rw [show singleQubitLayer uA₂ uB₂ uC₂ *
                    (singleQubitLayer I₂ I₂ uC₃ *
                      embedAB (V₃ * (kron2 uA₃ uB₃ * V))) *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer uA₂ uB₂ uC₂ *
                     singleQubitLayer I₂ I₂ uC₃) *
                    embedAB (V₃ * (kron2 uA₃ uB₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    (singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                      singleQubitLayer uA uB uC) from by noncomm_ring]
            rw [h_outer_merge]
            -- Now: (3,2,1) AB-BC-AB chain with merged AB.
            have h_chain := sandwich_AB_BC_AB_to_4embed V₁ V₂
              (V₃ * (kron2 uA₃ uB₃ * V))
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ (uC₂ * uC₃) uA uB uC
            have hV_merge : IsUnitary4 (V₃ * (kron2 uA₃ uB₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hA₃ hB₃) hV)
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV₁)
                (isUnitary4_kron2 hA₁ hB₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul h_pC hC₁)) hV₂)
                (isUnitary4_kron2 hB₂ (isUnitary2_mul hC₂ hC₃)),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₂ isUnitary2_one) hV_merge)
                (isUnitary4_kron2 hA hB),
              isUnitary4_kron2 isUnitary2_one hC, ?_⟩
            right; right; right; right; right; right; right; left
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    (singleQubitLayer uA₂ uB₂ (uC₂ * uC₃) *
                      embedAB (V₃ * (kron2 uA₃ uB₃ * V)) *
                      singleQubitLayer uA uB uC) =
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    singleQubitLayer uA₂ uB₂ (uC₂ * uC₃) *
                    embedAB (V₃ * (kron2 uA₃ uB₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_chain
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) BC-BC-AB-AB: V₁=V₂=BC inner pair, V₃=V=AB outer pair.
          -- Pattern F (both-pair-merge): merge both pairs, reduce to (3,1) BC-AB.
          -- Pattern #5 (BC-AB-BC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_outer_merge :
                singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                  singleQubitLayer uA uB uC =
                singleQubitLayer uA₂ uB₂ (uC₂ * uC₃) *
                  embedAB (V₃ * (kron2 uA₃ uB₃ * V)) *
                  singleQubitLayer uA uB uC := by
              rw [show
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                      singleQubitLayer uA uB uC =
                    singleQubitLayer uA₂ uB₂ uC₂ *
                      (embedAB V₃ * singleQubitLayer uA₃ uB₃ uC₃ *
                        embedAB V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedAB_merge]
              rw [show singleQubitLayer uA₂ uB₂ uC₂ *
                    (singleQubitLayer I₂ I₂ uC₃ *
                      embedAB (V₃ * (kron2 uA₃ uB₃ * V))) *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer uA₂ uB₂ uC₂ *
                     singleQubitLayer I₂ I₂ uC₃) *
                    embedAB (V₃ * (kron2 uA₃ uB₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have h_inner_merge :
                singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                  singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ =
                singleQubitLayer (u_pA * uA₁) u_pB u_pC *
                  embedBC (V₁ * (kron2 uB₁ uC₁ * V₂)) := by
              rw [show
                    singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                      singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedBC V₁ * singleQubitLayer uA₁ uB₁ uC₁ *
                        embedBC V₂) from by noncomm_ring]
              rw [embedBC_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                    (singleQubitLayer uA₁ I₂ I₂ *
                      embedBC (V₁ * (kron2 uB₁ uC₁ * V₂))) =
                  (singleQubitLayer u_pA u_pB u_pC *
                     singleQubitLayer uA₁ I₂ I₂) *
                    embedBC (V₁ * (kron2 uB₁ uC₁ * V₂))
                  from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂) *
                    (singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                      singleQubitLayer uA uB uC) from by noncomm_ring]
            rw [h_inner_merge, h_outer_merge]
            have hV_inner : IsUnitary4 (V₁ * (kron2 uB₁ uC₁ * V₂)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hB₁ hC₁) hV₂)
            have hV_outer : IsUnitary4 (V₃ * (kron2 uA₃ uB₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hA₃ hB₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AB_at_3_2_canonical
                (V₁ * (kron2 uB₁ uC₁ * V₂))
                (V₃ * (kron2 uA₃ uB₃ * V))
                hV_inner hV_outer
                (u_pA * uA₁) u_pB u_pC uA₂ uB₂ (uC₂ * uC₃) uA uB uC
                (isUnitary2_mul h_pA hA₁) h_pB h_pC hA₂ hB₂
                (isUnitary2_mul hC₂ hC₃) hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; left
            rw [show
                  singleQubitLayer (u_pA * uA₁) u_pB u_pC *
                    embedBC (V₁ * (kron2 uB₁ uC₁ * V₂)) *
                    (singleQubitLayer uA₂ uB₂ (uC₂ * uC₃) *
                      embedAB (V₃ * (kron2 uA₃ uB₃ * V)) *
                      singleQubitLayer uA uB uC) =
                  singleQubitLayer (u_pA * uA₁) u_pB u_pC *
                    embedBC (V₁ * (kron2 uB₁ uC₁ * V₂)) *
                    singleQubitLayer uA₂ uB₂ (uC₂ * uC₃) *
                    embedAB (V₃ * (kron2 uA₃ uB₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AC-BC-AB-AB: V₁=AC, V₂=BC, V₃=V=AB. Merge outer pair.
          -- Pattern #3 (AC-BC-AB-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_outer_merge :
                singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                  singleQubitLayer uA uB uC =
                singleQubitLayer uA₂ uB₂ (uC₂ * uC₃) *
                  embedAB (V₃ * (kron2 uA₃ uB₃ * V)) *
                  singleQubitLayer uA uB uC := by
              rw [show
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                      singleQubitLayer uA uB uC =
                    singleQubitLayer uA₂ uB₂ uC₂ *
                      (embedAB V₃ * singleQubitLayer uA₃ uB₃ uC₃ *
                        embedAB V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedAB_merge]
              rw [show singleQubitLayer uA₂ uB₂ uC₂ *
                    (singleQubitLayer I₂ I₂ uC₃ *
                      embedAB (V₃ * (kron2 uA₃ uB₃ * V))) *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer uA₂ uB₂ uC₂ *
                     singleQubitLayer I₂ I₂ uC₃) *
                    embedAB (V₃ * (kron2 uA₃ uB₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    (singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                      singleQubitLayer uA uB uC) from by noncomm_ring]
            rw [h_outer_merge]
            have h_chain := sandwich_AC_BC_AB_to_4embed V₁ V₂
              (V₃ * (kron2 uA₃ uB₃ * V))
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ (uC₂ * uC₃) uA uB uC
            have hV_merge : IsUnitary4 (V₃ * (kron2 uA₃ uB₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hA₃ hB₃) hV)
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV₁)
                (isUnitary4_kron2 hA₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pB hB₁) isUnitary2_one) hV₂)
                (isUnitary4_kron2 hB₂ (isUnitary2_mul hC₂ hC₃)),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₂ isUnitary2_one) hV_merge)
                (isUnitary4_kron2 hA hB),
              isUnitary4_kron2 isUnitary2_one hC, ?_⟩
            right; right; left
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    (singleQubitLayer uA₂ uB₂ (uC₂ * uC₃) *
                      embedAB (V₃ * (kron2 uA₃ uB₃ * V)) *
                      singleQubitLayer uA uB uC) =
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    singleQubitLayer uA₂ uB₂ (uC₂ * uC₃) *
                    embedAB (V₃ * (kron2 uA₃ uB₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_chain
      | compose_AC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,3,2) AC-AB-AB adjacent-same: V₃ and V outer merge (both AB).
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := outer_AB_pair_merge_sandwich (embedAC V₂) V₃ V
              u_pA u_pB u_pC uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            have hV_merged : IsUnitary4 (V₃ * (kron2 uA₃ uB₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hA₃ hB₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_AB_at_3_2_canonical V₂
                (V₃ * (kron2 uA₃ uB₃ * V)) hV₂ hV_merged
                u_pA u_pB u_pC uA₂ uB₂ (uC₂ * uC₃) uA uB uC
                h_pA h_pB h_pC hA₂ hB₂ (isUnitary2_mul hC₂ hC₃) hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AB-AC-AB-AB: V₁=AB, V₂=AC, V₃=V=AB. Merge outer pair.
          -- Pattern #7 (AB-AC-AB-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_outer_merge :
                singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                  singleQubitLayer uA uB uC =
                singleQubitLayer uA₂ uB₂ (uC₂ * uC₃) *
                  embedAB (V₃ * (kron2 uA₃ uB₃ * V)) *
                  singleQubitLayer uA uB uC := by
              rw [show
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                      singleQubitLayer uA uB uC =
                    singleQubitLayer uA₂ uB₂ uC₂ *
                      (embedAB V₃ * singleQubitLayer uA₃ uB₃ uC₃ *
                        embedAB V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedAB_merge]
              rw [show singleQubitLayer uA₂ uB₂ uC₂ *
                    (singleQubitLayer I₂ I₂ uC₃ *
                      embedAB (V₃ * (kron2 uA₃ uB₃ * V))) *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer uA₂ uB₂ uC₂ *
                     singleQubitLayer I₂ I₂ uC₃) *
                    embedAB (V₃ * (kron2 uA₃ uB₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                    (singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                      singleQubitLayer uA uB uC) from by noncomm_ring]
            rw [h_outer_merge]
            have h_chain := sandwich_AB_AC_AB_to_4embed V₁ V₂
              (V₃ * (kron2 uA₃ uB₃ * V))
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ (uC₂ * uC₃) uA uB uC
            have hV_merge : IsUnitary4 (V₃ * (kron2 uA₃ uB₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hA₃ hB₃) hV)
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV₁)
                (isUnitary4_kron2 hA₁ hB₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul h_pC hC₁)) hV₂)
                (isUnitary4_kron2 hA₂ (isUnitary2_mul hC₂ hC₃)),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hB₂) hV_merge)
                (isUnitary4_kron2 hA hB),
              isUnitary4_kron2 isUnitary2_one hC, ?_⟩
            right; right; right; right; right; right; left
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                    (singleQubitLayer uA₂ uB₂ (uC₂ * uC₃) *
                      embedAB (V₃ * (kron2 uA₃ uB₃ * V)) *
                      singleQubitLayer uA uB uC) =
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                    singleQubitLayer uA₂ uB₂ (uC₂ * uC₃) *
                    embedAB (V₃ * (kron2 uA₃ uB₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_chain
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) BC-AC-AB-AB: V₁=BC, V₂=AC, V₃=V=AB. Merge outer pair.
          -- Pattern #1 (BC-AC-AB-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_outer_merge :
                singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                  singleQubitLayer uA uB uC =
                singleQubitLayer uA₂ uB₂ (uC₂ * uC₃) *
                  embedAB (V₃ * (kron2 uA₃ uB₃ * V)) *
                  singleQubitLayer uA uB uC := by
              rw [show
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                      singleQubitLayer uA uB uC =
                    singleQubitLayer uA₂ uB₂ uC₂ *
                      (embedAB V₃ * singleQubitLayer uA₃ uB₃ uC₃ *
                        embedAB V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedAB_merge]
              rw [show singleQubitLayer uA₂ uB₂ uC₂ *
                    (singleQubitLayer I₂ I₂ uC₃ *
                      embedAB (V₃ * (kron2 uA₃ uB₃ * V))) *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer uA₂ uB₂ uC₂ *
                     singleQubitLayer I₂ I₂ uC₃) *
                    embedAB (V₃ * (kron2 uA₃ uB₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                    (singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                      singleQubitLayer uA uB uC) from by noncomm_ring]
            rw [h_outer_merge]
            have h_chain := sandwich_BC_AC_AB_to_4embed V₁ V₂
              (V₃ * (kron2 uA₃ uB₃ * V))
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ (uC₂ * uC₃) uA uB uC
            have hV_merge : IsUnitary4 (V₃ * (kron2 uA₃ uB₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hA₃ hB₃) hV)
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV₁)
                (isUnitary4_kron2 hB₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pA hA₁) isUnitary2_one) hV₂)
                (isUnitary4_kron2 hA₂ (isUnitary2_mul hC₂ hC₃)),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hB₂) hV_merge)
                (isUnitary4_kron2 hA hB),
              isUnitary4_kron2 isUnitary2_one hC, ?_⟩
            left
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                    (singleQubitLayer uA₂ uB₂ (uC₂ * uC₃) *
                      embedAB (V₃ * (kron2 uA₃ uB₃ * V)) *
                      singleQubitLayer uA uB uC) =
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                    singleQubitLayer uA₂ uB₂ (uC₂ * uC₃) *
                    embedAB (V₃ * (kron2 uA₃ uB₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_chain
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AC-AC-AB-AB: V₁=V₂=AC inner pair, V₃=V=AB outer pair.
          -- Pattern F (both-pair-merge): merge both pairs, reduce to (3,1) AC-AB.
          -- Pattern #4 (AC-AB-AC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_outer_merge :
                singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                  singleQubitLayer uA uB uC =
                singleQubitLayer uA₂ uB₂ (uC₂ * uC₃) *
                  embedAB (V₃ * (kron2 uA₃ uB₃ * V)) *
                  singleQubitLayer uA uB uC := by
              rw [show
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                      singleQubitLayer uA uB uC =
                    singleQubitLayer uA₂ uB₂ uC₂ *
                      (embedAB V₃ * singleQubitLayer uA₃ uB₃ uC₃ *
                        embedAB V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedAB_merge]
              rw [show singleQubitLayer uA₂ uB₂ uC₂ *
                    (singleQubitLayer I₂ I₂ uC₃ *
                      embedAB (V₃ * (kron2 uA₃ uB₃ * V))) *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer uA₂ uB₂ uC₂ *
                     singleQubitLayer I₂ I₂ uC₃) *
                    embedAB (V₃ * (kron2 uA₃ uB₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have h_inner_merge :
                singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                  singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ =
                singleQubitLayer u_pA (u_pB * uB₁) u_pC *
                  embedAC (V₁ * (kron2 uA₁ uC₁ * V₂)) := by
              rw [show
                    singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                      singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAC V₁ * singleQubitLayer uA₁ uB₁ uC₁ *
                        embedAC V₂) from by noncomm_ring]
              rw [embedAC_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                    (singleQubitLayer I₂ uB₁ I₂ *
                      embedAC (V₁ * (kron2 uA₁ uC₁ * V₂))) =
                  (singleQubitLayer u_pA u_pB u_pC *
                     singleQubitLayer I₂ uB₁ I₂) *
                    embedAC (V₁ * (kron2 uA₁ uC₁ * V₂))
                  from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂) *
                    (singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                      singleQubitLayer uA uB uC) from by noncomm_ring]
            rw [h_inner_merge, h_outer_merge]
            have hV_inner : IsUnitary4 (V₁ * (kron2 uA₁ uC₁ * V₂)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hC₁) hV₂)
            have hV_outer : IsUnitary4 (V₃ * (kron2 uA₃ uB₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hA₃ hB₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_AB_at_3_2_canonical
                (V₁ * (kron2 uA₁ uC₁ * V₂))
                (V₃ * (kron2 uA₃ uB₃ * V))
                hV_inner hV_outer
                u_pA (u_pB * uB₁) u_pC uA₂ uB₂ (uC₂ * uC₃) uA uB uC
                h_pA (isUnitary2_mul h_pB hB₁) h_pC hA₂ hB₂
                (isUnitary2_mul hC₂ hC₃) hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; left
            rw [show
                  singleQubitLayer u_pA (u_pB * uB₁) u_pC *
                    embedAC (V₁ * (kron2 uA₁ uC₁ * V₂)) *
                    (singleQubitLayer uA₂ uB₂ (uC₂ * uC₃) *
                      embedAB (V₃ * (kron2 uA₃ uB₃ * V)) *
                      singleQubitLayer uA uB uC) =
                  singleQubitLayer u_pA (u_pB * uB₁) u_pC *
                    embedAC (V₁ * (kron2 uA₁ uC₁ * V₂)) *
                    singleQubitLayer uA₂ uB₂ (uC₂ * uC₃) *
                    embedAB (V₃ * (kron2 uA₃ uB₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_eq
    | compose_BC V₃ hV₃ uA₃ uB₃ uC₃ hA₃ hB₃ hC₃ h2 =>
      -- (4,3) outer AB inner BC. Pattern #5 (BC-AB-BC-AB).
      cases h2 with
      | weaken h1 =>
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AB_at_3_2_canonical V₃ V hV₃ hV
                u_pA u_pB u_pC uA₃ uB₃ uC₃ uA uB uC
                h_pA h_pB h_pC hA₃ hB₃ hC₃ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; left
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,1) AB-BC-AB non-adjacent-same: V₁ and V outer both AB.
          -- Pattern #8 (AB-BC-AB-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AB_BC_AB_to_4embed V₁ V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV₁)
                (isUnitary4_kron2 hA₁ hB₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul h_pC hC₁)) hV₃)
                (isUnitary4_kron2 hB₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₃ isUnitary2_one) hV)
                (isUnitary4_kron2 hA hB),
              isUnitary4_kron2 isUnitary2_one hC, ?_⟩
            right; right; right; right; right; right; right; left
            exact h_chain
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,1) BC-BC-AB inner-pair-merge: V₁ and V₃ both BC.
          -- Pattern #5 (BC-AB-BC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := inner_BC_pair_merge_sandwich V₁ V₃ (embedAB V)
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            have hV_merged : IsUnitary4 (V₁ * (kron2 uB₁ uC₁ * V₃)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hB₁ hC₁) hV₃)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AB_at_3_2_canonical
                (V₁ * (kron2 uB₁ uC₁ * V₃)) V hV_merged hV
                (u_pA * uA₁) u_pB u_pC uA₃ uB₃ uC₃ uA uB uC
                (isUnitary2_mul h_pA hA₁) h_pB h_pC hA₃ hB₃ hC₃ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,1) AC-BC-AB all-different: V₁=AC, V₃=BC, V outer=AB.
          -- Pattern #3 (AC-BC-AB-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AC_BC_AB_to_4embed V₁ V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV₁)
                (isUnitary4_kron2 hA₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pB hB₁) isUnitary2_one) hV₃)
                (isUnitary4_kron2 hB₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₃ isUnitary2_one) hV)
                (isUnitary4_kron2 hA hB),
              isUnitary4_kron2 isUnitary2_one hC, ?_⟩
            right; right; left
            exact h_chain
      | compose_AB V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,3,2) AB-BC-AB section (V outer=AB, V₃=BC, V₂=AB).
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            -- (4,3,2) AB-BC-AB: 3-real-gate natural chain.
            -- Pattern #8 (AB-BC-AB-BC).
            have h_chain := sandwich_AB_BC_AB_to_4embed V₂ V₃ V
              u_pA u_pB u_pC uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV₂)
                (isUnitary4_kron2 hA₂ hB₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul h_pC hC₂)) hV₃)
                (isUnitary4_kron2 hB₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₃ isUnitary2_one) hV)
                (isUnitary4_kron2 hA hB),
              isUnitary4_kron2 isUnitary2_one hC, ?_⟩
            right; right; right; right; right; right; right; left
            exact h_chain
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AB-AB-BC-AB: V₁=V₂=AB inner pair, V₃=BC, V outer=AB.
          -- Pattern D inner-pair-merge: merge V₁,V₂ then (3,2,1) AB-BC-AB. Pattern #8.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_inner_merge :
                singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                  singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ =
                singleQubitLayer u_pA u_pB (u_pC * uC₁) *
                  embedAB (V₁ * (kron2 uA₁ uB₁ * V₂)) := by
              rw [show
                    singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                      singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAB V₁ * singleQubitLayer uA₁ uB₁ uC₁ *
                        embedAB V₂) from by noncomm_ring]
              rw [embedAB_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                    (singleQubitLayer I₂ I₂ uC₁ *
                      embedAB (V₁ * (kron2 uA₁ uB₁ * V₂))) =
                  (singleQubitLayer u_pA u_pB u_pC *
                     singleQubitLayer I₂ I₂ uC₁) *
                    embedAB (V₁ * (kron2 uA₁ uB₁ * V₂))
                  from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂) *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_inner_merge]
            have h_chain := sandwich_AB_BC_AB_to_4embed
              (V₁ * (kron2 uA₁ uB₁ * V₂)) V₃ V
              u_pA u_pB (u_pC * uC₁) uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            have hV_merge : IsUnitary4 (V₁ * (kron2 uA₁ uB₁ * V₂)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hB₁) hV₂)
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV_merge)
                (isUnitary4_kron2 hA₂ hB₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul (isUnitary2_mul h_pC hC₁) hC₂)) hV₃)
                (isUnitary4_kron2 hB₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₃ isUnitary2_one) hV)
                (isUnitary4_kron2 hA hB),
              isUnitary4_kron2 isUnitary2_one hC, ?_⟩
            right; right; right; right; right; right; right; left
            exact h_chain
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) BC-AB-BC-AB: V₁=BC, V₂=AB, V₃=BC, V outer=AB.
          -- Direct pattern #5 (BC-AB-BC-AB) match. Pattern E.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_BC_AB_BC_AB_to_4embed V₁ V₂ V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV₁)
                (isUnitary4_kron2 hB₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pA hA₁) isUnitary2_one) hV₂)
                (isUnitary4_kron2 hA₂ hB₂),
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₂) hV₃)
                  (isUnitary4_kron2 hB₃ hC₃))
                (isUnitary4_kron2 isUnitary2_one hC),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₃ isUnitary2_one) hV)
                (isUnitary4_kron2 hA hB), ?_⟩
            right; right; right; right; left
            exact h_chain
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- AC-AB-BC-AB: gates 2,4 are AB, so conjugating gate 3 by SWAP_AB is free; BC becomes
          -- AC and the word is pattern #4 (AC-AB-AC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_eq := (retype3_AB_BC_to_AC (embedAC V₁) V₂ V₃ V
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC).trans
              (sandwich_AC_AB_AC_AB_to_4embed V₁ (V₂ * SWAP_4) V₃ (SWAP_4 * V)
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uB₂ uA₂ uC₂ uB₃ uA₃ uC₃ uA uB uC)
            refine ⟨_, _, _, _, ?_, ?_, ?_, ?_,
              Or.inr (Or.inr (Or.inr (Or.inl h_eq)))⟩ <;> unitary_auto
      | compose_BC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,3,2) BC-BC-AB inner-pair-merge: V₂ and V₃ both BC.
        -- Pattern #5 (BC-AB-BC-AB).
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := inner_BC_pair_merge_sandwich V₂ V₃ (embedAB V)
              u_pA u_pB u_pC uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            have hV_merged : IsUnitary4 (V₂ * (kron2 uB₂ uC₂ * V₃)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hB₂ hC₂) hV₃)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AB_at_3_2_canonical
                (V₂ * (kron2 uB₂ uC₂ * V₃)) V hV_merged hV
                (u_pA * uA₂) u_pB u_pC uA₃ uB₃ uC₃ uA uB uC
                (isUnitary2_mul h_pA hA₂) h_pB h_pC hA₃ hB₃ hC₃ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AB-BC-BC-AB: V₁=V=AB outer, V₂=V₃=BC middle pair.
          -- Pattern C (middle-pair-merge): merge BC pair, reduce to (3,2,1) AB-BC-AB.
          -- Pattern #8 (AB-BC-AB-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_middle_merge :
                singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                  singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ =
                singleQubitLayer (uA₁ * uA₂) uB₁ uC₁ *
                  embedBC (V₂ * (kron2 uB₂ uC₂ * V₃)) *
                  singleQubitLayer uA₃ uB₃ uC₃ := by
              rw [show
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ =
                    singleQubitLayer uA₁ uB₁ uC₁ *
                      (embedBC V₂ * singleQubitLayer uA₂ uB₂ uC₂ *
                        embedBC V₃) *
                      singleQubitLayer uA₃ uB₃ uC₃ from by noncomm_ring]
              rw [embedBC_merge]
              rw [show singleQubitLayer uA₁ uB₁ uC₁ *
                    (singleQubitLayer uA₂ I₂ I₂ *
                      embedBC (V₂ * (kron2 uB₂ uC₂ * V₃))) *
                    singleQubitLayer uA₃ uB₃ uC₃ =
                  (singleQubitLayer uA₁ uB₁ uC₁ *
                     singleQubitLayer uA₂ I₂ I₂) *
                    embedBC (V₂ * (kron2 uB₂ uC₂ * V₃)) *
                    singleQubitLayer uA₃ uB₃ uC₃ from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    (singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃) *
                    embedAB V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_middle_merge]
            have h_chain := sandwich_AB_BC_AB_to_4embed V₁
              (V₂ * (kron2 uB₂ uC₂ * V₃)) V
              u_pA u_pB u_pC (uA₁ * uA₂) uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            have hV_merge : IsUnitary4 (V₂ * (kron2 uB₂ uC₂ * V₃)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hB₂ hC₂) hV₃)
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV₁)
                (isUnitary4_kron2 (isUnitary2_mul hA₁ hA₂) hB₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul h_pC hC₁)) hV_merge)
                (isUnitary4_kron2 hB₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₃ isUnitary2_one) hV)
                (isUnitary4_kron2 hA hB),
              isUnitary4_kron2 isUnitary2_one hC, ?_⟩
            right; right; right; right; right; right; right; left
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    (singleQubitLayer (uA₁ * uA₂) uB₁ uC₁ *
                      embedBC (V₂ * (kron2 uB₂ uC₂ * V₃)) *
                      singleQubitLayer uA₃ uB₃ uC₃) *
                    embedAB V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer (uA₁ * uA₂) uB₁ uC₁ *
                    embedBC (V₂ * (kron2 uB₂ uC₂ * V₃)) *
                    singleQubitLayer uA₃ uB₃ uC₃ *
                    embedAB V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_chain
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) BC-BC-BC-AB: V₁=V₂=V₃=BC, V=AB. Inner-3-merge.
          -- Pattern #5 (BC-AB-BC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_inner_merge :
                singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                  singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                  singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ =
                singleQubitLayer ((u_pA * uA₁) * uA₂) u_pB u_pC *
                  embedBC (V₁ * (kron2 uB₁ uC₁ * V₂) *
                    (kron2 uB₂ uC₂ * V₃)) *
                  singleQubitLayer uA₃ uB₃ uC₃ :=
              sandwich_BC_BC_BC_to_BC V₁ V₂ V₃
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃) *
                    embedAB V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_inner_merge]
            have hV_merge : IsUnitary4
                (V₁ * (kron2 uB₁ uC₁ * V₂) * (kron2 uB₂ uC₂ * V₃)) :=
              isUnitary4_mul
                (isUnitary4_mul hV₁
                  (isUnitary4_mul (isUnitary4_kron2 hB₁ hC₁) hV₂))
                (isUnitary4_mul (isUnitary4_kron2 hB₂ hC₂) hV₃)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AB_at_3_2_canonical
                (V₁ * (kron2 uB₁ uC₁ * V₂) * (kron2 uB₂ uC₂ * V₃)) V
                hV_merge hV
                ((u_pA * uA₁) * uA₂) u_pB u_pC uA₃ uB₃ uC₃ uA uB uC
                (isUnitary2_mul (isUnitary2_mul h_pA hA₁) hA₂) h_pB h_pC
                hA₃ hB₃ hC₃ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; left
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AC-BC-BC-AB: V₁=AC, V₂=V₃=BC middle pair, V=AB.
          -- Pattern C (middle-pair-merge): merge BC pair, reduce to (3,2,1) AC-BC-AB.
          -- Pattern #3 (AC-BC-AB-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_middle_merge :
                singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                  singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ =
                singleQubitLayer (uA₁ * uA₂) uB₁ uC₁ *
                  embedBC (V₂ * (kron2 uB₂ uC₂ * V₃)) *
                  singleQubitLayer uA₃ uB₃ uC₃ := by
              rw [show
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ =
                    singleQubitLayer uA₁ uB₁ uC₁ *
                      (embedBC V₂ * singleQubitLayer uA₂ uB₂ uC₂ *
                        embedBC V₃) *
                      singleQubitLayer uA₃ uB₃ uC₃ from by noncomm_ring]
              rw [embedBC_merge]
              rw [show singleQubitLayer uA₁ uB₁ uC₁ *
                    (singleQubitLayer uA₂ I₂ I₂ *
                      embedBC (V₂ * (kron2 uB₂ uC₂ * V₃))) *
                    singleQubitLayer uA₃ uB₃ uC₃ =
                  (singleQubitLayer uA₁ uB₁ uC₁ *
                     singleQubitLayer uA₂ I₂ I₂) *
                    embedBC (V₂ * (kron2 uB₂ uC₂ * V₃)) *
                    singleQubitLayer uA₃ uB₃ uC₃ from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    (singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃) *
                    embedAB V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_middle_merge]
            have h_chain := sandwich_AC_BC_AB_to_4embed V₁
              (V₂ * (kron2 uB₂ uC₂ * V₃)) V
              u_pA u_pB u_pC (uA₁ * uA₂) uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            have hV_merge : IsUnitary4 (V₂ * (kron2 uB₂ uC₂ * V₃)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hB₂ hC₂) hV₃)
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV₁)
                (isUnitary4_kron2 (isUnitary2_mul hA₁ hA₂) hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pB hB₁) isUnitary2_one) hV_merge)
                (isUnitary4_kron2 hB₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₃ isUnitary2_one) hV)
                (isUnitary4_kron2 hA hB),
              isUnitary4_kron2 isUnitary2_one hC, ?_⟩
            right; right; left
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    (singleQubitLayer (uA₁ * uA₂) uB₁ uC₁ *
                      embedBC (V₂ * (kron2 uB₂ uC₂ * V₃)) *
                      singleQubitLayer uA₃ uB₃ uC₃) *
                    embedAB V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer (uA₁ * uA₂) uB₁ uC₁ *
                    embedBC (V₂ * (kron2 uB₂ uC₂ * V₃)) *
                    singleQubitLayer uA₃ uB₃ uC₃ *
                    embedAB V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_chain
      | compose_AC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,3,2) AC-BC-AB section (V outer=AB, V₃=BC, V₂=AC).
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            -- (4,3,2) AC-BC-AB: 3-real-gate natural chain.
            -- Pattern #3 (AC-BC-AB-AC).
            have h_chain := sandwich_AC_BC_AB_to_4embed V₂ V₃ V
              u_pA u_pB u_pC uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV₂)
                (isUnitary4_kron2 hA₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pB hB₂) isUnitary2_one) hV₃)
                (isUnitary4_kron2 hB₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₃ isUnitary2_one) hV)
                (isUnitary4_kron2 hA hB),
              isUnitary4_kron2 isUnitary2_one hC, ?_⟩
            right; right; left
            exact h_chain
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- AB-AC-BC-AB: gates 1,4 are AB, so conjugating the middle block by SWAP_AB is free; AC
          -- and BC swap and the word is pattern #2 (AB-BC-AC-AB). Table 4 row 2.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_eq := (retype23_AB V₁ V₂ V₃ V
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC).trans
              (sandwich_AB_BC_AC_AB_to_4embed (V₁ * SWAP_4) V₂ V₃ (SWAP_4 * V)
                u_pA u_pB u_pC uB₁ uA₁ uC₁ uB₂ uA₂ uC₂ uB₃ uA₃ uC₃ uA uB uC)
            refine ⟨_, _, _, _, ?_, ?_, ?_, ?_,
              Or.inr (Or.inl h_eq)⟩ <;> unitary_auto
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- BC-AC-BC-AB: gates 1,3 are BC, so conjugating gate 2 by SWAP_BC is free; AC becomes
          -- AB and the word is pattern #5 (BC-AB-BC-AB). Table 4 row 7.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_eq := (retype2_BC_AC_to_AB (embedAB V) V₁ V₂ V₃
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC).trans
              (sandwich_BC_AB_BC_AB_to_4embed (V₁ * SWAP_4) V₂ (SWAP_4 * V₃) V
                u_pA u_pB u_pC uA₁ uC₁ uB₁ uA₂ uC₂ uB₂ uA₃ uB₃ uC₃ uA uB uC)
            refine ⟨_, _, _, _, ?_, ?_, ?_, ?_,
              Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_eq))))⟩ <;> unitary_auto
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AC-AC-BC-AB: V₁=V₂=AC inner pair, V₃=BC, V outer=AB.
          -- Pattern D inner-pair-merge → (3,2,1) AC-BC-AB. Pattern #3.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_inner_merge :
                singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                  singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ =
                singleQubitLayer u_pA (u_pB * uB₁) u_pC *
                  embedAC (V₁ * (kron2 uA₁ uC₁ * V₂)) := by
              rw [show
                    singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                      singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAC V₁ * singleQubitLayer uA₁ uB₁ uC₁ *
                        embedAC V₂) from by noncomm_ring]
              rw [embedAC_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                    (singleQubitLayer I₂ uB₁ I₂ *
                      embedAC (V₁ * (kron2 uA₁ uC₁ * V₂))) =
                  (singleQubitLayer u_pA u_pB u_pC *
                     singleQubitLayer I₂ uB₁ I₂) *
                    embedAC (V₁ * (kron2 uA₁ uC₁ * V₂))
                  from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂) *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_inner_merge]
            have h_chain := sandwich_AC_BC_AB_to_4embed
              (V₁ * (kron2 uA₁ uC₁ * V₂)) V₃ V
              u_pA (u_pB * uB₁) u_pC uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            have hV_merge : IsUnitary4 (V₁ * (kron2 uA₁ uC₁ * V₂)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hC₁) hV₂)
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV_merge)
                (isUnitary4_kron2 hA₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul (isUnitary2_mul h_pB hB₁) hB₂)
                  isUnitary2_one) hV₃)
                (isUnitary4_kron2 hB₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₃ isUnitary2_one) hV)
                (isUnitary4_kron2 hA hB),
              isUnitary4_kron2 isUnitary2_one hC, ?_⟩
            right; right; left
            exact h_chain
    | compose_AC V₃ hV₃ uA₃ uB₃ uC₃ hA₃ hB₃ hC₃ h2 =>
      -- (4,3) outer AB inner AC. Pattern #4 (AC-AB-AC-AB).
      cases h2 with
      | weaken h1 =>
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_AB_at_3_2_canonical V₃ V hV₃ hV
                u_pA u_pB u_pC uA₃ uB₃ uC₃ uA uB uC
                h_pA h_pB h_pC hA₃ hB₃ hC₃ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; left
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,1) AB-AC-AB non-adjacent-same: V₁ and V outer both AB.
          -- Pattern #7 (AB-AC-AB-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AB_AC_AB_to_4embed V₁ V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV₁)
                (isUnitary4_kron2 hA₁ hB₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul h_pC hC₁)) hV₃)
                (isUnitary4_kron2 hA₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hB₃) hV)
                (isUnitary4_kron2 hA hB),
              isUnitary4_kron2 isUnitary2_one hC, ?_⟩
            right; right; right; right; right; right; left
            exact h_chain
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,1) BC-AC-AB all-different: V₁=BC, V₃=AC, V outer=AB.
          -- Pattern #1 (BC-AC-AB-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_BC_AC_AB_to_4embed V₁ V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV₁)
                (isUnitary4_kron2 hB₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pA hA₁) isUnitary2_one) hV₃)
                (isUnitary4_kron2 hA₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hB₃) hV)
                (isUnitary4_kron2 hA hB),
              isUnitary4_kron2 isUnitary2_one hC, ?_⟩
            left
            exact h_chain
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,1) AC-AC-AB inner-pair-merge: V₁ and V₃ both AC.
          -- Pattern #4 (AC-AB-AC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := inner_AC_pair_merge_sandwich V₁ V₃ (embedAB V)
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            have hV_merged : IsUnitary4 (V₁ * (kron2 uA₁ uC₁ * V₃)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hC₁) hV₃)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_AB_at_3_2_canonical
                (V₁ * (kron2 uA₁ uC₁ * V₃)) V hV_merged hV
                u_pA (u_pB * uB₁) u_pC uA₃ uB₃ uC₃ uA uB uC
                h_pA (isUnitary2_mul h_pB hB₁) h_pC hA₃ hB₃ hC₃ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; left
            rw [h_merge]
            exact h_eq
      | compose_AB V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,3,2) AB-AC-AB section (V outer=AB, V₃=AC, V₂=AB).
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            -- (4,3,2) AB-AC-AB: 3-real-gate natural chain. Pattern #7.
            have h_chain := sandwich_AB_AC_AB_to_4embed V₂ V₃ V
              u_pA u_pB u_pC uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV₂)
                (isUnitary4_kron2 hA₂ hB₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul h_pC hC₂)) hV₃)
                (isUnitary4_kron2 hA₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hB₃) hV)
                (isUnitary4_kron2 hA hB),
              isUnitary4_kron2 isUnitary2_one hC, ?_⟩
            right; right; right; right; right; right; left
            exact h_chain
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AB-AB-AC-AB: V₁=V₂=AB inner pair, V₃=AC, V outer=AB.
          -- Pattern D inner-pair-merge → (3,2,1) AB-AC-AB. Pattern #7.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_inner_merge :
                singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                  singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ =
                singleQubitLayer u_pA u_pB (u_pC * uC₁) *
                  embedAB (V₁ * (kron2 uA₁ uB₁ * V₂)) := by
              rw [show
                    singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                      singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAB V₁ * singleQubitLayer uA₁ uB₁ uC₁ *
                        embedAB V₂) from by noncomm_ring]
              rw [embedAB_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                    (singleQubitLayer I₂ I₂ uC₁ *
                      embedAB (V₁ * (kron2 uA₁ uB₁ * V₂))) =
                  (singleQubitLayer u_pA u_pB u_pC *
                     singleQubitLayer I₂ I₂ uC₁) *
                    embedAB (V₁ * (kron2 uA₁ uB₁ * V₂))
                  from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂) *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_inner_merge]
            have h_chain := sandwich_AB_AC_AB_to_4embed
              (V₁ * (kron2 uA₁ uB₁ * V₂)) V₃ V
              u_pA u_pB (u_pC * uC₁) uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            have hV_merge : IsUnitary4 (V₁ * (kron2 uA₁ uB₁ * V₂)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hB₁) hV₂)
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV_merge)
                (isUnitary4_kron2 hA₂ hB₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul (isUnitary2_mul h_pC hC₁) hC₂)) hV₃)
                (isUnitary4_kron2 hA₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hB₃) hV)
                (isUnitary4_kron2 hA hB),
              isUnitary4_kron2 isUnitary2_one hC, ?_⟩
            right; right; right; right; right; right; left
            exact h_chain
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- BC-AB-AC-AB: gates 2,4 are AB; conjugating gate 3 turns AC into BC, giving pattern #5
          -- (BC-AB-BC-AB). Table 4 row 1.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_eq := (retype3_AB_AC_to_BC (embedBC V₁) V₂ V₃ V
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC).trans
              (sandwich_BC_AB_BC_AB_to_4embed V₁ (V₂ * SWAP_4) V₃ (SWAP_4 * V)
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uB₂ uA₂ uC₂ uB₃ uA₃ uC₃ uA uB uC)
            refine ⟨_, _, _, _, ?_, ?_, ?_, ?_,
              Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_eq))))⟩ <;> unitary_auto
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AC-AB-AC-AB: V₁=AC, V₂=AB, V₃=AC, V outer=AB.
          -- Direct pattern #4 (AC-AB-AC-AB) match. Pattern E flagship case.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AC_AB_AC_AB_to_4embed V₁ V₂ V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV₁)
                (isUnitary4_kron2 hA₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul h_pB hB₁)) hV₂)
                (isUnitary4_kron2 hA₂ hB₂),
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₂) hV₃)
                  (isUnitary4_kron2 hA₃ hC₃))
                (isUnitary4_kron2 isUnitary2_one hC),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hB₃) hV)
                (isUnitary4_kron2 hA hB), ?_⟩
            right; right; right; left
            exact h_chain
      | compose_BC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,3,2) BC-AC-AB section (V outer=AB, V₃=AC, V₂=BC).
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            -- (4,3,2) BC-AC-AB: 3-real-gate natural chain. Pattern #1.
            have h_chain := sandwich_BC_AC_AB_to_4embed V₂ V₃ V
              u_pA u_pB u_pC uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV₂)
                (isUnitary4_kron2 hB₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pA hA₂) isUnitary2_one) hV₃)
                (isUnitary4_kron2 hA₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hB₃) hV)
                (isUnitary4_kron2 hA hB),
              isUnitary4_kron2 isUnitary2_one hC, ?_⟩
            left
            exact h_chain
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- AB-BC-AC-AB is literally pattern #2 — no SWAP needed.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_eq := sandwich_AB_BC_AC_AB_to_4embed V₁ V₂ V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _, ?_, ?_, ?_, ?_,
              Or.inr (Or.inl h_eq)⟩ <;> unitary_auto
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) BC-BC-AC-AB: V₁=V₂=BC inner pair, V₃=AC, V outer=AB.
          -- Pattern D inner-pair-merge → (3,2,1) BC-AC-AB. Pattern #1.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_inner_merge :
                singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                  singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ =
                singleQubitLayer (u_pA * uA₁) u_pB u_pC *
                  embedBC (V₁ * (kron2 uB₁ uC₁ * V₂)) := by
              rw [show
                    singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                      singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedBC V₁ * singleQubitLayer uA₁ uB₁ uC₁ *
                        embedBC V₂) from by noncomm_ring]
              rw [embedBC_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                    (singleQubitLayer uA₁ I₂ I₂ *
                      embedBC (V₁ * (kron2 uB₁ uC₁ * V₂))) =
                  (singleQubitLayer u_pA u_pB u_pC *
                     singleQubitLayer uA₁ I₂ I₂) *
                    embedBC (V₁ * (kron2 uB₁ uC₁ * V₂))
                  from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂) *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_inner_merge]
            have hV_inner : IsUnitary4 (V₁ * (kron2 uB₁ uC₁ * V₂)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hB₁ hC₁) hV₂)
            have h_chain := sandwich_BC_AC_AB_to_4embed
              (V₁ * (kron2 uB₁ uC₁ * V₂)) V₃ V
              (u_pA * uA₁) u_pB u_pC uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV_inner)
                (isUnitary4_kron2 hB₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul (isUnitary2_mul h_pA hA₁) hA₂)
                  isUnitary2_one) hV₃)
                (isUnitary4_kron2 hA₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hB₃) hV)
                (isUnitary4_kron2 hA hB),
              isUnitary4_kron2 isUnitary2_one hC, ?_⟩
            left
            exact h_chain
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- AC-BC-AC-AB: gates 1,3 are AC; conjugating gate 2 by SWAP_AC turns BC into AB, giving
          -- pattern #4 (AC-AB-AC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_eq := (retype2_AC_BC_to_AB (embedAB V) V₁ V₂ V₃
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC).trans
              (sandwich_AC_AB_AC_AB_to_4embed (V₁ * SWAP_4) (SWAP_4 * V₂ * SWAP_4)
                (SWAP_4 * V₃) V
                u_pA u_pB u_pC uC₁ uB₁ uA₁ uC₂ uB₂ uA₂ uA₃ uB₃ uC₃ uA uB uC)
            refine ⟨_, _, _, _, ?_, ?_, ?_, ?_,
              Or.inr (Or.inr (Or.inr (Or.inl h_eq)))⟩ <;> unitary_auto
      | compose_AC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,3,2) AC-AC-AB section (V outer=AB, V₃=AC, V₂=AC).
        -- V₂=V₃=AC consecutive adjacent same-XY merge.
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            -- (4,3,2) AC-AC-AB: merge V₂,V₃ (both AC) → (3,2) AC-AB chain.
            -- Pattern #4 (AC-AB-AC-AB).
            have h_merge :
                singleQubitLayer u_pA u_pB u_pC * embedAC V₂ *
                  singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ =
                singleQubitLayer u_pA (u_pB * uB₂) u_pC *
                  embedAC (V₂ * (kron2 uA₂ uC₂ * V₃)) *
                  singleQubitLayer uA₃ uB₃ uC₃ := by
              rw [show
                    singleQubitLayer u_pA u_pB u_pC * embedAC V₂ *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAC V₂ * singleQubitLayer uA₂ uB₂ uC₂ *
                        embedAC V₃) *
                      singleQubitLayer uA₃ uB₃ uC₃ from by noncomm_ring]
              rw [embedAC_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                    (singleQubitLayer I₂ uB₂ I₂ *
                      embedAC (V₂ * (kron2 uA₂ uC₂ * V₃))) *
                    singleQubitLayer uA₃ uB₃ uC₃ =
                  (singleQubitLayer u_pA u_pB u_pC *
                     singleQubitLayer I₂ uB₂ I₂) *
                    embedAC (V₂ * (kron2 uA₂ uC₂ * V₃)) *
                    singleQubitLayer uA₃ uB₃ uC₃ from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₂ * (kron2 uA₂ uC₂ * V₃)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hA₂ hC₂) hV₃)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_AB_at_3_2_canonical
                (V₂ * (kron2 uA₂ uC₂ * V₃)) V hV_merged hV
                u_pA (u_pB * uB₂) u_pC uA₃ uB₃ uC₃ uA uB uC
                h_pA (isUnitary2_mul h_pB hB₂) h_pC hA₃ hB₃ hC₃ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; left
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer u_pA u_pB u_pC * embedAC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃) *
                    embedAB V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_merge]
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- AB-AC-AC-AB: adjacent AC pair at slots (2,3) merges, leaving
          -- AB-AC-AB = pattern #7 (AB-AC-AB-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have hW : IsUnitary4 (V₂ * (kron2 uA₂ uC₂ * V₃)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hA₂ hC₂) hV₃)
            have h_merge := merge23_AC (embedAB V₁) (embedAB V) V₂ V₃
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            have h_chain := sandwich_AB_AC_AB_to_4embed V₁
              (V₂ * (kron2 uA₂ uC₂ * V₃)) V
              u_pA u_pB u_pC uA₁ (uB₁ * uB₂) uC₁ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV₁)
                (isUnitary4_kron2 hA₁ (isUnitary2_mul hB₁ hB₂)),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul h_pC hC₁)) hW)
                (isUnitary4_kron2 hA₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hB₃) hV)
                (isUnitary4_kron2 hA hB),
              isUnitary4_kron2 isUnitary2_one hC, ?_⟩
            right; right; right; right; right; right; left
            rw [h_merge]
            exact h_chain
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) BC-AC-AC-AB: V₁=BC, V₂=V₃=AC middle pair, V outer=AB.
          -- Pattern C middle-pair-merge → (3,2,1) BC-AC-AB. Pattern #1.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_middle_merge :
                singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                  singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ =
                singleQubitLayer uA₁ (uB₁ * uB₂) uC₁ *
                  embedAC (V₂ * (kron2 uA₂ uC₂ * V₃)) := by
              rw [show
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ =
                    singleQubitLayer uA₁ uB₁ uC₁ *
                      (embedAC V₂ * singleQubitLayer uA₂ uB₂ uC₂ *
                        embedAC V₃) from by noncomm_ring]
              rw [embedAC_merge]
              rw [show singleQubitLayer uA₁ uB₁ uC₁ *
                    (singleQubitLayer I₂ uB₂ I₂ *
                      embedAC (V₂ * (kron2 uA₂ uC₂ * V₃))) =
                  (singleQubitLayer uA₁ uB₁ uC₁ *
                     singleQubitLayer I₂ uB₂ I₂) *
                    embedAC (V₂ * (kron2 uA₂ uC₂ * V₃))
                  from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    (singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃) *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_middle_merge]
            have h_chain := sandwich_BC_AC_AB_to_4embed V₁
              (V₂ * (kron2 uA₂ uC₂ * V₃)) V
              u_pA u_pB u_pC uA₁ (uB₁ * uB₂) uC₁ uA₃ uB₃ uC₃ uA uB uC
            have hV_merge : IsUnitary4 (V₂ * (kron2 uA₂ uC₂ * V₃)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hA₂ hC₂) hV₃)
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV₁)
                (isUnitary4_kron2 (isUnitary2_mul hB₁ hB₂) hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pA hA₁) isUnitary2_one) hV_merge)
                (isUnitary4_kron2 hA₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hB₃) hV)
                (isUnitary4_kron2 hA hB),
              isUnitary4_kron2 isUnitary2_one hC, ?_⟩
            left
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    (singleQubitLayer uA₁ (uB₁ * uB₂) uC₁ *
                      embedAC (V₂ * (kron2 uA₂ uC₂ * V₃))) *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ (uB₁ * uB₂) uC₁ *
                    embedAC (V₂ * (kron2 uA₂ uC₂ * V₃)) *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_chain
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AC-AC-AC-AB: V₁=V₂=V₃=AC inner three, V outer=AB.
          -- Pattern G inner-3-merge → (3,1) AC-AB chain. Pattern #4.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_inner_merge :
                singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                  singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                  singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ =
                singleQubitLayer u_pA (((u_pB * uB₁) * uB₂)) u_pC *
                  embedAC (V₁ * (kron2 uA₁ uC₁ * V₂) *
                    (kron2 uA₂ uC₂ * V₃)) *
                  singleQubitLayer uA₃ uB₃ uC₃ :=
              sandwich_AC_AC_AC_to_AC V₁ V₂ V₃
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAB V *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃) *
                    embedAB V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_inner_merge]
            have hV_merge : IsUnitary4
                (V₁ * (kron2 uA₁ uC₁ * V₂) * (kron2 uA₂ uC₂ * V₃)) :=
              isUnitary4_mul
                (isUnitary4_mul hV₁
                  (isUnitary4_mul (isUnitary4_kron2 hA₁ hC₁) hV₂))
                (isUnitary4_mul (isUnitary4_kron2 hA₂ hC₂) hV₃)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_AB_at_3_2_canonical
                (V₁ * (kron2 uA₁ uC₁ * V₂) * (kron2 uA₂ uC₂ * V₃)) V
                hV_merge hV
                u_pA ((u_pB * uB₁) * uB₂) u_pC uA₃ uB₃ uC₃ uA uB uC
                h_pA (isUnitary2_mul (isUnitary2_mul h_pB hB₁) hB₂) h_pC
                hA₃ hB₃ hC₃ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; left
            exact h_eq
  | compose_BC V hV uA uB uC hA hB hC h3 =>
    -- Position-4 BC outer.
    cases h3 with
    | weaken h2 =>
      cases h2 with
      | weaken h1 =>
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁, V₂, V₃, V₄', hV₁, hV₂, hV₃, hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleBC_canonical V hV
                u_pA u_pB u_pC h_pA h_pB h_pC uA uB uC hA hB hC
            refine ⟨V₁, V₂, V₃, V₄', hV₁, hV₂, hV₃, hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,1) outer BC inner AB. Pattern #8 (AB-BC-AB-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_BC_at_3_2_canonical V₁ V hV₁ hV
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA uB uC
                h_pA h_pB h_pC hA₁ hB₁ hC₁ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,1) BC-BC consecutive same-XY merge. Pattern #9.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge :
              singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                singleQubitLayer uA₁ uB₁ uC₁ * embedBC V *
                singleQubitLayer uA uB uC =
              singleQubitLayer (u_pA * uA₁) u_pB u_pC *
                embedBC (V₁ * (kron2 uB₁ uC₁ * V)) *
                singleQubitLayer uA uB uC := by
              rw [show singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                        singleQubitLayer uA₁ uB₁ uC₁ * embedBC V *
                        singleQubitLayer uA uB uC =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedBC V₁ * singleQubitLayer uA₁ uB₁ uC₁ * embedBC V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedBC_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                        (singleQubitLayer uA₁ I₂ I₂ *
                          embedBC (V₁ * (kron2 uB₁ uC₁ * V))) *
                        singleQubitLayer uA uB uC =
                    (singleQubitLayer u_pA u_pB u_pC *
                       singleQubitLayer uA₁ I₂ I₂) *
                      embedBC (V₁ * (kron2 uB₁ uC₁ * V)) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₁ * (kron2 uB₁ uC₁ * V)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hB₁ hC₁) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleBC_canonical (V₁ * (kron2 uB₁ uC₁ * V))
                hV_merged
                (u_pA * uA₁) u_pB u_pC (isUnitary2_mul h_pA hA₁) h_pB h_pC
                uA uB uC hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            rw [h_merge]
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,1) outer BC inner AC. Pattern #9 (AC-BC-AC-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_BC_at_3_2_canonical V₁ V hV₁ hV
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA uB uC
                h_pA h_pB h_pC hA₁ hB₁ hC₁ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            exact h_eq
      | compose_AB V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,2) outer BC inner AB. Pattern #8 (AB-BC-AB-BC).
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_BC_at_3_2_canonical V₂ V hV₂ hV
                u_pA u_pB u_pC uA₂ uB₂ uC₂ uA uB uC
                h_pA h_pB h_pC hA₂ hB₂ hC₂ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,2,1) AB-AB-BC inner-pair-merge: V₁ and V₂ both AB.
          -- Pattern #8 (AB-BC-AB-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := inner_AB_pair_merge_sandwich V₁ V₂ (embedBC V)
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA uB uC
            have hV_merged : IsUnitary4 (V₁ * (kron2 uA₁ uB₁ * V₂)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hB₁) hV₂)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_BC_at_3_2_canonical
                (V₁ * (kron2 uA₁ uB₁ * V₂)) V hV_merged hV
                u_pA u_pB (u_pC * uC₁) uA₂ uB₂ uC₂ uA uB uC
                h_pA h_pB (isUnitary2_mul h_pC hC₁) hA₂ hB₂ hC₂ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,2,1) BC-AB-BC non-adjacent-same: V₁ and V outer both BC.
          -- Pattern #5 (BC-AB-BC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_BC_AB_BC_to_4embed V₁ V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV₁)
                (isUnitary4_kron2 hB₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pA hA₁) isUnitary2_one) hV₂)
                (isUnitary4_kron2 hA₂ hB₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₂) hV)
                (isUnitary4_kron2 hB hC),
              isUnitary4_kron2 hA isUnitary2_one, ?_⟩
            right; right; right; right; left
            exact h_chain
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) AC-AB-BC all-different. Pattern #1 (BC-AC-AB-BC), V₁ = 1.
          -- Iter 1038: closed via `sandwich_AC_AB_BC_to_4embed` — the trailing
          -- A-only leftover commutes past `embedBC` and absorbs into the AB
          -- gate, so no fourth real embed is needed (retracts the iter-729
          -- "3-XY gap"; see the declaration docstring).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AC_AB_BC_to_4embed V₁ V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA uB uC
            refine ⟨1,
              kron2 u_pA u_pC * V₁ * kron2 uA₁ uC₁,
              kron2 1 (u_pB * uB₁) * V₂ * kron2 uA₂ uB₂ * kron2 uA 1,
              kron2 1 uC₂ * V * kron2 uB uC,
              isUnitary4_one,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV₁)
                (isUnitary4_kron2 hA₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul
                    (isUnitary4_kron2 isUnitary2_one (isUnitary2_mul h_pB hB₁))
                    hV₂)
                  (isUnitary4_kron2 hA₂ hB₂))
                (isUnitary4_kron2 hA isUnitary2_one),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₂) hV)
                (isUnitary4_kron2 hB hC), ?_⟩
            left
            rw [embedBC_one, one_mul]
            exact h_chain
      | compose_BC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,2) BC-BC consecutive same-XY merge. Pattern #9.
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge :
              singleQubitLayer u_pA u_pB u_pC * embedBC V₂ *
                singleQubitLayer uA₂ uB₂ uC₂ * embedBC V *
                singleQubitLayer uA uB uC =
              singleQubitLayer (u_pA * uA₂) u_pB u_pC *
                embedBC (V₂ * (kron2 uB₂ uC₂ * V)) *
                singleQubitLayer uA uB uC := by
              rw [show singleQubitLayer u_pA u_pB u_pC * embedBC V₂ *
                        singleQubitLayer uA₂ uB₂ uC₂ * embedBC V *
                        singleQubitLayer uA uB uC =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedBC V₂ * singleQubitLayer uA₂ uB₂ uC₂ * embedBC V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedBC_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                        (singleQubitLayer uA₂ I₂ I₂ *
                          embedBC (V₂ * (kron2 uB₂ uC₂ * V))) *
                        singleQubitLayer uA uB uC =
                    (singleQubitLayer u_pA u_pB u_pC *
                       singleQubitLayer uA₂ I₂ I₂) *
                      embedBC (V₂ * (kron2 uB₂ uC₂ * V)) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₂ * (kron2 uB₂ uC₂ * V)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hB₂ hC₂) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleBC_canonical (V₂ * (kron2 uB₂ uC₂ * V))
                hV_merged
                (u_pA * uA₂) u_pB u_pC (isUnitary2_mul h_pA hA₂) h_pB h_pC
                uA uB uC hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            rw [h_merge]
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,2,1) AB-BC-BC outer-pair-BC-merge: V₂ and V outer both BC.
          -- Pattern #8 (AB-BC-AB-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := outer_BC_pair_merge_sandwich (embedAB V₁) V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA uB uC
            have hV_merged : IsUnitary4 (V₂ * (kron2 uB₂ uC₂ * V)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hB₂ hC₂) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_BC_at_3_2_canonical V₁
                (V₂ * (kron2 uB₂ uC₂ * V)) hV₁ hV_merged
                u_pA u_pB u_pC (uA₁ * uA₂) uB₁ uC₁ uA uB uC
                h_pA h_pB h_pC (isUnitary2_mul hA₁ hA₂) hB₁ hC₁ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,2,1) BC-BC-BC triple same-XY merge. Pattern #9.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have hV_merged : IsUnitary4
                (V₁ * (kron2 uB₁ uC₁ * V₂) * (kron2 uB₂ uC₂ * V)) :=
              isUnitary4_mul
                (isUnitary4_mul hV₁
                  (isUnitary4_mul (isUnitary4_kron2 hB₁ hC₁) hV₂))
                (isUnitary4_mul (isUnitary4_kron2 hB₂ hC₂) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleBC_canonical
                (V₁ * (kron2 uB₁ uC₁ * V₂) * (kron2 uB₂ uC₂ * V))
                hV_merged
                ((u_pA * uA₁) * uA₂) u_pB u_pC
                (isUnitary2_mul (isUnitary2_mul h_pA hA₁) hA₂) h_pB h_pC
                uA uB uC hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            rw [sandwich_BC_BC_BC_to_BC V₁ V₂ V
                  u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA uB uC]
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,2,1) AC-BC-BC outer-pair-BC-merge: V₂ and V outer both BC.
          -- Pattern #9 (AC-BC-AC-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := outer_BC_pair_merge_sandwich (embedAC V₁) V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA uB uC
            have hV_merged : IsUnitary4 (V₂ * (kron2 uB₂ uC₂ * V)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hB₂ hC₂) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_BC_at_3_2_canonical V₁
                (V₂ * (kron2 uB₂ uC₂ * V)) hV₁ hV_merged
                u_pA u_pB u_pC (uA₁ * uA₂) uB₁ uC₁ uA uB uC
                h_pA h_pB h_pC (isUnitary2_mul hA₁ hA₂) hB₁ hC₁ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            rw [h_merge]
            exact h_eq
      | compose_AC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,2) outer BC inner AC. Pattern #9 (AC-BC-AC-BC).
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_BC_at_3_2_canonical V₂ V hV₂ hV
                u_pA u_pB u_pC uA₂ uB₂ uC₂ uA uB uC
                h_pA h_pB h_pC hA₂ hB₂ hC₂ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,2,1) AB-AC-BC all-different. Pattern #1 (BC-AC-AB-BC), V₁ = SWAP_4.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AB_AC_BC_to_4embed V₁ V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_SWAP_4,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV₁)
                (isUnitary4_kron2 hA₁ hB₁),
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul
                    (isUnitary4_kron2 isUnitary2_one (isUnitary2_mul h_pC hC₁))
                    hV₂)
                  (isUnitary4_kron2 hA₂ hC₂))
                (isUnitary4_kron2 hA isUnitary2_one),
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hB₂)
                    (isUnitary4_swap4_conj V hV))
                  (isUnitary4_kron2 hC hB))
                isUnitary4_SWAP_4, ?_⟩
            left
            exact h_chain
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,2,1) BC-AC-BC non-adjacent-same: V₁ and V outer both BC.
          -- Pattern #6 (BC-AC-BC-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_BC_AC_BC_to_4embed V₁ V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV₁)
                (isUnitary4_kron2 hB₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pA hA₁) isUnitary2_one) hV₂)
                (isUnitary4_kron2 hA₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hB₂ isUnitary2_one) hV)
                (isUnitary4_kron2 hB hC),
              isUnitary4_kron2 hA isUnitary2_one, ?_⟩
            right; right; right; right; right; left
            exact h_chain
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,2,1) AC-AC-BC inner-pair-merge: V₁ and V₂ both AC.
          -- Pattern #9 (AC-BC-AC-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := inner_AC_pair_merge_sandwich V₁ V₂ (embedBC V)
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA uB uC
            have hV_merged : IsUnitary4 (V₁ * (kron2 uA₁ uC₁ * V₂)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hC₁) hV₂)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_BC_at_3_2_canonical
                (V₁ * (kron2 uA₁ uC₁ * V₂)) V hV_merged hV
                u_pA (u_pB * uB₁) u_pC uA₂ uB₂ uC₂ uA uB uC
                h_pA (isUnitary2_mul h_pB hB₁) h_pC hA₂ hB₂ hC₂ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            rw [h_merge]
            exact h_eq
    | compose_AB V₃ hV₃ uA₃ uB₃ uC₃ hA₃ hB₃ hC₃ h2 =>
      -- (4,3) outer BC inner AB. Pattern #8 (AB-BC-AB-BC).
      cases h2 with
      | weaken h1 =>
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_BC_at_3_2_canonical V₃ V hV₃ hV
                u_pA u_pB u_pC uA₃ uB₃ uC₃ uA uB uC
                h_pA h_pB h_pC hA₃ hB₃ hC₃ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,1) AB-AB-BC inner-pair-merge: V₁ and V₃ both AB.
          -- Pattern #8 (AB-BC-AB-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := inner_AB_pair_merge_sandwich V₁ V₃ (embedBC V)
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            have hV_merged : IsUnitary4 (V₁ * (kron2 uA₁ uB₁ * V₃)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hB₁) hV₃)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_BC_at_3_2_canonical
                (V₁ * (kron2 uA₁ uB₁ * V₃)) V hV_merged hV
                u_pA u_pB (u_pC * uC₁) uA₃ uB₃ uC₃ uA uB uC
                h_pA h_pB (isUnitary2_mul h_pC hC₁) hA₃ hB₃ hC₃ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,1) BC-AB-BC non-adjacent-same: V₁ and V outer both BC.
          -- Pattern #5 (BC-AB-BC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_BC_AB_BC_to_4embed V₁ V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV₁)
                (isUnitary4_kron2 hB₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pA hA₁) isUnitary2_one) hV₃)
                (isUnitary4_kron2 hA₃ hB₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₃) hV)
                (isUnitary4_kron2 hB hC),
              isUnitary4_kron2 hA isUnitary2_one, ?_⟩
            right; right; right; right; left
            exact h_chain
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) AC-AB-BC all-different. Pattern #1 (BC-AC-AB-BC), V₁ = 1.
          -- Iter 1038: closed via `sandwich_AC_AB_BC_to_4embed` — the trailing
          -- A-only leftover commutes past `embedBC` and absorbs into the AB
          -- gate, so no fourth real embed is needed (retracts the iter-729
          -- "3-XY gap"; see the declaration docstring).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AC_AB_BC_to_4embed V₁ V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨1,
              kron2 u_pA u_pC * V₁ * kron2 uA₁ uC₁,
              kron2 1 (u_pB * uB₁) * V₃ * kron2 uA₃ uB₃ * kron2 uA 1,
              kron2 1 uC₃ * V * kron2 uB uC,
              isUnitary4_one,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV₁)
                (isUnitary4_kron2 hA₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul
                    (isUnitary4_kron2 isUnitary2_one (isUnitary2_mul h_pB hB₁))
                    hV₃)
                  (isUnitary4_kron2 hA₃ hB₃))
                (isUnitary4_kron2 hA isUnitary2_one),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₃) hV)
                (isUnitary4_kron2 hB hC), ?_⟩
            left
            rw [embedBC_one, one_mul]
            exact h_chain
      | compose_AB V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,3,2) AB-AB-BC section (V outer=BC, V₃=AB, V₂=AB).
        -- V₂=V₃=AB consecutive adjacent same-XY merge.
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            -- (4,3,2) AB-AB-BC: merge V₂,V₃ (both AB) → (3,2) AB-BC chain.
            -- Pattern #8 (AB-BC-AB-BC).
            have h_merge :
                singleQubitLayer u_pA u_pB u_pC * embedAB V₂ *
                  singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ =
                singleQubitLayer u_pA u_pB (u_pC * uC₂) *
                  embedAB (V₂ * (kron2 uA₂ uB₂ * V₃)) *
                  singleQubitLayer uA₃ uB₃ uC₃ := by
              rw [show
                    singleQubitLayer u_pA u_pB u_pC * embedAB V₂ *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAB V₂ * singleQubitLayer uA₂ uB₂ uC₂ *
                        embedAB V₃) *
                      singleQubitLayer uA₃ uB₃ uC₃ from by noncomm_ring]
              rw [embedAB_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                    (singleQubitLayer I₂ I₂ uC₂ *
                      embedAB (V₂ * (kron2 uA₂ uB₂ * V₃))) *
                    singleQubitLayer uA₃ uB₃ uC₃ =
                  (singleQubitLayer u_pA u_pB u_pC *
                     singleQubitLayer I₂ I₂ uC₂) *
                    embedAB (V₂ * (kron2 uA₂ uB₂ * V₃)) *
                    singleQubitLayer uA₃ uB₃ uC₃ from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₂ * (kron2 uA₂ uB₂ * V₃)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hA₂ hB₂) hV₃)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_BC_at_3_2_canonical
                (V₂ * (kron2 uA₂ uB₂ * V₃)) V hV_merged hV
                u_pA u_pB (u_pC * uC₂) uA₃ uB₃ uC₃ uA uB uC
                h_pA h_pB (isUnitary2_mul h_pC hC₂) hA₃ hB₃ hC₃ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer u_pA u_pB u_pC * embedAB V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃) *
                    embedBC V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_merge]
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AB-AB-AB-BC: V₁=V₂=V₃=AB inner three, V outer=BC.
          -- Pattern G inner-3-merge → (3,1) AB-BC chain. Pattern #8.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_inner_merge :
                singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                  singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                  singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ =
                singleQubitLayer u_pA u_pB (((u_pC * uC₁) * uC₂)) *
                  embedAB (V₁ * (kron2 uA₁ uB₁ * V₂) *
                    (kron2 uA₂ uB₂ * V₃)) *
                  singleQubitLayer uA₃ uB₃ uC₃ :=
              sandwich_AB_AB_AB_to_AB V₁ V₂ V₃
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃) *
                    embedBC V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_inner_merge]
            have hV_merge : IsUnitary4
                (V₁ * (kron2 uA₁ uB₁ * V₂) * (kron2 uA₂ uB₂ * V₃)) :=
              isUnitary4_mul
                (isUnitary4_mul hV₁
                  (isUnitary4_mul (isUnitary4_kron2 hA₁ hB₁) hV₂))
                (isUnitary4_mul (isUnitary4_kron2 hA₂ hB₂) hV₃)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_BC_at_3_2_canonical
                (V₁ * (kron2 uA₁ uB₁ * V₂) * (kron2 uA₂ uB₂ * V₃)) V
                hV_merge hV
                u_pA u_pB ((u_pC * uC₁) * uC₂) uA₃ uB₃ uC₃ uA uB uC
                h_pA h_pB
                (isUnitary2_mul (isUnitary2_mul h_pC hC₁) hC₂)
                hA₃ hB₃ hC₃ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) BC-AB-AB-BC: V₁=BC, V₂=V₃=AB middle pair, V outer=BC.
          -- Pattern C middle-pair-merge → (3,2,1) BC-AB-BC. Pattern #5.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_middle_merge :
                singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                  singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ =
                singleQubitLayer uA₁ uB₁ (uC₁ * uC₂) *
                  embedAB (V₂ * (kron2 uA₂ uB₂ * V₃)) := by
              rw [show
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ =
                    singleQubitLayer uA₁ uB₁ uC₁ *
                      (embedAB V₂ * singleQubitLayer uA₂ uB₂ uC₂ *
                        embedAB V₃) from by noncomm_ring]
              rw [embedAB_merge]
              rw [show singleQubitLayer uA₁ uB₁ uC₁ *
                    (singleQubitLayer I₂ I₂ uC₂ *
                      embedAB (V₂ * (kron2 uA₂ uB₂ * V₃))) =
                  (singleQubitLayer uA₁ uB₁ uC₁ *
                     singleQubitLayer I₂ I₂ uC₂) *
                    embedAB (V₂ * (kron2 uA₂ uB₂ * V₃))
                  from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    (singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃) *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_middle_merge]
            have h_chain := sandwich_BC_AB_BC_to_4embed V₁
              (V₂ * (kron2 uA₂ uB₂ * V₃)) V
              u_pA u_pB u_pC uA₁ uB₁ (uC₁ * uC₂) uA₃ uB₃ uC₃ uA uB uC
            have hV_merge : IsUnitary4 (V₂ * (kron2 uA₂ uB₂ * V₃)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hA₂ hB₂) hV₃)
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV₁)
                (isUnitary4_kron2 hB₁ (isUnitary2_mul hC₁ hC₂)),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pA hA₁) isUnitary2_one) hV_merge)
                (isUnitary4_kron2 hA₃ hB₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₃) hV)
                (isUnitary4_kron2 hB hC),
              isUnitary4_kron2 hA isUnitary2_one, ?_⟩
            right; right; right; right; left
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    (singleQubitLayer uA₁ uB₁ (uC₁ * uC₂) *
                      embedAB (V₂ * (kron2 uA₂ uB₂ * V₃))) *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ (uC₁ * uC₂) *
                    embedAB (V₂ * (kron2 uA₂ uB₂ * V₃)) *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_chain
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- AC-AB-AB-BC: adjacent AB pair at slots (2,3) merges, leaving
          -- AC-AB-BC = pattern #1 (BC-AC-AB-BC) with V₁ = 1.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have hW : IsUnitary4 (V₂ * (kron2 uA₂ uB₂ * V₃)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hA₂ hB₂) hV₃)
            have h_merge := merge23_AB (embedAC V₁) (embedBC V) V₂ V₃
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            have h_chain := sandwich_AC_AB_BC_to_4embed V₁
              (V₂ * (kron2 uA₂ uB₂ * V₃)) V
              u_pA u_pB u_pC uA₁ uB₁ (uC₁ * uC₂) uA₃ uB₃ uC₃ uA uB uC
            refine ⟨1, _, _, _,
              isUnitary4_one,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV₁)
                (isUnitary4_kron2 hA₁ (isUnitary2_mul hC₁ hC₂)),
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul
                    (isUnitary4_kron2 isUnitary2_one (isUnitary2_mul h_pB hB₁))
                    hW)
                  (isUnitary4_kron2 hA₃ hB₃))
                (isUnitary4_kron2 hA isUnitary2_one),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₃) hV)
                (isUnitary4_kron2 hB hC), ?_⟩
            left
            rw [h_merge, embedBC_one, one_mul]
            exact h_chain
      | compose_BC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,3,2) BC-AB-BC section (V outer=BC, V₃=AB, V₂=BC).
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            -- (4,3,2) BC-AB-BC: 3-real-gate natural chain. Pattern #5.
            have h_chain := sandwich_BC_AB_BC_to_4embed V₂ V₃ V
              u_pA u_pB u_pC uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV₂)
                (isUnitary4_kron2 hB₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pA hA₂) isUnitary2_one) hV₃)
                (isUnitary4_kron2 hA₃ hB₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₃) hV)
                (isUnitary4_kron2 hB hC),
              isUnitary4_kron2 hA isUnitary2_one, ?_⟩
            right; right; right; right; left
            exact h_chain
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AB-BC-AB-BC: V₁=AB, V₂=BC, V₃=AB, V outer=BC.
          -- Direct pattern #8 (AB-BC-AB-BC) match. Pattern E.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AB_BC_AB_BC_to_4embed V₁ V₂ V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV₁)
                (isUnitary4_kron2 hA₁ hB₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul h_pC hC₁)) hV₂)
                (isUnitary4_kron2 hB₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul (isUnitary4_kron2 hA₂ isUnitary2_one) hV₃)
                  (isUnitary4_kron2 hA₃ hB₃))
                (isUnitary4_kron2 hA isUnitary2_one),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₃) hV)
                (isUnitary4_kron2 hB hC), ?_⟩
            right; right; right; right; right; right; right; left
            exact h_chain
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) BC-BC-AB-BC: V₁=V₂=BC inner pair, V₃=AB, V outer=BC.
          -- Pattern D inner-pair-merge → (3,2,1) BC-AB-BC. Pattern #5.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_inner_merge :
                singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                  singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ =
                singleQubitLayer (u_pA * uA₁) u_pB u_pC *
                  embedBC (V₁ * (kron2 uB₁ uC₁ * V₂)) := by
              rw [show
                    singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                      singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedBC V₁ * singleQubitLayer uA₁ uB₁ uC₁ *
                        embedBC V₂) from by noncomm_ring]
              rw [embedBC_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                    (singleQubitLayer uA₁ I₂ I₂ *
                      embedBC (V₁ * (kron2 uB₁ uC₁ * V₂))) =
                  (singleQubitLayer u_pA u_pB u_pC *
                     singleQubitLayer uA₁ I₂ I₂) *
                    embedBC (V₁ * (kron2 uB₁ uC₁ * V₂))
                  from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂) *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_inner_merge]
            have h_chain := sandwich_BC_AB_BC_to_4embed
              (V₁ * (kron2 uB₁ uC₁ * V₂)) V₃ V
              (u_pA * uA₁) u_pB u_pC uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            have hV_merge : IsUnitary4 (V₁ * (kron2 uB₁ uC₁ * V₂)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hB₁ hC₁) hV₂)
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV_merge)
                (isUnitary4_kron2 hB₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul (isUnitary2_mul h_pA hA₁) hA₂)
                  isUnitary2_one) hV₃)
                (isUnitary4_kron2 hA₃ hB₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₃) hV)
                (isUnitary4_kron2 hB hC),
              isUnitary4_kron2 hA isUnitary2_one, ?_⟩
            right; right; right; right; left
            exact h_chain
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- AC-BC-AB-BC: gates 2,4 are BC; conjugating gate 3 turns AB into AC, giving pattern #9
          -- (AC-BC-AC-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_eq := (retype3_BC_AB_to_AC (embedAC V₁) V₂ V₃ V
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC).trans
              (sandwich_AC_BC_AC_BC_to_4embed V₁ (V₂ * SWAP_4) V₃ (SWAP_4 * V)
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uC₂ uB₂ uA₃ uC₃ uB₃ uA uB uC)
            refine ⟨_, _, _, _, ?_, ?_, ?_, ?_,
              Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h_eq)))))))⟩ <;> unitary_auto
      | compose_AC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- Gate slot 1 still undestructed: four sub-cases (none / AB / AC / BC).
        cases h1 with
        | weaken h0 =>
          -- 3-gate AC-AB-BC = pattern #1 with V₁ = 1.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_eq := sandwich_AC_AB_BC_to_4embed V₂ V₃ V
              u_pA u_pB u_pC uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _, ?_, ?_, ?_, ?_,
              Or.inl (pad_BC_one _ _ _ _ h_eq)⟩ <;> unitary_auto
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- AB-AC-AB-BC: gates 1,3 are AB; re-typing gate 2 gives pattern #8 (AB-BC-AB-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_eq := (retype2_AB_AC_to_BC (embedBC V) V₁ V₂ V₃
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC).trans
              (sandwich_AB_BC_AB_BC_to_4embed (V₁ * SWAP_4) V₂ (SWAP_4 * V₃) V
                u_pA u_pB u_pC uB₁ uA₁ uC₁ uB₂ uA₂ uC₂ uA₃ uB₃ uC₃ uA uB uC)
            refine ⟨_, _, _, _, ?_, ?_, ?_, ?_,
              Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_eq)))))))⟩ <;> unitary_auto
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- AC-AC-AB-BC: adjacent AC pair at slots (1,2) merges, leaving AC-AB-BC.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_eq := (merge12_AC V₁ V₂ (embedAB V₃) (embedBC V)
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC).trans
              (sandwich_AC_AB_BC_to_4embed (V₁ * (kron2 uA₁ uC₁ * V₂)) V₃ V
                u_pA (u_pB * uB₁) u_pC uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC)
            refine ⟨_, _, _, _, ?_, ?_, ?_, ?_,
              Or.inl (pad_BC_one _ _ _ _ h_eq)⟩ <;> unitary_auto
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- BC-AC-AB-BC is literally pattern #1.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_eq := sandwich_BC_AC_AB_BC_to_4embed V₁ V₂ V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _, ?_, ?_, ?_, ?_,
              Or.inl h_eq⟩ <;> unitary_auto
    | compose_BC V₃ hV₃ uA₃ uB₃ uC₃ hA₃ hB₃ hC₃ h2 =>
      -- (4,3) BC-BC consecutive same-XY merge. Pattern #9.
      cases h2 with
      | weaken h1 =>
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge :
              singleQubitLayer u_pA u_pB u_pC * embedBC V₃ *
                singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                singleQubitLayer uA uB uC =
              singleQubitLayer (u_pA * uA₃) u_pB u_pC *
                embedBC (V₃ * (kron2 uB₃ uC₃ * V)) *
                singleQubitLayer uA uB uC := by
              rw [show singleQubitLayer u_pA u_pB u_pC * embedBC V₃ *
                        singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                        singleQubitLayer uA uB uC =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedBC V₃ * singleQubitLayer uA₃ uB₃ uC₃ * embedBC V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedBC_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                        (singleQubitLayer uA₃ I₂ I₂ *
                          embedBC (V₃ * (kron2 uB₃ uC₃ * V))) *
                        singleQubitLayer uA uB uC =
                    (singleQubitLayer u_pA u_pB u_pC *
                       singleQubitLayer uA₃ I₂ I₂) *
                      embedBC (V₃ * (kron2 uB₃ uC₃ * V)) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₃ * (kron2 uB₃ uC₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hB₃ hC₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleBC_canonical (V₃ * (kron2 uB₃ uC₃ * V))
                hV_merged
                (u_pA * uA₃) u_pB u_pC (isUnitary2_mul h_pA hA₃) h_pB h_pC
                uA uB uC hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            rw [h_merge]
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,1) AB-BC-BC outer-pair-BC-merge: V₃ and V outer both BC.
          -- Pattern #8 (AB-BC-AB-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := outer_BC_pair_merge_sandwich (embedAB V₁) V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            have hV_merged : IsUnitary4 (V₃ * (kron2 uB₃ uC₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hB₃ hC₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_BC_at_3_2_canonical V₁
                (V₃ * (kron2 uB₃ uC₃ * V)) hV₁ hV_merged
                u_pA u_pB u_pC (uA₁ * uA₃) uB₁ uC₁ uA uB uC
                h_pA h_pB h_pC (isUnitary2_mul hA₁ hA₃) hB₁ hC₁ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,1) BC-BC-BC triple same-XY merge. Pattern #9.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have hV_merged : IsUnitary4
                (V₁ * (kron2 uB₁ uC₁ * V₃) * (kron2 uB₃ uC₃ * V)) :=
              isUnitary4_mul
                (isUnitary4_mul hV₁
                  (isUnitary4_mul (isUnitary4_kron2 hB₁ hC₁) hV₃))
                (isUnitary4_mul (isUnitary4_kron2 hB₃ hC₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleBC_canonical
                (V₁ * (kron2 uB₁ uC₁ * V₃) * (kron2 uB₃ uC₃ * V))
                hV_merged
                ((u_pA * uA₁) * uA₃) u_pB u_pC
                (isUnitary2_mul (isUnitary2_mul h_pA hA₁) hA₃) h_pB h_pC
                uA uB uC hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            rw [sandwich_BC_BC_BC_to_BC V₁ V₃ V
                  u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC]
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,1) AC-BC-BC outer-pair-BC-merge: V₃ and V outer both BC.
          -- Pattern #9 (AC-BC-AC-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := outer_BC_pair_merge_sandwich (embedAC V₁) V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            have hV_merged : IsUnitary4 (V₃ * (kron2 uB₃ uC₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hB₃ hC₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_BC_at_3_2_canonical V₁
                (V₃ * (kron2 uB₃ uC₃ * V)) hV₁ hV_merged
                u_pA u_pB u_pC (uA₁ * uA₃) uB₁ uC₁ uA uB uC
                h_pA h_pB h_pC (isUnitary2_mul hA₁ hA₃) hB₁ hC₁ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            rw [h_merge]
            exact h_eq
      | compose_AB V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,3,2) AB-BC-BC section (V outer=BC, V₃=BC, V₂=AB).
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            -- V₃,V_outer both BC outer pair → (3,2) AB-BC. Pattern #8.
            have h_outer_merge :
                singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                  singleQubitLayer uA uB uC =
                singleQubitLayer (uA₂ * uA₃) uB₂ uC₂ *
                  embedBC (V₃ * (kron2 uB₃ uC₃ * V)) *
                  singleQubitLayer uA uB uC := by
              rw [show
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                      singleQubitLayer uA uB uC =
                    singleQubitLayer uA₂ uB₂ uC₂ *
                      (embedBC V₃ * singleQubitLayer uA₃ uB₃ uC₃ *
                        embedBC V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedBC_merge]
              rw [show singleQubitLayer uA₂ uB₂ uC₂ *
                    (singleQubitLayer uA₃ I₂ I₂ *
                      embedBC (V₃ * (kron2 uB₃ uC₃ * V))) *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer uA₂ uB₂ uC₂ *
                     singleQubitLayer uA₃ I₂ I₂) *
                    embedBC (V₃ * (kron2 uB₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₂ *
                    (singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                      singleQubitLayer uA uB uC) from by noncomm_ring]
            rw [h_outer_merge]
            have hV_merged : IsUnitary4 (V₃ * (kron2 uB₃ uC₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hB₃ hC₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_BC_at_3_2_canonical V₂
                (V₃ * (kron2 uB₃ uC₃ * V)) hV₂ hV_merged
                u_pA u_pB u_pC (uA₂ * uA₃) uB₂ uC₂ uA uB uC
                h_pA h_pB h_pC (isUnitary2_mul hA₂ hA₃) hB₂ hC₂ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₂ *
                    (singleQubitLayer (uA₂ * uA₃) uB₂ uC₂ *
                      embedBC (V₃ * (kron2 uB₃ uC₃ * V)) *
                      singleQubitLayer uA uB uC) =
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₂ *
                    singleQubitLayer (uA₂ * uA₃) uB₂ uC₂ *
                    embedBC (V₃ * (kron2 uB₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AB-AB-BC-BC: V₁=V₂=AB inner pair, V₃=V outer=BC outer pair.
          -- Pattern F (both-pair-merge): merge both pairs, reduce to (3,2) AB-BC.
          -- Pattern #8 (AB-BC-AB-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_outer_merge :
                singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                  singleQubitLayer uA uB uC =
                singleQubitLayer (uA₂ * uA₃) uB₂ uC₂ *
                  embedBC (V₃ * (kron2 uB₃ uC₃ * V)) *
                  singleQubitLayer uA uB uC := by
              rw [show
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                      singleQubitLayer uA uB uC =
                    singleQubitLayer uA₂ uB₂ uC₂ *
                      (embedBC V₃ * singleQubitLayer uA₃ uB₃ uC₃ *
                        embedBC V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedBC_merge]
              rw [show singleQubitLayer uA₂ uB₂ uC₂ *
                    (singleQubitLayer uA₃ I₂ I₂ *
                      embedBC (V₃ * (kron2 uB₃ uC₃ * V))) *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer uA₂ uB₂ uC₂ *
                     singleQubitLayer uA₃ I₂ I₂) *
                    embedBC (V₃ * (kron2 uB₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have h_inner_merge :
                singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                  singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ =
                singleQubitLayer u_pA u_pB (u_pC * uC₁) *
                  embedAB (V₁ * (kron2 uA₁ uB₁ * V₂)) := by
              rw [show
                    singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                      singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAB V₁ * singleQubitLayer uA₁ uB₁ uC₁ *
                        embedAB V₂) from by noncomm_ring]
              rw [embedAB_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                    (singleQubitLayer I₂ I₂ uC₁ *
                      embedAB (V₁ * (kron2 uA₁ uB₁ * V₂))) =
                  (singleQubitLayer u_pA u_pB u_pC *
                     singleQubitLayer I₂ I₂ uC₁) *
                    embedAB (V₁ * (kron2 uA₁ uB₁ * V₂))
                  from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂) *
                    (singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                      singleQubitLayer uA uB uC) from by noncomm_ring]
            rw [h_inner_merge, h_outer_merge]
            have hV_inner : IsUnitary4 (V₁ * (kron2 uA₁ uB₁ * V₂)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hB₁) hV₂)
            have hV_outer : IsUnitary4 (V₃ * (kron2 uB₃ uC₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hB₃ hC₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_BC_at_3_2_canonical
                (V₁ * (kron2 uA₁ uB₁ * V₂))
                (V₃ * (kron2 uB₃ uC₃ * V))
                hV_inner hV_outer
                u_pA u_pB (u_pC * uC₁) (uA₂ * uA₃) uB₂ uC₂ uA uB uC
                h_pA h_pB (isUnitary2_mul h_pC hC₁)
                (isUnitary2_mul hA₂ hA₃) hB₂ hC₂ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            rw [show
                  singleQubitLayer u_pA u_pB (u_pC * uC₁) *
                    embedAB (V₁ * (kron2 uA₁ uB₁ * V₂)) *
                    (singleQubitLayer (uA₂ * uA₃) uB₂ uC₂ *
                      embedBC (V₃ * (kron2 uB₃ uC₃ * V)) *
                      singleQubitLayer uA uB uC) =
                  singleQubitLayer u_pA u_pB (u_pC * uC₁) *
                    embedAB (V₁ * (kron2 uA₁ uB₁ * V₂)) *
                    singleQubitLayer (uA₂ * uA₃) uB₂ uC₂ *
                    embedBC (V₃ * (kron2 uB₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) BC-AB-BC-BC: V₁=BC, V₂=AB, V₃=V outer=BC outer pair.
          -- Pattern B outer-pair-merge → (3,2,1) BC-AB-BC. Pattern #5.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_outer_merge :
                singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                  singleQubitLayer uA uB uC =
                singleQubitLayer (uA₂ * uA₃) uB₂ uC₂ *
                  embedBC (V₃ * (kron2 uB₃ uC₃ * V)) *
                  singleQubitLayer uA uB uC := by
              rw [show
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                      singleQubitLayer uA uB uC =
                    singleQubitLayer uA₂ uB₂ uC₂ *
                      (embedBC V₃ * singleQubitLayer uA₃ uB₃ uC₃ *
                        embedBC V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedBC_merge]
              rw [show singleQubitLayer uA₂ uB₂ uC₂ *
                    (singleQubitLayer uA₃ I₂ I₂ *
                      embedBC (V₃ * (kron2 uB₃ uC₃ * V))) *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer uA₂ uB₂ uC₂ *
                     singleQubitLayer uA₃ I₂ I₂) *
                    embedBC (V₃ * (kron2 uB₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                    (singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                      singleQubitLayer uA uB uC) from by noncomm_ring]
            rw [h_outer_merge]
            have h_chain := sandwich_BC_AB_BC_to_4embed V₁ V₂
              (V₃ * (kron2 uB₃ uC₃ * V))
              u_pA u_pB u_pC uA₁ uB₁ uC₁ (uA₂ * uA₃) uB₂ uC₂ uA uB uC
            have hV_merge : IsUnitary4 (V₃ * (kron2 uB₃ uC₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hB₃ hC₃) hV)
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV₁)
                (isUnitary4_kron2 hB₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pA hA₁) isUnitary2_one) hV₂)
                (isUnitary4_kron2 (isUnitary2_mul hA₂ hA₃) hB₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₂) hV_merge)
                (isUnitary4_kron2 hB hC),
              isUnitary4_kron2 hA isUnitary2_one, ?_⟩
            right; right; right; right; left
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                    (singleQubitLayer (uA₂ * uA₃) uB₂ uC₂ *
                      embedBC (V₃ * (kron2 uB₃ uC₃ * V)) *
                      singleQubitLayer uA uB uC) =
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                    singleQubitLayer (uA₂ * uA₃) uB₂ uC₂ *
                    embedBC (V₃ * (kron2 uB₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_chain
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- AC-AB-BC-BC: adjacent BC pair at slots (3,4) merges, leaving
          -- AC-AB-BC = pattern #1 (BC-AC-AB-BC) with V₁ = 1.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have hW : IsUnitary4 (V₃ * (kron2 uB₃ uC₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hB₃ hC₃) hV)
            have h_merge := merge34_BC (embedAC V₁) (embedAB V₂) V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            have h_chain := sandwich_AC_AB_BC_to_4embed V₁ V₂
              (V₃ * (kron2 uB₃ uC₃ * V))
              u_pA u_pB u_pC uA₁ uB₁ uC₁ (uA₂ * uA₃) uB₂ uC₂ uA uB uC
            refine ⟨1, _, _, _,
              isUnitary4_one,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV₁)
                (isUnitary4_kron2 hA₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul
                    (isUnitary4_kron2 isUnitary2_one (isUnitary2_mul h_pB hB₁))
                    hV₂)
                  (isUnitary4_kron2 (isUnitary2_mul hA₂ hA₃) hB₂))
                (isUnitary4_kron2 hA isUnitary2_one),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₂) hW)
                (isUnitary4_kron2 hB hC), ?_⟩
            left
            rw [h_merge, embedBC_one, one_mul]
            exact h_chain
      | compose_BC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,3,2) BC-BC-BC triple same-XY merge. Pattern #9.
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have hV_merged : IsUnitary4
                (V₂ * (kron2 uB₂ uC₂ * V₃) * (kron2 uB₃ uC₃ * V)) :=
              isUnitary4_mul
                (isUnitary4_mul hV₂
                  (isUnitary4_mul (isUnitary4_kron2 hB₂ hC₂) hV₃))
                (isUnitary4_mul (isUnitary4_kron2 hB₃ hC₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleBC_canonical
                (V₂ * (kron2 uB₂ uC₂ * V₃) * (kron2 uB₃ uC₃ * V))
                hV_merged
                ((u_pA * uA₂) * uA₃) u_pB u_pC
                (isUnitary2_mul (isUnitary2_mul h_pA hA₂) hA₃) h_pB h_pC
                uA uB uC hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            rw [sandwich_BC_BC_BC_to_BC V₂ V₃ V
                  u_pA u_pB u_pC uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC]
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AB-BC-BC-BC: V₁=AB, V₂=V₃=V=BC. Merge outer 3 BCs.
          -- Pattern #8 (AB-BC-AB-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge_inner :
                singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                  singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                  singleQubitLayer uA uB uC =
                singleQubitLayer ((uA₁ * uA₂) * uA₃) uB₁ uC₁ *
                  embedBC (V₂ * (kron2 uB₂ uC₂ * V₃) *
                    (kron2 uB₃ uC₃ * V)) *
                  singleQubitLayer uA uB uC :=
              sandwich_BC_BC_BC_to_BC V₂ V₃ V
                uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    (singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                      singleQubitLayer uA uB uC) from by noncomm_ring]
            rw [h_merge_inner]
            have hV_merged : IsUnitary4
                (V₂ * (kron2 uB₂ uC₂ * V₃) * (kron2 uB₃ uC₃ * V)) :=
              isUnitary4_mul
                (isUnitary4_mul hV₂
                  (isUnitary4_mul (isUnitary4_kron2 hB₂ hC₂) hV₃))
                (isUnitary4_mul (isUnitary4_kron2 hB₃ hC₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_BC_at_3_2_canonical V₁
                (V₂ * (kron2 uB₂ uC₂ * V₃) * (kron2 uB₃ uC₃ * V))
                hV₁ hV_merged
                u_pA u_pB u_pC ((uA₁ * uA₂) * uA₃) uB₁ uC₁ uA uB uC
                h_pA h_pB h_pC
                (isUnitary2_mul (isUnitary2_mul hA₁ hA₂) hA₃) hB₁ hC₁
                hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; left
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    (singleQubitLayer ((uA₁ * uA₂) * uA₃) uB₁ uC₁ *
                      embedBC (V₂ * (kron2 uB₂ uC₂ * V₃) *
                        (kron2 uB₃ uC₃ * V)) *
                      singleQubitLayer uA uB uC) =
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer ((uA₁ * uA₂) * uA₃) uB₁ uC₁ *
                    embedBC (V₂ * (kron2 uB₂ uC₂ * V₃) *
                      (kron2 uB₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) BC-BC-BC-BC: all 4 gates BC, full 4-way merge.
          -- Pattern #9 (AC-BC-AC-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have hV_merged : IsUnitary4
                (V₁ * (kron2 uB₁ uC₁ * V₂) * (kron2 uB₂ uC₂ * V₃) *
                  (kron2 uB₃ uC₃ * V)) :=
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul hV₁
                    (isUnitary4_mul (isUnitary4_kron2 hB₁ hC₁) hV₂))
                  (isUnitary4_mul (isUnitary4_kron2 hB₂ hC₂) hV₃))
                (isUnitary4_mul (isUnitary4_kron2 hB₃ hC₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleBC_canonical
                (V₁ * (kron2 uB₁ uC₁ * V₂) * (kron2 uB₂ uC₂ * V₃) *
                  (kron2 uB₃ uC₃ * V))
                hV_merged
                (((u_pA * uA₁) * uA₂) * uA₃) u_pB u_pC
                (isUnitary2_mul
                  (isUnitary2_mul (isUnitary2_mul h_pA hA₁) hA₂) hA₃)
                h_pB h_pC
                uA uB uC hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            rw [sandwich_BC_BC_BC_BC_to_BC V₁ V₂ V₃ V
                  u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃
                  uA uB uC]
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AC-BC-BC-BC: V₁=AC, V₂=V₃=V=BC. Merge outer 3 BCs.
          -- Pattern #9 (AC-BC-AC-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge_inner :
                singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                  singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                  singleQubitLayer uA uB uC =
                singleQubitLayer ((uA₁ * uA₂) * uA₃) uB₁ uC₁ *
                  embedBC (V₂ * (kron2 uB₂ uC₂ * V₃) *
                    (kron2 uB₃ uC₃ * V)) *
                  singleQubitLayer uA uB uC :=
              sandwich_BC_BC_BC_to_BC V₂ V₃ V
                uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    (singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                      singleQubitLayer uA uB uC) from by noncomm_ring]
            rw [h_merge_inner]
            have hV_merged : IsUnitary4
                (V₂ * (kron2 uB₂ uC₂ * V₃) * (kron2 uB₃ uC₃ * V)) :=
              isUnitary4_mul
                (isUnitary4_mul hV₂
                  (isUnitary4_mul (isUnitary4_kron2 hB₂ hC₂) hV₃))
                (isUnitary4_mul (isUnitary4_kron2 hB₃ hC₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_BC_at_3_2_canonical V₁
                (V₂ * (kron2 uB₂ uC₂ * V₃) * (kron2 uB₃ uC₃ * V))
                hV₁ hV_merged
                u_pA u_pB u_pC ((uA₁ * uA₂) * uA₃) uB₁ uC₁ uA uB uC
                h_pA h_pB h_pC
                (isUnitary2_mul (isUnitary2_mul hA₁ hA₂) hA₃) hB₁ hC₁
                hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    (singleQubitLayer ((uA₁ * uA₂) * uA₃) uB₁ uC₁ *
                      embedBC (V₂ * (kron2 uB₂ uC₂ * V₃) *
                        (kron2 uB₃ uC₃ * V)) *
                      singleQubitLayer uA uB uC) =
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer ((uA₁ * uA₂) * uA₃) uB₁ uC₁ *
                    embedBC (V₂ * (kron2 uB₂ uC₂ * V₃) *
                      (kron2 uB₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_eq
      | compose_AC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,3,2) AC-BC-BC section (V outer=BC, V₃=BC, V₂=AC).
        -- V₃=V=BC consecutive outer pair → merge.
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            -- (4,3,2) AC-BC-BC: merge V₃,V (both BC) → (3,2) AC-BC chain.
            -- Pattern #9 (AC-BC-AC-BC).
            have h_merge :
                singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                  singleQubitLayer uA uB uC =
                singleQubitLayer (uA₂ * uA₃) uB₂ uC₂ *
                  embedBC (V₃ * (kron2 uB₃ uC₃ * V)) *
                  singleQubitLayer uA uB uC := by
              rw [show
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                      singleQubitLayer uA uB uC =
                    singleQubitLayer uA₂ uB₂ uC₂ *
                      (embedBC V₃ * singleQubitLayer uA₃ uB₃ uC₃ *
                        embedBC V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedBC_merge]
              rw [show singleQubitLayer uA₂ uB₂ uC₂ *
                    (singleQubitLayer uA₃ I₂ I₂ *
                      embedBC (V₃ * (kron2 uB₃ uC₃ * V))) *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer uA₂ uB₂ uC₂ *
                     singleQubitLayer uA₃ I₂ I₂) *
                    embedBC (V₃ * (kron2 uB₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₃ * (kron2 uB₃ uC₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hB₃ hC₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_BC_at_3_2_canonical V₂
                (V₃ * (kron2 uB₃ uC₃ * V)) hV₂ hV_merged
                u_pA u_pB u_pC (uA₂ * uA₃) uB₂ uC₂ uA uB uC
                h_pA h_pB h_pC (isUnitary2_mul hA₂ hA₃) hB₂ hC₂ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₂ *
                    (singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                      singleQubitLayer uA uB uC) from by noncomm_ring]
            rw [h_merge]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₂ *
                    (singleQubitLayer (uA₂ * uA₃) uB₂ uC₂ *
                      embedBC (V₃ * (kron2 uB₃ uC₃ * V)) *
                      singleQubitLayer uA uB uC) =
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₂ *
                    singleQubitLayer (uA₂ * uA₃) uB₂ uC₂ *
                    embedBC (V₃ * (kron2 uB₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- AB-AC-BC-BC: adjacent BC pair at slots (3,4) merges, leaving
          -- AB-AC-BC = pattern #1 (BC-AC-AB-BC) with V₁ = SWAP_4.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have hW : IsUnitary4 (V₃ * (kron2 uB₃ uC₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hB₃ hC₃) hV)
            have h_merge := merge34_BC (embedAB V₁) (embedAC V₂) V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            have h_chain := sandwich_AB_AC_BC_to_4embed V₁ V₂
              (V₃ * (kron2 uB₃ uC₃ * V))
              u_pA u_pB u_pC uA₁ uB₁ uC₁ (uA₂ * uA₃) uB₂ uC₂ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_SWAP_4,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV₁)
                (isUnitary4_kron2 hA₁ hB₁),
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul
                    (isUnitary4_kron2 isUnitary2_one (isUnitary2_mul h_pC hC₁))
                    hV₂)
                  (isUnitary4_kron2 (isUnitary2_mul hA₂ hA₃) hC₂))
                (isUnitary4_kron2 hA isUnitary2_one),
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hB₂)
                    (isUnitary4_swap4_conj _ hW))
                  (isUnitary4_kron2 hC hB))
                isUnitary4_SWAP_4, ?_⟩
            left
            rw [h_merge]
            exact h_chain
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) BC-AC-BC-BC: V₁=BC, V₂=AC, V₃=V outer=BC outer pair.
          -- Pattern B outer-pair-merge → (3,2,1) BC-AC-BC. Pattern #6.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_outer_merge :
                singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                  singleQubitLayer uA uB uC =
                singleQubitLayer (uA₂ * uA₃) uB₂ uC₂ *
                  embedBC (V₃ * (kron2 uB₃ uC₃ * V)) *
                  singleQubitLayer uA uB uC := by
              rw [show
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                      singleQubitLayer uA uB uC =
                    singleQubitLayer uA₂ uB₂ uC₂ *
                      (embedBC V₃ * singleQubitLayer uA₃ uB₃ uC₃ *
                        embedBC V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedBC_merge]
              rw [show singleQubitLayer uA₂ uB₂ uC₂ *
                    (singleQubitLayer uA₃ I₂ I₂ *
                      embedBC (V₃ * (kron2 uB₃ uC₃ * V))) *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer uA₂ uB₂ uC₂ *
                     singleQubitLayer uA₃ I₂ I₂) *
                    embedBC (V₃ * (kron2 uB₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                    (singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                      singleQubitLayer uA uB uC) from by noncomm_ring]
            rw [h_outer_merge]
            have h_chain := sandwich_BC_AC_BC_to_4embed V₁ V₂
              (V₃ * (kron2 uB₃ uC₃ * V))
              u_pA u_pB u_pC uA₁ uB₁ uC₁ (uA₂ * uA₃) uB₂ uC₂ uA uB uC
            have hV_merge : IsUnitary4 (V₃ * (kron2 uB₃ uC₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hB₃ hC₃) hV)
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV₁)
                (isUnitary4_kron2 hB₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pA hA₁) isUnitary2_one) hV₂)
                (isUnitary4_kron2 (isUnitary2_mul hA₂ hA₃) hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hB₂ isUnitary2_one) hV_merge)
                (isUnitary4_kron2 hB hC),
              isUnitary4_kron2 hA isUnitary2_one, ?_⟩
            right; right; right; right; right; left
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                    (singleQubitLayer (uA₂ * uA₃) uB₂ uC₂ *
                      embedBC (V₃ * (kron2 uB₃ uC₃ * V)) *
                      singleQubitLayer uA uB uC) =
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                    singleQubitLayer (uA₂ * uA₃) uB₂ uC₂ *
                    embedBC (V₃ * (kron2 uB₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_chain
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AC-AC-BC-BC: V₁=V₂=AC inner pair, V₃=V outer=BC outer pair.
          -- Pattern F (both-pair-merge): merge both pairs, reduce to (3,2) AC-BC.
          -- Pattern #9 (AC-BC-AC-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_outer_merge :
                singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                  singleQubitLayer uA uB uC =
                singleQubitLayer (uA₂ * uA₃) uB₂ uC₂ *
                  embedBC (V₃ * (kron2 uB₃ uC₃ * V)) *
                  singleQubitLayer uA uB uC := by
              rw [show
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                      singleQubitLayer uA uB uC =
                    singleQubitLayer uA₂ uB₂ uC₂ *
                      (embedBC V₃ * singleQubitLayer uA₃ uB₃ uC₃ *
                        embedBC V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedBC_merge]
              rw [show singleQubitLayer uA₂ uB₂ uC₂ *
                    (singleQubitLayer uA₃ I₂ I₂ *
                      embedBC (V₃ * (kron2 uB₃ uC₃ * V))) *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer uA₂ uB₂ uC₂ *
                     singleQubitLayer uA₃ I₂ I₂) *
                    embedBC (V₃ * (kron2 uB₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have h_inner_merge :
                singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                  singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ =
                singleQubitLayer u_pA (u_pB * uB₁) u_pC *
                  embedAC (V₁ * (kron2 uA₁ uC₁ * V₂)) := by
              rw [show
                    singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                      singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAC V₁ * singleQubitLayer uA₁ uB₁ uC₁ *
                        embedAC V₂) from by noncomm_ring]
              rw [embedAC_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                    (singleQubitLayer I₂ uB₁ I₂ *
                      embedAC (V₁ * (kron2 uA₁ uC₁ * V₂))) =
                  (singleQubitLayer u_pA u_pB u_pC *
                     singleQubitLayer I₂ uB₁ I₂) *
                    embedAC (V₁ * (kron2 uA₁ uC₁ * V₂))
                  from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂) *
                    (singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                      singleQubitLayer uA uB uC) from by noncomm_ring]
            rw [h_inner_merge, h_outer_merge]
            have hV_inner : IsUnitary4 (V₁ * (kron2 uA₁ uC₁ * V₂)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hC₁) hV₂)
            have hV_outer : IsUnitary4 (V₃ * (kron2 uB₃ uC₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hB₃ hC₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_BC_at_3_2_canonical
                (V₁ * (kron2 uA₁ uC₁ * V₂))
                (V₃ * (kron2 uB₃ uC₃ * V))
                hV_inner hV_outer
                u_pA (u_pB * uB₁) u_pC (uA₂ * uA₃) uB₂ uC₂ uA uB uC
                h_pA (isUnitary2_mul h_pB hB₁) h_pC
                (isUnitary2_mul hA₂ hA₃) hB₂ hC₂ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            rw [show
                  singleQubitLayer u_pA (u_pB * uB₁) u_pC *
                    embedAC (V₁ * (kron2 uA₁ uC₁ * V₂)) *
                    (singleQubitLayer (uA₂ * uA₃) uB₂ uC₂ *
                      embedBC (V₃ * (kron2 uB₃ uC₃ * V)) *
                      singleQubitLayer uA uB uC) =
                  singleQubitLayer u_pA (u_pB * uB₁) u_pC *
                    embedAC (V₁ * (kron2 uA₁ uC₁ * V₂)) *
                    singleQubitLayer (uA₂ * uA₃) uB₂ uC₂ *
                    embedBC (V₃ * (kron2 uB₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_eq
    | compose_AC V₃ hV₃ uA₃ uB₃ uC₃ hA₃ hB₃ hC₃ h2 =>
      -- (4,3) outer BC inner AC. Pattern #9 (AC-BC-AC-BC).
      cases h2 with
      | weaken h1 =>
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_BC_at_3_2_canonical V₃ V hV₃ hV
                u_pA u_pB u_pC uA₃ uB₃ uC₃ uA uB uC
                h_pA h_pB h_pC hA₃ hB₃ hC₃ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,1) AB-AC-BC all-different. Pattern #1 (BC-AC-AB-BC), V₁ = SWAP_4.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AB_AC_BC_to_4embed V₁ V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_SWAP_4,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV₁)
                (isUnitary4_kron2 hA₁ hB₁),
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul
                    (isUnitary4_kron2 isUnitary2_one (isUnitary2_mul h_pC hC₁))
                    hV₃)
                  (isUnitary4_kron2 hA₃ hC₃))
                (isUnitary4_kron2 hA isUnitary2_one),
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hB₃)
                    (isUnitary4_swap4_conj V hV))
                  (isUnitary4_kron2 hC hB))
                isUnitary4_SWAP_4, ?_⟩
            left
            exact h_chain
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,1) BC-AC-BC non-adjacent-same: V₁ and V outer both BC.
          -- Pattern #6 (BC-AC-BC-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_BC_AC_BC_to_4embed V₁ V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV₁)
                (isUnitary4_kron2 hB₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pA hA₁) isUnitary2_one) hV₃)
                (isUnitary4_kron2 hA₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hB₃ isUnitary2_one) hV)
                (isUnitary4_kron2 hB hC),
              isUnitary4_kron2 hA isUnitary2_one, ?_⟩
            right; right; right; right; right; left
            exact h_chain
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,1) AC-AC-BC inner-pair-merge: V₁ and V₃ both AC.
          -- Pattern #9 (AC-BC-AC-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := inner_AC_pair_merge_sandwich V₁ V₃ (embedBC V)
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            have hV_merged : IsUnitary4 (V₁ * (kron2 uA₁ uC₁ * V₃)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hC₁) hV₃)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_BC_at_3_2_canonical
                (V₁ * (kron2 uA₁ uC₁ * V₃)) V hV_merged hV
                u_pA (u_pB * uB₁) u_pC uA₃ uB₃ uC₃ uA uB uC
                h_pA (isUnitary2_mul h_pB hB₁) h_pC hA₃ hB₃ hC₃ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            rw [h_merge]
            exact h_eq
      | compose_AB V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- Gate slot 1 still undestructed: four sub-cases (none / AB / AC / BC).
        cases h1 with
        | weaken h0 =>
          -- 3-gate AB-AC-BC = pattern #1 with V₁ = SWAP_4.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_eq := sandwich_AB_AC_BC_to_4embed V₂ V₃ V
              u_pA u_pB u_pC uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _, ?_, ?_, ?_, ?_,
              Or.inl h_eq⟩ <;> unitary_auto
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- AB-AB-AC-BC: adjacent AB pair at slots (1,2) merges, leaving AB-AC-BC.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_eq := (merge12_AB V₁ V₂ (embedAC V₃) (embedBC V)
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC).trans
              (sandwich_AB_AC_BC_to_4embed (V₁ * (kron2 uA₁ uB₁ * V₂)) V₃ V
                u_pA u_pB (u_pC * uC₁) uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC)
            refine ⟨_, _, _, _, ?_, ?_, ?_, ?_,
              Or.inl h_eq⟩ <;> unitary_auto
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- AC-AB-AC-BC: gates 1,3 are AC; re-typing gate 2 gives pattern #9 (AC-BC-AC-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_eq := (retype2_AC_AB_to_BC (embedBC V) V₁ V₂ V₃
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC).trans
              (sandwich_AC_BC_AC_BC_to_4embed (V₁ * SWAP_4) (SWAP_4 * V₂ * SWAP_4)
                (SWAP_4 * V₃) V
                u_pA u_pB u_pC uC₁ uB₁ uA₁ uC₂ uB₂ uA₂ uA₃ uB₃ uC₃ uA uB uC)
            refine ⟨_, _, _, _, ?_, ?_, ?_, ?_,
              Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h_eq)))))))⟩ <;> unitary_auto
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- BC-AB-AC-BC: gates 1,4 are BC; re-typing the middle block gives pattern #1.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_eq := (retype23_BC V₁ V₂ V₃ V
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC).trans
              (sandwich_BC_AC_AB_BC_to_4embed (V₁ * SWAP_4) V₂ V₃ (SWAP_4 * V)
                u_pA u_pB u_pC uA₁ uC₁ uB₁ uA₂ uC₂ uB₂ uA₃ uC₃ uB₃ uA uB uC)
            refine ⟨_, _, _, _, ?_, ?_, ?_, ?_,
              Or.inl h_eq⟩ <;> unitary_auto
      | compose_BC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,3,2) BC-AC-BC section (V outer=BC, V₃=AC, V₂=BC).
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            -- (4,3,2) BC-AC-BC: 3-real-gate natural chain. Pattern #6.
            have h_chain := sandwich_BC_AC_BC_to_4embed V₂ V₃ V
              u_pA u_pB u_pC uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV₂)
                (isUnitary4_kron2 hB₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pA hA₂) isUnitary2_one) hV₃)
                (isUnitary4_kron2 hA₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hB₃ isUnitary2_one) hV)
                (isUnitary4_kron2 hB hC),
              isUnitary4_kron2 hA isUnitary2_one, ?_⟩
            right; right; right; right; right; left
            exact h_chain
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- AB-BC-AC-BC: gates 2,4 are BC; conjugating gate 3 turns AC into AB, giving pattern #8
          -- (AB-BC-AB-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_eq := (retype3_BC_AC_to_AB (embedAB V₁) V₂ V₃ V
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC).trans
              (sandwich_AB_BC_AB_BC_to_4embed V₁ (V₂ * SWAP_4) V₃ (SWAP_4 * V)
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uC₂ uB₂ uA₃ uC₃ uB₃ uA uB uC)
            refine ⟨_, _, _, _, ?_, ?_, ?_, ?_,
              Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_eq)))))))⟩ <;> unitary_auto
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) BC-BC-AC-BC: V₁=V₂=BC inner pair, V₃=AC, V outer=BC.
          -- Pattern D inner-pair-merge → (3,2,1) BC-AC-BC. Pattern #6.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_inner_merge :
                singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                  singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ =
                singleQubitLayer (u_pA * uA₁) u_pB u_pC *
                  embedBC (V₁ * (kron2 uB₁ uC₁ * V₂)) := by
              rw [show
                    singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                      singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedBC V₁ * singleQubitLayer uA₁ uB₁ uC₁ *
                        embedBC V₂) from by noncomm_ring]
              rw [embedBC_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                    (singleQubitLayer uA₁ I₂ I₂ *
                      embedBC (V₁ * (kron2 uB₁ uC₁ * V₂))) =
                  (singleQubitLayer u_pA u_pB u_pC *
                     singleQubitLayer uA₁ I₂ I₂) *
                    embedBC (V₁ * (kron2 uB₁ uC₁ * V₂))
                  from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂) *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_inner_merge]
            have h_chain := sandwich_BC_AC_BC_to_4embed
              (V₁ * (kron2 uB₁ uC₁ * V₂)) V₃ V
              (u_pA * uA₁) u_pB u_pC uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            have hV_merge : IsUnitary4 (V₁ * (kron2 uB₁ uC₁ * V₂)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hB₁ hC₁) hV₂)
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV_merge)
                (isUnitary4_kron2 hB₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul (isUnitary2_mul h_pA hA₁) hA₂)
                  isUnitary2_one) hV₃)
                (isUnitary4_kron2 hA₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hB₃ isUnitary2_one) hV)
                (isUnitary4_kron2 hB hC),
              isUnitary4_kron2 hA isUnitary2_one, ?_⟩
            right; right; right; right; right; left
            exact h_chain
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AC-BC-AC-BC: V₁=AC, V₂=BC, V₃=AC, V outer=BC.
          -- Direct pattern #9 (AC-BC-AC-BC) match. Pattern E.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AC_BC_AC_BC_to_4embed V₁ V₂ V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV₁)
                (isUnitary4_kron2 hA₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pB hB₁) isUnitary2_one) hV₂)
                (isUnitary4_kron2 hB₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul (isUnitary4_kron2 hA₂ isUnitary2_one) hV₃)
                  (isUnitary4_kron2 hA₃ hC₃))
                (isUnitary4_kron2 hA isUnitary2_one),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hB₃ isUnitary2_one) hV)
                (isUnitary4_kron2 hB hC), ?_⟩
            right; right; right; right; right; right; right; right
            exact h_chain
      | compose_AC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,3,2) AC-AC-BC section (V outer=BC, V₃=AC, V₂=AC).
        -- V₂=V₃=AC consecutive adjacent same-XY merge.
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            -- (4,3,2) AC-AC-BC: merge V₂,V₃ (both AC) → (3,2) AC-BC chain.
            -- Pattern #9 (AC-BC-AC-BC).
            have h_merge :
                singleQubitLayer u_pA u_pB u_pC * embedAC V₂ *
                  singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ =
                singleQubitLayer u_pA (u_pB * uB₂) u_pC *
                  embedAC (V₂ * (kron2 uA₂ uC₂ * V₃)) *
                  singleQubitLayer uA₃ uB₃ uC₃ := by
              rw [show
                    singleQubitLayer u_pA u_pB u_pC * embedAC V₂ *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAC V₂ * singleQubitLayer uA₂ uB₂ uC₂ *
                        embedAC V₃) *
                      singleQubitLayer uA₃ uB₃ uC₃ from by noncomm_ring]
              rw [embedAC_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                    (singleQubitLayer I₂ uB₂ I₂ *
                      embedAC (V₂ * (kron2 uA₂ uC₂ * V₃))) *
                    singleQubitLayer uA₃ uB₃ uC₃ =
                  (singleQubitLayer u_pA u_pB u_pC *
                     singleQubitLayer I₂ uB₂ I₂) *
                    embedAC (V₂ * (kron2 uA₂ uC₂ * V₃)) *
                    singleQubitLayer uA₃ uB₃ uC₃ from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₂ * (kron2 uA₂ uC₂ * V₃)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hA₂ hC₂) hV₃)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_BC_at_3_2_canonical
                (V₂ * (kron2 uA₂ uC₂ * V₃)) V hV_merged hV
                u_pA (u_pB * uB₂) u_pC uA₃ uB₃ uC₃ uA uB uC
                h_pA (isUnitary2_mul h_pB hB₂) h_pC hA₃ hB₃ hC₃ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer u_pA u_pB u_pC * embedAC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃) *
                    embedBC V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_merge]
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- AB-AC-AC-BC: adjacent AC pair at slots (2,3) merges, leaving
          -- AB-AC-BC = pattern #1 (BC-AC-AB-BC) with V₁ = SWAP_4.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have hW : IsUnitary4 (V₂ * (kron2 uA₂ uC₂ * V₃)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hA₂ hC₂) hV₃)
            have h_merge := merge23_AC (embedAB V₁) (embedBC V) V₂ V₃
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            have h_chain := sandwich_AB_AC_BC_to_4embed V₁
              (V₂ * (kron2 uA₂ uC₂ * V₃)) V
              u_pA u_pB u_pC uA₁ (uB₁ * uB₂) uC₁ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_SWAP_4,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV₁)
                (isUnitary4_kron2 hA₁ (isUnitary2_mul hB₁ hB₂)),
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul
                    (isUnitary4_kron2 isUnitary2_one (isUnitary2_mul h_pC hC₁))
                    hW)
                  (isUnitary4_kron2 hA₃ hC₃))
                (isUnitary4_kron2 hA isUnitary2_one),
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hB₃)
                    (isUnitary4_swap4_conj V hV))
                  (isUnitary4_kron2 hC hB))
                isUnitary4_SWAP_4, ?_⟩
            left
            rw [h_merge]
            exact h_chain
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) BC-AC-AC-BC: V₁=BC, V₂=V₃=AC middle pair, V outer=BC.
          -- Pattern C middle-pair-merge → (3,2,1) BC-AC-BC. Pattern #6.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_middle_merge :
                singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                  singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ =
                singleQubitLayer uA₁ (uB₁ * uB₂) uC₁ *
                  embedAC (V₂ * (kron2 uA₂ uC₂ * V₃)) := by
              rw [show
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ =
                    singleQubitLayer uA₁ uB₁ uC₁ *
                      (embedAC V₂ * singleQubitLayer uA₂ uB₂ uC₂ *
                        embedAC V₃) from by noncomm_ring]
              rw [embedAC_merge]
              rw [show singleQubitLayer uA₁ uB₁ uC₁ *
                    (singleQubitLayer I₂ uB₂ I₂ *
                      embedAC (V₂ * (kron2 uA₂ uC₂ * V₃))) =
                  (singleQubitLayer uA₁ uB₁ uC₁ *
                     singleQubitLayer I₂ uB₂ I₂) *
                    embedAC (V₂ * (kron2 uA₂ uC₂ * V₃))
                  from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    (singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃) *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_middle_merge]
            have h_chain := sandwich_BC_AC_BC_to_4embed V₁
              (V₂ * (kron2 uA₂ uC₂ * V₃)) V
              u_pA u_pB u_pC uA₁ (uB₁ * uB₂) uC₁ uA₃ uB₃ uC₃ uA uB uC
            have hV_merge : IsUnitary4 (V₂ * (kron2 uA₂ uC₂ * V₃)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hA₂ hC₂) hV₃)
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV₁)
                (isUnitary4_kron2 (isUnitary2_mul hB₁ hB₂) hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pA hA₁) isUnitary2_one) hV_merge)
                (isUnitary4_kron2 hA₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hB₃ isUnitary2_one) hV)
                (isUnitary4_kron2 hB hC),
              isUnitary4_kron2 hA isUnitary2_one, ?_⟩
            right; right; right; right; right; left
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    (singleQubitLayer uA₁ (uB₁ * uB₂) uC₁ *
                      embedAC (V₂ * (kron2 uA₂ uC₂ * V₃))) *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ (uB₁ * uB₂) uC₁ *
                    embedAC (V₂ * (kron2 uA₂ uC₂ * V₃)) *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_chain
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AC-AC-AC-BC: V₁=V₂=V₃=AC inner three, V outer=BC.
          -- Pattern G inner-3-merge → (3,1) AC-BC chain. Pattern #9.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_inner_merge :
                singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                  singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                  singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ =
                singleQubitLayer u_pA (((u_pB * uB₁) * uB₂)) u_pC *
                  embedAC (V₁ * (kron2 uA₁ uC₁ * V₂) *
                    (kron2 uA₂ uC₂ * V₃)) *
                  singleQubitLayer uA₃ uB₃ uC₃ :=
              sandwich_AC_AC_AC_to_AC V₁ V₂ V₃
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedBC V *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃) *
                    embedBC V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_inner_merge]
            have hV_merge : IsUnitary4
                (V₁ * (kron2 uA₁ uC₁ * V₂) * (kron2 uA₂ uC₂ * V₃)) :=
              isUnitary4_mul
                (isUnitary4_mul hV₁
                  (isUnitary4_mul (isUnitary4_kron2 hA₁ hC₁) hV₂))
                (isUnitary4_mul (isUnitary4_kron2 hA₂ hC₂) hV₃)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AC_BC_at_3_2_canonical
                (V₁ * (kron2 uA₁ uC₁ * V₂) * (kron2 uA₂ uC₂ * V₃)) V
                hV_merge hV
                u_pA ((u_pB * uB₁) * uB₂) u_pC uA₃ uB₃ uC₃ uA uB uC
                h_pA (isUnitary2_mul (isUnitary2_mul h_pB hB₁) hB₂) h_pC
                hA₃ hB₃ hC₃ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; right; right
            exact h_eq
  | compose_AC V hV uA uB uC hA hB hC h3 =>
    -- Position-4 AC outer.
    cases h3 with
    | weaken h2 =>
      cases h2 with
      | weaken h1 =>
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁, V₂, V₃, V₄', hV₁, hV₂, hV₃, hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleAC_canonical V hV
                u_pA u_pB u_pC h_pA h_pB h_pC uA uB uC hA hB hC
            refine ⟨V₁, V₂, V₃, V₄', hV₁, hV₂, hV₃, hV₄', ?_⟩
            right; right; right; right; right; right; left
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,1) outer AC inner AB. Pattern #7 (AB-AC-AB-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_AC_at_3_2_canonical V₁ V hV₁ hV
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA uB uC
                h_pA h_pB h_pC hA₁ hB₁ hC₁ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,1) outer AC inner BC. Pattern #6 (BC-AC-BC-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AC_at_3_2_canonical V₁ V hV₁ hV
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA uB uC
                h_pA h_pB h_pC hA₁ hB₁ hC₁ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; left
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,1) AC-AC consecutive same-XY merge. Pattern #7.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge :
              singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                singleQubitLayer uA₁ uB₁ uC₁ * embedAC V *
                singleQubitLayer uA uB uC =
              singleQubitLayer u_pA (u_pB * uB₁) u_pC *
                embedAC (V₁ * (kron2 uA₁ uC₁ * V)) *
                singleQubitLayer uA uB uC := by
              rw [show singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                        singleQubitLayer uA₁ uB₁ uC₁ * embedAC V *
                        singleQubitLayer uA uB uC =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAC V₁ * singleQubitLayer uA₁ uB₁ uC₁ * embedAC V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedAC_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                        (singleQubitLayer I₂ uB₁ I₂ *
                          embedAC (V₁ * (kron2 uA₁ uC₁ * V))) *
                        singleQubitLayer uA uB uC =
                    (singleQubitLayer u_pA u_pB u_pC *
                       singleQubitLayer I₂ uB₁ I₂) *
                      embedAC (V₁ * (kron2 uA₁ uC₁ * V)) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₁ * (kron2 uA₁ uC₁ * V)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hC₁) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleAC_canonical (V₁ * (kron2 uA₁ uC₁ * V))
                hV_merged
                u_pA (u_pB * uB₁) u_pC h_pA (isUnitary2_mul h_pB hB₁) h_pC
                uA uB uC hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
      | compose_AB V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,2) outer AC inner AB. Pattern #7 (AB-AC-AB-AC).
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_AC_at_3_2_canonical V₂ V hV₂ hV
                u_pA u_pB u_pC uA₂ uB₂ uC₂ uA uB uC
                h_pA h_pB h_pC hA₂ hB₂ hC₂ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,2,1) AB-AB-AC inner-pair-merge: V₁ and V₂ both AB.
          -- Pattern #7 (AB-AC-AB-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := inner_AB_pair_merge_sandwich V₁ V₂ (embedAC V)
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA uB uC
            have hV_merged : IsUnitary4 (V₁ * (kron2 uA₁ uB₁ * V₂)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hB₁) hV₂)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_AC_at_3_2_canonical
                (V₁ * (kron2 uA₁ uB₁ * V₂)) V hV_merged hV
                u_pA u_pB (u_pC * uC₁) uA₂ uB₂ uC₂ uA uB uC
                h_pA h_pB (isUnitary2_mul h_pC hC₁) hA₂ hB₂ hC₂ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) BC-AB-AC all-different. Pattern #3 (AC-BC-AB-AC), V₁ = 1.
          -- Iter 1038: mirror of the AC-AB-BC closure — the trailing leftover
          -- is B-only, commutes past `embedAC` and absorbs into the AB gate,
          -- so no fourth real embed is needed.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_BC_AB_AC_to_4embed V₁ V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA uB uC
            refine ⟨1,
              kron2 u_pB u_pC * V₁ * kron2 uB₁ uC₁,
              kron2 (u_pA * uA₁) 1 * V₂ * kron2 uA₂ uB₂ * kron2 1 uB,
              kron2 1 uC₂ * V * kron2 uA uC,
              isUnitary4_one,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV₁)
                (isUnitary4_kron2 hB₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul
                    (isUnitary4_kron2 (isUnitary2_mul h_pA hA₁) isUnitary2_one)
                    hV₂)
                  (isUnitary4_kron2 hA₂ hB₂))
                (isUnitary4_kron2 isUnitary2_one hB),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₂) hV)
                (isUnitary4_kron2 hA hC), ?_⟩
            right; right; left
            rw [embedAC_one, one_mul]
            exact h_chain
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,2,1) AC-AB-AC non-adjacent-same: V₁ and V outer both AC.
          -- Pattern #4 (AC-AB-AC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AC_AB_AC_to_4embed V₁ V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV₁)
                (isUnitary4_kron2 hA₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul h_pB hB₁)) hV₂)
                (isUnitary4_kron2 hA₂ hB₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₂) hV)
                (isUnitary4_kron2 hA hC),
              isUnitary4_kron2 isUnitary2_one hB, ?_⟩
            right; right; right; left
            exact h_chain
      | compose_BC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,2) outer AC inner BC. Pattern #6 (BC-AC-BC-AC).
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AC_at_3_2_canonical V₂ V hV₂ hV
                u_pA u_pB u_pC uA₂ uB₂ uC₂ uA uB uC
                h_pA h_pB h_pC hA₂ hB₂ hC₂ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; left
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,2,1) AB-BC-AC all-different: V₁=AB, V₂=BC, V outer=AC.
          -- Pattern #2 (AB-BC-AC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AB_BC_AC_to_4embed V₁ V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV₁)
                (isUnitary4_kron2 hA₁ hB₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul h_pC hC₁)) hV₂)
                (isUnitary4_kron2 hB₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₂ isUnitary2_one) hV)
                (isUnitary4_kron2 hA hC),
              isUnitary4_kron2 isUnitary2_one hB, ?_⟩
            right; left
            exact h_chain
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,2,1) BC-BC-AC inner-pair-merge: V₁ and V₂ both BC.
          -- Pattern #6 (BC-AC-BC-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := inner_BC_pair_merge_sandwich V₁ V₂ (embedAC V)
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA uB uC
            have hV_merged : IsUnitary4 (V₁ * (kron2 uB₁ uC₁ * V₂)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hB₁ hC₁) hV₂)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AC_at_3_2_canonical
                (V₁ * (kron2 uB₁ uC₁ * V₂)) V hV_merged hV
                (u_pA * uA₁) u_pB u_pC uA₂ uB₂ uC₂ uA uB uC
                (isUnitary2_mul h_pA hA₁) h_pB h_pC hA₂ hB₂ hC₂ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,2,1) AC-BC-AC non-adjacent-same: V₁ and V outer both AC.
          -- Pattern #9 (AC-BC-AC-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AC_BC_AC_to_4embed V₁ V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV₁)
                (isUnitary4_kron2 hA₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pB hB₁) isUnitary2_one) hV₂)
                (isUnitary4_kron2 hB₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₂ isUnitary2_one) hV)
                (isUnitary4_kron2 hA hC),
              isUnitary4_kron2 hB isUnitary2_one, ?_⟩
            right; right; right; right; right; right; right; right
            exact h_chain
      | compose_AC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,2) AC-AC consecutive same-XY merge. Pattern #7.
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge :
              singleQubitLayer u_pA u_pB u_pC * embedAC V₂ *
                singleQubitLayer uA₂ uB₂ uC₂ * embedAC V *
                singleQubitLayer uA uB uC =
              singleQubitLayer u_pA (u_pB * uB₂) u_pC *
                embedAC (V₂ * (kron2 uA₂ uC₂ * V)) *
                singleQubitLayer uA uB uC := by
              rw [show singleQubitLayer u_pA u_pB u_pC * embedAC V₂ *
                        singleQubitLayer uA₂ uB₂ uC₂ * embedAC V *
                        singleQubitLayer uA uB uC =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAC V₂ * singleQubitLayer uA₂ uB₂ uC₂ * embedAC V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedAC_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                        (singleQubitLayer I₂ uB₂ I₂ *
                          embedAC (V₂ * (kron2 uA₂ uC₂ * V))) *
                        singleQubitLayer uA uB uC =
                    (singleQubitLayer u_pA u_pB u_pC *
                       singleQubitLayer I₂ uB₂ I₂) *
                      embedAC (V₂ * (kron2 uA₂ uC₂ * V)) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₂ * (kron2 uA₂ uC₂ * V)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hA₂ hC₂) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleAC_canonical (V₂ * (kron2 uA₂ uC₂ * V))
                hV_merged
                u_pA (u_pB * uB₂) u_pC h_pA (isUnitary2_mul h_pB hB₂) h_pC
                uA uB uC hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,2,1) AB-AC-AC outer-pair-AC-merge: V₂ and V outer both AC.
          -- Pattern #7 (AB-AC-AB-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := outer_AC_pair_merge_sandwich (embedAB V₁) V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA uB uC
            have hV_merged : IsUnitary4 (V₂ * (kron2 uA₂ uC₂ * V)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hA₂ hC₂) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_AC_at_3_2_canonical V₁
                (V₂ * (kron2 uA₂ uC₂ * V)) hV₁ hV_merged
                u_pA u_pB u_pC uA₁ (uB₁ * uB₂) uC₁ uA uB uC
                h_pA h_pB h_pC hA₁ (isUnitary2_mul hB₁ hB₂) hC₁ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,2,1) BC-AC-AC outer-pair-AC-merge: V₂ and V outer both AC.
          -- Pattern #6 (BC-AC-BC-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := outer_AC_pair_merge_sandwich (embedBC V₁) V₂ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA uB uC
            have hV_merged : IsUnitary4 (V₂ * (kron2 uA₂ uC₂ * V)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hA₂ hC₂) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AC_at_3_2_canonical V₁
                (V₂ * (kron2 uA₂ uC₂ * V)) hV₁ hV_merged
                u_pA u_pB u_pC uA₁ (uB₁ * uB₂) uC₁ uA uB uC
                h_pA h_pB h_pC hA₁ (isUnitary2_mul hB₁ hB₂) hC₁ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,2,1) AC-AC-AC triple same-XY merge. Pattern #7.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have hV_merged : IsUnitary4
                (V₁ * (kron2 uA₁ uC₁ * V₂) * (kron2 uA₂ uC₂ * V)) :=
              isUnitary4_mul
                (isUnitary4_mul hV₁
                  (isUnitary4_mul (isUnitary4_kron2 hA₁ hC₁) hV₂))
                (isUnitary4_mul (isUnitary4_kron2 hA₂ hC₂) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleAC_canonical
                (V₁ * (kron2 uA₁ uC₁ * V₂) * (kron2 uA₂ uC₂ * V))
                hV_merged
                u_pA ((u_pB * uB₁) * uB₂) u_pC h_pA
                (isUnitary2_mul (isUnitary2_mul h_pB hB₁) hB₂) h_pC
                uA uB uC hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            rw [sandwich_AC_AC_AC_to_AC V₁ V₂ V
                  u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA uB uC]
            exact h_eq
    | compose_AB V₃ hV₃ uA₃ uB₃ uC₃ hA₃ hB₃ hC₃ h2 =>
      -- (4,3) outer AC inner AB. Pattern #7 (AB-AC-AB-AC).
      cases h2 with
      | weaken h1 =>
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_AC_at_3_2_canonical V₃ V hV₃ hV
                u_pA u_pB u_pC uA₃ uB₃ uC₃ uA uB uC
                h_pA h_pB h_pC hA₃ hB₃ hC₃ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,1) AB-AB-AC inner-pair-merge: V₁ and V₃ both AB.
          -- Pattern #7 (AB-AC-AB-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := inner_AB_pair_merge_sandwich V₁ V₃ (embedAC V)
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            have hV_merged : IsUnitary4 (V₁ * (kron2 uA₁ uB₁ * V₃)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hB₁) hV₃)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_AC_at_3_2_canonical
                (V₁ * (kron2 uA₁ uB₁ * V₃)) V hV_merged hV
                u_pA u_pB (u_pC * uC₁) uA₃ uB₃ uC₃ uA uB uC
                h_pA h_pB (isUnitary2_mul h_pC hC₁) hA₃ hB₃ hC₃ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (3,2,1) BC-AB-AC all-different. Pattern #3 (AC-BC-AB-AC), V₁ = 1.
          -- Iter 1038: mirror of the AC-AB-BC closure — the trailing leftover
          -- is B-only, commutes past `embedAC` and absorbs into the AB gate,
          -- so no fourth real embed is needed.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_BC_AB_AC_to_4embed V₁ V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨1,
              kron2 u_pB u_pC * V₁ * kron2 uB₁ uC₁,
              kron2 (u_pA * uA₁) 1 * V₃ * kron2 uA₃ uB₃ * kron2 1 uB,
              kron2 1 uC₃ * V * kron2 uA uC,
              isUnitary4_one,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV₁)
                (isUnitary4_kron2 hB₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul
                    (isUnitary4_kron2 (isUnitary2_mul h_pA hA₁) isUnitary2_one)
                    hV₃)
                  (isUnitary4_kron2 hA₃ hB₃))
                (isUnitary4_kron2 isUnitary2_one hB),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₃) hV)
                (isUnitary4_kron2 hA hC), ?_⟩
            right; right; left
            rw [embedAC_one, one_mul]
            exact h_chain
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,1) AC-AB-AC non-adjacent-same: V₁ and V outer both AC.
          -- Pattern #4 (AC-AB-AC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AC_AB_AC_to_4embed V₁ V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV₁)
                (isUnitary4_kron2 hA₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul h_pB hB₁)) hV₃)
                (isUnitary4_kron2 hA₃ hB₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₃) hV)
                (isUnitary4_kron2 hA hC),
              isUnitary4_kron2 isUnitary2_one hB, ?_⟩
            right; right; right; left
            exact h_chain
      | compose_AB V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,3,2) AB-AB-AC section (V outer=AC, V₃=AB, V₂=AB).
        -- V₂=V₃=AB consecutive adjacent same-XY merge.
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            -- (4,3,2) AB-AB-AC: merge V₂,V₃ (both AB) → (3,2) AB-AC chain.
            -- Pattern #7 (AB-AC-AB-AC).
            have h_merge :
                singleQubitLayer u_pA u_pB u_pC * embedAB V₂ *
                  singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ =
                singleQubitLayer u_pA u_pB (u_pC * uC₂) *
                  embedAB (V₂ * (kron2 uA₂ uB₂ * V₃)) *
                  singleQubitLayer uA₃ uB₃ uC₃ := by
              rw [show
                    singleQubitLayer u_pA u_pB u_pC * embedAB V₂ *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAB V₂ * singleQubitLayer uA₂ uB₂ uC₂ *
                        embedAB V₃) *
                      singleQubitLayer uA₃ uB₃ uC₃ from by noncomm_ring]
              rw [embedAB_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                    (singleQubitLayer I₂ I₂ uC₂ *
                      embedAB (V₂ * (kron2 uA₂ uB₂ * V₃))) *
                    singleQubitLayer uA₃ uB₃ uC₃ =
                  (singleQubitLayer u_pA u_pB u_pC *
                     singleQubitLayer I₂ I₂ uC₂) *
                    embedAB (V₂ * (kron2 uA₂ uB₂ * V₃)) *
                    singleQubitLayer uA₃ uB₃ uC₃ from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₂ * (kron2 uA₂ uB₂ * V₃)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hA₂ hB₂) hV₃)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_AC_at_3_2_canonical
                (V₂ * (kron2 uA₂ uB₂ * V₃)) V hV_merged hV
                u_pA u_pB (u_pC * uC₂) uA₃ uB₃ uC₃ uA uB uC
                h_pA h_pB (isUnitary2_mul h_pC hC₂) hA₃ hB₃ hC₃ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer u_pA u_pB u_pC * embedAB V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃) *
                    embedAC V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_merge]
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AB-AB-AB-AC: V₁=V₂=V₃=AB inner three, V outer=AC.
          -- Pattern G inner-3-merge → (3,1) AB-AC chain. Pattern #7.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_inner_merge :
                singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                  singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                  singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ =
                singleQubitLayer u_pA u_pB (((u_pC * uC₁) * uC₂)) *
                  embedAB (V₁ * (kron2 uA₁ uB₁ * V₂) *
                    (kron2 uA₂ uB₂ * V₃)) *
                  singleQubitLayer uA₃ uB₃ uC₃ :=
              sandwich_AB_AB_AB_to_AB V₁ V₂ V₃
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃) *
                    embedAC V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_inner_merge]
            have hV_merge : IsUnitary4
                (V₁ * (kron2 uA₁ uB₁ * V₂) * (kron2 uA₂ uB₂ * V₃)) :=
              isUnitary4_mul
                (isUnitary4_mul hV₁
                  (isUnitary4_mul (isUnitary4_kron2 hA₁ hB₁) hV₂))
                (isUnitary4_mul (isUnitary4_kron2 hA₂ hB₂) hV₃)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_AC_at_3_2_canonical
                (V₁ * (kron2 uA₁ uB₁ * V₂) * (kron2 uA₂ uB₂ * V₃)) V
                hV_merge hV
                u_pA u_pB ((u_pC * uC₁) * uC₂) uA₃ uB₃ uC₃ uA uB uC
                h_pA h_pB
                (isUnitary2_mul (isUnitary2_mul h_pC hC₁) hC₂)
                hA₃ hB₃ hC₃ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- BC-AB-AB-AC: adjacent AB pair at slots (2,3) merges, leaving
          -- BC-AB-AC = pattern #3 (AC-BC-AB-AC) with V₁ = 1.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have hW : IsUnitary4 (V₂ * (kron2 uA₂ uB₂ * V₃)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hA₂ hB₂) hV₃)
            have h_merge := merge23_AB (embedBC V₁) (embedAC V) V₂ V₃
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            have h_chain := sandwich_BC_AB_AC_to_4embed V₁
              (V₂ * (kron2 uA₂ uB₂ * V₃)) V
              u_pA u_pB u_pC uA₁ uB₁ (uC₁ * uC₂) uA₃ uB₃ uC₃ uA uB uC
            refine ⟨1, _, _, _,
              isUnitary4_one,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV₁)
                (isUnitary4_kron2 hB₁ (isUnitary2_mul hC₁ hC₂)),
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul
                    (isUnitary4_kron2 (isUnitary2_mul h_pA hA₁) isUnitary2_one)
                    hW)
                  (isUnitary4_kron2 hA₃ hB₃))
                (isUnitary4_kron2 isUnitary2_one hB),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₃) hV)
                (isUnitary4_kron2 hA hC), ?_⟩
            right; right; left
            rw [h_merge, embedAC_one, one_mul]
            exact h_chain
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AC-AB-AB-AC: V₁=AC, V₂=V₃=AB middle pair, V outer=AC.
          -- Pattern C middle-pair-merge → (3,2,1) AC-AB-AC. Pattern #4.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_middle_merge :
                singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                  singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ =
                singleQubitLayer uA₁ uB₁ (uC₁ * uC₂) *
                  embedAB (V₂ * (kron2 uA₂ uB₂ * V₃)) := by
              rw [show
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ =
                    singleQubitLayer uA₁ uB₁ uC₁ *
                      (embedAB V₂ * singleQubitLayer uA₂ uB₂ uC₂ *
                        embedAB V₃) from by noncomm_ring]
              rw [embedAB_merge]
              rw [show singleQubitLayer uA₁ uB₁ uC₁ *
                    (singleQubitLayer I₂ I₂ uC₂ *
                      embedAB (V₂ * (kron2 uA₂ uB₂ * V₃))) =
                  (singleQubitLayer uA₁ uB₁ uC₁ *
                     singleQubitLayer I₂ I₂ uC₂) *
                    embedAB (V₂ * (kron2 uA₂ uB₂ * V₃))
                  from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    (singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃) *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_middle_merge]
            have h_chain := sandwich_AC_AB_AC_to_4embed V₁
              (V₂ * (kron2 uA₂ uB₂ * V₃)) V
              u_pA u_pB u_pC uA₁ uB₁ (uC₁ * uC₂) uA₃ uB₃ uC₃ uA uB uC
            have hV_merge : IsUnitary4 (V₂ * (kron2 uA₂ uB₂ * V₃)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hA₂ hB₂) hV₃)
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV₁)
                (isUnitary4_kron2 hA₁ (isUnitary2_mul hC₁ hC₂)),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul h_pB hB₁)) hV_merge)
                (isUnitary4_kron2 hA₃ hB₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₃) hV)
                (isUnitary4_kron2 hA hC),
              isUnitary4_kron2 isUnitary2_one hB, ?_⟩
            right; right; right; left
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    (singleQubitLayer uA₁ uB₁ (uC₁ * uC₂) *
                      embedAB (V₂ * (kron2 uA₂ uB₂ * V₃))) *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ (uC₁ * uC₂) *
                    embedAB (V₂ * (kron2 uA₂ uB₂ * V₃)) *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_chain
      | compose_BC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- Gate slot 1 still undestructed: four sub-cases (none / AB / AC / BC).
        cases h1 with
        | weaken h0 =>
          -- 3-gate BC-AB-AC = pattern #3 with V₁ = 1.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_eq := sandwich_BC_AB_AC_to_4embed V₂ V₃ V
              u_pA u_pB u_pC uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _, ?_, ?_, ?_, ?_,
              Or.inr (Or.inr (Or.inl (pad_AC_one _ _ _ _ h_eq)))⟩ <;> unitary_auto
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- AB-BC-AB-AC: gates 1,3 are AB; re-typing gate 2 gives pattern #7 (AB-AC-AB-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_eq := (retype2_AB_BC_to_AC (embedAC V) V₁ V₂ V₃
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC).trans
              (sandwich_AB_AC_AB_AC_to_4embed (V₁ * SWAP_4) V₂ (SWAP_4 * V₃) V
                u_pA u_pB u_pC uB₁ uA₁ uC₁ uB₂ uA₂ uC₂ uA₃ uB₃ uC₃ uA uB uC)
            refine ⟨_, _, _, _, ?_, ?_, ?_, ?_,
              Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_eq))))))⟩ <;> unitary_auto
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- AC-BC-AB-AC is literally pattern #3.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_eq := sandwich_AC_BC_AB_AC_to_4embed V₁ V₂ V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _, ?_, ?_, ?_, ?_,
              Or.inr (Or.inr (Or.inl h_eq))⟩ <;> unitary_auto
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- BC-BC-AB-AC: adjacent BC pair at slots (1,2) merges, leaving BC-AB-AC.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_eq := (merge12_BC V₁ V₂ (embedAB V₃) (embedAC V)
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC).trans
              (sandwich_BC_AB_AC_to_4embed (V₁ * (kron2 uB₁ uC₁ * V₂)) V₃ V
                (u_pA * uA₁) u_pB u_pC uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC)
            refine ⟨_, _, _, _, ?_, ?_, ?_, ?_,
              Or.inr (Or.inr (Or.inl (pad_AC_one _ _ _ _ h_eq)))⟩ <;> unitary_auto
      | compose_AC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,3,2) AC-AB-AC section (V outer=AC, V₃=AB, V₂=AC).
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            -- (4,3,2) AC-AB-AC: 3-real-gate natural chain. Pattern #4.
            have h_chain := sandwich_AC_AB_AC_to_4embed V₂ V₃ V
              u_pA u_pB u_pC uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV₂)
                (isUnitary4_kron2 hA₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul h_pB hB₂)) hV₃)
                (isUnitary4_kron2 hA₃ hB₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₃) hV)
                (isUnitary4_kron2 hA hC),
              isUnitary4_kron2 isUnitary2_one hB, ?_⟩
            right; right; right; left
            exact h_chain
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AB-AC-AB-AC: V₁=AB, V₂=AC, V₃=AB, V outer=AC.
          -- Direct pattern #7 (AB-AC-AB-AC) match. Pattern E.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AB_AC_AB_AC_to_4embed V₁ V₂ V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV₁)
                (isUnitary4_kron2 hA₁ hB₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul h_pC hC₁)) hV₂)
                (isUnitary4_kron2 hA₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hB₂) hV₃)
                  (isUnitary4_kron2 hA₃ hB₃))
                (isUnitary4_kron2 isUnitary2_one hB),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₃) hV)
                (isUnitary4_kron2 hA hC), ?_⟩
            right; right; right; right; right; right; left
            exact h_chain
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- BC-AC-AB-AC: gates 2,4 are AC; conjugating gate 3 by SWAP_AC turns AB into BC, giving
          -- pattern #6 (BC-AC-BC-AC). Table 4 row 5.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_eq := (retype3_AC_AB_to_BC (embedBC V₁) V₂ V₃ V
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC).trans
              (sandwich_BC_AC_BC_AC_to_4embed V₁ (V₂ * SWAP_4) (SWAP_4 * V₃ * SWAP_4)
                (SWAP_4 * V)
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uC₂ uB₂ uA₂ uC₃ uB₃ uA₃ uA uB uC)
            refine ⟨_, _, _, _, ?_, ?_, ?_, ?_,
              Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_eq)))))⟩ <;> unitary_auto
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AC-AC-AB-AC: V₁=V₂=AC inner pair, V₃=AB, V outer=AC.
          -- Pattern D inner-pair-merge → (3,2,1) AC-AB-AC. Pattern #4.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_inner_merge :
                singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                  singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ =
                singleQubitLayer u_pA (u_pB * uB₁) u_pC *
                  embedAC (V₁ * (kron2 uA₁ uC₁ * V₂)) := by
              rw [show
                    singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                      singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAC V₁ * singleQubitLayer uA₁ uB₁ uC₁ *
                        embedAC V₂) from by noncomm_ring]
              rw [embedAC_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                    (singleQubitLayer I₂ uB₁ I₂ *
                      embedAC (V₁ * (kron2 uA₁ uC₁ * V₂))) =
                  (singleQubitLayer u_pA u_pB u_pC *
                     singleQubitLayer I₂ uB₁ I₂) *
                    embedAC (V₁ * (kron2 uA₁ uC₁ * V₂))
                  from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂) *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAB V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_inner_merge]
            have h_chain := sandwich_AC_AB_AC_to_4embed
              (V₁ * (kron2 uA₁ uC₁ * V₂)) V₃ V
              u_pA (u_pB * uB₁) u_pC uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            have hV_merge : IsUnitary4 (V₁ * (kron2 uA₁ uC₁ * V₂)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hC₁) hV₂)
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV_merge)
                (isUnitary4_kron2 hA₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul (isUnitary2_mul h_pB hB₁) hB₂)) hV₃)
                (isUnitary4_kron2 hA₃ hB₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₃) hV)
                (isUnitary4_kron2 hA hC),
              isUnitary4_kron2 isUnitary2_one hB, ?_⟩
            right; right; right; left
            exact h_chain
    | compose_BC V₃ hV₃ uA₃ uB₃ uC₃ hA₃ hB₃ hC₃ h2 =>
      -- (4,3) outer AC inner BC. Pattern #6 (BC-AC-BC-AC).
      cases h2 with
      | weaken h1 =>
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AC_at_3_2_canonical V₃ V hV₃ hV
                u_pA u_pB u_pC uA₃ uB₃ uC₃ uA uB uC
                h_pA h_pB h_pC hA₃ hB₃ hC₃ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; left
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,1) AB-BC-AC all-different: V₁=AB, V₃=BC, V outer=AC.
          -- Pattern #2 (AB-BC-AC-AB).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AB_BC_AC_to_4embed V₁ V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV₁)
                (isUnitary4_kron2 hA₁ hB₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul h_pC hC₁)) hV₃)
                (isUnitary4_kron2 hB₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₃ isUnitary2_one) hV)
                (isUnitary4_kron2 hA hC),
              isUnitary4_kron2 isUnitary2_one hB, ?_⟩
            right; left
            exact h_chain
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,1) BC-BC-AC inner-pair-merge: V₁ and V₃ both BC.
          -- Pattern #6 (BC-AC-BC-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := inner_BC_pair_merge_sandwich V₁ V₃ (embedAC V)
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            have hV_merged : IsUnitary4 (V₁ * (kron2 uB₁ uC₁ * V₃)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hB₁ hC₁) hV₃)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AC_at_3_2_canonical
                (V₁ * (kron2 uB₁ uC₁ * V₃)) V hV_merged hV
                (u_pA * uA₁) u_pB u_pC uA₃ uB₃ uC₃ uA uB uC
                (isUnitary2_mul h_pA hA₁) h_pB h_pC hA₃ hB₃ hC₃ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,1) AC-BC-AC non-adjacent-same: V₁ and V outer both AC.
          -- Pattern #9 (AC-BC-AC-BC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_AC_BC_AC_to_4embed V₁ V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV₁)
                (isUnitary4_kron2 hA₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pB hB₁) isUnitary2_one) hV₃)
                (isUnitary4_kron2 hB₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₃ isUnitary2_one) hV)
                (isUnitary4_kron2 hA hC),
              isUnitary4_kron2 hB isUnitary2_one, ?_⟩
            right; right; right; right; right; right; right; right
            exact h_chain
      | compose_AB V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,3,2) AB-BC-AC section (V outer=AC, V₃=BC, V₂=AB).
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            -- (4,3,2) AB-BC-AC: 3-real-gate natural chain. Pattern #2.
            have h_chain := sandwich_AB_BC_AC_to_4embed V₂ V₃ V
              u_pA u_pB u_pC uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV₂)
                (isUnitary4_kron2 hA₂ hB₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul h_pC hC₂)) hV₃)
                (isUnitary4_kron2 hB₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₃ isUnitary2_one) hV)
                (isUnitary4_kron2 hA hC),
              isUnitary4_kron2 isUnitary2_one hB, ?_⟩
            right; left
            exact h_chain
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AB-AB-BC-AC: V₁=V₂=AB inner pair, V₃=BC, V outer=AC.
          -- Pattern D inner-pair-merge → (3,2,1) AB-BC-AC. Pattern #2.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_inner_merge :
                singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                  singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ =
                singleQubitLayer u_pA u_pB (u_pC * uC₁) *
                  embedAB (V₁ * (kron2 uA₁ uB₁ * V₂)) := by
              rw [show
                    singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                      singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAB V₁ * singleQubitLayer uA₁ uB₁ uC₁ *
                        embedAB V₂) from by noncomm_ring]
              rw [embedAB_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                    (singleQubitLayer I₂ I₂ uC₁ *
                      embedAB (V₁ * (kron2 uA₁ uB₁ * V₂))) =
                  (singleQubitLayer u_pA u_pB u_pC *
                     singleQubitLayer I₂ I₂ uC₁) *
                    embedAB (V₁ * (kron2 uA₁ uB₁ * V₂))
                  from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂) *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_inner_merge]
            have hV_inner : IsUnitary4 (V₁ * (kron2 uA₁ uB₁ * V₂)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hB₁) hV₂)
            have h_chain := sandwich_AB_BC_AC_to_4embed
              (V₁ * (kron2 uA₁ uB₁ * V₂)) V₃ V
              u_pA u_pB (u_pC * uC₁) uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV_inner)
                (isUnitary4_kron2 hA₂ hB₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul (isUnitary2_mul h_pC hC₁) hC₂)) hV₃)
                (isUnitary4_kron2 hB₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₃ isUnitary2_one) hV)
                (isUnitary4_kron2 hA hC),
              isUnitary4_kron2 isUnitary2_one hB, ?_⟩
            right; left
            exact h_chain
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- BC-AB-BC-AC: gates 1,3 are BC; conjugating gate 2 turns AB into AC, giving pattern #6
          -- (BC-AC-BC-AC). Table 4 row 4.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_eq := (retype2_BC_AB_to_AC (embedAC V) V₁ V₂ V₃
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC).trans
              (sandwich_BC_AC_BC_AC_to_4embed (V₁ * SWAP_4) V₂ (SWAP_4 * V₃) V
                u_pA u_pB u_pC uA₁ uC₁ uB₁ uA₂ uC₂ uB₂ uA₃ uB₃ uC₃ uA uB uC)
            refine ⟨_, _, _, _, ?_, ?_, ?_, ?_,
              Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_eq)))))⟩ <;> unitary_auto
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- AC-AB-BC-AC: gates 1,4 are AC; conjugating the middle block by SWAP_AC swaps AB and
          -- BC, giving pattern #3 (AC-BC-AB-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_eq := (retype23_AC V₁ V₂ V₃ V
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC).trans
              (sandwich_AC_BC_AB_AC_to_4embed (V₁ * SWAP_4) (SWAP_4 * V₂ * SWAP_4)
                (SWAP_4 * V₃ * SWAP_4) (SWAP_4 * V)
                u_pA u_pB u_pC uC₁ uB₁ uA₁ uC₂ uB₂ uA₂ uC₃ uB₃ uA₃ uA uB uC)
            refine ⟨_, _, _, _, ?_, ?_, ?_, ?_,
              Or.inr (Or.inr (Or.inl h_eq))⟩ <;> unitary_auto
      | compose_BC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,3,2) BC-BC-AC section (V outer=AC, V₃=BC, V₂=BC).
        -- V₂=V₃=BC consecutive adjacent same-XY merge.
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            -- (4,3,2) BC-BC-AC: merge V₂,V₃ (both BC) → (3,2) BC-AC chain.
            -- Pattern #6 (BC-AC-BC-AC).
            have h_merge :
                singleQubitLayer u_pA u_pB u_pC * embedBC V₂ *
                  singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ =
                singleQubitLayer (u_pA * uA₂) u_pB u_pC *
                  embedBC (V₂ * (kron2 uB₂ uC₂ * V₃)) *
                  singleQubitLayer uA₃ uB₃ uC₃ := by
              rw [show
                    singleQubitLayer u_pA u_pB u_pC * embedBC V₂ *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedBC V₂ * singleQubitLayer uA₂ uB₂ uC₂ *
                        embedBC V₃) *
                      singleQubitLayer uA₃ uB₃ uC₃ from by noncomm_ring]
              rw [embedBC_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                    (singleQubitLayer uA₂ I₂ I₂ *
                      embedBC (V₂ * (kron2 uB₂ uC₂ * V₃))) *
                    singleQubitLayer uA₃ uB₃ uC₃ =
                  (singleQubitLayer u_pA u_pB u_pC *
                     singleQubitLayer uA₂ I₂ I₂) *
                    embedBC (V₂ * (kron2 uB₂ uC₂ * V₃)) *
                    singleQubitLayer uA₃ uB₃ uC₃ from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₂ * (kron2 uB₂ uC₂ * V₃)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hB₂ hC₂) hV₃)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AC_at_3_2_canonical
                (V₂ * (kron2 uB₂ uC₂ * V₃)) V hV_merged hV
                (u_pA * uA₂) u_pB u_pC uA₃ uB₃ uC₃ uA uB uC
                (isUnitary2_mul h_pA hA₂) h_pB h_pC hA₃ hB₃ hC₃ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; left
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer u_pA u_pB u_pC * embedBC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃) *
                    embedAC V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_merge]
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AB-BC-BC-AC: V₁=AB, V₂=V₃=BC middle pair, V outer=AC.
          -- Pattern C middle-pair-merge → (3,2,1) AB-BC-AC. Pattern #2.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_middle_merge :
                singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                  singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ =
                singleQubitLayer (uA₁ * uA₂) uB₁ uC₁ *
                  embedBC (V₂ * (kron2 uB₂ uC₂ * V₃)) := by
              rw [show
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ =
                    singleQubitLayer uA₁ uB₁ uC₁ *
                      (embedBC V₂ * singleQubitLayer uA₂ uB₂ uC₂ *
                        embedBC V₃) from by noncomm_ring]
              rw [embedBC_merge]
              rw [show singleQubitLayer uA₁ uB₁ uC₁ *
                    (singleQubitLayer uA₂ I₂ I₂ *
                      embedBC (V₂ * (kron2 uB₂ uC₂ * V₃))) =
                  (singleQubitLayer uA₁ uB₁ uC₁ *
                     singleQubitLayer uA₂ I₂ I₂) *
                    embedBC (V₂ * (kron2 uB₂ uC₂ * V₃))
                  from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    (singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃) *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_middle_merge]
            have h_chain := sandwich_AB_BC_AC_to_4embed V₁
              (V₂ * (kron2 uB₂ uC₂ * V₃)) V
              u_pA u_pB u_pC (uA₁ * uA₂) uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            have hV_merge : IsUnitary4 (V₂ * (kron2 uB₂ uC₂ * V₃)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hB₂ hC₂) hV₃)
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV₁)
                (isUnitary4_kron2 (isUnitary2_mul hA₁ hA₂) hB₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul h_pC hC₁)) hV_merge)
                (isUnitary4_kron2 hB₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₃ isUnitary2_one) hV)
                (isUnitary4_kron2 hA hC),
              isUnitary4_kron2 isUnitary2_one hB, ?_⟩
            right; left
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    (singleQubitLayer (uA₁ * uA₂) uB₁ uC₁ *
                      embedBC (V₂ * (kron2 uB₂ uC₂ * V₃))) *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer (uA₁ * uA₂) uB₁ uC₁ *
                    embedBC (V₂ * (kron2 uB₂ uC₂ * V₃)) *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_chain
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) BC-BC-BC-AC: V₁=V₂=V₃=BC inner three, V outer=AC.
          -- Pattern G inner-3-merge → (3,2) BC-AC chain. Pattern #6 (BC-AC-BC-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_inner_merge :
                singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                  singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                  singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ =
                singleQubitLayer ((u_pA * uA₁) * uA₂) u_pB u_pC *
                  embedBC (V₁ * (kron2 uB₁ uC₁ * V₂) *
                    (kron2 uB₂ uC₂ * V₃)) *
                  singleQubitLayer uA₃ uB₃ uC₃ :=
              sandwich_BC_BC_BC_to_BC V₁ V₂ V₃
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃) *
                    embedAC V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_inner_merge]
            have hV_merge : IsUnitary4
                (V₁ * (kron2 uB₁ uC₁ * V₂) * (kron2 uB₂ uC₂ * V₃)) :=
              isUnitary4_mul
                (isUnitary4_mul hV₁
                  (isUnitary4_mul (isUnitary4_kron2 hB₁ hC₁) hV₂))
                (isUnitary4_mul (isUnitary4_kron2 hB₂ hC₂) hV₃)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AC_at_3_2_canonical
                (V₁ * (kron2 uB₁ uC₁ * V₂) * (kron2 uB₂ uC₂ * V₃)) V
                hV_merge hV
                ((u_pA * uA₁) * uA₂) u_pB u_pC uA₃ uB₃ uC₃ uA uB uC
                (isUnitary2_mul (isUnitary2_mul h_pA hA₁) hA₂) h_pB h_pC
                hA₃ hB₃ hC₃ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; left
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AC-BC-BC-AC: V₁=AC, V₂=V₃=BC middle pair, V outer=AC.
          -- Pattern C middle-pair-merge → (3,2,1) AC-BC-AC. Pattern #9.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_middle_merge :
                singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                  singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ =
                singleQubitLayer (uA₁ * uA₂) uB₁ uC₁ *
                  embedBC (V₂ * (kron2 uB₂ uC₂ * V₃)) := by
              rw [show
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ =
                    singleQubitLayer uA₁ uB₁ uC₁ *
                      (embedBC V₂ * singleQubitLayer uA₂ uB₂ uC₂ *
                        embedBC V₃) from by noncomm_ring]
              rw [embedBC_merge]
              rw [show singleQubitLayer uA₁ uB₁ uC₁ *
                    (singleQubitLayer uA₂ I₂ I₂ *
                      embedBC (V₂ * (kron2 uB₂ uC₂ * V₃))) =
                  (singleQubitLayer uA₁ uB₁ uC₁ *
                     singleQubitLayer uA₂ I₂ I₂) *
                    embedBC (V₂ * (kron2 uB₂ uC₂ * V₃))
                  from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    (singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃) *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_middle_merge]
            have h_chain := sandwich_AC_BC_AC_to_4embed V₁
              (V₂ * (kron2 uB₂ uC₂ * V₃)) V
              u_pA u_pB u_pC (uA₁ * uA₂) uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            have hV_merge : IsUnitary4 (V₂ * (kron2 uB₂ uC₂ * V₃)) :=
              isUnitary4_mul hV₂ (isUnitary4_mul (isUnitary4_kron2 hB₂ hC₂) hV₃)
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV₁)
                (isUnitary4_kron2 (isUnitary2_mul hA₁ hA₂) hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pB hB₁) isUnitary2_one) hV_merge)
                (isUnitary4_kron2 hB₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₃ isUnitary2_one) hV)
                (isUnitary4_kron2 hA hC),
              isUnitary4_kron2 hB isUnitary2_one, ?_⟩
            right; right; right; right; right; right; right; right
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    (singleQubitLayer (uA₁ * uA₂) uB₁ uC₁ *
                      embedBC (V₂ * (kron2 uB₂ uC₂ * V₃))) *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer (uA₁ * uA₂) uB₁ uC₁ *
                    embedBC (V₂ * (kron2 uB₂ uC₂ * V₃)) *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_chain
      | compose_AC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,3,2) AC-BC-AC section (V outer=AC, V₃=BC, V₂=AC).
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            -- (4,3,2) AC-BC-AC: 3-real-gate natural chain. Pattern #9.
            have h_chain := sandwich_AC_BC_AC_to_4embed V₂ V₃ V
              u_pA u_pB u_pC uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV₂)
                (isUnitary4_kron2 hA₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pB hB₂) isUnitary2_one) hV₃)
                (isUnitary4_kron2 hB₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₃ isUnitary2_one) hV)
                (isUnitary4_kron2 hA hC),
              isUnitary4_kron2 hB isUnitary2_one, ?_⟩
            right; right; right; right; right; right; right; right
            exact h_chain
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- AB-AC-BC-AC: gates 2,4 are AC; conjugating gate 3 by SWAP_AC turns BC into AB, giving
          -- pattern #7 (AB-AC-AB-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_eq := (retype3_AC_BC_to_AB (embedAB V₁) V₂ V₃ V
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC).trans
              (sandwich_AB_AC_AB_AC_to_4embed V₁ (V₂ * SWAP_4) (SWAP_4 * V₃ * SWAP_4)
                (SWAP_4 * V)
                u_pA u_pB u_pC uA₁ uB₁ uC₁ uC₂ uB₂ uA₂ uC₃ uB₃ uA₃ uA uB uC)
            refine ⟨_, _, _, _, ?_, ?_, ?_, ?_,
              Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_eq))))))⟩ <;> unitary_auto
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) BC-AC-BC-AC: V₁=BC, V₂=AC, V₃=BC, V outer=AC.
          -- Direct pattern #6 (BC-AC-BC-AC) match. Pattern E.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_chain := sandwich_BC_AC_BC_AC_to_4embed V₁ V₂ V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV₁)
                (isUnitary4_kron2 hB₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pA hA₁) isUnitary2_one) hV₂)
                (isUnitary4_kron2 hA₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul (isUnitary4_kron2 hB₂ isUnitary2_one) hV₃)
                  (isUnitary4_kron2 hB₃ hC₃))
                (isUnitary4_kron2 hB isUnitary2_one),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₃ isUnitary2_one) hV)
                (isUnitary4_kron2 hA hC), ?_⟩
            right; right; right; right; right; left
            exact h_chain
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AC-AC-BC-AC: V₁=V₂=AC inner pair, V₃=BC, V outer=AC.
          -- Pattern D inner-pair-merge → (3,2,1) AC-BC-AC. Pattern #9.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_inner_merge :
                singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                  singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ =
                singleQubitLayer u_pA (u_pB * uB₁) u_pC *
                  embedAC (V₁ * (kron2 uA₁ uC₁ * V₂)) := by
              rw [show
                    singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                      singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAC V₁ * singleQubitLayer uA₁ uB₁ uC₁ *
                        embedAC V₂) from by noncomm_ring]
              rw [embedAC_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                    (singleQubitLayer I₂ uB₁ I₂ *
                      embedAC (V₁ * (kron2 uA₁ uC₁ * V₂))) =
                  (singleQubitLayer u_pA u_pB u_pC *
                     singleQubitLayer I₂ uB₁ I₂) *
                    embedAC (V₁ * (kron2 uA₁ uC₁ * V₂))
                  from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂) *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedBC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            rw [h_inner_merge]
            have h_chain := sandwich_AC_BC_AC_to_4embed
              (V₁ * (kron2 uA₁ uC₁ * V₂)) V₃ V
              u_pA (u_pB * uB₁) u_pC uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            have hV_merge : IsUnitary4 (V₁ * (kron2 uA₁ uC₁ * V₂)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hC₁) hV₂)
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV_merge)
                (isUnitary4_kron2 hA₂ hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul (isUnitary2_mul h_pB hB₁) hB₂)
                  isUnitary2_one) hV₃)
                (isUnitary4_kron2 hB₃ hC₃),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₃ isUnitary2_one) hV)
                (isUnitary4_kron2 hA hC),
              isUnitary4_kron2 hB isUnitary2_one, ?_⟩
            right; right; right; right; right; right; right; right
            exact h_chain
    | compose_AC V₃ hV₃ uA₃ uB₃ uC₃ hA₃ hB₃ hC₃ h2 =>
      -- (4,3) AC-AC consecutive same-XY merge. Pattern #7.
      cases h2 with
      | weaken h1 =>
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge :
              singleQubitLayer u_pA u_pB u_pC * embedAC V₃ *
                singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                singleQubitLayer uA uB uC =
              singleQubitLayer u_pA (u_pB * uB₃) u_pC *
                embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                singleQubitLayer uA uB uC := by
              rw [show singleQubitLayer u_pA u_pB u_pC * embedAC V₃ *
                        singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                        singleQubitLayer uA uB uC =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAC V₃ * singleQubitLayer uA₃ uB₃ uC₃ * embedAC V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedAC_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                        (singleQubitLayer I₂ uB₃ I₂ *
                          embedAC (V₃ * (kron2 uA₃ uC₃ * V))) *
                        singleQubitLayer uA uB uC =
                    (singleQubitLayer u_pA u_pB u_pC *
                       singleQubitLayer I₂ uB₃ I₂) *
                      embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₃ * (kron2 uA₃ uC₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hA₃ hC₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleAC_canonical (V₃ * (kron2 uA₃ uC₃ * V))
                hV_merged
                u_pA (u_pB * uB₃) u_pC h_pA (isUnitary2_mul h_pB hB₃) h_pC
                uA uB uC hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,1) AB-AC-AC outer-pair-AC-merge: V₃ and V outer both AC.
          -- Pattern #7 (AB-AC-AB-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := outer_AC_pair_merge_sandwich (embedAB V₁) V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            have hV_merged : IsUnitary4 (V₃ * (kron2 uA₃ uC₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hA₃ hC₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_AC_at_3_2_canonical V₁
                (V₃ * (kron2 uA₃ uC₃ * V)) hV₁ hV_merged
                u_pA u_pB u_pC uA₁ (uB₁ * uB₃) uC₁ uA uB uC
                h_pA h_pB h_pC hA₁ (isUnitary2_mul hB₁ hB₃) hC₁ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,1) BC-AC-AC outer-pair-AC-merge: V₃ and V outer both AC.
          -- Pattern #6 (BC-AC-BC-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge := outer_AC_pair_merge_sandwich (embedBC V₁) V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC
            have hV_merged : IsUnitary4 (V₃ * (kron2 uA₃ uC₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hA₃ hC₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AC_at_3_2_canonical V₁
                (V₃ * (kron2 uA₃ uC₃ * V)) hV₁ hV_merged
                u_pA u_pB u_pC uA₁ (uB₁ * uB₃) uC₁ uA uB uC
                h_pA h_pB h_pC hA₁ (isUnitary2_mul hB₁ hB₃) hC₁ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; left
            rw [h_merge]
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,1) AC-AC-AC triple same-XY merge. Pattern #7.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have hV_merged : IsUnitary4
                (V₁ * (kron2 uA₁ uC₁ * V₃) * (kron2 uA₃ uC₃ * V)) :=
              isUnitary4_mul
                (isUnitary4_mul hV₁
                  (isUnitary4_mul (isUnitary4_kron2 hA₁ hC₁) hV₃))
                (isUnitary4_mul (isUnitary4_kron2 hA₃ hC₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleAC_canonical
                (V₁ * (kron2 uA₁ uC₁ * V₃) * (kron2 uA₃ uC₃ * V))
                hV_merged
                u_pA ((u_pB * uB₁) * uB₃) u_pC h_pA
                (isUnitary2_mul (isUnitary2_mul h_pB hB₁) hB₃) h_pC
                uA uB uC hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            rw [sandwich_AC_AC_AC_to_AC V₁ V₃ V
                  u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₃ uB₃ uC₃ uA uB uC]
            exact h_eq
      | compose_AB V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,3,2) AB-AC-AC section (V outer=AC, V₃=AC, V₂=AB).
        -- V₃=V=AC outer pair → merge.
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            -- (4,3,2) AB-AC-AC: merge V₃,V (both AC) → (3,2) AB-AC chain.
            -- Pattern #7 (AB-AC-AB-AC).
            have h_merge :
                singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                  singleQubitLayer uA uB uC =
                singleQubitLayer uA₂ (uB₂ * uB₃) uC₂ *
                  embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                  singleQubitLayer uA uB uC := by
              rw [show
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                      singleQubitLayer uA uB uC =
                    singleQubitLayer uA₂ uB₂ uC₂ *
                      (embedAC V₃ * singleQubitLayer uA₃ uB₃ uC₃ *
                        embedAC V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedAC_merge]
              rw [show singleQubitLayer uA₂ uB₂ uC₂ *
                    (singleQubitLayer I₂ uB₃ I₂ *
                      embedAC (V₃ * (kron2 uA₃ uC₃ * V))) *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer uA₂ uB₂ uC₂ *
                     singleQubitLayer I₂ uB₃ I₂) *
                    embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₃ * (kron2 uA₃ uC₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hA₃ hC₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_AC_at_3_2_canonical V₂
                (V₃ * (kron2 uA₃ uC₃ * V)) hV₂ hV_merged
                u_pA u_pB u_pC uA₂ (uB₂ * uB₃) uC₂ uA uB uC
                h_pA h_pB h_pC hA₂ (isUnitary2_mul hB₂ hB₃) hC₂ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₂ *
                    (singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                      singleQubitLayer uA uB uC) from by noncomm_ring]
            rw [h_merge]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₂ *
                    (singleQubitLayer uA₂ (uB₂ * uB₃) uC₂ *
                      embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                      singleQubitLayer uA uB uC) =
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₂ *
                    singleQubitLayer uA₂ (uB₂ * uB₃) uC₂ *
                    embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AB-AB-AC-AC: V₁=V₂=AB inner pair, V₃=V outer=AC outer pair.
          -- Pattern F (both-pair-merge): merge both pairs, reduce to (3,2) AB-AC.
          -- Pattern #7 (AB-AC-AB-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_outer_merge :
                singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                  singleQubitLayer uA uB uC =
                singleQubitLayer uA₂ (uB₂ * uB₃) uC₂ *
                  embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                  singleQubitLayer uA uB uC := by
              rw [show
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                      singleQubitLayer uA uB uC =
                    singleQubitLayer uA₂ uB₂ uC₂ *
                      (embedAC V₃ * singleQubitLayer uA₃ uB₃ uC₃ *
                        embedAC V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedAC_merge]
              rw [show singleQubitLayer uA₂ uB₂ uC₂ *
                    (singleQubitLayer I₂ uB₃ I₂ *
                      embedAC (V₃ * (kron2 uA₃ uC₃ * V))) *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer uA₂ uB₂ uC₂ *
                     singleQubitLayer I₂ uB₃ I₂) *
                    embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have h_inner_merge :
                singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                  singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ =
                singleQubitLayer u_pA u_pB (u_pC * uC₁) *
                  embedAB (V₁ * (kron2 uA₁ uB₁ * V₂)) := by
              rw [show
                    singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                      singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedAB V₁ * singleQubitLayer uA₁ uB₁ uC₁ *
                        embedAB V₂) from by noncomm_ring]
              rw [embedAB_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                    (singleQubitLayer I₂ I₂ uC₁ *
                      embedAB (V₁ * (kron2 uA₁ uB₁ * V₂))) =
                  (singleQubitLayer u_pA u_pB u_pC *
                     singleQubitLayer I₂ I₂ uC₁) *
                    embedAB (V₁ * (kron2 uA₁ uB₁ * V₂))
                  from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂) *
                    (singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                      singleQubitLayer uA uB uC) from by noncomm_ring]
            rw [h_inner_merge, h_outer_merge]
            have hV_inner : IsUnitary4 (V₁ * (kron2 uA₁ uB₁ * V₂)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hA₁ hB₁) hV₂)
            have hV_outer : IsUnitary4 (V₃ * (kron2 uA₃ uC₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hA₃ hC₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_AC_at_3_2_canonical
                (V₁ * (kron2 uA₁ uB₁ * V₂))
                (V₃ * (kron2 uA₃ uC₃ * V))
                hV_inner hV_outer
                u_pA u_pB (u_pC * uC₁) uA₂ (uB₂ * uB₃) uC₂ uA uB uC
                h_pA h_pB (isUnitary2_mul h_pC hC₁)
                hA₂ (isUnitary2_mul hB₂ hB₃) hC₂ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            rw [show
                  singleQubitLayer u_pA u_pB (u_pC * uC₁) *
                    embedAB (V₁ * (kron2 uA₁ uB₁ * V₂)) *
                    (singleQubitLayer uA₂ (uB₂ * uB₃) uC₂ *
                      embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                      singleQubitLayer uA uB uC) =
                  singleQubitLayer u_pA u_pB (u_pC * uC₁) *
                    embedAB (V₁ * (kron2 uA₁ uB₁ * V₂)) *
                    singleQubitLayer uA₂ (uB₂ * uB₃) uC₂ *
                    embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- BC-AB-AC-AC: adjacent AC pair at slots (3,4) merges, leaving
          -- BC-AB-AC = pattern #3 (AC-BC-AB-AC) with V₁ = 1.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have hW : IsUnitary4 (V₃ * (kron2 uA₃ uC₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hA₃ hC₃) hV)
            have h_merge := merge34_AC (embedBC V₁) (embedAB V₂) V₃ V
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            have h_chain := sandwich_BC_AB_AC_to_4embed V₁ V₂
              (V₃ * (kron2 uA₃ uC₃ * V))
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ (uB₂ * uB₃) uC₂ uA uB uC
            refine ⟨1, _, _, _,
              isUnitary4_one,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pB h_pC) hV₁)
                (isUnitary4_kron2 hB₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul
                    (isUnitary4_kron2 (isUnitary2_mul h_pA hA₁) isUnitary2_one)
                    hV₂)
                  (isUnitary4_kron2 hA₂ (isUnitary2_mul hB₂ hB₃)))
                (isUnitary4_kron2 isUnitary2_one hB),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₂) hW)
                (isUnitary4_kron2 hA hC), ?_⟩
            right; right; left
            rw [h_merge, embedAC_one, one_mul]
            exact h_chain
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AC-AB-AC-AC: V₁=AC, V₂=AB, V₃=V outer=AC outer pair.
          -- Pattern B outer-pair-merge → (3,2,1) AC-AB-AC. Pattern #4.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_outer_merge :
                singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                  singleQubitLayer uA uB uC =
                singleQubitLayer uA₂ (uB₂ * uB₃) uC₂ *
                  embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                  singleQubitLayer uA uB uC := by
              rw [show
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                      singleQubitLayer uA uB uC =
                    singleQubitLayer uA₂ uB₂ uC₂ *
                      (embedAC V₃ * singleQubitLayer uA₃ uB₃ uC₃ *
                        embedAC V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedAC_merge]
              rw [show singleQubitLayer uA₂ uB₂ uC₂ *
                    (singleQubitLayer I₂ uB₃ I₂ *
                      embedAC (V₃ * (kron2 uA₃ uC₃ * V))) *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer uA₂ uB₂ uC₂ *
                     singleQubitLayer I₂ uB₃ I₂) *
                    embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                    (singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                      singleQubitLayer uA uB uC) from by noncomm_ring]
            rw [h_outer_merge]
            have h_chain := sandwich_AC_AB_AC_to_4embed V₁ V₂
              (V₃ * (kron2 uA₃ uC₃ * V))
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ (uB₂ * uB₃) uC₂ uA uB uC
            have hV_merge : IsUnitary4 (V₃ * (kron2 uA₃ uC₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hA₃ hC₃) hV)
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV₁)
                (isUnitary4_kron2 hA₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul h_pB hB₁)) hV₂)
                (isUnitary4_kron2 hA₂ (isUnitary2_mul hB₂ hB₃)),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one hC₂) hV_merge)
                (isUnitary4_kron2 hA hC),
              isUnitary4_kron2 isUnitary2_one hB, ?_⟩
            right; right; right; left
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                    (singleQubitLayer uA₂ (uB₂ * uB₃) uC₂ *
                      embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                      singleQubitLayer uA uB uC) =
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAB V₂ *
                    singleQubitLayer uA₂ (uB₂ * uB₃) uC₂ *
                    embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_chain
      | compose_BC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,3,2) BC-AC-AC section (V outer=AC, V₃=AC, V₂=BC).
        -- V₃=V=AC outer pair → merge.
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            -- (4,3,2) BC-AC-AC: merge V₃,V (both AC) → (3,2) BC-AC chain.
            -- Pattern #6 (BC-AC-BC-AC).
            have h_merge :
                singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                  singleQubitLayer uA uB uC =
                singleQubitLayer uA₂ (uB₂ * uB₃) uC₂ *
                  embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                  singleQubitLayer uA uB uC := by
              rw [show
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                      singleQubitLayer uA uB uC =
                    singleQubitLayer uA₂ uB₂ uC₂ *
                      (embedAC V₃ * singleQubitLayer uA₃ uB₃ uC₃ *
                        embedAC V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedAC_merge]
              rw [show singleQubitLayer uA₂ uB₂ uC₂ *
                    (singleQubitLayer I₂ uB₃ I₂ *
                      embedAC (V₃ * (kron2 uA₃ uC₃ * V))) *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer uA₂ uB₂ uC₂ *
                     singleQubitLayer I₂ uB₃ I₂) *
                    embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have hV_merged : IsUnitary4 (V₃ * (kron2 uA₃ uC₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hA₃ hC₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AC_at_3_2_canonical V₂
                (V₃ * (kron2 uA₃ uC₃ * V)) hV₂ hV_merged
                u_pA u_pB u_pC uA₂ (uB₂ * uB₃) uC₂ uA uB uC
                h_pA h_pB h_pC hA₂ (isUnitary2_mul hB₂ hB₃) hC₂ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; left
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₂ *
                    (singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                      singleQubitLayer uA uB uC) from by noncomm_ring]
            rw [h_merge]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₂ *
                    (singleQubitLayer uA₂ (uB₂ * uB₃) uC₂ *
                      embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                      singleQubitLayer uA uB uC) =
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₂ *
                    singleQubitLayer uA₂ (uB₂ * uB₃) uC₂ *
                    embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AB-BC-AC-AC: V₁=AB, V₂=BC, V₃=V outer=AC outer pair.
          -- Pattern B outer-pair-merge → (3,2,1) AB-BC-AC. Pattern #2.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_outer_merge :
                singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                  singleQubitLayer uA uB uC =
                singleQubitLayer uA₂ (uB₂ * uB₃) uC₂ *
                  embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                  singleQubitLayer uA uB uC := by
              rw [show
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                      singleQubitLayer uA uB uC =
                    singleQubitLayer uA₂ uB₂ uC₂ *
                      (embedAC V₃ * singleQubitLayer uA₃ uB₃ uC₃ *
                        embedAC V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedAC_merge]
              rw [show singleQubitLayer uA₂ uB₂ uC₂ *
                    (singleQubitLayer I₂ uB₃ I₂ *
                      embedAC (V₃ * (kron2 uA₃ uC₃ * V))) *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer uA₂ uB₂ uC₂ *
                     singleQubitLayer I₂ uB₃ I₂) *
                    embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    (singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                      singleQubitLayer uA uB uC) from by noncomm_ring]
            rw [h_outer_merge]
            have h_chain := sandwich_AB_BC_AC_to_4embed V₁ V₂
              (V₃ * (kron2 uA₃ uC₃ * V))
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ (uB₂ * uB₃) uC₂ uA uB uC
            have hV_merge : IsUnitary4 (V₃ * (kron2 uA₃ uC₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hA₃ hC₃) hV)
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pB) hV₁)
                (isUnitary4_kron2 hA₁ hB₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 isUnitary2_one
                  (isUnitary2_mul h_pC hC₁)) hV₂)
                (isUnitary4_kron2 (isUnitary2_mul hB₂ hB₃) hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₂ isUnitary2_one) hV_merge)
                (isUnitary4_kron2 hA hC),
              isUnitary4_kron2 isUnitary2_one hB, ?_⟩
            right; left
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    (singleQubitLayer uA₂ (uB₂ * uB₃) uC₂ *
                      embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                      singleQubitLayer uA uB uC) =
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    singleQubitLayer uA₂ (uB₂ * uB₃) uC₂ *
                    embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_chain
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) BC-BC-AC-AC: V₁=V₂=BC inner pair, V₃=V outer=AC outer pair.
          -- Pattern F (both-pair-merge): merge both pairs, reduce to (3,2) BC-AC.
          -- Pattern #6 (BC-AC-BC-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_outer_merge :
                singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                  singleQubitLayer uA uB uC =
                singleQubitLayer uA₂ (uB₂ * uB₃) uC₂ *
                  embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                  singleQubitLayer uA uB uC := by
              rw [show
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                      singleQubitLayer uA uB uC =
                    singleQubitLayer uA₂ uB₂ uC₂ *
                      (embedAC V₃ * singleQubitLayer uA₃ uB₃ uC₃ *
                        embedAC V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedAC_merge]
              rw [show singleQubitLayer uA₂ uB₂ uC₂ *
                    (singleQubitLayer I₂ uB₃ I₂ *
                      embedAC (V₃ * (kron2 uA₃ uC₃ * V))) *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer uA₂ uB₂ uC₂ *
                     singleQubitLayer I₂ uB₃ I₂) *
                    embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            have h_inner_merge :
                singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                  singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ =
                singleQubitLayer (u_pA * uA₁) u_pB u_pC *
                  embedBC (V₁ * (kron2 uB₁ uC₁ * V₂)) := by
              rw [show
                    singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                      singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ =
                    singleQubitLayer u_pA u_pB u_pC *
                      (embedBC V₁ * singleQubitLayer uA₁ uB₁ uC₁ *
                        embedBC V₂) from by noncomm_ring]
              rw [embedBC_merge]
              rw [show singleQubitLayer u_pA u_pB u_pC *
                    (singleQubitLayer uA₁ I₂ I₂ *
                      embedBC (V₁ * (kron2 uB₁ uC₁ * V₂))) =
                  (singleQubitLayer u_pA u_pB u_pC *
                     singleQubitLayer uA₁ I₂ I₂) *
                    embedBC (V₁ * (kron2 uB₁ uC₁ * V₂))
                  from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂) *
                    (singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                      singleQubitLayer uA uB uC) from by noncomm_ring]
            rw [h_inner_merge, h_outer_merge]
            have hV_inner : IsUnitary4 (V₁ * (kron2 uB₁ uC₁ * V₂)) :=
              isUnitary4_mul hV₁ (isUnitary4_mul (isUnitary4_kron2 hB₁ hC₁) hV₂)
            have hV_outer : IsUnitary4 (V₃ * (kron2 uA₃ uC₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hA₃ hC₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AC_at_3_2_canonical
                (V₁ * (kron2 uB₁ uC₁ * V₂))
                (V₃ * (kron2 uA₃ uC₃ * V))
                hV_inner hV_outer
                (u_pA * uA₁) u_pB u_pC uA₂ (uB₂ * uB₃) uC₂ uA uB uC
                (isUnitary2_mul h_pA hA₁) h_pB h_pC
                hA₂ (isUnitary2_mul hB₂ hB₃) hC₂ hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; left
            rw [show
                  singleQubitLayer (u_pA * uA₁) u_pB u_pC *
                    embedBC (V₁ * (kron2 uB₁ uC₁ * V₂)) *
                    (singleQubitLayer uA₂ (uB₂ * uB₃) uC₂ *
                      embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                      singleQubitLayer uA uB uC) =
                  singleQubitLayer (u_pA * uA₁) u_pB u_pC *
                    embedBC (V₁ * (kron2 uB₁ uC₁ * V₂)) *
                    singleQubitLayer uA₂ (uB₂ * uB₃) uC₂ *
                    embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AC-BC-AC-AC: V₁=AC, V₂=BC, V₃=V outer=AC outer pair.
          -- Pattern B outer-pair-merge → (3,2,1) AC-BC-AC. Pattern #9.
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_outer_merge :
                singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                  singleQubitLayer uA uB uC =
                singleQubitLayer uA₂ (uB₂ * uB₃) uC₂ *
                  embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                  singleQubitLayer uA uB uC := by
              rw [show
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                      singleQubitLayer uA uB uC =
                    singleQubitLayer uA₂ uB₂ uC₂ *
                      (embedAC V₃ * singleQubitLayer uA₃ uB₃ uC₃ *
                        embedAC V) *
                      singleQubitLayer uA uB uC from by noncomm_ring]
              rw [embedAC_merge]
              rw [show singleQubitLayer uA₂ uB₂ uC₂ *
                    (singleQubitLayer I₂ uB₃ I₂ *
                      embedAC (V₃ * (kron2 uA₃ uC₃ * V))) *
                    singleQubitLayer uA uB uC =
                  (singleQubitLayer uA₂ uB₂ uC₂ *
                     singleQubitLayer I₂ uB₃ I₂) *
                    embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
              rw [singleQubitLayer_mul]
              simp [I₂]
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    (singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                      singleQubitLayer uA uB uC) from by noncomm_ring]
            rw [h_outer_merge]
            have h_chain := sandwich_AC_BC_AC_to_4embed V₁ V₂
              (V₃ * (kron2 uA₃ uC₃ * V))
              u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ (uB₂ * uB₃) uC₂ uA uB uC
            have hV_merge : IsUnitary4 (V₃ * (kron2 uA₃ uC₃ * V)) :=
              isUnitary4_mul hV₃ (isUnitary4_mul (isUnitary4_kron2 hA₃ hC₃) hV)
            refine ⟨_, _, _, _,
              isUnitary4_mul (isUnitary4_mul (isUnitary4_kron2 h_pA h_pC) hV₁)
                (isUnitary4_kron2 hA₁ hC₁),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2
                  (isUnitary2_mul h_pB hB₁) isUnitary2_one) hV₂)
                (isUnitary4_kron2 (isUnitary2_mul hB₂ hB₃) hC₂),
              isUnitary4_mul
                (isUnitary4_mul (isUnitary4_kron2 hA₂ isUnitary2_one) hV_merge)
                (isUnitary4_kron2 hA hC),
              isUnitary4_kron2 hB isUnitary2_one, ?_⟩
            right; right; right; right; right; right; right; right
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    (singleQubitLayer uA₂ (uB₂ * uB₃) uC₂ *
                      embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                      singleQubitLayer uA uB uC) =
                  singleQubitLayer u_pA u_pB u_pC * embedAC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedBC V₂ *
                    singleQubitLayer uA₂ (uB₂ * uB₃) uC₂ *
                    embedAC (V₃ * (kron2 uA₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_chain
      | compose_AC V₂ hV₂ uA₂ uB₂ uC₂ hA₂ hB₂ hC₂ h1 =>
        -- (4,3,2) AC-AC-AC triple same-XY merge. Pattern #7.
        cases h1 with
        | weaken h0 =>
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have hV_merged : IsUnitary4
                (V₂ * (kron2 uA₂ uC₂ * V₃) * (kron2 uA₃ uC₃ * V)) :=
              isUnitary4_mul
                (isUnitary4_mul hV₂
                  (isUnitary4_mul (isUnitary4_kron2 hA₂ hC₂) hV₃))
                (isUnitary4_mul (isUnitary4_kron2 hA₃ hC₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleAC_canonical
                (V₂ * (kron2 uA₂ uC₂ * V₃) * (kron2 uA₃ uC₃ * V))
                hV_merged
                u_pA ((u_pB * uB₂) * uB₃) u_pC h_pA
                (isUnitary2_mul (isUnitary2_mul h_pB hB₂) hB₃) h_pC
                uA uB uC hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            rw [sandwich_AC_AC_AC_to_AC V₂ V₃ V
                  u_pA u_pB u_pC uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC]
            exact h_eq
        | compose_AB V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AB-AC-AC-AC: V₁=AB, V₂=V₃=V=AC. Merge outer 3 ACs.
          -- Pattern #7 (AB-AC-AB-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge_inner :
                singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                  singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                  singleQubitLayer uA uB uC =
                singleQubitLayer uA₁ ((uB₁ * uB₂) * uB₃) uC₁ *
                  embedAC (V₂ * (kron2 uA₂ uC₂ * V₃) *
                    (kron2 uA₃ uC₃ * V)) *
                  singleQubitLayer uA uB uC :=
              sandwich_AC_AC_AC_to_AC V₂ V₃ V
                uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    (singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                      singleQubitLayer uA uB uC) from by noncomm_ring]
            rw [h_merge_inner]
            have hV_merged : IsUnitary4
                (V₂ * (kron2 uA₂ uC₂ * V₃) * (kron2 uA₃ uC₃ * V)) :=
              isUnitary4_mul
                (isUnitary4_mul hV₂
                  (isUnitary4_mul (isUnitary4_kron2 hA₂ hC₂) hV₃))
                (isUnitary4_mul (isUnitary4_kron2 hA₃ hC₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_AB_AC_at_3_2_canonical V₁
                (V₂ * (kron2 uA₂ uC₂ * V₃) * (kron2 uA₃ uC₃ * V))
                hV₁ hV_merged
                u_pA u_pB u_pC uA₁ ((uB₁ * uB₂) * uB₃) uC₁ uA uB uC
                h_pA h_pB h_pC hA₁
                (isUnitary2_mul (isUnitary2_mul hB₁ hB₂) hB₃) hC₁
                hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    (singleQubitLayer uA₁ ((uB₁ * uB₂) * uB₃) uC₁ *
                      embedAC (V₂ * (kron2 uA₂ uC₂ * V₃) *
                        (kron2 uA₃ uC₃ * V)) *
                      singleQubitLayer uA uB uC) =
                  singleQubitLayer u_pA u_pB u_pC * embedAB V₁ *
                    singleQubitLayer uA₁ ((uB₁ * uB₂) * uB₃) uC₁ *
                    embedAC (V₂ * (kron2 uA₂ uC₂ * V₃) *
                      (kron2 uA₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_eq
        | compose_BC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) BC-AC-AC-AC: V₁=BC, V₂=V₃=V=AC. Merge outer 3 ACs.
          -- Pattern #6 (BC-AC-BC-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have h_merge_inner :
                singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                  singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                  singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                  singleQubitLayer uA uB uC =
                singleQubitLayer uA₁ ((uB₁ * uB₂) * uB₃) uC₁ *
                  embedAC (V₂ * (kron2 uA₂ uC₂ * V₃) *
                    (kron2 uA₃ uC₃ * V)) *
                  singleQubitLayer uA uB uC :=
              sandwich_AC_AC_AC_to_AC V₂ V₃ V
                uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃ uA uB uC
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                    singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                    singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                    singleQubitLayer uA uB uC =
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    (singleQubitLayer uA₁ uB₁ uC₁ * embedAC V₂ *
                      singleQubitLayer uA₂ uB₂ uC₂ * embedAC V₃ *
                      singleQubitLayer uA₃ uB₃ uC₃ * embedAC V *
                      singleQubitLayer uA uB uC) from by noncomm_ring]
            rw [h_merge_inner]
            have hV_merged : IsUnitary4
                (V₂ * (kron2 uA₂ uC₂ * V₃) * (kron2 uA₃ uC₃ * V)) :=
              isUnitary4_mul
                (isUnitary4_mul hV₂
                  (isUnitary4_mul (isUnitary4_kron2 hA₂ hC₂) hV₃))
                (isUnitary4_mul (isUnitary4_kron2 hA₃ hC₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unitaryCircuit_4_BC_AC_at_3_2_canonical V₁
                (V₂ * (kron2 uA₂ uC₂ * V₃) * (kron2 uA₃ uC₃ * V))
                hV₁ hV_merged
                u_pA u_pB u_pC uA₁ ((uB₁ * uB₂) * uB₃) uC₁ uA uB uC
                h_pA h_pB h_pC hA₁
                (isUnitary2_mul (isUnitary2_mul hB₁ hB₂) hB₃) hC₁
                hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; left
            rw [show
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    (singleQubitLayer uA₁ ((uB₁ * uB₂) * uB₃) uC₁ *
                      embedAC (V₂ * (kron2 uA₂ uC₂ * V₃) *
                        (kron2 uA₃ uC₃ * V)) *
                      singleQubitLayer uA uB uC) =
                  singleQubitLayer u_pA u_pB u_pC * embedBC V₁ *
                    singleQubitLayer uA₁ ((uB₁ * uB₂) * uB₃) uC₁ *
                    embedAC (V₂ * (kron2 uA₂ uC₂ * V₃) *
                      (kron2 uA₃ uC₃ * V)) *
                    singleQubitLayer uA uB uC from by noncomm_ring]
            exact h_eq
        | compose_AC V₁ hV₁ uA₁ uB₁ uC₁ hA₁ hB₁ hC₁ h0 =>
          -- (4,3,2,1) AC-AC-AC-AC: all 4 gates AC, full 4-way merge.
          -- Pattern #7 (AB-AC-AB-AC).
          cases h0 with
          | product u_pA u_pB u_pC h_pA h_pB h_pC =>
            have hV_merged : IsUnitary4
                (V₁ * (kron2 uA₁ uC₁ * V₂) * (kron2 uA₂ uC₂ * V₃) *
                  (kron2 uA₃ uC₃ * V)) :=
              isUnitary4_mul
                (isUnitary4_mul
                  (isUnitary4_mul hV₁
                    (isUnitary4_mul (isUnitary4_kron2 hA₁ hC₁) hV₂))
                  (isUnitary4_mul (isUnitary4_kron2 hA₂ hC₂) hV₃))
                (isUnitary4_mul (isUnitary4_kron2 hA₃ hC₃) hV)
            obtain ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', h_eq⟩ :=
              unrestrictedCircuit_singleAC_canonical
                (V₁ * (kron2 uA₁ uC₁ * V₂) * (kron2 uA₂ uC₂ * V₃) *
                  (kron2 uA₃ uC₃ * V))
                hV_merged
                u_pA (((u_pB * uB₁) * uB₂) * uB₃) u_pC h_pA
                (isUnitary2_mul
                  (isUnitary2_mul (isUnitary2_mul h_pB hB₁) hB₂) hB₃)
                h_pC
                uA uB uC hA hB hC
            refine ⟨V₁', V₂', V₃', V₄', hV₁', hV₂', hV₃', hV₄', ?_⟩
            right; right; right; right; right; right; left
            rw [sandwich_AC_AC_AC_AC_to_AC V₁ V₂ V₃ V
                  u_pA u_pB u_pC uA₁ uB₁ uC₁ uA₂ uB₂ uC₂ uA₃ uB₃ uC₃
                  uA uB uC]
            exact h_eq

/-- Variant of `four_unrestricted_implies_S4_or_S5` for the
    `UnitaryUnrestrictedCircuit` type. As of iter 677, this uses the direct
    canonical form (`unitaryUnrestrictedCircuit_4_canonical_direct`) rather
    than delegating through the unrestricted version, bypassing the 16
    dispatcher sorries in `unrestrictedCircuit_4_canonical`. -/
theorem four_unitaryUnrestricted_implies_S4_or_S5 (Dg : DiagGate3)
    (h : UnitaryUnrestrictedCircuit 4 Dg.toMatrix) :
    Dg.inS4 ∨ Dg.inS5 := by
  obtain ⟨V₁, V₂, V₃, V₄, hV₁, hV₂, hV₃, hV₄, hcase⟩ :=
    unitaryUnrestrictedCircuit_4_canonical_direct Dg h
  rcases hcase with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact fourGate_BC_AC_AB_BC_implies_S4_or_S5 Dg V₁ V₂ V₃ V₄ hV₁ hV₂ hV₃ hV₄ h1
  · exact fourGate_AB_BC_AC_AB_implies_S4_or_S5 Dg V₁ V₂ V₃ V₄ hV₁ hV₂ hV₃ hV₄ h2
  · exact fourGate_AC_BC_AB_AC_implies_S4_or_S5 Dg V₁ V₂ V₃ V₄ hV₁ hV₂ hV₃ hV₄ h3
  · exact fourGate_AC_AB_AC_AB_implies_S4_or_S5 Dg V₁ V₂ V₃ V₄ hV₁ hV₂ hV₃ hV₄ h4
  · exact fourGate_BC_AB_BC_AB_implies_S4_or_S5 Dg V₁ V₂ V₃ V₄ hV₁ hV₂ hV₃ hV₄ h5
  · exact fourGate_BC_AC_BC_AC_implies_S4_or_S5 Dg V₁ V₂ V₃ V₄ hV₁ hV₂ hV₃ hV₄ h6
  · exact fourGate_AB_AC_AB_AC_implies_S4_or_S5 Dg V₁ V₂ V₃ V₄ hV₁ hV₂ hV₃ hV₄ h7
  · exact fourGate_AB_BC_AB_BC_implies_S4_or_S5 Dg V₁ V₂ V₃ V₄ hV₁ hV₂ hV₃ hV₄ h8
  · exact fourGate_AC_BC_AC_BC_implies_S4_or_S5 Dg V₁ V₂ V₃ V₄ hV₁ hV₂ hV₃ hV₄ h9

/-- Iter 735: Alternative entry point routing through SWAP_AC + paper Lemma 5.1.
    Equivalent to `four_unitaryUnrestricted_implies_S4_or_S5` but routes the
    chain through the swap-conjugated DiagGate3. Demonstrates the SWAP_AC
    bypass infrastructure (iters 733-734) is wired correctly end-to-end.

    For Dg whose chain is in one of the 3 covered 3-XY orderings (AC-BC-AB,
    AB-BC-AC, BC-AC-AB), this entry point would call the standard dispatcher
    on swapAC(Dg) — which has chain in one of the 3 MISSING orderings, so
    would hit a dispatcher sorry. So this alone doesn't help close anything,
    but it verifies the SWAP plumbing.

    The genuinely useful application: replace canonical_direct's missing-
    ordering sorries with calls to this theorem (refactor in iter 736+). -/
theorem four_unitaryUnrestricted_implies_S4_or_S5_via_swap_AC
    (Dg : DiagGate3) (h : UnitaryUnrestrictedCircuit 4 Dg.toMatrix) :
    Dg.inS4 ∨ Dg.inS5 :=
  (DiagGate3.swapAC_inS4_or_S5_iff Dg).mp
    (four_unitaryUnrestricted_implies_S4_or_S5 Dg.swapAC
      (swap_ac_unitaryUnrestricted_DiagGate3 Dg h))

/-- Iter 743 (stretch sketch): sigma-typed canonical-form variant. Returns
    EITHER a 4-V canonical form for Dg directly OR a 4-V canonical form for
    swapAC(Dg). When Dg's chain is in a missing 3-XY ordering, the direct
    branch fails but the swap branch succeeds (since SWAP_AC maps missing
    orderings to covered ones, per iter 731 finding).

    This signature lets `four_unitaryUnrestricted_implies_S4_or_S5` dispatch
    on which branch was returned, applying paper Lemma 5.1
    (`swapAC_inS4_or_S5_iff`) to the swap branch to obtain Dg ∈ S₄ ∪ S₅.

    Statement-only sketch (body = sorry). Implementation requires:
    1. Restructure canonical_direct's missing-ordering case branches to
       construct the swap-conjugated UnitaryUnrestrictedCircuit and recurse
       (or call the closed leaves of canonical_direct directly).
    2. Modify `four_unitaryUnrestricted_implies_S4_or_S5` to dispatch on the
       sigma-typed return. Both refactors are tractable but invasive.

    Estimated effort: ~200-400 lines refactor work. NOT undertaken in this
    autonomous loop session. -/
private theorem unitaryUnrestrictedCircuit_4_canonical_direct_or_swap
    (Dg : DiagGate3) (h : UnitaryUnrestrictedCircuit 4 Dg.toMatrix) :
    (∃ V₁ V₂ V₃ V₄ : Mat4,
      IsUnitary4 V₁ ∧ IsUnitary4 V₂ ∧ IsUnitary4 V₃ ∧ IsUnitary4 V₄ ∧
      (Dg.toMatrix = embedBC V₁ * embedAC V₂ * embedAB V₃ * embedBC V₄ ∨
       Dg.toMatrix = embedAB V₁ * embedBC V₂ * embedAC V₃ * embedAB V₄ ∨
       Dg.toMatrix = embedAC V₁ * embedBC V₂ * embedAB V₃ * embedAC V₄ ∨
       Dg.toMatrix = embedAC V₁ * embedAB V₂ * embedAC V₃ * embedAB V₄ ∨
       Dg.toMatrix = embedBC V₁ * embedAB V₂ * embedBC V₃ * embedAB V₄ ∨
       Dg.toMatrix = embedBC V₁ * embedAC V₂ * embedBC V₃ * embedAC V₄ ∨
       Dg.toMatrix = embedAB V₁ * embedAC V₂ * embedAB V₃ * embedAC V₄ ∨
       Dg.toMatrix = embedAB V₁ * embedBC V₂ * embedAB V₃ * embedBC V₄ ∨
       Dg.toMatrix = embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄)) ∨
    (∃ V₁ V₂ V₃ V₄ : Mat4,
      IsUnitary4 V₁ ∧ IsUnitary4 V₂ ∧ IsUnitary4 V₃ ∧ IsUnitary4 V₄ ∧
      (Dg.swapAC.toMatrix = embedBC V₁ * embedAC V₂ * embedAB V₃ * embedBC V₄ ∨
       Dg.swapAC.toMatrix = embedAB V₁ * embedBC V₂ * embedAC V₃ * embedAB V₄ ∨
       Dg.swapAC.toMatrix = embedAC V₁ * embedBC V₂ * embedAB V₃ * embedAC V₄ ∨
       Dg.swapAC.toMatrix = embedAC V₁ * embedAB V₂ * embedAC V₃ * embedAB V₄ ∨
       Dg.swapAC.toMatrix = embedBC V₁ * embedAB V₂ * embedBC V₃ * embedAB V₄ ∨
       Dg.swapAC.toMatrix = embedBC V₁ * embedAC V₂ * embedBC V₃ * embedAC V₄ ∨
       Dg.swapAC.toMatrix = embedAB V₁ * embedAC V₂ * embedAB V₃ * embedAC V₄ ∨
       Dg.swapAC.toMatrix = embedAB V₁ * embedBC V₂ * embedAB V₃ * embedBC V₄ ∨
       Dg.swapAC.toMatrix = embedAC V₁ * embedBC V₂ * embedAC V₃ * embedBC V₄)) := by
  -- Iter 763: trivial closure via Or.inl (always-LEFT). This makes the
  -- sketch a verified theorem (not a `sorry` stub), but vacuously: it
  -- always picks the LEFT branch, which propagates canonical_direct's 31
  -- sorries. Downstream callers pattern-matching on the result will
  -- always see LEFT and get canonical_direct's behavior unchanged.
  --
  -- The genuine BYPASS interpretation (returning RIGHT for missing 3-XY
  -- orderings to enable Lemma 5.1 conversion) requires the future work
  -- described in this theorem's docstring (~200-400 line refactor).
  exact Or.inl (unitaryUnrestrictedCircuit_4_canonical_direct Dg h)

/-! Retired iter 1043: `four_neighbor_implies_S4_or_S5` and
`five_neighbor_implies_S4_or_S5`, which were stated over the non-unitary
`NeighborCircuit`. Their content is below in unitary form. -/

/-- Theorem 7.1(4), forward direction: a diagonal gate implementable with 4
    neighbor gates (unitary 2-qubit gates) is in `S₄ ∪ S₅`. Routes through
    `unitaryUnrestrictedCircuit_4_canonical_direct` (paper Lemma C.1, closed
    iter 1040), so it is `sorryAx`-free. -/
theorem four_unitaryNeighbor_implies_S4_or_S5 (Dg : DiagGate3)
    (h : UnitaryNeighborCircuit 4 Dg.toMatrix) :
    Dg.inS4 ∨ Dg.inS5 :=
  four_unitaryUnrestricted_implies_S4_or_S5 Dg
    (unitaryNeighborCircuit_to_unitaryUnrestricted h)

/-- Combined (Theorem 4.5 + Theorem 6.2): a diagonal gate implementable with
    ≤ 5 neighbor gates (unitary 2-qubit gates) is in `S₄ ∪ S₅`.

    Iter 1043: routes through `five_unitaryNeighbor_to_four_unitaryUnrestricted`
    (paper Theorem 4.5, unitary form) rather than the retired non-unitary
    chain. -/
theorem five_unitaryNeighbor_implies_S4_or_S5 (Dg : DiagGate3)
    (h : UnitaryNeighborCircuit 5 Dg.toMatrix) :
    Dg.inS4 ∨ Dg.inS5 :=
  four_unitaryUnrestricted_implies_S4_or_S5 Dg
    (five_unitaryNeighbor_to_four_unitaryUnrestricted Dg.toMatrix ⟨Dg, rfl⟩ h)

/-! ## Upper bound: every diagonal gate needs at most 6 neighbor gates

Theorem 7.1(5): D ∈ S₆ ↔ 6 neighbor gates. Since S₆ = all diagonal gates,
every diagonal gate can be implemented with 6 neighbor gates.
(Construction given in Section 3 of the paper.)

**Note**: This theorem is NOT required for the main result `CCZ_requires_six_neighbor`,
which uses the specific construction `ccz_six_neighbor` (HP/SixGate.lean) for the CCZ case.
The general statement for arbitrary `DiagGate3` requires the paper's Section 3 construction
(parameterized 6-gate decomposition for any 8-entry diagonal unitary). -/

/-- Standard 2-qubit CNOT with the FIRST qubit as control: `0→0, 1→1, 2→3, 3→2`.
    Embedded on AB it implements `b ↦ a ⊕ b`. (Local copy: `HP/SixGate.lean`'s
    `CNOT_4_std` is not visible here — that file is not upstream of this one.) -/
def CNOT_AB_4 : Mat4 :=
  Matrix.of fun (i j : Fin 4) =>
    match i, j with
    | 0, 0 => (1 : ℂ) | 1, 1 => 1 | 2, 3 => 1 | 3, 2 => 1 | _, _ => 0

/-- `embedAC` of a diagonal 4×4 is diagonal, with entry `E[2a+c]` at index
    `4a+2b+c`. -/
theorem embedAC_diagonal4 (a0 a1 a2 a3 : ℂ) :
    embedAC (Matrix.diagonal ![a0, a1, a2, a3]) =
      Matrix.diagonal ![a0, a1, a0, a1, a2, a3, a2, a3] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedAC, Matrix.diagonal_apply, Matrix.of_apply]

/-- `embedBC` of a diagonal 4×4 is diagonal, with entry `G[2b+c]` at index
    `4a+2b+c`. -/
theorem embedBC_diagonal4 (b0 b1 b2 b3 : ℂ) :
    embedBC (Matrix.diagonal ![b0, b1, b2, b3]) =
      Matrix.diagonal ![b0, b1, b2, b3, b0, b1, b2, b3] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedBC, Matrix.diagonal_apply, Matrix.of_apply]

set_option maxHeartbeats 8000000 in
-- Heartbeats raised: 3-fold 8×8 product expanded entrywise over 64 index pairs.
/-- Conjugating a diagonal BC gate by `embedAB CNOT` re-indexes it by `b ↦ a ⊕ b`:
    the result is diagonal with entry `F[2(a ⊕ b)+c]` at index `4a+2b+c`.
    This is the only step of the Section-3 construction that moves information
    between qubits, and it is what supplies the `Z_A Z_B Z_C` component. -/
theorem cnot_conj_diagonal4 (f0 f1 f2 f3 : ℂ) :
    embedAB CNOT_AB_4 * embedBC (Matrix.diagonal ![f0, f1, f2, f3]) * embedAB CNOT_AB_4 =
      Matrix.diagonal ![f0, f1, f2, f3, f2, f3, f0, f1] := by
  ext i j
  simp only [embedAB, embedBC, CNOT_AB_4, Matrix.mul_apply, Matrix.of_apply,
             Fin.sum_univ_eight]
  fin_cases i <;> fin_cases j <;> simp

set_option maxHeartbeats 2000000 in
-- Heartbeats raised: three `noncomm_ring` re-brackets of a 6-factor 8×8 chain.
/-- **Paper Section 3, general six-gate construction.**

    Every 3-qubit diagonal gate is a product of six neighbor gates in the
    alternating pattern `BC-AB-BC-AB-BC-AB`. The skeleton is the same one
    `HP/SixGate.lean` uses for CCZ; here the three diagonal factors are
    parameterized by the target's entries.

    Why it works, in the `Z`-basis: writing the phase as
    `Σ_S θ_S Π_{j∈S} Z_j`, the four blocks cover all eight components —
    `embedAC E` (obtained free as `SWAP_BC · embedAB E · SWAP_BC`) gives
    `I, Z_A, Z_C, Z_A Z_C`; `embedBC G` gives `I, Z_B, Z_C, Z_B Z_C`; and the
    CNOT-conjugated `embedBC F` gives `I, Z_A Z_B, Z_C, Z_A Z_B Z_C`. A
    fourth `embedAB` block would be redundant, which is why six gates suffice.

    Concretely the diagonal entries must satisfy
    `E[2a+c] · G[2b+c] · F[2(a⊕b)+c] = d[4a+2b+c]`, and the displayed choice
    solves those eight equations; `s0, s1` are the square roots that the two
    consistency conditions force (this is why CCZ's version uses `CS`, a square
    root of `CZ`). -/
theorem sixGate_general (Dg : DiagGate3) (s0 s1 : ℂ)
    (hs0 : s0 ^ 2 = Dg.d 0 * Dg.d 2 * Dg.d 4 / Dg.d 6)
    (hs1 : s1 ^ 2 = Dg.d 1 * Dg.d 3 * Dg.d 5 / Dg.d 7)
    (hs0ne : s0 ≠ 0) (hs1ne : s1 ≠ 0) :
    embedBC SWAP_4 *
      embedAB (Matrix.diagonal ![1, 1, Dg.d 4 / s0, Dg.d 5 / s1]) *
      embedBC (SWAP_4 * Matrix.diagonal ![1, 1, Dg.d 2 / s0, Dg.d 3 / s1]) *
      embedAB CNOT_AB_4 *
      embedBC (Matrix.diagonal ![Dg.d 0, Dg.d 1, s0, s1]) *
      embedAB CNOT_AB_4 = Dg.toMatrix := by
  have h6 : Dg.d 6 ≠ 0 := Dg.d_ne_zero 6
  have h7 : Dg.d 7 ≠ 0 := Dg.d_ne_zero 7
  have hs0' : s0 ^ 2 * Dg.d 6 = Dg.d 0 * Dg.d 2 * Dg.d 4 := by rw [hs0]; field_simp
  have hs1' : s1 ^ 2 * Dg.d 7 = Dg.d 1 * Dg.d 3 * Dg.d 5 := by rw [hs1]; field_simp
  -- Split the third gate `BC(SWAP·G)` back into `BC(SWAP)·BC(G)`.
  rw [← embedBC_mul]
  -- Re-bracket into: [BC(SWAP)·AB(E)·BC(SWAP)] · BC(G) · [AB(N)·BC(F)·AB(N)].
  rw [show embedBC SWAP_4 *
        embedAB (Matrix.diagonal ![1, 1, Dg.d 4 / s0, Dg.d 5 / s1]) *
        (embedBC SWAP_4 * embedBC (Matrix.diagonal ![1, 1, Dg.d 2 / s0, Dg.d 3 / s1])) *
        embedAB CNOT_AB_4 *
        embedBC (Matrix.diagonal ![Dg.d 0, Dg.d 1, s0, s1]) *
        embedAB CNOT_AB_4 =
      (embedBC SWAP_4 *
        embedAB (Matrix.diagonal ![1, 1, Dg.d 4 / s0, Dg.d 5 / s1]) * embedBC SWAP_4) *
      embedBC (Matrix.diagonal ![1, 1, Dg.d 2 / s0, Dg.d 3 / s1]) *
      (embedAB CNOT_AB_4 * embedBC (Matrix.diagonal ![Dg.d 0, Dg.d 1, s0, s1]) *
        embedAB CNOT_AB_4) from by noncomm_ring]
  -- The SWAP-conjugated AB gate IS an AC gate — the two SWAPs cost nothing.
  rw [show embedBC SWAP_4 *
        embedAB (Matrix.diagonal ![1, 1, Dg.d 4 / s0, Dg.d 5 / s1]) * embedBC SWAP_4 =
      embedAC (Matrix.diagonal ![1, 1, Dg.d 4 / s0, Dg.d 5 / s1]) from by
    rw [← SWAP_BC_eq_embedBC]; exact swap_bc_embedAB _]
  -- All three blocks are now explicit 8×8 diagonals; multiply them entrywise.
  rw [embedAC_diagonal4, embedBC_diagonal4, cnot_conj_diagonal4]
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  unfold DiagGate3.toMatrix
  congr 1
  funext i
  fin_cases i <;> simp
  · field_simp
  · field_simp
  · field_simp
  · field_simp
  · field_simp; linear_combination -hs0'
  · field_simp; linear_combination -hs1'

/-- Theorem 7.1(5) (upper bound): every 3-qubit diagonal gate can be implemented
    with six neighbor gates. Closed iter 1041 via the parameterized Section-3
    construction `sixGate_general`; the two square roots exist because `ℂ` has
    `exp`/`log` and every diagonal entry is nonzero. -/
theorem six_neighbor_suffice (Dg : DiagGate3) :
    NeighborCircuit 6 Dg.toMatrix := by
  have hd : ∀ i, Dg.d i ≠ 0 := Dg.d_ne_zero
  have sqrt_ex : ∀ z : ℂ, z ≠ 0 → ∃ w : ℂ, w ^ 2 = z := by
    intro z hz
    refine ⟨Complex.exp (Complex.log z / 2), ?_⟩
    rw [sq, ← Complex.exp_add,
        show Complex.log z / 2 + Complex.log z / 2 = Complex.log z from by ring]
    exact Complex.exp_log hz
  have hz0 : Dg.d 0 * Dg.d 2 * Dg.d 4 / Dg.d 6 ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero (hd 0) (hd 2)) (hd 4)) (hd 6)
  have hz1 : Dg.d 1 * Dg.d 3 * Dg.d 5 / Dg.d 7 ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero (hd 1) (hd 3)) (hd 5)) (hd 7)
  obtain ⟨s0, hs0⟩ := sqrt_ex _ hz0
  obtain ⟨s1, hs1⟩ := sqrt_ex _ hz1
  have hs0ne : s0 ≠ 0 := fun h => hz0 (by rw [← hs0, h]; ring)
  have hs1ne : s1 ≠ 0 := fun h => hz1 (by rw [← hs1, h]; ring)
  rw [← sixGate_general Dg s0 s1 hs0 hs1 hs0ne hs1ne]
  have h : NeighborCircuit 6
    ((((((singleQubitLayer I₂ I₂ I₂ *
      embedBC SWAP_4 * singleQubitLayer I₂ I₂ I₂) *
      embedAB (Matrix.diagonal ![1, 1, Dg.d 4 / s0, Dg.d 5 / s1]) *
        singleQubitLayer I₂ I₂ I₂) *
      embedBC (SWAP_4 * Matrix.diagonal ![1, 1, Dg.d 2 / s0, Dg.d 3 / s1]) *
        singleQubitLayer I₂ I₂ I₂) *
      embedAB CNOT_AB_4 * singleQubitLayer I₂ I₂ I₂) *
      embedBC (Matrix.diagonal ![Dg.d 0, Dg.d 1, s0, s1]) * singleQubitLayer I₂ I₂ I₂) *
      embedAB CNOT_AB_4 * singleQubitLayer I₂ I₂ I₂) :=
    .compose_AB CNOT_AB_4 I₂ I₂ I₂ isUnitary2_one isUnitary2_one isUnitary2_one
      (.compose_BC (Matrix.diagonal ![Dg.d 0, Dg.d 1, s0, s1]) I₂ I₂ I₂
        isUnitary2_one isUnitary2_one isUnitary2_one
        (.compose_AB CNOT_AB_4 I₂ I₂ I₂ isUnitary2_one isUnitary2_one isUnitary2_one
          (.compose_BC (SWAP_4 * Matrix.diagonal ![1, 1, Dg.d 2 / s0, Dg.d 3 / s1])
            I₂ I₂ I₂ isUnitary2_one isUnitary2_one isUnitary2_one
            (.compose_AB (Matrix.diagonal ![1, 1, Dg.d 4 / s0, Dg.d 5 / s1])
              I₂ I₂ I₂ isUnitary2_one isUnitary2_one isUnitary2_one
              (.compose_BC SWAP_4 I₂ I₂ I₂ isUnitary2_one isUnitary2_one isUnitary2_one
                (.product I₂ I₂ I₂ isUnitary2_one isUnitary2_one isUnitary2_one))))))
  simp only [singleQubitLayer_one, mul_one, one_mul] at h
  exact h

end
