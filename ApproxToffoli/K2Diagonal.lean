import ApproxToffoli.RankOneSpectral

/-!
# (DIAGONAL TARGETS) at `k = 2`: the best two-gate approximation to a diagonal target is diagonal

The open lemma behind `d(6) = d(7) = sin(π/8)` is

> **(DIAGONAL TARGETS).**  For every diagonal 3-qubit gate `G` and every `k`,
> `max_{Y ∈ W_k} |tr(Gᴴ Y)| = max_{D ∈ W_k ∩ diag} |tr(Gᴴ D)|`,

where `W_k = K₁K₂K₁…` is an alternating word of `k` two-qubit neighbour gates.  `HS2` is the
single instance `G = CCZ`, `k = 5`.  `k = 1` is elementary.  **This file proves `k = 2`.**

## The reduction (not formalised here; see `notes/OPEN_PROBLEM.md` §7.61)

`α ⊗ 1_C` preserves the `A` index and `1_A ⊗ β` the `C` index, so only the diagonal blocks
survive: `tr(Gᴴ αβ) = Σ_{a,c} tr(D_ac A_a B_c)` with `D_ac = diag(ḡ_{a0c}, ḡ_{a1c})`.  The
functional is linear in each block, the diagonal blocks of a unitary are exactly the
contractions, and the extreme points of the contractions are the unitaries — so all four blocks
may be taken in `U(2)`.  Maximising over `B_0, B_1` turns the objective into
`‖D_00 + D_10 A‖_* + ‖D_01 + D_11 A‖_*` with `A = A_1A_0ᴴ`, and the claim becomes: *this is
maximised at a diagonal `A`*.

**The crucial hypothesis, missed for a whole session, is that the `D_ac` are UNITARY** (the
entries of a diagonal unitary `G` are unimodular).  That lets one normalise
`‖D_1 + D_2A‖_* = ‖1 + D_1ᴴD_2 A‖_*`, and with `C := D_1ᴴD_2 A`, `Δ := (D_3ᴴD_4)(D_1ᴴD_2)ᴴ`,

    max over A  =  max_{C ∈ U(2)} [ ‖1 + C‖_* + ‖1 + ΔC‖_* ],   `C` diagonal ⟺ `A` diagonal.

For **general** complex diagonal `D_i` — the `k=2` instance of the strictly stronger (ABELIAN)
conjecture — the statement is still open.

## What is proved here

`nuc2 M := sqrt(‖M‖²_F + 2|det M|)`, which is the nuclear norm of a `2×2` matrix (standard:
`(s₁+s₂)² = s₁² + s₂² + 2s₁s₂`).  That last identification is the one link left informal; every
step of the argument below is formal.

* `nucSq_one_add` — **Step 2**, the exact identity.  For `B ∈ U(2)` and `w` a square root of
  `det B`, with `x := Re w` and `z := Re(B₀₀ w̄)`,
  `‖1+B‖²_F + 2|det(1+B)| = 4 max{(1+x)(1+z), (1-x)(1-z)}`.
* `objTwo_le_boundary` — **Step 4**, the convexity step.  Written in the disk parameter
  `ζ := B₀₀ w̄` (so `‖ζ‖ = ‖B₀₀‖`, and `‖ζ‖ = 1` exactly on the diagonal locus), the objective is
  a max of four branches, each *monotone along a fixed direction*, so its maximum over the closed
  unit disk is attained on the unit circle.
* `k2_diagonal` — the two combined: for unitary diagonal `Δ` and any `C ∈ U(2)` there is a
  **diagonal** `C' ∈ U(2)` with `nuc2(1+C) + nuc2(1+ΔC) ≤ nuc2(1+C') + nuc2(1+ΔC')`.

Step 4 needs **neither convexity of the objective** (it has none: `‖·‖_*` is not convex in the
off-diagonality parameter — the square root destroys it) **nor any term-by-term argument** (a
single term is often maximised at `‖ζ‖ = 0`).  Only branchwise monotonicity along a fixed
direction, which the square root preserves.

## Closed form (§7.61.2, numerical certification in `PyScript/refl/step31_k2_proof.py`)

    max_{Y ∈ W_2} |tr(Gᴴ Y)| = 4 cos(d₁ᵉᶠᶠ/4) + 4 cos(d₂ᵉᶠᶠ/4),
    d_b = arg( g_{1b0} g_{0b1} / (g_{0b0} g_{1b1}) ),   dᵉᶠᶠ = min(d, 2π - d) ∈ [0, π],

`d_0, d_1` being exactly HP's two `S2` character defects.  For `CCZ` this is `4 + 2√2 = Φ_W(2)`.
The `k=5` curve `8 cos(θᵉᶠᶠ/8)` (§7.60) is the same computation with one character over all eight
entries instead of two characters over four entries each — so §7.56's Lagrange heuristic, and its
`θᵉᶠᶠ` reflection, are now **proved** at `k = 2`.
-/

open Matrix Complex

namespace K2Diagonal

/-! ### Generalities on `2×2` unitaries -/

/-- For a unitary matrix the adjugate is `det • conjTranspose`.  (`adjugate B = Bᴴ B adjugate B`.)
This is the source of both `trace_mul_star_eq` and `norm_entry_le_one`. -/
theorem adjugate_eq_det_smul_conjTranspose {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℂ) (hB : B ∈ Matrix.unitaryGroup n ℂ) : B.adjugate = B.det • Bᴴ := by
  have h1 : Bᴴ * B = 1 := hB.1
  calc B.adjugate = (Bᴴ * B) * B.adjugate := by rw [h1, one_mul]
    _ = Bᴴ * (B * B.adjugate) := by rw [mul_assoc]
    _ = Bᴴ * (B.det • (1 : Matrix n n ℂ)) := by rw [Matrix.mul_adjugate]
    _ = B.det • Bᴴ := by rw [Matrix.mul_smul, mul_one]

theorem norm_det_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℂ) (hB : B ∈ Matrix.unitaryGroup n ℂ) : ‖B.det‖ = 1 := by
  have h2 : B * Bᴴ = 1 := hB.2
  have h : B.det * (starRingEnd ℂ) B.det = 1 := by
    have h3 : (B * Bᴴ).det = (1 : Matrix n n ℂ).det := by rw [h2]
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h3
    exact h3
  have h4 : ‖B.det‖ * ‖B.det‖ = 1 := by
    have := congrArg norm h; simpa [norm_mul] using this
  nlinarith [norm_nonneg B.det]

/-- Every entry of a unitary is a contraction — here the `(0,0)` one, which is the only one used. -/
theorem norm_entry_le_one (B : Matrix (Fin 2) (Fin 2) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin 2) ℂ) : ‖B 0 0‖ ≤ 1 := by
  have h1 : Bᴴ * B = 1 := hB.1
  have h := congrFun (congrFun h1 0) 0
  rw [Matrix.mul_apply] at h
  simp only [Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
    show ∀ z : ℂ, star z = (starRingEnd ℂ) z from fun _ => rfl, Complex.conj_mul'] at h
  have h2 : ‖B 0 0‖ ^ 2 + ‖B 1 0‖ ^ 2 = 1 := by exact_mod_cast h
  nlinarith [norm_nonneg (B 0 0), sq_nonneg ‖B 1 0‖]

theorem diagonal_mem_unitary (d : Fin 2 → ℂ) (h : ∀ i, ‖d i‖ = 1) :
    Matrix.diagonal d ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  have h2 : d i * (starRingEnd ℂ) (d i) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h i]; norm_num
  simpa using h2

/-! ### Step 2 — the exact `2×2` identity -/

/-- The branch identity: `1 + xz + |x+z|` is the larger of two products.  This is what makes the
absolute value in `‖M‖²_* = ‖M‖²_F + 2|det M|` harmless. -/
theorem one_add_mul_add_abs (x z : ℝ) :
    1 + x * z + |x + z| = max ((1 + x) * (1 + z)) ((1 - x) * (1 - z)) := by
  rcases le_or_gt 0 (x + z) with h | h
  · rw [abs_of_nonneg h, max_eq_left (by nlinarith)]; ring
  · rw [abs_of_neg h, max_eq_right (by nlinarith)]; ring

/-- **Step 2.**  For `B ∈ U(2)` and `w` any square root of `det B`, with `x := Re w` and
`z := Re(B₀₀ w̄)`:  `‖1+B‖²_F + 2|det(1+B)| = 4 max{(1+x)(1+z), (1-x)(1-z)}`.

Both `Re tr B` and `det(1+B)` collapse: `tr B = 2zw` (its `w̄`-rotation is real, because
`conj(tr B) = tr B / det B` in `2×2`), and `det(1+B) = 1 + tr B + det B = 2w(x+z)`. -/
theorem nucSq_one_add (B : Matrix (Fin 2) (Fin 2) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (w : ℂ) (hw : w ^ 2 = B.det) :
    (Matrix.trace ((1 + B)ᴴ * (1 + B))).re + 2 * ‖(1 + B).det‖
      = 4 * max ((1 + w.re) * (1 + (B 0 0 * star w).re))
                ((1 - w.re) * (1 - (B 0 0 * star w).re)) := by
  have h1 : Bᴴ * B = 1 := hB.1
  have hw1 : ‖w‖ = 1 := by
    have h : ‖w‖ ^ 2 = 1 := by rw [← norm_pow, hw, norm_det_eq_one B hB]
    nlinarith [norm_nonneg w]
  have hws : w * star w = 1 := by
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw1]
  have hswv : (starRingEnd ℂ) w * w = 1 := by
    rw [show (starRingEnd ℂ) w = star w from rfl, mul_comm]; exact hws
  have hcw : ((w.re : ℝ) : ℂ) * 2 = w + star w := by
    rw [show star w = (starRingEnd ℂ) w from rfl, Complex.add_conj]; push_cast; ring
  set z : ℝ := (B 0 0 * star w).re with hz
  have hentry : B 1 1 = B.det * star (B 0 0) := by
    have h := congrFun (congrFun (adjugate_eq_det_smul_conjTranspose B hB) 0) 0
    rw [Matrix.adjugate_fin_two] at h; simpa using h
  have key : Matrix.trace B * star w = 2 * (z : ℂ) := by
    rw [Matrix.trace_fin_two, hentry, ← hw, add_mul,
      show w ^ 2 * star (B 0 0) * star w = (w * star w) * (w * star (B 0 0)) by ring, hws, one_mul,
      show w * star (B 0 0) = (starRingEnd ℂ) (B 0 0 * star w) by simp [mul_comm],
      Complex.add_conj, hz]
    push_cast; ring
  have htr : Matrix.trace B = 2 * (z : ℂ) * w := by
    have h := congrArg (· * w) key
    simpa [mul_assoc, hswv] using h
  have hFro : Matrix.trace ((1 + B)ᴴ * (1 + B)) = 4 + (Matrix.trace B + star (Matrix.trace B)) := by
    have h : (1 + B)ᴴ * (1 + B) = 1 + 1 + B + Bᴴ := by
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, add_mul, mul_add, mul_add, h1]
      simp only [Matrix.one_mul, Matrix.mul_one]; abel
    rw [h]; simp [Matrix.trace_conjTranspose, Matrix.trace_one]; ring
  have hdetadd : (1 + B).det = w * (((2 * w.re + 2 * z : ℝ)) : ℂ) := by
    have h2 : (1 + B).det = 1 + Matrix.trace B + B.det := by
      simp [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.add_apply]; ring
    rw [h2, htr, ← hw]; push_cast
    linear_combination (-w) * hcw - hws
  have hnorm : ‖(1 + B).det‖ = 2 * |w.re + z| := by
    rw [hdetadd, norm_mul, hw1, one_mul, Complex.norm_real, Real.norm_eq_abs,
      show 2 * w.re + 2 * z = 2 * (w.re + z) by ring, abs_mul]
    norm_num
  have hLre : (Matrix.trace ((1 + B)ᴴ * (1 + B))).re = 4 + 2 * (2 * z * w.re) := by
    rw [hFro, htr]; simp [Complex.add_re, Complex.mul_re]; ring
  rw [hLre, hnorm, ← one_add_mul_add_abs w.re z]
  ring

/-! ### Step 4 — a max of monotone branches is attained on the boundary -/

/-- A ray from a point of the closed unit disk, in any nonzero direction, meets the unit circle. -/
theorem exists_t_norm_eq_one (ζ δ : ℂ) (hζ : ‖ζ‖ ≤ 1) (hδ : δ ≠ 0) :
    ∃ t : ℝ, 0 ≤ t ∧ ‖ζ + (t : ℂ) * δ‖ = 1 := by
  have hδ0 : 0 < ‖δ‖ := norm_pos_iff.mpr hδ
  set T : ℝ := 2 / ‖δ‖ with hT
  have hT0 : 0 ≤ T := by positivity
  have hcont : ContinuousOn (fun t : ℝ => ‖ζ + (t : ℂ) * δ‖) (Set.Icc 0 T) :=
    (Continuous.norm (by fun_prop)).continuousOn
  have hf0 : ‖ζ + ((0 : ℝ) : ℂ) * δ‖ ≤ 1 := by simpa using hζ
  have hfT : 1 ≤ ‖ζ + ((T : ℝ) : ℂ) * δ‖ := by
    have h1 : ‖((T : ℝ) : ℂ) * δ‖ = 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT0, hT]; field_simp
    have h2 := norm_sub_norm_le (((T : ℝ) : ℂ) * δ) (-ζ)
    simp only [sub_neg_eq_add, norm_neg, h1] at h2
    rw [add_comm] at h2
    linarith
  obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc hT0 hcont ⟨hf0, hfT⟩
  exact ⟨t, ht.1, hteq⟩

/-- The larger of the two products is *itself* a product, with a sign `s = ±1`. -/
theorem max_eq_branch (x u : ℝ) : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
    max ((1 + x) * (1 + u)) ((1 - x) * (1 - u)) = (1 + s * x) * (1 + s * u) := by
  rcases le_or_gt ((1 - x) * (1 - u)) ((1 + x) * (1 + u)) with h | h
  · exact ⟨1, Or.inl rfl, by rw [max_eq_left h]; ring⟩
  · exact ⟨-1, Or.inr rfl, by rw [max_eq_right h.le]; ring⟩

theorem branch_le_max (x u s : ℝ) (hs : s = 1 ∨ s = -1) :
    (1 + s * x) * (1 + s * u) ≤ max ((1 + x) * (1 + u)) ((1 - x) * (1 - u)) := by
  rcases hs with rfl | rfl
  · simp
  · rw [show (1 + (-1) * x) * (1 + (-1) * u) = (1 - x) * (1 - u) by ring]; exact le_max_right _ _

/-- Branchwise monotonicity: if the branch `s` is active at `u` and `u` moves in the `s`
direction, the max does not decrease.  **This is the only monotonicity the proof needs** — no
convexity, which the square root would destroy anyway. -/
theorem branch_step (x u u' s : ℝ) (hx : |x| ≤ 1) (hs : s = 1 ∨ s = -1)
    (hmax : max ((1 + x) * (1 + u)) ((1 - x) * (1 - u)) = (1 + s * x) * (1 + s * u))
    (h : s * u ≤ s * u') :
    max ((1 + x) * (1 + u)) ((1 - x) * (1 - u))
      ≤ max ((1 + x) * (1 + u')) ((1 - x) * (1 - u')) := by
  rw [hmax]
  have hnn : (0 : ℝ) ≤ 1 + s * x := by
    rcases abs_le.mp hx with ⟨h1, h2⟩; rcases hs with rfl | rfl <;> linarith
  calc (1 + s * x) * (1 + s * u) ≤ (1 + s * x) * (1 + s * u') := by nlinarith
    _ ≤ _ := branch_le_max x u' s hs

/-- The Step-4 objective as a function of the disk parameter `ζ`.  The second term is read at
`ζ * v`, `v` being the unimodular twist coming from `Δ`. -/
noncomputable def objTwo (x x' : ℝ) (v ζ : ℂ) : ℝ :=
  2 * Real.sqrt (max ((1 + x) * (1 + ζ.re)) ((1 - x) * (1 - ζ.re)))
    + 2 * Real.sqrt (max ((1 + x') * (1 + (ζ * v).re)) ((1 - x') * (1 - (ζ * v).re)))

/-- **Step 4.**  On the closed unit disk the two-term objective is maximised on the unit circle.

The objective is the pointwise max of four branches `(s, s')`; branch `(s,s')` is nondecreasing
along the *fixed* direction `δ = s + s' v̄` (`s·Re δ = 1 + ss'·Re v ≥ 0` and
`s'·Re(δv) = 1 + ss'·Re v ≥ 0`), so following that ray to the circle does not decrease it.  A max
of finitely many functions, each maximised on the boundary, is maximised on the boundary.

The degenerate case `δ = 0` is exactly `v = ±1`, where both terms see only `Re ζ`; moving in the
`i` direction then changes nothing and still reaches the circle. -/
theorem objTwo_le_boundary (x x' : ℝ) (hx : |x| ≤ 1) (hx' : |x'| ≤ 1)
    (v : ℂ) (hv : ‖v‖ = 1) (ζ : ℂ) (hζ : ‖ζ‖ ≤ 1) :
    ∃ ζ' : ℂ, ‖ζ'‖ = 1 ∧ objTwo x x' v ζ ≤ objTwo x x' v ζ' := by
  obtain ⟨s, hs, hmax⟩ := max_eq_branch x ζ.re
  obtain ⟨s', hs', hmax'⟩ := max_eq_branch x' (ζ * v).re
  have hvre : |v.re| ≤ 1 := by rw [← hv]; exact Complex.abs_re_le_norm v
  by_cases hδ : (s : ℂ) + (s' : ℂ) * star v = 0
  · have hvim : v.im = 0 := by
      have h := congrArg Complex.im hδ
      simp at h
      rcases hs' with rfl | rfl <;> simp at h <;> linarith
    obtain ⟨t, ht0, ht1⟩ := exists_t_norm_eq_one ζ I hζ Complex.I_ne_zero
    refine ⟨ζ + (t : ℂ) * I, ht1, le_of_eq ?_⟩
    unfold objTwo
    have e1 : (ζ + (t : ℂ) * I).re = ζ.re := by simp
    have e2 : ((ζ + (t : ℂ) * I) * v).re = (ζ * v).re := by simp [Complex.mul_re, hvim, e1]
    rw [e1, e2]
  · obtain ⟨t, ht0, ht1⟩ := exists_t_norm_eq_one ζ _ hζ hδ
    refine ⟨ζ + (t : ℂ) * ((s : ℂ) + (s' : ℂ) * star v), ht1, ?_⟩
    have hvv : star v * v = 1 := by
      rw [show star v = (starRingEnd ℂ) v from rfl, mul_comm, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, hv]; norm_num
    have hre1 : (ζ + (t : ℂ) * ((s : ℂ) + (s' : ℂ) * star v)).re
        = ζ.re + t * (s + s' * v.re) := by simp
    have hre2 : ((ζ + (t : ℂ) * ((s : ℂ) + (s' : ℂ) * star v)) * v).re
        = (ζ * v).re + t * (s * v.re + s') := by
      have hx1 : (ζ + (t : ℂ) * ((s : ℂ) + (s' : ℂ) * star v)) * v
          = ζ * v + (t : ℂ) * ((s : ℂ) * v + (s' : ℂ) * (star v * v)) := by ring
      rw [hx1, hvv]; simp
    have step1 : s * ζ.re ≤ s * (ζ + (t : ℂ) * ((s : ℂ) + (s' : ℂ) * star v)).re := by
      rw [hre1]
      rcases abs_le.mp hvre with ⟨g1, g2⟩
      rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> nlinarith
    have step2 : s' * (ζ * v).re
        ≤ s' * ((ζ + (t : ℂ) * ((s : ℂ) + (s' : ℂ) * star v)) * v).re := by
      rw [hre2]
      rcases abs_le.mp hvre with ⟨g1, g2⟩
      rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> nlinarith
    have m1 := Real.sqrt_le_sqrt (branch_step x ζ.re _ s hx hs hmax step1)
    have m2 := Real.sqrt_le_sqrt (branch_step x' (ζ * v).re _ s' hx' hs' hmax' step2)
    unfold objTwo
    linarith

/-! ### Assembly -/

/-- The nuclear norm of a `2×2` matrix, in elementary form: `s₁ + s₂ = sqrt(s₁²+s₂²+2s₁s₂)`
`= sqrt(‖M‖²_F + 2|det M|)`.  (That identification is the one link this file leaves informal.) -/
noncomputable def nuc2 (M : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  Real.sqrt ((Matrix.trace (Mᴴ * M)).re + 2 * ‖M.det‖)

theorem nuc2_one_add (B : Matrix (Fin 2) (Fin 2) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (w : ℂ) (hw : w ^ 2 = B.det) :
    nuc2 (1 + B) = 2 * Real.sqrt (max ((1 + w.re) * (1 + (B 0 0 * star w).re))
                                      ((1 - w.re) * (1 - (B 0 0 * star w).re))) := by
  unfold nuc2
  rw [nucSq_one_add B hB w hw]
  set m : ℝ := max ((1 + w.re) * (1 + (B 0 0 * star w).re))
                  ((1 - w.re) * (1 - (B 0 0 * star w).re)) with hm
  rw [show (4 : ℝ) * m = 2 ^ 2 * m by ring, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by norm_num)]

/-- The bridge: the two-term objective *is* `objTwo`, read at the disk parameter `ζ = C₀₀ w̄`. -/
theorem nuc2_pair (Δ C : Matrix (Fin 2) (Fin 2) ℂ) (hΔ : Δ ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hΔd : Δ 0 1 = 0) (hC : C ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (w wΔ : ℂ) (hw : w ^ 2 = C.det) (hwΔ : wΔ ^ 2 = Δ.det) :
    nuc2 (1 + C) + nuc2 (1 + Δ * C)
      = objTwo w.re (wΔ * w).re (Δ 0 0 * star wΔ) (C 0 0 * star w) := by
  have hΔC : Δ * C ∈ Matrix.unitaryGroup (Fin 2) ℂ := Submonoid.mul_mem _ hΔ hC
  have hw2 : (wΔ * w) ^ 2 = (Δ * C).det := by rw [Matrix.det_mul, mul_pow, hw, hwΔ]
  have hentry : (Δ * C) 0 0 * star (wΔ * w) = (C 0 0 * star w) * (Δ 0 0 * star wΔ) := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, hΔd,
      show star (wΔ * w) = star wΔ * star w from by rw [StarMul.star_mul]; ring]
    ring
  unfold objTwo
  rw [nuc2_one_add C hC w hw, nuc2_one_add (Δ * C) hΔC (wΔ * w) hw2, hentry]

/-- **(DIAGONAL TARGETS) at `k = 2`, reduced form.**  For a unitary *diagonal* `Δ`, the objective
`nuc2(1+C) + nuc2(1+ΔC)` is maximised over `U(2)` at a **diagonal** `C`.

Combined with the block reduction recalled in the header (`α ⊗ 1` preserves `A`, `1 ⊗ β`
preserves `C`; the surviving blocks may be taken unitary; `‖D₁ + D₂A‖_* = ‖1 + Δ₁A‖_*` because the
`Dᵢ` are unitary), this says: *the best two-neighbour-gate approximation to a diagonal 3-qubit
gate may be taken diagonal.* -/
theorem k2_diagonal (Δ : Matrix (Fin 2) (Fin 2) ℂ) (hΔ : Δ ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hΔ01 : Δ 0 1 = 0) (C : Matrix (Fin 2) (Fin 2) ℂ)
    (hC : C ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ C' : Matrix (Fin 2) (Fin 2) ℂ, C' ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      C' 0 1 = 0 ∧ C' 1 0 = 0 ∧
      nuc2 (1 + C) + nuc2 (1 + Δ * C) ≤ nuc2 (1 + C') + nuc2 (1 + Δ * C') := by
  obtain ⟨w, hw⟩ := IsSepClosed.exists_pow_nat_eq C.det 2
  obtain ⟨wΔ, hwΔ⟩ := IsSepClosed.exists_pow_nat_eq Δ.det 2
  have hw1 : ‖w‖ = 1 := by
    have h : ‖w‖ ^ 2 = 1 := by rw [← norm_pow, hw, norm_det_eq_one C hC]
    nlinarith [norm_nonneg w]
  have hwΔ1 : ‖wΔ‖ = 1 := by
    have h : ‖wΔ‖ ^ 2 = 1 := by rw [← norm_pow, hwΔ, norm_det_eq_one Δ hΔ]
    nlinarith [norm_nonneg wΔ]
  have hws : w * star w = 1 := by simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw1]
  -- the data feeding Step 4
  have hx : |w.re| ≤ 1 := by rw [← hw1]; exact Complex.abs_re_le_norm w
  have hx' : |(wΔ * w).re| ≤ 1 := by
    have : ‖wΔ * w‖ = 1 := by rw [norm_mul, hw1, hwΔ1]; norm_num
    rw [← this]; exact Complex.abs_re_le_norm _
  have hv : ‖Δ 0 0 * star wΔ‖ = 1 := by
    -- `Δ` is unitary with `Δ 0 1 = 0`, so its `(0,0)` entry is already unimodular
    have hd : ‖Δ 0 0‖ = 1 := by
      have h2 : Δ * Δᴴ = 1 := hΔ.2
      have hrow := congrFun (congrFun h2 0) 0
      rw [Matrix.mul_apply] at hrow
      simp only [Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply_eq, hΔ01,
        show ∀ z : ℂ, star z = (starRingEnd ℂ) z from fun _ => rfl, Complex.mul_conj'] at hrow
      norm_num at hrow
      rcases hrow with h | h
      · exact h
      · exfalso
        have hneg : ‖Δ 0 0‖ = (-1 : ℝ) := by exact_mod_cast h
        linarith [norm_nonneg (Δ 0 0)]
    rw [norm_mul, hd, norm_star, hwΔ1]; norm_num
  have hζ : ‖C 0 0 * star w‖ ≤ 1 := by
    rw [norm_mul, norm_star, hw1, mul_one]; exact norm_entry_le_one C hC
  obtain ⟨ζ', hζ'1, hle⟩ := objTwo_le_boundary w.re (wΔ * w).re hx hx' _ hv _ hζ
  -- the diagonal witness realising `ζ'`
  refine ⟨Matrix.diagonal ![ζ' * w, w * star ζ'], diagonal_mem_unitary _ ?_, by simp, by simp, ?_⟩
  · intro i
    fin_cases i <;> simp [hw1, hζ'1]
  · have hCd : Matrix.diagonal ![ζ' * w, w * star ζ'] ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
      diagonal_mem_unitary _ (by intro i; fin_cases i <;> simp [hw1, hζ'1])
    have hζζ : ζ' * star ζ' = 1 := by simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ'1]
    have hdet : (Matrix.diagonal ![ζ' * w, w * star ζ']).det = w ^ 2 := by
      rw [Matrix.det_diagonal, Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      calc ζ' * w * (w * star ζ') = (ζ' * star ζ') * w ^ 2 := by ring
        _ = w ^ 2 := by rw [hζζ, one_mul]
    have hzeta : (Matrix.diagonal ![ζ' * w, w * star ζ']) 0 0 * star w = ζ' := by
      rw [Matrix.diagonal_apply_eq]
      simp only [Matrix.cons_val_zero]
      calc ζ' * w * star w = ζ' * (w * star w) := by ring
        _ = ζ' := by rw [hws, mul_one]
    rw [nuc2_pair Δ C hΔ hΔ01 hC w wΔ hw hwΔ,
      nuc2_pair Δ _ hΔ hΔ01 hCd w wΔ hdet.symm hwΔ, hzeta]
    exact hle

end K2Diagonal
