/-
  ApproxToffoli.Attainment

  **The lower bound is ATTAINED**, so the minimum Hilbert–Schmidt distance from `CCX`
  to a ≤5-CX circuit on AB/BC connectivity is EXACTLY `sin(π/8)`, not merely bounded
  below by it. `Basic.lean` supplies the `≥` half; this file supplies a witness.

  **The witness needs only FOUR CX gates** (`AchievableCircuit 5` accepts it through
  `weaken`), in the pattern `AB-BC-AB-BC` reading the matrix product left to right:

      U = (T³⊗T³⊗HT³H) · CX_AB · (I⊗TH⊗I) · CX_BC · (I⊗HT³⊗I)
                        · CX_AB · (I⊗TH⊗I) · CX_BC · (I⊗H⊗I)

  with `T = diag(1, e^{iπ/4})` the usual T gate. It is a **Clifford+T** circuit: every
  entry lies in `ℚ(√2, i)`, so `cos(π/8)` never appears in the circuit itself. That is
  forced rather than lucky —

      Tr(Uᴴ CCX) = 4 + 4·invSqrt2·(1 + i) = (4 + 2√2) + 2√2 i = 4 + 4e^{iπ/4},
      |Tr(Uᴴ CCX)|² = 32 + 16√2 = 64cos²(π/8),

  and `8cos(π/8) = |4 + 4e^{iπ/4}|` with `4 + 4e^{iπ/4} ∈ ℚ(√2,i)`.

  **How it was found** (notes/lemmas.md iter-1059): not by search, but by reading the
  equality conditions off `CutBound`'s own proof. At the optimum `Tr R = 0` (hence
  `P₃₃ = 0`), `|Tr(QR)| = 2√2` with argument `π/4`, `g₊ = g₋ = √2`, and Lemma T1 is
  EXACTLY tight. Since `M₂` is a product unitary, `P = I⊗(b₂ᴴZb₂)`, and `P₃₃ = 0` forces
  `b₂ᴴZb₂` into `span{X,Y}` — a ONE-PARAMETER family, not a single point. Picking the
  representative `X` is WLOG: the remaining freedom is a `Z`-rotation on qubit B, which
  is absorbed into the (free) `M₁`. That choice gives `b₂ = H`, the `H` on qubit B in
  the last layer.

  **Why the trace computation is cheap.** `U` is a product of nine factors, but every
  factor is a `kron3` or a sum of two `kron3`s, so `kron3_mul` keeps the whole product
  in `kron3`-sum form and `trace_kron3_ccx_expanded` reduces the objective to 2×2
  entries. No 8×8 matrix is ever expanded entrywise.
-/

import ApproxToffoli.Basic
import ApproxToffoli.CutAlgebra

open Matrix Complex

noncomputable section

/-! ## The gates -/

/-- `e^{3iπ/4}`, the phase of `T³`. -/
def zPh : ℂ := (-1 + Complex.I) * invSqrt2

/-- `T³ = diag(1, e^{3iπ/4})`. -/
def T3g : Mat2 := Matrix.of !![1, 0; 0, zPh]

/-- `T·H`. -/
def THg : Mat2 := Matrix.of !![invSqrt2, invSqrt2; (1 + Complex.I)/2, -((1 + Complex.I)/2)]

/-- `H·T³`. -/
def HT3g : Mat2 := Matrix.of !![invSqrt2, (-1 + Complex.I)/2; invSqrt2, (1 - Complex.I)/2]

/-- `H·T³·H`. -/
def HT3Hg : Mat2 := Matrix.of !![(1 + zPh)/2, (1 - zPh)/2; (1 - zPh)/2, (1 + zPh)/2]

lemma conj_invSqrt2 : (starRingEnd ℂ) invSqrt2 = invSqrt2 := by
  rw [invSqrt2, map_inv₀, Complex.conj_ofReal]

lemma isU_T3g : IsUnitary2 T3g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [T3g, zPh, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Complex.ext_iff, invSqrt2] <;>
    ring_nf <;> norm_num [Real.sq_sqrt]

lemma isU_THg : IsUnitary2 THg := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [THg, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Complex.ext_iff, invSqrt2] <;>
    ring_nf <;> norm_num [Real.sq_sqrt]

/-- `HT3g` really is `H·T³` — so its unitarity is inherited, no entrywise argument. -/
lemma HT3g_eq : HT3g = Hgate * T3g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [HT3g, Hgate, T3g, zPh, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.ext_iff, invSqrt2] <;>
    ring_nf <;> norm_num [Real.sq_sqrt]

lemma isU_HT3g : IsUnitary2 HT3g := by
  rw [HT3g_eq]; exact isUnitary2_mul hgate_unitary isU_T3g

/-- `HT3Hg` really is `(H·T³)·H`. -/
lemma HT3Hg_eq : HT3Hg = HT3g * Hgate := by
  have hs : invSqrt2 * invSqrt2 = 2⁻¹ := invSqrt2_sq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [HT3Hg, HT3g, Hgate, zPh, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
      | linear_combination hs
      | linear_combination (-1 : ℂ) * hs
      | linear_combination (2 : ℂ) * hs
      | linear_combination (-2 : ℂ) * hs
      | ring

lemma isU_HT3Hg : IsUnitary2 HT3Hg := by
  rw [HT3Hg_eq]; exact isUnitary2_mul isU_HT3g hgate_unitary

/-! ## The witness circuit -/

/-- The attaining circuit. Four CX gates, pattern `AB-BC-AB-BC`. -/
def witnessU : Mat8 :=
  singleQubitLayer T3g T3g HT3Hg * CX_AB * singleQubitLayer I₂ THg I₂
    * CX_BC * singleQubitLayer I₂ HT3g I₂
    * CX_AB * singleQubitLayer I₂ THg I₂
    * CX_BC * singleQubitLayer I₂ Hgate I₂

/-- It really is a legal circuit: four CX gates, all AB or BC, then `weaken` to 5. -/
theorem witness_achievable : AchievableCircuit 5 witnessU := by
  have hI : IsUnitary2 I₂ := by rw [IsUnitary2, I₂]; simp
  refine AchievableCircuit.weaken ?_
  exact AchievableCircuit.compose I₂ Hgate I₂ hI hgate_unitary hI
    (Or.inr (Or.inr (Or.inl rfl)))
    (AchievableCircuit.compose I₂ THg I₂ hI isU_THg hI (Or.inl rfl)
      (AchievableCircuit.compose I₂ HT3g I₂ hI isU_HT3g hI
        (Or.inr (Or.inr (Or.inl rfl)))
        (AchievableCircuit.compose I₂ THg I₂ hI isU_THg hI (Or.inl rfl)
          (AchievableCircuit.single_layer T3g T3g HT3Hg isU_T3g isU_T3g isU_HT3Hg))))

set_option maxHeartbeats 3200000 in
-- Heartbeat bump: the nine-factor product expands to sixteen `kron3` summands, each
-- contributing eight `trace_kron3_ccx_expanded` terms of 2×2 entries.
/-- **The trace of the witness.** `Tr(Uᴴ CCX) = 4 + 4·invSqrt2·(1 + i) = 4 + 4e^{iπ/4}`.

    Everything stays in `kron3`-sum form via `kron3_mul`, so no 8×8 matrix is ever
    expanded entrywise; `trace_kron3_ccx_expanded` then reduces to 2×2 entries, and the
    residue is a polynomial in `invSqrt2` and `i` killed by `invSqrt2² = ½`, `i² = -1`. -/
theorem witness_trace_val : Matrix.trace (witnessUᴴ * CCX)
    = 4 + 4 * invSqrt2 + 4 * invSqrt2 * Complex.I := by
  have e2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have e3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, e2]; ring
  have e4 : Complex.I ^ 4 = 1 := by
    have h : Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 := by ring
    rw [h, e2]; norm_num
  have s2 : invSqrt2 ^ 2 = 2⁻¹ := invSqrt2_pow2
  have s3 : invSqrt2 ^ 3 = invSqrt2 / 2 := by rw [pow_succ, s2]; ring
  have s4 : invSqrt2 ^ 4 = 4⁻¹ := invSqrt2_pow4
  have s5 : invSqrt2 ^ 5 = invSqrt2 / 4 := by rw [pow_succ, s4]; ring
  have s6 : invSqrt2 ^ 6 = 8⁻¹ := by
    have h : invSqrt2 ^ 6 = (invSqrt2 ^ 2) ^ 3 := by ring
    rw [h, s2]; norm_num
  rw [witnessU]
  simp only [singleQubitLayer, CX_AB, CX_BC, I₂, mul_one, mul_add, add_mul,
    kron3_mul, Matrix.conjTranspose_add, Matrix.trace_add, trace_kron3_ccx_expanded]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, T3g, THg, HT3g, HT3Hg, Hgate,
    proj0, proj1, pauliX, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [zPh, Complex.star_def, map_add, map_mul, map_sub, map_neg, map_div₀,
    map_one, map_ofNat, Complex.conj_I, conj_invSqrt2, map_zero]
  ring_nf
  simp only [e2, e3, e4, s2, s3, s4, s5, s6]
  ring

/-- `|Tr(Uᴴ CCX)|² = 32 + 16√2 = 64cos²(π/8)` — the bound of `Basic.lean`, attained. -/
theorem witness_normSq :
    Complex.normSq (Matrix.trace (witnessUᴴ * CCX)) = 32 + 16 * Real.sqrt 2 := by
  have hr : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hcast : invSqrt2 = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
    rw [invSqrt2, Complex.ofReal_inv]
  rw [witness_trace_val, hcast,
    show (4 : ℂ) + 4 * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
        + 4 * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * Complex.I
      = (((4 + 4 * (Real.sqrt 2)⁻¹ : ℝ) : ℂ))
        + (((4 * (Real.sqrt 2)⁻¹ : ℝ) : ℂ)) * Complex.I by push_cast; ring,
    Complex.normSq_add_mul_I]
  field_simp
  nlinarith [hsq, hr]

/-! ## The minimum -/

/-- `sin²(π/8) = ½ − √2/4`. -/
lemma sin_pi_eight_sq : Real.sin (Real.pi / 8) ^ 2 = 1/2 - Real.sqrt 2 / 4 := by
  have h2 : Real.cos (2 * (Real.pi/8)) = 2 * Real.cos (Real.pi/8) ^ 2 - 1 :=
    Real.cos_two_mul _
  rw [show 2 * (Real.pi/8) = Real.pi/4 by ring, Real.cos_pi_div_four] at h2
  have hpy := Real.sin_sq_add_cos_sq (Real.pi/8)
  linarith

/-- **The witness attains the bound exactly.** -/
theorem witness_distance : hsDistance witnessU CCX = Real.sin (Real.pi / 8) := by
  rw [hsDistance, hsFidelity, witness_normSq]
  rw [show (1 : ℝ) - (32 + 16 * Real.sqrt 2)/64 = Real.sin (Real.pi/8) ^ 2 by
    rw [sin_pi_eight_sq]; ring]
  exact Real.sqrt_sq (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
    (by nlinarith [Real.pi_pos]))

/-- **THE MINIMUM IS `sin(π/8)`.** The lower bound of `approxToffoli_lower_bound` is
    attained, so this is a genuine minimum and not just a bound: `sin(π/8)` is the
    least element of the set of achievable Hilbert–Schmidt distances to Toffoli. -/
theorem approxToffoli_isLeast_distance :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 5 U ∧ hsDistance U CCX = d}
      (Real.sin (Real.pi / 8)) :=
  ⟨⟨witnessU, witness_achievable, witness_distance⟩,
   by rintro d ⟨U, hU, rfl⟩; exact approxToffoli_lower_bound U hU⟩

/-- The same statement spelled out: every ≤5-CX circuit is at distance ≥ `sin(π/8)`,
    and some ≤5-CX circuit is at distance exactly `sin(π/8)`. -/
theorem approxToffoli_min_distance :
    (∀ U : Mat8, AchievableCircuit 5 U → hsDistance U CCX ≥ Real.sin (Real.pi / 8)) ∧
    (∃ U : Mat8, AchievableCircuit 5 U ∧ hsDistance U CCX = Real.sin (Real.pi / 8)) :=
  ⟨fun U hU => approxToffoli_lower_bound U hU,
   ⟨witnessU, witness_achievable, witness_distance⟩⟩

end
