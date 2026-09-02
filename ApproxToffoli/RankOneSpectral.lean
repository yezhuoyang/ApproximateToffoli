import ApproxToffoli.RankTwoLitmus

/-!
# The rank-one spectral obstruction, and why it is a determinant SIGN

`RankTwoLitmus` shows that any proof of `HS2` must use `rank P = 1` (the rank-two analogue is
false).  This file records the sharpest known form of *what* rank-one buys, and formalises the
two ends of it.

## The statement

For `u ∈ U(2)` and a unit `v ∈ ℂ⁴`, put `T := (1_A ⊗ u)(1 - 2|v⟩⟨v|)` and let
`λ⁴ - c₁λ³ + c₂λ² - c₃λ + c₄` be its characteristic polynomial.  `T` has a **doubly degenerate**
spectrum iff that polynomial is the square of a quadratic `(λ² - aλ + b)²`, which forces
`a = c₁/2`, `b = (c₂ - c₁²/4)/2` and, in particular, `e₂ := c₄ - b² = 0`.

Writing `α := tr u`, `d := det u` and `m := ⟨v|(1_A ⊗ u)|v⟩`, Cayley–Hamilton on the `2×2` `u`
collapses everything (`α` cancels entirely):

  `c₁ = 2α - 2m`,  `c₂ = α(α - 2m)`,  `c₄ = det T = -d²`,  `b = -m²/2`,

hence

  **`e₂ = -(d² + m⁴/4)`,  so  `|e₂| ≥ |d|² - |m|⁴/4 = 1 - |m|⁴/4 ≥ 3/4 > 0`.**

So the spectrum is **never** doubly degenerate.  Both bounds are tight: over 200000 random
`(u,v)`, `min |e₂| = 0.7580` and `max |e₂| = 1.2497`, converging on `3/4` and `5/4`
(`PyScript/refl/`).

## Why this is the rank-one accident, in one word: parity

`det(1 - 2Π) = (-1)^{rank Π}`.  The `-1` for **rank one** is exactly the `-d²` in `c₄` above,
and it is the *only* reason `e₂` cannot vanish, since `|d²| = 1 > 1/4 ≥ |m⁴/4|`.  For a
**rank-two** `Π` the sign flips to `+1`, `c₄ = +d²`, and `e₂ = d² - b²` *can* vanish — which is
precisely `RankTwoLitmus`' witnesses (`σ_z^A ⊗ 1_B` and `1_A ⊗ σ_z`, both with `e₂ = 0`).

This is the most economical form of `notes/lemmas.md` iter 1081's "rank-one/parity accident":
it is a determinant sign, and nothing else.

## What is formalised here, and what is not

* `abs_e2_ge` — the abstract half: `|d| = 1`, `|m| ≤ 1` ⟹ `|d² + m⁴/4| ≥ 3/4`.
* `det_one_sub_two_selfProj` — the rank-one input: `det(1 - 2|v⟩⟨v|) = -1` for unit `v`.

Not yet formalised: the closed form `e₂ = -(d² + m⁴/4)` itself, which is the finite trace
computation sketched above (`det` of a Kronecker product, Cayley–Hamilton in `2×2`, and
`c₂ = (tr² - tr(·²))/2`).  It needs no spectral theory.  Chaining it with the two theorems below
gives `|e₂| ≥ 3/4`.

See `notes/OPEN_PROBLEM.md` §7.54 and §7.54.1.
-/

open Matrix Complex

namespace RankOneSpectral

/-- `c₂` of the characteristic polynomial of a `4×4`, from traces. -/
noncomputable def c2 (T : Mat4) : ℂ := ((Matrix.trace T)^2 - Matrix.trace (T*T))/2

/-- The `b` of the square-completion `(λ² - aλ + b)²`. -/
noncomputable def bco (T : Mat4) : ℂ := (c2 T - (Matrix.trace T)^2/4)/2

/-- **The obstruction scalar.**  If the spectrum of `T` is doubly degenerate then `e₂ T = 0`. -/
noncomputable def e2 (T : Mat4) : ℂ := T.det - (bco T)^2

/-- **The abstract half of the obstruction.**  With `d = det u` (unimodular) and
    `m = ⟨v|(1_A ⊗ u)|v⟩` (a contraction), `e₂ = -(d² + m⁴/4)` is bounded away from `0`.
    The `1` beats the `1/4`, and that gap is the whole theorem. -/
theorem abs_e2_ge (d m : ℂ) (hd : ‖d‖ = 1) (hm : ‖m‖ ≤ 1) :
    (3:ℝ)/4 ≤ ‖d^2 + m^4/4‖ := by
  have h1 : ‖d^2‖ = 1 := by rw [norm_pow, hd]; norm_num
  have hm4 : ‖m‖^4 ≤ 1 := pow_le_one₀ (norm_nonneg m) hm
  have h2 : ‖m^4/4‖ ≤ 1/4 := by
    rw [norm_div, norm_pow]
    have h4 : ‖(4:ℂ)‖ = 4 := by norm_num
    rw [h4]; linarith
  have h3 : ‖d^2‖ - ‖m^4/4‖ ≤ ‖d^2 + m^4/4‖ := by
    have := norm_sub_norm_le (d^2) (-(m^4/4))
    simpa using this
  linarith

/-- **The rank-one input: `det(1 - 2|v⟩⟨v|) = -1` for a unit vector `v`.**

    This single sign is the rank-one accident.  For a rank-`r` projection the determinant is
    `(-1)^r`, so rank two gives `+1` and the obstruction disappears — cf.
    `RankTwoLitmus.hs2clean_rank2_false`. -/
theorem det_one_sub_two_selfProj (v : Fin 4 → ℂ)
    (hv : (∑ i, (starRingEnd ℂ) (v i) * v i) = 1) :
    (1 - (2:ℂ) • Matrix.vecMulVec v (fun i => (starRingEnd ℂ) (v i))).det = -1 := by
  have hrw : (1 : Matrix (Fin 4) (Fin 4) ℂ)
        - (2:ℂ) • Matrix.vecMulVec v (fun i => (starRingEnd ℂ) (v i))
      = 1 + Matrix.replicateCol (Fin 1) (fun i => -(2:ℂ) * v i)
            * Matrix.replicateRow (Fin 1) (fun i => (starRingEnd ℂ) (v i)) := by
    ext i j
    simp [Matrix.vecMulVec, Matrix.mul_apply, Matrix.one_apply, Matrix.sub_apply]
    ring
  rw [hrw, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct]
  rw [show (∑ i, (starRingEnd ℂ) (v i) * (-(2:ℂ) * v i))
        = -2 * (∑ i, (starRingEnd ℂ) (v i) * v i) by rw [Finset.mul_sum]; ring_nf]
  rw [hv]; ring

end RankOneSpectral
