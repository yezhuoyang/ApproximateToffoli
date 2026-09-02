/-
  ApproxToffoli.CurveMain

  The curve `d(n) = min { d_HS(U, CCX) : U ∈ A_n }` for every CNOT budget `n`, where
  `A_n` is the set of three-qubit unitaries built from at most `n` CNOT gates on the
  line `A–B–C` (pairs `AB` and `BC` only) interleaved with arbitrary single-qubit
  unitaries.

  | `n`   | `d(n)`        | status here                                        |
  |-------|---------------|----------------------------------------------------|
  | 0, 1  | `√7/4`        | **exact**, `curve_zero`, `curve_one`               |
  | 2, 3  | `√6/4`        | **exact**, `curve_two`, `curve_three`              |
  | 4, 5  | `sin(π/8)`    | **exact**, `curve_four`, `curve_five`              |
  | 6, 7  | `sin(π/8)`    | upper bound only, `curve_six_le`, `curve_seven_le` |
  | 8     | `0`           | **exact**, `curve_eight`                           |

  Seven of the nine entries are exact minima. The two open entries are `n = 6, 7`,
  where the witness gives `d ≤ sin(π/8)` and the matching lower bound is not proved;
  numerically it is an equality. See `notes/curve_report.md`.

  `d` is non-increasing (`A_n ⊆ A_{n+1}` via `AchievableCircuit.weaken`), so the three
  plateaux `{0,1}`, `{2,3}`, `{4,5,6,7}` each need only one lower bound, at the top,
  and one witness, at the bottom.
-/
import ApproxToffoli.Key2
import ApproxToffoli.CurveThree
import ApproxToffoli.OneGate
import ApproxToffoli.Basic
import ApproxToffoli.Attainment

open Matrix Complex

noncomputable section

/-! ## The one packaged hypothesis, discharged

`CurveThree` is stated relative to `SharpBounds.Key2`, the sharp two-trace inequality.
`Key2.key2` proves it, so everything downstream is unconditional. -/

/-- The packaged analytic input of the `m ≤ 1` cut bound is a theorem. -/
theorem key2_holds : SharpBounds.Key2 := fun Q N hQ hN => Key2.key2 Q N hQ hN

/-! ## The curve, entry by entry -/

/-- **`d(0) = √7/4`.** The best zero-CNOT approximation to Toffoli is the identity. -/
theorem curve_zero :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 0 U ∧ hsDistance U CCX = d}
      (Real.sqrt 7 / 4) :=
  Cost1.d_zero_isLeast

/-- **`d(1) = √7/4`.** The first CNOT buys nothing. -/
theorem curve_one :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 1 U ∧ hsDistance U CCX = d}
      (Real.sqrt 7 / 4) :=
  Cost1.d_one_isLeast

/-- **`d(2) = √6/4`.** Attained by the controlled-`S` gate on the pair `AB`. -/
theorem curve_two :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 2 U ∧ hsDistance U CCX = d}
      (Real.sqrt 6 / 4) :=
  approxToffoli_isLeast_two key2_holds

/-- **`d(3) = √6/4`.** The third CNOT buys nothing. -/
theorem curve_three :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 3 U ∧ hsDistance U CCX = d}
      (Real.sqrt 6 / 4) :=
  approxToffoli_isLeast_three key2_holds

/-- **`d(4) = sin(π/8)`.** The witness uses four CNOTs in the pattern `AB-BC-AB-BC`;
    the lower bound is `approxToffoli_lower_bound`, which covers all of `A_5 ⊇ A_4`. -/
theorem curve_four :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 4 U ∧ hsDistance U CCX = d}
      (Real.sin (Real.pi / 8)) := by
  constructor
  · exact ⟨Curve.witness4, Curve.witness4_achievable, Curve.witness4_distance⟩
  · rintro d ⟨U, hU, rfl⟩
    exact approxToffoli_lower_bound U (AchievableCircuit.weaken hU)

/-- **`d(5) = sin(π/8)`.** -/
theorem curve_five :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 5 U ∧ hsDistance U CCX = d}
      (Real.sin (Real.pi / 8)) :=
  approxToffoli_isLeast_distance

/-- **`d(6) ≤ sin(π/8)`.** The matching lower bound is not proved; see the module
    docstring. -/
theorem curve_six_le :
    ∃ U : Mat8, AchievableCircuit 6 U ∧ hsDistance U CCX = Real.sin (Real.pi / 8) :=
  ⟨Curve.witness4,
   AchievableCircuit.weaken (AchievableCircuit.weaken Curve.witness4_achievable),
   Curve.witness4_distance⟩

/-- **`d(7) ≤ sin(π/8)`.** -/
theorem curve_seven_le :
    ∃ U : Mat8, AchievableCircuit 7 U ∧ hsDistance U CCX = Real.sin (Real.pi / 8) :=
  ⟨Curve.witness4,
   AchievableCircuit.weaken (AchievableCircuit.weaken
     (AchievableCircuit.weaken Curve.witness4_achievable)),
   Curve.witness4_distance⟩

/-- **`d(8) = 0`.** Eight CNOTs on the line implement Toffoli exactly, and the explicit
    circuit `Curve.witness8` *equals* `CCX` (`Curve.witness8_eq_CCX`). -/
theorem curve_eight :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 8 U ∧ hsDistance U CCX = d} 0 := by
  constructor
  · exact ⟨Curve.witness8, Curve.witness8_achievable, Curve.witness8_distance⟩
  · rintro d ⟨U, hU, rfl⟩
    exact Real.sqrt_nonneg _

/-! ## The curve in one statement -/

/-- **The curve.** Seven exact entries and two upper bounds. -/
theorem approxToffoli_curve :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 0 U ∧ hsDistance U CCX = d}
        (Real.sqrt 7 / 4) ∧
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 1 U ∧ hsDistance U CCX = d}
        (Real.sqrt 7 / 4) ∧
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 2 U ∧ hsDistance U CCX = d}
        (Real.sqrt 6 / 4) ∧
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 3 U ∧ hsDistance U CCX = d}
        (Real.sqrt 6 / 4) ∧
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 4 U ∧ hsDistance U CCX = d}
        (Real.sin (Real.pi / 8)) ∧
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 5 U ∧ hsDistance U CCX = d}
        (Real.sin (Real.pi / 8)) ∧
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 8 U ∧ hsDistance U CCX = d} 0 :=
  ⟨curve_zero, curve_one, curve_two, curve_three, curve_four, curve_five, curve_eight⟩

end
