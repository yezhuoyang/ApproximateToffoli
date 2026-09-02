# ApproximateToffoli

Lean 4 + Mathlib formalization of two quantum-circuit lower-bound results.
**Both are complete**: `lake build ApproxToffoli` reports **0 errors and 0 sorries**, and
every top-level theorem depends on exactly `[propext, Classical.choice, Quot.sound]` —
no `sorryAx`, no custom axioms, no `native_decide`.

## 1. Approximate Toffoli: the minimum distance is exactly `sin(π/8)`

Ye 2026, [`ApproxToffoli.pdf`](ApproxToffoli.pdf). Among 3-qubit circuits built from at
most 5 CX gates on AB/BC connections only (with arbitrary single-qubit layers
interleaved), the minimum Hilbert–Schmidt distance to the Toffoli gate is exactly
`sin(π/8) ≈ 0.38268`.

Both directions are proved, so this is a genuine minimum and not just a bound:

* **lower bound** — every such circuit is at distance `≥ sin(π/8)`;
* **attainment** — an explicit 4-CX **Clifford+T** circuit sits at distance exactly
  `sin(π/8)` ([`Attainment.lean`](ApproxToffoli/Attainment.lean)).

⚠️ **Scope: the formalized gate set is the literal CNOT.** `AllowedCX` is exactly
`{CX_AB, CX_BA, CX_BC, CX_CB}`, whereas the preprint (§4, Eq. 6) poses the problem over
the arbitrary controlled-unitary `CU3(α,β,γ)`, of which CNOT is the single point
`α=π, β=γ=0`. So the Lean **lower** bound is proved for a strictly smaller circuit class
than the preprint's. The witness is a CNOT circuit and therefore lies in both classes, so
the **upper** bound transfers for free. Adversarial optimisation over arbitrary two-qubit
AB/BC unitaries (a superset of CU3) also returns `8cos(π/8)` to 2e-14, so the constant is
believed unchanged for the wider class — but that is numerics, not proof. Generalising
would mean reopening Lemma T1: a CU3 crossing conjugates to `I⊗diag(1,e^{iφ})` instead of
`I⊗Z`, so `P` and `Q` stop being rank-2 reflections.

The distance is the preprint's own Eq. (3), `d(U,V) = √(1 − |Tr(U†V)|²/2^{2n})`,
implemented verbatim as `hsDistance`. Note this is **not** the Frobenius distance
`‖U−V‖_F`; it is `sin θ` where `cos θ = |Tr(U†V)|/8`, i.e. the sine of the ray angle —
which is the phase-invariant quantity one wants for comparing gates.

Palsberg & Yu 2024 (`PY24.pdf`, LAA 694, 206–261) is a **different**, exact result and
supplies the `PY24/` lemma track, not this statement.

## 2. Toffoli requires 6 neighbor gates

Huang & Palsberg 2026, ACM TQC 7(2), Article 10. CCZ — and Toffoli/CCX — cannot be
implemented with 5 neighbor gates; 6 suffice.

⚠️ **Scope: stated over `UnitaryNeighborCircuit`**, i.e. two-qubit gates required to be
unitary. This was a deliberate restatement (iter 1042): the non-unitary `NeighborCircuit`
form is not merely unproved but was shown **unprovable as stated** (iter 1043), because
the paper's spectral arguments need gate unitarity and no forgetful lift can supply it.

## Top-level theorems

| Theorem | File:Line | Statement |
|---|---|---|
| `approxToffoli_isLeast_distance` | [Attainment.lean:194](ApproxToffoli/Attainment.lean#L194) | `IsLeast {d \| ∃ U, AchievableCircuit 5 U ∧ hsDistance U CCX = d} (sin(π/8))` |
| `approxToffoli_min_distance` | [Attainment.lean:202](ApproxToffoli/Attainment.lean#L202) | the same, spelled out as `≥` for all + `=` for one |
| `approxToffoli_lower_bound` | [Basic.lean:22](ApproxToffoli/Basic.lean#L22) | `AchievableCircuit 5 U → hsDistance U CCX ≥ sin(π/8)` |
| `witness_achievable` | [Attainment.lean:113](ApproxToffoli/Attainment.lean#L113) | the explicit 4-CX Clifford+T witness is achievable |
| `CCZ_not_five_neighbor` | [HP/Main.lean:44](ApproxToffoli/HP/Main.lean#L44) | `¬ UnitaryNeighborCircuit 5 CCZ_matrix` |
| `CCZ_requires_six_neighbor` | [HP/Main.lean:63](ApproxToffoli/HP/Main.lean#L63) | `UnitaryNeighborCircuit 6 CCZ_matrix ∧ ¬ … 5 …` |
| `CCX_not_five_neighbor` | [HP/Main.lean:145](ApproxToffoli/HP/Main.lean#L145) | `¬ UnitaryNeighborCircuit 5 CCX` |
| `CCX_requires_six_neighbor` | [HP/Main.lean:150](ApproxToffoli/HP/Main.lean#L150) | `UnitaryNeighborCircuit 6 CCX ∧ ¬ … 5 …` |

## Build

```bash
lake exe cache get    # prime the mathlib cache — recommended
lake build ApproxToffoli
```

Verify the headline claim:

```bash
lake build ApproxToffoli 2>&1 | grep -c "uses .sorry."   # => 0
```

## How result 1 is proved

Not by induction on gate count. That architecture (`compose_trace_bound`) was tried for
~800 iterations and **deleted** rather than filled: the induction hypothesis tracks one
scalar while the compose step needs an optimisation over all product layers.

The working proof is the **cut form**. An `AchievableCircuit n` circuit admits both an
AB|C and an A|BC cut with `m_BC + m_AB ≤ n`; since 5 is **odd**, one cut has `m ≤ 2`, and
the A|BC branch is mirrored onto the AB|C one by the A↔C relabelling, which fixes CCZ.
Bounding `F(m)` for `m ≤ 2` is then a statement about 4×4 traces with no circuits in it.
`m ≤ 2` is load-bearing: `F(2)² = 64cos²(π/8)` is exactly attained while `F(3) = F(4) = 8`
exceeds the target.

```
CutAlgebra → CutForm → CutNormalForm → LemmaT1 → CutBound → CutMain → TraceBound → Basic
                                                                              ↘ Attainment
```

The one genuinely new ingredient is `proj_trace_bound` in
[`CutBound.lean`](ApproxToffoli/CutBound.lean): for `Π` a rank-2 orthogonal projection and
`K`, `R` unitary, `|Tr(ΠK)|² + |Tr(ΠKR)|² ≤ 2(2 + |Tr(ΠR)|)`. The textbook proof picks an
orthonormal basis of `ran Π` — machinery this Mathlib does not have (it contains exactly
one `spectral_theorem`, the Hermitian one). The replacement uses three explicit matrices
`X = KᴴΠ`, `Y = Π`, `Z = RΠ` in the Hilbert–Schmidt inner product, where every needed
fact follows from `Π²=Π`, `Πᴴ=Π` and unitarity. No basis is ever chosen.

## Layout

```
ApproxToffoli/
├── Basic.lean          # lower bound (result 1)
├── Attainment.lean     # the attaining Clifford+T witness; min = sin(π/8)
├── TraceBound.lean     # thin adapter onto CutMain (compose_trace_bound DELETED)
├── CutAlgebra.lean     # R1/R2, the A↔C mirror, cos(π/8) constants
├── CutForm.lean        # BCCut/ABCut, achievable_to_both_cuts
├── CutNormalForm.lean  # R4 BCCut→CZCut, R5 explicit trace formulas
├── LemmaT1.lean        # Lemma T1
├── CutBound.lean       # proj_trace_bound, core_psi_bound, F(0)/F(1)/F(2)
├── CutMain.lean        # achievable_trace_bound_cut
├── PY24/               # PY24 lemma track (closed)
└── HP/                 # Huang–Palsberg track (closed); Main.lean = top-level
notes/                  # session log, lemmas, proof state, next-session prompt
PyScript/               # numerical falsity-checks (adversarial optimisation only)
```

## A note on the numerics

Random sampling is **worthless** for the inequalities in this project — random draws sit
far below every bound and have twice produced false "verified" claims. All numerical
checks here use adversarial optimisation (L-BFGS-B / Nelder–Mead on the violation, many
restarts). Algebraic identities are fine to check by sampling.

One consequence worth recording: exact optimisation gives the layout-count buckets
`320 / 640 / 64` for the three optimal distances, not the preprint's Table 1
`240 / 720 / 64`. Since gate direction is free (BA is a single-qubit conjugate of AB),
every bucket must be divisible by 32, which 240 is not; the discrepancy is consistent
with ~80 layouts where the Adam optimiser stalled at 0.52100. **The minimum itself,
0.38268, is confirmed.**

## Citation

- Ye (2026), "Approximate Toffoli gates with 5 two qubit gates"
  ([`ApproxToffoli.pdf`](ApproxToffoli.pdf)) — result 1.
- Huang & Palsberg (2026), ACM TQC 7(2), Article 10 — result 2.
- Palsberg & Yu (2024), LAA 694, 206–261 — the `PY24/` lemma track.

## License

See [LICENSE](LICENSE) if present, else default (TBD).
