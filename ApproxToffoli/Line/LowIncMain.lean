/-
The low incrementer on a line (`24 a - 23` CNOTs): its basis action.

Wires: `S_i = 2a - 2i` (`0 ≤ i ≤ a`), `T_i = 2a - 2i - 1` (`0 ≤ i < a`); `T` is the number
with bit `i` on `T_i` (`Tval`).  For `2 ≤ a`, `2a < N`, the circuit `lowInc N a` is, up to
phases of modulus one, the permutation `lowIncPerm N a` of basis states, which

* leaves the even wires `2, 4, …, 2a` and the wires above `2a` unchanged;
* replaces `T` by `T + 1` modulo `2^a`;
* flips wire `0` iff all `T_i` are one.

Proof: `lowIncPerm = τ ∘ rest ∘ centre ∘ rest⁻¹` with `τ` the terminal NOTs.  Every state
is `Add x = rest (PQ x)` for some `x` (`addSt_surjective`), and on it
`τ (rest (centre (PQ x))) = τ (rest (PQ (χ x))) = τ (Add (χ x))`; the claim is then the
identity `inc_bits` on bit sequences.
-/
import Mathlib
import ApproxToffoli.Line.LowIncCentre

namespace Line

open Matrix ExactLine

variable {N : ℕ}

/-! ### `Add` on the bits `S_i`, `T_i` -/

/-- `Add x` holds the sum bit `S_i ⊕ T_i ⊕ c_i` on `T_i`. -/
theorem addSt_T {a : ℕ} (h : 2 * a < N) (x : St N) {i : ℕ} (hi : i < a) :
    wire (addSt x a) (2 * a - 2 * i - 1) = gsumBit (sBit x a) (tBit x a) i := by
  have e1 : 2 * a - 2 * i - 1 + 1 = 2 * a - 2 * i := by omega
  have e2 : a - 1 - (2 * a - 2 * i - 1) / 2 = i := by omega
  rw [addSt_odd h x (by omega) (by omega), e1, e2]
  rfl

/-- **`Add` is injective**: recover the bits `T_0, T_1, …` and the carries one by one. -/
theorem addSt_injective {a : ℕ} (h : 2 ≤ a ∧ 2 * a < N) :
    Function.Injective (fun x : St N => addSt x a) := by
  intro x x' hxx
  have e : ∀ s t t' c : Bool, xor (xor s t) c = xor (xor s t') c → t = t' := by decide
  have e' : ∀ u u' c : Bool, xor u c = xor u' c → u = u' := by decide
  have hA : ∀ j, wire (addSt x a) j = wire (addSt x' a) j := fun j =>
    congrArg (fun y => wire y j) hxx
  have hS : ∀ i, i < a → sBit x a i = sBit x' a i := by
    intro i hi
    have := hA (2 * a - 2 * i)
    rwa [addSt_other h.2 x (by omega) (by omega), addSt_other h.2 x' (by omega) (by omega)]
      at this
  have hC : ∀ i, i ≤ a → cr x a i = cr x' a i ∧ ∀ l, l < i → tBit x a l = tBit x' a l := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨rfl, fun l hl => absurd hl (Nat.not_lt_zero l)⟩
    | succ i ih =>
      intro hi
      obtain ⟨hc, ht⟩ := ih (by omega)
      have hti : tBit x a i = tBit x' a i := by
        have := hA (2 * a - 2 * i - 1)
        rw [addSt_T h.2 x (by omega), addSt_T h.2 x' (by omega)] at this
        change xor (xor (sBit x a i) (tBit x a i)) (cr x a i)
          = xor (xor (sBit x' a i) (tBit x' a i)) (cr x' a i) at this
        rw [hS i (by omega), hc] at this
        exact e _ _ _ _ this
      refine ⟨?_, fun l hl => ?_⟩
      · rw [cr_succ, cr_succ, hS i (by omega), hti, hc]
      · by_cases hli : l = i
        · rw [hli]
          exact hti
        · exact ht l (by omega)
  apply wire_ext
  intro j
  by_cases h0 : j = 0
  · have := hA 0
    rw [addSt_zero h.2, addSt_zero h.2, (hC a (le_refl a)).1] at this
    rw [h0]
    exact e' _ _ _ this
  by_cases ho : j ≤ 2 * a ∧ j % 2 = 1
  · have := (hC a (le_refl a)).2 (a - 1 - j / 2) (by omega)
    rw [tBit, tBit, show 2 * a - 2 * (a - 1 - j / 2) - 1 = j by omega] at this
    exact this
  · have := hA j
    rwa [addSt_other h.2 x h0 ho, addSt_other h.2 x' h0 ho] at this

/-- Every basis state is `Add x` for some `x`. -/
theorem addSt_surjective {a : ℕ} (h : 2 ≤ a ∧ 2 * a < N) (z : St N) :
    ∃ x : St N, addSt x a = z :=
  Finite.surjective_of_injective (addSt_injective h) z

/-! ### The low incrementer on `Add x` -/

/-- `lowIncPerm (Add x) = τ (Add (χ x))`, from (i) and (ii). -/
theorem lowIncPerm_addSt {a : ℕ} (h : 2 ≤ a ∧ 2 * a < N) (x : St N) :
    lowIncPerm N a (addSt x a) = xsPerm N (2 * a + 1) (addSt (chiSt x a) a) := by
  have h1 : (restPerm N a)⁻¹ (addSt x a) = pqSt x a :=
    (Equiv.symm_apply_eq _).2 (restPerm_pqSt h x).symm
  change xsPerm N (2 * a + 1)
    (restPerm N a (centrePerm N a ((restPerm N a)⁻¹ (addSt x a)))) = _
  rw [h1, centrePerm_pqSt h, restPerm_pqSt h]

theorem lowIncPerm_addSt_wire {a : ℕ} (h : 2 ≤ a ∧ 2 * a < N) (x : St N) (j : ℕ) :
    wire (lowIncPerm N a (addSt x a)) j
      = if j < 2 * a + 1 then !wire (addSt (chiSt x a) a) j
        else wire (addSt (chiSt x a) a) j := by
  rw [lowIncPerm_addSt h, xsPerm_wire _ (by omega)]

/-- The sum bits of the complemented input. -/
theorem gsumBit_chiSt {a : ℕ} (h : 2 * a < N) (x : St N) {i : ℕ} (hi : i < a) :
    gsumBit (sBit (chiSt x a) a) (tBit (chiSt x a) a) i
      = gsumBit (fun l => !sBit x a l) (fun l => !tBit x a l) i := by
  have hs : ∀ l, l < a → sBit (chiSt x a) a l = !sBit x a l := fun l hl =>
    chiSt_in h x (by omega) (by omega)
  have ht : ∀ l, l < a → tBit (chiSt x a) a l = !tBit x a l := fun l hl =>
    chiSt_in h x (by omega) (by omega)
  unfold gsumBit
  rw [hs i hi, ht i hi,
    gcarry_congr i (fun l hl => hs l (by omega)) (fun l hl => ht l (by omega))]

/-- The last carry of the complemented input. -/
theorem cr_chiSt_top {a : ℕ} (h : 2 * a < N) (x : St N) :
    cr (chiSt x a) a a = gcarry (fun l => !sBit x a l) (fun l => !tBit x a l) a :=
  gcarry_congr a (fun _ hl => chiSt_in h x (by omega) (by omega))
    (fun _ hl => chiSt_in h x (by omega) (by omega))

/-- The number `T`, with bit `i` on wire `T_i = 2a - 2i - 1`. -/
def Tval (a : ℕ) (x : St N) : ℕ :=
  ∑ i ∈ Finset.range a, (wire x (2 * a - 2 * i - 1)).toNat * 2 ^ i

theorem Tval_addSt {a : ℕ} (h : 2 * a < N) (x : St N) :
    Tval a (addSt x a) = bsum (gsumBit (sBit x a) (tBit x a)) a :=
  Finset.sum_congr rfl (fun i hi => by rw [addSt_T h x (Finset.mem_range.1 hi)])

/-- After the low incrementer on `Add x`, `T_i` holds the complemented sum bit of the
complemented input. -/
theorem lowIncPerm_addSt_T {a : ℕ} (h : 2 ≤ a ∧ 2 * a < N) (x : St N) {i : ℕ} (hi : i < a) :
    wire (lowIncPerm N a (addSt x a)) (2 * a - 2 * i - 1)
      = !gsumBit (fun l => !sBit x a l) (fun l => !tBit x a l) i := by
  rw [lowIncPerm_addSt_wire h, if_pos (by omega), addSt_T h.2 _ hi, gsumBit_chiSt h.2 x hi]

/-! ### The basis action of the low incrementer -/

section spec

variable {a : ℕ} (h : 2 ≤ a ∧ 2 * a < N) (z : St N)
include h

/-- (a) The wires `S_i`, `i < a` (the even wires `2, 4, …, 2a`) are unchanged. -/
theorem lowIncPerm_wire_S {k : ℕ} (hk : 1 ≤ k) (hka : k ≤ a) :
    wire (lowIncPerm N a z) (2 * k) = wire z (2 * k) := by
  obtain ⟨x, rfl⟩ := addSt_surjective h z
  rw [lowIncPerm_addSt_wire h, if_pos (by omega), addSt_other h.2 _ (by omega) (by omega),
    chiSt_in h.2 x (by omega) (by omega), Bool.not_not,
    addSt_other h.2 x (by omega) (by omega)]

/-- (a) The wires above `2a` are unchanged. -/
theorem lowIncPerm_wire_above {j : ℕ} (hj : 2 * a < j) :
    wire (lowIncPerm N a z) j = wire z j := by
  obtain ⟨x, rfl⟩ := addSt_surjective h z
  rw [lowIncPerm_addSt_wire h, if_neg (by omega), addSt_other h.2 _ (by omega) (by omega),
    chiSt_out h.2 x (by omega), addSt_other h.2 x (by omega) (by omega)]

/-- (b) **The number `T` is incremented modulo `2^a`.** -/
theorem lowIncPerm_Tval : Tval a (lowIncPerm N a z) = (Tval a z + 1) % 2 ^ a := by
  obtain ⟨x, rfl⟩ := addSt_surjective h z
  have hL : Tval a (lowIncPerm N a (addSt x a))
      = bsum (fun i => !gsumBit (fun l => !sBit x a l) (fun l => !tBit x a l) i) a :=
    Finset.sum_congr rfl (fun i hi => by
      rw [lowIncPerm_addSt_T h x (Finset.mem_range.1 hi)])
  rw [hL, Tval_addSt h.2]
  exact (inc_bits (sBit x a) (tBit x a) a).1

/-- (c) **Wire `0` is flipped iff all `T_i` are one.** -/
theorem lowIncPerm_wire_zero :
    wire (lowIncPerm N a z) 0
      = xor (wire z 0) (decide (∀ i, i < a → wire z (2 * a - 2 * i - 1) = true)) := by
  obtain ⟨x, rfl⟩ := addSt_surjective h z
  have e : ∀ u c' c d : Bool, (!c') = xor c d → (!(xor u c')) = xor (xor u c) d := by decide
  have hd : decide (∀ i, i < a → wire (addSt x a) (2 * a - 2 * i - 1) = true)
      = decide (∀ i, i < a → gsumBit (sBit x a) (tBit x a) i = true) :=
    decide_eq_decide.2 (forall₂_congr (fun i hi => by rw [addSt_T h.2 x hi]))
  rw [lowIncPerm_addSt_wire h, if_pos (by omega), addSt_zero h.2, addSt_zero h.2,
    chiSt_out h.2 x (by omega), cr_chiSt_top h.2, hd]
  exact e _ _ _ _ (inc_bits (sBit x a) (tBit x a) a).2

end spec

/-- **The low incrementer.**  For `2 ≤ a` and `2a < N`, the circuit `lowInc N a` has
`24 a - 23` CNOTs and unitary one-qubit gates, and it is, up to phases of modulus one, a
permutation `ρ` of basis states that leaves the even wires `2, …, 2a` and the wires above
`2a` unchanged, increments `T` modulo `2^a`, and flips wire `0` iff all `T_i` are one. -/
theorem lowInc_spec {a : ℕ} (h : 2 ≤ a ∧ 2 * a < N) :
    cnots (lowInc N a) = 24 * a - 23 ∧ UnitaryGates (lowInc N a) ∧
    ∃ ρ : Equiv.Perm (St N), UMono (circMat (lowInc N a)) ρ ∧ ∀ x : St N,
      (∀ k, 1 ≤ k → k ≤ a → wire (ρ x) (2 * k) = wire x (2 * k)) ∧
      (∀ j, 2 * a < j → wire (ρ x) j = wire x j) ∧
      Tval a (ρ x) = (Tval a x + 1) % 2 ^ a ∧
      wire (ρ x) 0
        = xor (wire x 0) (decide (∀ i, i < a → wire x (2 * a - 2 * i - 1) = true)) :=
  ⟨cnots_lowInc h, unitaryGates_lowInc N a, lowIncPerm N a, umono_lowInc N a, fun x =>
    ⟨fun _ hk hka => lowIncPerm_wire_S h x hk hka, fun _ hj => lowIncPerm_wire_above h x hj,
      lowIncPerm_Tval h x, lowIncPerm_wire_zero h x⟩⟩

end Line
