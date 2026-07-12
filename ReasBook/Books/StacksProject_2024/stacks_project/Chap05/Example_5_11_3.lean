import Mathlib
import StacksProject_2024.Chap05.Definition_5_11_1

-- Declarations for this item will be appended below by the statement pipeline.

open Set Order TopologicalSpace Topology
open scoped unitInterval

/- Domain-style sampling for Example 5.11.3:
- primary domain: Noetherian topological spaces and codimension of irreducible closed subsets;
- inspected owner declarations: `IrreducibleCloseds`, `coheight`, `NoetherianSpace`, and the
  chapter recall `Definition_5_11_1`;
- best owner abstraction: the source-facing example space should be the named type
  `TailTopologyUnitInterval`; the canonical owners `IrreducibleCloseds` and `coheight` should then
  be used directly on that space, without parallel codimension wrappers;
- primitive-vs-derived split: the only primitive data here is the carrier `[0, 1]` together with
  its tail topology; the bundled irreducible closed subset `{0}` and its codimension are derived
  API from the canonical owners.

Layer triage:
- `source-facing`: the example space `TailTopologyUnitInterval` and the codimension statement for
  the irreducible closed subset `{0}`;
- `core/canonical`: `IrreducibleCloseds`, `coheight`, and `NoetherianSpace`;
- `bridge/view`: the named irreducible closed subset `tailTopologyUnitIntervalZero`. -/

/-- The point set `[0, 1]` equipped with the tail topology from Example 5.11.3. -/
structure TailTopologyUnitInterval where
  val : I

namespace TailTopologyUnitInterval

instance : Coe TailTopologyUnitInterval ℝ where
  coe x := x.val

@[ext]
theorem ext {x y : TailTopologyUnitInterval} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  simpa using h

instance : Zero TailTopologyUnitInterval := ⟨⟨0⟩⟩

@[simp] theorem coe_eq_zero {x : TailTopologyUnitInterval} : (x : ℝ) = 0 ↔ x = 0 := by
  sorry

@[simp] theorem coe_zero : ((0 : TailTopologyUnitInterval) : ℝ) = 0 :=
  rfl

end TailTopologyUnitInterval

/-- The right endpoint of the `n`th closed initial segment `[0, 1 - 1 / (n + 1)]`. -/
private noncomputable def tailCut (n : ℕ) : ℝ :=
  1 - 1 / (n + 1 : ℝ)

/-- The basic open tail `(1 - 1 / (n + 1), 1]` in the topology from Example 5.11.3. -/
private noncomputable def tailTopologyUnitIntervalBasicOpen (n : ℕ) : Set TailTopologyUnitInterval :=
  { x | tailCut n < x }

private theorem tailCut_nonneg (n : ℕ) : 0 ≤ tailCut n := by
  sorry

private theorem tailCut_le_one (n : ℕ) : tailCut n ≤ 1 := by
  sorry

private theorem tailCut_lt_one (n : ℕ) : tailCut n < 1 := by
  sorry

private theorem tailCut_strictMono : StrictMono tailCut := by
  sorry

private theorem exists_tailCut_ge_of_ne_one (x : TailTopologyUnitInterval) (hx : (x : ℝ) ≠ 1) :
    ∃ n, (x : ℝ) ≤ tailCut n := by
  sorry

private noncomputable def tailRankValue (x : TailTopologyUnitInterval) : ℕ∞ :=
  if hx : (x : ℝ) = 1 then ⊤ else Nat.find (exists_tailCut_ge_of_ne_one x hx)

private noncomputable def tailRank (x : TailTopologyUnitInterval) : WithUpper ℕ∞ :=
  WithUpper.toUpper (tailRankValue x)

/-- The topology on `[0, 1]` from Example 5.11.3, realized as the topology induced from the
canonical upper topology on the stage order `ℕ∞`. -/
@[reducible] noncomputable instance : TopologicalSpace TailTopologyUnitInterval :=
  TopologicalSpace.induced tailRank inferInstance

private theorem tailRank_inducing : IsInducing tailRank :=
  ⟨rfl⟩

private theorem tailRankValue_tailCut_lt_iff (x : TailTopologyUnitInterval) (n : ℕ) :
    tailCut n < (x : ℝ) ↔ (n : ℕ∞) < tailRankValue x := by
  sorry

private theorem tailRankValue_eq_zero_iff (x : TailTopologyUnitInterval) :
    tailRankValue x = 0 ↔ (x : ℝ) = 0 := by
  sorry

private theorem tailTopologyUnitIntervalBasicOpen_eq_preimage (n : ℕ) :
    tailTopologyUnitIntervalBasicOpen n =
      tailRank ⁻¹' (((Set.Iic (WithUpper.toUpper (n : ℕ∞))) : Set (WithUpper ℕ∞))ᶜ) := by
  ext x
  simp [tailTopologyUnitIntervalBasicOpen, tailRank, tailRankValue_tailCut_lt_iff]

private noncomputable def tailPoint (n : ℕ) : TailTopologyUnitInterval where
  val := ⟨tailCut n, tailCut_nonneg n, tailCut_le_one n⟩

@[simp] private theorem coe_tailPoint (n : ℕ) : ((tailPoint n : TailTopologyUnitInterval) : ℝ) = tailCut n :=
  rfl

@[simp] private theorem tailPoint_zero : tailPoint 0 = 0 := by
  sorry

private theorem tailRankValue_tailPoint (n : ℕ) : tailRankValue (tailPoint n) = n := by
  sorry

private theorem tailTopologyUnitInterval_zero_isClosed :
    IsClosed ({(0 : TailTopologyUnitInterval)} : Set TailTopologyUnitInterval) := by
  sorry

/-- The irreducible closed subset `{0}` of the tail-topology unit interval. -/
def tailTopologyUnitIntervalZero :
    IrreducibleCloseds TailTopologyUnitInterval :=
  ⟨{0}, isIrreducible_singleton, tailTopologyUnitInterval_zero_isClosed⟩

@[simp] theorem coe_tailTopologyUnitIntervalZero :
    (tailTopologyUnitIntervalZero : Set TailTopologyUnitInterval) = {0} :=
  rfl

private def tailPointClosure (n : ℕ) : IrreducibleCloseds TailTopologyUnitInterval :=
  ⟨closure ({tailPoint n} : Set TailTopologyUnitInterval), isIrreducible_singleton.closure,
    isClosed_closure⟩

private theorem coe_tailPointClosure (n : ℕ) :
    (tailPointClosure n : Set TailTopologyUnitInterval) =
      tailRank ⁻¹' (Set.Iic (WithUpper.toUpper (n : ℕ∞))) := by
  sorry

private theorem tailPointClosure_zero :
    tailPointClosure 0 = tailTopologyUnitIntervalZero := by
  ext x
  simp [tailPointClosure, tailTopologyUnitIntervalZero, tailPoint_zero,
    tailTopologyUnitInterval_zero_isClosed.closure_eq]

/-- The tail-topology unit interval is a Noetherian topological space. -/
instance : NoetherianSpace TailTopologyUnitInterval := by
  sorry

private theorem tailPointClosure_strictMono : StrictMono tailPointClosure := by
  sorry

/-- Example 5.11.3: in the topology on `[0, 1]` whose opens are `∅`, `[0, 1]`, and the tails
`(1 - 1 / n, 1]`, the irreducible closed subset `{0}` has infinite codimension. -/
theorem tailTopologyUnitInterval_zero_codimension_eq_top :
    coheight tailTopologyUnitIntervalZero = ⊤ := by
  apply Order.coheight_eq_top_iff.mpr
  intro n
  refine ⟨(LTSeries.range n).map tailPointClosure tailPointClosure_strictMono, ?_, ?_⟩
  · simp [tailPointClosure_zero, LTSeries.head_map]
  · simp
