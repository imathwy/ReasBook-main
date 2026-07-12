import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.RepresentationTheory.Character
import LinearRepresentations_Serre_1977.Chap04.Definition_4_9
import LinearRepresentations_Serre_1977.Chap04.Example_4_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

-- Analogue notes: `MeasureTheory.L2.inner_def` is the canonical `L²` formula API, and the local
-- Serre precedent is `squareIntegrableClassFunctionScalar` in Definition 4-28.
-- Source/core/bridge triage:
-- `source-facing`: Serre's pairing `(φ | ψ)_G` and the character pairing on `L²(G)`;
-- `core/canonical`: the normalized-Haar `L²(G)` inner product and `ContinuousMap.toLp`;
-- `bridge/view`: the reversed-argument scalar-product owner and `Representation.characterL2`.

universe u v w

section

variable {G : Type u} [Group G] [TopologicalSpace G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]

local notation "L²G" => (G →₂[(μG : Measure G)] ℂ)

/-- Definition 4-12 (1): the scalar product on square-integrable complex-valued functions on `G`
is the normalized-Haar `L²(G)` inner product, written in the source order `(φ | ψ)_G`. -/
def squareIntegrableFunctionInner (φ ψ : L²G) : Complex :=
  inner ℂ ψ φ

scoped[Representation] notation:max "(" φ " | " ψ ")_G" =>
  squareIntegrableFunctionInner φ ψ

open scoped Representation

/-- The textbook scalar product on `L²(G)` is the ambient normalized-Haar `L²(G)` inner product,
with Serre's convention that the second variable is conjugate-linear. -/
@[simp] theorem squareIntegrableFunctionInner_eq_inner
    (φ ψ : L²G) :
    (φ | ψ)_G = inner ℂ ψ φ :=
  rfl

/-- The scalar product on `L²(G)` is computed by integrating `φ t * conj (ψ t)` against the
normalized Haar measure. -/
theorem squareIntegrableFunctionInner_def
    (φ ψ : L²G) :
    (φ | ψ)_G = ∫ t, φ t * conj (ψ t) ∂μG := by
  simpa [mul_comm] using (L2.inner_def ψ φ)

section FiniteGroup

variable [Finite G] [DiscreteTopology G]

/-- The finite-group specialization uses the canonical `Fintype` structure induced by
`Finite G` to write Serre's averaging sum over `G`. -/
local instance instFintypeDefinition_4_12FiniteGroup : Fintype G := Fintype.ofFinite G

/-- For Definition 4-12, the finite-group specialization of the normalized-Haar scalar product is
the average `((Nat.card G : ℂ)⁻¹) * ∑ t : G, φ t * conj (ψ t)`. -/
theorem squareIntegrableFunctionInner_eq_average_sum
    (φ ψ : L²G) :
    (φ | ψ)_G = ((Nat.card G : ℂ)⁻¹) * ∑ t : G, φ t * conj (ψ t) := by
  rw [squareIntegrableFunctionInner_def]
  calc
    ∫ t, φ t * conj (ψ t) ∂μG =
        (Nat.card G : ℝ)⁻¹ • ∑ t : G, φ t * conj (ψ t) :=
      normalizedHaarMeasure_integral_eq_average (fun t ↦ φ t * conj (ψ t))
    _ = ((Nat.card G : ℂ)⁻¹) * ∑ t : G, φ t * conj (ψ t) := by
      simp

end FiniteGroup

end
