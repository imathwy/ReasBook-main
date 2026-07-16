import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import ConvexAnalysis_Rockafellar_1970.Chap08.Proposition_38_5_1
import ConvexAnalysis_Rockafellar_1970.Chap08.Proposition_39_0_13
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_0_1
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_0_5
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_0_14

noncomputable section

open scoped Rockafellar SetRel

universe u v w

namespace SetRel

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 39.8 is the process-level composition theorem for convex processes,
  together with its closed-case companion and the adjoint-side closure formula.
- `core/canonical`: the chapter already owns convex processes on `A : SetRel U X` via
  `A.IsConvexProcess 𝕜`, relation composition via the canonical `SetRel.comp` notation `A ○ B`,
  graph closure via `cl(·)` / `A.IsClosed`, and process adjoints via `A∗[...]`.
- `bridge/view`: this item is a direct process-side specialization of the Chapter 38 composition
  theorems for bifunctions, using the Chapter 39 indicator-fiber and process-adjoint bridges. No
  new packaged
  “composition data” or “adjoint composition data” owner should appear here.

Primary mathematical domain:
- composition of convex processes in the finite-dimensional real continuous-pairing setting used
  by Chapter 38.

Domain-style sampling used here:
- `SetRel.comp` and `SetRel.IsConvexProcess.comp` from `Chap08.Proposition_39_0_10`;
- `SetRel.closure` / `cl(·)` and `SetRel.IsClosed` from `Chap08.Definition_39_0_5`;
- `SetRel.adjoint` / `A∗[...]` from `Chap08.Definition_39_0_14`;
- `Bifunction.comp` together with the Chapter 38 composition theorems
  `Bifunction.adjointFunction_comp_eq_comp_adjointFunction_of_common_riDom` and
  `Bifunction.isClosedConvex_comp_of_common_riDom_adjoint_inverse` from
  `Chap08.Theorem_38_5` and `Chap08.Proposition_38_5_1`;
- `indicatorFibers`, `dom_indicatorFibers_eq_dom`, and
  `lowerSemicontinuous_uncurry_indicatorFibers_iff_isClosed` from
  `Chap08.Proposition_39_0_13`.

Primitive data vs derived API:
- primitive source data: convex processes `A : SetRel U X` and `B : SetRel X Y`;
- primitive reused owners: `A ○ B`, `(A∗[...]).dom`, `B.dom`, `(B∗[...]).cod`, `cl(·)`, and
  `IsClosed`;
- derived API here: the source adjoint-of-composition identity, the closedness theorem for
  `A ○ B` under the dual qualification, and the adjoint-side closure identity.

Layer target: `source-facing`, stated directly on the canonical `SetRel` owners.
-/

section

variable {U : Type u}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [_root_.FiniteDimensional ℝ U]
variable {X : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [_root_.FiniteDimensional ℝ X]
variable {Y : Type w}
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [_root_.FiniteDimensional ℝ Y]
variable [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ]
variable [HasLinearPairing X X ℝ] [HasContinuousPairing X X ℝ]
variable [HasLinearPairing Y Y ℝ] [HasContinuousPairing Y Y ℝ]

local notation "ri(" C ")" => intrinsicInterior ℝ C

local notation:100 A "∗ᵣ" => (A∗[X, U; ℝ])
local notation:100 A "∗ₛ" => (A∗[Y, X; ℝ])
local notation:100 A "∗ₜ" => (A∗[Y, U; ℝ])

-- Proof sketch: specialize the Chapter 38 product-adjoint theorem to the indicator bifunctions of
-- `A` and `B`, using the Chapter 39 bridge that identifies relation composition with the product
-- of the corresponding indicator bifunctions. The Chapter 38 qualification
-- `ri(dom (adjoint (indicatorFibers ℝ A))) ∩ ri(dom (indicatorFibers ℝ B)) ≠ ∅`
-- reads process-side as `ri((A∗ᵣ).dom) ∩ ri(B.dom) ≠ ∅`.
/-- Theorem 39.8 (1): if convex processes `A` and `B` have the same orientation and
`ri (dom A*)` meets `ri (dom B)`, then the adjoint of the product `(BA)` is the product of the
adjoints, rendered on the canonical `SetRel` owners as
`(A ○ B)∗ₜ = B∗ₛ ○ A∗ᵣ`. -/
theorem adjoint_comp_eq_comp_adjoint_of_common_ri_dom_adjoint_dom
    {aRel : SetRel U X} {bRel : SetRel X Y}
    (hA : aRel.IsConvexProcess ℝ) (hB : bRel.IsConvexProcess ℝ)
    (hri : (ri((aRel∗ᵣ).dom) ∩ ri(bRel.dom)).Nonempty) :
    (aRel ○ bRel)∗ₜ = bRel∗ₛ ○ aRel∗ᵣ := sorry

-- Proof sketch: specialize the closed-case Chapter 38 composition theorem to the indicator
-- bifunctions of `A` and `B`. The dual regularity hypothesis in Corollary 38.5.1 is
-- `ri(dom (adjoint (indicatorFibers ℝ A))) ∩
--   ri(dom ((adjoint (indicatorFibers ℝ B)) _*)) ≠ ∅`.
-- On the process surface this is `ri((A∗ᵣ).dom) ∩ ri(((B∗ₛ)⁻¹).dom)`, equivalently
-- `ri((A∗ᵣ).dom) ∩ ri((B∗ₛ).cod)` by `SetRel.dom_inv`.
/-- Theorem 39.8 (2): if `A` and `B` are closed convex processes and
`ri (range B*)` meets `ri (dom A*)`, then the product process `(BA)` is closed. -/
theorem isClosed_comp_of_isClosed_of_common_ri_cod_adjoint_dom_adjoint
    {aRel : SetRel U X} {bRel : SetRel X Y}
    (hA : aRel.IsConvexProcess ℝ) (hB : bRel.IsConvexProcess ℝ)
    (hA_closed : aRel.IsClosed) (hB_closed : bRel.IsClosed)
    (hri : (ri((bRel∗ₛ).cod) ∩ ri((aRel∗ᵣ).dom)).Nonempty) :
    (aRel ○ bRel).IsClosed := sorry

-- Proof sketch: under the same closedness and dual relative-interior hypothesis, apply the
-- Chapter 38 adjoint-side closure formula to the indicator bifunctions of `A` and `B`, then
-- translate back through the Chapter 39 adjoint-process and graph-closure owners.
/-- Theorem 39.8 (3): if `A` and `B` are closed convex processes and
`ri (range B*)` meets `ri (dom A*)`, then the adjoint of the product `(BA)` is the graph closure
of the product of the adjoints. -/
theorem adjoint_comp_eq_closure_comp_adjoint_of_isClosed_of_common_ri_cod_adjoint_dom_adjoint
    {aRel : SetRel U X} {bRel : SetRel X Y}
    (hA : aRel.IsConvexProcess ℝ) (hB : bRel.IsConvexProcess ℝ)
    (hA_closed : aRel.IsClosed) (hB_closed : bRel.IsClosed)
    (hri : (ri((bRel∗ₛ).cod) ∩ ri((aRel∗ᵣ).dom)).Nonempty) :
    (aRel ○ bRel)∗ₜ = cl(bRel∗ₛ ○ aRel∗ᵣ) := sorry

end

end SetRel
