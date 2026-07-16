import StacksProject_2024.stacks_project.Chap20.«20_14_1_1»
import StacksProject_2024.stacks_project.Chap20.Lemma_20_32_3
import StacksProject_2024.stacks_project.Chap20.Sections_on_open

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry.RingedSpaceCohomology RingedSpaceDerivedPushforward

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

open scoped RingedSpaceOpenHypercohomology

/-
Domain-style sampling for Lemma 20.32.6:
- primary domain: derived pushforward, objectwise hypercohomology presheaves, and cohomology
  sheaves on ringed spaces;
- sampled owner declarations:
  `(Opens.map f.hom.base).op ⋙ _`,
  `moduleDerivedPushforward`,
  `moduleUnderlyingPresheaf`,
  `moduleUnderlyingSheaf`,
  `objectwiseCohomologyPresheaf_sheafification_isomorphic_cohomologySheaf`;
- best owner abstraction: the source-facing presheaf `V ↦ H^i(f⁻¹(V), K)` should be expressed
  canonically as `(Opens.map f.hom.base).op ⋙ 𝓗'[i](X, K)`, while the sheafification owner remains
  the chapter theorem `objectwiseCohomologyPresheaf_sheafification_isomorphic_cohomologySheaf`;
- primitive data: `f : X ⟶ Y`, `K : D(𝒪_X)`, `i : ℤ`, and an open `V ⊆ Y`;
- derived API: the presheaf-level comparison with `𝓗'[i](Y, (R(f)_*).obj K)`, the resulting
  sheafification comparison, and the pointwise evaluation companion.

Source/core/bridge triage:
- `source-facing`: the presheaf `V ↦ H^i(f^{-1}(V), K)` on `Y` and its associated-sheaf
  comparison;
- `core/canonical`: `objectwiseCohomologyPresheaf_sheafification_isomorphic_cohomologySheaf`;
- `bridge/view`: the comparison between `(Opens.map f.hom.base).op ⋙ 𝓗'[i](X, K)` and
  `𝓗'[i](Y, (R(f)_*).obj K)`, plus the objectwise evaluation at `V`.

This file should therefore keep the preimage presheaf and its sheafification statement as the
source-facing public surface, while reusing the upstream sheafification owner theorem rather than
duplicating it under a second local name. -/

-- Proof sketch: Lemma `20.32.5` identifies `RΓ(f⁻¹(V), K)`, viewed over `Γ(V, 𝒪_Y)` by
-- restriction of scalars, with `RΓ(V, R(f)_* K)`. Taking degree-`i` homology and forgetting the
-- module structure yields a natural isomorphism between the source preimage presheaf
-- `V ↦ H^i(f⁻¹(V), K)` and the objectwise cohomology presheaf of `R(f)_* K`.
/-- The source-facing presheaf `V ↦ H^i(f⁻¹(V), K)` on `Y`, expressed through the canonical
objectwise cohomology presheaf on `X`. -/
abbrev preimageObjectwiseCohomologyPresheaf
    (f : X ⟶ Y)
    (K : DerivedCategory (RingedSpace.Modules X)) (i : ℤ) :
    (Opens Y.carrier)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (Opens.map f.hom.base).op ⋙ 𝓗'[i](X, K)

/-- The presheaf `V ↦ H^i(f^{-1}(V), K)` is canonically isomorphic to the degree-`i` objectwise
cohomology presheaf of `R(f)_* K`. -/
theorem preimageObjectwiseCohomologyPresheaf_isomorphic_pushforwardObjectwiseCohomologyPresheaf
    (f : X ⟶ Y)
    (K : DerivedCategory (RingedSpace.Modules X)) (i : ℤ) :
    IsIsomorphic
      (preimageObjectwiseCohomologyPresheaf f K i)
      (𝓗'[i](Y, (R(f)_*).obj K)) := by
  sorry

-- Proof sketch: replace the source presheaf `V ↦ H^i(f⁻¹(V), K)` by the canonically isomorphic
-- presheaf `𝓗'[i](Y, (R(f)_*).obj K)` using the previous theorem, then apply the chapter owner
-- theorem `objectwiseCohomologyPresheaf_sheafification_isomorphic_cohomologySheaf` to `R(f)_* K`.
/-- Lemma 20.32.6: for a morphism of ringed spaces `f : X ⟶ Y` and `K ∈ D(𝒪_X)`, the
sheaf associated to the presheaf `V ↦ H^i(f^{-1}(V), K)` is canonically isomorphic to the
degree-`i` cohomology sheaf of `R(f)_* K`. -/
@[stacks 0D5X]
theorem preimageObjectwiseCohomologyPresheaf_sheafification_isomorphic_pushforwardCohomologySheaf
    (f : X ⟶ Y)
    [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    (K : DerivedCategory (RingedSpace.Modules X)) (i : ℤ) :
    IsIsomorphic
      (𝓗[i](Y, (R(f)_*).obj K))
      ((presheafToSheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}).obj
        (preimageObjectwiseCohomologyPresheaf f K i)) := by
  sorry

-- Proof sketch: evaluate the presheaf comparison
-- `preimageObjectwiseCohomologyPresheaf_isomorphic_pushforwardObjectwiseCohomologyPresheaf` at
-- `V`, and identify `((Opens.map f.hom.base).obj V)` with `f^{-1}(V)`.
/-- On an open subset `V ⊆ Y`, the objectwise cohomology presheaf of `R(f)_* K` has value
`H^i(f^{-1}(V), K)`. -/
lemma pushforwardObjectwiseCohomologyPresheaf_obj_isomorphic_preimageHypercohomology
    (f : X ⟶ Y)
    (K : DerivedCategory (RingedSpace.Modules X)) (i : ℤ) (V : Opens Y.carrier) :
    IsIsomorphic
      ((𝓗'[i](Y, (R(f)_*).obj K)).obj (op V))
      (H^i(preimageOpen f V, K)) := by
  sorry

end AlgebraicGeometry.RingedSpace
