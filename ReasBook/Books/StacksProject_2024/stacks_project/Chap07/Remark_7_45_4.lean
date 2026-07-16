import Mathlib
import StacksProject_2024.stacks_project.Chap07.Definition_7_15_1_Topoi
import StacksProject_2024.stacks_project.Chap07.Remark_7_45_3
import StacksProject_2024.stacks_project.Chap18.Definition_18_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.TwoSquare
open scoped MorphismOfTopoiIn TwoSquare

noncomputable section

universe u v

variable {C'' C' C D'' D' D : Type u}
variable [Category.{v} C''] [Category.{v} C'] [Category.{v} C]
variable [Category.{v} D''] [Category.{v} D'] [Category.{v} D]
variable {JC'' : GrothendieckTopology C''}
variable {JC' : GrothendieckTopology C'}
variable {JC : GrothendieckTopology C}
variable {JD'' : GrothendieckTopology D''}
variable {JD' : GrothendieckTopology D'}
variable {JD : GrothendieckTopology D}

/- Domain-style sampling for Remark 7.45.4:
- primary domain: base-change mates for commutative squares of morphisms of ringed topoi;
- sampled owner API:
  `MorphismOfTopoiIn.comp`,
  `MorphismOfTopoiIn.baseChange`,
  `MorphismOfTopoiIn.baseChange_horizontal_composite_eq`,
  `Functor.morphismOfTopoiInOfContinuous`,
  `RingedSite.Hom.toMorphismOfTopoi`,
  `CategoryTheory.mateEquiv_hcomp`;
- source/core/bridge triage:
  `source-facing`: the ringed-topos horizontal-composition statement;
  `core/canonical`: `MorphismOfTopoiIn` together with `MorphismOfTopoiIn.baseChange`;
  `bridge/view`: passage from a ringed-site morphism to the canonical site-to-topos bridge
    `RingedSite.Hom.toMorphismOfTopoi`, defined through
    `Functor.morphismOfTopoiInOfContinuous`.

Primitive data are the ringed-site morphisms together with commutativity equalities for their
underlying morphisms of topoi. The induced inverse-image `TwoSquare`s are derived bridge data.
The horizontal-composition formula itself belongs to the canonical topos-level owner theorem
`MorphismOfTopoiIn.baseChange_horizontal_composite_eq`, so this file should reuse that owner
directly. -/

namespace RingedSite.Hom

variable {X'' X' X Y'' Y' Y : RingedSite.{u, v}}

/-- A commutative square of the underlying morphisms of topoi induces the corresponding
`TwoSquare` on inverse-image functors. This is an internal bridge from source-style commutativity
data to the canonical square datum used by base change. -/
private abbrev inverseImageSquareOfCompEq
    (g : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (h : Y' ⟶ Y)
    [PreservesFiniteLimits
      (g.base.sheafPullback (Type (max u v)) X.siteTopology X'.siteTopology)]
    [PreservesFiniteLimits
      (f'.base.sheafPullback (Type (max u v)) Y'.siteTopology X'.siteTopology)]
    [PreservesFiniteLimits
      (f.base.sheafPullback (Type (max u v)) Y.siteTopology X.siteTopology)]
    [PreservesFiniteLimits
      (h.base.sheafPullback (Type (max u v)) Y.siteTopology Y'.siteTopology)]
    (hcomm :
      MorphismOfTopoiIn.comp
          f.toMorphismOfTopoi
          g.toMorphismOfTopoi =
        MorphismOfTopoiIn.comp
          h.toMorphismOfTopoi
          f'.toMorphismOfTopoi) :
    TwoSquare
      (h.toMorphismOfTopoi⁻¹)
      (f.toMorphismOfTopoi⁻¹)
      (f'.toMorphismOfTopoi⁻¹)
      (g.toMorphismOfTopoi⁻¹) :=
  eqToHom
    ((by
        simpa [MorphismOfTopoiIn.comp] using
          congrArg LeftExactAdjunction.inverseImage hcomm :
          (f.toMorphismOfTopoi⁻¹) ⋙ (g.toMorphismOfTopoi⁻¹) =
            (h.toMorphismOfTopoi⁻¹) ⋙ (f'.toMorphismOfTopoi⁻¹)).symm)

/- Source/core/bridge triage for the public API below:
- `inverseImageSquareOfCompEq` is an internal bridge/view from commutativity of the underlying
  morphisms of topoi to the canonical square owner;
- the public theorem `baseChange_horizontal_composite_eq` is source-facing: it takes commutative
  squares of ringed-topos morphisms with commuting underlying morphisms of topoi, converts them
  to the canonical inverse-image squares internally, and then reuses the owner theorem.
-/

-- Proof sketch: convert the two commutative underlying squares of topoi to their canonical
-- inverse-image `TwoSquare`s using `inverseImageSquareOfCompEq`, then invoke the canonical
-- topos-level owner theorem directly.
/-- Remark 7.45.4: for two horizontally composable squares of morphisms of ringed topoi whose
underlying morphisms of topoi commute, the composite of the two base change maps is the base
change map of the outer rectangle. -/
theorem baseChange_horizontal_composite_eq
    (g' : X'' ⟶ X') (g : X' ⟶ X) (f'' : X'' ⟶ Y'') (f' : X' ⟶ Y') (f : X ⟶ Y)
    (h' : Y'' ⟶ Y') (h : Y' ⟶ Y)
    [PreservesFiniteLimits
      (g'.base.sheafPullback (Type (max u v)) X'.siteTopology X''.siteTopology)]
    [PreservesFiniteLimits
      (g.base.sheafPullback (Type (max u v)) X.siteTopology X'.siteTopology)]
    [PreservesFiniteLimits
      (f''.base.sheafPullback (Type (max u v)) Y''.siteTopology X''.siteTopology)]
    [PreservesFiniteLimits
      (f'.base.sheafPullback (Type (max u v)) Y'.siteTopology X'.siteTopology)]
    [PreservesFiniteLimits
      (f.base.sheafPullback (Type (max u v)) Y.siteTopology X.siteTopology)]
    [PreservesFiniteLimits
      (h'.base.sheafPullback (Type (max u v)) Y'.siteTopology Y''.siteTopology)]
    [PreservesFiniteLimits
      (h.base.sheafPullback (Type (max u v)) Y.siteTopology Y'.siteTopology)]
    (leftComm :
      MorphismOfTopoiIn.comp
          f'.toMorphismOfTopoi
          g'.toMorphismOfTopoi =
        MorphismOfTopoiIn.comp
          h'.toMorphismOfTopoi
          f''.toMorphismOfTopoi)
    (rightComm :
      MorphismOfTopoiIn.comp
          f.toMorphismOfTopoi
          g.toMorphismOfTopoi =
        MorphismOfTopoiIn.comp
          h.toMorphismOfTopoi
          f'.toMorphismOfTopoi) :
    (Functor.associator
        (f.toMorphismOfTopoi _*)
        (h.toMorphismOfTopoi⁻¹)
        (h'.toMorphismOfTopoi⁻¹)).inv ≫
        Functor.whiskerRight
          (MorphismOfTopoiIn.baseChange
            g.toMorphismOfTopoi
            f'.toMorphismOfTopoi
            f.toMorphismOfTopoi
            h.toMorphismOfTopoi
            (inverseImageSquareOfCompEq g f' f h rightComm))
          (h'.toMorphismOfTopoi⁻¹) ≫
          (Functor.associator
            (g.toMorphismOfTopoi⁻¹)
            (f'.toMorphismOfTopoi _*)
            (h'.toMorphismOfTopoi⁻¹)).hom ≫
            Functor.whiskerLeft
              (g.toMorphismOfTopoi⁻¹)
              (MorphismOfTopoiIn.baseChange
                g'.toMorphismOfTopoi
                f''.toMorphismOfTopoi
                f'.toMorphismOfTopoi
                h'.toMorphismOfTopoi
                (inverseImageSquareOfCompEq g' f'' f' h' leftComm)) ≫
              (Functor.associator
                (g.toMorphismOfTopoi⁻¹)
                (g'.toMorphismOfTopoi⁻¹)
                (f''.toMorphismOfTopoi _*)).inv =
      MorphismOfTopoiIn.baseChange
        (MorphismOfTopoiIn.comp
          g.toMorphismOfTopoi
          g'.toMorphismOfTopoi)
        f''.toMorphismOfTopoi
        f.toMorphismOfTopoi
        (MorphismOfTopoiIn.comp
          h.toMorphismOfTopoi
          h'.toMorphismOfTopoi)
        (inverseImageSquareOfCompEq g f' f h rightComm ≫ₕ
          inverseImageSquareOfCompEq g' f'' f' h' leftComm) := by
  simpa only [toMorphismOfTopoi_pushforward] using
    MorphismOfTopoiIn.baseChange_horizontal_composite_eq
      g'.toMorphismOfTopoi
      g.toMorphismOfTopoi
      f''.toMorphismOfTopoi
      f'.toMorphismOfTopoi
      f.toMorphismOfTopoi
      h'.toMorphismOfTopoi
      h.toMorphismOfTopoi
      (inverseImageSquareOfCompEq g' f'' f' h' leftComm)
      (inverseImageSquareOfCompEq g f' f h rightComm)

end RingedSite.Hom
