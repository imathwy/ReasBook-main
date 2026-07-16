import Mathlib
import StacksProject_2024.stacks_project.Chap21.Definition_21_31_2
import StacksProject_2024.stacks_project.Chap21.«21_30_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for 21.31.0.1:
- primary domain: inverse-image functors from the small Zariski site of `X` to localized slice
  sites `LC/X`;
- inspected owner declarations:
  `Functor.sheafPullback`,
  `comparisonTopologyPullback`,
  `TopCat.Sheaf.pullback`,
  `Functor.sheafPullbackComp'`;
- best owner abstraction: the primitive owner is the coefficient-category-generic inverse image
  along a chosen continuous functor `π : Opens X.obj ⥤ Over X`, with the qc owner obtained by
  postcomposing that owner with the localized topology-comparison pullback;
- primitive data: the coefficient category `A`, the localized topology on `Over X`, the
  comparison `τzar ≤ τqc`, the functor `π`, and the standard continuity/right-adjoint hypotheses;
  notation `π_X⁻¹`, `π_{X,*}`, `a_X⁻¹`, `a_{X,*}`.

Source/core/bridge triage:
- `source-facing`: the Chapter 21 symbols `π_X⁻¹`, `π_{X,*}`, `a_X⁻¹`, and `a_{X,*}`;
- `core/canonical`: `Functor.sheafPullback` and `comparisonTopologyPullback`;
- `bridge/view`: the coefficient-category specializations below for `Type` and
  `AddCommGrpCat`.
-/

open CategoryTheory TopologicalSpace
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u v

section

variable (A : Type v) [Category A]
variable {X : LCCat.{u}}

/-- Sheaves of `A` on the small Zariski site of `X`. -/
abbrev LCSmallSheaf (X : LCCat.{u}) :=
  TopCat.Sheaf A X.obj

/-- Sheaves of `A` on a localized slice site over `X`. -/
abbrev LCSliceSheaf (J : GrothendieckTopology (Over X)) :=
  Sheaf J A

/-- The small-to-slice inverse-image owner induced by a continuous functor
`π : Opens X.obj ⥤ Over X`. -/
abbrev piInverse
    (J : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) J]
    [(π.sheafPushforwardContinuous A (Opens.grothendieckTopology X.obj)
      J).IsRightAdjoint] :
    LCSmallSheaf A X ⥤ LCSliceSheaf A J :=
  π.sheafPullback A (Opens.grothendieckTopology X.obj) J

/-- The Chapter 21 inverse image `a_X⁻¹`, obtained by following `π_X⁻¹` with the localized
qc/Zariski comparison pullback. -/
abbrev aInverse
    {τzar τqc : GrothendieckTopology LCCat.{u}}
    (hle : τzar ≤ τqc)
    {X : LCCat.{u}}
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) (τzar.over X)]
    [(π.sheafPushforwardContinuous A (Opens.grothendieckTopology X.obj)
      (τzar.over X)).IsRightAdjoint]
    [HasWeakSheafify (τqc.over X) A] :
    LCSmallSheaf A X ⥤ LCSliceSheaf A (τqc.over X) :=
  piInverse A (τzar.over X) π ⋙ comparisonTopologyPullback A hle X

end

section

variable {X : LCCat.{u}}

/-- Sheaves of types on the small Zariski site of `X`. -/
abbrev SmallTypeSheaf (X : LCCat.{u}) :=
  LCSmallSheaf (Type u) X

/-- Sheaves of types on a localized slice site over `X`. -/
abbrev LCZarTypeSheaf {X : LCCat.{u}} (J : GrothendieckTopology (Over X)) :=
  LCSliceSheaf (Type u) J

/-- The canonical small abelian sheaf category on `X`. -/
abbrev smallAbSheafCategory (X : LCCat.{u}) :=
  Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}

/-- Sheaves of abelian groups on the small Zariski site of `X`. -/
abbrev SmallAbSheaf (X : LCCat.{u}) :=
  smallAbSheafCategory X

/-- Sheaves of abelian groups on a localized slice site over `X`. -/
abbrev LCZarAbSheaf {X : LCCat.{u}} (J : GrothendieckTopology (Over X)) :=
  LCSliceSheaf AddCommGrpCat.{u + 1} J

/-- `π_X⁻¹` on sheaves of types. -/
abbrev piInverseType
    (J : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) J]
    [(π.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology X.obj)
      J).IsRightAdjoint] :
    SmallTypeSheaf X ⥤ LCZarTypeSheaf J :=
  π.sheafPullback (Type u) (Opens.grothendieckTopology X.obj) J

/- Textbook notation for the `Type`-valued inverse-image owner `π_X⁻¹`. -/
notation "π[" J ", " π "]⁻¹" => piInverseType J π

/-- `π_X⁻¹` on abelian sheaves. -/
abbrev piInverseAb
    (J : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) J]
    [(π.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.obj) J).IsRightAdjoint] :
    SmallAbSheaf X ⥤ LCZarAbSheaf J :=
  π.sheafPullback AddCommGrpCat.{u + 1} (Opens.grothendieckTopology X.obj) J

/-- The direct-image owner `π_{X,*}` on abelian sheaves. -/
abbrev piPushforwardAb
    (J : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) J] :
    LCZarAbSheaf J ⥤ SmallAbSheaf X :=
  π.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X.obj) J

/- Textbook notation for the abelian direct-image owner `π_{X,*}`. -/
scoped[CategoryTheory.GrothendieckTopology] notation "π[" J ", " π "]*" =>
  piPushforwardAb J π

/-- The direct-image owner `π_{X,*}` is additive on abelian sheaves. -/
instance piPushforwardAb_additive
    (J : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) J]
    [Functor.Additive
      (π.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology X.obj) J)] :
    Functor.Additive (piPushforwardAb J π) := by
  simpa [piPushforwardAb]

/-- The abelian inverse-image owner `π_X⁻¹` is additive. -/
instance piInverseAb_additive
    (J : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) J]
    [((π.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.obj) J).IsRightAdjoint)]
    [Functor.Additive
      (π.sheafPullback AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology X.obj) J)] :
    Functor.Additive (piInverseAb J π) := by
  simpa [piInverseAb]

/-- The abelian inverse-image owner `π_X⁻¹` preserves finite limits. -/
instance piInverseAb_preservesFiniteLimits
    (J : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) J]
    [((π.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.obj) J).IsRightAdjoint)]
    [CategoryTheory.Limits.PreservesFiniteLimits
      (π.sheafPullback AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology X.obj) J)] :
    CategoryTheory.Limits.PreservesFiniteLimits (piInverseAb J π) := by
  simpa [piInverseAb]

/-- The abelian inverse-image owner `π_X⁻¹` preserves finite colimits. -/
instance piInverseAb_preservesFiniteColimits
    (J : GrothendieckTopology (Over X))
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) J]
    [((π.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.obj) J).IsRightAdjoint)]
    [CategoryTheory.Limits.PreservesFiniteColimits
      (π.sheafPullback AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology X.obj) J)] :
    CategoryTheory.Limits.PreservesFiniteColimits (piInverseAb J π) := by
  simpa [piInverseAb]

/-- `a_X⁻¹` on sheaves of types. -/
abbrev aInverseType
    {τzar τqc : GrothendieckTopology LCCat.{u}}
    (hle : τzar ≤ τqc)
    {X : LCCat.{u}}
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) (τzar.over X)]
    [(π.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology X.obj)
      (τzar.over X)).IsRightAdjoint]
    [HasWeakSheafify (τqc.over X) (Type u)] :
    SmallTypeSheaf X ⥤ Sheaf (τqc.over X) (Type u) :=
  piInverseType (τzar.over X) π ⋙ comparisonTopologyPullback (Type u) hle X

/- Textbook notation for the `Type`-valued inverse-image owner `a_X⁻¹`. -/
notation "a[" hle ", " π "]⁻¹" => aInverseType hle π

/-- `a_X⁻¹` on abelian sheaves. -/
abbrev aInverseAb
    {τzar τqc : GrothendieckTopology LCCat.{u}}
    (hle : τzar ≤ τqc)
    {X : LCCat.{u}}
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) (τzar.over X)]
    [(π.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.obj) (τzar.over X)).IsRightAdjoint]
    [HasWeakSheafify (τqc.over X) AddCommGrpCat.{u + 1}] :
    SmallAbSheaf X ⥤ Sheaf (τqc.over X) AddCommGrpCat.{u + 1} :=
  piInverseAb (τzar.over X) π ⋙ comparisonTopologyPullbackAb hle X

/-- The abelian inverse-image owner `a_X⁻¹` is additive. -/
instance aInverseAb_additive
    {τzar τqc : GrothendieckTopology LCCat.{u}}
    (hle : τzar ≤ τqc)
    {X : LCCat.{u}}
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) (τzar.over X)]
    [((π.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.obj) (τzar.over X)).IsRightAdjoint)]
    [HasWeakSheafify (τqc.over X) AddCommGrpCat.{u + 1}]
    [Functor.Additive (piInverseAb (τzar.over X) π)] :
    Functor.Additive (aInverseAb hle π) := by
  simpa [aInverseAb] using
    (inferInstance :
      Functor.Additive
        (piInverseAb (τzar.over X) π ⋙ comparisonTopologyPullbackAb hle X))

/-- The abelian inverse-image owner `a_X⁻¹` preserves finite limits. -/
instance aInverseAb_preservesFiniteLimits
    {τzar τqc : GrothendieckTopology LCCat.{u}}
    (hle : τzar ≤ τqc)
    {X : LCCat.{u}}
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) (τzar.over X)]
    [((π.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.obj) (τzar.over X)).IsRightAdjoint)]
    [HasWeakSheafify (τqc.over X) AddCommGrpCat.{u + 1}]
    [HasSheafify (τqc.over X) AddCommGrpCat.{u + 1}]
    [CategoryTheory.Limits.PreservesFiniteLimits (piInverseAb (τzar.over X) π)] :
    CategoryTheory.Limits.PreservesFiniteLimits (aInverseAb hle π) := by
  simpa [aInverseAb] using
    (inferInstance :
      CategoryTheory.Limits.PreservesFiniteLimits
        (piInverseAb (τzar.over X) π ⋙ comparisonTopologyPullbackAb hle X))

/-- The abelian inverse-image owner `a_X⁻¹` preserves finite colimits. -/
instance aInverseAb_preservesFiniteColimits
    {τzar τqc : GrothendieckTopology LCCat.{u}}
    (hle : τzar ≤ τqc)
    {X : LCCat.{u}}
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) (τzar.over X)]
    [((π.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.obj) (τzar.over X)).IsRightAdjoint)]
    [HasWeakSheafify (τqc.over X) AddCommGrpCat.{u + 1}]
    [HasSheafify (τqc.over X) AddCommGrpCat.{u + 1}]
    [CategoryTheory.Limits.PreservesFiniteColimits (piInverseAb (τzar.over X) π)] :
    CategoryTheory.Limits.PreservesFiniteColimits (aInverseAb hle π) := by
  simpa [aInverseAb] using
    (inferInstance :
      CategoryTheory.Limits.PreservesFiniteColimits
        (piInverseAb (τzar.over X) π ⋙ comparisonTopologyPullbackAb hle X))

/- Textbook notation for the abelian direct-image owner `a_{X,*}`. -/
/-- The Chapter 21 direct-image owner `a_{X,*}` on abelian sheaves. -/
abbrev aPushforwardAb
    {τzar τqc : GrothendieckTopology LCCat.{u}}
    (hle : τzar ≤ τqc)
    {X : LCCat.{u}}
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) (τzar.over X)] :
    Sheaf (τqc.over X) AddCommGrpCat.{u + 1} ⥤ SmallAbSheaf X :=
  comparisonTopologyPushforwardAb hle X ⋙ piPushforwardAb (τzar.over X) π

/-- The abelian direct-image owner `a_{X,*}` is additive. -/
instance aPushforwardAb_additive
    {τzar τqc : GrothendieckTopology LCCat.{u}}
    (hle : τzar ≤ τqc)
    {X : LCCat.{u}}
    (π : Opens X.obj ⥤ Over X)
    [Functor.IsContinuous π (Opens.grothendieckTopology X.obj) (τzar.over X)]
    [Functor.Additive (piPushforwardAb (τzar.over X) π)] :
    Functor.Additive (aPushforwardAb hle π) := by
  simpa [aPushforwardAb] using
    (inferInstance :
      Functor.Additive
        (comparisonTopologyPushforwardAb hle X ⋙ piPushforwardAb (τzar.over X) π))

/- Textbook notation for the abelian inverse-image owner `π_X⁻¹`. -/
scoped[CategoryTheory.GrothendieckTopology] notation "π[" J ", " π "]⁻¹" => piInverseAb J π

/- Textbook notation for the abelian inverse-image owner `a_X⁻¹`. -/
scoped[CategoryTheory.GrothendieckTopology] notation "a[" hle ", " π "]⁻¹" =>
  aInverseAb hle π

/- Textbook notation for the abelian direct-image owner `a_{X,*}`. -/
scoped[CategoryTheory.GrothendieckTopology] notation "a[" hle ", " π "]*" =>
  aPushforwardAb hle π

end
