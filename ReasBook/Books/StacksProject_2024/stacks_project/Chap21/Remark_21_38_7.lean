import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import StacksProject_2024.stacks_project.Chap19.AdditiveFunctorTotalRightDerived
import StacksProject_2024.stacks_project.Chap21.SiteAbelianDerived
import StacksProject_2024.stacks_project.Chap21.Situation_21_38_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.FibredCategoryMor

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory
namespace FibredCategoryOver

/- Domain-style sampling for Remark 21.38.7:
- primary domain: canonical comparison morphisms between the derived projection lower shrieks
  attached to `Situation 21.38.3`;
- sampled owner declarations:
  `FibredCategoryMor.inheritedRingedSiteHom`,
  `siteAbelianInverseImageDerived`,
  `Functor.leftAdjoint`,
  `Adjunction.homEquiv`;
- best owner abstraction: the chapter-level canonical owners are
  `siteAbelianInverseImageDerived` and `Functor.leftAdjoint`; the compiled declaration below is the
  corresponding `bridge/view` surface, taking the chosen right adjoint `g^{-1}` and lower-shriek
  functors as explicit inputs and assembling the induced map from those data;
- primitive data: the ringed site `D`, the fibred categories `C`, `C'`, the morphism
  `f : C' ⟶ C`, the sheaf map
  `t : ℱ' ⟶ g⁻¹ℱ`, the chosen identification
  `Lπ'_! ≅ Lg_! ⋙ Lπ_!`, and the degree-zero map
  `Lg_!(ℱ') ⟶ g_!(ℱ')`;
- derived API: the induced canonical map `Lπ'_!(ℱ') ⟶ Lπ_!(ℱ)`.

Source/core/bridge triage:
- `source-facing`: the explicit comparison morphism displayed below for Remark `21.38.7`;
- `core/canonical`: `FibredCategoryMor.inheritedRingedSiteHom`,
  `siteAbelianInverseImageDerived`, `Functor.leftAdjoint`, and `Adjunction.homEquiv`;
- `bridge/view`: the checked composite built from the chosen comparison
  `Lπ'_! ≅ Lg_! ⋙ Lπ_!`, the degree-zero map for `Lg_!`, and the adjoint transpose of `t`.

Because the chosen left-adjoint infrastructure is currently sorry-backed upstream, this file should
not package that composite as a new public `def`; the source-facing surface is therefore a
specification/check of the canonical composite rather than a new owner declaration. -/

section

variable {D : RingedSite.{u, v}}
variable {C C' : FibredCategoryOver.{u, v} D}
variable (f : C' ⟶ C)

private abbrev sourceTopology (D : RingedSite.{u, v}) (C : FibredCategoryOver.{u, v} D) :
    GrothendieckTopology C.S :=
  FibredCategoryOver.inheritedTopology D.siteTopology C

private abbrev baseTopology (D : RingedSite.{u, v}) : GrothendieckTopology D :=
  D.siteTopology

private abbrev SourceAbSheaf (D : RingedSite.{u, v}) (C : FibredCategoryOver.{u, v} D) :=
  Sheaf (sourceTopology D C) AddCommGrpCat.{max u v}

private abbrev BaseAbSheaf (D : RingedSite.{u, v}) :=
  Sheaf (baseTopology D) AddCommGrpCat.{max u v}

variable
  [(toFunctor f).IsContinuous
    (sourceTopology D C')
    (sourceTopology D C)]

private abbrev comparisonInverseImage (f : C' ⟶ C) :
    SourceAbSheaf D C ⥤ SourceAbSheaf D C' :=
  (toFunctor f).sheafPushforwardContinuous
    AddCommGrpCat.{max u v}
    (sourceTopology D C')
    (sourceTopology D C)

variable
  [Functor.IsContinuous C'.p (sourceTopology D C') (baseTopology D)]
  [Functor.IsContinuous C.p (sourceTopology D C) (baseTopology D)]
  [Functor.IsCocontinuous (toFunctor f) (sourceTopology D C') (sourceTopology D C)]
  [Functor.IsCocontinuous C'.p (sourceTopology D C') (baseTopology D)]
  [Functor.IsCocontinuous C.p (sourceTopology D C) (baseTopology D)]
  [HasWeakSheafify (sourceTopology D C') AddCommGrpCat.{max u v}]
  [HasWeakSheafify (sourceTopology D C) AddCommGrpCat.{max u v}]
  [HasWeakSheafify (baseTopology D) AddCommGrpCat.{max u v}]
  [HasSheafify (sourceTopology D C') AddCommGrpCat.{max u v}]
  [HasSheafify (sourceTopology D C) AddCommGrpCat.{max u v}]
  [HasSheafify (baseTopology D) AddCommGrpCat.{max u v}]
  [Functor.Additive (comparisonInverseImage f)]
  [Functor.Additive
    (C'.p.sheafPushforwardContinuous AddCommGrpCat.{max u v}
      (sourceTopology D C') (baseTopology D))]
  [Functor.Additive
    (C.p.sheafPushforwardContinuous AddCommGrpCat.{max u v}
      (sourceTopology D C) (baseTopology D))]
  [IsGrothendieckAbelian.{max u v} (SourceAbSheaf D C)]
  [IsGrothendieckAbelian.{max u v} (BaseAbSheaf D)]
  [Functor.IsRightAdjoint (comparisonInverseImage f)]
  [Functor.IsRightAdjoint
    (siteAbelianInverseImageDerived
      (sourceTopology D C') (sourceTopology D C) (toFunctor f))]
  [Functor.IsRightAdjoint
    (siteAbelianInverseImageDerived
      (sourceTopology D C') (baseTopology D) C'.p)]
  [Functor.IsRightAdjoint
    (siteAbelianInverseImageDerived
      (sourceTopology D C) (baseTopology D) C.p)]

private abbrev sourceSingle0 :
    SourceAbSheaf D C' ⥤ DerivedCategory (SourceAbSheaf D C') :=
  DerivedCategory.singleFunctor (SourceAbSheaf D C') (0 : ℤ)

private abbrev targetSingle0 :
    SourceAbSheaf D C ⥤ DerivedCategory (SourceAbSheaf D C) :=
  DerivedCategory.singleFunctor (SourceAbSheaf D C) (0 : ℤ)

/- Remark 21.38.7: in Situation `21.38.3`, suppose the inverse-image functors for `g`, `π`, and
`π'` on abelian sheaves admit left adjoints, and that one has a chosen identification
`Lπ'_! ≅ Lg_! ⋙ Lπ_!`. For a sheaf morphism `t : ℱ' ⟶ g⁻¹ℱ` and a degree-zero comparison
`Lg_!(ℱ') ⟶ g_!(ℱ')`, the induced comparison morphism
`Lπ'_!(ℱ') ⟶ Lπ_!(ℱ)` is the canonical composite displayed below. This file keeps that source-facing
description as a checked expression, rather than packaging a new public bridge map on top of the
current sorry-backed chosen left-adjoint infrastructure. -/
variable
    (projectionComparison :
      Functor.leftAdjoint
          (siteAbelianInverseImageDerived
            (sourceTopology D C')
            (baseTopology D)
            C'.p) ≅
        Functor.leftAdjoint
            (siteAbelianInverseImageDerived
              (sourceTopology D C')
              (sourceTopology D C)
              (toFunctor f)) ⋙
          Functor.leftAdjoint
            (siteAbelianInverseImageDerived
              (sourceTopology D C)
              (baseTopology D)
              C.p))
    {F : SourceAbSheaf D C}
    {F' : SourceAbSheaf D C'}
    (t : F' ⟶ (comparisonInverseImage f).obj F)
    (degreeZeroComparison :
      (Functor.leftAdjoint
          (siteAbelianInverseImageDerived
            (sourceTopology D C')
            (sourceTopology D C)
            (toFunctor f))).obj
          (sourceSingle0.obj F') ⟶
        targetSingle0.obj ((Functor.leftAdjoint (comparisonInverseImage f)).obj F'))

#check
  ((projectionComparison.app (sourceSingle0.obj F')).hom ≫
      (Functor.leftAdjoint
        (siteAbelianInverseImageDerived
          (sourceTopology D C)
          (baseTopology D)
          C.p)).map
        (degreeZeroComparison ≫
          targetSingle0.map
            (((Adjunction.ofIsRightAdjoint (comparisonInverseImage f)).homEquiv F' F).symm t)) :
    (Functor.leftAdjoint
        (siteAbelianInverseImageDerived
          (sourceTopology D C')
          (baseTopology D)
          C'.p)).obj
        (sourceSingle0.obj F') ⟶
      (Functor.leftAdjoint
          (siteAbelianInverseImageDerived
            (sourceTopology D C)
            (baseTopology D)
            C.p)).obj
          (targetSingle0.obj F))

end

end FibredCategoryOver
end CategoryTheory
