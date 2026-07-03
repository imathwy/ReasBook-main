import Mathlib
import StacksProject_2024.Chap12.Lemma_12_16_2
import StacksProject_2024.Chap13.Definition_13_13_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open ComplexShape
open scoped CategoryTheory

universe u v

namespace CategoryTheory

/- Domain-style sampling for Lemma `13.13.6`.
- primary domain: filtered derived associated-graded functors and the passage from
  `D(Gr(\mathcal A))` to graded objects in `D(\mathcal A)`;
- sampled owner declarations:
  `filteredAssociatedGradedHomotopyFunctor`,
  `filteredDerivedCategory`,
  `Localization.lift`,
  `Functor.mapDerivedCategory`,
  `GradedObject.eval`;
- best owner abstraction: the descended associated-graded functor
  `DF(\mathcal A) ⥤ D(Gr(\mathcal A))` together with its direct descended graded-piece functors
  `gr^p : DF(\mathcal A) ⥤ D(\mathcal A)`, each defined as the localization lift of the
  homotopy-level `gr^p`; the bundled bridge `DF(\mathcal A) ⥤ Gr(D(\mathcal A))` is only a
  companion view obtained from `D(Gr(\mathcal A)) ⥤ Gr(D(\mathcal A))`;
- primitive data: the homotopy-level associated-graded owner
  `filteredAssociatedGradedHomotopyFunctor 𝒜`, the homotopy-level graded-piece functors, the
  canonical quotient functor `((FAc(𝒜) : ObjectProperty KFilt).trW.Q : KFilt ⥤ DFilt)`, and the
  localization lifts of
  these source-facing functors;
- derived API: the bridge functor to `Gr(D(\mathcal A))`, the comparison isomorphism between its
  degree-`p` evaluation and the direct descended `gr^p`, and the exactness data for the
  source-facing lifts;
- source/core/bridge triage:
  `source-facing`: the descended associated-graded functor on `DF(\mathcal A)` and the direct
    descended `p`-th graded-piece functors;
  `core/canonical`: `filteredDerivedCategory`,
    `((FAc(𝒜) : ObjectProperty KFilt).trW.Q : KFilt ⥤ DFilt)`,
    `Localization.lift`, `Functor.mapDerivedCategory`, and `GradedObject.eval`;
  `bridge/view`: the comparison functor `D(Gr(\mathcal A)) ⥤ Gr(D(\mathcal A))` and the bundled
    graded-object-valued packaging of the direct `gr^p`.

This file therefore keeps the localization lift to `D(Gr(\mathcal A))` as the source-facing
descended `gr`, defines the descended `gr^p` directly by localization, and treats
`DF(\mathcal A) ⥤ Gr(D(\mathcal A))` only as a companion bridge/view. -/

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)]
variable [HasBinaryBiproducts (finiteFilteredObjectCat 𝒜)]

local notation "FilF" => finiteFilteredObjectCat 𝒜
local notation "KFilt" => HomotopyCategory FilF (up ℤ)
local notation "DFilt" => filteredDerivedCategory 𝒜
local notation "DGr" => DerivedCategory (GradedObject ℤ 𝒜)

private abbrev QFilt : KFilt ⥤ DFilt :=
  (((FAc(𝒜) : ObjectProperty KFilt).trW).Q : KFilt ⥤ DFilt)

instance qFilt_isLocalization :
    Functor.IsLocalization QFilt (FQis(𝒜) : MorphismProperty KFilt) := by
  rw [← filteredAcyclic_trW_eq_filteredQuasiIso]
  simpa [QFilt] using
    (Functor.q_isLocalization ((FAc(𝒜) : ObjectProperty KFilt).trW) :
      Functor.IsLocalization
        (((FAc(𝒜) : ObjectProperty KFilt).trW.Q : KFilt ⥤ DFilt))
        ((FAc(𝒜) : ObjectProperty KFilt).trW))

private noncomputable instance filteredDerived_shift_additive
    [IsTriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))] (n : ℤ) :
    (shiftFunctor DFilt n).Additive := by
  infer_instance

section AssociatedGraded

variable [HasDerivedCategory (GradedObject ℤ 𝒜)]

/-- The associated graded functor from `K(Fil^f(\mathcal A))` to `D(Gr(\mathcal A))`. -/
abbrev filteredAssociatedGradedHomotopyToDerivedFunctor :
    KFilt ⥤ DGr :=
  filteredAssociatedGradedHomotopyFunctor 𝒜 ⋙
    (DerivedCategory.Qh : HomotopyCategory (GradedObject ℤ 𝒜) (up ℤ) ⥤ DGr)

section DerivedGradedObject

variable [HasDerivedCategory 𝒜]

private noncomputable abbrev gradedObjectEvalMapDerivedCategory (p : ℤ) :
    DGr ⥤ DerivedCategory 𝒜 :=
  (GradedObject.eval p : GradedObject ℤ 𝒜 ⥤ 𝒜).mapDerivedCategory

/-- The bridge/view functor `D(Gr(\mathcal A)) ⥤ Gr(D(\mathcal A))` obtained by derived
evaluation in each degree. -/
abbrev gradedDerivedObjectFunctor :
    DGr ⥤ GradedObject ℤ (DerivedCategory 𝒜) where
  obj K := fun p ↦ (gradedObjectEvalMapDerivedCategory p).obj K
  map f := fun p ↦ (gradedObjectEvalMapDerivedCategory p).map f
  map_id X := by
    ext p
    simp
  map_comp f g := by
    ext p
    simp

section DerivedPiece

/-- The `p`-th graded piece functor from `K(Fil^f(\mathcal A))` to `D(\mathcal A)`. -/
abbrev filteredGradedPieceHomotopyToDerivedFunctor (p : ℤ) :
    KFilt ⥤ DerivedCategory 𝒜 :=
  filteredAssociatedGradedHomotopyFunctor 𝒜 ⋙
    (GradedObject.eval p).mapHomotopyCategory (up ℤ) ⋙
      (DerivedCategory.Qh : HomotopyCategory 𝒜 (up ℤ) ⥤ DerivedCategory 𝒜)

/-- Bridge/view comparison on the homotopy side: evaluating after passage to
`D(Gr(\mathcal A))` agrees with first taking the `p`-th graded piece and then localizing. -/
noncomputable abbrev filteredGradedPieceHomotopyToDerivedFunctorCompIso (p : ℤ) :
    filteredAssociatedGradedHomotopyToDerivedFunctor ⋙
        gradedObjectEvalMapDerivedCategory p ≅
      filteredAssociatedGradedHomotopyFunctor 𝒜 ⋙
        (GradedObject.eval p).mapHomotopyCategory (up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory 𝒜 (up ℤ) ⥤ DerivedCategory 𝒜) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (filteredAssociatedGradedHomotopyFunctor 𝒜)
      ((GradedObject.eval p : GradedObject ℤ 𝒜 ⥤ 𝒜).mapDerivedCategoryFactorsh) ≪≫
    (Functor.associator _ _ _).symm

end DerivedPiece

end DerivedGradedObject

end AssociatedGraded

section Forget

variable [HasDerivedCategory 𝒜]

/-- The forgetful functor from `K(Fil^f(\mathcal A))` to `D(\mathcal A)`. -/
abbrev filteredForgetHomotopyToDerivedFunctor :
    KFilt ⥤ DerivedCategory 𝒜 :=
  ((finiteFilteredObjectForgetFunctor 𝒜 : FilF ⥤ 𝒜).mapHomotopyCategory (up ℤ)) ⋙
    DerivedCategory.Qh

end Forget

section AssociatedGraded

variable [HasDerivedCategory (GradedObject ℤ 𝒜)]
variable [Pretriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

-- Proof sketch: a filtered quasi-isomorphism is, by definition, a quasi-isomorphism after
-- applying the associated graded functor, and `DerivedCategory.Qh` inverts quasi-isomorphisms.
/-- The associated graded functor to the derived category inverts filtered quasi-isomorphisms. -/
theorem filteredAssociatedGradedHomotopyToDerivedFunctor_inverts_filteredQuasiIsomorphisms :
    (FQis(𝒜) : MorphismProperty KFilt).IsInvertedBy
      (filteredAssociatedGradedHomotopyToDerivedFunctor : KFilt ⥤ DGr) := sorry

end AssociatedGraded

section GradedPiece

variable [HasDerivedCategory 𝒜]
variable [HasDerivedCategory (GradedObject ℤ 𝒜)]
variable [Pretriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

-- Proof sketch: a filtered quasi-isomorphism becomes a quasi-isomorphism after taking associated
-- graded objects, evaluation at `p` preserves quasi-isomorphisms degreewise, and `Qh` localizes
-- at quasi-isomorphisms.
/-- The `p`-th graded piece functor to the derived category inverts filtered quasi-isomorphisms. -/
theorem filteredGradedPieceHomotopyToDerivedFunctor_inverts_filteredQuasiIsomorphisms (p : ℤ) :
    (FQis(𝒜) : MorphismProperty KFilt).IsInvertedBy
      (filteredGradedPieceHomotopyToDerivedFunctor p : KFilt ⥤ DerivedCategory 𝒜) := sorry

/-- Lemma 13.13.6: the `p`-th graded-piece functor on `K(Fil^f(\mathcal A))` descends directly
to the canonical exact functor `DF(\mathcal A) ⥤ D(\mathcal A)` induced by `gr^p`. -/
abbrev filteredDerivedGradedPieceFunctor (p : ℤ) :
    DFilt ⥤ DerivedCategory 𝒜 :=
  Localization.lift
    (filteredGradedPieceHomotopyToDerivedFunctor p)
    (filteredGradedPieceHomotopyToDerivedFunctor_inverts_filteredQuasiIsomorphisms p)
    QFilt

/-- Textbook surface notation for the descended graded-piece functor `DF(\mathcal A) ⥤
D(\mathcal A)`. -/
scoped notation:max "gr^{" p "}" => filteredDerivedGradedPieceFunctor p

/-- The descended `p`-th graded piece functor commutes with shifts. -/
noncomputable instance filteredDerivedGradedPieceFunctor_commShift (p : ℤ) :
    (gr^{p} : DFilt ⥤ DerivedCategory 𝒜).CommShift ℤ := sorry

section Exact

variable [IsTriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

-- Proof sketch: the source-facing `gr^p` on `DF(\mathcal A)` is itself a localization lift of the
-- homotopy-level `gr^p`, so Lemma 13.5.7 applies directly. The bridge
-- `DF(\mathcal A) ⥤ Gr(D(\mathcal A))` is only a companion comparison.
/-- The descended `p`-th graded piece functor is exact. -/
instance filteredDerivedGradedPieceFunctor_isTriangulated (p : ℤ) :
    (gr^{p} : DFilt ⥤ DerivedCategory 𝒜).IsTriangulated := sorry

end Exact

end GradedPiece

section Forget

variable [HasDerivedCategory 𝒜]
variable [Pretriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

-- Proof sketch: if a morphism is a filtered quasi-isomorphism, then its cone is filtered acyclic.
-- Lemma 13.13.4 identifies this with the filtered acyclic subcategory, and the forgetful functor
-- sends filtered acyclic complexes to acyclic complexes, so `DerivedCategory.Qh` inverts it.
/-- The forgetful functor to the derived category inverts filtered quasi-isomorphisms. -/
theorem filteredForgetHomotopyToDerivedFunctor_inverts_filteredQuasiIsomorphisms :
    (FQis(𝒜) : MorphismProperty KFilt).IsInvertedBy
      (filteredForgetHomotopyToDerivedFunctor : KFilt ⥤ DerivedCategory 𝒜) := sorry

end Forget

section AssociatedGraded

variable [HasDerivedCategory (GradedObject ℤ 𝒜)]
variable [Pretriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

/-- Lemma 13.13.6: the associated graded functor on `K(Fil^f(\mathcal A))` descends to a
canonical exact functor `DF(\mathcal A) ⥤ D(Gr(\mathcal A))` commuting with the localization
functor. -/
abbrev filteredDerivedAssociatedGradedFunctor :
    DFilt ⥤ DGr :=
  Localization.lift
    filteredAssociatedGradedHomotopyToDerivedFunctor
    filteredAssociatedGradedHomotopyToDerivedFunctor_inverts_filteredQuasiIsomorphisms
    QFilt

/-- Textbook surface notation for the descended associated-graded functor
`DF(\mathcal A) ⥤ D(Gr(\mathcal A))`. -/
scoped notation "gr" => filteredDerivedAssociatedGradedFunctor

/-- The descended associated graded functor commutes with shifts. -/
noncomputable instance filteredDerivedAssociatedGradedFunctor_commShift :
    (gr : DFilt ⥤ DGr).CommShift ℤ :=
  by
    sorry

section Exact

variable [IsTriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

-- Proof sketch: the functor on the homotopy category obtained from the associated graded functor
-- is exact, and Lemma 13.5.7 upgrades exactness to the localization lift.
/-- The descended associated graded functor is exact. -/
theorem filteredDerivedAssociatedGradedFunctor_isTriangulated :
    (gr : DFilt ⥤ DGr).IsTriangulated := sorry

/-- The canonical exactness instance for the descended associated graded functor. -/
instance :
    (gr : DFilt ⥤ DGr).IsTriangulated :=
  filteredDerivedAssociatedGradedFunctor_isTriangulated

end Exact

end AssociatedGraded

section GradedDerivedObject

variable [HasDerivedCategory 𝒜]
variable [HasDerivedCategory (GradedObject ℤ 𝒜)]
variable [Pretriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

/-- Companion bridge/view for Lemma 13.13.6: package the descended associated graded functor as a
graded object in `D(\mathcal A)`. Its degree-`p` evaluation is compared to the source-facing
functor `gr^{p}` by `filteredDerivedGradedFunctorEvalIso`. -/
abbrev filteredDerivedGradedFunctor :
    DFilt ⥤ GradedObject ℤ (DerivedCategory 𝒜) :=
  gr ⋙ gradedDerivedObjectFunctor

section GradedPiece

/-- Evaluating the graded-object bridge in degree `p` recovers the source-facing descended
graded-piece functor `gr^p`. -/
noncomputable abbrev filteredDerivedGradedFunctorEvalIso (p : ℤ) :
    filteredDerivedGradedFunctor ⋙
        (GradedObject.eval p : GradedObject ℤ (DerivedCategory 𝒜) ⥤ DerivedCategory 𝒜) ≅
      gr^{p} :=
  by
    simpa [filteredDerivedGradedFunctor, gradedDerivedObjectFunctor] using
      (Localization.liftNatIso
        QFilt
        (FQis(𝒜) : MorphismProperty KFilt)
        (filteredAssociatedGradedHomotopyToDerivedFunctor ⋙
          gradedObjectEvalMapDerivedCategory p)
        (filteredGradedPieceHomotopyToDerivedFunctor p)
        (gr ⋙ gradedObjectEvalMapDerivedCategory p)
        (gr^{p})
        (filteredGradedPieceHomotopyToDerivedFunctorCompIso p))

end GradedPiece

end GradedDerivedObject

section Forget

variable [HasDerivedCategory 𝒜]
variable [Pretriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

/-- The forgetful functor on `DF(\mathcal A)`. -/
abbrev filteredDerivedForgetFunctor :
    DFilt ⥤ DerivedCategory 𝒜 :=
  Localization.lift
    filteredForgetHomotopyToDerivedFunctor
    filteredForgetHomotopyToDerivedFunctor_inverts_filteredQuasiIsomorphisms
    QFilt

/-- The descended forgetful functor commutes with shifts. -/
noncomputable instance filteredDerivedForgetFunctor_commShift :
    (filteredDerivedForgetFunctor : DFilt ⥤ DerivedCategory 𝒜).CommShift ℤ :=
  by
    sorry

section Exact

variable [IsTriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

-- Proof sketch: the forgetful functor on filtered complexes is exact on the homotopy category,
-- and once it is known to invert filtered quasi-isomorphisms, Lemma 13.5.7 gives exactness of
-- the descended localization lift.
/-- The descended forgetful functor is exact. -/
instance filteredDerivedForgetFunctor_isTriangulated :
    (filteredDerivedForgetFunctor : DFilt ⥤ DerivedCategory 𝒜).IsTriangulated := sorry

end Exact

end Forget

end CategoryTheory
