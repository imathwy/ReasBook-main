import Mathlib.Geometry.RingedSpace.OpenImmersion
import Mathlib.AlgebraicGeometry.Sites.Representability
import Mathlib.CategoryTheory.Subfunctor.Basic
import Mathlib.Topology.Sets.OpenCover
import StacksProject_2024.stacks_project.Chap26.Lemma_26_15_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u v

namespace CategoryTheory

-- Semantic recall: `lean_leansearch` surfaced the locally-ringed-space open-immersion owner
-- `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`, and Chapter 26 already uses
-- `AlgebraicGeometry.LocallyRingedSpace.GlueData` and `Scheme.GlueData.glued` as the canonical
-- gluing owners. This remark is therefore formalized as the locally-ringed-space analogue of the
-- local representability criterion, with an explicit Yoneda representation by a scheme.

/-
This remark keeps the stronger source-facing locally-ringed-space hypotheses as explicit local
predicates. The reusable canonical owners for the corresponding local-representability machinery
remain the Chapter 26 scheme-side declarations `Presheaf.IsSheaf Scheme.zariskiTopology`,
`Subfunctor.isRepresentableByOpenImmersions`, and `Subfunctor.covers`, together with
`isRepresentable_of_zariskiSheaf_of_openImmersionSubfunctorCover`, accessed below through the
bridge views `Functor.onSchemes`, `Subfunctor.onSchemes`, and their companion theorems.
-/

namespace Functor

/-- A contravariant set-valued functor on locally ringed spaces is represented by a scheme if it is
isomorphic to the Yoneda functor of some scheme viewed as a locally ringed space. -/
def IsRepresentableByScheme (F : LocallyRingedSpaceᵒᵖ ⥤ Type u) : Prop :=
  ∃ X : Scheme, Nonempty (yoneda.obj X.toLocallyRingedSpace ≅ F)

/-- The canonical inclusion of the overlap `U ∩ V` into `U`, viewed on restricted locally ringed
spaces. -/
private theorem overlapToLeft_condition {X : LocallyRingedSpace} (U V : Opens X) :
    Set.range (X.ofRestrict (U ⊓ V).isOpenEmbedding).base ⊆
      Set.range (X.ofRestrict U.isOpenEmbedding).base := by
  intro x
  rintro ⟨y, rfl⟩
  exact ⟨⟨y.1, y.2.1⟩, rfl⟩

/-- The canonical inclusion of the overlap `U ∩ V` into `V`, viewed on restricted locally ringed
spaces. -/
private theorem overlapToRight_condition {X : LocallyRingedSpace} (U V : Opens X) :
    Set.range (X.ofRestrict (U ⊓ V).isOpenEmbedding).base ⊆
      Set.range (X.ofRestrict V.isOpenEmbedding).base := by
  intro x
  rintro ⟨y, rfl⟩
  exact ⟨⟨y.1, y.2.2⟩, rfl⟩

/-- The canonical morphism from the overlap `U ∩ V` to the open subspace `U`. -/
def overlapToLeft {X : LocallyRingedSpace} (U V : Opens X) :
    X.restrict (U ⊓ V).isOpenEmbedding ⟶ X.restrict U.isOpenEmbedding :=
  LocallyRingedSpace.IsOpenImmersion.lift
    (X.ofRestrict U.isOpenEmbedding)
    (X.ofRestrict (U ⊓ V).isOpenEmbedding)
    (overlapToLeft_condition U V)

/-- The canonical morphism from the overlap `U ∩ V` to the open subspace `V`. -/
def overlapToRight {X : LocallyRingedSpace} (U V : Opens X) :
    X.restrict (U ⊓ V).isOpenEmbedding ⟶ X.restrict V.isOpenEmbedding :=
  LocallyRingedSpace.IsOpenImmersion.lift
    (X.ofRestrict V.isOpenEmbedding)
    (X.ofRestrict (U ⊓ V).isOpenEmbedding)
    (overlapToRight_condition U V)

/-- A family of sections on an open cover of a locally ringed space is compatible if its pullbacks
to pairwise overlaps agree. The overlap is expressed canonically by the restricted locally ringed
space on `U j ∩ U k`. -/
def openCoverCompatible
    (F : LocallyRingedSpaceᵒᵖ ⥤ Type u)
    {J : Type v} {X : LocallyRingedSpace}
    (U : J → Opens X)
    (s : ∀ j : J, F.obj (op (X.restrict (U j).isOpenEmbedding))) : Prop :=
  ∀ j k,
    F.map
        (overlapToLeft (U j) (U k)).op
        (s j) =
      F.map
        (overlapToRight (U j) (U k)).op
        (s k)

/-- The source-facing open-cover gluing condition for a contravariant set-valued functor on
locally ringed spaces. -/
def openCoverGluingOnLocallyRingedSpaces (F : LocallyRingedSpaceᵒᵖ ⥤ Type u) : Prop :=
  ∀ {J : Type v} ⦃X : LocallyRingedSpace⦄ (U : J → Opens X) (_ : IsOpenCover U)
    (s : ∀ j : J, F.obj (op (X.restrict (U j).isOpenEmbedding))),
      F.openCoverCompatible U s →
      ∃! t : F.obj (op X),
        ∀ j : J, F.map (X.ofRestrict (U j).isOpenEmbedding).op t = s j

/-- Restrict a contravariant set-valued functor on locally ringed spaces to schemes via the
canonical forgetful functor `Scheme ⥤ LocallyRingedSpace`. -/
def onSchemes (F : LocallyRingedSpaceᵒᵖ ⥤ Type u) : Schemeᵒᵖ ⥤ Type u :=
  Scheme.forgetToLocallyRingedSpace.op ⋙ F

/-- The object part of `F.onSchemes` is the object part of `F` after viewing a scheme as a locally
ringed space. -/
@[simp]
theorem onSchemes_obj (F : LocallyRingedSpaceᵒᵖ ⥤ Type u) (X : Schemeᵒᵖ) :
    F.onSchemes.obj X = F.obj ((Scheme.forgetToLocallyRingedSpace.op).obj X) := rfl

/-- The action of `F.onSchemes` on morphisms is the action of `F` after precomposition with
`Scheme.forgetToLocallyRingedSpace.op`. -/
@[simp]
theorem onSchemes_map (F : LocallyRingedSpaceᵒᵖ ⥤ Type u) {X Y : Schemeᵒᵖ} (f : X ⟶ Y) :
    F.onSchemes.map f = F.map ((Scheme.forgetToLocallyRingedSpace.op).map f) := rfl

/-- If a locally ringed-space functor is represented by a scheme, then its restriction to schemes
is representable by the same scheme. This is the canonical bridge from the source-facing
scheme-valued representation hypothesis to the Chapter 26 scheme-side owner
`Functor.IsRepresentable`. -/
theorem onSchemes_isRepresentable_of_isRepresentableByScheme
    {F : LocallyRingedSpaceᵒᵖ ⥤ Type u}
    (hF : F.IsRepresentableByScheme) :
    F.onSchemes.IsRepresentable := sorry

end Functor

namespace Subfunctor

/-- A subfunctor of a locally ringed-space functor is represented by a scheme if its associated
set-valued functor is represented by a scheme. -/
def IsRepresentableByScheme {F : LocallyRingedSpaceᵒᵖ ⥤ Type u} (H : Subfunctor F) : Prop :=
  H.toFunctor.IsRepresentableByScheme

/-- The source-facing open-immersion criterion for a subfunctor of a contravariant set-valued
functor on locally ringed spaces. -/
def isRepresentableByOpenImmersionsOnLocallyRingedSpaces
    {F : LocallyRingedSpaceᵒᵖ ⥤ Type u} (H : Subfunctor F) : Prop :=
  ∀ ⦃X : LocallyRingedSpace⦄ (ξ : F.obj (op X)),
    ∃ U : Opens X,
      ∀ ⦃Y : LocallyRingedSpace⦄ (f : Y ⟶ X),
        (∃ lift : Y ⟶ X.restrict U.isOpenEmbedding,
          lift ≫ X.ofRestrict U.isOpenEmbedding = f) ↔
        F.map f.op ξ ∈ H.obj (op Y)

/-- The source-facing covering condition for a family of subfunctors on locally ringed spaces. -/
def coversOnLocallyRingedSpaces
    {F : LocallyRingedSpaceᵒᵖ ⥤ Type u} {I : Type v} (H : I → Subfunctor F) : Prop :=
  ∀ ⦃X : LocallyRingedSpace⦄ (ξ : F.obj (op X)),
    ∃ U : I → Opens X, IsOpenCover U ∧
      ∀ i : I,
        F.map (X.ofRestrict (U i).isOpenEmbedding).op ξ ∈
          (H i).obj (op (X.restrict (U i).isOpenEmbedding))

/-- Restrict a subfunctor on locally ringed spaces to schemes. This thin bridge/view is obtained
by precomposing with `Scheme.forgetToLocallyRingedSpace.op`. -/
def onSchemes {F : LocallyRingedSpaceᵒᵖ ⥤ Type u} (H : Subfunctor F) :
    Subfunctor F.onSchemes where
  obj X := H.obj ((Scheme.forgetToLocallyRingedSpace.op).obj X)
  map f := H.map ((Scheme.forgetToLocallyRingedSpace.op).map f)

/-- The object part of `H.onSchemes` is the object part of `H` after viewing a scheme as a locally
ringed space. -/
@[simp]
theorem onSchemes_obj {F : LocallyRingedSpaceᵒᵖ ⥤ Type u} (H : Subfunctor F) (X : Schemeᵒᵖ) :
    H.onSchemes.obj X = H.obj ((Scheme.forgetToLocallyRingedSpace.op).obj X) := rfl

/-- The action of `H.onSchemes` on morphisms is the action of `H` after precomposition with
`Scheme.forgetToLocallyRingedSpace.op`. -/
@[simp]
theorem onSchemes_map {F : LocallyRingedSpaceᵒᵖ ⥤ Type u} (H : Subfunctor F)
    {X Y : Schemeᵒᵖ} (f : X ⟶ Y) :
    H.onSchemes.map f = H.map ((Scheme.forgetToLocallyRingedSpace.op).map f) := rfl

/-- Membership in the restricted subfunctor `H.onSchemes` is exactly membership in `H` after
viewing a scheme as a locally ringed space. -/
@[simp]
theorem mem_onSchemes_obj {F : LocallyRingedSpaceᵒᵖ ⥤ Type u} (H : Subfunctor F)
    {X : Schemeᵒᵖ} {x : F.onSchemes.obj X} :
    x ∈ H.onSchemes.obj X ↔ x ∈ H.obj ((Scheme.forgetToLocallyRingedSpace.op).obj X) := Iff.rfl

/-- A locally ringed-space subfunctor represented by a scheme restricts to a representable
scheme-side subfunctor. This is the source-facing companion bridge from the Remark 26.15.5
hypothesis `H.IsRepresentableByScheme` to the canonical input expected by
`Lemma_26_15_4.isRepresentable_of_zariskiSheaf_of_openImmersionSubfunctorCover`. -/
theorem onSchemes_isRepresentable_of_isRepresentableByScheme
    {F : LocallyRingedSpaceᵒᵖ ⥤ Type u} (H : Subfunctor F) (hH : H.IsRepresentableByScheme) :
    H.onSchemes.toFunctor.IsRepresentable := sorry

end Subfunctor

/-- The source-facing open-cover gluing hypothesis on locally ringed spaces restricts to the
canonical Zariski-sheaf owner on schemes. -/
theorem Functor.onSchemes_isSheaf_of_openCoverGluingOnLocallyRingedSpaces
    (F : LocallyRingedSpaceᵒᵖ ⥤ Type u)
    (hFsheaf : F.openCoverGluingOnLocallyRingedSpaces) :
    Presheaf.IsSheaf Scheme.zariskiTopology F.onSchemes := sorry

/-- The locally-ringed-space open-immersion criterion restricts to the canonical Chapter 26
predicate `Subfunctor.isRepresentableByOpenImmersions` on schemes. -/
theorem Subfunctor.onSchemes_isRepresentableByOpenImmersions_of_locallyRingedSpaces
    {F : LocallyRingedSpaceᵒᵖ ⥤ Type u} (H : Subfunctor F)
    (hHopen : H.isRepresentableByOpenImmersionsOnLocallyRingedSpaces) :
    H.onSchemes.isRepresentableByOpenImmersions := sorry

/-- The locally-ringed-space covering condition restricts to the canonical Chapter 26 predicate
`Subfunctor.covers` on schemes. -/
theorem Subfunctor.onSchemes_covers_of_locallyRingedSpaces
    {F : LocallyRingedSpaceᵒᵖ ⥤ Type u} {I : Type v} (H : I → Subfunctor F)
    (hHcover : Subfunctor.coversOnLocallyRingedSpaces H) :
    Subfunctor.covers (fun i : I ↦ (H i).onSchemes) := sorry

/-- Remark 26.15.5: if a set-valued contravariant functor on locally ringed spaces satisfies the
sheaf property and admits a covering family of subfunctors represented by schemes whose inclusions
are representable by open immersions on locally ringed spaces, then the functor is represented by
a scheme viewed as a locally ringed space. -/
@[stacks 01JK]
theorem isRepresentableByScheme_of_openCoverGluing_of_openImmersionSubfunctorCover
    (F : LocallyRingedSpaceᵒᵖ ⥤ Type u)
    {I : Type v} (H : I → Subfunctor F)
    (hFsheaf : F.openCoverGluingOnLocallyRingedSpaces)
    (hHrep : ∀ i, (H i).IsRepresentableByScheme)
    (hHopen : ∀ i, (H i).isRepresentableByOpenImmersionsOnLocallyRingedSpaces)
    (hHcover : Subfunctor.coversOnLocallyRingedSpaces H) :
    F.IsRepresentableByScheme := sorry

/-- The scheme-valued representability conclusion in Remark 26.15.5 yields the canonical
`Functor.IsRepresentable` owner for the underlying locally ringed-space functor. -/
theorem isRepresentable_of_isRepresentableByScheme
    (F : LocallyRingedSpaceᵒᵖ ⥤ Type u)
    (hF : F.IsRepresentableByScheme) :
    F.IsRepresentable := sorry

/-- Under the locally ringed space hypotheses above, the functor is representable in the category
of locally ringed spaces. -/
theorem isRepresentable_of_openCoverGluing_of_openImmersionSubfunctorCover
    (F : LocallyRingedSpaceᵒᵖ ⥤ Type u)
    {I : Type v} (H : I → Subfunctor F)
    (hFsheaf : F.openCoverGluingOnLocallyRingedSpaces)
    (hHrep : ∀ i, (H i).IsRepresentableByScheme)
    (hHopen : ∀ i, (H i).isRepresentableByOpenImmersionsOnLocallyRingedSpaces)
    (hHcover : Subfunctor.coversOnLocallyRingedSpaces H) :
    F.IsRepresentable := sorry

end CategoryTheory
