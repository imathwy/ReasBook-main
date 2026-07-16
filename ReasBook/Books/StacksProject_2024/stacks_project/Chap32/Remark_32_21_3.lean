import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.stacks_project.Chap29.Definition_29_21_1
import StacksProject_2024.stacks_project.Chap31.Lemma_31_13_3

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.ObjectProperty
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall note: the owner/API choice below is `source-facing`: keep the Chapter 32
-- category of finitely presented morphisms that are isomorphisms over a chosen open, but express
-- the open-side clause directly through the canonical restriction morphism `f ∣_ U` rather than
-- a chapter-local wrapper. The finite-presentation clause reuses the Chapter 29 owner
-- `Scheme.Hom.FinitePresentation`, and the restricted-category surface uses
-- `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`.

namespace Scheme.Hom

/-- A morphism of schemes is of finite presentation and an isomorphism over the open
`U ⊆ S`. The finite-presentation clause is expressed by the canonical scheme owner
`Scheme.Hom.FinitePresentation`, while the open-complement clause is encoded by the canonical
restriction morphism `f ∣_ U : (f ⁻¹ᵁ U).toScheme ⟶ U.toScheme`. -/
abbrev IsFinitePresentationIsoOverOpen
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) : Prop :=
  FinitePresentation f ∧ IsIso (f ∣_ U)

/-- Unfold the source-facing owner into finite presentation together with the restricted
isomorphism condition over `U`. -/
theorem isFinitePresentationIsoOverOpen_iff
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) :
    f.IsFinitePresentationIsoOverOpen U ↔
      FinitePresentation f ∧ IsIso (f ∣_ U) :=
  Iff.rfl

end Scheme.Hom

/-- The full subcategory of `Over S` cut out by morphisms that are of finite presentation and are
isomorphisms over the chosen open subset `U ⊆ S`. -/
abbrev finitePresentationIsoOverOpenProperty
    {S : Scheme.{u}} (U : S.Opens) : ObjectProperty (Over S) :=
  fun X ↦ X.hom.IsFinitePresentationIsoOverOpen U

/-- Membership in the restricted over-category is exactly finite presentation together with being
an isomorphism over `U`. -/
theorem finitePresentationIsoOverOpenProperty_iff
    {S : Scheme.{u}} (U : S.Opens) (X : Over S) :
    finitePresentationIsoOverOpenProperty U X ↔
      Scheme.Hom.FinitePresentation X.hom ∧ IsIso (X.hom ∣_ U) :=
  Scheme.Hom.isFinitePresentationIsoOverOpen_iff X.hom U

/-- The category of finitely presented `S`-schemes that are isomorphisms over `U ⊆ S`. -/
abbrev FinitePresentationIsoOverOpen
    {S : Scheme.{u}} (U : S.Opens) : Type (u + 1) :=
  (finitePresentationIsoOverOpenProperty U).FullSubcategory

namespace FinitePresentationIsoOverOpen

/-- The inclusion into the over-category `Over S`. -/
abbrev inclusion
    {S : Scheme.{u}} (U : S.Opens) : FinitePresentationIsoOverOpen U ⥤ Over S :=
  (finitePresentationIsoOverOpenProperty U).ι

/-- The structural morphism of an object of `FinitePresentationIsoOverOpen U` satisfies the
source-facing owner `IsFinitePresentationIsoOverOpen`. -/
theorem hom_isFinitePresentationIsoOverOpen
    {S : Scheme.{u}} (U : S.Opens) (X : FinitePresentationIsoOverOpen U) :
    X.obj.hom.IsFinitePresentationIsoOverOpen U :=
  X.property

/-- The structural morphism of an object of `FinitePresentationIsoOverOpen U` is of finite
presentation. -/
theorem finitePresentation_hom
    {S : Scheme.{u}} (U : S.Opens) (X : FinitePresentationIsoOverOpen U) :
    Scheme.Hom.FinitePresentation X.obj.hom :=
  (Scheme.Hom.isFinitePresentationIsoOverOpen_iff X.obj.hom U).1
    (hom_isFinitePresentationIsoOverOpen U X) |>.1

/-- The structural morphism of an object of `FinitePresentationIsoOverOpen U` is an isomorphism
after restriction to `U`. -/
theorem isIso_restrict_hom
    {S : Scheme.{u}} (U : S.Opens) (X : FinitePresentationIsoOverOpen U) :
    IsIso (X.obj.hom ∣_ U) :=
  (Scheme.Hom.isFinitePresentationIsoOverOpen_iff X.obj.hom U).1
    (hom_isFinitePresentationIsoOverOpen U X) |>.2

/-- Pullback along `s : W ⟶ S` preserves the finite-presentation / isomorphism-over-open owner
once `s` is affine and an isomorphism over `U`. -/
theorem isFinitePresentationIsoOverOpen_pullback
    {S W : Scheme.{u}} (s : W ⟶ S) [IsAffineHom s]
    (U : S.Opens)
    (hs : IsIso (s ∣_ U))
    (X : Over S)
    (hX : finitePresentationIsoOverOpenProperty U X) :
    finitePresentationIsoOverOpenProperty (s ⁻¹ᵁ U) ((Over.pullback s).obj X) := sorry

/-- The base-change functor on `Over` restricted to morphisms that are of finite presentation and
are isomorphisms over the chosen open subset `U ⊆ S`. -/
noncomputable def pullback
    {S W : Scheme.{u}} (s : W ⟶ S) [IsAffineHom s]
    (U : S.Opens)
    (hs : IsIso (s ∣_ U)) :
    FinitePresentationIsoOverOpen U ⥤ FinitePresentationIsoOverOpen (s ⁻¹ᵁ U) :=
  let _ : IsIso (s ∣_ U) := hs
  ObjectProperty.lift
    (finitePresentationIsoOverOpenProperty (s ⁻¹ᵁ U))
    ((inclusion U) ⋙ Over.pullback s)
    (fun X ↦ isFinitePresentationIsoOverOpen_pullback s U hs X.obj X.property)

end FinitePresentationIsoOverOpen

/-- Remark 32.21.3: let `S` be a scheme, let `T` be a closed subscheme of `S`, and let
`s : W ⟶ S` be the affine comparison morphism arising from the limit of a cofinal affine system of
open neighborhoods of `T`. Writing `U = S \setminus T`, so that `W` is identified with `S` over
`U`, pullback along `s` induces an equivalence between the category of finitely presented
`S`-schemes that are isomorphisms over `U` and the analogous category over `W`. The target open is
formalized as the pullback `s ⁻¹ᵁ U`. -/
theorem finitePresentationIsoOverOpenPullbackFunctor_isEquivalence
    {S W : Scheme.{u}} (s : W ⟶ S) [IsAffineHom s]
    (U : S.Opens)
    (hs : IsIso (s ∣_ U)) :
    (FinitePresentationIsoOverOpen.pullback s U hs).IsEquivalence := sorry

/-- Remark 32.21.3 in the source-facing closed-subscheme form: if `T ⟶ S` is a closed
subscheme, then for the open complement of its image in `S`, the restricted pullback functor
along the affine comparison map `s : W ⟶ S` is an equivalence. The open complement is the
canonical owner `closedImmersionComplement i`. -/
theorem finitePresentationIsoOverOpenPullback_isEquivalence
    {S W T : Scheme.{u}} (i : T ⟶ S) [IsClosedImmersion i]
    (s : W ⟶ S) [IsAffineHom s]
    (hs : IsIso (s ∣_ closedImmersionComplement i)) :
    (FinitePresentationIsoOverOpen.pullback
      s
      (closedImmersionComplement i)
      hs).IsEquivalence :=
  finitePresentationIsoOverOpenPullbackFunctor_isEquivalence
    s
    (closedImmersionComplement i)
    hs

end AlgebraicGeometry
