import Mathlib
import StacksProject_2024.Chap04.«4_34_2_2»
import StacksProject_2024.Chap04.«4_34_2_3»

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory
namespace CategoryOver

open BasedNatIso
open BasedNatTrans
open scoped Bicategory BasedFunctor

variable {C : Type*} [Category C]
variable {X Y : CategoryOver C}

/- Domain-style sampling for Lemma 4.34.3:
- primary domain: bicategorical `2`-fibre products in `Cat/C`, specialized to the relative and
  absolute inertia constructions of a morphism in `Cat/C`;
- inspected owner declarations:
  `BicategoricalTwoCommutativeSquare`,
  `Bicategory.IsFinal`,
  `absoluteInertiaIdentitySection`,
  `absoluteInertiaOverMap`,
  `relativeInertiaToAbsoluteInertia`,
  `relativeInertiaMap_obj_α`;
- best owner abstraction: the source-facing square below, expressed directly as a
  `BicategoricalTwoCommutativeSquare` in `Cat/C`;
- source/core/bridge triage:
  `source-facing`: `relativeAbsoluteInertiaSquare`;
  `core/canonical`: `Bicategory.IsFinal (relativeAbsoluteInertiaSquare F)`;
  `bridge/view`: the typed `Cat/C` comparison maps
  `relativeInertiaToAbsoluteInertia`, `absoluteInertiaOverMap`, and
  `absoluteInertiaIdentitySection`;
- primitive-vs-derived split: the square uses only the canonical inertia maps and their
  comparison isomorphism; the `IsFinal` universal property is derived API. -/

private abbrev relativeAbsoluteInertiaLeftMap
    (F : X ⥤ᵇ Y) :
    relativeInertiaOver F ⥤ᵇ Y :=
  relativeInertiaStructureMap F ⋙ F

private abbrev relativeAbsoluteInertiaTop
    (F : X ⥤ᵇ Y) :
    relativeInertiaOver F ⥤ᵇ absoluteInertiaOver Y :=
  relativeAbsoluteInertiaLeftMap F ⋙ absoluteInertiaIdentitySection Y

private noncomputable abbrev relativeAbsoluteInertiaBottom
    (F : X ⥤ᵇ Y) :
    relativeInertiaOver F ⥤ᵇ absoluteInertiaOver Y :=
  relativeInertiaToAbsoluteInertia F ⋙ absoluteInertiaOverMap F

private theorem relativeAbsoluteInertiaHom_comm
    (F : X ⥤ᵇ Y) (Z : RelativeInertiaObject F.toFunctor) :
    ((relativeAbsoluteInertiaTop F).obj Z).α.hom ≫
        𝟙 ((relativeAbsoluteInertiaTop F).obj Z).x =
      𝟙 ((relativeAbsoluteInertiaTop F).obj Z).x ≫
        ((relativeAbsoluteInertiaBottom F).obj Z).α.hom := by
  simpa [relativeAbsoluteInertiaTop, relativeAbsoluteInertiaBottom,
    relativeAbsoluteInertiaLeftMap, relativeInertiaStructureMap,
    absoluteInertiaIdentitySection, relativeInertiaToAbsoluteInertia,
    absoluteInertiaOverMap, relativeInertiaIdentitySection_obj_α,
    relativeInertiaMap_obj_x] using Z.map_hom_eq_id.symm

private theorem relativeAbsoluteInertiaInv_comm
    (F : X ⥤ᵇ Y) (Z : RelativeInertiaObject F.toFunctor) :
    ((relativeAbsoluteInertiaBottom F).obj Z).α.hom ≫
        𝟙 ((relativeAbsoluteInertiaBottom F).obj Z).x =
      𝟙 ((relativeAbsoluteInertiaBottom F).obj Z).x ≫
        ((relativeAbsoluteInertiaTop F).obj Z).α.hom := by
  simpa [relativeAbsoluteInertiaTop, relativeAbsoluteInertiaBottom,
    relativeAbsoluteInertiaLeftMap, relativeInertiaStructureMap,
    absoluteInertiaIdentitySection, relativeInertiaToAbsoluteInertia,
    absoluteInertiaOverMap, relativeInertiaIdentitySection_obj_α,
    relativeInertiaMap_obj_x] using Z.map_hom_eq_id

private noncomputable def relativeAbsoluteInertiaHom
    (F : X ⥤ᵇ Y) (Z : RelativeInertiaObject F.toFunctor) :
    (relativeAbsoluteInertiaTop F).obj Z ⟶ (relativeAbsoluteInertiaBottom F).obj Z :=
  { φ := 𝟙 _
    comm := relativeAbsoluteInertiaHom_comm F Z }

private noncomputable def relativeAbsoluteInertiaInv
    (F : X ⥤ᵇ Y) (Z : RelativeInertiaObject F.toFunctor) :
    (relativeAbsoluteInertiaBottom F).obj Z ⟶ (relativeAbsoluteInertiaTop F).obj Z :=
  { φ := 𝟙 _
    comm := relativeAbsoluteInertiaInv_comm F Z }

private noncomputable def relativeAbsoluteInertiaObjIso
    (F : X ⥤ᵇ Y) (Z : RelativeInertiaObject F.toFunctor) :
    (relativeAbsoluteInertiaTop F).obj Z ≅ (relativeAbsoluteInertiaBottom F).obj Z where
  hom := relativeAbsoluteInertiaHom F Z
  inv := relativeAbsoluteInertiaInv F Z
  hom_inv_id := by
    apply RelativeInertiaHom.ext
    change (relativeAbsoluteInertiaHom F Z).φ ≫
        (relativeAbsoluteInertiaInv F Z).φ =
      𝟙 ((relativeAbsoluteInertiaTop F).obj Z).x
    change 𝟙 (F.obj Z.x) ≫ 𝟙 (F.obj Z.x) = 𝟙 (F.obj Z.x)
    simp
  inv_hom_id := by
    apply RelativeInertiaHom.ext
    change (relativeAbsoluteInertiaInv F Z).φ ≫
        (relativeAbsoluteInertiaHom F Z).φ =
      𝟙 ((relativeAbsoluteInertiaBottom F).obj Z).x
    change 𝟙 (F.obj Z.x) ≫ 𝟙 (F.obj Z.x) = 𝟙 (F.obj Z.x)
    simp

private noncomputable def relativeAbsoluteInertiaComparisonNatIso
    (F : X ⥤ᵇ Y) :
    (relativeAbsoluteInertiaTop F).toFunctor ≅
      (relativeAbsoluteInertiaBottom F).toFunctor :=
  NatIso.ofComponents
    (fun Z ↦ relativeAbsoluteInertiaObjIso F Z)
    (fun {Z Z'} f ↦ by
      apply RelativeInertiaHom.ext
      change ((relativeAbsoluteInertiaTop F).map f).φ ≫
          (relativeAbsoluteInertiaHom F Z').φ =
        (relativeAbsoluteInertiaHom F Z).φ ≫
          ((relativeAbsoluteInertiaBottom F).map f).φ
      change F.map f.φ ≫ 𝟙 (F.obj Z'.x) = 𝟙 (F.obj Z.x) ≫ F.map f.φ
      simp)

private theorem relativeAbsoluteInertiaComparison_over_id
    (F : X ⥤ᵇ Y) :
    eqToHom (relativeAbsoluteInertiaTop F).w.symm ≫
        Functor.whiskerRight
          (relativeAbsoluteInertiaComparisonNatIso F).hom
          (absoluteInertiaOver Y).p ≫
      eqToHom (relativeAbsoluteInertiaBottom F).w =
        𝟙 (relativeInertiaOver F).p := by
  sorry

private noncomputable def relativeAbsoluteInertiaComparison
    (F : X ⥤ᵇ Y) :
    relativeAbsoluteInertiaTop F ≅ relativeAbsoluteInertiaBottom F :=
  let η : relativeAbsoluteInertiaTop F ⟶ relativeAbsoluteInertiaBottom F :=
    of_over_id
      (relativeAbsoluteInertiaComparisonNatIso F).hom
      (relativeAbsoluteInertiaComparison_over_id F)
  mkNatIso (relativeAbsoluteInertiaComparisonNatIso F) η.isHomLift'

/-- The canonical relative/absolute inertia square attached to a morphism in `Cat/\mathcal C` is
a `2`-commutative square in the ambient bicategory `Cat/\mathcal C`. -/
noncomputable def relativeAbsoluteInertiaSquare
    (F : X ⥤ᵇ Y) :=
  let G : absoluteInertiaOver X ⟶ absoluteInertiaOver Y := absoluteInertiaOverMap F
  show BicategoricalTwoCommutativeSquare
      (absoluteInertiaIdentitySection Y : Y ⟶ absoluteInertiaOver Y)
      G from
    { obj := relativeInertiaOver F
      p := relativeAbsoluteInertiaLeftMap F
      q := relativeInertiaToAbsoluteInertia F
      ψ := relativeAbsoluteInertiaComparison F }

-- Proof sketch: unpack the relative inertia and the absolute inertias into the canonical square
-- described in the text, then verify the universal property by giving the usual factorization of
-- any competing square through the inertia condition that the induced automorphism in
-- `\mathcal{I}_{\mathcal S'}` is the identity.
/-- Lemma 4.34.3: for a `1`-morphism `F : \mathcal{S} \to \mathcal{S}'` in `Cat/\mathcal C`, the
displayed square
`\mathcal{I}_{\mathcal S / \mathcal S'} \to \mathcal{I}_{\mathcal S} \to
\mathcal{I}_{\mathcal S'} \leftarrow \mathcal S'`
is a strict `2`-fibre product in `Cat/\mathcal C`. -/
theorem relativeAbsoluteInertiaSquare_isTwoFibreProduct
    (F : X ⥤ᵇ Y) :
    Bicategory.IsFinal (relativeAbsoluteInertiaSquare F) := sorry

end CategoryOver
end CategoryTheory
