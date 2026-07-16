import StacksProject_2024.stacks_project.Chap32.Lemma_32_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` returned the canonical scheme-morphism owners
-- `IsSeparated`, `IsProper`, `IsFinite`, `Etale`, `IsIntegralHom`, and their base-change
-- stability API. The local owner for the correspondence is the functor from Lemma 32.21.1.

/-- Lemma 32.21.2 (1): in the notation and assumptions of Lemma 32.21.1, if
`f : X ⟶ S` corresponds to `g : Y ⟶ Spec(𝒪_{S,s})` via the punctured-local equivalence, then
`f` is separated if and only if `g` is separated. -/
@[stacks 0BFN]
theorem puncturedLocalEquivalence_isSeparated_iff
    (S : Scheme.{u}) (s : S) (hs : s ∈ closedPoints S)
    (U : S.Opens) (hU : (U : Set S) = ({s} : Set S)ᶜ)
    (hUqc : QuasiCompact U.ι)
    (V : (Spec (CommRingCat.of (S.presheaf.stalk s))).Opens)
    (hV : (V : Set (Spec (CommRingCat.of (S.presheaf.stalk s)))) =
      ({IsLocalRing.closedPoint (S.presheaf.stalk s)} :
        Set (Spec (CommRingCat.of (S.presheaf.stalk s))))ᶜ)
    (X : PuncturedLocalFinitePresentationIsoOverOpen U)
    (Y : PuncturedLocalFinitePresentationIsoOverOpen V)
    (e : (ObjectProperty.lift
        (puncturedLocalFinitePresentationIsoOverOpenProperty V)
        ((puncturedLocalFinitePresentationIsoOverOpenInclusion U) ⋙
          Over.pullback (S.fromSpecStalk s))
        (fun X ↦ puncturedLocalBaseChange_mem S s hs U hU hUqc V hV X)).obj X ≅ Y) :
    IsSeparated X.obj.hom ↔ IsSeparated Y.obj.hom := sorry

/-- Lemma 32.21.2 (2): in the notation and assumptions of Lemma 32.21.1, if
`f : X ⟶ S` corresponds to `g : Y ⟶ Spec(𝒪_{S,s})` via the punctured-local equivalence, then
`f` is proper if and only if `g` is proper. -/
@[stacks 0BFN]
theorem puncturedLocalEquivalence_isProper_iff
    (S : Scheme.{u}) (s : S) (hs : s ∈ closedPoints S)
    (U : S.Opens) (hU : (U : Set S) = ({s} : Set S)ᶜ)
    (hUqc : QuasiCompact U.ι)
    (V : (Spec (CommRingCat.of (S.presheaf.stalk s))).Opens)
    (hV : (V : Set (Spec (CommRingCat.of (S.presheaf.stalk s)))) =
      ({IsLocalRing.closedPoint (S.presheaf.stalk s)} :
        Set (Spec (CommRingCat.of (S.presheaf.stalk s))))ᶜ)
    (X : PuncturedLocalFinitePresentationIsoOverOpen U)
    (Y : PuncturedLocalFinitePresentationIsoOverOpen V)
    (e : (ObjectProperty.lift
        (puncturedLocalFinitePresentationIsoOverOpenProperty V)
        ((puncturedLocalFinitePresentationIsoOverOpenInclusion U) ⋙
          Over.pullback (S.fromSpecStalk s))
        (fun X ↦ puncturedLocalBaseChange_mem S s hs U hU hUqc V hV X)).obj X ≅ Y) :
    IsProper X.obj.hom ↔ IsProper Y.obj.hom := sorry

/-- Lemma 32.21.2 (3): in the notation and assumptions of Lemma 32.21.1, if
`f : X ⟶ S` corresponds to `g : Y ⟶ Spec(𝒪_{S,s})` via the punctured-local equivalence, then
`f` is finite if and only if `g` is finite. -/
@[stacks 0BFN]
theorem puncturedLocalEquivalence_isFinite_iff
    (S : Scheme.{u}) (s : S) (hs : s ∈ closedPoints S)
    (U : S.Opens) (hU : (U : Set S) = ({s} : Set S)ᶜ)
    (hUqc : QuasiCompact U.ι)
    (V : (Spec (CommRingCat.of (S.presheaf.stalk s))).Opens)
    (hV : (V : Set (Spec (CommRingCat.of (S.presheaf.stalk s)))) =
      ({IsLocalRing.closedPoint (S.presheaf.stalk s)} :
        Set (Spec (CommRingCat.of (S.presheaf.stalk s))))ᶜ)
    (X : PuncturedLocalFinitePresentationIsoOverOpen U)
    (Y : PuncturedLocalFinitePresentationIsoOverOpen V)
    (e : (ObjectProperty.lift
        (puncturedLocalFinitePresentationIsoOverOpenProperty V)
        ((puncturedLocalFinitePresentationIsoOverOpenInclusion U) ⋙
          Over.pullback (S.fromSpecStalk s))
        (fun X ↦ puncturedLocalBaseChange_mem S s hs U hU hUqc V hV X)).obj X ≅ Y) :
    IsFinite X.obj.hom ↔ IsFinite Y.obj.hom := sorry

/-- Lemma 32.21.2 (4): in the notation and assumptions of Lemma 32.21.1, if
`f : X ⟶ S` corresponds to `g : Y ⟶ Spec(𝒪_{S,s})` via the punctured-local equivalence, then
`f` is étale if and only if `g` is étale. -/
@[stacks 0BFN]
theorem puncturedLocalEquivalence_etale_iff
    (S : Scheme.{u}) (s : S) (hs : s ∈ closedPoints S)
    (U : S.Opens) (hU : (U : Set S) = ({s} : Set S)ᶜ)
    (hUqc : QuasiCompact U.ι)
    (V : (Spec (CommRingCat.of (S.presheaf.stalk s))).Opens)
    (hV : (V : Set (Spec (CommRingCat.of (S.presheaf.stalk s)))) =
      ({IsLocalRing.closedPoint (S.presheaf.stalk s)} :
        Set (Spec (CommRingCat.of (S.presheaf.stalk s))))ᶜ)
    (X : PuncturedLocalFinitePresentationIsoOverOpen U)
    (Y : PuncturedLocalFinitePresentationIsoOverOpen V)
    (e : (ObjectProperty.lift
        (puncturedLocalFinitePresentationIsoOverOpenProperty V)
        ((puncturedLocalFinitePresentationIsoOverOpenInclusion U) ⋙
          Over.pullback (S.fromSpecStalk s))
        (fun X ↦ puncturedLocalBaseChange_mem S s hs U hU hUqc V hV X)).obj X ≅ Y) :
    Etale X.obj.hom ↔ Etale Y.obj.hom := sorry

/-- Lemma 32.21.2 (5): in the notation and assumptions of Lemma 32.21.1, if
`f : X ⟶ S` corresponds to `g : Y ⟶ Spec(𝒪_{S,s})` via the punctured-local equivalence, then
`f` is integral if and only if `g` is integral. -/
@[stacks 0BFN]
theorem puncturedLocalEquivalence_isIntegralHom_iff
    (S : Scheme.{u}) (s : S) (hs : s ∈ closedPoints S)
    (U : S.Opens) (hU : (U : Set S) = ({s} : Set S)ᶜ)
    (hUqc : QuasiCompact U.ι)
    (V : (Spec (CommRingCat.of (S.presheaf.stalk s))).Opens)
    (hV : (V : Set (Spec (CommRingCat.of (S.presheaf.stalk s)))) =
      ({IsLocalRing.closedPoint (S.presheaf.stalk s)} :
        Set (Spec (CommRingCat.of (S.presheaf.stalk s))))ᶜ)
    (X : PuncturedLocalFinitePresentationIsoOverOpen U)
    (Y : PuncturedLocalFinitePresentationIsoOverOpen V)
    (e : (ObjectProperty.lift
        (puncturedLocalFinitePresentationIsoOverOpenProperty V)
        ((puncturedLocalFinitePresentationIsoOverOpenInclusion U) ⋙
          Over.pullback (S.fromSpecStalk s))
        (fun X ↦ puncturedLocalBaseChange_mem S s hs U hU hUqc V hV X)).obj X ≅ Y) :
    IsIntegralHom X.obj.hom ↔ IsIntegralHom Y.obj.hom := sorry

end AlgebraicGeometry
