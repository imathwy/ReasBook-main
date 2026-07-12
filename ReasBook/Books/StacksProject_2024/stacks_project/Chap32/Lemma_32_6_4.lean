import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical owners
-- `AlgebraicGeometry.LocallyOfFinitePresentation`, `Scheme.fromSpecStalk`, and local-ring
-- closed points `IsLocalRing.closedPoint`. Local Chapter 32 precedent uses open subschemes
-- through `U.toScheme` and `U.ι`, and records morphisms over a base by equalities to the
-- structural morphism.

/-- Lemma 32.6.4: let `S` be a scheme, let `X` and `Y` be schemes over `S`, and assume
`Y` is locally of finite presentation over `S`. If `x ∈ X` is a closed point and the open
complement `U = X \ {x}` is quasi-compact over `X`, then restriction to `U` and to
`Spec(𝒪_{X,x})` gives a bijection from morphisms `X ⟶ Y` over `S` to pairs consisting of a
morphism `U ⟶ Y` over `S` and a morphism `Spec(𝒪_{X,x}) ⟶ Y` over `S` which agree on the
punctured local scheme `V = Spec(𝒪_{X,x}) \ {x}`. The comparison map `toU` records the canonical
factorization of the punctured local scheme through the open complement. -/
@[stacks 0GWT]
theorem morphismsOverRestrictPuncturedLocalSpecBijective
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)
    [LocallyOfFinitePresentation pY]
    (x : X) (hx : x ∈ closedPoints X)
    (U : X.Opens) (hU : (U : Set X) = ({x} : Set X)ᶜ)
    (hUqc : QuasiCompact U.ι)
    (V : (Spec (CommRingCat.of (X.presheaf.stalk x))).Opens)
    (hV : (V : Set (Spec (CommRingCat.of (X.presheaf.stalk x)))) =
      ({IsLocalRing.closedPoint (X.presheaf.stalk x)} :
        Set (Spec (CommRingCat.of (X.presheaf.stalk x))))ᶜ)
    (toU : V.toScheme ⟶ U.toScheme)
    (htoU : toU ≫ U.ι = V.ι ≫ X.fromSpecStalk x) :
    Set.BijOn
      (fun g : {g : X ⟶ Y // g ≫ pY = pX} ↦
        (U.ι ≫ g.1, X.fromSpecStalk x ≫ g.1))
      Set.univ
      ({ab : (U.toScheme ⟶ Y) × ((Spec (CommRingCat.of (X.presheaf.stalk x))) ⟶ Y) |
          ab.1 ≫ pY = U.ι ≫ pX} ∩
        {ab | ab.2 ≫ pY = X.fromSpecStalk x ≫ pX} ∩
        {ab | toU ≫ ab.1 = V.ι ≫ ab.2}) := sorry

end AlgebraicGeometry
