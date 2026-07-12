import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-theoretic-image owner
-- `Scheme.Hom.image` with the quasi-compact image map `Scheme.Hom.toImage`, and the valuative
-- criterion API uses `ValuationRing` together with `Spec.map` from an algebra map. The Stacks tag
-- evidence is consistent: item tag `02JQ` matches the source URL `/tag/02JQ`.

/-- Lemma 29.6.5 (1): if `f : X \to Y` is quasi-compact and `z` is a point of the
scheme-theoretic image of `f`, then there is a valuation ring `A` with fraction field `K` and a
commutative diagram `Spec K -> X -> Scheme.Hom.image f` over `Spec A -> Scheme.Hom.image f`
whose closed point maps to `z`. -/
@[stacks 02JQ]
theorem exists_valuationRing_diagram_of_mem_schemeTheoreticImage
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (z : Scheme.Hom.image f) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A)
      (K : Type u) (_ : Field K) (_ : Algebra A K) (_ : IsFractionRing A K)
      (genericToX : Spec (CommRingCat.of K) ⟶ X)
      (valuationToImage : Spec (CommRingCat.of A) ⟶ Scheme.Hom.image f),
        CommSq genericToX
          (Spec.map (CommRingCat.ofHom (algebraMap A K)))
          (Scheme.Hom.toImage f) valuationToImage ∧
        valuationToImage (IsLocalRing.closedPoint A) = z := sorry

/-- Lemma 29.6.5 (2): in particular, every point of the scheme-theoretic image of a
quasi-compact morphism is a specialization of a point in the image of `X`. -/
@[stacks 02JQ]
theorem exists_specialization_from_image_of_mem_schemeTheoreticImage
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (z : Scheme.Hom.image f) :
    ∃ x : X, (Scheme.Hom.toImage f) x ⤳ z := sorry

end

end AlgebraicGeometry
