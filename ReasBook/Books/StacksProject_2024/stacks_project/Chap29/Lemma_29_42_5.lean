import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the canonical properness owner `AlgebraicGeometry.IsProper` together
  with the valuative-criterion API.
- Local Chapter 29 precedent expresses extension across an inclusion of open subschemes by the
  canonical morphism `X.homOfLE h : U.toScheme ⟶ U'.toScheme`.
-/

section

variable {X Y S : Scheme.{u}} {fX : X ⟶ S} {fY : Y ⟶ S}
variable {x : X} {U : X.Opens}

/-- An extension of a morphism from an open subscheme `U` to an open neighbourhood of `x` as an
`S`-morphism. -/
@[stacks 0BX7]
structure OpenExtensionAtPoint
    (f : U.toScheme ⟶ Y) where
  U' : X.Opens
  hUU' : U ≤ U'
  hxU' : x ∈ U'
  f' : U'.toScheme ⟶ Y
  comm : f' ≫ fY = U'.ι ≫ fX
  restrict : X.homOfLE hUU' ≫ f' = f

/-- Lemma 29.42.5: let `S` be a scheme, let `X` and `Y` be schemes over `S`, let `x : X`, let
`U ⊆ X` be open, and let `f : U.toScheme ⟶ Y` be an `S`-morphism. Assume `x` lies in the closure
of `U`, assume either that `X` is reduced with finitely many irreducible components or that `X`
is locally Noetherian, assume `𝒪_{X, x}` is a valuation ring, and assume `Y ⟶ S` is proper. Then
there exists an open neighbourhood `U'` of `x` with `U ≤ U'` and an `S`-morphism
`f' : U'.toScheme ⟶ Y` extending `f`. -/
@[stacks 0BX7]
theorem exists_open_extension_of_isProper_of_stalk_valuationRing
    (f : U.toScheme ⟶ Y)
    (hf_over : f ≫ fY = U.ι ≫ fX)
    (hx_closure : x ∈ closure (U : Set X))
    [IsProper fY]
    [IsDomain (X.presheaf.stalk x)]
    [ValuationRing (X.presheaf.stalk x)]
    (hX :
      (IsReduced X ∧ Finite (irreducibleComponents X)) ∨ IsLocallyNoetherian X) :
    Nonempty (@OpenExtensionAtPoint X Y S fX fY x U f) := sorry

end

end AlgebraicGeometry
