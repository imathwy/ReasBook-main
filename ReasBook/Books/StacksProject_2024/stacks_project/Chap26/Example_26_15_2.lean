import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

noncomputable section

-- Semantic recall: `lean_leansearch` found `Scheme.Γ`, `Scheme.Γ_obj`, `Scheme.ΓSpecIso`, and
-- `AffineSpace.toSpecMvPolyIntEquiv`; the source example is therefore formalized by the
-- canonical global-sections functor and the affine-line representing scheme `Spec(ℤ[x])`.

/-- Example 26.15.2 (1): the contravariant functor sending a scheme `T` to its ring of global sections
`Γ(T, 𝒪_T)`, remembered as a set. -/
@[stacks 01JH]
def schemeGlobalSectionsFunctor : Schemeᵒᵖ ⥤ Type :=
  Scheme.Γ ⋙ forget CommRingCat

/-- Companion normal form for `schemeGlobalSectionsFunctor`: on a scheme `T`, it is the type
of global sections `Γ(T, 𝒪_T)`. -/
theorem schemeGlobalSectionsFunctor_obj (T : Scheme) :
    schemeGlobalSectionsFunctor.obj (op T) = Γ(T, ⊤) := sorry

/-- Example 26.15.2 (2): the universal global section `x ∈ Γ(Spec(ℤ[x]), 𝒪)` obtained from the polynomial generator
under the canonical affine global-sections isomorphism. -/
@[stacks 01JH]
def specPolynomialUniversalSection : Γ(Spec (CommRingCat.of (Polynomial ℤ)), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv Polynomial.X

/-- Example 26.15.2 (3): for each scheme `T`, the map sending
`f : T ⟶ Spec(ℤ[x])` to the pullback `f^♯(x)` of the universal section is bijective. This is
the componentwise form of the natural isomorphism `h_{Spec(ℤ[x])} ≅ F`. -/
@[stacks 01JH]
theorem specPolynomial_globalSectionsMap_bijective (T : Scheme) :
    Function.Bijective (fun f : T ⟶ Spec (CommRingCat.of (Polynomial ℤ)) ↦
      (Scheme.Γ.map f.op : Γ(Spec (CommRingCat.of (Polynomial ℤ)), ⊤) ⟶ Γ(T, ⊤))
        specPolynomialUniversalSection) := sorry

/-- Example 26.15.2 (4): under the canonical identification
`Γ(Spec(ℤ[x]), 𝒪) ≅ ℤ[x]`, the universal family corresponding to
`id_{Spec(ℤ[x])}` is the polynomial generator `x`. -/
@[stacks 01JH]
theorem specPolynomialUniversalSection_eq_X :
    (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).hom specPolynomialUniversalSection =
      Polynomial.X := sorry

end

end AlgebraicGeometry
