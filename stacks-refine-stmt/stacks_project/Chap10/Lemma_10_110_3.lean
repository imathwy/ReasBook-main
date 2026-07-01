import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.RingTheory.Ideal.Cotangent

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-
Domain triage:
* primary domain: homological bounds for the residue field of a Noetherian local ring;
* sampled owner declarations:
  `CategoryTheory.projectiveDimension`,
  `IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`,
  `IsRegularLocalRing.iff_finrank_cotangentSpace`,
  `projectiveDimension_le_iff`;
* owner abstraction: the canonical owners are `projectiveDimension` on `ModuleCat R` and
  `CotangentSpace R` for the embedding-dimension side;
* layer: `source-facing`, since the textbook item is the lower bound comparing these two canonical
  invariants rather than defining a new owner object.
-/

-- Proof sketch: choose a basis of the cotangent space `CotangentSpace R = maximalIdeal R / (maximalIdeal R)^2`
-- and the corresponding Koszul complex. Compare it with a minimal finite free resolution of
-- `ResidueField R`; after tensoring with the residue field, the comparison maps are injective in
-- each degree, forcing the resolution to be nonzero through degree
-- `Module.finrank (ResidueField R) (CotangentSpace R)`.
/-- Lemma 10.110.3: for a Noetherian local ring `R`, the projective dimension of the residue field
`ResidueField R` is at least the dimension of the cotangent space `CotangentSpace R = 𝔪 / 𝔪²`
over the residue field. -/
theorem finrank_cotangentSpace_le_projectiveDimension_residueField :
    Module.finrank (ResidueField R) (CotangentSpace R) ≤
      projectiveDimension (ModuleCat.of R (ResidueField R)) := sorry

end
