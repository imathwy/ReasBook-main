import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the exact preimage identity
-- `Scheme.toSpecΓ_preimage_basicOpen`, the ring-level qcqs comparison
-- `isIso_ΓSpec_adjunction_unit_app_basicOpen`, and the affine-open owner
-- `IsAffineOpen.isoSpec`; the source-facing statement is therefore the restricted scheme morphism
-- `X.toSpecΓ ∣_ PrimeSpectrum.basicOpen f`.

/-- Lemma 28.18.3: let `X` be a quasi-compact and quasi-separated scheme, and let
`f ∈ Γ(X, \mathcal O_X)`. If the principal open `X_f = X.basicOpen f` is affine, then the
canonical morphism `j : X ⟶ Spec Γ(X, \top)` induces an isomorphism of
`X_f = j^{-1}(D(f))` onto the standard affine open `D(f) ⊆ Spec Γ(X, \top)`, formalized as the
restricted morphism `X.toSpecΓ ∣_ PrimeSpectrum.basicOpen f` being an isomorphism. -/
@[stacks 01P8]
theorem isIso_restrict_toSpecΓ_basicOpen_of_isAffineOpen
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (f : Γ(X, ⊤)) (hf : IsAffineOpen (X.basicOpen f)) :
    CategoryTheory.IsIso (X.toSpecΓ ∣_ PrimeSpectrum.basicOpen f) := sorry

end AlgebraicGeometry
