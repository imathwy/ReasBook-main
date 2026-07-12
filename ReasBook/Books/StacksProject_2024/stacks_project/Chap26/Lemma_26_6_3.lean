import Mathlib.AlgebraicGeometry.AffineScheme

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (f : Γ(X, ⊤))

-- Source/core/bridge:
-- * source-facing: Lemma 26.6.3 is the affine comparison through `X.isoSpec`.
-- * core/canonical: the reusable owner is `Scheme.toSpecΓ_preimage_basicOpen`.
-- * bridge/view: the pointwise membership theorem below.

variable [IsAffine X]

/-- Lemma 26.6.3: under the canonical affine identification `X ≅ Spec Γ(X, ⊤)`, the basic open
`D(f)` on `Spec Γ(X, ⊤)` pulls back to the basic open `D(f)` on `X`. -/
@[stacks 01I0]
theorem isoSpec_preimage_basicOpen :
    X.isoSpec.hom ⁻¹ᵁ PrimeSpectrum.basicOpen f = X.basicOpen f :=
  Scheme.toSpecΓ_preimage_basicOpen X f

/-- Pointwise membership form of the affine comparison of basic opens from Lemma 26.6.3. -/
@[simp]
theorem mem_basicOpen_iff_mem_primeSpectrum_basicOpen (x : X) :
    x ∈ X.basicOpen f ↔ X.isoSpec.hom x ∈ PrimeSpectrum.basicOpen f := by
  show x ∈ X.isoSpec.hom ⁻¹ᵁ PrimeSpectrum.basicOpen f ↔ x ∈ X.basicOpen f
  rw [isoSpec_preimage_basicOpen X f]

end AlgebraicGeometry.Scheme
