import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CommRingCat
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical pullback formula
-- `AlgebraicGeometry.pullbackSpecIso`; the finite-limit owner for affine schemes is the canonical
-- category `AlgebraicGeometry.AffineScheme`, and the source's "same as locally ringed spaces"
-- clause is expressed by preservation under
-- `AffineScheme.forgetToScheme ⋙ Scheme.forgetToLocallyRingedSpace`.

/-- Lemma 26.6.7 (1): the category of affine schemes has finite limits. -/
@[stacks 01I4]
theorem affineScheme_hasFiniteLimits : HasFiniteLimits AffineScheme := sorry

/-- Lemma 26.6.7 (2): finite limits of affine schemes are computed by the underlying locally
ringed spaces. -/
@[stacks 01I4]
theorem affineScheme_forgetToLocallyRingedSpace_preservesFiniteLimits :
    PreservesFiniteLimits (AffineScheme.forgetToScheme ⋙ Scheme.forgetToLocallyRingedSpace) := sorry

/-- Lemma 26.6.7 (3): in locally ringed spaces, `Spec R × Spec S` is represented by
`Spec (R ⊗[ℤ] S)`. -/
@[stacks 01I4]
theorem specTensorProduct_isProduct_locallyRingedSpace
    (R S : Type u) [CommRing R] [CommRing S] :
    Nonempty (IsLimit (BinaryFan.mk
      (Scheme.Hom.toLRSHom (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[ℤ] S))))
      (Scheme.Hom.toLRSHom (Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight : S →ₐ[ℤ] R ⊗[ℤ] S).toRingHom)))))) := sorry

/-- Lemma 26.6.7 (4): in locally ringed spaces, for ring maps `R → A` and `R → B`,
`Spec A ×_{Spec R} Spec B` is represented by `Spec (A ⊗[R] B)`. -/
@[stacks 01I4]
theorem specTensorProduct_isPullback_locallyRingedSpace
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] :
    CategoryTheory.IsPullback
      (Scheme.Hom.toLRSHom (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B))))
      (Scheme.Hom.toLRSHom (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B))))
      (Scheme.Hom.toLRSHom (Spec.map (CommRingCat.ofHom (algebraMap R A))))
      (Scheme.Hom.toLRSHom (Spec.map (CommRingCat.ofHom (algebraMap R B)))) := sorry

end AlgebraicGeometry
