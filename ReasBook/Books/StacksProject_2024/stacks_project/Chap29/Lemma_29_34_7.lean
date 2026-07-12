import StacksProject_2024.Chap10.Lemma_10_137_9
import StacksProject_2024.Chap29.Lemma_29_30_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

private theorem syntomic_of_ringHomSmooth
    {R S : Type*} [CommRing R] [CommRing S] {φ : R →+* S}
    (hφ : φ.Smooth) :
    φ.Syntomic := by
  let _ : Algebra R S := φ.toAlgebra
  have hAlgSmooth : Algebra.Smooth R S := by
    exact (RingHom.smooth_algebraMap).1 <| by
      simpa [RingHom.algebraMap_toAlgebra] using hφ
  letI : Algebra.Smooth R S := hAlgSmooth
  simpa [RingHom.algebraMap_toAlgebra] using
    (Algebra.smooth_syntomic)

/- Semantic recall / analogue check:
- mathlib's canonical source-side owner is `Smooth f`, with affine-open criterion `smooth_iff`;
- Chapter 29 records scheme-side syntomicity source-faithfully as
  `Syntomic f := LocallyOfType RingHom.Syntomic f`, and `Lemma_29_14_3.lean` already exports the
  affine-open consequence of that owner for local ring-map properties;
- Chapter 10 exports the ring-level bridge `Algebra.smooth_syntomic`, so the present theorem is the
  source-facing scheme-level bridge obtained by applying those canonical affine-open owners.
-/

/-- Lemma 29.34.7: a smooth morphism is syntomic. -/
@[stacks 01VD]
theorem smooth_syntomic (hf : Smooth f) :
    Syntomic f := by
  rw [Scheme.Hom.syntomic_iff_affineOpen_appLE_syntomic]
  intro U hU V hV e
  exact syntomic_of_ringHomSmooth ((smooth_iff f).1 hf hV hU e)

/-- A smooth morphism is syntomic. -/
@[stacks 01VD, instance]
instance instSyntomicOfSmooth [Smooth f] :
    Syntomic f :=
  smooth_syntomic inferInstance

end AlgebraicGeometry
