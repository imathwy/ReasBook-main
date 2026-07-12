import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u v w x

section

variable {R : Type u} {S : Type v} {R' : Type w} {S' : Type x}
variable [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
variable [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S']
variable [IsScalarTower R S S'] [IsScalarTower R R' S']

/-- Helper for Chap10 Lemma 10 122 7: the canonical tensor-product map pulls `q'` back to the
same ideal of `S` as the structure map `S → S'`. -/
private lemma comap_productLeftAlgHom_includeRight
    (q' : Ideal S') :
    q'.comap (algebraMap S S') =
      (q'.comap
        (productLeftAlgHom (Algebra.ofId R' S') (IsScalarTower.toAlgHom R S S') :
          R' ⊗[R] S →ₐ[R'] S').toRingHom).comap
        (Algebra.TensorProduct.includeRight.toRingHom) := by
  -- Compare membership after pulling back along `includeRight`; the tensor-product computation
  -- reduces the composite to the original structure map `S → S'`.
  ext s
  simp [Ideal.mem_comap]

/-- Helper for Chap10 Lemma 10 122 7: quasi-finiteness base-changes to the prime of
`R' ⊗[R] S` lying over `q'`. -/
private lemma quasiFiniteAt_comap_productLeftAlgHom
    (q' : Ideal S') [q'.IsPrime]
    [Algebra.QuasiFiniteAt R (q'.comap (algebraMap S S'))] :
    Algebra.QuasiFiniteAt R'
      (q'.comap
        (productLeftAlgHom (Algebra.ofId R' S') (IsScalarTower.toAlgHom R S S') :
          R' ⊗[R] S →ₐ[R'] S').toRingHom) := by
  -- Name the canonical map so the base-change ideal has a stable normal form.
  let F : R' ⊗[R] S →ₐ[R'] S' :=
    productLeftAlgHom (Algebra.ofId R' S') (IsScalarTower.toAlgHom R S S')
  -- The adapter lemma supplies exactly the ideal equality required by `baseChange`.
  have hq : q'.comap (algebraMap S S') =
      (q'.comap F.toRingHom).comap Algebra.TensorProduct.includeRight.toRingHom := by
    simpa [F] using comap_productLeftAlgHom_includeRight (R := R) (S := S) (R' := R')
      (S' := S') q'
  -- Apply the canonical quasi-finite base-change theorem at the pulled-back prime.
  exact Algebra.QuasiFiniteAt.baseChange (q'.comap (algebraMap S S')) (q'.comap F.toRingHom) hq

-- Proof sketch: first base change quasi-finiteness at the pulled-back prime of `S` to the
-- corresponding prime of `R' ⊗[R] S` using `Algebra.QuasiFiniteAt.baseChange`. Then descend along
-- the surjective canonical tensor-product map
-- `productLeftAlgHom (Algebra.ofId R' S') (IsScalarTower.toAlgHom R S S')`
-- via `Algebra.QuasiFiniteAt.of_surjectiveOnStalks`, using
-- `RingHom.surjectiveOnStalks_of_surjective`.
/-- Chap10 Lemma 10 122 7: if the canonical map `R' ⊗[R] S → S'` is surjective and the pullback of `q'`
to `S` is a point where `R → S` is quasi-finite, then `R' → S'` is quasi-finite at `q'`.

The source states this in the finite-type setting, but the canonical owner proof only uses
`Algebra.QuasiFiniteAt.baseChange` and `Algebra.QuasiFiniteAt.of_surjectiveOnStalks`, so no finite
type hypothesis is needed in the public API. -/
@[stacks 00PN]
theorem quasiFiniteAt_baseChange_of_surjective
    (hSurj : Function.Surjective
      (productLeftAlgHom (Algebra.ofId R' S') (IsScalarTower.toAlgHom R S S') :
        R' ⊗[R] S →ₐ[R'] S'))
    (q' : Ideal S') [q'.IsPrime]
    [Algebra.QuasiFiniteAt R (q'.comap (algebraMap S S'))] :
    Algebra.QuasiFiniteAt R' q' := by
  -- Work with the canonical tensor-product algebra map throughout the descent step.
  let F : R' ⊗[R] S →ₐ[R'] S' :=
    productLeftAlgHom (Algebra.ofId R' S') (IsScalarTower.toAlgHom R S S')
  -- The base-change helper gives quasi-finiteness at the comap prime on `R' ⊗[R] S`.
  have hBase : Algebra.QuasiFiniteAt R' (q'.comap F.toRingHom) := by
    simpa [F] using quasiFiniteAt_comap_productLeftAlgHom (R := R) (S := S) (R' := R')
      (S' := S') q'
  letI : Algebra.QuasiFiniteAt R' (q'.comap F.toRingHom) := hBase
  -- Turn the assumed surjectivity of `F` into the stalkwise surjectivity needed for descent.
  have hFsurj : Function.Surjective F := by
    simpa [F] using hSurj
  have hStalks : F.SurjectiveOnStalks :=
    RingHom.surjectiveOnStalks_of_surjective hFsurj
  -- Descend quasi-finiteness from the tensor-product prime to `q'` using the defining comap.
  have hComap : q'.comap F.toRingHom = q'.comap F.toRingHom := rfl
  exact Algebra.QuasiFiniteAt.of_surjectiveOnStalks (q'.comap F.toRingHom) F hStalks q' hComap

end
