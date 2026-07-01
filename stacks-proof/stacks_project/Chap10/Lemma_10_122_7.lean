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

-- Proof sketch: first base change quasi-finiteness at the pulled-back prime of `S` to the
-- corresponding prime of `R' ⊗[R] S` using `Algebra.QuasiFiniteAt.baseChange`. Then descend along
-- the surjective canonical tensor-product map
-- `productLeftAlgHom (Algebra.ofId R' S') (IsScalarTower.toAlgHom R S S')`
-- via `Algebra.QuasiFiniteAt.of_surjectiveOnStalks`, using
-- `RingHom.surjectiveOnStalks_of_surjective`.
/-- Lemma 10.122.7: if the canonical map `R' ⊗[R] S → S'` is surjective and the pullback of `q'`
to `S` is a point where `R → S` is quasi-finite, then `R' → S'` is quasi-finite at `q'`.

The source states this in the finite-type setting, but the canonical owner proof only uses
`Algebra.QuasiFiniteAt.baseChange` and `Algebra.QuasiFiniteAt.of_surjectiveOnStalks`, so no finite
type hypothesis is needed in the public API. -/
theorem quasiFiniteAt_baseChange_of_surjective
    (hSurj : Function.Surjective
      (productLeftAlgHom (Algebra.ofId R' S') (IsScalarTower.toAlgHom R S S') :
        R' ⊗[R] S →ₐ[R'] S'))
    (q' : Ideal S') [q'.IsPrime]
    [Algebra.QuasiFiniteAt R (q'.comap (algebraMap S S'))] :
    Algebra.QuasiFiniteAt R' q' := sorry

end
