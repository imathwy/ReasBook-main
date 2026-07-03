import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise
open AlgEquiv

universe u v w

noncomputable section

section

variable {A : Type u} [CommRing A] [IsDomain A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type v} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
variable {M : Type w} [Field M] [Algebra L M] [Algebra K M] [Algebra A M]
  [IsScalarTower K L M] [IsScalarTower A K M] [IsScalarTower A L M] [IsGalois K M]

local notation "B" => integralClosure A L
local notation "C" => integralClosure A M

/- Domain-style sampling for Lemma 15.111.11:
- primary domain: decomposition and inertia groups in a tower of integral closures under Galois
  restriction
- sampled owner declarations:
  `MulAction.stabilizer`,
  `Ideal.inertia`,
  `Ideal.under`,
  `AlgEquiv.restrictNormalHom`,
  `IsIntegralClosure.MulSemiringAction`
- best owner abstraction: the canonical subgroup owners `MulAction.stabilizer G I` and `I.inertia G`
  together with the restriction homomorphism `restrictNormalHom`
- primitive data: the canonical `B`-algebra structure on `C` induced by `L ⊆ M` and a prime ideal
  `r : Ideal C`
- derived API: the image equalities for the decomposition and inertia groups of the contracted
  prime `r.under B`

Layer triage:
- `source-facing`: the two image-equality statements in the tower
- `core/canonical`: `MulAction.stabilizer`, `Ideal.inertia`, and `restrictNormalHom`
- `bridge/view`: contraction of `r` to `B`, canonically expressed as `r.under B`

The file should keep the source-facing statements, but state them directly in terms of those owner
declarations instead of repeating the integral-closure map inline or using a parallel inertia
surface. -/

private noncomputable local instance : Algebra B C :=
  ((IsScalarTower.toAlgHom A L M).mapIntegralClosure : B →ₐ[A] C).toAlgebra

/-- The canonical `Gal(M / K)`-action on the integral closure `C` of `A` in `M`. -/
private local instance integralClosureMulSemiringAction_top :
    MulSemiringAction Gal(M/K) C :=
  IsIntegralClosure.MulSemiringAction A K M C

/-- The canonical `Gal(L / K)`-action on the integral closure `B` of `A` in `L`. -/
private local instance integralClosureMulSemiringAction_base :
    MulSemiringAction Gal(L/K) B :=
  IsIntegralClosure.MulSemiringAction A K L B

-- Proof sketch: for `σ ∈ Gal(L / K)`, lift `σ` to some `τ ∈ Gal(M / K)` by surjectivity of
-- `restrictNormalHom`. Then `τ • r` and `r` contract to the same prime of `B`, so
-- Lemma `15.111.10` produces an element of `Gal(M / L)` carrying `τ • r` back to `r`. Composing
-- with `τ` yields an element of the decomposition group of `r` restricting to `σ`.
/-- Lemma 15.111.11 (1): if `q = B ∩ r` is the contraction of a prime `r ⊂ C`, then under the
restriction map `Gal(M / K) → Gal(L / K)` the image of the decomposition group of `r` is the
decomposition group of `q`. -/
theorem restrictNormalHom_image_decompositionGroup_eq
    (r : Ideal C) [r.IsPrime]
    :
    Subgroup.map (restrictNormalHom L)
      (MulAction.stabilizer Gal(M / K) r) =
    MulAction.stabilizer Gal(L / K) (r.under B) := sorry

-- Proof sketch: use the same lifting argument as in clause `(1)`, but now compare the induced
-- actions on the residue fields. Lemma `15.111.10` gives surjectivity from the decomposition group
-- onto residue-field automorphisms, so the lift may be adjusted by an element of `Gal(M / L)`
-- acting trivially on the residue field at `r`, placing the adjusted lift in the inertia group.
/-- Lemma 15.111.11 (2): if `q = B ∩ r` is the contraction of a prime `r ⊂ C`, then under the
restriction map `Gal(M / K) → Gal(L / K)` the image of the inertia group of `r` is the inertia
group of `q`. -/
theorem restrictNormalHom_image_inertiaGroup_eq
    (r : Ideal C) [r.IsPrime]
    :
    Subgroup.map (restrictNormalHom L)
      (r.inertia Gal(M / K)) =
    (r.under B).inertia Gal(L / K) := sorry

end
