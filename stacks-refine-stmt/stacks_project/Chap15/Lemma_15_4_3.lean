import Mathlib
import stacks_project.Chap10.Lemma_10_51_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

open scoped Pointwise

section

variable {A : Type u} {B : Type x} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

namespace LinearMap

/- Domain-style sampling:
- primary domain: Artin-Rees bounds for linear maps under flat scalar extension;
- sampled declarations: `LinearMap.IsArtinReesBound`,
  `LinearMap.isArtinReesBound_of_preimage_pow_smul_eq`, `LinearMap.baseChange`,
  and `Module.Flat.lTensor_exact`;
- core/canonical owner: `LinearMap.IsArtinReesBound`;
- source-facing content: the Stacks lemma that the same Artin-Rees constant survives flat base
  change;
- bridge/view target here: a base-change theorem for the owner-level predicate, not a parallel
  stronger reformulation in terms of preimage equalities. -/

-- Proof sketch: tensor the exact sequence computing the Artin-Rees quotient by `B`, use flatness
-- to preserve the relevant intersections and kernels, rewrite `I.map (algebraMap A B) ^ n` as the
-- base change of `I ^ n`, and identify the image term with the corresponding image for
-- `f.baseChange B`.
/-- Lemma 15.4.3: if `c` is an Artin-Rees bound for `f` with respect to `I`, then after flat base
change along `A → B` the same `c` is an Artin-Rees bound for `f.baseChange B` with respect to
`I.map (algebraMap A B)`. -/
theorem IsArtinReesBound.baseChange {f : M →ₗ[A] N} {I : Ideal A} {c : ℕ}
    (hc : f.IsArtinReesBound I c) :
    (f.baseChange B).IsArtinReesBound (I.map (algebraMap A B)) c := sorry

end LinearMap

end
