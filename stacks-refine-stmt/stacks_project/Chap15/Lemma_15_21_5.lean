import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Defs

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [Module.Finite R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

/- Domain triage:
- primary domain: flatness descent for modules under finite injective base change over Noetherian
  rings;
- sampled owner declarations of the same kind:
  `Module.Flat`,
  `flat_of_nilpotent_ideal_of_injective_algebraMap_of_flat_mod_ideal_and_flat_baseChange`,
  `flat_of_isArtinianRing_of_injective_algebraMap_of_flat_tensorProduct`,
  `Module.Flat.of_flat_tensorProduct`;
- best owner abstraction: the canonical flatness predicate `Module.Flat`, with the Chapter 10
  nilpotent-ideal descent criterion as the upstream owner theorem in the minimal dependency
  closure;
- primitive data: the Noetherian base ring `R`, the finite `R`-algebra `S`, the injective algebra
  map `R → S`, and the `R`-module `M`;
- derived API: flatness of the base-changed module `S ⊗[R] M`, expressed in the canonical Lean
  model of base change rather than through a parallel wrapper or renamed tensor-product owner.

Layering:
- this item is `source-facing`: it is the Noetherian finite-extension descent statement from the
  source text;
- `core/canonical`: `Module.Flat` and the Chapter 10 owner theorem
  `flat_of_nilpotent_ideal_of_injective_algebraMap_of_flat_mod_ideal_and_flat_baseChange`;
- companion source-facing specialization already upstream:
  `flat_of_isArtinianRing_of_injective_algebraMap_of_flat_tensorProduct`;
- no separate `bridge/view` declaration is warranted here.
-/

-- Proof sketch: after a finite locally free base change reducing to the split polynomial-quotient
-- case of Lemmas `15.21.3` and `15.21.4`, one obtains a nilpotent ideal `I ⊆ R` such that
-- `M / IM` is flat over `R ⧸ I`. Then apply the nilpotent-ideal descent criterion
-- `10.101.5`, using injectivity of `R → S` and the assumed flatness of `S ⊗[R] M`.
/-- Lemma 15.21.5: let `R → S` be a finite injective homomorphism of Noetherian rings, and let
`M` be an `R`-module. If the base change `S ⊗[R] M` is flat over `S`, then `M` is flat over `R`.
This is the canonical Lean form of the textbook statement for `M ⊗_R S`, and it remains a
source-facing Chapter 15 theorem rather than a renamed wrapper around the Chapter 10 owner
criterion. -/
theorem flat_of_isNoetherianRing_of_moduleFinite_of_injective_algebraMap_of_flat_tensorProduct
    (hinj : Function.Injective (algebraMap R S))
    (hflat : Module.Flat S (S ⊗[R] M)) :
    Module.Flat R M := sorry

end
