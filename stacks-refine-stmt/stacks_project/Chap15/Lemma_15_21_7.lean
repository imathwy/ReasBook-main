import stacks_project.Chap10.Lemma_10_77_7
import stacks_project.Chap15.Lemma_15_21_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [Module.Finite R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

/- Domain triage:
- primary domain: descent of projective modules under finite injective base change over
  Noetherian commutative rings;
- sampled owner declarations of the same kind:
  `Module.Projective`,
  `Module.projective_iff_flat_mittagLeffler_and_isDirectSumOfCountablyGenerated`,
  `Module.Flat.of_projective`,
  `flat_of_isNoetherianRing_of_moduleFinite_of_injective_algebraMap_of_flat_tensorProduct`,
  `projective_of_projective_quotient_of_isNilpotent_of_flat`;
- best owner abstraction: the canonical owner predicate `Module.Projective R M`;
- primitive data: the Noetherian base ring `R`, the finite `R`-algebra `S`, the injective
  algebra map `R → S`, and the `R`-module `M`;
- derived API: the descended projectivity of `M`, stated directly in terms of the owner predicate
  rather than via a parallel wrapper for the textbook module `M ⊗_R S`.

Layering:
- this numbered item is `source-facing`: it is the textbook finite-injective descent statement;
- `core/canonical`: `Module.Projective`, together with the flatness owner
  `flat_of_isNoetherianRing_of_moduleFinite_of_injective_algebraMap_of_flat_tensorProduct`, the
  projective-to-flat bridge `Module.Flat.of_projective`, and the Chapter 10 nilpotent-thickening
  descent theorem
  `projective_of_projective_quotient_of_isNilpotent_of_flat`;
- no separate `bridge/view` owner is warranted here: the source-facing statement already lands
  directly in the canonical owner predicate `Module.Projective`.
-/

-- Proof sketch: projective modules are flat, so
-- `flat_of_isNoetherianRing_of_moduleFinite_of_injective_algebraMap_of_flat_tensorProduct`
-- descends flatness of `M` from `hproj`. After the same finite locally free reduction used in
-- Lemmas `15.21.3` and `15.21.4`, one gets a nilpotent ideal `I` such that `M / IM` is
-- projective over `R ⧸ I`; the Chapter 10 projective descent theorem
-- `projective_of_projective_quotient_of_isNilpotent_of_flat` then finishes.
/-- Lemma 15.21.7: let `R → S` be a finite injective homomorphism of Noetherian rings, and let
`M` be an `R`-module. If the base change `S ⊗[R] M` is projective over `S`, then `M` is
projective over `R`. This is the canonical Lean form of the textbook statement for
`M ⊗_R S`, and it remains a source-facing Chapter 15 theorem rather than a renamed wrapper around
an upstream owner theorem with different hypotheses. -/
theorem projective_of_isNoetherianRing_of_moduleFinite_of_injective_algebraMap_of_projective_tensorProduct
    (hinj : Function.Injective (algebraMap R S))
    (hproj : Module.Projective S (S ⊗[R] M)) :
    Module.Projective R M := by
  letI : Module.Projective S (S ⊗[R] M) := hproj
  have hflatTensor : Module.Flat S (S ⊗[R] M) := Module.Flat.of_projective
  have hflat : Module.Flat R M :=
    flat_of_isNoetherianRing_of_moduleFinite_of_injective_algebraMap_of_flat_tensorProduct
      hinj hflatTensor
  sorry

end
