import StacksProject_2024.Chap10.Theorem_10_95_6
import StacksProject_2024.Chap10.Lemma_10_97_3
import StacksProject_2024.Chap10.Lemma_10_97_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {I : Ideal R}
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M]

omit [IsNoetherianRing R] [Module.Finite R M] [Module.Flat R M] in
private theorem descendProjectiveOfProjectiveCompletionTensor
    [Module.FaithfullyFlat R (AdicCompletion I R)]
    (h : Module.Projective (AdicCompletion I R) ((AdicCompletion I R) ⊗[R] M)) :
    Module.Projective R M :=
  @Module.Projective.of_projective_tensorProduct_of_faithfullyFlat
    R _ M _ _ (AdicCompletion I R) _ _ inferInstance h

/- Domain triage:
- primary domain: projective descent for finite flat modules across Jacobson-radical thickenings,
  organized through adic completion and faithfully flat descent;
- sampled owner declarations of the same kind:
  `Module.Projective`,
  `Module.Projective.of_projective_tensorProduct_of_faithfullyFlat`,
  `adicCompletion_algebraMap_faithfullyFlat_of_le_jacobson`,
  `completionMap_has_section_of_flat_of_projective_quotient`;
- best owner abstraction: the canonical predicate `Module.Projective R M`, with the completion map
  and quotient-projective lifting results treated as bridge API rather than parallel public owners;
- primitive data: the Noetherian commutative ring `R`, the ideal `I`, the finite flat `R`-module
  `M`, and projectivity of the reduction `M ⧸ (I • ⊤)` over `R ⧸ I`;
- derived API: projectivity of the completed base change of `M`, then projectivity of `M` itself
  by faithfully flat descent along the `I`-adic completion.

Layer classification:
- `source-facing`: the Jacobson-radical lifting criterion from the text;
- `core/canonical`: `Module.Projective R M`;
- `bridge/view`: the quotient module `M ⧸ (I • ⊤)` over `R ⧸ I` and the completed surjection
  supplied by `completionMap_has_section_of_flat_of_projective_quotient`.
-/

-- Proof sketch: choose a surjection `P → M` from a finite free module. Lemma `10.97.9` upgrades
-- the projectivity of `M / IM` to a section of the induced surjection on `I`-adic completions, so
-- `AdicCompletion I M` is projective over `AdicCompletion I R`. The canonical tensor/completion
-- equivalence `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian` identifies this with the
-- completed base change `(AdicCompletion I R) ⊗[R] M`, and faithfully flat descent along the
-- completion map finishes the proof via
-- `Module.Projective.of_projective_tensorProduct_of_faithfullyFlat`.
/-- Lemma 15.3.4: if `R` is Noetherian, `I` is contained in the Jacobson radical of `R`, `M` is
a finite flat `R`-module, and the quotient `M / IM` is projective over `R ⧸ I`, then `M` is
projective over `R`; since finiteness is already an ambient hypothesis, this is exactly the
finite-projective conclusion of the textbook statement. -/
theorem projective_of_projective_quotient_of_le_ring_jacobson
    (hI : I ≤ Ring.jacobson R)
    (hquot : Module.Projective (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))) :
    Module.Projective R M := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  letI : Module.FaithfullyFlat R (AdicCompletion I R) :=
    RingHom.faithfullyFlat_algebraMap_iff.mp
      (adicCompletion_algebraMap_faithfullyFlat_of_le_jacobson I hI)
  letI : Module.Free (AdicCompletion I R) (AdicCompletion I R) :=
    Module.Free.self (AdicCompletion I R)
  letI : Module.Projective (AdicCompletion I R) (AdicCompletion I R) := Module.Projective.of_free
  letI : Module.Projective R (Fin n → R) := Module.Projective.of_free
  letI : Module.Projective (AdicCompletion I R) ((AdicCompletion I R) ⊗[R] (Fin n → R)) :=
    Module.Projective.tensorProduct
  letI : Module.Projective (AdicCompletion I R) (AdicCompletion I (Fin n → R)) :=
    Module.Projective.of_equiv'
      (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I (Fin n → R))
  obtain ⟨s, hs⟩ :=
    completionMap_has_section_of_flat_of_projective_quotient I π hπ hquot
  letI : Module.Projective (AdicCompletion I R) (AdicCompletion I M) :=
    Module.Projective.of_split s (AdicCompletion.map I π) hs
  have htensor : Module.Projective (AdicCompletion I R) ((AdicCompletion I R) ⊗[R] M) :=
    Module.Projective.of_equiv'
      (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M).symm
  exact descendProjectiveOfProjectiveCompletionTensor htensor

end
