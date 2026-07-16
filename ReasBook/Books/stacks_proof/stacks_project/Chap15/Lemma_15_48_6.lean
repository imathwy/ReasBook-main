import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_110_7
import stacks_proof.stacks_project.Chap10.Definition_10_160_1
import stacks_proof.stacks_project.Chap10.Lemma_10_160_11
import stacks_proof.stacks_project.Chap15.Definition_15_47_1
import stacks_proof.stacks_project.Chap15.Lemma_15_47_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

/- Domain-style sampling:
- primary domain: Noetherian complete local domains, the chapter owner `IsJ0Ring`, and the
  finite regular complete-local subring / fraction-field descent machinery used to prove openness
  of the regular locus;
- sampled owner and bridge declarations of the same kind:
  `IsJ0Ring`,
  `PrimeSpectrum.regularLocus`,
  `exists_finite_regular_completeLocalSubring`,
  `Algebra.isJ0Ring_of_injective_finiteType_of_separable_fractionRingExtension`;
- best owner abstraction: the public statement should stay on the chapter owner `IsJ0Ring`,
  with the finite complete-local subring and the separable/purely inseparable fraction-field
  analysis kept internal to the proof route;
- source/core/bridge triage:
  * source-facing: the conclusion that a Noetherian complete local domain is `J-0`;
  * core/canonical: the chapter owner `IsJ0Ring`;
  * bridge/view: the finite regular complete local subring from Cohen structure, the separability
    bridge on fraction fields, and the purely inseparable derivation/adjoin-root regularity step;
- primitive vs. derived: the primitive public data are exactly the ambient assumptions
  `[IsNoetherianRing A]`, `[IsCompleteLocalRing A]`, and `[IsDomain A]`. The finite regular
  complete local subring, the separable versus purely inseparable case split on the fraction
  field extension, and the derivation witness used in the purely inseparable branch are all
  derived implementation data supplied by the chapter bridge lemmas, so this file should keep
  the public surface on `IsJ0Ring A` rather than introducing a parallel wrapper API.
-/

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsCompleteLocalRing A] [IsDomain A]

/-- Helper for Lemma 15.48.6: the algebra map from a subring of a domain into the ambient ring is
injective. -/
private theorem subring_algebraMap_injective (R₀ : Subring A) :
    Function.Injective (algebraMap R₀ A) := by
  -- The canonical algebra map is the subtype inclusion, so injectivity is immediate.
  intro x y hxy
  exact Subtype.ext hxy

/-- Helper for Lemma 15.48.6: a regular complete local subring already supplies the complete-local
source witness needed for the textbook induction. -/
private theorem completeLocal_source_witness_of_regular_subring
    (R₀ : Subring A) [IsCompleteLocalRing R₀] [IsRegularLocalRing R₀] :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsNoetherianRing R) (_ : IsCompleteLocalRing R)
      (_ : Algebra R R₀), Algebra.FiniteType R R₀ := by
  -- The source proof may take the regular complete local subring itself as the complete-local
  -- source; only finite type over that source is needed here.
  letI : IsRegularRing R₀ := inferInstance
  letI : IsNoetherianRing R₀ := IsRegularRing.toIsNoetherian
  refine ⟨R₀, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  infer_instance

/-- Helper for Lemma 15.48.6: Cohen structure yields a finite regular complete local subring that
is already `J-0` and carries the required source witness. -/
private theorem exists_finite_j0_completeLocalSubring :
    ∃ (R₀ : Subring A) (_ : IsCompleteLocalRing R₀) (_ : IsRegularLocalRing R₀)
      (_ : Module.Finite R₀ A) (_ : IsJ0Ring R₀),
      ∃ (R : Type u) (_ : CommRing R) (_ : IsNoetherianRing R) (_ : IsCompleteLocalRing R)
        (_ : Algebra R R₀), Algebra.FiniteType R R₀ := by
  -- Choose the finite regular complete local subring from Cohen structure.
  obtain ⟨R₀, hcomplete, hregular, _, _, hfinite, _⟩ :=
    exists_finite_regular_completeLocalSubring (R := A)
  letI : IsCompleteLocalRing R₀ := hcomplete
  letI : IsRegularLocalRing R₀ := hregular
  letI : IsRegularRing R₀ := inferInstance
  letI : IsJ0Ring R₀ := isJ0Ring_of_isRegularRing R₀
  -- Regularity gives the initial `J-0` input, and the subring itself is a valid source ring.
  refine ⟨R₀, hcomplete, hregular, hfinite, inferInstance, ?_⟩
  exact completeLocal_source_witness_of_regular_subring (A := A) R₀

/-- Helper for Lemma 15.48.6: the separable fraction-field branch of the source proof follows
directly from Lemma `15.47.5` once the base subring is regular. -/
private theorem isJ0Ring_of_separable_fractionField_extension
    (R₀ : Subring A) [IsCompleteLocalRing R₀] [IsRegularLocalRing R₀] [Module.Finite R₀ A]
    (hsep :
      Algebra.fractionRingIsSeparableOver
        (R := R₀) (S := A) (subring_algebraMap_injective (A := A) R₀)) :
    IsJ0Ring A := by
  letI : IsRegularRing R₀ := inferInstance
  letI : IsJ0Ring R₀ := isJ0Ring_of_isRegularRing R₀
  -- This is exactly the previously proved separable finite-type ascent theorem.
  exact
    Algebra.isJ0Ring_of_injective_finiteType_of_separable_fractionRingExtension
      (R := R₀) (S := A) (subring_algebraMap_injective (A := A) R₀) hsep

/-- Helper for Lemma 15.48.6: after choosing a finite `J-0` source inside `A`, the remaining work
is the source-proof fraction-field analysis combining the separable case, intermediate subfields,
and the terminal purely inseparable degree-`p` step. -/
private theorem isJ0Ring_of_moduleFinite_from_j0_source_nonseparable
    {B : Type v} [CommRing B] [IsDomain B] [Algebra B A] [Module.Finite B A] [IsJ0Ring B]
    (hinj : Function.Injective (algebraMap B A))
    (hsource :
      ∃ (R : Type v) (_ : CommRing R) (_ : IsNoetherianRing R) (_ : IsCompleteLocalRing R)
        (_ : Algebra R B), Algebra.FiniteType R B)
    (hnotsep :
      ¬ Algebra.fractionRingIsSeparableOver
        (R := B) (S := A) hinj) :
    IsJ0Ring A := by
  -- TODO: follow the source-proof nonseparable branch. First recurse through a proper
  -- intermediate fraction field via the canonical intersection ring `A ∩ M`; if there is no
  -- proper intermediate field, use the purely inseparable degree-`p` presentation, Lemmas
  -- `15.48.5` and `15.48.4`, and then transfer the resulting `J-0` adjoin-root model back to `A`.
  let _ := hsource
  let _ := hnotsep
  sorry

/-- Helper for Lemma 15.48.6: after choosing a finite `J-0` source inside `A`, the separable
fraction-field branch is already closed, so only the source-proof nonseparable branch remains. -/
private theorem isJ0Ring_of_moduleFinite_from_j0_source
    {B : Type v} [CommRing B] [IsDomain B] [Algebra B A] [Module.Finite B A] [IsJ0Ring B]
    (hinj : Function.Injective (algebraMap B A))
    (hsource :
      ∃ (R : Type v) (_ : CommRing R) (_ : IsNoetherianRing R) (_ : IsCompleteLocalRing R)
        (_ : Algebra R B), Algebra.FiniteType R B) :
    IsJ0Ring A := by
  -- Route correction: isolate the source-proof case split at the fraction-field level before
  -- introducing the intermediate-field and degree-`p` machinery.
  by_cases hsep :
      Algebra.fractionRingIsSeparableOver
        (R := B) (S := A) hinj
  · -- In the separable branch, Lemma `15.47.5` already gives the required `J-0` ascent.
    exact
      Algebra.isJ0Ring_of_injective_finiteType_of_separable_fractionRingExtension
        (R := B) (S := A) hinj hsep
  · -- The remaining source-faithful work is exactly the nonseparable branch isolated above.
    exact isJ0Ring_of_moduleFinite_from_j0_source_nonseparable
      (A := A) (B := B) hinj hsource hsep

-- Proof sketch: choose a finite regular complete local subring `A₀ ⊆ A` using
-- Lemma `10.160.11`.
-- If the induced fraction-field extension is separable, apply Lemma `15.47.5` to descend `J-0`
-- from the regular ring `A₀`. Otherwise, pass to a minimal purely inseparable subextension,
-- produce a derivation on the intermediate ring by Lemma `15.48.5`, and apply Lemma `15.48.4` to
-- obtain regularity on a nonempty open subset of `Spec A`; since the intermediate ring is already
-- `J-0`, this yields `IsJ0Ring A`.
/-- Lemma 15.48.6: a Noetherian complete local domain is `J-0`. -/
@[stacks 07PI]
theorem isJ0Ring_of_noetherian_completeLocalDomain : IsJ0Ring A := by
  -- Route correction: the first concrete step is to reduce to a finite `J-0` regular complete
  -- local subring; the unresolved part is the source-proof fraction-field induction from that
  -- subring to `A`.
  obtain ⟨R₀, hcomplete, hregular, hfinite, hJ0, hsource⟩ :=
    exists_finite_j0_completeLocalSubring (A := A)
  letI : IsCompleteLocalRing R₀ := hcomplete
  letI : IsRegularLocalRing R₀ := hregular
  letI : Module.Finite R₀ A := hfinite
  letI : IsJ0Ring R₀ := hJ0
  -- With the Cohen-structure source in hand, the remaining source-faithful argument is delegated
  -- to the structural helper.
  exact isJ0Ring_of_moduleFinite_from_j0_source
    (A := A) (B := R₀) (subring_algebraMap_injective (A := A) R₀) hsource

end
