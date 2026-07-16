import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_160_1
import stacks_proof.stacks_project.Chap10.Lemma_10_39_10
import stacks_proof.stacks_project.Chap10.Lemma_10_96_3
import stacks_proof.stacks_project.Chap10.Lemma_10_97_3
import stacks_proof.stacks_project.Chap10.Lemma_10_97_6
import stacks_proof.stacks_project.Chap10.Lemma_10_97_7
import stacks_proof.stacks_project.Chap15.Definition_15_37_3

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

noncomputable section

universe u v

namespace RingHom

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A
local notation "BCompletion" => AdicCompletion (maximalIdeal B) B

local instance : IsNoetherianRing ACompletion :=
  adicCompletion_isNoetherianRing (maximalIdeal A)

local instance : IsNoetherianRing BCompletion :=
  adicCompletion_isNoetherianRing (maximalIdeal B)

/- Domain-style sampling for Lemma 15.40.3:
- primary domain: adic formal smoothness of local homomorphisms of Noetherian local rings and the
  resulting flatness criterion.
- sampled owner declarations:
  * `RingHom.formally_smooth_for_adic`
  * `RingHom.formally_smooth_for_adic_tfae_completion_invariance`
  * `adicCompletion_algebraMap_flat`
  * `exists_powerSeries_presentation_of_localHom_completeLocal`
- best owner abstraction: the primitive datum is the local ring map `f : A →+* B` itself, so the
  public statement should live on the owner `RingHom` and conclude with the canonical flatness
  predicate `f.Flat`, not with an auxiliary wrapper around the source and target rings.
- primitive data: the ring map `f`, the local/Noetherian hypotheses on `A` and `B`, and the
  maximal-ideal-adic formal smoothness hypothesis on `f`.
- derived API: flatness of `f`.

Source/core/bridge triage:
- `source-facing`: the Stacks-project implication from maximal-ideal-adic formal smoothness to
  flatness for a local homomorphism of Noetherian local rings;
- `core/canonical`: `RingHom.formally_smooth_for_adic` and `RingHom.Flat`;
- `bridge/view`: completion invariance, flatness of Noetherian adic completions, and the complete
  local power-series presentation from Lemma `15.39.3`.
-/

/-- Helper for Lemma 15.40.3: in the maximal-ideal completion of a Noetherian local ring, the
image of the original maximal ideal is maximal. -/
private theorem completion_map_maximalIdeal_isMaximal
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    Ideal.IsMaximal
      (Ideal.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) (maximalIdeal R)) := by
  letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
  letI : Field (R ⧸ (maximalIdeal R) ^ 1) := by
    let e : R ⧸ (maximalIdeal R) ^ 1 ≃+* R ⧸ maximalIdeal R :=
      Ideal.quotEquivOfEq (pow_one (maximalIdeal R))
    exact IsField.toField (e.toMulEquiv.isField (Field.toIsField _))
  -- Compare the extended maximal ideal with the kernel of the first completion evaluation map.
  have hker :
      Ideal.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) (maximalIdeal R) =
        RingHom.ker (AdicCompletion.evalₐ (maximalIdeal R) 1) := by
    simpa [pow_one] using
      completionIdeal_pow_eq_ker_evalₐ (maximalIdeal R)
        (Ideal.fg_of_isNoetherianRing (maximalIdeal R)) 1
  -- The first quotient of the completion is the residue field, so this kernel is maximal.
  simpa [hker] using
    (RingHom.ker_isMaximal_of_surjective
      (AdicCompletion.evalₐ (maximalIdeal R) 1)
      (AdicCompletion.surjective_evalₐ (maximalIdeal R) 1) :
        Ideal.IsMaximal (RingHom.ker (AdicCompletion.evalₐ (maximalIdeal R) 1)))

/-- Helper for Lemma 15.40.3: the maximal-ideal completion of a Noetherian local ring is again a
local ring. -/
private theorem completion_isLocalRing
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    IsLocalRing (AdicCompletion (maximalIdeal R) R) := by
  let hmax :
      Ideal.IsMaximal
        (Ideal.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) (maximalIdeal R)) :=
    completion_map_maximalIdeal_isMaximal R
  letI :
      Ideal.IsMaximal
        (Ideal.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) (maximalIdeal R)) :=
    hmax
  let hcomplete :
      IsAdicComplete
        (Ideal.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) (maximalIdeal R))
        (AdicCompletion (maximalIdeal R) R) :=
    (adicCompletion_isNoetherian_and_isAdicComplete (maximalIdeal R)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal R))).2
  letI :
      IsAdicComplete
        (Ideal.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) (maximalIdeal R))
        (AdicCompletion (maximalIdeal R) R) :=
    hcomplete
  -- A ring complete for a maximal ideal of definition is local.
  exact
    @isLocalRing_of_isAdicComplete_maximal
      (AdicCompletion (maximalIdeal R) R) _
      (Ideal.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) (maximalIdeal R))
      hmax hcomplete

/-- Helper for Lemma 15.40.3: in the maximal-ideal completion, the extended maximal ideal agrees
with the actual maximal ideal. -/
private theorem completion_map_maximalIdeal_eq_maximalIdeal
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsLocalRing (AdicCompletion (maximalIdeal R) R)] :
    Ideal.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) (maximalIdeal R) =
      maximalIdeal (AdicCompletion (maximalIdeal R) R) := by
  letI :
      Ideal.IsMaximal
        (Ideal.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) (maximalIdeal R)) :=
    completion_map_maximalIdeal_isMaximal R
  -- In a local ring every maximal ideal is the distinguished maximal ideal.
  exact IsLocalRing.eq_maximalIdeal inferInstance

/-- Helper for Lemma 15.40.3: the canonical map to the maximal-ideal completion is a local
homomorphism. -/
private theorem completion_isLocalHom
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    IsLocalHom (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
  letI : IsLocalRing (AdicCompletion (maximalIdeal R) R) := completion_isLocalRing R
  let φ : AdicCompletion (maximalIdeal R) R →+* R ⧸ maximalIdeal R :=
    (AdicCompletion.evalOneₐ (maximalIdeal R)).toRingHom
  have hcomp :
      φ.comp (algebraMap R (AdicCompletion (maximalIdeal R) R)) =
        Ideal.Quotient.mk (maximalIdeal R) := by
    ext x
    simp [φ]
  -- The quotient map to the residue field is local, so cancel through the surjective evaluation
  -- map to see that the completion map is local as well.
  haveI : IsLocalHom (Ideal.Quotient.mk (maximalIdeal R)) :=
    Function.Surjective.isLocalHom _ Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (φ.comp (algebraMap R (AdicCompletion (maximalIdeal R) R))) := by
    simpa [hcomp]
  exact isLocalHom_of_comp (algebraMap R (AdicCompletion (maximalIdeal R) R)) φ

/-- Helper for Lemma 15.40.3: the maximal-ideal completion is complete for its own maximal-ideal
adic topology. -/
private theorem completion_isAdicComplete_maximalIdeal
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsLocalRing (AdicCompletion (maximalIdeal R) R)] :
    IsAdicComplete
      (maximalIdeal (AdicCompletion (maximalIdeal R) R))
      (AdicCompletion (maximalIdeal R) R) := by
  -- Rewrite the defining ideal on the completion into the actual maximal ideal.
  simpa [completion_map_maximalIdeal_eq_maximalIdeal R] using
    (adicCompletion_isNoetherian_and_isAdicComplete (maximalIdeal R)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal R))).2

/-- Helper for Lemma 15.40.3: the maximal-ideal completion of a Noetherian local ring is a
complete local ring. -/
private theorem completion_isCompleteLocalRing
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    IsCompleteLocalRing (AdicCompletion (maximalIdeal R) R) := by
  letI : IsLocalRing (AdicCompletion (maximalIdeal R) R) := completion_isLocalRing R
  exact
    { toIsLocalRing := completion_isLocalRing R
      toIsAdicComplete := completion_isAdicComplete_maximalIdeal R }

/-- Helper for Lemma 15.40.3: once both source and target are complete local, the remaining
Stacks argument is the presentation-plus-splitting core. -/
private theorem flat_of_completeLocal_formallySmooth_for_maximalIdeal_adic
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [IsCompleteLocalRing R] [IsCompleteLocalRing S]
    (f : R →+* S)
    (hfs : f.formally_smooth_for_adic (maximalIdeal S)) :
    f.Flat := by
  -- TODO: choose the flat power-series presentation from Lemma `15.39.3`, quotient by
  -- `ker(P → A)`, split the induced surjection onto `S` using
  -- `exists_continuous_lift_of_formally_smooth_for_adic`, and conclude by `Module.Flat.of_retract`.
  sorry

/-- Helper for Lemma 15.40.3: once the target is already complete local, the remaining proof is
the source-faithful complete-target splitting argument from the Stacks proof. -/
private theorem flat_of_completeTarget_formallySmooth_for_maximalIdeal_adic
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [IsCompleteLocalRing S]
    (f : R →+* S) [IsLocalHom f]
    (hfs : f.formally_smooth_for_adic (maximalIdeal S)) :
    f.Flat := by
  letI : IsLocalRing (AdicCompletion (maximalIdeal R) R) := completion_isLocalRing R
  letI : IsCompleteLocalRing (AdicCompletion (maximalIdeal R) R) := completion_isCompleteLocalRing R
  letI : IsLocalRing (AdicCompletion (maximalIdeal S) S) := completion_isLocalRing S
  letI : IsCompleteLocalRing (AdicCompletion (maximalIdeal S) S) := completion_isCompleteLocalRing S
  -- First build the canonical comparison map on maximal-ideal completions.
  have hcont :
      letI : TopologicalSpace R := Ideal.adicTopology (maximalIdeal R)
      letI : TopologicalSpace S := Ideal.adicTopology (maximalIdeal S)
      Continuous f := by
    rw [RingHom.continuous_adic_iff_exists_pow_map_le]
    refine ⟨1, ?_⟩
    simpa [pow_one] using
      (Ideal.map_le_iff_le_comap.mpr (pow_maximalIdeal_le_comap_pow_maximalIdeal f 1))
  let fhat : AdicCompletion (maximalIdeal R) R →+* AdicCompletion (maximalIdeal S) S :=
    f.adicCompletionMap (maximalIdeal R) (maximalIdeal S) hcont
  -- Completion invariance transports the adic formal-smoothness hypothesis to `R^ -> S^`.
  have hTFAE :
      List.TFAE [
        f.formally_smooth_for_adic (maximalIdeal S),
        ((algebraMap S (AdicCompletion (maximalIdeal S) S)).comp f).formally_smooth_for_adic
          (Ideal.map (algebraMap S (AdicCompletion (maximalIdeal S) S)) (maximalIdeal S)),
        fhat.formally_smooth_for_adic
          (Ideal.map (algebraMap S (AdicCompletion (maximalIdeal S) S)) (maximalIdeal S))
      ] := by
    simpa [fhat] using
      RingHom.formally_smooth_for_adic_tfae_completion_invariance
        (maximalIdeal R) (Ideal.fg_of_isNoetherianRing (maximalIdeal R))
        (maximalIdeal S) (Ideal.fg_of_isNoetherianRing (maximalIdeal S))
        f hcont
  have hfhat_map :
      fhat.formally_smooth_for_adic
        (Ideal.map (algebraMap S (AdicCompletion (maximalIdeal S) S)) (maximalIdeal S)) :=
    (hTFAE.out 0 2).mp hfs
  have hcompletionIdeal :
      Ideal.map (algebraMap S (AdicCompletion (maximalIdeal S) S)) (maximalIdeal S) =
        maximalIdeal (AdicCompletion (maximalIdeal S) S) :=
    completion_map_maximalIdeal_eq_maximalIdeal S
  have hfhat :
      fhat.formally_smooth_for_adic (maximalIdeal (AdicCompletion (maximalIdeal S) S)) :=
    hcompletionIdeal ▸ hfhat_map
  -- Apply the complete-local core to the completed map.
  have hfhat_flat : fhat.Flat :=
    flat_of_completeLocal_formallySmooth_for_maximalIdeal_adic fhat hfhat
  let hsource_ff : (algebraMap R (AdicCompletion (maximalIdeal R) R)).FaithfullyFlat :=
    maximalIdeal_adicCompletion_algebraMap_faithfullyFlat R
  have hsource_flat : (algebraMap R (AdicCompletion (maximalIdeal R) R)).Flat := hsource_ff.flat
  let gS : AdicCompletion (maximalIdeal S) S →+* S :=
    (AdicCompletion.ofAlgEquiv (maximalIdeal S)).symm.toRingHom
  have hgS_flat : gS.Flat :=
    RingHom.Flat.of_bijective (AdicCompletion.ofAlgEquiv (maximalIdeal S)).symm.bijective
  have hgS_comp :
      gS.comp (algebraMap S (AdicCompletion (maximalIdeal S) S)) = RingHom.id S := by
    ext x
    change (AdicCompletion.ofAlgEquiv (maximalIdeal S)).symm (AdicCompletion.of (maximalIdeal S) S x) = x
    simpa using ofAlgEquiv_symm_of (maximalIdeal S) x
  -- The composite `R -> R^ -> S^ -> S` is exactly the original map `f`.
  have htotal :
      ((gS.comp fhat).comp (algebraMap R (AdicCompletion (maximalIdeal R) R))) = f := by
    calc
      ((gS.comp fhat).comp (algebraMap R (AdicCompletion (maximalIdeal R) R)))
          = gS.comp (fhat.comp (algebraMap R (AdicCompletion (maximalIdeal R) R))) := rfl
      _ = gS.comp ((algebraMap S (AdicCompletion (maximalIdeal S) S)).comp f) := by
            rw [RingHom.adicCompletionMap_comp]
      _ = (gS.comp (algebraMap S (AdicCompletion (maximalIdeal S) S))).comp f := rfl
      _ = (RingHom.id S).comp f := by rw [hgS_comp]
      _ = f := by
            ext x
            rfl
  -- Flatness is stable under composition, so the completed factorization gives flatness of `f`.
  have hmid_flat : (gS.comp fhat).Flat :=
    RingHom.Flat.comp hfhat_flat hgS_flat
  have htotal_flat :
      (((gS.comp fhat).comp (algebraMap R (AdicCompletion (maximalIdeal R) R)))).Flat :=
    RingHom.Flat.comp hsource_flat hmid_flat
  rw [htotal] at htotal_flat
  exact htotal_flat

-- Proof sketch: pass to the maximal-ideal completion of the target using the completion-invariance
-- result for adic formal smoothness. Once the completed target is flat over `A`, faithful
-- flatness of `B → B^∧` descends flatness back to the original map `A → B`.
/-- Lemma 15.40.3: a local homomorphism of Noetherian local rings which is formally smooth for the
`maximalIdeal B`-adic topology is flat. -/
@[stacks 07NP]
theorem flat_of_formallySmooth_for_maximalIdeal_adic
    (f : A →+* B) [IsLocalHom f]
    (hfs : f.formally_smooth_for_adic (maximalIdeal B)) :
    f.Flat := by
  letI : IsLocalRing BCompletion := completion_isLocalRing B
  letI : IsCompleteLocalRing BCompletion := completion_isCompleteLocalRing B
  have hlocalCompletion : IsLocalHom (algebraMap B BCompletion) := completion_isLocalHom B
  letI : Algebra A B := f.toAlgebra
  letI : Algebra B BCompletion := (algebraMap B BCompletion).toAlgebra
  letI : Algebra A BCompletion := ((algebraMap B BCompletion).comp f).toAlgebra
  haveI : IsLocalHom ((algebraMap B BCompletion).comp f) :=
    letI : IsLocalHom (algebraMap B BCompletion) := hlocalCompletion
    IsLocalHom.mk fun x hx_unit ↦ by
      have hfx_unit : IsUnit (f x) :=
        (isUnit_map_iff (algebraMap B BCompletion) (f x)).mp hx_unit
      exact (isUnit_map_iff f x).mp hfx_unit
  -- First transfer maximal-ideal-adic formal smoothness to the completed target.
  have hcont :
      letI : TopologicalSpace A := Ideal.adicTopology (maximalIdeal A)
      letI : TopologicalSpace B := Ideal.adicTopology (maximalIdeal B)
      Continuous f := by
    rw [RingHom.continuous_adic_iff_exists_pow_map_le]
    refine ⟨1, ?_⟩
    simpa [pow_one] using
      (Ideal.map_le_iff_le_comap.mpr (pow_maximalIdeal_le_comap_pow_maximalIdeal f 1))
  have hTFAE :
      List.TFAE [
        f.formally_smooth_for_adic (maximalIdeal B),
        ((algebraMap B BCompletion).comp f).formally_smooth_for_adic
          (Ideal.map (algebraMap B BCompletion) (maximalIdeal B)),
        RingHom.formally_smooth_for_adic
          (f.adicCompletionMap (maximalIdeal A) (maximalIdeal B) hcont)
          (Ideal.map (algebraMap B BCompletion) (maximalIdeal B))
      ] := by
    simpa using
      RingHom.formally_smooth_for_adic_tfae_completion_invariance
        (maximalIdeal A) (Ideal.fg_of_isNoetherianRing (maximalIdeal A))
        (maximalIdeal B) (Ideal.fg_of_isNoetherianRing (maximalIdeal B))
        f hcont
  have hcompletion_map :
      ((algebraMap B BCompletion).comp f).formally_smooth_for_adic
        (Ideal.map (algebraMap B BCompletion) (maximalIdeal B)) :=
    (hTFAE.out 0 1).mp hfs
  have hflat_completion :
      ((algebraMap B BCompletion).comp f).Flat := by
    have hcompletionIdeal :
        Ideal.map (algebraMap B BCompletion) (maximalIdeal B) =
          maximalIdeal BCompletion :=
      completion_map_maximalIdeal_eq_maximalIdeal B
    have hcompletion_map_maximal :
        ((algebraMap B BCompletion).comp f).formally_smooth_for_adic
          (maximalIdeal BCompletion) :=
      hcompletionIdeal ▸ hcompletion_map
    -- Rewrite the completed target into its canonical maximal ideal and apply the complete-target
    -- helper.
    have hflat_target :
        ((algebraMap B BCompletion).comp f).Flat :=
      flat_of_completeTarget_formallySmooth_for_maximalIdeal_adic
        (((algebraMap B BCompletion).comp f)) hcompletion_map_maximal
    exact hflat_target
  -- View `B^∧` as a flat `A`-module, then descend along the faithfully flat completion map.
  have hmoduleFlat : Module.Flat A BCompletion := by
    have halgebraMap_flat : (algebraMap A BCompletion).Flat := by
      simpa [RingHom.algebraMap_toAlgebra] using hflat_completion
    exact RingHom.flat_algebraMap_iff.mp halgebraMap_flat
  let hfaithful :
      RingHom.FaithfullyFlat (algebraMap B BCompletion) :=
    maximalIdeal_adicCompletion_algebraMap_faithfullyFlat B
  letI : Module.Flat A BCompletion := hmoduleFlat
  have hmoduleFlatRestrict : Module.Flat A (RestrictScalars A B BCompletion) := by
    simpa using hmoduleFlat
  letI : Module.Flat A (RestrictScalars A B BCompletion) := hmoduleFlatRestrict
  letI : Module.FaithfullyFlat B BCompletion :=
    RingHom.faithfullyFlat_algebraMap_iff.mp hfaithful
  -- The descent owner theorem now returns flatness of the original algebra map `A → B = f`.
  have hflatAB : (algebraMap A B).Flat :=
    algebraMap_flat_of_flat_of_faithfullyFlat BCompletion
  simpa [RingHom.algebraMap_toAlgebra] using hflatAB

end

end RingHom
