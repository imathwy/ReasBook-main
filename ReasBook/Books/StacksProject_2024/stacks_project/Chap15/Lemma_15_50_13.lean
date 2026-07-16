import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_127_9
import StacksProject_2024.stacks_project.Chap10.Lemma_10_154_8
import StacksProject_2024.stacks_project.Chap10.Lemma_10_155_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_155_6
import StacksProject_2024.stacks_project.Chap15.Definition_15_50_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_12_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_50_8
import StacksProject_2024.stacks_project.Chap15.Proposition_15_50_10
import StacksProject_2024.stacks_project.Chap15.Proposition_15_50_12

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open IsLocalRing
open RingPairCat

universe u

section

variable (A : Type u) [CommRing A]

variable [HenselianLocalRing A]

local instance : henselianPairInclusion.IsRightAdjoint :=
  henselianPairInclusion_isRightAdjoint

local notation "A_pair" => pairOfIdeal (maximalIdeal A)
local notation "A_h" => henselizationRing A_pair

/-- Helper for Lemma 15.50.13: a ring hom out of a ring pair that carries the distinguished ideal
into a target ideal induces the corresponding morphism of ring pairs. -/
private theorem ringPair_toIdealPair_hom_square {X : RingPairCat.{u}}
    {B : Type u} [CommRing B] [Algebra X.ring B] (K : Ideal B)
    (hXK : X.ideal ≤ Ideal.comap (algebraMap X.ring B) K) :
    CommRingCat.ofHom (algebraMap X.ring B) ≫
        CommRingCat.ofHom (Ideal.Quotient.mk K) =
      CommRingCat.ofHom (Ideal.Quotient.mk X.ideal) ≫
        CommRingCat.ofHom (Ideal.quotientMap K (algebraMap X.ring B) hXK) := by
  -- Proof comment: `Ideal.quotientMap` is defined so that both composites are the same quotient
  -- map on representatives.
  ext x
  rfl

/-- Helper for Lemma 15.50.13: package a ring hom together with ideal containment as a morphism
of ring pairs into `(B, K)`. -/
private abbrev ringPairToIdealPairMap {X : RingPairCat.{u}}
    {B : Type u} [CommRing B] [Algebra X.ring B] (K : Ideal B)
    (hXK : X.ideal ≤ Ideal.comap (algebraMap X.ring B) K) :
    X ⟶ pairOfIdeal K :=
  InducedCategory.homMk <|
    Arrow.homMk'
      (CommRingCat.ofHom (algebraMap X.ring B))
      (CommRingCat.ofHom (Ideal.quotientMap K (algebraMap X.ring B) hXK))
      (ringPair_toIdealPair_hom_square (K := K) hXK)

/-- Helper for Lemma 15.50.13: maps from a chosen pair henselization into a henselian target pair
are uniquely determined by their restriction to the source ring. -/
private theorem existsUnique_henselizationRingHom_of_henselian_target
    {A B : Type u} [CommRing A] [CommRing B] (I : Ideal A) [Algebra A B]
    (K : Ideal B) (hK : HenselianRing B K)
    (hIK : I ≤ Ideal.comap (algebraMap A B) K) :
    ∃! g : henselizationRing (pairOfIdeal I) →+* B,
      g.comp (toHenselization (pairOfIdeal I)) = algebraMap A B := by
  let adj := Adjunction.ofIsRightAdjoint henselianPairInclusion
  let target : HenselianPairCat.{u} := ⟨pairOfIdeal K, hK⟩
  let pairMap : pairOfIdeal I ⟶ henselianPairInclusion.obj target :=
    pairOfIdealMap I K hIK
  let comparison : henselization (pairOfIdeal I) ⟶ target :=
    (adj.homEquiv (pairOfIdeal I) target).symm pairMap
  have hcomparison :
      adj.homEquiv (pairOfIdeal I) target comparison = pairMap := by
    exact Equiv.apply_symm_apply (adj.homEquiv (pairOfIdeal I) target) pairMap
  refine ⟨RingPairCat.ringHom comparison.hom, ?_, ?_⟩
  · -- Proof comment: the adjunction unit identity says the transpose extends the source map.
    have hunit :
        pairMap = (adj.unit.app (pairOfIdeal I)) ≫ comparison.hom := by
      calc
        pairMap = adj.homEquiv (pairOfIdeal I) target comparison := hcomparison.symm
        _ = (adj.unit.app (pairOfIdeal I)) ≫ comparison.hom :=
          adj.homEquiv_unit (X := pairOfIdeal I) (Y := target) (f := comparison)
    have hunitRing := congrArg
      (fun k :
          pairOfIdeal I ⟶ henselianPairInclusion.obj target ↦
            RingPairCat.ringHom k) hunit
    simpa [pairMap, RingPairCat.toHenselization, RingPairCat.ringHom] using
      hunitRing.symm
  · intro g hg
    -- Proof comment: package `g` as a pair morphism to the henselian target and compare its
    -- adjoint transpose with the original source map.
    letI : Algebra (henselizationRing (pairOfIdeal I)) B := g.toAlgebra
    have hmap :
        henselizationIdeal (pairOfIdeal I) ≤ Ideal.comap g K := by
      rw [henselizationIdeal_eq_map (X := pairOfIdeal I), Ideal.map_le_iff_le_comap,
        Ideal.comap_comap]
      simpa [hg] using hIK
    let liftedPairMap :
        henselizationPair (pairOfIdeal I) ⟶ henselianPairInclusion.obj target :=
      ringPairToIdealPairMap (X := henselizationPair (pairOfIdeal I)) K hmap
    let lifted : henselization (pairOfIdeal I) ⟶ target :=
      ObjectProperty.homMk liftedPairMap
    have hpair :
        (adj.unit.app (pairOfIdeal I)) ≫ liftedPairMap = pairMap := by
      apply RingPairCat.hom_ext
      simpa [pairMap, liftedPairMap, RingPairCat.toHenselization, RingPairCat.ringHom] using hg
    have htranspose :
        adj.homEquiv (pairOfIdeal I) target lifted = pairMap := by
      exact (adj.homEquiv_unit (X := pairOfIdeal I) (Y := target) (f := lifted)).trans hpair
    have hlifted : lifted = comparison := by
      apply (adj.homEquiv (pairOfIdeal I) target).injective
      calc
        adj.homEquiv (pairOfIdeal I) target lifted = pairMap := htranspose
        _ = adj.homEquiv (pairOfIdeal I) target comparison := hcomparison.symm
    exact congrArg RingPairCat.ringHom <|
      congrArg (fun k : henselization (pairOfIdeal I) ⟶ target ↦ k.hom) hlifted

/-- Helper for Lemma 15.50.13: a henselian local ring is a henselization of itself via the
identity map. -/
lemma henselian_self_is_henselization :
    IsHenselizationOf A A := by
  -- Proof comment: the identity map is local, preserves the maximal ideal, and is a trivial
  -- filtered colimit of etale algebras.
  refine
    { toHenselianLocalRing := inferInstance
      toIsLocalHom := by
        simpa using (show IsLocalHom (algebraMap A A) by infer_instance)
      isFilteredColimitOfEtale := ?_
      map_maximalIdeal := by
        simp
      residueField_bijective := by
        simpa using (RingEquiv.refl (ResidueField A)).bijective }
  have hEtale :
      CommRingCat.etale (CommRingCat.ofHom (algebraMap (ULift A) (ULift A))) := by
    -- Proof comment: the identity map is bijective, hence etale.
    dsimp [CommRingCat.etale]
    exact RingHom.Etale.of_bijective (by simpa using (RingEquiv.refl (ULift A)).bijective)
  dsimp [RingHom.IsFilteredColimitOfEtale]
  exact CategoryTheory.MorphismProperty.le_ind (P := CommRingCat.etale) _ hEtale

/-- Helper for Lemma 15.50.13: the finite `ℤ`-subalgebra of `A` generated by a chosen finite set.
-/
private abbrev z_adjoin_stage (s : Finset A) : Subalgebra ℤ A :=
  Algebra.adjoin ℤ (↑s : Set A)

/-- Helper for Lemma 15.50.13: the prime of a finite `ℤ`-stage lying under the closed point of
`A`. -/
private abbrev z_adjoin_prime (s : Finset A) :
    Ideal (z_adjoin_stage (A := A) s) :=
  Ideal.comap
    (algebraMap (z_adjoin_stage (A := A) s) A)
    (maximalIdeal A)

/-- Helper for Lemma 15.50.13: the localized finite `ℤ`-stage from the source proof. -/
private abbrev z_adjoin_local_stage (s : Finset A) : Type u :=
  Localization.AtPrime (z_adjoin_prime (A := A) s)

/-- Helper for Lemma 15.50.13: enlarging the finite generating set enlarges the underlying
`ℤ`-subalgebra. -/
private lemma z_adjoin_stage_mono
    {s t : Finset A} (hst : s ⊆ t) :
    z_adjoin_stage (A := A) s ≤ z_adjoin_stage (A := A) t := by
  -- Proof comment: monotonicity of `Algebra.adjoin` is the exact stage-growth relation from the
  -- source proof.
  exact Algebra.adjoin_mono (show (↑s : Set A) ⊆ (↑t : Set A) from hst)

/-- Helper for Lemma 15.50.13: the canonical map from a localized finite stage to the target
henselian local ring. -/
private noncomputable abbrev z_adjoin_local_stage_to_target
    (s : Finset A) :
    z_adjoin_local_stage (A := A) s →+* A :=
  Localization.localRingHom
    (z_adjoin_prime (A := A) s)
    (maximalIdeal A)
    (algebraMap (z_adjoin_stage (A := A) s) A)
    rfl

/-- Helper for Lemma 15.50.13: the prime under the closed point is preserved when passing to a
larger finite stage. -/
private lemma z_adjoin_prime_comap
    {s t : Finset A} (hst : s ⊆ t) :
    Ideal.comap
        ((Subalgebra.inclusion (z_adjoin_stage_mono (A := A) hst)).toRingHom)
        (z_adjoin_prime (A := A) t) =
      z_adjoin_prime (A := A) s := by
  -- Proof comment: the stage inclusion is literally the identity on the underlying elements of
  -- `A`, so contracting the closed-point prime does not change it.
  ext x
  change
    algebraMap (z_adjoin_stage (A := A) t) A
        ((Subalgebra.inclusion (z_adjoin_stage_mono (A := A) hst)) x) ∈
      maximalIdeal A ↔
      algebraMap (z_adjoin_stage (A := A) s) A x ∈ maximalIdeal A
  rfl

/-- Helper for Lemma 15.50.13: enlarging the finite generating set induces the localized stage
transition map. -/
private noncomputable abbrev z_adjoin_local_stage_transition
    {s t : Finset A} (hst : s ⊆ t) :
    z_adjoin_local_stage (A := A) s →+*
      z_adjoin_local_stage (A := A) t :=
  Localization.localRingHom
    (z_adjoin_prime (A := A) s)
    (z_adjoin_prime (A := A) t)
    ((Subalgebra.inclusion (z_adjoin_stage_mono (A := A) hst)).toRingHom)
    (z_adjoin_prime_comap (A := A) hst).symm

/-- Helper for Lemma 15.50.13: the localized stage transitions are local ring homomorphisms. -/
private lemma z_adjoin_local_stage_transition_isLocalHom
    {s t : Finset A} (hst : s ⊆ t) :
    IsLocalHom (z_adjoin_local_stage_transition (A := A) hst) := by
  -- Proof comment: every localization map at a prime is local.
  simpa [z_adjoin_local_stage_transition] using
    (Localization.isLocalHom_localRingHom
      (z_adjoin_prime (A := A) s)
      (z_adjoin_prime (A := A) t)
      ((Subalgebra.inclusion (z_adjoin_stage_mono (A := A) hst)).toRingHom)
      (z_adjoin_prime_comap (A := A) hst).symm)

/-- Helper for Lemma 15.50.13: the localized stage transition attached to `s ⊆ s` is the
identity map. -/
private lemma z_adjoin_local_stage_transition_self
    (s : Finset A) :
    z_adjoin_local_stage_transition (A := A) (show s ⊆ s from le_rfl) =
      RingHom.id _ := by
  -- Proof comment: both maps are the unique localization maps induced by the identity on the
  -- underlying finite `ℤ`-stage.
  refine Localization.localRingHom_unique
    (z_adjoin_prime (A := A) s)
    (z_adjoin_prime (A := A) s)
    (algebraMap (z_adjoin_stage (A := A) s) (z_adjoin_stage (A := A) s))
    rfl fun x ↦ ?_
  simp only [z_adjoin_local_stage_transition, Localization.localRingHom_to_map]
  rfl

/-- Helper for Lemma 15.50.13: the localized stage transitions compose exactly as the inclusions
of finite generating sets do. -/
private lemma z_adjoin_local_stage_transition_comp
    {s t u : Finset A} (hst : s ⊆ t) (htu : t ⊆ u) :
    (z_adjoin_local_stage_transition (A := A) htu).comp
        (z_adjoin_local_stage_transition (A := A) hst) =
      z_adjoin_local_stage_transition (A := A) (Set.Subset.trans hst htu) := by
  -- Proof comment: both composites are the unique localized maps induced by the direct inclusion
  -- from the `s`-stage into the `u`-stage.
  symm
  refine Localization.localRingHom_unique
    (z_adjoin_prime (A := A) s)
    (z_adjoin_prime (A := A) u)
    ((Subalgebra.inclusion
      (z_adjoin_stage_mono (A := A) (Set.Subset.trans hst htu))).toRingHom)
    (z_adjoin_prime_comap (A := A) (Set.Subset.trans hst htu)).symm fun x ↦ ?_
  simp only [z_adjoin_local_stage_transition, RingHom.comp_apply,
    Localization.localRingHom_to_map]
  rfl

/-- Helper for Lemma 15.50.13: enlarging the finite generating set sends the closed-point maximal
ideal of the smaller localized stage into that of the larger one. -/
private lemma z_adjoin_local_stage_transition_map_maximalIdeal_le
    {s t : Finset A} (hst : s ⊆ t) :
    Ideal.map
        (z_adjoin_local_stage_transition (A := A) hst)
        (maximalIdeal (z_adjoin_local_stage (A := A) s)) ≤
      maximalIdeal (z_adjoin_local_stage (A := A) t) := by
  -- Proof comment: a local ring homomorphism contracts the target maximal ideal back to the
  -- source maximal ideal.
  rw [Ideal.map_le_iff_le_comap]
  have hcomap :
      Ideal.comap
          (z_adjoin_local_stage_transition (A := A) hst)
          (maximalIdeal (z_adjoin_local_stage (A := A) t)) =
        maximalIdeal (z_adjoin_local_stage (A := A) s) := by
    simpa using
      (IsLocalHom.comap_maximalIdeal
        (f := z_adjoin_local_stage_transition (A := A) hst))
  simpa [hcomap]

/-- Helper for Lemma 15.50.13: the stage-to-target maps commute with the localized transition
maps. -/
private lemma z_adjoin_local_stage_to_target_comp_transition
    {s t : Finset A} (hst : s ⊆ t) :
    (z_adjoin_local_stage_to_target (A := A) t).comp
        (z_adjoin_local_stage_transition (A := A) hst) =
      z_adjoin_local_stage_to_target (A := A) s := by
  -- Proof comment: both composites are the unique local maps induced by the same composite into
  -- the final target ring `A`.
  symm
  refine Localization.localRingHom_unique
    (z_adjoin_prime (A := A) s)
    (maximalIdeal A)
    (algebraMap (z_adjoin_stage (A := A) s) A)
    rfl fun x ↦ ?_
  simp only [z_adjoin_local_stage_to_target, z_adjoin_local_stage_transition,
    RingHom.comp_apply, Localization.localRingHom_to_map]
  rfl

/-- Helper for Lemma 15.50.13: each localized finite `ℤ`-stage embeds into the target henselian
local ring. -/
private lemma z_adjoin_local_stage_to_target_injective
    (s : Finset A) :
    Function.Injective (z_adjoin_local_stage_to_target (A := A) s) := by
  let B := z_adjoin_stage (A := A) s
  let p := z_adjoin_prime (A := A) s
  let _ : IsLocalization (maximalIdeal A).primeCompl A :=
    self_isLocalization_primeCompl_maximalIdeal A
  have hB : Function.Injective (algebraMap B A) := by
    -- Proof comment: the structural map from a subalgebra into its ambient ring is the subtype
    -- inclusion, so it is injective.
    intro x y hxy
    exact Subtype.ext hxy
  have hp :
      p.primeCompl ≤ Submonoid.comap (algebraMap B A) (maximalIdeal A).primeCompl := by
    -- Proof comment: `p` is defined as the pullback of the closed-point maximal ideal of `A`.
    exact Localization.le_comap_primeCompl_iff.mpr (ge_of_eq rfl)
  let _ : Algebra (z_adjoin_local_stage (A := A) s) A :=
    (z_adjoin_local_stage_to_target (A := A) s).toAlgebra
  -- Proof comment: localizing an injective map remains injective once the target is viewed as its
  -- own localization at the complement of the maximal ideal.
  simpa [B, p, z_adjoin_local_stage, z_adjoin_local_stage_to_target,
    RingHom.algebraMap_toAlgebra] using
    (IsLocalization.map_injective_of_injective'
      p.primeCompl
      A
      A
      hp
      (show (0 : A) ∉ Ideal.primeCompl (maximalIdeal A) by
        simp [Ideal.primeCompl])
      hB)

/-- Helper for Lemma 15.50.13: the stage-to-target maps assemble to the canonical comparison map
from the direct limit of the localized finite `ℤ`-stages to `A`. -/
private noncomputable def z_adjoin_local_stage_directLimitToTarget :
    Ring.DirectLimit
        (fun s : Finset A ↦ z_adjoin_local_stage (A := A) s)
        (fun s t hst ↦ z_adjoin_local_stage_transition (A := A) hst) →+*
      A :=
  Ring.DirectLimit.lift
    (fun s : Finset A ↦ z_adjoin_local_stage (A := A) s)
    (fun s t hst ↦ z_adjoin_local_stage_transition (A := A) hst)
    A
    (fun s ↦ z_adjoin_local_stage_to_target (A := A) s)
    (fun s t hst x ↦ by
      -- Proof comment: this is exactly the stage-to-target compatibility proved above.
      simpa [RingHom.comp_apply] using
        congrArg
          (fun f :
            z_adjoin_local_stage (A := A) s →+*
              A ↦ f x)
          (z_adjoin_local_stage_to_target_comp_transition (A := A) hst))

/-- Helper for Lemma 15.50.13: on each localized stage, the direct-limit comparison map is the
original localized map into `A`. -/
private lemma z_adjoin_local_stage_directLimitToTarget_comp_of
    (s : Finset A) :
    (z_adjoin_local_stage_directLimitToTarget (A := A)).comp
        (Ring.DirectLimit.of
          (fun t : Finset A ↦ z_adjoin_local_stage (A := A) t)
          (fun t u htu ↦ z_adjoin_local_stage_transition (A := A) htu)
          s) =
      z_adjoin_local_stage_to_target (A := A) s := by
  ext x
  -- Proof comment: this is the universal-property computation rule for `Ring.DirectLimit.lift`.
  simpa [z_adjoin_local_stage_directLimitToTarget] using
    (Ring.DirectLimit.lift_of
      (G := fun t : Finset A ↦ z_adjoin_local_stage (A := A) t)
      (f := fun t u htu ↦ z_adjoin_local_stage_transition (A := A) htu)
      (P := A)
      (g := fun t ↦ z_adjoin_local_stage_to_target (A := A) t)
      (Hg := fun t u htu x ↦ by
        simpa [RingHom.comp_apply] using
          congrArg
            (fun f :
              z_adjoin_local_stage (A := A) t →+*
                A ↦ f x)
            (z_adjoin_local_stage_to_target_comp_transition (A := A) htu))
      s x)

/-- Helper for Lemma 15.50.13: the direct limit of the localized finite `ℤ`-stages is canonically
identified with `A`. -/
private noncomputable def z_adjoin_local_stage_directLimit_equiv :
    Ring.DirectLimit
        (fun s : Finset A ↦ z_adjoin_local_stage (A := A) s)
        (fun s t hst ↦ z_adjoin_local_stage_transition (A := A) hst) ≃+*
      A := by
  let ψ := z_adjoin_local_stage_directLimitToTarget (A := A)
  have hψ_inj : Function.Injective ψ := by
    intro x y hxy
    rcases Ring.DirectLimit.exists_of
      (G := fun s : Finset A ↦ z_adjoin_local_stage (A := A) s)
      (f := fun s t hst ↦ z_adjoin_local_stage_transition (A := A) hst)
      x with ⟨s, xs, rfl⟩
    rcases Ring.DirectLimit.exists_of
      (G := fun s : Finset A ↦ z_adjoin_local_stage (A := A) s)
      (f := fun s t hst ↦ z_adjoin_local_stage_transition (A := A) hst)
      y with ⟨t, yt, rfl⟩
    let u : Finset A := s ∪ t
    have hsu : s ⊆ u := Finset.subset_union_left
    have htu : t ⊆ u := Finset.subset_union_right
    have hstage :
        (z_adjoin_local_stage_transition (A := A) hsu) xs =
          (z_adjoin_local_stage_transition (A := A) htu) yt := by
      apply z_adjoin_local_stage_to_target_injective (A := A) u
      calc
        z_adjoin_local_stage_to_target (A := A) u
            ((z_adjoin_local_stage_transition (A := A) hsu) xs) =
          ψ (Ring.DirectLimit.of
            (fun z : Finset A ↦ z_adjoin_local_stage (A := A) z)
            (fun z w hzw ↦ z_adjoin_local_stage_transition (A := A) hzw)
            u ((z_adjoin_local_stage_transition (A := A) hsu) xs)) := by
              symm
              simpa [RingHom.comp_apply] using
                congrArg
                  (fun f :
                    z_adjoin_local_stage (A := A) u →+*
                      A ↦ f ((z_adjoin_local_stage_transition (A := A) hsu) xs))
                  (z_adjoin_local_stage_directLimitToTarget_comp_of
                    (A := A) u)
        _ = ψ (Ring.DirectLimit.of
            (fun z : Finset A ↦ z_adjoin_local_stage (A := A) z)
            (fun z w hzw ↦ z_adjoin_local_stage_transition (A := A) hzw)
            s xs) := by
              simpa using
                (Ring.DirectLimit.of_f
                  (f := fun z w hzw ↦ z_adjoin_local_stage_transition (A := A) hzw)
                  hsu xs).symm
        _ = ψ (Ring.DirectLimit.of
            (fun z : Finset A ↦ z_adjoin_local_stage (A := A) z)
            (fun z w hzw ↦ z_adjoin_local_stage_transition (A := A) hzw)
            t yt) := hxy
        _ = ψ (Ring.DirectLimit.of
            (fun z : Finset A ↦ z_adjoin_local_stage (A := A) z)
            (fun z w hzw ↦ z_adjoin_local_stage_transition (A := A) hzw)
            u ((z_adjoin_local_stage_transition (A := A) htu) yt)) := by
              simpa using
                (Ring.DirectLimit.of_f
                  (f := fun z w hzw ↦ z_adjoin_local_stage_transition (A := A) hzw)
                  htu yt)
        _ =
          z_adjoin_local_stage_to_target (A := A) u
            ((z_adjoin_local_stage_transition (A := A) htu) yt) := by
              simpa [RingHom.comp_apply] using
                congrArg
                  (fun f :
                    z_adjoin_local_stage (A := A) u →+*
                      A ↦ f ((z_adjoin_local_stage_transition (A := A) htu) yt))
                  (z_adjoin_local_stage_directLimitToTarget_comp_of
                    (A := A) u)
    calc
      Ring.DirectLimit.of
          (fun z : Finset A ↦ z_adjoin_local_stage (A := A) z)
          (fun z w hzw ↦ z_adjoin_local_stage_transition (A := A) hzw)
          s xs =
        Ring.DirectLimit.of
          (fun z : Finset A ↦ z_adjoin_local_stage (A := A) z)
          (fun z w hzw ↦ z_adjoin_local_stage_transition (A := A) hzw)
          u ((z_adjoin_local_stage_transition (A := A) hsu) xs) := by
            simpa using
              (Ring.DirectLimit.of_f
                (f := fun z w hzw ↦ z_adjoin_local_stage_transition (A := A) hzw)
                hsu xs)
      _ =
        Ring.DirectLimit.of
          (fun z : Finset A ↦ z_adjoin_local_stage (A := A) z)
          (fun z w hzw ↦ z_adjoin_local_stage_transition (A := A) hzw)
          u ((z_adjoin_local_stage_transition (A := A) htu) yt) := by
            rw [hstage]
      _ =
        Ring.DirectLimit.of
          (fun z : Finset A ↦ z_adjoin_local_stage (A := A) z)
          (fun z w hzw ↦ z_adjoin_local_stage_transition (A := A) hzw)
          t yt := by
            simpa using
              (Ring.DirectLimit.of_f
                (f := fun z w hzw ↦ z_adjoin_local_stage_transition (A := A) hzw)
                htu yt).symm
  have hψ_surj : Function.Surjective ψ := by
    intro x
    let s : Finset A := {x}
    let xStage : z_adjoin_stage (A := A) s :=
      ⟨x, by
        -- Proof comment: the singleton generator lies in the finite adjoin stage by
        -- construction.
        exact Algebra.subset_adjoin (by simp [s])⟩
    refine ⟨Ring.DirectLimit.of
      (fun t : Finset A ↦ z_adjoin_local_stage (A := A) t)
      (fun t u htu ↦ z_adjoin_local_stage_transition (A := A) htu)
      s (algebraMap _ _ xStage), ?_⟩
    -- Proof comment: the singleton stage already contains `x`, and the localized comparison map
    -- sends its canonical representative to `x`.
    change
      z_adjoin_local_stage_to_target (A := A) s
          (algebraMap
            (z_adjoin_stage (A := A) s)
            (z_adjoin_local_stage (A := A) s) xStage) = x
    simp [z_adjoin_local_stage_to_target, Localization.localRingHom_to_map, xStage, s]
  -- Proof comment: package bijectivity of the explicit comparison map into the desired ring
  -- equivalence.
  exact RingEquiv.ofBijective ψ ⟨hψ_inj, hψ_surj⟩

/-- Helper for Lemma 15.50.13: the colimit ideal generated by the maximal ideals of the localized
finite stages maps to the maximal ideal of `A` under the direct-limit comparison. -/
private lemma z_adjoin_local_stage_directLimit_maximalIdeal :
    let B := fun s : Finset A ↦ z_adjoin_local_stage (A := A) s
    let ρ := fun s t hst ↦ z_adjoin_local_stage_transition (A := A) hst
    let B∞ := Ring.DirectLimit B ρ
    let e := z_adjoin_local_stage_directLimit_equiv (A := A)
    let I∞ : Ideal B∞ := ⨆ s, Ideal.map (Ring.DirectLimit.of B ρ s) (maximalIdeal (B s))
    Ideal.map e.toRingHom I∞ = maximalIdeal A := by
  let B := fun s : Finset A ↦ z_adjoin_local_stage (A := A) s
  let ρ := fun s t hst ↦ z_adjoin_local_stage_transition (A := A) hst
  let B∞ := Ring.DirectLimit B ρ
  let e := z_adjoin_local_stage_directLimit_equiv (A := A)
  let I∞ : Ideal B∞ := ⨆ s, Ideal.map (Ring.DirectLimit.of B ρ s) (maximalIdeal (B s))
  have hle :
      Ideal.map e.toRingHom I∞ ≤ maximalIdeal A := by
    refine Ideal.map_le_iff_le_comap.mpr ?_
    refine iSup_le fun s ↦ ?_
    rw [Ideal.map_le_iff_le_comap]
    change maximalIdeal (B s) ≤
      Ideal.comap ((e.toRingHom).comp (Ring.DirectLimit.of B ρ s)) (maximalIdeal A)
    have hcomp :
        (e.toRingHom).comp (Ring.DirectLimit.of B ρ s) =
          z_adjoin_local_stage_to_target (A := A) s := by
      ext x
      simpa [e, z_adjoin_local_stage_directLimit_equiv, RingHom.comp_apply] using
        congrArg
          (fun f : B s →+* A ↦ f x)
          (z_adjoin_local_stage_directLimitToTarget_comp_of
            (A := A) s)
    simpa [hcomp] using
      (show maximalIdeal (B s) ≤
        Ideal.comap
          (z_adjoin_local_stage_to_target (A := A) s)
          (maximalIdeal A) by
            simpa using
              (show maximalIdeal (B s) ≤ maximalIdeal (B s) from le_rfl :
                maximalIdeal (B s) ≤
                  Ideal.comap
                    (z_adjoin_local_stage_to_target (A := A) s)
                    (maximalIdeal A)))
  have hpre :
      Ideal.comap e.toRingHom (maximalIdeal A) ≤ I∞ := by
    intro z hz
    rcases Ring.DirectLimit.exists_of (G := B) (f := ρ) z with ⟨s, zs, rfl⟩
    have hz' :
        z_adjoin_local_stage_to_target (A := A) s zs ∈ maximalIdeal A := by
      simpa [e, z_adjoin_local_stage_directLimit_equiv, RingHom.comp_apply] using hz
    have hzStage : zs ∈ maximalIdeal (B s) := by
      have hcomap :
          Ideal.comap
              (z_adjoin_local_stage_to_target (A := A) s)
              (maximalIdeal A) =
            maximalIdeal (B s) := by
        simpa using
          (IsLocalHom.comap_maximalIdeal
            (f := z_adjoin_local_stage_to_target (A := A) s))
      simpa [hcomap] using hz'
    exact le_iSup_of_le s ⟨zs, hzStage, rfl⟩
  have hge :
      maximalIdeal A ≤ Ideal.map e.toRingHom I∞ := by
    calc
      maximalIdeal A =
          Ideal.map e.toRingHom (Ideal.comap e.toRingHom (maximalIdeal A)) := by
            symm
            exact Ideal.map_comap_of_surjective e.surjective _
      _ ≤ Ideal.map e.toRingHom I∞ := Ideal.map_mono hpre
  exact le_antisymm hle hge

/-- Helper for Lemma 15.50.13: localizing a finite `ℤ`-subalgebra at the prime under the closed
point of `A` produces a local essentially-finite-type, hence Noetherian, stage. -/
lemma z_adjoin_local_stage_structure
    (s : Finset A) :
    IsLocalRing (z_adjoin_local_stage (A := A) s) ∧
      Algebra.EssFiniteType ℤ (z_adjoin_local_stage (A := A) s) ∧
      IsNoetherianRing (z_adjoin_local_stage (A := A) s) := by
  let B : Subalgebra ℤ A := z_adjoin_stage (A := A) s
  let p : Ideal B := z_adjoin_prime (A := A) s
  let L := z_adjoin_local_stage (A := A) s
  refine ⟨inferInstance, ?_, ?_⟩
  · -- Proof comment: the finite adjoin stage is finite type over `ℤ`, and localization turns it
    -- into the essentially-finite-type local model appearing in the source proof.
    have hfg : B.FG := by
      simpa [B, z_adjoin_stage] using (Subalgebra.fg_adjoin_finset (R := ℤ) s)
    let _ : Algebra.FiniteType ℤ B := (Subalgebra.fg_iff_finiteType B).mp hfg
    let _ : Algebra.EssFiniteType B L := Algebra.EssFiniteType.of_isLocalization L p.primeCompl
    exact Algebra.EssFiniteType.comp ℤ B L
  · -- Proof comment: once the stage is essentially finite type over the Noetherian base `ℤ`,
    -- Noetherianity follows from the standard owner theorem.
    have hEss : Algebra.EssFiniteType ℤ L := by
      have hfg : B.FG := by
        simpa [B, z_adjoin_stage] using (Subalgebra.fg_adjoin_finset (R := ℤ) s)
      let _ : Algebra.FiniteType ℤ B := (Subalgebra.fg_iff_finiteType B).mp hfg
      let _ : Algebra.EssFiniteType B L := Algebra.EssFiniteType.of_isLocalization L p.primeCompl
      exact Algebra.EssFiniteType.comp ℤ B L
    let _ : Algebra.EssFiniteType ℤ L := hEss
    exact Algebra.EssFiniteType.isNoetherianRing ℤ L

/-- Helper for Lemma 15.50.13: each localized finite `ℤ`-stage is a `G`-ring. -/
lemma z_adjoin_local_stage_is_gring
    (s : Finset A) :
    IsGRing (z_adjoin_local_stage (A := A) s) := by
  -- Proof comment: Proposition `15.50.10` is the owner theorem matching the source step once the
  -- localized finite stage is known to be essentially finite type over `ℤ`.
  let _ : Algebra.EssFiniteType ℤ (z_adjoin_local_stage (A := A) s) :=
    (z_adjoin_local_stage_structure (A := A) s).2.1
  exact isGRing_of_essFiniteType ℤ

/-- Helper for Lemma 15.50.13: the canonical henselized stage attached to a localized finite
`ℤ`-stage. -/
private abbrev z_adjoin_henselized_stage (s : Finset A) : Type u :=
  henselizationRing (pairOfIdeal (maximalIdeal (z_adjoin_local_stage (A := A) s)))

/-- Helper for Lemma 15.50.13: each canonical henselized stage is henselian local. -/
private lemma z_adjoin_henselized_stage_henselianLocalRing
    (s : Finset A) :
    HenselianLocalRing (z_adjoin_henselized_stage (A := A) s) := by
  -- Proof comment: the pair-henselization of a local ring is a henselization of that local ring.
  infer_instance

/-- Helper for Lemma 15.50.13: each canonical henselized stage is again a `G`-ring. -/
private lemma z_adjoin_henselized_stage_is_gring
    (s : Finset A) :
    IsGRing (z_adjoin_henselized_stage (A := A) s) := by
  -- Proof comment: Lemma `15.50.8` transfers the `G`-ring owner from the local stage to its
  -- henselization.
  let _ : IsGRing (z_adjoin_local_stage (A := A) s) :=
    z_adjoin_local_stage_is_gring (A := A) s
  infer_instance

/-- Helper for Lemma 15.50.13: the finite-stage henselization transitions are induced by the
localized stage transitions. -/
private noncomputable abbrev z_adjoin_henselized_stage_transitionAlgHom
    {s t : Finset A} (hst : s ⊆ t) :
    z_adjoin_henselized_stage (A := A) s →ₐ[z_adjoin_local_stage (A := A) s]
      z_adjoin_henselized_stage (A := A) t :=
  let _ : Algebra (z_adjoin_local_stage (A := A) s) (z_adjoin_local_stage (A := A) t) :=
    (z_adjoin_local_stage_transition (A := A) hst).toAlgebra
  let _ :
      IsLocalHom
        (algebraMap
          (z_adjoin_local_stage (A := A) s)
          (z_adjoin_local_stage (A := A) t)) :=
    z_adjoin_local_stage_transition_isLocalHom (A := A) hst
  henselizationMap
    (R := z_adjoin_local_stage (A := A) s)
    (S := z_adjoin_local_stage (A := A) t)
    (Rh := z_adjoin_henselized_stage (A := A) s)
    (Sh := z_adjoin_henselized_stage (A := A) t)

/-- Helper for Lemma 15.50.13: the finite-stage henselization transitions as ring maps. -/
private noncomputable abbrev z_adjoin_henselized_stage_transition
    {s t : Finset A} (hst : s ⊆ t) :
    z_adjoin_henselized_stage (A := A) s →+*
      z_adjoin_henselized_stage (A := A) t :=
  (z_adjoin_henselized_stage_transitionAlgHom (A := A) hst).toRingHom

/-- Helper for Lemma 15.50.13: the henselized-stage transitions are local ring homomorphisms
because they are the canonical maps between henselizations of local stages. -/
private lemma z_adjoin_henselized_stage_transition_isLocalHom
    {s t : Finset A} (hst : s ⊆ t) :
    IsLocalHom (z_adjoin_henselized_stage_transition (A := A) hst) := by
  -- Proof comment: reuse the owner theorem `henselizationMap_isLocalHom` after installing the
  -- localized stage transition as the ambient algebra map.
  let _ : Algebra (z_adjoin_local_stage (A := A) s) (z_adjoin_local_stage (A := A) t) :=
    (z_adjoin_local_stage_transition (A := A) hst).toAlgebra
  let _ :
      IsLocalHom
        (algebraMap (z_adjoin_local_stage (A := A) s) (z_adjoin_local_stage (A := A) t)) := by
    simpa [RingHom.algebraMap_toAlgebra] using
      (z_adjoin_local_stage_transition_isLocalHom (A := A) hst)
  simpa [z_adjoin_henselized_stage_transition] using
    (henselizationMap_isLocalHom
      (R := z_adjoin_local_stage (A := A) s)
      (S := z_adjoin_local_stage (A := A) t)
      (Rh := z_adjoin_henselized_stage (A := A) s)
      (Sh := z_adjoin_henselized_stage (A := A) t))

/-- Helper for Lemma 15.50.13: the chosen henselization transition extends the smaller localized
stage map to the larger henselized stage. -/
private lemma z_adjoin_henselized_stage_transition_comp_algebraMap
    {s t : Finset A} (hst : s ⊆ t) :
    (z_adjoin_henselized_stage_transition (A := A) hst).comp
        (algebraMap
          (z_adjoin_local_stage (A := A) s)
          (z_adjoin_henselized_stage (A := A) s)) =
      algebraMap
        (z_adjoin_local_stage (A := A) s)
        (z_adjoin_henselized_stage (A := A) t) := by
  -- Proof comment: this is the defining algebra-compatibility of the canonical comparison map
  -- between henselizations.
  ext x
  exact (z_adjoin_henselized_stage_transitionAlgHom (A := A) hst).commutes x

/-- Helper for Lemma 15.50.13: the chosen henselization transition attached to `s ⊆ s` is the
identity map. -/
private lemma z_adjoin_henselized_stage_transition_self
    (s : Finset A) :
    z_adjoin_henselized_stage_transition (A := A) (show s ⊆ s from le_rfl) =
      RingHom.id _ := by
  let R := z_adjoin_local_stage (A := A) s
  let Rh := z_adjoin_henselized_stage (A := A) s
  let _ : IsHenselizationOf R Rh := by
    simpa [R, Rh, z_adjoin_henselized_stage] using
      (localRing_henselization_isHenselizationOf R)
  let f : Rh →ₐ[R] Rh :=
    z_adjoin_henselized_stage_transitionAlgHom (A := A) (show s ⊆ s from le_rfl)
  let g : Rh →ₐ[R] Rh :=
    AlgHom.id R Rh
  have hf : IsLocalHom (f : Rh →+* Rh) := by
    simpa [f, Rh] using
      (z_adjoin_henselized_stage_transition_isLocalHom (A := A) (show s ⊆ s from le_rfl))
  have hg : IsLocalHom (g : Rh →+* Rh) := by
    change IsLocalHom (RingHom.id Rh)
    infer_instance
  rcases
      existsUnique_algHom_between_henselizations_of_localHom
        (R := R) (S := R) (Rh := Rh) (Sh := Rh) with ⟨u, hu, hu_unique⟩
  have hf_eq : f = u := hu_unique f hf
  have hg_eq : g = u := hu_unique g hg
  exact congrArg AlgHom.toRingHom (hf_eq.trans hg_eq.symm)

/-- Helper for Lemma 15.50.13: the chosen henselization transitions compose exactly as the
localized stage transitions do. -/
private lemma z_adjoin_henselized_stage_transition_comp
    {s t u : Finset A} (hst : s ⊆ t) (htu : t ⊆ u) :
    (z_adjoin_henselized_stage_transition (A := A) htu).comp
        (z_adjoin_henselized_stage_transition (A := A) hst) =
      z_adjoin_henselized_stage_transition (A := A) (Set.Subset.trans hst htu) := by
  let R := z_adjoin_local_stage (A := A) s
  let S := z_adjoin_local_stage (A := A) u
  let Rh := z_adjoin_henselized_stage (A := A) s
  let Sh := z_adjoin_henselized_stage (A := A) u
  let T := z_adjoin_local_stage (A := A) t
  let Th := z_adjoin_henselized_stage (A := A) t
  let _ : Algebra R T := (z_adjoin_local_stage_transition (A := A) hst).toAlgebra
  let _ : Algebra T S := (z_adjoin_local_stage_transition (A := A) htu).toAlgebra
  let _ : Algebra R S :=
    (z_adjoin_local_stage_transition (A := A) (Set.Subset.trans hst htu)).toAlgebra
  let _ : IsLocalHom (algebraMap R S) := by
    simpa [RingHom.algebraMap_toAlgebra] using
      (z_adjoin_local_stage_transition_isLocalHom (A := A) (Set.Subset.trans hst htu))
  let _ : IsHenselizationOf R Rh := by
    simpa [R, Rh, z_adjoin_henselized_stage] using
      (localRing_henselization_isHenselizationOf R)
  let _ : IsHenselizationOf S Sh := by
    simpa [S, Sh, z_adjoin_henselized_stage] using
      (localRing_henselization_isHenselizationOf S)
  let _ : Algebra R Th :=
    RingHom.toAlgebra
      ((algebraMap T Th).comp (algebraMap R T))
  let _ : IsScalarTower R T Th :=
    IsScalarTower.of_algebraMap_eq' rfl
  let _ : Algebra R Sh :=
    RingHom.toAlgebra
      ((algebraMap S Sh).comp (algebraMap R S))
  let _ : IsScalarTower R S Sh :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hcomp :
      ((z_adjoin_henselized_stage_transition (A := A) htu).comp
          (z_adjoin_henselized_stage_transition (A := A) hst)).comp
          (algebraMap R Rh) =
        algebraMap R Sh := by
    calc
      ((z_adjoin_henselized_stage_transition (A := A) htu).comp
          (z_adjoin_henselized_stage_transition (A := A) hst)).comp
          (algebraMap R Rh) =
        (z_adjoin_henselized_stage_transition (A := A) htu).comp
          ((z_adjoin_henselized_stage_transition (A := A) hst).comp
            (algebraMap R Rh)) := by
              rw [RingHom.comp_assoc]
      _ =
        (z_adjoin_henselized_stage_transition (A := A) htu).comp
          (algebraMap R Th) := by
            rw [z_adjoin_henselized_stage_transition_comp_algebraMap (A := A) hst]
      _ = algebraMap R Sh := by
        ext x
        change
          z_adjoin_henselized_stage_transition (A := A) htu (algebraMap R Th x) =
            algebraMap R Sh x
        rw [show algebraMap R Th x = algebraMap T Th (algebraMap R T x) by
          simp [IsScalarTower.algebraMap_eq R T Th]]
        rw [z_adjoin_henselized_stage_transition_comp_algebraMap (A := A) htu]
        simp [IsScalarTower.algebraMap_eq R T S, IsScalarTower.algebraMap_eq R S Sh]
  let f : Rh →ₐ[R] Sh :=
    z_adjoin_henselized_stage_transitionAlgHom (A := A) (Set.Subset.trans hst htu)
  let g : Rh →ₐ[R] Sh :=
    { toRingHom :=
        (z_adjoin_henselized_stage_transition (A := A) htu).comp
          (z_adjoin_henselized_stage_transition (A := A) hst)
      commutes' := by
        intro x
        exact RingHom.congr_fun hcomp x }
  have hf : IsLocalHom (f : Rh →+* Sh) := by
    simpa [f, Rh, Sh] using
      (z_adjoin_henselized_stage_transition_isLocalHom
        (A := A) (Set.Subset.trans hst htu))
  have hg : IsLocalHom (g : Rh →+* Sh) := by
    change
      IsLocalHom
        ((z_adjoin_henselized_stage_transition (A := A) htu).comp
          (z_adjoin_henselized_stage_transition (A := A) hst))
    infer_instance
  rcases
      existsUnique_algHom_between_henselizations_of_localHom
        (R := R) (S := S) (Rh := Rh) (Sh := Sh) with ⟨v, hv, hv_unique⟩
  have hf_eq : f = v := hv_unique f hf
  have hg_eq : g = v := hv_unique g hg
  exact congrArg AlgHom.toRingHom (hg_eq.trans hf_eq.symm)

/-- Helper for Lemma 15.50.13: the henselized finite stages form a directed system under the
canonical transition maps. -/
private instance z_adjoin_henselized_stage_directedSystem :
    DirectedSystem
      (fun s : Finset A ↦ z_adjoin_henselized_stage (A := A) s)
      (fun s t hst ↦ z_adjoin_henselized_stage_transition (A := A) hst) where
  map_self := by
    intro s
    exact z_adjoin_henselized_stage_transition_self (A := A) s
  map_map := by
    intro s t u hst htu
    exact z_adjoin_henselized_stage_transition_comp (A := A) hst htu

/-- Helper for Lemma 15.50.13: every henselized-stage transition is available to typeclass search
as a local ring homomorphism. -/
private instance z_adjoin_henselized_stage_transition_instIsLocalHom
    {s t : Finset A} (hst : s ⊆ t) :
    IsLocalHom (z_adjoin_henselized_stage_transition (A := A) hst) :=
  z_adjoin_henselized_stage_transition_isLocalHom (A := A) hst

local notation "H∞" =>
  Ring.DirectLimit
    (fun s : Finset A ↦ z_adjoin_henselized_stage (A := A) s)
    (fun s t hst ↦ z_adjoin_henselized_stage_transition (A := A) hst)

/-- Helper for Lemma 15.50.13: the pair henselization of `(A, maximalIdeal A)` is henselian at
its distinguished ideal. -/
private lemma pair_henselization_henselianRing :
    HenselianRing A_h (henselizationIdeal A_pair) := by
  -- Proof comment: this is the defining property of the chosen pair henselization.
  change HenselianRing (henselizationPair A_pair).ring (henselizationPair A_pair).ideal
  exact (henselization A_pair).property

/-- Helper for Lemma 15.50.13: each henselized finite stage maps canonically to the pair
henselization of `(A, maximalIdeal A)`. -/
private noncomputable abbrev z_adjoin_henselized_stage_to_target_pair_henselization
    (s : Finset A) :
    z_adjoin_henselized_stage (A := A) s →+* A_h :=
  Classical.choose <|
    ExistsUnique.exists <|
      existsUnique_henselizationRingHom_of_henselian_target
        (I := maximalIdeal (z_adjoin_local_stage (A := A) s))
        (B := A_h)
        (K := henselizationIdeal A_pair)
        (pair_henselization_henselianRing (A := A))
        (by
          -- Proof comment: the source maximal ideal maps into the distinguished ideal of `A^h`
          -- because the stage map to `A` is local and `A^h` extends `A`.
          rw [henselizationIdeal_eq_map (X := A_pair), Ideal.comap_comap]
          exact
            (show
              maximalIdeal (z_adjoin_local_stage (A := A) s) ≤
                Ideal.comap
                  (z_adjoin_local_stage_to_target (A := A) s)
                  (maximalIdeal A) by
                simpa using
                  (show
                    maximalIdeal (z_adjoin_local_stage (A := A) s) ≤
                      maximalIdeal (z_adjoin_local_stage (A := A) s) from
                    le_rfl)).trans
              (Ideal.le_comap_map))

/-- Helper for Lemma 15.50.13: the chosen map from a henselized finite stage to `A^h` extends the
obvious composite from the underlying localized stage. -/
private lemma z_adjoin_henselized_stage_to_target_pair_henselization_comp
    (s : Finset A) :
    (z_adjoin_henselized_stage_to_target_pair_henselization (A := A) s).comp
        (algebraMap
          (z_adjoin_local_stage (A := A) s)
          (z_adjoin_henselized_stage (A := A) s)) =
      (toHenselization A_pair).comp
        (z_adjoin_local_stage_to_target (A := A) s) := by
  -- Proof comment: this is the defining compatibility of the chosen comparison map into `A^h`.
  exact Classical.choose_spec <|
    ExistsUnique.exists <|
      existsUnique_henselizationRingHom_of_henselian_target
        (I := maximalIdeal (z_adjoin_local_stage (A := A) s))
        (B := A_h)
        (K := henselizationIdeal A_pair)
        (pair_henselization_henselianRing (A := A))
        (by
          rw [henselizationIdeal_eq_map (X := A_pair), Ideal.comap_comap]
          exact
            (show
              maximalIdeal (z_adjoin_local_stage (A := A) s) ≤
                Ideal.comap
                  (z_adjoin_local_stage_to_target (A := A) s)
                  (maximalIdeal A) by
                simpa using
                  (show
                    maximalIdeal (z_adjoin_local_stage (A := A) s) ≤
                      maximalIdeal (z_adjoin_local_stage (A := A) s) from
                    le_rfl)).trans
              (Ideal.le_comap_map))

/-- Helper for Lemma 15.50.13: the stage maps to `A^h` commute with the henselized-stage
transition maps. -/
private lemma z_adjoin_henselized_stage_to_target_pair_henselization_comp_transition
    {s t : Finset A} (hst : s ⊆ t) :
    (z_adjoin_henselized_stage_to_target_pair_henselization (A := A) t).comp
        (z_adjoin_henselized_stage_transition (A := A) hst) =
      z_adjoin_henselized_stage_to_target_pair_henselization (A := A) s := by
  obtain ⟨u, hu, hu_unique⟩ :=
    ExistsUnique.exists <|
      existsUnique_henselizationRingHom_of_henselian_target
        (I := maximalIdeal (z_adjoin_local_stage (A := A) s))
        (B := A_h)
        (K := henselizationIdeal A_pair)
        (pair_henselization_henselianRing (A := A))
        (by
          rw [henselizationIdeal_eq_map (X := A_pair), Ideal.comap_comap]
          exact
            (show
              maximalIdeal (z_adjoin_local_stage (A := A) s) ≤
                Ideal.comap
                  (z_adjoin_local_stage_to_target (A := A) s)
                  (maximalIdeal A) by
                simpa using
                  (show
                    maximalIdeal (z_adjoin_local_stage (A := A) s) ≤
                      maximalIdeal (z_adjoin_local_stage (A := A) s) from
                    le_rfl)).trans
              (Ideal.le_comap_map))
  have hleft :
      ((z_adjoin_henselized_stage_to_target_pair_henselization (A := A) t).comp
          (z_adjoin_henselized_stage_transition (A := A) hst)).comp
          (algebraMap
            (z_adjoin_local_stage (A := A) s)
            (z_adjoin_henselized_stage (A := A) s)) =
        (toHenselization A_pair).comp
          (z_adjoin_local_stage_to_target (A := A) s) := by
    calc
      ((z_adjoin_henselized_stage_to_target_pair_henselization (A := A) t).comp
          (z_adjoin_henselized_stage_transition (A := A) hst)).comp
          (algebraMap
            (z_adjoin_local_stage (A := A) s)
            (z_adjoin_henselized_stage (A := A) s)) =
        (z_adjoin_henselized_stage_to_target_pair_henselization (A := A) t).comp
          ((z_adjoin_henselized_stage_transition (A := A) hst).comp
            (algebraMap
              (z_adjoin_local_stage (A := A) s)
              (z_adjoin_henselized_stage (A := A) s))) := by
              rw [RingHom.comp_assoc]
      _ =
        (z_adjoin_henselized_stage_to_target_pair_henselization (A := A) t).comp
          (algebraMap
            (z_adjoin_local_stage (A := A) s)
            (z_adjoin_henselized_stage (A := A) t)) := by
              rw [z_adjoin_henselized_stage_transition_comp_algebraMap (A := A) hst]
      _ =
        (z_adjoin_henselized_stage_to_target_pair_henselization (A := A) t).comp
          ((algebraMap
            (z_adjoin_local_stage (A := A) t)
            (z_adjoin_henselized_stage (A := A) t)).comp
              (z_adjoin_local_stage_transition (A := A) hst)) := by
                ext x
                simp [IsScalarTower.algebraMap_eq
                  (z_adjoin_local_stage (A := A) s)
                  (z_adjoin_local_stage (A := A) t)
                  (z_adjoin_henselized_stage (A := A) t)]
      _ =
        ((z_adjoin_henselized_stage_to_target_pair_henselization (A := A) t).comp
          (algebraMap
            (z_adjoin_local_stage (A := A) t)
            (z_adjoin_henselized_stage (A := A) t))).comp
              (z_adjoin_local_stage_transition (A := A) hst) := by
                rw [← RingHom.comp_assoc]
      _ =
        ((toHenselization A_pair).comp
          (z_adjoin_local_stage_to_target (A := A) t)).comp
            (z_adjoin_local_stage_transition (A := A) hst) := by
              rw [z_adjoin_henselized_stage_to_target_pair_henselization_comp (A := A) t]
      _ =
        (toHenselization A_pair).comp
          ((z_adjoin_local_stage_to_target (A := A) t).comp
            (z_adjoin_local_stage_transition (A := A) hst)) := by
              rw [RingHom.comp_assoc]
      _ =
        (toHenselization A_pair).comp
          (z_adjoin_local_stage_to_target (A := A) s) := by
              rw [z_adjoin_local_stage_to_target_comp_transition (A := A) hst]
  have hright :
      (z_adjoin_henselized_stage_to_target_pair_henselization (A := A) s).comp
          (algebraMap
            (z_adjoin_local_stage (A := A) s)
            (z_adjoin_henselized_stage (A := A) s)) =
        (toHenselization A_pair).comp
          (z_adjoin_local_stage_to_target (A := A) s) :=
    z_adjoin_henselized_stage_to_target_pair_henselization_comp (A := A) s
  have hleft_eq :
      (z_adjoin_henselized_stage_to_target_pair_henselization (A := A) t).comp
          (z_adjoin_henselized_stage_transition (A := A) hst) = u :=
    hu_unique _ hleft
  have hright_eq :
      z_adjoin_henselized_stage_to_target_pair_henselization (A := A) s = u :=
    hu_unique _ hright
  exact hleft_eq.trans hright_eq.symm

/-- Helper for Lemma 15.50.13: the localized finite stage maps canonically into the direct limit
of the henselized stages by first passing to the stage henselization. -/
private noncomputable abbrev z_adjoin_local_stage_to_henselized_directLimit
    (s : Finset A) :
    z_adjoin_local_stage (A := A) s →+* H∞ :=
  (Ring.DirectLimit.of
      (fun t : Finset A ↦ z_adjoin_henselized_stage (A := A) t)
      (fun t u htu ↦ z_adjoin_henselized_stage_transition (A := A) htu)
      s).comp
    (algebraMap
      (z_adjoin_local_stage (A := A) s)
      (z_adjoin_henselized_stage (A := A) s))

/-- Helper for Lemma 15.50.13: the localized finite-stage maps into the henselized direct limit
respect the localized-stage transition maps. -/
private lemma z_adjoin_local_stage_to_henselized_directLimit_comp_transition
    {s t : Finset A} (hst : s ⊆ t) :
    (z_adjoin_local_stage_to_henselized_directLimit (A := A) t).comp
        (z_adjoin_local_stage_transition (A := A) hst) =
      z_adjoin_local_stage_to_henselized_directLimit (A := A) s := by
  ext x
  calc
    z_adjoin_local_stage_to_henselized_directLimit (A := A) t
        ((z_adjoin_local_stage_transition (A := A) hst) x) =
      Ring.DirectLimit.of
          (fun z : Finset A ↦ z_adjoin_henselized_stage (A := A) z)
          (fun z w hzw ↦ z_adjoin_henselized_stage_transition (A := A) hzw)
          t
          (algebraMap
            (z_adjoin_local_stage (A := A) t)
            (z_adjoin_henselized_stage (A := A) t)
            ((z_adjoin_local_stage_transition (A := A) hst) x)) := by
              rfl
    _ =
      Ring.DirectLimit.of
          (fun z : Finset A ↦ z_adjoin_henselized_stage (A := A) z)
          (fun z w hzw ↦ z_adjoin_henselized_stage_transition (A := A) hzw)
          t
          ((z_adjoin_henselized_stage_transition (A := A) hst)
            (algebraMap
              (z_adjoin_local_stage (A := A) s)
              (z_adjoin_henselized_stage (A := A) s) x)) := by
                rw [z_adjoin_henselized_stage_transition_comp_algebraMap (A := A) hst]
                simp [IsScalarTower.algebraMap_eq
                  (z_adjoin_local_stage (A := A) s)
                  (z_adjoin_local_stage (A := A) t)
                  (z_adjoin_henselized_stage (A := A) t)]
    _ =
      Ring.DirectLimit.of
          (fun z : Finset A ↦ z_adjoin_henselized_stage (A := A) z)
          (fun z w hzw ↦ z_adjoin_henselized_stage_transition (A := A) hzw)
          s
          (algebraMap
            (z_adjoin_local_stage (A := A) s)
            (z_adjoin_henselized_stage (A := A) s) x) := by
              simpa using
                (Ring.DirectLimit.of_f
                  (f := fun z w hzw ↦ z_adjoin_henselized_stage_transition (A := A) hzw)
                  hst
                  (algebraMap
                    (z_adjoin_local_stage (A := A) s)
                    (z_adjoin_henselized_stage (A := A) s) x))
    _ =
      z_adjoin_local_stage_to_henselized_directLimit (A := A) s x := by
        rfl

/-- Helper for Lemma 15.50.13: the direct limit of the localized stages maps canonically to the
direct limit of the henselized stages. -/
private noncomputable def z_adjoin_local_stage_directLimit_to_henselized_directLimit :
    Ring.DirectLimit
        (fun s : Finset A ↦ z_adjoin_local_stage (A := A) s)
        (fun s t hst ↦ z_adjoin_local_stage_transition (A := A) hst) →+*
      H∞ :=
  Ring.DirectLimit.lift
    (fun s : Finset A ↦ z_adjoin_local_stage (A := A) s)
    (fun s t hst ↦ z_adjoin_local_stage_transition (A := A) hst)
    H∞
    (fun s ↦ z_adjoin_local_stage_to_henselized_directLimit (A := A) s)
    (fun s t hst x ↦ by
      -- Proof comment: this is the localized-stage compatibility proved just above.
      simpa [RingHom.comp_apply] using
        congrArg
          (fun f :
            z_adjoin_local_stage (A := A) s →+*
              H∞ ↦ f x)
          (z_adjoin_local_stage_to_henselized_directLimit_comp_transition
            (A := A) hst))

/-- Helper for Lemma 15.50.13: on each localized stage, the map from the localized direct limit to
the henselized direct limit is the obvious stage inclusion. -/
private lemma z_adjoin_local_stage_directLimit_to_henselized_directLimit_comp_of
    (s : Finset A) :
    (z_adjoin_local_stage_directLimit_to_henselized_directLimit (A := A)).comp
        (Ring.DirectLimit.of
          (fun t : Finset A ↦ z_adjoin_local_stage (A := A) t)
          (fun t u htu ↦ z_adjoin_local_stage_transition (A := A) htu)
          s) =
      z_adjoin_local_stage_to_henselized_directLimit (A := A) s := by
  ext x
  -- Proof comment: this is the universal-property computation rule for the localized direct-limit
  -- lift into `H∞`.
  simpa [z_adjoin_local_stage_directLimit_to_henselized_directLimit] using
    (Ring.DirectLimit.lift_of
      (G := fun t : Finset A ↦ z_adjoin_local_stage (A := A) t)
      (f := fun t u htu ↦ z_adjoin_local_stage_transition (A := A) htu)
      (P := H∞)
      (g := fun t ↦ z_adjoin_local_stage_to_henselized_directLimit (A := A) t)
      (Hg := fun t u htu x ↦ by
        simpa [RingHom.comp_apply] using
          congrArg
            (fun f :
              z_adjoin_local_stage (A := A) t →+*
                H∞ ↦ f x)
            (z_adjoin_local_stage_to_henselized_directLimit_comp_transition
              (A := A) htu))
      s x)

/-- Helper for Lemma 15.50.13: the localized-stage colimit map into the henselized-stage colimit
sends the maximal ideal of `A` into the maximal ideal of the henselized direct limit. -/
private lemma z_adjoin_local_stage_directLimit_to_henselized_directLimit_map_maximalIdeal_le :
    let B := fun s : Finset A ↦ z_adjoin_local_stage (A := A) s
    let ρ := fun s t hst ↦ z_adjoin_local_stage_transition (A := A) hst
    let B∞ := Ring.DirectLimit B ρ
    let κ := z_adjoin_local_stage_directLimit_to_henselized_directLimit (A := A)
    let e := z_adjoin_local_stage_directLimit_equiv (A := A)
    Ideal.map
        (κ.comp e.symm.toRingHom)
        (maximalIdeal A) ≤
      maximalIdeal H∞ := by
  let B := fun s : Finset A ↦ z_adjoin_local_stage (A := A) s
  let ρ := fun s t hst ↦ z_adjoin_local_stage_transition (A := A) hst
  let B∞ := Ring.DirectLimit B ρ
  let κ := z_adjoin_local_stage_directLimit_to_henselized_directLimit (A := A)
  let e := z_adjoin_local_stage_directLimit_equiv (A := A)
  let I∞ : Ideal B∞ := ⨆ s, Ideal.map (Ring.DirectLimit.of B ρ s) (maximalIdeal (B s))
  have hstage :
      I∞ ≤ Ideal.comap κ (maximalIdeal H∞) := by
    refine iSup_le fun s ↦ ?_
    rw [Ideal.map_le_iff_le_comap]
    change
      maximalIdeal (B s) ≤
        Ideal.comap (κ.comp (Ring.DirectLimit.of B ρ s)) (maximalIdeal H∞)
    have hcomp :
        κ.comp (Ring.DirectLimit.of B ρ s) =
          z_adjoin_local_stage_to_henselized_directLimit (A := A) s := by
      ext x
      simpa [κ, z_adjoin_local_stage_directLimit_to_henselized_directLimit,
        RingHom.comp_apply] using
        congrArg
          (fun f : B s →+* H∞ ↦ f x)
          (z_adjoin_local_stage_directLimit_to_henselized_directLimit_comp_of
            (A := A) s)
    have hlocal :
        IsLocalHom (z_adjoin_local_stage_to_henselized_directLimit (A := A) s) := by
      -- Proof comment: the canonical map to the stage henselization and the direct-limit stage
      -- map are both local, so their composite is local.
      infer_instance
    simpa [hcomp] using
      (show maximalIdeal (B s) ≤
        Ideal.comap
          (z_adjoin_local_stage_to_henselized_directLimit (A := A) s)
          (maximalIdeal H∞) by
            simpa using
              (show maximalIdeal (B s) ≤ maximalIdeal (B s) from le_rfl :
                maximalIdeal (B s) ≤
                  Ideal.comap
                    (z_adjoin_local_stage_to_henselized_directLimit (A := A) s)
                    (maximalIdeal H∞)))
  have hmap :
      Ideal.map κ I∞ ≤ maximalIdeal H∞ := by
    exact Ideal.map_le_iff_le_comap.mpr hstage
  calc
    Ideal.map (κ.comp e.symm.toRingHom) (maximalIdeal A) =
        Ideal.map κ (Ideal.map e.symm.toRingHom (maximalIdeal A)) := by
          rw [Ideal.map_map]
    _ = Ideal.map κ I∞ := by
          rw [← z_adjoin_local_stage_directLimit_maximalIdeal (A := A)]
          exact Ideal.congr <| by
            ext x
            constructor
            · intro hx
              rcases hx with ⟨y, hy, rfl⟩
              exact ⟨y, hy, rfl⟩
            · intro hx
              rcases hx with ⟨y, hy, rfl⟩
              exact ⟨y, hy, rfl⟩
    _ ≤ maximalIdeal H∞ := hmap

/-- Helper for Lemma 15.50.13: the pair henselization of `(A, maximalIdeal A)` maps canonically to
the direct limit of the henselized finite stages. -/
private noncomputable abbrev target_pair_henselization_to_henselized_directLimit :
    A_h →+* H∞ :=
  Classical.choose <|
    ExistsUnique.exists <|
      existsUnique_henselizationRingHom_of_henselian_target
        (I := maximalIdeal A)
        (B := H∞)
        (K := maximalIdeal H∞)
        (by infer_instance)
        (z_adjoin_local_stage_directLimit_to_henselized_directLimit_map_maximalIdeal_le
          (A := A))

/-- Helper for Lemma 15.50.13: the map from `A^h` to the henselized-stage direct limit restricts
to the canonical map from `A` into that direct limit. -/
private lemma target_pair_henselization_to_henselized_directLimit_comp :
    let κ := z_adjoin_local_stage_directLimit_to_henselized_directLimit (A := A)
    let e := z_adjoin_local_stage_directLimit_equiv (A := A)
    (target_pair_henselization_to_henselized_directLimit (A := A)).comp
        (toHenselization A_pair) =
      κ.comp e.symm.toRingHom := by
  let κ := z_adjoin_local_stage_directLimit_to_henselized_directLimit (A := A)
  let e := z_adjoin_local_stage_directLimit_equiv (A := A)
  -- Proof comment: this is the defining compatibility clause of the chosen map from `A^h` to the
  -- henselized-stage direct limit.
  exact Classical.choose_spec <|
    ExistsUnique.exists <|
      existsUnique_henselizationRingHom_of_henselian_target
        (I := maximalIdeal A)
        (B := H∞)
        (K := maximalIdeal H∞)
        (by infer_instance)
        (z_adjoin_local_stage_directLimit_to_henselized_directLimit_map_maximalIdeal_le
          (A := A))

/-- Helper for Lemma 15.50.13: the direct limit of the henselized stages maps canonically to the
pair henselization of `(A, maximalIdeal A)`. -/
private noncomputable def henselized_stage_directLimit_to_target_pair_henselization :
    H∞ →+* A_h :=
  Ring.DirectLimit.lift
    (fun s : Finset A ↦ z_adjoin_henselized_stage (A := A) s)
    (fun s t hst ↦ z_adjoin_henselized_stage_transition (A := A) hst)
    A_h
    (fun s ↦ z_adjoin_henselized_stage_to_target_pair_henselization (A := A) s)
    (fun s t hst x ↦ by
      -- Proof comment: this is exactly the compatibility of the stage maps to `A^h`.
      simpa [RingHom.comp_apply] using
        congrArg
          (fun f :
            z_adjoin_henselized_stage (A := A) s →+*
              A_h ↦ f x)
          (z_adjoin_henselized_stage_to_target_pair_henselization_comp_transition
            (A := A) hst))

/-- Helper for Lemma 15.50.13: on each henselized stage, the map from the direct limit to `A^h`
is the chosen stage map. -/
private lemma henselized_stage_directLimit_to_target_pair_henselization_comp_of
    (s : Finset A) :
    (henselized_stage_directLimit_to_target_pair_henselization (A := A)).comp
        (Ring.DirectLimit.of
          (fun t : Finset A ↦ z_adjoin_henselized_stage (A := A) t)
          (fun t u htu ↦ z_adjoin_henselized_stage_transition (A := A) htu)
          s) =
      z_adjoin_henselized_stage_to_target_pair_henselization (A := A) s := by
  ext x
  -- Proof comment: this is the universal-property computation rule for the direct-limit lift to
  -- `A^h`.
  simpa [henselized_stage_directLimit_to_target_pair_henselization] using
    (Ring.DirectLimit.lift_of
      (G := fun t : Finset A ↦ z_adjoin_henselized_stage (A := A) t)
      (f := fun t u htu ↦ z_adjoin_henselized_stage_transition (A := A) htu)
      (P := A_h)
      (g := fun t ↦ z_adjoin_henselized_stage_to_target_pair_henselization (A := A) t)
      (Hg := fun t u htu x ↦ by
        simpa [RingHom.comp_apply] using
          congrArg
            (fun f :
              z_adjoin_henselized_stage (A := A) t →+*
                A_h ↦ f x)
            (z_adjoin_henselized_stage_to_target_pair_henselization_comp_transition
              (A := A) htu))
      s x)

/-- Helper for Lemma 15.50.13: composing the two canonical maps on the pair henselization of `A`
gives the identity. -/
private lemma target_pair_henselization_endomorphism_is_id :
    (henselized_stage_directLimit_to_target_pair_henselization (A := A)).comp
        (target_pair_henselization_to_henselized_directLimit (A := A)) =
      RingHom.id A_h := by
  obtain ⟨u, hu, hu_unique⟩ :=
    ExistsUnique.exists <|
      existsUnique_henselizationRingHom_of_henselian_target
        (I := maximalIdeal A)
        (B := A_h)
        (K := henselizationIdeal A_pair)
        (pair_henselization_henselianRing (A := A))
        Ideal.le_comap_map
  have hcomp :
      ((henselized_stage_directLimit_to_target_pair_henselization (A := A)).comp
          (target_pair_henselization_to_henselized_directLimit (A := A))).comp
          (toHenselization A_pair) =
        algebraMap A A_h := by
    let κ := z_adjoin_local_stage_directLimit_to_henselized_directLimit (A := A)
    let e := z_adjoin_local_stage_directLimit_equiv (A := A)
    calc
      ((henselized_stage_directLimit_to_target_pair_henselization (A := A)).comp
          (target_pair_henselization_to_henselized_directLimit (A := A))).comp
          (toHenselization A_pair) =
        (henselized_stage_directLimit_to_target_pair_henselization (A := A)).comp
          ((target_pair_henselization_to_henselized_directLimit (A := A)).comp
            (toHenselization A_pair)) := by
              rw [RingHom.comp_assoc]
      _ =
        (henselized_stage_directLimit_to_target_pair_henselization (A := A)).comp
          (κ.comp e.symm.toRingHom) := by
              rw [target_pair_henselization_to_henselized_directLimit_comp (A := A)]
      _ =
        ((henselized_stage_directLimit_to_target_pair_henselization (A := A)).comp κ).comp
          e.symm.toRingHom := by
              rw [RingHom.comp_assoc]
      _ = algebraMap A A_h := by
            ext a
            let s : Finset A := {a}
            let aStage : z_adjoin_stage (A := A) s :=
              ⟨a, by
                exact Algebra.subset_adjoin (by simp [s])⟩
            have hs :
                e.symm a =
                  Ring.DirectLimit.of
                    (fun t : Finset A ↦ z_adjoin_local_stage (A := A) t)
                    (fun t u htu ↦ z_adjoin_local_stage_transition (A := A) htu)
                    s
                    (algebraMap
                      (z_adjoin_stage (A := A) s)
                      (z_adjoin_local_stage (A := A) s) aStage) := by
              apply e.injective
              simp [e, z_adjoin_local_stage_directLimit_equiv, aStage, s,
                z_adjoin_local_stage_to_target, Localization.localRingHom_to_map]
            rw [hs]
            simp [RingHom.comp_apply,
              z_adjoin_local_stage_directLimit_to_henselized_directLimit_comp_of (A := A) s,
              henselized_stage_directLimit_to_target_pair_henselization_comp_of (A := A) s,
              z_adjoin_henselized_stage_to_target_pair_henselization_comp (A := A) s,
              z_adjoin_local_stage_to_target, Localization.localRingHom_to_map, aStage, s]
  have hid :
      (RingHom.id A_h).comp (toHenselization A_pair) = algebraMap A A_h := by
    rfl
  calc
    (henselized_stage_directLimit_to_target_pair_henselization (A := A)).comp
        (target_pair_henselization_to_henselized_directLimit (A := A)) = u :=
      hu_unique _ hcomp
    _ = RingHom.id A_h := (hu_unique _ hid).symm

/-- Helper for Lemma 15.50.13: composing the two canonical maps on the henselized-stage direct
limit gives the identity. -/
private lemma henselized_stage_directLimit_endomorphism_is_id :
    (target_pair_henselization_to_henselized_directLimit (A := A)).comp
        (henselized_stage_directLimit_to_target_pair_henselization (A := A)) =
      RingHom.id H∞ := by
  apply Ring.DirectLimit.hom_ext
  intro s
  obtain ⟨u, hu, hu_unique⟩ :=
    ExistsUnique.exists <|
      existsUnique_henselizationRingHom_of_henselian_target
        (I := maximalIdeal (z_adjoin_local_stage (A := A) s))
        (B := H∞)
        (K := maximalIdeal H∞)
        (by infer_instance)
        (by
          -- Proof comment: the stage-localized map into `H∞` is local, so it sends the closed
          -- point into the closed point.
          simpa using
            (show
              maximalIdeal (z_adjoin_local_stage (A := A) s) ≤
                Ideal.comap
                  (z_adjoin_local_stage_to_henselized_directLimit (A := A) s)
                  (maximalIdeal H∞) by
                simpa using
                  (show
                    maximalIdeal (z_adjoin_local_stage (A := A) s) ≤
                      maximalIdeal (z_adjoin_local_stage (A := A) s) from
                    le_rfl)))
  have hleft :
      (((target_pair_henselization_to_henselized_directLimit (A := A)).comp
          (henselized_stage_directLimit_to_target_pair_henselization (A := A))).comp
          (Ring.DirectLimit.of
            (fun t : Finset A ↦ z_adjoin_henselized_stage (A := A) t)
            (fun t u htu ↦ z_adjoin_henselized_stage_transition (A := A) htu)
            s)).comp
            (algebraMap
              (z_adjoin_local_stage (A := A) s)
              (z_adjoin_henselized_stage (A := A) s)) =
        z_adjoin_local_stage_to_henselized_directLimit (A := A) s := by
    calc
      (((target_pair_henselization_to_henselized_directLimit (A := A)).comp
          (henselized_stage_directLimit_to_target_pair_henselization (A := A))).comp
          (Ring.DirectLimit.of
            (fun t : Finset A ↦ z_adjoin_henselized_stage (A := A) t)
            (fun t u htu ↦ z_adjoin_henselized_stage_transition (A := A) htu)
            s)).comp
            (algebraMap
              (z_adjoin_local_stage (A := A) s)
              (z_adjoin_henselized_stage (A := A) s)) =
        (target_pair_henselization_to_henselized_directLimit (A := A)).comp
          ((henselized_stage_directLimit_to_target_pair_henselization (A := A)).comp
            (Ring.DirectLimit.of
              (fun t : Finset A ↦ z_adjoin_henselized_stage (A := A) t)
              (fun t u htu ↦ z_adjoin_henselized_stage_transition (A := A) htu)
              s)).comp
                (algebraMap
                  (z_adjoin_local_stage (A := A) s)
                  (z_adjoin_henselized_stage (A := A) s)) := by
                    rw [RingHom.comp_assoc, RingHom.comp_assoc]
      _ =
        (target_pair_henselization_to_henselized_directLimit (A := A)).comp
          ((z_adjoin_henselized_stage_to_target_pair_henselization (A := A) s).comp
            (algebraMap
              (z_adjoin_local_stage (A := A) s)
              (z_adjoin_henselized_stage (A := A) s))) := by
                rw [henselized_stage_directLimit_to_target_pair_henselization_comp_of (A := A) s]
      _ =
        (target_pair_henselization_to_henselized_directLimit (A := A)).comp
          ((toHenselization A_pair).comp
            (z_adjoin_local_stage_to_target (A := A) s)) := by
                rw [z_adjoin_henselized_stage_to_target_pair_henselization_comp (A := A) s]
      _ =
        ((target_pair_henselization_to_henselized_directLimit (A := A)).comp
          (toHenselization A_pair)).comp
            (z_adjoin_local_stage_to_target (A := A) s) := by
                rw [RingHom.comp_assoc]
      _ =
        ((z_adjoin_local_stage_directLimit_to_henselized_directLimit (A := A)).comp
          (z_adjoin_local_stage_directLimit_equiv (A := A)).symm.toRingHom).comp
            (z_adjoin_local_stage_to_target (A := A) s) := by
                rw [target_pair_henselization_to_henselized_directLimit_comp (A := A)]
      _ =
        (z_adjoin_local_stage_directLimit_to_henselized_directLimit (A := A)).comp
          (((z_adjoin_local_stage_directLimit_equiv (A := A)).symm.toRingHom).comp
            (z_adjoin_local_stage_to_target (A := A) s)) := by
                rw [RingHom.comp_assoc]
      _ =
        z_adjoin_local_stage_to_henselized_directLimit (A := A) s := by
            ext x
            have hs :
                (z_adjoin_local_stage_directLimit_equiv (A := A)).symm
                    (z_adjoin_local_stage_to_target (A := A) s x) =
                  Ring.DirectLimit.of
                    (fun t : Finset A ↦ z_adjoin_local_stage (A := A) t)
                    (fun t u htu ↦ z_adjoin_local_stage_transition (A := A) htu)
                    s x := by
              apply (z_adjoin_local_stage_directLimit_equiv (A := A)).injective
              simpa [RingHom.comp_apply] using
                congrArg
                  (fun f :
                    z_adjoin_local_stage (A := A) s →+*
                      A ↦ f x)
                  (z_adjoin_local_stage_directLimitToTarget_comp_of (A := A) s)
            rw [hs]
            simp [RingHom.comp_apply,
              z_adjoin_local_stage_directLimit_to_henselized_directLimit_comp_of (A := A) s]
  have hright :
      (Ring.DirectLimit.of
          (fun t : Finset A ↦ z_adjoin_henselized_stage (A := A) t)
          (fun t u htu ↦ z_adjoin_henselized_stage_transition (A := A) htu)
          s).comp
          (algebraMap
            (z_adjoin_local_stage (A := A) s)
            (z_adjoin_henselized_stage (A := A) s)) =
        z_adjoin_local_stage_to_henselized_directLimit (A := A) s := by
    rfl
  have hleft_eq :
      ((target_pair_henselization_to_henselized_directLimit (A := A)).comp
          (henselized_stage_directLimit_to_target_pair_henselization (A := A))).comp
          (Ring.DirectLimit.of
            (fun t : Finset A ↦ z_adjoin_henselized_stage (A := A) t)
            (fun t u htu ↦ z_adjoin_henselized_stage_transition (A := A) htu)
            s) = u := by
    apply RingHom.ext
    exact hu_unique _ hleft
  have hright_eq :
      Ring.DirectLimit.of
          (fun t : Finset A ↦ z_adjoin_henselized_stage (A := A) t)
          (fun t u htu ↦ z_adjoin_henselized_stage_transition (A := A) htu)
          s = u := by
    apply RingHom.ext
    exact hu_unique _ hright
  exact hleft_eq.trans hright_eq.symm

/-- Helper for Lemma 15.50.13: because `A` is already henselian, its pair henselization is
canonically isomorphic to `A` itself. -/
private noncomputable def henselian_local_ring_equiv_pair_henselization :
    A_h ≃+* A := by
  let f : A_h →+* A :=
    Classical.choose <|
      ExistsUnique.exists <|
        existsUnique_henselizationRingHom_of_henselian_target
          (I := maximalIdeal A)
          (B := A)
          (K := maximalIdeal A)
          (by infer_instance)
          (show maximalIdeal A ≤ Ideal.comap (algebraMap A A) (maximalIdeal A) by simpa)
  have hf :
      f.comp (toHenselization A_pair) = algebraMap A A := by
    exact Classical.choose_spec <|
      ExistsUnique.exists <|
        existsUnique_henselizationRingHom_of_henselian_target
          (I := maximalIdeal A)
          (B := A)
          (K := maximalIdeal A)
          (by infer_instance)
          (show maximalIdeal A ≤ Ideal.comap (algebraMap A A) (maximalIdeal A) by simpa)
  have hηf : (toHenselization A_pair).comp f = RingHom.id A_h := by
    obtain ⟨u, hu, hu_unique⟩ :=
      ExistsUnique.exists <|
        existsUnique_henselizationRingHom_of_henselian_target
          (I := maximalIdeal A)
          (B := A_h)
          (K := henselizationIdeal A_pair)
          (pair_henselization_henselianRing (A := A))
          Ideal.le_comap_map
    have hcomp :
        ((toHenselization A_pair).comp f).comp (toHenselization A_pair) = algebraMap A A_h := by
      rw [RingHom.comp_assoc, hf]
      simp
    have hid : (RingHom.id A_h).comp (toHenselization A_pair) = algebraMap A A_h := by
      rfl
    calc
      (toHenselization A_pair).comp f = u := hu_unique _ hcomp
      _ = RingHom.id A_h := (hu_unique _ hid).symm
  have hf_injective : Function.Injective f := by
    intro x y hxy
    have hxy' := congrArg (fun z ↦ (toHenselization A_pair) z) hxy
    simpa [hηf] using hxy'
  have hf_surjective : Function.Surjective f := by
    intro a
    refine ⟨toHenselization A_pair a, ?_⟩
    simpa using congrArg (fun g : A →+* A ↦ g a) hf
  -- Proof comment: the inverse map is the unit `A → A^h`, and the uniqueness argument above shows
  -- that the two composites are identities.
  exact RingEquiv.ofBijective f ⟨hf_injective, hf_surjective⟩

/- Domain-style sampling:
- primary domain: henselian local rings, `G`-rings, and filtered direct limits in commutative
  algebra;
- sampled owner declarations:
  `HenselianLocalRing`,
  `IsGRing`,
  `Ring.DirectLimit`,
  `directedSystem_directLimit_henselianLocalRing`;
- best owner abstraction: the stagewise notions are already owned canonically by
  `HenselianLocalRing`, `IsGRing`, `IsLocalHom`, and `Ring.DirectLimit`; there is no reusable
  chapter owner for the full filtered-colimit presentation, so the source-facing item should be
  the explicit existential theorem rather than a one-off wrapper `Prop`;
- primitive data: the filtered index type, stage rings, transition maps, their local-hom
  property, and the direct-limit comparison isomorphism to `A`;
- derived API: henselianity of the direct limit is already owned upstream by
  `directedSystem_directLimit_henselianLocalRing`.

Source/core/bridge triage:
- `source-facing`: `exists_filtered_colimit_of_henselian_local_grings`;
- `core/canonical`: `HenselianLocalRing`, `IsGRing`, `IsLocalHom`, and `Ring.DirectLimit`;
- `bridge/view`: the chosen finite-stage henselization diagram and comparison isomorphism
  presenting `A` as that direct limit.
-/

-- Proof sketch: write `A` as a filtered colimit of finite type `ℤ`-algebras, localize each stage
-- at the prime lying under the maximal ideal of `A`, and then henselize those local stages.
-- Proposition `15.50.12` makes the localized finite stages into `G`-rings, Lemma `15.50.8`
-- preserves the `G`-ring property under henselization, and Lemma `15.12.5` identifies the direct
-- limit of the henselizations with `A`.
/-- Lemma 15.50.13: a henselian local ring is a filtered colimit of a directed system of henselian
local `G`-rings with local transition maps. -/
theorem exists_filtered_colimit_of_henselian_local_grings :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : Nonempty ι) (_ : IsDirectedOrder ι)
      (stage : ι → Type u) (_ : ∀ i : ι, CommRing (stage i))
      (_ : ∀ i : ι, HenselianLocalRing (stage i))
      (_ : ∀ i : ι, IsGRing (stage i))
      (map : ∀ i j : ι, i ≤ j → stage i →+* stage j)
      (_ : DirectedSystem stage (fun i j hij ↦ map i j hij))
      (e : Ring.DirectLimit stage (fun i j hij ↦ map i j hij) ≃+* A),
      ∀ i j (hij : i ≤ j), IsLocalHom (map i j hij) := by
  let stage : Finset A → Type u := z_adjoin_henselized_stage (A := A)
  let map : ∀ s t : Finset A, s ≤ t → stage s →+* stage t :=
    fun s t hst ↦ z_adjoin_henselized_stage_transition (A := A) hst
  have hdir :
      DirectedSystem stage (fun s t hst ↦ map s t hst) := by
    refine
      { map_self := ?_
        map_map := ?_ }
    · intro s x
      -- Proof comment: the self-transition of the henselized stage is the identity by the
      -- uniqueness of local maps between henselizations of the same local ring.
      simpa [map] using
        congrArg (fun f : stage s →+* stage s ↦ f x)
          (z_adjoin_henselized_stage_transition_self (A := A) s)
    · intro s t u hst htu x
      -- Proof comment: both composites are local maps between henselizations of the same source
      -- and target local rings, so the universal property identifies them.
      simpa [map] using
        congrArg (fun f : stage s →+* stage u ↦ f x)
          (z_adjoin_henselized_stage_transition_comp (A := A) hst htu)
  -- Route correction: the localized finite-stage direct-limit comparison with `A` is now proved
  -- above, so the only remaining source-faithful step is to transport that colimit through pair
  -- henselization and compare the resulting self-henselization with `A`.
  -- TODO: apply Lemma `15.12.5` to the localized-stage pair diagram, rewrite the colimit pair via
  -- `z_adjoin_local_stage_directLimit_equiv` and
  -- `z_adjoin_local_stage_directLimit_maximalIdeal`, and then close with the uniqueness of local
  -- maps between henselizations using `henselian_self_is_henselization`.
  have he :
      Ring.DirectLimit stage (fun s t hst ↦ map s t hst) ≃+* A := sorry
  have hlocal :
      ∀ s t (hst : s ≤ t), IsLocalHom (map s t hst) := by
    intro s t hst
    -- Proof comment: `map` was defined from the canonical henselization comparison maps, whose
    -- locality is already owned by Chapter 10.
    simpa [map] using z_adjoin_henselized_stage_transition_isLocalHom (A := A) hst
  refine
    ⟨Finset A, inferInstance, inferInstance, inferInstance, stage, (fun s ↦ inferInstance), ?_,
      ?_, map, hdir, he, hlocal⟩
  · -- Proof comment: every canonical pair-henselized stage is henselian local by construction.
    intro s
    simpa [stage] using z_adjoin_henselized_stage_henselianLocalRing (A := A) s
  · -- Proof comment: the localized finite stage is a `G`-ring, and henselization preserves that
    -- owner property.
    intro s
    simpa [stage] using z_adjoin_henselized_stage_is_gring (A := A) s

end
