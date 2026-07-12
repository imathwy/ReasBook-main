import StacksProject_2024.Chap10.Lemma_10_127_11_Tower
import Mathlib.Tactic.StacksAttribute

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

section SameUniverse

variable {R S : Type u} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
variable (f : R →+* S) [IsLocalHom f]

/-- Lemma 10.127.11: if `f : R →+* S` is a local homomorphism of local rings and `S` is essentially
of finite presentation over `R`, then there is a directed system of local homomorphisms
approximating `f` whose source stages are essentially of finite type over `ℤ`, whose target
stages are essentially of finite type over the corresponding source stages, and whose transition
maps identify each stage after base change with a localization at a prime ideal. -/
@[stacks 00QV]
theorem exists_localEssFinitePresentationApproximation
    (hf : f.EssFinitePresentation) :
    ∃ A : DirectedLocalHomApproximation.{u, u, u} f,
      DirectedLocalHomApproximation.HasPrimeLocalizationTransitions A := by
  classical
  obtain ⟨A₀, _, hA₀lim, P, _, g, _, q, hq, _, hlocq, hfg, _, i₀, P₀, _, _, _, ⟨e⟩⟩ :=
    exists_descended_local_finitePresentation_model (f := f) hf
  letI : Algebra R P := g.toAlgebra
  -- Proof comment: the source-faithful prefix is now fixed. We have
  -- * an `id_R` approximation `A₀`,
  -- * a descended finitely presented algebra `P₀` at stage `i₀`,
  -- * the comparison equivalence `e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P`,
  -- * and the prime `q` of `P` lying over `maximalIdeal R`.
  letI : Algebra (A₀.RStage i₀) R :=
    (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀).toAlgebra
  have hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀ := rfl
  have hPalg : algebraMap R P = g := rfl
  let tail : Type u := Set.Ici i₀
  letI : Preorder tail := inferInstance
  letI : Nonempty tail := inferInstance
  letI : IsDirectedOrder tail := tail_index_isDirected i₀
  let rawStage : tail → Type u := descendedTailRawStage A₀ i₀ P₀
  let rawMap : ∀ j k : tail, j ≤ k → rawStage j →+* rawStage k := fun j k hjk ↦
    descendedTailRawMap A₀ i₀ P₀ j k hjk
  let σ : (j : tail) → rawStage j →+* S := fun j ↦
    descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e j
  let qTail : (j : tail) → Ideal (rawStage j) := fun j ↦
    Ideal.comap (σ j) (IsLocalRing.maximalIdeal S)
  have hσ_comp :
      ∀ j : tail,
        (σ j).comp (algebraMap (A₀.RStage j.1) (rawStage j)) =
          f.comp
            (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso j.1) :=
      by
    intro j
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
    letI : Algebra (A₀.RStage j.1) R :=
      RingHom.toAlgebra
        (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso j.1)
    letI : IsScalarTower (A₀.RStage i₀) (A₀.RStage j.1) R :=
      Ring.DirectLimit.toLimit_isScalarTower A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso j.2
    ext x
    -- The raw stage comparison sends the right-factor generator `x` to its image in `R`, then
    -- transports across the descended model `e` and finally into `S`, which recovers `f`.
    simp only [σ, RingHom.comp_apply, hfg]
    have h1 : (algebraMap (A₀.RStage j.1) (rawStage j)) x =
        (1 : P₀) ⊗ₜ[A₀.RStage i₀] x := rfl
    rw [h1]
    simp only [RingHom.coe_coe]
    exact congrArg (algebraMap P S) (e.commutes ((algebraMap (A₀.RStage j.1) R) x))
  have hσ_local :
      ∀ j : tail,
        IsLocalHom ((σ j).comp (algebraMap (A₀.RStage j.1) (rawStage j))) := by
    intro j
    haveI := hA₀lim j.1
    rw [hσ_comp j]
    -- The descended raw comparison is local because it factors as the local stage-to-limit map
    -- into `R` followed by the given local homomorphism `f`.
    exact RingHom.isLocalHom_comp _ _
  have hqTail_prime :
      ∀ j : tail, (qTail j).IsPrime := by
    intro j
    -- Each contracted maximal ideal is prime because the target ring `S` is local.
    simpa [qTail] using Ideal.comap_isPrime (σ j) (IsLocalRing.maximalIdeal S)
  let j0 : tail := ⟨i₀, le_rfl⟩
  have hσ_raw_comp :
      ∀ j k : tail, ∀ hjk : j ≤ k, σ j = (σ k).comp (rawMap j k hjk) := by
    intro j k hjk
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
    letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.map i₀ k.1 k.2).toAlgebra
    letI : Algebra (A₀.RStage j.1) R :=
      RingHom.toAlgebra
        (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso j.1)
    letI : Algebra (A₀.RStage k.1) R :=
      RingHom.toAlgebra
        (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso k.1)
    letI : IsScalarTower (A₀.RStage i₀) (A₀.RStage j.1) R :=
      Ring.DirectLimit.toLimit_isScalarTower A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso j.2
    letI : IsScalarTower (A₀.RStage i₀) (A₀.RStage k.1) R :=
      Ring.DirectLimit.toLimit_isScalarTower A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso k.2
    refine RingHom.ext fun x ↦ ?_
    -- Proof comment: both tensor-stage comparison maps first move from `R_j` to `R`, and the
    -- compatibility of `A₀` with its colimit identifies the two resulting tensor maps.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp only [map_zero]
    · intro x y
      simp only [σ, rawMap, RingHom.comp_apply]
      have hy : Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso
            k.1 ((A₀.map j.1 k.1 hjk) y) =
          Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso j.1 y :=
        by simp [Ring.DirectLimit.toLimitHom, Ring.DirectLimit.of_f]
      exact (congrArg (algebraMap P S)
        (congrArg e (congrArg (fun r ↦ (x : P₀) ⊗ₜ[A₀.RStage i₀] r) hy))).symm
    · intro x y hx hy
      simp [map_add, hx, hy]
  let SStage : tail → Type u := fun j ↦
    Localization.AtPrime (Ideal.comap (σ j) (IsLocalRing.maximalIdeal S))
  let targetMap : ∀ j k : tail, j ≤ k → SStage j →+* SStage k := fun j k hjk ↦
    Localization.localRingHom (Ideal.comap (σ j) (IsLocalRing.maximalIdeal S))
      (Ideal.comap (σ k) (IsLocalRing.maximalIdeal S)) (rawMap j k hjk)
      ((comap_contracted_maximalIdeal_eq_of_comp
        (τ := rawMap j k hjk) (σA := σ j) (σB := σ k) (hσ_raw_comp j k hjk)).symm)
  have hqTail_comp :
      ∀ j k : tail, ∀ hjk : j ≤ k,
        Ideal.comap (rawMap j k hjk) (qTail k) = qTail j := by
    intro j k hjk
    -- Proof comment: the contracted maximal ideals agree because the stage comparisons to `S`
    -- differ only by precomposition with the raw transition map.
    exact comap_contracted_maximalIdeal_eq_of_comp
      (τ := rawMap j k hjk) (σA := σ j) (σB := σ k) (hσ_raw_comp j k hjk)
  have rawMap_id : ∀ j : tail, rawMap j j le_rfl = RingHom.id _ := by
    intro j
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
    refine RingHom.ext fun x ↦ ?_
    -- Proof comment: on a fixed stage the tensor transition uses the identity on the right
    -- factor, so it is the identity map.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp [rawMap]
    · intro x y
      simp only [rawMap,
        RingHom.id_apply]
      exact congrArg (fun r ↦ (x : P₀) ⊗ₜ[A₀.RStage i₀] r)
        (DirectedSystem.map_self (f := fun i j h ↦ A₀.map i j h) y)
    · intro x y hx hy
      simp [map_add, hx, hy]
  have rawMap_comp :
      ∀ i j k : tail, ∀ hij : i ≤ j, ∀ hjk : j ≤ k,
        rawMap i k (le_trans hij hjk) = (rawMap j k hjk).comp (rawMap i j hij) := by
    intro i j k hij hjk
    letI : Algebra (A₀.RStage i₀) (A₀.RStage i.1) := (A₀.map i₀ i.1 i.2).toAlgebra
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
    letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.map i₀ k.1 k.2).toAlgebra
    refine RingHom.ext fun x ↦ ?_
    -- Proof comment: the tensor transition maps only change the right factor, so composition is
    -- inherited from the source directed system.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp [rawMap]
    · intro x y
      simp only [rawMap, RingHom.comp_apply]
      exact congrArg (fun r ↦ (x : P₀) ⊗ₜ[A₀.RStage i₀] r)
        (DirectedSystem.map_map (f := fun i j h ↦ A₀.map i j h) hij hjk y).symm
    · intro x y hx hy
      simp [map_add, hx, hy]
  haveI : DirectedSystem rawStage (fun j k h ↦ rawMap j k h) :=
    { map_self := fun j x ↦ by
        simpa using congrArg (fun g : rawStage j →+* rawStage j => g x) (rawMap_id j)
      map_map := fun {k j i} hij hjk x ↦ by
        simpa [RingHom.comp_apply] using
          (congrArg (fun g : rawStage i →+* rawStage k => g x)
            (rawMap_comp i j k hij hjk)).symm }
  haveI targetDirectedSystem :
      DirectedSystem SStage (fun j k h ↦ targetMap j k h) :=
    { map_self := by
        intro j x
        have hself :
            targetMap j j le_rfl = RingHom.id (SStage j) := by
          -- Proof comment: after identifying the raw transition with the identity, the induced
          -- localization map is the canonical identity localization map.
          apply Localization.localRingHom_unique
          intro x
          simp [rawMap_id j]
        simpa using congrArg (fun g : SStage j →+* SStage j => g x) hself
      map_map := by
        intro k j i hij hjk x
        have hcomp :
            targetMap i k (le_trans hij hjk) =
              (targetMap j k hjk).comp (targetMap i j hij) := by
          -- Proof comment: once the raw transitions compose, the canonical maps between prime
          -- localizations compose as well.
          simpa [targetMap, rawMap_comp i j k hij hjk] using
            (Localization.localRingHom_comp
              (R := rawStage i)
              (S := rawStage j)
              (P := rawStage k)
              (I := qTail i)
              (J := qTail j)
              (K := qTail k)
              (f := rawMap i j hij)
              ((hqTail_comp i j hij).symm)
              (g := rawMap j k hjk)
              ((hqTail_comp j k hjk).symm))
        simpa [RingHom.comp_apply] using
          (congrArg (fun g : SStage i →+* SStage k => g x) hcomp).symm }
  let stageMapTail :
      ∀ j : tail, A₀.RStage j.1 →+* SStage j := fun j ↦ algebraMap _ _
  have hstageMapTail_local :
      ∀ j : tail, IsLocalHom (stageMapTail j) := by
    intro j
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
    -- Proof comment: each target stage is defined by localizing the descended tensor algebra at
    -- the prime cut out by the final comparison to `S`.
    simpa [stageMapTail, SStage, qTail] using
      (localized_descended_stage_of_local_comparison
        (R₀ := A₀.RStage i₀) (Rj := A₀.RStage j.1) (P₀ := P₀) (T := S) (σ := σ j)).1
  have hstageMapTail_essFiniteType :
      ∀ j : tail, (stageMapTail j).EssFiniteType := by
    intro j
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
    -- Proof comment: finite presentation of the descended algebra plus prime localization gives
    -- the stagewise essential finite-type property required by the approximation object.
    simpa [stageMapTail, SStage, qTail] using
      (localized_descended_stage_of_local_comparison
        (R₀ := A₀.RStage i₀) (Rj := A₀.RStage j.1) (P₀ := P₀) (T := S) (σ := σ j)).2
  have hcommTail :
      ∀ {j k : tail} (hjk : j ≤ k),
        (stageMapTail k).comp (A₀.map j.1 k.1 hjk) =
          (targetMap j k hjk).comp (stageMapTail j) := by
    intro j k hjk
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
    letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.map i₀ k.1 k.2).toAlgebra
    refine RingHom.ext fun x ↦ ?_
    -- Proof comment: both composites are canonical maps from the earlier source stage into the
    -- prime localization of the later raw tensor stage.
    have h2 : rawMap j k hjk ((1 : P₀) ⊗ₜ[A₀.RStage i₀] x) =
        (1 : P₀) ⊗ₜ[A₀.RStage i₀] ((A₀.map j.1 k.1 hjk) x) := by
      simp only [rawMap]
      rfl
    symm
    calc (targetMap j k hjk) ((stageMapTail j) x)
        = algebraMap (rawStage k) (SStage k)
            (rawMap j k hjk ((1 : P₀) ⊗ₜ[A₀.RStage i₀] x)) := by
          rw [show (stageMapTail j) x =
            algebraMap (rawStage j) (SStage j) ((1 : P₀) ⊗ₜ[A₀.RStage i₀] x) from rfl]
          exact Localization.localRingHom_to_map _ _ _ _ _
      _ = algebraMap (rawStage k) (SStage k)
            ((1 : P₀) ⊗ₜ[A₀.RStage i₀] ((A₀.map j.1 k.1 hjk) x)) :=
          congrArg (algebraMap (rawStage k) (SStage k)) h2
      _ = (stageMapTail k) ((A₀.map j.1 k.1 hjk) x) := rfl
  have hstageMapTail_apply : ∀ (j : tail) (x : A₀.RStage j.1),
      stageMapTail j x =
        algebraMap (rawStage j) (SStage j)
          ((algebraMap (A₀.RStage j.1) (rawStage j)) x) := by
    intro j x
    rfl
  have hSourceStage : ∀ (i : tail) (x : A₀.RStage i.1),
      sourceToTargetDirectLimitOf A₀ i₀ SStage targetMap stageMapTail
          (fun {j} {k} hjk ↦ hcommTail hjk)
          (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h)
            A₀.colimitIso i.1 x) =
        Ring.DirectLimit.of SStage (fun j k h ↦ targetMap j k h) i (stageMapTail i x) := by
    intro i x
    exact sourceToTargetDirectLimit_stage_of (A₀ := A₀) (i₀ := i₀)
      (SStage := SStage) (targetMap := targetMap) (stageMapTail := stageMapTail)
      (hcommTail := fun {j} {k} hjk ↦ hcommTail hjk) i x
  -- The remaining blocker is now concentrated in the source-faithful global comparisons:
  -- 1. identify the direct limit of the raw tail system with the descended model `P`,
  -- 2. identify the direct limit of the localized stages `SStage` with `S`,
  -- 3. normalize each owner base-change domain and transport the canonical localization map back
  --    by `transitionIsLocalizationAtPrime_of_domain_equiv`.
  let sourceColimitIso :
      Ring.DirectLimit (fun j : tail ↦ A₀.RStage j.1) (fun j k h ↦ A₀.map j.1 k.1 h) ≃+* R :=
    tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.map i j h) i₀ A₀.colimitIso
  exact finish_localEssFinitePresentationApproximation (f := f) A₀ g q hlocq hfg i₀ e
    hRalg hPalg inferInstance hσ_comp hσ_raw_comp
    targetDirectedSystem stageMapTail hstageMapTail_apply hstageMapTail_local
    hstageMapTail_essFiniteType (fun {j} {k} hjk ↦ hcommTail hjk) hSourceStage

end SameUniverse
