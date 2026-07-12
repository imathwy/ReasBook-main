import StacksProject_2024.Chap10.Lemma_10_127_13.MixedTargetStages

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w uR uS uM uN

section

variable {R : Type uR} {S : Type uS} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
variable (f : R →+* S) [IsLocalHom f]
variable {M : Type uM} [AddCommGroup M] [Module S M]

/-- Helper for Lemma 10.127.13: package the joint-universe localized tail data needed to rebuild
the target colimit without re-expanding the full construction at every call site. -/
structure JointUniverseTargetTailData
    (A₀ : DirectedLocalHomApproximation.{uR, uR, uR} (RingHom.id R))
    {P : Type uR} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type uR) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (hσ_raw_comp : ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
      descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j =
        (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k).comp
          (descendedTailRawMap A₀ i₀ P₀ j k hjk)) where
  instTailDirected : IsDirectedOrder (Set.Ici i₀)
  instDirectedSystemRaw :
    DirectedSystem (descendedTailRawStage A₀ i₀ P₀)
      (fun j k h ↦ descendedTailRawMap A₀ i₀ P₀ j k h)
  instDirectedSystemTarget :
    DirectedSystem (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e)
      (fun j k h ↦ descendedTailTargetMapJointUniverse
        (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k h)
  stageMapTail : (j : Set.Ici i₀) → A₀.RStage j.1 →+*
    descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e j
  hstageMapTail_apply : ∀ (j : Set.Ici i₀) (x : A₀.RStage j.1),
    stageMapTail j x =
      algebraMap (descendedTailRawStage A₀ i₀ P₀ j)
        (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e j)
        ((algebraMap (A₀.RStage j.1) (descendedTailRawStage A₀ i₀ P₀ j)) x)
  hcommTail : ∀ {j k : Set.Ici i₀} (hjk : j ≤ k),
    (stageMapTail k).comp (A₀.map j.1 k.1 hjk) =
      (descendedTailTargetMapJointUniverse
        (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k hjk).comp
        (stageMapTail j)
  hSourceStage : ∀ (i : Set.Ici i₀) (x : A₀.RStage i.1),
    sourceToTargetDirectLimitOf A₀ i₀
      (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e)
      (descendedTailTargetMapJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp)
      stageMapTail (fun {j} {k} hjk ↦ hcommTail hjk)
      (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h)
        A₀.colimitIso i.1 x) =
    descendedTailTargetOfJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp i
      (stageMapTail i x)
  htargetColimitToAmbient_comm :
    (tail_target_colimit_to_ambient (S := S)
        (descendedTailRawStage A₀ i₀ P₀) (descendedTailRawMap A₀ i₀ P₀)
        (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e) hσ_raw_comp).comp
        (Ring.DirectLimit.map stageMapTail (fun _ _ h ↦ hcommTail h)) =
      f.comp (tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.map i j h)
        i₀ A₀.colimitIso).toRingHom

/-- Helper for Lemma 10.127.13: package the mixed-universe descended tail data before rebuilding
the target colimit. This isolates the source-faithful tail-system construction from the later
owner packaging. -/
noncomputable def joint_universe_target_tail_data
    (A₀ : DirectedLocalHomApproximation.{uR, uR, uR} (RingHom.id R))
    {P : Type uR} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type uR) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    [Algebra.FinitePresentation (A₀.RStage i₀) P₀]
    (hfg : f = (algebraMap P S).comp (algebraMap R P))
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (hσ_raw_comp : ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
      descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j =
        (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k).comp
          (descendedTailRawMap A₀ i₀ P₀ j k hjk)) :
    JointUniverseTargetTailData (f := f) (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp := by
  let tail : Type uR := Set.Ici i₀
  letI : Preorder tail := inferInstance
  letI : Nonempty tail := inferInstance
  letI : IsDirectedOrder tail := tail_index_isDirected i₀
  let rawStage : tail → Type uR := descendedTailRawStage A₀ i₀ P₀
  let rawMap : ∀ j k : tail, j ≤ k → rawStage j →+* rawStage k := fun j k hjk ↦
    descendedTailRawMap A₀ i₀ P₀ j k hjk
  let SStage : tail → Type uR := descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e
  let targetMap : ∀ j k : tail, j ≤ k → SStage j →+* SStage k := fun j k hjk ↦
    descendedTailTargetMapJointUniverse
      (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k hjk
  have hqTail_comp :
      ∀ j k : tail, ∀ hjk : j ≤ k,
        Ideal.comap (rawMap j k hjk)
            (Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k)
              (IsLocalRing.maximalIdeal S)) =
          Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j)
            (IsLocalRing.maximalIdeal S) := by
    intro j k hjk
    -- Proof comment: the contracted maximal ideals agree because the later stage comparison to
    -- `S` factors through the earlier one by the raw transition map.
    exact comap_contracted_maximalIdeal_eq_of_comp
      (S := S) (τ := rawMap j k hjk)
      (σA := descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j)
      (σB := descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k)
      (hσ_raw_comp j k hjk)
  have rawMap_id : ∀ j : tail, rawMap j j le_rfl = RingHom.id _ := by
    intro j
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
    refine RingHom.ext fun x ↦ ?_
    -- Proof comment: on a fixed stage, the raw transition only acts on the right tensor factor by
    -- the identity map of the source directed system.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp [rawMap]
    · intro x y
      simp only [rawMap, RingHom.id_apply]
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
    -- Proof comment: the raw tensor transitions compose because they only rewrite the right tensor
    -- factor through the source directed system.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp [rawMap]
    · intro x y
      simp only [rawMap, RingHom.comp_apply]
      exact congrArg (fun r ↦ (x : P₀) ⊗ₜ[A₀.RStage i₀] r)
        (DirectedSystem.map_map (f := fun i j h ↦ A₀.map i j h) hij hjk y).symm
    · intro x y hx hy
      simp [map_add, hx, hy]
  letI : DirectedSystem rawStage (fun j k h ↦ rawMap j k h) :=
    { map_self := fun j x ↦ by
        simpa using congrArg (fun g : rawStage j →+* rawStage j ↦ g x) (rawMap_id j)
      map_map := fun {k j i} hij hjk x ↦ by
        simpa [RingHom.comp_apply] using
          (congrArg (fun g : rawStage i →+* rawStage k ↦ g x)
            (rawMap_comp i j k hij hjk)).symm }
  letI : DirectedSystem SStage (fun j k h ↦ targetMap j k h) :=
    { map_self := by
        intro j x
        have hself : targetMap j j le_rfl = RingHom.id (SStage j) := by
          -- Proof comment: once the raw self-transition is the identity, the induced localization
          -- map is the canonical identity localization map.
          change Localization.localRingHom
              (Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j)
                (IsLocalRing.maximalIdeal S))
              (Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j)
                (IsLocalRing.maximalIdeal S))
              (rawMap j j le_rfl)
              ((hqTail_comp j j le_rfl).symm) = RingHom.id (SStage j)
          exact Localization.localRingHom_unique _ _ _ _ fun y ↦ by
            have hy : rawMap j j le_rfl y = y := by
              simpa using congrArg (fun g : rawStage j →+* rawStage j ↦ g y) (rawMap_id j)
            rw [hy]
            rfl
        simpa using congrArg (fun g : SStage j →+* SStage j ↦ g x) hself
      map_map := by
        intro k j i hij hjk x
        have hcomp :
            targetMap i k (le_trans hij hjk) =
              (targetMap j k hjk).comp (targetMap i j hij) := by
          -- Proof comment: the canonical localization maps compose because the underlying raw
          -- tensor transitions compose and the contracted primes match.
          change Localization.localRingHom
              (Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e i)
                (IsLocalRing.maximalIdeal S))
              (Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k)
                (IsLocalRing.maximalIdeal S))
              (rawMap i k (le_trans hij hjk))
              ((hqTail_comp i k (le_trans hij hjk)).symm) =
            (Localization.localRingHom
                (Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j)
                  (IsLocalRing.maximalIdeal S))
                (Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k)
                  (IsLocalRing.maximalIdeal S))
                (rawMap j k hjk)
                ((hqTail_comp j k hjk).symm)).comp
              (Localization.localRingHom
                (Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e i)
                  (IsLocalRing.maximalIdeal S))
                (Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j)
                  (IsLocalRing.maximalIdeal S))
                (rawMap i j hij)
                ((hqTail_comp i j hij).symm))
          simpa [rawMap_comp i j k hij hjk] using
            (Localization.localRingHom_comp
              (I := Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e i)
                (IsLocalRing.maximalIdeal S))
              (J := Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j)
                (IsLocalRing.maximalIdeal S))
              (K := Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k)
                (IsLocalRing.maximalIdeal S))
              (f := rawMap i j hij)
              ((hqTail_comp i j hij).symm)
              (g := rawMap j k hjk)
              ((hqTail_comp j k hjk).symm))
        simpa [RingHom.comp_apply] using
          (congrArg (fun g : SStage i →+* SStage k ↦ g x) hcomp).symm }
  let stageMapTail : ∀ j : tail, A₀.RStage j.1 →+* SStage j := fun j ↦ algebraMap _ _
  have hstageMapTail_apply : ∀ (j : tail) (x : A₀.RStage j.1),
      stageMapTail j x =
        algebraMap (rawStage j) (SStage j)
          ((algebraMap (A₀.RStage j.1) (rawStage j)) x) := by
    intro j x
    rfl
  have hcommTail :
      ∀ {j k : tail} (hjk : j ≤ k),
        (stageMapTail k).comp (A₀.map j.1 k.1 hjk) =
          (targetMap j k hjk).comp (stageMapTail j) := by
    intro j k hjk
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
    letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.map i₀ k.1 k.2).toAlgebra
    refine RingHom.ext fun x ↦ ?_
    have hraw :
        rawMap j k hjk ((1 : P₀) ⊗ₜ[A₀.RStage i₀] x) =
          (1 : P₀) ⊗ₜ[A₀.RStage i₀] ((A₀.map j.1 k.1 hjk) x) := by
      simp only [rawMap]
      rfl
    -- Proof comment: both composites are the canonical maps from the earlier source stage into
    -- the localization of the later raw tensor stage.
    symm
    calc
      (targetMap j k hjk) ((stageMapTail j) x) =
          algebraMap (rawStage k) (SStage k)
            (rawMap j k hjk ((1 : P₀) ⊗ₜ[A₀.RStage i₀] x)) := by
            rw [show (stageMapTail j) x =
                algebraMap (rawStage j) (SStage j) ((1 : P₀) ⊗ₜ[A₀.RStage i₀] x) from rfl]
            exact descended_tail_target_map_joint_universe_algebra_map
              (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k hjk
              ((1 : P₀) ⊗ₜ[A₀.RStage i₀] x)
      _ = algebraMap (rawStage k) (SStage k)
            ((1 : P₀) ⊗ₜ[A₀.RStage i₀] ((A₀.map j.1 k.1 hjk) x)) := by
            exact congrArg (algebraMap (rawStage k) (SStage k)) hraw
      _ = (stageMapTail k) ((A₀.map j.1 k.1 hjk) x) := rfl
  have hSourceStage : ∀ (i : tail) (x : A₀.RStage i.1),
      sourceToTargetDirectLimitOf A₀ i₀ SStage targetMap stageMapTail
          (fun {j} {k} hjk ↦ hcommTail hjk)
          (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h)
            A₀.colimitIso i.1 x) =
        descendedTailTargetOfJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp i
          (stageMapTail i x) := by
    intro i x
    -- Proof comment: the source-to-target direct-limit comparison is defined to send each source
    -- stage generator to the corresponding target stage generator.
    exact sourceToTargetDirectLimit_stage_of (A₀ := A₀) (i₀ := i₀)
      (SStage := SStage) (targetMap := targetMap) (stageMapTail := stageMapTail)
      (hcommTail := fun {j} {k} hjk ↦ hcommTail hjk) i x
  let sourceColimitIso :
      Ring.DirectLimit (fun j : tail ↦ A₀.RStage j.1)
        (fun j k h ↦ A₀.map j.1 k.1 h) ≃+* R :=
    tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.map i j h) i₀ A₀.colimitIso
  have hσ_comp :
      ∀ j : tail,
        (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j).comp
            (algebraMap (A₀.RStage j.1) (rawStage j)) =
          f.comp
            (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h)
              A₀.colimitIso j.1) := by
    intro j
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
    letI : Algebra (A₀.RStage j.1) R :=
      RingHom.toAlgebra
        (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso j.1)
    letI : IsScalarTower (A₀.RStage i₀) (A₀.RStage j.1) R :=
      tail_toLimit_isScalarTower_of_base_eq A₀ i₀ hRalg j
    ext x
    -- Proof comment: evaluating the raw tensor-stage comparison on the right tensor generator
    -- recovers the image of `x` in `R`, then in `P`, and finally in `S`.
    simp only [descendedTailSigmaJointUniverse, RingHom.comp_apply, hfg]
    have h1 : (algebraMap (A₀.RStage j.1) (rawStage j)) x =
        (1 : P₀) ⊗ₜ[A₀.RStage i₀] x := rfl
    rw [h1]
    simp only [RingHom.coe_coe]
    exact congrArg (algebraMap P S) (e.commutes ((algebraMap (A₀.RStage j.1) R) x))
  have htargetColimitToAmbient_comm :
      (tail_target_colimit_to_ambient (S := S)
          (descendedTailRawStage A₀ i₀ P₀) (descendedTailRawMap A₀ i₀ P₀)
          (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e) hσ_raw_comp).comp
          (Ring.DirectLimit.map stageMapTail (fun _ _ h ↦ hcommTail h)) =
        f.comp sourceColimitIso.toRingHom := by
    apply Ring.DirectLimit.hom_ext
    intro j
    ext x
    -- Proof comment: on each source-stage generator, the ambient colimit map collapses to the raw
    -- stage comparison to `S`, and that comparison is exactly the original map `f`.
    change
      (tail_target_colimit_to_ambient (S := S)
          (descendedTailRawStage A₀ i₀ P₀) (descendedTailRawMap A₀ i₀ P₀)
          (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e) hσ_raw_comp)
          (descendedTailTargetOfJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j
            (stageMapTail j x)) =
        f (sourceColimitIso.toRingHom
          (Ring.DirectLimit.of (fun j : tail ↦ A₀.RStage j.1)
            (fun j k h ↦ A₀.map j.1 k.1 h) j x))
    rw [tail_target_colimit_to_ambient_of (S := S) (G := rawStage) (map := rawMap)
      (σ := descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e) (hσ := hσ_raw_comp)]
    rw [hstageMapTail_apply j x]
    rw [Localization.localRingHom_to_map]
    have hcompj := congrArg (fun g : A₀.RStage j.1 →+* S ↦ g x) (hσ_comp j)
    change
      descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j
          ((algebraMap (A₀.RStage j.1) (rawStage j)) x) =
        f ((Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h)
          A₀.colimitIso j.1) x) at hcompj
    rw [hcompj]
    simp only [RingHom.coe_coe, maxLocalizationCollapse_algebraMap, sourceColimitIso,
      tail_directLimitIso, Ring.DirectLimit.toLimitHom, RingHom.comp_apply]
    exact congrArg (fun y ↦ f (A₀.colimitIso y))
      (tail_directLimit_to_full_of A₀.RStage (fun i j h ↦ A₀.map i j h) i₀ j x).symm
  exact
    { instTailDirected := inferInstance
      instDirectedSystemRaw := inferInstance
      instDirectedSystemTarget := inferInstance
      stageMapTail := stageMapTail
      hstageMapTail_apply := hstageMapTail_apply
      hcommTail := fun {j} {k} hjk ↦ hcommTail hjk
      hSourceStage := hSourceStage
      htargetColimitToAmbient_comm := htargetColimitToAmbient_comm }

/-- Helper for Lemma 10.127.13: the forward comparison `F` undoes `descentPsi` even when the
ambient target ring lives in a different universe from the descended presentation data. -/
private theorem descentPsi_comp_eq_mixed
    {R₀ P₀ R' P' C : Type uR} {T : Type uS}
    [CommRing R₀] [CommRing P₀] [CommRing R'] [CommRing P'] [CommRing C] [CommRing T]
    [Algebra R₀ P₀] [Algebra R₀ R'] [Algebra R₀ C] [Algebra R' P'] [Algebra P' T]
    (e : P₀ ⊗[R₀] R' ≃ₐ[R'] P') (fP₀ : P₀ →ₐ[R₀] C) (fR : R' →ₐ[R₀] C) (F : C →+* T)
    (hp0 : ∀ p, F (fP₀ p) = algebraMap P' T (e (p ⊗ₜ[R₀] 1)))
    (hsrc : ∀ r, F (fR r) = algebraMap P' T (e ((1 : P₀) ⊗ₜ[R₀] r))) :
    F.comp (descentPsi e fP₀ fR) = algebraMap P' T := by
  have key : ∀ x : P₀ ⊗[R₀] R',
      F (descentPsi e fP₀ fR (e x)) = algebraMap P' T (e x) := by
    intro x
    -- Proof comment: the inverse comparison is multiplicative and is determined by the two tensor
    -- generators, so tensor induction reduces everything to the prescribed formulas on `P₀` and
    -- `R'`.
    induction x using TensorProduct.induction_on with
    | zero =>
        simp
    | tmul p r =>
        rw [descentPsi_apply, map_mul, hp0, hsrc, ← map_mul, ← map_mul,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    | add a b ha hb =>
        simp only [map_add, ha, hb]
  refine RingHom.ext fun p ↦ ?_
  obtain ⟨x, rfl⟩ := e.surjective p
  exact key x

/-- Helper for Lemma 10.127.13: the canonical map from the direct limit of the mixed-universe
localized tail to the ambient local target ring is a local homomorphism. -/
private theorem tail_target_colimit_isLocalHom_mixed
    {Λ : Type w} [Preorder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (G : Λ → Type uR) [∀ i, CommRing (G i)]
    (map : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ map i j h)]
    (σ : (i : Λ) → G i →+* S)
    (hσ : ∀ i j (hij : i ≤ j), σ i = (σ j).comp (map i j hij)) :
    IsLocalHom (tail_target_colimit_to_ambient (S := S) G map σ hσ) := by
  let q : (i : Λ) → Ideal (G i) := fun i ↦ Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)
  let ρ : ∀ i j, i ≤ j → Localization.AtPrime (q i) →+* Localization.AtPrime (q j) :=
    fun i j hij ↦
      Localization.localRingHom (q i) (q j) (map i j hij)
        ((comap_contracted_maximalIdeal_eq_of_comp
          (S := S) (τ := map i j hij) (σA := σ i) (σB := σ j) (hσ i j hij)).symm)
  let φ : (i : Λ) → Localization.AtPrime (q i) →+* S :=
    fun i ↦ (maxLocalizationCollapse S :
        Localization.AtPrime (IsLocalRing.maximalIdeal S) →+* S).comp
      (Localization.localRingHom (q i) (IsLocalRing.maximalIdeal S) (σ i) rfl)
  haveI hDS : DirectedSystem (fun i ↦ Localization.AtPrime (q i)) (fun i j h ↦ ρ i j h) :=
    localized_contracted_maximalIdeal_directedSystem (S := S) G map σ hσ
  haveI : ∀ i j h, IsLocalHom (ρ i j h) := fun i j h ↦
    Localization.isLocalHom_localRingHom _ _ _ _
  haveI hcollapse :
      IsLocalHom
        (maxLocalizationCollapse S :
          Localization.AtPrime (IsLocalRing.maximalIdeal S) →+* S) :=
    Function.Surjective.isLocalHom _ (maxLocalizationCollapse S).surjective
  haveI : ∀ i, IsLocalHom (φ i) := fun i ↦ by
    haveI :
        IsLocalHom
          (Localization.localRingHom (q i) (IsLocalRing.maximalIdeal S) (σ i) rfl) :=
      Localization.isLocalHom_localRingHom _ _ _ _
    exact RingHom.isLocalHom_comp _ _
  have hφcompat : ∀ i j (hij : i ≤ j), φ i = (φ j).comp (ρ i j hij) :=
    localized_stage_maps_to_ambient_compatible (S := S) G map σ hσ
  -- Proof comment: the ambient comparison is the direct-limit lift of compatible local maps from
  -- each localized stage, so the resulting colimit map is local as well.
  exact Ring.DirectLimit.lift_isLocalHom (fun i ↦ Localization.AtPrime (q i)) ρ φ hφcompat

/-- Helper for Lemma 10.127.13: a mixed-universe localized tail direct limit is canonically
identified with the ambient local target ring once an inverse comparison map has been built. -/
private theorem tailTargetColimitEquiv_mixed
    {Λ : Type w} [Preorder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (G : Λ → Type uR) [∀ i, CommRing (G i)]
    (map : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ map i j h)]
    (σ : (i : Λ) → G i →+* S)
    (hσ : ∀ i j (hij : i ≤ j), σ i = (σ j).comp (map i j hij))
    {P : Type uR} [CommRing P] [Algebra P S]
    (q : Ideal P) [q.IsPrime] [IsLocalization q.primeCompl S]
    (pComp : (i : Λ) → G i →+* P)
    (hpComp : ∀ i, (algebraMap P S).comp (pComp i) = σ i)
    (ψ : P →+* Ring.DirectLimit
        (fun i ↦ Localization.AtPrime (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)))
        (fun i j h ↦ Localization.localRingHom _ _ (map i j h)
          ((comap_contracted_maximalIdeal_eq_of_comp
            (S := S) (τ := map i j h) (σA := σ i) (σB := σ j) (hσ i j h)).symm)))
    (hψ : (tail_target_colimit_to_ambient (S := S) G map σ hσ).comp ψ = algebraMap P S)
    (hfactB : ∀ (i : Λ) (w : G i),
      ψ (pComp i w) = Ring.DirectLimit.of
        (fun i ↦ Localization.AtPrime (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)))
        (fun i j h ↦ Localization.localRingHom _ _ (map i j h)
          ((comap_contracted_maximalIdeal_eq_of_comp
            (S := S) (τ := map i j h) (σA := σ i) (σB := σ j) (hσ i j h)).symm))
        i (algebraMap (G i)
          (Localization.AtPrime (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S))) w)) :
    ∃ eTail : Ring.DirectLimit
        (fun i ↦ Localization.AtPrime (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)))
        (fun i j h ↦ Localization.localRingHom _ _ (map i j h)
          ((comap_contracted_maximalIdeal_eq_of_comp
            (S := S) (τ := map i j h) (σA := σ i) (σB := σ j) (hσ i j h)).symm)) ≃+* S,
      eTail.toRingHom = tail_target_colimit_to_ambient (S := S) G map σ hσ := by
  haveI hDS := localized_contracted_maximalIdeal_directedSystem (S := S) G map σ hσ
  have hlocal : IsLocalHom (tail_target_colimit_to_ambient (S := S) G map σ hσ) :=
    tail_target_colimit_isLocalHom_mixed (S := S) G map σ hσ
  have hunits : ∀ y : q.primeCompl, IsUnit (ψ (y : P)) := by
    intro y
    -- Proof comment: the inverse comparison sends each denominator to a unit because its image in
    -- `S` is already a unit and the ambient colimit map is local.
    apply hlocal.1
    rw [show (tail_target_colimit_to_ambient (S := S) G map σ hσ) (ψ (y : P))
        = algebraMap P S (y : P) from congrArg (fun h : P →+* S ↦ h (y : P)) hψ]
    exact IsLocalization.map_units S y
  let invMap : S →+* Ring.DirectLimit
      (fun i ↦ Localization.AtPrime (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)))
      (fun i j h ↦ Localization.localRingHom _ _ (map i j h)
        ((comap_contracted_maximalIdeal_eq_of_comp
          (S := S) (τ := map i j h) (σA := σ i) (σB := σ j) (hσ i j h)).symm)) :=
    IsLocalization.lift (M := q.primeCompl) hunits
  have hforward : (tail_target_colimit_to_ambient (S := S) G map σ hσ).comp invMap =
      RingHom.id S := by
    apply IsLocalization.ringHom_ext q.primeCompl
    refine RingHom.ext fun x ↦ ?_
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [show invMap (algebraMap P S x) = ψ x from IsLocalization.lift_eq hunits x]
    exact congrArg (fun h : P →+* S ↦ h x) hψ
  have hbackward :
      invMap.comp (tail_target_colimit_to_ambient (S := S) G map σ hσ) = RingHom.id _ := by
    apply Ring.DirectLimit.hom_ext
    intro i
    apply IsLocalization.ringHom_ext
      (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)).primeCompl
    refine RingHom.ext fun w ↦ ?_
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [tail_target_colimit_to_ambient_of (S := S) G map σ hσ, Localization.localRingHom_to_map]
    simp only [RingHom.coe_coe, maxLocalizationCollapse_algebraMap]
    rw [show σ i w = algebraMap P S (pComp i w) from
      (congrArg (fun h : G i →+* S ↦ h w) (hpComp i)).symm]
    rw [IsLocalization.lift_eq hunits (pComp i w)]
    exact hfactB i w
  -- Proof comment: the lifted inverse map is inverse to the ambient colimit map because both
  -- composites agree on localization generators, hence on the whole localized tail.
  exact ⟨RingEquiv.ofRingHom (tail_target_colimit_to_ambient (S := S) G map σ hσ) invMap
    hforward hbackward, rfl⟩

/-- Helper for Lemma 10.127.13: package only the short descended-comparison inputs needed by the
mixed-universe tail-colimit equivalence, keeping the giant tail bundle out of the application
boundary. -/
private structure JointUniverseTargetColimitInputs
    (A₀ : DirectedLocalHomApproximation.{uR, uR, uR} (RingHom.id R))
    {P : Type uR} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type uR) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (hσ_raw_comp : ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
      descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j =
        (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k).comp
          (descendedTailRawMap A₀ i₀ P₀ j k hjk))
    [IsDirectedOrder (Set.Ici i₀)]
    [DirectedSystem (descendedTailRawStage A₀ i₀ P₀)
      (fun j k h ↦ descendedTailRawMap A₀ i₀ P₀ j k h)]
    [DirectedSystem (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e)
      (fun j k h ↦ descendedTailTargetMapJointUniverse
        (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k h)] where
  instAlgTargetLimit : Algebra (A₀.RStage i₀)
    (descendedTailTargetLimitJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp)
  p0Alg :
    let _ : Algebra (A₀.RStage i₀)
        (descendedTailTargetLimitJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp) :=
      instAlgTargetLimit
    P₀ →ₐ[A₀.RStage i₀]
      descendedTailTargetLimitJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp
  srcAlg :
    let _ : Algebra (A₀.RStage i₀)
        (descendedTailTargetLimitJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp) :=
      instAlgTargetLimit
    R →ₐ[A₀.RStage i₀]
      descendedTailTargetLimitJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp
  psi : P →+*
    descendedTailTargetLimitJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp
  hpsi :
    (tail_target_colimit_to_ambient (S := S)
        (descendedTailRawStage A₀ i₀ P₀) (descendedTailRawMap A₀ i₀ P₀)
        (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e) hσ_raw_comp).comp psi =
      algebraMap P S
  hfactB : ∀ (i : Set.Ici i₀) (w : descendedTailRawStage A₀ i₀ P₀ i),
    psi (descendedTailPComp A₀ i₀ P₀ hRalg e i w) =
      descendedTailTargetOfJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp i
        (algebraMap (descendedTailRawStage A₀ i₀ P₀ i)
          (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e i) w)

/-- Helper for Lemma 10.127.13: from the packaged joint-universe tail bundle, construct the
minimal `p₀`, source, and inverse-comparison maps needed by `tailTargetColimitEquiv_mixed`. -/
private theorem joint_universe_target_colimit_inputs
    (A₀ : DirectedLocalHomApproximation.{uR, uR, uR} (RingHom.id R))
    {P : Type uR} [CommRing P] [Algebra R P] [Algebra P S]
    (g : R →+* P) (hfg : f = (algebraMap P S).comp g)
    (i₀ : A₀.Λ) (P₀ : Type uR) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (hPalg : algebraMap R P = g)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (hσ_raw_comp : ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
      descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j =
        (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k).comp
          (descendedTailRawMap A₀ i₀ P₀ j k hjk))
    [IsDirectedOrder (Set.Ici i₀)]
    [DirectedSystem (descendedTailRawStage A₀ i₀ P₀)
      (fun j k h ↦ descendedTailRawMap A₀ i₀ P₀ j k h)]
    [DirectedSystem (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e)
      (fun j k h ↦ descendedTailTargetMapJointUniverse
        (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k h)]
    (bundle : JointUniverseTargetTailData (f := f) (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp) :
    Nonempty (JointUniverseTargetColimitInputs (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp) := by
  let tail : Type uR := Set.Ici i₀
  letI : Preorder tail := inferInstance
  letI : Nonempty tail := inferInstance
  letI : IsDirectedOrder tail := bundle.instTailDirected
  let j0 : tail := ⟨i₀, le_rfl⟩
  let rawStage : tail → Type uR := descendedTailRawStage A₀ i₀ P₀
  let rawMap : ∀ j k : tail, j ≤ k → rawStage j →+* rawStage k := fun j k h ↦
    descendedTailRawMap A₀ i₀ P₀ j k h
  let SStage : tail → Type uR := descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e
  let targetMap : ∀ j k : tail, j ≤ k → SStage j →+* SStage k := fun j k h ↦
    descendedTailTargetMapJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k h
  letI : DirectedSystem rawStage (fun j k h ↦ rawMap j k h) := bundle.instDirectedSystemRaw
  letI : DirectedSystem SStage (fun j k h ↦ targetMap j k h) := bundle.instDirectedSystemTarget
  let targetLimit : Type uR :=
    descendedTailTargetLimitJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp
  let targetOf : (j : tail) → SStage j →+* targetLimit := fun j ↦
    descendedTailTargetOfJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j
  let targetColimitToAmbient : targetLimit →+* S :=
    tail_target_colimit_to_ambient (S := S) rawStage rawMap
      (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e) hσ_raw_comp
  let minimalStageMap : P₀ →+* SStage j0 :=
    (algebraMap (rawStage j0) (SStage j0)).comp (algebraMap P₀ (rawStage j0))
  let p0ToTargetDirectLimit : P₀ →+* targetLimit :=
    tail_targetDirectLimit_of_minimal_stage (i₀ := i₀) (Sj := SStage)
      (fun j k h ↦ targetMap j k h) minimalStageMap
  have htargetColimitToAmbient_p0 :
      targetColimitToAmbient.comp p0ToTargetDirectLimit =
        ((algebraMap P S).comp e.toRingHom).comp
          (algebraMap P₀ (P₀ ⊗[A₀.RStage i₀] R)) := by
    ext x
    -- Proof comment: the minimal-stage map lands in the first tail stage, so the ambient colimit
    -- map evaluates it using the raw comparison at that stage and then `e`.
    change
      (tail_target_colimit_to_ambient (S := S) rawStage rawMap
          (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e) hσ_raw_comp)
          (Ring.DirectLimit.of SStage (fun j k h ↦ targetMap j k h) j0
            (minimalStageMap x)) =
        (algebraMap P S) (e (algebraMap P₀ (P₀ ⊗[A₀.RStage i₀] R) x))
    refine (tail_target_colimit_to_ambient_of (S := S) (G := rawStage) (map := rawMap)
      (σ := descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e)
      (hσ := hσ_raw_comp) j0 (minimalStageMap x)).trans ?_
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j0.1) := (A₀.map i₀ j0.1 j0.2).toAlgebra
    rw [show minimalStageMap x =
      algebraMap (rawStage j0) (SStage j0) ((algebraMap P₀ (rawStage j0)) x) from rfl]
    rw [Localization.localRingHom_to_map]
    simp only [RingHom.comp_apply, descendedTailSigmaJointUniverse]
    have h1 : (algebraMap P₀ (rawStage j0)) x =
        (x ⊗ₜ[A₀.RStage i₀] (1 : A₀.RStage j0.1) : rawStage j0) := rfl
    rw [h1]
    simp only [RingHom.coe_coe, maxLocalizationCollapse_algebraMap]
    exact congrArg (fun y : P₀ ⊗[A₀.RStage i₀] R ↦ (algebraMap P S) (e y)) (by
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl)
  let sourceToTargetDirectLimit : R →+* targetLimit :=
    sourceToTargetDirectLimitOf A₀ i₀ SStage targetMap bundle.stageMapTail
      (fun {j} {k} hjk ↦ bundle.hcommTail hjk)
  letI algColim : Algebra (A₀.RStage i₀) targetLimit :=
    ((targetOf j0).comp (bundle.stageMapTail j0)).toAlgebra
  let p0Alg : P₀ →ₐ[A₀.RStage i₀] targetLimit :=
    algHomOfCompBase (target := targetOf j0) (stage := bundle.stageMapTail j0)
      (pmap := minimalStageMap) (fun r ↦ by
        letI : Algebra (A₀.RStage i₀) (A₀.RStage j0.1) := (A₀.map i₀ j0.1 j0.2).toAlgebra
        rw [bundle.hstageMapTail_apply j0 r]
        change (algebraMap (rawStage j0) (SStage j0))
            ((algebraMap P₀ (rawStage j0)) (algebraMap (A₀.RStage i₀) P₀ r)) =
          (algebraMap (rawStage j0) (SStage j0)) ((1 : P₀) ⊗ₜ[A₀.RStage i₀] r)
        exact tensor_minimalStage_base_comm (targetOf := RingHom.id (SStage j0))
          (hself := fun r ↦ by
            change (A₀.map i₀ j0.1 j0.2) r = r
            exact DirectedSystem.map_self (f := fun i j h ↦ A₀.map i j h) r) r)
  let srcAlg : R →ₐ[A₀.RStage i₀] targetLimit :=
    { sourceToTargetDirectLimit with
      commutes' := fun r ↦ by
        dsimp [sourceToTargetDirectLimit, sourceToTargetDirectLimitOf]
        change (Ring.DirectLimit.map bundle.stageMapTail (fun _ _ h ↦ bundle.hcommTail h))
            ((tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.map i j h)
              i₀ A₀.colimitIso).symm ((algebraMap (A₀.RStage i₀) R) r)) =
          (targetOf j0) (bundle.stageMapTail j0 r)
        have hsrcfull :
            (tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.map i j h)
                i₀ A₀.colimitIso).symm (algebraMap (A₀.RStage i₀) R r) =
              Ring.DirectLimit.of (fun j : tail ↦ A₀.RStage j.1)
                (fun j k h ↦ A₀.map j.1 k.1 h) j0 r := by
          apply (tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.map i j h)
            i₀ A₀.colimitIso).injective
          rw [RingEquiv.apply_symm_apply]
          show algebraMap (A₀.RStage i₀) R r =
            (tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.map i j h)
              i₀ A₀.colimitIso) (Ring.DirectLimit.of (fun j : tail ↦ A₀.RStage j.1)
                (fun j k h ↦ A₀.map j.1 k.1 h) j0 r)
          simp only [tail_directLimitIso, RingEquiv.trans_apply, RingEquiv.ofRingHom_apply]
          exact congrArg (fun h : A₀.RStage i₀ →+* R ↦ h r) hRalg
        rw [hsrcfull]
        rfl }
  have htargetColimitToAmbient_source :
      targetColimitToAmbient.comp sourceToTargetDirectLimit = f := by
    ext x
    -- Proof comment: the packaged tail colimit square already identifies the source-to-target
    -- direct-limit map followed by the ambient comparison with the original local map `f`.
    have h := congrArg
      (fun g : Ring.DirectLimit (fun j : tail ↦ A₀.RStage j.1)
          (fun j k h ↦ A₀.map j.1 k.1 h) →+* S ↦
        g ((tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.map i j h)
          i₀ A₀.colimitIso).symm x))
      bundle.htargetColimitToAmbient_comm
    simpa [sourceToTargetDirectLimit, sourceToTargetDirectLimitOf, RingHom.comp_apply] using h
  let psi : P →+* targetLimit := descentPsi e p0Alg srcAlg
  have hpsi : targetColimitToAmbient.comp psi = algebraMap P S := by
    -- Proof comment: the ambient comparison and the inverse comparison agree on the descended
    -- algebra generators and the source generators, so `descentPsi_comp_eq_mixed` applies.
    refine descentPsi_comp_eq_mixed e p0Alg srcAlg targetColimitToAmbient ?_ ?_
    · intro p
      have := congrArg (fun h : P₀ →+* S ↦ h p) htargetColimitToAmbient_p0
      simp only [RingHom.comp_apply] at this
      simpa [p0Alg, p0ToTargetDirectLimit] using this
    · intro r
      have hsrc0 := congrArg (fun h : R →+* S ↦ h r) htargetColimitToAmbient_source
      simp only [RingHom.comp_apply] at hsrc0
      change targetColimitToAmbient (srcAlg r) =
        algebraMap P S (e ((1 : P₀) ⊗ₜ[A₀.RStage i₀] r))
      rw [show srcAlg r = sourceToTargetDirectLimit r from rfl, hsrc0]
      have he : e ((1 : P₀) ⊗ₜ[A₀.RStage i₀] r) = g r := by
        have hc := e.commutes r
        rwa [show algebraMap R (P₀ ⊗[A₀.RStage i₀] R) r =
            (1 : P₀) ⊗ₜ[A₀.RStage i₀] r from rfl,
          congrArg (fun h : R →+* P ↦ h r) hPalg] at hc
      rw [he]
      exact congrArg (fun h : R →+* S ↦ h r) hfg
  have hfactB : ∀ (i : tail) (w : rawStage i),
      psi (descendedTailPComp A₀ i₀ P₀ hRalg e i w) =
        targetOf i (algebraMap (rawStage i) (SStage i) w) := by
    intro i w
    -- Proof comment: the descended inverse comparison hits the direct-limit generator attached to
    -- `w`, exactly as in the same-universe case, because the target limit now lives in the
    -- packaged joint universe.
    exact descended_tail_descentPsi_factB_joint_universe
      (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp bundle.stageMapTail
      bundle.hstageMapTail_apply sourceToTargetDirectLimit
      (fun i x ↦ by
        simpa [sourceToTargetDirectLimit, targetOf] using bundle.hSourceStage i x) p0Alg srcAlg
      (fun p ↦ rfl) (fun r ↦ rfl) i w
  exact ⟨{
      instAlgTargetLimit := algColim
      p0Alg := p0Alg
      srcAlg := srcAlg
      psi := psi
      hpsi := hpsi
      hfactB := hfactB }⟩

/-- Helper for Lemma 10.127.13: the packaged mixed-universe target-tail data identifies the
localized target colimit with the ambient local target ring. -/
theorem joint_universe_target_colimit_equiv_from_bundle
    (A₀ : DirectedLocalHomApproximation.{uR, uR, uR} (RingHom.id R))
    {P : Type uR} [CommRing P] [Algebra R P] [Algebra P S]
    (g : R →+* P) (q : Ideal P) [q.IsPrime]
    (hlocq : q.primeCompl.IsLocalizationMap (algebraMap P S))
    (hfg : f = (algebraMap P S).comp g)
    (i₀ : A₀.Λ) (P₀ : Type uR) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R] [Algebra.FinitePresentation (A₀.RStage i₀) P₀]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (hPalg : algebraMap R P = g)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (hσ_raw_comp : ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
      descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j =
        (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k).comp
          (descendedTailRawMap A₀ i₀ P₀ j k hjk))
    [IsDirectedOrder (Set.Ici i₀)]
    [DirectedSystem (descendedTailRawStage A₀ i₀ P₀)
      (fun j k h ↦ descendedTailRawMap A₀ i₀ P₀ j k h)]
    [DirectedSystem (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e)
      (fun j k h ↦ descendedTailTargetMapJointUniverse
        (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k h)]
    (bundle : JointUniverseTargetTailData (f := f) (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp) :
    ∃ eTail :
        descendedTailTargetLimitJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp ≃+* S,
      eTail.toRingHom =
        tail_target_colimit_to_ambient (S := S)
          (descendedTailRawStage A₀ i₀ P₀) (descendedTailRawMap A₀ i₀ P₀)
          (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e) hσ_raw_comp := by
  letI : IsDirectedOrder (Set.Ici i₀) := bundle.instTailDirected
  letI : DirectedSystem (descendedTailRawStage A₀ i₀ P₀)
      (fun j k h ↦ descendedTailRawMap A₀ i₀ P₀ j k h) := bundle.instDirectedSystemRaw
  letI : DirectedSystem (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e)
      (fun j k h ↦ descendedTailTargetMapJointUniverse
        (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k h) := bundle.instDirectedSystemTarget
  obtain ⟨inputs⟩ := joint_universe_target_colimit_inputs (f := f) (S := S) A₀ g hfg i₀ P₀
    hRalg hPalg e hσ_raw_comp bundle
  letI : Algebra (A₀.RStage i₀)
      (descendedTailTargetLimitJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp) :=
    inputs.instAlgTargetLimit
  haveI : IsLocalization q.primeCompl S :=
    (isLocalization_iff_isLocalizationMap (M := q.primeCompl) (S := S)).mpr hlocq
  -- Proof comment: after shrinking the theorem boundary to `p0Alg`, `srcAlg`, and `ψ`, the
  -- mixed-universe tail-colimit equivalence theorem applies directly to the joint-universe tail.
  obtain ⟨eTail, hTail⟩ :=
    tailTargetColimitEquiv_mixed
      (S := S)
      (G := descendedTailRawStage A₀ i₀ P₀)
      (map := descendedTailRawMap A₀ i₀ P₀)
      (σ := descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e)
      (hσ := hσ_raw_comp)
      (q := q)
      (pComp := descendedTailPComp A₀ i₀ P₀ hRalg e)
      (hpComp := fun i ↦ rfl)
      inputs.psi
      inputs.hpsi
      inputs.hfactB
  exact ⟨eTail, hTail⟩

end
