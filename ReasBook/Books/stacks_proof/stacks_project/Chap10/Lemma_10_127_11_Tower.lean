import StacksProject_2024.Chap10.Lemma_10_127_11_Tower_Local

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

section SameUniverse

variable {R S : Type u} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
variable (f : R →+* S) [IsLocalHom f]

/-- Helper for the transition tower: the pure-tensor formula for the owner base-change map,
with the owner fields rewritten by pointwise equalities rather than dependent function rewrites. -/
theorem stageBaseChangeMap_tensorBridge_tensorMapLeft_tmul_pointwise
    {R' S' T : Type u} [CommRing R'] [CommRing S'] [CommRing T] {f' : R' →+* S'}
    (A' : DirectedLocalHomApproximation.{u, u, u} f') {i j : A'.Λ} (h : i ≤ j)
    [Algebra (A'.RStage i) T]
    (algStage : Algebra (A'.RStage i) (A'.SStage i))
    (hinst : (A'.stageMap i).toAlgebra = algStage)
    (φ : T →ₐ[A'.RStage i] A'.SStage i)
    (targetMapIJ : A'.SStage i →+* A'.SStage j)
    (stageMapJ : A'.RStage j →+* A'.SStage j)
    (htarget : ∀ z : A'.SStage i, A'.targetMap i j h z = targetMapIJ z)
    (hstage : ∀ y : A'.RStage j, A'.stageMap j y = stageMapJ y)
    (x : T) (y : A'.RStage j) :
    letI : Algebra (A'.RStage i) (A'.RStage j) := (A'.map i j h).toAlgebra
    letI : Algebra (A'.RStage i) (A'.SStage i) := algStage
    ((A'.stageBaseChangeMap h).comp
        (tensorRingHomOfAlgEqSymm (R := A'.RStage i) (Sj := A'.SStage i)
          (Rk := A'.RStage j) ((A'.stageMap i).toAlgebra) algStage hinst))
      (tensorMapLeft (R := A'.RStage i) (A := T) (B := A'.RStage j)
        (C := A'.SStage i) φ (x ⊗ₜ[A'.RStage i] y)) =
    targetMapIJ (φ x) * stageMapJ y := by
  letI : Algebra (A'.RStage i) (A'.RStage j) := (A'.map i j h).toAlgebra
  letI : Algebra (A'.RStage i) (A'.SStage i) := algStage
  calc
    ((A'.stageBaseChangeMap h).comp
        (tensorRingHomOfAlgEqSymm (R := A'.RStage i) (Sj := A'.SStage i)
          (Rk := A'.RStage j) ((A'.stageMap i).toAlgebra) algStage hinst))
      (tensorMapLeft (R := A'.RStage i) (A := T) (B := A'.RStage j)
        (C := A'.SStage i) φ (x ⊗ₜ[A'.RStage i] y)) =
        A'.targetMap i j h (φ x) * A'.stageMap j y := by
      exact stageBaseChangeMap_tensorBridge_tensorMapLeft_tmul A' h algStage hinst φ x y
    _ = targetMapIJ (φ x) * stageMapJ y := by
      rw [htarget (φ x), hstage y]

/-- Helper for Lemma 10.127.11: once the raw localized tail system has been constructed, package
it as a directed local approximation and prove that its transition base changes are prime
localizations. -/
theorem finish_localEssFinitePresentationApproximation
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    {P : Type u} [CommRing P] [Algebra R P] (g : R →+* P) [Algebra P S]
    (q : Ideal P) [q.IsPrime]
    (hlocq : q.primeCompl.IsLocalizationMap (algebraMap P S))
    (hfg : f = (algebraMap P S).comp g)
    (i₀ : A₀.Λ) {P₀ : Type u} [CommRing P₀]
    [Algebra (A₀.RStage i₀) P₀] [Algebra (A₀.RStage i₀) R]
    [Algebra.FinitePresentation (A₀.RStage i₀) P₀]
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (hPalg : algebraMap R P = g)
    (rawDirectedSystem :
      DirectedSystem (descendedTailRawStage A₀ i₀ P₀)
        (fun j k h ↦ descendedTailRawMap A₀ i₀ P₀ j k h))
    (hσ_comp : ∀ j : Set.Ici i₀,
      (descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e j).comp
          (algebraMap (A₀.RStage j.1) (descendedTailRawStage A₀ i₀ P₀ j)) =
        f.comp (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h)
          A₀.colimitIso j.1))
    (hσ_raw_comp : ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
      descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e j =
        (descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e k).comp
          (descendedTailRawMap A₀ i₀ P₀ j k hjk))
    (targetDirectedSystem :
      DirectedSystem (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e)
        (fun j k h ↦ descendedTailTargetMap (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k h))
    (stageMapTail : (j : Set.Ici i₀) → A₀.RStage j.1 →+*
      descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j)
    (hstageMapTail_apply : ∀ (j : Set.Ici i₀) (x : A₀.RStage j.1),
      stageMapTail j x =
        algebraMap (descendedTailRawStage A₀ i₀ P₀ j)
          (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j)
          ((algebraMap (A₀.RStage j.1) (descendedTailRawStage A₀ i₀ P₀ j)) x))
    (hstageMapTail_local : ∀ j : Set.Ici i₀, IsLocalHom (stageMapTail j))
    (hstageMapTail_essFiniteType : ∀ j : Set.Ici i₀, (stageMapTail j).EssFiniteType)
    (hcommTail : ∀ {j k : Set.Ici i₀} (hjk : j ≤ k),
      (stageMapTail k).comp (A₀.map j.1 k.1 hjk) =
        (descendedTailTargetMap (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k hjk).comp
          (stageMapTail j))
    (hSourceStage : ∀ (i : Set.Ici i₀) (x : A₀.RStage i.1),
      sourceToTargetDirectLimitOf A₀ i₀
        (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e)
        (descendedTailTargetMap (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp)
        stageMapTail (fun {_ _} hjk ↦ hcommTail hjk)
        (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h)
          A₀.colimitIso i.1 x) =
      Ring.DirectLimit.of (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e)
        (fun j k h ↦ descendedTailTargetMap (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k h)
        i (stageMapTail i x)) :
    ∃ A : DirectedLocalHomApproximation.{u, u, u} f,
      DirectedLocalHomApproximation.HasPrimeLocalizationTransitions A := by
  let tail : Type u := Set.Ici i₀
  letI : Preorder tail := inferInstance
  letI : Nonempty tail := inferInstance
  letI : IsDirectedOrder tail := tail_index_isDirected i₀
  let j0 : tail := ⟨i₀, le_rfl⟩
  let rawStage : tail → Type u := descendedTailRawStage A₀ i₀ P₀
  let rawMap : ∀ j k : tail, j ≤ k → rawStage j →+* rawStage k := fun j k h ↦
    descendedTailRawMap A₀ i₀ P₀ j k h
  letI : DirectedSystem rawStage (fun j k h ↦ rawMap j k h) := rawDirectedSystem
  let σ : (j : tail) → rawStage j →+* S := fun j ↦
    descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e j
  let qTail : (j : tail) → Ideal (rawStage j) := fun j ↦
    Ideal.comap (σ j) (IsLocalRing.maximalIdeal S)
  have hqTail_prime : ∀ j : tail, (qTail j).IsPrime := by
    intro j
    simpa [qTail] using Ideal.comap_isPrime (σ j) (IsLocalRing.maximalIdeal S)
  have hqTail_comp :
      ∀ j k : tail, ∀ hjk : j ≤ k,
        Ideal.comap (rawMap j k hjk) (qTail k) = qTail j := by
    intro j k hjk
    exact comap_contracted_maximalIdeal_eq_of_comp
      (τ := rawMap j k hjk) (σA := σ j) (σB := σ k) (hσ_raw_comp j k hjk)
  let SStage : tail → Type u := localizedTailStage (S := S) rawStage σ
  let targetMap : ∀ j k : tail, j ≤ k → SStage j →+* SStage k := fun j k h ↦
    descendedTailTargetMap (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k h
  letI : DirectedSystem SStage (fun j k h ↦ targetMap j k h) := targetDirectedSystem
  let sourceColimitIso :
      Ring.DirectLimit (fun j : tail ↦ A₀.RStage j.1)
        (fun j k h ↦ A₀.map j.1 k.1 h) ≃+* R :=
    tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.map i j h) i₀ A₀.colimitIso
  let targetLimit : Type u := Ring.DirectLimit SStage (fun j k h ↦ targetMap j k h)
  let targetOf : (j : tail) → SStage j →+* targetLimit := fun j ↦
    Ring.DirectLimit.of SStage (fun j k h ↦ targetMap j k h) j
  let targetColimitToAmbient : targetLimit →+* S :=
    tail_target_colimit_to_ambient (S := S) rawStage rawMap σ hσ_raw_comp
  have htargetColimitToAmbient_comm :
      targetColimitToAmbient.comp
          (Ring.DirectLimit.map stageMapTail (fun _ _ h ↦ hcommTail h)) =
        f.comp sourceColimitIso.toRingHom := by
    apply Ring.DirectLimit.hom_ext
    intro j
    ext x
    -- Proof comment: on each source-stage generator, the localized tail comparison is exactly
    -- the raw tensor-stage map to `S`, which the descended presentation identifies with `f`.
    change
      targetColimitToAmbient
          (targetOf j
            (stageMapTail j x)) =
        f (sourceColimitIso.toRingHom
          (Ring.DirectLimit.of (fun j : tail ↦ A₀.RStage j.1)
            (fun j k h ↦ A₀.map j.1 k.1 h) j x))
    rw [tail_target_colimit_to_ambient_of (S := S) (G := rawStage) (map := rawMap)
      (σ := σ) (hσ := hσ_raw_comp)]
    rw [hstageMapTail_apply j x]
    rw [Localization.localRingHom_to_map]
    have hcompj := congrArg (fun g : A₀.RStage j.1 →+* S => g x) (hσ_comp j)
    change (σ j) ((algebraMap (A₀.RStage j.1) (rawStage j)) x) =
      f ((Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h)
        A₀.colimitIso j.1) x) at hcompj
    rw [hcompj]
    simp only [RingHom.coe_coe, maxLocalizationCollapse_algebraMap, sourceColimitIso,
      tail_directLimitIso,
      Ring.DirectLimit.toLimitHom, RingHom.comp_apply]
    exact congrArg (fun y ↦ f (A₀.colimitIso y))
      (tail_directLimit_to_full_of A₀.RStage (fun i j h ↦ A₀.map i j h) i₀ j x).symm
  have hTargetColimit_data :
      ∃ eTail : targetLimit ≃+* S,
        eTail.toRingHom = targetColimitToAmbient := by
    exact descendedTailTargetColimitData (f := f) A₀ g q hlocq hfg i₀ P₀ hRalg hPalg e
      hσ_raw_comp stageMapTail hstageMapTail_apply (fun {j} {k} hjk ↦ hcommTail hjk)
      hSourceStage htargetColimitToAmbient_comm
  obtain ⟨hTargetColimit, hTargetColimit_toRingHom⟩ := hTargetColimit_data
  have hcolimit_comm :
      hTargetColimit.toRingHom.comp
          (Ring.DirectLimit.map stageMapTail (fun _ _ h ↦ hcommTail h)) =
        f.comp sourceColimitIso.toRingHom := by
    -- Proof comment: once the target direct-limit equivalence is known to extend the forward
    -- ambient comparison map, the colimit square is exactly the stagewise formula proved above.
    rw [hTargetColimit_toRingHom]
    exact htargetColimitToAmbient_comm
  let A : DirectedLocalHomApproximation f :=
    { Λ := tail
      instPreorder := inferInstance
      instNonempty := inferInstance
      instDirectedOrder := inferInstance
      RStage := fun j ↦ A₀.RStage j.1
      instCommRingRStage := fun j ↦ inferInstance
      map := fun j k h ↦ A₀.map j.1 k.1 h
      instDirectedSystemRStage := inferInstance
      colimitIso := sourceColimitIso
      instIsLocalRingRStage := fun j ↦ inferInstance
      SStage := SStage
      instCommRingSStage := fun j ↦ inferInstance
      instIsLocalRingSStage := fun j ↦ inferInstance
      stageMap := stageMapTail
      stageMap_isLocalHom := hstageMapTail_local
      targetMap := targetMap
      instDirectedSystemTarget := targetDirectedSystem
      comm := fun h ↦ hcommTail h
      targetColimit := hTargetColimit
      colimit_comm := hcolimit_comm
      source_essFiniteType := fun j ↦ A₀.source_essFiniteType j.1
      target_essFiniteType := hstageMapTail_essFiniteType }
  have hA_targetMap : A.targetMap = targetMap := rfl
  have hA_stageMap : A.stageMap = stageMapTail := rfl
  -- Proof comment: after packaging the tail system as an owner object, only the normalization of
  -- `A.stageBaseChangeMap` to an explicit iterated prime localization remains.
  -- TODO: normalize `A.targetStageBaseChange` to the iterated localization of `rawStage k` at the
  -- image of `qTail j`, rewrite `A.stageBaseChangeMap` to the canonical `Localization.localRingHom`,
  -- and conclude with `transitionIsLocalizationAtPrime_of_domain_equiv`.
  have hTransitions : DirectedLocalHomApproximation.HasPrimeLocalizationTransitions A := by
    intro j k hjk
    change tail at j
    change tail at k
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
    letI : Algebra (A₀.RStage j.1) (A₀.RStage k.1) := (A₀.map j.1 k.1 hjk).toAlgebra
    haveI hpj : (Ideal.comap (σ j) (IsLocalRing.maximalIdeal S)).IsPrime := hqTail_prime j
    haveI hpk : (Ideal.comap (σ k) (IsLocalRing.maximalIdeal S)).IsPrime := hqTail_prime k
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
    letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.map i₀ k.1 k.2).toAlgebra
    letI : Algebra (A₀.RStage j.1) (A₀.RStage k.1) := (A₀.map j.1 k.1 hjk).toAlgebra
    have hcomp : (A₀.map j.1 k.1 hjk).comp (A₀.map i₀ j.1 j.2) = A₀.map i₀ k.1 k.2 := by
      ext x; exact DirectedSystem.map_map (f := fun a b h ↦ A₀.map a b h) j.2 hjk x
    letI : IsScalarTower (A₀.RStage i₀) (A₀.RStage j.1) (A₀.RStage k.1) :=
      IsScalarTower.of_algebraMap_eq' hcomp.symm
    -- The record's algebra on `SStage j` agrees with the canonical localization one.
    have hinst : (A.stageMap j).toAlgebra = (inferInstance : Algebra (A₀.RStage j.1) (SStage j)) := by
      apply Algebra.algebra_ext
      intro x
      change stageMapTail j x = algebraMap (A₀.RStage j.1) (SStage j) x
      rw [hstageMapTail_apply j x]
      rfl
    let algStage : Algebra (A₀.RStage j.1) (SStage j) := inferInstance
    have hinstStage : (A.stageMap j).toAlgebra = algStage := hinst
    letI : Algebra (A₀.RStage j.1) (SStage j) := algStage
    letI : Mul (SStage j ⊗[A₀.RStage j.1] A₀.RStage k.1) :=
      Algebra.TensorProduct.instMul
    letI : NonAssocSemiring (SStage j ⊗[A₀.RStage j.1] A₀.RStage k.1) :=
      Algebra.TensorProduct.instNonAssocSemiring
    let RawJ : Type u := descendedTailRawStage A₀ i₀ P₀ j
    let RawK : Type u := descendedTailRawStage A₀ i₀ P₀ k
    let T0 : Type u := towerLocalT0 A₀ i₀ P₀ j k hjk
    let T1 : Type u := towerLocalT1 (S := S) A₀ i₀ P₀ hRalg e j k hjk
    let U0 : Type u := SStage k
    let eTensor :=
      tensorRingEquivOfAlgEq (R := A₀.RStage j.1) (Sj := SStage j)
        (Rk := A₀.RStage k.1) ((A.stageMap j).toAlgebra) algStage hinstStage
    let cancel : T0 ≃+* RawK :=
      rawTensorCancel A₀.RStage (fun a b h ↦ A₀.map a b h) P₀ j.2 k.2 hjk hcomp
    let eSymmHom :=
      tensorRingHomOfAlgEqSymm (R := A₀.RStage j.1) (Sj := SStage j)
        (Rk := A₀.RStage k.1) ((A.stageMap j).toAlgebra) algStage hinstStage
    let gammaBase : T1 →+* U0 := ((A.stageBaseChangeMap hjk).comp eSymmHom)
    let leftAlgHom : RawJ →ₐ[A₀.RStage j.1] SStage j :=
      IsScalarTower.toAlgHom (A₀.RStage j.1) RawJ (SStage j)
    let alpha : T0 →+* T1 :=
      tensorMapLeft (R := A₀.RStage j.1) (A := RawJ)
        (B := A₀.RStage k.1) (C := SStage j) leftAlgHom
    let betaMap : T0 →+* U0 := gammaBase.comp alpha
    let M0 : Submonoid T0 :=
      Algebra.algebraMapSubmonoid _ (qTail j).primeCompl
    let qkPrimeIdeal : Ideal T0 :=
      Ideal.comap cancel.toRingHom (qTail k)
    have hqkPrimeIdeal_prime : qkPrimeIdeal.IsPrime := by
      haveI := hpk
      dsimp [qkPrimeIdeal]
      exact Ideal.comap_isPrime cancel.toRingHom (qTail k)
    have hM0 : M0 ≤ qkPrimeIdeal.primeCompl := by
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      intro hmem
      have hcancel :
          cancel.toRingHom
              (algebraMap (rawStage j)
                ((rawStage j) ⊗[A₀.RStage j.1] A₀.RStage k.1) x) =
            rawMap j k hjk x := by
        change
          rawTensorCancel A₀.RStage (fun a b h ↦ A₀.map a b h) P₀ j.2 k.2 hjk hcomp
              (algebraMap (P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1)
                ((P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1) ⊗[A₀.RStage j.1] A₀.RStage k.1) x) =
            (Algebra.TensorProduct.map (AlgHom.id P₀ P₀)
              { toRingHom := A₀.map j.1 k.1 hjk
                commutes' := fun r ↦ by
                  change (A₀.map j.1 k.1 hjk) ((A₀.map i₀ j.1 j.2) r) =
                    (A₀.map i₀ k.1 k.2) r
                  exact congrArg (fun g : A₀.RStage i₀ →+* A₀.RStage k.1 => g r) hcomp } :
              P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1 →ₐ[P₀]
                P₀ ⊗[A₀.RStage i₀] A₀.RStage k.1) x
        exact rawTensorCancel_algebraMap (RStage := A₀.RStage)
          (map := fun a b h ↦ A₀.map a b h) (P₀ := P₀)
          (i₀ := i₀) (j := j.1) (k := k.1) j.2 k.2 hjk hcomp x
      have hraw : rawMap j k hjk x ∈ qTail k := by
        have hmem' := Ideal.mem_comap.mp hmem
        rwa [hcancel] at hmem'
      have hxmem : x ∈ qTail j := by
        rw [← hqTail_comp j k hjk]
        exact Ideal.mem_comap.mpr hraw
      exact hx hxmem
    have hT1 : @IsLocalization T0 _ M0 T1 _ alpha.toAlgebra := by
      simpa [M0, qTail, rawStage, SStage, alpha, tensorMapLeft] using
        tensorLocalization_of_atPrime A₀.RStage (fun a b h ↦ A₀.map a b h) P₀
          j.2 hjk (Ideal.comap (σ j) (IsLocalRing.maximalIdeal S)) (hqTail_prime j)
    have hStageFormula : ∀ (x : RawJ) (y : A₀.RStage k.1),
        gammaBase (alpha (x ⊗ₜ[A₀.RStage j.1] y)) =
          targetMap j k hjk (leftAlgHom x) * stageMapTail k y := by
      intro x y
      exact stageBaseChangeMap_tensorBridge_tensorMapLeft_tmul_pointwise A hjk
        algStage hinstStage leftAlgHom (targetMap j k hjk) (stageMapTail k)
        (by intro z; rfl) (by intro y; rfl) x y
    exact towerLocal_descended_transition_prime_elim (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp
      stageMapTail hstageMapTail_apply j k hjk hcomp leftAlgHom (by rfl)
      (targetMap j k hjk) (by rfl) alpha gammaBase M0 qkPrimeIdeal
      hqkPrimeIdeal_prime (by rfl) hM0 hT1 hStageFormula
      (fun p hp hmap => by
        haveI := hp
        exact towerLocal_transitionIsLocalizationAtPrime_of_tensorBridge A hjk
          algStage hinstStage p hmap)
  exact ⟨A, hTransitions⟩

end SameUniverse
