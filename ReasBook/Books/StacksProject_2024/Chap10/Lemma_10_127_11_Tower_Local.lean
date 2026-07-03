import StacksProject_2024.Chap10.Lemma_10_127_11_Pre

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

section SameUniverse

/-- Map-form variant of `isLocalization_atPrime_of_ringEquiv_source_map`, avoiding an
`IsLocalization.AtPrime` target type in large local contexts. -/
theorem towerLocal_isLocalizationMap_atPrime_of_ringEquiv_source_map
    {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
    (e : A ≃+* B) (q : Ideal B) [q.IsPrime]
    [Algebra B T] [IsLocalization.AtPrime T q]
    (φ : A →+* T) (hφ : φ = (algebraMap B T).comp e.toRingHom) :
    (Ideal.comap e.toRingHom q).primeCompl.IsLocalizationMap φ := by
  letI : Algebra A T := φ.toAlgebra
  have h := isLocalization_atPrime_of_ringEquiv_source_map e q φ hφ
  exact (isLocalization_iff_isLocalizationMap (Ideal.comap e.toRingHom q).primeCompl T).mp h

/-- Tensor-product ring-hom extensionality with both generators named explicitly. -/
theorem towerLocal_tensorRingHom_eq_of_generators
    {R A B C D : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [CommRing D] [Algebra R A] [Algebra R B] [Algebra R C]
    (γ : C ⊗[R] B →+* D) (α : A ⊗[R] B →+* C ⊗[R] B)
    (δ : A ⊗[R] B →+* D)
    (hleft : ∀ x : A, γ (α (x ⊗ₜ[R] (1 : B))) = δ (x ⊗ₜ[R] (1 : B)))
    (hright : ∀ y : B, γ (α ((1 : A) ⊗ₜ[R] y)) = δ ((1 : A) ⊗ₜ[R] y)) :
    γ.comp α = δ := by
  apply Algebra.TensorProduct.ringHom_ext
  · apply RingHom.ext
    intro x
    simpa [RingHom.comp_apply] using hleft x
  · apply RingHom.ext
    intro y
    simpa [RingHom.comp_apply, Algebra.TensorProduct.includeRight_apply] using hright y

/-- Map-form variant of the localization tower helper, with the composite map supplied by name. -/
theorem towerLocal_isLocalizationMap_of_localization_tower_map_named
    {T₀ T₁ U : Type u} [CommRing T₀] [CommRing T₁] [CommRing U] [IsLocalRing U]
    (α : T₀ →+* T₁) (g : T₁ →+* U) (β : T₀ →+* U) (hβ : β = g.comp α)
    (M₀ : Submonoid T₀) (qk' : Ideal T₀) (hqk'_prime : qk'.IsPrime)
    (hM₀ : M₀ ≤ qk'.primeCompl)
    (hT₁ : @IsLocalization T₀ _ M₀ T₁ _ α.toAlgebra)
    (hUmap : qk'.primeCompl.IsLocalizationMap β) :
    ∃ q : Ideal T₁, ∃ _ : q.IsPrime, q.primeCompl.IsLocalizationMap g := by
  letI : Algebra T₀ U := (g.comp α).toAlgebra
  have hU : @IsLocalization.AtPrime T₀ _ U _ (g.comp α).toAlgebra qk' hqk'_prime := by
    exact (isLocalization_iff_isLocalizationMap qk'.primeCompl U).mpr (by
      rwa [hβ] at hUmap)
  exact isLocalizationMap_of_localization_tower α g M₀ qk' hqk'_prime hM₀ hT₁ hU

/-- Tensor-generator form of the localization tower.  The two generator identities prove that
`γ ∘ α` is the canonical map obtained from the source equivalence `e`; the rest is the localization
tower argument. -/
theorem towerLocal_isLocalizationMap_of_tensor_generators_localization_tower
    {R A B C D E : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [CommRing D] [CommRing E] [IsLocalRing D]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (e : A ⊗[R] B ≃+* E) (q : Ideal E) [q.IsPrime]
    [Algebra E D] [IsLocalization.AtPrime D q]
    (α : A ⊗[R] B →+* C ⊗[R] B) (γ : C ⊗[R] B →+* D)
    (M₀ : Submonoid (A ⊗[R] B)) (qk' : Ideal (A ⊗[R] B))
    (hqk'_prime : qk'.IsPrime)
    (hqk' : qk' = Ideal.comap e.toRingHom q)
    (hM₀ : M₀ ≤ qk'.primeCompl)
    (hT₁ : @IsLocalization (A ⊗[R] B) _ M₀ (C ⊗[R] B) _ α.toAlgebra)
    (hleft : ∀ x : A,
      γ (α (x ⊗ₜ[R] (1 : B))) = algebraMap E D (e (x ⊗ₜ[R] (1 : B))))
    (hright : ∀ y : B,
      γ (α ((1 : A) ⊗ₜ[R] y)) = algebraMap E D (e ((1 : A) ⊗ₜ[R] y))) :
    ∃ p : Ideal (C ⊗[R] B), ∃ _ : p.IsPrime, p.primeCompl.IsLocalizationMap γ := by
  have hcomp : γ.comp α = (algebraMap E D).comp e.toRingHom :=
    towerLocal_tensorRingHom_eq_of_generators γ α ((algebraMap E D).comp e.toRingHom)
      hleft hright
  have hUmap0 :
      (Ideal.comap e.toRingHom q).primeCompl.IsLocalizationMap (γ.comp α) :=
    towerLocal_isLocalizationMap_atPrime_of_ringEquiv_source_map e q (γ.comp α) hcomp
  have hUmap : qk'.primeCompl.IsLocalizationMap (γ.comp α) := by
    cases hqk'
    exact hUmap0
  exact towerLocal_isLocalizationMap_of_localization_tower_map_named α γ (γ.comp α) rfl
    M₀ qk' hqk'_prime hM₀ hT₁ hUmap


/-- The raw source of one descended transition, with the stage algebra fixed to the directed-system
map.  Keeping this instance fixed avoids later unification against arbitrary local algebra
instances. -/
abbrev towerLocalT0
    {R : Type u} [CommRing R]
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    (i₀ : A₀.Λ) (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    (j k : Set.Ici i₀) (hjk : j ≤ k) : Type u :=
  letI : Algebra (A₀.RStage j.1) (A₀.RStage k.1) := (A₀.map j.1 k.1 hjk).toAlgebra
  descendedTailRawStage A₀ i₀ P₀ j ⊗[A₀.RStage j.1] A₀.RStage k.1

/-- The target of one descended transition, with the stage algebra fixed to the directed-system
map. -/
abbrev towerLocalT1
    {R S : Type u} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    {P : Type u} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type u) [CommRing P₀]
    [Algebra (A₀.RStage i₀) P₀] [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (j k : Set.Ici i₀) (hjk : j ≤ k) : Type u :=
  letI : Algebra (A₀.RStage j.1) (A₀.RStage k.1) := (A₀.map j.1 k.1 hjk).toAlgebra
  descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j ⊗[A₀.RStage j.1] A₀.RStage k.1

/-- Descended-tail specialization of the previous tensor-generator tower lemma.  The owner
base-change formula is supplied as `hStageFormula`; the comparison with the canonical localization
map is proved here, away from the large construction of the final approximation. -/
theorem towerLocal_descended_transition_prime
    {R S : Type u} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    {P : Type u} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type u) [CommRing P₀]
    [Algebra (A₀.RStage i₀) P₀] [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (hσ_raw_comp : ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
      descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e j =
        (descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e k).comp
          (descendedTailRawMap A₀ i₀ P₀ j k hjk))
    (stageMapTail : (j : Set.Ici i₀) → A₀.RStage j.1 →+*
      descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j)
    (hstageMapTail_apply : ∀ (j : Set.Ici i₀) (x : A₀.RStage j.1),
      stageMapTail j x =
        algebraMap (descendedTailRawStage A₀ i₀ P₀ j)
          (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j)
          ((algebraMap (A₀.RStage j.1) (descendedTailRawStage A₀ i₀ P₀ j)) x))
    (j k : Set.Ici i₀) (hjk : j ≤ k)
    (hcomp : (A₀.map j.1 k.1 hjk).comp (A₀.map i₀ j.1 j.2) = A₀.map i₀ k.1 k.2)
    (leftAlgHom : descendedTailRawStage A₀ i₀ P₀ j →ₐ[A₀.RStage j.1]
      descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j)
    (hleftAlgHom : leftAlgHom =
      IsScalarTower.toAlgHom (A₀.RStage j.1)
        (descendedTailRawStage A₀ i₀ P₀ j)
        (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j))
    (targetMapJK : descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j →+*
      descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e k)
    (htargetMapJK : targetMapJK =
      descendedTailTargetMap (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k hjk)
    (alpha : towerLocalT0 A₀ i₀ P₀ j k hjk →+*
      towerLocalT1 (S := S) A₀ i₀ P₀ hRalg e j k hjk)
    (gammaBase : towerLocalT1 (S := S) A₀ i₀ P₀ hRalg e j k hjk →+*
      descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e k)
    (M0 : Submonoid (towerLocalT0 A₀ i₀ P₀ j k hjk))
    (qkPrimeIdeal : Ideal (towerLocalT0 A₀ i₀ P₀ j k hjk))
    (hqkPrimeIdeal_prime : qkPrimeIdeal.IsPrime)
    (hqkPrimeIdeal_def : qkPrimeIdeal =
      Ideal.comap
        (rawTensorCancel A₀.RStage (fun a b h ↦ A₀.map a b h) P₀ j.2 k.2 hjk hcomp).toRingHom
        (Ideal.comap (descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e k)
          (IsLocalRing.maximalIdeal S)))
    (hM0 : M0 ≤ qkPrimeIdeal.primeCompl)
    (hT1 : @IsLocalization (towerLocalT0 A₀ i₀ P₀ j k hjk) _ M0
      (towerLocalT1 (S := S) A₀ i₀ P₀ hRalg e j k hjk) _ alpha.toAlgebra)
    (hStageFormula :
      letI : Algebra (A₀.RStage j.1) (A₀.RStage k.1) := (A₀.map j.1 k.1 hjk).toAlgebra
      ∀ (x : descendedTailRawStage A₀ i₀ P₀ j) (y : A₀.RStage k.1),
        gammaBase (alpha (x ⊗ₜ[A₀.RStage j.1] y)) =
          targetMapJK (leftAlgHom x) * stageMapTail k y) :
    ∃ p : Ideal (towerLocalT1 (S := S) A₀ i₀ P₀ hRalg e j k hjk),
      ∃ _ : p.IsPrime, p.primeCompl.IsLocalizationMap gammaBase := by
  letI : Algebra (A₀.RStage j.1) (A₀.RStage k.1) := (A₀.map j.1 k.1 hjk).toAlgebra
  let RawJ : Type u := descendedTailRawStage A₀ i₀ P₀ j
  let RawK : Type u := descendedTailRawStage A₀ i₀ P₀ k
  let SStageK : Type u := descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e k
  let qTailK : Ideal RawK :=
    Ideal.comap (descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e k)
      (IsLocalRing.maximalIdeal S)
  let cancel : towerLocalT0 A₀ i₀ P₀ j k hjk ≃+* RawK :=
    rawTensorCancel A₀.RStage (fun a b h ↦ A₀.map a b h) P₀ j.2 k.2 hjk hcomp
  have hqTailK_prime : qTailK.IsPrime := by
    simpa [RawK, qTailK] using
      Ideal.comap_isPrime (descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e k)
        (IsLocalRing.maximalIdeal S)
  letI : qTailK.IsPrime := hqTailK_prime
  have hqkPrimeIdeal : qkPrimeIdeal = Ideal.comap cancel.toRingHom qTailK := by
    simpa [RawK, cancel, qTailK] using hqkPrimeIdeal_def
  have hleftGen : ∀ x : RawJ,
      gammaBase (alpha (x ⊗ₜ[A₀.RStage j.1] (1 : A₀.RStage k.1))) =
        algebraMap (descendedTailRawStage A₀ i₀ P₀ k)
          (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e k)
          (rawTensorCancel A₀.RStage (fun a b h ↦ A₀.map a b h) P₀ j.2 k.2 hjk hcomp
            (x ⊗ₜ[A₀.RStage j.1] (1 : A₀.RStage k.1))) := by
    intro x
    exact (hStageFormula x (1 : A₀.RStage k.1)).trans (by
      have hxOwner := descendedTailTargetMap_stageMap_mul_eq_cancel (S := S) A₀ i₀ P₀
        hRalg e hσ_raw_comp stageMapTail hstageMapTail_apply j k hjk hcomp x
        (1 : A₀.RStage k.1)
      rw [hleftAlgHom, htargetMapJK]
      exact hxOwner)
  have hrightGen : ∀ y : A₀.RStage k.1,
      gammaBase (alpha ((1 : RawJ) ⊗ₜ[A₀.RStage j.1] y)) =
        algebraMap (descendedTailRawStage A₀ i₀ P₀ k)
          (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e k)
          (rawTensorCancel A₀.RStage (fun a b h ↦ A₀.map a b h) P₀ j.2 k.2 hjk hcomp
            ((1 : RawJ) ⊗ₜ[A₀.RStage j.1] y)) := by
    intro y
    exact (hStageFormula (1 : RawJ) y).trans (by
      have hyOwner := descendedTailTargetMap_stageMap_mul_eq_cancel (S := S) A₀ i₀ P₀
        hRalg e hσ_raw_comp stageMapTail hstageMapTail_apply j k hjk hcomp
        (1 : RawJ) y
      rw [hleftAlgHom, htargetMapJK]
      exact hyOwner)
  exact towerLocal_isLocalizationMap_of_tensor_generators_localization_tower
    (e := cancel) (q := qTailK) (α := alpha) (γ := gammaBase)
    (M₀ := M0) (qk' := qkPrimeIdeal)
    (hqk'_prime := hqkPrimeIdeal_prime) (hqk' := hqkPrimeIdeal)
    (hM₀ := hM0) (hT₁ := hT1) hleftGen hrightGen

/-- Forward compatibility for the named tensor bridge. -/
theorem towerLocal_tensorBridge_forward_comp
    {R Sj Rk U : Type u} [CommRing R] [CommRing Sj] [CommRing Rk] [CommRing U]
    [Algebra R Rk]
    (alg1 alg2 : Algebra R Sj) (halg : alg1 = alg2)
    (g : (letI := alg1; Sj ⊗[R] Rk) →+* U)
    (z : letI := alg1; Sj ⊗[R] Rk) :
    g z =
      (g.comp (tensorRingHomOfAlgEqSymm (R := R) (Sj := Sj) (Rk := Rk) alg1 alg2 halg))
        (tensorRingEquivOfAlgEq (R := R) (Sj := Sj) (Rk := Rk) alg1 alg2 halg z) := by
  dsimp [tensorRingHomOfAlgEqSymm, RingHom.comp_apply]
  rw [RingEquiv.symm_apply_apply]

/-- Variant of `transitionIsLocalizationAtPrime_of_domain_equiv` where the localization map on the
transported source is supplied as a named map `φ`.  The compatibility is stated in the forward
form `stageBaseChangeMap z = φ (e z)`, avoiding a large rewrite of the localization-map target at
call sites. -/
theorem towerLocal_transitionIsLocalizationAtPrime_of_domain_equiv_map
    {R S : Type u} [CommRing R] [CommRing S]
    {f : R →+* S} (A : DirectedLocalHomApproximation.{u, u, u} f)
    {i j : A.Λ} (h : i ≤ j)
    {T : Type u} [CommRing T] (e : A.targetStageBaseChange h ≃+* T)
    (φ : T →+* A.SStage j)
    (hφ : ∀ z : A.targetStageBaseChange h, A.stageBaseChangeMap h z = φ (e z))
    (p : Ideal T) [p.IsPrime]
    (hmap : p.primeCompl.IsLocalizationMap φ) :
    A.TransitionIsLocalizationAtPrime h := by
  refine transitionIsLocalizationAtPrime_of_domain_equiv A h e p ?_
  have hφ' : φ = (A.stageBaseChangeMap h).comp e.symm.toRingHom := by
    ext x
    simpa [RingHom.comp_apply] using (hφ (e.symm x)).symm
  rwa [← hφ']

/-- Tensor-bridge form of `TransitionIsLocalizationAtPrime`: if the named reverse bridge composed
with the owner base-change map is a prime localization, then the original owner transition is a
prime localization. -/
theorem towerLocal_transitionIsLocalizationAtPrime_of_tensorBridge
    {R S : Type u} [CommRing R] [CommRing S]
    {f : R →+* S} (A : DirectedLocalHomApproximation.{u, u, u} f)
    {i j : A.Λ} (h : i ≤ j)
    (algStage : Algebra (A.RStage i) (A.SStage i))
    (hinstStage : (A.stageMap i).toAlgebra = algStage)
    (p : Ideal
      (letI : Algebra (A.RStage i) (A.RStage j) := (A.map i j h).toAlgebra
       letI : Algebra (A.RStage i) (A.SStage i) := algStage
       A.SStage i ⊗[A.RStage i] A.RStage j))
    [p.IsPrime]
    (hmap :
      letI : Algebra (A.RStage i) (A.RStage j) := (A.map i j h).toAlgebra
      letI : Algebra (A.RStage i) (A.SStage i) := algStage
      p.primeCompl.IsLocalizationMap
        ((A.stageBaseChangeMap h).comp
          (tensorRingHomOfAlgEqSymm (R := A.RStage i) (Sj := A.SStage i) (Rk := A.RStage j)
            ((A.stageMap i).toAlgebra) algStage hinstStage))) :
    A.TransitionIsLocalizationAtPrime h := by
  letI : Algebra (A.RStage i) (A.RStage j) := (A.map i j h).toAlgebra
  letI : Algebra (A.RStage i) (A.SStage i) := algStage
  let eTensor :=
    tensorRingEquivOfAlgEq (R := A.RStage i) (Sj := A.SStage i) (Rk := A.RStage j)
      ((A.stageMap i).toAlgebra) algStage hinstStage
  let γ : (A.SStage i ⊗[A.RStage i] A.RStage j) →+* A.SStage j :=
    (A.stageBaseChangeMap h).comp
      (tensorRingHomOfAlgEqSymm (R := A.RStage i) (Sj := A.SStage i) (Rk := A.RStage j)
        ((A.stageMap i).toAlgebra) algStage hinstStage)
  exact towerLocal_transitionIsLocalizationAtPrime_of_domain_equiv_map A h eTensor γ (by
    intro z
    exact towerLocal_tensorBridge_forward_comp
      ((A.stageMap i).toAlgebra) algStage hinstStage (A.stageBaseChangeMap h) z) p hmap

/-- Continuation form of `towerLocal_descended_transition_prime`.  This keeps callers from
pattern-matching on the heavy existential type in a large local context. -/
theorem towerLocal_descended_transition_prime_elim
    {R S : Type u} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    {P : Type u} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type u) [CommRing P₀]
    [Algebra (A₀.RStage i₀) P₀] [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (hσ_raw_comp : ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
      descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e j =
        (descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e k).comp
          (descendedTailRawMap A₀ i₀ P₀ j k hjk))
    (stageMapTail : (j : Set.Ici i₀) → A₀.RStage j.1 →+*
      descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j)
    (hstageMapTail_apply : ∀ (j : Set.Ici i₀) (x : A₀.RStage j.1),
      stageMapTail j x =
        algebraMap (descendedTailRawStage A₀ i₀ P₀ j)
          (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j)
          ((algebraMap (A₀.RStage j.1) (descendedTailRawStage A₀ i₀ P₀ j)) x))
    (j k : Set.Ici i₀) (hjk : j ≤ k)
    (hcomp : (A₀.map j.1 k.1 hjk).comp (A₀.map i₀ j.1 j.2) = A₀.map i₀ k.1 k.2)
    (leftAlgHom : descendedTailRawStage A₀ i₀ P₀ j →ₐ[A₀.RStage j.1]
      descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j)
    (hleftAlgHom : leftAlgHom =
      IsScalarTower.toAlgHom (A₀.RStage j.1)
        (descendedTailRawStage A₀ i₀ P₀ j)
        (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j))
    (targetMapJK : descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j →+*
      descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e k)
    (htargetMapJK : targetMapJK =
      descendedTailTargetMap (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k hjk)
    (alpha : towerLocalT0 A₀ i₀ P₀ j k hjk →+*
      towerLocalT1 (S := S) A₀ i₀ P₀ hRalg e j k hjk)
    (gammaBase : towerLocalT1 (S := S) A₀ i₀ P₀ hRalg e j k hjk →+*
      descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e k)
    (M0 : Submonoid (towerLocalT0 A₀ i₀ P₀ j k hjk))
    (qkPrimeIdeal : Ideal (towerLocalT0 A₀ i₀ P₀ j k hjk))
    (hqkPrimeIdeal_prime : qkPrimeIdeal.IsPrime)
    (hqkPrimeIdeal_def : qkPrimeIdeal =
      Ideal.comap
        (rawTensorCancel A₀.RStage (fun a b h ↦ A₀.map a b h) P₀ j.2 k.2 hjk hcomp).toRingHom
        (Ideal.comap (descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e k)
          (IsLocalRing.maximalIdeal S)))
    (hM0 : M0 ≤ qkPrimeIdeal.primeCompl)
    (hT1 : @IsLocalization (towerLocalT0 A₀ i₀ P₀ j k hjk) _ M0
      (towerLocalT1 (S := S) A₀ i₀ P₀ hRalg e j k hjk) _ alpha.toAlgebra)
    (hStageFormula :
      letI : Algebra (A₀.RStage j.1) (A₀.RStage k.1) := (A₀.map j.1 k.1 hjk).toAlgebra
      ∀ (x : descendedTailRawStage A₀ i₀ P₀ j) (y : A₀.RStage k.1),
        gammaBase (alpha (x ⊗ₜ[A₀.RStage j.1] y)) =
          targetMapJK (leftAlgHom x) * stageMapTail k y)
    {Q : Prop}
    (hnext : (p : Ideal (towerLocalT1 (S := S) A₀ i₀ P₀ hRalg e j k hjk)) →
      (hp : p.IsPrime) →
        (letI : p.IsPrime := hp; p.primeCompl.IsLocalizationMap gammaBase) → Q) : Q := by
  obtain ⟨p, hp, hmap⟩ :=
    towerLocal_descended_transition_prime (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp
      stageMapTail hstageMapTail_apply j k hjk hcomp leftAlgHom hleftAlgHom
      targetMapJK htargetMapJK alpha gammaBase M0 qkPrimeIdeal hqkPrimeIdeal_prime
      hqkPrimeIdeal_def hM0 hT1 hStageFormula
  exact hnext p hp hmap

end SameUniverse
