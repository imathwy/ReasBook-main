import StacksProject_2024.Chap10.Lemma_10_97_8

open IsLocalRing Ideal AdicCompletion

universe u v

namespace Lemma101243CompletionHelpers

/-- Helper for Chap10 Lemma 10 124 3: a ring equivalence of local rings is a local
homomorphism. -/
theorem ringEquiv_isLocalHom_of_localRings
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    IsLocalHom e.toRingHom := by
  -- A surjective map between local rings is local, and a ring equivalence is surjective.
  exact Function.Surjective.isLocalHom _ e.surjective

/-- Helper for Chap10 Lemma 10 124 3: a ring equivalence of local rings maps the maximal ideal
onto the maximal ideal. -/
theorem ringEquiv_map_maximalIdeal_eq_of_localRings
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    Ideal.map e.toRingHom (maximalIdeal A) = maximalIdeal B := by
  letI : IsLocalHom e.toRingHom := ringEquiv_isLocalHom_of_localRings e
  -- The image of the unique maximal ideal under a surjective local map is the target maximal
  -- ideal.
  simpa using IsLocalRing.map_maximalIdeal_of_surjective e.toRingHom e.surjective

/-- Helper for Chap10 Lemma 10 124 3: a local-ring equivalence sends powers of the source
maximal ideal into the corresponding powers of the target maximal ideal. -/
theorem ringEquiv_pow_maximalIdeal_le_comap_pow_maximalIdeal
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) (n : ℕ) :
    maximalIdeal A ^ n ≤ Ideal.comap e.toRingHom (maximalIdeal B ^ n) := by
  letI : IsLocalHom e.toRingHom := ringEquiv_isLocalHom_of_localRings e
  -- This is the standard maximal-ideal power containment for local homomorphisms.
  simpa using pow_maximalIdeal_le_comap_pow_maximalIdeal e.toRingHom n

/-- Helper for Chap10 Lemma 10 124 3: contracting a target maximal-ideal power along a
local-ring equivalence recovers the source maximal-ideal power. -/
theorem ringEquiv_comap_maximalIdeal_pow_eq
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) (n : ℕ) :
    Ideal.comap e.toRingHom (maximalIdeal B ^ n) = maximalIdeal A ^ n := by
  have hker : Ideal.comap e.toRingHom (⊥ : Ideal B) = ⊥ := by
    ext x
    simp [Ideal.mem_comap]
  have hmap :
      Ideal.map e.toRingHom (maximalIdeal A ^ n) = maximalIdeal B ^ n := by
    calc
      Ideal.map e.toRingHom (maximalIdeal A ^ n)
          = Ideal.map e.toRingHom (maximalIdeal A) ^ n := by
            rw [Ideal.map_pow]
      _ = maximalIdeal B ^ n := by
            rw [ringEquiv_map_maximalIdeal_eq_of_localRings e]
  -- Surjectivity of the equivalence identifies contraction after extension with the original
  -- ideal.
  calc
    Ideal.comap e.toRingHom (maximalIdeal B ^ n)
        = Ideal.comap e.toRingHom (Ideal.map e.toRingHom (maximalIdeal A ^ n)) := by
            rw [hmap]
    _ = maximalIdeal A ^ n ⊔ Ideal.comap e.toRingHom (⊥ : Ideal B) := by
          exact Ideal.comap_map_of_surjective e.toRingHom e.surjective (maximalIdeal A ^ n)
    _ = maximalIdeal A ^ n := by rw [hker, sup_bot_eq]

/-- Helper for Chap10 Lemma 10 124 3: the quotient map induced by a local-ring equivalence on
maximal-ideal powers is bijective. -/
theorem ringEquiv_quotient_maximalIdeal_pow_bijective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) (n : ℕ) :
    Function.Bijective
      (Ideal.quotientMap (maximalIdeal B ^ n) e.toRingHom
        (ringEquiv_pow_maximalIdeal_le_comap_pow_maximalIdeal e n)) := by
  let qPow :
      A ⧸ Ideal.comap e.toRingHom (maximalIdeal B ^ n) →+* B ⧸ maximalIdeal B ^ n :=
    Ideal.quotientMap (maximalIdeal B ^ n) e.toRingHom le_rfl
  let eSource :
      A ⧸ Ideal.comap e.toRingHom (maximalIdeal B ^ n) ≃+* A ⧸ maximalIdeal A ^ n :=
    Ideal.quotEquivOfEq (ringEquiv_comap_maximalIdeal_pow_eq e n)
  have hEq :
      Ideal.quotientMap (maximalIdeal B ^ n) e.toRingHom
          (ringEquiv_pow_maximalIdeal_le_comap_pow_maximalIdeal e n) =
        qPow.comp eSource.symm.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    have hs :
        eSource.symm ((Ideal.Quotient.mk (maximalIdeal A ^ n)) x) =
          Ideal.Quotient.mk (Ideal.comap e.toRingHom (maximalIdeal B ^ n)) x := by
      apply eSource.symm_apply_eq.2
      rw [Ideal.quotEquivOfEq_mk]
    -- Both quotient maps send the class of `x` to the class of `e x`.
    calc
      (Ideal.quotientMap (maximalIdeal B ^ n) e.toRingHom
          (ringEquiv_pow_maximalIdeal_le_comap_pow_maximalIdeal e n))
          ((Ideal.Quotient.mk (maximalIdeal A ^ n)) x)
          = (Ideal.Quotient.mk (maximalIdeal B ^ n)) (e.toRingHom x) := by
              rw [Ideal.quotientMap_mk]
      _ = qPow (eSource.symm ((Ideal.Quotient.mk (maximalIdeal A ^ n)) x)) := by
              rw [hs, Ideal.quotientMap_mk]
  have hqPow_inj : Function.Injective qPow := by
    change Function.Injective (Ideal.quotientMap (maximalIdeal B ^ n) e.toRingHom le_rfl)
    exact Ideal.quotientMap_injective
  have hqPow_surj : Function.Surjective qPow := by
    intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, rfl⟩ := e.surjective b
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Ideal.quotientMap_mk]
    rfl
  rw [hEq]
  constructor
  · intro x y hxy
    apply eSource.symm.injective
    exact hqPow_inj hxy
  · intro z
    obtain ⟨w, hw⟩ := hqPow_surj z
    refine ⟨eSource w, ?_⟩
    change qPow (eSource.symm (eSource w)) = z
    rw [eSource.symm_apply_apply]
    exact hw

/-- Helper for Chap10 Lemma 10 124 3: a local-ring equivalence induces quotient-power
equivalences on the maximal-ideal inverse systems. -/
noncomputable abbrev ringEquiv_quotient_maximalIdeal_pow
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) (n : ℕ) :
    A ⧸ maximalIdeal A ^ n ≃+* B ⧸ maximalIdeal B ^ n :=
  let _ : IsLocalHom e.toRingHom := ringEquiv_isLocalHom_of_localRings e
  RingEquiv.ofBijective
    (Ideal.quotientMap (maximalIdeal B ^ n) e.toRingHom
      (ringEquiv_pow_maximalIdeal_le_comap_pow_maximalIdeal e n))
    (ringEquiv_quotient_maximalIdeal_pow_bijective e n)

/-- Helper for Chap10 Lemma 10 124 3: quotient-power equivalences from a local-ring equivalence
commute with transition maps. -/
theorem ringEquiv_quotient_maximalIdeal_pow_compatible
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B)
    {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal B) hle).comp
        (ringEquiv_quotient_maximalIdeal_pow e n).toRingHom =
      (ringEquiv_quotient_maximalIdeal_pow e m).toRingHom.comp
        (Ideal.Quotient.factorPow (maximalIdeal A) hle) := by
  letI : IsLocalHom e.toRingHom := ringEquiv_isLocalHom_of_localRings e
  -- Both transition routes send the class of `x` to the smaller quotient class of `e x`.
  apply Ideal.Quotient.ringHom_ext
  ext x
  simp [ringEquiv_quotient_maximalIdeal_pow, Ideal.quotientMap_mk]

/-- Helper for Chap10 Lemma 10 124 3: quotient-stage evaluations on an adic completion commute
with the transition maps of the inverse system. -/
theorem completion_eval_factor
    {A : Type u} [CommRing A] (I : Ideal A)
    {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion I A) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  let p : AdicCompletion I A → Prop := fun y ↦
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n y) =
      AdicCompletion.evalₐ I m y
  change p x
  -- Reduce to a Cauchy representative and use compatibility of its quotient classes.
  refine AdicCompletion.induction_on I A x ?_
  intro f
  change
    Ideal.Quotient.factorPow I hle
        (AdicCompletion.evalₐ I n (AdicCompletion.mk I A f)) =
      AdicCompletion.evalₐ I m (AdicCompletion.mk I A f)
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  simpa using (AdicCompletion.Ideal.mk_eq_mk I hle f)

/-- Helper for Chap10 Lemma 10 124 3: a ring equivalence of local rings induces a bijection on
maximal-ideal completions. -/
theorem maximalIdealCompletionMap_evalₐ
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) [IsLocalHom f]
    (n : ℕ) (x : AdicCompletion (maximalIdeal A) A) :
    AdicCompletion.evalₐ (maximalIdeal B) n (maximalIdealCompletionMap f x) =
      Ideal.quotientMap (maximalIdeal B ^ n) f
        (pow_maximalIdeal_le_comap_pow_maximalIdeal f n)
        (AdicCompletion.evalₐ (maximalIdeal A) n x) := by
  let p : AdicCompletion (maximalIdeal A) A → Prop := fun y ↦
    AdicCompletion.evalₐ (maximalIdeal B) n (maximalIdealCompletionMap f y) =
      Ideal.quotientMap (maximalIdeal B ^ n) f
        (pow_maximalIdeal_le_comap_pow_maximalIdeal f n)
        (AdicCompletion.evalₐ (maximalIdeal A) n y)
  change p x
  -- Proof comment: completion-stage values are determined on Cauchy representatives, where the
  -- defining quotient map of `maximalIdealCompletionMap` is explicit.
  refine AdicCompletion.induction_on (maximalIdeal A) A x ?_
  intro r
  change
    AdicCompletion.evalₐ (maximalIdeal B) n
        (maximalIdealCompletionMap f (AdicCompletion.mk (maximalIdeal A) A r)) =
      Ideal.quotientMap (maximalIdeal B ^ n) f
        (pow_maximalIdeal_le_comap_pow_maximalIdeal f n)
        (AdicCompletion.evalₐ (maximalIdeal A) n (AdicCompletion.mk (maximalIdeal A) A r))
  rw [AdicCompletion.evalₐ_mk]
  simpa using maximalIdealCompletionMap_evalₐ_mk f n r

/-- Helper for Chap10 Lemma 10 124 3: under a local-ring equivalence, the completion map acts on
finite quotient stages by the induced quotient equivalence. -/
theorem maximalIdealCompletionMap_evalₐ_of_ringEquiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B)
    (n : ℕ) (x : AdicCompletion (maximalIdeal A) A) :
    AdicCompletion.evalₐ (maximalIdeal B) n
        (@maximalIdealCompletionMap A B _ _ _ _ e.toRingHom
          (ringEquiv_isLocalHom_of_localRings e) x) =
      (ringEquiv_quotient_maximalIdeal_pow e n)
        (AdicCompletion.evalₐ (maximalIdeal A) n x) := by
  letI : IsLocalHom e.toRingHom := ringEquiv_isLocalHom_of_localRings e
  -- Proof comment: specialize the generic stage formula and recognize the quotient map hidden in
  -- `ringEquiv_quotient_maximalIdeal_pow`.
  simpa [ringEquiv_quotient_maximalIdeal_pow, Ideal.quotientMap_mk] using
    (maximalIdealCompletionMap_evalₐ (f := e.toRingHom) n x)

/-- Helper for Chap10 Lemma 10 124 3: the inverse quotient-power equivalence sends a dense target
class to the dense source class of the inverse image. -/
theorem ringEquiv_quotient_maximalIdeal_pow_symm_mk
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B)
    (n : ℕ) (b : B) :
    (ringEquiv_quotient_maximalIdeal_pow e n).symm
        (Ideal.Quotient.mk (maximalIdeal B ^ n) b) =
      Ideal.Quotient.mk (maximalIdeal A ^ n) (e.symm b) := by
  apply (ringEquiv_quotient_maximalIdeal_pow e n).injective
  -- Proof comment: apply the forward quotient equivalence and use that `e` cancels `e.symm`.
  simp [ringEquiv_quotient_maximalIdeal_pow, Ideal.quotientMap_mk]

/-- Helper for Chap10 Lemma 10 124 3: a ring equivalence of local rings induces a bijection on
maximal-ideal completions. -/
theorem maximalIdealCompletionMap_bijective_of_ringEquiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    Function.Bijective (@maximalIdealCompletionMap A B _ _ _ _ e.toRingHom
      (ringEquiv_isLocalHom_of_localRings e)) := by
  letI : IsLocalHom e.toRingHom := ringEquiv_isLocalHom_of_localRings e
  change Function.Bijective (maximalIdealCompletionMap e.toRingHom)
  let π : ∀ n : ℕ, A ⧸ maximalIdeal A ^ n →+* B ⧸ maximalIdeal B ^ n :=
    fun n ↦ (ringEquiv_quotient_maximalIdeal_pow e n).toRingHom
  let eQuot : ∀ n : ℕ, A ⧸ maximalIdeal A ^ n ≃+* B ⧸ maximalIdeal B ^ n :=
    fun n ↦ ringEquiv_quotient_maximalIdeal_pow e n
  let q : ∀ n : ℕ, AdicCompletion (maximalIdeal B) B →+* A ⧸ maximalIdeal A ^ n :=
    fun n ↦ (eQuot n).symm.toRingHom.comp (AdicCompletion.evalₐ (maximalIdeal B) n)
  have hπ_compat :
      ∀ {m n : ℕ} (hle : m ≤ n),
        (Ideal.Quotient.factorPow (maximalIdeal B) hle).comp (π n) =
          (π m).comp (Ideal.Quotient.factorPow (maximalIdeal A) hle) := by
    intro m n hle
    -- The quotient equivalences commute with the inverse-system transition maps.
    simpa [π, eQuot] using
      ringEquiv_quotient_maximalIdeal_pow_compatible e hle
  have hq_compat :
      ∀ {m n : ℕ} (hle : m ≤ n),
        (Ideal.Quotient.factorPow (maximalIdeal A) hle).comp (q n) = q m := by
    intro m n hle
    ext x
    -- Compare after applying the stage equivalence, where both sides reduce to the target
    -- completion's transition formula.
    apply (eQuot m).injective
    calc
      π m ((Ideal.Quotient.factorPow (maximalIdeal A) hle) (q n x)) =
          (Ideal.Quotient.factorPow (maximalIdeal B) hle) (π n (q n x)) := by
            symm
            exact DFunLike.congr_fun (hπ_compat hle) (q n x)
      _ = (Ideal.Quotient.factorPow (maximalIdeal B) hle)
            (AdicCompletion.evalₐ (maximalIdeal B) n x) := by
              congr 1
              exact RingEquiv.apply_symm_apply
                (eQuot n) (AdicCompletion.evalₐ (maximalIdeal B) n x)
      _ = AdicCompletion.evalₐ (maximalIdeal B) m x := by
              simpa using completion_eval_factor (maximalIdeal B) hle x
      _ = π m (q m x) := by
              exact
                (RingEquiv.apply_symm_apply
                  (eQuot m) (AdicCompletion.evalₐ (maximalIdeal B) m x)).symm
  let ψ : AdicCompletion (maximalIdeal B) B →+*
      AdicCompletion (maximalIdeal A) A :=
    AdicCompletion.liftRingHom (maximalIdeal A) q hq_compat
  let φ : AdicCompletion (maximalIdeal A) A →+*
      AdicCompletion (maximalIdeal B) B :=
    maximalIdealCompletionMap e.toRingHom
  have hφ_eval :
      ∀ n : ℕ, ∀ x : AdicCompletion (maximalIdeal A) A,
        AdicCompletion.evalₐ (maximalIdeal B) n (φ x) =
          π n (AdicCompletion.evalₐ (maximalIdeal A) n x) := by
    intro n x
    let p : AdicCompletion (maximalIdeal A) A → Prop := fun y ↦
      AdicCompletion.evalₐ (maximalIdeal B) n (φ y) =
        π n (AdicCompletion.evalₐ (maximalIdeal A) n y)
    change p x
    -- On Cauchy representatives, the completion map is exactly the quotient map induced by `e`.
    refine AdicCompletion.induction_on (maximalIdeal A) A x ?_
    intro f
    rfl
  have hleft : ψ.comp φ = RingHom.id _ := by
    apply RingHom.ext
    intro x
    -- The inverse composite is checked stagewise on the source completion.
    apply AdicCompletion.ext_evalₐ
    intro n
    calc
      AdicCompletion.evalₐ (maximalIdeal A) n ((ψ.comp φ) x)
          = q n (φ x) := by
              simp [ψ]
      _ = (eQuot n).symm (AdicCompletion.evalₐ (maximalIdeal B) n (φ x)) := by
              rfl
      _ = (eQuot n).symm (π n (AdicCompletion.evalₐ (maximalIdeal A) n x)) := by
              rw [hφ_eval n x]
      _ = AdicCompletion.evalₐ (maximalIdeal A) n x := by
              exact
                RingEquiv.symm_apply_apply
                  (eQuot n) (AdicCompletion.evalₐ (maximalIdeal A) n x)
  have hright : φ.comp ψ = RingHom.id _ := by
    apply RingHom.ext
    intro x
    -- The other composite is the same stagewise calculation on the target completion.
    apply AdicCompletion.ext_evalₐ
    intro n
    calc
      AdicCompletion.evalₐ (maximalIdeal B) n ((φ.comp ψ) x)
          = π n (AdicCompletion.evalₐ (maximalIdeal A) n (ψ x)) := by
              change AdicCompletion.evalₐ (maximalIdeal B) n (φ (ψ x)) =
                π n (AdicCompletion.evalₐ (maximalIdeal A) n (ψ x))
              rw [hφ_eval n (ψ x)]
      _ = π n (q n x) := by
              simp [ψ]
      _ = π n ((eQuot n).symm (AdicCompletion.evalₐ (maximalIdeal B) n x)) := by
              rfl
      _ = AdicCompletion.evalₐ (maximalIdeal B) n x := by
              exact
                RingEquiv.apply_symm_apply
                  (eQuot n) (AdicCompletion.evalₐ (maximalIdeal B) n x)
  exact ⟨
    -- A left inverse gives injectivity of the canonical completion map.
    Function.LeftInverse.injective (fun x ↦ by
      simpa using DFunLike.congr_fun hleft x),
    -- A right inverse gives surjectivity of the canonical completion map.
    Function.RightInverse.surjective (fun x ↦ by
      simpa using DFunLike.congr_fun hright x)⟩

/-- Helper for Chap10 Lemma 10 124 3: the inverse completion equivalence induced by a local-ring
equivalence acts on quotient stages by the inverse quotient-power equivalence. -/
theorem ringEquiv_completion_symm_evalₐ
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B)
    (n : ℕ) (x : AdicCompletion (maximalIdeal B) B) :
    AdicCompletion.evalₐ (maximalIdeal A) n
        ((RingEquiv.ofBijective
            (@maximalIdealCompletionMap A B _ _ _ _ e.toRingHom
              (ringEquiv_isLocalHom_of_localRings e))
            (maximalIdealCompletionMap_bijective_of_ringEquiv e)).symm x) =
      (ringEquiv_quotient_maximalIdeal_pow e n).symm
        (AdicCompletion.evalₐ (maximalIdeal B) n x) := by
  let eCompletion :
      AdicCompletion (maximalIdeal A) A ≃+* AdicCompletion (maximalIdeal B) B :=
    RingEquiv.ofBijective
      (@maximalIdealCompletionMap A B _ _ _ _ e.toRingHom
        (ringEquiv_isLocalHom_of_localRings e))
      (maximalIdealCompletionMap_bijective_of_ringEquiv e)
  apply (ringEquiv_quotient_maximalIdeal_pow e n).injective
  -- Proof comment: apply the forward quotient-stage comparison to the inverse image and then
  -- cancel both the completion equivalence and the quotient equivalence.
  calc
    (ringEquiv_quotient_maximalIdeal_pow e n)
        (AdicCompletion.evalₐ (maximalIdeal A) n (eCompletion.symm x)) =
      AdicCompletion.evalₐ (maximalIdeal B) n
        (@maximalIdealCompletionMap A B _ _ _ _ e.toRingHom
          (ringEquiv_isLocalHom_of_localRings e) (eCompletion.symm x)) := by
            symm
            exact maximalIdealCompletionMap_evalₐ_of_ringEquiv e n (eCompletion.symm x)
    _ = AdicCompletion.evalₐ (maximalIdeal B) n (eCompletion (eCompletion.symm x)) := by
          rfl
    _ = AdicCompletion.evalₐ (maximalIdeal B) n x := by
          rw [eCompletion.apply_symm_apply]
    _ =
      (ringEquiv_quotient_maximalIdeal_pow e n)
        ((ringEquiv_quotient_maximalIdeal_pow e n).symm
          (AdicCompletion.evalₐ (maximalIdeal B) n x)) := by
            symm
            exact
              (ringEquiv_quotient_maximalIdeal_pow e n).apply_symm_apply
                (AdicCompletion.evalₐ (maximalIdeal B) n x)

end Lemma101243CompletionHelpers
