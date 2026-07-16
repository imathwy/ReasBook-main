import stacks_proof.stacks_project.Chap10.Lemma_10_99_11.PrimeLocalizationTensor

open CategoryTheory.Limits IsLocalRing
open scoped TensorProduct Pointwise

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite S M]

/-- Helper for Lemma 10.99.11: the inverse of `localizedQuotientEquiv` sends a localized quotient
generator to the quotient class of the localized numerator. -/
lemma localized_quotient_equiv_symm_apply_mk
    {A : Type*} [CommRing A] (T : Submonoid A)
    {P : Type*} [AddCommGroup P] [Module A P]
    (K0 : Submodule A P) (x : P) :
    (localizedQuotientEquiv T K0).symm
      (LocalizedModule.mkLinearMap T (P ⧸ K0) (Submodule.Quotient.mk x)) =
        Submodule.Quotient.mk (LocalizedModule.mkLinearMap T P x) := by
  -- Proof comment: the canonical localization equivalence is characterized by its action on
  -- quotient generators.
  simpa [localizedQuotientEquiv, Submodule.toLocalizedQuotient] using
    (IsLocalizedModule.linearEquiv_symm_apply
      (S := T)
      (f := K0.toLocalizedQuotient T)
      (g := LocalizedModule.mkLinearMap T (P ⧸ K0))
      (x := Submodule.Quotient.mk x))

/-- Helper for Lemma 10.99.11: quotienting by an ideal contained in a prime sends the source prime
complement to the induced prime complement in the quotient ring. -/
lemma quotient_primeCompl_eq_algebraMapSubmonoid_at_under
    {A : Type*} [CommRing A] (I q : Ideal A) [q.IsPrime]
    [(Ideal.map (Ideal.Quotient.mk I) q).IsPrime] (hIq : I ≤ q) :
    Algebra.algebraMapSubmonoid (A ⧸ I) q.primeCompl =
      (Ideal.map (Ideal.Quotient.mk I) q).primeCompl := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    -- Proof comment: if `a mod I` landed in the quotient prime, pulling back along the quotient
    -- map would force `a ∈ q`, contradicting `a ∉ q`.
    change Ideal.Quotient.mk I a ∉ Ideal.map (Ideal.Quotient.mk I) q
    intro hx
    have hqx : a ∈ Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) q) := by
      exact hx
    exact ha <| by simpa [Ideal.comap_map_mk hIq] using hqx
  · intro hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨a, ?_, rfl⟩
    -- Proof comment: conversely, if `a mod I` avoids the quotient prime, then `a` itself already
    -- avoids `q`.
    intro ha
    exact hx (Ideal.mem_map_of_mem (Ideal.Quotient.mk I) ha)

/-- Helper for Lemma 10.99.11: quotienting by `IS • M` over `S` is the same source quotient as
quotienting by `I • M` over `R`, after restricting scalars. -/
lemma smul_top_eq_mapped_ideal_restrictScalars
    (I : Ideal R) :
    (I • (⊤ : Submodule R M)) =
      (((Ideal.map (algebraMap R S) I) • (⊤ : Submodule S M)).restrictScalars R) := by
  -- Proof comment: this is the standard denominator rewrite from the source `R`-ideal owner to
  -- the mapped `S`-ideal owner used by the localization bridge.
  simpa using
    (Ideal.smul_restrictScalars
      (R := R) (S := S) (M := M) I (⊤ : Submodule S M)).symm

/-- Helper for Lemma 10.99.11: localizing the mapped denominator `(IS) • ⊤` at `q` rewrites to
the direct image ideal acting on `M_q`. -/
lemma localized_mapped_ideal_smul_top_eq
    (I : Ideal R) (q : PrimeSpectrum S) :
    let Sq := Localization.AtPrime q.asIdeal
    let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
    (((Ideal.map (algebraMap R S) I) • (⊤ : Submodule S M)).localized q.asIdeal.primeCompl) =
      ((Ideal.map (algebraMap R Sq) I) • (⊤ : Submodule Sq Mq)) := by
  let Sq := Localization.AtPrime q.asIdeal
  let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
  -- Proof comment: localizing a mapped ideal action commutes with localizing the ideal and the
  -- module separately.
  rw [Submodule.localized, Submodule.localized'_smul, Ideal.localized'_eq_map, Ideal.map_map,
    Submodule.localized'_top]
  have hmap :
      Ideal.map ((algebraMap S Sq).comp (algebraMap R S)) I =
        Ideal.map (algebraMap R Sq) I := by
    exact congrArg (fun f : R →+* Sq ↦ Ideal.map f I) (by ext r <;> rfl)
  simpa [Sq, Mq, hmap]

/-- Helper for Lemma 10.99.11: localizing the mapped-ideal closed fiber over `S` is the same as
quotienting `M_q` by the localized image ideal `(IS)_q`. -/
noncomputable def localized_quotient_equiv_mapped_ideal
    (I : Ideal R) (q : PrimeSpectrum S) :
    let Sq := Localization.AtPrime q.asIdeal
    let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
    LocalizedModule.AtPrime q.asIdeal
        (M ⧸ ((Ideal.map (algebraMap R S) I) • (⊤ : Submodule S M))) ≃ₗ[Sq]
      Mq ⧸ ((Ideal.map (algebraMap R Sq) I) • (⊤ : Submodule Sq Mq)) :=
  let Sq := Localization.AtPrime q.asIdeal
  let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
  let IS : Ideal S := Ideal.map (algebraMap R S) I
  let Kq : Ideal Sq := Ideal.map (algebraMap R Sq) I
  (localizedQuotientEquiv q.asIdeal.primeCompl (IS • (⊤ : Submodule S M))).symm.trans
    (Submodule.quotEquivOfEq
      (((IS • (⊤ : Submodule S M)).localized q.asIdeal.primeCompl))
      (Kq • (⊤ : Submodule Sq Mq))
      (localized_mapped_ideal_smul_top_eq (R := R) (S := S) (M := M) I q))

/-- Helper for Lemma 10.99.11: the quotient-localization comparison sends the localized class of
`m` to the class of the localized numerator in `M_q / (IS)_q M_q`. -/
lemma localized_quotient_equiv_mapped_ideal_apply_mk
    (I : Ideal R) (q : PrimeSpectrum S) (m : M) :
    let Sq := Localization.AtPrime q.asIdeal
    let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
    localized_quotient_equiv_mapped_ideal (R := R) (S := S) (M := M) I q
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl
        (M ⧸ ((Ideal.map (algebraMap R S) I) • (⊤ : Submodule S M))) (Submodule.Quotient.mk m)) =
      Submodule.Quotient.mk (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M m) := by
  let Sq := Localization.AtPrime q.asIdeal
  let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
  let IS : Ideal S := Ideal.map (algebraMap R S) I
  let Kq : Ideal Sq := Ideal.map (algebraMap R Sq) I
  -- Proof comment: compute the two comparison steps separately on the quotient generator `m`.
  rw [localized_quotient_equiv_mapped_ideal]
  simp only [LinearEquiv.trans_apply]
  rw [localized_quotient_equiv_symm_apply_mk]
  rw [Submodule.quotEquivOfEq_mk]

/-- Helper for Lemma 10.99.11: the concrete quotient-localization map from
`M / ISM` to `M_q / I S_q M_q`. -/
noncomputable def localized_closed_fiber_mapped_ideal_map
    (I : Ideal R) (q : PrimeSpectrum S)
    (hlocalized :
      (((Ideal.map (algebraMap R S) I) • (⊤ : Submodule S M)).localized q.asIdeal.primeCompl) =
        ((Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) I) •
          (⊤ : Submodule (Localization.AtPrime q.asIdeal)
            (LocalizedModule.AtPrime q.asIdeal M)))) :
    let Sq := Localization.AtPrime q.asIdeal
    let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let Kq : Ideal Sq := Ideal.map (algebraMap R Sq) I
    (M ⧸ (IS • (⊤ : Submodule S M))) →ₗ[S] (Mq ⧸ (Kq • (⊤ : Submodule Sq Mq))) :=
  let Sq := Localization.AtPrime q.asIdeal
  let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
  let IS : Ideal S := Ideal.map (algebraMap R S) I
  let Kq : Ideal Sq := Ideal.map (algebraMap R Sq) I
  ((LinearEquiv.restrictScalars S <|
      localized_quotient_equiv_mapped_ideal (R := R) (S := S) (M := M) I q).toLinearMap).comp
    (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (M ⧸ (IS • (⊤ : Submodule S M))))

/-- Helper for Lemma 10.99.11: the concrete quotient-localization map sends the class of `m` to
the class of the localized numerator. -/
@[simp] theorem localized_closed_fiber_mapped_ideal_map_apply_mk
    (I : Ideal R) (q : PrimeSpectrum S)
    (hlocalized :
      (((Ideal.map (algebraMap R S) I) • (⊤ : Submodule S M)).localized q.asIdeal.primeCompl) =
        ((Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) I) •
          (⊤ : Submodule (Localization.AtPrime q.asIdeal)
            (LocalizedModule.AtPrime q.asIdeal M))))
    (m : M) :
    let Sq := Localization.AtPrime q.asIdeal
    let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let Kq : Ideal Sq := Ideal.map (algebraMap R Sq) I
    localized_closed_fiber_mapped_ideal_map (R := R) (S := S) (M := M) I q hlocalized
      (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M m) := by
  -- Proof comment: the concrete map is the localization map followed by the packaged quotient
  -- comparison, so its generator formula is immediate from the previous helper.
  change
    (LinearEquiv.restrictScalars S
      (localized_quotient_equiv_mapped_ideal (R := R) (S := S) (M := M) I q))
        (LocalizedModule.mkLinearMap q.asIdeal.primeCompl
          (M ⧸ ((Ideal.map (algebraMap R S) I) • (⊤ : Submodule S M))) (Submodule.Quotient.mk m)) =
      Submodule.Quotient.mk (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M m)
  simpa using
    localized_quotient_equiv_mapped_ideal_apply_mk (R := R) (S := S) (M := M) I q m

/-- Helper for Lemma 10.99.11: after restricting scalars from `S_q` to `R_p`, the concrete
quotient target `M_q / I S_q M_q` becomes the textbook closed fiber `M_q / J M_q`. -/
noncomputable def localized_closed_fiber_target_equiv
    {A : Type*} {B : Type*} {N : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (J : Ideal A) (K : Ideal B)
    (hdenom :
      ((K • (⊤ : Submodule B N)).restrictScalars A) = J • (⊤ : Submodule A N)) :
    (N ⧸ (K • (⊤ : Submodule B N))) ≃ₗ[A]
      (N ⧸ (J • (⊤ : Submodule A N))) :=
  (Submodule.Quotient.restrictScalarsEquiv A (K • (⊤ : Submodule B N))).symm.trans
    (Submodule.quotEquivOfEq _ _ hdenom)

/-- Helper for Chap10 Lemma 10 99 11: when the target denominator ideal is the image of the
source denominator ideal, the denominator comparison is linear over the quotient source ring. -/
noncomputable def localized_closed_fiber_target_equiv_quotient_linear
    {A : Type*} {B : Type*} {N : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (J : Ideal A)
    (hdenom :
      (((Ideal.map (algebraMap A B) J) • (⊤ : Submodule B N)).restrictScalars A) =
        J • (⊤ : Submodule A N)) :
    (N ⧸ ((Ideal.map (algebraMap A B) J) • (⊤ : Submodule B N))) ≃ₗ[A ⧸ J]
      (N ⧸ (J • (⊤ : Submodule A N))) :=
  let K : Ideal B := Ideal.map (algebraMap A B) J
  letI : Algebra (A ⧸ J) (B ⧸ K) := Ideal.Quotient.algebraQuotientMapQuotient
  letI : Module (A ⧸ J) (N ⧸ (K • (⊤ : Submodule B N))) :=
    Module.compHom _ (algebraMap (A ⧸ J) (B ⧸ K))
  let e : (N ⧸ (K • (⊤ : Submodule B N))) ≃ₗ[A]
      (N ⧸ (J • (⊤ : Submodule A N))) :=
    localized_closed_fiber_target_equiv (A := A) (B := B) (N := N) J K hdenom
  e.extendScalarsOfSurjective Ideal.Quotient.mk_surjective

/-- Helper for Chap10 Lemma 10 99 11: the quotient-linear denominator comparison sends quotient
generators to the same numerator class. -/
lemma localized_closed_fiber_target_equiv_quotient_linear_apply_mk
    {A : Type*} {B : Type*} {N : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (J : Ideal A)
    (hdenom :
      (((Ideal.map (algebraMap A B) J) • (⊤ : Submodule B N)).restrictScalars A) =
        J • (⊤ : Submodule A N))
    (n : N) :
    localized_closed_fiber_target_equiv_quotient_linear
        (A := A) (B := B) (N := N) J hdenom (Submodule.Quotient.mk n) =
      (Submodule.Quotient.mk n : N ⧸ (J • (⊤ : Submodule A N))) := by
  -- Proof comment: the quotient-linear comparison is the source-linear denominator equivalence
  -- with scalars extended along `A → A / J`, so its value on quotient generators is unchanged.
  simp [localized_closed_fiber_target_equiv_quotient_linear,
    localized_closed_fiber_target_equiv]

/-- Helper for Lemma 10.99.11: after localizing at a prime, pushing forward the pullback ideal
recovers the original ideal in the localization. -/
theorem source_localized_ideal_map_eq
    {A : Type u} [CommRing A] {p : Ideal A} [p.IsPrime] (K : Ideal (Localization.AtPrime p)) :
    Ideal.map (algebraMap A (Localization.AtPrime p))
      (Ideal.comap (algebraMap A (Localization.AtPrime p)) K) = K := by
  -- Proof comment: this is the canonical localization identity `map (comap K) = K`.
  simpa using
    (IsLocalization.map_comap p.primeCompl (Localization.AtPrime p) K :
      Ideal.map (algebraMap A (Localization.AtPrime p))
        (Ideal.comap (algebraMap A (Localization.AtPrime p)) K) = K)

/-- Helper for Lemma 10.99.11: the quotient of a localization by an ideal carries the canonical
quotient-ring algebra structure coming from the source ring. -/
@[reducible]
noncomputable def localized_quotient_target_algebra
    {A : Type u} [CommRing A] {p : Ideal A} [p.IsPrime] (K : Ideal (Localization.AtPrime p)) :
    Algebra (A ⧸ Ideal.comap (algebraMap A (Localization.AtPrime p)) K)
      (Localization.AtPrime p ⧸ K) :=
  inferInstance

/-- Helper for Lemma 10.99.11: mapping an ideal along the identity algebra equivalence does not
change that ideal. -/
theorem ideal_map_algEquiv_refl
    {A : Type u} [CommRing A] (I : Ideal A) :
    Ideal.map (AlgEquiv.refl : A ≃ₐ[A] A) I = I := by
  -- Proof comment: the identity algebra equivalence is just the identity ring homomorphism.
  change Ideal.map (RingHom.id A) I = I
  simpa using (Ideal.map_id (I := I))

/-- Helper for Lemma 10.99.11: the quotient of `A_p` by the localized source ideal carries the
canonical `A / J`-algebra structure induced from the quotient map `A → A_p`. -/
@[reducible]
noncomputable def source_localized_quotient_target_algebra
    {A : Type u} [CommRing A] {p : Ideal A} [p.IsPrime] (J : Ideal A) :
    Algebra (A ⧸ J)
      (Localization.AtPrime p ⧸ Ideal.map (algebraMap A (Localization.AtPrime p)) J) :=
  Ideal.Quotient.algebraQuotientMapQuotient

/-- Helper for Lemma 10.99.11: the mapped ideal inside `A_p` lies over its contracted source
ideal. -/
theorem source_localized_mapped_ideal_liesOver
    {A : Type u} [CommRing A] {p : Ideal A} [p.IsPrime] (K : Ideal (Localization.AtPrime p)) :
    let J : Ideal A := Ideal.comap (algebraMap A (Localization.AtPrime p)) K
    let Kmap : Ideal (Localization.AtPrime p) :=
      Ideal.map (algebraMap A (Localization.AtPrime p)) J
    Kmap.LiesOver J := by
  let J : Ideal A := Ideal.comap (algebraMap A (Localization.AtPrime p)) K
  let Kmap : Ideal (Localization.AtPrime p) :=
    Ideal.map (algebraMap A (Localization.AtPrime p)) J
  have hKmap : Kmap = K := source_localized_ideal_map_eq (A := A) (p := p) K
  -- Proof comment: after replacing `Kmap` by `K`, the defining contraction is the source ideal.
  refine ⟨?_⟩
  simpa [Ideal.under_def, J, hKmap]

/-- Helper for Lemma 10.99.11: the target ideal `K ⊂ A_p` lies over its contracted source
ideal. -/
theorem source_localized_target_ideal_liesOver
    {A : Type u} [CommRing A] {p : Ideal A} [p.IsPrime] (K : Ideal (Localization.AtPrime p)) :
    let J : Ideal A := Ideal.comap (algebraMap A (Localization.AtPrime p)) K
    K.LiesOver J := by
  let J : Ideal A := Ideal.comap (algebraMap A (Localization.AtPrime p)) K
  -- Proof comment: this is the defining contraction equality for the source ideal `J`.
  refine ⟨?_⟩
  simp [Ideal.under_def, J]

/-- Helper for Lemma 10.99.11: the quotient transport from `Kmap` to `K` is induced by the
identity algebra equivalence on the localization. -/
theorem source_localized_target_ideal_eq_map_refl
    {A : Type u} [CommRing A] {p : Ideal A} [p.IsPrime] (K : Ideal (Localization.AtPrime p)) :
    let J : Ideal A := Ideal.comap (algebraMap A (Localization.AtPrime p)) K
    let Kmap : Ideal (Localization.AtPrime p) :=
      Ideal.map (algebraMap A (Localization.AtPrime p)) J
    K =
      Ideal.map (AlgEquiv.refl : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime p) Kmap := by
  let J : Ideal A := Ideal.comap (algebraMap A (Localization.AtPrime p)) K
  let Kmap : Ideal (Localization.AtPrime p) :=
    Ideal.map (algebraMap A (Localization.AtPrime p)) J
  have hKmap : Kmap = K := source_localized_ideal_map_eq (A := A) (p := p) K
  calc
    K = Ideal.map (AlgEquiv.refl : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime p) K := by
      exact (ideal_map_algEquiv_refl (A := Localization.AtPrime p) K).symm
    _ =
        Ideal.map (AlgEquiv.refl : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime p) Kmap := by
          simpa using
            congrArg
              (fun I : Ideal (Localization.AtPrime p) ↦
                Ideal.map (AlgEquiv.refl : Localization.AtPrime p ≃ₐ[A]
                  Localization.AtPrime p) I)
              hKmap.symm

/-- Helper for Lemma 10.99.11: localizing the quotient `A / comap K` at the image of
`p.primeCompl` identifies with the quotient of `A_p` by `K`. -/
noncomputable def source_localized_quotient_localization_algEquiv
    {A : Type u} [CommRing A] {p : Ideal A} [p.IsPrime] (K : Ideal (Localization.AtPrime p)) :
    Localization
        (Algebra.algebraMapSubmonoid
          (A ⧸ Ideal.comap (algebraMap A (Localization.AtPrime p)) K) p.primeCompl) ≃ₐ[
        A ⧸ Ideal.comap (algebraMap A (Localization.AtPrime p)) K] (Localization.AtPrime p ⧸ K) :=
  by
    let J : Ideal A := Ideal.comap (algebraMap A (Localization.AtPrime p)) K
    let Kmap : Ideal (Localization.AtPrime p) :=
      Ideal.map (algebraMap A (Localization.AtPrime p)) J
    letI : Algebra (A ⧸ J) (Localization.AtPrime p ⧸ Kmap) :=
      source_localized_quotient_target_algebra (A := A) (p := p) J
    let hKmap : Kmap = K := source_localized_ideal_map_eq (A := A) (p := p) K
    letI : Kmap.LiesOver J := ⟨by simpa [Ideal.under_def, J, hKmap]⟩
    letI : K.LiesOver J := ⟨by simpa [Ideal.under_def, J]⟩
    let eLoc :
        Localization (Algebra.algebraMapSubmonoid (A ⧸ J) p.primeCompl) ≃ₐ[A ⧸ J]
          (Localization.AtPrime p ⧸ Kmap) :=
      Localization.algEquiv
        (Algebra.algebraMapSubmonoid (A ⧸ J) p.primeCompl)
        (Localization.AtPrime p ⧸ Kmap)
    let eQuot :
        (Localization.AtPrime p ⧸ Kmap) ≃ₐ[A ⧸ J] (Localization.AtPrime p ⧸ K) :=
      let hKmap' :
          K = Ideal.map (AlgEquiv.refl : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime p)
            Kmap := by
        calc
          K = Ideal.map (AlgEquiv.refl : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime p) K := by
            exact (ideal_map_algEquiv_refl (A := Localization.AtPrime p) K).symm
          _ = Ideal.map (AlgEquiv.refl : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime p) Kmap := by
              simpa using
                congrArg
                  (fun I : Ideal (Localization.AtPrime p) ↦
                    Ideal.map (AlgEquiv.refl : Localization.AtPrime p ≃ₐ[A]
                      Localization.AtPrime p) I)
                  hKmap.symm
      Ideal.Quotient.algEquivOfEqMap
        (p := J)
        (P := Kmap)
        (Q := K)
        (σ := (AlgEquiv.refl : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime p))
        hKmap'
    -- Proof comment: first identify the localization of `A / J` with the quotient by `Kmap`, then
    -- rewrite `Kmap = K` by the canonical localization map-comap identity.
    exact eLoc.trans eQuot

/-- Helper for Lemma 10.99.11: the quotient-localization ring comparison sends the class of
`x / 1` to the class of its image in the localized quotient. -/
theorem source_localized_quotient_localization_algEquiv_apply_mk
    {A : Type u} [CommRing A] {p : Ideal A} [p.IsPrime] (K : Ideal (Localization.AtPrime p))
    (x : A) :
    let J : Ideal A := Ideal.comap (algebraMap A (Localization.AtPrime p)) K
    source_localized_quotient_localization_algEquiv (A := A) (p := p) K
      (algebraMap (A ⧸ J)
        (Localization
          (Algebra.algebraMapSubmonoid (A ⧸ J) p.primeCompl))
        (Ideal.Quotient.mk J x)) =
      Ideal.Quotient.mk K (algebraMap A (Localization.AtPrime p) x) := by
  let J : Ideal A := Ideal.comap (algebraMap A (Localization.AtPrime p)) K
  let Kmap : Ideal (Localization.AtPrime p) :=
    Ideal.map (algebraMap A (Localization.AtPrime p)) J
  letI : Algebra (A ⧸ J) (Localization.AtPrime p ⧸ Kmap) :=
    source_localized_quotient_target_algebra (A := A) (p := p) J
  let hKmap : Kmap = K := source_localized_ideal_map_eq (A := A) (p := p) K
  letI : Kmap.LiesOver J := ⟨by simpa [Ideal.under_def, J, hKmap]⟩
  letI : K.LiesOver J := ⟨by simpa [Ideal.under_def, J]⟩
  let eLoc :
      Localization (Algebra.algebraMapSubmonoid (A ⧸ J) p.primeCompl) ≃ₐ[A ⧸ J]
        (Localization.AtPrime p ⧸ Kmap) :=
    Localization.algEquiv
      (Algebra.algebraMapSubmonoid (A ⧸ J) p.primeCompl)
      (Localization.AtPrime p ⧸ Kmap)
  let hKmap' :
      K = Ideal.map (AlgEquiv.refl : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime p) Kmap := by
    calc
      K = Ideal.map (AlgEquiv.refl : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime p) K := by
        exact (ideal_map_algEquiv_refl (A := Localization.AtPrime p) K).symm
      _ = Ideal.map (AlgEquiv.refl : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime p) Kmap := by
          simpa using
            congrArg
              (fun I : Ideal (Localization.AtPrime p) ↦
                Ideal.map (AlgEquiv.refl : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime p) I)
              hKmap.symm
  let eQuot :
      (Localization.AtPrime p ⧸ Kmap) ≃ₐ[A ⧸ J] (Localization.AtPrime p ⧸ K) :=
    Ideal.Quotient.algEquivOfEqMap
      (p := J)
      (P := Kmap)
      (Q := K)
      (σ := (AlgEquiv.refl : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime p))
      hKmap'
  -- Proof comment: compute the localization step on the class of `x / 1`, then apply the
  -- quotient transport from `Kmap` to `K`.
  change eQuot
      (eLoc
        (algebraMap (A ⧸ J)
          (Localization (Algebra.algebraMapSubmonoid (A ⧸ J) p.primeCompl))
          (Ideal.Quotient.mk J x))) =
    Ideal.Quotient.mk K (algebraMap A (Localization.AtPrime p) x)
  rw [← IsLocalization.mk'_one
    (M := Algebra.algebraMapSubmonoid (A ⧸ J) p.primeCompl)
    (S := Localization (Algebra.algebraMapSubmonoid (A ⧸ J) p.primeCompl))
    (x := Ideal.Quotient.mk J x)]
  rw [show eLoc =
      Localization.algEquiv
        (Algebra.algebraMapSubmonoid (A ⧸ J) p.primeCompl)
        (Localization.AtPrime p ⧸ Kmap) by rfl]
  rw [Localization.algEquiv_mk']
  rw [IsLocalization.mk'_one]
  simpa [eQuot] using
    (Ideal.Quotient.algEquivOfEqMap_apply
      (p := J)
      (σ := (AlgEquiv.refl : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime p))
      hKmap'
      (algebraMap A (Localization.AtPrime p) x))

end
