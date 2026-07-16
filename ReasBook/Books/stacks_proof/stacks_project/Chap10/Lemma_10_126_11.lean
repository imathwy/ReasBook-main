import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_32_1
import stacks_proof.stacks_project.Chap10.Lemma_10_23_1
import stacks_proof.stacks_project.Chap10.Lemma_10_32_3
import stacks_proof.stacks_project.Chap10.Lemma_10_79_2
import stacks_proof.stacks_project.Chap10.Lemma_10_126_9
import stacks_proof.stacks_project.Chap10.Lemma_10_126_10

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling:
* primary domain: commutative algebra of extended ideals and quotient algebra maps under an
  `R`-algebra morphism;
* sampled owner declarations:
  `Ideal.le_comap_map`,
  `Ideal.map_map`,
  `Ideal.quotientMapₐ`,
  `Ideal.IsLocallyNilpotent`;
* best owner abstraction: the induced quotient algebra map is the canonical `Ideal.quotientMapₐ`
  for the extended ideals, with containment supplied from `Ideal.le_comap_map` plus
  functoriality of `Ideal.map`;
* layer: the numbered item is `source-facing`, while the quotient map on extended ideals is only a
  `bridge/view` built directly from the owner quotient construction;
* primitive data: `I`, `f`, and the finite type / finite presentation / flatness hypotheses;
* derived API: the quotient map modulo the extended ideal.
-/

universe u v w

section

variable {R : Type u} {S : Type v} {S' : Type w}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S']

private theorem extendedIdeal_le_comap_extendedIdeal {I : Ideal R} (f : S →ₐ[R] S') :
    Ideal.map (algebraMap R S) I ≤
      Ideal.comap (f : S →+* S') (Ideal.map (algebraMap R S') I) := by
  simpa [Ideal.map_map] using
    (show Ideal.map (algebraMap R S) I ≤
        Ideal.comap (f : S →+* S')
          (Ideal.map (f : S →+* S') (Ideal.map (algebraMap R S) I)) from
      Ideal.le_comap_map)

/-- Helper for Lemma 10.126.11: localizing the extended ideal `I S` at `q.primeCompl`
agrees with extending `I` directly to `S_q`. -/
private theorem localized_extendedIdeal_eq
    {I : Ideal R} (q : Ideal S) [q.IsPrime] :
    Ideal.map (algebraMap S (Localization q.primeCompl)) (Ideal.map (algebraMap R S) I) =
      Ideal.map (algebraMap R (Localization q.primeCompl)) I := by
  -- Rewrite both sides as the image of `I` under the composed structure map `R → S → S_q`.
  rw [Ideal.map_map]
  congr 1

/-- Helper for Lemma 10.126.11: localizing the extended ideal `I S'` at the image of
`q.primeCompl` agrees with extending `I` directly to `S'_q`. -/
private theorem mapped_localized_extendedIdeal_eq
    {I : Ideal R} (f : S →ₐ[R] S') (q : Ideal S) [q.IsPrime] :
    Ideal.map
        (algebraMap S' (Localization (Submonoid.map (f : S →+* S') q.primeCompl)))
        (Ideal.map (algebraMap R S') I) =
      Ideal.map
        (algebraMap R (Localization (Submonoid.map (f : S →+* S') q.primeCompl))) I := by
  -- Again, functoriality of `Ideal.map` reduces the statement to the scalar-tower identity.
  rw [Ideal.map_map]
  congr 1

/-- Helper for Lemma 10.126.11: the quotient map modulo `I` sends the source prime-complement
submonoid exactly to the target prime-complement submonoid. -/
private theorem quotient_map_sourceSub_map_eq_targetSub
    {I : Ideal R} (f : S →ₐ[R] S') (q : Ideal S) [q.IsPrime] :
    Submonoid.map
        (Ideal.quotientMapₐ (Ideal.map (algebraMap R S') I) f
          (extendedIdeal_le_comap_extendedIdeal f)).toMonoidHom
        (Algebra.algebraMapSubmonoid (S ⧸ Ideal.map (algebraMap R S) I) q.primeCompl) =
      Algebra.algebraMapSubmonoid (S' ⧸ Ideal.map (algebraMap R S') I)
        (Submonoid.map (f : S →+* S') q.primeCompl) := by
  -- Compare both submonoids on generators coming from elements of `q.primeCompl`.
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨f z, ⟨z, hz, rfl⟩, ?_⟩
    simp [Ideal.quotient_map_mkₐ]
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R S) I) z, ⟨z, hz, rfl⟩, ?_⟩
    simp [Ideal.quotient_map_mkₐ]

/-- Helper for Lemma 10.126.11: under the canonical `S`-algebra structure induced by `f`, the
image of `q.primeCompl` is exactly the algebra-map submonoid on `S'`. -/
private theorem mapped_prime_compl_eq_algebraMapSubmonoid
    (f : S →ₐ[R] S') (q : Ideal S) [q.IsPrime] :
    letI : Algebra S S' := f.toRingHom.toAlgebra
    Submonoid.map (f : S →+* S') q.primeCompl = Algebra.algebraMapSubmonoid S' q.primeCompl := by
  letI : Algebra S S' := f.toRingHom.toAlgebra
  -- Both submonoids consist of the same algebra-map images of elements of `q.primeCompl`.
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

/-- Helper for Lemma 10.126.11: under the canonical `S`-algebra structure on `S'`, localizing the
extended ideal `I S'` at the owner prime-complement submonoid agrees with extending `I` directly
to the target localization. -/
private theorem owner_localized_extendedIdeal_eq
    {I : Ideal R} (f : S →ₐ[R] S') (q : Ideal S) [q.IsPrime] :
    letI : Algebra S S' := f.toRingHom.toAlgebra
    Ideal.map
        (algebraMap S' (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl)))
        (Ideal.map (algebraMap R S') I) =
      Ideal.map
        (algebraMap R (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))) I := by
  letI : Algebra S S' := f.toRingHom.toAlgebra
  -- Both sides are the image of `I` under the same composite `R → S' → S'_q`.
  rw [Ideal.map_map]
  congr 1

/-- Helper for Lemma 10.126.11: the public localized quotient map carries the class of `s / 1`
to the class of `f(s) / 1`. -/
private theorem localizedQuotientMapModIdealAtPrimeCompl_apply_algebraMap
    {I : Ideal R} (f : S →ₐ[R] S') (q : Ideal S) [q.IsPrime] (s : S) :
    localizedQuotientMapModIdealAtPrimeCompl f q I
      (Ideal.Quotient.mk
        (Ideal.map (algebraMap R (Localization q.primeCompl)) I)
        (algebraMap S (Localization q.primeCompl) s)) =
      Ideal.Quotient.mk
        (Ideal.map
          (algebraMap R (Localization (Submonoid.map (f : S →+* S') q.primeCompl))) I)
        (algebraMap S'
          (Localization (Submonoid.map (f : S →+* S') q.primeCompl))
          (f s)) := by
  letI : Algebra S S' := f.toRingHom.toAlgebra
  let localizedMap :
      Localization q.primeCompl →ₐ[R]
        Localization (Algebra.algebraMapSubmonoid S' q.primeCompl) := by
    let g :
        Localization q.primeCompl →ₐ[Localization q.primeCompl]
          Localization (Algebra.algebraMapSubmonoid S' q.primeCompl) :=
      IsLocalization.mapₐ q.primeCompl
        (Localization q.primeCompl)
        (Localization q.primeCompl)
        (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))
        (Algebra.ofId S S')
    exact
      { __ := g.toRingHom
        commutes' := fun r ↦ by
          simpa [IsScalarTower.algebraMap_eq R S (Localization q.primeCompl),
            IsScalarTower.algebraMap_eq R S
              (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))] using
            g.commutes ((algebraMap R (Localization q.primeCompl)) r) }
  have hlocalizedMap_apply :
      localizedMap (algebraMap S (Localization q.primeCompl) s) =
        algebraMap S' (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl)) (f s) := by
    -- The named localized map still sends `s / 1` to `f(s) / 1`.
    change
      (IsLocalization.mapₐ q.primeCompl
        (Localization q.primeCompl)
        (Localization q.primeCompl)
        (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))
        (Algebra.ofId S S'))
        (algebraMap S (Localization q.primeCompl) s) =
          algebraMap S'
            (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))
            (f s)
  -- The localized owner map commutes with the `S`-algebra structure induced by `f`.
    simpa [show (algebraMap S S') s = f s by rfl,
      IsScalarTower.algebraMap_eq S S'
        (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))]
  -- Re-express the public quotient map using the named localized map before taking the quotient.
  have hleLoc :
      Ideal.map (algebraMap R (Localization q.primeCompl)) I ≤
        Ideal.comap localizedMap.toRingHom
          (Ideal.map (algebraMap R (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))) I) := by
    -- This is the same extended-ideal containment, now for the named localized map.
    have hcomp :
        (localizedMap : Localization q.primeCompl →+* Localization (Algebra.algebraMapSubmonoid S' q.primeCompl)).comp
            (algebraMap R (Localization q.primeCompl)) =
          algebraMap R (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl)) := by
      ext r
      exact localizedMap.commutes r
    have hmapeq :
        Ideal.map localizedMap.toRingHom (Ideal.map (algebraMap R (Localization q.primeCompl)) I) =
          Ideal.map (algebraMap R (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))) I := by
      simpa [hcomp] using
        (Ideal.map_map (I := I)
          (f := algebraMap R (Localization q.primeCompl))
          (g := localizedMap.toRingHom))
    calc
      Ideal.map (algebraMap R (Localization q.primeCompl)) I ≤
          Ideal.comap localizedMap.toRingHom
            (Ideal.map localizedMap.toRingHom (Ideal.map (algebraMap R (Localization q.primeCompl)) I)) :=
        Ideal.le_comap_map
      _ = Ideal.comap localizedMap.toRingHom
            (Ideal.map (algebraMap R (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))) I) := by
          rw [hmapeq]
  change
    Ideal.quotientMapₐ
      (Ideal.map (algebraMap R (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))) I)
      localizedMap
      hleLoc
      (Ideal.Quotient.mk
        (Ideal.map (algebraMap R (Localization q.primeCompl)) I)
        (algebraMap S (Localization q.primeCompl) s)) =
      _
  rw [Ideal.quotient_map_mkₐ]
  simpa using congrArg
    (Ideal.Quotient.mk
      (Ideal.map (algebraMap R (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))) I))
    hlocalizedMap_apply

/-- Helper for Lemma 10.126.11: localizing the global quotient comparison at `q.primeCompl`
identifies it with the localized quotient map used in Lemma `10.126.10`. -/
private theorem localized_quotient_bijective_of_bijective_mod_ideal
    {I : Ideal R} (f : S →ₐ[R] S') (q : Ideal S) [q.IsPrime]
    (hquot :
      Function.Bijective
        (Ideal.quotientMapₐ (Ideal.map (algebraMap R S') I) f
          (extendedIdeal_le_comap_extendedIdeal f))) :
    Function.Bijective (localizedQuotientMapModIdealAtPrimeCompl f q I) := by
  -- Route correction: the quotient isomorphism should first be viewed as an `S`-algebra
  -- equivalence, so the localization step uses the owner prime-complement submonoids directly.
  letI : Algebra S S' := f.toRingHom.toAlgebra
  let IS : Ideal S := Ideal.map (algebraMap R S) I
  let IS' : Ideal S' := Ideal.map (algebraMap R S') I
  let M : Submonoid (S ⧸ IS) := Algebra.algebraMapSubmonoid (S ⧸ IS) q.primeCompl
  let T : Submonoid (S' ⧸ IS') :=
    Algebra.algebraMapSubmonoid (S' ⧸ IS') (Submonoid.map (f : S →+* S') q.primeCompl)
  have hleS : IS ≤ Ideal.comap (Algebra.ofId S S') IS' := by
    -- This is the same containment of extended ideals, now viewed over the base ring `S`.
    simpa [IS, IS', Algebra.ofId_apply] using extendedIdeal_le_comap_extendedIdeal f
  let qmapS : (S ⧸ IS) →ₐ[S] (S' ⧸ IS') :=
    Ideal.quotientMapₐ (R₁ := S) IS' (Algebra.ofId S S') hleS
  have hquotS : Function.Bijective qmapS := by
    -- The `S`-algebra quotient map has the same underlying function as the original hypothesis.
    simpa [qmapS, IS, IS', Algebra.ofId_apply] using hquot
  let eQuot : (S ⧸ IS) ≃ₐ[S] (S' ⧸ IS') := AlgEquiv.ofBijective qmapS hquotS
  have hT : Submonoid.map eQuot.toMonoidHom M = T := by
    -- The quotient map modulo `I` sends the source prime-complement image to the public target
    -- prime-complement image, and `eQuot` has exactly that underlying map.
    simpa [M, T, eQuot, qmapS, IS, IS', Algebra.ofId_apply] using
      quotient_map_sourceSub_map_eq_targetSub (I := I) f q
  let eLocQuot : Localization M ≃ₐ[S] Localization T :=
    IsLocalization.algEquivOfAlgEquiv
      (A := S)
      (S := Localization M)
      (Q := Localization T)
      eQuot
      hT
  let eSrc :
      Localization M ≃+*
        (Localization q.primeCompl ⧸ Ideal.map (algebraMap R (Localization q.primeCompl)) I) :=
    (Localization.algEquiv M
      (Localization q.primeCompl ⧸ Ideal.map (algebraMap S (Localization q.primeCompl)) IS)
        : Localization M ≃ₐ[S ⧸ IS]
            (Localization q.primeCompl ⧸ Ideal.map (algebraMap S (Localization q.primeCompl)) IS)
      ).toRingEquiv.trans (Ideal.quotEquivOfEq (localized_extendedIdeal_eq (I := I) q))
  let eTgt :
      Localization T ≃+*
        (Localization (Submonoid.map (f : S →+* S') q.primeCompl) ⧸
          Ideal.map
            (algebraMap R (Localization (Submonoid.map (f : S →+* S') q.primeCompl))) I) :=
    (Localization.algEquiv T
      (Localization (Submonoid.map (f : S →+* S') q.primeCompl) ⧸
        Ideal.map
          (algebraMap S' (Localization (Submonoid.map (f : S →+* S') q.primeCompl))) IS')
        : Localization T ≃ₐ[S' ⧸ IS']
            (Localization (Submonoid.map (f : S →+* S') q.primeCompl) ⧸
              Ideal.map
                (algebraMap S' (Localization (Submonoid.map (f : S →+* S') q.primeCompl))) IS')
      ).toRingEquiv.trans (Ideal.quotEquivOfEq (mapped_localized_extendedIdeal_eq f q))
  have hSrc_apply (s : S) :
      eSrc (algebraMap (S ⧸ IS) (Localization M) (Ideal.Quotient.mk IS s)) =
        Ideal.Quotient.mk (Ideal.map (algebraMap R (Localization q.primeCompl)) I)
          (algebraMap S (Localization q.primeCompl) s) := by
    -- Unfold the source quotient/localization comparison on the generator represented by `s`.
    change
      Ideal.quotEquivOfEq (localized_extendedIdeal_eq (I := I) q)
          ((Localization.algEquiv M
            (Localization q.primeCompl ⧸
              Ideal.map (algebraMap S (Localization q.primeCompl)) IS))
            (algebraMap (S ⧸ IS) (Localization M) (Ideal.Quotient.mk IS s))) =
        _
    rw [← IsLocalization.mk'_one (M := M) (S := Localization M) (Ideal.Quotient.mk IS s)]
    rw [Localization.algEquiv_mk', IsLocalization.mk'_one]
    simpa [Ideal.Quotient.mk_algebraMap] using
      (Ideal.quotEquivOfEq_mk (localized_extendedIdeal_eq (I := I) q)
        (algebraMap S (Localization q.primeCompl) s))
  have hSrc_symm_apply (s : S) :
      eSrc.symm
          (Ideal.Quotient.mk (Ideal.map (algebraMap R (Localization q.primeCompl)) I)
            (algebraMap S (Localization q.primeCompl) s)) =
        algebraMap (S ⧸ IS) (Localization M) (Ideal.Quotient.mk IS s) := by
    -- The inverse source transport is determined by the forward transport on generators.
    apply eSrc.injective
    rw [RingEquiv.apply_symm_apply, hSrc_apply]
  have hTgt_apply (s : S') :
      eTgt (algebraMap (S' ⧸ IS') (Localization T) (Ideal.Quotient.mk IS' s)) =
        Ideal.Quotient.mk
          (Ideal.map
            (algebraMap R (Localization (Submonoid.map (f : S →+* S') q.primeCompl))) I)
          (algebraMap S' (Localization (Submonoid.map (f : S →+* S') q.primeCompl)) s) := by
    -- Unfold the target quotient/localization comparison on the generator represented by `s`.
    change
      Ideal.quotEquivOfEq (mapped_localized_extendedIdeal_eq f q)
          ((Localization.algEquiv T
            (Localization (Submonoid.map (f : S →+* S') q.primeCompl) ⧸
              Ideal.map
                (algebraMap S' (Localization (Submonoid.map (f : S →+* S') q.primeCompl))) IS'))
            (algebraMap (S' ⧸ IS') (Localization T) (Ideal.Quotient.mk IS' s))) =
        _
    rw [← IsLocalization.mk'_one (M := T) (S := Localization T) (Ideal.Quotient.mk IS' s)]
    rw [Localization.algEquiv_mk', IsLocalization.mk'_one]
    simpa [Ideal.Quotient.mk_algebraMap] using
      (Ideal.quotEquivOfEq_mk (mapped_localized_extendedIdeal_eq f q)
        (algebraMap S' (Localization (Submonoid.map (f : S →+* S') q.primeCompl)) s))
  have hQuot_apply (s : S) :
      eQuot (Ideal.Quotient.mk IS s) = Ideal.Quotient.mk IS' (f s) := by
    -- The quotient equivalence itself is induced by the global quotient map modulo `I`.
    simpa [IS, IS', Algebra.ofId_apply] using eQuot.commutes s
  have hLocQuot_apply (s : S) :
      eLocQuot (algebraMap (S ⧸ IS) (Localization M) (Ideal.Quotient.mk IS s)) =
        algebraMap (S' ⧸ IS') (Localization T) (Ideal.Quotient.mk IS' (f s)) := by
    -- The localization equivalence carries quotient generators according to `eQuot`.
    simpa [eLocQuot, hQuot_apply s] using
      (IsLocalization.algEquivOfAlgEquiv_eq
        (S := Localization M)
        (Q := Localization T)
        (h := eQuot)
        (H := hT)
        (x := Ideal.Quotient.mk IS s))
  let psi :
      Localization q.primeCompl ⧸ Ideal.map (algebraMap R (Localization q.primeCompl)) I →+*
        Localization (Submonoid.map (f : S →+* S') q.primeCompl) ⧸
          Ideal.map
            (algebraMap R (Localization (Submonoid.map (f : S →+* S') q.primeCompl))) I :=
    eTgt.toRingHom.comp (eLocQuot.toRingEquiv.toRingHom.comp eSrc.symm.toRingHom)
  have hpsi_apply (s : S) :
      psi
          (Ideal.Quotient.mk
            (Ideal.map (algebraMap R (Localization q.primeCompl)) I)
            (algebraMap S (Localization q.primeCompl) s)) =
        Ideal.Quotient.mk
          (Ideal.map
            (algebraMap R (Localization (Submonoid.map (f : S →+* S') q.primeCompl))) I)
          (algebraMap S'
            (Localization (Submonoid.map (f : S →+* S') q.primeCompl))
            (f s)) := by
    -- Evaluate the conjugated comparison directly on the quotient class of `s / 1`.
    simp only [psi, RingHom.comp_apply]
    change
      eTgt (eLocQuot (eSrc.symm (Ideal.Quotient.mk
        (Ideal.map (algebraMap R (Localization q.primeCompl)) I)
        (algebraMap S (Localization q.primeCompl) s)))) = _
    rw [hSrc_symm_apply, hLocQuot_apply, hTgt_apply]
  have hconj :
      psi = localizedQuotientMapModIdealAtPrimeCompl f q I := by
    -- Compare both quotient maps on generators of the localization, then extend across the
    -- quotient and the localization by the standard extensionality lemmas.
    apply Ideal.Quotient.ringHom_ext
    apply IsLocalization.ringHom_ext q.primeCompl
    ext s
    change
      psi
          (Ideal.Quotient.mk
            (Ideal.map (algebraMap R (Localization q.primeCompl)) I)
            (algebraMap S (Localization q.primeCompl) s)) =
        localizedQuotientMapModIdealAtPrimeCompl f q I
          (Ideal.Quotient.mk
            (Ideal.map (algebraMap R (Localization q.primeCompl)) I)
            (algebraMap S (Localization q.primeCompl) s))
    rw [hpsi_apply, localizedQuotientMapModIdealAtPrimeCompl_apply_algebraMap]
  have hbijPsi : Function.Bijective psi := by
    -- The conjugated map is bijective because it is a composite of three equivalences.
    have hbijPsi' : Function.Bijective (fun x ↦ eTgt (eLocQuot (eSrc.symm x))) := by
      exact Function.Bijective.comp (RingEquiv.bijective eTgt)
        (Function.Bijective.comp (AlgEquiv.bijective eLocQuot) (RingEquiv.bijective eSrc.symm))
    simpa only [psi, RingHom.comp_apply] using hbijPsi'
  have hbijPhi :
      Function.Bijective (localizedQuotientMapModIdealAtPrimeCompl f q I) := by
    -- Transport bijectivity across the direct comparison with the public localized quotient map.
    simpa [hconj] using hbijPsi
  -- Once the localized quotient map is identified with the conjugate of `eLocQuot`, bijectivity
  -- is immediate because conjugation preserves bijectivity.
  exact hbijPhi

/-- Helper for Lemma 10.126.11: if `g ∉ q`, then every power of `g` lies in `q.primeCompl`. -/
private theorem powers_le_prime_compl_of_not_mem
    (q : Ideal S) [q.IsPrime] (g : S) (hgq : g ∉ q) :
    Submonoid.powers g ≤ q.primeCompl :=
  Submonoid.powers_le.2 hgq

/-- Helper for Lemma 10.126.11: if `g ∉ q`, the prime localization `S_q` carries the canonical
`S_g`-algebra structure coming from the inclusion `powers g ≤ q.primeCompl`. -/
@[implicit_reducible] private noncomputable def prime_compl_away_algebra
    (q : Ideal S) [q.IsPrime] (g : S) (hgq : g ∉ q) :
    Algebra (Localization.Away g) (Localization q.primeCompl) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe
    (Localization.Away g)
    (Localization q.primeCompl)
    (Submonoid.powers g)
    q.primeCompl
    (powers_le_prime_compl_of_not_mem q g hgq)

/-- Helper for Lemma 10.126.11: after applying `f`, every power of `f g` lies in the image of
`q.primeCompl`. -/
private theorem mapped_powers_le_mapped_prime_compl_of_not_mem
    (f : S →ₐ[R] S') (q : Ideal S) [q.IsPrime] (g : S) (hgq : g ∉ q) :
    Submonoid.powers (f g) ≤ Submonoid.map (f : S →+* S') q.primeCompl := by
  rw [← Submonoid.map_powers]
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact ⟨y, powers_le_prime_compl_of_not_mem q g hgq hy, rfl⟩

/-- Helper for Lemma 10.126.11: after mapping `g` to `S'`, the target prime localization carries
the canonical `S'_{f(g)}`-algebra structure coming from the image inclusion. -/
@[implicit_reducible] private noncomputable def mapped_prime_compl_away_algebra
    (f : S →ₐ[R] S') (q : Ideal S) [q.IsPrime] (g : S) (hgq : g ∉ q) :
    Algebra (Localization.Away (f g))
      (Localization (Submonoid.map (f : S →+* S') q.primeCompl)) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe
    (Localization.Away (f g))
    (Localization (Submonoid.map (f : S →+* S') q.primeCompl))
    (Submonoid.powers (f g))
    (Submonoid.map (f : S →+* S') q.primeCompl)
    (mapped_powers_le_mapped_prime_compl_of_not_mem f q g hgq)

/-- Helper for Lemma 10.126.11: for the canonical `S`-algebra structure on `S'`, every power of
`algebraMap S S' g` lies in the prime-complement image. -/
private theorem algebraMap_powers_le_prime_compl_of_not_mem
    [Algebra S S'] (q : Ideal S) [q.IsPrime] (g : S) (hgq : g ∉ q) :
    Submonoid.powers (algebraMap S S' g) ≤ Algebra.algebraMapSubmonoid S' q.primeCompl := by
  rw [← Submonoid.map_powers]
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact ⟨y, powers_le_prime_compl_of_not_mem q g hgq hy, rfl⟩

/-- Helper for Lemma 10.126.11: with the canonical `S`-algebra structure on `S'`, the target
prime localization is naturally an algebra over `S'_{g}`. -/
@[implicit_reducible] private noncomputable def algebraMap_prime_compl_away_algebra
    [Algebra S S'] (q : Ideal S) [q.IsPrime] (g : S) (hgq : g ∉ q) :
    Algebra (Localization.Away (algebraMap S S' g))
      (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl)) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe
    (Localization.Away (algebraMap S S' g))
    (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))
    (Submonoid.powers (algebraMap S S' g))
    (Algebra.algebraMapSubmonoid S' q.primeCompl)
    (algebraMap_powers_le_prime_compl_of_not_mem q g hgq)

/-- Helper for Lemma 10.126.11: once the away map `S_g → S'_g` is bijective and `g ∉ q`, the
induced map is already bijective at every prime in the basic open `D(g)`. -/
private theorem prime_localization_bijective_of_away_linear_bijective
    [Algebra S S'] (q : Ideal S) [q.IsPrime] (g : S) (hgq : g ∉ q)
    (hawayLinear :
      Function.Bijective (LocalizedModule.map (Submonoid.powers g) (Algebra.linearMap S S'))) :
    Function.Bijective (LocalizedModule.map q.primeCompl (Algebra.linearMap S S')) := by
  let p : PrimeSpectrum S := ⟨q, inferInstance⟩
  have hp :
      Function.Bijective (LocalizedModule.map q.primeCompl (Algebra.linearMap S S')) := by
    have hbasic :
        (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) ⊆
          { p : PrimeSpectrum S |
            Function.Bijective
              (LocalizedModule.map p.asIdeal.primeCompl (Algebra.linearMap S S')) } :=
      basicOpen_subset_moduleMapIsomorphismLocus_of_bijective_away
        (R := S) (M := S) (N := S') (φ := Algebra.linearMap S S') hawayLinear
    have hp_mem : p ∈ PrimeSpectrum.basicOpen g := by
      exact (PrimeSpectrum.mem_basicOpen g p).2 hgq
    simpa [p] using hbasic hp_mem
  exact hp

/-- Helper for Lemma 10.126.11: the away algebra map `S_g → S'_g` is the owner map whose
bijectivity is equivalent to bijectivity of the localized module map on `S`-modules. -/
private theorem away_localized_linear_bijective_of_away_alg_bijective
    [Algebra S S'] (g : S)
    (haway : Function.Bijective (Localization.awayMapₐ (Algebra.ofId S S') g)) :
    Function.Bijective (LocalizedModule.map (Submonoid.powers g) (Algebra.linearMap S S')) := by
  let awayMapS : Localization.Away g →ₐ[S] Localization.Away (algebraMap S S' g) :=
    Localization.awayMapₐ (Algebra.ofId S S') g
  letI : Algebra (Localization.Away g) (Localization.Away (algebraMap S S' g)) :=
    awayMapS.toAlgebra
  letI : IsScalarTower S (Localization.Away g) (Localization.Away (algebraMap S S' g)) :=
    IsScalarTower.of_algebraMap_eq fun s ↦ by
      exact (awayMapS.commutes s).symm
  -- Rewrite the public localized module map into the owner `IsLocalizedModule.map`.
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective
    (Algebra.linearMap S (Localization.Away g))
    ((IsScalarTower.toAlgHom S S' (Localization.Away (algebraMap S S' g))).toLinearMap)]
  -- Then identify that owner map with the canonical away algebra map.
  rw [IsLocalization.map_linearMap_eq_toLinearMap_mapₐ
    (M := Submonoid.powers g)
    (R := S)
    (A := S')
    (Rₚ := Localization.Away g)
    (Aₚ := Localization.Away (algebraMap S S' g))]
  simpa [awayMapS, Localization.awayMapₐ] using haway

/-- Helper for Lemma 10.126.11: once the away map `S_g → S'_g` is bijective and `g ∉ q`, the
induced map on the prime localizations at `q` is injective. -/
private theorem injective_prime_localization_of_away_bijective
    (f : S →ₐ[R] S') (q : Ideal S) [q.IsPrime] (g : S) (hgq : g ∉ q)
    (haway : Function.Bijective (Localization.awayMapₐ f g)) :
    letI : Algebra S S' := f.toRingHom.toAlgebra
    Function.Injective (LocalizedModule.map q.primeCompl (Algebra.linearMap S S')) := by
  letI : Algebra S S' := f.toRingHom.toAlgebra
  have hawayS :
      Function.Bijective (Localization.awayMapₐ (Algebra.ofId S S') g) := by
    -- Under the canonical `S`-algebra structure induced by `f`, both away maps are the same map.
    simpa [Algebra.ofId_apply] using haway
  have hawayLinear :
      Function.Bijective (LocalizedModule.map (Submonoid.powers g) (Algebra.linearMap S S')) :=
    away_localized_linear_bijective_of_away_alg_bijective
      (S := S) (S' := S') (g := g) hawayS
  -- Feed the away-localized bijectivity into the already-stable basic-open to prime-local step.
  exact (prime_localization_bijective_of_away_linear_bijective q g hgq hawayLinear).1

/-- Helper for Lemma 10.126.11: for every prime ideal `q ⊆ S`, the induced map on localizations
at `q` is injective. This is the prime-local core of the source proof. -/
private theorem prime_local_injective_of_bijective_mod_ideal
    {I : Ideal R} (hI : I.IsLocallyNilpotent) (f : S →ₐ[R] S')
    [Algebra.FiniteType R S] [Algebra.FinitePresentation R S'] [Module.Flat R S']
    (hquot :
      Function.Bijective
        (Ideal.quotientMapₐ (Ideal.map (algebraMap R S') I) f
          (extendedIdeal_le_comap_extendedIdeal f)))
    (q : Ideal S) [q.IsPrime] :
    letI : Algebra S S' := f.toRingHom.toAlgebra
    Function.Injective (LocalizedModule.map q.primeCompl (Algebra.linearMap S S')) := by
  letI : Algebra S S' := f.toRingHom.toAlgebra
  have hquotSurj :
      Function.Surjective
        ((Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R S') I)).comp f) := by
    intro z
    obtain ⟨zbar, hzbar⟩ := hquot.2 z
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (Ideal.map (algebraMap R S) I) zbar
    exact ⟨s, by simpa using hzbar⟩
  -- First recover global surjectivity of `f` from the quotient-surjectivity hypothesis.
  have hsurj : Function.Surjective f :=
    surjective_of_surjective_quotient_of_finiteType_of_locallyNilpotent hI f hquotSurj
  have hIS :
      (Ideal.map (algebraMap R S) I).IsLocallyNilpotent :=
    Ideal.map_isLocallyNilpotent (algebraMap R S) hI
  have hIq : Ideal.map (algebraMap R S) I ≤ q := by
    -- Every prime ideal contains a locally nilpotent ideal.
    exact hIS.trans (nilradical_le_prime q)
  have hquotLoc :
      Function.Bijective (localizedQuotientMapModIdealAtPrimeCompl f q I) :=
    localized_quotient_bijective_of_bijective_mod_ideal f q hquot
  -- Lemma `10.126.10` produces a neighborhood on which the map is already bijective.
  obtain ⟨g, hgq, haway⟩ :=
    exists_notMem_and_awayMap_bijective_of_localizedQuotient_bijective
      (f := f) (I := I) (q := q) hIq hsurj hquotLoc
  -- A further localization from `S_g` to `S_q` preserves injectivity.
  simpa using injective_prime_localization_of_away_bijective f q g hgq haway

-- Proof sketch: Lemma `10.126.9` makes `f` surjective from the surjectivity of the quotient map.
-- By Lemma `10.32.3`, the extended ideals `I S` and `I S'` are locally nilpotent, so every prime
-- of `S` contains `I S`. Localizing at any prime `q ⊆ S`, the induced quotient map remains
-- bijective, and Lemma `10.126.10` yields a neighborhood on which `f` is bijective. Hence every
-- localization `S_q → S'_q` is an isomorphism, and Lemma `10.23.1` then gives injectivity of `f`.
/-- Lemma 10.126.11: let `I ⊆ R` be a locally nilpotent ideal and `f : S →ₐ[R] S'` an
`R`-algebra map. If the induced map `S / I S → S' / I S'` is bijective, `S` is of finite type
over `R`, `S'` is of finite presentation over `R`, and `S'` is flat over `R`, then `f` is
bijective. -/
@[stacks 07RE]
theorem bijective_of_bijective_mod_ideal_of_locallyNilpotent_of_finiteType_of_finitePresentation_of_flat
    {I : Ideal R} (hI : I.IsLocallyNilpotent) (f : S →ₐ[R] S')
    [Algebra.FiniteType R S] [Algebra.FinitePresentation R S'] [Module.Flat R S']
    (hquot :
      Function.Bijective
        (Ideal.quotientMapₐ (Ideal.map (algebraMap R S') I) f
          (extendedIdeal_le_comap_extendedIdeal f))) :
    Function.Bijective f := by
  letI : Algebra S S' := f.toRingHom.toAlgebra
  have hquotSurj :
      Function.Surjective
        ((Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R S') I)).comp f) := by
    intro z
    obtain ⟨zbar, hzbar⟩ := hquot.2 z
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (Ideal.map (algebraMap R S) I) zbar
    exact ⟨s, by simpa using hzbar⟩
  -- The source proof starts by recovering global surjectivity from the quotient comparison.
  have hsurj : Function.Surjective f :=
    surjective_of_surjective_quotient_of_finiteType_of_locallyNilpotent hI f hquotSurj
  have htfae :
      List.TFAE [
        Function.Injective (Algebra.linearMap S S'),
        ∀ (q : Ideal S) [q.IsPrime],
          Function.Injective (LocalizedModule.map q.primeCompl (Algebra.linearMap S S')),
        ∀ (q : Ideal S) [q.IsMaximal],
          Function.Injective (LocalizedModule.map q.primeCompl (Algebra.linearMap S S'))
      ] :=
    injective_localization_tfae (Algebra.linearMap S S')
  have hprime :
      ∀ (q : Ideal S) [q.IsPrime],
        Function.Injective (LocalizedModule.map q.primeCompl (Algebra.linearMap S S')) := by
    intro q hq
    letI : q.IsPrime := hq
    simpa using prime_local_injective_of_bijective_mod_ideal hI f hquot q
  have hlininj : Function.Injective (Algebra.linearMap S S') :=
    (htfae.out 0 1).mpr hprime
  -- Injectivity of the `S`-linear map is exactly injectivity of the underlying algebra map.
  have hinj : Function.Injective f := by
    simpa using hlininj
  exact ⟨hinj, hsurj⟩

end
