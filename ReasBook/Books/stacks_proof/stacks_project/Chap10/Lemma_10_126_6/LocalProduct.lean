import Mathlib

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FinitePresentation R S]
variable (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]

/-- Helper for Lemma 10.126.6: a bijective local ring map `R_𝔭 → S_𝔮` makes `S_𝔮`
quasi-finite over `R`. -/
theorem quasiFiniteAt_of_bijective_localRingHom
    (hq : q.LiesOver p)
    (hlocal :
      Function.Bijective (Localization.localRingHom p q (algebraMap R S) hq.over)) :
    Algebra.QuasiFiniteAt R q := by
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Localization.localRingHom p q (algebraMap R S) hq.over).toAlgebra
  have hlocal' :
      Function.Bijective
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
    simpa [RingHom.algebraMap_toAlgebra] using hlocal
  let e : Localization.AtPrime p ≃ₐ[Localization.AtPrime p] Localization.AtPrime q :=
    AlgEquiv.ofBijective (Algebra.ofId _ _) hlocal'
  let eR : Localization.AtPrime q ≃ₐ[R] Localization.AtPrime p := e.symm.restrictScalars R
  -- The target local ring is already a localization of `R`, hence quasi-finite over `R`.
  exact (Algebra.QuasiFinite.iff_of_algEquiv (R := R) eR).mpr inferInstance

/-- Helper for Lemma 10.126.6: any `A`-algebra which is already `A` isomorphic admits the required
product decomposition with a trivial complementary factor. -/
theorem exists_trivial_product_factor_of_algEquiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (e : B ≃ₐ[A] A) :
    ∃ (C : Type w) (_ : CommRing C) (_ : Algebra A C),
      Nonempty (B ≃ₐ[A] (A × C)) := by
  let C : Type w := ULift.{w, 0} PUnit
  let eProd : A ≃ₐ[A] (A × C) :=
    AlgEquiv.ofBijective (Algebra.ofId A (A × C)) <| by
      constructor
      · intro x y hxy
        exact congrArg Prod.fst hxy
      · intro x
        refine ⟨x.1, ?_⟩
        apply Prod.ext
        · rfl
        · exact Subsingleton.elim _ _
  refine ⟨C, inferInstance, inferInstance, ?_⟩
  exact ⟨e.trans eProd⟩

/-- Helper for Lemma 10.126.6: if the away map `R_f → S_f` is bijective, then the desired product
decomposition follows immediately by taking a trivial complementary factor. -/
theorem exists_product_factor_of_bijective_awayMap
    (f : R) (hbij : Function.Bijective (Localization.awayMap (algebraMap R S) f)) :
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
      (Localization.awayMap (algebraMap R S) f).toAlgebra
    ∃ (C : Type w) (_ : CommRing C) (_ : Algebra (Localization.Away f) C),
      Nonempty
        (Localization.Away (algebraMap R S f) ≃ₐ[Localization.Away f]
          (Localization.Away f × C)) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  have hbij' :
      Function.Bijective
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))) := by
    simpa [RingHom.algebraMap_toAlgebra] using hbij
  let e : Localization.Away (algebraMap R S f) ≃ₐ[Localization.Away f] Localization.Away f :=
    (AlgEquiv.ofBijective (Algebra.ofId _ _) hbij').symm
  -- Once the localized algebra is actually `R_f`, the requested product is `R_f × 0`.
  exact exists_trivial_product_factor_of_algEquiv (A := Localization.Away f) e

/-- Helper for Lemma 10.126.6: if a basic-open map `S'_r → S_r` is bijective and `r` avoids the
target prime `q`, then the induced map on the prime localizations `S'_{q'} → S_q` is bijective. -/
theorem subalgebra_localRingHom_bijective_of_awayMap_bijective
    (S' : Subalgebra R S) (r : S') (hrq : r.1 ∉ q)
    (hr : Function.Bijective (Localization.awayMap S'.val.toRingHom r)) :
    let q' : Ideal S' := Ideal.comap S'.val.toRingHom q
    Function.Bijective (Localization.localRingHom q' q S'.val.toRingHom rfl) := by
  let q' : Ideal S' := Ideal.comap S'.val.toRingHom q
  letI : q'.IsPrime := Ideal.comap_isPrime S'.val.toRingHom q
  letI : q.LiesOver q' := by
    refine ⟨rfl⟩
  have hsat : S'.saturation (q.primeCompl ⊓ S'.toSubmonoid) (by simp) = ⊤ := by
    -- Proof comment: surjectivity of `S'_r → S_r` says every element of `S` becomes an element of
    -- `S'` after multiplying by a power of `r`, which is exactly the saturation criterion.
    rw [← top_le_iff]
    intro x hx
    obtain ⟨b, n, hb⟩ := (Localization.awayMap_surjective_iff).mp hr.2 x
    refine ⟨r.1 ^ n, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · exact q.primeCompl.pow_mem (show r.1 ∈ q.primeCompl from hrq) n
      · exact (show r.1 ^ n ∈ S' from S'.pow_mem r.2 n)
    · simpa [smul_eq_mul] using (show r.1 ^ n * x ∈ S' from hb.symm ▸ b.2)
  -- Proof comment: the saturation-top criterion is the canonical bridge from a basic-open
  -- isomorphism to a bijection on the stalk at `q`.
  simpa [q'] using
    (Localization.localRingHom_bijective_of_saturated_inf_eq_top
      (S := S) (P := q) (s := S') (p := q') hsat)

/-- Helper for Lemma 10.126.6: the original local isomorphism `R_p → S_q` factors through the
finite subalgebra neighborhood `S'`, so `R_p → S'_{q'}` is already bijective. -/
theorem finite_subalgebra_localRingHom_bijective_of_quasiFinite_neighborhood
    (hq : q.LiesOver p)
    (S' : Subalgebra R S) (r : S') (hrq : r.1 ∉ q)
    (hr : Function.Bijective (Localization.awayMap S'.val.toRingHom r))
    (hlocal :
      Function.Bijective (Localization.localRingHom p q (algebraMap R S) hq.over)) :
    let q' : Ideal S' := Ideal.comap S'.val.toRingHom q
    Function.Bijective
      (Localization.localRingHom p q' (algebraMap R S')
        (by simpa [q', Ideal.comap_comap] using hq.over)) := by
  let q' : Ideal S' := Ideal.comap S'.val.toRingHom q
  letI : q'.IsPrime := Ideal.comap_isPrime S'.val.toRingHom q
  have hq' : p = Ideal.comap (algebraMap R S') q' := by
    simpa [q', Ideal.comap_comap] using hq.over
  have hsub :
      Function.Bijective (Localization.localRingHom q' q S'.val.toRingHom rfl) :=
    subalgebra_localRingHom_bijective_of_awayMap_bijective
      (S' := S') (q := q) r hrq hr
  have hcomp :
      Localization.localRingHom p q (algebraMap R S) hq.over =
        (Localization.localRingHom q' q S'.val.toRingHom rfl).comp
          (Localization.localRingHom p q' (algebraMap R S') hq') := by
    -- Proof comment: localizing along `R → S' → S` is governed by the canonical
    -- `Localization.localRingHom_comp` theorem.
    simpa [q', hq', RingHom.comp_assoc] using
      (Localization.localRingHom_comp
        (I := p)
        (J := q')
        (K := q)
        (f := algebraMap R S')
        (hIJ := hq')
        (g := S'.val.toRingHom)
        (hJK := rfl))
  -- Proof comment: once the second localization step is bijective, bijectivity of the composite
  -- is equivalent to bijectivity of the first step.
  rw [hcomp] at hlocal
  exact (Function.Bijective.of_comp_iff' hsub _).mp hlocal

/-- Helper for Lemma 10.126.6: once a localized retraction has idempotent kernel, the algebra
splits as the base factor times the complementary quotient. -/
theorem away_product_decomposition_of_idempotent_kernel_retraction
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (σ : B →ₐ[A] A)
    (hσ : Function.LeftInverse σ (algebraMap A B))
    {e : B} (he : IsIdempotentElem e)
    (hker : RingHom.ker σ.toRingHom = Ideal.span ({e} : Set B)) :
    ∃ (C : Type v) (_ : CommRing C) (_ : Algebra A C),
      Nonempty (B ≃ₐ[A] (A × C)) := by
  let C : Type v := B ⧸ Ideal.span ({1 - e} : Set B)
  let quotientEquiv : (B ⧸ Ideal.span ({e} : Set B)) ≃ₐ[A] A :=
    -- Proof comment: rewrite the quotient by the displayed kernel and then apply the first
    -- isomorphism theorem for the retraction `σ`.
    (Ideal.quotientEquivAlgOfEq (R₁ := A) hker.symm).trans <|
      Ideal.quotientKerAlgEquivOfRightInverse (f := σ) (g := algebraMap A B) hσ
  let splitEquiv :
      B ≃ₐ[A] ((B ⧸ Ideal.span ({e} : Set B)) × C) :=
    -- Proof comment: the complementary idempotents `e` and `1 - e` give the standard product
    -- decomposition of `B`.
    AlgEquiv.prodQuotientOfIsIdempotentElem A he he.one_sub (by simp) (by
      rw [mul_sub, mul_one, he.eq, sub_self])
  let finalEquiv : B ≃ₐ[A] (A × C) :=
    splitEquiv.trans <|
      AlgEquiv.prodCongr quotientEquiv (AlgEquiv.refl : C ≃ₐ[A] C)
  refine ⟨C, inferInstance, inferInstance, ⟨finalEquiv⟩⟩

/-- Helper for Lemma 10.126.6: a pure finitely generated ideal of a commutative ring is generated
by an idempotent element. This is the exact algebraic closing step used after the second shrink. -/
theorem exists_idempotent_generator_of_pure_finitely_generated_ideal
    {A : Type*} [CommRing A] (I : Ideal A)
    (hPure : I.Pure) (hfg : I.FG) :
    ∃ e : A, IsIdempotentElem e ∧ I = Ideal.span ({e} : Set A) := by
  letI : I.Pure := hPure
  -- Proof comment: purity gives ideal idempotence, and finite generation upgrades ideal
  -- idempotence to generation by one idempotent element.
  have hidem : IsIdempotentElem I := Ideal.isIdempotentElem_of_pure I
  exact (Ideal.isIdempotentElem_iff_of_fg I hfg).mp hidem

/-- Helper for Lemma 10.126.6: once the kernel of a retraction is known to be pure and finitely
generated, it is generated by an idempotent element of the source ring. -/
theorem exists_idempotent_generator_of_pure_finitely_generated_kernel
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (σ : B →ₐ[A] A)
    (hkerPure : (RingHom.ker σ.toRingHom).Pure)
    (hkerFg : (RingHom.ker σ.toRingHom).FG) :
    ∃ e : B, IsIdempotentElem e ∧
      RingHom.ker σ.toRingHom = Ideal.span ({e} : Set B) := by
  -- Proof comment: specialize the pure-plus-finitely-generated ideal criterion to the kernel ideal
  -- of the retraction produced after the second shrink.
  simpa using
    exists_idempotent_generator_of_pure_finitely_generated_ideal
      (I := RingHom.ker σ.toRingHom) hkerPure hkerFg

/-- Helper for Lemma 10.126.6: a retraction with pure finitely generated kernel gives the product
decomposition in the natural universe of the source algebra. -/
theorem away_product_decomposition_of_pure_finitely_generated_kernel_retraction
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (σ : B →ₐ[A] A)
    (hσ : Function.LeftInverse σ (algebraMap A B))
    (hkerPure : (RingHom.ker σ.toRingHom).Pure)
    (hkerFg : (RingHom.ker σ.toRingHom).FG) :
    ∃ (C : Type v) (_ : CommRing C) (_ : Algebra A C),
      Nonempty (B ≃ₐ[A] (A × C)) := by
  obtain ⟨e, he, hker⟩ :=
    exists_idempotent_generator_of_pure_finitely_generated_kernel σ hkerPure hkerFg
  -- Proof comment: purity plus finite generation supplies an idempotent generator for the kernel;
  -- the standard idempotent-kernel retraction lemma then produces the product factor.
  exact away_product_decomposition_of_idempotent_kernel_retraction σ hσ he hker

/-- Helper for Lemma 10.126.6: a pure finitely generated retraction kernel gives a product
decomposition with the complementary factor in any requested universe. -/
theorem awayProductDecomposition_of_pureKernel_ulift
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (σ : B →ₐ[A] A)
    (hσ : Function.LeftInverse σ (algebraMap A B))
    (hkerPure : (RingHom.ker σ.toRingHom).Pure)
    (hkerFg : (RingHom.ker σ.toRingHom).FG) :
    ∃ (C : Type (max v w)) (_ : CommRing C) (_ : Algebra A C),
      Nonempty (B ≃ₐ[A] (A × C)) := by
  obtain ⟨C₀, hC₀, hAlgC₀, ⟨e⟩⟩ :=
    away_product_decomposition_of_pure_finitely_generated_kernel_retraction σ hσ hkerPure hkerFg
  let C : Type (max v w) := ULift.{max v w, v} C₀
  letI : CommRing C := inferInstance
  letI : Algebra A C := inferInstance
  let liftEquiv : C₀ ≃ₐ[A] C := (ULift.algEquiv (R := A) (A := C₀)).symm
  let finalEquiv : B ≃ₐ[A] (A × C) :=
    e.trans (AlgEquiv.prodCongr (AlgEquiv.refl : A ≃ₐ[A] A) liftEquiv)
  -- Proof comment: the idempotent splitter naturally returns a complement in the source
  -- algebra universe; transporting only that second factor by `ULift` gives a harmless larger
  -- universe without changing the algebra on the first factor.
  exact ⟨C, inferInstance, inferInstance, ⟨finalEquiv⟩⟩

/-- Helper for Lemma 10.126.6: localizing an algebra retraction along a submonoid of the base
preserves the left-inverse identity. This isolates the transport-free part of the semilocal
retraction step before comparing with the canonical map `S_p → S_q`. -/
theorem localized_leftInverse_of_leftInverse
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (M : Submonoid R)
    (f : A →ₐ[R] B) (g : B →ₐ[R] A)
    (hgf : Function.LeftInverse g f) :
    Function.LeftInverse
      (IsLocalization.mapₐ M (Localization M)
        (Localization (Algebra.algebraMapSubmonoid B M))
        (Localization (Algebra.algebraMapSubmonoid A M)) g)
      (IsLocalization.mapₐ M (Localization M)
        (Localization (Algebra.algebraMapSubmonoid A M))
        (Localization (Algebra.algebraMapSubmonoid B M)) f) := by
  intro x
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (Algebra.algebraMapSubmonoid A M) x
  -- Proof comment: once the localized source element is written as one fraction `a / s`, both
  -- localized maps are computed by `map_mk'`, and the numerator and denominator collapse by the
  -- original left-inverse identity `g ∘ f = id`.
  simp [IsLocalization.mapₐ, IsLocalization.map_mk', hgf a, hgf (s : A)]

/-- Helper for Lemma 10.126.6: conjugating a retraction by algebra equivalences preserves the
left-inverse identity. This packages the transport step used to move the semilocal retraction
from the final away chart back to the source objects `R_p` and `S_p`. -/
theorem leftInverse_of_algEquiv_conj
    {A : Type*} {B : Type*} {C : Type*} {D : Type*}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (eA : A ≃ₐ[R] C) (eB : B ≃ₐ[R] D)
    (ι : A →ₐ[R] B) (σ : B →ₐ[R] A)
    (hσ : Function.LeftInverse σ ι) :
    Function.LeftInverse
      (((eA.toAlgHom).comp σ).comp eB.symm.toAlgHom)
      (((eB.toAlgHom).comp ι).comp eA.symm.toAlgHom) := by
  intro x
  -- Proof comment: after expanding the conjugated maps, the middle terms cancel by the inverse
  -- identities for `eA`, `eB`, and the original left-inverse formula for `σ`.
  simpa [AlgHom.comp_apply] using congrArg eA (hσ (eA.symm x))

/-- Helper for Lemma 10.126.6: if `M ≤ N`, then localizing first at `M` and then at the image of
`N` agrees with localizing the source ring directly at `N`. This is the semilocal transport step
used to return from the final away chart to the source object `S_p`. -/
noncomputable def iterated_localization_algEquiv_of_submonoid_le
    {A : Type*} [CommRing A] (M N : Submonoid A) (hMN : M ≤ N) :
    Localization (Algebra.algebraMapSubmonoid (Localization M) N) ≃ₐ[A] Localization N := by
  letI : Algebra (Localization M) (Localization N) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe
      (S := Localization M)
      (T := Localization N)
      M
      N
      hMN
  letI : IsScalarTower A (Localization M) (Localization N) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      (S := Localization M)
      (T := Localization N)
      M
      N
      hMN
  letI : IsLocalization (Algebra.algebraMapSubmonoid (Localization M) N) (Localization N) := by
    -- Proof comment: once every denominator from `M` already lies in `N`, the direct localization
    -- at `N` is also a localization of `Localization M` at the transported copy of `N`.
    simpa [Algebra.algebraMapSubmonoid] using
      (IsLocalization.isLocalization_of_submonoid_le
        (S := Localization M)
        (T := Localization N)
        (M := M)
        (N := N)
        hMN :
          IsLocalization (N.map (algebraMap A (Localization M))) (Localization N))
  let e :
      Localization (Algebra.algebraMapSubmonoid (Localization M) N) ≃ₐ[Localization M]
        Localization N :=
    Localization.algEquiv (Algebra.algebraMapSubmonoid (Localization M) N) (Localization N)
  -- Proof comment: the canonical localization equivalence is first over `Localization M`; then we
  -- restrict scalars back to the original ring `A`.
  exact e.restrictScalars A

/-- Helper for Lemma 10.126.6: a finite family of elements of `R_𝔭` admits one common
denominator away from `p`. -/
theorem exists_notMem_and_common_denominator_atPrime
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → Localization.AtPrime p) :
    ∃ (f : R) (_ : f ∉ p) (a : ι → R), ∀ i,
      algebraMap R (Localization.AtPrime p) f * x i =
        algebraMap R (Localization.AtPrime p) (a i) := by
  choose num den hden using fun i ↦
    IsLocalization.exists_mk'_eq p.primeCompl (x i)
  let fCompl : p.primeCompl := ⟨∏ i, (den i : R), by
    -- Proof comment: the product of finitely many denominators still avoids the prime `p`.
    simpa using p.primeCompl.prod_mem fun i _ ↦ (den i).2⟩
  let a : ι → R := fun i ↦ num i * ∏ j ∈ ({i}ᶜ : Finset ι), (den j : R)
  refine ⟨(fCompl : R), fCompl.2, a, ?_⟩
  intro i
  -- Proof comment: rewrite `x i` with its chosen denominator and absorb all other denominators
  -- into a single common numerator.
  calc
    algebraMap R (Localization.AtPrime p) (fCompl : R) * x i
        = algebraMap R (Localization.AtPrime p) (fCompl : R) *
            IsLocalization.mk' (Localization.AtPrime p) (num i) (den i) := by
              rw [hden i]
    _ = IsLocalization.mk' (Localization.AtPrime p) ((fCompl : R) * num i)
          ((1 : p.primeCompl) * den i) := by
            rw [← IsLocalization.mk'_one (M := p.primeCompl) (S := Localization.AtPrime p)
              (x := (fCompl : R))]
            exact
              (IsLocalization.mk'_mul
                (M := p.primeCompl)
                (S := Localization.AtPrime p)
                (x₁ := (fCompl : R))
                (x₂ := num i)
                (y₁ := (1 : p.primeCompl))
                (y₂ := den i)).symm
    _ = IsLocalization.mk' (Localization.AtPrime p) ((fCompl : R) * num i) (den i) := by
          simp
    _ = algebraMap R (Localization.AtPrime p) (a i) := by
          rw [IsLocalization.mk'_eq_iff_eq_mul, ← map_mul]
          congr 1
          dsimp [a]
          rw [show (fCompl : R) = ∏ j, (den j : R) by rfl]
          rw [Fintype.prod_eq_prod_compl_mul i fun j ↦ (den j : R)]
          ring

end
