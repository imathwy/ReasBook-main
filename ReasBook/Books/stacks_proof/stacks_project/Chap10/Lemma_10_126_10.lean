import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import stacks_proof.stacks_project.Chap10.Lemma_10_96_1

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling:
* primary domain: localization of `R`-algebra maps at a prime complement and passage to quotients
  by extended ideals;
* sampled owner declarations:
  `IsLocalization.mapₐ`,
  `Ideal.quotientMapₐ`,
  `Ideal.map_le_iff_le_comap`,
  `Localization.awayMapₐ`;
* best owner abstraction:
  the canonical localized quotient comparison algebra map built from `IsLocalization.mapₐ`
  and `Ideal.quotientMapₐ`;
* layer:
  the main existence statement is `source-facing`, while the localized quotient map is a
  `bridge/view` built from the owner localization and quotient constructions;
* primitive data:
  `f`, `I`, `q`, and the finite type / finite presentation / flatness hypotheses;
* derived API:
  the induced quotient algebra map on localizations modulo `I`.
-/

section

universe u v w

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {S' : Type w} [CommRing S'] [Algebra R S']

variable (f : S →ₐ[R] S') (I : Ideal R) (q : Ideal S) [q.IsPrime]

local notation "Sq" => Localization q.primeCompl
local notation "Sqf" => Localization (Submonoid.map (f : S →+* S') q.primeCompl)

private theorem ideal_map_le_comap_map_of_algHom
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (I : Ideal R) :
    Ideal.map (algebraMap R A) I ≤ Ideal.comap f (Ideal.map (algebraMap R B) I) :=
  (Ideal.map_le_iff_le_comap).mp <| by
    calc
      Ideal.map (f : A →+* B) (Ideal.map (algebraMap R A) I) =
          Ideal.map ((f : A →+* B).comp (algebraMap R A)) I := by
            rw [Ideal.map_map]
      _ = Ideal.map (algebraMap R B) I := by
            congr 1
            ext r
            exact f.commutes r
      _ ≤ Ideal.map (algebraMap R B) I := le_rfl

/-- Helper for Chap10 Lemma 10 126 10: the owner localized map commutes with the original
`R`-algebra structures. -/
private theorem localizedMapAtPrimeCompl_commutes (r : R) :
    letI : Algebra S S' := f.toRingHom.toAlgebra
    (IsLocalization.mapₐ q.primeCompl Sq Sq
        (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))
        (Algebra.ofId S S'))
        ((algebraMap R Sq) r) =
      algebraMap R (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl)) r := by
  letI : Algebra S S' := f.toRingHom.toAlgebra
  -- The localized `S`-algebra map sends the image of `r` through `S_q` to the same scalar in
  -- the target localization.
  simpa [IsScalarTower.algebraMap_eq R S Sq,
    IsScalarTower.algebraMap_eq R S
      (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))] using
    (IsLocalization.mapₐ q.primeCompl Sq Sq
      (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))
      (Algebra.ofId S S')).commutes ((algebraMap R Sq) r)

/-- Helper for Chap10 Lemma 10 126 10: the canonical `R`-algebra map from `S_q` to the target
localization induced by `f`. -/
private noncomputable abbrev localizedMapAtPrimeCompl :
    Sq →ₐ[R] Sqf := by
  letI : Algebra S S' := f.toRingHom.toAlgebra
  -- Route correction: keep the owner localization spelling while building the map, then let the
  -- public target notation reduce to the same localization under the canonical `S`-algebra.
  exact
    { __ :=
        (IsLocalization.mapₐ q.primeCompl Sq Sq
          (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))
          (Algebra.ofId S S')).toRingHom
      commutes' := localizedMapAtPrimeCompl_commutes (f := f) (q := q) }

/-- The quotient map modulo `I` induced by the localized map at `q.primeCompl`. -/
noncomputable abbrev localizedQuotientMapModIdealAtPrimeCompl (I : Ideal R) :
    Sq ⧸ Ideal.map (algebraMap R Sq) I →ₐ[R]
      Sqf ⧸ Ideal.map (algebraMap R Sqf) I :=
  Ideal.quotientMapₐ
    (Ideal.map (algebraMap R Sqf) I)
    (localizedMapAtPrimeCompl f q)
    (ideal_map_le_comap_map_of_algHom (localizedMapAtPrimeCompl f q) I)

/-- Helper for Chap10 Lemma 10 126 10: the localized quotient map is computed on quotient
representatives by applying the localized algebra map first. -/
private theorem localizedQuotientMapModIdealAtPrimeCompl_apply_mk (x : Sq) :
    localizedQuotientMapModIdealAtPrimeCompl f q I
        (Ideal.Quotient.mk (Ideal.map (algebraMap R Sq) I) x) =
      Ideal.Quotient.mk (Ideal.map (algebraMap R Sqf) I)
        (localizedMapAtPrimeCompl f q x) := by
  -- This is the stable representative-level computation for the quotient map modulo `I`.
  exact Ideal.quotient_map_mkₐ
    (Ideal.map (algebraMap R Sqf) I)
    (localizedMapAtPrimeCompl f q)
    (ideal_map_le_comap_map_of_algHom (localizedMapAtPrimeCompl f q) I)

/-- Helper for Chap10 Lemma 10 126 10: the quotient map on submodule quotients induced by the
localized algebra map is injective when the public ideal-quotient map is bijective. -/
private theorem localizedMapAtPrimeCompl_quotientMapByIdeal_injective_of_bijective_quotient
    (hquot : Function.Bijective (localizedQuotientMapModIdealAtPrimeCompl f q I)) :
    Function.Injective (((localizedMapAtPrimeCompl f q).toLinearMap).quotientMapByIdeal I) := by
  -- Route correction: compare quotient maps only after transporting both sides to ideal
  -- quotients, and then use the representative computation above.
  let ISq : Ideal Sq := Ideal.map (algebraMap R Sq) I
  let ISqf : Ideal Sqf := Ideal.map (algebraMap R Sqf) I
  let Psrc : Submodule R Sq := I • (⊤ : Submodule R Sq)
  let PsrcI : Submodule R Sq := ISq.restrictScalars R
  let Ptgt : Submodule R Sqf := I • (⊤ : Submodule R Sqf)
  let PtgtI : Submodule R Sqf := ISqf.restrictScalars R
  let eSrcSmul :
      (Sq ⧸ Psrc) ≃ₗ[R] (Sq ⧸ PsrcI) :=
    Submodule.quotEquivOfEq _ _ (by
      dsimp [Psrc, PsrcI, ISq]
      exact (Ideal.smul_top_eq_map (R := R) (S := Sq) I :
        I • (⊤ : Submodule R Sq) =
          (Ideal.map (algebraMap R Sq) I).restrictScalars R))
  let eSrcIdeal :
      (Sq ⧸ PsrcI) ≃ₗ[R] (Sq ⧸ ISq) :=
    Submodule.Quotient.restrictScalarsEquiv R ISq
  let eSrc :
      (Sq ⧸ Psrc) ≃ₗ[R] (Sq ⧸ ISq) :=
    eSrcSmul.trans eSrcIdeal
  let eTgtSmul :
      (Sqf ⧸ Ptgt) ≃ₗ[R] (Sqf ⧸ PtgtI) :=
    Submodule.quotEquivOfEq _ _ (by
      dsimp [Ptgt, PtgtI, ISqf]
      exact (Ideal.smul_top_eq_map (R := R) (S := Sqf) I :
        I • (⊤ : Submodule R Sqf) =
          (Ideal.map (algebraMap R Sqf) I).restrictScalars R))
  let eTgtIdeal :
      (Sqf ⧸ PtgtI) ≃ₗ[R] (Sqf ⧸ ISqf) :=
    Submodule.Quotient.restrictScalarsEquiv R ISqf
  let eTgt :
      (Sqf ⧸ Ptgt) ≃ₗ[R] (Sqf ⧸ ISqf) :=
    eTgtSmul.trans eTgtIdeal
  have hcomm :
      eTgt ∘ₗ ((localizedMapAtPrimeCompl f q).toLinearMap).quotientMapByIdeal I =
        (localizedQuotientMapModIdealAtPrimeCompl f q I).toLinearMap ∘ₗ eSrc := by
    -- Quotient representatives generate both source quotients, so the commuting square is
    -- checked on `mk x`.
    apply Submodule.quot_hom_ext
    intro x
    dsimp [eSrc, eSrcSmul, eSrcIdeal, eTgt, eTgtSmul, eTgtIdeal, ISq, ISqf,
      LinearMap.quotientMapByIdeal, localizedMapAtPrimeCompl]
    rw [Submodule.Quotient.restrictScalarsEquiv_mk,
      Submodule.Quotient.restrictScalarsEquiv_mk]
    exact (localizedQuotientMapModIdealAtPrimeCompl_apply_mk (f := f) (I := I) (q := q) x).symm
  intro x y hxy
  apply eSrc.injective
  apply hquot.1
  -- Transport the equality through the commuting square and cancel the target quotient
  -- equivalence.
  calc
    (localizedQuotientMapModIdealAtPrimeCompl f q I).toLinearMap (eSrc x) =
        eTgt (((localizedMapAtPrimeCompl f q).toLinearMap.quotientMapByIdeal I) x) := by
          simpa using (LinearMap.congr_fun hcomm x).symm
    _ = eTgt (((localizedMapAtPrimeCompl f q).toLinearMap.quotientMapByIdeal I) y) := by
          rw [hxy]
    _ = (localizedQuotientMapModIdealAtPrimeCompl f q I).toLinearMap (eSrc y) := by
          simpa using LinearMap.congr_fun hcomm y

/-- Helper for Chap10 Lemma 10 126 10: the kernel ideal of a surjective map from a finite-type
algebra to a finitely presented algebra is finitely generated over the source. -/
private theorem kernel_fg_of_surjective_of_finitePresentation_over_source
    [Algebra.FiniteType R S] [Algebra.FinitePresentation R S']
    (hsurj : Function.Surjective f) :
    (RingHom.ker (f : S →+* S')).FG := by
  letI : Algebra S S' := f.toRingHom.toAlgebra
  have hfp : RingHom.FinitePresentation (f : S →+* S') :=
    RingHom.FinitePresentation.of_comp_finiteType
      (f := algebraMap R S)
      (g := (f : S →+* S'))
      (by
        simpa [RingHom.finitePresentation_algebraMap] using
          (inferInstance : Algebra.FinitePresentation R S'))
      (by
        simpa [RingHom.finiteType_algebraMap] using
          (inferInstance : Algebra.FiniteType R S))
  letI : Algebra.FinitePresentation S S' := hfp
  -- Finite presentation over the source identifies the kernel as a finitely generated ideal.
  simpa using Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId S S') hsurj

/-- Helper for Chap10 Lemma 10 126 10: the kernel ideal is a finite `S`-module, which is the
form needed when the source proof localizes the kernel and later applies Nakayama. -/
private theorem kernel_finite_of_surjective_of_finitePresentation_over_source
    [Algebra.FiniteType R S] [Algebra.FinitePresentation R S']
    (hsurj : Function.Surjective f) :
    Module.Finite S (RingHom.ker (f : S →+* S')) := by
  -- Package finite generation of the kernel ideal into the finite-module form used later.
  rw [Module.Finite.iff_fg]
  exact kernel_fg_of_surjective_of_finitePresentation_over_source
    (f := f) (R := R) hsurj

/-- Helper for Chap10 Lemma 10 126 10: extending `I` to the prime localization at `q` lands in
the Jacobson radical whenever its extension to `S` is contained in `q`. -/
private theorem mapIdeal_le_jacobson_localization_at_primeCompl
    (hIq : Ideal.map (algebraMap R S) I ≤ q) :
    Ideal.map (algebraMap R Sq) I ≤ Ring.jacobson Sq := by
  -- In the local ring `S_q`, the Jacobson radical is the maximal ideal.
  rw [IsLocalRing.ringJacobson_eq_maximalIdeal Sq]
  -- It is enough to test the generators coming from `I` before extension.
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff Sq q ((algebraMap R S) r)).2
    (hIq (Ideal.mem_map_of_mem (algebraMap R S) hr))

/-- Helper for Chap10 Lemma 10 126 10: in an exact sequence, if both quotient maps modulo an
ideal are injective, then the left quotient modulo that ideal is zero. -/
private theorem quotient_left_subsingleton_of_exact_and_quotient_injective
    {P Q T : Type*}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] [AddCommGroup T] [Module R T]
    (I : Ideal R) (φ : P →ₗ[R] Q) (ψ : Q →ₗ[R] T)
    (hφq : Function.Injective (φ.quotientMapByIdeal I))
    (hψq : Function.Injective (ψ.quotientMapByIdeal I))
    (hExact : Function.Exact φ ψ) :
    Subsingleton (P ⧸ (I • (⊤ : Submodule R P))) := by
  -- It is enough to show that every representative already lies in the ideal multiple.
  rw [Submodule.Quotient.subsingleton_iff]
  apply top_le_iff.mp
  intro x hx
  -- Exactness gives `ψ (φ x) = 0`, hence the image of `x` in the middle quotient maps to zero.
  have hxpsi :
      (ψ.quotientMapByIdeal I) ((φ.quotientMapByIdeal I) (Submodule.Quotient.mk x)) =
        (ψ.quotientMapByIdeal I)
          (0 : Q ⧸ (I • (⊤ : Submodule R Q))) := by
    have hcomp : ψ (φ x) = 0 := by
      have hxrange : φ x ∈ LinearMap.range φ := ⟨x, rfl⟩
      have hxker : φ x ∈ LinearMap.ker ψ := by
        rwa [LinearMap.exact_iff.mp hExact]
      exact hxker
    simpa [LinearMap.quotientMapByIdeal, hcomp]
  -- The two quotient injectivity hypotheses then force the original quotient class to vanish.
  have hφxzero :
      (φ.quotientMapByIdeal I) (Submodule.Quotient.mk x) =
        (0 : Q ⧸ (I • (⊤ : Submodule R Q))) := hψq hxpsi
  have hφxzero' :
      (φ.quotientMapByIdeal I) (Submodule.Quotient.mk x) =
        (φ.quotientMapByIdeal I)
          (0 : P ⧸ (I • (⊤ : Submodule R P))) := by
    simpa using hφxzero
  have hxquot :
      Submodule.Quotient.mk x =
        (0 : P ⧸ (I • (⊤ : Submodule R P))) := hφq hφxzero'
  exact (Submodule.Quotient.mk_eq_zero _).mp hxquot

/-- Helper for Chap10 Lemma 10 126 10: the inclusion of the ring kernel of an algebra map
followed by the algebra map is exact as a sequence of `R`-modules. -/
private theorem algHom_ringKerSubtype_exact
    {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (g : A →ₐ[R] B) :
    Function.Exact (((RingHom.ker g.toRingHom : Ideal A).subtype).restrictScalars R)
      g.toLinearMap := by
  -- The range is precisely the elements whose image under `g` is zero.
  rw [LinearMap.exact_iff]
  ext x
  constructor
  · intro hx
    refine ⟨⟨x, ?_⟩, rfl⟩
    simpa [RingHom.mem_ker] using hx
  · rintro ⟨y, rfl⟩
    exact y.property

/-- Helper for Chap10 Lemma 10 126 10: quotienting by an ideal commutes with the tensor
description of the quotient, without requiring the two modules to live in the same universe. -/
private theorem quotientMapByIdeal_lTensor_naturality_arbitraryUniverse
    {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (J : Ideal R) (φ : P →ₗ[R] Q) :
    φ.quotientMapByIdeal J ∘ₗ TensorProduct.quotTensorEquivQuotSMul P J =
      TensorProduct.quotTensorEquivQuotSMul Q J ∘ₗ φ.lTensor (R ⧸ J) := by
  -- Check the naturality square on pure tensors, where both quotient maps have the same value.
  apply TensorProduct.ext'
  intro q x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [LinearMap.quotientMapByIdeal]

/-- Helper for Chap10 Lemma 10 126 10: flat exactness makes the left quotient map injective even
when the right-hand term is in a different universe. -/
private theorem quotientMapByIdeal_injective_of_exact_of_flat_arbitraryUniverse
    {P Q T : Type*}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [AddCommGroup T] [Module R T] [Module.Flat R T]
    (J : Ideal R) (φ : P →ₗ[R] Q) (ψ : Q →ₗ[R] T)
    (hφ : Function.Injective φ) (hψ : Function.Surjective ψ)
    (hExact : Function.Exact φ ψ) :
    Function.Injective (φ.quotientMapByIdeal J) := by
  -- Tensor the exact sequence with `R / J`; flatness of `T` preserves injectivity on the left.
  have hTensorInj : Function.Injective (φ.lTensor (R ⧸ J)) := by
    simpa [LinearMap.lTensor_inj_iff_rTensor_inj] using
      LinearMap.lTensor_injective_of_exact_of_flat ψ hψ φ hφ hExact (R ⧸ J)
  -- Transport the tensor-side injectivity back through the canonical quotient equivalences.
  exact injective_of_ladder_linearEquiv (R := R)
    (quotientMapByIdeal_lTensor_naturality_arbitraryUniverse (R := R) J φ) hTensorInj

/-- Helper for Chap10 Lemma 10 126 10: the public localized map is surjective when the original
map is surjective. -/
private theorem localizedMapAtPrimeCompl_surjective
    (hsurj : Function.Surjective f) :
    Function.Surjective (localizedMapAtPrimeCompl f q) := by
  letI : Algebra S S' := f.toRingHom.toAlgebra
  -- Localizing a surjective algebra map remains surjective; the `AlgHom` and its underlying
  -- ring hom have the same function.
  have h :
      Function.Surjective
        (IsLocalization.map (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))
          (algebraMap S S')
          (Algebra.algebraMapSubmonoid_le_comap q.primeCompl (Algebra.ofId S S'))) :=
    IsLocalization.mapₐ_surjective_of_surjective
      (M := q.primeCompl) (Rₚ := Sq) (Aₚ := Sq)
      (Bₚ := Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))
      (Algebra.ofId S S') hsurj
  intro y
  obtain ⟨x, hx⟩ := h y
  refine ⟨x, ?_⟩
  dsimp [localizedMapAtPrimeCompl]
  change
    (IsLocalization.map (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))
      (algebraMap S S')
      (Algebra.algebraMapSubmonoid_le_comap q.primeCompl (Algebra.ofId S S'))) x = y
  exact hx

/-- Helper for Chap10 Lemma 10 126 10: if the localized public kernel is finite and its quotient
modulo `I` is zero, Nakayama kills it. -/
private theorem localizedPublicKernel_subsingleton_of_quotient_subsingleton
    (hIq : Ideal.map (algebraMap R S) I ≤ q)
    (hKfinite : Module.Finite Sq (RingHom.ker (localizedMapAtPrimeCompl f q).toRingHom))
    (hquotK :
      Subsingleton
        ((RingHom.ker (localizedMapAtPrimeCompl f q).toRingHom) ⧸
          (I • (⊤ : Submodule R (RingHom.ker (localizedMapAtPrimeCompl f q).toRingHom))))) :
    Subsingleton (RingHom.ker (localizedMapAtPrimeCompl f q).toRingHom) := by
  let K := RingHom.ker (localizedMapAtPrimeCompl f q).toRingHom
  have hJac : Ideal.map (algebraMap R Sq) I ≤ Ring.jacobson Sq :=
    mapIdeal_le_jacobson_localization_at_primeCompl (I := I) (q := q) hIq
  have hIKtopR :
      I • (⊤ : Submodule R K) = ⊤ := by
    -- The quotient `K / IK` is zero precisely when `IK` is the whole module over `R`.
    exact Submodule.Quotient.subsingleton_iff.mp hquotK
  have hIKtopSq :
      Ideal.map (algebraMap R Sq) I • (⊤ : Submodule Sq K) = ⊤ := by
    -- Convert the `R`-linear equality to the equivalent `Sq`-linear ideal multiple.
    apply Submodule.restrictScalars_injective R
    calc
      Submodule.restrictScalars R (Ideal.map (algebraMap R Sq) I • (⊤ : Submodule Sq K)) =
          I • (⊤ : Submodule R K) := by
            simpa [K] using (Ideal.smul_restrictScalars (R := R) (S := Sq)
              (M := K) I (⊤ : Submodule Sq K))
      _ = Submodule.restrictScalars R (⊤ : Submodule Sq K) := by
            simpa [hIKtopR, Submodule.restrictScalars_top]
  -- Nakayama over the local ring `S_q` kills the finite public kernel.
  exact subsingleton_of_ideal_smul_top_eq_top_of_le_ring_jacobson
    (I := Ideal.map (algebraMap R Sq) I) hIKtopSq hJac

/-- Helper for Chap10 Lemma 10 126 10: flat exactness makes the quotient map from the public
ring kernel injective modulo `I`. -/
private theorem localizedMapAtPrimeCompl_ringKernelSubtype_quotientMapByIdeal_injective
    (hsurj : Function.Surjective f)
    [Module.Flat R Sqf] :
    Function.Injective
      (((RingHom.ker (localizedMapAtPrimeCompl f q).toRingHom : Ideal Sq).subtype
        |>.restrictScalars R).quotientMapByIdeal I) := by
  -- The subtype map is injective, and exactness is the tautological kernel exactness above.
  have hSubtype :
      Function.Injective
        (((RingHom.ker (localizedMapAtPrimeCompl f q).toRingHom : Ideal Sq).subtype)
          |>.restrictScalars R) := by
    intro x y hxy
    exact Subtype.ext hxy
  have hLocalizedSurj :
      Function.Surjective (localizedMapAtPrimeCompl f q) :=
    localizedMapAtPrimeCompl_surjective (f := f) (q := q) hsurj
  have hExact :
      Function.Exact
        (((RingHom.ker (localizedMapAtPrimeCompl f q).toRingHom : Ideal Sq).subtype)
          |>.restrictScalars R)
        (localizedMapAtPrimeCompl f q).toLinearMap :=
    algHom_ringKerSubtype_exact (R := R) (g := localizedMapAtPrimeCompl f q)
  -- Flatness of the localized target transports this exactness to injectivity after quotienting.
  exact quotientMapByIdeal_injective_of_exact_of_flat_arbitraryUniverse
    (R := R) I
    (((RingHom.ker (localizedMapAtPrimeCompl f q).toRingHom : Ideal Sq).subtype)
      |>.restrictScalars R)
    (localizedMapAtPrimeCompl f q).toLinearMap
    hSubtype hLocalizedSurj hExact

/-- Helper for Chap10 Lemma 10 126 10: flat exactness and the quotient-map hypothesis kill the
quotient of the public ring kernel of the localized map by `I`. -/
private theorem localizedMapAtPrimeCompl_ringKernelQuotient_subsingleton
    (hsurj : Function.Surjective f)
    [Module.Flat R Sqf]
    (hquot : Function.Bijective (localizedQuotientMapModIdealAtPrimeCompl f q I)) :
    Subsingleton
      ((RingHom.ker (localizedMapAtPrimeCompl f q).toRingHom) ⧸
        (I • (⊤ : Submodule R
          (RingHom.ker (localizedMapAtPrimeCompl f q).toRingHom)))) := by
  -- Route correction: avoid the old linear-kernel quotient transport by choosing the public
  -- ring kernel as the left term of the exact sequence from the start.
  exact quotient_left_subsingleton_of_exact_and_quotient_injective
    (R := R) I
    (((RingHom.ker (localizedMapAtPrimeCompl f q).toRingHom : Ideal Sq).subtype)
      |>.restrictScalars R)
    (localizedMapAtPrimeCompl f q).toLinearMap
    (localizedMapAtPrimeCompl_ringKernelSubtype_quotientMapByIdeal_injective
      (f := f) (I := I) (q := q) hsurj)
    (localizedMapAtPrimeCompl_quotientMapByIdeal_injective_of_bijective_quotient
      (f := f) (I := I) (q := q) hquot)
    (algHom_ringKerSubtype_exact (R := R) (g := localizedMapAtPrimeCompl f q))

/-- Helper for Chap10 Lemma 10 126 10: localization of the source kernel is linearly equivalent
to the public ring kernel of the localized map. -/
private theorem localizedSourceKernel_linearEquiv_publicRingKernel :
    Nonempty
      (LocalizedModule q.primeCompl (RingHom.ker (f : S →+* S')) ≃ₗ[Sq]
        RingHom.ker (localizedMapAtPrimeCompl f q).toRingHom) := by
  let J : Ideal S := RingHom.ker (f : S →+* S')
  letI : Algebra S S' := f.toRingHom.toAlgebra
  let κ : J →ₗ[S] RingHom.ker (localizedMapAtPrimeCompl f q).toRingHom := by
    -- The kernel-localization map from mathlib has the same target after unfolding our public
    -- localized algebra map.
    simpa [J, localizedMapAtPrimeCompl] using
      (AlgHom.toKerIsLocalization
        (R := S) (M := q.primeCompl) (A := S) (B := S')
        (Rₚ := Sq) (Aₚ := Sq)
        (Bₚ := Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))
        (Algebra.ofId S S'))
  let _ : IsLocalizedModule q.primeCompl κ := by
    -- The same unfolding identifies the `IsLocalizedModule` instance for the kernel map.
    simpa [κ, J, localizedMapAtPrimeCompl] using
      (AlgHom.toKerIsLocalization_isLocalizedModule
        (R := S) (M := q.primeCompl) (A := S) (B := S')
        (Rₚ := Sq) (Aₚ := Sq)
        (Bₚ := Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))
        (Algebra.ofId S S'))
  -- The universal property gives an `S`-linear equivalence; extending scalars makes it
  -- `S_q`-linear for the finiteness transport.
  exact ⟨LinearEquiv.extendScalarsOfIsLocalization q.primeCompl Sq
    (IsLocalizedModule.iso q.primeCompl κ)⟩

/-- Chap10 Lemma 10 126 10: the localized kernel of `f` at `q.primeCompl` vanishes once the
comparison modulo `I` is bijective. -/
private theorem localized_kernel_subsingleton_at_prime_compl_of_bijective_quotient
    [Algebra.FiniteType R S] [Algebra.FinitePresentation R S']
    (hIq : Ideal.map (algebraMap R S) I ≤ q)
    (hsurj : Function.Surjective f)
    [Module.Flat R Sqf]
    (hquot : Function.Bijective (localizedQuotientMapModIdealAtPrimeCompl f q I)) :
    Subsingleton (LocalizedModule q.primeCompl (RingHom.ker (f : S →+* S'))) := by
  let J : Ideal S := RingHom.ker (f : S →+* S')
  letI : Algebra S S' := f.toRingHom.toAlgebra
  letI : Module.Finite S J :=
    kernel_finite_of_surjective_of_finitePresentation_over_source (f := f) (R := R) hsurj
  have hKquot :
      Subsingleton
        ((RingHom.ker (localizedMapAtPrimeCompl f q).toRingHom) ⧸
          (I • (⊤ : Submodule R
            (RingHom.ker (localizedMapAtPrimeCompl f q).toRingHom)))) :=
    localizedMapAtPrimeCompl_ringKernelQuotient_subsingleton
      (f := f) (I := I) (q := q) hsurj hquot
  obtain ⟨e⟩ := localizedSourceKernel_linearEquiv_publicRingKernel
    (f := f) (q := q)
  have hKfinite :
      Module.Finite Sq (RingHom.ker (localizedMapAtPrimeCompl f q).toRingHom) := by
    -- Finiteness localizes from `J` and then transports across the kernel-localization
    -- equivalence.
    exact Module.Finite.equiv e
  have hKpublic :
      Subsingleton (RingHom.ker (localizedMapAtPrimeCompl f q).toRingHom) :=
    localizedPublicKernel_subsingleton_of_quotient_subsingleton
      (f := f) (I := I) (q := q) hIq hKfinite hKquot
  -- Transport the public-kernel vanishing back to the textbook localized source kernel.
  exact (e.toEquiv.subsingleton_congr).2 hKpublic

-- Proof sketch: let `J = RingHom.ker f`. Finite presentation of `S'` and finite type of `S`
-- imply that `J` is finitely generated. Flatness of the localized target over `R` identifies the
-- kernel of `(S_q / I S_q) → (S'_q / I S'_q)` with `J_q / I J_q`; the assumed bijectivity forces
-- this quotient to vanish. Nakayama then gives `J_q = 0`, so `S_q → S'_q` is bijective, and the
-- finite-presentation spreading lemma upgrades this to `S_g → S'_g` for some `g ∉ q`.
/-- Consequence of Chap10 Lemma 10 126 10: let `R` be a ring, let `I ⊆ R` be an ideal, let
`f : S →ₐ[R] S'` be a surjective `R`-algebra map, and let `q` be a prime ideal of `S`
containing `I S`. If `S` is of
finite type over `R`, `S'` is of finite presentation over `R`, the induced quotient algebra map on
the localizations at `q.primeCompl` modulo `I` is bijective, and the localized target `S'_q` is
flat over `R`,
then there exists `g ∉ q` such that `S_g → S'_g` is bijective. -/
@[stacks 087P]
lemma exists_notMem_and_awayMap_bijective_of_localizedQuotient_bijective
    [Algebra.FiniteType R S] [Algebra.FinitePresentation R S']
    (hIq : Ideal.map (algebraMap R S) I ≤ q)
    (hsurj : Function.Surjective f)
    [Module.Flat R Sqf]
    (hquot : Function.Bijective (localizedQuotientMapModIdealAtPrimeCompl f q I)) :
    ∃ g : S, g ∉ q ∧ Function.Bijective (Localization.awayMapₐ f g) :=
  by
  let J : Ideal S := RingHom.ker (f : S →+* S')
  letI : Algebra S S' := f.toRingHom.toAlgebra
  letI : Module.Finite S J := kernel_finite_of_surjective_of_finitePresentation_over_source
    (f := f) (R := R) hsurj
  have hJq :
      Subsingleton (LocalizedModule q.primeCompl J) :=
    localized_kernel_subsingleton_at_prime_compl_of_bijective_quotient
      (f := f) (R := R) (I := I) (q := q) hIq hsurj hquot
  letI : Subsingleton (LocalizedModule q.primeCompl J) := hJq
  obtain ⟨g, hgq, hJaway⟩ := LocalizedModule.exists_subsingleton_away (M := J) q
  have hAwayInj : Function.Injective (Localization.awayMap (f := (f : S →+* S')) g) := by
    rw [Localization.awayMap_injective_iff]
    intro x hx
    obtain ⟨r, hr, hrx⟩ :=
      (LocalizedModule.subsingleton_iff (R := S) (M := J) (S := Submonoid.powers g)).1 hJaway
        ⟨x, hx⟩
    rcases hr with ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    simpa [J, Algebra.smul_def, smul_eq_mul] using congrArg Subtype.val hrx
  have hAwaySurj : Function.Surjective (Localization.awayMap (f := (f : S →+* S')) g) := by
    rw [Localization.awayMap_surjective_iff]
    intro x
    obtain ⟨y, rfl⟩ := hsurj x
    exact ⟨y, 0, by simp⟩
  refine ⟨g, hgq, ?_⟩
  -- The algebra-valued away map is bijective exactly when the underlying ring map is.
  simpa using ⟨hAwayInj, hAwaySurj⟩

end
