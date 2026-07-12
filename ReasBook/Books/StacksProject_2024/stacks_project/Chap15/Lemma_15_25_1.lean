import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.MvPolynomial.Basic
import StacksProject_2024.Chap10.Lemma_10_23_2
import StacksProject_2024.Chap10.Lemma_10_24_5
import StacksProject_2024.Chap10.Lemma_10_126_4
import StacksProject_2024.Chap10.Theorem_10_129_4
import StacksProject_2024.Chap15.Lemma_15_18_3
import StacksProject_2024.Chap15.Remark_15_25_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u w

noncomputable section

variable {R : Type u} [CommRing R]
variable (n : ℕ)
variable {M : Type w} [AddCommGroup M]
variable [Module (MvPolynomial (Fin n) R) M] [Module R M]
variable [IsScalarTower R (MvPolynomial (Fin n) R) M]
variable [Module.Finite (MvPolynomial (Fin n) R) M] [Module.Flat R M]

/- Domain-style sampling:
* primary domain: finite-presentation descent for flat finite modules over polynomial algebras from
  prime-local finite-presentation data;
* sampled owner declarations:
  - `Module.FinitePresentation`,
  - `module_finitePresentation_of_localizationAway`,
  - `primeLocalizationsDetectEquality`,
  - `MvPolynomial.algebraTensorAlgEquiv`,
  - the chapter-local weighted graded specialization
    `finitePresentation_of_local_flat_finite_weighted_graded_mvPolynomial_module`;
* best owner abstraction: the canonical predicate
  `Module.FinitePresentation (MvPolynomial (Fin n) R) M`;
* primitive data: the polynomial-module structure on `M`, finite generation over
  `MvPolynomial (Fin n) R`, flatness over `R`, and the prime-local tensor-product base changes
  `((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R) ⊗[MvPolynomial (Fin n) R] M`;
* derived API: only the global finite-presentation conclusion.

Source/core/bridge triage:
* `source-facing`: the descent theorem below;
* `core/canonical`: `Module.FinitePresentation` together with the localization owners behind
  tensor-product base change;
* `bridge/view`: `MvPolynomial.algebraTensorAlgEquiv`, identifying the tensor-base-change algebra
  `Localization.AtPrime p.asIdeal ⊗[R] MvPolynomial (Fin n) R` with the textbook polynomial ring
  `MvPolynomial (Fin n) (Localization.AtPrime p.asIdeal)`.
-/

-- Proof sketch: choose a finite presentation of `M` by a finite free `S`-module and let `K` be the
-- kernel. Use the local finite-presentation hypotheses to find a finitely generated submodule of
-- `K` that agrees with `K` after passing to the prime-local tensor-product base changes over
-- `Localization.AtPrime p.asIdeal ⊗[R] MvPolynomial (Fin n) R`, equivalently over
-- `MvPolynomial (Fin n) (Localization.AtPrime p.asIdeal)`, at the distinguished finitely
-- many primes and at the prime under a chosen prime of `S`. Replace `M` by the resulting
-- finite-presentation quotient,
-- use openness of flatness to preserve `R`-flatness after inverting one element of `S`, and then
-- apply injectivity of `R → ∏ R_{p_j}` together with flatness to deduce the quotient map is an
-- isomorphism after localizing away from that element. Conclude by the standard local criterion for
-- finite presentation.
/-- Helper for Lemma 15.25.1: the right tensor factor gives the polynomial-ring algebra structure
on the prime-local tensor product. Making this instance explicit keeps later typeclass search
stable. -/
local instance tensorAtPrime_rightAlgebra (p : PrimeSpectrum R) :
    Algebra (MvPolynomial (Fin n) R)
      ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R) :=
  Algebra.TensorProduct.rightAlgebra

/-- Helper for Lemma 15.25.1: the prime-local tensor product acts on itself in the evident way.
Making this instance explicit prevents typeclass search from re-deriving the ambient ring module
structure through the tensor-product stack. -/
local instance tensorAtPrime_selfSMul (p : PrimeSpectrum R) :
    SMul
      ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R)
      ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R) where
  smul := (· * ·)

/-- Helper for Lemma 15.25.1: the prime-local tensor product acts on itself in the evident way.
Making this instance explicit prevents typeclass search from re-deriving the ambient ring module
structure through the tensor-product stack. -/
local instance tensorAtPrime_selfModule (p : PrimeSpectrum R) :
    Module
      ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R)
      ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R) :=
  Semiring.toModule

/-- Helper for Lemma 15.25.1: the explicit `MvPolynomial (Fin n) R`-module structure on the
prime-local tensor product induced by the right-factor algebra structure. -/
local instance tensorAtPrime_rightSMul (p : PrimeSpectrum R) :
    SMul (MvPolynomial (Fin n) R)
      ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R) :=
  Algebra.toSMul

/-- Helper for Lemma 15.25.1: the explicit `MvPolynomial (Fin n) R`-module structure on the
prime-local tensor product induced by the right-factor algebra structure. -/
local instance tensorAtPrime_rightModule (p : PrimeSpectrum R) :
    Module (MvPolynomial (Fin n) R)
      ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R) :=
  Algebra.toModule

/-- Helper for Lemma 15.25.1: scalar actions coming from `MvPolynomial (Fin n) R` commute with
multiplication by elements of the prime-local tensor product. Pinning this instance avoids a
costly search through generic tensor-product scalar-compatibility rules. -/
local instance tensorAtPrime_smulCommClass (p : PrimeSpectrum R) :
    SMulCommClass (MvPolynomial (Fin n) R)
      ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R)
      ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R) := by
  infer_instance

/-- Helper for Lemma 15.25.1: the prime-local tensor product acts on its scalar extension of `M`
through the standard left-factor tensor action. -/
local instance tensorAtPrime_leftTensorModule (p : PrimeSpectrum R) :
    Module
      ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R)
      (((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R) ⊗[MvPolynomial (Fin n) R] M) :=
  TensorProduct.leftModule

/-- Helper for Lemma 15.25.1: the prime-local tensor product
`Localization.AtPrime p.asIdeal ⊗[R] MvPolynomial (Fin n) R` is the localization of
`MvPolynomial (Fin n) R` at the image of `p.asIdeal.primeCompl`. -/
lemma tensorAtPrime_mvPolynomial_isLocalization (p : PrimeSpectrum R) :
    IsLocalization
      (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl)
      ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R) := by
  -- Commute the tensor factors so that the standard left-tensor localization owner applies.
  let ecomm :
      ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R) ≃ₐ[MvPolynomial (Fin n) R]
        ((MvPolynomial (Fin n) R) ⊗[R] Localization.AtPrime p.asIdeal) :=
    { toRingEquiv :=
        (Algebra.TensorProduct.comm R (Localization.AtPrime p.asIdeal)
          (MvPolynomial (Fin n) R)).toRingEquiv
      commutes' := by
        intro f
        change (Algebra.TensorProduct.comm R (Localization.AtPrime p.asIdeal)
          (MvPolynomial (Fin n) R)) (1 ⊗ₜ[R] f) = _
        simp }
  let eloc :
      ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R) ≃ₐ[MvPolynomial (Fin n) R]
        Localization
          (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl) :=
    ecomm.trans (Localization.tensorLeftAlgEquiv p.asIdeal.primeCompl
      (MvPolynomial (Fin n) R))
  -- Transport the canonical localization structure across the algebra equivalence.
  exact IsLocalization.isLocalization_of_algEquiv
    (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl) eloc.symm

/-- Helper for Lemma 15.25.1: the prime-local tensor product algebra is canonically the
prime-complement localization of the polynomial ring. Naming this equivalence keeps the later
module-side transport focused on one algebra owner. -/
noncomputable def tensorAtPrime_localizationAlgEquiv (p : PrimeSpectrum R) :
    ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R) ≃ₐ[MvPolynomial (Fin n) R]
      Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl) :=
  IsLocalization.algEquiv
    (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl)
    ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R)
    (Localization
      (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl))

/-- Helper for Lemma 15.25.1: the canonical comparison map from the localization owner back to the
prime-local tensor-product ring is bijective. This is the ring-side input needed before
transporting the module finite-presentation hypothesis. -/
lemma tensorAtPrime_localizationAlgEquiv_symm_bijective (p : PrimeSpectrum R) :
    Function.Bijective
      ((tensorAtPrime_localizationAlgEquiv (n := n) (R := R) p).symm :
        Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl) →
          ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R)) := by
  exact (tensorAtPrime_localizationAlgEquiv (n := n) (R := R) p).symm.bijective

/-- Helper for Lemma 15.25.1: finite presentation over an algebra transports to the canonical
localization owner along an algebra equivalence. This isolates the ring-owner change before the
module-side localization argument. -/
lemma finitePresentation_of_algEquiv_localization_target
    {A B N : Type*} [CommRing A] [CommRing B]
    [Algebra (MvPolynomial (Fin n) R) A] [Algebra (MvPolynomial (Fin n) R) B]
    (e : A ≃ₐ[MvPolynomial (Fin n) R] B)
    [AddCommGroup N] [Module A N] [Module.FinitePresentation A N] :
    letI : Algebra B A := e.symm.toRingHom.toAlgebra
    letI : Module B N := Module.compHom N e.symm.toRingHom
    letI : IsScalarTower B A N := IsScalarTower.of_compHom B A N
    Module.FinitePresentation B N := by
  letI : Algebra B A := e.symm.toRingHom.toAlgebra
  letI : Module B N := Module.compHom N e.symm.toRingHom
  letI : IsScalarTower B A N := IsScalarTower.of_compHom B A N
  have hAfp : Module.FinitePresentation B A := by
    -- The algebra equivalence identifies `A` with the localization owner `B`.
    refine Module.finitePresentation_of_surjective (Algebra.linearMap B A) ?_ ?_
    · simpa [RingHom.algebraMap_toAlgebra] using e.symm.surjective
    · have hinj : Function.Injective (algebraMap B A) := by
        simpa [RingHom.algebraMap_toAlgebra] using e.symm.injective
      rw [LinearMap.ker_eq_bot.2 hinj]
      exact Submodule.fg_bot
  letI : Module.FinitePresentation B A := hAfp
  -- With the intermediate algebra finitely presented over `B`, transitivity closes the step.
  exact Module.FinitePresentation.trans B N A

/-- Helper for Lemma 15.25.1: the algebra equivalence from the prime-local tensor owner back to
the canonical localization target supplies the transported scalar action on the tensor module. -/
noncomputable abbrev tensorAtPrime_localizationTargetAlgebra (p : PrimeSpectrum R) :
    let U :
        Submonoid (MvPolynomial (Fin n) R) :=
      Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
    let A :=
      ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R)
    Algebra (Localization U) A :=
  let U :
      Submonoid (MvPolynomial (Fin n) R) :=
    Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
  let A :=
    ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R)
  (tensorAtPrime_localizationAlgEquiv (n := n) (R := R) p).symm.toRingHom.toAlgebra

/-- Helper for Lemma 15.25.1: after transporting scalars along the localization algebra
equivalence, the base-change tensor module acquires the canonical `Localization U`-module
structure needed for the owner comparison. -/
noncomputable abbrev tensorAtPrime_localizationTargetModule (p : PrimeSpectrum R) :
    let U :
        Submonoid (MvPolynomial (Fin n) R) :=
      Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
    let A :=
      ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R)
    Module (Localization U) (A ⊗[MvPolynomial (Fin n) R] M) :=
  let U :
      Submonoid (MvPolynomial (Fin n) R) :=
    Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
  let A :=
    ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R)
  Module.compHom (A ⊗[MvPolynomial (Fin n) R] M)
    (tensorAtPrime_localizationAlgEquiv (n := n) (R := R) p).symm.toRingHom

/-- Helper for Lemma 15.25.1: the inverse localization algebra equivalence fixes the polynomial
subring. This is the concrete rewrite needed when proving that the transported localization action
agrees with the original scalar action on the tensor module. -/
lemma tensorAtPrime_localizationAlgEquiv_symm_commutes (p : PrimeSpectrum R)
    (f : MvPolynomial (Fin n) R) :
    (tensorAtPrime_localizationAlgEquiv (n := n) (R := R) p).symm
        (algebraMap (MvPolynomial (Fin n) R)
          (Localization
            (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl)) f) =
      algebraMap (MvPolynomial (Fin n) R)
        ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R) f := by
  simpa using
    (tensorAtPrime_localizationAlgEquiv (n := n) (R := R) p).symm.commutes f

/-- Helper for Lemma 15.25.1: the transported `Localization U`-algebra structure on the
prime-local tensor product restricts to the original `MvPolynomial (Fin n) R`-algebra structure.
This is the scalar-tower bridge needed before comparing tensor modules over the two owners. -/
lemma tensorAtPrime_localizationTarget_isScalarTower (p : PrimeSpectrum R) :
    let U :
        Submonoid (MvPolynomial (Fin n) R) :=
      Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
    let A :=
      ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R)
    letI : Algebra (Localization U) A :=
      tensorAtPrime_localizationTargetAlgebra (n := n) (R := R) p
    IsScalarTower (MvPolynomial (Fin n) R) (Localization U) A := by
  let U :
      Submonoid (MvPolynomial (Fin n) R) :=
    Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
  let A :=
    ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R)
  letI : Algebra (Localization U) A :=
    tensorAtPrime_localizationTargetAlgebra (n := n) (R := R) p
  -- Proof comment: the transported `Localization U`-action is defined through the inverse
  -- algebra equivalence, so the tower condition reduces to the fact that this inverse fixes the
  -- polynomial subring.
  refine IsScalarTower.of_algebraMap_smul ?_
  intro f a
  change
    (tensorAtPrime_localizationAlgEquiv (n := n) (R := R) p).symm
        (algebraMap (MvPolynomial (Fin n) R) (Localization U) f) * a =
      algebraMap (MvPolynomial (Fin n) R) A f * a
  rw [tensorAtPrime_localizationAlgEquiv_symm_commutes (n := n) (R := R) p f]

/-- Helper for Lemma 15.25.1: after transporting the target algebra structure along the inverse
localization algebra equivalence, the left tensor factor comparison is already
`Localization U`-linear. This packages the owner change before applying
`TensorProduct.AlgebraTensorModule.congr`. -/
noncomputable def tensorAtPrime_localizationAlgEquiv_symm_linearEquiv (p : PrimeSpectrum R) :
    let U :
        Submonoid (MvPolynomial (Fin n) R) :=
      Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
    let A :=
      ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R)
    letI : Algebra (Localization U) A :=
      tensorAtPrime_localizationTargetAlgebra (n := n) (R := R) p
    Localization U ≃ₗ[Localization U] A :=
  let U :
      Submonoid (MvPolynomial (Fin n) R) :=
    Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
  let A :=
    ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R)
  letI : Algebra (Localization U) A :=
    tensorAtPrime_localizationTargetAlgebra (n := n) (R := R) p
  { __ := (tensorAtPrime_localizationAlgEquiv (n := n) (R := R) p).symm.toAddEquiv
    map_smul' := by
      intro x y
      -- The transported scalar action is multiplication through the inverse algebra equivalence.
      change (tensorAtPrime_localizationAlgEquiv (n := n) (R := R) p).symm (x * y) =
        (tensorAtPrime_localizationAlgEquiv (n := n) (R := R) p).symm x *
          (tensorAtPrime_localizationAlgEquiv (n := n) (R := R) p).symm y
      simp }

/-- Helper for Lemma 15.25.1: the prime-local tensor-product hypothesis already yields finite
presentation for the canonical localized module over the prime-complement localization owner. -/
lemma tensorAtPrime_finitePresentation_localizedModule (p : PrimeSpectrum R) (hp :
    Module.FinitePresentation
      ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R)
      (((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R) ⊗[MvPolynomial (Fin n) R] M)) :
    let U :
        Submonoid (MvPolynomial (Fin n) R) :=
      Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
    Module.FinitePresentation (Localization U) (LocalizedModule U M) := by
  let U :
      Submonoid (MvPolynomial (Fin n) R) :=
    Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
  let A :=
    ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R)
  letI : Algebra (Localization U) A :=
    tensorAtPrime_localizationTargetAlgebra (n := n) (R := R) p
  letI : Module (Localization U) (A ⊗[MvPolynomial (Fin n) R] M) :=
    tensorAtPrime_localizationTargetModule (n := n) (R := R) (M := M) p
  letI : IsScalarTower (MvPolynomial (Fin n) R) (Localization U) A :=
    tensorAtPrime_localizationTarget_isScalarTower (n := n) (R := R) p
  have hTensorFp : Module.FinitePresentation (Localization U) (A ⊗[MvPolynomial (Fin n) R] M) :=
    finitePresentation_of_algEquiv_localization_target
      (n := n) (R := R)
      (e := tensorAtPrime_localizationAlgEquiv (n := n) (R := R) p)
      (N := A ⊗[MvPolynomial (Fin n) R] M)
  let eTensor :
      (Localization U ⊗[MvPolynomial (Fin n) R] M) ≃ₗ[Localization U]
        (A ⊗[MvPolynomial (Fin n) R] M) :=
    TensorProduct.AlgebraTensorModule.congr
      (tensorAtPrime_localizationAlgEquiv_symm_linearEquiv (n := n) (R := R) p)
      (LinearEquiv.refl (MvPolynomial (Fin n) R) M)
  have hLocalizedTensorFp :
      Module.FinitePresentation (Localization U)
        (Localization U ⊗[MvPolynomial (Fin n) R] M) := by
    exact Module.FinitePresentation.of_equiv eTensor.symm
  letI :
      Module.FinitePresentation (Localization U)
        (Localization U ⊗[MvPolynomial (Fin n) R] M) := hLocalizedTensorFp
  -- Proof comment: after transporting the tensor base-change along the ring equivalence, the
  -- canonical localization/tensor comparison identifies it with `LocalizedModule U M`.
  exact Module.FinitePresentation.of_equiv (LocalizedModule.equivTensorProduct U M).symm

/-- Helper for Lemma 15.25.1: localizing a fixed surjective finite free cover preserves
surjectivity. This is the first input in the localized-kernel argument. -/
lemma localized_cover_surjective_at_prime
    {m : ℕ}
    (π : (Fin m → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (hπ : Function.Surjective π) (p : PrimeSpectrum R) :
    let U :
        Submonoid (MvPolynomial (Fin n) R) :=
      Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
    Function.Surjective (LocalizedModule.map U π) := by
  let U :
      Submonoid (MvPolynomial (Fin n) R) :=
    Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
  -- Localization is exact enough to preserve surjective linear maps.
  simpa [U] using LocalizedModule.map_surjective U π hπ

/-- Helper for Lemma 15.25.1: the explicit localized owner of `ker π` obtained from
`Submodule.toLocalized'` is canonically the same localized module as `LocalizedModule U (ker π)`.
This isolates the owner comparison needed to transport finiteness of the localized kernel. -/
noncomputable abbrev localized_kernel_owner_linear_equiv
    {m : ℕ}
    (π : (Fin m → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (p : PrimeSpectrum R) :
    let U :
        Submonoid (MvPolynomial (Fin n) R) :=
      Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
    Submodule.localized' (Localization U) U
        (LocalizedModule.mkLinearMap U (Fin m → MvPolynomial (Fin n) R))
        (LinearMap.ker π) ≃ₗ[Localization U]
      LocalizedModule U (LinearMap.ker π) :=
  let U :
      Submonoid (MvPolynomial (Fin n) R) :=
    Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
  let κ :
      LinearMap.ker π →ₗ[MvPolynomial (Fin n) R]
        Submodule.localized' (Localization U) U
          (LocalizedModule.mkLinearMap U (Fin m → MvPolynomial (Fin n) R))
          (LinearMap.ker π) :=
    Submodule.toLocalized' (Localization U) U
      (LocalizedModule.mkLinearMap U (Fin m → MvPolynomial (Fin n) R))
      (LinearMap.ker π)
  letI : IsLocalizedModule U κ := inferInstance
  -- Compare the explicit localized owner with the canonical localized module and then upgrade the
  -- comparison to the localization ring itself.
  (IsLocalizedModule.linearEquiv U κ
    (LocalizedModule.mkLinearMap U (LinearMap.ker π))).extendScalarsOfIsLocalization U
    (Localization U)

/-- Helper for Lemma 15.25.1: after fixing one finite free cover of `M`, finite presentation of
the localized target at a chosen prime forces the localized kernel of that cover to be finite.
Lemma `10.126.4` then clears denominators and produces a finite submodule of the original kernel
whose localization is the whole localized kernel. -/
lemma exists_finite_submodule_of_kernel_with_top_localized_at_prime
    {m : ℕ}
    (π : (Fin m → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (hπ : Function.Surjective π) (p : PrimeSpectrum R)
    (hfp :
      let U :
          Submonoid (MvPolynomial (Fin n) R) :=
        Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
      Module.FinitePresentation (Localization U) (LocalizedModule U M)) :
    ∃ Kp : Submodule (MvPolynomial (Fin n) R) (LinearMap.ker π),
      Module.Finite (MvPolynomial (Fin n) R) Kp ∧
        Kp.localized
          (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl) = ⊤ := by
  let U :
      Submonoid (MvPolynomial (Fin n) R) :=
    Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
  let πU :
      LocalizedModule U (Fin m → MvPolynomial (Fin n) R) →ₗ[Localization U]
        LocalizedModule U M :=
    LocalizedModule.map U π
  have hπU : Function.Surjective πU := by
    -- Proof comment: localizing the fixed finite free cover preserves surjectivity.
    simpa [U, πU] using localized_cover_surjective_at_prime
      (n := n) (R := R) (M := M) π hπ p
  have hlocalizedKernelFinite :
      Module.Finite (Localization U)
        (Submodule.localized' (Localization U) U
          (LocalizedModule.mkLinearMap U (Fin m → MvPolynomial (Fin n) R))
          (LinearMap.ker π)) := by
    letI : Module.FinitePresentation (Localization U) (LocalizedModule U M) := hfp
    have hkerEq :
        Submodule.localized' (Localization U) U
            (LocalizedModule.mkLinearMap U (Fin m → MvPolynomial (Fin n) R))
            (LinearMap.ker π) =
          LinearMap.ker πU := by
      simpa [πU] using
        (LinearMap.localized'_ker_eq_ker_localizedMap
          (Localization U)
          U
          (LocalizedModule.mkLinearMap U (Fin m → MvPolynomial (Fin n) R))
          (LocalizedModule.mkLinearMap U M)
          π)
    have hkerFp :
        Module.FinitePresentation (Localization U) (LinearMap.ker πU) := by
      -- Proof comment: the localized free source and the localized finitely presented target make
      -- the localized kernel itself finitely presented.
      exact Module.finitePresentation_of_ker πU hπU
    letI : Module.FinitePresentation (Localization U) (LinearMap.ker πU) := hkerFp
    have hkerFinite : Module.Finite (Localization U) (LinearMap.ker πU) := inferInstance
    exact (Module.Finite.equiv_iff (LinearEquiv.ofEq _ _ hkerEq)).2 hkerFinite
  letI :
      Module.Finite (Localization U)
        (Submodule.localized' (Localization U) U
          (LocalizedModule.mkLinearMap U (Fin m → MvPolynomial (Fin n) R))
          (LinearMap.ker π)) := hlocalizedKernelFinite
  have hcanonicalKernelFinite :
      Module.Finite (Localization U) (LocalizedModule U (LinearMap.ker π)) := by
    -- Proof comment: transport finiteness from the explicit `Submodule.localized'` owner back to
    -- the canonical localized kernel module.
    exact
      (Module.Finite.equiv_iff
        ((localized_kernel_owner_linear_equiv
          (n := n) (R := R) (M := M) π p).symm)).2 hlocalizedKernelFinite
  letI : Module.Finite (Localization U) (LocalizedModule U (LinearMap.ker π)) :=
    hcanonicalKernelFinite
  -- Proof comment: Lemma `10.126.4` now clears denominators inside the original kernel.
  simpa [U] using
    (exists_finite_submodule_with_top_localized
      (S := U) (M := LinearMap.ker π))

/-- Helper for Lemma 15.25.1: localizing submodules is monotone. We use the explicit carrier of
`Submodule.localized` so the family-supremum argument can pass from `K_r ≤ K₀` to
`K_r.localized ≤ K₀.localized` without introducing another owner mismatch. -/
lemma localized_submodule_mono
    {A : Type*} [CommSemiring A] {N : Type*} [AddCommMonoid N] [Module A N]
    (U : Submonoid A) {P Q : Submodule A N} (hPQ : P ≤ Q) :
    P.localized U ≤ Q.localized U := by
  intro x hx
  -- Unfold the localization carrier once, then keep the same numerator/denominator witness.
  change x ∈ Submodule.localized₀ U (LocalizedModule.mkLinearMap U N) Q
  change x ∈ Submodule.localized₀ U (LocalizedModule.mkLinearMap U N) P at hx
  rcases hx with ⟨m, hm, s, rfl⟩
  exact ⟨m, hPQ hm, s, rfl⟩

/-- Helper for Lemma 15.25.1: a finite supremum of finite submodules is finite. This keeps the
enlarged-family denominator clearing argument flat instead of nested inside the main theorem. -/
lemma moduleFinite_finset_sup
    {ι : Type*} {A : Type*} [Semiring A]
    {N : Type*} [AddCommMonoid N] [Module A N]
    (t : Finset ι) (K : ι → Submodule A N)
    (hK : ∀ i ∈ t, Module.Finite A (K i)) :
    Module.Finite A (t.sup (α := Submodule A N) K) := by
  classical
  refine Module.Finite.of_fg ?_
  induction t using Finset.induction_on with
  | empty =>
      simpa using (Submodule.fg_bot : (⊥ : Submodule A N).FG)
  | @insert a s ha ih =>
      -- Finite generation of the new supremum comes from finite generation of each summand.
      have hKa : (K a).FG := by
        letI : Module.Finite A (K a) := hK a (by simp)
        exact Submodule.FG.of_finite
      have hKs : (s.sup K).FG := by
        exact ih fun i hi ↦ hK i (by simp [hi])
      simpa [Finset.sup_insert, ha] using Submodule.FG.sup hKa hKs

/-- Helper for Lemma 15.25.1: after adjoining the distinguished prime to the detecting family, one
can choose a single finite submodule of the fixed kernel whose localization is the whole localized
kernel at every prime in that enlarged family. -/
lemma exists_finite_submodule_of_kernel_with_top_localized_at_detecting_family
    {m : ℕ}
    (t : Finset (PrimeSpectrum R))
    (π : (Fin m → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (hπ : Function.Surjective π)
    (hfp :
      ∀ r ∈ t,
        let U :
            Submonoid (MvPolynomial (Fin n) R) :=
          Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) r.asIdeal.primeCompl
        Module.FinitePresentation (Localization U) (LocalizedModule U M)) :
    ∃ K0 : Submodule (MvPolynomial (Fin n) R) (LinearMap.ker π),
      Module.Finite (MvPolynomial (Fin n) R) K0 ∧
        ∀ r ∈ t,
          K0.localized
            (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) r.asIdeal.primeCompl) = ⊤ := by
  classical
  have hprime :
      ∀ r ∈ t,
        ∃ Kp : Submodule (MvPolynomial (Fin n) R) (LinearMap.ker π),
          Module.Finite (MvPolynomial (Fin n) R) Kp ∧
            Kp.localized
              (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) r.asIdeal.primeCompl) = ⊤ := by
    intro r hr
    -- Normalize the local finite-presentation input to the canonical localization owner, then
    -- apply the single-prime denominator-clearing lemma already proved above.
    exact
      exists_finite_submodule_of_kernel_with_top_localized_at_prime
        (n := n) (R := R) (M := M) π hπ r (hfp r hr)
  have hprime_all :
      ∀ r : PrimeSpectrum R,
        ∃ Kp : Submodule (MvPolynomial (Fin n) R) (LinearMap.ker π),
          r ∈ t →
            Module.Finite (MvPolynomial (Fin n) R) Kp ∧
              Kp.localized
                (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R)
                  r.asIdeal.primeCompl) = ⊤ := by
    intro r
    by_cases hr : r ∈ t
    · refine ⟨Classical.choose (hprime r hr), ?_⟩
      intro _
      exact Classical.choose_spec (hprime r hr)
    · refine ⟨⊥, ?_⟩
      intro hr'
      exact (hr hr').elim
  let Kfun : PrimeSpectrum R → Submodule (MvPolynomial (Fin n) R) (LinearMap.ker π) :=
    fun r ↦ Classical.choose (hprime_all r)
  have hKfun_finite :
      ∀ r ∈ t, Module.Finite (MvPolynomial (Fin n) R) (Kfun r) := by
    intro r hr
    -- On the chosen family, `Kfun r` is exactly the single-prime denominator-clearing witness.
    exact (Classical.choose_spec (hprime_all r) hr).1
  have hKfun_localized :
      ∀ r ∈ t,
        (Kfun r).localized
          (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) r.asIdeal.primeCompl) = ⊤ := by
    intro r hr
    -- The same chosen witness also has full localization at `r`.
    exact (Classical.choose_spec (hprime_all r) hr).2
  let K0 : Submodule (MvPolynomial (Fin n) R) (LinearMap.ker π) :=
    t.sup (α := Submodule (MvPolynomial (Fin n) R) (LinearMap.ker π))
      Kfun
  refine ⟨K0, ?_, ?_⟩
  · -- The enlarged denominator is finite because it is a finite supremum of finite summands.
    refine moduleFinite_finset_sup
      (A := MvPolynomial (Fin n) R)
      (N := LinearMap.ker π)
      t
      Kfun
      hKfun_finite
  · intro r hr
    -- Route correction: do not compute localization of the finite supremum; use monotonicity from
    -- `K_r ≤ K₀` and the already known equality `K_r.localized = ⊤`.
    apply top_unique
    rw [← hKfun_localized r hr]
    refine localized_submodule_mono
      (U := Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) r.asIdeal.primeCompl) ?_
    simpa [K0] using (Finset.le_sup (s := t) (f := Kfun) hr)

/-- Helper for Lemma 15.25.1: after mapping a denominator-clearing submodule of `ker π` into the
fixed finite free cover, localizing recovers the full kernel of the localized cover. This is the
owner-normalization step needed before comparing the quotient model with the localized target. -/
lemma localized_map_subtype_image_eq_map_localized_kernel
    {m : ℕ}
    (π : (Fin m → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (p : PrimeSpectrum R)
    (K0 : Submodule (MvPolynomial (Fin n) R) (LinearMap.ker π)) :
    let U :
        Submonoid (MvPolynomial (Fin n) R) :=
      Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
    let K : Submodule (MvPolynomial (Fin n) R) (Fin m → MvPolynomial (Fin n) R) :=
      K0.map (LinearMap.ker π).subtype
    Submodule.localized (p := U) K =
      (Submodule.localized (p := U) K0).map (LocalizedModule.map U (LinearMap.ker π).subtype) := by
  let U :
      Submonoid (MvPolynomial (Fin n) R) :=
    Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
  let K : Submodule (MvPolynomial (Fin n) R) (Fin m → MvPolynomial (Fin n) R) :=
    K0.map (LinearMap.ker π).subtype
  -- Proof comment: unfold localization membership on both sides and keep the same localized
  -- numerator/denominator witness while switching between `K0` and its image in the ambient
  -- finite free cover.
  ext x
  constructor
  · intro hx
    change x ∈ Submodule.localized₀ U
      (LocalizedModule.mkLinearMap U (Fin m → MvPolynomial (Fin n) R)) K at hx
    rcases hx with ⟨y, hy, s, rfl⟩
    rcases hy with ⟨z, hz, rfl⟩
    refine ⟨LocalizedModule.mk z s, ?_, ?_⟩
    · change LocalizedModule.mk z s ∈ Submodule.localized₀ U
        (LocalizedModule.mkLinearMap U (LinearMap.ker π)) K0
      exact ⟨z, hz, s, by rw [IsLocalizedModule.mk_eq_mk']⟩
    · rw [LocalizedModule.map_mk]
  · rintro ⟨y, hy, rfl⟩
    change y ∈ Submodule.localized₀ U
      (LocalizedModule.mkLinearMap U (LinearMap.ker π)) K0 at hy
    rcases hy with ⟨z, hz, s, rfl⟩
    have hmap :
        ((LocalizedModule.map U (LinearMap.ker π).subtype)
            (IsLocalizedModule.mk'
              (LocalizedModule.mkLinearMap U (LinearMap.ker π)) z s)) =
          IsLocalizedModule.mk'
            (LocalizedModule.mkLinearMap U (Fin m → MvPolynomial (Fin n) R))
            ((LinearMap.ker π).subtype z) s := by
      simpa [LocalizedModule.map] using
        (IsLocalizedModule.map_mk'
          (S := U)
          (f := LocalizedModule.mkLinearMap U (LinearMap.ker π))
          (f' := LocalizedModule.mkLinearMap U (Fin m → MvPolynomial (Fin n) R))
          (g := (LinearMap.ker π).subtype)
          z s)
    rw [hmap]
    change IsLocalizedModule.mk'
        (LocalizedModule.mkLinearMap U (Fin m → MvPolynomial (Fin n) R))
        ((LinearMap.ker π).subtype z) s ∈ Submodule.localized₀ U
      (LocalizedModule.mkLinearMap U (Fin m → MvPolynomial (Fin n) R)) K
    exact ⟨(LinearMap.ker π).subtype z, ⟨z, hz, rfl⟩, s, rfl⟩

/-- Helper for Lemma 15.25.1: localizing the kernel inclusion identifies its image with the
kernel of the localized cover. This isolates the stable owner comparison needed in the quotient
model argument. -/
lemma localized_kernel_subtype_range_eq_ker_localized_cover
    {m : ℕ}
    (π : (Fin m → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (p : PrimeSpectrum R) :
    let U :
        Submonoid (MvPolynomial (Fin n) R) :=
      Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
    LinearMap.range (LocalizedModule.map U (LinearMap.ker π).subtype) =
      LinearMap.ker (LocalizedModule.map U π) := by
  let U :
      Submonoid (MvPolynomial (Fin n) R) :=
    Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
  let ι :
      LocalizedModule U (LinearMap.ker π) →ₗ[Localization U]
        LocalizedModule U (Fin m → MvPolynomial (Fin n) R) :=
    LocalizedModule.map U (LinearMap.ker π).subtype
  have hrange₀ :
      (((LinearMap.restrictScalars (MvPolynomial (Fin n) R) ι).range :
          Submodule (MvPolynomial (Fin n) R)
            (LocalizedModule U (Fin m → MvPolynomial (Fin n) R)))) =
        (Submodule.localized₀ U
          (LocalizedModule.mkLinearMap U (Fin m → MvPolynomial (Fin n) R))
          (LinearMap.ker π) :
            Submodule (MvPolynomial (Fin n) R)
              (LocalizedModule U (Fin m → MvPolynomial (Fin n) R))) := by
    -- Proof comment: the localized image of the kernel inclusion is exactly the localized copy of
    -- the original kernel submodule inside the localized free module.
    simpa [ι, Submodule.range_subtype] using
      (LinearMap.range_localizedMap_eq_localized₀_range
        (p := U)
        (f := LocalizedModule.mkLinearMap U (LinearMap.ker π))
        (f' := LocalizedModule.mkLinearMap U (Fin m → MvPolynomial (Fin n) R))
        (g := (LinearMap.ker π).subtype))
  have hrange :
      ι.range = Submodule.localized (p := U) (LinearMap.ker π) := by
    -- Proof comment: `Submodule.localized` and `localized₀` have the same carrier; the previous
    -- range computation therefore upgrades directly to an equality of `Localization U`-submodules.
    ext x
    change x ∈ (((LinearMap.restrictScalars (MvPolynomial (Fin n) R) ι).range :
        Submodule (MvPolynomial (Fin n) R)
          (LocalizedModule U (Fin m → MvPolynomial (Fin n) R))) : Set
          (LocalizedModule U (Fin m → MvPolynomial (Fin n) R))) ↔
      x ∈ (Submodule.localized₀ U
        (LocalizedModule.mkLinearMap U (Fin m → MvPolynomial (Fin n) R))
        (LinearMap.ker π) :
          Submodule (MvPolynomial (Fin n) R)
            (LocalizedModule U (Fin m → MvPolynomial (Fin n) R)))
    simpa [Submodule.localized] using congrArg (fun P ↦ x ∈ P) hrange₀
  have hker :
      Submodule.localized (p := U) (LinearMap.ker π) =
        LinearMap.ker (LocalizedModule.map U π) := by
    -- Proof comment: localizing commutes with taking the kernel of the fixed finite free cover.
    simpa [Submodule.localized] using
      (LinearMap.localized'_ker_eq_ker_localizedMap
        (S := Localization U)
        (p := U)
        (f := LocalizedModule.mkLinearMap U (Fin m → MvPolynomial (Fin n) R))
        (f' := LocalizedModule.mkLinearMap U M)
        (g := π))
  calc
    LinearMap.range ι = Submodule.localized (p := U) (LinearMap.ker π) := hrange
    _ = LinearMap.ker (LocalizedModule.map U π) := hker

/-- Helper for Lemma 15.25.1: the inverse localized quotient comparison sends a localized quotient
generator to the quotient class of the corresponding localized generator. This is the concrete
computation used when comparing the explicit localized quotient-model map with the canonical
quotient/localization equivalence. -/
lemma localizedQuotientEquiv_symm_apply_mk
    {A : Type*} [CommRing A]
    {X : Type*} [AddCommGroup X] [Module A X]
    (U : Submonoid A) (K : Submodule A X) (x : X) :
    (localizedQuotientEquiv U K).symm (LocalizedModule.mk (Submodule.Quotient.mk x) (1 : U)) =
      Submodule.Quotient.mk (LocalizedModule.mk x (1 : U)) := by
  change
    (IsLocalizedModule.iso U
      (Submodule.toLocalizedQuotient' (Localization U) U
        (LocalizedModule.mkLinearMap U X) K))
      ((IsLocalizedModule.iso U (LocalizedModule.mkLinearMap U (X ⧸ K))).symm
        (LocalizedModule.mk (Submodule.Quotient.mk x) 1)) =
      _
  have hs :
      (IsLocalizedModule.iso U (LocalizedModule.mkLinearMap U (X ⧸ K))).symm
        (LocalizedModule.mk (Submodule.Quotient.mk x) 1) =
      LocalizedModule.mk (Submodule.Quotient.mk x) 1 := by
    -- Proof comment: for the canonical localization owner, the localization isomorphism fixes the
    -- standard generator `mk x 1`.
    simpa using
      (IsLocalizedModule.iso_symm_apply U
        (LocalizedModule.mkLinearMap U (X ⧸ K))
        (Submodule.Quotient.mk x))
  rw [hs]
  -- Proof comment: the quotient owner map sends a quotient generator to the quotient class of the
  -- localized generator by construction.
  simpa [Submodule.toLocalizedQuotient, Submodule.toLocalizedQuotient'_mk] using
    (IsLocalizedModule.iso_apply_mk U
      (Submodule.toLocalizedQuotient' (Localization U) U
        (LocalizedModule.mkLinearMap U X) K)
      (Submodule.Quotient.mk x) (1 : U))

lemma localized_model_submodule_eq_ker_localized_cover
    {m : ℕ}
    (π : (Fin m → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (p : PrimeSpectrum R)
    (K0 : Submodule (MvPolynomial (Fin n) R) (LinearMap.ker π))
    (hK0 :
      K0.localized
        (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl) = ⊤) :
    let U :
        Submonoid (MvPolynomial (Fin n) R) :=
      Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
    let K : Submodule (MvPolynomial (Fin n) R) (Fin m → MvPolynomial (Fin n) R) :=
      K0.map (LinearMap.ker π).subtype
    Submodule.localized (p := U) K = LinearMap.ker (LocalizedModule.map U π) := by
  let U :
      Submonoid (MvPolynomial (Fin n) R) :=
    Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
  let K : Submodule (MvPolynomial (Fin n) R) (Fin m → MvPolynomial (Fin n) R) :=
    K0.map (LinearMap.ker π).subtype
  -- Proof comment: first rewrite the localized image of `K0` in the ambient free module as the
  -- image of the localized kernel owner, then replace `K0.localized` by `⊤`, and finally use the
  -- range/kernel comparison for the localized kernel inclusion.
  calc
    Submodule.localized (p := U) K =
        (Submodule.localized (p := U) K0).map
          (LocalizedModule.map U (LinearMap.ker π).subtype) := by
            simpa [K] using
              localized_map_subtype_image_eq_map_localized_kernel
                (n := n) (R := R) (M := M) π p K0
    _ = (⊤ : Submodule (Localization U) (LocalizedModule U (LinearMap.ker π))).map
          (LocalizedModule.map U (LinearMap.ker π).subtype) := by
            rw [hK0]
    _ = LinearMap.range (LocalizedModule.map U (LinearMap.ker π).subtype) := by
          rw [Submodule.map_top]
    _ = LinearMap.ker (LocalizedModule.map U π) := by
          simpa using
            localized_kernel_subtype_range_eq_ker_localized_cover
              (n := n) (R := R) (M := M) π p

/-- Helper for Lemma 15.25.1: once the chosen denominator fills the localized kernel of the fixed
free cover, the corresponding localized quotient model is canonically the localized target. -/
noncomputable def localized_quotient_model_linearEquiv_at_family_prime
    {m : ℕ}
    (π : (Fin m → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (hπ : Function.Surjective π)
    (p : PrimeSpectrum R)
    (K0 : Submodule (MvPolynomial (Fin n) R) (LinearMap.ker π))
    (hK0 :
      K0.localized
        (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl) = ⊤) :
    let U :
        Submonoid (MvPolynomial (Fin n) R) :=
      Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
    let K : Submodule (MvPolynomial (Fin n) R) (Fin m → MvPolynomial (Fin n) R) :=
      K0.map (LinearMap.ker π).subtype
    let N := (Fin m → MvPolynomial (Fin n) R) ⧸ K
    LocalizedModule U N ≃ₗ[Localization U] LocalizedModule U M := by
  let U :
      Submonoid (MvPolynomial (Fin n) R) :=
    Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
  let K : Submodule (MvPolynomial (Fin n) R) (Fin m → MvPolynomial (Fin n) R) :=
    K0.map (LinearMap.ker π).subtype
  let N := (Fin m → MvPolynomial (Fin n) R) ⧸ K
  let πU :
      LocalizedModule U (Fin m → MvPolynomial (Fin n) R) →ₗ[Localization U]
        LocalizedModule U M :=
    LocalizedModule.map U π
  have hπU : Function.Surjective πU := by
    -- Proof comment: localizing the fixed finite free cover preserves surjectivity.
    simpa [U, πU] using
      localized_cover_surjective_at_prime
        (n := n) (R := R) (M := M) π hπ p
  -- Proof comment: localize the quotient, rewrite the localized denominator to the localized
  -- kernel, and then apply the standard quotient-by-kernel equivalence for the localized cover.
  exact
    (localizedQuotientEquiv U K).symm.trans <|
      (Submodule.quotEquivOfEq _ _
        (localized_model_submodule_eq_ker_localized_cover
          (n := n) (R := R) (M := M) π p K0 hK0)).trans <|
        (LinearMap.quotKerEquivOfSurjective πU hπU)

/-- Helper for Lemma 15.25.1: after localizing at a prime where the descended denominator
submodule becomes the full localized kernel of the fixed finite free cover, the localized quotient
model map itself is bijective. This separates the genuine map-level input from the later
base-prime/away owner transport. -/
lemma localized_quotient_model_map_bijective_at_detecting_prime
    {m : ℕ}
    (π : (Fin m → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (hπ : Function.Surjective π)
    (p : PrimeSpectrum R)
    (K : Submodule (MvPolynomial (Fin n) R) (Fin m → MvPolynomial (Fin n) R))
    (hKle : K ≤ LinearMap.ker π)
    (hKloc :
      let U :
          Submonoid (MvPolynomial (Fin n) R) :=
        Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
      Submodule.localized (p := U) K = LinearMap.ker (LocalizedModule.map U π)) :
    let U :
        Submonoid (MvPolynomial (Fin n) R) :=
      Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
    let φ :
        ((Fin m → MvPolynomial (Fin n) R) ⧸ K) →ₗ[MvPolynomial (Fin n) R] M :=
      Submodule.liftQ K π hKle
    Function.Bijective (LocalizedModule.map U φ) := by
  let U :
      Submonoid (MvPolynomial (Fin n) R) :=
    Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
  let F := Fin m → MvPolynomial (Fin n) R
  let φ :
      (F ⧸ K) →ₗ[MvPolynomial (Fin n) R] M :=
    Submodule.liftQ K π hKle
  let πU :
      LocalizedModule U F →ₗ[Localization U] LocalizedModule U M :=
    LocalizedModule.map U π
  let φU :
      (LocalizedModule U F ⧸ Submodule.localized (p := U) K) →ₗ[Localization U]
        LocalizedModule U M :=
    Submodule.liftQ (Submodule.localized (p := U) K) πU <| by
      simpa [hKloc] using
        (show Submodule.localized (p := U) K ≤ Submodule.localized (p := U) K from le_rfl)
  have hπU : Function.Surjective πU := by
    -- Proof comment: the localized free cover remains surjective at the chosen prime.
    simpa [U, πU] using
      localized_cover_surjective_at_prime
        (n := n) (R := R) (M := M) π hπ p
  have hφUinj : Function.Injective φU := by
    -- Proof comment: the quotient lift becomes injective once the localized denominator agrees
    -- with the kernel of the localized cover.
    refine LinearMap.ker_eq_bot.mp ?_
    refine Submodule.ker_liftQ_eq_bot (p := Submodule.localized (p := U) K) πU ?_ ?_
    · simpa [hKloc] using
        (show Submodule.localized (p := U) K ≤ Submodule.localized (p := U) K from le_rfl)
    · simpa [hKloc] using
        (show LinearMap.ker πU ≤ LinearMap.ker πU from le_rfl)
  have hφUsurj : Function.Surjective φU := by
    -- Proof comment: surjectivity of the localized cover descends to the quotient by the
    -- localized denominator via quotient representatives.
    intro z
    rcases hπU z with ⟨y, rfl⟩
    refine ⟨Submodule.mkQ (Submodule.localized (p := U) K) y, ?_⟩
    simp [φU, Submodule.liftQ_apply]
  let eQuot :
      LocalizedModule U (F ⧸ K) ≃ₗ[Localization U]
        (LocalizedModule U F ⧸ Submodule.localized (p := U) K) :=
    (localizedQuotientEquiv U K).symm
  have hfactor :
      φU.comp eQuot.toLinearMap = LocalizedModule.map U φ := by
    -- Proof comment: both localized quotient-model maps agree on the standard localized quotient
    -- generators, hence they agree everywhere by the localization universal property.
    have hfactorR :
        (LinearMap.restrictScalars (MvPolynomial (Fin n) R)
          (φU.comp eQuot.toLinearMap)).comp
            (LocalizedModule.mkLinearMap U (F ⧸ K)) =
          (LinearMap.restrictScalars (MvPolynomial (Fin n) R)
            (LocalizedModule.map U φ)).comp
              (LocalizedModule.mkLinearMap U (F ⧸ K)) := by
      ext x
      rcases (Submodule.mkQ_surjective K x) with ⟨y, rfl⟩
      change φU (eQuot (LocalizedModule.mk (Submodule.Quotient.mk y) 1)) =
        (LocalizedModule.map U φ) (LocalizedModule.mk (Submodule.Quotient.mk y) 1)
      rw [localizedQuotientEquiv_symm_apply_mk]
      simp [eQuot, φU, φ, LocalizedModule.map_mk, Submodule.liftQ_apply,
        Submodule.liftQ_mkQ]
    have hfactorR' :
        LinearMap.restrictScalars (MvPolynomial (Fin n) R)
          (φU.comp eQuot.toLinearMap) =
        LinearMap.restrictScalars (MvPolynomial (Fin n) R)
          (LocalizedModule.map U φ) := by
      exact
        IsLocalizedModule.linearMap_ext
          (S := U)
          (LocalizedModule.mkLinearMap U (F ⧸ K))
          (LocalizedModule.mkLinearMap U M)
          hfactorR
    ext x
    exact congrArg (fun f ↦ f x) hfactorR'
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply eQuot.injective
    apply hφUinj
    simpa [hfactor, LinearMap.comp_apply] using hxy
  · intro z
    rcases hφUsurj z with ⟨w, rfl⟩
    refine ⟨eQuot.symm w, ?_⟩
    simpa [hfactor] using rfl

/-- Helper for Lemma 15.25.1: the denominator-cleared kernel submodule defines a quotient model
of the fixed finite free cover which still surjects onto `M`, and that quotient model is already
finitely presented. -/
lemma quotient_model_descends_cover
    {m : ℕ}
    (π : (Fin m → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (hπ : Function.Surjective π)
    (K0 : Submodule (MvPolynomial (Fin n) R) (LinearMap.ker π))
    [Module.Finite (MvPolynomial (Fin n) R) K0] :
    let K : Submodule (MvPolynomial (Fin n) R) (Fin m → MvPolynomial (Fin n) R) :=
      K0.map (LinearMap.ker π).subtype
    let N := (Fin m → MvPolynomial (Fin n) R) ⧸ K
    ∃ φ : N →ₗ[MvPolynomial (Fin n) R] M,
      Function.Surjective φ ∧ Module.FinitePresentation (MvPolynomial (Fin n) R) N := by
  let K : Submodule (MvPolynomial (Fin n) R) (Fin m → MvPolynomial (Fin n) R) :=
    K0.map (LinearMap.ker π).subtype
  have hKle : K ≤ LinearMap.ker π := by
    -- Proof comment: every element of `K` comes from the chosen finite denominator submodule
    -- inside `ker π`, so its image under `π` is zero.
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact y.2
  let N : Type _ := (Fin m → MvPolynomial (Fin n) R) ⧸ K
  let φ : N →ₗ[MvPolynomial (Fin n) R] M := Submodule.liftQ K π hKle
  have hφsurj : Function.Surjective φ := by
    -- Proof comment: choose a representative in the original finite free cover and evaluate the
    -- quotient lift on its class.
    intro x
    rcases hπ x with ⟨y, rfl⟩
    refine ⟨Submodule.mkQ K y, ?_⟩
    have hcomp : φ.comp (Submodule.mkQ K) = π := by
      ext z
      rw [← LinearMap.comp_apply, Submodule.liftQ_mkQ]
    exact LinearMap.congr_fun hcomp y
  have hKfg : K.FG := by
    -- Proof comment: finite generation passes through the inclusion of `K0` into the ambient
    -- finite free cover.
    let hK0fg : K0.FG := Submodule.FG.of_finite
    simpa [K] using hK0fg.map (LinearMap.ker π).subtype
  have hNfp : Module.FinitePresentation (MvPolynomial (Fin n) R) N := by
    -- Proof comment: the quotient of a finite free module by a finitely generated submodule is
    -- finitely presented.
    exact Module.finitePresentation_of_surjective K.mkQ K.mkQ_surjective <| by
      show (LinearMap.ker K.mkQ).FG
      simpa [Submodule.ker_mkQ] using hKfg
  exact ⟨φ, hφsurj, hNfp⟩

/-- Helper for Lemma 15.25.1: once every prime of `Spec R[x₁, …, xₙ]` has a principal-open
neighborhood on which `M` is finitely presented, the standard cover criterion from
Lemma `10.23.2` gives the global finite-presentation conclusion. -/
lemma finitePresentation_of_primewise_localizationAway
    (haway :
      ∀ q : PrimeSpectrum (MvPolynomial (Fin n) R),
        ∃ g : MvPolynomial (Fin n) R, g ∉ q.asIdeal ∧
          Module.FinitePresentation (Localization.Away g) (LocalizedModule.Away g M)) :
    Module.FinitePresentation (MvPolynomial (Fin n) R) M := by
  let good : Set (MvPolynomial (Fin n) R) :=
    { g | Module.FinitePresentation (Localization.Away g) (LocalizedModule.Away g M) }
  have hspan : Ideal.span good = ⊤ := by
    -- If the good elements failed to generate the unit ideal, some maximal ideal would contain
    -- them all, contradicting the chosen principal-open neighborhood at the corresponding point.
    by_contra htop
    obtain ⟨m, hmmax, hspanm⟩ := Ideal.exists_le_maximal (Ideal.span good) htop
    let q : PrimeSpectrum (MvPolynomial (Fin n) R) := ⟨m, hmmax.isPrime⟩
    obtain ⟨g, hgq, hfg⟩ := haway q
    have hgood : g ∈ good := hfg
    have hgm : g ∈ m := (Ideal.span_le.1 hspanm) hgood
    exact hgq hgm
  obtain ⟨s, hsgood, hstop⟩ := (Ideal.span_eq_top_iff_finite good).mp hspan
  -- Apply the standard finite principal-open descent theorem to the finite subcover.
  refine module_finitePresentation_of_localizationAway (R := MvPolynomial (Fin n) R)
    (M := M) s hstop ?_
  intro g
  exact hsgood g.2

/-- Helper for Lemma 15.25.1: if `p` is the contraction of a prime `q` of the polynomial ring,
then the polynomial localization submonoid coming from `p.asIdeal.primeCompl` is disjoint from
`q`. This is the spectrum-side witness needed to lift `q` to a prime of `Localization U`. -/
lemma comap_prime_disjoint_algebraMapSubmonoid
    (q : PrimeSpectrum (MvPolynomial (Fin n) R)) :
    let p : PrimeSpectrum R :=
      PrimeSpectrum.comap (algebraMap R (MvPolynomial (Fin n) R)) q
    Disjoint
      (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl :
        Set (MvPolynomial (Fin n) R))
      q.asIdeal := by
  let p : PrimeSpectrum R :=
    PrimeSpectrum.comap (algebraMap R (MvPolynomial (Fin n) R)) q
  refine Set.disjoint_left.mpr ?_
  intro y hyU hyq
  rcases hyU with ⟨r, hr, rfl⟩
  -- Proof comment: membership of `algebraMap R S r` in `q` means exactly that `r` lies in the
  -- contracted prime `p = q ∩ R`, contradicting the choice `r ∈ p.asIdeal.primeCompl`.
  exact hr <| by
    simpa [p, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] using hyq

/-- Helper for Lemma 15.25.1: the detecting family of prime localizations defines the canonical
`R`-linear map from `R` into their finite product. Naming this map keeps the later tensor
factorization at the ring-owner level. -/
noncomputable abbrev detecting_prime_localization_ring_linearMap
    (s : Finset (PrimeSpectrum R)) :
    R →ₗ[R] ∀ p : s, Localization.AtPrime p.1.asIdeal :=
  LinearMap.pi fun p : s ↦ Algebra.linearMap R (Localization.AtPrime p.1.asIdeal)

/-- Helper for Lemma 15.25.1: after tensoring with an `R`-module, the product of prime-localized
rings becomes the product of the corresponding prime-localized modules. This is the tensor-side
owner rewrite behind the detecting-family argument. -/
noncomputable abbrev detecting_prime_localization_codomain_linearEquiv
    {X : Type*} [AddCommGroup X] [Module R X]
    (s : Finset (PrimeSpectrum R)) :
    X ⊗[R] (∀ p : s, Localization.AtPrime p.1.asIdeal) ≃ₗ[R]
      ∀ p : s, LocalizedModule.AtPrime p.1.asIdeal X :=
  -- Proof comment: first split the tensor with the finite product into a product of tensors, then
  -- rewrite each factor by the standard tensor/localization equivalence for prime localization.
  (TensorProduct.piRight R R X (fun p : s ↦ Localization.AtPrime p.1.asIdeal)) ≪≫ₗ
    LinearEquiv.piCongrRight fun p : s ↦
      TensorProduct.comm R X (Localization.AtPrime p.1.asIdeal) ≪≫ₗ
        ((LocalizedModule.equivTensorProduct p.1.asIdeal.primeCompl X).symm.restrictScalars R)

/-- Helper for Lemma 15.25.1: on a generator `x ⊗ 1`, the tensor/product comparison is exactly
the canonical family of prime-localization maps. This is the concrete computation used to identify
the flat tensor factorization with the map whose injectivity we need. -/
lemma detecting_prime_localization_codomain_linearEquiv_tmul_one_apply
    {X : Type*} [AddCommGroup X] [Module R X]
    (s : Finset (PrimeSpectrum R)) (x : X) :
    (detecting_prime_localization_codomain_linearEquiv (R := R) (X := X) s)
        (x ⊗ₜ[R] (fun p : s ↦ (1 : Localization.AtPrime p.1.asIdeal))) =
      fun p : s ↦ LocalizedModule.mk x (1 : p.1.asIdeal.primeCompl) := by
  classical
  -- Proof comment: evaluate the product comparison coordinatewise and then use the standard
  -- tensor/localization formula for the inverse equivalence on the pure tensor `1 ⊗ x`.
  ext p
  simp [detecting_prime_localization_codomain_linearEquiv,
    LocalizedModule.equivTensorProduct_symm_apply_tmul_one]

/-- Helper for Lemma 15.25.1: the canonical map from a flat module into the product of the chosen
prime localizations factors as tensoring the detecting-family ring map, followed by the standard
tensor/product comparison. This isolates the flatness input from the localization bookkeeping. -/
lemma detecting_prime_localization_map_eq_tensor_factor
    {X : Type*} [AddCommGroup X] [Module R X]
    (s : Finset (PrimeSpectrum R)) :
    (detecting_prime_localization_codomain_linearEquiv (R := R) (X := X) s).toLinearMap.comp
        (LinearMap.lTensor X (detecting_prime_localization_ring_linearMap (R := R) s)).comp
        (Algebra.TensorProduct.rid R R X).symm.toLinearMap =
      LinearMap.pi
        (fun p : s ↦
          (LocalizedModule.mkLinearMap p.1.asIdeal.primeCompl X :
            X →ₗ[R] LocalizedModule.AtPrime p.1.asIdeal X)) := by
  -- Proof comment: both maps are `R`-linear, so it is enough to evaluate them on `x : X`; after
  -- `TensorProduct.rid`, the source is exactly the generator `x ⊗ 1`.
  ext x p
  simpa [LinearMap.comp_apply, detecting_prime_localization_ring_linearMap,
    TensorProduct.rid_symm_apply] using
    congrArg (fun y ↦ y p)
      (detecting_prime_localization_codomain_linearEquiv_tmul_one_apply
        (R := R) (X := X) s x)

/-- Helper for Lemma 15.25.1: if a finite family of prime localizations detects equality in `R`,
then tensoring that family map with any flat `R`-module gives an injective map into the product of
the corresponding prime-localized modules. This is the source-faithful detecting-family step used
to kill the away-local kernel. -/
lemma detecting_family_localization_map_injective_of_flat
    {X : Type*} [AddCommGroup X] [Module R X] [Module.Flat R X]
    (s : Finset (PrimeSpectrum R))
    (hsinj :
      Function.Injective
        (fun r : R ↦ fun p : s ↦ algebraMap R (Localization.AtPrime p.1.asIdeal) r)) :
    Function.Injective
      ⇑(LinearMap.pi fun p : s ↦
          (LocalizedModule.mkLinearMap p.1.asIdeal.primeCompl X :
            X →ₗ[R] LocalizedModule.AtPrime p.1.asIdeal X)) := by
  let f :
      R →ₗ[R] ∀ p : s, Localization.AtPrime p.1.asIdeal :=
    detecting_prime_localization_ring_linearMap (R := R) s
  let fTensor :
      X ⊗[R] R →ₗ[R] X ⊗[R] ∀ p : s, Localization.AtPrime p.1.asIdeal :=
    LinearMap.lTensor X f
  let eDom : X ≃ₗ[R] X ⊗[R] R :=
    (Algebra.TensorProduct.rid R R X).symm
  let eCod :
      X ⊗[R] ∀ p : s, Localization.AtPrime p.1.asIdeal ≃ₗ[R]
        ∀ p : s, LocalizedModule.AtPrime p.1.asIdeal X :=
    detecting_prime_localization_codomain_linearEquiv (R := R) (X := X) s
  have hf : Function.Injective f := hsinj
  have hfTensor : Function.Injective fTensor := by
    simpa [fTensor] using
      (Module.Flat.lTensor_preserves_injective_linearMap (M := X) f hf)
  intro x y hxy
  have hcomp :
      (eCod.toLinearMap.comp fTensor.comp eDom.toLinearMap) x =
        (eCod.toLinearMap.comp fTensor.comp eDom.toLinearMap) y := by
    simpa [f, fTensor, eDom, eCod, LinearMap.comp_apply,
      detecting_prime_localization_map_eq_tensor_factor (R := R) (X := X) s] using hxy
  have hTensorEq : fTensor (eDom x) = fTensor (eDom y) := by
    apply eCod.injective
    simpa [LinearMap.comp_apply] using hcomp
  exact eDom.injective (hfTensor hTensorEq)

/-- Helper for Lemma 15.25.1: a flat module is zero once a detecting finite family of prime
localizations all vanish. This packages the previous injectivity statement into the exact
subsingleton form used in the theorem. -/
lemma subsingleton_of_detecting_prime_localizations_of_flat
    {X : Type*} [AddCommGroup X] [Module R X] [Module.Flat R X]
    (s : Finset (PrimeSpectrum R))
    (hsinj :
      Function.Injective
        (fun r : R ↦ fun p : s ↦ algebraMap R (Localization.AtPrime p.1.asIdeal) r))
    (hsub : ∀ p : s, Subsingleton (LocalizedModule.AtPrime p.1.asIdeal X)) :
    Subsingleton X := by
  let f :
      X →ₗ[R] ∀ p : s, LocalizedModule.AtPrime p.1.asIdeal X :=
    LinearMap.pi fun p : s ↦ LocalizedModule.mkLinearMap p.1.asIdeal.primeCompl X
  have hf :
      Function.Injective f :=
    detecting_family_localization_map_injective_of_flat (R := R) (X := X) s hsinj
  refine ⟨fun x y ↦ hf ?_⟩
  ext p
  exact Subsingleton.elim _ _

/-- Helper for Lemma 15.25.1: localizing a localized module at a prime of `Localization U`
agrees with localizing the original module at the contracted prime, first over the owner ring
`Localization U`. -/
noncomputable def localized_atPrime_linearEquiv_over_localized_base
    {A : Type*} [CommRing A]
    {X : Type*} [AddCommGroup X] [Module A X]
    (U : Submonoid A) (qU : PrimeSpectrum (Localization U)) :
    LocalizedModule.AtPrime qU.asIdeal (LocalizedModule U X) ≃ₗ[Localization U]
      LocalizedModule.AtPrime
        (PrimeSpectrum.comap (algebraMap A (Localization U)) qU).asIdeal X := by
  -- Route correction: reuse the Chapter 15 owner for iterated localization instead of rebuilding
  -- the scalar-tower and `IsLocalizedModule` data locally in this file.
  simpa using
    localized_atPrime_linearEquiv_over_isLocalization_target
      (A := A) (S₀ := Localization U) (X := X) U qU

/-- Helper for Lemma 15.25.1: the prime of `Localization U` corresponding to a disjoint prime
`q` of `A` contracts back to `q`. This isolates the spectrum-homeomorphism rewrite used in the
iterated-localization comparison. -/
lemma comap_lifted_localization_prime_eq
    {A : Type*} [CommRing A]
    (U : Submonoid A) {q : PrimeSpectrum A}
    (hq : Disjoint (U : Set A) q.asIdeal) :
    PrimeSpectrum.comap (algebraMap A (Localization U))
      ((primeSpectrum_localization_homeomorph U).symm ⟨q, hq⟩) = q := by
  -- Proof comment: this is exactly the `symm_apply_apply` identity of the localization-spectrum
  -- homeomorphism, viewed after forgetting the disjointness witness.
  simpa using congrArg Subtype.val
    ((primeSpectrum_localization_homeomorph U).apply_symm_apply ⟨q, hq⟩)

/-- Helper for Lemma 15.25.1: after choosing the lifted prime of `Localization U`, the iterated
localization is canonically the same as localizing the original module at the original prime. -/
noncomputable def localized_atPrime_linearEquiv
    {A : Type*} [CommRing A]
    {X : Type*} [AddCommGroup X] [Module A X]
    (U : Submonoid A) {q : PrimeSpectrum A}
    (hq : Disjoint (U : Set A) q.asIdeal) :
    let qU : PrimeSpectrum (Localization U) :=
      (primeSpectrum_localization_homeomorph U).symm ⟨q, hq⟩
    LocalizedModule.AtPrime qU.asIdeal (LocalizedModule U X) ≃ₗ[Localization U]
      LocalizedModule.AtPrime q.asIdeal X := by
  -- Proof comment: instantiate the previous comparison at the lifted prime of `Localization U`
  -- and rewrite its contraction back to the original prime using the localization-spectrum
  -- homeomorphism.
  let qU : PrimeSpectrum (Localization U) :=
    (primeSpectrum_localization_homeomorph U).symm ⟨q, hq⟩
  have hcomap : PrimeSpectrum.comap (algebraMap A (Localization U)) qU = q := by
    -- The lifted prime maps back to the original one by the localization-spectrum homeomorphism.
    simpa [qU] using comap_lifted_localization_prime_eq (A := A) U hq
  simpa [qU, hcomap] using
    localized_atPrime_linearEquiv_over_localized_base (A := A) (X := X) U qU

/-- Helper for Lemma 15.25.1: localizing the localized model equivalence at the lifted prime and
normalizing the iterated localization yields the required stalk comparison over the original base
ring. -/
noncomputable def atPrime_localization_model_linearEquiv
    {A : Type*} [CommRing A]
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [Module A X] [Module A Y]
    (U : Submonoid A) {q : PrimeSpectrum A}
    (hq : Disjoint (U : Set A) q.asIdeal)
    (eU : LocalizedModule U X ≃ₗ[Localization U] LocalizedModule U Y) :
    LocalizedModule.AtPrime q.asIdeal X ≃ₗ[A]
      LocalizedModule.AtPrime q.asIdeal Y := by
  -- Proof comment: localize the source-side equivalence at the lifted prime of `Localization U`
  -- before comparing both iterated localizations back with the original `q`-stalks.
  let qU : PrimeSpectrum (Localization U) :=
    (primeSpectrum_localization_homeomorph U).symm ⟨q, hq⟩
  let eSourceAtPrime :
      LocalizedModule.AtPrime qU.asIdeal (LocalizedModule U X) ≃ₗ[Localization U]
        LocalizedModule.AtPrime q.asIdeal X :=
    localized_atPrime_linearEquiv (A := A) (X := X) U hq
  let eTargetAtPrime :
      LocalizedModule.AtPrime qU.asIdeal (LocalizedModule U Y) ≃ₗ[Localization U]
        LocalizedModule.AtPrime q.asIdeal Y :=
    localized_atPrime_linearEquiv (A := A) (X := Y) U hq
  let eLocalized :
      LocalizedModule.AtPrime qU.asIdeal (LocalizedModule U X) ≃ₗ[Localization U]
        LocalizedModule.AtPrime qU.asIdeal (LocalizedModule U Y) :=
    (LinearEquiv.extendScalarsOfIsLocalization qU.asIdeal.primeCompl
      (Localization.AtPrime qU.asIdeal) eU).restrictScalars (Localization U)
  -- Proof comment: after all three equivalences are linear over `Localization U`, restrict scalars
  -- along `A → Localization U` to recover the advertised `A`-linear stalk comparison.
  exact ((eSourceAtPrime.symm.trans eLocalized).trans eTargetAtPrime).restrictScalars A

/-- Helper for Lemma 15.25.1: once the source-faithful missing transport supplies a stalk
comparison `N_q ≃ M_q`, flatness of `M_q` immediately puts `q` in the flat-over-base locus of the
model module `N`. This isolates the post-transport step from the still-missing iterated
localization rewrite. -/
lemma mem_flatOverBaseLocus_of_atPrime_linearEquiv
    {N : Type*} [AddCommGroup N]
    [Module (MvPolynomial (Fin n) R) N] [Module R N]
    [IsScalarTower R (MvPolynomial (Fin n) R) N]
    (q : PrimeSpectrum (MvPolynomial (Fin n) R))
    (eAtPrime :
      LocalizedModule.AtPrime q.asIdeal N ≃ₗ[R]
        LocalizedModule.AtPrime q.asIdeal M)
    (hqflat : Module.Flat R (LocalizedModule.AtPrime q.asIdeal M)) :
    q ∈ Module.flatOverBaseLocus R (MvPolynomial (Fin n) R) N := by
  letI : Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) := hqflat
  have hmodelFlat :
      Module.Flat R (LocalizedModule.AtPrime q.asIdeal N) := by
    -- Proof comment: after the missing transport, flatness transfers across the stalk equivalence.
    exact Module.Flat.of_linearEquiv eAtPrime
  -- Proof comment: membership in `flatOverBaseLocus` is exactly flatness of the local module.
  exact (Module.mem_flatOverBaseLocus R (MvPolynomial (Fin n) R) N q).2 hmodelFlat

/-- Helper for Lemma 15.25.1: once the localized quotient-model map is surjective on `D(g)` and
the source model is flat there, the away-localized kernel is flat over the base ring. This is the
short-exact-sequence step in the source proof before the detecting-family vanishing argument. -/
lemma away_localized_kernel_flat
    {N : Type*} [AddCommGroup N]
    [Module (MvPolynomial (Fin n) R) N] [Module R N]
    [IsScalarTower R (MvPolynomial (Fin n) R) N]
    [Module.FinitePresentation (MvPolynomial (Fin n) R) N]
    (φ : N →ₗ[MvPolynomial (Fin n) R] M)
    (hφsurj : Function.Surjective φ)
    (g : MvPolynomial (Fin n) R)
    (hbasic :
      (basicOpen g : Set (PrimeSpectrum (MvPolynomial (Fin n) R))) ⊆
        Module.flatOverBaseLocus R (MvPolynomial (Fin n) R) N) :
    Module.Flat R (LinearMap.ker (LocalizedModule.map (Submonoid.powers g) φ)) := by
  let ψ :
      LocalizedModule.Away g N →ₗ[Localization.Away g]
        LocalizedModule.Away g M :=
    LocalizedModule.map (Submonoid.powers g) φ
  let ψR :
      LocalizedModule.Away g N →ₗ[R]
        LocalizedModule.Away g M :=
    ψ.restrictScalars R
  have hψRsurj : Function.Surjective ψR := by
    -- Proof comment: surjectivity survives the away localization, and restricting scalars does
    -- not change the underlying function.
    simpa [ψR, ψ] using
      (LocalizedModule.map_surjective (Submonoid.powers g) φ hφsurj)
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.moduleCatMk (LinearMap.ker ψR).subtype ψR (by
      ext x
      simpa [LinearMap.mem_ker] using x.2)
  have hS : S.ShortExact := by
    -- Proof comment: package the kernel inclusion and the away-localized quotient map into the
    -- standard short exact sequence `0 → ker ψ_g → N_g → M_g → 0`.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      simpa using (LinearMap.exact_subtype_ker_map ψR)
    · exact (ModuleCat.mono_iff_injective _).2 (LinearMap.ker ψR).injective_subtype
    · exact (ModuleCat.epi_iff_surjective _).2 hψRsurj
  letI : Module.Flat R (LocalizedModule.Away g N) :=
    flat_localizedAway_of_basicOpen_subset_flatOverBaseLocus
      (A := R) (T := MvPolynomial (Fin n) R) (N := N) g hbasic
  letI : Module.Flat R (LocalizedModule.Away g M) := by
    infer_instance
  have hkerFlatR : Module.Flat R (LinearMap.ker ψR) :=
    CategoryTheory.ShortComplex.ShortExact.flat_X₁ hS
  -- Proof comment: the kernel of the restricted-scalars map is the same away-local kernel.
  simpa [ψR, ψ, LinearMap.ker_restrictScalars R ψ] using hkerFlatR

/-- Helper for Lemma 15.25.1: if the base-prime localization of the away-localized quotient-model
map is injective, then the corresponding base-prime localization of its away-local kernel is
subsingleton. This isolates the final kernel-killing step from the remaining owner transport that
identifies the actual localized away map. -/
lemma away_localized_kernel_atPrime_subsingleton_of_localized_map_injective
    {N : Type*} [AddCommGroup N]
    [Module (MvPolynomial (Fin n) R) N] [Module R N]
    [IsScalarTower R (MvPolynomial (Fin n) R) N]
    (φ : N →ₗ[MvPolynomial (Fin n) R] M)
    (g : MvPolynomial (Fin n) R)
    (r : PrimeSpectrum R)
    (hinj :
      Function.Injective
        (LocalizedModule.map r.asIdeal.primeCompl
          ((LocalizedModule.map (Submonoid.powers g) φ).restrictScalars R))) :
    Subsingleton
      (LocalizedModule.AtPrime r.asIdeal
        (LinearMap.ker (LocalizedModule.map (Submonoid.powers g) φ))) := by
  let ψ :
      LocalizedModule.Away g N →ₗ[Localization.Away g]
        LocalizedModule.Away g M :=
    LocalizedModule.map (Submonoid.powers g) φ
  let ψR :
      LocalizedModule.Away g N →ₗ[R]
        LocalizedModule.Away g M :=
    ψ.restrictScalars R
  let ι :
      LinearMap.ker ψ →ₗ[R] LocalizedModule.Away g N :=
    ((LinearMap.ker ψ).subtype).restrictScalars R
  have hi :
      Function.Injective (LocalizedModule.map r.asIdeal.primeCompl ι) := by
    -- Proof comment: localizing the kernel inclusion preserves injectivity.
    exact LocalizedModule.map_injective r.asIdeal.primeCompl ι ι.injective
  have hzero :
      ψR.comp ι = 0 := by
    -- Proof comment: the kernel inclusion is annihilated by the away-localized map by
    -- construction of `ker ψ`.
    ext x
    simpa [ψR, ψ, ι] using x.2
  have hcomp :
      (LocalizedModule.map r.asIdeal.primeCompl ψR).comp
          (LocalizedModule.map r.asIdeal.primeCompl ι) =
        0 := by
    -- Proof comment: after localizing, the same kernel-inclusion composite is still zero.
    simpa [hzero] using
      (IsLocalizedModule.map_comp
        (S := r.asIdeal.primeCompl)
        (f :=
          LocalizedModule.mkLinearMap r.asIdeal.primeCompl (LinearMap.ker ψ))
        (f' := LocalizedModule.mkLinearMap r.asIdeal.primeCompl (LocalizedModule.Away g N))
        (f'' := LocalizedModule.mkLinearMap r.asIdeal.primeCompl (LocalizedModule.Away g M))
        (g := ι)
        (g' := ψR))
  refine ⟨fun x y ↦ hi ?_⟩
  have hx :
      LocalizedModule.map r.asIdeal.primeCompl ι x = 0 := by
    -- Proof comment: injectivity of the localized away map forces every localized kernel element
    -- to map to zero under the localized kernel inclusion.
    apply hinj
    simpa using LinearMap.congr_fun hcomp x
  have hy :
      LocalizedModule.map r.asIdeal.primeCompl ι y = 0 := by
    -- Proof comment: the same argument applies to any second localized kernel element.
    apply hinj
    simpa using LinearMap.congr_fun hcomp y
  rw [hx, hy]

/-- Helper for Lemma 15.25.1: base-prime localization of a polynomial module over `R` agrees with
localization at the induced polynomial submonoid `U`. This freezes the first owner transport in
the source proof before any away-localization is introduced. -/
noncomputable def atPrime_linearEquiv_localized_polynomial_module
    {X : Type*} [AddCommGroup X]
    [Module (MvPolynomial (Fin n) R) X] [Module R X]
    [IsScalarTower R (MvPolynomial (Fin n) R) X]
    (r : PrimeSpectrum R) :
    let U :
        Submonoid (MvPolynomial (Fin n) R) :=
      Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) r.asIdeal.primeCompl
    LocalizedModule.AtPrime r.asIdeal X ≃ₗ[R] LocalizedModule U X := by
  let U :
      Submonoid (MvPolynomial (Fin n) R) :=
    Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) r.asIdeal.primeCompl
  let A :=
    ((Localization.AtPrime r.asIdeal) ⊗[R] MvPolynomial (Fin n) R)
  let eAtPrime :
      LocalizedModule.AtPrime r.asIdeal X ≃ₗ[Localization.AtPrime r.asIdeal]
        Localization.AtPrime r.asIdeal ⊗[R] X :=
    LocalizedModule.equivTensorProduct r.asIdeal.primeCompl X
  let eCancel :
      A ⊗[MvPolynomial (Fin n) R] X ≃ₗ[Localization.AtPrime r.asIdeal]
        Localization.AtPrime r.asIdeal ⊗[R] X :=
    Algebra.IsPushout.cancelBaseChange R (Localization.AtPrime r.asIdeal)
      (MvPolynomial (Fin n) R) A X
  let eOwner :
      Localization U ⊗[MvPolynomial (Fin n) R] X ≃ₗ[Localization U]
        A ⊗[MvPolynomial (Fin n) R] X :=
    TensorProduct.AlgebraTensorModule.congr
      (tensorAtPrime_localizationAlgEquiv_symm_linearEquiv
        (n := n) (R := R) r)
      (LinearEquiv.refl (MvPolynomial (Fin n) R) X)
  let eLocalized :
      LocalizedModule U X ≃ₗ[Localization U]
        Localization U ⊗[MvPolynomial (Fin n) R] X :=
    LocalizedModule.equivTensorProduct U X
  -- Proof comment: compare both localizations with the common tensor base-change model and then
  -- transport along the already proved prime-local tensor/algebra equivalence.
  exact (((eAtPrime.trans eCancel.symm).trans eOwner.symm).trans eLocalized.symm).restrictScalars R

/-- Helper for Lemma 15.25.1: after passing to the detecting-prime localization `U`, the away
localization at `g` is the away localization at the image of `g` in `Localization U`. This is the
ring-level base-change step underlying the remaining module transport. -/
noncomputable def localized_away_tensor_algEquiv
    (g : MvPolynomial (Fin n) R)
    (r : PrimeSpectrum R) :
    let U :
        Submonoid (MvPolynomial (Fin n) R) :=
      Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) r.asIdeal.primeCompl
    Localization U ⊗[MvPolynomial (Fin n) R] Localization.Away g ≃ₐ[Localization U]
      Localization.Away (algebraMap (MvPolynomial (Fin n) R) (Localization U) g) := by
  let U :
      Submonoid (MvPolynomial (Fin n) R) :=
    Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) r.asIdeal.primeCompl
  let eComm :
      Localization U ⊗[MvPolynomial (Fin n) R] Localization.Away g ≃ₐ[Localization U]
        Localization.Away g ⊗[MvPolynomial (Fin n) R] Localization U :=
    Algebra.TensorProduct.commRight
      (MvPolynomial (Fin n) R) (Localization U) (Localization.Away g)
  -- Proof comment: once the tensor factors are swapped, this is exactly the standard away
  -- localization base-change equivalence from mathlib.
  exact eComm.trans
    (IsLocalization.Away.tensorRightEquiv
      (Localization U) g (Localization.Away g))

/-- Helper for Lemma 15.25.1: if the quotient-model map is already bijective after localizing at
the detecting base prime inside the polynomial ring, then the corresponding base-prime
localization of its away-localization is injective. This isolates the last owner-transport step
used in `hsub_r`. -/
lemma away_localized_map_injective_of_detecting_prime_bijective
    {N : Type*} [AddCommGroup N]
    [Module (MvPolynomial (Fin n) R) N] [Module R N]
    [IsScalarTower R (MvPolynomial (Fin n) R) N]
    (φ : N →ₗ[MvPolynomial (Fin n) R] M)
    (g : MvPolynomial (Fin n) R)
    (r : PrimeSpectrum R)
    (hbij :
      let U :
          Submonoid (MvPolynomial (Fin n) R) :=
        Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) r.asIdeal.primeCompl
      Function.Bijective (LocalizedModule.map U φ)) :
    Function.Injective
      (LocalizedModule.map r.asIdeal.primeCompl
        ((LocalizedModule.map (Submonoid.powers g) φ).restrictScalars R)) := by
  -- Route correction: the remaining source-faithful step is an owner comparison, not another
  -- kernel computation. One must identify base-prime localization after inverting `g` with away
  -- localization after passing to the detecting-prime owner `U`. The first owner change is now
  -- frozen by `atPrime_linearEquiv_localized_polynomial_module`, and the remaining gap is the
  -- module-level version of `localized_away_tensor_algEquiv`.
  -- TODO: upgrade `localized_away_tensor_algEquiv` from rings to modules, conjugate
  -- `LocalizedModule.map r.asIdeal.primeCompl ((LocalizedModule.map (Submonoid.powers g) φ)
  --   .restrictScalars R)` to the away-localization of `LocalizedModule.map U φ`, and then apply
  -- `LocalizedModule.map_injective` to the injective half of `hbij`.
  sorry

/-- Lemma 15.25.1: let `S = R[x₁, …, xₙ]` and let `M` be a finite `S`-module that is flat over
`R` via the restricted scalar action along `R → S`. If there is a finite family of primes of `R`
whose product of localizations detects equality in `R`, and if for every prime `p` of `R` the
canonical tensor-product base change
`((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R) ⊗[MvPolynomial (Fin n) R] M`,
equivalently the textbook localized module over `Rₚ[x₁, …, xₙ]`, is of finite presentation over
`(Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R`, then `M` is of finite
presentation over `S`. -/
theorem finitePresentation_of_flat_of_localized_finitePresentation
    (hdetect : primeLocalizationsDetectEquality R)
    (hloc :
      ∀ p : PrimeSpectrum R,
        Module.FinitePresentation
          ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R)
          (((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R) ⊗[MvPolynomial (Fin n) R] M)) :
    Module.FinitePresentation (MvPolynomial (Fin n) R) M := by
  -- Route correction: abandon the abstract local model from Lemma `10.126.4` and return to the
  -- fixed finite-free quotient model already built in this file. This restores the surjective
  -- map required by the source-faithful kernel-killing endgame.
  have haway :
      ∀ q : PrimeSpectrum (MvPolynomial (Fin n) R),
        ∃ g : MvPolynomial (Fin n) R, g ∉ q.asIdeal ∧
          Module.FinitePresentation (Localization.Away g) (LocalizedModule.Away g M) := by
    intro q
    obtain ⟨s, hsinj⟩ := hdetect
    obtain ⟨m, π, hπ⟩ := Module.Finite.exists_fin' (MvPolynomial (Fin n) R) M
    let p : PrimeSpectrum R :=
      PrimeSpectrum.comap (algebraMap R (MvPolynomial (Fin n) R)) q
    let t : Finset (PrimeSpectrum R) := insert p s
    have hlocalized_t :
        ∀ r ∈ t,
          let U :
              Submonoid (MvPolynomial (Fin n) R) :=
            Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) r.asIdeal.primeCompl
          Module.FinitePresentation (Localization U) (LocalizedModule U M) := by
      intro r hr
      -- Proof comment: each detecting prime still carries the original prime-local
      -- finite-presentation hypothesis after normalizing to the canonical localization owner.
      simpa using
        tensorAtPrime_finitePresentation_localizedModule
          (n := n) (R := R) (M := M) r (hloc r)
    obtain ⟨K0, hK0finite, hK0top⟩ :=
      exists_finite_submodule_of_kernel_with_top_localized_at_detecting_family
        (n := n) (R := R) (M := M) t π hπ hlocalized_t
    letI : Module.Finite (MvPolynomial (Fin n) R) K0 := hK0finite
    let K : Submodule (MvPolynomial (Fin n) R) (Fin m → MvPolynomial (Fin n) R) :=
      K0.map (LinearMap.ker π).subtype
    let N := (Fin m → MvPolynomial (Fin n) R) ⧸ K
    have hKle : K ≤ LinearMap.ker π := by
      -- Proof comment: every element of `K` comes from the chosen denominator submodule inside
      -- `ker π`, so the quotient map `F → N` descends canonically to a map `N → M`.
      intro x hx
      rcases hx with ⟨y, hy, rfl⟩
      exact y.2
    let φ : N →ₗ[MvPolynomial (Fin n) R] M := Submodule.liftQ K π hKle
    have hφsurj : Function.Surjective φ := by
      -- Proof comment: the explicit quotient model still surjects because `π` is surjective and
      -- `φ` agrees with `π` on quotient representatives.
      intro x
      rcases hπ x with ⟨y, rfl⟩
      refine ⟨Submodule.mkQ K y, ?_⟩
      simp [φ, Submodule.liftQ_apply]
    have hKfg : K.FG := by
      -- Proof comment: finite generation of `K0` passes through the inclusion into the fixed free
      -- cover, giving the finitely generated denominator needed for the quotient presentation.
      let hK0fg : K0.FG := Submodule.FG.of_finite
      simpa [K] using hK0fg.map (LinearMap.ker π).subtype
    have hNfp : Module.FinitePresentation (MvPolynomial (Fin n) R) N := by
      -- Proof comment: the quotient of the finite free module by the finitely generated
      -- denominator submodule is finitely presented.
      exact Module.finitePresentation_of_surjective
        (Submodule.mkQ K)
        (Submodule.mkQ_surjective K)
        hKfg
    letI : Module.FinitePresentation (MvPolynomial (Fin n) R) N := hNfp
    have hφlocalized_bij :
        ∀ r ∈ t,
          let U :
              Submonoid (MvPolynomial (Fin n) R) :=
            Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) r.asIdeal.primeCompl
          Function.Bijective (LocalizedModule.map U φ) := by
      intro r hr
      have hKloc :
          let U :
              Submonoid (MvPolynomial (Fin n) R) :=
            Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) r.asIdeal.primeCompl
          Submodule.localized (p := U) K = LinearMap.ker (LocalizedModule.map U π) := by
        -- Proof comment: the denominator-clearing construction makes the localized denominator
        -- submodule equal to the localized kernel at every detecting prime in `t`.
        simpa [K] using
          localized_model_submodule_eq_ker_localized_cover
            (n := n) (R := R) (M := M) π r K0 (hK0top r hr)
      -- Proof comment: at each detecting prime, the explicit localized quotient-model map is
      -- already bijective before any away-localization/base-prime transport is introduced.
      simpa [φ] using
        localized_quotient_model_map_bijective_at_detecting_prime
          (n := n) (R := R) (M := M) π hπ r K hKle hKloc
    let U :
        Submonoid (MvPolynomial (Fin n) R) :=
      Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl
    have hdisj :
        Disjoint (U : Set (MvPolynomial (Fin n) R)) q.asIdeal := by
      -- Proof comment: the contracted prime `p = q ∩ R` is the exact localization center, so the
      -- canonical localization-spectrum homeomorphism applies to `q`.
      simpa [U, p] using
        (comap_prime_disjoint_algebraMapSubmonoid (n := n) (R := R) q)
    have hK0p :
        K0.localized
          (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl) = ⊤ :=
      hK0top p (by simp [t])
    let eU :
        LocalizedModule U N ≃ₗ[Localization U] LocalizedModule U M :=
      localized_quotient_model_linearEquiv_at_family_prime
        (n := n) (R := R) (M := M) π hπ p K0 hK0p
    have hqflat : Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) := by
      infer_instance
    let eAtPrime :
        LocalizedModule.AtPrime q.asIdeal N ≃ₗ[R]
          LocalizedModule.AtPrime q.asIdeal M :=
      atPrime_localization_model_linearEquiv
        (A := MvPolynomial (Fin n) R) (X := N) (Y := M) U hdisj eU
    have hqModel :
        q ∈ Module.flatOverBaseLocus R (MvPolynomial (Fin n) R) N :=
      mem_flatOverBaseLocus_of_atPrime_linearEquiv
        (n := n) (R := R) (M := M) q eAtPrime hqflat
    let flatLocus : Set (PrimeSpectrum (MvPolynomial (Fin n) R)) :=
      Module.flatOverBaseLocus R (MvPolynomial (Fin n) R) N
    have hopen : IsOpen flatLocus := by
      -- Proof comment: the finitely presented model `N` has open flat-over-`R` locus.
      simpa [flatLocus] using
        Module.isOpen_flatOverBaseLocus_of_finitePresentation
          (R := R) (S := MvPolynomial (Fin n) R) (M := N)
    have hqnhds : flatLocus ∈ nhds q := hopen.mem_nhds hqModel
    rcases (PrimeSpectrum.isTopologicalBasis_basic_opens.mem_nhds_iff).1 hqnhds with
      ⟨V, hV, hqV, hVsub⟩
    rcases hV with ⟨g, rfl⟩
    have hgq : g ∉ q.asIdeal := (PrimeSpectrum.mem_basicOpen g q).1 hqV
    have htinj :
        Function.Injective
          (fun r : R ↦
            fun r' : t ↦ algebraMap R (Localization.AtPrime r'.1.asIdeal) r) := by
      intro x y hxy
      apply hsinj
      ext r
      -- Proof comment: equality on the enlarged family restricts to equality on the original
      -- detecting subfamily by evaluating at the corresponding subtype points.
      exact congrFun hxy ⟨r.1, by simpa [t] using Finset.mem_insert_of_mem r.2⟩
    have hkernelFlat :
        Module.Flat R (LinearMap.ker (LocalizedModule.map (Submonoid.powers g) φ)) :=
      away_localized_kernel_flat
        (n := n) (R := R) (M := M) φ hφsurj g hVsub
    let ψ :
        LocalizedModule.Away g N →ₗ[Localization.Away g]
          LocalizedModule.Away g M :=
      LocalizedModule.map (Submonoid.powers g) φ
    let Kaway := LinearMap.ker ψ
    have hsub_r :
        ∀ r : t, Subsingleton (LocalizedModule.AtPrime r.1.asIdeal Kaway) := by
      intro r
      -- Proof comment: once the final owner-comparison lemma supplies injectivity of the
      -- localized away map, the localized kernel vanishes by the generic kernel-killing helper.
      exact
        away_localized_kernel_atPrime_subsingleton_of_localized_map_injective
          (n := n) (R := R) (M := M) φ g r.1
          (hinj :=
            away_localized_map_injective_of_detecting_prime_bijective
              (n := n) (R := R) (M := M) φ g r.1 (hφlocalized_bij r.1 r.2))
    have hsubK : Subsingleton Kaway := by
      -- Proof comment: the detecting family kills the flat away-local kernel once all of its
      -- base-prime localizations are subsingleton.
      letI : Module.Flat R Kaway := hkernelFlat
      exact
        subsingleton_of_detecting_prime_localizations_of_flat
          (R := R) (X := Kaway) t htinj hsub_r
    have hker_bot : Kaway = ⊥ := by
      -- Proof comment: a subsingleton submodule is the zero submodule.
      exact Submodule.subsingleton_iff_eq_bot.mp hsubK
    have hψinj : Function.Injective ψ := by
      -- Proof comment: zero kernel is exactly injectivity of the away-local quotient-model map.
      exact LinearMap.ker_eq_bot.mp hker_bot
    have hψsurj : Function.Surjective ψ := by
      -- Proof comment: surjectivity survives away localization of the quotient-model map.
      exact LocalizedModule.map_surjective (Submonoid.powers g) φ hφsurj
    let eψ :
        LocalizedModule.Away g N ≃ₗ[Localization.Away g]
          LocalizedModule.Away g M :=
      LinearEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
    have hNaway :
        Module.FinitePresentation (Localization.Away g) (LocalizedModule.Away g N) := by
      -- Proof comment: finite presentation of the quotient model persists after inverting `g`.
      infer_instance
    letI : Module.FinitePresentation (Localization.Away g) (LocalizedModule.Away g N) := hNaway
    exact ⟨g, hgq, Module.FinitePresentation.of_equiv eψ.symm⟩
  -- The local-to-global cover argument is now fully verified.
  exact finitePresentation_of_primewise_localizationAway (n := n) (M := M) haway

end
