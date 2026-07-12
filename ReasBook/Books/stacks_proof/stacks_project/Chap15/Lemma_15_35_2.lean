import Mathlib
import StacksProject_2024.Chap10.Definition_10_60_10
import StacksProject_2024.Chap10.Definition_10_110_7
import StacksProject_2024.Chap10.Lemma_10_106_3
import StacksProject_2024.Chap10.Lemma_10_112_8
import StacksProject_2024.Chap10.Lemma_10_128_2
import StacksProject_2024.Chap10.Lemma_10_134_6
import StacksProject_2024.Chap10.Lemma_10_134_11
import StacksProject_2024.Chap10.Lemma_10_134_7
import StacksProject_2024.Chap10.Lemma_10_150_7
import StacksProject_2024.Chap10.Lemma_10_166_5
import StacksProject_2024.Chap10.Proposition_10_114_2
import StacksProject_2024.Chap15.Lemma_15_33_8
import StacksProject_2024.Chap15.Lemma_15_34_2
import StacksProject_2024.Chap15.Proposition_15_35_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open KaehlerDifferential
open RingTheory Sequence
open scoped TensorProduct

universe u v

namespace Algebra

noncomputable section

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra k A]

/- Domain-style sampling:
* primary domain: local geometric regularity in characteristic `p`, expressed through a chosen
  polynomial map `k[y₁, …, yₘ] → A`, its induced localization at the inverse-image of the maximal
  ideal, and the cotangent-theoretic differential family over a finitely generated residue-field
  subextension;
* sampled owner declarations:
  - `IsGeometricallyRegular`,
  - `Localization.AtPrime`,
  - `Localization.localRingHom`,
  - `Ideal.Fiber`,
  - `closedFiberQuotAlgEquiv`,
  - `KaehlerDifferential.D`,
  - `LinearIndependent`,
  - `Submodule.span`,
  - `IntermediateField`;
* best owner abstraction: this file is `source-facing`, and the conclusion should be stated for
  the canonical local map from the localized polynomial ring
  `Localization.AtPrime (Ideal.comap φ.toRingHom (maximalIdeal A))` to `A`; the matching closed
  fiber should live on the canonical owner `Ideal.Fiber (maximalIdeal Aφ) A`, while the explicit
  quotient of `A` by the image of the source maximal ideal under that map is only the companion
  bridge/view supplied upstream by `closedFiberQuotAlgEquiv`; the finitely generated residue-field
  subextension should be carried by the canonical owner `IntermediateField k (ResidueField A)`;
* primitive data vs. derived API:
  - primitive data: `m`, `φ`, the chosen generators in
    `F : IntermediateField k (ResidueField A)`, the finite-generation hypothesis `F.FG`, the
    residue-field compatibility, and the differential family together with its linear independence
    and spanning;
  - derived API: the inverse-image prime
    `Ideal.comap φ.toRingHom (maximalIdeal A)`, the canonical localized map
    `Localization.AtPrime 𝔭 →+* A`, and the quotient presentation of its canonical closed fiber.

Source/core/bridge triage:
* `source-facing`: the theorem below;
* `core/canonical`: `IsGeometricallyRegular`, `Localization.AtPrime`,
  `Localization.localRingHom`, `Localization.algEquiv`, `Ideal.Fiber`,
  `KaehlerDifferential.D`, `LinearIndependent`, and `Submodule.span`;
* `bridge/view`: the derived prime ideal of `φ` and the quotient presentation of the closed fiber.
-/

section LocalRingLocalization

variable {A : Type v} [CommRing A] [IsLocalRing A]

/-- A local ring is already a localization at the complement of its maximal ideal. -/
private theorem self_isLocalization_primeCompl_maximalIdeal :
    IsLocalization (maximalIdeal A).primeCompl A := by
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    exact IsLocalRing.notMem_maximalIdeal.mp y.2
  · intro z
    exact ⟨⟨z, 1⟩, by simp⟩
  · intro x y hxy
    exact ⟨1, by simpa using hxy⟩

attribute [local instance] self_isLocalization_primeCompl_maximalIdeal

end LocalRingLocalization

private instance localRing_isLocalization_primeCompl_maximalIdeal :
    IsLocalization (maximalIdeal A).primeCompl A :=
  self_isLocalization_primeCompl_maximalIdeal

variable {p : ℕ} [Fact p.Prime] [CharP k p]

section LocalizedPolynomialSubextensionMap

variable (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] A)

local notation "pφ" => Ideal.comap φ.toRingHom (maximalIdeal A)
local notation "Aφ" => Localization.AtPrime pφ

/-- The canonical local map from the localized polynomial presentation
`Localization.AtPrime (Ideal.comap φ.toRingHom (maximalIdeal A))` to `A`. -/
noncomputable def localizedPolynomialSubextensionMap : Aφ →+* A :=
  ((Localization.algEquiv (maximalIdeal A).primeCompl A).toRingHom).comp
    (Localization.localRingHom pφ (maximalIdeal A) φ.toRingHom rfl)

local instance localizedPolynomialSubextensionMapAlgebra : Algebra Aφ A :=
  (localizedPolynomialSubextensionMap m φ).toAlgebra

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal Aφ) A

private instance polynomialSubextensionPrime_isPrime :
    (Ideal.comap φ.toRingHom (maximalIdeal A)).IsPrime := by
  let _ : (maximalIdeal A).IsPrime := (maximalIdeal.isMaximal A).isPrime
  exact Ideal.comap_isPrime φ.toRingHom (maximalIdeal A)

/-- Helper for Lemma 15.35.2: mapping a chosen parameter family termwise identifies the
corresponding parameter ideals. -/
private theorem parameterIdeal_map_eq_parameterIdeal_of_forall
    {P Q : Type*} [CommRing P] [CommRing Q] [IsLocalRing P] [IsLocalRing Q]
    (f : P →+* Q) {d : ℕ}
    (x : Fin d → maximalIdeal P) (z : Fin d → maximalIdeal Q)
    (hf : ∀ i, f (x i : P) = (z i : Q)) :
    Ideal.map f (parameterIdeal x) = parameterIdeal z := by
  -- Rewrite both parameter ideals as spans of the chosen generators.
  rw [parameterIdeal_eq_span, parameterIdeal_eq_span, Ideal.map_span]
  have hrange :
      f '' Set.range (fun i ↦ ((x i : maximalIdeal P) : P)) =
        Set.range fun i ↦ ((z i : maximalIdeal Q) : Q) := by
    ext q
    constructor
    · rintro ⟨p, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hf i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x i, ⟨i, rfl⟩, hf i⟩
  rw [hrange]

/-- Helper for Lemma 15.35.2: once the source parameter family maps termwise to a family that is
part of a regular system of parameters on the target, flatness and regularity of the closed fiber
follow from the Chapter 10 parameter lemmas. -/
private theorem flat_and_regularFiber_of_parameter_image
    {P Q : Type*} [CommRing P] [CommRing Q]
    [IsLocalRing P] [IsLocalRing Q] [IsRegularLocalRing P] [IsRegularLocalRing Q]
    [IsNoetherianRing Q] [Algebra P Q] [IsLocalHom (algebraMap P Q)]
    {d : ℕ} (x : Fin d → maximalIdeal P) (z : Fin d → maximalIdeal Q)
    (hx : IsRegularSystemOfParameters x)
    (hmap : ∀ i, algebraMap P Q (x i : P) = (z i : Q))
    (hz : IsPartOfRegularSystemOfParameters (maximalIdeal Q).spanFinrank z) :
    (algebraMap P Q).Flat ∧ IsRegularLocalRing ((maximalIdeal P).Fiber Q) := by
  -- The image family is regular because it is part of a regular system of parameters on `Q`.
  have himage_regular :
      Sequence.IsRegular Q (List.ofFn fun i ↦ algebraMap P Q (x i : P)) := by
    simpa [hmap] using
      (IsPartOfRegularSystemOfParameters.isRegular hz :
        Sequence.IsRegular Q (List.ofFn fun i ↦ (z i : Q)))
  have hflatAlg : Module.Flat P Q :=
    flat_of_regularSystemOfParameters_image_isRegular x hx himage_regular
  have hmapIdeal :
      Ideal.map (algebraMap P Q) (parameterIdeal x) = parameterIdeal z :=
    parameterIdeal_map_eq_parameterIdeal_of_forall (algebraMap P Q) x z hmap
  have hclosedQuot :
      IsRegularLocalRing (Q ⧸ Ideal.map (algebraMap P Q) (maximalIdeal P)) := by
    -- The closed-fiber quotient is exactly the quotient by the target parameter ideal.
    have hmapMax :
        Ideal.map (algebraMap P Q) (maximalIdeal P) = parameterIdeal z := by
      rw [← hx.2]
      exact hmapIdeal
    exact
      hmapMax.symm ▸
        (IsPartOfRegularSystemOfParameters.isRegularLocalRing_quotient_parameterIdeal hz :
          IsRegularLocalRing (Q ⧸ parameterIdeal z))
  let _ : IsRegularLocalRing (Q ⧸ Ideal.map (algebraMap P Q) (maximalIdeal P)) := hclosedQuot
  have hclosedFiber : IsRegularLocalRing ((maximalIdeal P).Fiber Q) := by
    -- Chapter 10 identifies the canonical closed fiber with that regular quotient.
    simpa using (isRegularLocalRing_closedFiber_of_quotient (R := P) (S := Q))
  refine ⟨?_, hclosedFiber⟩
  exact RingHom.flat_algebraMap_iff.mpr hflatAlg

/-- Helper for Lemma 15.35.2: the localized polynomial source is a regular local ring because a
polynomial ring over a field is regular and regularity localizes at prime ideals. -/
private theorem localized_polynomial_source_isRegularLocalRing :
    IsRegularLocalRing Aφ := by
  -- Move from global regularity of the polynomial ring to the chosen prime localization.
  exact
    IsRegularRing.isRegularLocalRing_atPrime
      (R := MvPolynomial (Fin m) k)
      ⟨pφ, polynomialSubextensionPrime_isPrime (m := m) (φ := φ)⟩

/-- Helper for Lemma 15.35.2: localizing the polynomial presentation is formally étale over the
polynomial ring, so the canonical base-change map on Kähler differentials is bijective. -/
private theorem localized_polynomial_mapBaseChange_bijective :
    Function.Bijective (KaehlerDifferential.mapBaseChange k (MvPolynomial (Fin m) k) Aφ) := by
  -- Localization is formally étale, and the chapter owner theorem identifies the resulting
  -- differential base-change map with a linear equivalence.
  letI : Algebra.FormallyEtale (MvPolynomial (Fin m) k) Aφ :=
    Algebra.FormallyEtale.of_isLocalization pφ.primeCompl
  simpa using
    formallyEtale_kaehlerDifferential_mapBaseChange_bijective
      (R := k) (S := MvPolynomial (Fin m) k) (S' := Aφ)

/-- Helper for Lemma 15.35.2: evaluating a polynomial at the chosen elements of `F` and then
including into `ResidueField A` agrees with reducing the original polynomial map modulo the
maximal ideal. -/
private theorem polynomial_eval_to_subextension_comp_residue
    (F : IntermediateField k (ResidueField A)) (y : Fin m → F)
    (hresidue :
      ∀ i, residue A (φ (MvPolynomial.X i)) = algebraMap F (ResidueField A) (y i)) :
    (algebraMap F (ResidueField A)).comp (MvPolynomial.aeval y).toRingHom =
      (residue A).comp φ.toRingHom := by
  -- Proof comment: both polynomial maps agree on coefficients and on every variable image.
  ext i <;> simp [hresidue i]

/-- Helper for Lemma 15.35.2: every denominator in the localization defining `Aφ` evaluates to a
unit in `F`, because its image in `ResidueField A` is the residue of an element outside the
maximal ideal. -/
private theorem polynomial_eval_to_subextension_isUnit
    (F : IntermediateField k (ResidueField A)) (y : Fin m → F)
    (hresidue :
      ∀ i, residue A (φ (MvPolynomial.X i)) = algebraMap F (ResidueField A) (y i))
    (s : pφ.primeCompl) :
    IsUnit ((MvPolynomial.aeval y) s) := by
  -- Proof comment: vanishing in the field `F` would force the residue of `φ(s)` to vanish, hence
  -- `φ(s)` would lie in the maximal ideal and `s` would belong to the defining prime.
  apply isUnit_iff_ne_zero.mpr
  intro hs
  have hcomp :=
    congrArg (fun g : MvPolynomial (Fin m) k →+* ResidueField A ↦ g s)
      (polynomial_eval_to_subextension_comp_residue (m := m) (φ := φ) F y hresidue)
  have hzero : residue A (φ s) = 0 := by
    simpa [hs] using hcomp.symm
  have hs_mem : (s : MvPolynomial (Fin m) k) ∈ pφ := by
    change φ s ∈ maximalIdeal A
    exact (IsLocalRing.residue_eq_zero_iff (R := A) (a := φ s)).1 hzero
  exact s.2 hs_mem

/-- Helper for Lemma 15.35.2: localizing the polynomial evaluation at the inverse image prime
produces the source-faithful map `Aφ → F` from the textbook proof. -/
private noncomputable def localized_polynomial_to_subextension
    (F : IntermediateField k (ResidueField A)) (y : Fin m → F)
    (hresidue :
      ∀ i, residue A (φ (MvPolynomial.X i)) = algebraMap F (ResidueField A) (y i)) :
    Aφ →ₐ[k] F :=
  IsLocalization.liftAlgHom
    (S := Aφ) (f := MvPolynomial.aeval y)
    (fun s ↦ polynomial_eval_to_subextension_isUnit (m := m) (φ := φ) F y hresidue s)

/-- Helper for Lemma 15.35.2: the localized evaluation map extends polynomial evaluation on the
base ring before localization. -/
private theorem localized_polynomial_to_subextension_apply_algebraMap
    (F : IntermediateField k (ResidueField A)) (y : Fin m → F)
    (hresidue :
      ∀ i, residue A (φ (MvPolynomial.X i)) = algebraMap F (ResidueField A) (y i))
    (f : MvPolynomial (Fin m) k) :
    localized_polynomial_to_subextension (m := m) (φ := φ) F y hresidue
        (algebraMap (MvPolynomial (Fin m) k) Aφ f) =
      (MvPolynomial.aeval y) f := by
  -- Proof comment: this is exactly the defining compatibility of the localization lift.
  change
    IsLocalization.lift
        (fun s : pφ.primeCompl ↦
          polynomial_eval_to_subextension_isUnit (m := m) (φ := φ) F y hresidue s)
        (algebraMap (MvPolynomial (Fin m) k) Aφ f) =
      (MvPolynomial.aeval y) f
  simpa [localized_polynomial_to_subextension, IsLocalization.liftAlgHom] using
    (IsLocalization.lift_eq
      (S := Aφ)
      (g := (MvPolynomial.aeval y).toRingHom)
      (fun s : pφ.primeCompl ↦
        polynomial_eval_to_subextension_isUnit (m := m) (φ := φ) F y hresidue s)
      f)

/-- Helper for Lemma 15.35.2: the localized evaluation map still sends each coordinate variable to
the chosen element of `F`. -/
@[simp] private theorem localized_polynomial_to_subextension_apply_X
    (F : IntermediateField k (ResidueField A)) (y : Fin m → F)
    (hresidue :
      ∀ i, residue A (φ (MvPolynomial.X i)) = algebraMap F (ResidueField A) (y i))
    (i : Fin m) :
    localized_polynomial_to_subextension (m := m) (φ := φ) F y hresidue
        (algebraMap (MvPolynomial (Fin m) k) Aφ (MvPolynomial.X i)) = y i := by
  -- Proof comment: specialize the compatibility on base polynomials to the coordinate variable
  -- `X i`.
  simpa [MvPolynomial.aeval_X] using
    localized_polynomial_to_subextension_apply_algebraMap
      (m := m) (φ := φ) F y hresidue (MvPolynomial.X i)

/-- Helper for Lemma 15.35.2: after composing `Aφ → F` with the inclusion `F → κ(A)`, one
recovers the residue of the localized polynomial map into `A`. -/
private theorem localized_polynomial_to_subextension_comp_residue
    (F : IntermediateField k (ResidueField A)) (y : Fin m → F)
    (hresidue :
      ∀ i, residue A (φ (MvPolynomial.X i)) = algebraMap F (ResidueField A) (y i)) :
    (algebraMap F (ResidueField A)).comp
        (localized_polynomial_to_subextension (m := m) (φ := φ) F y hresidue).toRingHom =
      (residue A).comp (localizedPolynomialSubextensionMap m φ) := by
  -- Proof comment: both maps out of the localization agree on the polynomial ring, so the
  -- localization universal property identifies them.
  apply IsLocalization.ringHom_ext pφ.primeCompl
  intro f
  rw [RingHom.comp_apply, RingHom.comp_apply,
    localized_polynomial_to_subextension_apply_algebraMap (m := m) (φ := φ) F y hresidue]
  have hcomp :=
    congrArg (fun g : MvPolynomial (Fin m) k →+* ResidueField A ↦ g f)
      (polynomial_eval_to_subextension_comp_residue (m := m) (φ := φ) F y hresidue)
  simpa [localizedPolynomialSubextensionMap, Localization.localRingHom_to_map] using hcomp

/-- Helper for Lemma 15.35.2: the canonical localized polynomial map is local, so every element
of the source maximal ideal maps into the target maximal ideal. -/
private theorem localized_polynomial_maximalIdeal_mem
    (x : maximalIdeal Aφ) :
    algebraMap Aφ A (x : Aφ) ∈ maximalIdeal A := by
  -- Proof comment: for a local homomorphism, the preimage of the target maximal ideal is exactly
  -- the source maximal ideal.
  have hcomap :
      Ideal.comap (algebraMap Aφ A) (maximalIdeal A) = maximalIdeal Aφ := by
    simpa [RingHom.algebraMap_toAlgebra] using
      (IsLocalHom.comap_maximalIdeal (f := algebraMap Aφ A))
  exact show (x : Aφ) ∈ Ideal.comap (algebraMap Aφ A) (maximalIdeal A) by
    simpa [hcomap]

/-- Helper for Lemma 15.35.2: the image of a source parameter family under the localized
polynomial map is regarded as a family inside the target maximal ideal. -/
private noncomputable def localized_polynomial_parameter_image
    {d : ℕ} (x : Fin d → maximalIdeal Aφ) :
    Fin d → maximalIdeal A :=
  fun i ↦
    ⟨algebraMap Aφ A (x i : Aφ),
      localized_polynomial_maximalIdeal_mem (m := m) (φ := φ) (x i)⟩

/-- Helper for Lemma 15.35.2: the underlying target element of the image parameter family is just
the algebra-map image of the source parameter. -/
@[simp] private theorem localized_polynomial_parameter_image_coe
    {d : ℕ} (x : Fin d → maximalIdeal Aφ) (i : Fin d) :
    ((localized_polynomial_parameter_image (m := m) (φ := φ) x i : maximalIdeal A) : A) =
      algebraMap Aφ A (x i : Aφ) :=
  rfl

/-- Helper for Lemma 15.35.2: Proposition 15.35.1 supplies the target-side regularity and
injective `H₁ → cotangent` comparison for any geometrically regular local `k`-algebra in
characteristic `p > 0`. -/
private theorem geometricallyRegularLocalRing_h1Cotangent_map_injective_of_charP
    [IsGeometricallyRegular k A] :
    IsRegularLocalRing A ∧
      Function.Injective (H1Cotangent.map k A (ResidueField A) (ResidueField A)) := by
  let T : List Prop :=
    [ IsGeometricallyRegular k A
    , ∀ (K : IntermediateField k (AlgebraicClosure k)) [FiniteDimensional k K],
        K ≤ onePthRootExtension k p → IsRegularRing (K ⊗[k] A)
    , IsRegularLocalRing A ∧
        Function.Injective (H1Cotangent.map k A (ResidueField A) (ResidueField A))
    , IsRegularLocalRing A ∧
        Function.Injective (KaehlerDifferential.residueFieldComparison (ZMod p) k A)
    ]
  have hTfae : List.TFAE T := by
    -- Proof comment: package Proposition `15.35.1` into a named list so the `(1) → (3)` leg can
    -- be extracted once and reused in the square chase.
    simpa [T] using
      (geometricallyRegularLocalRing_tfae_of_charP (k := k) (A := A) (p := p))
  -- Proof comment: this is exactly the target-side injectivity used in the textbook square.
  simpa [T] using (hTfae.out 0 2).mp (show IsGeometricallyRegular k A from inferInstance)

/-- Helper for Lemma 15.35.2: Proposition 15.35.1 also supplies the target-side injective
residue-field comparison on Kähler differentials. -/
private theorem geometricallyRegularLocalRing_residueFieldComparison_injective_of_charP
    [IsGeometricallyRegular k A] :
    IsRegularLocalRing A ∧
      Function.Injective (KaehlerDifferential.residueFieldComparison (ZMod p) k A) := by
  let T : List Prop :=
    [ IsGeometricallyRegular k A
    , ∀ (K : IntermediateField k (AlgebraicClosure k)) [FiniteDimensional k K],
        K ≤ onePthRootExtension k p → IsRegularRing (K ⊗[k] A)
    , IsRegularLocalRing A ∧
        Function.Injective (H1Cotangent.map k A (ResidueField A) (ResidueField A))
    , IsRegularLocalRing A ∧
        Function.Injective (KaehlerDifferential.residueFieldComparison (ZMod p) k A)
    ]
  have hTfae : List.TFAE T := by
    -- Proof comment: again extract the required TFAE leg once rather than rebuilding the chapter
    -- criterion inside the main proof.
    simpa [T] using
      (geometricallyRegularLocalRing_tfae_of_charP (k := k) (A := A) (p := p))
  -- Proof comment: this is the differential-side injectivity needed for the source-to-target
  -- comparison.
  simpa [T] using (hTfae.out 0 3).mp (show IsGeometricallyRegular k A from inferInstance)

section SourceCotangentComparison

variable {R : Type*} [CommRing R] [IsLocalRing R] [Algebra k R]

/-- Helper for Lemma 15.35.2: reducing a local ring modulo its maximal ideal identifies the
kernel of the residue-field algebra map with the maximal ideal itself. -/
private theorem ker_algebraMap_residueField_eq_maximalIdeal :
    RingHom.ker (algebraMap R (ResidueField R)) = maximalIdeal R := by
  -- Proof comment: `algebraMap R κ(R)` is the residue map, so its kernel is the maximal ideal.
  simpa [ResidueField.algebraMap_eq] using
    (ker_residue : RingHom.ker (IsLocalRing.residue R) = maximalIdeal R)

/-- Helper for Lemma 15.35.2: the canonical residue-field surjection identifies
`H₁(L_{κ(R)/R})` with the conormal module `𝔪_R / 𝔪_R²`. -/
private noncomputable def residueField_h1Cotangent_to_cotangent :
    H1Cotangent k (ResidueField R) →ₗ[ResidueField R] (maximalIdeal R).Cotangent :=
  ((Ideal.Cotangent.equivOfEq
      (maximalIdeal R)
      (RingHom.ker (algebraMap R (ResidueField R)))
      (ker_algebraMap_residueField_eq_maximalIdeal (k := k) (R := R)).symm).symm.toLinearMap).comp
    (((surjective_algebra_h1Cotangent_equiv_cotangent
        (A := R) (B := ResidueField R)
        (by
          simpa [ResidueField.algebraMap_eq] using
            (residue_surjective : Function.Surjective (IsLocalRing.residue R)))).toLinearMap).comp
      (H1Cotangent.map k R (ResidueField R) (ResidueField R)))

/-- Helper for Lemma 15.35.2: once
`κ(R) ⊗[R] Ω[R⁄k] → Ω[κ(R)⁄k]` is injective, the Jacobi-Zariski connecting morphism vanishes and
the source map `H₁(L_{κ(R)/k}) → H₁(L_{κ(R)/R})` becomes surjective. -/
private theorem residueField_h1Cotangent_map_surjective_of_mapBaseChange_injective
    (hres :
      Function.Injective (KaehlerDifferential.mapBaseChange k R (ResidueField R))) :
    Function.Surjective (H1Cotangent.map k R (ResidueField R) (ResidueField R)) := by
  let K0 := ResidueField R
  have hsurj :
      Function.Surjective (algebraMap R K0) := by
    simpa [ResidueField.algebraMap_eq] using
      (residue_surjective : Function.Surjective (IsLocalRing.residue R))
  have hδ_exact :
      Function.Exact
        (H1Cotangent.δ k R K0)
        (KaehlerDifferential.mapBaseChange k R K0) :=
    H1Cotangent.exact_δ_mapBaseChange k R K0
  have hδ_range :
      LinearMap.range (H1Cotangent.δ k R K0) = ⊥ := by
    -- Proof comment: exactness identifies the range of `δ` with the kernel of the injective
    -- differential comparison.
    rw [← hδ_exact.linearMap_ker_eq]
    exact LinearMap.ker_eq_bot.mpr hres
  have hδ_zero : H1Cotangent.δ k R K0 = 0 := by
    -- Proof comment: a linear map with zero range is the zero map.
    ext x
    have hx :
        H1Cotangent.δ k R K0 x ∈ LinearMap.range (H1Cotangent.δ k R K0) := ⟨x, rfl⟩
    rw [hδ_range] at hx
    simpa using hx
  have hmap_exact :
      Function.Exact
        (H1Cotangent.map k R K0 K0)
        (H1Cotangent.δ k R K0) :=
    (surjective_jacobi_zariski_conormal_sequence (A := k) (B := R) (C := K0) hsurj).1
  -- Proof comment: with `δ = 0`, exactness forces the left Jacobi-Zariski map to hit all of
  -- `H₁(L_{κ(R)/R})`.
  rw [← LinearMap.range_eq_top]
  rw [← hmap_exact.linearMap_ker_eq]
  rw [hδ_zero, LinearMap.ker_zero]

/-- Helper for Lemma 15.35.2: if the residue-field differential comparison is injective and the
regular-local `H₁`-criterion is available, then the textbook map
`H₁(L_{κ(R)/k}) → 𝔪_R / 𝔪_R²` is bijective. -/
private theorem residueField_h1Cotangent_to_cotangent_bijective_of_mapBaseChange_injective
    [IsNoetherianRing R] [Fact p.Prime] [CharP k p] [IsGeometricallyRegular k R]
    (hres :
      Function.Injective (KaehlerDifferential.mapBaseChange k R (ResidueField R))) :
    Function.Bijective (residueField_h1Cotangent_to_cotangent (k := k) (R := R)) := by
  let K0 := ResidueField R
  have hsurj :
      Function.Surjective (algebraMap R K0) := by
    simpa [ResidueField.algebraMap_eq] using
      (residue_surjective : Function.Surjective (IsLocalRing.residue R))
  have hmap_injective :
      Function.Injective (H1Cotangent.map k R K0 K0) :=
    (geometricallyRegularLocalRing_h1Cotangent_map_injective_of_charP
      (k := k) (A := R) (p := p)).2
  have hmap_surjective :
      Function.Surjective (H1Cotangent.map k R K0 K0) :=
    residueField_h1Cotangent_map_surjective_of_mapBaseChange_injective
      (k := k) (R := R) hres
  -- Proof comment: the two transport equivalences preserve bijectivity, so the preceding
  -- surjective `H₁` map becomes the desired `H₁ → 𝔪/𝔪²` bijection.
  constructor
  · intro x y hxy
    apply hmap_injective
    apply (surjective_algebra_h1Cotangent_equiv_cotangent
      (A := R) (B := K0) hsurj).injective
    apply
      ((Ideal.Cotangent.equivOfEq
        (maximalIdeal R)
        (RingHom.ker (algebraMap R K0))
        (ker_algebraMap_residueField_eq_maximalIdeal (k := k) (R := R)).symm).symm).injective
    simpa [residueField_h1Cotangent_to_cotangent, LinearMap.comp_apply] using hxy
  · intro x
    obtain ⟨y, hy⟩ := hmap_surjective
      (((surjective_algebra_h1Cotangent_equiv_cotangent
          (A := R) (B := K0) hsurj).symm)
        (((Ideal.Cotangent.equivOfEq
            (maximalIdeal R)
            (RingHom.ker (algebraMap R K0))
            (ker_algebraMap_residueField_eq_maximalIdeal (k := k) (R := R)).symm).symm) x))
    refine ⟨y, ?_⟩
    simpa [residueField_h1Cotangent_to_cotangent, LinearMap.comp_apply] using congrArg
      (((Ideal.Cotangent.equivOfEq
          (maximalIdeal R)
          (RingHom.ker (algebraMap R K0))
          (ker_algebraMap_residueField_eq_maximalIdeal (k := k) (R := R)).symm).symm))
      ((surjective_algebra_h1Cotangent_equiv_cotangent
          (A := R) (B := K0) hsurj) hy)

end SourceCotangentComparison

section CotangentParameterBridge

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsRegularLocalRing R]

local notation "κR" => ResidueField R

/-- Helper for Lemma 15.35.2: a family in the maximal ideal whose cotangent classes span the full
cotangent space is already a regular system of parameters. -/
private theorem regularSystemOfParameters_of_toCotangent_span_top
    {n : ℕ} (z : Fin n → maximalIdeal R)
    (hn : n = (maximalIdeal R).spanFinrank)
    (hspan :
      Submodule.span κR (Set.range fun i ↦ (maximalIdeal R).toCotangent (z i)) = ⊤) :
    IsRegularSystemOfParameters z := by
  -- Translate spanning in the cotangent space back to generation of the maximal ideal.
  have hcot_range :
      (maximalIdeal R).toCotangent '' Set.range z =
        Set.range fun i ↦ (maximalIdeal R).toCotangent (z i) := by
    ext y
    constructor
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨z i, ⟨i, rfl⟩, rfl⟩
  have hspanR : Submodule.span R (Set.range z) = ⊤ := by
    have hspanImage :
        Submodule.span κR ((maximalIdeal R).toCotangent '' Set.range z) = ⊤ := by
      simpa [hcot_range] using hspan
    exact
      (IsLocalRing.CotangentSpace.span_image_eq_top_iff
        (R := R) (s := Set.range z)).1 hspanImage
  have hsubtype_range :
      (((↑) : maximalIdeal R → R) '' Set.range z) =
        Set.range fun i ↦ ((z i : maximalIdeal R) : R) := by
    ext r
    constructor
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨z i, ⟨i, rfl⟩, rfl⟩
  have hparam : parameterIdeal z = maximalIdeal R := by
    rw [IsLocalRing.parameterIdeal_eq_span]
    have hmap := congrArg (Submodule.map (maximalIdeal R).subtype) hspanR
    simpa [Submodule.map_top, Submodule.map_span, hsubtype_range] using hmap
  have hdim : ringKrullDim R = n := by
    have hregdim : (maximalIdeal R).spanFinrank = ringKrullDim R :=
      (isRegularLocalRing_iff R).1 inferInstance
    simpa [hn] using hregdim.symm
  -- With the dimension identified, the standard owner criterion closes the goal.
  exact (IsLocalRing.isRegularSystemOfParameters_iff_of_ringKrullDim_eq hdim z).2 hparam

/-- Helper for Lemma 15.35.2: a linearly independent cotangent family extends to one spanning the
full cotangent space. -/
private theorem append_toCotangent_span_top_of_linearIndependent
    {m : ℕ} (x : Fin m → maximalIdeal R)
    (hlin : LinearIndependent κR (fun j ↦ (maximalIdeal R).toCotangent (x j))) :
    ∃ y : Fin ((maximalIdeal R).spanFinrank - m) → maximalIdeal R,
      Submodule.span κR
          (Set.range fun i ↦ (maximalIdeal R).toCotangent ((Fin.append x y) i)) = ⊤ := by
  -- Complete the independent family to a basis of the cotangent space and lift the complement.
  let v : Fin m → CotangentSpace R := fun j ↦ (maximalIdeal R).toCotangent (x j)
  let V : Submodule κR (CotangentSpace R) := Submodule.span κR (Set.range v)
  let bW : Module.Basis (Fin m) κR V := by
    change Module.Basis (Fin m) κR (Submodule.span κR (Set.range v))
    exact Module.Basis.span hlin
  have hbW_apply : ∀ j, (((bW j : V) : CotangentSpace R)) = v j := by
    intro j
    change ↑((Module.Basis.span hlin) j) = v j
    simp [v]
  have hbW_finrank : Module.finrank κR V = m := by
    simpa [bW] using Module.finrank_eq_card_basis bW
  have hquot_dim :
      Module.finrank κR (CotangentSpace R ⧸ V) = (maximalIdeal R).spanFinrank - m := by
    -- The quotient dimension is the cotangent dimension minus the span of the chosen family.
    have hsum := Submodule.finrank_quotient_add_finrank V
    have hdimR : Module.finrank κR (CotangentSpace R) = (maximalIdeal R).spanFinrank := by
      symm
      exact IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)
    rw [hbW_finrank, hdimR] at hsum
    omega
  let bQ0 :
      Module.Basis (Fin (Module.finrank κR (CotangentSpace R ⧸ V))) κR (CotangentSpace R ⧸ V) :=
    Module.finBasis κR (CotangentSpace R ⧸ V)
  let bQ :
      Module.Basis (Fin ((maximalIdeal R).spanFinrank - m)) κR (CotangentSpace R ⧸ V) :=
    bQ0.reindex (finCongr hquot_dim)
  let b :
      Module.Basis
        (Fin m ⊕ Fin ((maximalIdeal R).spanFinrank - m))
        κR
        (CotangentSpace R) :=
    bW.sumQuot bQ
  have hy :
      ∃ y : Fin ((maximalIdeal R).spanFinrank - m) → maximalIdeal R,
        ∀ j, (maximalIdeal R).toCotangent (y j) = b (Sum.inr j) := by
    -- Surjectivity of `toCotangent` lifts the complementary basis vectors.
    choose y hy using fun j ↦
      Ideal.toCotangent_surjective (maximalIdeal R) (b (Sum.inr j))
    exact ⟨y, hy⟩
  rcases hy with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  have happend :
      (fun i : Fin (m + ((maximalIdeal R).spanFinrank - m)) ↦
          (maximalIdeal R).toCotangent ((Fin.append x y) i)) =
        b ∘ finSumFinEquiv.symm := by
    -- Reindex the appended family by the basis `b`.
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [Function.comp_apply, Fin.append_left]
      rw [show
          finSumFinEquiv.symm (Fin.castAdd ((maximalIdeal R).spanFinrank - m) j) = Sum.inl j by
        simp]
      rw [Module.Basis.sumQuot_inl]
      symm
      exact hbW_apply j
    · intro j
      simp only [Function.comp_apply, Fin.append_right]
      rw [show finSumFinEquiv.symm (Fin.natAdd m j) = Sum.inr j by simp]
      exact hy j
  have hrangeb : Set.range (b ∘ finSumFinEquiv.symm) = Set.range b := by
    -- Reindexing by an equivalence preserves the range.
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨finSumFinEquiv.symm i, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨finSumFinEquiv s, by simp⟩
  -- The basis family spans the whole cotangent space, so the appended family does as well.
  calc
    Submodule.span κR
        (Set.range fun i ↦ (maximalIdeal R).toCotangent ((Fin.append x y) i)) =
      Submodule.span κR (Set.range (b ∘ finSumFinEquiv.symm)) := by
        rw [happend]
    _ = Submodule.span κR (Set.range b) := by
        rw [hrangeb]
    _ = ⊤ := Module.Basis.span_eq b

/-- Helper for Lemma 15.35.2: linearly independent cotangent classes extend to a family that is
part of a regular system of parameters. -/
private theorem part_regularSystemOfParameters_of_toCotangent_linearIndependent
    {m : ℕ} (x : Fin m → maximalIdeal R)
    (hlin : LinearIndependent κR (fun j ↦ (maximalIdeal R).toCotangent (x j))) :
    IsPartOfRegularSystemOfParameters (maximalIdeal R).spanFinrank x := by
  -- First complete the independent family to one spanning the full cotangent space.
  obtain ⟨y, hspan⟩ :=
    append_toCotangent_span_top_of_linearIndependent (R := R) x hlin
  refine ⟨y, ?_⟩
  -- The completed family has the full regular-local length, so the span-top criterion applies.
  apply regularSystemOfParameters_of_toCotangent_span_top (R := R) (z := Fin.append x y)
  · have hspanFinrank :
        (maximalIdeal R).spanFinrank = Module.finrank κR (CotangentSpace R) :=
      IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)
    rw [hspanFinrank]
    exact Nat.add_sub_of_le (by simpa using hlin.cardinalMk_le_finrank)
  · simpa using hspan

/-- Helper for Lemma 15.35.2: for the localized polynomial source `Aφ`, the canonical map
`H₁(L_{κ(Aφ)/k}) → 𝔪_{Aφ} / 𝔪_{Aφ}²` is bijective. -/
private theorem localized_polynomial_source_h1Cotangent_to_cotangent_bijective :
    Function.Bijective (residueField_h1Cotangent_to_cotangent (k := k) (R := Aφ)) := by
  let K0 := ResidueField Aφ
  have hsurj :
      Function.Surjective (algebraMap Aφ K0) := by
    simpa [ResidueField.algebraMap_eq] using
      (residue_surjective : Function.Surjective (IsLocalRing.residue Aφ))
  have hflat :
      Function.Bijective (H1Cotangent.map k (MvPolynomial (Fin m) k) K0 K0) := by
    -- Proof comment: polynomial algebras are flat over the base field, so the owner flat-source
    -- comparison theorem applies directly to the residue field target `K0`.
    exact h1Cotangent_map_bijective_of_flat_source
      (R := k) (R' := MvPolynomial (Fin m) k) (T := K0)
  have hloc :
      Function.Bijective (H1Cotangent.map (MvPolynomial (Fin m) k) Aφ K0 K0) := by
    -- Proof comment: source localization does not change `H₁`, so passing from the polynomial
    -- ring to its localization at `pφ` is again a bijection on the owner `H₁` term.
    exact h1Cotangent_map_bijective_of_isLocalization_source
      (A := MvPolynomial (Fin m) k) (Aₛ := Aφ) (B := K0) pφ.primeCompl
  have hcomp :
      Function.Bijective (H1Cotangent.map k Aφ K0 K0) := by
    -- Proof comment: the owner map for `k → Aφ` factors through the polynomial ring
    -- presentation, so it is a composition of the two already-bijective comparison maps above.
    have hmap :
        H1Cotangent.map k Aφ K0 K0 =
          (H1Cotangent.map (MvPolynomial (Fin m) k) Aφ K0 K0).comp
            (H1Cotangent.map k (MvPolynomial (Fin m) k) K0 K0) := by
      funext x
      -- Route correction: compare the source-change maps through the canonical self-presentations
      -- rather than trying to synthesize a bespoke `H1Cotangent.map_comp` wrapper.
      simp only [H1Cotangent.map]
      let f₁ :=
        ((Generators.self k K0).defaultHom (Generators.self (MvPolynomial (Fin m) k) K0)).toExtensionHom
      let f₂ :=
        ((Generators.self (MvPolynomial (Fin m) k) K0).defaultHom (Generators.self Aφ K0)).toExtensionHom
      let f := ((Generators.self k K0).defaultHom (Generators.self Aφ K0)).toExtensionHom
      have hcomp_apply := (Extension.H1Cotangent.map_comp_apply f₁ f₂ x).symm
      have hEq :
          Extension.H1Cotangent.map (f₂.comp f₁) = Extension.H1Cotangent.map f :=
        Extension.H1Cotangent.map_eq _ _
      exact hcomp_apply.trans <| by
        simpa using congrArg (fun g ↦ g x) hEq
    rw [hmap]
    exact hloc.comp hflat
  -- Proof comment: the source cotangent bridge is the standard surjective-algebra equivalence
  -- composed with the owner map just shown to be bijective.
  simpa [residueField_h1Cotangent_to_cotangent, LinearMap.comp_apply] using
    (surjective_algebra_h1Cotangent_equiv_cotangent (A := Aφ) (B := K0) hsurj).bijective.comp hcomp

/-- Helper for Lemma 15.35.2: after pulling the source cotangent basis back along the bijective
map `H₁(L_{κ(Aφ)/k}) → 𝔪_{Aφ} / 𝔪_{Aφ}²`, each lifted basis vector still maps to the corresponding
source parameter class. -/
private theorem localized_polynomial_liftedSource_eq_source_toCotangent
    {d : ℕ} (x : Fin d → maximalIdeal Aφ) (hx : IsRegularSystemOfParameters x)
    (j : Fin d) :
    let sourceBasis :
        Basis (Fin d) (ResidueField Aφ) (maximalIdeal Aφ).Cotangent :=
      regularSystemOfParameters_cotangentBasis hx
    let liftedSource :
        Fin d → H1Cotangent k (ResidueField Aφ) :=
      fun i ↦ Function.invFun (residueField_h1Cotangent_to_cotangent (k := k) (R := Aφ))
        (sourceBasis i)
    residueField_h1Cotangent_to_cotangent (k := k) (R := Aφ) (liftedSource j) =
      (maximalIdeal Aφ).toCotangent (x j) := by
  intro sourceBasis liftedSource
  -- Proof comment: the pulled-back family is defined by `invFun`, so applying the bijection
  -- returns the original basis vector, which is the cotangent class of `x j`.
  have hsource :
      Function.Bijective (residueField_h1Cotangent_to_cotangent (k := k) (R := Aφ)) :=
    localized_polynomial_source_h1Cotangent_to_cotangent_bijective
      (k := k) (A := A) (p := p) (m := m) (φ := φ)
  calc
    residueField_h1Cotangent_to_cotangent (k := k) (R := Aφ) (liftedSource j) =
      sourceBasis j := by
        exact Function.rightInverse_invFun hsource.surjective (sourceBasis j)
    _ = (maximalIdeal Aφ).toCotangent (x j) := by
        simpa [sourceBasis] using regularSystemOfParameters_cotangentBasis_apply hx j

/-- Helper for Lemma 15.35.2: on the tensorized lifted source basis, the textbook square sends the
source `H₁` class to the cotangent class of the image parameter in `A`. -/
private theorem localized_polynomial_h1_to_target_cotangent_on_source_basis
    {d : ℕ} (x : Fin d → maximalIdeal Aφ) (hx : IsRegularSystemOfParameters x)
    (j : Fin d) :
    let K0 := ResidueField Aφ
    let K := ResidueField A
    let sourceBasis :
        Basis (Fin d) K0 (maximalIdeal Aφ).Cotangent :=
      regularSystemOfParameters_cotangentBasis hx
    let liftedSource :
        Fin d → H1Cotangent k K0 :=
      fun i ↦ Function.invFun (residueField_h1Cotangent_to_cotangent (k := k) (R := Aφ))
        (sourceBasis i)
    residueField_h1Cotangent_to_cotangent (k := k) (R := A)
      ((LinearMap.liftBaseChange K (H1Cotangent.map k k K0 K)) ((1 : K) ⊗ₜ[K0] liftedSource j)) =
        (maximalIdeal A).toCotangent
          (localized_polynomial_parameter_image (m := m) (φ := φ) x j) := by
  intro K0 K sourceBasis liftedSource
  -- TODO: unfold the outer owner definitions of `residueField_h1Cotangent_to_cotangent` on the
  -- target, rewrite the source basis vector by
  -- `localized_polynomial_liftedSource_eq_source_toCotangent`, and use the owner-map functoriality
  -- lemmas from `Lemma_15_33_6` and `Lemma_15_34_2` to identify the resulting `H₁` image with the
  -- cotangent class of `algebraMap Aφ A (x j)`.
  sorry

/-- Helper for Lemma 15.35.2: a regular system of parameters of the localized polynomial source
maps to cotangent classes in `A` that remain linearly independent. -/
private theorem localized_polynomial_parameter_images_toCotangent_linearIndependent
    (F : IntermediateField k (ResidueField A)) (hF : F.FG)
    (y : Fin m → F)
    (hresidue :
      ∀ i, residue A (φ (MvPolynomial.X i)) = algebraMap F (ResidueField A) (y i))
    (hy : LinearIndependent F (D k F ∘ y))
    (hspan : Submodule.span F (Set.range (D k F ∘ y)) = ⊤)
    {d : ℕ} (x : Fin d → maximalIdeal Aφ) (hx : IsRegularSystemOfParameters x) :
    LinearIndependent (ResidueField A)
      (fun j ↦
        (maximalIdeal A).toCotangent
          (localized_polynomial_parameter_image (m := m) (φ := φ) x j)) := by
  -- Proof comment: the source side is now reduced to a proved bijection
  -- `H₁(L_{κ(Aφ)/k}) ≃ 𝔪_{Aφ}/𝔪_{Aφ}²`, obtained by factoring through the polynomial ring and its
  -- localization. The remaining work is the textbook square chase sending the source cotangent
  -- basis attached to `x` through the left Jacobi-Zariski map and the target `H₁ → cotangent`
  -- injection.
  have hsource :
      Function.Bijective (residueField_h1Cotangent_to_cotangent (k := k) (R := Aφ)) :=
    localized_polynomial_source_h1Cotangent_to_cotangent_bijective
      (k := k) (A := A) (p := p) (m := m) (φ := φ)
  let K0 := ResidueField Aφ
  let K := ResidueField A
  let sourceBasis :
      Basis (Fin d) K0 (maximalIdeal Aφ).Cotangent :=
    regularSystemOfParameters_cotangentBasis hx
  let liftedSource :
      Fin d → H1Cotangent k K0 :=
    fun j ↦ Function.invFun (residueField_h1Cotangent_to_cotangent (k := k) (R := Aφ))
      (sourceBasis j)
  have hliftedSource :
      ∀ j,
        residueField_h1Cotangent_to_cotangent (k := k) (R := Aφ) (liftedSource j) = sourceBasis j := by
    intro j
    exact Function.rightInverse_invFun hsource.surjective (sourceBasis j)
  have htarget :
      Function.Injective (H1Cotangent.map k A K K) :=
    (geometricallyRegularLocalRing_h1Cotangent_map_injective_of_charP
      (k := k) (A := A) (p := p)).2
  have hfield :
      Function.Injective (LinearMap.liftBaseChange K (H1Cotangent.map k k K0 K)) :=
    field_jacobi_zariski_left_injective (K := k) (L := K0) (M := K)
  have hliftedSource_toCotangent :
      ∀ j,
        residueField_h1Cotangent_to_cotangent (k := k) (R := Aφ) (liftedSource j) =
          (maximalIdeal Aφ).toCotangent (x j) := by
    -- Proof comment: rewrite the pulled-back basis through the already-packaged source bijection.
    intro j
    simpa [sourceBasis, liftedSource] using
      localized_polynomial_liftedSource_eq_source_toCotangent
        (k := k) (A := A) (p := p) (m := m) (φ := φ) x hx j
  -- TODO: after the normalization above, finish the textbook square chase by combining the
  -- basis-level image formula
  -- `localized_polynomial_h1_to_target_cotangent_on_source_basis` with the injective maps
  -- `liftBaseChange K (H1Cotangent.map k k K0 K)` and `H1Cotangent.map k A K K`.
  let _ := hF
  let _ := hresidue
  let _ := hy
  let _ := hspan
  let _ := hliftedSource_toCotangent
  let _ := hsource
  let _ := hliftedSource
  let _ := htarget
  let _ := hfield
  sorry

end CotangentParameterBridge

-- Proof sketch: apply Proposition `15.35.1` to the localized polynomial source
-- `k[y₁, …, yₘ]_𝔭`, using that a polynomial algebra over a field is geometrically regular and that
-- the differentials `D k F (y i)` are linearly independent and span `Ω[F⁄k]`, so they identify the
-- residue-field cotangent map with the inclusion from
-- the finitely generated subextension `F ⊆ κ(A)`. The injectivity criterion then implies that the
-- localized map is flat and that the canonical closed fiber of `Aφ → A`, equivalently the
-- quotient of `A` by the image of the maximal ideal of `Aφ`, is a regular local ring.
/-- Lemma 15.35.2: let `k` be a field of characteristic `p > 0`, let `A` be a Noetherian local
`k`-algebra that is geometrically regular over `k`, and let `F ⊆ κ(A)` be a finitely generated
subextension with a polynomial presentation `k[y₁, …, yₘ] → A` whose residue-field values lie in
`F` and whose differentials are linearly independent and span `Ω[F⁄k]`. Then the localized map
`Aφ → A`, with `Aφ = Localization.AtPrime pφ` and `pφ = φ⁻¹(maximalIdeal A)`, is flat and its
canonical closed fiber `Ideal.Fiber (maximalIdeal Aφ) A`, equivalently the quotient
`A / Ideal.map (Aφ → A) (maximalIdeal Aφ)`, is a regular local ring. -/
@[stacks 07E6]
theorem localizedPolynomialSubextensionMap_flat_and_regular_closedFiber_of_geometricallyRegularLocalRing
    [IsGeometricallyRegular k A]
    (F : IntermediateField k (ResidueField A)) (hF : F.FG)
    (y : Fin m → F)
    (hresidue :
      ∀ i, residue A (φ (MvPolynomial.X i)) = algebraMap F (ResidueField A) (y i))
    (hy : LinearIndependent F (D k F ∘ y))
    (hspan : Submodule.span F (Set.range (D k F ∘ y)) = ⊤) :
    (localizedPolynomialSubextensionMap m φ).Flat ∧ IsRegularLocalRing ClosedFiber := by
  -- Route correction: isolate the textbook square chase into the single source-side helper
  -- `localized_polynomial_parameter_images_toCotangent_linearIndependent`, then let the Chapter 10
  -- parameter lemmas finish the flatness and regular-fiber conclusion formally.
  let _ : IsRegularLocalRing A := (geometricallyRegularLocalRing_h1Cotangent_map_injective_of_charP
    (k := k) (A := A) (p := p)).1
  let _ : IsRegularLocalRing Aφ :=
    localized_polynomial_source_isRegularLocalRing (m := m) (φ := φ)
  have hdim :
      ringKrullDim Aφ = (maximalIdeal Aφ).spanFinrank := by
    symm
    exact (isRegularLocalRing_iff Aφ).1 inferInstance
  obtain ⟨x, hx⟩ :=
    (isRegularLocalRing_iff_exists_regularSystemOfParameters (R := Aφ) hdim).mp inferInstance
  let z : Fin (maximalIdeal Aφ).spanFinrank → maximalIdeal A :=
    localized_polynomial_parameter_image (m := m) (φ := φ) x
  have hz_linearIndependent :
      LinearIndependent (ResidueField A)
        (fun j ↦ (maximalIdeal A).toCotangent (z j)) := by
    -- Proof comment: this is exactly the localized source-to-target cotangent comparison produced
    -- by the remaining helper.
    simpa [z] using
      localized_polynomial_parameter_images_toCotangent_linearIndependent
        (m := m) (φ := φ) F hF y hresidue hy hspan x hx
  have hz :
      IsPartOfRegularSystemOfParameters (maximalIdeal A).spanFinrank z :=
    part_regularSystemOfParameters_of_toCotangent_linearIndependent
      (R := A) z hz_linearIndependent
  -- Proof comment: with a source regular system of parameters whose image is part of one on `A`,
  -- the Chapter 10 parameter criterion yields flatness and regularity of the closed fiber.
  exact
    flat_and_regularFiber_of_parameter_image
      (P := Aφ) (Q := A) x z hx
      (by
        intro i
        rfl)
      hz

end LocalizedPolynomialSubextensionMap

end

end Algebra
