import Mathlib
import Mathlib.Tactic.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_140_1 (from Chap10) -/
open scoped TensorProduct

universe u v

noncomputable section

variable {k : Type u} {S : Type v}
variable [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S] [IsAlgClosed k]
variable (m : Ideal S) [m.IsMaximal]

attribute [local instance] Ideal.Quotient.field

/- Domain-style sampling for Lemma 10.140.1:
- primary domain: the conormal sequence at a maximal ideal and the closed-point fiber of Kähler
  differentials over an algebraically closed base field;
- sampled owner declarations:
  `KaehlerDifferential.kerCotangentToTensor`,
  `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`,
  `finite_residueField_of_isMaximal_of_finiteType`,
  `Ideal.bijective_algebraMap_quotient_residueField`;
- best owner abstraction: the canonical conormal map
  `KaehlerDifferential.kerCotangentToTensor k S m.ResidueField`;
- primitive data: the maximal ideal `m` in the finite type `k`-algebra `S`;
- derived API: exactness of the conormal sequence, the finite closed-point residue field supplied
  by Hilbert Nullstellensatz, and the quotient-residue comparison for maximal ideals.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma for a closed point over an algebraically closed field,
  asserting equality of the cotangent-space dimension and the Kähler-fiber dimension at `m`;
- `core/canonical`: the conormal owner map `KaehlerDifferential.kerCotangentToTensor k S
  m.ResidueField` and its exactness API;
- `bridge/view`: the maximal-ideal equivalence between `S ⧸ m` and `m.ResidueField`, used only to
  present the closed-point fiber in the quotient form used downstream. -/

-- Proof sketch: the conormal exact sequence for the surjective residue map `S → m.ResidueField`
-- gives `m / m² → m.ResidueField ⊗[S] Ω[S⁄k] → Ω[m.ResidueField⁄k] → 0`. For a maximal ideal of a
-- finite type algebra over an algebraically closed field, Hilbert Nullstellensatz identifies the
-- closed-point residue field with a finite extension of `k`, and the algebraically closed base
-- hypothesis places this in the source-faithful closed-point case where the terminal Kähler term
-- vanishes. Exactness then identifies the Kähler fiber with the cotangent space, and the
-- quotient-residue comparison rewrites the result in the downstream quotient form.
/-- Lemma 10.140.1: if `k` is algebraically closed, `S` is a finite type `k`-algebra, and `m` is
a maximal ideal of `S`, then the closed-point fiber of `Ω[S⁄k]` at `m` and the cotangent space
`m / m²` have the same `κ(m) = S ⧸ m`-dimension. -/
theorem finrank_kaehlerFiber_eq_finrank_cotangent :
    Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) =
      Module.finrank (S ⧸ m) m.Cotangent := by
  let eResidue : (S ⧸ m) ≃ₐ[k] m.ResidueField :=
    AlgEquiv.ofBijective
      (IsScalarTower.toAlgHom k (S ⧸ m) m.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField m)
  letI : Module.Finite k m.ResidueField :=
    finite_residueField_of_isMaximal_of_finiteType k m
  letI : Module.Finite k (S ⧸ m) := Module.Finite.equiv eResidue.toLinearEquiv.symm
  letI : Algebra.IsIntegral k (S ⧸ m) := Algebra.IsIntegral.of_finite k (S ⧸ m)
  let eBase : k ≃ₐ[k] (S ⧸ m) :=
    AlgEquiv.ofBijective
      (Algebra.ofId k (S ⧸ m))
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k))
  let β : S ⧸ m →ₐ[k] S :=
    (Algebra.ofId k S).comp eBase.symm.toAlgHom
  have hβ : (IsScalarTower.toAlgHom k S (S ⧸ m)).comp β = AlgHom.id k (S ⧸ m) := by
    ext x
    change eBase (eBase.symm x) = x
    simpa using eBase.apply_symm_apply x
  have hsurjQuot : Function.Surjective (algebraMap S (S ⧸ m)) := by
    simpa using (Ideal.Quotient.mkₐ_surjective k m)
  have hsurjBase : Function.Surjective (algebraMap k (S ⧸ m)) := by
    simpa using eBase.surjective
  letI : Subsingleton Ω[S ⧸ m⁄k] :=
    KaehlerDifferential.subsingleton_of_surjective k (S ⧸ m) hsurjBase
  have hker : RingHom.ker (algebraMap S (S ⧸ m)) = m := by
    simpa using (Ideal.Quotient.mkₐ_ker k m)
  let eCot :
      m.Cotangent ≃ₗ[S] (RingHom.ker (algebraMap S (S ⧸ m))).Cotangent :=
    Ideal.Cotangent.equivOfEq m (RingHom.ker (algebraMap S (S ⧸ m))) hker.symm
  let cotangentToTensor :
      m.Cotangent →ₗ[S] ((S ⧸ m) ⊗[S] Ω[S⁄k]) :=
    (KaehlerDifferential.kerCotangentToTensor k S (S ⧸ m)).comp eCot.toLinearMap
  letI : IsScalarTower k (S ⧸ m) m.Cotangent :=
    Module.IsTorsionBySet.isScalarTower (Ideal.isTorsionBySet_cotangent (R := S) (I := m))
  let cotangentToTensorOverQuotient :
      m.Cotangent →ₗ[S ⧸ m] ((S ⧸ m) ⊗[S] Ω[S⁄k]) :=
    (cotangentToTensor.restrictScalars k).extendScalarsOfSurjective hsurjBase
  -- The source proof identifies the closed point with the base field, so the quotient map splits.
  have hsplit :
      Function.Exact
          (KaehlerDifferential.kerCotangentToTensor k S (S ⧸ m))
          (KaehlerDifferential.mapBaseChange k S (S ⧸ m)) ∧
        Function.Surjective (KaehlerDifferential.mapBaseChange k S (S ⧸ m)) ∧
        ∃ l : (S ⧸ m) ⊗[S] Ω[S⁄k] →ₗ[S]
            (RingHom.ker (algebraMap S (S ⧸ m))).Cotangent,
          l ∘ₗ KaehlerDifferential.kerCotangentToTensor k S (S ⧸ m) = LinearMap.id :=
    kaehlerDifferential_conormal_sequence_split_of_section k S (S ⧸ m) β hβ
  obtain ⟨-, -, lOwner, hlOwner⟩ := hsplit
  let leftInverse :
      ((S ⧸ m) ⊗[S] Ω[S⁄k]) →ₗ[S] m.Cotangent :=
    eCot.symm.toLinearMap.comp lOwner
  have hleftInverse :
      leftInverse.comp cotangentToTensor = LinearMap.id := by
    ext x
    have hx := LinearMap.congr_fun hlOwner (eCot x)
    rw [LinearMap.comp_apply, LinearMap.id_apply]
    change eCot.symm (lOwner ((KaehlerDifferential.kerCotangentToTensor k S (S ⧸ m)) (eCot x))) = x
    have hx' :
        lOwner ((KaehlerDifferential.kerCotangentToTensor k S (S ⧸ m)) (eCot x)) = eCot x := by
      simpa using hx
    rw [hx']
    exact eCot.symm_apply_apply x
  have hInjective :
      Function.Injective cotangentToTensorOverQuotient := by
    have hLeftInverseFun : Function.LeftInverse leftInverse cotangentToTensor := by
      intro x
      exact LinearMap.congr_fun hleftInverse x
    have hInjectiveS : Function.Injective cotangentToTensor := hLeftInverseFun.injective
    simpa [cotangentToTensorOverQuotient] using hInjectiveS
  -- Since `Ω[(S ⧸ m)⁄k] = 0`, exactness forces the conormal map to be surjective as well.
  have hExact :
      Function.Exact cotangentToTensor (KaehlerDifferential.mapBaseChange k S (S ⧸ m)) :=
    (kaehlerDifferential_exact_cotangent_tensor_of_surjective
      (R := k) (S := S) (S' := S ⧸ m) m hker hsurjQuot).1
  have hMapBaseChangeZero :
      ((KaehlerDifferential.mapBaseChange k S (S ⧸ m)) :
        ((S ⧸ m) ⊗[S] Ω[S⁄k]) →ₗ[S] Ω[S ⧸ m⁄k]) = 0 := by
    exact Subsingleton.elim _ _
  have hSurjective :
      Function.Surjective cotangentToTensorOverQuotient := by
    have hSurjectiveS : Function.Surjective cotangentToTensor := by
      have hKer :
          LinearMap.ker
              (((KaehlerDifferential.mapBaseChange k S (S ⧸ m)) :
                ((S ⧸ m) ⊗[S] Ω[S⁄k]) →ₗ[S] Ω[S ⧸ m⁄k])) = ⊤ := by
        rw [hMapBaseChangeZero, LinearMap.ker_zero]
      rw [← LinearMap.range_eq_top]
      rw [← Function.Exact.linearMap_ker_eq hExact]
      exact hKer
    intro x
    obtain ⟨y, hy⟩ := hSurjectiveS x
    exact ⟨y, hy⟩
  -- The conormal map is therefore a quotient-linear equivalence, and finrank is preserved.
  let eFiber :
      m.Cotangent ≃ₗ[S ⧸ m] ((S ⧸ m) ⊗[S] Ω[S⁄k]) :=
    LinearEquiv.ofBijective cotangentToTensorOverQuotient ⟨hInjective, hSurjective⟩
  simpa using eFiber.finrank_eq.symm

end

/-! ### Lemma_10_140_2 (from Chap10) -/
open scoped TensorProduct

universe u v

section

variable {k : Type u} {S : Type v}
variable [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S] [IsAlgClosed k]
variable (m : Ideal S) [m.IsMaximal]

attribute [local instance] Ideal.Quotient.field

/- Domain-style sampling for Lemma 10.140.2:
- primary domain: smoothness and regularity criteria at a closed point of a finite type
  `k`-algebra, expressed via the Kähler fiber and the cotangent space;
- sampled owner declarations:
  `smoothAtPrime_iff_isSmoothAt`,
  `isSmoothAt_tfae_finrank_kaehlerFiber_le_eq`,
  `isRegularLocalRing_of_isSmoothAt`,
  `finrank_kaehlerFiber_eq_finrank_cotangent`;
- best owner abstraction: the core/canonical owner is the primewise criterion
  `IsSmoothAt k q.asIdeal`, with the present file staying `source-facing` by packaging the closed
  point `q = ⟨m, inferInstance⟩`, the quotient-fiber form `κ(m) = S ⧸ m`, and the extra regular
  local clause from the Stacks statement;
- primitive data: the maximal ideal `m` of the finite type `k`-algebra `S`;
- derived API: the quotient presentation of the Kähler fiber at `m`, the cotangent comparison from
  `Lemma 10.140.1`, and the regular-local clause on `Localization.AtPrime m`.

Source/core/bridge triage:
- `source-facing`: the four-way closed-point `List.TFAE` statement in the quotient form used by the
  source text;
- `core/canonical`: `IsSmoothAt k m`, `IsRegularLocalRing (Localization.AtPrime m)`, and the
  prime-level three-way TFAE from `Lemma 10.140.3`;
- `bridge/view`: `smoothAtPrime_iff_isSmoothAt` and the closed-point quotient bridge
  `finrank_kaehlerFiber_eq_finrank_cotangent`. -/

private theorem smoothAtPrime_tfae_finrank_kaehlerFiber_le_eq :
    List.TFAE
      ([ Algebra.SmoothAtPrime k S ⟨m, inferInstance⟩
      , Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) ≤ ringKrullDim (Localization.AtPrime m)
      , Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) = ringKrullDim (Localization.AtPrime m) ] :
        List Prop) := by
  letI : Algebra.FinitePresentation k S :=
    (show Algebra.FiniteType k S ↔ Algebra.FinitePresentation k S from
      Algebra.FinitePresentation.of_finiteType).mp inferInstance
  let q : PrimeSpectrum S := ⟨m, inferInstance⟩
  have howner :
      List.TFAE
        [ Algebra.IsSmoothAt k m
        , Module.finrank (Ideal.ResidueField m)
            ((Ideal.ResidueField m) ⊗[S] Ω[S⁄k]) ≤ ringKrullDim (Localization.AtPrime m)
        , Module.finrank (Ideal.ResidueField m)
            ((Ideal.ResidueField m) ⊗[S] Ω[S⁄k]) = ringKrullDim (Localization.AtPrime m) ] :=
    Algebra.isSmoothAt_tfae_finrank_kaehlerFiber_le_eq m
  have hsmooth :
      Algebra.SmoothAtPrime k S q ↔ Algebra.IsSmoothAt k q.asIdeal :=
    Algebra.smoothAtPrime_iff_isSmoothAt k S q
  have hfiber :
      Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) =
        Module.finrank (S ⧸ m) m.Cotangent :=
    finrank_kaehlerFiber_eq_finrank_cotangent m
  sorry

-- Proof sketch: Lemma `10.140.1` identifies the Kähler-differential fiber
-- `κ(m) ⊗[S] Ω[S⁄k]` with the cotangent space `m / m²`, so clauses `(1)`, `(2)`, and `(3)` are
-- equivalent by the regular-local criterion comparing dimension with embedding dimension. If
-- `SmoothAtPrime k S ⟨m, inferInstance⟩` holds, then standard smoothness on a basic open
-- neighborhood gives a free Kähler module of rank equal to the local dimension, yielding
-- regularity of `S_m`. Conversely, if `S_m` is regular, cut out a local complete intersection
-- presentation near `m` and apply the Jacobian criterion to obtain `SmoothAtPrime k S
-- ⟨m, inferInstance⟩`.
/-- Lemma 10.140.2: for an algebraically closed field `k`, a finite type `k`-algebra `S`, and a
maximal ideal `m ⊂ S`, the following are equivalent: the local ring `Sₘ`, formalized as
`Localization.AtPrime m`, is regular; the fiber of `Ω[S⁄k]` at `m` has dimension at most
`dim(Sₘ)` over `κ(m) = S ⧸ m`; the same fiber dimension equals `dim(Sₘ)`; and `S/k` is smooth at
`m`, formalized as `Algebra.SmoothAtPrime k S ⟨m, inferInstance⟩`. -/
theorem regularLocalRing_finrank_kaehlerFiber_le_eq_and_exists_smoothLocalization_tfae :
    List.TFAE
      ([ IsRegularLocalRing (Localization.AtPrime m)
      , Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) ≤ ringKrullDim (Localization.AtPrime m)
      , Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) = ringKrullDim (Localization.AtPrime m)
      , Algebra.SmoothAtPrime k S ⟨m, inferInstance⟩ ] : List Prop) := by
  letI : Algebra.FinitePresentation k S :=
    (show Algebra.FiniteType k S ↔ Algebra.FinitePresentation k S from
      Algebra.FinitePresentation.of_finiteType).mp inferInstance
  have hcore :
      List.TFAE
        ([ Algebra.SmoothAtPrime k S ⟨m, inferInstance⟩
        , Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) ≤ ringKrullDim (Localization.AtPrime m)
        , Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) = ringKrullDim (Localization.AtPrime m) ] :
          List Prop) :=
    smoothAtPrime_tfae_finrank_kaehlerFiber_le_eq m
  let q : PrimeSpectrum S := ⟨m, inferInstance⟩
  have hsmooth :
      Algebra.SmoothAtPrime k S q ↔ Algebra.IsSmoothAt k q.asIdeal :=
    Algebra.smoothAtPrime_iff_isSmoothAt k S q
  have hregular_of_smooth :
      Algebra.SmoothAtPrime k S q → IsRegularLocalRing (Localization.AtPrime m) := by
    intro h
    exact Algebra.isRegularLocalRing_of_isSmoothAt q.asIdeal (hsmooth.mp h)
  have hfiber :
      Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) =
        Module.finrank (S ⧸ m) m.Cotangent :=
    finrank_kaehlerFiber_eq_finrank_cotangent m
  sorry

end

/-! ### Lemma_10_140_3 (from Chap10) -/
open scoped TensorProduct

universe u v

namespace Algebra

section

variable {k : Type u} {S : Type v}
variable [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/-
Domain-style sampling for Lemma 10.140.3:
- primary domain: smoothness at a prime ideal of a finite type algebra over a field, expressed via
  the residue-field fiber of Kähler differentials and regularity of the localized ring;
- sampled owner declarations:
  `Algebra.IsSmoothAt`,
  `Algebra.smoothAtPrime_iff_isSmoothAt`,
  `IsRegularLocalRing.iff_finrank_cotangentSpace`,
  `finrank_kaehlerFiber_eq_finrank_cotangent`;
- best owner abstraction: the canonical owner is the prime-ideal predicate `Algebra.IsSmoothAt k q`
  for `q : Ideal S` with `[q.IsPrime]`; the corresponding residue-field fiber
  `Ideal.ResidueField q ⊗[S] Ω[S⁄k]` and localized ring `Localization.AtPrime q` are derived data
  on that owner, so the public theorems should live directly at the ideal level rather than
  through a parallel `PrimeSpectrum S` wrapper;
- primitive data: a prime ideal `q : Ideal S`;
- derived API: the finrank comparison on the Kähler fiber and the regular-local consequence for
  `Localization.AtPrime q`.

Source/core/bridge triage:
- `source-facing`: the primewise TFAE and the regular-local consequence stated for the given prime;
- `core/canonical`: `Algebra.IsSmoothAt k q`;
- `bridge/view`: the `PrimeSpectrum S` presentation used downstream in `SmoothAtPrime`-style
  statements and the maximal-ideal quotient bridge from `Lemma 10.140.1`.
-/

-- Proof sketch: first pass to an algebraic closure `K / k` and choose a maximal ideal of
-- `K ⊗[k] S` lying over `q`. The local smoothness condition `IsSmoothAt k q` transfers to
-- the lifted maximal ideal after base change, while base change for Kähler differentials
-- identifies the fiber dimension with the one over `q`. Then Lemma `10.140.2` gives the
-- equivalence between smoothness and the inequality/equality of the cotangent-space dimension at
-- the lifted maximal ideal, and the result descends back to `q`.
/-- Lemma 10.140.3: for a finite type `k`-algebra `S` over a field and a prime `q` of `S`, the
following are equivalent: `S` is smooth at `q` over `k`, formalized as `IsSmoothAt k q`;
the fiber of `Ω[S⁄k]` at `q` has `κ(q)`-dimension at most `dim(S_q)`; the same fiber dimension
equals `dim(S_q)`. -/
theorem isSmoothAt_tfae_finrank_kaehlerFiber_le_eq (q : Ideal S) [q.IsPrime] :
    List.TFAE
      [ IsSmoothAt k q
      , Module.finrank (Ideal.ResidueField q)
          ((Ideal.ResidueField q) ⊗[S] Ω[S⁄k]) ≤ ringKrullDim (Localization.AtPrime q)
      , Module.finrank (Ideal.ResidueField q)
          ((Ideal.ResidueField q) ⊗[S] Ω[S⁄k]) = ringKrullDim (Localization.AtPrime q) ] := sorry

-- Proof sketch: after base change to an algebraic closure of `k`, the smoothness hypothesis gives
-- a smooth point on the base-changed algebra lying over `q`. Lemma `10.140.2` makes the
-- corresponding localized ring regular, and Lemma `10.110.9` descends regularity along the flat
-- local map from `S_q` to that localized base change.
/-- If `S` is smooth at the prime `q` over the field `k`, formalized as `IsSmoothAt k q`,
then the local ring `S_q` is regular. -/
theorem isRegularLocalRing_of_isSmoothAt (q : Ideal S) [q.IsPrime] (hsmooth : IsSmoothAt k q) :
    IsRegularLocalRing (Localization.AtPrime q) := sorry

end

end Algebra

/-! ### Lemma_10_140_4 (from Chap10) -/
open scoped TensorProduct
open IsLocalRing

universe u v

noncomputable section

variable (k : Type u) (R : Type v)
  [Field k] [CommRing R] [Algebra k R] [IsLocalRing R]

/- Domain-style sampling for Lemma 10.140.4:
- primary domain: the conormal map for the residue-field quotient of a local `k`-algebra and its
  split-injectivity via formal smoothness of the residue-field extension;
- sampled owner declarations:
  `KaehlerDifferential.kerCotangentToTensor`,
  `FormallySmooth.liftOfSurjective`,
  `retractionKerCotangentToTensorEquivSection`,
  `Algebra.formallySmooth_of_isSeparableOver`;
- best owner abstraction: the canonical conormal map
  `KaehlerDifferential.kerCotangentToTensor k R (ResidueField R)`;
- primitive data: the surjective algebra map `R → ResidueField R` and the source-facing
  separability hypothesis on `ResidueField R / k`;
- derived API: the split retraction of the conormal map coming from formal smoothness, and the
  resulting injectivity.

Source/core/bridge triage:
- `source-facing`: the injectivity statement for the cotangent-space map of a local `k`-algebra;
- `core/canonical`: `KaehlerDifferential.kerCotangentToTensor` together with the formal-smooth
  lifting owner `FormallySmooth.liftOfSurjective`;
- `bridge/view`: the identification of `ker (R → ResidueField R)` with the maximal ideal
  via `IsLocalRing.ker_residue`, which explains the cotangent-space reading but is not a second
  owner. -/

-- Proof sketch: `ResidueField R / k` is formally smooth by the chapter field-extension owner
-- `Algebra.formallySmooth_of_isSeparableOver`. Lift the identity map of `ResidueField R` across
-- the square-zero surjection `(R ⧸ m²) → ResidueField R`, obtained as the canonical
-- `kerSquareLift` of `R → ResidueField R`. The resulting section is converted by
-- `retractionKerCotangentToTensorEquivSection` into a retraction of
-- `KaehlerDifferential.kerCotangentToTensor k R (ResidueField R)`, so the conormal map is
-- injective.
/-- Lemma 10.140.4: if `R` is a local `k`-algebra whose residue field is separable over `k` in the
Stacks Project sense, then the differential induces an
injective map from the cotangent space `m/m²` to the residue-field base change of `Ω[R⁄k]`;
equivalently, the canonical conormal map for `R → ResidueField R` is injective. -/
theorem residueCotangentToKaehler_injective_of_isSeparableOver
    [Algebra.IsSeparableOver k (ResidueField R)] :
    Function.Injective (KaehlerDifferential.kerCotangentToTensor k R (ResidueField R)) := by
  have hresidueSurj : Function.Surjective (IsLocalRing.residue R) := residue_surjective
  have hsurj : Function.Surjective (algebraMap R (ResidueField R)) := by
    simpa [ResidueField.algebraMap_eq] using hresidueSurj
  have hsurjLift :
      Function.Surjective (IsScalarTower.toAlgHom k R (ResidueField R)).kerSquareLift := by
    exact Ideal.Quotient.lift_surjective_of_surjective _ _ hsurj
  have hsqz :
      RingHom.ker (IsScalarTower.toAlgHom k R (ResidueField R)).kerSquareLift.toRingHom ^ 2 = ⊥ := by
    rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]
  let σ : ResidueField R →ₐ[k] R ⧸ RingHom.ker (algebraMap R (ResidueField R)) ^ 2 :=
    Algebra.FormallySmooth.liftOfSurjective
      (AlgHom.id k (ResidueField R))
      (IsScalarTower.toAlgHom k R (ResidueField R)).kerSquareLift
      hsurjLift
      ⟨2, hsqz⟩
  have hσ :
      (IsScalarTower.toAlgHom k R (ResidueField R)).kerSquareLift.comp σ =
        AlgHom.id k (ResidueField R) := by
    simpa [σ] using
      (Algebra.FormallySmooth.comp_liftOfSurjective
        (AlgHom.id k (ResidueField R))
        (IsScalarTower.toAlgHom k R (ResidueField R)).kerSquareLift
        hsurjLift
        ⟨2, hsqz⟩ : _)
  obtain ⟨l, hl⟩ := ((retractionKerCotangentToTensorEquivSection hsurj).symm ⟨σ, hσ⟩)
  exact LinearMap.injective_of_comp_eq_id _ _ hl

end

/-! ### Lemma_10_140_5 (from Chap10) -/
universe u v

namespace Algebra

section

variable {k : Type u} {S : Type v}
variable [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/-
Domain-style sampling for Lemma 10.140.5:
- primary domain: smoothness at a prime of a finite type algebra over a field versus regularity of
  the corresponding local ring, under a separable residue-field hypothesis;
- sampled owner declarations:
  `Algebra.IsSmoothAt`,
  `Algebra.isRegularLocalRing_of_isSmoothAt`,
  `residueCotangentToKaehler_injective_of_isSeparableOver`,
  `IsRegularLocalRing.iff_finrank_cotangentSpace`;
- best owner abstraction: the canonical owner is the ideal-level predicate `IsSmoothAt k q` for a
  prime ideal `q : Ideal S`; the prime-spectrum presentation is only a bridge/view, since the
  mathematical payload is entirely carried by `q`, `q.ResidueField`, and `Localization.AtPrime q`;
- primitive data: a prime ideal `q : Ideal S` and the Stacks-project separability hypothesis
  `IsSeparableOver k q.ResidueField`;
- derived API: the regular-local condition on `Localization.AtPrime q` and the resulting
  equivalence with `IsSmoothAt k q`.

Source/core/bridge triage:
- `source-facing`: the Stacks equivalence between smoothness at `q` and regularity of `S_q` under
  separability of `κ(q) / k`;
- `core/canonical`: `IsSmoothAt k q` and `IsRegularLocalRing (Localization.AtPrime q)`;
- `bridge/view`: a `PrimeSpectrum S` wrapper, which is not retained as the main owner surface. -/

-- Proof sketch: one direction is Lemma `10.140.3`, which shows that smoothness at `q` implies the
-- regularity of `S_q`. For the converse, use Lemma `10.140.4` and the conormal exact sequence from
-- Lemma `10.131.9` to identify the dimension of the Kähler-differential fiber with the embedding
-- dimension of `S_q`; the Stacks-project separability hypothesis on `κ(q) / k` and Lemma
-- `10.116.3` then turn regularity into the equality criterion in Lemma `10.140.3`.
/-- Lemma 10.140.5: let `q` be a prime of the finite type `k`-algebra `S` and assume the residue
field `κ(q) = q.ResidueField` is separable over `k` in the Stacks Project sense. Then `S` is
smooth at `q` over `k`
if and only if the local ring `S_q`, formalized as `Localization.AtPrime q`, is a regular local
ring. -/
theorem isSmoothAt_iff_isRegularLocalRing_of_separable_residueField
    (q : Ideal S) [q.IsPrime] [IsSeparableOver k q.ResidueField] :
    IsSmoothAt k q ↔ IsRegularLocalRing (Localization.AtPrime q) := sorry

end

end Algebra

/-! ### Lemma_10_140_6 (from Chap10) -/
universe u v

section

open KaehlerDifferential

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S] [Algebra ℚ S]
variable (f : S)

/-- Helper for Lemma 10.140.6: the derivation corresponding to an `S`-linear functional on
`Ω[S⁄R]` evaluates on `x` by applying the functional to `dx`. -/
private theorem linearMapEquivDerivation_apply_D
    (θ : Ω[S⁄R] →ₗ[S] S) (x : S) :
    ((KaehlerDifferential.linearMapEquivDerivation R S) θ) x = θ (D R S x) := by
  -- This is the universal-property bridge from linear maps on `Ω[S⁄R]` to derivations.
  simpa using
    (Derivation.liftKaehlerDifferential_comp_D
      (((KaehlerDifferential.linearMapEquivDerivation R S) θ)) x)

/-- Helper for Lemma 10.140.6: membership in a power of the principal ideal `(f)` is equivalent to
being a right multiple of `f ^ n`. -/
private theorem mem_span_singleton_pow_iff_exists_mul
    (a f : S) (n : ℕ) :
    a ∈ (Ideal.span ({f} : Set S)) ^ n ↔ ∃ b : S, a = f ^ n * b := by
  -- Rewrite principal-ideal powers and then unpack principal-ideal membership as divisibility.
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, by simpa [mul_comm] using hb⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, by simp [mul_comm]⟩

/-- Helper for Lemma 10.140.6: over a `ℚ`-algebra, a nonzero natural-number scalar cannot kill an
element. -/
private theorem eq_zero_of_nat_smul_eq_zero
    [Nontrivial S] (n : ℕ) (a : S) (hn : n ≠ 0) (h : n • a = 0) :
    a = 0 := by
  -- Convert the `ℕ`-smul relation to a `ℚ`-smul relation and cancel the nonzero scalar.
  rw [← Nat.cast_smul_eq_nsmul ℚ] at h
  have hnq : ((n : ℚ) : ℚ) ≠ 0 := by
    exact_mod_cast hn
  rcases smul_eq_zero.mp h with hzero | ha
  · exact (hnq hzero).elim
  · exact ha

/-- Helper for Lemma 10.140.6: a derivation with `δ(f) = 1` rules out nilpotence of `f`. -/
private theorem not_isNilpotent_of_derivation_eq_one
    [Nontrivial S] (δ : Derivation R S S) (hδf : δ f = 1) :
    ¬ IsNilpotent f := by
  intro hf
  -- Apply the derivation to the minimal nilpotence relation and cancel the nonzero scalar.
  have hpow : f ^ nilpotencyClass f = 0 := pow_nilpotencyClass hf
  have hderiv : nilpotencyClass f • f ^ (nilpotencyClass f - 1) = 0 := by
    simpa [hδf] using congrArg δ hpow
  have hzero : f ^ (nilpotencyClass f - 1) = 0 := by
    exact eq_zero_of_nat_smul_eq_zero
      (nilpotencyClass f) (f ^ (nilpotencyClass f - 1))
      (Nat.ne_of_gt <| (pos_nilpotencyClass_iff.mpr hf)) hderiv
  exact pow_pred_nilpotencyClass hf hzero

/-- Helper for Lemma 10.140.6: if `δ(f) = 1` and `f * a = 0`, then `a` lies in every power of the
principal ideal `(f)`. -/
private theorem factorization_step_of_derivation_eq_one
    [Nontrivial S] (δ : Derivation R S S) (hδf : δ f = 1)
    (a b : S) (n : ℕ) (hfa : f * a = 0) (hab : a = f ^ n * b) :
    ∃ c : S, a = f ^ (n + 1) * c := by
  -- Route correction: switch from ideal-membership induction to the source-faithful
  -- factorization induction `a = f^n * b`, so differentiation only sees a single product.
  have hpowMulZero : f ^ (n + 1) * b = 0 := by
    -- Rewrite the annihilator relation using the current factorization of `a`.
    calc
      f ^ (n + 1) * b = f * a := by
        rw [pow_succ', hab, mul_assoc]
      _ = 0 := hfa
  have hpowDeriv : δ (f ^ (n + 1)) = (n + 1) • f ^ n := by
    -- Differentiate the power and simplify using `δ(f) = 1`.
    calc
      δ (f ^ (n + 1)) = (n + 1) • f ^ ((n + 1) - 1) • δ f := by
        rw [Derivation.leibniz_pow]
      _ = (n + 1) • f ^ n • (1 : S) := by simp [hδf]
      _ = (n + 1) • f ^ n := by simp
  have hderivZero : δ (f ^ (n + 1) * b) = 0 := by
    -- Apply the derivation to the zero relation `f^(n+1) * b = 0`.
    simpa using congrArg δ hpowMulZero
  have hscaled : (n + 1 : S) * a + f ^ (n + 1) * δ b = 0 := by
    -- After Leibniz, rewrite the differentiated power term back in terms of `a`.
    rw [Derivation.leibniz, hpowDeriv] at hderivZero
    simpa [smul_eq_mul, nsmul_eq_mul, hab, pow_succ', mul_assoc, mul_left_comm, mul_comm,
      add_comm]
      using hderivZero
  have hscaledRat : ((n + 1 : ℚ) : ℚ) • a + f ^ (n + 1) * δ b = 0 := by
    -- Rewrite the cast multiple as scalar multiplication by the corresponding rational.
    simpa [Algebra.smul_def] using hscaled
  have hq_ne_zero : ((n + 1 : ℚ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hrescaled :
      a + ((n + 1 : ℚ) : ℚ)⁻¹ • (f ^ (n + 1) * δ b) = 0 := by
    -- Multiply the relation by `(n + 1)⁻¹` in the `ℚ`-module `S`.
    have htmp :=
      congrArg (fun x : S => ((n + 1 : ℚ) : ℚ)⁻¹ • x) hscaledRat
    simpa [smul_add, smul_smul, hq_ne_zero] using htmp
  have hsmul_mul :
      ((n + 1 : ℚ) : ℚ)⁻¹ • (f ^ (n + 1) * δ b) =
        f ^ (n + 1) * (((n + 1 : ℚ) : ℚ)⁻¹ • δ b) := by
    -- Move the rational scalar from the whole product to the second factor.
    rw [Algebra.smul_def, Algebra.smul_def]
    calc
      algebraMap ℚ S (((n + 1 : ℚ) : ℚ)⁻¹) * (f ^ (n + 1) * δ b)
          = (algebraMap ℚ S (((n + 1 : ℚ) : ℚ)⁻¹) * f ^ (n + 1)) * δ b := by
            rw [mul_assoc]
      _ = (f ^ (n + 1) * algebraMap ℚ S (((n + 1 : ℚ) : ℚ)⁻¹)) * δ b := by
            rw [mul_comm (algebraMap ℚ S (((n + 1 : ℚ) : ℚ)⁻¹)) (f ^ (n + 1))]
      _ = f ^ (n + 1) * (algebraMap ℚ S (((n + 1 : ℚ) : ℚ)⁻¹) * δ b) := by
            rw [← mul_assoc]
  refine ⟨-(((n + 1 : ℚ) : ℚ)⁻¹ • δ b), ?_⟩
  -- Repackage the rescaled relation as one extra factor of `f`.
  calc
    a = -(((n + 1 : ℚ) : ℚ)⁻¹ • (f ^ (n + 1) * δ b)) := by
      exact eq_neg_iff_add_eq_zero.mpr hrescaled
    _ = -(f ^ (n + 1) * (((n + 1 : ℚ) : ℚ)⁻¹ • δ b)) := by
      rw [hsmul_mul]
    _ = f ^ (n + 1) * (-(((n + 1 : ℚ) : ℚ)⁻¹ • δ b)) := by
      rw [neg_mul_eq_mul_neg]

/-- Helper for Lemma 10.140.6: if `δ(f) = 1` and `f * a = 0`, then `a` factors as `f ^ n` times
some element for every `n`. -/
private theorem exists_factor_of_mul_eq_zero_of_derivation_eq_one
    [Nontrivial S] (δ : Derivation R S S) (hδf : δ f = 1)
    (a : S) (hfa : f * a = 0) (n : ℕ) :
    ∃ b : S, a = f ^ n * b := by
  induction n with
  | zero =>
      -- The base case is the trivial factorization `a = f^0 * a`.
      refine ⟨a, ?_⟩
      simp
  | succ n ih =>
      -- The induction step differentiates the zero relation for the current factorization.
      rcases ih with ⟨b, hb⟩
      exact factorization_step_of_derivation_eq_one
        (R := R) (S := S) (f := f) δ hδf a b n hfa hb

/-- Helper for Lemma 10.140.6: if `δ(f) = 1` and `f * a = 0`, then `a` lies in every power of the
principal ideal `(f)`. -/
private theorem mem_span_singleton_pow_of_mul_eq_zero_of_derivation_eq_one
    [Nontrivial S] (δ : Derivation R S S) (hδf : δ f = 1)
    (a : S) (hfa : f * a = 0) (n : ℕ) :
    a ∈ (Ideal.span ({f} : Set S)) ^ n := by
  -- Convert the source-faithful factorization induction back into principal-ideal membership.
  rcases exists_factor_of_mul_eq_zero_of_derivation_eq_one
      (R := R) (S := S) (f := f) δ hδf a hfa n with ⟨b, hb⟩
  exact (mem_span_singleton_pow_iff_exists_mul (a := a) (f := f) n).2 ⟨b, hb⟩

/-- Helper for Lemma 10.140.6: in a Noetherian local `ℚ`-algebra, a derivation with `δ(f) = 1`
forces `f` to be regular. -/
private theorem isRegular_of_derivation_eq_one
    [Nontrivial S] [IsLocalRing S] [IsNoetherianRing S]
    (δ : Derivation R S S) (hδf : δ f = 1) :
    IsRegular f := by
  classical
  by_cases hunit : IsUnit f
  · -- A unit is automatically regular.
    exact hunit.isRegular
  · -- Otherwise the principal ideal `(f)` is proper, so Krull intersection kills every
    -- annihilator of `f`.
    rw [isRegular_iff_mem_nonZeroDivisors, mem_nonZeroDivisors_iff_left]
    intro a hfa
    let I : Ideal S := Ideal.span ({f} : Set S)
    have hmem : ∀ n : ℕ, a ∈ I ^ n := by
      intro n
      simpa [I] using
        mem_span_singleton_pow_of_mul_eq_zero_of_derivation_eq_one
          (R := R) (S := S) (f := f) δ hδf a hfa n
    have haInf : a ∈ ⨅ n : ℕ, I ^ n := by
      exact Ideal.mem_iInf.mpr hmem
    have hIneTop : I ≠ ⊤ := by
      intro hI
      apply hunit
      exact Ideal.span_singleton_eq_top.mp hI
    have hbot : a ∈ (⊥ : Ideal S) := by
      rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing I hIneTop]
      exact haInf
    simpa using hbot

-- Proof sketch: the hypothesis gives an `S`-linear functional `θ : Ω[S⁄R] →ₗ[S] S` with
-- `θ (df) = 1`. Via the owner equivalence `KaehlerDifferential.linearMapEquivDerivation`, this
-- yields an `R`-derivation `δ : S → S` with `δ f = 1`. If `f` were nilpotent, applying `δ` to a
-- minimal relation `f^n = 0` would give `n • f^(n - 1) = 0`; since `S` is a `ℚ`-algebra, `n` is
-- invertible, contradicting minimality.
/-- Lemma 10.140.6: if there exists an `S`-linear map `Ω[S⁄R] →ₗ[S] S` sending `df` to `1`
(equivalently, `df` generates a free rank-one direct summand of `Ω[S⁄R]`), then `f` is not
nilpotent. -/
theorem not_isNilpotent_of_kaehlerDifferential_directSummand
    [Nontrivial S]
    (hdf : ∃ θ : Ω[S⁄R] →ₗ[S] S, θ (D R S f) = 1) :
    ¬ IsNilpotent f := by
  rcases hdf with ⟨θ, hθ⟩
  -- Pass from the linear functional on `Ω[S⁄R]` to the corresponding derivation.
  let δ : Derivation R S S := (KaehlerDifferential.linearMapEquivDerivation R S) θ
  have hδf : δ f = 1 := by
    have hδ : δ f = θ (D R S f) := by
      simpa [δ] using linearMapEquivDerivation_apply_D (R := R) (S := S) θ f
    exact hδ.trans hθ
  -- The abstract nilpotence obstruction finishes the source proof route.
  exact not_isNilpotent_of_derivation_eq_one (R := R) (S := S) (f := f) δ hδf

-- Proof sketch: with the same derivation `δ` satisfying `δ f = 1`, any relation `f * a = 0`
-- yields `a = -f * δ a`, so `a ∈ (f)`. Iterating this argument shows `a ∈ (f^n)` for every `n`.
-- In a Noetherian local ring, Krull's intersection theorem gives `⋂ n, (f^n) = 0`, hence `a = 0`
-- and multiplication by `f` is injective.
/-- Under the same hypothesis that `df` admits an `S`-linear functional with value `1`, if `S` is
Noetherian local, then `f` is a nonzerodivisor. -/
theorem isRegular_of_kaehlerDifferential_directSummand
    [Nontrivial S] [IsLocalRing S] [IsNoetherianRing S]
    (hdf : ∃ θ : Ω[S⁄R] →ₗ[S] S, θ (D R S f) = 1) :
    IsRegular f := by
  rcases hdf with ⟨θ, hθ⟩
  -- Pass to the derivation appearing in the source proof.
  let δ : Derivation R S S := (KaehlerDifferential.linearMapEquivDerivation R S) θ
  have hδf : δ f = 1 := by
    have hδ : δ f = θ (D R S f) := by
      simpa [δ] using linearMapEquivDerivation_apply_D (R := R) (S := S) θ f
    exact hδ.trans hθ
  -- The Krull-intersection argument is packaged at the derivation level.
  exact isRegular_of_derivation_eq_one (R := R) (S := S) (f := f) δ hδf

end

/-! ### Lemma_10_140_7 (from Chap10) -/
open scoped TensorProduct

universe u v

namespace Algebra

section

variable {k : Type u} {S : Type v}
variable [Field k] [CharZero k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/-
Domain-style sampling for Lemma 10.140.7:
- primary domain: primewise smoothness criteria for finite type algebras over a characteristic-zero
  field, organized around the local owner `Localization.AtPrime q`;
- sampled owner declarations:
  `Algebra.IsSmoothAt`,
  `Algebra.FormallySmooth.projective_kaehlerDifferential`,
  `KaehlerDifferential.finite`,
  `isSmoothAt_iff_isRegularLocalRing_of_separable_residueField`;
- best owner abstraction: the canonical owner is the ideal-level smoothness predicate
  `IsSmoothAt k q` for a prime ideal `q : Ideal S`; the `PrimeSpectrum S` wrapper carried no extra
  mathematical data here, so the public theorem should live directly on `q`, with the localized
  Kähler module and the regular-local condition as derived views of the same owner local ring
  `Localization.AtPrime q`;
- primitive data: a prime ideal `q : Ideal S`;
- derived API: the finite/free condition on `Ω[Localization.AtPrime q⁄k]` and the regular-local
  condition on `Localization.AtPrime q`.

Source/core/bridge triage:
- `source-facing`: the three-way Stacks criterion relating smoothness, finite freeness of the local
  Kähler module, and regularity of the local ring;
- `core/canonical`: `IsSmoothAt k q`, equivalently `FormallySmooth k (Localization.AtPrime q)`,
  together with `IsRegularLocalRing (Localization.AtPrime q)`;
- `bridge/view`: the finite/free Kähler-differential clause, which is derived from the local smooth
  owner rather than a second owner abstraction.
-/

variable (q : Ideal S) [q.IsPrime]

local notation "S_q" => Localization.AtPrime q
local notation "Ω_q" => Ω[S_q⁄k]

-- Proof sketch: under characteristic `0`, the residue-field extension `q.ResidueField / k` is
-- separable by the chapter's perfect-field owner, so Lemma `10.140.5` identifies smoothness at
-- `q` with regularity of `S_q`. If `S_q` is smooth over `k`, then `S_q` is formally smooth and
-- essentially of finite type, so `Ω_q` is finite and projective; since `S_q` is local, this makes
-- `Ω_q` free. The converse from finite freeness of `Ω_q` to regularity is the genuinely new local
-- argument of the present lemma.
/-- Lemma 10.140.7: let `k` be a field of characteristic `0`, let `S` be a finite type
`k`-algebra, and let `q` be a prime ideal of `S`. The following are equivalent: `(1)` `S` is
smooth at `q` over `k`, i.e. `IsSmoothAt k q`; `(2)` the localized module of Kähler differentials
`Ω[Localization.AtPrime q⁄k]` is finite free over `Localization.AtPrime q`; and `(3)` the local
ring `Localization.AtPrime q` is regular. -/
theorem isSmoothAt_tfae_finite_free_kaehlerDifferential_isRegularLocalRing_of_charZero :
    List.TFAE
      [ IsSmoothAt k q
      , Module.Finite S_q Ω_q ∧ Module.Free S_q Ω_q
      , IsRegularLocalRing S_q
      ] := by
  tfae_have 1 ↔ 3 := by
    letI : PerfectField k := PerfectField.ofCharZero
    letI : IsSeparableOver k q.ResidueField := inferInstance
    simpa using
      (isSmoothAt_iff_isRegularLocalRing_of_separable_residueField q)
  tfae_have 1 → 2 := by
    intro hsmooth
    letI : FormallySmooth k S_q := hsmooth
    letI : Algebra.EssFiniteType S S_q := .of_isLocalization _ q.primeCompl
    letI : Algebra.EssFiniteType k S_q := .comp _ S _
    letI : Module.Flat S_q Ω_q := Module.Flat.of_projective
    exact ⟨inferInstance, Module.free_of_flat_of_isLocalRing⟩
  tfae_have 2 → 3 := by
    intro hOmega
    sorry
  tfae_finish

end

end Algebra

/-! ### Example_10_140_8 (from Chap10) -/
open MvPolynomial
open scoped RatFunc

noncomputable section

namespace Algebra

section

variable (p : ℕ) [Fact p.Prime]

/-
Domain-style sampling for Example 10.140.8:
- primary domain: positive-characteristic commutative-algebra counterexamples to smoothness,
  organized around quotient rings, prime-spectrum points, and the owner predicates
  `Smooth`/`IsSmoothAt`/`IsRegularLocalRing`;
- sampled owner declarations:
  `Ideal.Quotient.mk`,
  `Algebra.SmoothAtPrime`,
  `Algebra.smoothAtPrime_iff_isSmoothAt`,
  `IsRegularLocalRing`;
- best owner abstraction: the quotient map to a ring presented as a quotient should be the
  canonical owner `Ideal.Quotient.mk`, not a parallel local alias; the primewise smoothness
  failure is expressed on the canonical local owner `IsSmoothAt`, with the chapter's
  `SmoothAtPrime` available as the source-facing bridge when needed;
- primitive data: the quotient rings and the named prime ideal `q`;
- derived API: smoothness failure at `q` and regularity of the localization at `q`.

Source/core/bridge triage:
- `source-facing`: the concrete rings and the named prime `q = (y, x^p + t)` appearing in the
  example;
- `core/canonical`: `Ideal.Quotient.mk`, `IsSmoothAt`, and `IsRegularLocalRing`;
- `bridge/view`: `SmoothAtPrime` together with `smoothAtPrime_iff_isSmoothAt` for finitely
  presented algebras.
-/

/-- The quotient `F_p[x]/(x^p)` used for the first positive-characteristic counterexample. -/
abbrev charPNilpotentQuotient : Type :=
  Polynomial (ZMod p) ⧸ Ideal.span ({Polynomial.X ^ p} : Set (Polynomial (ZMod p)))

/-- The coefficient field `F_p(t)` used in the plane-curve counterexample. -/
abbrev charPRationalFunctionField : Type :=
  RatFunc (ZMod p)

/-- The bivariate polynomial ring over `F_p(t)` with coordinates `x` and `y`. -/
abbrev charPPlaneCurvePolynomialRing : Type :=
  MvPolynomial (Fin 2) (charPRationalFunctionField p)

/-- The defining equation `x^p + y^2 + t` of the plane-curve example over `F_p(t)`. -/
abbrev charPPlaneCurveEquation : charPPlaneCurvePolynomialRing p :=
  X (0 : Fin 2) ^ p + X (1 : Fin 2) ^ 2 + C (RatFunc.X : charPRationalFunctionField p)

/-- The quotient `F_p(t)[x, y]/(x^p + y^2 + t)` used for the second counterexample. -/
abbrev charPPlaneCurveQuotient : Type :=
  charPPlaneCurvePolynomialRing p ⧸
    Ideal.span ({charPPlaneCurveEquation p} : Set (charPPlaneCurvePolynomialRing p))

local notation "π" =>
  Ideal.Quotient.mk
    (Ideal.span ({charPPlaneCurveEquation p} : Set (charPPlaneCurvePolynomialRing p)))

/-- The ideal `(y, x^p + t)` in the plane-curve quotient ring. -/
def charPPlaneCurvePrimeIdeal : Ideal (charPPlaneCurveQuotient p) :=
  Ideal.span
    ({ π (X (1 : Fin 2)),
       π (X (0 : Fin 2) ^ p + C (RatFunc.X : charPRationalFunctionField p)) } :
      Set (charPPlaneCurveQuotient p))

-- Proof sketch: in the quotient by `x^p + y^2 + t`, modding out further by `(y, x^p + t)` gives a
-- field, so this ideal is maximal and hence prime.
/-- The ideal `(y, x^p + t)` is prime in the plane-curve quotient ring. -/
lemma charPPlaneCurvePrimeIdeal_isPrime : (charPPlaneCurvePrimeIdeal p).IsPrime := sorry

/-- The prime `q = (y, x^p + t)` in the plane-curve example. -/
def charPPlaneCurvePrime : PrimeSpectrum (charPPlaneCurveQuotient p) :=
  ⟨charPPlaneCurvePrimeIdeal p, charPPlaneCurvePrimeIdeal_isPrime p⟩

-- Proof sketch: compute `Ω` for `F_p[x]/(x^p)` from the quotient presentation. The relation has
-- derivative `p x^(p-1) dx = 0`, which vanishes in characteristic `p`, so the resulting module of
-- differentials remains free of rank `1`.
/-- Example 10.140.8 (1): the quotient `F_p[x]/(x^p)` has free module of Kähler differentials over
`F_p`. -/
theorem free_kaehlerDifferential_charPNilpotentQuotient :
    Module.Free (charPNilpotentQuotient p) Ω[charPNilpotentQuotient p⁄ZMod p] := sorry

-- Proof sketch: the ring `F_p[x]/(x^p)` has a nonzero nilpotent class, so it is not smooth over
-- `F_p`.
/-- Example 10.140.8 (2): the quotient `F_p[x]/(x^p)` is not smooth over `F_p`. -/
theorem charPNilpotentQuotient_not_smooth :
    ¬ Smooth (ZMod p) (charPNilpotentQuotient p) := sorry

-- Proof sketch: for `p > 2`, apply the Jacobian criterion at
-- `q = (y, x^p + t)`; the derivative in the `x`-direction vanishes in characteristic `p`, and the
-- resulting residue-field extension is purely inseparable, so smoothness fails at `q`.
/-- Example 10.140.8 (3): for `p > 2`, the quotient `F_p(t)[x, y]/(x^p + y^2 + t)` is not smooth
at the prime `q = (y, x^p + t)`. -/
theorem charPPlaneCurvePrime_not_isSmoothAt_of_two_lt (hp : 2 < p) :
    ¬ IsSmoothAt (charPRationalFunctionField p) (charPPlaneCurvePrime p).asIdeal := sorry

-- Proof sketch: for `p > 2`, the localization at `q = (y, x^p + t)` is a one-dimensional regular
-- local ring.
/-- Example 10.140.8 (4): for `p > 2`, the local ring of
`F_p(t)[x, y]/(x^p + y^2 + t)` at `q = (y, x^p + t)` is regular. -/
theorem charPPlaneCurvePrime_isRegularLocalRing_of_two_lt (hp : 2 < p) :
    IsRegularLocalRing (Localization.AtPrime (charPPlaneCurvePrime p).asIdeal) := sorry

end

end Algebra

/-! ### Lemma_10_140_9 (from Chap10) -/
noncomputable section

universe u v

namespace Algebra

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [Algebra R S]
variable [Algebra.FiniteType R S]

/-- Bridge/view: the Stacks-project separability predicate on the induced fraction-field extension
attached to an injective finite-type map of domains. The only non-source-facing data are the
derived faithful action of `R` on `S` and the canonical induced algebra `FractionRing R →
FractionRing S`, both kept internal to this bridge. -/
noncomputable abbrev fractionRingIsSeparableOver
    (hinj : Function.Injective (algebraMap R S)) : Prop :=
  let _ : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  let _ : Algebra (FractionRing R) (FractionRing S) :=
    FractionRing.liftAlgebra R (FractionRing S)
  IsSeparableOver (FractionRing R) (FractionRing S)

-- Proof sketch: for the forward implication, replace the smooth-at-`(0)` hypothesis by a smooth
-- localization `S_g`, base change along `R → FractionRing R`, and use the field case together with
-- geometric reducedness to deduce that `FractionRing S / FractionRing R` is separable in the
-- Stacks Project sense. For the reverse implication, first localize so the map is of finite
-- presentation, apply smooth-locus base change to the generic fiber over `FractionRing R`, and
-- then use the field criterion from Lemma `10.140.5` at the generic point.
/-- Lemma 10.140.9: let `R → S` be an injective finite type ring map of domains. Then `R → S` is
smooth at the generic point `q = (0)` if and only if the induced extension of fraction fields
`FractionRing S / FractionRing R` is separable in the Stacks Project sense. -/
theorem isSmoothAt_zero_iff_isSeparableOver_fractionRing
    (hinj : Function.Injective (algebraMap R S)) :
    IsSmoothAt R (⊥ : Ideal S) ↔ fractionRingIsSeparableOver hinj := sorry

end

end Algebra
