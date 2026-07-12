import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap10.Definition_10_110_7
import StacksProject_2024.Chap10.Definition_10_42_1
import StacksProject_2024.Chap10.Lemma_10_131_9
import StacksProject_2024.Chap10.Lemma_10_44_2
import StacksProject_2024.Chap10.Lemma_10_158_6
import StacksProject_2024.Chap10.Lemma_10_158_7
import StacksProject_2024.Chap10.Lemma_10_164_4
import StacksProject_2024.Chap10.Lemma_10_166_5

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open scoped TensorProduct
open TensorProduct.AlgebraTensorModule

noncomputable section

universe u v w

/- Domain triage:
* primary domain: geometric regularity of local `k`-algebras in characteristic `p`, together with
  the cotangent-theoretic criteria for the local map `k → A`;
* sampled owner declarations:
  - `Algebra.IsGeometricallyRegular`,
  - `onePthRootExtension`,
  - `Algebra.H1Cotangent.map`,
  - `_root_.KaehlerDifferential.mapBaseChange`,
  - `_root_.LinearMap.liftBaseChange`;
* best owner abstraction: the proposition should keep the source-facing finite test
  `k ⊂ k' ⊂ k^{1/p}` through the chapter-local owner `onePthRootExtension`, and use
  `IsGeometricallyRegular`, `H1Cotangent.map`, and `KaehlerDifferential.mapBaseChange` only as the
  canonical bridge/core layer;
* layer triage:
  - `source-facing`: Proposition `15.35.1`, the four-way equivalence;
  - `core/canonical`: `IsGeometricallyRegular`, `onePthRootExtension`,
    `H1Cotangent.map`, and `KaehlerDifferential.mapBaseChange`;
  - `bridge/view`: the named residue-field comparison
    `KaehlerDifferential.residueFieldComparison`, obtained from
    `KaehlerDifferential.mapBaseChange` by tensoring to `κ(A)`.

Primitive data are the canonical owner maps themselves. The conjunction clauses in the `TFAE`
statement are derived API, so the only extracted bridge is the reusable residue-field comparison
map needed by both this proposition and Theorem `15.40.1`.
-/

namespace KaehlerDifferential

section

variable (R : Type u) [CommRing R]
variable (S : Type v) [CommRing S]
variable (A : Type w) [CommRing A] [Algebra R S] [Algebra S A] [Algebra R A]
variable [IsScalarTower R S A] [IsLocalRing A]

/-- The canonical comparison map
`κ(A) ⊗[S] Ω[S⁄R] → κ(A) ⊗[A] Ω[A⁄R]` induced by
`KaehlerDifferential.mapBaseChange R S A` and residue-field base change. -/
noncomputable abbrev residueFieldComparison :
    ResidueField A ⊗[S] Ω[S⁄R] →ₗ[ResidueField A] ResidueField A ⊗[A] Ω[A⁄R] :=
  lTensor (ResidueField A) (ResidueField A) (KaehlerDifferential.mapBaseChange R S A) ∘ₗ
    (cancelBaseChange S A (ResidueField A) (ResidueField A) Ω[S⁄R]).symm.toLinearMap

end

end KaehlerDifferential

namespace Algebra

section

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [IsLocalRing A] [Algebra k A]
variable {p : ℕ} [Fact p.Prime]
variable [CharP k p] [IsNoetherianRing A]

/-- Helper for Proposition 15.35.1: a finite intermediate field inside the chosen model
`onePthRootExtension k p` of `k^{1/p}` is purely inseparable over `k`. -/
private theorem onePthRootIntermediate_isPurelyInseparable
    (K : IntermediateField k (AlgebraicClosure k)) [FiniteDimensional k K]
    (hK : K ≤ onePthRootExtension k p) :
    IsPurelyInseparable k K := by
  -- Proof comment: every element of `K` already lies in `k^{1/p}`, so its `p`th power comes from
  -- `k`; this is exactly the pointwise criterion for pure inseparability.
  rw [isPurelyInseparable_iff_pow_mem k p]
  intro x
  have hx_mem : ((x : K) : AlgebraicClosure k) ∈ onePthRootExtension k p := hK x.2
  rw [mem_onePthRootExtension_iff] at hx_mem
  rcases hx_mem with ⟨a, ha⟩
  refine ⟨1, ?_⟩
  refine ⟨a, ?_⟩
  apply Subtype.ext
  simpa using ha

/-- Helper for Proposition 15.35.1: regularity transports across a ring equivalence. -/
private theorem isRegularRing_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) [IsRegularRing S] :
    IsRegularRing R := by
  -- Proof comment: a ring equivalence is faithfully flat, so regularity descends along it.
  exact
    isRegularRing_of_faithfullyFlat e.toRingHom
      (RingHom.FaithfullyFlat.of_bijective e.bijective)

/-- Helper for Proposition 15.35.1: geometric regularity over `k` makes every finite
purely inseparable intermediate tensor base change inside `k^{1/p}` regular, after a universe
lift on the field factor. -/
private theorem isRegularRing_tensorBaseChange_of_isGeometricallyRegular_intermediateField
    (hgeom : IsGeometricallyRegular k A)
    (K : IntermediateField k (AlgebraicClosure k)) [FiniteDimensional k K]
    (hK : K ≤ onePthRootExtension k p) :
    IsRegularRing (K ⊗[k] A) := by
  let K' := ULift.{v} K
  let _ : Field K' := inferInstance
  let _ : Algebra k K' := ULift.algebra
  let _ : FiniteDimensional k K' := by
    -- Proof comment: move finite dimensionality to the lifted carrier via the canonical
    -- `k`-algebra equivalence `ULift K ≃ₐ[k] K`.
    exact (ULift.algEquiv : K' ≃ₐ[k] K).symm.toLinearEquiv.finiteDimensional
  have hpure : IsPurelyInseparable k K :=
    onePthRootIntermediate_isPurelyInseparable (k := k) (p := p) K hK
  let _ : IsPurelyInseparable k K := hpure
  let _ : IsPurelyInseparable k K' := by
    -- Proof comment: pure inseparability is invariant under the lift equivalence.
    exact (ULift.algEquiv : K' ≃ₐ[k] K).symm.isPurelyInseparable
  letI : IsGeometricallyRegular k A := hgeom
  have hLift : IsRegularRing (K' ⊗[k] A) := inferInstance
  let eTensor : K' ⊗[k] A ≃ₐ[k] K ⊗[k] A :=
    Algebra.TensorProduct.congr (ULift.algEquiv : K' ≃ₐ[k] K) (AlgEquiv.refl : A ≃ₐ[k] A)
  -- Proof comment: transport regularity back from the universe-adjusted tensor product.
  exact isRegularRing_of_ringEquiv eTensor.symm.toRingEquiv

/-- Helper for Proposition 15.35.1: a local ring is already the localization at the complement of
its maximal ideal. -/
private theorem self_isLocalization_primeCompl_maximalIdeal :
    IsLocalization (maximalIdeal A).primeCompl A := by
  -- Proof comment: in a local ring every element outside the maximal ideal is a unit, so the
  -- localization at the prime complement is identified with the ring itself.
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    exact IsLocalRing.notMem_maximalIdeal.mp y.2
  · intro z
    exact ⟨⟨z, 1⟩, by simp⟩
  · intro x y hxy
    exact ⟨1, by simpa using hxy⟩

/-- Helper for Proposition 15.35.1: clause `(2)` already forces the base local ring `A` itself to
be regular local by specializing the finite test field to `k = ⊥ ⊂ k^{1/p}` and collapsing the
trivial tensor factor. -/
private theorem regularLocal_of_onePthRoot_test
    (htest :
      ∀ (K : IntermediateField k (AlgebraicClosure k)) [FiniteDimensional k K],
        K ≤ onePthRootExtension k p → IsRegularRing (K ⊗[k] A)) :
    IsRegularLocalRing A := by
  let eBot :
      (⊥ : IntermediateField k (AlgebraicClosure k)) ≃ₐ[k] k :=
    IntermediateField.botEquiv k (AlgebraicClosure k)
  let eTensor :
      ((⊥ : IntermediateField k (AlgebraicClosure k)) ⊗[k] A) ≃ₐ[k] A :=
    (Algebra.TensorProduct.congr eBot (AlgEquiv.refl : A ≃ₐ[k] A)).trans
      (Algebra.TensorProduct.lid k A)
  have hregularTensor :
      IsRegularRing ((⊥ : IntermediateField k (AlgebraicClosure k)) ⊗[k] A) :=
    htest ⊥ bot_le
  have hregularA : IsRegularRing A :=
    isRegularRing_of_ringEquiv eTensor.symm.toRingEquiv
  letI : IsRegularRing A := hregularA
  let pA : PrimeSpectrum A := ⟨maximalIdeal A, inferInstance⟩
  have hloc :
      IsRegularLocalRing (Localization.AtPrime pA.asIdeal) :=
    IsRegularRing.isRegularLocalRing_atPrime pA
  let _ : IsLocalization (maximalIdeal A).primeCompl A :=
    self_isLocalization_primeCompl_maximalIdeal (A := A)
  let eLoc : Localization.AtPrime pA.asIdeal ≃ₐ[A] A :=
    Localization.algEquiv (maximalIdeal A).primeCompl A
  -- Proof comment: the closed-point localization of a local ring is the ring itself.
  exact IsRegularLocalRing.of_ringEquiv eLoc.toRingEquiv

section ResidueFieldSourceMaps

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- Helper for Proposition 15.35.1: the residue-field quotient has kernel equal to the maximal
ideal. This is the source-facing ideal identification used in both Jacobi-Zariski rows. -/
private theorem ker_algebraMap_residueField_eq_maximalIdeal :
    RingHom.ker (algebraMap R (ResidueField R)) = maximalIdeal R := by
  -- Proof comment: the canonical map `R → κ(R)` is the residue map, whose kernel is `𝔪_R`.
  simpa [ResidueField.algebraMap_eq] using
    (ker_residue : RingHom.ker (IsLocalRing.residue R) = maximalIdeal R)

/-- Helper for Proposition 15.35.1: transport the kernel-form conormal module of
`R → κ(R)` to the source-facing cotangent space `𝔪_R / 𝔪_R²`. -/
private noncomputable def residueFieldKerCotangentEquiv :
    (maximalIdeal R).Cotangent ≃ₗ[R]
      (RingHom.ker (algebraMap R (ResidueField R))).Cotangent :=
  Ideal.Cotangent.equivOfEq
    (maximalIdeal R)
    (RingHom.ker (algebraMap R (ResidueField R)))
    (ker_algebraMap_residueField_eq_maximalIdeal (R := R)).symm

variable {k : Type*} [CommRing k] [Algebra k R]

/-- Helper for Proposition 15.35.1: this is the source top-row conormal map
`𝔪_R / 𝔪_R² → κ(R) ⊗[R] Ω[R⁄k]`, written in owner form by transporting
`KaehlerDifferential.kerCotangentToTensor`. -/
private noncomputable def residueFieldCotangentToTensorOverBase :
    (maximalIdeal R).Cotangent →ₗ[R] ResidueField R ⊗[R] Ω[R⁄k] :=
  (KaehlerDifferential.kerCotangentToTensor k R (ResidueField R)).comp
    (residueFieldKerCotangentEquiv (R := R)).toLinearMap

/-- Helper for Proposition 15.35.1: the source top Jacobi-Zariski row for `k → R → κ(R)` is
exact at the middle term after identifying the conormal module with `𝔪_R / 𝔪_R²`. -/
private theorem residueFieldCotangentToTensorOverBase_exact :
    Function.Exact
      (residueFieldCotangentToTensorOverBase (k := k) (R := R))
      (KaehlerDifferential.mapBaseChange k R (ResidueField R)) := by
  have hsurj : Function.Surjective (algebraMap R (ResidueField R)) := by
    -- Proof comment: `algebraMap R κ(R)` is the residue quotient, hence surjective.
    simpa [ResidueField.algebraMap_eq] using
      (residue_surjective : Function.Surjective (IsLocalRing.residue R))
  -- Proof comment: this is exactly the conormal exact sequence for the surjection `R → κ(R)`,
  -- rewritten through the ideal equality `ker(R → κ(R)) = maximalIdeal R`.
  exact
    (kaehlerDifferential_exact_cotangent_tensor_of_surjective
      (R := k)
      (S := R)
      (S' := ResidueField R)
      (maximalIdeal R)
      (ker_algebraMap_residueField_eq_maximalIdeal (R := R))
      hsurj).1

variable {pR : ℕ} [Fact pR.Prime] [CharP R pR] [Algebra (ZMod pR) R]
variable [IsScalarTower (ZMod pR) R (ResidueField R)]

/-- Helper for Proposition 15.35.1: over the perfect prime field `ZMod p`, the residue-field
conormal map `𝔪_R / 𝔪_R² → κ(R) ⊗[R] Ω[R⁄ZMod p]` is injective. -/
private theorem residueFieldCotangentToTensorOverBase_injective_of_charP :
    Function.Injective
      (residueFieldCotangentToTensorOverBase (k := ZMod pR) (R := R)) := by
  letI : PerfectField (ZMod pR) := inferInstance
  letI : Algebra.IsSeparableOver (ZMod pR) (ResidueField R) :=
    Algebra.IsSeparableOver.of_perfectField
  letI : Algebra.FormallySmooth (ZMod pR) (ResidueField R) :=
    Algebra.formallySmooth_of_isSeparableOver
  have hresidueSurj : Function.Surjective (IsLocalRing.residue R) := residue_surjective
  have hsurj : Function.Surjective (algebraMap R (ResidueField R)) := by
    -- Proof comment: the source surjection is the residue map written as an algebra map.
    simpa [ResidueField.algebraMap_eq] using hresidueSurj
  have hsurjLift :
      Function.Surjective (IsScalarTower.toAlgHom (ZMod pR) R (ResidueField R)).kerSquareLift := by
    -- Proof comment: the square-zero quotient `R / ker(algebraMap)^2` still maps onto `κ(R)`.
    exact Ideal.Quotient.lift_surjective_of_surjective _ _ hsurj
  have hsqz :
      RingHom.ker (IsScalarTower.toAlgHom (ZMod pR) R (ResidueField R)).kerSquareLift.toRingHom ^ 2 =
        ⊥ := by
    -- Proof comment: the kernel of the lifted quotient map is the square of the cotangent ideal.
    rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]
  let σ : ResidueField R →ₐ[ZMod pR] R ⧸ RingHom.ker (algebraMap R (ResidueField R)) ^ 2 :=
    Algebra.FormallySmooth.liftOfSurjective
      (AlgHom.id (ZMod pR) (ResidueField R))
      (IsScalarTower.toAlgHom (ZMod pR) R (ResidueField R)).kerSquareLift
      hsurjLift
      ⟨2, hsqz⟩
  have hσ :
      (IsScalarTower.toAlgHom (ZMod pR) R (ResidueField R)).kerSquareLift.comp σ =
        AlgHom.id (ZMod pR) (ResidueField R) := by
    -- Proof comment: the formal-smooth lift is a genuine section of the square-zero quotient map.
    simpa [σ] using
      (Algebra.FormallySmooth.comp_liftOfSurjective
        (AlgHom.id (ZMod pR) (ResidueField R))
        (IsScalarTower.toAlgHom (ZMod pR) R (ResidueField R)).kerSquareLift
        hsurjLift
        ⟨2, hsqz⟩ : _)
  obtain ⟨l, hl⟩ := ((retractionKerCotangentToTensorEquivSection hsurj).symm ⟨σ, hσ⟩)
  have hker_inj :
      Function.Injective (KaehlerDifferential.kerCotangentToTensor (ZMod pR) R (ResidueField R)) :=
    LinearMap.injective_of_comp_eq_id _ _ hl
  -- Proof comment: transport injectivity across the kernel-identification equivalence
  -- `ker(algebraMap R κ(R)) = maximalIdeal R`.
  intro x y hxy
  apply (residueFieldKerCotangentEquiv (R := R)).injective
  exact hker_inj <| by
    simpa [residueFieldCotangentToTensorOverBase, LinearMap.comp_apply] using hxy

end ResidueFieldSourceMaps

/-- Helper for Proposition 15.35.1: over the prime field `ZMod p`, the connecting map
`H₁(L_{κ(A)/k}) → κ(A) ⊗[k] Ω[k⁄ZMod p]` is injective because `κ(A) / ZMod p` is separable and
thus has vanishing first cotangent homology. -/
private theorem h1Cotangent_delta_injective_of_charP
    (k : Type u) [Field k]
    (A : Type v) [CommRing A] [IsLocalRing A] [Algebra k A]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    [Algebra (ZMod p) k] [Algebra (ZMod p) A] [IsScalarTower (ZMod p) k A] :
    Function.Injective (H1Cotangent.δ (ZMod p) k (ResidueField A)) := by
  letI : PerfectField (ZMod p) := inferInstance
  letI : Algebra.IsSeparableOver (ZMod p) (ResidueField A) :=
    Algebra.IsSeparableOver.of_perfectField
  letI : Algebra.FormallySmooth (ZMod p) (ResidueField A) :=
    Algebra.formallySmooth_of_isSeparableOver
  have hsub :
      Subsingleton (H1Cotangent (ZMod p) (ResidueField A)) :=
    (Algebra.formallySmooth_iff_subsingleton_h1Cotangent_of_field
      (ZMod p) (ResidueField A)).1 Algebra.formallySmooth_of_isSeparableOver
  intro x y hxy
  have hxy0 : H1Cotangent.δ (ZMod p) k (ResidueField A) (x - y) = 0 := by
    -- Proof comment: injectivity reduces to showing the difference lies in the zero fiber.
    rw [LinearMap.map_sub, hxy, sub_self]
  obtain ⟨z, hz⟩ :=
    (H1Cotangent.exact_map_δ (ZMod p) k (ResidueField A) (x - y)).1 hxy0
  have hz0 : z = 0 := Subsingleton.elim _ _
  have hsub_eq : x - y = 0 := by
    -- Proof comment: the exactness witness comes from the subsingleton left term, so it vanishes.
    simpa [hz0] using hz.symm
  exact sub_eq_zero.mp hsub_eq

/-- Helper for Proposition 15.35.1: injectivity of the residue-field differential comparison over
`ZMod p` implies injectivity of the owner map
`H1Cotangent.map k A (ResidueField A) (ResidueField A)`. -/
private theorem h1Cotangent_map_residueFieldComparison_square
    {k : Type u} [Field k]
    {A : Type v} [CommRing A] [IsLocalRing A] [Algebra k A]
    {p : ℕ} [Fact p.Prime] [CharP k p] [CharP A p]
    [Algebra (ZMod p) k] [Algebra (ZMod p) A] [IsScalarTower (ZMod p) k A] :
    (H1Cotangent.δ (ZMod p) A (ResidueField A)).comp
        (H1Cotangent.map k A (ResidueField A) (ResidueField A)) =
      (KaehlerDifferential.residueFieldComparison (ZMod p) k A).comp
        (H1Cotangent.δ (ZMod p) k (ResidueField A)) := by
  -- Proof comment: after unfolding `H1Cotangent.map`, `H1Cotangent.δ`, and
  -- `KaehlerDifferential.residueFieldComparison`, the remaining goal is the presentation-level
  -- naturality of `Generators.H1Cotangent.δ` for the self-presentation morphism
  -- `self k κ(A) ⟶ self A κ(A)`. This is the exact owner-form square needed by the source proof.
  -- TODO: prove this by an explicit presentation-level naturality lemma for
  -- `Generators.H1Cotangent.δ`, using the self-presentation morphism
  -- `((Generators.self k (ResidueField A)).defaultHom (Generators.self A (ResidueField A)))`
  -- and the corresponding `Extension.CotangentSpace.map_comp_apply` compatibility on the right.
  sorry

/-- Helper for Proposition 15.35.1: injectivity of the residue-field differential comparison over
`ZMod p` implies injectivity of the owner map
`H1Cotangent.map k A (ResidueField A) (ResidueField A)`. -/
private theorem h1Cotangent_map_injective_of_residueFieldComparison_injective
    {k : Type u} [Field k]
    {A : Type v} [CommRing A] [IsLocalRing A] [Algebra k A]
    {p : ℕ} [Fact p.Prime] [CharP k p] [CharP A p] [IsNoetherianRing A]
    [Algebra (ZMod p) k] [Algebra (ZMod p) A] [IsScalarTower (ZMod p) k A]
    (hdiff : Function.Injective (KaehlerDifferential.residueFieldComparison (ZMod p) k A)) :
    Function.Injective (H1Cotangent.map k A (ResidueField A) (ResidueField A)) := by
  have hδ_inj :
      Function.Injective (H1Cotangent.δ (ZMod p) k (ResidueField A)) :=
    h1Cotangent_delta_injective_of_charP k A p
  have hsquare :
      (H1Cotangent.δ (ZMod p) A (ResidueField A)).comp
          (H1Cotangent.map k A (ResidueField A) (ResidueField A)) =
        (KaehlerDifferential.residueFieldComparison (ZMod p) k A).comp
          (H1Cotangent.δ (ZMod p) k (ResidueField A)) :=
    h1Cotangent_map_residueFieldComparison_square (k := k) (A := A) (p := p)
  intro x y hxy
  have hmap0 : H1Cotangent.map k A (ResidueField A) (ResidueField A) (x - y) = 0 := by
    -- Proof comment: injectivity reduces to the vanishing of the source difference.
    rw [LinearMap.map_sub, hxy, sub_self]
  have hres0 :
      KaehlerDifferential.residueFieldComparison (ZMod p) k A
          (H1Cotangent.δ (ZMod p) k (ResidueField A) (x - y)) = 0 := by
    -- Proof comment: rewrite the vanishing of `H1Cotangent.map (x - y)` across the owner square.
    have hcomp0 :
        ((H1Cotangent.δ (ZMod p) A (ResidueField A)).comp
            (H1Cotangent.map k A (ResidueField A) (ResidueField A))) (x - y) = 0 := by
      simp [LinearMap.comp_apply, hmap0]
    rw [hsquare] at hcomp0
    simpa [LinearMap.comp_apply] using hcomp0
  have hδ0 : H1Cotangent.δ (ZMod p) k (ResidueField A) (x - y) = 0 := by
    -- Proof comment: the differential comparison is injective by assumption.
    apply hdiff
    simpa using hres0
  have hsub : x - y = 0 := by
    -- Proof comment: the source connecting map over `ZMod p` is already injective.
    apply hδ_inj
    simpa using hδ0
  exact sub_eq_zero.mp hsub

-- Proof sketch: use the source-facing finite `k ⊂ k' ⊂ k^{1/p}` test as a bridge to geometric
-- regularity, then combine the cotangent-homology and differential criteria for the residue
-- field. The third
-- clause uses the canonical Jacobi-Zariski map
-- `H1Cotangent.map k A κ(A) κ(A)`, which corresponds to `H_1(L_{κ(A)/k}) → 𝔪/𝔪²`.
/-- Proposition 15.35.1: for a Noetherian local `k`-algebra `A` in characteristic `p > 0`, the
following are equivalent: `A` is geometrically regular over `k`; for every finite intermediate
field `k ⊂ k' ⊂ k^{1/p}`, realized through the chosen chapter-local model
`onePthRootExtension k p`, the tensor base change `k' ⊗[k] A` is regular; `A` is regular local and
the canonical map `H_1(L_{κ(A)/k}) → 𝔪_A / 𝔪_A^2` is injective, expressed in the library-facing
form `Function.Injective (H1Cotangent.map k A κ(A) κ(A))`; and `A` is regular local and
`KaehlerDifferential.residueFieldComparison (ZMod p) k A` is injective. -/
@[stacks 07E5]
theorem geometricallyRegularLocalRing_tfae_of_charP :
    by
      letI : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
      letI : Algebra (ZMod p) k := ZMod.algebra k p
      letI : Algebra (ZMod p) A := ZMod.algebra A p
      letI : IsScalarTower (ZMod p) k A := by infer_instance
      exact
        List.TFAE [
          IsGeometricallyRegular k A,
          ∀ (K : IntermediateField k (AlgebraicClosure k)) [FiniteDimensional k K],
            K ≤ onePthRootExtension k p →
              IsRegularRing (K ⊗[k] A),
          IsRegularLocalRing A ∧
            Function.Injective (H1Cotangent.map k A (ResidueField A) (ResidueField A)),
          IsRegularLocalRing A ∧
            Function.Injective (KaehlerDifferential.residueFieldComparison (ZMod p) k A)
        ] := by
  letI : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  letI : Algebra (ZMod p) A := ZMod.algebra A p
  letI : IsScalarTower (ZMod p) k A := by infer_instance
  -- Proof comment: keep the source-proof organization as a TFAE cycle
  -- `(1) → (2) → (4) → (3) → (1)`.
  tfae_have 1 → 2 := by
    intro hgeom K _ hK
    -- Proof comment: clause `(2)` is the geometric-regularity base-change test, with a `ULift`
    -- inserted only to match the universe level expected by the owner theorem.
    exact
      isRegularRing_tensorBaseChange_of_isGeometricallyRegular_intermediateField
        (k := k) (A := A) (p := p) hgeom K hK
  tfae_have 2 → 4 := by
    intro htest
    have hregA : IsRegularLocalRing A :=
      regularLocal_of_onePthRoot_test (k := k) (A := A) (p := p) htest
    refine ⟨hregA, ?_⟩
    -- TODO: follow the source-proof Faltings argument through finite `k ⊂ k' ⊂ k^{1/p}`,
    -- now keeping the already extracted regular-local input `hregA` fixed while the remaining
    -- work proves injectivity of `KaehlerDifferential.residueFieldComparison (ZMod p) k A`.
    sorry
  tfae_have 4 → 3 := by
    intro hdiff
    refine ⟨hdiff.1, ?_⟩
    -- Route correction: package the `δ`-injective chase behind the single missing owner square,
    -- so the theorem body only uses the named local injectivity bridge.
    exact
      h1Cotangent_map_injective_of_residueFieldComparison_injective
        (k := k) (A := A) (p := p) hdiff.2
  tfae_have 3 → 1 := by
    intro hh1
    -- TODO: follow the source proof for arbitrary finite purely inseparable `k'/k`, compare
    -- the Jacobi-Zariski rows for `k → A → κ(A)` and `k' → k' ⊗[k] A → κ(k' ⊗[k] A)`, use
    -- the Euler-characteristic identity from Lemma `15.34.3`, and conclude regularity of the
    -- base change from the cotangent-space inequality.
    sorry
  tfae_finish

end

end Algebra
