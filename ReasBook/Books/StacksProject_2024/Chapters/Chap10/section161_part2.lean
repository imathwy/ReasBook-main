import Mathlib
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_161_7 (from Chap10) -/
universe u v

/-
Domain triage: this file is in the commutative algebra of `N-1`/`N-2` descent along
module-finite extensions of domains.

Owner abstractions sampled for this item:
- `IsN1Ring`, the source-facing `N-1` owner from `Definition_10_161_1`;
- `IsN2Ring`, the source-facing `N-2` owner from `Definition_10_161_1`;
- `IsN1Ring.integralClosure_finite`, the derived finite-normalization field of the `N-1` owner;
- `IsN2Ring.integralClosure_finite`, the derived finite-normalization-in-finite-extensions field
  of the `N-2` owner.

This file is `source-facing`: the textbook item states descent of the `N-1` and `N-2` properties
themselves along a finite extension `R ⊂ S`. The primitive data are the rings and the finite
extension `R → S`; the finiteness statements for integral closures are derived API coming from the
owner classes and should remain internal to the eventual proofs rather than becoming new public
wrapper declarations here.
-/

section

variable {R : Type u} {S : Type v} [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S]

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

omit [IsDomain R] [IsNoetherianRing R] [IsDomain S] [Module.Finite R S] in
/-- Helper for Lemma 10.161.7: an element integral over `R` remains integral over `S` after
mapping into a larger ambient field over `S`. -/
lemma map_integralClosure_to_larger_base_mem
    {L : Type*} {M : Type*} [Field L] [Field M] [Algebra R L] [Algebra S M] [Algebra R M]
    [IsScalarTower R S M] (f : L →ₐ[R] M) (x : integralClosure R L) :
    f x ∈ integralClosure S M := by
  -- The source element is integral over `R`, so its image is integral over `R` and hence over `S`.
  change IsIntegral S (f x)
  exact (IsIntegral.map f x.2).tower_top

omit [IsDomain R] [IsNoetherianRing R] [IsDomain S] [Module.Finite R S] in
/-- Helper for Lemma 10.161.7: an `R`-algebra map into an `S`-algebra field restricts to a map
from the integral closure over `R` to the integral closure over `S`. -/
noncomputable def map_integralClosure_to_larger_base
    {L : Type*} {M : Type*} [Field L] [Field M] [Algebra R L] [Algebra S M] [Algebra R M]
    [IsScalarTower R S M] (f : L →ₐ[R] M) :
    integralClosure R L →ₐ[R] (integralClosure S M).restrictScalars R :=
  (f.restrictDomain (integralClosure R L)).codRestrict ((integralClosure S M).restrictScalars R)
    (map_integralClosure_to_larger_base_mem (R := R) (S := S) f)

omit [IsDomain R] [IsNoetherianRing R] [IsDomain S] [Module.Finite R S] in
/-- Helper for Lemma 10.161.7: the restricted map on integral closures is injective whenever the
ambient field map is injective. -/
lemma map_integralClosure_to_larger_base_injective
    {L : Type*} {M : Type*} [Field L] [Field M] [Algebra R L] [Algebra S M] [Algebra R M]
    [IsScalarTower R S M] (f : L →ₐ[R] M) (hf : Function.Injective f) :
    Function.Injective (map_integralClosure_to_larger_base (R := R) (S := S) f) := by
  intro x y hxy
  apply Subtype.ext
  exact hf (congrArg (fun z : integralClosure S M ↦ (z : M)) hxy)

-- Proof sketch: let `R'` be the integral closure of `R` in `FractionRing R`. The fraction field of
-- `S` is a finite extension of `FractionRing R`, so `R'` maps into the integral closure of `S` in
-- `FractionRing S`. Since `S` is finite over `R` and `R` is Noetherian, the finiteness of that
-- larger integral closure over `S` descends to finiteness of `R'` over `R`.
/-- Lemma 10.161.7 (1): if `R` is a Noetherian domain, `R ⊂ S` is a finite extension of domains,
and `S` is `N-1`, then `R` is `N-1`. -/
theorem isN1Ring_of_finite_extension
    (hRS : Function.Injective (algebraMap R S)) [IsN1Ring S] :
    IsN1Ring R := by
  letI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hRS
  letI : FaithfulSMul R (FractionRing S) := inferInstance
  letI : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R (FractionRing S)
  letI : IsScalarTower R (FractionRing R) (FractionRing S) :=
    FractionRing.isScalarTower_liftAlgebra R (FractionRing S)
  let f : FractionRing R →ₐ[R] FractionRing S :=
    IsScalarTower.toAlgHom R (FractionRing R) (FractionRing S)
  let g :
      integralClosure R (FractionRing R) →ₐ[R]
        (integralClosure S (FractionRing S)).restrictScalars R :=
    map_integralClosure_to_larger_base (R := R) (S := S) f
  have hfin : Module.Finite R (integralClosure S (FractionRing S)) := by
    -- The normalization of `S` is finite over `S`, hence finite over `R`.
    exact Module.Finite.trans S (integralClosure S (FractionRing S))
  letI : Module.Finite R ((integralClosure S (FractionRing S)).restrictScalars R) := by
    simpa using hfin
  refine IsN1Ring.mk ?_
  -- Descend finiteness along the injective map into the finite `R`-module on the `S`-side.
  exact Module.Finite.of_injective g.toLinearMap
    (map_integralClosure_to_larger_base_injective (R := R) (S := S) f
      f.injective)

/-- Helper for Lemma 10.161.7: the image of a basis vector remains integral after mapping into an
algebraic closure over the larger fraction field. -/
lemma basis_image_isIntegral_over_fractionRingS
    {L : Type*} {Ω : Type*} {ι : Type*}
    [Field L] [Field Ω] [Algebra (FractionRing R) (FractionRing S)]
    [Algebra (FractionRing R) L] [Algebra (FractionRing S) Ω]
    [Algebra (FractionRing R) Ω] [IsScalarTower (FractionRing R) (FractionRing S) Ω]
    [FiniteDimensional (FractionRing R) L]
    (b : Module.Basis ι (FractionRing R) L) (iota : L →ₐ[FractionRing R] Ω) (j : ι) :
    IsIntegral (FractionRing S) (iota (b j)) := by
  -- Each basis vector is algebraic over `FractionRing R`, hence integral there.
  have h_integral_R : IsIntegral (FractionRing R) (b j) := by
    exact (Algebra.IsAlgebraic.isAlgebraic (b j)).isIntegral
  -- Mapping preserves integrality, and the integral relation ascends along the scalar tower.
  exact (h_integral_R.map iota).tower_top

/-- Helper for Lemma 10.161.7: adjoining the images of a finite basis over `FractionRing S`
produces a finite-dimensional intermediate field. -/
lemma finite_common_overfield_of_basis
    {L : Type*} {Ω : Type*} {ι : Type*}
    [Field L] [Field Ω] [Fintype ι]
    [Algebra (FractionRing R) (FractionRing S)]
    [Algebra (FractionRing R) L] [Algebra (FractionRing S) Ω]
    [Algebra (FractionRing R) Ω] [IsScalarTower (FractionRing R) (FractionRing S) Ω]
    [FiniteDimensional (FractionRing R) L]
    (b : Module.Basis ι (FractionRing R) L) (iota : L →ₐ[FractionRing R] Ω) :
    FiniteDimensional (FractionRing S)
      (IntermediateField.adjoin (FractionRing S) (Set.range fun j : ι => iota (b j))) := by
  -- The adjoin is finite because its finitely many generators are integral over `FractionRing S`.
  refine IntermediateField.finiteDimensional_adjoin ?_
  rintro x ⟨j, rfl⟩
  exact basis_image_isIntegral_over_fractionRingS (R := R) (S := S) b iota j

/-- Helper for Lemma 10.161.7: coefficients from `FractionRing R` land in the common overfield via
the scalar tower `FractionRing R → FractionRing S → Ω`. -/
lemma fractionRingR_image_mem_common_overfield
    {L : Type*} {Ω : Type*} {ι : Type*}
    [Field L] [Field Ω] [Fintype ι]
    [Algebra (FractionRing R) (FractionRing S)]
    [Algebra (FractionRing R) L] [Algebra (FractionRing S) Ω]
    [Algebra (FractionRing R) Ω] [IsScalarTower (FractionRing R) (FractionRing S) Ω]
    (b : Module.Basis ι (FractionRing R) L) (iota : L →ₐ[FractionRing R] Ω)
    (c : FractionRing R) :
    algebraMap (FractionRing S) Ω (algebraMap (FractionRing R) (FractionRing S) c) ∈
      IntermediateField.adjoin (FractionRing S) (Set.range fun j : ι => iota (b j)) := by
  -- Every intermediate field contains the image of its base field.
  exact IntermediateField.algebraMap_mem _ _

/-- Helper for Lemma 10.161.7: the embedding of the finite `FractionRing R`-extension lands in the
intermediate field generated by the images of a basis. -/
lemma lift_mem_common_overfield_of_basis
    {L : Type*} {Ω : Type*} {ι : Type*}
    [Field L] [Field Ω] [Fintype ι]
    [Algebra (FractionRing R) (FractionRing S)]
    [Algebra (FractionRing R) L] [Algebra (FractionRing S) Ω]
    [Algebra (FractionRing R) Ω] [IsScalarTower (FractionRing R) (FractionRing S) Ω]
    (b : Module.Basis ι (FractionRing R) L) (iota : L →ₐ[FractionRing R] Ω) (x : L) :
    iota x ∈ IntermediateField.adjoin (FractionRing S) (Set.range fun j : ι => iota (b j)) := by
  let T : IntermediateField (FractionRing S) Ω :=
    IntermediateField.adjoin (FractionRing S) (Set.range fun j : ι => iota (b j))
  -- Expand `x` in the chosen basis and map that equality into `Ω`.
  have hx :
      iota x = ∑ j, algebraMap (FractionRing R) Ω (b.repr x j) * iota (b j) := by
    calc
      iota x = iota (∑ j, b.repr x j • b j) := by rw [b.sum_repr]
      _ = ∑ j, algebraMap (FractionRing R) Ω (b.repr x j) * iota (b j) := by
        simp [map_sum, Algebra.smul_def]
  -- Each term of the mapped basis expansion already lies in the adjoined intermediate field.
  rw [hx]
  refine T.sum_mem ?_
  intro j _
  have hcoeff :
      algebraMap (FractionRing R) Ω (b.repr x j) ∈ T := by
    have hcoeff' :
        algebraMap (FractionRing S) Ω
            (algebraMap (FractionRing R) (FractionRing S) (b.repr x j)) ∈ T := by
      exact fractionRingR_image_mem_common_overfield (R := R) (S := S) b iota (b.repr x j)
    have hmap :
        algebraMap (FractionRing R) Ω (b.repr x j) =
          algebraMap (FractionRing S) Ω
            (algebraMap (FractionRing R) (FractionRing S) (b.repr x j)) := by
      simpa using congrArg
        (fun f : FractionRing R →+* Ω ↦ f (b.repr x j))
        (IsScalarTower.algebraMap_eq (FractionRing R) (FractionRing S) Ω)
    exact hmap.symm ▸ hcoeff'
  have hbasis : iota (b j) ∈ T := by
    exact IntermediateField.subset_adjoin (F := FractionRing S)
      (S := Set.range fun k : ι => iota (b k)) (by exact ⟨j, rfl⟩)
  have hmul :
      algebraMap (FractionRing R) Ω (b.repr x j) * iota (b j) ∈ T := by
    exact T.mul_mem hcoeff hbasis
  -- Rewrite the coefficient multiplication back into the scalar action coming from `FractionRing R`.
  simpa [Algebra.smul_def] using hmul

/-- Helper for Lemma 10.161.7: a named finite intermediate field over `FractionRing S` inherits
finite normalization over `S` from the `N-2` property of `S`. -/
lemma common_overfield_integralClosure_finite
    {Ω : Type*} [Field Ω] [Algebra S Ω] [Algebra (FractionRing S) Ω]
    [IsScalarTower S (FractionRing S) Ω] [IsN2Ring S]
    (T : IntermediateField (FractionRing S) Ω)
    [FiniteDimensional (FractionRing S) T] :
    Module.Finite S (integralClosure S T) := by
  -- Keep the common overfield opaque and invoke the `N-2` bridge on this named field.
  exact IsN2Ring.integralClosure_finite_of_finiteDimensional (R := S) (L := T)

/-- Helper for Lemma 10.161.7: if an embedding into `Ω` lands in a named common overfield `T`,
codrestrict it once so later proofs never elaborate the raw adjoin carrier again. -/
noncomputable def common_overfield_codrestrict
    {L : Type*} {Ω : Type*} [Field L] [Field Ω]
    [Algebra (FractionRing R) (FractionRing S)] [Algebra (FractionRing R) L]
    [Algebra (FractionRing S) Ω]
    [Algebra (FractionRing R) Ω] [IsScalarTower (FractionRing R) (FractionRing S) Ω]
    (T : IntermediateField (FractionRing S) Ω)
    (iota : L →ₐ[FractionRing R] Ω) (hiota : ∀ x : L, iota x ∈ T) :
    L →ₐ[FractionRing R] T := by
  -- Restrict the ambient embedding to the named intermediate field once and for all.
  let T' : IntermediateField (FractionRing R) Ω := T.restrictScalars (FractionRing R)
  refine iota.codRestrict T'.toSubalgebra ?_
  intro x
  simpa [IntermediateField.mem_restrictScalars] using hiota x

/-- Helper for Lemma 10.161.7: use the `FractionRing R`-view of a named common overfield as the
single carrier in the final descent step. -/
abbrev common_overfield_carrier
    {Ω : Type*} [Field Ω] [Algebra (FractionRing R) (FractionRing S)]
    [Algebra (FractionRing S) Ω] [Algebra (FractionRing R) Ω]
    [IsScalarTower (FractionRing R) (FractionRing S) Ω]
    (T : IntermediateField (FractionRing S) Ω) :=
  ↥(T.restrictScalars (FractionRing R))

/-- Helper for Lemma 10.161.7: finiteness of the larger integral closure descends along an
injective map into a larger field over `S`. -/
lemma finite_of_integralClosure_map_to_larger_base
    {L : Type*} {M : Type*}
    [Field L] [Field M] [Algebra R L] [Algebra S M] [Algebra R M]
    [IsScalarTower R S M] (f : L →ₐ[R] M) (hf : Function.Injective f)
    (hfin : Module.Finite S (integralClosure S M)) :
    Module.Finite R (integralClosure R L) := by
  let g :
      integralClosure R L →ₐ[R]
        (integralClosure S M).restrictScalars R :=
    map_integralClosure_to_larger_base (R := R) (S := S) f
  have hfinR : Module.Finite R (integralClosure S M) := by
    -- The larger integral closure is finite over `S`, hence finite over `R`.
    exact Module.Finite.trans S (integralClosure S M)
  letI : Module.Finite R ((integralClosure S M).restrictScalars R) := by
    simpa using hfinR
  -- Descend finiteness through the injective restricted map on integral closures.
  exact Module.Finite.of_injective g.toLinearMap
    (map_integralClosure_to_larger_base_injective (R := R) (S := S) f hf)

/-- Helper for Lemma 10.161.7: after choosing a named finite common overfield `T`, finiteness of
its integral closure over `S` descends to finiteness of the integral closure of `R` in `L`. -/
lemma named_common_overfield_descent
    {L : Type*} {Ω : Type*} [Field L] [Field Ω]
    [Algebra (FractionRing R) (FractionRing S)]
    [Algebra R L] [Algebra (FractionRing R) L] [IsScalarTower R (FractionRing R) L]
    [Algebra S Ω] [Algebra (FractionRing S) Ω] [Algebra R Ω]
    [Algebra (FractionRing R) Ω] [IsScalarTower R S Ω]
    [IsScalarTower R (FractionRing R) Ω]
    [IsScalarTower S (FractionRing S) Ω]
    [IsScalarTower (FractionRing R) (FractionRing S) Ω]
    [IsN2Ring S]
    (T : IntermediateField (FractionRing S) Ω)
    [FiniteDimensional (FractionRing S) T]
    (iota : L →ₐ[FractionRing R] Ω) (hiota : ∀ x : L, iota x ∈ T) :
    Module.Finite R (integralClosure R L) := by
  -- Route correction: fix one carrier alias for `T` first, then keep both the `S`-side
  -- finiteness theorem and the `R`-side codrestricted map on that single carrier.
  let K := common_overfield_carrier (R := R) T
  letI : Field K := by
    dsimp [K, common_overfield_carrier]
    infer_instance
  letI : Algebra (FractionRing R) K := by
    dsimp [K, common_overfield_carrier]
    exact ((T.restrictScalars (FractionRing R)).toSubalgebra).algebra
  letI : Algebra R K := by
    dsimp [K, common_overfield_carrier]
    exact ((T.restrictScalars (FractionRing R)).toSubalgebra).algebra'
  letI : IsScalarTower R (FractionRing R) K := by
    refine ⟨fun x y z => ?_⟩
    exact Subtype.ext (smul_assoc x y (z : Ω))
  letI : Algebra S K := by
    dsimp [K, common_overfield_carrier]
    exact T.toSubalgebra.algebra'
  letI : IsScalarTower R S K := by
    refine ⟨fun x y z => ?_⟩
    exact Subtype.ext (smul_assoc x y (z : Ω))
  have hfinK : Module.Finite S (integralClosure S K) := by
    -- The `N-2` finiteness theorem for `S` applies to the same underlying common overfield.
    dsimp [K, common_overfield_carrier]
    simpa using common_overfield_integralClosure_finite (S := S) T
  let iotaK₀ : L →ₐ[FractionRing R] K := by
    -- Codrestrict once to the common overfield, keeping the fixed carrier alias.
    change L →ₐ[FractionRing R] ↥(T.restrictScalars (FractionRing R))
    exact common_overfield_codrestrict (R := R) (S := S) T iota hiota
  let iotaK : L →ₐ[R] K := AlgHom.restrictScalars R iotaK₀
  have hiotaK_injective : Function.Injective iotaK := by
    -- The restricted map has the same underlying values as the original embedding `iota`.
    intro x y hxy
    exact iota.injective (congrArg (fun z : K ↦ (z : Ω)) hxy)
  -- Descend finiteness along the injective map into the named common overfield.
  exact finite_of_integralClosure_map_to_larger_base
    (R := R) (S := S) iotaK hiotaK_injective hfinK

/-- Helper for Lemma 10.161.7: for a finite extension `L / FractionRing R`, the common-overfield
construction over `FractionRing S` gives the finiteness of the integral closure of `R` in `L`. -/
lemma integralClosure_finite_of_finite_extension
    (hRS : Function.Injective (algebraMap R S)) [IsN2Ring S]
    {L : Type u} [Field L] [Algebra R L] [Algebra (FractionRing R) L]
    [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L] :
    Module.Finite R (integralClosure R L) := by
  -- Route correction: keep the source-faithful common-overfield construction, but isolate the
  -- final packaging step instead of unfolding the adjoin expression in the main theorem.
  letI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hRS
  letI : FaithfulSMul R (FractionRing S) := inferInstance
  letI : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R (FractionRing S)
  letI : IsScalarTower R (FractionRing R) (FractionRing S) :=
    FractionRing.isScalarTower_liftAlgebra R (FractionRing S)
  let Ω := AlgebraicClosure (FractionRing S)
  letI : Algebra R Ω := inferInstance
  letI : Algebra S Ω := inferInstance
  letI : Algebra (FractionRing R) Ω := inferInstance
  letI : IsScalarTower R S Ω := inferInstance
  letI : IsScalarTower R (FractionRing R) Ω := inferInstance
  letI : IsScalarTower S (FractionRing S) Ω := inferInstance
  letI : IsScalarTower (FractionRing R) (FractionRing S) Ω := inferInstance
  let iota : L →ₐ[FractionRing R] Ω := IsAlgClosed.lift (R := FractionRing R) (S := L) (M := Ω)
  let b := Module.finBasis (FractionRing R) L
  let T : IntermediateField (FractionRing S) Ω :=
    IntermediateField.adjoin (FractionRing S) (Set.range fun j => iota (b j))
  letI : FiniteDimensional (FractionRing S) T :=
    finite_common_overfield_of_basis (R := R) (S := S) b iota
  have hiota : ∀ x : L, iota x ∈ T := by
    -- The common overfield is generated by the images of a basis, so it contains all of `L`.
    intro x
    exact lift_mem_common_overfield_of_basis (R := R) (S := S) b iota x
  -- Invoke the abstract descent step on the named common overfield `T`.
  exact named_common_overfield_descent (R := R) (S := S) T iota hiota

-- Proof sketch: fix a finite extension `L` of `FractionRing R`. Using the finite domain extension
-- `R ⊂ S`, view `L` as a finite extension of `FractionRing S`. The integral closure of `R` in `L`
-- is contained in the integral closure of `S` in `L`; the latter is finite over `S` by the `N-2`
-- hypothesis on `S`, hence finite over `R` because `S` is finite over `R`.
/-- Lemma 10.161.7 (2): if `R` is a Noetherian domain, `R ⊂ S` is a finite extension of domains,
and `S` is `N-2`, then `R` is `N-2`. -/
theorem isN2Ring_of_finite_extension
    (hRS : Function.Injective (algebraMap R S)) [IsN2Ring S] :
    IsN2Ring R := by
  refine IsN2Ring.mk ?_
  intro L _ _ _ _ _
  exact integralClosure_finite_of_finite_extension (R := R) (S := S) hRS

end

/-! ### Lemma_10_161_8 (from Chap10) -/
/- Lemma 10.161.8: if `R` is a Noetherian normal domain with fraction field `K` and `L / K` is a
finite separable field extension, then the integral closure of `R` in `L` is finite over `R`.
This is the canonical theorem `IsIntegralClosure.finite`. -/
recall IsIntegralClosure.finite

/-! ### Example_10_161_9 (from Chap10) -/
/-
Domain triage: this file is in the commutative algebra of monomially generated subalgebras of
countable polynomial rings, together with their integral-closure and module-finiteness behavior.

Owner abstractions sampled for this item:
- `Algebra.adjoin`, the canonical owner for the quadratic-monomial subalgebra;
- `Algebra.subset_adjoin`, the canonical generator-membership API for that owner;
- `IsIntegralClosure`, the canonical owner predicate for normalization inside a larger ring;
- `IsIntegralClosure.finite`, the canonical finite-normalization theorem recalled in
  `Lemma_10_161_8`.

Source/core/bridge triage:
- `source-facing`: the final counterexample theorem for the explicit quadratic-monomial
  subalgebra of `ℂ[x_0, x_1, x_2, \ldots]`;
- `core/canonical`: the owner subalgebra `complexQuadraticMonomialSubalgebra` and the canonical
  predicates `IsIntegrallyClosed`, `IsIntegralClosure`, and `Module.Finite`;
- `bridge/view`: the generator-membership lemma below.

Primitive data are only the ambient polynomial ring and the quadratic-monomial-generated
subalgebra. Integrally closedness, being an integral closure, and failure of module finiteness are
derived API and should not be bundled into a replacement wrapper structure.
-/

open MvPolynomial

noncomputable section

section

local notation "A∞" => MvPolynomial ℕ ℂ

/-- The quadratic monomials `X i * X j` inside `ℂ[x_0, x_1, x_2, \ldots]`. -/
private def complexQuadraticMonomials : Set A∞ :=
  Set.range fun p : ℕ × ℕ ↦ ((X p.1 : A∞) * X p.2 : A∞)

/-- The `ℂ`-subalgebra of `ℂ[x_0, x_1, x_2, \ldots]` generated by all quadratic monomials
`X i * X j`. -/
def complexQuadraticMonomialSubalgebra : Subalgebra ℂ A∞ :=
  Algebra.adjoin ℂ complexQuadraticMonomials

local notation "R∞" => complexQuadraticMonomialSubalgebra

/-- Each quadratic monomial generator lies in the quadratic subalgebra. -/
-- Proof sketch: each displayed quadratic monomial belongs to the generating set used in the
-- definition of `Algebra.adjoin`.
theorem quadratic_monomial_mem_complexQuadraticMonomialSubalgebra (i j : ℕ) :
    ((X i : A∞) * X j : A∞) ∈ R∞ := by
  simpa [complexQuadraticMonomialSubalgebra, complexQuadraticMonomials] using
    (Algebra.subset_adjoin <|
      show ((X i : A∞) * X j : A∞) ∈ complexQuadraticMonomials from
        ⟨(i, j), rfl⟩)

/-- The quadratic subalgebra is integrally closed. -/
-- Proof sketch: identify `R∞` with the invariant ring for the order-two sign action on `A∞`.
-- Since `A∞` is a normal domain over a characteristic-zero field, the invariant subring is
-- integrally closed.
theorem isIntegrallyClosed_complexQuadraticMonomialSubalgebra :
    IsIntegrallyClosed R∞ := sorry

/-- The countable polynomial ring is the integral closure of the quadratic subalgebra in its
fraction field. -/
-- Proof sketch: each variable `X i` is integral over `R∞` because it satisfies a monic quadratic
-- polynomial with coefficients in `R∞`; conversely, the integral closure of `R∞` inside
-- `Frac(A∞)` is exactly `A∞`.
theorem isIntegralClosure_complexQuadraticMonomialSubalgebra :
    IsIntegralClosure A∞ R∞ (FractionRing A∞) := sorry

/-- The countable polynomial ring is not finite as a module over the quadratic monomial
subalgebra. -/
-- Proof sketch: the sign action of `{±1}` identifies `R∞` with the invariant ring, but the
-- infinitely many variables prevent `A∞` from being a finite `R∞`-module.
theorem complexQuadraticMonomialSubalgebra_not_module_finite :
    ¬ Module.Finite R∞ A∞ := sorry

/-- Example 10.161.9: for `A = ℂ[x_0, x_1, x_2, \ldots]` and `R = ℂ[x_i x_j]`, the extension
`R ⊆ A` is not finite, although `A` is the integral closure of `R` in the fraction field of `A`.
This gives a non-Noetherian counterexample to Lemma 10.161.8. -/
-- Proof sketch: `A` is integral over `R∞` because each variable satisfies a monic quadratic
-- polynomial over `R∞`. The sign action of `{±1}` identifies `R∞` with the invariant ring, but
-- the infinitely many variables prevent `A` from being a finite `R∞`-module.
theorem complexQuadraticMonomialSubalgebra_not_module_finite_and_has_integral_closure :
    ¬ Module.Finite R∞ A∞ ∧ IsIntegralClosure A∞ R∞ (FractionRing A∞) := by
  exact ⟨complexQuadraticMonomialSubalgebra_not_module_finite,
    isIntegralClosure_complexQuadraticMonomialSubalgebra⟩

end

end

/-! ### Lemma_10_161_10 (from Chap10) -/
open Polynomial

universe u v

section

variable {R : Type u} {K : Type v}
variable [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {p : ℕ} [Fact p.Prime] [CharP K p]

/-- Helper for Lemma 10.161.10: after writing an element of the fraction field as a quotient
`x / y`, multiplying by `y ^ p` clears denominators and keeps the derivation value nonzero. -/
lemma exists_rescaled_mem_range
    (a : K) (D : Derivation ℤ K K) (hDa : D a ≠ 0) :
    ∃ f b : R,
      algebraMap R K f ≠ 0 ∧
      algebraMap R K b = (algebraMap R K f) ^ p * a ∧
      ((algebraMap R K f) ^ p) * D a ≠ 0 := by
  let hp : Nat.Prime p := Fact.out
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective R a
  refine ⟨y, x * y ^ (p - 1), ?_, ?_, ?_⟩
  · -- The chosen denominator stays nonzero in the fraction field.
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  · -- Multiplying the quotient `x / y` by `y ^ p` leaves an element coming from `R`.
    have hyK : algebraMap R K y ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    have hp1 : 1 ≤ p := Nat.succ_le_of_lt hp.pos
    calc
      algebraMap R K (x * y ^ (p - 1))
          = algebraMap R K x * (algebraMap R K y) ^ (p - 1) := by
              simp [map_mul, map_pow]
      _ = algebraMap R K x * ((algebraMap R K y) ^ p * (algebraMap R K y)⁻¹) := by
            simpa using congrArg (fun z => algebraMap R K x * z) (pow_sub₀ (algebraMap R K y) hyK hp1)
      _ = (algebraMap R K y) ^ p * (algebraMap R K x / algebraMap R K y) := by
            rw [div_eq_mul_inv]
            ac_rfl
  · -- A nonzero scalar multiple of the nonzero derivation value is still nonzero.
    exact mul_ne_zero (pow_ne_zero _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy)) hDa

/-- Helper for Lemma 10.161.10: a derivation that does not kill `a` rules out `a` being a
`p`th power. -/
lemma pth_power_ne_of_derivation_nonzero
    (D : Derivation ℤ K K) {a : K} (hDa : D a ≠ 0) :
    ∀ b : K, b ^ p ≠ a := by
  intro b hb
  apply hDa
  rw [← hb, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K]
  simp

/-- Helper for Lemma 10.161.10: the derivation hypothesis makes `X ^ p - C a` irreducible over
the fraction field. -/
lemma irreducible_X_pow_sub_C_of_exists_derivation
    (a : K)
    (hD : ∃ D : Derivation ℤ K K,
      Set.MapsTo D (Set.range (algebraMap R K)) (Set.range (algebraMap R K)) ∧
        D a ≠ 0) :
    Irreducible (X ^ p - C a) := by
  rcases hD with ⟨D, -, hDa⟩
  apply X_pow_sub_C_irreducible_of_prime (Fact.out : Nat.Prime p)
  exact pth_power_ne_of_derivation_nonzero (p := p) D hDa

/-- Helper for Lemma 10.161.10: after the denominator-clearing step, differentiating the relation
`b = f ^ p * a` shows that the new coefficient still has nonzero derivative. -/
lemma rescaled_derivation_nonzero
    (D : Derivation ℤ K K)
    {f b : R}
    (hf : algebraMap R K f ≠ 0)
    (hb : algebraMap R K b = (algebraMap R K f) ^ p * a)
    (hDa : D a ≠ 0) :
    D (algebraMap R K b) ≠ 0 := by
  -- Differentiate the rescaling identity; the `p`th power factor contributes no derivative in
  -- characteristic `p`, so the new derivative is the same nonzero scalar multiple of `D a`.
  have hpow :
      D ((algebraMap R K f) ^ p) = 0 := by
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K]
    simp
  have hderiv :
      D (algebraMap R K b) = ((algebraMap R K f) ^ p) * D a := by
    calc
      D (algebraMap R K b) = D ((algebraMap R K f) ^ p * a) := by rw [hb]
      _ = ((algebraMap R K f) ^ p) * D a + a * D ((algebraMap R K f) ^ p) := by
            rw [Derivation.leibniz]
            simp [Algebra.smul_def, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
              mul_assoc]
      _ = ((algebraMap R K f) ^ p) * D a := by simp [hpow]
  rw [hderiv]
  exact mul_ne_zero (pow_ne_zero _ hf) hDa

/-- Helper for Lemma 10.161.10: if `b = f ^ p * a` with `f ≠ 0`, then adjoining a `p`th root of
`b` is `K`-algebra equivalent to adjoining a `p`th root of `a`, by rescaling the distinguished
root by `f`. -/
theorem adjoinRoot_pth_root_rescale_equiv_of_mem_range
    (a : K) {f b : R}
    (hf : algebraMap R K f ≠ 0)
    (hb : algebraMap R K b = (algebraMap R K f) ^ p * a) :
    Nonempty (AdjoinRoot (X ^ p - C (algebraMap R K b)) ≃ₐ[K] AdjoinRoot (X ^ p - C a)) := by
  let Pₐ : K[X] := X ^ p - C a
  let P_b : K[X] := X ^ p - C (algebraMap R K b)
  let Lₐ := AdjoinRoot Pₐ
  let L_b := AdjoinRoot P_b
  let u : K := algebraMap R K f
  have hu : u ≠ 0 := hf
  let α : Lₐ := algebraMap K Lₐ u * AdjoinRoot.root Pₐ
  have hα :
      P_b.eval₂ (Algebra.ofId K Lₐ) α = 0 := by
    -- The scaled root satisfies the polynomial with coefficient `b`.
    have hαpow : α ^ p = algebraMap K Lₐ (algebraMap R K b) := by
      calc
        α ^ p = (algebraMap K Lₐ u * AdjoinRoot.root Pₐ) ^ p := by rfl
        _ = (algebraMap K Lₐ u) ^ p * (AdjoinRoot.root Pₐ) ^ p := by
              rw [mul_pow]
        _ = algebraMap K Lₐ (u ^ p) * AdjoinRoot.of Pₐ a := by
              rw [map_pow, root_X_pow_sub_C_pow]
        _ = algebraMap K Lₐ (u ^ p * a) := by
              rw [AdjoinRoot.algebraMap_eq]
              simp [map_mul]
        _ = algebraMap K Lₐ (algebraMap R K b) := by rw [hb]
    calc
      P_b.eval₂ (Algebra.ofId K Lₐ) α = α ^ p - algebraMap K Lₐ (algebraMap R K b) := by
        simp [P_b, α]
      _ = 0 := by rw [hαpow, sub_self]
  let φ : L_b →ₐ[K] Lₐ := AdjoinRoot.liftAlgHom P_b (Algebra.ofId K Lₐ) α hα
  let β : L_b := algebraMap K L_b u⁻¹ * AdjoinRoot.root P_b
  have hβ :
      Pₐ.eval₂ (Algebra.ofId K L_b) β = 0 := by
    -- Rescaling by the inverse scalar sends a root of `X ^ p - b` back to a root of `X ^ p - a`.
    have hu_pow : u ^ p ≠ 0 := pow_ne_zero _ hu
    have hβpow : β ^ p = algebraMap K L_b a := by
      calc
        β ^ p = (algebraMap K L_b u⁻¹ * AdjoinRoot.root P_b) ^ p := by rfl
        _ = (algebraMap K L_b u⁻¹) ^ p * (AdjoinRoot.root P_b) ^ p := by
              rw [mul_pow]
        _ = algebraMap K L_b ((u⁻¹) ^ p) * AdjoinRoot.of P_b (algebraMap R K b) := by
              rw [map_pow, root_X_pow_sub_C_pow]
        _ = algebraMap K L_b (((u⁻¹) ^ p) * algebraMap R K b) := by
              rw [AdjoinRoot.algebraMap_eq]
              simp [map_mul]
        _ = algebraMap K L_b (((u⁻¹) ^ p) * (u ^ p * a)) := by rw [hb]
        _ = algebraMap K L_b a := by
              rw [← mul_assoc, inv_pow, inv_mul_cancel₀ hu_pow, one_mul]
    calc
      Pₐ.eval₂ (Algebra.ofId K L_b) β = β ^ p - algebraMap K L_b a := by
        simp [Pₐ, β]
      _ = 0 := by rw [hβpow, sub_self]
  let ψ : Lₐ →ₐ[K] L_b := AdjoinRoot.liftAlgHom Pₐ (Algebra.ofId K L_b) β hβ
  have hψφ : ψ.comp φ = AlgHom.id K L_b := by
    -- The composite fixes the distinguished root, hence is the identity.
    apply AdjoinRoot.algHom_ext
    calc
      ψ (φ (AdjoinRoot.root P_b))
          = ψ (algebraMap K Lₐ u * AdjoinRoot.root Pₐ) := by
              rw [AdjoinRoot.liftAlgHom_root]
      _ = ψ (algebraMap K Lₐ u) * ψ (AdjoinRoot.root Pₐ) := by rw [map_mul]
      _ = algebraMap K L_b u * (algebraMap K L_b u⁻¹ * AdjoinRoot.root P_b) := by
            rw [AlgHom.commutes, AdjoinRoot.liftAlgHom_root]
      _ = AdjoinRoot.root P_b := by
            rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hu, map_one, one_mul]
      _ = AlgHom.id K L_b (AdjoinRoot.root P_b) := rfl
  have hφψ : φ.comp ψ = AlgHom.id K Lₐ := by
    -- The symmetric computation shows the reverse composite is also the identity.
    apply AdjoinRoot.algHom_ext
    calc
      φ (ψ (AdjoinRoot.root Pₐ))
          = φ (algebraMap K L_b u⁻¹ * AdjoinRoot.root P_b) := by
              rw [AdjoinRoot.liftAlgHom_root]
      _ = φ (algebraMap K L_b u⁻¹) * φ (AdjoinRoot.root P_b) := by rw [map_mul]
      _ = algebraMap K Lₐ u⁻¹ * (algebraMap K Lₐ u * AdjoinRoot.root Pₐ) := by
            rw [AlgHom.commutes, AdjoinRoot.liftAlgHom_root]
      _ = AdjoinRoot.root Pₐ := by
            rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hu, map_one, one_mul]
      _ = AlgHom.id K Lₐ (AdjoinRoot.root Pₐ) := rfl
  exact ⟨AlgEquiv.ofAlgHom φ ψ hφψ hψφ⟩

/-- Helper for Lemma 10.161.10: the derivation value on an element of `R` again comes from
`R` when the derivation preserves the image of `R`. -/
lemma exists_derivation_image_eq
    (b : R)
    (D : Derivation ℤ K K)
    (hMaps : Set.MapsTo D (Set.range (algebraMap R K)) (Set.range (algebraMap R K))) :
    ∃ delta0 : R, algebraMap R K delta0 = D (algebraMap R K b) := by
  -- Apply the range-preserving hypothesis to the coefficient coming from `b`.
  simpa using hMaps ⟨b, rfl⟩

/-- Helper for Lemma 10.161.10: the coefficient `δ₀ ∈ R` mapping to `D(b)` is nonzero whenever
`D(b)` is nonzero. -/
lemma derivation_image_ne_zero
    (b : R)
    (D : Derivation ℤ K K)
    {delta0 : R}
    (hdelta : algebraMap R K delta0 = D (algebraMap R K b))
    (hDb : D (algebraMap R K b) ≠ 0) :
    delta0 ≠ 0 := by
  -- Injectivity of the fraction-field map lets us pull the nonvanishing back to `R`.
  intro hzero
  apply hDb
  simpa [hzero] using hdelta.symm

/-- Helper for Lemma 10.161.10: fix the `Fin p`-indexed power basis for the reduced polynomial
`X ^ p - b`. -/
noncomputable def adjoinRoot_pth_root_basis (b : R) :
    Module.Basis (Fin p) K (AdjoinRoot (X ^ p - C (algebraMap R K b))) :=
  (AdjoinRoot.powerBasis' (monic_X_pow_sub_C (algebraMap R K b) (Fact.out : Nat.Prime p).ne_zero)).basis.reindex <|
    finCongr (natDegree_X_pow_sub_C (R := K) (n := p) (r := algebraMap R K b))

/-- Helper for Lemma 10.161.10: the fixed `Fin p` basis vectors are the powers of the adjoined
root. -/
lemma adjoinRoot_pth_root_basis_apply
    (b : R) (j : Fin p) :
    adjoinRoot_pth_root_basis (R := R) (K := K) (p := p) b j =
      AdjoinRoot.root (X ^ p - C (algebraMap R K b)) ^ (j : ℕ) := by
  -- Reindexing the canonical power basis only changes the index type, not the basis vectors.
  rw [adjoinRoot_pth_root_basis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow,
    finCongr_symm_apply, Fin.val_cast]
  simp [AdjoinRoot.powerBasis']

/-- Helper for Lemma 10.161.10: coordinates in the fixed `Fin p` power basis. -/
noncomputable def adjoinRoot_pth_root_coord (b : R) :
    AdjoinRoot (X ^ p - C (algebraMap R K b)) → Fin p → K :=
  fun y j ↦ (adjoinRoot_pth_root_basis (R := R) (K := K) (p := p) b).repr y j

/-- Helper for Lemma 10.161.10: every element of the reduced `AdjoinRoot` algebra reconstructs
from its fixed `Fin p` power-basis coordinates. -/
lemma adjoinRoot_pth_root_sum_repr
    (b : R)
    (y : AdjoinRoot (X ^ p - C (algebraMap R K b))) :
    ∑ j : Fin p, adjoinRoot_pth_root_coord (R := R) (K := K) (p := p) b y j •
        AdjoinRoot.root (X ^ p - C (algebraMap R K b)) ^ (j : ℕ) = y := by
  -- Reconstruct from the basis coordinates, then rewrite the basis vectors as powers of the root.
  simpa [adjoinRoot_pth_root_coord, Algebra.smul_def, adjoinRoot_pth_root_basis_apply] using
    (adjoinRoot_pth_root_basis (R := R) (K := K) (p := p) b).sum_repr y

/-- Helper for Lemma 10.161.10: when the coefficient already lies in `R`, the distinguished root
is integral over `R`. -/
lemma adjoinRoot_root_isIntegral_of_mem_range
    (b : R) :
    IsIntegral R
      (AdjoinRoot.root (X ^ p - C (algebraMap R K b)) :
        AdjoinRoot (X ^ p - C (algebraMap R K b))) := by
  refine ⟨X ^ p - C b, monic_X_pow_sub_C b (Fact.out : Nat.Prime p).ne_zero, ?_⟩
  -- The distinguished root satisfies the monic polynomial `X ^ p - b` over `R`.
  calc
    aeval
        (AdjoinRoot.root (X ^ p - C (algebraMap R K b)) :
          AdjoinRoot (X ^ p - C (algebraMap R K b)))
        (X ^ p - C b)
      = (AdjoinRoot.root (X ^ p - C (algebraMap R K b))) ^ p -
          algebraMap R (AdjoinRoot (X ^ p - C (algebraMap R K b))) b := by
            simp
    _ = 0 := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
            IsScalarTower.algebraMap_eq R K
              (AdjoinRoot (X ^ p - C (algebraMap R K b)))] using
            sub_eq_zero.mpr (root_X_pow_sub_C_pow p (algebraMap R K b))

/-- Helper for Lemma 10.161.10: once the integral closure is trapped in the span of a finite
family, Noetherianity turns that containment into module finiteness. -/
lemma integralClosure_finite_of_le_span
    {L : Type*} [Field L] [Algebra R L]
    {s : Set L} (hs : s.Finite)
    (hle : Subalgebra.toSubmodule (integralClosure R L) ≤ Submodule.span R s) :
    Module.Finite R (integralClosure R L) := by
  -- The finite family gives a finitely generated ambient span.
  have hfg_span : (Submodule.span R s).FG := by
    rw [← Module.Finite.iff_fg]
    exact Module.Finite.span_of_finite R hs
  -- The integral closure submodule is finitely generated inside that Noetherian ambient module.
  have hfg_ic : (Subalgebra.toSubmodule (integralClosure R L)).FG :=
    Submodule.FG.of_le hfg_span hle
  exact ⟨(Subalgebra.toSubmodule (integralClosure R L)).fg_top.mpr hfg_ic⟩

/-- Helper for Lemma 10.161.10: once every fixed power-basis coefficient is cleared by the same
power of `D(b)`, the element lies in the span of the corresponding rescaled root powers. -/
lemma mem_span_scaled_root_powers_of_cleared_coordinates
    (b delta0 : R)
    (hdelta0 : delta0 ≠ 0)
    (y : AdjoinRoot (X ^ p - C (algebraMap R K b)))
    (hcoeff : ∀ j : Fin p, ∃ r : R,
      algebraMap R K r =
        (algebraMap R K delta0 : K) ^ (p - 1) *
          adjoinRoot_pth_root_coord (R := R) (K := K) (p := p) b y j) :
    y ∈ Submodule.span R
      (Set.range fun j : Fin p ↦
        algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b)))
          (((algebraMap R K delta0 : K) ^ (p - 1))⁻¹) *
            AdjoinRoot.root (X ^ p - C (algebraMap R K b)) ^ (j : ℕ)) := by
  let delta : K := algebraMap R K delta0
  let deltaPow : K := delta ^ (p - 1)
  have hdelta : delta ≠ 0 := by
    -- The derivative value stays nonzero after mapping into the fraction field.
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hdelta0)
  have hdeltaPow : deltaPow ≠ 0 := by
    -- The common clearing scalar is a nonzero power of `delta`.
    simp [deltaPow, delta, hdelta]
  -- Reconstruct `y` from its fixed power-basis coordinates and place each summand in the span.
  rw [← adjoinRoot_pth_root_sum_repr (R := R) (K := K) (p := p) b y]
  refine Submodule.sum_mem _ ?_
  intro j hj
  rcases hcoeff j with ⟨r, hr⟩
  have hcoord :
      (algebraMap R K r : K) * deltaPow⁻¹ =
        adjoinRoot_pth_root_coord (R := R) (K := K) (p := p) b y j := by
    -- Solving for the coefficient is the endgame algebra from the source proof.
    calc
      (algebraMap R K r : K) * deltaPow⁻¹ =
          (deltaPow *
              adjoinRoot_pth_root_coord (R := R) (K := K) (p := p) b y j) * deltaPow⁻¹ := by
            simpa [deltaPow, delta] using congrArg (fun z : K ↦ z * deltaPow⁻¹) hr
      _ = adjoinRoot_pth_root_coord (R := R) (K := K) (p := p) b y j *
            (deltaPow * deltaPow⁻¹) := by
            ac_rfl
      _ = adjoinRoot_pth_root_coord (R := R) (K := K) (p := p) b y j := by
            rw [mul_inv_cancel₀ hdeltaPow, mul_one]
  have hterm :
      adjoinRoot_pth_root_coord (R := R) (K := K) (p := p) b y j •
          AdjoinRoot.root (X ^ p - C (algebraMap R K b)) ^ (j : ℕ) =
        r •
          (algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b))) (deltaPow⁻¹) *
            AdjoinRoot.root (X ^ p - C (algebraMap R K b)) ^ (j : ℕ)) := by
    -- Rewrite the `K`-coefficient as an `R`-scalar times the rescaled basis vector.
    rw [Algebra.smul_def, Algebra.smul_def, ← hcoord]
    calc
      algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b)))
          ((algebraMap R K r : K) * deltaPow⁻¹) *
          AdjoinRoot.root (X ^ p - C (algebraMap R K b)) ^ (j : ℕ) =
        (algebraMap R (AdjoinRoot (X ^ p - C (algebraMap R K b))) r *
            algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b))) (deltaPow⁻¹)) *
          AdjoinRoot.root (X ^ p - C (algebraMap R K b)) ^ (j : ℕ) := by
            simp [map_mul, IsScalarTower.algebraMap_eq R K
              (AdjoinRoot (X ^ p - C (algebraMap R K b)))]
      _ = algebraMap R (AdjoinRoot (X ^ p - C (algebraMap R K b))) r *
            (algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b))) (deltaPow⁻¹) *
              AdjoinRoot.root (X ^ p - C (algebraMap R K b)) ^ (j : ℕ)) := by
            rw [mul_assoc]
  rw [hterm]
  -- Each rescaled power is one of the chosen generators, so scalar closure finishes.
  have hgen :
      algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b))) (deltaPow⁻¹) *
          AdjoinRoot.root (X ^ p - C (algebraMap R K b)) ^ (j : ℕ) ∈
        Set.range fun j : Fin p ↦
          algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b))) (deltaPow⁻¹) *
            AdjoinRoot.root (X ^ p - C (algebraMap R K b)) ^ (j : ℕ) := by
    exact ⟨j, rfl⟩
  exact Submodule.smul_mem _ r (Submodule.subset_span hgen)

/-- Helper for Lemma 10.161.10: once the coefficient lies in `R`, the remaining argument is the
source-proof induction that clears the power-basis coefficients using the nonzero derivative. -/
lemma integralClosure_finite_adjoinRoot_pth_root_of_mem_range_of_exists_derivation
    (b : R)
    (D : Derivation ℤ K K)
    (hMaps : Set.MapsTo D (Set.range (algebraMap R K)) (Set.range (algebraMap R K)))
    (hDb : D (algebraMap R K b) ≠ 0) :
    Module.Finite R (integralClosure R (AdjoinRoot (X ^ p - C (algebraMap R K b)))) := by
  let hIrred : Irreducible (X ^ p - C (algebraMap R K b)) :=
    irreducible_X_pow_sub_C_of_exists_derivation (R := R) (p := p) (algebraMap R K b)
      ⟨D, hMaps, hDb⟩
  letI : Fact (Irreducible (X ^ p - C (algebraMap R K b))) := Fact.mk hIrred
  letI : Field (AdjoinRoot (X ^ p - C (algebraMap R K b))) := AdjoinRoot.instField
  obtain ⟨delta0, hdelta⟩ :=
    exists_derivation_image_eq (R := R) (K := K) b D hMaps
  have hdelta0 : delta0 ≠ 0 :=
    derivation_image_ne_zero (R := R) (K := K) b D hdelta hDb
  let x : AdjoinRoot (X ^ p - C (algebraMap R K b)) :=
    AdjoinRoot.root (X ^ p - C (algebraMap R K b))
  let coord :
      AdjoinRoot (X ^ p - C (algebraMap R K b)) → Fin p → K :=
    adjoinRoot_pth_root_coord (R := R) (K := K) (p := p) b
  have hxIntegral : IsIntegral R x := by
    -- The source proof uses that the adjoined root is integral once the coefficient lies in `R`.
    simpa [x] using adjoinRoot_root_isIntegral_of_mem_range (R := R) (K := K) (p := p) b
  have hsum_repr :
      ∀ y : AdjoinRoot (X ^ p - C (algebraMap R K b)),
        ∑ j : Fin p, coord y j • x ^ (j : ℕ) = y := by
    -- Fix the `Fin p` coordinates once so the remaining induction can work with explicit sums.
    intro y
    simpa [coord, x] using
      adjoinRoot_pth_root_sum_repr (R := R) (K := K) (p := p) b y
  let scaledRootPowers :
      Set (AdjoinRoot (X ^ p - C (algebraMap R K b))) :=
    Set.range fun j : Fin p ↦
      algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b)))
          (((algebraMap R K delta0 : K) ^ (p - 1))⁻¹) * x ^ (j : ℕ)
  have hcontain :
      Subalgebra.toSubmodule
          (integralClosure R (AdjoinRoot (X ^ p - C (algebraMap R K b)))) ≤
        Submodule.span R scaledRootPowers := by
    intro y hy
    have clear_trunc :
        ∀ i : ℕ, i ≤ p - 1 →
          ∀ z : integralClosure R (AdjoinRoot (X ^ p - C (algebraMap R K b))),
            (∀ j : Fin p, i < j.1 → coord (z : _) j = 0) →
            ∀ j : Fin p, j.1 ≤ i →
              ∃ r : R,
                algebraMap R K r =
                  (algebraMap R K delta0 : K) ^ i * coord (z : _) j := by
      intro i hi
      induction i with
      | zero =>
          intro z hz j hj
          have hj0 : j = 0 := Fin.ext (Nat.eq_zero_of_le_zero hj)
          subst hj0
          have hscalar :
              (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) =
                algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b)))
                  (coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) 0) := by
            -- The truncation hypothesis kills every positive root-power coefficient, so only the
            -- constant scalar term remains in the fixed basis expansion.
            calc
              (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) =
                  ∑ j : Fin p,
                    coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) j •
                      x ^ (j : ℕ) := by
                        symm
                        exact hsum_repr (z : AdjoinRoot (X ^ p - C (algebraMap R K b)))
              _ =
                  coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) 0 • x ^ (0 : ℕ) := by
                    refine Finset.sum_eq_single 0 ?_ ?_
                    · intro j _ hj0
                      have hjpos : 0 < j.1 := Nat.pos_of_ne_zero fun hzero ↦
                        hj0 (Fin.ext hzero)
                      simp [hz j hjpos]
                    · intro hzero
                      simp at hzero
              _ =
                  algebraMap K (AdjoinRoot (X ^ p - C (algebraMap R K b)))
                    (coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) 0) := by
                      simp [Algebra.smul_def]
          have hcoord_integral :
              IsIntegral R
                (coord (z : AdjoinRoot (X ^ p - C (algebraMap R K b))) 0) := by
            -- Rewriting the integral element as a scalar in the fraction field lets us descend
            -- that scalar back to `R` because `R` is integrally closed in `K`.
            rw [← isIntegral_algebraMap_iff (algebraMap K
              (AdjoinRoot (X ^ p - C (algebraMap R K b)))).injective, ← hscalar]
            exact z.2
          obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hcoord_integral
          exact ⟨r, by simpa using hr⟩
      | succ i ih =>
          intro z hz j hj
          -- TODO: Source-faithful successor step. Build the lowered derivative element
          -- `z' = Σ_j ((j+1) * D(b) * coeff_{j+1}(z)) x^j`, prove `(z')^p` comes from `R` by
          -- differentiating the scalar witness for `z^p ∈ R`, apply `ih` to clear the shifted
          -- coefficients, and then recover the constant term by subtracting the controlled tail.
          sorry
    -- Route correction: the remaining open step is now isolated to the source-proof induction
    -- that clears the fixed `Fin p` coordinates of the integral element `y`.
    have hcoeff :
        ∀ j : Fin p, ∃ r : R,
          algebraMap R K r =
            (algebraMap R K delta0 : K) ^ (p - 1) * coord (y : _) j := by
      -- Apply the source invariant at the full truncation degree `p - 1`; the upper-tail
      -- vanishing hypothesis is vacuous because `Fin p` has no indices above `p - 1`.
      intro j
      exact clear_trunc (p - 1) le_rfl ⟨y, hy⟩
        (fun j hj ↦ False.elim <| Nat.not_lt_of_ge (Nat.le_pred_of_lt j.2) hj)
        j (Nat.le_pred_of_lt j.2)
    -- Once the coefficients are cleared, the source proof ends by rewriting `y` in the fixed
    -- power basis and observing that each summand is an `R`-multiple of a rescaled root power.
    simpa [scaledRootPowers, coord, x] using
      mem_span_scaled_root_powers_of_cleared_coordinates
        (R := R) (K := K) (p := p) b delta0 hdelta0 (y : _)
        hcoeff
  -- Route correction: the remaining work is the reduced-case coefficient-clearing induction from
  -- the source proof, after extracting `δ = D(b)` in the image of `R`. The endgame is now
  -- isolated in `hcontain`, which is the finite-span trap from the textbook proof.
  exact integralClosure_finite_of_le_span (R := R) (hs := Set.finite_range _) hcontain

/-
Domain-style sampling:
* primary domain: commutative algebra of finite normalization in purely inseparable degree-`p`
  extensions of a fraction field, with the auxiliary input of an absolute derivation detecting that
  the adjoined element is not a `p`th power;
* sampled owner-style declarations:
  - `IsN2Ring.integralClosure_finite`, the chapter owner field for finite normalization in finite
    fraction-field extensions;
  - `Derivation ℤ K K`, the canonical absolute-derivation owner from Chapter `10.131`;
  - `integralClosure`, the normalization owner from Chapter `10.36`;
  - `Polynomial.Monic.finite_adjoinRoot`, the canonical finite `K`-algebra API for
    `AdjoinRoot (X ^ p - C a)`;
  - `X_pow_sub_C_irreducible_of_prime`, the standard bridge for the degree-`p` purely inseparable
    step when `a` is not a `p`th power.
* layer triage:
  - `source-facing`: the finiteness theorem for the normalization in the single-root extension
    `AdjoinRoot (X ^ p - C a)`;
  - `core/canonical`: `Derivation ℤ K K` for the absolute derivation,
    `AdjoinRoot (X ^ p - C a)` for the degree-`p` purely inseparable step,
    `integralClosure` for the normalization owner, and `Module.Finite` for the finiteness
    conclusion;
  - `bridge/view`: the canonical irreducibility theorem `X_pow_sub_C_irreducible_of_prime`,
    together with the derived `AdjoinRoot` field and finite `K`-algebra API
    `AdjoinRoot.instField` and `Polynomial.Monic.finite_adjoinRoot`.
* owner decision: this file stays `source-facing`. The textbook item is not introducing a new owner
  abstraction beyond the canonical normalization/finiteness owners; it is a criterion for one
  specific purely inseparable step, so no wrapper around `integralClosure` or `AdjoinRoot` should
  be added here.
* primitive data: `R`, its fraction field `K`, the prime characteristic `p`, the element `a : K`,
  and the chosen derivation witness.
* derived API: the `AdjoinRoot` algebra structure and its finiteness over `K` are canonical
  consequences of the sampled owner API and should not be promoted to separate public data in this
  file. They are auxiliary to the source-facing normalization statement, not a replacement for it.
-/

/-- Lemma 10.161.10: if `R` is a Noetherian normal domain, `K` is a fraction field of `R` of
characteristic `p > 0`, `a : K`, and there exists an absolute derivation of `K` preserving the
image of `R` and not killing `a`, then the integral closure of `R` in the canonical quotient
`AdjoinRoot (X ^ p - C a) ≅ K[x] / (x^p - a)` is finite over `R`. -/
-- Proof sketch: clear denominators so that `a ∈ R`, then extend the derivation to the fraction
-- field and argue by induction on the degree in the adjoined root. For an integral element
-- `y = a₀ + a₁x + ... + aᵢxᵢ`, differentiating `y ^ p ∈ R` shows that suitable powers of `D a`
-- clear the coefficients `aⱼ`. Hence every integral element lies in a fixed finite `R`-submodule
-- generated by finitely many rescaled powers of `x`, so the integral closure is module-finite.
theorem integralClosure_finite_adjoinRoot_pth_root_of_exists_derivation
    (a : K)
    (hD : ∃ D : Derivation ℤ K K,
      Set.MapsTo D (Set.range (algebraMap R K)) (Set.range (algebraMap R K)) ∧
        D a ≠ 0) :
    Module.Finite R (integralClosure R (AdjoinRoot (X ^ p - C a))) := by
  let hp : Nat.Prime p := Fact.out
  -- The derivation witness first shows that `x ^ p - a` is irreducible, so the adjoined-root
  -- algebra is the degree-`p` field extension used in the source proof.
  have hIrred : Irreducible (X ^ p - C a) :=
    irreducible_X_pow_sub_C_of_exists_derivation (R := R) (p := p) a hD
  letI : Fact (Irreducible (X ^ p - C a)) := Fact.mk hIrred
  letI : Field (AdjoinRoot (X ^ p - C a)) := AdjoinRoot.instField
  have hfiniteK : Module.Finite K (AdjoinRoot (X ^ p - C a)) := by
    exact (monic_X_pow_sub_C a hp.ne_zero).finite_adjoinRoot
  letI : Module.Finite K (AdjoinRoot (X ^ p - C a)) := hfiniteK
  letI : FiniteDimensional K (AdjoinRoot (X ^ p - C a)) := by infer_instance
  -- The source-proof reduction starts by clearing denominators and replacing `a` by `f ^ p * a`,
  -- which lies in the image of `R` while preserving the nonzero derivation value.
  obtain ⟨D, hMaps, hDa⟩ := hD
  obtain ⟨f, b, hf, hb, hDb⟩ := exists_rescaled_mem_range (R := R) (p := p) a D hDa
  have hDb' : D (algebraMap R K b) ≠ 0 :=
    rescaled_derivation_nonzero (R := R) (a := a) (p := p) D hf hb hDa
  have hfiniteReduced :
      Module.Finite R (integralClosure R (AdjoinRoot (X ^ p - C (algebraMap R K b)))) :=
    integralClosure_finite_adjoinRoot_pth_root_of_mem_range_of_exists_derivation
      (R := R) (K := K) (p := p) b D hMaps hDb'
  obtain ⟨e⟩ :=
    adjoinRoot_pth_root_rescale_equiv_of_mem_range (R := R) (K := K) (p := p) a hf hb
  let eR :
      AdjoinRoot (X ^ p - C (algebraMap R K b)) ≃ₐ[R] AdjoinRoot (X ^ p - C a) :=
    e.restrictScalars R
  letI :
      Module.Finite R (integralClosure R (AdjoinRoot (X ^ p - C (algebraMap R K b)))) :=
    hfiniteReduced
  exact Module.Finite.equiv eR.mapIntegralClosure.toLinearEquiv

end

/-! ### Lemma_10_161_11 (from Chap10) -/
universe u

/-
Domain-style sampling:
* primary domain: commutative algebra of finite normalization and the `N-1`/`N-2` conditions;
* owner abstractions sampled:
  - `IsN1Ring` and `IsN2Ring`, the chapter-owner source-facing classes from
    `Definition_10_161_1`;
  - `isN2Ring_of_finite_extension`, the chapter bridge/view theorem for descending `N-2` along a
    finite extension of domains;
  - `Lemma 10.161.8` / `IsIntegralClosure.finite`, the chapter recall of the canonical finite
    integral-closure theorem for finite separable fraction-field extensions over a Noetherian
    normal domain.
* layer triage:
  - `source-facing`: the equivalence theorem below;
  - `core/canonical`: the owner classes `IsN1Ring` and `IsN2Ring`;
  - `bridge/view`: passing to the normalization `integralClosure R (FractionRing R)` and
    descending `N-2` back to `R` through `isN2Ring_of_finite_extension`.
* primitive data are only the ring `R` together with the Noetherian, domain, and
  characteristic-zero hypotheses. Finiteness of the normalization and separability of finite
  fraction-field extensions are derived API from the owner abstractions and mathlib.
-/

section

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [CharZero (FractionRing R)]

-- Proof sketch: the implication `IsN2Ring R → IsN1Ring R` is the owner instance from
-- `Definition 10.161.1`. For the converse, pass to the normalization
-- `S = integralClosure R (FractionRing R)`, which is finite over `R` by the `N-1` hypothesis.
-- The ring `S` is a Noetherian normal domain with fraction field `FractionRing R`, so every
-- finite extension of its fraction field is separable in characteristic zero and
-- Lemma `10.161.8` / `IsIntegralClosure.finite` makes `S` an `N-2` ring. Then descend `N-2`
-- from `S` to `R` via the finite-extension theorem `isN2Ring_of_finite_extension`.
/-- Lemma 10.161.11: A Noetherian domain whose fraction field has characteristic zero is `N-1`
if and only if it is `N-2`, i.e. Japanese. -/
theorem isN1Ring_iff_isN2Ring_of_noetherian_of_fractionRing_charZero
    : IsN1Ring R ↔ IsN2Ring R := by
  constructor
  · intro hN1
    let S := integralClosure R (FractionRing R)
    letI : Module.Finite R S := hN1.integralClosure_finite
    letI : IsFractionRing S (FractionRing R) :=
      integralClosure.isFractionRing_of_finite_extension
        (A := R) (K := FractionRing R) (L := FractionRing R)
    letI : CharZero S := RingHom.charZero (algebraMap S (FractionRing R))
    letI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
    letI : IsIntegrallyClosed S :=
      integralClosure.isIntegrallyClosedOfFiniteExtension
        (R := R) (K := FractionRing R) (L := FractionRing R)
    have hRS : Function.Injective (algebraMap R S) := by
      intro x y hxy
      apply IsFractionRing.injective R (FractionRing R)
      simpa [S] using congrArg (fun z : S => (z : FractionRing R)) hxy
    have hSN2 : IsN2Ring S := by
      -- The normalization has the same fraction field, so characteristic zero forces every finite
      -- extension of that fraction field to be separable.
      refine IsN2Ring.mk ?_
      intro L _ _ _ _ _
      letI : PerfectField (FractionRing S) := PerfectField.ofCharZero
      letI : Algebra.IsSeparable (FractionRing S) L :=
        Algebra.IsAlgebraic.isSeparable_of_perfectField
      letI : Algebra S (integralClosure S L) :=
        SubalgebraClass.toAlgebra (s := integralClosure S L)
      letI : SMul S (integralClosure S L) :=
        (show Algebra S (integralClosure S L) from inferInstance).toSMul
      have hScalarTower : IsScalarTower S (integralClosure S L) L := by
        refine IsScalarTower.of_algebraMap_eq ?_
        intro x
        cases x
        rfl
      letI : IsScalarTower S (integralClosure S L) L := hScalarTower
      -- Lemma 10.161.8 applies to the Noetherian normal domain `S`.
      exact IsIntegralClosure.finite S (FractionRing S) L (integralClosure S L)
    letI : IsN2Ring S := hSN2
    -- Descend the `N-2` property along the finite normalization map `R → S`.
    exact isN2Ring_of_finite_extension (R := R) (S := S) hRS
  · intro hN2
    letI : IsN2Ring R := hN2
    -- The reverse implication is the owner instance `IsN2Ring R → IsN1Ring R`.
    infer_instance

end

/-! ### Lemma_10_161_12 (from Chap10) -/
open IntermediateField

universe u v

section

/-  
Domain triage: this file is in the commutative algebra of Japanese (`N-2`) domains in positive
characteristic, with the source test family restricted to finite purely inseparable fraction-field
extensions.

Owner abstractions sampled for this item:
- `IsN2Ring`, the source-facing owner from `Definition_10_161_1`;
- `IsN2Ring.integralClosure_finite_of_finiteDimensional`, the arbitrary-universe bridge theorem
  for finite normalization in finite fraction-field extensions;
- `isGalois_over_relative_perfectClosure_of_normal`, the local source-faithful decomposition step
  for the relative perfect closure inside a finite normal extension;
- `IsIntegralClosure.finite`, recalled in `Lemma_10_161_8` for the separable normalization step.

This file is `source-facing`: the textbook item is a characteristic-`p` test criterion for the
existing owner `IsN2Ring`, not a new owner. The primitive data are the Noetherian domain `R`, the
positive characteristic prime `p`, and the family of finite purely inseparable extensions of
`FractionRing R`. Finiteness of integral closures is derived API from `IsN2Ring` and the sampled
integral-closure owners, so no extra wrapper predicate should be introduced here.
-/
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable (p : ℕ) [Fact p.Prime] [CharP (FractionRing R) p]

/-- Helper for Lemma 10.161.12: a finite normal extension is Galois over its relative perfect
closure, hence separable over that purely inseparable subextension. -/
theorem isGalois_over_relative_perfectClosure_of_normal
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E] [Normal F E] :
    IsGalois (perfectClosure F E) E := by
  -- Route correction: reuse the Chapter 9 normal/perfect-closure theorem instead of
  -- reproving the fixed-field characterization locally.
  exact isGalois_over_perfectClosure_of_normal_algebraic (F := F) (E := E)

omit [IsDomain R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.161.12: the one-step and iterated integral closures inside `M` agree
after restricting scalars back to the original base ring `R`. -/
lemma iterated_integralClosure_eq_restrictScalars
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    {M_insep : Type v} [Field M_insep] [Algebra K M_insep] [Algebra R M_insep]
    [IsScalarTower R K M_insep]
    {M : Type v} [Field M] [Algebra K M] [Algebra R M] [IsScalarTower R K M]
    [Algebra M_insep M] [IsScalarTower K M_insep M] [IsScalarTower R M_insep M] :
    integralClosure R M =
      (integralClosure (integralClosure R M_insep) M).restrictScalars R := by
  -- Route correction: compare the two subalgebras by the integrality predicates they encode,
  -- instead of transporting through `IsIntegralClosure.trans` on the carrier aliases.
  ext x
  rw [Subalgebra.mem_restrictScalars]
  constructor
  · intro hx
    -- Integrality over `R` ascends to integrality over the intermediate integral closure.
    exact IsIntegral.tower_top (A := integralClosure R M_insep) hx
  · intro hx
    -- Integrality over the intermediate integral closure descends back to integrality over `R`.
    exact isIntegral_trans (R := R) (A := integralClosure R M_insep) (x := x) hx

/-- Helper for Lemma 10.161.12: finiteness of the integral closure descends along an embedding
into a larger normal overfield without changing the base ring. -/
lemma finite_integralClosure_of_normal_overfield
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    {L : Type v} [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    {M : Type v} [Field M] [Algebra R M] [Algebra K M] [IsScalarTower R K M]
    (f : L →ₐ[K] M) (hfin : Module.Finite R (integralClosure R M)) :
    Module.Finite R (integralClosure R L) := by
  let fR : L →ₐ[R] M := AlgHom.restrictScalars R f
  exact finite_of_integralClosure_map_to_larger_base (R := R) (S := R) fR fR.injective hfin

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Helper for Lemma 10.161.12: for a finite normal extension, finiteness of the normalization
over the purely inseparable perfect closure and the separable upper step implies finiteness over
the original base ring `R`. -/
lemma finite_integralClosure_of_finite_normal_extension
    (hpure :
      ∀ (L : Type u) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
        [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L]
        [IsPurelyInseparable (FractionRing R) L],
        Module.Finite R (integralClosure R L))
    {M : Type u} [Field M] [Algebra R M] [Algebra (FractionRing R) M]
    [IsScalarTower R (FractionRing R) M] [FiniteDimensional (FractionRing R) M]
    [Normal (FractionRing R) M] :
    Module.Finite R (integralClosure R M) := by
  let P₀ : IntermediateField (FractionRing R) M := perfectClosure (FractionRing R) M
  letI : Algebra (FractionRing R) ↥P₀ := P₀.algebra'
  letI : Algebra R ↥P₀ :=
    (RingHom.comp (algebraMap (FractionRing R) ↥P₀) (algebraMap R (FractionRing R))).toAlgebra
  letI : Algebra ↥P₀ M := P₀.toAlgebra
  letI : IsScalarTower R (FractionRing R) ↥P₀ := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (FractionRing R) ↥P₀ M := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    rfl
  letI : IsScalarTower R ↥P₀ M := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    rw [IsScalarTower.algebraMap_eq R (FractionRing R) M]
    rfl
  letI : FiniteDimensional (FractionRing R) ↥P₀ :=
    IntermediateField.finiteDimensional_left (K := FractionRing R) (F := P₀) (L := M)
  letI : FiniteDimensional ↥P₀ M :=
    IntermediateField.finiteDimensional_right (K := FractionRing R) (F := P₀) (L := M)
  letI : IsPurelyInseparable (FractionRing R) ↥P₀ := by
    simpa [P₀] using
      (perfectClosure.isPurelyInseparable (F := FractionRing R) (E := M))
  have hfinLower : Module.Finite R (integralClosure R ↥P₀) :=
    hpure ↥P₀
  letI : IsGalois ↥P₀ M := by
    simpa [P₀] using
      (isGalois_over_relative_perfectClosure_of_normal (F := FractionRing R) (E := M))
  let S := integralClosure R ↥P₀
  letI : Module.Finite R S := hfinLower
  letI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  letI : Algebra S ↥P₀ := Subalgebra.toAlgebra S
  letI : SMul S ↥P₀ :=
    (show Algebra S ↥P₀ from inferInstance).toSMul
  letI : Algebra S M :=
    (RingHom.comp (algebraMap ↥P₀ M) (algebraMap S ↥P₀)).toAlgebra
  letI : SMul S M :=
    (show Algebra S M from inferInstance).toSMul
  letI : Module S M := RingHom.toModule (algebraMap S M)
  letI : IsScalarTower S ↥P₀ M :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : IsScalarTower R S M := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    rw [IsScalarTower.algebraMap_eq R (FractionRing R) M]
    rfl
  letI : IsFractionRing S ↥P₀ :=
    integralClosure.isFractionRing_of_finite_extension
      (A := R) (K := FractionRing R) (L := ↥P₀)
  letI : IsIntegrallyClosed S :=
    integralClosure.isIntegrallyClosedOfFiniteExtension
      (R := R) (K := FractionRing R) (L := ↥P₀)
  letI : Algebra.IsSeparable ↥P₀ M := inferInstance
  letI : Algebra S (integralClosure S M) := SubalgebraClass.toAlgebra (s := integralClosure S M)
  letI : SMul S (integralClosure S M) :=
    (show Algebra S (integralClosure S M) from inferInstance).toSMul
  letI : Module S (integralClosure S M) :=
    RingHom.toModule (algebraMap S (integralClosure S M))
  letI : IsScalarTower S (integralClosure S M) M := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    cases x
    rfl
  letI : Algebra R (integralClosure S M) :=
    (RingHom.comp (algebraMap S (integralClosure S M)) (algebraMap R S)).toAlgebra
  letI : Module R (integralClosure S M) :=
    RingHom.toModule (algebraMap R (integralClosure S M))
  letI : IsScalarTower R S (integralClosure S M) := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Finite S (integralClosure S M) :=
    IsIntegralClosure.finite
      (A := S) (K := ↥P₀) (L := M) (C := integralClosure S M)
  have hfinRestrict : Module.Finite R ((integralClosure S M).restrictScalars R) := by
    let C' := (integralClosure S M).restrictScalars R
    let f : S →+* C' :=
      { toFun := fun s => ⟨algebraMap S M s, isIntegral_algebraMap⟩
        map_one' := by
          ext
          simp
        map_mul' := by
          intro x y
          ext
          simp
        map_zero' := by
          ext
          simp
        map_add' := by
          intro x y
          ext
          simp }
    letI : Algebra S C' := f.toAlgebra
    letI : Module S C' := RingHom.toModule f
    letI : Module.Finite S C' := by
      simpa [C'] using (inferInstance : Module.Finite S (integralClosure S M))
    letI : IsScalarTower R S C' := by
      refine IsScalarTower.of_algebraMap_eq ?_
      intro x
      ext
      change (algebraMap R M) x = (algebraMap S M) ((algebraMap R S) x)
      simpa using congrArg (fun g : R →+* M => g x) (IsScalarTower.algebraMap_eq R S M)
    exact Module.Finite.trans (R := R) (A := S) (M := C')
  rw [iterated_integralClosure_eq_restrictScalars
    (R := R) (K := FractionRing R) (M_insep := ↥P₀) (M := M)]
  exact hfinRestrict

set_option synthInstance.maxHeartbeats 100000 in
/-- Helper for Lemma 10.161.12: finiteness for arbitrary finite extensions follows by passing to
their normal closures and descending back. -/
lemma finite_integralClosure_of_finite_extension_via_normal_closure
    (hpure :
      ∀ (L : Type u) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
        [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L]
        [IsPurelyInseparable (FractionRing R) L],
        Module.Finite R (integralClosure R L))
    {L : Type u} [Field L] [Algebra R L] [Algebra (FractionRing R) L]
    [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L] :
    Module.Finite R (integralClosure R L) := by
  let Ω := AlgebraicClosure (FractionRing R)
  letI : Algebra R Ω :=
    (RingHom.comp (algebraMap (FractionRing R) Ω) (algebraMap R (FractionRing R))).toAlgebra
  let iotaΩ : L →ₐ[FractionRing R] Ω :=
    IsAlgClosed.lift (R := FractionRing R) (S := L) (M := Ω)
  letI : Algebra L Ω := iotaΩ.toAlgebra
  letI : IsScalarTower (FractionRing R) L Ω := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    exact (iotaΩ.commutes x).symm
  let M₀ : IntermediateField (FractionRing R) Ω := normalClosure (FractionRing R) L Ω
  letI : Algebra (FractionRing R) ↥M₀ := M₀.algebra'
  letI : Algebra R ↥M₀ :=
    (RingHom.comp (algebraMap (FractionRing R) ↥M₀) (algebraMap R (FractionRing R))).toAlgebra
  letI : IsScalarTower R (FractionRing R) ↥M₀ := IsScalarTower.of_algebraMap_eq' rfl
  letI : Normal (FractionRing R) ↥M₀ := by
    simpa [M₀] using normalClosure.normal (F := FractionRing R) (K := L) (L := Ω)
  letI : FiniteDimensional (FractionRing R) ↥M₀ := by
    simpa [M₀] using normalClosure.is_finiteDimensional (F := FractionRing R) (K := L) (L := Ω)
  let iota : L →ₐ[FractionRing R] ↥M₀ :=
    (normalClosure.algHomEquiv (FractionRing R) L Ω).symm iotaΩ
  have hfinM : Module.Finite R (integralClosure R ↥M₀) :=
    finite_integralClosure_of_finite_normal_extension (R := R) hpure (M := ↥M₀)
  exact finite_integralClosure_of_normal_overfield
    (R := R) (K := FractionRing R) iota hfinM

-- Proof sketch: the forward implication is immediate by restricting the `N-2` finiteness
-- condition to finite purely inseparable extensions. For the converse, given a finite extension
-- `L / FractionRing R`, choose a finite normal closure `M`, decompose `M` into the purely
-- inseparable relative perfect closure and the separable upper step, and then descend the finite
-- normalization of `M` back to `L`.
/-- Lemma 10.161.12: for a Noetherian domain whose fraction field has characteristic `p > 0`, the
`N-2` condition is equivalent to requiring finite integral closure only for finite purely
inseparable extensions of the fraction field. -/
theorem isN2Ring_iff_integralClosure_finite_for_finite_purelyInseparable_extensions
    :
    IsN2Ring R ↔
      ∀ (L : Type u) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
        [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L]
        [IsPurelyInseparable (FractionRing R) L],
        Module.Finite R (integralClosure R L) := by
  constructor
  · intro hR L _ _ _ _ _ _
    letI : IsN2Ring R := hR
    exact IsN2Ring.integralClosure_finite_of_finiteDimensional L
  · intro hpure
    -- The converse is now the packaged source proof: use the normal-closure descent lemma as the
    -- small-universe `N-2` field required by `IsN2Ring.mk`.
    refine IsN2Ring.mk ?_
    intro L _ _ _ _ _
    exact finite_integralClosure_of_finite_extension_via_normal_closure (R := R) hpure (L := L)

end
