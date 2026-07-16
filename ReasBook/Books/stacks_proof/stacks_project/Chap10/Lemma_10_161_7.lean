import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_161_1

-- Declarations for this item will be appended below by the statement pipeline.

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
@[stacks 032K]
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
@[stacks 032K]
theorem isN2Ring_of_finite_extension
    (hRS : Function.Injective (algebraMap R S)) [IsN2Ring S] :
    IsN2Ring R := by
  refine IsN2Ring.mk ?_
  intro L _ _ _ _ _
  exact integralClosure_finite_of_finite_extension (R := R) (S := S) hRS

end
