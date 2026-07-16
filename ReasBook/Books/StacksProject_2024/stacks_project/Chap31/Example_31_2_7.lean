import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap10.Definition_10_32_1
import StacksProject_2024.stacks_project.Chap10.Remark_10_63_12
import StacksProject_2024.stacks_project.Chap17.ModuleRestrictionAndStalks
import StacksProject_2024.stacks_project.Chap15.Example_15_15_5
import StacksProject_2024.stacks_project.Chap31.Definition_31_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open AlgebraicGeometry
open IsLocalRing
open scoped AlgebraicGeometry

section

variable (k : Type u) [Field k]

local notation "S∞" => infiniteSquareZeroPolynomialQuotient k
local notation "X∞" => Scheme.Spec.obj (Opposite.op <| CommRingCat.of S∞)

noncomputable local instance : Module S∞ S∞ :=
  Semiring.toModule

/-- Example 31.2.7 (1): for a field `k`, the ring
`k[x_1, x_2, x_3, \ldots]/(x_i^2)` is local. -/
@[stacks 05AI]
theorem infiniteSquareZeroPolynomialQuotient_isLocal :
    IsLocalRing S∞ := inferInstance

/-- Example 31.2.7 (2): for a field `k`, the maximal ideal of
`k[x_1, x_2, x_3, \ldots]/(x_i^2)` is locally nilpotent. -/
@[stacks 05AI]
theorem infiniteSquareZeroPolynomialQuotient_maximalIdeal_isLocallyNilpotent :
    (maximalIdeal S∞).IsLocallyNilpotent := by
  rw [maximalIdeal_eq_span_squareZeroVariables k]
  rw [Ideal.IsLocallyNilpotent, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact mem_nilradical.2 ⟨2, by simpa using squareZeroVariable_sq_eq_zero k i⟩

/-- Example 31.2.7 (3): for a field `k`, no element of
`k[x_1, x_2, x_3, \ldots]/(x_i^2)` has annihilator equal to its maximal ideal. -/
@[stacks 05AI]
theorem infiniteSquareZeroPolynomialQuotient_no_element_with_annihilator_maximalIdeal :
    ¬ ∃ x : S∞, Ideal.torsionOf S∞ S∞ x = maximalIdeal S∞ := by
  intro hx
  rcases hx with ⟨x, hx⟩
  have hmax : maximalIdeal S∞ ∈ associatedPrimesOfModule S∞ S∞ := by
    rw [mem_associatedPrimesOfModule_iff]
    exact ⟨(maximalIdeal.isMaximal S∞).isPrime, x, hx.symm⟩
  have hempty : maximalIdeal S∞ ∉ associatedPrimesOfModule S∞ S∞ := by
    simpa [infiniteSquareZeroPolynomialQuotient_associatedPrimesOfModule_self_eq_empty]
  exact hempty hmax

/- Example 31.2.7 (4): for a field `k`, the textbook associated primes of
`k[x_1, x_2, x_3, \ldots]/(x_i^2)` as a module over itself are empty. This is exactly the
canonical Chapter 10 theorem
`infiniteSquareZeroPolynomialQuotient_associatedPrimesOfModule_self_eq_empty`. -/
recall infiniteSquareZeroPolynomialQuotient_associatedPrimesOfModule_self_eq_empty

private theorem infiniteSquareZeroPolynomialQuotient_prime_eq_closedPoint (x : X∞) :
    x = IsLocalRing.closedPoint S∞ := by
  apply PrimeSpectrum.ext
  calc
    x.asIdeal = maximalIdeal S∞ := by
      apply le_antisymm
      · letI : x.asIdeal.IsPrime := x.isPrime
        exact IsLocalRing.le_maximalIdeal_of_isPrime x.asIdeal
      · rw [maximalIdeal_eq_span_squareZeroVariables k, Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        exact x.isPrime.mem_of_pow_mem 2 <|
          by simpa [squareZeroVariable_sq_eq_zero k i] using x.asIdeal.zero_mem
    _ = (IsLocalRing.closedPoint S∞).asIdeal := by
      simpa [IsLocalRing.closedPoint] using
        (IsLocalRing.PrimeSpectrum.asIdeal_top S∞).symm

/-- Example 31.2.7 (5): for a field `k`, the affine scheme
`Spec(k[x_1, x_2, x_3, \ldots]/(x_i^2))` has no associated points. -/
@[stacks 05AI]
theorem infiniteSquareZeroPolynomialQuotient_spec_associatedPoints_eq_empty :
    X∞.associatedPoints = ∅ := by
  ext x
  constructor
  · intro hx
    rw [infiniteSquareZeroPolynomialQuotient_prime_eq_closedPoint k x] at hx ⊢
    rw [Scheme.mem_associatedPoints_iff] at hx
    rw [mem_associatedPrimesOfModule_iff] at hx
    rcases hx with ⟨_, m, hm⟩
    let x0 : X∞ := IsLocalRing.closedPoint S∞
    let A := X∞.presheaf.stalk x0
    let M :=
      RingedSpace.stalkModuleCat
        (SheafOfModules.unit X∞.ringCatSheaf)
        x0
    let eR : A ≃+* S∞ :=
      (stalkClosedPointIso (CommRingCat.of S∞)).commRingCatIsoToRingEquiv
    let eM : M ≃ₗ[A] A :=
      RingedSpace.unitStalkLinearEquiv x0
    have hmA : Ideal.IsAssociatedToModule A A (maximalIdeal A) := by
      exact eM.isAssociatedToModule_iff.mp
        ⟨(maximalIdeal.isMaximal A).isPrime, m, hm⟩
    rcases hmA with ⟨_, a, ha⟩
    let s : S∞ := eR a
    have hmap_maximal :
        Ideal.map eR (maximalIdeal A) = maximalIdeal S∞ := by
      have hmax : (Ideal.map eR (maximalIdeal A)).IsMaximal := by infer_instance
      exact (IsLocalRing.isMaximal_iff S∞).1 hmax
    have hs_torsion :
        Ideal.torsionOf S∞ S∞ s = Ideal.map eR (Ideal.torsionOf A A a) := by
      have hcomap :
          Ideal.comap eR (Ideal.torsionOf S∞ S∞ s) = Ideal.torsionOf A A a := by
        ext y
        rw [Ideal.mem_comap, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
        change eR y * eR a = 0 ↔ y * a = 0
        constructor
        · intro h
          apply eR.injective
          simpa [map_mul] using h
        · intro h
          simpa [map_mul] using congrArg eR h
      calc
        Ideal.torsionOf S∞ S∞ s = Ideal.map eR (Ideal.comap eR (Ideal.torsionOf S∞ S∞ s)) := by
          symm
          exact Ideal.map_comap_of_surjective eR.toRingHom eR.surjective _
        _ = Ideal.map eR (Ideal.torsionOf A A a) := by rw [hcomap]
    have hs :
        ∃ t : S∞, Ideal.torsionOf S∞ S∞ t = maximalIdeal S∞ := by
      refine ⟨s, ?_⟩
      calc
        Ideal.torsionOf S∞ S∞ s = Ideal.map eR (Ideal.torsionOf A A a) := hs_torsion
        _ = Ideal.map eR (maximalIdeal A) := by rw [← ha]
        _ = maximalIdeal S∞ := hmap_maximal
    simpa using
      infiniteSquareZeroPolynomialQuotient_no_element_with_annihilator_maximalIdeal
        k hs
  · intro hx
    exact hx.elim

end
