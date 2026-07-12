import Mathlib
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_3
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_3
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_4
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1.FiniteRepScalarExtension
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_8_ProjectiveTriangleSupport
import LinearRepresentations_Serre_1977.Chap16.Lemma_16_16_3_1
import LinearRepresentations_Serre_1977.Chap16.Lemma_16_16_3_1.PositiveConeBridge
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_2.CommonOwner
import LinearRepresentations_Serre_1977.Chap16.Exercise_16_16_3_8.ReductionProjectiveClassBridge
import LinearRepresentations_Serre_1977.Chap16.Exercise_16_16_3_8.ProjectivePositiveReflection
import LinearRepresentations_Serre_1977.Chap16.Exercise_16_16_3_8.PositiveGeneration

noncomputable section

universe u v

open CategoryTheory
open scoped Representation ZeroObject

namespace Representation

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A
local notation "e" =>
  (projectiveGrothendieckBaseChangeHom K :
    finiteProjectiveGroupAlgebraGrothendieckGroup A G →+
      finiteRepGrothendieckGroup K G)

/-- Helper for Exercise 16-16.3-8: a dual family of nonnegative target coordinates makes a
positive multiple of a reduced projective class positive in the source basis. -/
theorem positiveConeOfDualCoordinatesOnReduction
    {ι : Type u} {κ : Type*}
    {PA Pk RK : Type*}
    [AddCommGroup PA] [AddCommGroup Pk] [AddCommGroup RK]
    (bP : Module.Basis ι ℤ Pk)
    (bK : Module.Basis κ ℤ RK)
    (red : PA →ₗ[ℤ] Pk)
    (f : PA →ₗ[ℤ] RK)
    {n : ℕ}
    (z : ι → RK)
    (hdual :
      ∀ i y,
        bP.repr (n • red y) i =
          (bK.repr (f y)).sum fun j a ↦ a * bK.repr (z i) j)
    {y : PA}
    (hy : f y ∈ bK.positiveCone)
    (hz : ∀ i, z i ∈ bK.positiveCone) :
    n • red y ∈ bP.positiveCone := by
  -- Each source coordinate is a finite dot product of two coordinatewise nonnegative families.
  intro i
  rw [hdual i y]
  exact Finsupp.sum_nonneg fun j _ ↦ mul_nonneg (hy j) ((hz i) j)

/-- Helper for Exercise 16-16.3-8: a residue-degree-scaled dual family of nonnegative target
coordinates makes the same positive multiple of a reduced projective class positive. -/
theorem positiveConeOfScaledDualCoordinatesOnReduction
    {ι : Type u} {κ : Type*}
    {PA Pk RK : Type*}
    [AddCommGroup PA] [AddCommGroup Pk] [AddCommGroup RK]
    (bP : Module.Basis ι ℤ Pk)
    (bK : Module.Basis κ ℤ RK)
    (red : PA →ₗ[ℤ] Pk)
    (f : PA →ₗ[ℤ] RK)
    {n : ℕ}
    (z : ι → RK)
    (hdual :
      ∀ i y,
        bP.repr (n • red y) i =
          (n : ℤ) *
            ((bK.repr (f y)).sum fun j a ↦ a * bK.repr (z i) j))
    {y : PA}
    (hy : f y ∈ bK.positiveCone)
    (hz : ∀ i, z i ∈ bK.positiveCone) :
    n • red y ∈ bP.positiveCone := by
  -- Each coordinate is the nonnegative residue degree times a nonnegative finite dot product.
  intro i
  rw [hdual i y]
  exact
    mul_nonneg (Int.natCast_nonneg n) <|
      Finsupp.sum_nonneg fun j _ ↦ mul_nonneg (hy j) ((hz i) j)

/-- Helper for Exercise 16-16.3-8: if decomposition coordinates compute the reduced projective
coordinates and a positive column realizes each decomposition-coordinate functional on the target
basis, then the required dual-coordinate identity holds on the unreduced source. -/
theorem dualCoordinateIdentityOnReduction_of_decompositionCoordinates
    {ι : Type u} {κ : Type*}
    {PA Pk RK Rk' : Type*}
    [AddCommGroup PA] [AddCommGroup Pk] [AddCommGroup RK] [AddCommGroup Rk']
    (bP : Module.Basis ι ℤ Pk)
    (bK : Module.Basis κ ℤ RK)
    (red : PA →ₗ[ℤ] Pk)
    (f : PA →ₗ[ℤ] RK)
    (d : RK →ₗ[ℤ] Rk')
    (ψ : ι → Rk' →ₗ[ℤ] ℤ)
    {n : ℕ}
    (z : ι → RK)
    (hcoord : ∀ i y, bP.repr (n • red y) i = ψ i (d (f y)))
    (hcolumn : ∀ i j, ψ i (d (bK j)) = bK.repr (z i) j) :
    ∀ i y,
      bP.repr (n • red y) i =
        (bK.repr (f y)).sum fun j a ↦ a * bK.repr (z i) j := by
  intro i y
  -- Turn the column data into an equality of linear functionals on the target Grothendieck group.
  have hfunctional :
      (bK.constr ℤ fun j ↦ ψ i (d (bK j))) = (ψ i).comp d := by
    apply bK.ext
    intro j
    simp [Module.Basis.constr_basis]
  -- Expand `f y` in the target basis and rewrite the coefficients by the positive column.
  calc
    bP.repr (n • red y) i = ψ i (d (f y)) := hcoord i y
    _ = (bK.constr ℤ (fun j ↦ ψ i (d (bK j)))) (f y) := by
          simpa using congrArg (fun g : RK →ₗ[ℤ] ℤ ↦ g (f y)) hfunctional.symm
    _ = (bK.repr (f y)).sum (fun j a ↦ a * ψ i (d (bK j))) := by
          simp [Module.Basis.constr_apply]
    _ = (bK.repr (f y)).sum (fun j a ↦ a * bK.repr (z i) j) := by
          apply Finsupp.sum_congr
          intro j _hj
          rw [hcolumn i j]

/-- Helper for Exercise 16-16.3-8: decomposition-coordinate control plus positive columns gives
positivity of the reduced positive multiple. -/
theorem positiveConeOnReduction_of_decompositionCoordinates
    {ι : Type u} {κ : Type*}
    {PA Pk RK Rk' : Type*}
    [AddCommGroup PA] [AddCommGroup Pk] [AddCommGroup RK] [AddCommGroup Rk']
    (bP : Module.Basis ι ℤ Pk)
    (bK : Module.Basis κ ℤ RK)
    (red : PA →ₗ[ℤ] Pk)
    (f : PA →ₗ[ℤ] RK)
    (d : RK →ₗ[ℤ] Rk')
    (ψ : ι → Rk' →ₗ[ℤ] ℤ)
    {n : ℕ}
    (z : ι → RK)
    (hcoord : ∀ i y, bP.repr (n • red y) i = ψ i (d (f y)))
    (hcolumn : ∀ i j, ψ i (d (bK j)) = bK.repr (z i) j)
    {y : PA}
    (hy : f y ∈ bK.positiveCone)
    (hz : ∀ i, z i ∈ bK.positiveCone) :
    n • red y ∈ bP.positiveCone := by
  -- The coordinate identity reduces the goal to finite dot products of nonnegative coordinates.
  exact
    positiveConeOfDualCoordinatesOnReduction bP bK red f z
      (dualCoordinateIdentityOnReduction_of_decompositionCoordinates
        bP bK red f d ψ z hcoord hcolumn)
      hy hz

end

end Representation
