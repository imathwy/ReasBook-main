import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCartanForwardScaledProducer
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerPointMassProjectiveRestrictionProducer
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.IntegerDivisibilityDescent

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanCoordinateDivisibilityProducer

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveCartanCoordinateDivisibilityProducerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCartanCoordinateDivisibilityProducerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Integer descent for fixed Cartan-coordinate rows: if the cast of an integer-valued regular
class function lies in Serre's regular-value divisibility lattice, then its integer coordinates
are divisible by the corresponding centralizer `p`-parts. -/
theorem regularIntegerFunction_coordinate_divisible_of_cast_mem_regularValueDivisibility
    {f : PRegularConjClass G p → ℤ}
    (hf :
      regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    ∀ d : PRegularConjClass G p,
      ∃ a : ℤ,
        f d = (ConjClasses.centralizerPPart p d.1 : ℤ) * a := by
  intro d
  rcases
      centralizerPPart_dvd_of_regularIntegerFunctionCast_mem_regularValueDivisibilitySubmodule
        (p := p) (A := A) (K := K) (G := G) hf d with
    ⟨a, ha⟩
  exact ⟨a, ha⟩

omit [HenselianLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [CharZero K]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Coordinatewise Cartan divisibility is reduced to regular classes with nontrivial
centralizer `p`-part.  The `centralizerPPart = 1` coordinates are automatic. -/
theorem cartanCoordinateAddHom_coordinate_divisible_of_nontrivial_centralizerPPart
    (hdiv :
      ∀ x : P₀[IsLocalRing.ResidueField A](G), ∀ c : PRegularConjClass G p,
        ConjClasses.centralizerPPart p c.1 ≠ 1 →
          ∃ a : ℤ,
            cartanCoordinateAddHom
                (p := p) (k := IsLocalRing.ResidueField A) (G := G) x c =
              (ConjClasses.centralizerPPart p c.1 : ℤ) * a) :
    ∀ x : P₀[IsLocalRing.ResidueField A](G), ∀ c : PRegularConjClass G p,
      ∃ a : ℤ,
        cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) x c =
          (ConjClasses.centralizerPPart p c.1 : ℤ) * a := by
  intro x c
  by_cases hc : ConjClasses.centralizerPPart p c.1 = 1
  · refine
      ⟨cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) x c, ?_⟩
    simp [hc]
  · exact hdiv x c hc

/-- The existing projective-envelope regular-restriction divisibility theorem gives membership
of each projective-envelope row in Serre's regular-value divisibility lattice.  This is the
field-valued value-side input; it does not by itself say that the Brauer-basis readback
coordinates are divisible. -/
theorem coordinate_normalized_projective_envelope_regularRestriction_mem_regularValueDivisibility
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π c).ρ,
        f.IsProjectiveEnvelope) :
    ∀ c : PRegularConjClass G p,
      regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  intro c
  refine
    (mem_regularValueDivisibilitySubmodule_iff
      (p := p) (A := A) (K := K) (G := G) _).2 ?_
  intro d
  exact
    coordinate_normalized_projective_envelope_regularRestriction_coordinateDivisibility
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope c d

/-- Local readback-preservation statement for the projective-envelope rows: after applying the
Brauer-basis readback map to each value-divisible projective-envelope regular restriction, the
result is still in Serre's regular-value divisibility lattice.

This is the exact non-formal bridge between the already proved value-side divisibility and the
integer Cartan-coordinate divisibility target. -/
def coordinate_normalized_projective_envelope_readbackPreserves_regularValueDivisibility
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G) : Prop :=
  ∀ c : PRegularConjClass G p,
    projectiveCartanASpanBrauerRepr
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
        (regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀)) ∈
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)

/-- The global forward-stability form of the Brauer readback map implies the local
projective-envelope readback-preservation statement.  This adapter is non-circular: it uses only
the value-side projective-envelope divisibility plus the stated forward stability hypothesis. -/
theorem
    coordinate_normalized_projective_envelope_readbackPreserves_regularValueDivisibility_of_forward_le
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π c).ρ,
        f.IsProjectiveEnvelope)
    (hforward :
      Submodule.map
          (projectiveCartanASpanBrauerRepr
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
          (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) ≤
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    coordinate_normalized_projective_envelope_readbackPreserves_regularValueDivisibility
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P := by
  intro c
  have hrow :=
    coordinate_normalized_projective_envelope_regularRestriction_mem_regularValueDivisibility
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord P hP_envelope c
  exact hforward ⟨_, hrow, rfl⟩

/-- The precise local bridge requested by the B-side reduction, with the non-formal
readback-preservation input made explicit. -/
theorem
    coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_of_readbackPreserves
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hreadback :
      coordinate_normalized_projective_envelope_readbackPreserves_regularValueDivisibility
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord P) :
    ∀ c : PRegularConjClass G p,
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [P c]ₚ₀) ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  intro c
  have hrepr :=
    projectiveCartanASpanBrauerRepr_regularRestriction_projectiveCharacter
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord [P c]ₚ₀
  simpa [regularIntegerFunctionCast_cartanCoordinateAddHom
      (p := p) (A := A) (K := K) (G := G), hrepr] using hreadback c

/-- Local congruence form of the projective-envelope Cartan-coordinate readback problem.

The already proved projective-envelope regular-restriction divisibility puts the first row in
Serre's lattice.  Thus the cast Cartan-coordinate row is in the same lattice exactly when the two
rows are congruent modulo that lattice. -/
def coordinate_normalized_projective_envelope_cartanCoordinateRegularValueCongruence
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G) : Prop :=
  ∀ c : PRegularConjClass G p,
    regularRestriction (p := p) (A := A) (K := K) (G := G)
        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) -
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) [P c]ₚ₀) ∈
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)

/-- For projective-envelope rows, the cast Cartan-coordinate regular-value membership is
equivalent to the local congruence between the regular restriction and its Cartan-coordinate
readback. -/
theorem
    coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_iff_regularValueCongruence
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π c).ρ,
        f.IsProjectiveEnvelope) :
    (∀ c : PRegularConjClass G p,
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [P c]ₚ₀) ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) ↔
      coordinate_normalized_projective_envelope_cartanCoordinateRegularValueCongruence
        (p := p) (A := A) (K := K) (G := G) P := by
  constructor
  · intro hcast c
    let D : Submodule A (PRegularConjClass G p → K) :=
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
    have hrowD :
        regularRestriction (p := p) (A := A) (K := K) (G := G)
            (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) ∈
          D :=
      coordinate_normalized_projective_envelope_regularRestriction_mem_regularValueDivisibility
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope c
    have hcastD :
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) [P c]ₚ₀) ∈ D := by
      simpa [D] using hcast c
    simpa [coordinate_normalized_projective_envelope_cartanCoordinateRegularValueCongruence, D]
      using D.sub_mem hrowD hcastD
  · intro hcong c
    let D : Submodule A (PRegularConjClass G p → K) :=
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
    let row : PRegularConjClass G p → K :=
      regularRestriction (p := p) (A := A) (K := K) (G := G)
        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀)
    let coord : PRegularConjClass G p → K :=
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
        (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) [P c]ₚ₀)
    have hrowD : row ∈ D :=
      coordinate_normalized_projective_envelope_regularRestriction_mem_regularValueDivisibility
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope c
    have hcongD : row - coord ∈ D := by
      simpa [coordinate_normalized_projective_envelope_cartanCoordinateRegularValueCongruence,
        row, coord, D] using hcong c
    have hcoordD : row - (row - coord) ∈ D := D.sub_mem hrowD hcongD
    have hcoord_eq : row - (row - coord) = coord := by
      ext d
      simp only [Pi.sub_apply]
      ring
    simpa [row, coord, D, hcoord_eq] using hcoordD

theorem
    coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_of_regularValueCongruence
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π c).ρ,
        f.IsProjectiveEnvelope)
    (hcong :
      coordinate_normalized_projective_envelope_cartanCoordinateRegularValueCongruence
        (p := p) (A := A) (K := K) (G := G) P) :
    ∀ c : PRegularConjClass G p,
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [P c]ₚ₀) ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
  (coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_iff_regularValueCongruence
    (p := p) (A := A) (K := K) (G := G)
    π hπ_simple hπ_coord P hP_envelope).2 hcong

omit [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Basis-vector Cartan-coordinate divisibility follows from the exact missing readback
membership: the cast of the integer Cartan-coordinate row lies in Serre's regular-value
divisibility lattice. -/
theorem coordinate_normalized_projective_envelope_cartanCoordinate_divisibility_of_cast_mem
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hcast :
      ∀ c : PRegularConjClass G p,
        regularIntegerFunctionCast (p := p) (K := K) (G := G)
            (cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) [P c]ₚ₀) ∈
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    ∀ c d : PRegularConjClass G p,
      ∃ a : ℤ,
        cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [P c]ₚ₀ d =
          (ConjClasses.centralizerPPart p d.1 : ℤ) * a := by
  intro c d
  exact
    regularIntegerFunction_coordinate_divisible_of_cast_mem_regularValueDivisibility
      (p := p) (A := A) (K := K) (G := G) (hcast c) d

/-- Integer-coordinate form of the local congruence reduction. -/
theorem coordinate_normalized_projective_envelope_cartanCoordinate_divisibility_of_regularValueCongruence
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π c).ρ,
        f.IsProjectiveEnvelope)
    (hcong :
      coordinate_normalized_projective_envelope_cartanCoordinateRegularValueCongruence
        (p := p) (A := A) (K := K) (G := G) P) :
    ∀ c d : PRegularConjClass G p,
      ∃ a : ℤ,
        cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [P c]ₚ₀ d =
          (ConjClasses.centralizerPPart p d.1 : ℤ) * a := by
  exact
    coordinate_normalized_projective_envelope_cartanCoordinate_divisibility_of_cast_mem
      (p := p) (A := A) (K := K) (G := G) P
      (coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_of_regularValueCongruence
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope hcong)

omit [HenselianLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A] in
/-- Extension from coordinate-normalized projective-envelope basis vectors to all projective
Grothendieck classes.  This is the formal `bP.sum_repr` plus `map_sum`/`map_zsmul` layer. -/
theorem cartanCoordinateAddHom_coordinate_divisible_of_projectiveEnvelope_basis_vectors
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : PRegularConjClass G p →
      FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π c).ρ,
        f.IsProjectiveEnvelope)
    (hbasis_div :
      ∀ c d : PRegularConjClass G p,
        ∃ a : ℤ,
          cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) [P c]ₚ₀ d =
            (ConjClasses.centralizerPPart p d.1 : ℤ) * a) :
    ∀ x : P₀[IsLocalRing.ResidueField A](G), ∀ d : PRegularConjClass G p,
      ∃ a : ℤ,
        cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) x d =
          (ConjClasses.centralizerPPart p d.1 : ℤ) * a := by
  classical
  let bP :=
    projectiveEnvelope_classes_basis_of_complete_family
      π hπ_pairwise hπ_complete P hP_envelope
  let F := cartanCoordinateAddHom (p := p) (k := IsLocalRing.ResidueField A) (G := G)
  intro x d
  let z : ℤ := ConjClasses.centralizerPPart p d.1
  choose a ha using hbasis_div
  refine ⟨∑ c, (bP.repr x c) * a c d, ?_⟩
  have hFx :
      F x = ∑ c, (bP.repr x c) • F (bP c) := by
    symm
    calc
      ∑ c, (bP.repr x c) • F (bP c) =
          ∑ c, F ((bP.repr x c) • bP c) := by
            refine Finset.sum_congr rfl ?_
            intro c hc
            rw [map_zsmul]
      _ = F (∑ c, (bP.repr x c) • bP c) := by
            rw [map_sum]
      _ = F x := by
            rw [bP.sum_repr x]
  calc
    cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) x d
        = (∑ c, (bP.repr x c) • F (bP c)) d := by
            exact congrFun hFx d
    _ = ∑ c, (bP.repr x c) * F (bP c) d := by
            simp [zsmul_eq_mul]
    _ = ∑ c, (bP.repr x c) * (z * a c d) := by
            refine Finset.sum_congr rfl ?_
            intro c hc
            have hcdiv :
                F (bP c) d = z * a c d := by
              simpa [F, bP, z, projectiveEnvelope_classes_basis_of_complete_family_apply]
                using ha c d
            rw [hcdiv]
    _ = z * ∑ c, (bP.repr x c) * a c d := by
            calc
              ∑ c, (bP.repr x c) * (z * a c d) =
                  ∑ c, z * ((bP.repr x c) * a c d) := by
                    refine Finset.sum_congr rfl ?_
                    intro c hc
                    ring
              _ = z * ∑ c, (bP.repr x c) * a c d := by
                    rw [Finset.mul_sum]
    _ =
        (ConjClasses.centralizerPPart p d.1 : ℤ) *
          ∑ c, (bP.repr x c) * a c d := rfl

end ProjectiveCartanCoordinateDivisibilityProducer

section FullMixedModelProjectiveCartanCoordinateDivisibilityProducer

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance
    fullMixedModelProjectiveCartanCoordinateDivisibilityProducerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance
    fullMixedModelProjectiveCartanCoordinateDivisibilityProducerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Full mixed-model input saying that the projective-envelope basis vectors have divisible
fixed Cartan coordinates.  This is the non-formal basis-vector layer isolated from the extension
argument. -/
def fullMixedModelForwardScaledProjectiveEnvelopeBasisCoordinateDivisibilityStatement : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      ∃ π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G,
        (∀ c, Simple (π c)) ∧
          (∀ c,
            regularClassCoordinateAddEquiv
                (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
              (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) ∧
          ∃ _ : PairwiseNonisomorphic π,
            ∃ _ : IsCompleteIrreducibleFamily π,
              ∃ P : PRegularConjClass G p →
                  FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G,
                ∃ _ :
                  ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]]
                    asModule (π c).ρ, f.IsProjectiveEnvelope,
                  ∀ c d : PRegularConjClass G p,
                    ∃ a : ℤ,
                      cartanCoordinateAddHom
                          (p := p) (k := IsLocalRing.ResidueField A) (G := G) [P c]ₚ₀ d =
                        (ConjClasses.centralizerPPart p d.1 : ℤ) * a

/-- Full mixed-model form of the missing readback-preservation input for projective-envelope
basis vectors: after reading back the regular-restriction row to Cartan coordinates, the cast
integer row is still in Serre's regular-value divisibility lattice. -/
def fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement : Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      ∃ π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G,
        ∃ _ : ∀ c, Simple (π c),
          ∃ _ :
            ∀ c,
              regularClassCoordinateAddEquiv
                  (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
            ∃ _ : PairwiseNonisomorphic π,
              ∃ _ : IsCompleteIrreducibleFamily π,
                ∃ P : PRegularConjClass G p →
                    FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G,
                  ∃ _ :
                    ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]]
                      asModule (π c).ρ, f.IsProjectiveEnvelope,
                    ∀ c : PRegularConjClass G p,
                      regularIntegerFunctionCast (p := p) (K := K) (G := G)
                          (cartanCoordinateAddHom
                            (p := p) (k := IsLocalRing.ResidueField A) (G := G)
                            [P c]ₚ₀) ∈
                      regularValueDivisibilitySubmodule
                        (p := p) (A := A) (K := K) (G := G)

/-- Full mixed-model form of the local regular-value congruence blocker for projective-envelope
rows.  This is equivalent to
`fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement`, because
projective-envelope regular restrictions are already in Serre's regular-value divisibility
lattice. -/
def fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateRegularValueCongruenceStatement :
    Prop :=
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p],
    IsLocalRing.ResidueField A ≃+* k →
      ∃ π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G,
        ∃ _ : ∀ c, Simple (π c),
          ∃ _ :
            ∀ c,
              regularClassCoordinateAddEquiv
                  (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ),
            ∃ _ : PairwiseNonisomorphic π,
              ∃ _ : IsCompleteIrreducibleFamily π,
                ∃ P : PRegularConjClass G p →
                    FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G,
                  ∃ _ :
                    ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]]
                      asModule (π c).ρ, f.IsProjectiveEnvelope,
                    coordinate_normalized_projective_envelope_cartanCoordinateRegularValueCongruence
                      (p := p) (A := A) (K := K) (G := G) P

omit [IsAlgClosed k] [CharP k p] in
/-- The endpoint-facing cast-membership target is exactly the local congruence blocker. -/
theorem
    fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement_iff_regularValueCongruence :
    fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement
        (p := p) (k := k) (G := G) ↔
      fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateRegularValueCongruenceStatement
        (p := p) (k := k) (G := G) := by
  constructor
  · intro hcast A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    rcases hcast (A := A) (K := K) e0 with
      ⟨π, hπ_simple, hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope, hcast_rows⟩
    refine ⟨π, hπ_simple, hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope, ?_⟩
    exact
      (coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_iff_regularValueCongruence
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope).1 hcast_rows
  · intro hcong A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
      _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
      _instAlgClosed _instCharP e0
    rcases hcong (A := A) (K := K) e0 with
      ⟨π, hπ_simple, hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope, hcong_rows⟩
    refine ⟨π, hπ_simple, hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope, ?_⟩
    exact
      (coordinate_normalized_projective_envelope_cartanCoordinate_cast_mem_regularValue_iff_regularValueCongruence
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord P hP_envelope).2 hcong_rows

omit [IsAlgClosed k] [CharP k p] in
/-- Projective-envelope basis-vector coordinate divisibility extends to the requested full
mixed-model coordinatewise Cartan divisibility statement. -/
theorem
    fullMixedModelForwardScaledCartanCoordinateDivisibilityStatement_of_projectiveEnvelopeBasisCoordinateDivisibility
    (hbasis :
      fullMixedModelForwardScaledProjectiveEnvelopeBasisCoordinateDivisibilityStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelForwardScaledCartanCoordinateDivisibilityStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hbasis (A := A) (K := K) e0 with
    ⟨π, _hπ_simple, _hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope, hbasis_div⟩
  exact
    cartanCoordinateAddHom_coordinate_divisible_of_projectiveEnvelope_basis_vectors
      (p := p) (A := A) (G := G)
      π hπ_pairwise hπ_complete P hP_envelope hbasis_div

omit [IsAlgClosed k] [CharP k p] in
/-- The missing readback-preservation input gives the projective-envelope basis-vector
coordinate divisibility layer by integer descent. -/
theorem
    fullMixedModelForwardScaledProjectiveEnvelopeBasisCoordinateDivisibilityStatement_of_projectiveEnvelope_castRegularValue
    (hcast :
      fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelForwardScaledProjectiveEnvelopeBasisCoordinateDivisibilityStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hcast (A := A) (K := K) e0 with
    ⟨π, hπ_simple, hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope, hcast_rows⟩
  refine ⟨π, hπ_simple, hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope, ?_⟩
  exact
    coordinate_normalized_projective_envelope_cartanCoordinate_divisibility_of_cast_mem
      (p := p) (A := A) (K := K) (G := G) P hcast_rows

omit [IsAlgClosed k] [CharP k p] in
/-- The missing readback-preservation input closes the requested full mixed-model
coordinatewise Cartan divisibility statement. -/
theorem
    fullMixedModelForwardScaledCartanCoordinateDivisibilityStatement_of_projectiveEnvelope_castRegularValue
    (hcast :
      fullMixedModelForwardScaledProjectiveEnvelopeCartanCoordinateCastRegularValueStatement
        (p := p) (k := k) (G := G)) :
    fullMixedModelForwardScaledCartanCoordinateDivisibilityStatement
      (p := p) (k := k) (G := G) := by
  intro A _instComm _instLocal _instHenselian _instDomain _instDVR _instNoetherian
    _instComplete K _instField _instAlgebra _instFraction _instCharZero _instRoots
    _instAlgClosed _instCharP e0
  rcases hcast (A := A) (K := K) e0 with
    ⟨π, _hπ_simple, _hπ_coord, hπ_pairwise, hπ_complete, P, hP_envelope, hcast_rows⟩
  have hbasis_div :
      ∀ c d : PRegularConjClass G p,
        ∃ a : ℤ,
          cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) [P c]ₚ₀ d =
            (ConjClasses.centralizerPPart p d.1 : ℤ) * a :=
    coordinate_normalized_projective_envelope_cartanCoordinate_divisibility_of_cast_mem
      (p := p) (A := A) (K := K) (G := G) P hcast_rows
  exact
    cartanCoordinateAddHom_coordinate_divisible_of_projectiveEnvelope_basis_vectors
      (p := p) (A := A) (G := G)
      π hπ_pairwise hπ_complete P hP_envelope hbasis_div

end FullMixedModelProjectiveCartanCoordinateDivisibilityProducer

end Representation
