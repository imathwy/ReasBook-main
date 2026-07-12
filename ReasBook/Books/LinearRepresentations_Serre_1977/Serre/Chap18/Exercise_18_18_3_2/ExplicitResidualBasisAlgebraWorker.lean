import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.OrthogonalityResidualSourceClosureWorker

/-!
Pure `Basis.repr` algebra for the explicit A-side residual.

The point of this worker is to isolate exactly what can be obtained from the canonical Brauer
basis as a basis of `PRegularConjClass G p → A`, with no Cartan range/cokernel/product endpoint.
The residual term containing `bA.repr` is already visibly a multiple of the target
centralizer `p`-part.  Therefore the requested pointwise residual is equivalent, by pure ring
algebra, to the visible row-entry divisibility

```
bA c d - delta_cd = z(d) * a.
```

The file also records the `basis.sum_repr` reconstruction of the prime-to-`p` point mass, which
is the strongest unconditional basis-algebra identity available at this layer.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section PureBasisAlgebra

variable {ι : Type u}
variable {R : Type u} [CommRing R] [Fintype ι]

/-- Evaluating `Basis.sum_repr` for a basis of functions. -/
theorem basis_sum_repr_apply_comm
    (b : Module.Basis ι R (ι → R)) (f : ι → R) (j : ι) :
    ∑ i : ι, b i j * b.repr f i = f j := by
  calc
    ∑ i : ι, b i j * b.repr f i =
        ∑ i : ι, b.repr f i * b i j := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [mul_comm]
    _ = f j := by
          simpa [Pi.smul_apply] using congrFun (b.sum_repr f) j

/-- Multiplying the coordinate reconstruction by a scalar, with the scalar kept inside the
coefficient column. -/
theorem basis_sum_repr_apply_mul_coeff
    (b : Module.Basis ι R (ι → R)) (f : ι → R) (z : R) (j : ι) :
    ∑ i : ι, b i j * (z * b.repr f i) = z * f j := by
  have hsum : ∑ i : ι, b.repr f i * b i j = f j := by
    simpa [Pi.smul_apply] using congrFun (b.sum_repr f) j
  calc
    ∑ i : ι, b i j * (z * b.repr f i) =
        z * ∑ i : ι, b.repr f i * b i j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i _hi
          ring
    _ = z * f j := by
          rw [hsum]

/-- Pure ring algebra: subtracting an already visible `z`-multiple does not change
divisibility by `z`. -/
theorem residual_divisibility_iff_visible_divisibility
    (x delta z coeff : R) :
    (∃ a : R, x - delta - z * coeff = z * a) ↔
      ∃ a : R, x - delta = z * a := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a + coeff, ?_⟩
    calc
      x - delta = (x - delta - z * coeff) + z * coeff := by
        ring
      _ = z * a + z * coeff := by
        rw [ha]
      _ = z * (a + coeff) := by
        ring
  · rintro ⟨a, ha⟩
    refine ⟨a - coeff, ?_⟩
    calc
      x - delta - z * coeff = z * a - z * coeff := by
        rw [ha]
      _ = z * (a - coeff) := by
        ring

end PureBasisAlgebra

section ExplicitResidualBasisAlgebraWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance explicitResidualBasisAlgebraWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance explicitResidualBasisAlgebraWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The visible readback divisibility left after the pure `repr` residual term is removed. -/
def coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  ∀ c d : PRegularConjClass G p,
    ∃ a : A,
      bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
        (ConjClasses.centralizerPPart p d.1 : A) * a

/-- The unconditional `basis.sum_repr` identity for the inverse prime-to-`p` point mass in the
canonical DVR Brauer basis. -/
theorem canonicalDVRBrauerBasis_primeToPIndicator_sum_repr_basisAlgebra
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (d t : PRegularConjClass G p) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    let bA :=
      canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    let f :=
      primeToP_regular_indicator
        (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)
    ∑ i : PRegularConjClass G p,
        bA i t *
          ((ConjClasses.centralizerPPart p d.1 : A) * (bA.repr f i)) =
      (ConjClasses.centralizerPPart p d.1 : A) * f t := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  let f :=
    primeToP_regular_indicator
      (p := p) (A := A) (G := G) (inversePRegularConjClass (p := p) d)
  exact
    basis_sum_repr_apply_mul_coeff
      (b := bA) (f := f)
      (z := (ConjClasses.centralizerPPart p d.1 : A)) (j := t)

/-- Pointwise, the explicit residual is pure ring-algebra equivalent to the visible
row-entry divisibility.  No property of Brauer characters beyond the existence of the basis is
used here. -/
theorem coordinateNormalizedBrauerBasis_pointwiseResidual_iff_visibleReadback_basisAlgebra
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (c d : PRegularConjClass G p) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord
    let bA :=
      canonicalDVRBrauerBasis
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
    (∃ a : A,
      bA c d -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) -
        (ConjClasses.centralizerPPart p d.1 : A) *
          (bA.repr
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G)
              (inversePRegularConjClass (p := p) d)) c) =
          (ConjClasses.centralizerPPart p d.1 : A) * a) ↔
      ∃ a : A,
        bA c d -
            ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A) =
          (ConjClasses.centralizerPPart p d.1 : A) * a := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    canonicalDVRBrauerBasis
      (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete
  exact
    residual_divisibility_iff_visible_divisibility
      (x := bA c d)
      (delta := ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) d : A))
      (z := (ConjClasses.centralizerPPart p d.1 : A))
      (coeff :=
        (bA.repr
          (primeToP_regular_indicator
            (p := p) (A := A) (G := G)
            (inversePRegularConjClass (p := p) d)) c))

/-- Fixed-family residual equivalence obtained by applying the pointwise pure ring lemma. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_visibleReadback_basisAlgebra
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  constructor
  · intro hresidual c d
    exact
      (coordinateNormalizedBrauerBasis_pointwiseResidual_iff_visibleReadback_basisAlgebra
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d).1
        (hresidual c d)
  · intro hvisible c d
    exact
      (coordinateNormalizedBrauerBasis_pointwiseResidual_iff_visibleReadback_basisAlgebra
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord c d).2
        (hvisible c d)

/-- The explicit orthogonality residual from the source-closure worker has the same pure
basis-algebra boundary: after the `repr` multiple is removed, the remaining missing statement is
exactly visible row-entry divisibility. -/
theorem coordinateNormalizedBrauerBasisExplicitOrthogonalityResidual_iff_visibleReadback_basisAlgebra
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisExplicitOrthogonalityResidual
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord := by
  rw [coordinateNormalizedBrauerBasisExplicitOrthogonalityResidual_iff_pairingResidual]
  exact
    coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_visibleReadback_basisAlgebra
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord

/-- A visible row-entry divisibility proof is sufficient for both named residual formulations. -/
theorem coordinateNormalizedBrauerBasisPairingResidualDivisibility_of_visibleReadback_basisAlgebra
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hvisible :
      coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    coordinateNormalizedBrauerBasisPairingResidualDivisibility
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  (coordinateNormalizedBrauerBasisPairingResidualDivisibility_iff_visibleReadback_basisAlgebra
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hvisible

theorem coordinateNormalizedBrauerBasisExplicitOrthogonalityResidual_of_visibleReadback_basisAlgebra
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hvisible :
      coordinateNormalizedBrauerBasisVisibleReadbackDivisibilityBasisAlgebra
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord) :
    coordinateNormalizedBrauerBasisExplicitOrthogonalityResidual
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord :=
  (coordinateNormalizedBrauerBasisExplicitOrthogonalityResidual_iff_visibleReadback_basisAlgebra
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).2 hvisible

end ExplicitResidualBasisAlgebraWorker

end Representation
