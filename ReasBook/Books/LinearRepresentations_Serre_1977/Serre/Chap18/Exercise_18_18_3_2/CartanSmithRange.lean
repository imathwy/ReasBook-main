import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.SmithDiagonal
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanCoordinates

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

section SmithRangeAdapter

variable {ι : Type x}
variable {M : Type u} [AddCommGroup M] [Finite ι]

/-- Additive-subgroup wrapper for the Smith diagonal adapter: if the Smith coefficients of a
full-rank additive subgroup match a requested diagonal after a permutation, then some additive
coordinate equivalence sends that subgroup to the requested diagonal lattice. -/
theorem addSubgroup_exists_coordinate_equiv_with_diagonal_of_smith_coeffs_perm
    (N : AddSubgroup M)
    (b : Module.Basis ι ℤ M)
    (h : Module.finrank ℤ N.toIntSubmodule = Module.finrank ℤ M)
    (d : ι → ℕ)
    (σ : ι ≃ ι)
    (hcoeff :
      ∀ i,
        Int.natAbs (Submodule.smithNormalFormCoeffs (N := N.toIntSubmodule) b h i) =
          d (σ i)) :
    ∃ e : M ≃+ (ι → ℤ),
      N.map e.toAddMonoidHom =
        (Submodule.pi Set.univ fun i ↦
          Submodule.span ℤ ({(d i : ℤ)} : Set ℤ)).toAddSubgroup := by
  simpa using
    (exists_coordinate_equiv_with_diagonal_of_smith_coeffs_perm
      (N := N.toIntSubmodule) (b := b) (h := h) (d := d) (σ := σ) hcoeff)

/-- Existential form of
`addSubgroup_exists_coordinate_equiv_with_diagonal_of_smith_coeffs_perm`: it is enough to supply
some ambient basis, full-rank proof, and reindexing for the Smith coefficients. -/
theorem addSubgroup_exists_coordinate_equiv_with_diagonal_of_exists_smith_coeffs_perm
    (N : AddSubgroup M)
    (d : ι → ℕ)
    (hSmith :
      ∃ (b : Module.Basis ι ℤ M)
        (h : Module.finrank ℤ N.toIntSubmodule = Module.finrank ℤ M)
        (σ : ι ≃ ι),
        ∀ i,
          Int.natAbs (Submodule.smithNormalFormCoeffs (N := N.toIntSubmodule) b h i) =
            d (σ i)) :
    ∃ e : M ≃+ (ι → ℤ),
      N.map e.toAddMonoidHom =
        (Submodule.pi Set.univ fun i ↦
          Submodule.span ℤ ({(d i : ℤ)} : Set ℤ)).toAddSubgroup := by
  rcases hSmith with ⟨b, h, σ, hcoeff⟩
  exact
    addSubgroup_exists_coordinate_equiv_with_diagonal_of_smith_coeffs_perm
      (N := N) (b := b) (h := h) (d := d) (σ := σ) hcoeff

end SmithRangeAdapter

section CartanSmithRange

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanSmithRangeFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanSmithRangeDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAlgClosed k] [CharP k p] in
/-- Smith/invariant-factor adapter for the Cartan range in Exercise 18-18.3-2. If the Cartan
range is full-rank in `R₀[k](G)` and its Smith coefficients, for some ambient integral basis, are
the centralizer `p`-parts up to reindexing, then the Cartan range has the desired regular-class
diagonal coordinate description.

This theorem is intentionally only an adapter: the hypotheses are exactly the Smith/full-rank
input that a projective-character lattice argument should supply. -/
theorem existsCartanRangeCoordinateEquiv_of_smith_coeffs_perm
    (b : Module.Basis (PRegularConjClass G p) ℤ (R₀[k](G)))
    (hfull :
      Module.finrank ℤ ((cartanHom k G).range.toIntSubmodule) =
        Module.finrank ℤ (R₀[k](G)))
    (σ : PRegularConjClass G p ≃ PRegularConjClass G p)
    (hcoeff :
      ∀ c : PRegularConjClass G p,
        Int.natAbs
            (Submodule.smithNormalFormCoeffs
              (N := (cartanHom k G).range.toIntSubmodule) b hfull c) =
          ConjClasses.centralizerPPart p (σ c).1) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  simpa [regularIntegerDiagonalSubmodule] using
    (addSubgroup_exists_coordinate_equiv_with_diagonal_of_smith_coeffs_perm
      (N := (cartanHom k G).range)
      (b := b)
      (h := hfull)
      (d := fun c : PRegularConjClass G p ↦ ConjClasses.centralizerPPart p c.1)
      (σ := σ)
      hcoeff)

omit [IsAlgClosed k] [CharP k p] in
/-- Existential Smith/invariant-factor adapter for the Cartan range. The only Cartan-specific
input is the Smith package for `(cartanHom k G).range`; once that package is supplied, the range
coordinate equivalence follows formally from Smith normal form. -/
theorem existsCartanRangeCoordinateEquiv_of_exists_smith_coeffs_perm
    (hSmith :
      ∃ (b : Module.Basis (PRegularConjClass G p) ℤ (R₀[k](G)))
        (hfull :
          Module.finrank ℤ ((cartanHom k G).range.toIntSubmodule) =
            Module.finrank ℤ (R₀[k](G)))
        (σ : PRegularConjClass G p ≃ PRegularConjClass G p),
        ∀ c : PRegularConjClass G p,
          Int.natAbs
              (Submodule.smithNormalFormCoeffs
                (N := (cartanHom k G).range.toIntSubmodule) b hfull c) =
            ConjClasses.centralizerPPart p (σ c).1) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  rcases hSmith with ⟨b, hfull, σ, hcoeff⟩
  exact
    existsCartanRangeCoordinateEquiv_of_smith_coeffs_perm
      (p := p) (k := k) (G := G) (b := b) (hfull := hfull) (σ := σ) hcoeff

end CartanSmithRange

end Representation
