import Mathlib
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_2_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2

noncomputable section

open Representation

universe u v

namespace Representation
namespace MatrixTailBasisData

section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A
local notation:max "P_k(" G ")" => finiteProjectiveGroupAlgebraGrothendieckGroup k G
local notation:max "R_K(" G ")" => finiteRepGrothendieckGroup K G
local notation:max "R_k(" G ")" => finiteRepGrothendieckGroup k G

/-- Helper for Proposition 15-15.5-1: if a linear map sends the chosen `K`-simple basis to the
reduced simple basis, then the basis-built map `bk.constr ℤ bK` is a left inverse. -/
theorem basis_constr_leftInverse_of_basis_images
    {S : Type v}
    (bK : Module.Basis S ℤ (R_K(G)))
    (bk : Module.Basis S ℤ (R_k(G)))
    (f : R_K(G) →ₗ[ℤ] R_k(G))
    (hf : ∀ i, f (bK i) = bk i) :
    (bk.constr ℤ bK).comp f = LinearMap.id := by
  -- It is enough to compare both endomorphisms on the basis vectors `bK i`.
  apply bK.ext
  intro i
  -- The reconstruction map sends the image basis vector `bk i` straight back to `bK i`.
  simp [LinearMap.comp_apply, hf i]

/-- Helper for Proposition 15-15.5-1: the reduced simple family attached to the chosen lattices. -/
def reduction_family_of_order_prime_to_p
    {S : Type v}
    (πK : S → FDRep K G)
    (L : ∀ i : S, StableLattice A (πK i).ρ) :
    S → FDRep k G := fun i ↦ FDRep.of (L i).reductionRepresentation

/-- Helper for Proposition 15-15.5-1: the canonical simple-class basis over `K` for the chosen
generic simple family. -/
def generic_simple_basis_of_order_prime_to_p
    {S : Type v}
    (πK : S → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK) :
    Module.Basis S ℤ (R_K(G)) :=
  simple_finiteRep_classes_basis_of_complete_family
    πK hπK_pairwise hπK_complete

/-- Helper for Proposition 15-15.5-1: the canonical simple-class basis over `k` for the reduced
lattice family. -/
def reduced_simple_basis_of_order_prime_to_p
    {S : Type v}
    (πK : S → FDRep K G)
    (L : ∀ i, StableLattice A (πK i).ρ)
    (hπk_pairwise :
      PairwiseNonisomorphic
        (reduction_family_of_order_prime_to_p (A := A) (K := K) (G := G) πK L))
    (hπk_complete :
      IsCompleteIrreducibleFamily
        (reduction_family_of_order_prime_to_p (A := A) (K := K) (G := G) πK L)) :
    Module.Basis S ℤ (R_k(G)) :=
  simple_finiteRep_classes_basis_of_complete_family
    (reduction_family_of_order_prime_to_p (A := A) (K := K) (G := G) πK L)
    hπk_pairwise hπk_complete

/-- Helper for Proposition 15-15.5-1: the canonical projective-envelope basis over `k` attached to
the reduced lattice family. -/
def projective_envelope_basis_of_order_prime_to_p
    {S : Type v}
    (πK : S → FDRep K G)
    (L : ∀ i, StableLattice A (πK i).ρ)
    (hπk_pairwise :
      PairwiseNonisomorphic
        (reduction_family_of_order_prime_to_p (A := A) (K := K) (G := G) πK L))
    (hπk_complete :
      IsCompleteIrreducibleFamily
        (reduction_family_of_order_prime_to_p (A := A) (K := K) (G := G) πK L))
    (P : S → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i,
        ∃ f : (P i).V →ₗ[k[G]]
          asModule (L i).reductionRepresentation,
          f.IsProjectiveEnvelope) :
    Module.Basis S ℤ (P_k(G)) :=
  projectiveEnvelope_classes_basis_of_complete_family
    (reduction_family_of_order_prime_to_p (A := A) (K := K) (G := G) πK L)
    hπk_pairwise hπk_complete P hP_envelope

/-- Helper for Proposition 15-15.5-1: once the reduced family is complete and pairwise
nonisomorphic, the basis-built map `bk.constr ℤ bK` is a left inverse to `decompositionHom`. -/
theorem decomposition_basis_leftInverse_named_of_order_prime_to_p
    {S : Type v}
    (πK : S → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ)
    (hπk_pairwise :
      PairwiseNonisomorphic
        (reduction_family_of_order_prime_to_p (A := A) (K := K) (G := G) πK L))
    (hπk_complete :
      IsCompleteIrreducibleFamily
        (reduction_family_of_order_prime_to_p (A := A) (K := K) (G := G) πK L)) :
    ((reduced_simple_basis_of_order_prime_to_p
        (A := A) (K := K) (G := G) πK L hπk_pairwise hπk_complete).constr ℤ
      (generic_simple_basis_of_order_prime_to_p
        (G := G) πK hπK_pairwise hπK_complete)).comp
      (decompositionHom A K G).toIntLinearMap = LinearMap.id := by
  let bK : Module.Basis S ℤ (R_K(G)) :=
    generic_simple_basis_of_order_prime_to_p (G := G) πK hπK_pairwise hπK_complete
  let bk : Module.Basis S ℤ (R_k(G)) :=
    reduced_simple_basis_of_order_prime_to_p
      (A := A) (K := K) (G := G) πK L hπk_pairwise hπk_complete
  -- Evaluate `decompositionHom` on the `K`-simple basis and package the resulting basis images.
  refine basis_constr_leftInverse_of_basis_images (G := G) bK bk
    (decompositionHom A K G).toIntLinearMap ?_
  intro i
  rw [simple_finiteRep_classes_basis_of_complete_family_apply,
    simple_finiteRep_classes_basis_of_complete_family_apply]
  -- The chosen lattice `L i` is exactly the reduction datum defining the `i`-th reduced basis
  -- vector.
  simpa using
    decompositionHom_finiteRepClass_eq (A := A) (K := K) (G := G) (πK i) (L i)

end

end MatrixTailBasisData
end Representation
