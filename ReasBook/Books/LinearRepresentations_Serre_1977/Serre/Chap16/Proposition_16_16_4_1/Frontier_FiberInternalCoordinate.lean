import LinearRepresentations_Serre_1977.Serre.Chap16.Proposition_16_16_4_1.Index
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.CanonicalPacketFrontier
import LinearRepresentations_Serre_1977.Serre.Chap16.Proposition_16_16_4_1.Frontier_PacketReindex
import LinearRepresentations_Serre_1977.Serre.Chap16.Proposition_16_16_4_1.Frontier_CharZeroSupportedFamily
import LinearRepresentations_Serre_1977.Serre.Chap16.Proposition_16_16_4_1.Frontier_AsAlgebraHomTransport

noncomputable section

open scoped MonoidAlgebra
open Representation
open CategoryTheory

universe u v w x y

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type w} [Group G]
variable {E : Type x} [AddCommGroup E] [Module A E] [Module K E] [IsScalarTower A K E]

local notation "k" => IsLocalRing.ResidueField A

namespace StableLattice

section DefectZero

variable [Finite G] [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
variable {ρ : Representation K G E} [FiniteDimensional K E]
variable (L : StableLattice A ρ)

/-- Helper for Proposition 16-16.4-1: the Chapter `12` honest packet fibers are nonempty once the
visible multiplicities `d i` are positive. This restores the source-faithful choice of one actual
constituent in each packet before any Shrink-transport or coefficient comparison. -/
lemma packet_fiber_nonempty_local
    {ι : Type*} [Fintype ι] [CharZero K]
    (ψ : ι → Rep.{max w v} (AlgebraicClosure K) G)
    (d : ι → ℕ)
    (hd_pos : ∀ i, 0 < d i)
    (hψ_fd : ∀ i, FiniteDimensional (AlgebraicClosure K) (ψ i))
    (hψ_irr : ∀ i, (ψ i).ρ.IsIrreducible)
    (a : ℕ)
    (σ : Fin a →
      Subrepresentation
        (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ))
    (S : ι → Finset (Fin a))
    (hfiber :
      ∀ i,
        Finset.sum
            (S i)
            (fun j ↦ ((σ j).toRepresentation).character) =
          (d i : AlgebraicClosure K) • (ψ i).ρ.character) :
    ∀ i, (S i).Nonempty := by
  intro i
  letI : FiniteDimensional (AlgebraicClosure K) (ψ i) := hψ_fd i
  letI : (ψ i).ρ.IsIrreducible := hψ_irr i
  by_contra hSi_empty
  have hfiber_degree :=
    by
      -- Evaluate the honest fiber character identity at `1` to turn it into a degree sum.
      simpa [Representation.char_one, smul_eq_mul] using congrFun (hfiber i) 1
  have hd_ne : (d i : AlgebraicClosure K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hd_pos i))
  have hdim_ne :
      (Module.finrank (AlgebraicClosure K) (ψ i) : AlgebraicClosure K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr
      (Nat.ne_of_gt
        (Representation.irreducible_rep_finrank_pos_local (G := G) (V := ψ i)))
  have hfiber_degree_zero :
      (Finset.sum (S i)
          (fun j ↦ (Module.finrank (AlgebraicClosure K) ↥((σ j).toSubmodule) :
            AlgebraicClosure K))) = 0 := by
    -- If the honest fiber were empty, its degree sum would vanish.
    simp [Finset.not_nonempty_iff_eq_empty.mp hSi_empty]
  have hmul_zero :
      (d i : AlgebraicClosure K) *
          (Module.finrank (AlgebraicClosure K) (ψ i) : AlgebraicClosure K) =
        0 := by
    -- Compare the positive target degree with the vanished empty-fiber degree sum.
    exact hfiber_degree_zero ▸ hfiber_degree.symm
  exact (mul_ne_zero hd_ne hdim_ne) hmul_zero

/-- Helper for Proposition 16-16.4-1: for an internal direct-sum decomposition `σ`, the genuine
source-faithful way to read the `j`-th part of an ambient endomorphism `F` is not to "restrict"
`F` to `σ j`, but to include `σ j`, apply `F`, and project back to the `j`-th coordinate. -/
noncomputable def internal_coordinate_endomorphism_local
    {L' : Type*} [Field L']
    {G' : Type*} [Group G']
    {V' : Type*} [AddCommGroup V'] [Module L' V']
    {ρ' : Representation L' G' V'}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : ι → Subrepresentation ρ')
    (hinternal : DirectSum.IsInternal (fun j ↦ (σ j).toSubmodule))
    (F : Module.End L' V') (j : ι) :
    Module.End L' (σ j).toSubmodule :=
  letI := DirectSum.IsInternal.chooseDecomposition _ hinternal
  let projj : V' →ₗ[L'] (σ j).toSubmodule :=
    (DirectSum.component L' ι _ j).comp
      (DirectSum.decomposeLinearEquiv (fun t ↦ (σ t).toSubmodule)).toLinearMap
  projj.comp (F.comp (σ j).toSubmodule.subtype)

/-- Helper for Proposition 16-16.4-1: when the ambient map is the identity, the `j`-th internal
coordinate endomorphism is just the identity on the `j`-th summand. This records the projection
normalization coming from `DirectSum.decomposeLinearEquiv_apply_coe`. -/
lemma internal_coordinate_endomorphism_id_local
    {L' : Type*} [Field L']
    {G' : Type*} [Group G']
    {V' : Type*} [AddCommGroup V'] [Module L' V']
    {ρ' : Representation L' G' V'}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : ι → Subrepresentation ρ')
    (hinternal : DirectSum.IsInternal (fun j ↦ (σ j).toSubmodule))
    (j : ι) :
    StableLattice.internal_coordinate_endomorphism_local σ hinternal
        (LinearMap.id : Module.End L' V') j =
      LinearMap.id := by
  letI := DirectSum.IsInternal.chooseDecomposition _ hinternal
  ext x
  -- On a vector already lying in the `j`-th summand, the decomposition map reads exactly the
  -- `j`-th direct-sum basis vector.
  dsimp [StableLattice.internal_coordinate_endomorphism_local]
  rw [DirectSum.decomposeLinearEquiv_apply_coe (fun t ↦ (σ t).toSubmodule) j x]
  simp


end DefectZero

end StableLattice

end
