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

omit [HenselianLocalRing A] in
/-- Helper for Exercise 16-16.3-8: decomposing an actual positive representation class over `K`
gives an actual positive class over the residue field. -/
theorem decompositionHom_image_subset_finiteRepPositive
    [IsDomain A] [IsDiscreteValuationRing A] :
    decompositionHom A K G '' R⁺[K](G) ⊆ R⁺[k](G) := by
  -- Represent the positive class by a finite-dimensional representation and reduce a stable
  -- lattice for that representation.
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨V, rfl⟩ := (mem_finiteRepPositiveSubset_iff (K := K) (G := G)).1 hx
  obtain ⟨L⟩ := Representation.exists_stableLattice A V.ρ
  rw [decompositionHom_finiteRepClass_eq (A := A) (K := K) (G := G) V L]
  exact (mem_finiteRepPositiveSubset_iff (K := k) (G := G)).2
    ⟨FDRep.of L.reductionRepresentation, rfl⟩

omit [HenselianLocalRing A] in
/-- Helper for Exercise 16-16.3-8: a simple stable-lattice lift of a residue-field
representation puts its class in the positive image of the decomposition homomorphism. -/
theorem simpleStableLatticeLift_simpleClass_mem_decompositionHom_image
    [IsDomain A] [IsDiscreteValuationRing A]
    {S : FDRep k G} (hS : Simple S)
    (hLift :
      ∃ X : FDRep K G, Simple X ∧
        ∃ L : StableLattice A X.ρ, Nonempty (FDRep.of L.reductionRepresentation ≅ S)) :
    ([S]₀ : R₀[k](G)) ∈ decompositionHom A K G '' R⁺[K](G) := by
  -- Unpack the lifted simple `K`-representation and its stable lattice reduction.
  rcases hLift with ⟨X, _hXsimple, L, ⟨iso⟩⟩
  let _ := hS
  refine ⟨[X]₀, ?_, ?_⟩
  · -- The source witness is an actual finite-dimensional representation over `K`.
    exact (mem_finiteRepPositiveSubset_iff (K := K) (G := G)).2 ⟨X, rfl⟩
  · -- The decomposition formula identifies its reduction with the requested simple class.
    rw [decompositionHom_finiteRepClass_eq (A := A) (K := K) (G := G) X L]
    exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := G) ⟨iso⟩

omit [HenselianLocalRing A] in
/-- Helper for Exercise 16-16.3-8: the source-facing Cartan triangle holds on all projective
Grothendieck classes without passing through the complete-only reduction equivalence. -/
theorem decompositionHom_baseChangeHom_eq_cartanHom_reductionHom
    [IsDomain A] [IsDiscreteValuationRing A]
    (y : P₀[A](G)) :
    decompositionHom A K G
        (projectiveGrothendieckBaseChangeHom (A := A) (G := G) K y) =
      cartanHom k G (projectiveGrothendieckReductionHom (A := A) (G := G) y) := by
  -- Prove the additive identity on projective generators, where the Chapter 16 support lemma
  -- gives Serre's `d([Q_K]) = c([Q_k])`, then descend through the free presentation.
  refine QuotientAddGroup.induction_on y ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro Q
    calc
      decompositionHom A K G
          (projectiveGrothendieckBaseChangeHom (A := A) (G := G) K [Q]ₚ₀) =
          decompositionHom A K G [Q.scalarExtension K]₀ := by
            rw [projectiveGrothendieckBaseChangeHom_projectiveClass_eq]
      _ = cartanHom k G [Q.residueFieldReduction]ₚ₀ :=
            decompositionHom_projective_scalarExtension_class_eq_cartan_reduction_class_support
              (A := A) (K := K) (G := G) Q
      _ = cartanHom k G
          (projectiveGrothendieckReductionHom (A := A) (G := G) [Q]ₚ₀) := by
            rw [projectiveGrothendieckReductionHom_projectiveClass_eq]
  · intro a ha
    simpa using congrArg Neg.neg ha
  · intro a b ha hb
    simpa [map_add] using congrArg₂ (fun u v ↦ u + v) ha hb

end

end Representation
