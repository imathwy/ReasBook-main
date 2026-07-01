import Mathlib
import Serre.Chap15.Theorem_15_15_2_2
import Serre.Chap16.Theorem_16_16_2_1
import Serre.Chap16.Proposition_16_16_4_1

noncomputable section

open scoped MonoidAlgebra
open Representation

universe u

namespace Representation

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
local notation "k" => IsLocalRing.ResidueField A
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

/-- Helper for Corollary 16-16.4-2: a stable lattice whose `A[G]`-module is projective yields an
actual finite projective `A[G]`-owner whose generic fiber is the original representation. -/
lemma projective_lift_iso_of_stable_lattice
    (V : FDRep K G) (L : StableLattice A V.ρ)
    (hproj : Module.Projective A[G] L.toRepresentation.asModule) :
    ∃ Q : FiniteProjectiveGroupAlgebraModule A G, Nonempty (Q.scalarExtension K ≅ V) := by
  -- Package the lattice as the canonical finite-projective `A[G]` owner.
  let Qfg : FGModuleCat A[G] := ⟨ModuleCat.of A[G] L.toSubmodule, by infer_instance⟩
  let Q : FiniteProjectiveGroupAlgebraModule A G := ⟨Qfg, by
    simpa using hproj⟩
  refine ⟨Q, ?_⟩
  -- The stable-lattice base-change equivalence is exactly the desired generic-fiber isomorphism.
  refine ⟨Representation.Equiv.toFDRepIso ?_⟩
  refine Representation.Equiv.mk (L.toSubmodule_subtype_isBaseChange.equiv) ?_
  intro g
  ext x
  simp [FiniteProjectiveGroupAlgebraModule.scalarExtension, Representation.ofModule']

/-- Helper for Corollary 16-16.4-2: defect zero produces an actual finite projective `A[G]`-lift
whose scalar-extension class is `[V]₀`. -/
lemma projective_scalar_extension_class_of_defect_zero
    [Fact p.Prime] [CharP k p]
    (V : FDRep K G) (hdefect : Representation.HasDefectZero V.ρ p) :
    ∃ Q : FiniteProjectiveGroupAlgebraModule A G, [Q.scalarExtension K]₀ = [V]₀ := by
  -- Choose a stable lattice and apply Proposition `16-16.4-1 (1)` to make it projective.
  obtain ⟨L⟩ := Representation.exists_stableLattice A V.ρ
  have hproj : Module.Projective A[G] L.toRepresentation.asModule :=
    L.projective_of_defect_zero hdefect
  -- Repackage that projective lattice as an actual finite projective owner.
  obtain ⟨Q, hQ⟩ :=
    projective_lift_iso_of_stable_lattice (A := A) (K := K) (G := G) V L hproj
  refine ⟨Q, ?_⟩
  -- Isomorphic finite-dimensional representations define the same Grothendieck class.
  exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := K) (G := G) hQ

/-- Helper for Corollary 16-16.4-2: an actual projective scalar-extension lift gives the exact
range witness needed by Theorem `16-16.2-1`. -/
lemma mem_projectiveGrothendieckScalarExtension_range_of_projective_scalar_extension_class
    (V : FDRep K G)
    (hV : ∃ Q : FiniteProjectiveGroupAlgebraModule A G, [Q.scalarExtension K]₀ = [V]₀) :
    [V]₀ ∈ (projectiveGrothendieckScalarExtensionHom A K : P₀[k](G) →+ R₀[K](G)).range := by
  rcases hV with ⟨Q, hQ⟩
  refine ⟨projectiveGrothendieckReductionEquiv (A := A) (G := G) [Q]ₚ₀, ?_⟩
  -- Evaluate Serre's scalar-extension map on the explicit projective witness.
  calc
    projectiveGrothendieckScalarExtensionHom A K
        ((projectiveGrothendieckReductionEquiv (A := A) (G := G)) [Q]ₚ₀) =
        [Q.scalarExtension K]₀ := by
          have hred :
              (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm
                  ((projectiveGrothendieckReductionEquiv (A := A) (G := G)) [Q]ₚ₀) = [Q]ₚ₀ := by
            exact
              (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm_apply_apply [Q]ₚ₀
          rw [projectiveGrothendieckScalarExtensionHom_apply]
          rw [hred]
          exact projectiveGrothendieckBaseChangeHom_projectiveClass_eq (K := K) Q
    _ = [V]₀ := hQ

/-- Corollary 16-16.4-2: for a defect-zero irreducible finite-dimensional `K`-representation, the
ordinary character is zero on `p`-singular elements of `G`. -/
theorem character_eq_zero_of_not_isPRegular_of_defect_zero
    [Fact p.Prime] [CharP k p]
    (V : FDRep K G) (hdefect : Representation.HasDefectZero V.ρ p)
    (g : G) (hg : ¬ IsPRegular p g) :
    V.character g = 0 := by
  -- Follow Serre's source route: defect zero gives an actual projective lattice lift.
  have hclass :
      ∃ Q : FiniteProjectiveGroupAlgebraModule A G, [Q.scalarExtension K]₀ = [V]₀ :=
    projective_scalar_extension_class_of_defect_zero
      (A := A) (K := K) (G := G) (p := p) V hdefect
  -- Convert that actual lift into the canonical range hypothesis of Theorem `16-16.2-1`.
  have hrange :
      [V]₀ ∈ (projectiveGrothendieckScalarExtensionHom A K : P₀[k](G) →+ R₀[K](G)).range :=
    mem_projectiveGrothendieckScalarExtension_range_of_projective_scalar_extension_class
      (A := A) (K := K) (G := G) V hclass
  -- The forward character-vanishing theorem now applies directly to the actual class `[V]₀`.
  have hvanish :=
    character_eq_zero_on_pSingular_of_mem_projectiveGrothendieckScalarExtension_range
      (A := A) (K := K) (G := G) (p := p) hrange g hg
  simpa [finiteRepGrothendieckCharacter_class] using hvanish

end

end Representation
