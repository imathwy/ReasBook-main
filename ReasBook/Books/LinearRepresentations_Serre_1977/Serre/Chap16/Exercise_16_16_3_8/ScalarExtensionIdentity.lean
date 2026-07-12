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

/-- Helper for Exercise 16-16.3-8: additive homomorphisms out of the finite-representation
Grothendieck group are determined by their values on actual representation classes. -/
theorem fdRepGrothendieckAddHom_ext_of_class_eq {H : Type v} [AddCommGroup H]
    {K : Type u} [Field K] {G : Type u} [Group G]
    (f g : R₀[K](G) →+ H)
    (h : ∀ V : FDRep K G, f [V]₀ = g [V]₀) : f = g := by
  -- Descend the class comparison through the free presentation of `R₀[K](G)`.
  refine AddMonoidHom.ext ?_
  intro x
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (finiteRepGrothendieckRelations K G) x
  have hcomp :
      f.comp (QuotientAddGroup.mk' (finiteRepGrothendieckRelations K G)) =
        g.comp (QuotientAddGroup.mk' (finiteRepGrothendieckRelations K G)) := by
    apply FreeAbelianGroup.lift_ext
    intro V
    exact h V
  exact DFunLike.congr_fun hcomp y

/-- Helper for Exercise 16-16.3-8: rebuilding an `FDRep` from its representation owner does not
change the object up to equivariant isomorphism. -/
theorem fdRepNonemptyIsoOfRho
    {K : Type u} [Field K] {G : Type u} [Group G] (V : FDRep K G) :
    Nonempty (V ≅ FDRep.of V.ρ) := by
  -- The identity linear map is equivariant for the same representation action.
  refine ⟨Action.mkIso (Iso.refl _) ?_⟩
  intro g
  ext x
  rfl

/-- Helper for Exercise 16-16.3-8: scalar extension along the identity field map is equivariantly
isomorphic to the original representation. -/
theorem representationNonemptyEquivScalarExtensionSelf
    {K : Type u} [Field K] {G : Type u} [Group G]
    {V : Type u} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) :
    Nonempty (ρ.Equiv (Representation.scalarExtension ρ)) := by
  -- The tensor left unitor identifies `K ⊗[K] V` with `V` and respects the `G`-action.
  refine ⟨Representation.Equiv.mk (_root_.TensorProduct.lid K V).symm ?_⟩
  intro g
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  change (1 : K) ⊗ₜ[K] (ρ g x) =
    LinearMap.baseChange K (ρ g) ((1 : K) ⊗ₜ[K] x)
  rw [LinearMap.baseChange_tmul]

/-- Helper for Exercise 16-16.3-8: scalar extension from a field to itself preserves each actual
finite-representation Grothendieck class. -/
theorem finiteRepGrothendieckClass_scalarExtension_self
    {K : Type u} [Field K] {G : Type u} [Group G] (V : FDRep K G) :
    ([(FDRep.scalarExtension V)]₀ : R₀[K](G)) = [V]₀ := by
  -- Convert the self-scalar-extension equivalence into equality in the Grothendieck group.
  symm
  refine finiteRepGrothendieckClass_eq_of_nonempty_iso (L := K) (G := G) ?_
  obtain ⟨equivSelf⟩ := representationNonemptyEquivScalarExtensionSelf V.ρ
  obtain ⟨isoRho⟩ := fdRepNonemptyIsoOfRho V
  exact ⟨isoRho.trans equivSelf.toFDRepIso⟩

/-- Helper for Exercise 16-16.3-8: scalar extension `K → K` is the identity on
`R₀[K](G)`. -/
theorem finiteRepGrothendieckScalarExtensionHom_self_eq_id
    {K : Type u} [Field K] {G : Type u} [Group G] :
    finiteRepGrothendieckScalarExtensionHom K K G = AddMonoidHom.id (R₀[K](G)) := by
  -- It is enough to compare both homomorphisms on actual representation generators.
  apply fdRepGrothendieckAddHom_ext_of_class_eq (K := K) (G := G)
  intro V
  rw [finiteRepGrothendieckScalarExtensionHom_class_eq, AddMonoidHom.id_apply]
  exact finiteRepGrothendieckClass_scalarExtension_self V

end

end Representation
