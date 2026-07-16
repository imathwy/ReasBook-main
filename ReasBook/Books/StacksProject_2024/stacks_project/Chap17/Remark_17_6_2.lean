import Mathlib
import Mathlib.Topology.Sheaves.Abelian
import StacksProject_2024.stacks_project.Chap06.ClosedSubsetInclusion
import StacksProject_2024.stacks_project.Chap06.Lemma_6_32_1
import StacksProject_2024.stacks_project.Chap17.Definition_17_5_1

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

noncomputable section

universe u

section

variable {X : TopCat.{u}} {Z : Set X}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

local instance : HasKernels (TopCat.Sheaf AddCommGrpCat.{u} X) := inferInstance

/- Remark 17.6.2: the source-facing content is the support-theoretic description of the kernel
subsheaf cut out by the restriction to the open complement of a closed subset. -/

/-- Helper for Remark 17.6.2: the open complement `X \ Z` viewed as an open subset. -/
private abbrev closedSubsetOpenComplement (hZ : IsClosed Z) : Opens X :=
  ⟨Zᶜ, hZ.isOpen_compl⟩

/-- Helper for Remark 17.6.2: the inclusion of the open complement into `X`. -/
private abbrev closedSubsetOpenComplementInclusion (hZ : IsClosed Z) :
    (Opens.toTopCat X).obj (closedSubsetOpenComplement hZ) ⟶ X :=
  Opens.inclusion' (closedSubsetOpenComplement hZ)

/-- Helper for Remark 17.6.2: the restriction map from a sheaf on `X` to its pushforward from
the open complement `X \ Z`. -/
private abbrev openComplementRestriction
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    ℱ ⟶
      (Sheaf.pushforward AddCommGrpCat.{u}
        (closedSubsetOpenComplementInclusion hZ)).obj
        ((Sheaf.pullback AddCommGrpCat.{u}
          (closedSubsetOpenComplementInclusion hZ)).obj ℱ) :=
  (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    (closedSubsetOpenComplementInclusion hZ)).unit.app ℱ

/-- The subsheaf of an abelian sheaf on `X` consisting of sections supported on the closed subset
`Z`. -/
def closedSubsetSectionsWithSupportSubsheaf
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) : Subobject ℱ :=
  let f := openComplementRestriction hZ ℱ
  let _ : HasKernel f := HasKernels.has_limit f
  kernelSubobject f

/-- Remark 17.6.2: for an open set `U ⊆ X`, the image of the canonical inclusion
`\mathcal H_Z(\mathcal F)(U) \hookrightarrow \mathcal F(U)` is exactly the set of sections whose
support is contained in `Z ∩ U`. This is the source-facing sectionwise description of
`\mathcal H_Z(\mathcal F)`. -/
theorem closedSubsetSectionsWithSupportSubsheaf_app_range
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) (U : Opens X) :
    Set.range ((closedSubsetSectionsWithSupportSubsheaf hZ ℱ).arrow.1.app (op U)) =
      { s | abelianSheafSectionSupport ℱ s ⊆ { x : U | x.1 ∈ Z } } := by
  sorry

/-- A section of `ℱ(U)` lies in the image of `\mathcal H_Z(\mathcal F)(U)` exactly when its
support is contained in `Z ∩ U`. -/
theorem closedSubsetSectionsWithSupportSubsheaf_app_iff
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) (U : Opens X)
    (s : ℱ.presheaf.obj (op U)) :
    s ∈ Set.range ((closedSubsetSectionsWithSupportSubsheaf hZ ℱ).arrow.1.app (op U)) ↔
      abelianSheafSectionSupport ℱ s ⊆ { x : U | x.1 ∈ Z } := by
  sorry

/-- The subsheaf of sections supported in `Z` has support contained in `Z`. -/
theorem closedSubsetSectionsWithSupportSubsheaf_support_subset
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    abelianSheafSupport (closedSubsetSectionsWithSupportSubsheaf hZ ℱ) ⊆ Z := by
  sorry

/-- Any abelian subsheaf of `ℱ` whose support is contained in `Z` factors through the
sections-with-support subsheaf. -/
theorem le_closedSubsetSectionsWithSupportSubsheaf_of_support_subset
    (hZ : IsClosed Z) {ℱ : X.Sheaf AddCommGrpCat.{u}} (G : Subobject ℱ)
    (hG : abelianSheafSupport G ⊆ Z) :
    G ≤ closedSubsetSectionsWithSupportSubsheaf hZ ℱ := by
  sorry

end
