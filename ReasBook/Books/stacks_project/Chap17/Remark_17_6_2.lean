import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap17.Definition_17_5_1
import stacks_project.Chap17.Lemma_17_6_3

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open scoped ClosedSubsetSectionsWithSupport

noncomputable section

universe u

section

variable {X : TopCat.{u}} {Z : Set X}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/- Domain-style sampling for Remark 17.6.2:
- primary domain: abelian sheaves on a closed subset and the canonical sections-with-support
  right adjoint to closed-subset pushforward;
- sampled owner declarations:
  `abelianSheafSectionSupport`,
  `closedSubsetOpenComplementRestriction`,
  `TopCat.closedSubsetInclusion`,
  `closedSubsetSectionsWithSupportSubsheaf`,
  `closedSubsetSectionsWithSupportFunctor`;
- owner abstraction: the chapter owner is
  `𝓗[hZ]`, together with its object part
  `closedSubsetSectionsWithSupportSubsheaf hZ ℱ`;
- primitive data: the closed subset `Z`, its closedness proof `hZ`, and the canonical kernel model
  already supplied by Lemma 17.6.3, plus the local-section support notion
  `abelianSheafSectionSupport`;
- derived API: the sectionwise support characterization of that owner, its support-containment and
  universal-factorization properties, and the left exactness of the canonical
  `Ab(X) ⥤ Ab(Z)` functor.

Source/core/bridge triage:
- `source-facing`: the Stacks remark that `𝒢 = 𝒥_Z(ℱ)` is the subsheaf of sections supported in
  `Z`, i.e. `𝒢(U) = { s ∈ ℱ(U) | support(s) ⊆ Z ∩ U }`, together with its support-based
  universal property;
- `core/canonical`: `TopCat.closedSubsetInclusion X Z` and the owner
  `𝓗[hZ]` from Lemma 17.6.3;
- `bridge/view`: this file adds the support-theoretic characterization of the existing owner rather
  than introducing a second `X`-valued functorial implementation of `𝒥_Z`. -/

/- Lemma 17.6.3 provides the canonical kernel-model owner for sections with support in `Z`,
together with the adjunction `i_* ⊣ 𝓗[hZ]`. -/
recall closedSubsetSectionsWithSupportSubsheaf
recall closedSubsetSectionsWithSupportSheaf
recall closedSubsetSectionsWithSupportFunctor
recall closedSubset_pushforwardSectionsWithSupportAdjunction

-- Proof sketch: a section of `ℱ(U)` lies in the kernel of the restriction to the open complement
-- exactly when its germs vanish at every point of `U ∩ Zᶜ`; by the definition of section support,
-- this is equivalent to the support being contained in `Z ∩ U`.
/-- Remark 17.6.2: for an open set `U ⊆ X`, the image of the canonical inclusion
`\mathcal H_Z(\mathcal F)(U) \hookrightarrow \mathcal F(U)` is exactly the set of sections whose
support is contained in `Z ∩ U`. This is the source-facing sectionwise description of
`\mathcal H_Z(\mathcal F)`. -/
theorem closedSubsetSectionsWithSupportSubsheaf_app_range
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) (U : Opens X) :
    Set.range ((closedSubsetSectionsWithSupportSubsheaf hZ ℱ).arrow.1.app (op U)) =
      { s | abelianSheafSectionSupport ℱ s ⊆ { x : U | x.1 ∈ Z } } := sorry

/-- A section of `ℱ(U)` lies in the image of `\mathcal H_Z(\mathcal F)(U)` exactly when its
support is contained in `Z ∩ U`. -/
theorem closedSubsetSectionsWithSupportSubsheaf_app_iff
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) (U : Opens X)
    (s : ℱ.presheaf.obj (op U)) :
    s ∈ Set.range ((closedSubsetSectionsWithSupportSubsheaf hZ ℱ).arrow.1.app (op U)) ↔
      abelianSheafSectionSupport ℱ s ⊆ { x : U | x.1 ∈ Z } := by
  simp [closedSubsetSectionsWithSupportSubsheaf_app_range hZ ℱ U]

-- Proof sketch: at points of the open complement, the unit
-- `ℱ ⟶ j_* j⁻¹ ℱ` is an isomorphism on stalks, so the kernel stalk is zero there. Hence the
-- support of the kernel subsheaf is contained in the closed complement `Z`.
/-- The subsheaf of sections supported in `Z` has support contained in `Z`. -/
theorem closedSubsetSectionsWithSupportSubsheaf_support_subset
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    abelianSheafSupport (closedSubsetSectionsWithSupportSubsheaf hZ ℱ) ⊆ Z := sorry

-- Proof sketch: if a subsheaf `G ⊆ ℱ` is supported inside `Z`, then its restriction to the open
-- complement vanishes. Therefore the inclusion `G ⟶ ℱ` factors through the kernel of
-- `ℱ ⟶ j_* j⁻¹ ℱ`, which is exactly `closedSubsetSectionsWithSupportSubsheaf hZ ℱ`.
/-- Any abelian subsheaf of `ℱ` whose support is contained in `Z` factors through the
sections-with-support subsheaf. -/
theorem le_closedSubsetSectionsWithSupportSubsheaf_of_support_subset
    (hZ : IsClosed Z) {ℱ : X.Sheaf AddCommGrpCat.{u}} (G : Subobject ℱ)
    (hG : abelianSheafSupport G ⊆ Z) :
    G ≤ closedSubsetSectionsWithSupportSubsheaf hZ ℱ := sorry

variable (hZ : IsClosed Z)

local instance : Functor.IsRightAdjoint (𝓗[hZ]) :=
  (closedSubset_pushforwardSectionsWithSupportAdjunction hZ).isRightAdjoint

/- Remark 17.6.2: the canonical sections-with-support functor
`\mathcal H_Z : Ab(X) \to Ab(Z)` is left exact. This is the canonical owner form
`PreservesFiniteLimits (𝓗[hZ])`, obtained from the right-adjoint structure of `𝓗[hZ]`. -/
#synth PreservesFiniteLimits (𝓗[hZ])

end
