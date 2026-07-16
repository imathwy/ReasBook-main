import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_5_1
import StacksProject_2024.stacks_project.Chap28.Lemma_28_5_12
import StacksProject_2024.stacks_project.Chap29.Definition_29_50_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent]

-- Semantic recall: `lean_leansearch` surfaced the generic-point API
-- `genericPoints.ofComponent`/`genericPoints.isGenericPoint_ofComponent`, while local Chapter 17
-- and Chapter 31 owner search confirmed the source-facing scheme-module owners `moduleSupport`,
-- `Scheme.Modules.weakAss`, and `Scheme.weakAss`.

/-- Lemma 31.5.7 (1): every minimal specialization point of the support of a quasi-coherent
`\mathcal O_X`-module `\mathcal F` is weakly associated to `\mathcal F`. This records the source
phrase “a point of `Supp(ℱ)` that is not the specialization of any other point of `Supp(ℱ)`”
through the Chapter 28 owner `X.minimalSpecializationPoints (moduleSupport ℱ)`. -/
theorem minimalSpecializationPoints_moduleSupport_subset_weakAss :
    X.minimalSpecializationPoints (moduleSupport ℱ) ⊆ ℱ.weakAss := sorry

/-- Pointwise form of `minimalSpecializationPoints_moduleSupport_subset_weakAss`. -/
theorem mem_weakAss_of_mem_minimalSpecializationPoints_moduleSupport {x : X}
    (hx : x ∈ X.minimalSpecializationPoints (moduleSupport ℱ)) :
    x ∈ ℱ.weakAss :=
  minimalSpecializationPoints_moduleSupport_subset_weakAss ℱ hx

/-- Lemma 31.5.7 (1): if `x` lies in the support of a quasi-coherent `\mathcal O_X`-module
`\mathcal F` and is not the specialization of any other point of `\operatorname{Supp}(\mathcal
F)`, then `x` is weakly associated to `\mathcal F`. -/
theorem mem_weakAss_of_support_minimal {x : X} (hx : x ∈ moduleSupport ℱ)
    (hminimal : ¬ ∃ y : X, y ∈ moduleSupport ℱ ∩ ({x} : Set X)ᶜ ∧ y ⤳ x) :
    x ∈ ℱ.weakAss := by
  apply mem_weakAss_of_mem_minimalSpecializationPoints_moduleSupport ℱ
  rw [Scheme.mem_minimalSpecializationPoints_iff X]
  constructor
  · exact hx
  · intro y hy hyx
    by_contra hne
    exact hminimal ⟨y, ⟨hy, by simpa [Set.mem_compl_iff] using hne⟩, hyx⟩

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- Lemma 31.5.7 (2): the generic points of irreducible components of a scheme `X` are weakly
associated to the structure sheaf `\mathcal O_X`. -/
theorem genericPointsOfIrreducibleComponents_subset_weakAss :
    genericPointsOfIrreducibleComponents X ⊆ X.weakAss := sorry

/-- Pointwise generic-point form of
`genericPointsOfIrreducibleComponents_subset_weakAss`. -/
theorem genericPoint_mem_weakAss (Z : irreducibleComponents X) {x : X}
    (hx : IsGenericPoint x (Z : Set X)) :
    x ∈ X.weakAss := by
  apply genericPointsOfIrreducibleComponents_subset_weakAss X
  rw [mem_genericPointsOfIrreducibleComponents_iff]
  have hgp : IsGenericPoint (genericPoints.ofComponent Z : X) (Z : Set X) :=
    genericPoints.isGenericPoint_ofComponent Z
  have hxeq : x = genericPoints.ofComponent Z := IsGenericPoint.eq hx hgp
  simpa [hxeq] using (genericPoints.ofComponent Z).2

end AlgebraicGeometry.Scheme
