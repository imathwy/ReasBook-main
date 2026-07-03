import Mathlib
import StacksProject_2024.Chap04.Lemma_4_22_3
import StacksProject_2024.Chap12.Lemma_12_30_2

open CategoryTheory
open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {I : Type u₁} [Category.{v₁} I] [IsFiltered I]
variable {A : Type u₂} [Category.{v₂} A] [HasZeroMorphisms A] [HasBinaryBiproducts A]
variable [IsIdempotentComplete A]

/- Domain-style sampling for Lemma 12.30.3 in the filtered additive-diagram domain:
- sampled chapter/mathlib declarations:
  * `IsEssentiallyConstantFilteredDiagram`
  * `IsEssentiallyConstantFilteredCocone`
  * `essentiallyConstantFilteredDiagram_exists_essentiallyConstant_colimitCocone`
  * `Limits.hasColimit_biprod_iff`
  * `Limits.colimit_biprod_iso`

Primitive-vs-derived split:
- primitive source-facing data: essentially constant cocones on `F`, `G`, and `F ⊞ G`
- derived API used in the proof: the canonical colimit cocones supplied by
  `essentiallyConstantFilteredDiagram_exists_essentiallyConstant_colimitCocone` and the biproduct
  colimit comparison from Lemma 12.30.2

Source/core/bridge triage:
- `source-facing`: `essentiallyConstantFilteredDiagram_biprod_iff`, the Chapter 12 closure theorem
  for the Chapter 4 owner predicate `IsEssentiallyConstantFilteredDiagram`
- `core/canonical`: the owner predicate `IsEssentiallyConstantFilteredDiagram`
- `bridge/view`: the internal cocone-level transport to the canonical biproduct colimit vertex in
  the reverse implication; no separate public `HasEventuallySplitColimit` bridge is retained here

The refinement therefore keeps the public statement directly at the owner level and at the minimal
binary-biproduct assumption layer already used by `Limits.hasColimit_biprod_iff`, instead of
routing the file through a parallel split-colimit theorem or a local finite-biproduct bridge. -/

/-- Lemma 12.30.3: in the canonical owner predicate
`IsEssentiallyConstantFilteredDiagram`, the pointwise direct-sum diagram `F ⊞ G` is essentially
constant if and only if both `F` and `G` are essentially constant. -/
theorem essentiallyConstantFilteredDiagram_biprod_iff (F G : I ⥤ A) :
    IsEssentiallyConstantFilteredDiagram (F ⊞ G) ↔
      IsEssentiallyConstantFilteredDiagram F ∧ IsEssentiallyConstantFilteredDiagram G := by
  constructor
  · intro hFG
    obtain ⟨c, hc⟩ :=
      essentiallyConstantFilteredDiagram_exists_essentiallyConstant_colimitCocone (F ⊞ G) hFG
    letI : HasColimit (F ⊞ G) := HasColimit.mk c
    have hcol := (Limits.hasColimit_biprod_iff F G).mp inferInstance
    letI : HasColimit F := hcol.1
    letI : HasColimit G := hcol.2
    -- Transport the essentially constant colimit cocone on `F ⊞ G` to the canonical vertex
    -- `colimit F ⊞ colimit G` via `Limits.colimit_biprod_iso`, then project the source-facing
    -- section/factorization data to the two summand cocones.
    sorry
  · rintro ⟨hF, hG⟩
    obtain ⟨cF, hcF⟩ :=
      essentiallyConstantFilteredDiagram_exists_essentiallyConstant_colimitCocone F hF
    obtain ⟨cG, hcG⟩ :=
      essentiallyConstantFilteredDiagram_exists_essentiallyConstant_colimitCocone G hG
    -- Combine the two essentially constant colimit cocones into a cocone on the pointwise
    -- biproduct diagram `F ⊞ G`; filteredness supplies a common distinguished stage and a common
    -- eventual target for the componentwise factorization data.
    sorry

end

end CategoryTheory
