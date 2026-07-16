import Mathlib
import stacks_proof.stacks_project.Chap07.Definition_7_40_2
import stacks_proof.stacks_project.Chap07.Lemma_7_17_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.SemiRepresentableFamily.Over

universe u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)

/- Domain-style sampling for Situation 18.30.5:
- primary domain: Grothendieck-topology basis conditions on site objects;
- sampled owner abstractions:
  `GrothendieckTopology.HasEnoughObjectsWithProperty`,
  `SemiRepresentableFamily.Over`,
  `SemiRepresentableFamily.Over.toSieve`,
  `GrothendieckTopology.QuasiCompactObject`,
  `GrothendieckTopology.HasQuasiCompactPairwiseOverlaps`;
- source-facing layer: the Stacks-project situation asserting a quasi-compact basis with
  quasi-compact fiber products;
- core/canonical owners already present upstream for the primitive basis data:
  `J.HasEnoughObjectsWithProperty (· ∈ B)`, `J.QuasiCompactObject U`, and
  `J.HasQuasiCompactPairwiseOverlaps 𝒰`;
- bridge/view layer here: `𝒰.toSieve ∈ J U`, expressing a source-facing covering family through
  the canonical generated sieve when formulating the overlap hypothesis on an explicit family.

Primitive data are that the site has enough objects in `B`, quasi-compactness of basis objects,
and the existence of pairwise fibre products for any explicit `B`-cover of a basis object. The
quasi-compactness of those overlaps is derived through the Chapter 7 owner
`J.HasQuasiCompactPairwiseOverlaps 𝒰` rather than being restated entrywise. The cover-existence
layer is already canonically owned by `J.HasEnoughObjectsWithProperty (· ∈ B)`, so this situation
should reuse that owner directly and only add the genuinely extra quasi-compactness and overlap
hypotheses.
-/

/-- Situation 18.30.5: a subset `B` of objects of a site `(C, J)` such that every object of `C`
admits a `J`-cover by objects of `B`, every object of `B` is quasi-compact, and for any covering
family of an object `U ∈ B` by objects of `B`, the fibre products of any two members of that
chosen family exist and are quasi-compact. -/
@[stacks 0937]
class HasQuasiCompactBasisWithQuasiCompactFiberProducts (B : Set C) : Prop where
  /-- Every object admits a `J`-cover whose members lie in `B`. -/
  hasEnoughObjectsWithProperty :
    J.HasEnoughObjectsWithProperty (· ∈ B)
  /-- Each object of the chosen basis `B` is quasi-compact for the topology `J`. -/
  quasiCompactObject {U : C} (hU : U ∈ B) :
    J.QuasiCompactObject U
  /-- If `U ∈ B` and `𝒰` is a covering family of `U` whose members lie in `B`, then the chosen
  family has pairwise fibre products and those canonical overlaps are quasi-compact. -/
  hasQuasiCompactPairwiseOverlaps
      {U : C} (hU : U ∈ B)
      (𝒰 : SemiRepresentableFamily.Over.{v, u, max u v} U) (h𝒰 : 𝒰.toSieve ∈ J U)
      (h𝒰B : ∀ i, (𝒰.obj i).left ∈ B) :
      ∃ hpair : 𝒰.toPresieve.HasPairwisePullbacks,
        let _ : 𝒰.toPresieve.HasPairwisePullbacks := hpair
        J.HasQuasiCompactPairwiseOverlaps 𝒰

end CategoryTheory.GrothendieckTopology
