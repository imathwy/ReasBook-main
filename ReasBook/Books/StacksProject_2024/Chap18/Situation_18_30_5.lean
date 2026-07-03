import Mathlib
import StacksProject_2024.Chap07.Lemma_7_17_7

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
  `SemiRepresentableFamily.Over`,
  `SemiRepresentableFamily.Over.toSieve`,
  `GrothendieckTopology.QuasiCompactObject`,
  `GrothendieckTopology.HasQuasiCompactPairwiseOverlaps`;
- source-facing layer: the Stacks-project situation asserting a quasi-compact basis with
  quasi-compact fiber products;
- core/canonical owners already present upstream for the derived consequences:
  `J.QuasiCompactObject U` and `J.HasQuasiCompactPairwiseOverlaps 𝒰`;
- bridge/view layer here: `𝒰.toSieve ∈ J U`, expressing a source-facing covering family through
  the canonical generated sieve.

Primitive data are a covering family by basis objects, quasi-compactness of basis objects, and
existence of pairwise fibre products for such a chosen family. The quasi-compactness of those
overlaps is derived through the Chapter 7 owner `J.HasQuasiCompactPairwiseOverlaps 𝒰` rather than
being restated entrywise. The stronger cover-sieve owner
`J.HasEnoughObjectsWithProperty (· ∈ B)` is not source-faithful here: it speaks about every arrow
in a covering sieve, while the Stacks situation only asks for one chosen covering family and
pairwise overlaps inside that family.
-/

/-- Situation 18.30.5: a subset `B` of objects of a site `(C, J)` such that every object of `C`
admits a `J`-covering family by objects of `B`, every object of `B` is quasi-compact, and for any
covering family of an object `U ∈ B` by objects of `B`, the fibre products of any two members of
that chosen family exist and are quasi-compact. -/
class HasQuasiCompactBasisWithQuasiCompactFiberProducts (B : Set C) where
  /-- Every object admits a source-facing covering family by objects of `B`. -/
  cover_by_basis :
    ∀ U : C, ∃ 𝒰 : SemiRepresentableFamily.Over.{v, u, max u v} U,
      𝒰.toSieve ∈ J U ∧ ∀ i, (𝒰.obj i).left ∈ B
  /-- Each object of the chosen basis `B` is quasi-compact for the topology `J`. -/
  basis_quasiCompact (U : C) (hU : U ∈ B) :
    J.QuasiCompactObject U
  /-- If `U ∈ B` and `𝒰` is a covering family of `U` whose members lie in `B`, then the chosen
  family has pairwise fibre products and those canonical overlaps are quasi-compact. -/
  hasQuasiCompactPairwiseOverlaps
      (U : C) (hU : U ∈ B)
      (𝒰 : SemiRepresentableFamily.Over.{v, u, max u v} U) (h𝒰 : 𝒰.toSieve ∈ J U)
      (h𝒰B : ∀ i, (𝒰.obj i).left ∈ B) :
      ∃ hpair : 𝒰.toPresieve.HasPairwisePullbacks,
        let _ : 𝒰.toPresieve.HasPairwisePullbacks := hpair
        J.HasQuasiCompactPairwiseOverlaps 𝒰

end CategoryTheory.GrothendieckTopology
