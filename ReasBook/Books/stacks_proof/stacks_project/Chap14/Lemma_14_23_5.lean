import Mathlib
import StacksProject_2024.Chap14.Definition_14_22_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open Abelian.DoldKan
open HomologicalComplex
open scoped Simplicial

noncomputable section

universe v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Lemma 14.23.5:
- primary domain: the Dold-Kan equivalence for simplicial objects in an abelian category and the
  degreewise behavior of the single chain complex;
- sampled same-kind declarations:
  `eilenbergMacLaneObjectNormalizedMooreComplexIsoSingle`,
  `eilenbergMacLaneObjectIsoDoldKanSingle`,
  `Functor.mapIso`,
  `HomologicalComplex.singleObjXSelf`,
  `HomologicalComplex.isZero_single_obj_X`;
- best owner abstraction:
  `source-facing`: the degreewise comparison of the normalized Moore complex of `K(A, k)` with the
    single complex concentrated in degree `k`;
  `core/canonical`: the chapter owner
    `eilenbergMacLaneObjectNormalizedMooreComplexIsoSingle A k` together with the single-complex
    degree isomorphism;
  `bridge/view`: the degree-`k` objectwise iso and the off-degree vanishing statement below.
- primitive data: only `A` and `k`;
- derived API: the degree-`k` iso and the off-degree zero object result.

This file is therefore a `bridge/view` refinement: it should reuse the canonical normalized-Moore
comparison and single-complex owners directly, rather than duplicating the Dold-Kan comparison
chain locally. -/

-- Proof sketch: the Dold-Kan counit identifies the normalized Moore complex of the simplicial
-- Eilenberg-MacLane object with the chain complex concentrated in degree `k`, and
-- `singleObjXSelf` identifies that degree-`k` term with `A`.
/-- Lemma 14.23.5 (1): the degree-`k` object of the normalized Moore complex of `K(A, k)` is
canonically isomorphic to `A`. -/
@[stacks 0199]
noncomputable def eilenbergMacLaneObjectNormalizedMooreComplexXSelfIso
    (A : 𝒜) (k : ℕ) :
    ((normalizedMooreComplex 𝒜).obj (K(A, k))).X k ≅ A :=
  (HomologicalComplex.eval 𝒜 (ComplexShape.down ℕ) k).mapIso
      (eilenbergMacLaneObjectNormalizedMooreComplexIsoSingle A k) ≪≫
    singleObjXSelf (ComplexShape.down ℕ) k A

-- Proof sketch: the Dold-Kan counit identifies `N(K(A,k))` with the chain complex concentrated in
-- degree `k`, and `isZero_single_obj_X` shows that every other degree of that
-- single complex is zero.
/-- Lemma 14.23.5 (2): for `i ≠ k`, the degree-`i` object of the normalized Moore complex of
`K(A, k)` is zero. -/
@[stacks 0199]
theorem eilenbergMacLaneObjectNormalizedMooreComplexXIsZero
    (A : 𝒜) (k i : ℕ) (h : i ≠ k) :
    IsZero (((normalizedMooreComplex 𝒜).obj (K(A, k))).X i) := by
  let e : ((normalizedMooreComplex 𝒜).obj (K(A, k))).X i ≅
      (((single 𝒜 (ComplexShape.down ℕ) k).obj A).X i) :=
    (HomologicalComplex.eval 𝒜 (ComplexShape.down ℕ) i).mapIso
        (eilenbergMacLaneObjectNormalizedMooreComplexIsoSingle A k)
  exact (isZero_single_obj_X (ComplexShape.down ℕ) k A i h).of_iso e

end CategoryTheory
