import Mathlib
import stacks_proof.stacks_project.Chap14.Definition_14_22_3
import stacks_proof.stacks_project.Chap14.Lemma_14_23_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open AlgebraicTopology.DoldKan
open Abelian.DoldKan
open HomologicalComplex
open scoped Simplicial DoldKan

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Lemma 14.23.3:
- primary domain: Dold-Kan/Eilenberg-MacLane homology computations in an abelian category.
- sampled owner declarations:
  `HomotopyEquiv.toHomologyIso`,
  `eilenbergMacLaneObjectNormalizedMooreComplexIsoSingle`,
  `HomologicalComplex.singleObjHomologySelfIso`,
  `HomologicalComplex.isZero_single_obj_homology`.
- best owner abstraction: the canonical homology isomorphism from `s[K(A, k)]` to the single
  complex concentrated in degree `k`, obtained by composing the Dold-Kan homotopy-equivalence
  homology isomorphism with the canonical normalized-Moore comparison isomorphism.
- primitive data: the simplicial Eilenberg-MacLane object `K(A, k)` and the chapter bridge
  `eilenbergMacLaneObjectNormalizedMooreComplexIsoSingle`.
- derived API: the degree-`k` homology isomorphism and the off-degree vanishing theorem.

Source/core/bridge triage:
- `source-facing`: the textbook claims `H_k(s(K(A, k))) ≅ A` and `H_i(s(K(A, k))) = 0` for
  `i ≠ k`.
- `core/canonical`: `HomotopyEquiv.toHomologyIso`, `homologyFunctor.mapIso`,
  `HomologicalComplex.singleObjHomologySelfIso`, and
  `HomologicalComplex.isZero_single_obj_homology`.
- `bridge/view`: the chapter comparison from `N(K(A, k))` to the single complex
  concentrated in degree `k`.

The file should therefore expose the canonical homology isomorphism as the main owner and derive
the source-facing vanishing API from it, rather than storing a parallel raw comparison morphism.
-/

/-- Lemma 14.23.3 (1): the canonical isomorphism from `H_k(s(K(A, k)))` to `A`. -/
@[stacks 0197]
noncomputable def eilenbergMacLaneObject_homologyIso (A : 𝒜) (k : ℕ) :
    s[K(A, k)].homology k ≅ A :=
  let e :
      HomotopyEquiv ((normalizedMooreComplex 𝒜).obj (K(A, k))) s[K(A, k)] :=
    homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
  (e.toHomologyIso k).symm ≪≫
    (homologyFunctor 𝒜 (ComplexShape.down ℕ) k).mapIso
      (eilenbergMacLaneObjectNormalizedMooreComplexIsoSingle A k) ≪≫
    singleObjHomologySelfIso (ComplexShape.down ℕ) k A

-- Proof sketch: pass from the alternating face map complex to the normalized Moore complex via
-- the Dold-Kan homotopy equivalence, identify the normalized Moore complex of `K(A,k)` with the
-- single complex concentrated in degree `k`, and then use
-- `HomologicalComplex.isZero_single_obj_homology` away from degree `k`.
/-- Lemma 14.23.3 (2): for `i ≠ k`, the homology object `H_i(s(K(A, k)))` is zero. -/
@[stacks 0197]
theorem eilenbergMacLaneObject_homology_isZero
    (A : 𝒜) (k i : ℕ) (h : i ≠ k) :
    IsZero (s[K(A, k)].homology i) := by
  let e :
      HomotopyEquiv ((normalizedMooreComplex 𝒜).obj (K(A, k))) s[K(A, k)] :=
    homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
  refine IsZero.of_iso ?_ ((e.toHomologyIso i).symm ≪≫
    (homologyFunctor 𝒜 (ComplexShape.down ℕ) i).mapIso
      (eilenbergMacLaneObjectNormalizedMooreComplexIsoSingle A k))
  exact isZero_single_obj_homology (ComplexShape.down ℕ) k A i h

end CategoryTheory
