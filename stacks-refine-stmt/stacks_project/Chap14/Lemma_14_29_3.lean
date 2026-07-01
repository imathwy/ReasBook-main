import Mathlib
import stacks_project.Chap14.Lemma_14_27_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicTopology
open AlgebraicTopology.DoldKan

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {U V : SimplicialObject A} {a b : U ⟶ V}

/-
Domain-style sampling:
- primary domain: simplicial homotopies and their image on normalized Moore complexes under the
  Dold-Kan comparison;
- sampled owner declarations:
  `CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy`,
  `CategoryTheory.SimplicialObject.Homotopy.toNormalizedMooreComplexHomotopy`,
  `inclusionOfMooreComplexMap`,
  `PInftyToNormalizedMooreComplex`;
- best owner abstraction: the canonical owner abstraction for the derived normalized-Moore chain
  homotopy is `Homotopy.toNormalizedMooreComplexHomotopy`, built from the core owner
  `Homotopy.toChainHomotopy` and the Dold-Kan comparison maps;
- primitive data: a simplicial homotopy `H : Homotopy a b`;
- derived API: the induced normalized-Moore chain homotopy
  `H.toNormalizedMooreComplexHomotopy`, with its degreewise comparison formula.

Source/core/bridge triage:
- `source-facing`: existence of a simplicial homotopy lifting a prescribed normalized-Moore chain
  homotopy;
- `core/canonical`: `Homotopy.toChainHomotopy`;
- `bridge/view`: `Homotopy.toNormalizedMooreComplexHomotopy`.
-/

-- Proof sketch: form the Stacks cylinder object for `N(U)` as in Lemma 14.29.1 and use the
-- factorization result of Lemma 14.29.2 to lift the given chain homotopy to a simplicial homotopy
-- `H : Homotopy a b`. The lifted homotopy is then identified with the prescribed normalized-Moore
-- chain homotopy through the canonical bridge owner
-- `Homotopy.toNormalizedMooreComplexHomotopy`.
/-- Lemma 14.29.3: every chain homotopy between the normalized Moore maps `N(a)` and `N(b)` comes
from a simplicial homotopy `H : a ⟶ b`, and the given chain homotopy is exactly the canonical
normalized-Moore homotopy induced by `H`. -/
theorem exists_simplicialHomotopy_of_normalizedMooreComplexHomotopy
    (N : _root_.Homotopy ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b)) :
    ∃ H : Homotopy a b,
      N = H.toNormalizedMooreComplexHomotopy := sorry

/-- Degreewise reformulation of Lemma 14.29.3 via the canonical owner
`Homotopy.toNormalizedMooreComplexHomotopy`. -/
theorem exists_simplicialHomotopy_of_normalizedMooreComplexHomotopy_hom
    (N : _root_.Homotopy ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b)) :
    ∃ H : Homotopy a b,
      ∀ n : ℕ,
        N.hom n (n + 1) =
          (inclusionOfMooreComplexMap U).f n ≫ H.toChainHomotopy.hom n (n + 1) ≫
            (PInftyToNormalizedMooreComplex V).f (n + 1) := by
  rcases exists_simplicialHomotopy_of_normalizedMooreComplexHomotopy N with ⟨H, hH⟩
  refine ⟨H, fun n ↦ ?_⟩
  rw [hH]
  simpa using H.toNormalizedMooreComplexHomotopy_hom n

end CategoryTheory.SimplicialObject
