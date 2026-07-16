import StacksProject_2024.stacks_project.Chap13.Definition_13_37_1
import StacksProject_2024.stacks_project.Chap20.Global_sections_cohomology_delta_functor
import StacksProject_2024.stacks_project.Chap20.Lemma_20_11_5
import StacksProject_2024.stacks_project.Chap20.Definition_20_49_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable [CompactSpace X.carrier] [PrespectralSpace X.carrier] [QuasiSeparatedSpace X.carrier]

local notation "DMod" => ModuleDerived X
local notation "plusι" => ObjectProperty.ι (t.plus : ObjectProperty DMod)

/- Domain-style sampling for Lemma 20.53.2:
- primary domain: perfect objects and compactness/coproduct preservation in `D(𝒪_X)` and
  its bounded-below subcategory;
- sampled owner declarations:
  `CategoryTheory.IsCompactObject`,
  `CategoryTheory.isCompactObject_iff`,
  `DerivedCategory.IsPerfect`,
  `globalCohomologyDeltaFunctor`,
  `globalCohomologyDegree_obj_eq_moduleCohomologyAtOpen`,
  `t.plus`;
- best owner abstraction: the intrinsic perfectness predicate is already owned by
  `DerivedCategory.IsPerfect`, compactness in the ambient derived category is already owned by
  `CategoryTheory.IsCompactObject`, the finite-cohomological-dimension input in part `(2)` is
  canonically owned by the global-sections cohomological `δ`-functor
  `globalCohomologyDeltaFunctor X`, with
  `globalCohomologyDegree_obj_eq_moduleCohomologyAtOpen` as the degreewise bridge to the top-open
  module cohomology owner, and the bounded-below subcategory is canonically cut out by the
  `t`-structure owner `t.plus`; the first theorem is therefore a `bridge/view` statement about the
  inclusion `plusι`, while the second theorem is the source-facing compactness statement itself;
- primitive data: the ringed space `X`, the perfect object `K`, and the cohomological-dimension
  hypothesis in part `(2)`;
- derived API: the represented-Hom coproduct preservation statement on `D⁺(𝒪_X)` and
  the resulting compactness statement in `D(𝒪_X)`.

Source/core/bridge triage:
- `source-facing`: `perfect_isCompactObject_of_finiteCohomologicalDimension`;
- `core/canonical`: `DerivedCategory.IsPerfect`, `IsCompactObject`, and `t.plus`;
- `bridge/view`: `perfect_preserves_boundedBelowCoproducts`, expressed through the canonical
  inclusion `plusι`. -/

-- Proof sketch: let `Kᵛ` be the derived dual of `K` from Lemma `20.50.5`. For bounded-below
-- objects, the functor `- ⊗^L Kᵛ` preserves arbitrary direct sums, and Lemma `20.19.1` together
-- with Lemma `20.53.1` shows that `RΓ(X, -)` preserves those same direct sums under the stated
-- topological hypotheses. The identification
-- `Hom_{D(𝒪_X)}(K, M) ≅ H⁰(X, Kᵛ ⊗^L M)` then gives preservation of coproducts by `Hom(K, -)` on
-- `D⁺(𝒪_X)`.
/-- Lemma 20.53.2 (1): if the underlying topological space of the ringed space `X` is
quasi-compact, has a basis of quasi-compact opens, and intersections of quasi-compact opens are
quasi-compact, then for a perfect object `K` of `D(𝒪_X)` the functor `Hom_{D(𝒪_X)}(K, -)`
preserves arbitrary direct sums on the bounded-below derived subcategory `D⁺(𝒪_X)`. -/
@[stacks 09J7]
theorem perfect_preserves_boundedBelowCoproducts
    (K : DMod) (hK : DerivedCategory.IsPerfect K) (I : Type v) :
    PreservesColimitsOfShape (Discrete I) (plusι ⋙ preadditiveCoyoneda.obj (op K)) := sorry

section

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasInjectiveResolutions (Modules X)]

-- Proof sketch: apply part `(1)` to reduce compactness to the preservation of direct sums by
-- `RΓ(X, -)` on all of `D(𝒪_X)`. The finite cohomological-dimension hypothesis is
-- expressed on the source-facing Chapter 20 owner `globalCohomologyDeltaFunctor X`; the degreewise
-- bridge `globalCohomologyDegree_obj_eq_moduleCohomologyAtOpen` identifies this with the
-- top-open module cohomology owner used elsewhere, and Lemma `20.13.3` then matches that with
-- the underlying-abelian-sheaf cohomology on `X`.
-- In the Grothendieck context used for the proof, this is the top-open input for the compactness
-- bridge of Lemma `20.53.1`, upgrading the bounded-below statement to compactness in the full
-- derived category.
/-- Lemma 20.53.2 (2): under the same topological hypotheses, if there exists an integer `d` such
that `H^i(X, ℱ) = 0` for all `i > d` and all `𝒪_X`-modules `ℱ`, then every perfect object `K` of
`D(𝒪_X)` is a compact object of `D(𝒪_X)`. -/
@[stacks 09J7]
theorem perfect_isCompactObject_of_finiteCohomologicalDimension
    (K : DMod) (hK : DerivedCategory.IsPerfect K)
    (hcd :
      ∃ d : ℤ,
        ∀ p : ℕ, d < p → ∀ ℱ : Modules X,
          IsZero (((globalCohomologyDeltaFunctor X p).obj).obj ℱ)) :
    IsCompactObject K := sorry

/-- The canonical top-open cohomology reformulation of Lemma 20.53.2 (2), obtained from the
source-facing `globalCohomologyDeltaFunctor X` statement via
`globalCohomologyDegree_obj_eq_moduleCohomologyAtOpen`. -/
theorem perfect_isCompactObject_of_finiteCohomologicalDimension_of_moduleCohomologyAtOpen
    (K : DMod) (hK : DerivedCategory.IsPerfect K)
    (hcd :
      ∃ d : ℤ,
        ∀ p : ℕ, d < p → ∀ ℱ : Modules X,
          IsZero (moduleCohomologyAtOpen (⊤ : Opens X.carrier) ℱ p)) :
    IsCompactObject K := by
  apply perfect_isCompactObject_of_finiteCohomologicalDimension K hK
  rcases hcd with ⟨d, hd⟩
  refine ⟨d, ?_⟩
  intro p hp ℱ
  simpa [globalCohomologyDegree_obj_eq_moduleCohomologyAtOpen X ℱ p] using hd p hp ℱ

end

end

end AlgebraicGeometry.RingedSpace
