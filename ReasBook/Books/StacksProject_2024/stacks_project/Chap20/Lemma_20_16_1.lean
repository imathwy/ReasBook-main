import StacksProject_2024.Chap20.«20_15_0_1»
import StacksProject_2024.Chap20.Lemma_20_11_3
import StacksProject_2024.Chap20.OpensInstances

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

variable {X : TopCat.{u + 1}}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 2} (X.Sheaf AddCommGrpCat.{u + 1})]

/-
Domain-style sampling for Lemma 20.16.1:
- primary domain: global Čech cohomology of abelian sheaves on a topological space and its
  comparison with derived sheaf cohomology in degree `1`;
- sampled owner declarations:
  `indexedOpenCoverCechCohomologyFunctor`,
  `globalCechCohomology`,
  `exists_cech_H1_comparison_to_H1_of_isOpenCover`,
  `IsCechH1ComparisonToH1OfIsOpenCover`,
  `CategoryTheory.Sheaf.H`,
  `CategoryTheory.Limits.colimit.desc`,
  `CategoryTheory.IsIso`;
- best owner abstraction: the public owner here should be the source-facing predicate
  `IsGlobalCechH1Comparison ℱ τ` on a candidate global comparison morphism
  `τ : globalCechCohomology ℱ 1 ⟶ AddCommGrpCat.of (ℱ.H 1)`, together with the existence of a
  compatible coverwise natural transformation whose objectwise components satisfy the source-facing
  predicate `IsCechH1ComparisonToH1OfIsOpenCover` from Lemma `20.11.3`;
- primitive data: the space `X` and the abelian sheaf `ℱ`;
- derived API: the existence theorem for a global comparison morphism, the induced `IsIso`
  consequence for any such morphism, and the object-level `IsIsomorphic` corollary.

Source/core/bridge triage:
- `source-facing`: the global degree-one Čech-versus-sheaf-cohomology comparison;
- `core/canonical`: `indexedOpenCoverCechCohomologyFunctor`, `globalCechCohomology`,
  `Sheaf.H`, and `IsIso`;
- `bridge/view`: the internal cocone assembled from coverwise morphisms in
  `Lemma_20_11_3`.
-/

/-- There exists a compatible family of coverwise comparison morphisms from Lemma `20.11.3`,
assembled as a natural transformation on the indexed-open-cover diagram. This is bridge data for
the concrete global comparison morphism below. -/
theorem exists_coverwiseCechH1Comparison
    (ℱ : X.Sheaf AddCommGrpCat.{u + 1}) :
    ∃ ι : indexedOpenCoverCechCohomologyFunctor ℱ 1 ⟶
        (Functor.const (IndexedOpenCoverCat X)).obj (AddCommGrpCat.of (ℱ.H 1)),
      ∀ A : IndexedOpenCoverCat X,
        IsCechH1ComparisonToH1OfIsOpenCover
          (indexedOpenCoverFamily A) ℱ (indexedOpenCoverCechCohomologyFunctorApp ℱ 1 ι A) := by
  sorry

/-- Lemma 20.16.1: a morphism `τ : Čech H¹(X, ℱ) ⟶ H¹(X, ℱ)` is a global Čech-to-`H¹`
comparison if it descends from a compatible family of coverwise comparison morphisms from
Lemma `20.11.3`. -/
@[stacks 09V1]
def IsGlobalCechH1Comparison
    (ℱ : X.Sheaf AddCommGrpCat.{u + 1})
    (τ : globalCechCohomology ℱ 1 ⟶ AddCommGrpCat.of (ℱ.H 1)) : Prop :=
  ∃ ι : indexedOpenCoverCechCohomologyFunctor ℱ 1 ⟶
      (Functor.const (IndexedOpenCoverCat X)).obj (AddCommGrpCat.of (ℱ.H 1)),
    (∀ A : IndexedOpenCoverCat X,
      IsCechH1ComparisonToH1OfIsOpenCover
        (indexedOpenCoverFamily A) ℱ (indexedOpenCoverCechCohomologyFunctorApp ℱ 1 ι A)) ∧
      globalCechCohomologyDesc ℱ 1 ι = τ

omit [HasExt.{u + 2} (X.Sheaf AddCommGrpCat.{u + 1})] in
/-- Any compatible coverwise comparison family induces a global Čech-to-`H¹` comparison. -/
theorem IsGlobalCechH1Comparison.of_desc
    (ℱ : X.Sheaf AddCommGrpCat.{u + 1})
    (ι : indexedOpenCoverCechCohomologyFunctor ℱ 1 ⟶
      (Functor.const (IndexedOpenCoverCat X)).obj (AddCommGrpCat.of (ℱ.H 1)))
    (hι : ∀ A : IndexedOpenCoverCat X,
      IsCechH1ComparisonToH1OfIsOpenCover
        (indexedOpenCoverFamily A) ℱ (indexedOpenCoverCechCohomologyFunctorApp ℱ 1 ι A)) :
    IsGlobalCechH1Comparison ℱ (globalCechCohomologyDesc ℱ 1 ι) :=
  ⟨ι, hι, rfl⟩

/-- Lemma 20.16.1, desc form: any coverwise Čech-to-`H¹` comparison family induces an isomorphism
from global Čech cohomology to first sheaf cohomology. -/
@[stacks 09V1]
theorem globalCechH1ComparisonDesc_isIso
    (ℱ : X.Sheaf AddCommGrpCat.{u + 1})
    (ι : indexedOpenCoverCechCohomologyFunctor ℱ 1 ⟶
      (Functor.const (IndexedOpenCoverCat X)).obj (AddCommGrpCat.of (ℱ.H 1)))
    (hι : ∀ A : IndexedOpenCoverCat X,
      IsCechH1ComparisonToH1OfIsOpenCover
        (indexedOpenCoverFamily A) ℱ (indexedOpenCoverCechCohomologyFunctorApp ℱ 1 ι A)) :
    IsIso (globalCechCohomologyDesc ℱ 1 ι) := sorry

/-- Any global Čech-to-`H¹` comparison morphism is an isomorphism. -/
theorem IsGlobalCechH1Comparison.isIso
    {ℱ : X.Sheaf AddCommGrpCat.{u + 1}}
    {τ : globalCechCohomology ℱ 1 ⟶ AddCommGrpCat.of (ℱ.H 1)}
    (hτ : IsGlobalCechH1Comparison ℱ τ) :
    IsIso τ := by
  rcases hτ with ⟨ι, hι, rfl⟩
  exact globalCechH1ComparisonDesc_isIso ℱ ι hι

/-- Lemma 20.16.1: for an abelian sheaf `ℱ` on a topological space `X`, there exists a global
comparison morphism `Čech H¹(X, ℱ) ⟶ H¹(X, ℱ)` assembled from the coverwise comparisons of
Lemma `20.11.3`. -/
@[stacks 09V1]
theorem exists_globalCechH1Comparison
    (ℱ : X.Sheaf AddCommGrpCat.{u + 1}) :
    ∃ τ : globalCechCohomology ℱ 1 ⟶ AddCommGrpCat.of (ℱ.H 1),
      IsGlobalCechH1Comparison ℱ τ := by
  rcases exists_coverwiseCechH1Comparison ℱ with ⟨ι, hι⟩
  exact ⟨globalCechCohomologyDesc ℱ 1 ι, IsGlobalCechH1Comparison.of_desc ℱ ι hι⟩

/-- Lemma 20.16.1: for an abelian sheaf `ℱ` on a topological space `X`, the global
Čech cohomology object `Čech H¹(X, ℱ)` is isomorphic to the first sheaf cohomology group
`H¹(X, ℱ)`. -/
@[stacks 09V1]
theorem globalCechH1_isomorphic_sheafCohomology
    (ℱ : X.Sheaf AddCommGrpCat.{u + 1}) :
    IsIsomorphic (globalCechCohomology ℱ 1) (AddCommGrpCat.of (ℱ.H 1)) := by
  rcases exists_globalCechH1Comparison ℱ with ⟨τ, hτ⟩
  letI : IsIso τ := hτ.isIso
  exact ⟨asIso τ⟩

end Sheaf
end CategoryTheory
