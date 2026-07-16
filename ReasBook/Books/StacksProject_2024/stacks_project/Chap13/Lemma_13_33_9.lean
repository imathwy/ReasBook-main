import Mathlib
import Mathlib.Algebra.Category.Grp.AB
import StacksProject_2024.stacks_project.Chap13.Lemma_13_33_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Opposite

noncomputable section

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]

/- Domain-style sampling for Lemma 13.33.9:
- primary domain: represented Hom functors on triangulated categories and sequential homotopy
  colimits;
- sampled owner declarations:
  `CategoryTheory.homologicalFunctor_hocolim_comparison`,
  `CategoryTheory.homologicalFunctor_hocolim_comparison_is_iso`,
  `CategoryTheory.IsHomotopyColimitOf`,
  `CategoryTheory.preadditiveCoyoneda.obj`;
- best owner abstraction: the Chapter 13 bridge owner
  `homologicalFunctor_hocolim_comparison`, specialized to the represented functor
  `preadditiveCoyoneda.obj (op K)`;
- primitive-vs-derived split:
  the primitive data are the sequential diagram `L₀ ⟶ L₁ ⟶ L₂ ⟶ ⋯` and a distinguished telescope
  triangle presenting `Lhocolim`;
  the Hom comparison map is derived API and should be reused from the generic homological-functor
  owner rather than redefined locally.

Source/core/bridge triage:
- `source-facing`: the specialization of the generic homological-functor comparison theorem to the
  represented functor `Hom_D(K,-)`;
- `core/canonical`: `homologicalFunctor_hocolim_comparison_is_iso`;
- `bridge/view`: substituting `H = preadditiveCoyoneda.obj (op K)`. -/

-- Proof sketch: this is exactly Lemma 13.33.8 applied to the canonical homological functor
-- `preadditiveCoyoneda.obj (op K)`, which is the mathematically correct owner for the comparison
-- morphism. The local file keeps only the source-facing specialization, not a duplicate cocone or
-- comparison-map API.
/-- Lemma 13.33.9: if the covariant Hom functor `Hom_D(K,-)` commutes with countable direct sums,
then for any sequential system presented by a distinguished telescope triangle, the canonical map
`colim Hom_D(K, L_n) ⟶ Hom_D(K, hocolim L_n)` is an isomorphism, hence a bijection. -/
theorem preadditiveCoyoneda_hocolim_comparison_is_iso
    (K : D) [PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op K))]
    {L : ℕ → D} [HasCountableCoproducts D] (f : ∀ n, L n ⟶ L (n + 1))
    {Lhocolim : D} (g : ∐ L ⟶ Lhocolim) (h : Lhocolim ⟶ (∐ L)⟦(1 : ℤ)⟧)
    (hLhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D) :
    IsIso
      (homologicalFunctor_hocolim_comparison (preadditiveCoyoneda.obj (op K))
        f g h hLhocolim) := by
  let _ : AB5OfSize.{0, 0} AddCommGrpCat.{v} := AB5OfSize_shrink AddCommGrpCat.{v}
  simpa using
    homologicalFunctor_hocolim_comparison_is_iso (preadditiveCoyoneda.obj (op K))
      f g h hLhocolim

end

end CategoryTheory
