import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import StacksProject_2024.Chap12.Definition_12_12_1
import StacksProject_2024.Chap13.Definition_13_3_6

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

noncomputable section

universe vA vB vD uA uB uD

namespace CategoryTheory

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

namespace DeltaFunctor

section

/-
Domain-style sampling for Lemma 13.4.22:
- primary domain: composing a source-side `δ`-functor with a homological functor on a
  pretriangulated target to obtain the induced cohomological long exact sequence;
- sampled owner declarations in this domain:
  `CategoryTheory.DeltaFunctor`,
  `CategoryTheory.CohomologicalDeltaFunctor`,
  `CategoryTheory.Functor.homologySequenceδ`,
  `CategoryTheory.Functor.homologySequenceComposableArrows₅_exact`;
- best owner abstraction:
  `source-facing`: `DeltaFunctor.toCohomologicalDeltaFunctor`;
  `core/canonical`: the chapter owners `DeltaFunctor`, `CohomologicalDeltaFunctor`, and the
    mathlib long-exact-sequence owners attached to `Functor.IsHomological`;
  `bridge/view`: the direct reuse of `Functor.homologySequenceδ` on the distinguished triangle
    `G.triangle hS`, with no separate local boundary-map owner.
- primitive data: a `δ`-functor `G : A ⥤ D`, a homological functor `H : D ⥤ B` with shift
- primitive data: a `δ`-functor `G : A ⥤ D` with its owner-level additive structure, a
  homological functor `H : D ⥤ B` with shift
  sequence, and the degree-`-1` vanishing hypothesis needed for left exactness in degree `0`;
- derived API: the resulting cohomological `δ`-functor owner assembled directly from the
  canonical long-exact-sequence maps.

The adjacent exactness windows and boundary-map naturality are already canonically owned by the
homological-functor API in mathlib once one passes to the distinguished triangle
`G.triangle hS`. This file should therefore build the source-facing cohomological `δ`-functor
directly from those owners instead of keeping parallel local exactness wrapper theorems.
-/

variable (G : DeltaFunctor A D) (H : D ⥤ B)
variable [H.IsHomological] [H.ShiftSequence ℤ]

/-- Lemma 13.4.22: if `G : A ⥤ D` is a `δ`-functor and `H : D ⥤ B` is a homological functor
such that `H^{-1}(G(X)) = 0` for every object `X` of `A`, then the degreewise composites
`H^n ∘ G` with their induced connecting morphisms form a cohomological `δ`-functor
`A ⥤ B`. -/
noncomputable def toCohomologicalDeltaFunctor
    (hneg : ∀ X : A, IsZero ((H.shift (-1)).obj (G.obj X))) :
    CohomologicalDeltaFunctor A B where
  F := fun n ↦ AdditiveFunctor.of (G.toFunctor ⋙ H.shift (n : ℤ))
  δ := fun {S} hS n ↦ by
    simpa using H.homologySequenceδ (G.triangle hS) (n : ℤ) (n + 1 : ℤ) (by simp)
  mono_map_f_zero := fun {S} hS ↦ by
    have hδ : H.homologySequenceδ (G.triangle hS) (-1) 0 (by simp) = 0 := by
      exact (hneg S.X₃).eq_of_src _ _
    exact (H.homologySequence_mono_shift_map_mor₁_iff
      (G.triangle hS) (G.triangle_distinguished hS) (-1) 0 (by simp)).2 (by
        simpa [triangle] using hδ)
  exact₅ := fun {_} hS n ↦ by
    simpa [triangle] using
      H.homologySequenceComposableArrows₅_exact
        (G.triangle hS) (G.triangle_distinguished hS) (n : ℤ) (n + 1 : ℤ) (by simp)
  δ_naturality := fun {_ _} hS hT φ n ↦ by
    refine CommSq.mk ?_
    simpa [triangle] using
      H.homologySequenceδ_naturality
        (G.triangle hS) (G.triangle hT) (G.triangleMap hS hT φ)
        (n : ℤ) (n + 1 : ℤ) (by simp)

end

end DeltaFunctor

end CategoryTheory
