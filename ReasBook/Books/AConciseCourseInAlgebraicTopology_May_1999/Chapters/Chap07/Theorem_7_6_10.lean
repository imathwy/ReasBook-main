import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Proposition_7_5_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Theorem_7_6_9

open CategoryTheory
open TopCat
open scoped ContinuousMap
open Path.Homotopic.Quotient

noncomputable section

universe u

variable {E F A B : Type u}
variable [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace A] [TopologicalSpace B]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} E]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} F]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} A]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} B]

-- Semantic recall via `lean_leansearch`: `ContinuousMap.Homotopy.evalAt` gives the path traced by
-- a point under a homotopy. Theorem 7.6.10 is source-facing, so its public surface quantifies
-- over an arbitrary class satisfying `IsFiberTranslation` along that path.

/-- Theorem 7.6.10: if two maps of fibrations `φ₀, φ₁ : p ⟶ q` are homotopic through maps of
fibrations, then for each `a : A` the induced maps on fibers over `a` differ by translation along
the base homotopy path `H.right.evalAt a`. -/
theorem mapOfFibrationsToFiber_homotopic {p : C(E, A)} {q : C(F, B)}
    [IsFibration p] [IsFibration q]
    (φ₀ φ₁ : Arrow.mk (TopCat.ofHom p) ⟶ Arrow.mk (TopCat.ofHom q))
    (H : ArrowHomotopy φ₀ φ₁) (a : A)
    {τ : fiberMapHomotopyClasses q (φ₀.right.hom a) (φ₁.right.hom a)}
    (hτ : IsFiberTranslation q (mk (H.right.evalAt a)) τ) :
    continuousMapHomotopyClassesPrecompose
      (mapOfFibrationsToFiber (CommSq.flip (CommSq.of_arrow φ₀)) a) τ =
    ⟦mapOfFibrationsToFiber (CommSq.flip (CommSq.of_arrow φ₁)) a⟧ := sorry
