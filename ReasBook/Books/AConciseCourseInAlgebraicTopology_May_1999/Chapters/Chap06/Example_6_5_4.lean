import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Lemma_6_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Proposition_6_5_3

open CategoryTheory
open scoped ContinuousMap

noncomputable section

universe u

variable {A X : Type u} [TopologicalSpace A] [TopologicalSpace X]

-- Semantic recall via `lean_leansearch`: the available hits only exposed model-categorical
-- cofibration APIs, so this item uses the local Chapter 6 owners
-- `mappingCylinderFactorizationIn`, `mappingCylinderProjection`, and
-- `isCofiberHomotopyEquivalence_of_homotopyEquiv`.

/-- Helper for Example 6.5.4: the mapping cylinder of `i : A ⟶ X` viewed as a space under `A`
via the canonical map in the mapping cylinder factorization of `i`. -/
def mappingCylinderUnder (i : C(A, X)) : Under (TopCat.of A) :=
  Under.mk (TopCat.ofHom (mappingCylinderFactorizationIn i))

/-- Helper for Example 6.5.4: the structure map `A ⟶ M_i` of `mappingCylinderUnder i` is the
factorization leg `mappingCylinderFactorizationIn i`. -/
@[simp] theorem mappingCylinderUnder_hom (i : C(A, X)) :
    (mappingCylinderUnder i).hom = TopCat.ofHom (mappingCylinderFactorizationIn i) :=
  rfl

/-- Helper for Example 6.5.4: the canonical projection `M_i ⟶ X` of the mapping cylinder
factorization, viewed as a morphism in `Under (TopCat.of A)`. -/
def mappingCylinderProjectionUnder (i : C(A, X)) :
    mappingCylinderUnder i ⟶ (Under.mk (TopCat.ofHom i) : Under (TopCat.of A)) :=
  Under.homMk (TopCat.ofHom (mappingCylinderProjection i))
    (congrArg TopCat.ofHom (mappingCylinderProjection_comp_factorizationIn i))

/-- Helper for Example 6.5.4: the underlying map of `mappingCylinderProjectionUnder i` is
`mappingCylinderProjection i`. -/
@[simp] theorem mappingCylinderProjectionUnder_right (i : C(A, X)) :
    (mappingCylinderProjectionUnder i).right = TopCat.ofHom (mappingCylinderProjection i) :=
  rfl

/-- Example 6.5.4. For a cofibration `i : A ⟶ X`, the mapping cylinder diagram
`A ⟶ M_i ⟶ X` is a cofiber homotopy equivalence under `A`. -/
theorem mappingCylinderProjectionUnder_isCofiberHomotopyEquivalence
    {i : C(A, X)} (hi : IsCofibration.{u, u, u} i) :
    IsCofiberHomotopyEquivalence (mappingCylinderProjectionUnder i) := by
  -- Route correction: package the mapping cylinder factorization under `A`, then apply
  -- Proposition 6.5.3 directly to the canonical projection.
  have hProjection :
      (mappingCylinderProjection_homotopyEquiv i).toFun =
        (mappingCylinderProjectionUnder i).right.hom := by
    -- The repaired `Under` morphism is built from `mappingCylinderProjection i`.
    rw [mappingCylinderProjection_homotopyEquiv_toFun, mappingCylinderProjectionUnder_right]
    rfl
  exact isCofiberHomotopyEquivalence_of_homotopyEquiv
    (mappingCylinderFactorizationIn_isCofibration i) hi (mappingCylinderProjectionUnder i)
    (mappingCylinderProjection_homotopyEquiv i) hProjection

/-- Example 6.5.4. For a cofibration `i : A ⟶ X`, the mapping cylinder diagram
`A ⟶ M_i ⟶ X` is a cofiber homotopy equivalence under `A`. -/
instance mappingCylinderProjectionUnder.instIsCofiberHomotopyEquivalence
    {i : C(A, X)} (hi : IsCofibration.{u, u, u} i) :
    IsCofiberHomotopyEquivalence (mappingCylinderProjectionUnder i) :=
  mappingCylinderProjectionUnder_isCofiberHomotopyEquivalence hi
