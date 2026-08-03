module

public import Topology_Munkres_2000.Book.Definition_57_2.Antipodal

import Topology_Munkres_2000.Book.Theorem_57_3
import Mathlib.Geometry.Manifold.Instances.Sphere

public section

/-- Helper for Exercise 57.2: the ambient Euclidean space of `S²` has dimension three. -/
private lemma standardSphereTwo_finrank :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 + 1))) = 2 + 1 := by
  -- The standard finrank formula reduces both sides to the same numeral.
  exact (finrank_euclideanSpace_fin :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 + 1))) = 2 + 1)

/-- Helper for Exercise 57.2: the dimension fact required by stereographic projection on `S²`. -/
private instance standardSphereTwo_finrankFact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 + 1))) = 2 + 1) :=
  ⟨standardSphereTwo_finrank⟩

/-- Helper for Exercise 57.2: stereographic projection after a continuous sphere map
is continuous when the map omits the projection center. -/
private lemma continuous_stereographicComp
    (p : StandardSphere 2) (g : C(StandardSphere 2, StandardSphere 2))
    (hp : ∀ x, g x ≠ p) :
    Continuous (fun x ↦ stereographic' 2 p (g x)) := by
  -- It suffices to prove continuity on the whole sphere while tracking the chart source.
  rw [← continuousOn_univ]
  refine (stereographic' 2 p).continuousOn_toFun.comp g.continuous.continuousOn ?_
  -- The omitted-point hypothesis places every image point in the punctured chart domain.
  intro x _
  rw [stereographic'_source]
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hp x

/-- Helper for Exercise 57.2: the stereographic projection of a sphere map omitting
its center, packaged as a continuous map to `ℝ²`. -/
private noncomputable def stereographicComp
    (p : StandardSphere 2) (g : C(StandardSphere 2, StandardSphere 2))
    (hp : ∀ x, g x ≠ p) :
    C(StandardSphere 2, EuclideanSpace ℝ (Fin 2)) :=
  ⟨fun x ↦ stereographic' 2 p (g x), continuous_stereographicComp p g hp⟩

/-- Helper for Exercise 57.2: equality after stereographic projection is equivalent
to equality before projection for a sphere map omitting the projection center. -/
private lemma stereographicComp_eq_iff
    (p : StandardSphere 2) (g : C(StandardSphere 2, StandardSphere 2))
    (hp : ∀ x, g x ≠ p) (x y : StandardSphere 2) :
    stereographicComp p g hp x = stereographicComp p g hp y ↔ g x = g y := by
  -- Injectivity on the punctured source reflects equality of projected values.
  constructor
  · intro hxy
    apply (stereographic' 2 p).injOn
    · rw [stereographic'_source]
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hp x
    · rw [stereographic'_source]
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hp y
    · exact hxy
  -- Equal original values plainly have equal projected values.
  · intro hxy
    exact congrArg (stereographic' 2 p) hxy

/-- Exercise 57.2: A continuous self-map of `S²` that separates every pair of
antipodal points is surjective. -/
theorem surjectiveOfContinuousNeAntipodal
    (g : C(StandardSphere 2, StandardSphere 2))
    (h_antipodal : ∀ x, g x ≠ g (-x)) :
    Function.Surjective g := by
  -- If surjectivity fails, choose a point omitted by the entire image of `g`.
  classical
  by_contra hsurjective
  simp only [Function.Surjective] at hsurjective
  push Not at hsurjective
  obtain ⟨p, hp⟩ := hsurjective
  -- Borsuk--Ulam identifies an antipodal pair after projecting away from the omitted point.
  obtain ⟨x, hx⟩ := existsAntipodalEqSphereTwo (stereographicComp p g hp)
  -- Stereographic injectivity transports that equality back to `g`, giving the contradiction.
  exact h_antipodal x ((stereographicComp_eq_iff p g hp x (-x)).mp hx)
