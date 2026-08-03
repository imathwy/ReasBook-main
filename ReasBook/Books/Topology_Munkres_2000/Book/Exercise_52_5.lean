module

public import Topology_Munkres_2000.Book.Definition_52_5.Convention
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

universe u v w

namespace FundamentalGroup.LeftToRight

/-- Helper for Exercise 52.5: a map factoring through a simply connected space induces
the trivial homomorphism on fundamental groups. -/
private lemma mapOfEq_comp_eq_one_of_simplyConnected
    {X : Type u} {T : Type v} {Y : Type w}
    [TopologicalSpace X] [TopologicalSpace T] [TopologicalSpace Y]
    [SimplyConnectedSpace T] (f : C(X, T)) (g : C(T, Y))
    (x₀ : X) (y₀ : Y) (hy : g (f x₀) = y₀) :
    mapOfEq (g.comp f) hy = 1 := by
  -- Normalize the target basepoint so all endpoint casts are reflexive.
  subst y₀
  -- Compare the two homomorphisms on an arbitrary loop class.
  ext p
  rw [mapOfEq_apply]
  rw [Path.Homotopic.Quotient.map_comp]
  rw [Subsingleton.elim (Path.Homotopic.Quotient.map p.unop f)
    (Path.Homotopic.Quotient.refl (f x₀))]
  rfl

/-- Exercise 52.5. A pointed continuous map from a subspace of Euclidean space that
extends continuously over the whole Euclidean space induces the trivial homomorphism on
fundamental groups. -/
theorem mapOfEq_eq_one_of_euclideanExtension {n : ℕ}
    {A : Set (EuclideanSpace ℝ (Fin n))} {Y : Type u} [TopologicalSpace Y]
    (h : C(A, Y)) (a₀ : A) (y₀ : Y) (ha₀ : h a₀ = y₀)
    (H : C(EuclideanSpace ℝ (Fin n), Y)) (hH : H.restrict A = h) :
    mapOfEq h ha₀ = 1 := by
  -- Replace the given map by the restriction of its Euclidean extension.
  subst h
  -- Factor the restriction through the continuous subtype inclusion.
  let inclusion : C(A, EuclideanSpace ℝ (Fin n)) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  exact mapOfEq_comp_eq_one_of_simplyConnected inclusion H a₀ y₀ ha₀

end FundamentalGroup.LeftToRight
