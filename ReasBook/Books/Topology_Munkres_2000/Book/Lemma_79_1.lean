module

public import Topology_Munkres_2000.Book.Theorem_54_6.Monodromy

public section

universe u v w

namespace FundamentalGroup

/-- Helper for Lemma 79.1: choosing a reflexive target basepoint in `mapOfEq` gives the
ordinary induced fundamental-group map. -/
private lemma mapOfEq_refl {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    mapOfEq f (rfl : f x = f x) = map f x := by
  -- Evaluate on loop classes and remove the reflexive endpoint cast.
  ext γ
  simp only [mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl, map_apply]

/-- Helper for Lemma 79.1: based fundamental-group maps preserve composition, including the
chosen endpoint equalities. -/
private lemma mapOfEq_comp {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) {x : X} {y : Y} {z : Z}
    (hf : f x = y) (hg : g y = z) (hgf : (g.comp f) x = z) :
    (mapOfEq g hg).comp (mapOfEq f hf) = mapOfEq (g.comp f) hgf := by
  -- Normalize the selected endpoints, then compare the mapped loop classes.
  subst y
  subst z
  have hg_rfl : hg = rfl := Subsingleton.elim _ _
  cases hg_rfl
  ext γ
  simp only [MonoidHom.coe_comp, Function.comp_apply, mapOfEq_apply,
    Path.Homotopic.Quotient.cast_rfl_rfl, Path.Homotopic.Quotient.map_comp]
  apply eq_of_heq
  exact Path.Homotopic.Quotient.cast_heq _ _

/-- Helper for Lemma 79.1: a based factorization gives the corresponding factorization of
fundamental-group homomorphisms. -/
private lemma map_eq_mapOfEq_comp_of_comp_eq
    {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (g : C(Y, Z)) (F : C(X, Y)) (f : C(X, Z)) (x₀ : X) (y₀ : Y)
    (hF₀ : F x₀ = y₀) (hg₀ : g y₀ = f x₀) (hcomp : g.comp F = f) :
    map f x₀ = (mapOfEq g hg₀).comp (mapOfEq F hF₀) := by
  -- Replace the factored map, then compare its ordinary and pointed induced maps.
  subst f
  rw [← mapOfEq_refl]
  exact (mapOfEq_comp F g hF₀ hg₀ rfl).symm

/-- Helper for Lemma 79.1: the range of a based map that factors through another map lies in
the range of the latter map on fundamental groups. -/
private lemma map_range_le_mapOfEq_range_of_comp_eq
    {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (g : C(Y, Z)) (F : C(X, Y)) (f : C(X, Z)) (x₀ : X) (y₀ : Y)
    (hF₀ : F x₀ = y₀) (hg₀ : g y₀ = f x₀) (hcomp : g.comp F = f) :
    (map f x₀).range ≤ (mapOfEq g hg₀).range := by
  -- Rewrite through the induced factorization, then retain the outer-map witness.
  rw [map_eq_mapOfEq_comp_of_comp_eq g F f x₀ y₀ hF₀ hg₀ hcomp]
  rintro γ ⟨δ, rfl⟩
  exact ⟨mapOfEq F hF₀ δ, rfl⟩

end FundamentalGroup

/-- Lemma 79.1 (The general lifting lemma): a based continuous map lifts uniquely
through a covering map exactly when its induced fundamental-group range is contained
in the subgroup corresponding to the covering at the chosen point of the fiber. -/
theorem IsCoveringMap.existsUnique_continuousMap_lifts_iff_range_le
    {E : Type u} {B : Type v} {Y : Type w}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace Y]
    (p : E → B) (hp : IsCoveringMap p) [PathConnectedSpace Y]
    [LocallyPathConnectedSpace Y] (f : C(Y, B)) (y₀ : Y) (e₀ : E)
    (he : p e₀ = f y₀) :
    (∃! F : C(Y, E), F y₀ = e₀ ∧ p ∘ F = f) ↔
      (FundamentalGroup.map f y₀).range ≤
        hp.fundamentalGroupMapRange he := by
  constructor
  · rintro ⟨F, hF, -⟩
    -- Package the covering projection continuously and turn the pointwise lift equation into
    -- an equality of continuous maps.
    let pMap : C(E, B) := ⟨p, hp.continuous⟩
    have hcomp : pMap.comp F = f := by
      ext y
      exact congrFun hF.2 y
    -- Functoriality sends every loop in the range of the induced map into the covering subgroup.
    simpa only [IsCoveringMap.fundamentalGroupMapRange, pMap] using
      FundamentalGroup.map_range_le_mapOfEq_range_of_comp_eq
        pMap F f y₀ e₀ hF.1 he hcomp
  · intro h_range
    -- Mathlib's lifting criterion constructs the lift and supplies its uniqueness.
    unfold IsCoveringMap.fundamentalGroupMapRange at h_range
    exact hp.existsUnique_continuousMap_lifts_of_range_le he h_range
