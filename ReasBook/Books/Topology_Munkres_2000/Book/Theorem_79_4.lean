module

public import Topology_Munkres_2000.Book.Theorem_79_2
public import Topology_Munkres_2000.Book.Lemma_79_3

public section

universe u v w

namespace IsCoveringMap

/-- Helper for Theorem 79.4: a pointed equivalence of connected coverings identifies their
fundamental-group ranges. -/
private lemma fundamentalGroupMapRange_eq_of_equiv
    {E : Type u} {E' : Type v} {B : Type w}
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
    [PathConnectedSpace E] [PathConnectedSpace E']
    [LocallyPathConnectedSpace E] [LocallyPathConnectedSpace E']
    {p : E → B} {p' : E' → B} (hp : IsCoveringMap p) (hp' : IsCoveringMap p')
    {e₀ : E} {e₁' : E'} {b₀ : B} (he₀ : p e₀ = b₀) (he₁' : p' e₁' = b₀)
    (h : CoveringMap.Equiv p p') (h_base : h.toHomeomorph e₀ = e₁') :
    hp.fundamentalGroupMapRange he₀ = hp'.fundamentalGroupMapRange he₁' := by
  -- Upgrade the supplied equivalence to the unique pointed equivalence required by Theorem 79.2.
  apply (existsUnique_equiv_iff_fundamentalGroupMapRange_eq
    p p' hp hp' e₀ e₁' b₀ he₀ he₁').mp
  refine ExistsUnique.intro h h_base ?_
  intro k k_base
  -- Uniqueness of covering lifts identifies any second pointed equivalence with the first.
  apply CoveringMap.Equiv.ext
  apply Homeomorph.ext
  exact congrFun (hp'.eq_of_comp_eq k.toHomeomorph.continuous h.toHomeomorph.continuous
    (k.commutes.symm.trans h.commutes) e₀ (k_base.trans h_base.symm))

/-- Theorem 79.4. Two connected covering maps over the same base are equivalent if and
only if their basepoint-induced fundamental-group ranges are conjugate subgroups. -/
theorem equivalent_iff_fundamentalGroupMapRange_isConj
    {E : Type u} {E' : Type v} {B : Type w}
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
    [PathConnectedSpace E] [PathConnectedSpace E']
    [LocallyPathConnectedSpace E] [LocallyPathConnectedSpace E']
    {p : E → B} {p' : E' → B} (hp : IsCoveringMap p) (hp' : IsCoveringMap p')
    (e₀ : E) (e₀' : E') (b₀ : B) (he₀ : p e₀ = b₀) (he₀' : p' e₀' = b₀) :
    CoveringMap.Equivalent p p' ↔
      (hp.fundamentalGroupMapRange he₀).IsConj
        (hp'.fundamentalGroupMapRange he₀') := by
  constructor
  · intro hequiv
    obtain ⟨hHomeomorph, hcommutes⟩ := CoveringMap.equivalent_iff.mp hequiv
    let h : CoveringMap.Equiv p p' :=
      { toHomeomorph := hHomeomorph
        commutes := hcommutes }
    -- Regard the image of `e₀` as a second point over `b₀` and identify its range with the
    -- range of the first covering.
    have he₁' : p' (h.toHomeomorph e₀) = b₀ :=
      (h.commutes_apply e₀).symm.trans he₀
    have h_base : h.toHomeomorph e₀ = h.toHomeomorph e₀ := rfl
    have hrange : hp.fundamentalGroupMapRange he₀ =
        hp'.fundamentalGroupMapRange he₁' :=
      fundamentalGroupMapRange_eq_of_equiv hp hp' he₀ he₁' h h_base
    -- A path from the chosen point of `E'` to that image conjugates the two ranges in the
    -- orientation needed for the conclusion.
    have γ : Path e₀' (h.toHomeomorph e₀) :=
      PathConnectedSpace.somePath e₀' (h.toHomeomorph e₀)
    have hconj : (hp'.fundamentalGroupMapRange he₁').IsConj
        (hp'.fundamentalGroupMapRange he₀') :=
      hp'.fundamentalGroupMapRange_isConj_of_path he₀' he₁' γ
    rw [hrange]
    exact hconj
  · intro hconj
    -- Realize the conjugate subgroup at a point of the second fiber.
    obtain ⟨e₁', he₁', hrange⟩ :=
      hp'.exists_fiberPoint_fundamentalGroupMapRange_eq_of_isConj
        e₀' he₀' (hp.fundamentalGroupMapRange he₀) hconj
    -- The pointed classification theorem turns the resulting range equality into an
    -- equivalence of the underlying coverings.
    obtain ⟨h, _, _⟩ := (existsUnique_equiv_iff_fundamentalGroupMapRange_eq
      p p' hp hp' e₀ e₁' b₀ he₀ he₁').mpr hrange.symm
    apply CoveringMap.equivalent_iff.mpr
    exact Exists.intro h.toHomeomorph h.commutes

end IsCoveringMap
