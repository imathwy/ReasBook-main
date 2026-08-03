module

public import Topology_Munkres_2000.Book.Definition_52_6.BasepointChange

public section

universe u v

namespace FundamentalGroup.LeftToRight

/-- Helper for Exercise 52.6: the path-class representation of an element of
`π₁(X, x₀)` is injective. -/
private lemma toPath_injective {X : Type u} [TopologicalSpace X] {x₀ : X}
    (a b : π₁(X, x₀)) (h : toPath a = toPath b) : a = b := by
  -- Recover both group elements by applying the inverse path-class representation.
  calc
    a = fromPath (toPath a) := (fromPath_toPath a).symm
    _ = fromPath (toPath b) := congrArg fromPath h
    _ = b := fromPath_toPath b

/-- Helper for Exercise 52.6: mapping path-homotopy classes preserves their
left-to-right concatenation. -/
private lemma quotientMapPreservesTrans {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {x₀ x₁ x₂ : X}
    (p : Path.Homotopic.Quotient x₀ x₁) (q : Path.Homotopic.Quotient x₁ x₂)
    (h : C(X, Y)) :
    (p.trans q).map h = (p.map h).trans (q.map h) := by
  -- Descend the ordinary path identity through representatives of both classes.
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
      induction q using Path.Homotopic.Quotient.ind with
      | mk q =>
          simp only [← Path.Homotopic.Quotient.mk_trans,
            ← Path.Homotopic.Quotient.mk_map, Path.map_trans]

/-- Helper for Exercise 52.6: mapping a reversed path-homotopy class gives the
reverse of its image. -/
private lemma quotientMapPreservesSymm {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {x₀ x₁ : X}
    (p : Path.Homotopic.Quotient x₀ x₁) (h : C(X, Y)) :
    p.symm.map h = (p.map h).symm := by
  -- Descend the ordinary path-reversal identity through a representative.
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
      simp only [← Path.Homotopic.Quotient.mk_symm,
        ← Path.Homotopic.Quotient.mk_map, Path.map_symm]

/-- Exercise 52.6. If `β` is the image of `α` under `h`, then the induced maps on
fundamental groups commute with the basepoint-change maps:
`β̂ ∘ mapOfEq h hx₀ = mapOfEq h hx₁ ∘ α̂`. -/
theorem mapOfEq_naturality {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (h : C(X, Y))
    (x₀ x₁ : X) (y₀ y₁ : Y) (hx₀ : h x₀ = y₀) (hx₁ : h x₁ = y₁)
    (α : Path x₀ x₁) :
    ((α.map h.continuous).cast hx₀.symm hx₁.symm)̂ ∘ mapOfEq h hx₀ =
      mapOfEq h hx₁ ∘ α̂ := by
  -- Replace the named codomain endpoints so all endpoint casts become reflexive.
  subst y₀
  subst y₁
  -- Compare the two maps pointwise through the injective path-class representation.
  funext p
  apply toPath_injective
  -- Expand conjugation and the induced map, then distribute mapping over its factors.
  simp only [Function.comp_apply, mapOfEq_apply,
    MulOpposite.unop_op, Path.cast_rfl_rfl,
    Path.Homotopic.Quotient.cast_rfl_rfl]
  rw [quotientMapPreservesTrans, quotientMapPreservesTrans,
    quotientMapPreservesSymm, ← Path.Homotopic.Quotient.mk_map]

/-- The bundled homomorphism form of `mapOfEq_naturality`. -/
theorem mapOfEq_naturality_hom {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (h : C(X, Y))
    (x₀ x₁ : X) (y₀ y₁ : Y) (hx₀ : h x₀ = y₀) (hx₁ : h x₁ = y₁)
    (α : Path x₀ x₁) :
    (mulEquivOfPath ((α.map h.continuous).cast hx₀.symm hx₁.symm)).toMonoidHom.comp
        (mapOfEq h hx₀) =
      (mapOfEq h hx₁).comp (mulEquivOfPath α).toMonoidHom := by
  ext p
  exact congrFun (mapOfEq_naturality h x₀ x₁ y₀ y₁ hx₀ hx₁ α) p

end FundamentalGroup.LeftToRight
