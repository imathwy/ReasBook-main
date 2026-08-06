import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_2_1

open scoped unitInterval

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

-- Analogue retrieval found mathlib's `IsCoveringMap.liftPath` and the local subtype-based
-- path-space owners `MappingPathSpace` and `PathSpace`. The textbook notion is best exposed as a
-- bundled map `MappingPathSpace p → C(I, E)` together with its two defining laws.

/-- Definition 7.2.2. A path lifting function for `p : E → B` is a map
`s : MappingPathSpace p → C(I, E)` such that for each `x = (e, β)` in `MappingPathSpace p`,
the path `s x` starts at `e` and projects along `p` to `β`. -/
structure PathLiftingFunction (p : E → B) where
  toFun : MappingPathSpace p → C(I, E)
  source_eq (x : MappingPathSpace p) : toFun x 0 = x.point
  proj_comp_eq (x : MappingPathSpace p) : p ∘ toFun x = x.path

namespace PathLiftingFunction

variable {p : E → B}

/-- A path lifting function may be used as its underlying map `MappingPathSpace p → C(I, E)`. -/
instance instCoeFun : CoeFun (PathLiftingFunction p) (fun _ ↦ MappingPathSpace p → C(I, E)) where
  coe s := s.toFun

/-- Evaluating a path lifting function at `0` recovers the chosen initial point. -/
@[simp] theorem apply_zero (s : PathLiftingFunction p) (x : MappingPathSpace p) :
    s x 0 = x.point :=
  s.source_eq x

/-- Evaluating the projection identity pointwise recovers the prescribed path in `B`. -/
@[simp] theorem proj_apply (s : PathLiftingFunction p) (x : MappingPathSpace p) (t : I) :
    p (s x t) = x.path t := by
  simpa using congrArg (fun γ : I → B ↦ γ t) (s.proj_comp_eq x)

/-- The defining conditions of a path lifting function expose both the initial point and the
projected path. -/
theorem spec (s : PathLiftingFunction p) (x : MappingPathSpace p) :
    s x 0 = x.point ∧ p ∘ s x = x.path :=
  ⟨s.apply_zero x, s.proj_comp_eq x⟩

end PathLiftingFunction
