import Mathlib.Topology.ContinuousMap.ContinuousMapZero
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_2_4

open scoped ContinuousMapZero PathSpace

universe u v

variable {X : Type u} {Y : Type v} [Zero X] [Zero Y] [TopologicalSpace X] [TopologicalSpace Y]

-- Semantic recall via `lean_leansearch` surfaced only the canonical path owner `Path`; for this
-- source-faithful based analogue of `N_f`, the right owner in the current project is the subtype
-- of `X × P[(0 : Y)]` cut out by the endpoint equation.

/-- Definition 8.5.3. For a based map `f : C(X, Y)₀`, the based mapping path space `N_f` is the
subtype of `X × P[(0 : Y)]` consisting of pairs `(x, χ)` with `χ(1) = f(x)`. Here
`P[(0 : Y)]` models paths in `Y` based at `0`. -/
def basedMappingPathSpace (f : C(X, Y)₀) : Type (max u v) :=
  { xχ : X × P[(0 : Y)] // xχ.2.endpoint = f xχ.1 }

namespace basedMappingPathSpace

variable {f : C(X, Y)₀}

/-- `basedMappingPathSpace f` carries the subtype topology inherited from
`X × P[(0 : Y)]`. -/
instance instTopologicalSpace : TopologicalSpace (basedMappingPathSpace f) :=
  inferInstanceAs
    (TopologicalSpace { xχ : X × P[(0 : Y)] // xχ.2.endpoint = f xχ.1 })

/-- The point of `X` underlying an element of `basedMappingPathSpace f`. -/
def point (xχ : basedMappingPathSpace f) : X :=
  xχ.1.1

/-- The based path in `Y` underlying an element of `basedMappingPathSpace f`. -/
def path (xχ : basedMappingPathSpace f) : P[(0 : Y)] :=
  xχ.1.2

/-- Construct an element of `basedMappingPathSpace f` from a point `x : X` and a based path
`χ : P[(0 : Y)]` whose endpoint is `f x`. -/
def mk (x : X) (χ : P[(0 : Y)]) (hχ : χ.endpoint = f x) : basedMappingPathSpace f :=
  ⟨(x, χ), hχ⟩

@[simp] theorem point_mk (x : X) (χ : P[(0 : Y)]) (hχ : χ.endpoint = f x) :
    (mk x χ hχ).point = x :=
  rfl

@[simp] theorem path_mk (x : X) (χ : P[(0 : Y)]) (hχ : χ.endpoint = f x) :
    (mk x χ hχ).path = χ :=
  rfl

@[ext] theorem ext {xχ yχ : basedMappingPathSpace f} (hpoint : xχ.point = yχ.point)
    (hpath : xχ.path = yχ.path) : xχ = yχ := by
  apply Subtype.ext
  exact Prod.ext hpoint hpath

/-- The defining condition on an element of `basedMappingPathSpace f` is that the endpoint of its
path component is `f` evaluated at its point component. -/
theorem endpoint_eq (xχ : basedMappingPathSpace f) : xχ.path.endpoint = f xχ.point :=
  xχ.2

@[simp] theorem mk_point_path (xχ : basedMappingPathSpace f) :
    mk xχ.point xχ.path xχ.endpoint_eq = xχ := by
  cases xχ
  rfl

end basedMappingPathSpace
