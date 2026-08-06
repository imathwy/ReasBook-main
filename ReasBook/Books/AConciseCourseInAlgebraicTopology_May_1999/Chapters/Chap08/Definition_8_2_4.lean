import Mathlib.Topology.Path

open scoped unitInterval

universe u

variable {X : Type u} [TopologicalSpace X]

-- Semantic recall: mathlib's `Path x y` fixes both endpoints. The textbook path space `PX`
-- lets the terminal point vary, so the natural owner is the subtype of `C(I, X)` sending `0`
-- to the chosen basepoint.

/-- Definition 8.2.4. For a pointed space `(X, x₀)`, the path space `PX` is the subtype of
`C(I, X)` consisting of maps `γ` with `γ 0 = x₀`; equivalently, its points are paths in `X`
starting at the basepoint `x₀`. -/
def PathSpace (x₀ : X) : Type u :=
  { γ : C(I, X) // γ 0 = x₀ }

namespace PathSpace

/- May's `PX` notation is modeled by the scoped Lean notation `P[x₀]` for paths starting at the
chosen basepoint `x₀`. -/
scoped notation "P[" x₀ "]" => _root_.PathSpace x₀

end PathSpace

open scoped PathSpace

namespace PathSpace

variable {x₀ y : X}

/-- `P[x₀]` carries the subtype topology inherited from `C(I, X)`. -/
instance instTopologicalSpace : TopologicalSpace P[x₀] :=
  inferInstanceAs (TopologicalSpace { γ : C(I, X) // γ 0 = x₀ })

/-- A point of `P[x₀]` may be evaluated on `I` as a map `I → X`. -/
instance instCoeFun : CoeFun P[x₀] (fun _ ↦ I → X) where
  coe γ := γ.1

/-- Construct a point of `P[x₀]` from a continuous map on `I` starting at `x₀`. -/
def mk (γ : C(I, X)) (hγ : γ 0 = x₀) : P[x₀] :=
  ⟨γ, hγ⟩

@[simp] theorem coe_mk (γ : C(I, X)) (hγ : γ 0 = x₀) : ⇑(mk γ hγ) = γ :=
  rfl

/-- The terminal point of a path in `P[x₀]`. -/
def endpoint (γ : P[x₀]) : X :=
  γ 1

@[simp] theorem endpoint_mk (γ : C(I, X)) (hγ : γ 0 = x₀) : (mk γ hγ).endpoint = γ 1 :=
  rfl

/-- A point of `P[x₀]` determines a path from `x₀` to its endpoint. -/
def toPath (γ : P[x₀]) : Path x₀ γ.endpoint where
  toContinuousMap := γ.1
  source' := γ.2
  target' := rfl

@[simp] theorem toPath_apply (γ : P[x₀]) (t : I) : γ.toPath t = γ t :=
  rfl

/-- A path in `X` with initial point `x₀` determines a point of `P[x₀]`. -/
def ofPath (γ : Path x₀ y) : P[x₀] :=
  mk γ.toContinuousMap γ.source'

@[simp] theorem ofPath_toPath (γ : P[x₀]) : ofPath γ.toPath = γ := by
  cases γ
  rfl

@[simp] theorem toPath_ofPath (γ : Path x₀ y) : ⇑(ofPath γ).toPath = γ :=
  rfl

@[simp] theorem endpoint_ofPath (γ : Path x₀ y) : (ofPath γ).endpoint = y :=
  γ.target'

/-- The constant path at the basepoint gives a canonical point of `P[x₀]`. -/
def basepoint (x₀ : X) : P[x₀] :=
  ofPath (Path.refl x₀)

@[simp] theorem endpoint_basepoint (x₀ : X) : (basepoint x₀).endpoint = x₀ :=
  rfl

/-- The defining condition on `γ : P[x₀]` is that it starts at the basepoint `x₀`. -/
@[simp] theorem source_eq (γ : P[x₀]) : γ 0 = x₀ :=
  γ.2

end PathSpace
