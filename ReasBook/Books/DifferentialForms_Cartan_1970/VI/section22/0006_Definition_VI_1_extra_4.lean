import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- this definition uses mathlib's canonical owner `OpenPartialHomeomorph ℂ ℂ` for the underlying
-- homeomorphism data between open subsets of the complex plane, and adds only the holomorphic
-- conditions as extra structure.

namespace OpenPartialHomeomorph

/-- The holomorphicity data carried by an open partial homeomorphism `e : ℂ ⇿ ℂ` whose source is
`D` and whose target is `D'`. -/
class IsHolomorphicIsoOn (e : OpenPartialHomeomorph ℂ ℂ) (D D' : Set ℂ) : Prop where
  source_eq : e.source = D
  target_eq : e.target = D'
  analyticOn_toFun : AnalyticOnNhd ℂ e D
  analyticOn_symm : AnalyticOnNhd ℂ e.symm D'

end OpenPartialHomeomorph

/-- Definition VI.1-extra-4: a holomorphic isomorphism from the open set `D` onto the open set
`D'` is an open partial homeomorphism of `ℂ` with source `D` and target `D'` whose defining map
and inverse are holomorphic on their respective domains. -/
abbrev HolomorphicIsomorph (D D' : Set ℂ) :=
  { e : OpenPartialHomeomorph ℂ ℂ // e.IsHolomorphicIsoOn D D' }

namespace HolomorphicIsomorph

variable {D D' : Set ℂ}

/-- A holomorphic isomorphism is used by its underlying map. -/
instance : CoeFun (HolomorphicIsomorph D D') (fun _ ↦ ℂ → ℂ) where
  coe e := (e : OpenPartialHomeomorph ℂ ℂ)

/-- The source of a holomorphic isomorphism is the prescribed domain `D`. -/
theorem source_eq (e : HolomorphicIsomorph D D') :
    (e : OpenPartialHomeomorph ℂ ℂ).source = D :=
  e.property.source_eq

/-- The target of a holomorphic isomorphism is the prescribed codomain `D'`. -/
theorem target_eq (e : HolomorphicIsomorph D D') :
    (e : OpenPartialHomeomorph ℂ ℂ).target = D' :=
  e.property.target_eq

/-- A holomorphic isomorphism is holomorphic on its source. -/
theorem analyticOn_toFun (e : HolomorphicIsomorph D D') :
    AnalyticOnNhd ℂ (e : OpenPartialHomeomorph ℂ ℂ) D :=
  e.property.analyticOn_toFun

/-- The inverse of a holomorphic isomorphism is holomorphic on its target. -/
theorem analyticOn_invFun (e : HolomorphicIsomorph D D') :
    AnalyticOnNhd ℂ (e : OpenPartialHomeomorph ℂ ℂ).symm D' :=
  e.property.analyticOn_symm

/-- A holomorphic isomorphism induces a homeomorphism between its source and target. -/
def toHomeomorph (e : HolomorphicIsomorph D D') : D ≃ₜ D' :=
  (Homeomorph.setCongr e.source_eq.symm).trans <|
    (e : OpenPartialHomeomorph ℂ ℂ).toHomeomorphSourceTarget.trans (Homeomorph.setCongr e.target_eq)

/-- The source of a holomorphic isomorphism is open. -/
theorem isOpen_source (e : HolomorphicIsomorph D D') :
    IsOpen D := by
  simpa [e.source_eq] using (e : OpenPartialHomeomorph ℂ ℂ).open_source

/-- The target of a holomorphic isomorphism is open. -/
theorem isOpen_target (e : HolomorphicIsomorph D D') :
    IsOpen D' := by
  simpa [e.target_eq] using (e : OpenPartialHomeomorph ℂ ℂ).open_target

end HolomorphicIsomorph

end
