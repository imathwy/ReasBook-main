import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory FundamentalGroupoidFunctor
open scoped ContinuousMap

noncomputable section

variable {X : Type u} [TopologicalSpace X]
variable {Y : Type v} [TopologicalSpace Y]

namespace ContinuousMap.HomotopyEquiv

/-- Proposition 2.4.6: if `e : X ≃ₕ Y` is an unbased homotopy equivalence, then for every
basepoint `x : X` the induced map `e_* : π₁(X, x) → π₁(Y, e x)` is an isomorphism of groups. -/
-- Proof sketch: the equivalence of fundamental groupoids induced by `e` is fully faithful, so
-- on the vertex group at `x` it induces the corresponding multiplicative equivalence on
-- endomorphism groups.
def fundamentalGroupMulEquiv (e : X ≃ₕ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) :=
  let F := (equivOfHomotopyEquiv e).functor
  let hF : F.FullyFaithful := .ofFullyFaithful F
  hF.mulEquivEnd (FundamentalGroupoid.mk x)

/-- The underlying homomorphism of `e.fundamentalGroupMulEquiv x` is the usual map on
fundamental groups induced by the forward map of the homotopy equivalence. -/
@[simp] theorem fundamentalGroupMulEquiv_toMonoidHom (e : X ≃ₕ Y) (x : X) :
    (e.fundamentalGroupMulEquiv x).toMonoidHom = FundamentalGroup.map e.toFun x :=
  rfl

end ContinuousMap.HomotopyEquiv
