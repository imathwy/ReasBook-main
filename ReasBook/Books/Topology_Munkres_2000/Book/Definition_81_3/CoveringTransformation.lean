module

public import Topology_Munkres_2000.Book.Definition_81_1.CoveringTransformation
public import Mathlib.Topology.Covering.Basic

public section

open scoped CoveringTransformation

universe u v

namespace CoveringTransformation

variable {E : Type u} {B : Type v} [TopologicalSpace E]
variable {p : E → B}

/-- A covering transformation sends a chosen point to the same fiber of `p`. -/
theorem eval_mem_fiber (b₀ : B) (e₀ : E) (he₀ : p e₀ = b₀)
    (h : 𝒞(E, p, B)) : h • e₀ ∈ p ⁻¹' {b₀} := by
  exact (map_smul p h e₀).trans he₀

/-- Evaluation at `e₀` gives a point of the fiber over `b₀`. -/
@[expose]
def evalInFiber (b₀ : B) (e₀ : E) (he₀ : p e₀ = b₀) :
    𝒞(E, p, B) → p ⁻¹' {b₀} :=
  fun h ↦ ⟨h • e₀, eval_mem_fiber b₀ e₀ he₀ h⟩

/-- Evaluation in the fiber has underlying value `h • e₀`. -/
theorem evalInFiber_apply (b₀ : B) (e₀ : E) (he₀ : p e₀ = b₀)
    (h : 𝒞(E, p, B)) :
    (evalInFiber b₀ e₀ he₀ h : E) = h • e₀ := rfl

/-- For a covering map with preconnected total space, a covering transformation is uniquely
determined by its value at one point. -/
theorem evalInFiber_injective [TopologicalSpace B] (hp : IsCoveringMap p)
    [PreconnectedSpace E]
    (b₀ : B) (e₀ : E) (he₀ : p e₀ = b₀) :
    Function.Injective
      (evalInFiber b₀ e₀ he₀ : 𝒞(E, p, B) → p ⁻¹' {b₀}) := by
  intro h k heval
  -- Equality in the fiber gives agreement of the two transformations at the chosen point.
  have hbase : h • e₀ = k • e₀ := by
    simpa only [evalInFiber_apply] using congrArg Subtype.val heval
  -- Membership in the transformation group says both homeomorphisms lie over `p`.
  have hprojection : p ∘ (h : E → E) = p ∘ (k : E → E) :=
    ((mem_group p h.1).mp h.2).trans ((mem_group p k.1).mp k.2).symm
  -- Uniqueness of lifts upgrades agreement at one point to equality of the underlying maps.
  have hmaps : (h : E → E) = k :=
    hp.eq_of_comp_eq h.1.continuous k.1.continuous
      hprojection e₀ hbase
  -- Extensionality then recovers equality first of homeomorphisms and then of subgroup elements.
  apply Subtype.ext
  apply Homeomorph.ext
  exact congrFun hmaps

end CoveringTransformation
