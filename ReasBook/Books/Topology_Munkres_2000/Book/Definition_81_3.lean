module

public import Topology_Munkres_2000.Book.Definition_81_1.CoveringTransformation
import Topology_Munkres_2000.Book.Theorem_54_6.Monodromy
public import Mathlib.Topology.Covering.Basic

public section

open scoped CoveringTransformation

universe u v

/- Definition 81.3 (1): The lifting correspondence `Φ` from right cosets of the induced
fundamental-group image to the fiber over `b₀`. -/
#check IsCoveringMap.monodromyRightCosetMap

/- Definition 81.3 (2): For a path-connected covering space, the lifting correspondence `Φ`
is a bijection. -/
#check IsCoveringMap.monodromyRightCosetMap_bijective

/- Definition 81.3 (3): Evaluation at `e₀` defines the correspondence `Ψ` from covering
transformations to the fiber over `b₀`. -/
namespace CoveringTransformation

variable {E : Type u} {B : Type v} [TopologicalSpace E]
variable {p : E → B}

/-- Helper for Definition 81.3: a covering transformation sends a chosen point to the same
fiber of `p`. -/
theorem eval_mem_fiber (b₀ : B) (e₀ : E) (he₀ : p e₀ = b₀)
    (h : 𝒞(E, p, B)) : h • e₀ ∈ p ⁻¹' {b₀} := by
  exact (map_smul p h e₀).trans he₀

/-- The correspondence `Ψ` from Definition 81.3 evaluates a covering transformation at `e₀`. -/
@[expose]
def evalInFiber (b₀ : B) (e₀ : E) (he₀ : p e₀ = b₀) :
    𝒞(E, p, B) → p ⁻¹' {b₀} :=
  fun h ↦ ⟨h • e₀, eval_mem_fiber b₀ e₀ he₀ h⟩

/-- Helper for Definition 81.3: evaluation in the fiber has underlying value `h • e₀`. -/
theorem evalInFiber_apply (b₀ : B) (e₀ : E) (he₀ : p e₀ = b₀)
    (h : 𝒞(E, p, B)) :
    (evalInFiber b₀ e₀ he₀ h : E) = h • e₀ := rfl

/-- Definition 81.3 (4): Uniqueness of lifts makes the evaluation correspondence `Ψ`
injective. -/
theorem evalInFiber_injective [TopologicalSpace B] (hp : IsCoveringMap p)
    [PreconnectedSpace E]
    (b₀ : B) (e₀ : E) (he₀ : p e₀ = b₀) :
    Function.Injective
      (evalInFiber b₀ e₀ he₀ : 𝒞(E, p, B) → p ⁻¹' {b₀}) := by
  intro h k heval
  -- Equality in the fiber gives agreement of the two transformations at the chosen point.
  have hbase : h • e₀ = k • e₀ := by
    simpa only [evalInFiber_apply] using congrArg Subtype.val heval
  -- Both transformations lie over `p`, so uniqueness of lifts applies.
  have hprojection : p ∘ (h : E → E) = p ∘ (k : E → E) :=
    ((mem_group p h.1).mp h.2).trans ((mem_group p k.1).mp k.2).symm
  have hmaps : (h : E → E) = k :=
    hp.eq_of_comp_eq h.1.continuous k.1.continuous
      hprojection e₀ hbase
  -- Equality of the underlying maps determines the bundled transformations.
  apply Subtype.ext
  apply Homeomorph.ext
  exact congrFun hmaps

end CoveringTransformation
