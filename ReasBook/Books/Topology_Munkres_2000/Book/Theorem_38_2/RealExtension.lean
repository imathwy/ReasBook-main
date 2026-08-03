module

public import Topology_Munkres_2000.Book.Proposition_38_1.StoneCech
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed

@[expose] public section

open scoped BoundedContinuousFunction ContinuousMap

universe u v

namespace Compactification

variable {X : Type u} [TopologicalSpace X]

/-- A compactification has the bounded-real extension property when every bounded continuous
real-valued function has a unique continuous extension along its dense embedding. -/
def ExtendsBoundedContinuousReal (C : Compactification.{u, v} X) : Prop :=
  ∀ f : X →ᵇ ℝ, ∃! g : ContinuousMap C ℝ, ∀ x : X, g (C x) = f x

/-- The Stone–Čech compactification has the bounded-real extension property. -/
theorem stoneCech_extendsBoundedContinuousReal (X : Type u) [TopologicalSpace X] [T35Space X] :
    (stoneCech X).ExtendsBoundedContinuousReal := by
  intro f
  let restricted : X →ᵇ Set.Icc (-‖f‖) ‖f‖ :=
    f.codRestrict (Set.Icc (-‖f‖) ‖f‖) fun x ↦
      ⟨f.neg_norm_le_apply x, f.apply_le_norm x⟩
  let intervalExtension : ContinuousMap (stoneCech X) (Set.Icc (-‖f‖) ‖f‖) :=
    ⟨stoneCechExtend restricted.continuous,
      continuous_stoneCechExtend restricted.continuous⟩
  let extension : ContinuousMap (stoneCech X) ℝ :=
    ContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩ intervalExtension
  refine ⟨extension, ?_, ?_⟩
  · intro x
    simp only [extension, intervalExtension, restricted, stoneCech_apply, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, stoneCechExtend_stoneCechUnit]
    rfl
  · intro g hg
    apply ContinuousMap.ext
    apply congrFun
    apply stoneCech_hom_ext g.continuous extension.continuous
    ext x
    have hx := hg x
    rw [stoneCech_apply] at hx
    rw [Function.comp_apply, Function.comp_apply, hx]
    simp only [extension, intervalExtension, restricted, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, stoneCechExtend_stoneCechUnit]
    rfl

end Compactification

end
