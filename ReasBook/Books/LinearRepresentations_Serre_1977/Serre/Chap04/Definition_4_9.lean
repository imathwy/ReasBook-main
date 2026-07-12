import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Complex

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

variable {G : Type u} [Group G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]

/--
Helper for Definition 4-9: Lean uses the action-map formulation as the primary owner. A
representation `ρ : Representation ℂ G V` is continuous when `G × V → V`, `(s, x) ↦ ρ s x`, is
continuous. The induced homomorphism into `V ≃L[ℂ] V` is exposed below by
`Representation.toContinuousLinearEquivHom`. -/
class Representation.IsContinuous [TopologicalSpace G] [TopologicalSpace V]
    (ρ : Representation ℂ G V) : Prop where
  /-- The action map attached to `ρ` is continuous. -/
  continuous_action : Continuous fun gv : G × V ↦ ρ gv.1 gv.2

/-- A packaged proof of continuity of the action map supplies the canonical continuity class. -/
instance instRepresentationIsContinuousOfContinuousAction [TopologicalSpace G] [TopologicalSpace V]
    (ρ : Representation ℂ G V)
    [hρ : Fact (Continuous fun gv : G × V ↦ ρ gv.1 gv.2)] :
    Representation.IsContinuous ρ where
  continuous_action := hρ.out

namespace Representation

section Topological

variable [TopologicalSpace G] [TopologicalSpace V]

/-- A continuous representation has a continuous action map. -/
theorem continuousAction (ρ : Representation ℂ G V) [IsContinuous ρ] :
    Continuous fun gv : G × V ↦ ρ gv.1 gv.2 :=
  IsContinuous.continuous_action

/-- Each orbit map of a continuous representation is continuous. -/
theorem continuous_apply (ρ : Representation ℂ G V) [IsContinuous ρ] (v : V) :
    Continuous fun g ↦ ρ g v :=
  continuousAction ρ |>.comp (continuous_id.prodMk continuous_const)

/-- Build `ρ.IsContinuous` from continuity of its action map. -/
theorem isContinuous_of_continuousAction (ρ : Representation ℂ G V)
    (hρ : Continuous fun gv : G × V ↦ ρ gv.1 gv.2) :
    IsContinuous ρ where
  continuous_action := hρ

/-- The Lean owner `ρ.IsContinuous` is exactly continuity of the action map `G × V → V`. -/
theorem isContinuous_iff_continuousAction (ρ : Representation ℂ G V) :
    IsContinuous ρ ↔ Continuous fun gv : G × V ↦ ρ gv.1 gv.2 :=
  ⟨fun hρ ↦ hρ.continuous_action, isContinuous_of_continuousAction ρ⟩

end Topological

section ContinuousLinearEquiv

variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℂ V]
  [T2Space V] [FiniteDimensional ℂ V]

/-- In finite dimension, every linear endomorphism of `V` is canonically a continuous linear
endomorphism. -/
def toContinuousLinearMapMonoidHom : Module.End ℂ V →* (V →L[ℂ] V) where
  toFun := LinearMap.toContinuousLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The canonical `G`-homomorphism attached to `ρ` with values in units of continuous linear
endomorphisms of `V`. -/
def toContinuousLinearMapUnitsHom (ρ : Representation ℂ G V) : G →* (V →L[ℂ] V)ˣ :=
  (Units.map toContinuousLinearMapMonoidHom).comp ρ.asGroupHom

/-- The representation `ρ` induces a homomorphism `G → V ≃L[ℂ] V` into invertible continuous
linear operators on `V`. -/
def toContinuousLinearEquivHom (ρ : Representation ℂ G V) : G →* (V ≃L[ℂ] V) :=
  (ContinuousLinearEquiv.unitsEquiv ℂ V).toMonoidHom.comp ρ.toContinuousLinearMapUnitsHom

/-- The induced continuous linear equivalence is the continuous version of the linear operator
`ρ g`. -/
theorem toContinuousLinearEquivHom_apply (ρ : Representation ℂ G V) (g : G) :
    (ρ.toContinuousLinearEquivHom g : V →L[ℂ] V) = LinearMap.toContinuousLinearMap (ρ g) := by
  rfl

/-- The induced continuous linear equivalence acts on vectors by the same formula as `ρ g`. -/
theorem toContinuousLinearEquivHom_apply_apply (ρ : Representation ℂ G V) (g : G) (v : V) :
    ρ.toContinuousLinearEquivHom g v = ρ g v := by
  rfl

end ContinuousLinearEquiv

section ContinuousLinearEquivTopology

variable [TopologicalSpace V]

-- This snapshot has no ambient topology on `V ≃L[ℂ] V`, so the source-facing bridge uses the
-- induced pointwise topology on automorphisms.
/-- The automorphism group `V ≃L[ℂ] V` carries the topology induced by evaluation on vectors of
`V`. -/
instance instTopologicalSpaceContinuousLinearEquiv : TopologicalSpace (V ≃L[ℂ] V) :=
  TopologicalSpace.induced
    (fun e : V ≃L[ℂ] V ↦ (e : V → V))
    inferInstance

end ContinuousLinearEquivTopology

section TopologicalContinuousLinearEquiv

variable [TopologicalSpace G] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℂ V]
  [T2Space V] [FiniteDimensional ℂ V]

/-- Helper for Definition 4-9: a continuous action gives a continuous map to continuous linear
automorphisms because the target topology is induced from pointwise evaluation. -/
theorem continuousToContinuousLinearEquivHom_of_isContinuous (ρ : Representation ℂ G V)
    [IsContinuous ρ] : Continuous ρ.toContinuousLinearEquivHom := by
  -- Unpack the induced topology and check continuity on each vector orbit map.
  rw [continuous_induced_rng]
  refine continuous_pi fun v => ?_
  -- Each orbit map is already continuous for a continuous representation.
  simpa [Representation.toContinuousLinearEquivHom_apply_apply] using
    (Representation.continuous_apply ρ v)

omit [TopologicalSpace G] in
/-- Helper for Definition 4-9: after expanding a vector in a finite basis, the action is the
corresponding finite sum of the images of the basis vectors. -/
theorem action_eq_sum_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ V)
    (ρ : Representation ℂ G V) (g : G) (v : V) :
    ρ g v = ∑ i, b.equivFun v i • ρ.toContinuousLinearEquivHom g (b i) := by
  -- Expand `v` in the chosen basis and distribute the linear action across the sum.
  calc
    ρ g v = ρ g (∑ i, b.equivFun v i • b i) := by rw [Module.Basis.sum_equivFun]
    _ = ∑ i, ρ g (b.equivFun v i • b i) := by
      rw [_root_.map_sum]
    _ = ∑ i, b.equivFun v i • ρ g (b i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [LinearMap.map_smulₛₗ, RingHom.id_apply]
    _ = ∑ i, b.equivFun v i • ρ.toContinuousLinearEquivHom g (b i) := by
      simp only [Representation.toContinuousLinearEquivHom_apply_apply]

/-- Helper for Definition 4-9: continuity into the induced topology on `V ≃L[ℂ] V` is equivalent
to continuity of the underlying function-valued map. -/
theorem continuousCoeFun_of_continuousToContinuousLinearEquivHom (ρ : Representation ℂ G V)
    (hρ : Continuous ρ.toContinuousLinearEquivHom) :
    Continuous fun g ↦ ((ρ.toContinuousLinearEquivHom g : V ≃L[ℂ] V) : V → V) := by
  -- This is exactly the induced-topology characterization of continuity.
  rw [continuous_induced_rng] at hρ
  exact hρ

/-- Helper for Definition 4-9: continuity of `ρ.toContinuousLinearEquivHom` implies continuity of
the action map `G × V → V`. -/
theorem continuousAction_of_continuousToContinuousLinearEquivHom
    (ρ : Representation ℂ G V) (hρ : Continuous ρ.toContinuousLinearEquivHom) :
    Continuous fun gv : G × V ↦ ρ gv.1 gv.2 := by
  let b : Module.Basis (Module.Basis.ofVectorSpaceIndex ℂ V) ℂ V :=
    Module.Basis.ofVectorSpace ℂ V
  letI : Fintype (Module.Basis.ofVectorSpaceIndex ℂ V) :=
    Fintype.ofFinite (Module.Basis.ofVectorSpaceIndex ℂ V)
  have hcoord : Continuous fun gv : G × V ↦ b.equivFun gv.2 := by
    -- Finite-dimensional coordinates are continuous in the vector variable.
    exact (continuous_equivFun_basis b).comp continuous_snd
  have hcoe :
      Continuous fun g ↦ ((ρ.toContinuousLinearEquivHom g : V ≃L[ℂ] V) : V → V) :=
    continuousCoeFun_of_continuousToContinuousLinearEquivHom ρ hρ
  have horbit (i : Module.Basis.ofVectorSpaceIndex ℂ V) :
      Continuous fun g ↦ ρ.toContinuousLinearEquivHom g (b i) := by
    -- Evaluate the function-valued map at the fixed basis vector `b i`.
    simpa using (_root_.continuous_apply (b i)).comp hcoe
  have hsum :
      Continuous fun gv : G × V ↦
        ∑ i, b.equivFun gv.2 i • ρ.toContinuousLinearEquivHom gv.1 (b i) := by
    -- Each summand is a product of a continuous coordinate function and a continuous orbit map.
    refine continuous_finset_sum Finset.univ fun i _ => ?_
    exact ((_root_.continuous_apply i).comp hcoord).smul ((horbit i).comp continuous_fst)
  have hrewrite :
      (fun gv : G × V ↦ ρ gv.1 gv.2) =
        fun gv : G × V ↦ ∑ i, b.equivFun gv.2 i • ρ.toContinuousLinearEquivHom gv.1 (b i) := by
    -- The action coincides pointwise with its basis expansion.
    funext gv
    exact action_eq_sum_basis b ρ gv.1 gv.2
  rw [hrewrite]
  exact hsum

/-- Definition 4-9: for a finite-dimensional complex representation `ρ`, continuity of the action
map is equivalent to continuity of the induced homomorphism
`ρ.toContinuousLinearEquivHom : G → V ≃L[ℂ] V`. -/
theorem isContinuous_iff_continuousToContinuousLinearEquivHom (ρ : Representation ℂ G V) :
    IsContinuous ρ ↔ Continuous ρ.toContinuousLinearEquivHom := by
  constructor
  · intro hρ
    -- The forward implication is the induced-topology reformulation of orbit-map continuity.
    letI : IsContinuous ρ := hρ
    exact continuousToContinuousLinearEquivHom_of_isContinuous ρ
  · intro hρ
    -- The reverse implication rebuilds action continuity from the finite-basis expansion.
    exact isContinuous_of_continuousAction ρ
      (continuousAction_of_continuousToContinuousLinearEquivHom ρ hρ)

/-- A continuous representation has a continuous induced homomorphism
`ρ.toContinuousLinearEquivHom : G → V ≃L[ℂ] V`. -/
theorem continuous_toContinuousLinearEquivHom (ρ : Representation ℂ G V) [IsContinuous ρ] :
    Continuous ρ.toContinuousLinearEquivHom :=
  (isContinuous_iff_continuousToContinuousLinearEquivHom ρ).mp inferInstance

end TopologicalContinuousLinearEquiv

end Representation

end
