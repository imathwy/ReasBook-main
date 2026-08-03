module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Homotopy.Lifting

public section

universe u v

namespace IsCoveringMap

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- Helper for Exercise 54.8: a covering map between path-connected spaces is surjective. -/
lemma surjective_of_pathConnected {p : E → B} (hp : IsCoveringMap p) [PathConnectedSpace E]
    [PathConnectedSpace B] : Function.Surjective p := by
  -- Lift a path from the image of a fixed point to the prescribed base point.
  let e₀ : E := Classical.choice (PathConnectedSpace.nonempty (X := E))
  intro b
  let γ : Path (p e₀) b := PathConnectedSpace.somePath (p e₀) b
  refine ⟨hp.liftPath γ e₀ γ.source 1, ?_⟩
  -- The endpoint of the lift maps to the endpoint of the original path.
  exact (congr_fun (hp.liftPath_lifts γ e₀ γ.source) 1).trans γ.target

/-- Helper for Exercise 54.8: a path in the total space whose endpoints have the same image
has equal endpoints when the base is simply connected. -/
lemma eq_of_path_of_eq_image {p : E → B} (hp : IsCoveringMap p) [SimplyConnectedSpace B]
    {e₁ e₂ : E} (γ : Path e₁ e₂) (h : p e₁ = p e₂) : e₁ = e₂ := by
  -- Regard the projected path as a loop and compare it with the constant loop.
  let baseLoop : Path (p e₁) (p e₁) := (γ.map hp.continuous).cast rfl h
  let constLoop : Path (p e₁) (p e₁) := Path.refl (p e₁)
  have gamma_eq : (γ : C(unitInterval, E)) = hp.liftPath baseLoop e₁ baseLoop.source := by
    apply (hp.eq_liftPath_iff' _).mpr
    constructor
    · funext t
      simp [baseLoop]
    · exact γ.source
  -- Homotopic base loops have lifts with the same endpoint.
  have endpoint_eq := hp.liftPath_apply_one_eq_of_homotopicRel
    (SimplyConnectedSpace.paths_homotopic baseLoop constLoop) e₁ baseLoop.source constLoop.source
  have const_eq : (Path.refl e₁).toContinuousMap =
      hp.liftPath constLoop.toContinuousMap e₁ constLoop.source := by
    apply (hp.eq_liftPath_iff' _).mpr
    constructor
    · funext t
      simp [constLoop]
    · exact (Path.refl e₁).source
  -- Read the endpoint equality through the two concrete lift identifications.
  calc
    e₁ = (Path.refl e₁) 1 := (Path.refl e₁).target.symm
    _ = hp.liftPath constLoop.toContinuousMap e₁ constLoop.source 1 :=
      congrArg (fun f : C(unitInterval, E) ↦ f 1) const_eq
    _ = hp.liftPath baseLoop.toContinuousMap e₁ baseLoop.source 1 := endpoint_eq.symm
    _ = γ 1 := (congrArg (fun f : C(unitInterval, E) ↦ f 1) gamma_eq).symm
    _ = e₂ := γ.target

/-- Helper for Exercise 54.8: a covering map with path-connected total space and simply
connected base is injective. -/
lemma injective_of_pathConnected_of_simplyConnected {p : E → B} (hp : IsCoveringMap p)
    [PathConnectedSpace E] [SimplyConnectedSpace B] : Function.Injective p := by
  -- Join two points in one fiber and apply uniqueness of the endpoint of the lifted loop.
  intro e₁ e₂ h
  exact hp.eq_of_path_of_eq_image (PathConnectedSpace.somePath e₁ e₂) h

/-- Exercise 54.8. A covering map from a path-connected space to a simply connected
space is a homeomorphism. -/
theorem isHomeomorph {p : E → B} (hp : IsCoveringMap p) [PathConnectedSpace E]
    [SimplyConnectedSpace B] : IsHomeomorph p := by
  -- Continuity and openness come from the covering map; the helpers supply bijectivity.
  exact ⟨hp.continuous, hp.isOpenMap,
    hp.injective_of_pathConnected_of_simplyConnected, hp.surjective_of_pathConnected⟩

end IsCoveringMap
