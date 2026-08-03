module

public import Mathlib.Logic.Function.Basic

public section

namespace Function

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}

namespace Surjective

/-- A map constant on the fibers of a surjective map factors through its codomain. -/
theorem exists_comp_eq {p : X → Y} (hp : Surjective p) {g : X → Z}
    (hg : g.FactorsThrough p) : ∃ f : Y → Z, f ∘ p = g := by
  obtain ⟨s, hs⟩ := hp.hasRightInverse
  exact ⟨g ∘ s, funext fun x ↦ hg (hs (p x))⟩

/-- The factorization of a map through a surjective map is unique. -/
theorem existsUnique_comp_eq {p : X → Y} (hp : Surjective p) {g : X → Z}
    (hg : g.FactorsThrough p) : ∃! f : Y → Z, f ∘ p = g := by
  obtain ⟨f, hfp⟩ := hp.exists_comp_eq hg
  refine ⟨f, hfp, ?_⟩
  intro f' hf'p
  exact hp.injective_comp_right (hf'p.trans hfp.symm)

end Surjective

end Function
