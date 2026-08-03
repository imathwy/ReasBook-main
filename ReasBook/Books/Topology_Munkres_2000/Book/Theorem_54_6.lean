module

public import Topology_Munkres_2000.Book.Theorem_54_6.Monodromy

public section

universe u v

namespace IsCoveringMap

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable {p : E → B} (hp : IsCoveringMap p) {e₀ : E} {b₀ : B}

/-- Theorem 54.6 (a). A covering map induces an injective homomorphism on fundamental
groups. -/
theorem inducedFundamentalGroupMap_injective (he₀ : p e₀ = b₀) :
    Function.Injective (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he₀) := by
  -- Apply the injectivity theorem for the canonical induced map.
  exact hp.fundamentalGroupMap_injective he₀

/-- Part (b) of Theorem 54.6: monodromy embeds the right cosets of the induced subgroup
into the fiber. -/
theorem rightCosetMonodromy_injective (he₀ : p e₀ = b₀) :
    Function.Injective (hp.monodromyRightCosetMap he₀) := by
  -- Use the representative-independent endpoint map on right cosets.
  exact hp.monodromyRightCosetMap_injective he₀

/-- The path-connected case of Theorem 54.6 (b): monodromy gives a bijection from the
right cosets of the induced subgroup to the fiber. -/
theorem rightCosetMonodromy_bijective (he₀ : p e₀ = b₀) [PathConnectedSpace E] :
    Function.Bijective (hp.monodromyRightCosetMap he₀) := by
  -- Path connectedness supplies surjectivity in addition to the coset injection.
  exact hp.monodromyRightCosetMap_bijective he₀

/-- Part (c) of Theorem 54.6: a based loop class lies in the induced subgroup exactly
when its lift from the selected point is again a loop. -/
theorem loopClass_mem_inducedRange_iff_liftPath_one (he₀ : p e₀ = b₀)
    (f : Path b₀ b₀) :
    FundamentalGroup.fromPath (.mk f) ∈ hp.fundamentalGroupMapRange he₀ ↔
      hp.liftPath f e₀ (f.source.trans he₀.symm) 1 = e₀ := by
  -- Invoke the canonical lifted-endpoint characterization of subgroup membership.
  exact hp.loopClass_mem_range_iff_liftPath_one he₀ f

end IsCoveringMap
