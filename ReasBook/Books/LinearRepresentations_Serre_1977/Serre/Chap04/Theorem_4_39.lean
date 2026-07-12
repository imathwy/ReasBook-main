import Mathlib.RepresentationTheory.Irreducible
import LinearRepresentations_Serre_1977.Chap04.Definition_4_9

noncomputable section

universe u v

namespace Representation

section

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- Theorem 4-39 — Abelian Compact Groups: a compact group `G` is abelian if and only if every
irreducible finite-dimensional continuous complex representation of `G` has degree `1`. Lean
records “degree `1`” as `Module.finrank ℂ W = 1`, and the left side is expressed by the canonical
owner `IsMulCommutative G`. -/
theorem abelian_iff_finrank_eq_one_of_isIrreducible :
    IsMulCommutative G ↔
      ∀ {W : Type v} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
        [IsTopologicalAddGroup W] [ContinuousSMul ℂ W] [T2Space W] [FiniteDimensional ℂ W]
        (π : Representation ℂ G W) [π.IsContinuous] [π.IsIrreducible],
          Module.finrank ℂ W = 1 := sorry

end

end Representation
