import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_3
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_4

noncomputable section

universe u

open scoped Representation

namespace Representation

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A
local notation:max "P⁺[" R "](" G ")" =>
  Set.range fun P : FiniteProjectiveGroupAlgebraModule R G ↦ [P]ₚ₀

/-- Helper for Exercise 16-16.3-8: positivity of a projective class should reflect back along the
reduction homomorphism `P₀[A](G) → P₀[k](G)`. -/
theorem mem_projectivePositiveSubset_of_reduction_mem_local
    {x : P₀[A](G)}
    (hx : projectiveGrothendieckReductionEquiv (A := A) (G := G) x ∈ P⁺[k](G)) :
    x ∈ P⁺[A](G) := by
  -- Route correction: the source-faithful proof must use Lemma 22's positive-cone description,
  -- not the Henselian lift theorem from Chapter 14, since the current statement has no
  -- Henselian hypothesis.
  -- TODO: expose the minimal basis-level positive-cone corollary on this import surface and use
  -- it to reflect `P⁺[k](G)` membership back across `projectiveGrothendieckReductionEquiv`.
  sorry

end

end Representation
