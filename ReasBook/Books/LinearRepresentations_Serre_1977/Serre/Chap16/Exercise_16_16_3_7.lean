import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_3_1.FiniteRepScalarExtension
import LinearRepresentations_Serre_1977.Serre.Chap16.Lemma_16_16_3_1.PositiveConeBridge

noncomputable section

open scoped Representation

universe u

namespace Representation

section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {A' : Type u} [CommRing A'] [IsLocalRing A']
variable {K : Type u} [Field K]
variable {K' : Type u} [Field K'] [Algebra K K']
variable [Algebra A K'] [Algebra A' K']
variable {G : Type u} [Group G] [Finite G]

local notation "eA" => (projectiveGrothendieckBaseChangeHom K' : P₀[A](G) →+ R₀[K'](G))
local notation "eA'" => (projectiveGrothendieckBaseChangeHom K' : P₀[A'](G) →+ R₀[K'](G))
local notation "eK" => (finiteRepGrothendieckScalarExtensionHom K K' G : R₀[K](G) →+ R₀[K'](G))

/-- The source-facing positive subset `P_A^+(G)` viewed in this item file as the set of actual
projective classes in `P₀[A](G)`. -/
private def projectivePositiveSubsetLocal (A : Type u) [CommRing A] (G : Type u) [Group G] :
    Set (P₀[A](G)) :=
  Set.range fun P : FiniteProjectiveGroupAlgebraModule A G ↦ [P]ₚ₀

-- `P⁺[A](G)` notation is provided by `Serre.Chap16.Lemma_16_16_3_1.PositiveConeBridge`
-- (owner `projectivePositiveSubset`), available here via `open scoped Representation`.

/- Domain-style sampling for Exercise 16-16.3-7:
* primary domain: projective and finite-representation Grothendieck groups under base change to a
  common field `K'`;
* relevant owner declarations inspected in this domain:
  `projectiveGrothendieckBaseChangeHom`,
  `finiteRepGrothendieckScalarExtensionHom`,
  `projectivePositiveSubset`,
  `projectiveGrothendieckScalarExtensionHom`;
* best owner abstraction: the existing Chapter `15` homomorphism owners together with their
  canonical additive-subgroup ranges, viewed on this source-facing set-equality surface via the
  usual coercion to sets.

Primitive data vs derived API:
* primitive data: the actual homomorphisms `eA`, `eA'`, and `eK` and the source-facing positive
  subsets `P⁺[A](G)` and `P⁺[A'](G)`;
* derived API: this exercise's image-intersection identity inside the common ambient group
  `R₀[K'](G)`.

Source/core/bridge triage:
* source-facing: the equality comparing the positive images over `A` and `A'` inside `R₀[K'](G)`;
* core/canonical: the Chapter `15` homomorphism owners and their `.range` additive subgroups;
* bridge/view: this theorem, which rewrites the source statement using those canonical owner
  ranges rather than a parallel set-theoretic range wrapper.
-/
-- Proof sketch: rewrite the source-facing subsets `P_A^+(G)`, `P_{A'}^+(G)`, `P_A(G)`,
-- `P_{A'}(G)`, and `R_K(G)` inside the common ambient group `R_K'(G)` using the canonical
-- scalar-extension maps `eA`, `eA'`, and `eK`. The source inclusion `P_{A'}^+(G) ⊆ P_{A'}(G)`
-- becomes the tautological inclusion of `eA' '' P⁺[A'](G)` into the canonical additive-hom range
-- of `eA'`, so the conclusion is the set-theoretic simplification of
-- `(X ∩ (eA').range) ∩ (eK).range` to `X ∩ (eK).range`.
/-- Helper for Exercise 16-16.3-7: the positive image over `A'` is already contained in the
range of the canonical base-change map `eA'`. -/
private lemma image_projectivePositive_inter_range :
    (eA' '' P⁺[A'](G)) ∩ (eA').range = eA' '' P⁺[A'](G) := by
  -- Every point in the image of `eA'` lies in the range of `eA'`.
  exact Set.inter_eq_left.2 <| Set.image_subset_range _ _

/-- Exercise 16-16.3-7: viewed in the common ambient Grothendieck group `R_K'(G)` via the
canonical scalar-extension maps, if the positive image of `P_A(G)` is
`eA '' P⁺[A](G) = (eA' '' P⁺[A'](G)) ∩ (eA).range` and the full image of
`P_A(G)` is `(eA).range = (eA').range ⊓ (eK).range`, then
`eA '' P⁺[A](G) = (eA' '' P⁺[A'](G)) ∩ (eK).range`. The
source-side inclusion
`P_{A'}^+(G) ⊆ P_{A'}(G)` is absorbed here by the automatic inclusion of
`eA' '' P⁺[A'](G)` into `(eA').range`. -/
theorem
    projectivePositiveImage_eq_inter_scalarExtension_range
    (h_positive :
      eA '' P⁺[A](G) =
        (eA' '' P⁺[A'](G)) ∩ (eA).range)
    (h_projective :
      (eA).range = (eA').range ⊓ (eK).range) :
    eA '' P⁺[A](G) =
      (eA' '' P⁺[A'](G)) ∩ (eK).range := by
  -- Rewrite the left-hand side using the given description of the positive image over `A`.
  calc
    eA '' P⁺[A](G)
        = (eA' '' P⁺[A'](G)) ∩ (eA).range :=
          h_positive
    -- Replace the projective image of `A` with the intersection of the `A'`- and `K`-ranges.
    _ = (eA' '' P⁺[A'](G)) ∩ ↑((eA').range ⊓ (eK).range) := by
          rw [h_projective]
    -- The subgroup infimum is the ambient set-theoretic intersection.
    _ = (eA' '' P⁺[A'](G)) ∩ ((eA').range ∩ (eK).range) := by
          rfl
    -- Reassociate so the redundant intersection with `(eA').range` is visible.
    _ = ((eA' '' P⁺[A'](G)) ∩ (eA').range) ∩ (eK).range := by
          rw [Set.inter_assoc]
    -- Collapse that redundant factor using the helper lemma above.
    _ = (eA' '' P⁺[A'](G)) ∩ (eK).range := by
          rw [image_projectivePositive_inter_range]

end

end Representation
