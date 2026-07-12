import StacksProject_2024.Chap17.Definition_17_14_1
import StacksProject_2024.Chap30.Definition_30_11_4
import StacksProject_2024.Chap28.Lemma_28_9_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: Chapter 28 already fixes the source-facing scheme owner `Scheme.Regular`,
-- together with the stalkwise regularity characterizations of Lemma 28.9.2. For the right-hand
-- side, the existing sheaf owner `SheafOfModules.IsFiniteLocallyFree` is the canonical project
-- surface; the source phrase “rank > 0” is represented here by full support.

section

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable (ℱ : X.Modules) [ℱ.IsCoherent]

/-- Lemma 30.11.5: let `X` be a regular scheme, and let `ℱ` be a coherent `\mathcal O_X`-module
with `Supp(ℱ) = X`. Then `ℱ` is Cohen-Macaulay exactly when it is finite locally free. Here the
full-support condition is the project-level encoding of the textbook phrase “finite locally free
of rank `> 0`”. -/
theorem cohenMacaulay_iff_isFiniteLocallyFree_of_regular_of_support_eq_univ
    [Scheme.Regular X] (hsupp : moduleSupport ℱ = Set.univ) :
    CohenMacaulay ℱ ↔ SheafOfModules.IsFiniteLocallyFree ℱ := sorry

/-- Stalkwise regular-locality is a source-faithful bridge to the regular-scheme form of
Lemma 30.11.5. -/
theorem cohenMacaulay_iff_isFiniteLocallyFree_of_regular_stalk_and_support_eq_univ
    (hX : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hsupp : moduleSupport ℱ = Set.univ) :
    CohenMacaulay ℱ ↔ SheafOfModules.IsFiniteLocallyFree ℱ := by
  let hregular : Scheme.Regular X :=
    (Scheme.regular_iff_isLocallyNoetherian_and_forall_isRegularLocalRing_stalk X).2
      ⟨inferInstance, hX⟩
  letI : Scheme.Regular X := hregular
  exact cohenMacaulay_iff_isFiniteLocallyFree_of_regular_of_support_eq_univ ℱ hsupp

end

end AlgebraicGeometry.Scheme.Modules
