import Mathlib
import StacksProject_2024.stacks_project.Chap28.Lemma_28_24_5

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` confirmed the canonical scheme-module pushforward owner
-- `Scheme.Modules.pushforward`; the local closed-support owner is already the kernel-model
-- `sectionsWithSupportIn` from Lemma 28.24.5, so the source statement is best exposed as equality
-- of the pushed-forward image subsheaf with the target closed-support subsheaf on every open.

/-- Lemma 28.24.7: for a quasi-compact and quasi-separated morphism `f : X ⟶ Y`, the pushforward
of the subsheaf of `ℱ` supported in `f ⁻¹' Z` is, sectionwise on every open of `Y`, the subsheaf
of `f_* ℱ` supported in `Z`. -/
@[stacks 07ZQ]
theorem range_pushforward_sectionsWithSupportInι_app_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (Z : TopologicalSpace.Closeds Y)
    (hretro : IsRetrocompact ((openComplement Z : Y.Opens) : Set Y))
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (U : Y.Opens) :
    Set.range (((pushforward f).map
        (sectionsWithSupportInι (Z.preimage f.continuous) ℱ)).app U) =
      Set.range ((sectionsWithSupportInι Z ((pushforward f).obj ℱ)).app U) := sorry

end AlgebraicGeometry.Scheme.Modules
