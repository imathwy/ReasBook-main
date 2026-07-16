import Mathlib.AlgebraicGeometry.Noetherian
import StacksProject_2024.stacks_project.Chap30.Lemma_30_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Semantic recall: `lean_leansearch` surfaced the canonical `IsProper` morphism owner. The
packaged Chapter 29 owner `RelativelyAmple f L` is not dependency-closed in this item check, so
the statement uses its affine-open defining condition directly. Chapter 30 precedent represents
twists as `schemeModuleTwistByTensorPower` and higher direct images as
`((Scheme.Modules.pushforward f).rightDerived p).obj`. The tag evidence is consistent for
Stacks tag `02O1`. -/

variable {X S : Scheme.{u}}

/-- Lemma 30.16.2: let `f : X ⟶ S` be a morphism of schemes, let `F` be a quasi-coherent
`\mathcal O_X`-module, and let `L` be an invertible sheaf on `X`. If `S` is Noetherian, `f` is
proper, `F` is coherent, and `L` is relatively ample on `X/S`, then for all sufficiently large
`n`, all positive-degree higher direct images
`R^p f_*(F ⊗ L^{\otimes n})` vanish. -/
@[stacks 02O1]
theorem properRelativelyAmpleCoherentTwist_higherDirectImage_eventually_isZero
    (f : X ⟶ S) [IsNoetherian S] [IsProper f]
    [HasInjectiveResolutions X.Modules]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsCoherent]
    (L : X.Modules) [MonoidalCategory X.Modules] [Scheme.Modules.Invertible L]
    [QuasiCompact f]
    [∀ U : S.affineOpens,
      MonoidalCategory ((f ⁻¹ᵁ (U : S.Opens)).toScheme.Modules)]
    [∀ U : S.affineOpens,
      Scheme.Modules.Invertible (L.restrict ((f ⁻¹ᵁ (U : S.Opens)).ι))]
    (hL_relativelyAmple : ∀ U : S.affineOpens,
      Scheme.Modules.IsAmple (L.restrict ((f ⁻¹ᵁ (U : S.Opens)).ι))) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ p : ℕ, 0 < p →
      IsZero (((Scheme.Modules.pushforward f).rightDerived p).obj
        (schemeModuleTwistByTensorPower L F (n : ℤ))) := sorry

end AlgebraicGeometry.Scheme.Modules
