import StacksProject_2024.Chap10.Lemma_10_66_11
import StacksProject_2024.Chap29.Lemma_29_25_4
import StacksProject_2024.Chap31.Lemma_31_5_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f]
variable (ℱ : X.Modules) [ℱ.IsQuasicoherent]

/- Refine triage:
* `source-facing`: the Stacks item is the image inclusion for weakly associated points of an
  affine pushforward.
* `core/canonical`: the owners are `Scheme.Modules.pushforward`, `IsAffineHom`, and
  `Scheme.Modules.weakAss`.
* `bridge/view`: Chapter 10 supplies the affine ring-level image inclusion through
  `weaklyAssociatedPrimes.subset_comap_image`, while the companion theorem below repackages the set
  inclusion as an explicit witness statement for downstream use. -/

/-- Lemma 31.6.1: let `f : X ⟶ S` be an affine morphism of schemes and let `\mathcal F` be a
quasi-coherent `\mathcal O_X`-module. Then the weakly associated points of the pushforward
`f_* \mathcal F` are contained in the image under `f` of the weakly associated points of
`\mathcal F`. -/
@[stacks 05EX]
theorem weakAss_pushforward_subset_image_of_isAffine :
    ((Scheme.Modules.pushforward f).obj ℱ).weakAss ⊆ f.base '' ℱ.weakAss := sorry

/-- Pointwise form of Lemma 31.6.1: every weakly associated point of `f_* \mathcal F` comes from
some weakly associated point of `\mathcal F`. -/
theorem exists_mem_weakAss_of_mem_weakAss_pushforward_of_isAffine
    {s : S} (hs : s ∈ ((Scheme.Modules.pushforward f).obj ℱ).weakAss) :
    ∃ x : X, x ∈ ℱ.weakAss ∧ f.base x = s := by
  exact weakAss_pushforward_subset_image_of_isAffine f ℱ hs

end AlgebraicGeometry.Scheme.Modules
