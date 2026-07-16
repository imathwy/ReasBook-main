import StacksProject_2024.stacks_project.Chap31.Lemma_31_5_8

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f]
variable (ℱ : X.Modules) [ℱ.IsQuasicoherent] [IsLocallyNoetherian X]

/- Refine triage:
* `source-facing`: the Stacks item identifies the associated and weakly associated points of an
  affine pushforward over a locally Noetherian source.
* `core/canonical`: the owners are `Scheme.Modules.pushforward`, `IsAffineHom`,
  `Scheme.Modules.associatedPoints`, and `Scheme.Modules.weakAss`.
* `bridge/view`: the pointwise `mem_*_iff` lemmas expose the set-level source equalities in the
  forms downstream files actually rewrite with. -/

/-- Lemma 31.6.2 (1): let `f : X ⟶ S` be an affine morphism of schemes and let `\mathcal F` be a
quasi-coherent `\mathcal O_X`-module. If `X` is locally Noetherian, then the image of the
associated points of `\mathcal F` is the set of associated points of `f_* \mathcal F`. -/
@[stacks 05EY]
theorem image_associatedPoints_eq_associatedPoints_pushforward_of_isAffine_of_isLocallyNoetherian :
    f.base '' ℱ.associatedPoints =
      ((Scheme.Modules.pushforward f).obj ℱ).associatedPoints := sorry

/-- Lemma 31.6.2 (2): let `f : X ⟶ S` be an affine morphism of schemes and let `\mathcal F` be a
quasi-coherent `\mathcal O_X`-module. If `X` is locally Noetherian, then the associated points of
`f_* \mathcal F` are exactly the weakly associated points of `f_* \mathcal F`. -/
@[stacks 05EY]
theorem associatedPoints_pushforward_eq_weakAss_pushforward_of_isAffine_of_isLocallyNoetherian :
    ((Scheme.Modules.pushforward f).obj ℱ).associatedPoints =
      ((Scheme.Modules.pushforward f).obj ℱ).weakAss := sorry

/-- Lemma 31.6.2 (3): let `f : X ⟶ S` be an affine morphism of schemes and let `\mathcal F` be a
quasi-coherent `\mathcal O_X`-module. If `X` is locally Noetherian, then the weakly associated
points of `f_* \mathcal F` are the image under `f` of the weakly associated points of
`\mathcal F`. -/
@[stacks 05EY]
theorem weakAss_pushforward_eq_image_of_isAffine_of_isLocallyNoetherian :
    ((Scheme.Modules.pushforward f).obj ℱ).weakAss = f.base '' ℱ.weakAss := by
  rw [← associatedPoints_pushforward_eq_weakAss_pushforward_of_isAffine_of_isLocallyNoetherian
    f ℱ]
  rw [← image_associatedPoints_eq_associatedPoints_pushforward_of_isAffine_of_isLocallyNoetherian
    f ℱ]
  rw [associatedPoints_eq_weakAss_of_isLocallyNoetherian ℱ]

/-- Pointwise form of Lemma 31.6.2 (1): a point of `S` is associated to `f_* \mathcal F` exactly
when it is the image of an associated point of `\mathcal F`. -/
theorem mem_associatedPoints_pushforward_iff_exists_mem_associatedPoints_of_isAffine_of_isLocallyNoetherian
    (s : S) :
    s ∈ ((Scheme.Modules.pushforward f).obj ℱ).associatedPoints ↔
      ∃ x : X, x ∈ ℱ.associatedPoints ∧ f.base x = s := by
  rw [← image_associatedPoints_eq_associatedPoints_pushforward_of_isAffine_of_isLocallyNoetherian
    f ℱ]
  simpa [Set.mem_image]

/-- Pointwise form of Lemma 31.6.2 (2): on the affine pushforward from a locally Noetherian
source, associated and weakly associated points coincide pointwise. -/
theorem mem_associatedPoints_pushforward_iff_mem_weakAss_pushforward_of_isAffine_of_isLocallyNoetherian
    (s : S) :
    s ∈ ((Scheme.Modules.pushforward f).obj ℱ).associatedPoints ↔
      s ∈ ((Scheme.Modules.pushforward f).obj ℱ).weakAss := by
  rw [associatedPoints_pushforward_eq_weakAss_pushforward_of_isAffine_of_isLocallyNoetherian
    f ℱ]

/-- Pointwise form of Lemma 31.6.2 (3): a point of `S` is weakly associated to `f_* \mathcal F`
exactly when it is the image of a weakly associated point of `\mathcal F`. -/
theorem mem_weakAss_pushforward_iff_exists_mem_weakAss_of_isAffine_of_isLocallyNoetherian
    (s : S) :
    s ∈ ((Scheme.Modules.pushforward f).obj ℱ).weakAss ↔
      ∃ x : X, x ∈ ℱ.weakAss ∧ f.base x = s := by
  rw [weakAss_pushforward_eq_image_of_isAffine_of_isLocallyNoetherian f ℱ]
  simpa [Set.mem_image]

end AlgebraicGeometry.Scheme.Modules
