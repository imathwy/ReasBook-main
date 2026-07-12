import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-side owner
-- `AlgebraicGeometry.IsLocallyNoetherian`, the affine-cover equivalences
-- `isLocallyNoetherian_iff_of_iSup_eq_top` / `isLocallyNoetherian_of_affine_cover`, and the
-- open-subscheme instance `instIsLocallyNoetherianToScheme`.

variable (X : Scheme.{u})

/-- Lemma 28.5.2 (1): a scheme `X` is locally Noetherian if and only if for every affine open
`U ⊆ X` the ring of sections `Γ(X, U)` is Noetherian. -/
@[stacks 01OW]
theorem isLocallyNoetherian_iff_forall_isNoetherianRing_sections_affineOpen :
    IsLocallyNoetherian X ↔ ∀ U : X.affineOpens, IsNoetherianRing Γ(X, U) := by
  constructor
  · intro hX U
    letI := hX
    simpa using IsLocallyNoetherian.component_noetherian U
  · intro hX
    exact ⟨hX⟩

/-- Lemma 28.5.2 (2): a scheme `X` is locally Noetherian if and only if it admits an affine open
cover by affine opens whose rings of sections are Noetherian. -/
@[stacks 01OW]
theorem isLocallyNoetherian_iff_exists_affineOpenCover_sections_isNoetherianRing :
    IsLocallyNoetherian X ↔
      ∃ 𝒰 : Scheme.AffineOpenCover.{u, u} X,
        ∀ i : 𝒰.I₀, IsNoetherianRing Γ(X, (𝒰.f i).opensRange) := by
  constructor
  · intro hX
    refine ⟨X.affineOpenCover, ?_⟩
    intro i
    exact
      (isLocallyNoetherian_iff_forall_isNoetherianRing_sections_affineOpen X).1 hX
        ⟨(X.affineOpenCover.f i).opensRange, isAffineOpen_opensRange (X.affineOpenCover.f i)⟩
  · rintro ⟨𝒰, h𝒰_noetherian⟩
    let U : 𝒰.I₀ → X.affineOpens :=
      fun i ↦ ⟨(𝒰.f i).opensRange, isAffineOpen_opensRange (𝒰.f i)⟩
    have hU_cover : iSup (fun i ↦ ((U i : X.affineOpens) : X.Opens)) = ⊤ := by
      simpa [U] using 𝒰.openCover.isOpenCover_opensRange.iSup_eq_top
    have hU_noetherian : ∀ i : 𝒰.I₀, IsNoetherianRing Γ(X, U i) := by
      intro i
      simpa [U] using h𝒰_noetherian i
    exact isLocallyNoetherian_of_affine_cover hU_cover hU_noetherian

/-- Lemma 28.5.2 (3): a scheme `X` is locally Noetherian if and only if it admits an open cover by
open subschemes that are locally Noetherian. -/
@[stacks 01OW]
theorem isLocallyNoetherian_iff_exists_openCover_by_isLocallyNoetherian :
    IsLocallyNoetherian X ↔
      ∃ 𝒰 : X.OpenCover, ∀ i : 𝒰.I₀, IsLocallyNoetherian (𝒰.X i) := by
  constructor
  · intro hX
    refine ⟨X.openCoverOfIsOpenCover (fun _ : PUnit ↦ (⊤ : X.Opens)) (by
      change iSup (fun _ : PUnit ↦ (⊤ : X.Opens)) = ⊤
      simp), ?_⟩
    intro i
    letI := hX
    infer_instance
  · rintro ⟨𝒰, h𝒰_noetherian⟩
    exact
      (isLocallyNoetherian_iff_openCover 𝒰).2 <| by
        simpa using h𝒰_noetherian

/-- Lemma 28.5.2 (4): every open subscheme of a locally Noetherian scheme is locally Noetherian.
-/
@[stacks 01OW]
theorem isLocallyNoetherian_toScheme (hX : IsLocallyNoetherian X) (U : X.Opens) :
    IsLocallyNoetherian U.toScheme := by
  letI := hX
  infer_instance

end AlgebraicGeometry
