import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe w vC vD uC uD

noncomputable section

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (u : C ⥤ D)
variable {A : Type w} [Category A]
variable [u.Full] [u.Faithful]

/- Domain-style sampling for Lemma 7.21.7:
- primary domain: adjunctions on `A`-valued sheaf categories induced by continuous and
  cocontinuous functors of sites;
- sampled owner API:
  `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`,
  `Functor.sheafAdjunctionContinuous`,
  `Functor.sheafAdjunctionCocontinuous`,
  `Functor.lanAdjunction`,
  `Functor.ranAdjunction`;
- source/core/bridge triage:
  `source-facing`: the two canonical Stacks maps
    `ℱ ⟶ g⁻¹ g_! ℱ` and `g⁻¹ g_* ℱ ⟶ ℱ`;
  `core/canonical`: for clause `(1)`, the source-facing lower shriek `g_!` is owned by the
    sheafified left Kan extension adjunction
    `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`, while the chapter's chosen
    owner `u.sheafAdjunctionContinuous A J K` is the canonical bridge-view obtained from the same
    inverse-image functor; for clause `(2)`, the owner is
    `u.sheafAdjunctionCocontinuous A J K`;
  `bridge/view`: this file keeps the public `IsIso` consequences on the canonical unit and
    counit components, but clause `(1)` should be driven by the construction-level lower-shriek
    owner rather than by a bare abstract `IsRightAdjoint` placeholder.

Primitive data are the site functor `u` and its full faithfulness, together with the
owner-specific adjunction-existence hypotheses: for clause `(1)`, the sheafification and left
Kan-extension data defining the source-facing lower shriek `g_!`; for clause `(2)`, continuity,
cocontinuity, and pointwise right Kan extensions for the cocontinuous direct image. The `IsIso`
assertions are derived API of those owners, so the public surface should stay on the canonical
unit and counit morphisms rather than introducing a second package around them.
-/

section

variable [u.IsContinuous J K]
variable [HasWeakSheafify K A]
variable [∀ P : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension P]

-- Proof sketch: realize `g_!` by the sheafified left Kan extension along `u.op`, whose presheaf
-- unit is invertible for fully faithful `u.op`; then transport that source-facing construction to
-- the chapter's chosen owner `u.sheafAdjunctionContinuous`.
/-- Lemma 7.21.7 (1): for a fully faithful continuous functor of sites, the
canonical map from a sheaf on `C` to `g⁻¹ g_!` of that sheaf is an isomorphism. -/
instance unit_isIso_sheafAdjunctionContinuous_of_fullyFaithful
    (ℱ : Sheaf J A) :
    IsIso ((u.sheafAdjunctionContinuous A J K).unit.app ℱ) := by
  sorry

end

section

variable [u.IsContinuous J K] [u.IsCocontinuous J K]

-- Proof sketch: identify `g_*` with `u.sheafPushforwardCocontinuous` and compare its counit with
-- the counit of right Kan extension along the fully faithful functor `u.op`.
/-- Lemma 7.21.7 (2): for a fully faithful continuous and cocontinuous functor of sites, the
canonical map from `g⁻¹ g_*` of a sheaf on `C` back to the original sheaf is an isomorphism. -/
instance counit_isIso_sheafAdjunctionCocontinuous_of_fullyFaithful
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension P]
    (ℱ : Sheaf J A) :
    IsIso ((u.sheafAdjunctionCocontinuous A J K).counit.app ℱ) := by
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf J A)]
  change IsIso (((u.sheafAdjunctionCocontinuous A J K).counit.app ℱ).hom)
  simpa [u.sheafAdjunctionCocontinuous_counit_app_hom A J K ℱ] using
    (inferInstance : IsIso ((u.op.ranAdjunction A).counit.app ℱ.obj))

end
