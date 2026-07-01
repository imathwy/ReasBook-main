import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace TopCat
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory
namespace Sheaf

/-- A compatible inverse-limit situation of abelian sheaves on a cofiltered diagram of topological
spaces, together with the chosen limiting sheaf on the inverse limit space. -/
structure SpectralInverseLimitAbelianSheafSituation
    {I : Type u} [Category.{v} I] (F : I ⥤ TopCat.{max u v}) [HasLimit F] where
  /-- The abelian sheaf `\mathcal F_i` on the stage `X_i`. -/
  stageSheaf : ∀ i : I, (F.obj i).Sheaf AddCommGrpCat.{max u v}
  /-- The transition map `\mathcal F_i \to f_{a,*}\mathcal F_j` attached to `a : j ⟶ i`. -/
  stageMap : ∀ {j i : I} (a : j ⟶ i),
    stageSheaf i ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{max u v} (F.map a)).obj (stageSheaf j)
  /-- The sheaf `\mathcal F` on the inverse-limit space `X = \varprojlim X_i`. -/
  limitSheaf : (limit F).Sheaf AddCommGrpCat.{max u v}
  /-- The comparison map `\mathcal F_i \to p_{i,*}\mathcal F` to the pushforward of the limit
  sheaf along the projection `p_i : X \to X_i`. -/
  limitMap : ∀ i : I,
    stageSheaf i ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{max u v} (limit.π F i)).obj limitSheaf
  /-- For a fixed stage `i`, quasi-compact open `U_i`, and degree `p`, the chosen over-category
  diagram `a : j ⟶ i ↦ H^p(f_a^{-1}(U_i), \mathcal F_j)`, expressed in the library-facing
  pushforward form. -/
  projectionOpenCohomologyDiagram :
    ∀ (i : I) (_Ui : Opens (F.obj i)) (_p : ℕ), (Over i)ᵒᵖ ⥤ AddCommGrpCat.{max u v}

variable {X Y : TopCat.{u}}

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
variable [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})]

-- Proof sketch: pushforward along `f` is right adjoint to inverse image, and inverse image of
-- abelian sheaves is exact, so pushforward preserves injective resolutions. Since sections of
-- `f_* \mathcal F` on `U` are sections of `\mathcal F` on `f^{-1}(U)`, the derived functors
-- computing these two cohomology groups agree.
/-- The cohomology of the pushforward sheaf on an open `U ⊆ Y` identifies with the cohomology of
the original sheaf on the inverse-image open `f^{-1}(U)`. -/
theorem pushforward_cohomologyOnOpen_isomorphic_preimage
    (f : X ⟶ Y) (ℱ : X.Sheaf AddCommGrpCat.{u}) (U : Opens Y) (p : ℕ) :
    IsIsomorphic (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj ℱ).H' p U)
      (ℱ.H' p ((Opens.map f).obj U)) := sorry

variable {I : Type u} [Category.{v} I] [IsCofiltered I]
variable (F : I ⥤ TopCat.{max u v}) [HasLimit F]
variable [∀ j : I, SpectralSpace ↥(F.obj j)]
variable [HasSheafify (Opens.grothendieckTopology ↥(limit F)) AddCommGrpCat.{max u v}]
variable [HasExt.{max u v} (Sheaf (Opens.grothendieckTopology ↥(limit F))
  AddCommGrpCat.{max u v})]

-- Proof sketch: first identify the source with the colimit of the degree-`p` cohomology objects
-- of the stage sheaves over the over-category of arrows `a : j ⟶ i`, using the pushforward form
-- of cohomology on inverse-image opens. Then choose compatible injective embeddings stagewise,
-- reduce to vanishing for the colimit sheaf on quasi-compact opens, and finish with the Čech
-- acyclicity argument from the preceding lemmas together with exactness of filtered colimits.
/-- Lemma 20.19.3: in the inverse-limit situation for spectral spaces and compatible abelian
sheaves, if `U_i ⊆ X_i` is quasi-compact open, then the filtered colimit of the groups
`H^p(f_a^{-1}(U_i), \mathcal F_j)` over arrows `a : j ⟶ i` is canonically isomorphic to
`H^p(p_i^{-1}(U_i), \mathcal F)`. -/
theorem spectralInverseLimit_projectionOpenCohomology_isomorphic
    (S : SpectralInverseLimitAbelianSheafSituation F)
    (i : I) (Ui : Opens (F.obj i)) (hUi : IsCompact (Ui : Set (F.obj i))) (p : ℕ)
    [HasColimit (S.projectionOpenCohomologyDiagram i Ui p)] :
    IsIsomorphic
      (colimit (S.projectionOpenCohomologyDiagram i Ui p))
      (S.limitSheaf.H' p ((Opens.map (limit.π F i)).obj Ui)) := sorry

-- Proof sketch: apply Lemma `20.19.3` to the top open `U_i = X_i`, which is quasi-compact for a
-- spectral space, and rewrite `p_i^{-1}(X_i)` as the whole inverse-limit space `X`.
/-- The global cohomology of the limit sheaf is the filtered colimit of the stagewise global
cohomology groups in the inverse-limit situation of Lemma `20.19.3`. -/
theorem spectralInverseLimit_globalCohomology_isomorphic
    (S : SpectralInverseLimitAbelianSheafSituation F) (i : I) (p : ℕ)
    [HasColimit (S.projectionOpenCohomologyDiagram i (⊤ : Opens (F.obj i)) p)] :
    IsIsomorphic
      (colimit (S.projectionOpenCohomologyDiagram i (⊤ : Opens (F.obj i)) p))
      (S.limitSheaf.H' p (⊤ : Opens ↥(limit F))) := sorry

end Sheaf
end CategoryTheory
