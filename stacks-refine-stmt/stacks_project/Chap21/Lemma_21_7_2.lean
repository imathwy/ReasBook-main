import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

section

variable {C : Type u} [Category.{u} C]
variable {D : Type u} [Category.{u} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)
variable [u.Full] [u.Faithful] [u.IsContinuous J K] [u.IsCocontinuous J K]
variable [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf J AddCommGrpCat.{u})] [HasExt.{u} (Sheaf K AddCommGrpCat.{u})]

-- Proof sketch: apply Homology, Lemma `12.29.1` to the adjunction
-- `u.sheafPullback AddCommGrpCat J K ⊣ u.sheafPushforwardContinuous AddCommGrpCat J K`.
-- The left adjoint is exact under the site hypotheses from Lemma `7.21.8`, so the right adjoint
-- preserves injective abelian sheaves. Compute cohomology over `U` by injective resolutions on
-- the slice sites `C/U` and `D/u(U)`.
/-- Lemma 21.7.2: if `u : C ⥤ D` satisfies the hypotheses of Sites, Lemma `7.21.8`, then for any
abelian sheaf `F` on `D`, any degree `p`, and any object `U` of `C`, the cohomology of the
inverse image `g⁻¹ F`, formalized as
`(u.sheafPushforwardContinuous AddCommGrpCat J K).obj F`, over `U` is canonically isomorphic to
the cohomology of `F` over `u(U)`. -/
theorem inverseImage_site_cohomology_over_obj_iso
    (F : Sheaf K AddCommGrpCat.{u}) (p : ℕ) (U : C) :
    IsIsomorphic (((u.sheafPushforwardContinuous AddCommGrpCat.{u} J K).obj F).H' p U)
      (F.H' p (u.obj U)) := sorry

variable [HasGlobalSectionsFunctor J AddCommGrpCat.{u}]
variable [HasGlobalSectionsFunctor K AddCommGrpCat.{u}]

-- Proof sketch: this is the global-sections case of the same injective-resolution argument.
-- Since `u.sheafPushforwardContinuous AddCommGrpCat J K` preserves injective objects, the right
-- derived functors of global sections identify on `g⁻¹ F` and on `F`.
/-- For the inverse-image functor attached to `u`, global site cohomology agrees with the global
cohomology of the original sheaf on `D`. -/
theorem inverseImage_site_global_cohomology_iso
    (F : Sheaf K AddCommGrpCat.{u}) (p : ℕ) :
    IsIsomorphic (AddCommGrpCat.of (((u.sheafPushforwardContinuous AddCommGrpCat.{u} J K).obj F).H p))
      (AddCommGrpCat.of (F.H p)) := sorry

end

end Sheaf
end CategoryTheory
