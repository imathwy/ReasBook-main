import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap29.Lemma_29_11_5_Core
import StacksProject_2024.Chap34.Definition_34_7_8

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open Opposite
open RingedSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme

-- Semantic recall: `lean_leansearch` only surfaced absolute affine-spectrum owners, while local
-- project inspection verified the available relative owners are `Scheme.AffineOver` on the scheme
-- side and same-site `\mathcal O_S`-algebra/module infrastructure via `Under S.sheaf`,
-- `restrictionAlong`, and `unitModule` on the sheaf side. The source-facing anti-equivalence is
-- therefore stated against the full subcategory of `\mathcal O_S`-algebras whose underlying unit
-- module is quasi-coherent.

variable (S : Scheme.{u})

local notation "J" => Opens.grothendieckTopology S

/-- Lemma 29.11.5 (1): for a scheme `S`, the category of affine schemes over `S` is
anti-equivalent to the category of quasi-coherent sheaves of `\mathcal O_S`-algebras. -/
theorem affineOverOpEquivQcAlgebraUnder :
    Nonempty (S.AffineOverᵒᵖ ≌ S.QcAlgebraUnder) := sorry

/-- Lemma 29.11.5 (2): the anti-equivalence may be chosen so that an affine `S`-scheme
`f : X ⟶ S` is sent to the `\mathcal O_S`-algebra `f_* \mathcal O_X`. -/
theorem exists_affineOverOpEquivQcAlgebraUnder_objIso_pushforward :
    ∃ e : S.AffineOverᵒᵖ ≌ S.QcAlgebraUnder,
      ∀ T : S.AffineOver,
        let f := T.obj.hom
        Nonempty
          (((QcAlgebraUnder.forget S).obj (e.functor.obj (op T))) ≅
            Under.mk (Hom.commRingSheafPushforwardMap f.toShHom)) := sorry

/-- Lemma 29.11.5 (3): for any base change `g : S' ⟶ S`, one can choose the affine-side pullback
functor and the quasi-coherent-algebra-side base-change functor so that the anti-equivalences for
`S` and `S'` are compatible. -/
theorem exists_baseChangeCompatibleAffineOverOpEquivQcAlgebraUnder
    {S' : Scheme.{u}} (g : S' ⟶ S) :
    ∃ (eS : S.AffineOverᵒᵖ ≌ S.QcAlgebraUnder)
      (eS' : S'.AffineOverᵒᵖ ≌ S'.QcAlgebraUnder)
      (baseChangeAffine : S.AffineOverᵒᵖ ⥤ S'.AffineOverᵒᵖ)
      (baseChangeQcAlgebra : S.QcAlgebraUnder ⥤ S'.QcAlgebraUnder),
      Nonempty (baseChangeAffine ⋙ eS'.functor ≅ eS.functor ⋙ baseChangeQcAlgebra) := sorry

end Scheme
end AlgebraicGeometry
