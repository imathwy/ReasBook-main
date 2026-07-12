import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Restrict

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

-- Semantic recall note: this file uses the canonical specialization of
-- `Scheme.pullback_map_isOpenImmersion` to restriction morphisms, together with
-- `Scheme.Pullback.range_map` and the standard `resLE`/`ι` range lemmas from `Restrict`.

open Scheme

variable {S X Y : Scheme}
variable (f : X ⟶ S) (g : Y ⟶ S)
variable (U : S.Opens) (V : X.Opens) (W : Y.Opens)
variable (hV : V ≤ f ⁻¹ᵁ U) (hW : W ≤ g ⁻¹ᵁ U)

/-- Lemma 26.17.3: if `V ⊆ X` and `W ⊆ Y` both lie over the same open subscheme `U ⊆ S`, then
the canonical morphism `V ×_U W ⟶ X ×_S Y` is an open immersion. -/
@[stacks 01JR]
theorem isOpenImmersion_pullbackComparison :
    IsOpenImmersion
      (pullback.map (f.resLE U V hV) (g.resLE U W hW) f g V.ι W.ι U.ι
        (Scheme.Hom.resLE_comp_ι f hV) (Scheme.Hom.resLE_comp_ι g hW)) := by
  infer_instance

/-- Lemma 26.17.3: the canonical morphism `V ×_U W ⟶ X ×_S Y` identifies the source with the
intersection `p⁻¹(V) ∩ q⁻¹(W)` inside `X ×_S Y`. -/
@[stacks 01JR]
theorem pullbackComparison_opensRange :
    (pullback.map (f.resLE U V hV) (g.resLE U W hW) f g V.ι W.ι U.ι
      (Scheme.Hom.resLE_comp_ι f hV) (Scheme.Hom.resLE_comp_ι g hW)).opensRange =
      (pullback.fst f g) ⁻¹ᵁ V ⊓ (pullback.snd f g) ⁻¹ᵁ W := by
  apply TopologicalSpace.Opens.ext
  rw [Scheme.Hom.coe_opensRange, Scheme.Pullback.range_map]
  simp [Scheme.Opens.range_ι]

end AlgebraicGeometry
