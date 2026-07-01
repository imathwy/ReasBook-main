import Mathlib
import Mathlib.Tactic.Recall

open CategoryTheory Limits MonoidalCategory

universe u v

section

variable {R : Type u} [CommRing R]
variable {I : Type v} [Preorder I]
variable (N : ModuleCat.{u} R) (F : I ⥤ ModuleCat.{u} R) [HasColimit F]

/-- Lemma 10.12.9 (Tensor products commute with colimits): for a system of `R`-modules indexed by
a preordered set, the colimit of the tensor products `Mᵢ ⊗ N` is canonically isomorphic to the
tensor product of the colimit of the system with `N`. -/
noncomputable def colimit_tensor_right_iso : colimit (F ⋙ tensorRight N) ≅ (colimit F) ⊗ N :=
  (preservesColimitIso (tensorRight N) F).symm

/-- On each cocone leg, the comparison isomorphism from the colimit of `Mᵢ ⊗ N` to
`(colimit Mᵢ) ⊗ N` is induced by tensoring the colimit map `μᵢ` with the identity on `N`. -/
-- Proof sketch: specialize `ι_preservesColimitIso_inv` to the right-tensoring functor
-- `tensorRight N`; this is exactly the cocone-leg formula for the inverse of
-- `preservesColimitIso`, which is the `hom` of `colimit_tensor_right_iso`.
theorem colimit_tensor_right_iso_hom_ι (i : I) :
    colimit.ι (F ⋙ tensorRight N) i ≫ (colimit_tensor_right_iso N F).hom =
      colimit.ι F i ▷ N := by
  -- The comparison map is the inverse leg of `preservesColimitIso` for `tensorRight N`.
  -- The standard cocone-leg formula then gives exactly the induced map `μᵢ ⊗ 1`.
  simpa [colimit_tensor_right_iso] using
    (CategoryTheory.ι_preservesColimitIso_inv (G := tensorRight N) (F := F) i)

end
