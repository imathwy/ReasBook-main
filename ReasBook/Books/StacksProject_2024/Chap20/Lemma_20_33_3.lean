import Mathlib
import StacksProject_2024.Chap20.Lemma_20_32_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The Hom group `Hom_{D(\mathcal O_X)}(E, F)` viewed as an object of `AddCommGrpCat`. -/
abbrev derived_hom_group (X : RingedSpace.{u}) (E F : DerivedCategory (RingedSpace.Modules X)) :
    AddCommGrpCat :=
  AddCommGrpCat.of (E ⟶ F)

/-- The Hom group on an open subspace `U`, i.e. `Hom_{D(\mathcal O_U)}(E|_U, F|_U)`. -/
abbrev derived_open_hom_group (X : RingedSpace.{u}) (U : Opens X.carrier)
    (E F : DerivedCategory (RingedSpace.Modules X)) : AddCommGrpCat :=
  AddCommGrpCat.of
    (((moduleRestrictionToOpenDerived X U).obj E) ⟶
      ((moduleRestrictionToOpenDerived X U).obj F))

/-- The degree `-1` Ext group on an open subspace `U`, written as `Hom(E|_U, F|_U[-1])`. -/
abbrev derived_open_ext_neg_one_group (X : RingedSpace.{u}) (U : Opens X.carrier)
    (E F : DerivedCategory (RingedSpace.Modules X)) : AddCommGrpCat :=
  AddCommGrpCat.of
    (((moduleRestrictionToOpenDerived X U).obj E) ⟶
      (((moduleRestrictionToOpenDerived X U).obj F)⟦(-1 : ℤ)⟧))

/-- The middle term `Hom(E|_U, F|_U) \oplus Hom(E|_V, F|_V)` in the Mayer-Vietoris segment. -/
abbrev derived_open_pair_hom_group (X : RingedSpace.{u}) (U V : Opens X.carrier)
    (E F : DerivedCategory (RingedSpace.Modules X)) : AddCommGrpCat :=
  derived_open_hom_group X U E F ⊞ derived_open_hom_group X V E F

section

variable {X : RingedSpace.{u}}

-- Proof sketch: apply the contravariant Hom functor `Hom_{D(\mathcal O_X)}(-, F)` to the
-- Mayer-Vietoris distinguished triangle for `E` from Lemma `20.33.1`, then rewrite the resulting
-- terms using the derived adjunction between extension by zero and restriction to opens from
-- Lemma `20.32.8`.
/-- Lemma 20.33.3: if a ringed space `X` is covered by two opens `U` and `V`, then the groups
`Ext^{-1}_{D(\mathcal O_{U \cap V})}(E|_{U \cap V}, F|_{U \cap V})`,
`Hom_{D(\mathcal O_X)}(E, F)`,
`Hom_{D(\mathcal O_U)}(E|_U, F|_U) \oplus Hom_{D(\mathcal O_V)}(E|_V, F|_V)`, and
`Hom_{D(\mathcal O_{U \cap V})}(E|_{U \cap V}, F|_{U \cap V})`
fit into the displayed Mayer-Vietoris exact segment. -/
theorem module_derived_mayer_vietoris_hom_exact_segment
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (E F : DerivedCategory (RingedSpace.Modules X)) :
    ∃ δ :
        derived_open_ext_neg_one_group X (U ⊓ V) E F ⟶
          derived_hom_group X E F,
      ∃ α :
          derived_hom_group X E F ⟶
            derived_open_pair_hom_group X U V E F,
        ∃ β :
            derived_open_pair_hom_group X U V E F ⟶
              derived_open_hom_group X (U ⊓ V) E F,
          (mk₃ δ α β).Exact := sorry

end

end AlgebraicGeometry.RingedSpace
