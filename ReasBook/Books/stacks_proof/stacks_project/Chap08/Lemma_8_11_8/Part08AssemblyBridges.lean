import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap08.Lemma_8_11_8.CoherenceAPI

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

section
set_option allowUnsafeReducibility true in
attribute [local irreducible] canonicalPullbackChoice

/-- Bridge iso for Lemma 8.11.8 (assembly, source/`chosen_gerbe_cover_object` side): the broken
definitional identification between the pulled chosen-local source object and the source
secondary-cover descent datum on the self-leg `L`. -/
noncomputable def assembly_clai_source_to_ssdd_bridge
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C}
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.obj
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.obj
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)))).obj K)).obj L ≅
      ((J.pseudofunctorOver (Type (max u v))).map (𝟙 L.Y).op.toLoc).toFunctor.obj
        ((local_overlap_source_secondary_descent_data (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).obj L) := by
  set F := J.pseudofunctorOver (Type (max u v)) with hF
  set W := automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base) with hW
  refine ?_ ≪≫ ((Cat.Hom.toNatIso (F.mapId (LocallyDiscrete.mk (op L.Y)))).app _).symm
  refine (F.map L.f.op.toLoc).toFunctor.mapIso ?_
  exact ((Cat.Hom.toNatIso (F.mapComp g₁.op.toLoc K.f.op.toLoc)).app W).symm

/-- Bridge iso for Lemma 8.11.8 (assembly, `I₁.f ^* y` side): the target analogue of
`assembly_clai_source_to_ssdd_bridge` on the `I₁.f ^*[cpc] y` automorphism sheaf. -/
noncomputable def assembly_clai_target_to_ssdd_bridge
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C}
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.obj
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.obj
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)))).obj K)).obj L ≅
      ((J.pseudofunctorOver (Type (max u v))).map (𝟙 L.Y).op.toLoc).toFunctor.obj
        ((local_overlap_source_secondary_descent_data (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).obj L) :=
  ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
      (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
          (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
      (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).symm)) ≪≫
    assembly_clai_source_to_ssdd_bridge (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L

/-- Bridge iso for Lemma 8.11.8 (assembly, mid): the pulled source secondary-cover descent datum on
the self-leg `L` identifies with the automorphism sheaf of the local-overlap source object. -/
noncomputable def assembly_ssdd_to_local_overlap_source_bridge
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C}
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map (𝟙 L.Y).op.toLoc).toFunctor.obj
        ((local_overlap_source_secondary_descent_data (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).obj L) ≅
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (L.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_source_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (K.f ≫ g₁))) := by
  set F := J.pseudofunctorOver (Type (max u v)) with hF
  set x := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base with hx
  refine (Cat.Hom.toNatIso (F.mapId _)).app _ ≪≫ ?_
  exact
    (F.map L.f.op.toLoc).toFunctor.mapIso
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (K.f ≫ g₁) x) ≪≫
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f _

/-- Bridge iso for Lemma 8.11.8 (assembly, right mid): the automorphism sheaf of the local-overlap
target object identifies with the pulled target secondary-cover descent datum on the self-leg. -/
noncomputable def assembly_local_overlap_target_to_tsdd_bridge
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C}
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (L.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_target_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₂ := I₂.base) (K.f ≫ g₂))) ≅
      ((J.pseudofunctorOver (Type (max u v))).map (𝟙 L.Y).op.toLoc).toFunctor.obj
        ((local_overlap_target_secondary_descent_data (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).obj L) := by
  refine Iso.symm ?_
  set F := J.pseudofunctorOver (Type (max u v)) with hF
  set x := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base with hx
  refine (Cat.Hom.toNatIso (F.mapId _)).app _ ≪≫ ?_
  exact
    (F.map L.f.op.toLoc).toFunctor.mapIso
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (K.f ≫ g₂) x) ≪≫
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f _

/-- Bridge iso for Lemma 8.11.8 (assembly, right source): the automorphism sheaf of the
local-overlap source object identifies with the pulled chosen descent datum at `I₁.base`. -/
noncomputable def assembly_chosen_to_local_overlap_source_bridge
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C}
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (L.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_source_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (K.f ≫ g₁))) ≅
      ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.obj
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.obj
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.obj
          ((chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian U).obj I₁.base))).obj K)).obj L :=
  (assembly_clai_source_to_ssdd_bridge (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L ≪≫
      assembly_ssdd_to_local_overlap_source_bridge (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).symm ≪≫
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
      (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I₁.base).symm))

/-- Bridge iso for Lemma 8.11.8 (assembly, right target): the pulled target secondary-cover descent
datum on the self-leg identifies with the pulled abstract `I₂.f ^* y` automorphism sheaf. -/
noncomputable def assembly_clai_target_to_tsdd_bridge
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C}
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map (𝟙 L.Y).op.toLoc).toFunctor.obj
        ((local_overlap_target_secondary_descent_data (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).obj L) ≅
      ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.obj
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.obj
        (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)))).obj K)).obj L := by
  set F := J.pseudofunctorOver (Type (max u v)) with hF
  refine (Cat.Hom.toNatIso (F.mapId _)).app _ ≪≫ ?_
  refine (F.map L.f.op.toLoc).toFunctor.mapIso ?_
  exact
    (F.map (K.f ≫ g₂).op.toLoc).toFunctor.mapIso
        (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
          (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)) ≪≫
      (Cat.Hom.toNatIso (F.mapComp g₂.op.toLoc K.f.op.toLoc)).app _

/-- Bridge iso for Lemma 8.11.8 (assembly, descent-target side): the pulled abstract descent datum
at `I₂` identifies with the automorphism sheaf of the local-overlap target object. -/
noncomputable def assembly_descent_to_local_overlap_target_bridge
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C}
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.obj
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.obj
        (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.obj
          ((((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).obj I₂))).obj K)).obj L ≅
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (L.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_target_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₂ := I₂.base) (K.f ≫ g₂))) :=
  ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.mapIso
      (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
        (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y))) ≪≫
    (assembly_clai_target_to_tsdd_bridge (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).symm ≪≫
    (assembly_local_overlap_target_to_tsdd_bridge (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).symm

end

end CategoryTheory
