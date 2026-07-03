import StacksProject_2024.Chap12.Lemma_12_19_7

open CategoryTheory
open CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜] [HasImages 𝒜] [HasPullbacks 𝒜]
  [HasBinaryBiproducts 𝒜]

namespace FilteredObject.Hom

open FilteredObject

variable {A B C : FilteredObject 𝒜}

/-
Source/core/bridge triage for Lemma 12.19.5:
- source-facing: strictness of the filtered biproduct lift attached to a strict monomorphism
- core/canonical owners: `strict_iff_induced_filtration_of_mono` and
  `biprod.mono_lift_of_mono_left`, `HasBinaryBiproducts (FilteredObject C)`
- bridge/view: the canonical map `biprod.lift f g : A ⟶ B ⊞ C`
-/

-- Proof sketch: first recover `Mono (biprod.lift f g).hom` from the ambient owner instance
-- `biprod.mono_lift_of_mono_left`. Then apply the canonical
-- mono-side strictness criterion `strict_iff_induced_filtration_of_mono` to `biprod.lift f g`.
-- The induced filtration along `biprod.lift f.hom g.hom` is computed from the left component
-- using strictness of `f`; `g` contributes only the already bundled filtration-preservation data.
/-- Lemma 12.19.5: if `f : A ⟶ B` is a strict monomorphism of filtered objects and
`g : A ⟶ C` is any filtered morphism, then the induced morphism
`A ⟶ B ⊞ C` is strict. Its monomorphism part is the ambient owner instance
`biprod.mono_lift_of_mono_left` on the underlying biproduct-lift map. -/
theorem strict_biprodLift (f : A ⟶ B) (g : A ⟶ C) [Mono f.hom] (hf : Strict f) :
    Strict (biprod.lift f g) := by
  letI : Mono (biprod.lift f g).hom := by
    change Mono (biprod.lift f.hom g.hom)
    infer_instance
  rw [strict_iff_induced_filtration_of_mono]
  refine OrderHom.ext _ _ (funext fun i ↦ le_antisymm ?_ ?_)
  · refine Subobject.le_of_factors ?_
    exact Limits.pullback_factors (biprod.lift f g).hom (((B ⊞ C : FilteredObject 𝒜)).filtration i)
      (A.filtration i).arrow ((biprod.lift f g).preserves i)
  · have hstage :
        ((B ⊞ C : FilteredObject 𝒜)).filtration i ≤
          (Subobject.pullback biprod.fst).obj (B.filtration i) := by
      refine Subobject.le_of_factors ?_
      exact Limits.pullback_factors biprod.fst (B.filtration i)
        (((B ⊞ C : FilteredObject 𝒜)).filtration i).arrow (biprod.fst.preserves i)
    calc
      (Subobject.pullback (biprod.lift f g).hom).obj (((B ⊞ C : FilteredObject 𝒜)).filtration i)
          ≤ (Subobject.pullback (biprod.lift f g).hom).obj
              ((Subobject.pullback biprod.fst).obj (B.filtration i)) :=
            (Subobject.pullback (biprod.lift f g).hom).monotone hstage
      _ = (Subobject.pullback f.hom).obj (B.filtration i) := by
            calc
              (Subobject.pullback (biprod.lift f g).hom).obj
                  ((Subobject.pullback biprod.fst).obj (B.filtration i))
                  = (Subobject.pullback ((biprod.lift f g).hom ≫ biprod.fst)).obj
                      (B.filtration i) := by
                          symm
                          exact Subobject.pullback_comp (biprod.lift f g).hom biprod.fst
                            (B.filtration i)
              _ = (Subobject.pullback f.hom).obj (B.filtration i) := by
                    change
                      (Subobject.pullback ((biprod.lift f g).hom ≫ biprod.fst)).obj
                          (B.filtration i)
                        = (Subobject.pullback f.hom).obj (B.filtration i)
                    simp
      _ = A.filtration i := by
            simpa using
              (congrArg (fun F ↦ F i)
                ((strict_iff_induced_filtration_of_mono f).1 hf)).symm

end FilteredObject.Hom

end CategoryTheory
