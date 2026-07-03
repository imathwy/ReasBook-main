import StacksProject_2024.Chap12.Lemma_12_19_7

open CategoryTheory
open CategoryTheory.Limits

universe u v

noncomputable section

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜] [HasImages 𝒜] [HasPullbacks 𝒜]
  [HasBinaryBiproducts 𝒜] [Balanced 𝒜]

namespace FilteredObject.Hom

open FilteredObject

variable {X Y Z : FilteredObject 𝒜}

/-
Source/core/bridge triage for Lemma 12.19.6:
- sampled owner declarations in this filtered-object domain:
  `FilteredObject.Hom.Strict`,
  `FilteredObject.Hom.strict_iff_quotient_eq_inf`,
  `FilteredObject.Hom.strict_iff_quotient_filtration_of_epi`,
  `CategoryTheory.Limits.biprod.epi_desc_of_epi_left`
- source-facing: strictness of the filtered biproduct descent map
- core/canonical owner: `FilteredObject.Hom.Strict`, accessed through the epi-side criterion
  `strict_iff_quotient_filtration_of_epi`
- bridge/view: the canonical map `biprod.desc f g : X ⊞ Y ⟶ Z`; the sampled ambient owner
  `biprod.epi_desc_of_epi_left` supplies the needed `Epi` instance on the underlying biproduct
  descent map
- primitive data: filtered morphisms `f`, `g`, together with the strict epimorphism data on `f`
- derived API: strictness of `biprod.desc f g`, obtained by identifying its quotient filtration
  with the filtration on `Z`
-/

-- Proof sketch: apply the canonical epi-side strictness criterion
-- `strict_iff_quotient_filtration_of_epi` to `biprod.desc f g`. The required epimorphism on the
-- underlying map is the canonical mathlib instance `biprod.epi_desc_of_epi_left`. The quotient
-- filtration of the stagewise biproduct along `biprod.desc f.hom g.hom` is then computed from the
-- left summand because `g` already preserves filtration stages, and strictness of `f` identifies
-- that quotient filtration with the given filtration on `Z`.
/-- Lemma 12.19.6: if `f : X ⟶ Z` is a strict epimorphism of filtered objects and `g : Y ⟶ Z` is
any filtered morphism, then the induced morphism `X ⊞ Y ⟶ Z` is again a
strict morphism. The key owner criterion is the epi-side strictness reformulation
`strict_iff_quotient_filtration_of_epi`, together with the canonical ambient instance
`biprod.epi_desc_of_epi_left` on the underlying biproduct descent map. -/
theorem strict_biprodDesc (f : X ⟶ Z) (g : Y ⟶ Z) [Epi f.hom] (hf : Strict f) :
    Strict (biprod.desc f g) := by
  have hinl : (biprod.inl : X ⟶ X ⊞ Y).hom ≫ (biprod.desc f g).hom = f.hom := by
    exact congrArg FilteredObject.Hom.hom (biprod.inl_desc f g)
  letI : Epi (biprod.desc f g).hom := by
    exact epi_of_epi_fac hinl
  refine (strict_iff_quotient_filtration_of_epi (biprod.desc f g)).2 ?_
  refine OrderHom.ext _ _ (funext fun i ↦ le_antisymm ?_ ?_)
  · rw [DecreasingFiltration.quotient_eq_imageSubobject_comp]
    have hquot :
        Z.filtration i = imageSubobject ((X.filtration i).arrow ≫ f.hom) := by
      simpa [DecreasingFiltration.quotient_eq_imageSubobject_comp] using
        congrArg (fun F ↦ F i) ((strict_iff_quotient_filtration_of_epi f).1 hf)
    have hstage :
        ((X ⊞ Y).filtration i).Factors
          ((X.filtration i).arrow ≫ (biprod.inl : X ⟶ X ⊞ Y).hom) := by
      simpa using (biprod.inl : X ⟶ X ⊞ Y).preserves i
    let α :=
      ((X ⊞ Y).filtration i).factorThru
        ((X.filtration i).arrow ≫ (biprod.inl : X ⟶ X ⊞ Y).hom) hstage
    have hα :
        α ≫ ((X ⊞ Y).filtration i).arrow =
          (X.filtration i).arrow ≫ (biprod.inl : X ⟶ X ⊞ Y).hom := by
      simpa [α] using
        Subobject.factorThru_arrow ((X ⊞ Y).filtration i)
          ((X.filtration i).arrow ≫ (biprod.inl : X ⟶ X ⊞ Y).hom) hstage
    have hcomp :
        (X.filtration i).arrow ≫ f.hom =
          α ≫ ((X ⊞ Y).filtration i).arrow ≫ (biprod.desc f g).hom := by
      calc
        (X.filtration i).arrow ≫ f.hom =
            (X.filtration i).arrow ≫ (biprod.inl : X ⟶ X ⊞ Y).hom ≫ (biprod.desc f g).hom := by
              simpa [Category.assoc] using
                (congrArg (fun t ↦ (X.filtration i).arrow ≫ t) hinl).symm
        _ = (α ≫ ((X ⊞ Y).filtration i).arrow) ≫ (biprod.desc f g).hom := by
              simpa [hα]
        _ = α ≫ ((X ⊞ Y).filtration i).arrow ≫ (biprod.desc f g).hom := by
              simp [Category.assoc]
    calc
      Z.filtration i = imageSubobject (α ≫ ((X ⊞ Y).filtration i).arrow ≫ (biprod.desc f g).hom) := by
        simpa [hcomp] using hquot
      _ ≤ imageSubobject (((X ⊞ Y).filtration i).arrow ≫ (biprod.desc f g).hom) := by
        simpa [Category.assoc] using
          (imageSubobject_comp_le α
            (((X ⊞ Y).filtration i).arrow ≫ (biprod.desc f g).hom))
  · simpa [DecreasingFiltration.quotient_eq_imageSubobject_comp] using
      imageSubobject_le _ _ (Subobject.factorThru_arrow _ _ ((biprod.desc f g).preserves i))

end FilteredObject.Hom

end CategoryTheory
