import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.WithTerminal.Cone
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.CoprodI
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Definition_2_4_1

universe u

open CategoryTheory Limits

namespace GrpCat

private noncomputable def coproductCofan {ι : Type u} (f : ι → GrpCat.{u}) : Cofan f :=
  Cofan.mk (GrpCat.of (Monoid.CoprodI fun i ↦ f i))
    (fun i ↦ GrpCat.ofHom (@Monoid.CoprodI.of ι (fun i ↦ f i) _ i))

private noncomputable def coproductCofanIsColimit {ι : Type u} (f : ι → GrpCat.{u}) :
    IsColimit (coproductCofan f) :=
  mkCofanColimit _
    (fun s ↦ GrpCat.ofHom (Monoid.CoprodI.lift fun i ↦ (s.inj i).hom))
    (fun s i ↦ by
      apply GrpCat.hom_ext
      ext x
      simp [coproductCofan])
    (fun s m h ↦ by
      apply GrpCat.hom_ext
      apply Monoid.CoprodI.ext_hom
      intro i
      apply GrpCat.ofHom_injective
      simpa [coproductCofan, GrpCat.ofHom_comp] using h i)

noncomputable instance {ι : Type u} (f : ι → GrpCat.{u}) : HasCoproduct f :=
  HasColimit.mk ⟨coproductCofan f, coproductCofanIsColimit f⟩

noncomputable instance : HasCoproducts.{u} GrpCat.{u} :=
  hasCoproducts_of_colimit_cofans coproductCofan coproductCofanIsColimit

private abbrev coequalizerRelations {X Y : GrpCat.{u}} (p q : X ⟶ Y) : Subgroup Y :=
  Subgroup.normalClosure (Set.range fun x : X ↦ p x * (q x)⁻¹)

private noncomputable def coequalizerCofork {X Y : GrpCat.{u}} (p q : X ⟶ Y) : Cofork p q :=
  Cofork.ofπ (GrpCat.ofHom (QuotientGroup.mk' (coequalizerRelations p q))) <| by
    ext x
    change (QuotientGroup.mk' (coequalizerRelations p q)) (p x) =
      (QuotientGroup.mk' (coequalizerRelations p q)) (q x)
    exact (QuotientGroup.eq_iff_div_mem).2 <| by
      have hx : p x * (q x)⁻¹ ∈ Set.range (fun x : X ↦ p x * (q x)⁻¹) := ⟨x, rfl⟩
      simpa [coequalizerRelations, div_eq_mul_inv] using
        (Subgroup.subset_normalClosure hx)

private lemma coequalizerRelations_le_ker {X Y : GrpCat.{u}} {p q : X ⟶ Y} (s : Cofork p q) :
    coequalizerRelations p q ≤ s.π.hom.ker := by
  refine Subgroup.normalClosure_le_normal ?_
  intro y hy
  rcases hy with ⟨x, rfl⟩
  change s.π.hom (p x * (q x)⁻¹) = 1
  rw [MonoidHom.map_mul, MonoidHom.map_inv, mul_inv_eq_one]
  simpa [GrpCat.comp_apply] using congrArg (fun k : X ⟶ s.pt ↦ k x) s.condition

private noncomputable def coequalizerCoforkIsColimit {X Y : GrpCat.{u}} (p q : X ⟶ Y) :
    IsColimit (coequalizerCofork p q) :=
  Cofork.IsColimit.mk _
    (fun s ↦
      GrpCat.ofHom
        (QuotientGroup.lift (coequalizerRelations p q) s.π.hom
          (coequalizerRelations_le_ker s)))
    (fun s ↦ by
      apply GrpCat.hom_ext
      exact
        QuotientGroup.lift_comp_mk' (coequalizerRelations p q) s.π.hom
          (coequalizerRelations_le_ker s))
    (fun s m hm ↦ by
      let l : (coequalizerCofork p q).pt ⟶ s.pt :=
        GrpCat.ofHom
          (QuotientGroup.lift (coequalizerRelations p q) s.π.hom
            (coequalizerRelations_le_ker s))
      have hl : (coequalizerCofork p q).π ≫ l = s.π := by
        apply GrpCat.hom_ext
        exact
          QuotientGroup.lift_comp_mk' (coequalizerRelations p q) s.π.hom
            (coequalizerRelations_le_ker s)
      apply GrpCat.hom_ext
      apply QuotientGroup.monoidHom_ext
      apply GrpCat.ofHom_injective
      simpa [l, coequalizerCofork, GrpCat.ofHom_comp] using hm.trans hl.symm)

noncomputable instance {X Y : GrpCat.{u}} (p q : X ⟶ Y) :
    HasColimit (parallelPair p q) :=
  HasColimit.mk ⟨coequalizerCofork p q, coequalizerCoforkIsColimit p q⟩

noncomputable instance : HasCoequalizers GrpCat.{u} :=
  hasCoequalizers_of_hasColimit_parallelPair GrpCat.{u}

noncomputable instance : HasColimits GrpCat.{u} :=
  has_colimits_of_hasCoequalizers_and_coproducts

end GrpCat

/- Remark 2.6.8: the category of sets is complete and cocomplete, via the canonical instances
`HasLimits (Type u)` and `HasColimits (Type u)`. -/
#check (inferInstance : HasLimits (Type u))
#check (inferInstance : HasColimits (Type u))

/- The category of topological spaces is complete and cocomplete. -/
#check (inferInstance : HasLimits TopCat.{u})
#check (inferInstance : HasColimits TopCat.{u})

/- The category of based spaces, formalized earlier as `BasedSpace`, is complete and
cocomplete. -/
#check (inferInstance : HasLimits BasedSpace.{u})
#check (inferInstance : HasColimits BasedSpace.{u})

/- The category of groups is complete and cocomplete. Limits are already available canonically,
while the cocompleteness side is supplied here by the free-product coproducts and quotient-group
coequalizers, giving the standard abstract instance `HasColimits GrpCat`. -/
#check (inferInstance : HasLimits GrpCat.{u})
#check (inferInstance : HasCoproducts GrpCat.{u})
#check (inferInstance : HasCoequalizers GrpCat.{u})
#check (inferInstance : HasColimits GrpCat.{u})

/- The category of abelian groups is complete and cocomplete. -/
#check (inferInstance : HasLimits AddCommGrpCat.{u})
#check (inferInstance : HasColimits AddCommGrpCat.{u})
