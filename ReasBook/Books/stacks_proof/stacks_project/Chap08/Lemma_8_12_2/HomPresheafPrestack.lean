import StacksProject_2024.Chap08.Lemma_8_12_2.OverPostContinuous
import StacksProject_2024.Chap08.Lemma_8_12_2.PullHomPostcomposition
import StacksProject_2024.Chap08.Lemma_8_12_2.PullHomConjugation

open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology.Cover

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)

/-- Helper for Lemma 8.12.2: target Hom presheaves remain sheaves after pulling them back to the
slice over `U` along `Over.post u`. -/
theorem pullbackProjection_targetPresheafHom_opComp_isSheaf
    [Functor.IsContinuous u J K]
    (p : S ⥤ D) [IsStackOnSite K p] {U : C}
    (X Y : (CategoricalPullback.π₁ u p).Fiber U) :
    Presheaf.IsSheaf (J.over U)
      ((Over.post u).op ⋙
        (canonicalFiberPseudofunctor p).presheafHom
          (pullbackProjection_targetFiberObj u p X)
          (pullbackProjection_targetFiberObj u p Y)) := by
  -- First use the stack condition on `p` to get the target Hom sheaf, then transport it across
  -- the continuous slice functor `Over.post u`.
  letI : p.IsFibered := inferInstance
  let P :=
    (canonicalFiberPseudofunctor p).presheafHom
      (pullbackProjection_targetFiberObj u p X)
      (pullbackProjection_targetFiberObj u p Y)
  have hTarget : Presheaf.IsSheaf (K.over (u.obj U)) P := by
    exact Pseudofunctor.IsPrestack.isSheaf (F := canonicalFiberPseudofunctor p) (J := K)
      (S := u.obj U)
      (pullbackProjection_targetFiberObj u p X)
      (pullbackProjection_targetFiberObj u p Y)
  exact overPost_op_comp_isSheaf_of_isContinuous_local (J := J) (K := K) u P hTarget

/-- Helper for Lemma 8.12.2: objectwise comparison between Hom sections in the pullback fiber
and Hom sections after strictifying the target component. -/
noncomputable def pullbackProjection_presheafHomAppEquiv
    (p : S ⥤ D) [p.IsFibered] {U : C}
    (X Y : (CategoricalPullback.π₁ u p).Fiber U) (T : Over U) :
    ((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).presheafHom X Y).obj
        (Opposite.op T) ≃
      (((Over.post u).op ⋙
        (canonicalFiberPseudofunctor p).presheafHom
          (pullbackProjection_targetFiberObj u p X)
          (pullbackProjection_targetFiberObj u p Y) ⋙
            uliftFunctor.{vC}).obj (Opposite.op T)) := by
  -- Restrict first in the pullback fiber, then use the fiber equivalence and the canonical
  -- restriction comparison to reach the target Hom presheaf at `Over.post u T`.
  let Fsrc := pullbackProjection_targetFiberFunctor u p T.left
  letI : Fsrc.IsEquivalence := pullbackProjection_targetFiberFunctor_isEquivalence u p T.left
  let hFsrc : Fsrc.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful Fsrc
  let eX := pullbackProjection_targetRestrictionIso u p T.hom X
  let eY := pullbackProjection_targetRestrictionIso u p T.hom Y
  exact ((hFsrc.homEquiv).trans (Iso.homCongr eX eY)).trans Equiv.ulift.symm

/-- Helper for Lemma 8.12.2: the pointwise Hom comparison is the explicit strictification
conjugation on target-fiber morphisms. -/
theorem pullbackProjection_presheafHomAppEquiv_apply_down
    (p : S ⥤ D) [p.IsFibered] {U : C}
    (X Y : (CategoricalPullback.π₁ u p).Fiber U) (T : Over U)
    (φ : ((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).presheafHom X Y).obj
      (Opposite.op T)) :
    ((pullbackProjection_presheafHomAppEquiv u p X Y T) φ).down =
      (pullbackProjection_targetRestrictionIso u p T.hom X).inv ≫
        (pullbackProjection_targetFiberFunctor u p T.left).map φ ≫
          (pullbackProjection_targetRestrictionIso u p T.hom Y).hom := by
  rfl


/-- Helper for Lemma 8.12.2: the objectwise Hom comparison commutes with restriction along a
slice morphism. -/
theorem pullbackProjection_presheafHomAppEquiv_pullHom
    (p : S ⥤ D) [p.IsFibered] {U : C}
    (X Y : (CategoricalPullback.π₁ u p).Fiber U) {T₁ T₂ : Over U} (g : T₂ ⟶ T₁)
    (φ : ((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).presheafHom X Y).obj
      (Opposite.op T₁)) :
    ((pullbackProjection_presheafHomAppEquiv u p X Y T₂)
      (Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ g.left T₂.hom T₂.hom
        (by simpa using g.w) (by simpa using g.w))).down =
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (((pullbackProjection_presheafHomAppEquiv u p X Y T₁) φ).down)
          (u.map g.left) (u.map T₂.hom) (u.map T₂.hom)
          (overPost_map_left_comp_hom u g) (overPost_map_left_comp_hom u g) := by
  rw [pullbackProjection_presheafHomAppEquiv_apply_down]
  rw [pullbackProjection_presheafHomAppEquiv_apply_down]
  exact
    pullbackProjection_targetRestrictionIso_pullHom_conjugation u p T₁.hom g.left T₂.hom
      (by simpa using g.w) (overPost_map_left_comp_hom u g) X Y φ

/-- Helper for Lemma 8.12.2: the objectwise Hom comparison is natural over the slice. -/
theorem pullbackProjection_presheafHomAppEquiv_naturality
    (p : S ⥤ D) [p.IsFibered] {U : C}
    (X Y : (CategoricalPullback.π₁ u p).Fiber U) :
    ∀ {T₁ T₂ : (Over U)ᵒᵖ} (α : T₁ ⟶ T₂),
      ((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).presheafHom X Y).map α ≫
          (Equiv.toIso (pullbackProjection_presheafHomAppEquiv u p X Y T₂.unop)).hom =
        (Equiv.toIso (pullbackProjection_presheafHomAppEquiv u p X Y T₁.unop)).hom ≫
          (((Over.post u).op ⋙
            (canonicalFiberPseudofunctor p).presheafHom
              (pullbackProjection_targetFiberObj u p X)
              (pullbackProjection_targetFiberObj u p Y) ⋙
                uliftFunctor.{vC}).map α) := by
  intro T₁ T₂ α
  funext φ
  -- TODO for Lemma 8.12.2: normalize both sides to `pullHom` and use
  -- `pullbackProjection_targetRestrictionIso` compatibility with restriction composition.
  apply ULift.ext
  simpa [pullbackProjection_presheafHomAppEquiv] using
    pullbackProjection_presheafHomAppEquiv_pullHom u p X Y α.unop φ

/-- Helper for Lemma 8.12.2: Hom presheaves for the pullback projection are isomorphic to the
corresponding target Hom presheaves pulled back along `Over.post u`. -/
noncomputable def pullbackProjection_presheafHomIso
    (p : S ⥤ D) [p.IsFibered] {U : C}
    (X Y : (CategoricalPullback.π₁ u p).Fiber U) :
    (canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).presheafHom X Y ≅
      (Over.post u).op ⋙
        (canonicalFiberPseudofunctor p).presheafHom
          (pullbackProjection_targetFiberObj u p X)
          (pullbackProjection_targetFiberObj u p Y) ⋙
            uliftFunctor.{vC} :=
  -- Package the pointwise strictification equivalence into the presheaf-level bridge used below.
  NatIso.ofComponents
    (fun T ↦ Equiv.toIso (pullbackProjection_presheafHomAppEquiv u p X Y T.unop))
    (pullbackProjection_presheafHomAppEquiv_naturality u p X Y)

/-- Helper for Lemma 8.12.2: the pullback projection is a prestack once Hom sheaves are
transported along the strictification equivalence with the target fibers. -/
theorem pullbackProjection_canonicalFiber_isPrestack
    [Functor.IsContinuous u J K]
    (p : S ⥤ D) [IsStackOnSite K p] :
    Pseudofunctor.IsPrestack (canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)) J := by
  -- The Hom-presheaf bridge transports target Hom sheafness back to the pullback fiber.
  refine ⟨?_⟩
  intro U X Y
  exact
    (Presheaf.isSheaf_of_iso_iff
      (pullbackProjection_presheafHomIso u p X Y)).2
      ((CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).2
        (Presieve.isSheaf_comp_uliftFunctor (J := J.over U)
          ((CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).1
            (pullbackProjection_targetPresheafHom_opComp_isSheaf (J := J) (K := K) u p X Y))))


end

end CategoryTheory
