import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_16_1 (from Chap21) -/
open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe wI w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The index type of the degree-`n` iterated Čech intersections of a covering `cover` of `U`. -/
abbrev cechCoverIntersectionIndex {U : C} [HasFiniteProducts (Over U)]
    (cover : FormalCoproduct (Over U)) (n : ℕ) :=
  (cover.cech.obj (op (SimplexCategory.mk n))).I

/-- The underlying object of `C` of the `i`-th degree-`n` Čech intersection of a covering
`cover` of `U`; this is the iterated fibre product of the corresponding members of the covering
over `U`. -/
abbrev cechCoverIntersectionObject {U : C} [HasFiniteProducts (Over U)]
    (cover : FormalCoproduct (Over U)) (n : ℕ)
    (i : cechCoverIntersectionIndex cover n) : C :=
  ((cover.cech.obj (op (SimplexCategory.mk n))).obj i).left

namespace Sheaf

variable {J : GrothendieckTopology C}
variable {I : Type wI} [Category.{wI} I] [IsFiltered I]
variable [HasFiniteWidePullbacks C]
variable [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
variable [HasColimitsOfShape I (Sheaf J AddCommGrpCat.{v})]
variable [HasColimitsOfShape I (Cᵒᵖ ⥤ AddCommGrpCat.{v})]

-- Proof sketch: argue by induction on `p`. For `p = 0`, the chosen finite cofinal coverings force
-- the objects of `B` to satisfy the quasi-compactness criterion used to commute sections with
-- filtered colimits. For the inductive step, embed the filtered diagram into a filtered diagram of
-- injective sheaves, use exactness of filtered colimits to pass to cokernels, and reduce via the
-- long exact cohomology sequence. The injective-colimit term is acyclic in positive degree because
-- the finite chosen coverings keep all Čech intersections inside `B`, so degree-zero commutation
-- identifies the Čech complex of the colimit with the filtered colimit of the injective Čech
-- complexes, which are acyclic by Lemma `21.10.2`; then Lemma `21.10.9` upgrades this Čech
-- vanishing to vanishing of higher cohomology over every `U ∈ B`.
/-- Lemma 21.16.1: let `B` be a collection of objects of the site `(\mathcal C, J)` and, for each
`U`, let `Cov` be a set of coverings of `U` formalized as a set of `FormalCoproduct (Over U)`.
Assume that every selected covering in `Cov` is finite, has target in `B`, all of its members lie
in `B`, and every iterated Čech intersection of its members lies in `B`. Assume moreover that for
every `U ∈ B`, the coverings of `U` occurring in `Cov` form a cofinal system among all coverings
of `U`. Then for every filtered diagram of abelian sheaves, every `p : ℕ`, and every `U ∈ B`, the
canonical map `\operatorname{colim}_i H^p(U, \mathcal F_i) \to H^p(U, \operatorname{colim}_i
\mathcal F_i)` is an isomorphism. -/
theorem cohomologyOverColimitComparison_isIso_of_cofinal_finite_coverings
    (B : Set C)
    (Cov : ∀ U : C, Set (FormalCoproduct (Over U)))
    (hCov_cover : ∀ ⦃U : C⦄ (cover : FormalCoproduct (Over U)),
      cover ∈ Cov U → (J.over U).CoversTop cover.obj)
    (hCov_finite : ∀ ⦃U : C⦄ (cover : FormalCoproduct (Over U)),
      cover ∈ Cov U → Finite cover.I)
    (hCov_target : ∀ ⦃U : C⦄ (cover : FormalCoproduct (Over U)),
      cover ∈ Cov U → U ∈ B)
    (hCov_members : ∀ ⦃U : C⦄ (cover : FormalCoproduct (Over U)),
      cover ∈ Cov U → ∀ i : cover.I, (cover.obj i).left ∈ B)
    (hCov_intersections : ∀ ⦃U : C⦄ (cover : FormalCoproduct (Over U)),
      cover ∈ Cov U → ∀ n : ℕ, ∀ i : cechCoverIntersectionIndex cover n,
        cechCoverIntersectionObject cover n i ∈ B)
    (hCofinal : ∀ ⦃U : C⦄, U ∈ B → ∀ ⦃ι : Type w⦄ (family : ι → Over U),
      (J.over U).CoversTop family →
        ∃ cover : FormalCoproduct (Over U),
          cover ∈ Cov U ∧ Nonempty (cover ⟶ FormalCoproduct.mk ι family))
    (ℱ : I ⥤ Sheaf J AddCommGrpCat.{v}) (p : ℕ) {U : C} (hU : U ∈ B) :
    IsIso ((colimit.post ℱ (cohomologyPresheafFunctor J p)).app (op U)) := sorry

end Sheaf
end CategoryTheory

/-! ### Lemma_21_16_2 (from Chap21) -/
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe wI v u

namespace CategoryTheory.GrothendieckTopology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type (max u v))]

/-- A subset of sheaves satisfying the surjective-cover, product, equalizer, and
quasi-compactness hypotheses used to commute global sheaf cohomology with filtered colimits. -/
class IsCohomologyColimitTestSet (S : Set (Sheaf J (Type (max u v)))) : Prop where
  exists_surjective_to_terminal :
    ∃ K : Sheaf J (Type (max u v)), K ∈ S ∧
      ∃ π : K ⟶ ⊤_ (Sheaf J (Type (max u v))), Sheaf.IsLocallySurjective π
  refine_surjection :
    ∀ ⦃F K : Sheaf J (Type (max u v))⦄ (π : F ⟶ K),
      K ∈ S → Sheaf.IsLocallySurjective π →
        ∃ K' : Sheaf J (Type (max u v)), K' ∈ S ∧
          ∃ κ : K' ⟶ F, Sheaf.IsLocallySurjective (κ ≫ π)
  surjective_product :
    ∀ ⦃K K' : Sheaf J (Type (max u v))⦄,
      K ∈ S → K' ∈ S →
        ∃ K'' : Sheaf J (Type (max u v)), K'' ∈ S ∧
          ∃ π : K'' ⟶ K ⨯ K', Sheaf.IsLocallySurjective π
  surjective_equalizer :
    ∀ ⦃K K' : Sheaf J (Type (max u v))⦄ (a b : K ⟶ K'),
      K ∈ S → K' ∈ S →
        ∃ K'' : Sheaf J (Type (max u v)), K'' ∈ S ∧
          ∃ π : K'' ⟶ equalizer a b, Sheaf.IsLocallySurjective π
  quasiCompact :
    ∀ ⦃K : Sheaf J (Type (max u v))⦄, K ∈ S → Sheaf.IsQuasiCompactObject K

-- Proof sketch: for a surjection `F ⟶ *`, first choose the distinguished cover `K ⟶ *` from the
-- stronger test-set data and refine the pullback `F ×_* K ⟶ K` through another object of `S`,
-- giving the lifting clause required by Lemma `7.17.8 (4)`. For quasi-compact self-products, use
-- the product-surjection clause to produce `K'' ⟶ K × K` with `K'' ∈ S`, then descend
-- quasi-compactness along this locally surjective map via Lemma `7.17.5 (2)`.
/-- A cohomology-colimit test set is, in particular, a quasi-compact test set in the sense of
Lemma `7.17.8 (4)`. -/
theorem isQuasiCompactTestSet_of_isCohomologyColimitTestSet
    {S : Set (Sheaf J (Type (max u v)))}
    (hS : IsCohomologyColimitTestSet J S) :
    IsQuasiCompactTestSet J S := sorry

variable {I : Type wI} [Category.{wI} I] [IsFiltered I]
variable [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
variable [HasColimitsOfShape I (Sheaf J AddCommGrpCat.{v})]
variable [HasColimitsOfShape I AddCommGrpCat.{v}]

-- Proof sketch: proceed by induction on `p`. The case `p = 0` reduces to Lemma `7.17.8 (4)`
-- using the weaker quasi-compact test-set extracted above. For the induction step, choose a
-- surjection `K ⟶ *` with `K ∈ S`, apply the Čech-to-cohomology spectral sequence of Lemma
-- `21.13.2`, and use the source hypotheses on products, equalizers, and quasi-compactness to show
-- that every localized site over `K^(n + 1)` again satisfies the same test-set condition. Then
-- filtered colimits commute with the lower-degree terms by the induction hypothesis, forcing the
-- injective-colimit term to be acyclic in degree `p + 1`.
/-- Lemma 21.16.2: if a site admits a subset `S` of sheaves of sets satisfying the source
surjectivity, product, equalizer, and quasi-compactness hypotheses, then for every filtered
diagram `\mathcal F_\lambda` of abelian sheaves and every degree `p`, the canonical map
`\operatorname{colim}_\lambda H^p(\mathcal C, \mathcal F_\lambda) \to
H^p(\mathcal C, \operatorname{colim}_\lambda \mathcal F_\lambda)` is an isomorphism. -/
theorem siteCohomologyColimitComparison_isIso_of_isCohomologyColimitTestSet
    (S : Set (Sheaf J (Type (max u v))))
    (hS : IsCohomologyColimitTestSet J S)
    (ℱ : I ⥤ Sheaf J AddCommGrpCat.{v}) (p : ℕ) :
    IsIso (colimit.post ℱ (Sheaf.cohomologyFunctor J p)) := sorry

end CategoryTheory.GrothendieckTopology

/-! ### Remark_21_16_3 (from Chap21) -/
open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe v u

namespace CategoryTheory.GrothendieckTopology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type (max u v))]

/-- The sheafified representable sheaf `h_U^#` on the site `(C, J)`. -/
abbrev sheafifiedRepresentableSheaf (U : C) : Sheaf J (Type (max u v)) :=
  (presheafToSheaf J (Type (max u v))).obj (CategoryTheory.uliftYoneda.{max u v}.obj U)

/-- A sheaf belongs to the finite representable test set attached to `B` if it is a finite
coproduct of sheafified representables `h_U^#` with `U ∈ B`, exhibited by an explicit coproduct
cocone. -/
def IsFiniteCoproductOfSheafifiedRepresentables (B : Set C)
    (K : Sheaf J (Type (max u v))) : Prop :=
  ∃ n : ℕ, ∃ U : Fin n → C,
    (∀ i, U i ∈ B) ∧
      ∃ ι : (i : Fin n) → sheafifiedRepresentableSheaf J (U i) ⟶ K,
        Nonempty (IsColimit (Cofan.mk K ι))

/-- The set of sheaves on `(C, J)` which are finite coproducts of sheafified representables
`h_U^#` with `U ∈ B`. -/
abbrev finiteSheafifiedRepresentableSet (B : Set C) : Set (Sheaf J (Type (max u v))) :=
  { K | IsFiniteCoproductOfSheafifiedRepresentables J B K }

/-- A subset `B` of objects of a site satisfies the finite sheafified-representable basis criterion
if it provides the terminal-cover, cover-refinement, product, and equalizer data from the remark. -/
class IsFiniteSheafifiedRepresentableCohomologyBasis (B : Set C) : Prop where
  exists_surjective_to_terminal :
    ∃ K : Sheaf J (Type (max u v)), K ∈ finiteSheafifiedRepresentableSet J B ∧
      ∃ π : K ⟶ ⊤_ (Sheaf J (Type (max u v))), Sheaf.IsLocallySurjective π
  refine_cover :
    ∀ ⦃U : C⦄, U ∈ B → ∀ ⦃ι : Type u⦄ (family : ι → Over U),
      (J.over U).CoversTop family →
        ∃ n : ℕ, ∃ cover : Fin n → Over U,
          (∀ i, (cover i).left ∈ B) ∧
          (J.over U).CoversTop cover ∧
          Nonempty (
            ((FormalCoproduct.mk (ULift (Fin n)) (fun i ↦ cover i.down) :
                FormalCoproduct (Over U)) ⟶
              (FormalCoproduct.mk ι family : FormalCoproduct (Over U))))
  surjective_product :
    ∀ ⦃U U' : C⦄, U ∈ B → U' ∈ B →
      ∃ K : Sheaf J (Type (max u v)), K ∈ finiteSheafifiedRepresentableSet J B ∧
        ∃ π : K ⟶ sheafifiedRepresentableSheaf J U ⨯ sheafifiedRepresentableSheaf J U',
          Sheaf.IsLocallySurjective π
  surjective_equalizer :
    ∀ ⦃U U' : C⦄ (a b : U ⟶ U'), U ∈ B → U' ∈ B →
      ∃ K : Sheaf J (Type (max u v)), K ∈ finiteSheafifiedRepresentableSet J B ∧
        ∃ π : K ⟶ equalizer (J.sheafifiedRepresentableMap a) (J.sheafifiedRepresentableMap b),
          Sheaf.IsLocallySurjective π

-- Proof sketch: use the coproduct presentations built into
-- `finiteSheafifiedRepresentableSet J B` together with the four basis hypotheses on `B`. The
-- terminal, product, and equalizer clauses are supplied directly by the corresponding fields of
-- `IsFiniteSheafifiedRepresentableCohomologyBasis`. The cover-refinement clause upgrades any
-- locally surjective map onto a finite coproduct of representables by refining the cover over each
-- summand. Finally, part (2) of the remark makes every `U ∈ B` quasi-compact, and then finite
-- coproducts of the corresponding `h_U^#` are quasi-compact as well.
/-- Remark 21.16.3: if a subset `B` of objects of a site satisfies the finite cover-refinement,
product, and equalizer conditions from the remark, then the sheaves which are finite coproducts of
sheafified representables `h_U^#` with `U ∈ B` satisfy the hypotheses of Lemma `21.16.2`. -/
theorem finiteSheafifiedRepresentableSet_isCohomologyColimitTestSet
    (B : Set C) [IsFiniteSheafifiedRepresentableCohomologyBasis J B] :
    IsCohomologyColimitTestSet J (finiteSheafifiedRepresentableSet J B) := sorry

end CategoryTheory.GrothendieckTopology

/-! ### Lemma_21_16_4 (from Chap21) -/
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {I : Type u} [Category.{u} I]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (u : D ⥤ C) [Functor.IsContinuous u JD JC]
variable [HasSheafify JC AddCommGrpCat.{u}] [HasSheafify JD AddCommGrpCat.{u}]
variable [HasExt (Sheaf JC AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (Sheaf JC AddCommGrpCat.{u})]
variable [HasColimitsOfShape I (Sheaf JC AddCommGrpCat.{u})]
variable [HasColimitsOfShape I (Sheaf JD AddCommGrpCat.{u})]
variable [Functor.Additive (u.sheafPushforwardContinuous AddCommGrpCat.{u} JD JC)]

-- Proof sketch: compute `R^p f_*` as the sheafification of the objectwise cohomology presheaf,
-- use that sheafification is a left adjoint and therefore preserves colimits, and apply the local
-- criterion from Lemma `7.10.17` to the comparison map of cohomology presheaves using the covering
-- hypothesis.
/-- Lemma 21.16.4: if every object of `\mathcal D` admits a covering by objects `V` for which the
canonical map `\operatorname{colim}_i H^p(u(V), \mathcal F_i) \to H^p(u(V), \operatorname{colim}_i
\mathcal F_i)` is an isomorphism, then the `p`-th higher direct image of the colimit sheaf is the
colimit of the `p`-th higher direct images. -/
theorem higherDirectImage_colimit_iso_of_locally_objectwise_cohomology_colimit
    (ℱ : I ⥤ Sheaf JC AddCommGrpCat.{u}) (p : ℕ)
    (hcover : ∀ V : D,
      ∃ (ι : Type u) (W : ι → D) (f : ∀ i, W i ⟶ V),
        Sieve.ofArrows W f ∈ JD V ∧
          ∀ i,
            IsIso ((colimit.post ℱ (cohomologyPresheafFunctor JC p)).app
              (op (u.obj (W i))))) :
    IsIsomorphic
      (((u.sheafPushforwardContinuous AddCommGrpCat.{u} JD JC).rightDerived p).obj (colimit ℱ))
      (colimit (ℱ ⋙ (u.sheafPushforwardContinuous AddCommGrpCat.{u} JD JC).rightDerived p)) := sorry

end Sheaf
end CategoryTheory

/-! ### Lemma_21_16_5 (from Chap21) -/
open CategoryTheory Opposite

noncomputable section

universe uI uC vC

namespace CategoryTheory

open CofilteredSiteDiagram

/-- A compatible inverse system of abelian sheaves on the stage sites of `S`, with transition maps
`f_a^{-1} \mathcal F_i ⟶ \mathcal F_j` for arrows `a : j ⟶ i`. -/
structure InverseSystemOfAbelianSheaves
    (S : CofilteredSiteDiagram.{uI, uC, vC}) where
  /-- The abelian sheaf on the stage site `i`. -/
  obj : ∀ i : S.I, Sheaf (S.stageTopology i) AddCommGrpCat.{max uC vC}
  /-- The transition morphism `f_a^{-1} \mathcal F_i ⟶ \mathcal F_j` for `a : j ⟶ i`. -/
  transition : ∀ {i j : S.I} (a : j ⟶ i),
    ((S.stageFunctor a).sheafPullback AddCommGrpCat.{max uC vC}
      (S.stageTopology i) (S.stageTopology j)).obj (obj i) ⟶
      obj j
  /-- The transition morphism for the identity arrow is the canonical identity pullback map. -/
  transition_id : ∀ i : S.I,
    transition (𝟙 i) = (S.stageSheafPullbackIdIso AddCommGrpCat.{max uC vC} i).hom.app (obj i)
  /-- The transition morphisms satisfy the cocycle condition. -/
  transition_comp : ∀ {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j),
    (S.stageSheafPullbackCompIso AddCommGrpCat.{max uC vC} a b).hom.app (obj i) ≫
        transition (b ≫ a) =
      ((S.stageFunctor b).sheafPullback AddCommGrpCat.{max uC vC}
        (S.stageTopology j) (S.stageTopology k)).map (transition a) ≫
        transition b

/-- A morphism of inverse systems of abelian sheaves is a componentwise morphism commuting with
all transition maps. -/
structure InverseSystemOfAbelianSheavesHom
    {S : CofilteredSiteDiagram.{uI, uC, vC}}
    (F G : InverseSystemOfAbelianSheaves S) where
  /-- The morphism on the stage `i`. -/
  app : ∀ i : S.I, F.obj i ⟶ G.obj i
  /-- Compatibility of the component maps with the transition morphisms. -/
  comm : ∀ {i j : S.I} (a : j ⟶ i),
    ((S.stageFunctor a).sheafPullback AddCommGrpCat.{max uC vC}
      (S.stageTopology i) (S.stageTopology j)).map (app i) ≫
        G.transition a =
      F.transition a ≫
        app j

-- Proof sketch: choose for each stage an injective embedding `F.obj i ⟶ A_i`, then form the
-- product over all arrows `b : k ⟶ i` of the pushforwards `f_{b,*} A_k`. The adjoints of the
-- composites `f_b^{-1} F_i ⟶ F_k ⟶ A_k` give a componentwise monomorphism into this product, and
-- the canonical pullback-pushforward comparison maps make the targets into a compatible inverse
-- system. Exactness of stage pushforwards preserves injectives, so each stage of the target system
-- is injective.
/-- Lemma 21.16.5: every inverse system of abelian sheaves on a cofiltered inverse system of sites
admits a morphism into another inverse system whose stagewise maps are monomorphisms and whose
stagewise targets are injective abelian sheaves. -/
theorem exists_mono_to_injective_inverse_system_of_abelian_sheaves
    (S : CofilteredSiteDiagram.{uI, uC, vC})
    (F : InverseSystemOfAbelianSheaves S) :
    ∃ (G : InverseSystemOfAbelianSheaves S) (ι : InverseSystemOfAbelianSheavesHom F G),
      (∀ i : S.I, Mono (ι.app i)) ∧ ∀ i : S.I, Injective (G.obj i) := sorry

end CategoryTheory

/-! ### Lemma_21_16_6 (from Chap21) -/
open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace CategoryTheory

open CofilteredSiteDiagram

/-- The transition morphism between the pullbacks of an inverse system of abelian sheaves to the
colimit site. -/
noncomputable def inverseSystemColimitAbelianSheafTransition
    (S : CofilteredSiteDiagram.{u, u, u})
    [HasColimit S.diagram]
    [HasWeakSheafify S.colimitTopology AddCommGrpCat]
    (F : InverseSystemOfAbelianSheaves S)
    {i j : S.I} (a : j ⟶ i) :
    (((S.stageCoconeFunctor i).sheafPullback AddCommGrpCat
        (S.stageTopology i) S.colimitTopology).obj (F.obj i)) ⟶
      (((S.stageCoconeFunctor j).sheafPullback AddCommGrpCat
        (S.stageTopology j) S.colimitTopology).obj (F.obj j)) :=
  (S.colimitStageSheafPullbackCompIso AddCommGrpCat a).inv.app (F.obj i) ≫
    (((S.stageCoconeFunctor j).sheafPullback AddCommGrpCat
      (S.stageTopology j) S.colimitTopology)).map (F.transition a)

-- Proof sketch: unfold `inverseSystemColimitAbelianSheafTransition`; for the identity arrow the
-- pullback-comparison isomorphism reduces to the identity, and `F.transition_id i` identifies the
-- remaining stagewise transition with the identity morphism.
/-- The colimit-site transition attached to the identity arrow is the identity morphism. -/
private theorem inverseSystemColimitAbelianSheafTransition_id
    (S : CofilteredSiteDiagram.{u, u, u})
    [HasColimit S.diagram]
    [HasWeakSheafify S.colimitTopology AddCommGrpCat]
    (F : InverseSystemOfAbelianSheaves S) (i : S.I) :
    inverseSystemColimitAbelianSheafTransition S F (𝟙 i) =
      𝟙 (((S.stageCoconeFunctor i).sheafPullback AddCommGrpCat
        (S.stageTopology i) S.colimitTopology).obj (F.obj i)) := sorry

-- Proof sketch: compare the two pullback routes from stage `i` to stage `k` through stage `j`,
-- use the coherence isomorphism for the two left-adjoint comparison maps, and finish with
-- `F.transition_comp a b`.
/-- The colimit-site transitions of an inverse system compose canonically. -/
private theorem inverseSystemColimitAbelianSheafTransition_comp
    (S : CofilteredSiteDiagram.{u, u, u})
    [HasColimit S.diagram]
    [HasWeakSheafify S.colimitTopology AddCommGrpCat]
    (F : InverseSystemOfAbelianSheaves S)
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    inverseSystemColimitAbelianSheafTransition S F (b ≫ a) =
      inverseSystemColimitAbelianSheafTransition S F a ≫
        inverseSystemColimitAbelianSheafTransition S F b := sorry

/-- The inverse system `F` pulled back to the colimit site along the stage cocone functors. -/
noncomputable def inverseSystemColimitAbelianSheafDiagram
    (S : CofilteredSiteDiagram.{u, u, u})
    [HasColimit S.diagram]
    [HasWeakSheafify S.colimitTopology AddCommGrpCat]
    (F : InverseSystemOfAbelianSheaves S) :
    S.Iᵒᵖ ⥤ Sheaf S.colimitTopology AddCommGrpCat where
  obj i := (((S.stageCoconeFunctor i.unop).sheafPullback AddCommGrpCat
    (S.stageTopology i.unop) S.colimitTopology).obj (F.obj i.unop))
  map a := inverseSystemColimitAbelianSheafTransition S F a.unop
  map_id := fun i ↦ inverseSystemColimitAbelianSheafTransition_id S F i.unop
  map_comp := fun a b ↦ inverseSystemColimitAbelianSheafTransition_comp S F a.unop b.unop

/-- The colimit abelian sheaf `\mathcal F = \operatorname{colim}_i u_i^{-1} \mathcal F_i`
attached to an inverse system of abelian sheaves on the stage sites of `S`. -/
noncomputable abbrev inverseSystemColimitAbelianSheaf
    (S : CofilteredSiteDiagram.{u, u, u})
    [HasColimit S.diagram]
    [HasWeakSheafify S.colimitTopology AddCommGrpCat]
    [HasColimitsOfShape S.Iᵒᵖ (Sheaf S.colimitTopology AddCommGrpCat)]
    (F : InverseSystemOfAbelianSheaves S) :
    Sheaf S.colimitTopology AddCommGrpCat :=
  colimit (inverseSystemColimitAbelianSheafDiagram S F)

/-- The image of a stage object `X_i` in the colimit category of the site diagram `S`. -/
abbrev colimitStageObject
    (S : CofilteredSiteDiagram.{u, u, u})
    [HasColimit S.diagram] {i : S.I} (X : S.diagram.obj (op i)) :
    (colimit S.diagram : Cat) :=
  (S.stageCoconeFunctor i).obj X

/-- The canonical map from the filtered colimit of the stagewise cohomology objects over the image
of `X_i` to the cohomology of the colimit sheaf over `u_i(X_i)`. This is the Lean model of the
source comparison `\operatorname{colim}_{a : j \to i} H^p(u_a(X_i), \mathcal F_j) \to
H^p(u_i(X_i), \mathcal F)`. -/
noncomputable def inverseSystemStageObjectCohomologyColimitComparison
    (S : CofilteredSiteDiagram.{u, u, u})
    [HasColimit S.diagram]
    [HasWeakSheafify S.colimitTopology AddCommGrpCat]
    [HasSheafify S.colimitTopology AddCommGrpCat]
    [HasExt (Sheaf S.colimitTopology AddCommGrpCat)]
    [HasColimitsOfShape S.Iᵒᵖ (Sheaf S.colimitTopology AddCommGrpCat)]
    [HasColimitsOfShape S.Iᵒᵖ (((colimit S.diagram : Cat)ᵒᵖ) ⥤ AddCommGrpCat)]
    (F : InverseSystemOfAbelianSheaves S) (p : ℕ) {i : S.I} (X : S.diagram.obj (op i)) :
    (colimit
        (inverseSystemColimitAbelianSheafDiagram S F ⋙
          Sheaf.cohomologyPresheafFunctor S.colimitTopology p)).obj
      (op (colimitStageObject S X)) ⟶
    (((Sheaf.cohomologyPresheafFunctor S.colimitTopology p).obj
        (inverseSystemColimitAbelianSheaf S F)).obj
      (op (colimitStageObject S X))) :=
  (colimit.post (inverseSystemColimitAbelianSheafDiagram S F)
      (Sheaf.cohomologyPresheafFunctor S.colimitTopology p)).app
    (op (colimitStageObject S X))

-- Proof sketch: the case `p = 0` is the stagewise section comparison of Lemma `7.18.4`. For
-- `p > 0`, choose a stagewise monomorphism into a stagewise injective system as in Lemma
-- `21.16.5`, pass to the colimit sheaf on the colimit site, and apply the same injective
-- resolution argument as in Lemma `21.16.1`. The remaining acyclicity statement is reduced to
-- Čech cohomology vanishing by Lemmas `21.10.9` and `21.10.2`.
/-- Lemma 21.16.6: for an inverse system of abelian sheaves on a cofiltered inverse system of
sites with colimit sheaf `\mathcal F = \operatorname{colim}_i u_i^{-1}\mathcal F_i`, the
canonical map from the filtered colimit of the cohomology objects over the images `u_a(X_i)` to
the cohomology of `\mathcal F` over `u_i(X_i)` is an isomorphism. This is the canonical Lean form
of the source identity `\operatorname{colim}_{a : j \to i} H^p(u_a(X_i), \mathcal F_j) =
H^p(u_i(X_i), \mathcal F)`. -/
theorem inverseSystemStageObjectCohomologyColimitComparison_isIso
    (S : CofilteredSiteDiagram.{u, u, u})
    [HasColimit S.diagram]
    [HasWeakSheafify S.colimitTopology AddCommGrpCat]
    [HasSheafify S.colimitTopology AddCommGrpCat]
    [HasExt (Sheaf S.colimitTopology AddCommGrpCat)]
    [HasColimitsOfShape S.Iᵒᵖ (Sheaf S.colimitTopology AddCommGrpCat)]
    [HasColimitsOfShape S.Iᵒᵖ (((colimit S.diagram : Cat)ᵒᵖ) ⥤ AddCommGrpCat)]
    (F : InverseSystemOfAbelianSheaves S) {i : S.I} (X : S.diagram.obj (op i)) (p : ℕ) :
    IsIso (inverseSystemStageObjectCohomologyColimitComparison S F p X) := sorry

end CategoryTheory
