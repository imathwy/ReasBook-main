import Mathlib
import stacks_proof.stacks_project.Chap04.Definition_4_35_1
import stacks_proof.stacks_project.Chap08.Definition_8_12_4
import stacks_proof.stacks_project.Chap08.Lemma_8_12_5
import stacks_proof.stacks_project.Chap08.Lemma_8_12_6

open CategoryTheory
open CategoryTheory.Limits
open scoped FibredCategoryOver
open scoped Functor

universe u v uS vS

namespace CategoryTheory

section

variable {C : Type u} {D : Type u}
variable [Category.{v} C] [Category.{v} D]

section Pushforward

variable (u : C ⥤ D)
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

namespace FibredCategoryOver

/-- The fibred category over `D` obtained from `X` by the localized pushforward construction
`uₚ X`. -/
noncomputable abbrev pushforward
    (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (X : FibredCategoryOver C) :
    FibredCategoryOver D :=
  ofFunctor (u.pushforwardProjection X.p)

/- Textbook notation for the pushforward fibred category of `X` along `u`. -/
scoped infixr:100 " ₚ " => pushforward

/-- The projection of `uₚ X` is the strict construction-lift localized pushforward projection. -/
@[simp] theorem pushforward_p
    (X : FibredCategoryOver C) :
    (FibredCategoryOver.pushforward u X).p = u.pushforwardProjection X.p := rfl

end FibredCategoryOver

/-- Helper for Lemma 8.12.8: in a categorical pullback of functors, a morphism whose second
component is strongly cartesian is strongly cartesian for the first projection. -/
theorem pullbackProjection_isStronglyCartesian_of_snd
    {S : Type uS} [Category.{vS} S] (u : C ⥤ D) (p : S ⥤ D)
    {a b : CategoricalPullback u p} (φ : a ⟶ b)
    (hφ : p.IsStronglyCartesian (p.map φ.snd) φ.snd) :
    (CategoricalPullback.π₁ u p).IsStronglyCartesian
      ((CategoricalPullback.π₁ u p).map φ) φ := by
  letI : p.IsStronglyCartesian (p.map φ.snd) φ.snd := hφ
  refine
    { toIsHomLift := by
        simpa using (show (CategoricalPullback.π₁ u p).IsHomLift
          ((CategoricalPullback.π₁ u p).map φ) φ from inferInstance)
      universal_property' := ?_ }
  intro z g θ hθ
  have hθlift : (CategoricalPullback.π₁ u p).IsHomLift (g ≫ φ.fst) θ := by
    simpa using hθ
  have hθfst : g ≫ φ.fst = θ.fst :=
    @IsHomLift.eq_of_isHomLift _ _ _ _ (CategoricalPullback.π₁ u p) _ _
      (g ≫ φ.fst) θ hθlift
  have hθsnd_base :
      p.map θ.snd = (z.iso.inv ≫ u.map g ≫ a.iso.hom) ≫ p.map φ.snd := by
    calc
      p.map θ.snd = z.iso.inv ≫ (z.iso.hom ≫ p.map θ.snd) := by simp
      _ = z.iso.inv ≫ (u.map θ.fst ≫ b.iso.hom) := by rw [θ.w]
      _ = z.iso.inv ≫ (u.map (g ≫ φ.fst) ≫ b.iso.hom) := by
        simpa using
          congrArg (fun k ↦ z.iso.inv ≫ (u.map k ≫ b.iso.hom)) hθfst.symm
      _ = z.iso.inv ≫ (u.map g ≫ u.map φ.fst ≫ b.iso.hom) := by
        simp [Functor.map_comp]
      _ = z.iso.inv ≫ (u.map g ≫ (a.iso.hom ≫ p.map φ.snd)) := by
        simpa [Category.assoc] using
          congrArg (fun k ↦ z.iso.inv ≫ (u.map g ≫ k)) φ.w
      _ = (z.iso.inv ≫ u.map g ≫ a.iso.hom) ≫ p.map φ.snd := by
        simp [Category.assoc]
  have hθsndLift :
      p.IsHomLift ((z.iso.inv ≫ u.map g ≫ a.iso.hom) ≫ p.map φ.snd) θ.snd :=
    IsHomLift.of_fac' p (((z.iso.inv ≫ u.map g ≫ a.iso.hom) ≫ p.map φ.snd))
      θ.snd rfl rfl (by simpa using hθsnd_base)
  letI : p.IsHomLift ((z.iso.inv ≫ u.map g ≫ a.iso.hom) ≫ p.map φ.snd) θ.snd :=
    hθsndLift
  obtain ⟨χsnd, hχsnd, hχuniq⟩ :=
    Functor.IsStronglyCartesian.universal_property p (p.map φ.snd) φ.snd
      (z.iso.inv ≫ u.map g ≫ a.iso.hom)
      (((z.iso.inv ≫ u.map g ≫ a.iso.hom) ≫ p.map φ.snd)) rfl θ.snd
  letI : p.IsHomLift (z.iso.inv ≫ u.map g ≫ a.iso.hom) χsnd := hχsnd.1
  let χ : z ⟶ a :=
    { fst := g
      snd := χsnd
      w := by
        have hχfac :
            p.map χsnd =
              eqToHom rfl ≫ (z.iso.inv ≫ u.map g ≫ a.iso.hom) ≫ eqToHom rfl := by
          simpa using (IsHomLift.fac' p (z.iso.inv ≫ u.map g ≫ a.iso.hom) χsnd)
        calc
          u.map g ≫ a.iso.hom =
              z.iso.hom ≫ (z.iso.inv ≫ u.map g ≫ a.iso.hom) := by simp
          _ = z.iso.hom ≫ p.map χsnd := by
            rw [hχfac]
            simp }
  refine ⟨χ, ⟨?_, ?_⟩, ?_⟩
  · simpa [χ] using (show (CategoricalPullback.π₁ u p).IsHomLift
      ((CategoricalPullback.π₁ u p).map χ) χ from inferInstance)
  · apply CategoricalPullback.hom_ext
    · simpa [χ] using hθfst
    · exact hχsnd.2
  · intro τ hτ
    have hτlift : (CategoricalPullback.π₁ u p).IsHomLift g τ := hτ.1
    have hτfst : g = τ.fst := by
      simpa using
        (@IsHomLift.eq_of_isHomLift _ _ _ _ (CategoricalPullback.π₁ u p) _ _ g τ
          hτlift)
    apply CategoricalPullback.hom_ext
    · simpa [χ] using hτfst.symm
    · have hτsnd_base : p.map τ.snd = z.iso.inv ≫ u.map g ≫ a.iso.hom := by
        calc
          p.map τ.snd = z.iso.inv ≫ (z.iso.hom ≫ p.map τ.snd) := by simp
          _ = z.iso.inv ≫ (u.map τ.fst ≫ a.iso.hom) := by rw [← τ.w]
          _ = z.iso.inv ≫ u.map g ≫ a.iso.hom := by
            simpa using
              congrArg (fun k ↦ z.iso.inv ≫ (u.map k ≫ a.iso.hom)) hτfst.symm
      have hτsndLift : p.IsHomLift (z.iso.inv ≫ u.map g ≫ a.iso.hom) τ.snd :=
        IsHomLift.of_fac' p (z.iso.inv ≫ u.map g ≫ a.iso.hom) τ.snd rfl rfl
          (by simpa using hτsnd_base)
      letI : p.IsHomLift (z.iso.inv ≫ u.map g ≫ a.iso.hom) τ.snd := hτsndLift
      have hτcomp : τ.snd ≫ φ.snd = θ.snd := by
        simpa using congrArg CategoricalPullback.Hom.snd hτ.2
      exact hχuniq τ.snd ⟨inferInstance, hτcomp⟩

abbrev pushforwardFibredCategoryMapPrelocalizedSquare
    {X Y : FibredCategoryOver C} (G : X ⟶ Y) :
    CategoricalPullback.CatCommSqOver
      (Comma.snd (𝟭 D) u) Y.p (u ₚₚ X.p) where
  fst := CategoricalPullback.π₁ (Comma.snd (𝟭 D) u) X.p
  snd := CategoricalPullback.π₂ (Comma.snd (𝟭 D) u) X.p ⋙ FibredCategoryMor.toFunctor G
  iso :=
    (CatCommSq.iso
      (CategoricalPullback.π₁ (Comma.snd (𝟭 D) u) X.p)
      (CategoricalPullback.π₂ (Comma.snd (𝟭 D) u) X.p)
      (Comma.snd (𝟭 D) u) X.p) ≪≫
      eqToIso (by rw [Functor.assoc, FibredCategoryMor.comm G])

abbrev pushforwardFibredCategoryMapPrelocalizedFunctor
    {X Y : FibredCategoryOver C} (G : X ⟶ Y) :
    u ₚₚ X.p ⥤ u ₚₚ Y.p :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
    (Comma.snd (𝟭 D) u) Y.p (u ₚₚ X.p)).obj
      (pushforwardFibredCategoryMapPrelocalizedSquare u G)

/-- Helper for Lemma 8.12.8: the prelocalized map induced by a fibred morphism sends
pushforward denominators for `X` to pushforward denominators for `Y`. -/
theorem pushforwardFibredCategoryMapPrelocalizedFunctor_mapsFraction
    {X Y : FibredCategoryOver C} (G : X ⟶ Y)
    {A B : u ₚₚ X.p} (f : A ⟶ B)
    (hf : u.pushforwardFractions X.p f) :
    u.pushforwardFractions Y.p
      ((pushforwardFibredCategoryMapPrelocalizedFunctor u G).map f) := by
  rcases hf with ⟨hvertical, hstrong⟩
  constructor
  · exact hvertical
  · simpa [pushforwardFibredCategoryMapPrelocalizedFunctor] using
      (FibredCategoryMor.map_stronglyCartesian G f.snd hstrong)

theorem pushforwardFibredCategoryMapPrelocalizedFunctor_invertsFractionProperty
    {X Y : FibredCategoryOver C} (G : X ⟶ Y) :
    (u.pushforwardFractions X.p).IsInvertedBy
      (pushforwardFibredCategoryMapPrelocalizedFunctor u G ⋙
        (u.pushforwardFractions Y.p).Q) := by
  intro A B f hf
  exact Localization.inverts ((u.pushforwardFractions Y.p).Q) (u.pushforwardFractions Y.p)
    ((pushforwardFibredCategoryMapPrelocalizedFunctor u G).map f)
    (pushforwardFibredCategoryMapPrelocalizedFunctor_mapsFraction u G f hf)

noncomputable abbrev pushforwardFibredCategoryMapFunctor
    {X Y : FibredCategoryOver C} (G : X ⟶ Y) :
    (u.pushforwardFractions X.p).Localization ⥤
      (u.pushforwardFractions Y.p).Localization :=
  Localization.Construction.lift
    (pushforwardFibredCategoryMapPrelocalizedFunctor u G ⋙
      (u.pushforwardFractions Y.p).Q)
    (pushforwardFibredCategoryMapPrelocalizedFunctor_invertsFractionProperty u G)

/-- Helper for Lemma 8.12.8: before localization, the map induced by a fibred morphism keeps
the pushforward source projection to `D` unchanged. -/
theorem pushforwardFibredCategoryMapPrelocalizedFunctor_comp_sourceProjection
    {X Y : FibredCategoryOver C} (G : X ⟶ Y) :
    pushforwardFibredCategoryMapPrelocalizedFunctor u G ⋙
        Functor.pushforwardSourceProjection u Y.p =
      Functor.pushforwardSourceProjection u X.p := by
  rfl

theorem pushforwardFibredCategoryMapFunctor_comm
    {X Y : FibredCategoryOver C} (G : X ⟶ Y) :
    pushforwardFibredCategoryMapFunctor u G ⋙ (FibredCategoryOver.pushforward u Y).p =
      (FibredCategoryOver.pushforward u X).p := by
  rw [FibredCategoryOver.pushforward_p, FibredCategoryOver.pushforward_p,
    pushforwardFibredCategoryMapFunctor]
  apply Localization.Construction.uniq
  rw [Localization.Construction.fac]
  rw [← Functor.assoc, Localization.Construction.fac]
  rw [Functor.pushforwardProjection]
  rw [Functor.assoc, Localization.Construction.fac]
  exact pushforwardFibredCategoryMapPrelocalizedFunctor_comp_sourceProjection u G

noncomputable abbrev pushforwardFibredCategoryMapBasedFunctor
    {X Y : FibredCategoryOver C} (G : X ⟶ Y) :
    (FibredCategoryOver.pushforward u X).toBasedCategory ⥤ᵇ
      (FibredCategoryOver.pushforward u Y).toBasedCategory where
  toFunctor := pushforwardFibredCategoryMapFunctor u G
  w := pushforwardFibredCategoryMapFunctor_comm u G

/-- Helper for Lemma 8.12.8: the pushforward map induced by a fibred morphism sends every
morphism to a lift over the original source pushforward base map. -/
theorem pushforwardFibredCategoryMapBasedFunctor_map_isHomLift
    {X Y : FibredCategoryOver C} (G : X ⟶ Y)
    {a b : (FibredCategoryOver.pushforward u X).S} (φ : a ⟶ b) :
    (FibredCategoryOver.pushforward u Y).p.IsHomLift
      ((FibredCategoryOver.pushforward u X).p.map φ)
      ((pushforwardFibredCategoryMapBasedFunctor u G).map φ) := by
  let F := pushforwardFibredCategoryMapBasedFunctor u G
  let pX := (FibredCategoryOver.pushforward u X).p
  let pY := (FibredCategoryOver.pushforward u Y).p
  let hfun : F.toFunctor ⋙ pY = pX := F.w
  let ha : pY.obj (F.obj a) = pX.obj a := Functor.congr_obj hfun a
  let hb : pY.obj (F.obj b) = pX.obj b := Functor.congr_obj hfun b
  refine IsHomLift.of_fac' pY (pX.map φ) (F.map φ) ha hb ?_
  simpa [F, pX, pY, hfun, ha, hb, Functor.comp_map] using Functor.congr_hom hfun φ

/-- Helper for Lemma 8.12.8: the prelocalized map induced by a fibred morphism carries the
source-precomposition chart for `X` to the corresponding source-precomposition chart for `Y`,
up to the canonical pullback isomorphism on the source object. -/
theorem pushforwardFibredCategoryMapPrelocalizedFunctor_map_sourcePrecompose_iso
    {X Y : FibredCategoryOver C} (G : X ⟶ Y)
    (A : u ₚₚ X.p) {V : D} (f : V ⟶ A.fst.left) :
    ∃ e :
        (pushforwardFibredCategoryMapPrelocalizedFunctor u G).obj
            (Functor.pushforwardSourcePrecomposeObj (u := u) (p := X.p) A f) ≅
          Functor.pushforwardSourcePrecomposeObj (u := u) (p := Y.p)
            ((pushforwardFibredCategoryMapPrelocalizedFunctor u G).obj A) f,
      (pushforwardFibredCategoryMapPrelocalizedFunctor u G).map
          (Functor.pushforwardSourcePrecomposeHom (u := u) (p := X.p) A f) =
        e.hom ≫
          Functor.pushforwardSourcePrecomposeHom (u := u) (p := Y.p)
            ((pushforwardFibredCategoryMapPrelocalizedFunctor u G).obj A) f := by
  let e :
      (pushforwardFibredCategoryMapPrelocalizedFunctor u G).obj
          (Functor.pushforwardSourcePrecomposeObj (u := u) (p := X.p) A f) ≅
        Functor.pushforwardSourcePrecomposeObj (u := u) (p := Y.p)
          ((pushforwardFibredCategoryMapPrelocalizedFunctor u G).obj A) f :=
    CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _) (by
      dsimp [pushforwardFibredCategoryMapPrelocalizedFunctor,
        Functor.pushforwardSourcePrecomposeObj]
      simp)
  refine ⟨e, ?_⟩
  apply CategoricalPullback.hom_ext
  · apply CategoryTheory.Comma.hom_ext
    · simp [e, pushforwardFibredCategoryMapPrelocalizedFunctor,
        Functor.pushforwardSourcePrecomposeHom]
    · simp [e, pushforwardFibredCategoryMapPrelocalizedFunctor,
        Functor.pushforwardSourcePrecomposeHom]
  · simp [e, pushforwardFibredCategoryMapPrelocalizedFunctor,
      Functor.pushforwardSourcePrecomposeHom]

/-- Helper for Lemma 8.12.8: an external strong-cartesian result for the mapped localized arrow
over the source pushforward base map rebases to the owner-form strong-cartesian goal in the
target pushforward. -/
theorem pushforwardFibredCategoryMapBasedFunctor_ownerStronglyCartesian_of_external
    {X Y : FibredCategoryOver C} (G : X ⟶ Y)
    {a b : (FibredCategoryOver.pushforward u X).S} (φ : a ⟶ b)
    (hφ :
      (FibredCategoryOver.pushforward u Y).p.IsStronglyCartesian
        ((FibredCategoryOver.pushforward u X).p.map φ)
        ((pushforwardFibredCategoryMapBasedFunctor u G).map φ)) :
    (FibredCategoryOver.pushforward u Y).p.IsStronglyCartesian
      ((FibredCategoryOver.pushforward u Y).p.map
        ((pushforwardFibredCategoryMapBasedFunctor u G).map φ))
      ((pushforwardFibredCategoryMapBasedFunctor u G).map φ) := by
  let F := pushforwardFibredCategoryMapBasedFunctor u G
  let pY := (FibredCategoryOver.pushforward u Y).p
  let hb : pY.obj (F.obj b) = (FibredCategoryOver.pushforward u X).p.obj b :=
    Functor.congr_obj F.w b
  letI :
      pY.IsStronglyCartesian
        ((FibredCategoryOver.pushforward u X).p.map φ) (F.map φ) := by
    simpa [F, pY] using hφ
  simpa [F, pY] using
    (BasedFunctor.isStronglyCartesian_rebase_over_target_eq
      (p := pY) (hb := hb)
      (f := (FibredCategoryOver.pushforward u X).p.map φ) (φ := F.map φ))

end Pushforward

end

end CategoryTheory
