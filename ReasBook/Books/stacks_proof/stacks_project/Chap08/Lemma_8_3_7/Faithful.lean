import StacksProject_2024.Chap08.Lemma_8_3_7.Base

noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)

open SemiRepresentableFamily.Over

/-- Helper for Lemma 8.3.7: a strongly cartesian morphism is right-cancellable against vertical
morphisms once both branches lie over the identity on the same base object. -/
theorem strongly_cartesian_cancel_vertical_postcompose
    {R T : C} {a b c : S} {f : R ⟶ T} (φ : a ⟶ b) [p.IsStronglyCartesian f φ]
    {α β : c ⟶ a} [p.IsHomLift (𝟙 R) α] [p.IsHomLift (𝟙 R) β]
    (h : α ≫ φ = β ≫ φ) :
    α = β := by
  -- This is the strong-cartesian uniqueness principle specialized to vertical lifts over `𝟙 R`.
  simpa using
    (Functor.IsStronglyCartesian.ext (p := p) (f := f) (φ := φ) (g := 𝟙 R)
      (ψ := α) (ψ' := β) h)

/-- Helper for Lemma 8.3.7: `familyDescentFunctor` acts on a morphism by pulling it back
componentwise along the chosen family maps. -/
theorem familyDescentFunctor_map_hom
    {U : C} (𝒰 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    {X Y : p.Fiber U} (θ : X ⟶ Y) (i : 𝒰.index) :
    ((familyDescentFunctor hc 𝒰).map θ).hom i =
      (hc.pullbackFunctor (𝒰.obj i).hom).map θ := by
  -- Unfolding the canonical descent functor shows that the `i`-component is the chosen pullback
  -- map along `Uᵢ ⟶ U`.
  rfl

/-- Helper for Lemma 8.3.7: `pullbackFamilyDescentFunctor` acts on a morphism by pulling it back
componentwise along the refinement maps. -/
theorem pullbackFamilyDescentFunctor_map_hom
    {U V : C}
    {𝒰 : SemiRepresentableFamily.Over U}
    {𝒱 : SemiRepresentableFamily.Over V}
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    (base : U ⟶ V)
    (φ : ((SemiRepresentableFamily.map (Over.map base)).obj 𝒰 ⟶ 𝒱))
    {D₁ D₂ : DescentDatum p hc 𝒱} (θ : D₁ ⟶ D₂) (i : 𝒰.index) :
    ((pullbackFamilyDescentFunctor hc base φ).map θ).hom i =
      (hc.pullbackFunctor (φ.f i).left).map (θ.hom (φ.α i)) := by
  -- Unfolding the refinement pullback functor shows that the `i`-component is the chosen pullback
  -- map along the refinement arrow `Uᵢ ⟶ V_{α(i)}`.
  rfl

/-- Helper for Lemma 8.3.7: swapping the overlap legs rewrites prime-level naturality into the
inverse naturality of the packaged descent comparison isomorphism. -/
theorem descentData_iso_inv_naturality
    {U : C} {𝒰 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰]
    {D₁ D₂ : DescentDatum p hc 𝒰} (θ : D₁ ⟶ D₂)
    {Y : C} (q : Y ⟶ U) {i₁ i₂ : 𝒰.index}
    (f₁ : Y ⟶ (𝒰.obj i₁).left) (f₂ : Y ⟶ (𝒰.obj i₂).left)
    (hf₁ : f₁ ≫ (𝒰.obj i₁).hom = q := by cat_disch)
    (hf₂ : f₂ ≫ (𝒰.obj i₂).hom = q := by cat_disch) :
    (hc.pullbackFunctor f₂).map (θ.hom i₂) ≫
        (D₂.descentData.iso q f₁ f₂ hf₁ hf₂).inv =
      (D₁.descentData.iso q f₁ f₂ hf₁ hf₂).inv ≫
        (hc.pullbackFunctor f₁).map (θ.hom i₁) := by
  -- The owner-level naturality statement is `DescentData'.comm` with the two legs swapped.
  simpa [PullbackChoice.pullbackFunctor, Pseudofunctor.DescentData.iso,
    Pseudofunctor.DescentData.iso_hom] using
    (Pseudofunctor.DescentData'.comm θ q f₂ f₁ hf₂ hf₁)

/-- Helper for Lemma 8.3.7: the inverse pullback-composition comparison is natural in the source
fiber object. -/
theorem pullbackCompComponentIso_inv_naturality
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    {X Y : p.Fiber U} (θ : X ⟶ Y) :
    ((hc.pullbackFunctor g).map ((hc.pullbackFunctor f).map θ)) ≫
        (hc.pullbackCompComponentIso f g Y).inv =
      (hc.pullbackCompComponentIso f g X).inv ≫
        (hc.pullbackFunctor (g ≫ f)).map θ := by
  -- Rewrite hom-side naturality of `hc.pullbackCompIso` so it can be consumed by `rw`.
  let ex := hc.pullbackCompComponentIso f g X
  let ey := hc.pullbackCompComponentIso f g Y
  let η := (hc.pullbackFunctor (g ≫ f)).map θ
  let θ' := ((hc.pullbackFunctor f ⋙ hc.pullbackFunctor g).map θ)
  have hhom : η ≫ ey.hom = ex.hom ≫ θ' := by
    simpa [ex, ey, η, θ'] using (hc.pullbackCompIso f g).hom.naturality θ
  symm
  apply (Iso.eq_comp_inv ey).2
  have hpre :
      ex.inv ≫ (((hc.pullbackFunctor (g ≫ f)).map θ) ≫ ey.hom) =
        ex.inv ≫ (ex.hom ≫ (hc.pullbackFunctor g).map ((hc.pullbackFunctor f).map θ)) := by
    exact congrArg (fun k ↦ ex.inv ≫ k) hhom
  simpa only [← Category.assoc, ex.inv_hom_id, Category.id_comp] using hpre

/-- Helper for Lemma 8.3.7: the component comparison on `U_i ×[U] V_j` is natural in a morphism
of descent data on `𝒰`. -/
theorem member_base_change_comparison_component_naturality
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    {D₁ D₂ : DescentDatum p hc 𝒰} (θ : D₁ ⟶ D₂)
    (φ : 𝒱 ⟶ 𝒰) (i : 𝒰.index) (j : 𝒱.index) :
    (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)).map
        (((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).map θ).hom j) ≫
        (member_base_change_comparison_component_iso hc D₂ φ i j).hom =
      (member_base_change_comparison_component_iso hc D₁ φ i j).hom ≫
        (hc.pullbackFunctor (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)).map (θ.hom i) := by
  -- Route correction: normalize the two comparison factors separately, first through pullback
  -- composition and then through the descent comparison on `D₁` and `D₂`.
  let ex :=
    hc.pullbackCompComponentIso (φ.f j).left
      (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom) (D₁.obj (φ.α j))
  let ey :=
    hc.pullbackCompComponentIso (φ.f j).left
      (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom) (D₂.obj (φ.α j))
  let ζ₁ :=
    D₁.descentData.iso
      (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom ≫ (𝒰.obj i).hom)
      (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)
      (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left)
      rfl
      (by simpa [Category.assoc] using member_base_change_comparison_component_map φ i j)
  let ζ₂ :=
    D₂.descentData.iso
      (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom ≫ (𝒰.obj i).hom)
      (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)
      (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left)
      rfl
      (by simpa [Category.assoc] using member_base_change_comparison_component_map φ i j)
  simp only [pullbackFamilyDescentFunctor_map_hom, member_base_change_comparison_component_iso_hom]
  have hcomp :
      (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)).map
          ((hc.pullbackFunctor (φ.f j).left).map (θ.hom (φ.α j))) ≫
        ey.inv =
      ex.inv ≫
        (hc.pullbackFunctor
          (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left)).map
          (θ.hom (φ.α j)) := by
    -- First pass across the iterated pullback comparison.
    simpa [ex, ey, Functor.map_comp] using
      pullbackCompComponentIso_inv_naturality (hc := hc)
        (φ.f j).left (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)
        (θ.hom (φ.α j))
  have hdesc :
      (hc.pullbackFunctor
          (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left)).map
          (θ.hom (φ.α j)) ≫
        ζ₂.inv =
      ζ₁.inv ≫
        (hc.pullbackFunctor (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)).map (θ.hom i) := by
    -- Then pass across the descent comparison between the two legs to `U`.
    simpa [ζ₁, ζ₂] using
      descentData_iso_inv_naturality (p := p) (hc := hc) θ
        (q := pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom ≫ (𝒰.obj i).hom)
        (i₁ := i) (i₂ := φ.α j)
        (f₁ := pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)
        (f₂ := pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left)
        (hf₁ := rfl)
        (hf₂ := by
          simpa [Category.assoc] using member_base_change_comparison_component_map φ i j)
  trans
      (((hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)).map
            ((hc.pullbackFunctor (φ.f j).left).map (θ.hom (φ.α j))) ≫
          ey.inv) ≫
        ζ₂.inv)
  · -- Reassociate to expose the first comparison factor.
    simpa [identity_refinement_adapter] using
      (Category.assoc
        ((hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)).map
          ((hc.pullbackFunctor (φ.f j).left).map (θ.hom (φ.α j))))
        ey.inv ζ₂.inv).symm
  trans
      ((ex.inv ≫
          (hc.pullbackFunctor
            (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left)).map
            (θ.hom (φ.α j))) ≫
        ζ₂.inv)
  · exact congrArg (fun k ↦ k ≫ ζ₂.inv) hcomp
  trans
      ex.inv ≫
        (ζ₁.inv ≫
          (hc.pullbackFunctor (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)).map (θ.hom i))
  · -- Move the second comparison factor across the fixed left isomorphism.
    calc
      ((ex.inv ≫
            (hc.pullbackFunctor
              (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left)).map
              (θ.hom (φ.α j))) ≫
          ζ₂.inv)
          =
        ex.inv ≫
          ((hc.pullbackFunctor
              (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left)).map
              (θ.hom (φ.α j)) ≫
            ζ₂.inv) := by
              exact Category.assoc ex.inv
                ((hc.pullbackFunctor
                    (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left)).map
                    (θ.hom (φ.α j)))
                ζ₂.inv
      _ = ex.inv ≫
            (ζ₁.inv ≫
              (hc.pullbackFunctor (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)).map
                (θ.hom i)) := by
              exact congrArg (fun k ↦ ex.inv ≫ k) hdesc
  · -- Reassociate back to the packaged right-hand comparison.
    simpa [ex, ζ₁] using
      (Category.assoc ex.inv ζ₁.inv
        ((hc.pullbackFunctor (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)).map (θ.hom i))).symm

/-- Helper for Lemma 8.3.7: the refinement pullback functor is faithful once each local descent
functor on `𝒱_i` is faithful. -/
theorem pullbackFamilyDescentFunctor_faithful_of_refinement
    {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index,
      HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    [∀ i : 𝒰.index,
      Functor.Faithful (familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i))]
    (φ : 𝒱 ⟶ 𝒰) :
    Functor.Faithful
      (pullbackFamilyDescentFunctor hc (𝟙 U)
        (identity_refinement_adapter φ)) := by
  let P :=
    pullbackFamilyDescentFunctor hc (𝟙 U)
      (identity_refinement_adapter φ)
  refine ⟨?_⟩
  intro D₁ D₂ θ₁ θ₂ hθ
  -- Follow the source proof: recover equality of each `U_i`-component via the faithful local
  -- descent functor on `𝒱_i`, using the comparison isomorphism to transport `P.map θ`.
  apply Pseudofunctor.DescentData'.hom_ext
  intro i
  have hlocalMap :
      (familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).map (θ₁.hom i) =
        (familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).map (θ₂.hom i) := by
    apply Pseudofunctor.DescentData'.hom_ext
    intro j
    let e₁ := member_base_change_comparison_component_iso hc D₁ φ i j
    let e₂ := member_base_change_comparison_component_iso hc D₂ φ i j
    have hPj : (P.map θ₁).hom j = (P.map θ₂).hom j := by
      simpa [P] using congrArg (fun ψ ↦ ψ.hom j) hθ
    have hleft :
        (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)).map
            ((P.map θ₁).hom j) ≫ e₂.hom =
          (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)).map
            ((P.map θ₂).hom j) ≫ e₂.hom := by
      exact congrArg
        (fun k ↦
          (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)).map k ≫ e₂.hom)
        hPj
    have hcomp :
        e₁.hom ≫
            (hc.pullbackFunctor (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)).map (θ₁.hom i) =
          e₁.hom ≫
            (hc.pullbackFunctor (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)).map (θ₂.hom i) := by
      have hnat₁ :
          (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)).map
              ((P.map θ₁).hom j) ≫ e₂.hom =
            e₁.hom ≫
              (hc.pullbackFunctor (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)).map (θ₁.hom i) := by
        simpa [e₁, e₂] using
          (member_base_change_comparison_component_naturality
            (p := p) (hc := hc) (D₁ := D₁) (D₂ := D₂) θ₁ φ i j)
      have hnat₂ :
          (hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)).map
              ((P.map θ₂).hom j) ≫ e₂.hom =
            e₁.hom ≫
              (hc.pullbackFunctor (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)).map (θ₂.hom i) := by
        simpa [e₁, e₂] using
          (member_base_change_comparison_component_naturality
            (p := p) (hc := hc) (D₁ := D₁) (D₂ := D₂) θ₂ φ i j)
      exact hnat₁.symm.trans (hleft.trans hnat₂)
    have hcomponent :
        (hc.pullbackFunctor (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)).map (θ₁.hom i) =
          (hc.pullbackFunctor (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)).map (θ₂.hom i) := by
      -- Cancel the left comparison isomorphism.
      have hpre := congrArg (fun k ↦ e₁.inv ≫ k) hcomp
      simpa [Category.assoc, e₁.inv_hom_id] using hpre
    -- The local descent functor acts componentwise by pullback along `U_i ×[U] V_j ⟶ U_i`.
    simpa [familyDescentFunctor_map_hom] using hcomponent
  exact (familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).map_injective hlocalMap

end CategoryTheory
