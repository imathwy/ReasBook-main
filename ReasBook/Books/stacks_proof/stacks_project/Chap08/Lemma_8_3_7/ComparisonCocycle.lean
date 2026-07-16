import stacks_proof.stacks_project.Chap08.Lemma_8_3_7.Base

noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory.Bicategory

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)

open SemiRepresentableFamily.Over

private theorem member_base_change_comparison_component_iso_inv_to_owner_pullHom'
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (D : DescentDatum p hc 𝒰) (φ : 𝒱 ⟶ 𝒰) (i : 𝒰.index) (j : 𝒱.index) :
    Functor.Fiber.fiberInclusion.map
        ((D.descentData.iso
          (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom ≫ (𝒰.obj i).hom)
          (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)
          (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left)
          rfl
          (by
            simpa [Category.assoc] using
              member_base_change_comparison_component_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j)).inv)
      =
    Functor.Fiber.fiberInclusion.map
      (Pseudofunctor.DescentData'.pullHom' D.hom
        (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫
          (φ.f j).left ≫ (𝒰.obj (φ.α j)).hom)
        (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left)
        (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)
        (by simp)
        (by
          simpa [Category.assoc] using
            (member_base_change_comparison_component_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j).symm)) := by
  -- Rewrite the inverse comparison as the owner theorem `pullHom'_ofDescentData_hom` for
  -- `D.descentData`, using the owner-side route to `U` as the controlling map.
  simpa [Pseudofunctor.DescentData.iso, Pseudofunctor.DescentData.iso_hom] using
    congrArg Functor.Fiber.fiberInclusion.map <|
      (Pseudofunctor.DescentData'.pullHom'_ofDescentData_hom
        (sq := 𝒰.pairwisePullback) (sq₃ := 𝒰.triplePullback) (D := D.descentData)
        (q := pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫
          (φ.f j).left ≫ (𝒰.obj (φ.α j)).hom)
        (i₁ := φ.α j) (i₂ := i)
        (f₁ := pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left)
        (f₂ := pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)
        (hf₁ := by simp)
        (hf₂ := by
          simpa [Category.assoc] using
            (member_base_change_comparison_component_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j).symm))

/-- Helper for Lemma 8.3.7: at the fiber level, the inverse descent comparison appearing in a
component comparison is exactly the owner-side `pullHom'` term. -/
private theorem member_base_change_comparison_component_iso_inv_hom_to_owner_pullHom'
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (D : DescentDatum p hc 𝒰) (φ : 𝒱 ⟶ 𝒰) (i : 𝒰.index) (j : 𝒱.index) :
    (D.descentData.iso
        (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom ≫ (𝒰.obj i).hom)
        (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)
        (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left)
        rfl
        (by
          simpa [Category.assoc] using
            member_base_change_comparison_component_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j)).inv
      =
    Pseudofunctor.DescentData'.pullHom' D.hom
      (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫
        (φ.f j).left ≫ (𝒰.obj (φ.α j)).hom)
      (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left)
      (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)
      (by simp)
      (by
        simpa [Category.assoc] using
          (member_base_change_comparison_component_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j).symm) := by
  -- This is the fiber-level form of the owner-side `pullHom'` identification used later under
  -- further pullback functors.
  simpa [Pseudofunctor.DescentData.iso, Pseudofunctor.DescentData.iso_hom] using
    (Pseudofunctor.DescentData'.pullHom'_ofDescentData_hom
      (sq := 𝒰.pairwisePullback) (sq₃ := 𝒰.triplePullback) (D := D.descentData)
      (q := pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫
        (φ.f j).left ≫ (𝒰.obj (φ.α j)).hom)
      (i₁ := φ.α j) (i₂ := i)
      (f₁ := pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left)
      (f₂ := pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)
      (hf₁ := by simp)
      (hf₂ := by
        simpa [Category.assoc] using
          (member_base_change_comparison_component_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j).symm))

/-- Helper for Lemma 8.3.7: before forgetting to the ambient category, the full comparison
component is the iterated-pullback comparison followed by the owner-side `pullHom'` term. -/
private theorem member_base_change_comparison_component_iso_hom_to_owner_pullHom'
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (D : DescentDatum p hc 𝒰) (φ : 𝒱 ⟶ 𝒰) (i : 𝒰.index) (j : 𝒱.index) :
    (member_base_change_comparison_component_iso hc D φ i j).hom =
      (hc.pullbackCompComponentIso (φ.f j).left
        (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom) (D.obj (φ.α j))).inv ≫
      Pseudofunctor.DescentData'.pullHom' D.hom
        (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫
          (φ.f j).left ≫ (𝒰.obj (φ.α j)).hom)
        (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left)
        (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)
        (by simp)
        (by
          simpa [Category.assoc] using
            (member_base_change_comparison_component_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j).symm) := by
  -- Unfold the component comparison and replace the inverse descent comparison by the owner-side
  -- `pullHom'` term at the fiber level.
  rw [member_base_change_comparison_component_iso_hom]
  rw [member_base_change_comparison_component_iso_inv_hom_to_owner_pullHom'
    (p := p) (hc := hc) D φ i j]
  rfl

/-- Helper for Lemma 8.3.7: after forgetting to the ambient category, the full comparison component
is the iterated-pullback comparison followed by the owner-side `pullHom'` term. -/
private theorem member_base_change_comparison_component_iso_to_owner_pullHom'
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (D : DescentDatum p hc 𝒰) (φ : 𝒱 ⟶ 𝒰) (i : 𝒰.index) (j : 𝒱.index) :
    Functor.Fiber.fiberInclusion.map
        ((member_base_change_comparison_component_iso hc D φ i j).hom) =
      Functor.Fiber.fiberInclusion.map
          ((hc.pullbackCompComponentIso (φ.f j).left
            (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom) (D.obj (φ.α j))).inv) ≫
      Functor.Fiber.fiberInclusion.map
          (Pseudofunctor.DescentData'.pullHom' D.hom
            (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫
              (φ.f j).left ≫ (𝒰.obj (φ.α j)).hom)
            (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left)
            (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)
            (by simp)
            (by
              simpa [Category.assoc] using
                (member_base_change_comparison_component_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j).symm)) := by
  -- Unfold the component comparison once, then replace its inverse descent comparison by the
  -- owner-side `pullHom'` shell isolated above.
  rw [member_base_change_comparison_component_iso_hom]
  -- First split the ambient functor across the composite comparison, then normalize the second
  -- factor to the owner-side `pullHom'`.
  calc
    Functor.Fiber.fiberInclusion.map
        ((hc.pullbackCompComponentIso (φ.f j).left
          (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom) (D.obj (φ.α j))).inv ≫
          (D.descentData.iso
            (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom ≫ (𝒰.obj i).hom)
            (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)
            (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left)
            rfl
            (by
              simpa [Category.assoc] using
                member_base_change_comparison_component_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j)).inv)
      =
        Functor.Fiber.fiberInclusion.map
            ((hc.pullbackCompComponentIso (φ.f j).left
              (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom) (D.obj (φ.α j))).inv) ≫
          Functor.Fiber.fiberInclusion.map
            ((D.descentData.iso
              (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom ≫ (𝒰.obj i).hom)
              (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)
              (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left)
              rfl
              (by
                simpa [Category.assoc] using
                  member_base_change_comparison_component_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j)).inv) := by
            simp [Functor.map_comp]
    _ =
        Functor.Fiber.fiberInclusion.map
            ((hc.pullbackCompComponentIso (φ.f j).left
              (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom) (D.obj (φ.α j))).inv) ≫
          Functor.Fiber.fiberInclusion.map
            (Pseudofunctor.DescentData'.pullHom' D.hom
              (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫
                (φ.f j).left ≫ (𝒰.obj (φ.α j)).hom)
              (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left)
              (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)
              (by simp)
              (by
                simpa [Category.assoc] using
                  (member_base_change_comparison_component_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j).symm)) := by
            exact congrArg
              (fun k ↦
                Functor.Fiber.fiberInclusion.map
                    ((hc.pullbackCompComponentIso (φ.f j).left
                      (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom) (D.obj (φ.α j))).inv) ≫ k)
              (member_base_change_comparison_component_iso_inv_to_owner_pullHom'
                (p := p) (hc := hc) D φ i j)

/-- Helper for Lemma 8.3.7: the owner-side normalization of a comparison component remains valid
after postcomposition in the ambient category. This isolates the typed boundary used in the
transport-heavy overlap calculation. -/
private theorem member_base_change_comparison_component_iso_to_owner_pullHom'_assoc
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (D : DescentDatum p hc 𝒰) (φ : 𝒱 ⟶ 𝒰) (i : 𝒰.index) (j : 𝒱.index)
    {Z : S}
    (m :
      (hc.obj (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom) (D.obj i)).1 ⟶ Z) :
    Functor.Fiber.fiberInclusion.map
        ((member_base_change_comparison_component_iso hc D φ i j).hom) ≫ m =
      Functor.Fiber.fiberInclusion.map
          ((hc.pullbackCompComponentIso (φ.f j).left
            (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom) (D.obj (φ.α j))).inv) ≫
        Functor.Fiber.fiberInclusion.map
          (Pseudofunctor.DescentData'.pullHom' D.hom
            (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫
              (φ.f j).left ≫ (𝒰.obj (φ.α j)).hom)
            (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left)
            (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)
            (by simp)
            (by
              simpa [Category.assoc] using
                (member_base_change_comparison_component_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j).symm)) ≫
        m := by
  -- Postcompose the already-proved owner-side normalization by the fixed ambient arrow `m`.
  calc
    Functor.Fiber.fiberInclusion.map
        ((member_base_change_comparison_component_iso hc D φ i j).hom) ≫
        m
      =
        (Functor.Fiber.fiberInclusion.map
            (hc.pullbackCompComponentIso (φ.f j).left
              (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom) (D.obj (φ.α j))).inv ≫
          Functor.Fiber.fiberInclusion.map
            (Pseudofunctor.DescentData'.pullHom' D.hom
              (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫
                (φ.f j).left ≫ (𝒰.obj (φ.α j)).hom)
              (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left)
              (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)
              (by simp)
              (by
                simpa [Category.assoc] using
                  (member_base_change_comparison_component_map
                    (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j).symm))) ≫
          m := by
            exact congrArg (fun k ↦ k ≫ m)
              (member_base_change_comparison_component_iso_to_owner_pullHom'
                (p := p) (hc := hc) D φ i j)
    _ =
        Functor.Fiber.fiberInclusion.map
            (hc.pullbackCompComponentIso (φ.f j).left
              (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom) (D.obj (φ.α j))).inv ≫
          Functor.Fiber.fiberInclusion.map
            (Pseudofunctor.DescentData'.pullHom' D.hom
              (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫
                (φ.f j).left ≫ (𝒰.obj (φ.α j)).hom)
              (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left)
              (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)
              (by simp)
              (by
                simpa [Category.assoc] using
                  (member_base_change_comparison_component_map
                    (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j).symm)) ≫
            m := by
              simp [Category.assoc]

-- Proof sketch: pull a descent datum on `𝒰` back to one on `𝒱` along the refinement morphism
-- `φ : 𝒱 ⟶ 𝒰` using Lemma `8.3.3`; by
-- effectiveness for `𝒱`, it comes from a global object over `U`. The fully faithful local
-- functors for the families `𝒱_i` identify the restrictions of that global object with the given
-- local pieces over each `U_i`, and the faithfulness for `𝒱_{ii'}` forces compatibility on
-- pairwise overlaps. This yields essential surjectivity, while the same local full-faithfulness
-- and overlap faithfulness give full faithfulness of the canonical descent functor for `𝒰`.
/-- Helper for Lemma 8.3.7: `familyDescentFunctor` acts on a morphism by pulling it back
componentwise along the chosen family maps. -/
private theorem familyDescentFunctor_map_hom
    {U : C} (𝒰 : SemiRepresentableFamily.Over U)
    [HasDescentPullbacks 𝒰]
    {X Y : p.Fiber U} (θ : X ⟶ Y) (i : 𝒰.index) :
    ((familyDescentFunctor hc 𝒰).map θ).hom i =
      (hc.pullbackFunctor (𝒰.obj i).hom).map θ := by
  -- Unfolding the chosen-overlap descent functor shows that its `i`-component is literally the
  -- pullback-functor map along `Uᵢ ⟶ U`.
  rfl

/-- Helper for Lemma 8.3.7: `pullbackFamilyDescentFunctor` acts on a morphism by pulling it back
componentwise along the refinement maps. -/
private theorem pullbackFamilyDescentFunctor_map_hom
    {U V : C}
    {𝒰 : SemiRepresentableFamily.Over U}
    {𝒱 : SemiRepresentableFamily.Over V}
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    (base : U ⟶ V)
    (φ : ((SemiRepresentableFamily.map (Over.map base)).obj 𝒰 ⟶ 𝒱))
    {D₁ D₂ : DescentDatum p hc 𝒱} (θ : D₁ ⟶ D₂) (i : 𝒰.index) :
    ((pullbackFamilyDescentFunctor hc base φ).map θ).hom i =
      (hc.pullbackFunctor (φ.f i).left).map (θ.hom (φ.α i)) := by
  -- Unfolding the refinement pullback functor shows that its `i`-component is the pullback-functor
  -- map along the refinement arrow `Uᵢ ⟶ V_{α(i)}`.
  rfl

/-- Helper for Lemma 8.3.7: forgetting a fiber morphism composite is just the ambient
composite of the forgotten morphisms. -/
private theorem fiberInclusion_map_comp_local
    {U : C} {p : S ⥤ C} [p.IsFibered] {X Y Z : p.Fiber U}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.Fiber.fiberInclusion.map (f ≫ g) =
      Functor.Fiber.fiberInclusion.map f ≫ Functor.Fiber.fiberInclusion.map g := rfl

private theorem fiberInclusion_map_comp_two_iso_cancel
    {U : C} {p : S ⥤ C} [p.IsFibered]
    {X₀ X₁ X₂ X₃ X₄ : p.Fiber U}
    (a : X₀ ⟶ X₁) (m : X₁ ⟶ X₂) (e : X₂ ≅ X₃) (e' : X₃ ≅ X₄) :
    Functor.Fiber.fiberInclusion.map (a ≫ m ≫ e.hom) ≫
        Functor.Fiber.fiberInclusion.map e'.hom ≫
        Functor.Fiber.fiberInclusion.map e'.inv ≫
        Functor.Fiber.fiberInclusion.map e.inv =
      Functor.Fiber.fiberInclusion.map a ≫ Functor.Fiber.fiberInclusion.map m := by
  have he' :
      Functor.Fiber.fiberInclusion.map e'.hom ≫
          Functor.Fiber.fiberInclusion.map e'.inv = 𝟙 _ := by
    rw [← Functor.map_comp]
    simp
  have he :
      Functor.Fiber.fiberInclusion.map e.hom ≫
          Functor.Fiber.fiberInclusion.map e.inv = 𝟙 _ := by
    rw [← Functor.map_comp]
    simp
  calc
    Functor.Fiber.fiberInclusion.map (a ≫ m ≫ e.hom) ≫
        Functor.Fiber.fiberInclusion.map e'.hom ≫
        Functor.Fiber.fiberInclusion.map e'.inv ≫
        Functor.Fiber.fiberInclusion.map e.inv
        = (Functor.Fiber.fiberInclusion.map a ≫
            Functor.Fiber.fiberInclusion.map m ≫
            Functor.Fiber.fiberInclusion.map e.hom) ≫
          Functor.Fiber.fiberInclusion.map e'.hom ≫
          Functor.Fiber.fiberInclusion.map e'.inv ≫
          Functor.Fiber.fiberInclusion.map e.inv := by
          simp [Functor.map_comp, Category.assoc]
    _ = Functor.Fiber.fiberInclusion.map a ≫ Functor.Fiber.fiberInclusion.map m := by
          simp [he', he, Category.assoc]

private theorem pullbackFunctor_map_eq_fiberPseudofunctor_map
    {U V : C} (f : V ⟶ U) {x y : p.Fiber U} (φ : x ⟶ y) :
    (hc.pullbackFunctor f).map φ =
      (hc.fiberPseudofunctor.map f.op.toLoc).toFunctor.map φ := rfl

/-- Helper for Lemma 8.3.7: after forgetting to the ambient category, a chosen pullback-functor
map factors through the chosen cartesian arrow over the target object. -/
private theorem fiberInclusion_map_pullbackFunctor_map_fac_local
    {U V : C} (f : V ⟶ U) {x y : p.Fiber U} (φ : x ⟶ y) :
    Functor.Fiber.fiberInclusion.map ((hc.pullbackFunctor f).map φ) ≫ hc.map f y =
      hc.map f x ≫ φ.1 := by
  -- Unfold the chosen pullback map as the universal arrow induced by strong cartesianness.
  letI : p.IsHomLift (𝟙 U) φ.1 := φ.2
  letI : p.IsHomLift f (hc.map f x ≫ φ.1) :=
    IsHomLift.comp_lift_id_right' p f (hc.map f x) U φ.1
  change Functor.IsStronglyCartesian.map p f (hc.map f y) (Category.id_comp f).symm
      (hc.map f x ≫ φ.1) ≫ hc.map f y = hc.map f x ≫ φ.1
  -- The defining factorization of the chosen lift is exactly the desired ambient equality.
  simpa using
    (IsStronglyCartesian.fac p f (hc.map f y) (Category.id_comp f).symm
      (hc.map f x ≫ φ.1))

/-- Helper for Lemma 8.3.7: the factorization of a mapped pullback morphism is stable after a
fixed postcomposition in the ambient category. -/
private theorem fiberInclusion_map_pullbackFunctor_map_fac_assoc_local
    {U V : C} (f : V ⟶ U) {x y : p.Fiber U} (φ : x ⟶ y) {Z : S}
    (m : y.1 ⟶ Z) :
    Functor.Fiber.fiberInclusion.map ((hc.pullbackFunctor f).map φ) ≫ hc.map f y ≫ m =
      hc.map f x ≫ φ.1 ≫ m := by
  -- Postcompose the basic factorization equality by the fixed ambient morphism `m`.
  have hpost :
      (Functor.Fiber.fiberInclusion.map ((hc.pullbackFunctor f).map φ) ≫ hc.map f y) ≫ m =
        (hc.map f x ≫ φ.1) ≫ m := by
    exact congrArg (fun k ↦ k ≫ m)
      (fiberInclusion_map_pullbackFunctor_map_fac_local (hc := hc) f φ)
  calc
    Functor.Fiber.fiberInclusion.map ((hc.pullbackFunctor f).map φ) ≫ hc.map f y ≫ m
      = (hc.map f x ≫ φ.1) ≫ m := by
          simpa [Category.assoc] using hpost
    _ = hc.map f x ≫ φ.1 ≫ m := by
          simp [Category.assoc]

/-- Helper for Lemma 8.3.7: swapping the two overlap legs turns prime-level naturality into
inverse naturality for the packaged comparison isomorphisms. -/
private theorem descentData_iso_inv_naturality
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
  -- Swapping the overlap legs rewrites inverse naturality into the prime-level morphism
  -- naturality relation `DescentData'.comm`.
  simpa [PullbackChoice.pullbackFunctor, Pseudofunctor.DescentData.iso,
    Pseudofunctor.DescentData.iso_hom] using
    (Pseudofunctor.DescentData'.comm θ q f₂ f₁ hf₂ hf₁)

/-- Helper for Lemma 8.3.7: the inverse of the pullback-composition comparison isomorphism is
natural in the object of the source fiber. -/
private theorem pullbackCompComponentIso_inv_naturality
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    {X Y : p.Fiber U} (θ : X ⟶ Y) :
    ((hc.pullbackFunctor g).map ((hc.pullbackFunctor f).map θ)) ≫
        (hc.pullbackCompComponentIso f g Y).inv =
      (hc.pullbackCompComponentIso f g X).inv ≫
        (hc.pullbackFunctor (g ≫ f)).map θ := by
  -- Repackage the hom-side naturality of `hc.pullbackCompIso f g` so the inverse comparison can
  -- be used directly in later `rw`-style component calculations.
  let ex := hc.pullbackCompComponentIso f g X
  let ey := hc.pullbackCompComponentIso f g Y
  let η := (hc.pullbackFunctor (g ≫ f)).map θ
  let θ' := ((hc.pullbackFunctor f ⋙ hc.pullbackFunctor g).map θ)
  have hhom :
      η ≫ ey.hom = ex.hom ≫ θ' := by
    simpa [ex, ey, η, θ'] using
      (hc.pullbackCompIso f g).hom.naturality θ
  -- Move the right comparison hom across the naturality square, then cancel the left comparison.
  symm
  apply (Iso.eq_comp_inv ey).2
  have hhom' := hhom
  dsimp [η, θ'] at hhom' ⊢
  have hpre :
      ex.inv ≫ (((hc.pullbackFunctor (g ≫ f)).map θ) ≫ ey.hom) =
        ex.inv ≫ (ex.hom ≫
          (hc.pullbackFunctor g).map ((hc.pullbackFunctor f).map θ)) := by
    exact congrArg (fun k ↦ ex.inv ≫ k) hhom'
  simpa only [← Category.assoc, ex.inv_hom_id, Category.id_comp] using hpre

/-- Helper for Lemma 8.3.7: the inverse pullback-composition factorization stays valid after a
fixed ambient postcomposition. This is the form used when the common middle leg has already been
chosen in the overlap calculation. -/
private theorem pullbackCompComponentIso_inv_fac_assoc
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : p.Fiber U) {Z : S}
    (m : x.1 ⟶ Z) :
    (hc.pullbackCompComponentIso f g x).inv.1 ≫ hc.map (g ≫ f) x ≫ m =
      hc.map g (f ^*[hc] x) ≫ hc.map f x ≫ m := by
  -- Postcompose the standard iterated-pullback factorization by the fixed ambient morphism `m`.
  simpa [Category.assoc] using
    congrArg (fun k ↦ k ≫ m)
      (hc.pullbackCompComponentIso_inv_fac (f := f) (g := g) x)

/-- Helper for Lemma 8.3.7: the component comparison on `U_i ×[U] V_j` is natural in the descent
datum morphism. -/
private theorem member_base_change_comparison_component_naturality
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
  -- Route correction: first rewrite the iterated pullback factor with the new inverse-side
  -- naturality of `hc.pullbackCompComponentIso`, then close the remaining packaged comparison by
  -- `descentData_iso_inv_naturality`.
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
    -- This is the cast-stable inverse naturality of `hc.pullbackCompComponentIso`.
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
    -- The remaining comparison is the packaged inverse naturality square for `D₁` and `D₂`.
    simpa [ζ₁, ζ₂] using
      descentData_iso_inv_naturality (p := p) (hc := hc) θ
        (q := pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom ≫ (𝒰.obj i).hom)
        (i₁ := i) (i₂ := φ.α j)
        (f₁ := pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)
        (f₂ := pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom ≫ (φ.f j).left)
        (hf₁ := rfl)
        (hf₂ := by
          simpa [Category.assoc] using
            member_base_change_comparison_component_map φ i j)
  -- Insert the inverse pullback-comparison naturality, then the descent-data inverse
  -- naturality, and only reassociate at the boundaries where the packaged comparison reappears.
  trans
      (((hc.pullbackFunctor (pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)).map
            ((hc.pullbackFunctor (φ.f j).left).map (θ.hom (φ.α j))) ≫
          ey.inv) ≫
        ζ₂.inv)
  · -- Reassociate the source composite so the inverse pullback-comparison factor is isolated.
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
  · -- Move the descent-data inverse naturality across the fixed left comparison `ex.inv`.
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
  · -- Reassociate once more so the packaged comparison morphism on the right is visible again.
    simpa [ex, ζ₁] using
      (Category.assoc ex.inv ζ₁.inv
        ((hc.pullbackFunctor (pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)).map (θ.hom i))).symm

/-- Helper for Lemma 8.3.7: the source transition on the chosen overlap of `𝒱_i` is the owner-side
descent morphism of the restricted pulled-back datum. -/
private theorem member_base_change_source_transition_hom
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index, HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (D : DescentDatum p hc 𝒰) (φ : 𝒱 ⟶ 𝒰) (i : 𝒰.index) (j₁ j₂ : 𝒱.index) :
    (pullbackFamilyDescentDatum hc (𝒰 := 𝒱.memberBaseChange 𝒰 i) (𝒱 := 𝒱) (𝒰.obj i).hom
      (member_base_change_refinement_adapter 𝒰 𝒱 i)
      ((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D)).descentData.hom
        ((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p
        ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
        ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
        ((𝒱.memberBaseChange 𝒰 i).pr0_map j₁ j₂)
        ((𝒱.memberBaseChange 𝒰 i).pr1_map j₁ j₂)
      =
    (pullbackFamilyDescentDatum hc (𝒰 := 𝒱.memberBaseChange 𝒰 i) (𝒱 := 𝒱) (𝒰.obj i).hom
      (member_base_change_refinement_adapter 𝒰 𝒱 i)
      ((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D)).hom j₁ j₂ := by
  -- On the chosen overlap, the primed descent datum stores exactly this owner-side morphism.
  simpa using
    (Pseudofunctor.DescentData'.pullHom'_eq_hom
      (pullbackFamilyDescentDatum hc (𝒰 := 𝒱.memberBaseChange 𝒰 i) (𝒱 := 𝒱) (𝒰.obj i).hom
        (member_base_change_refinement_adapter 𝒰 𝒱 i)
        ((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D))
      j₁ j₂)

/-- Helper for Lemma 8.3.7: on the overlap of `𝒱_i`, the raw left outer leg to `V_{j₁}` lies
over the common owner map to `U`. -/
private theorem member_base_change_source_left_raw_leg_map
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index, HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    (i : 𝒰.index) (j₁ j₂ : 𝒱.index) :
    ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
        pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom ≫
          (𝒱.obj j₁).hom =
      ((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom := by
  -- First replace the route through `V_{j₁}` by the route through `U_i`, then collapse the
  -- restricted overlap map by `pr0_map`.
  calc
    ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
        pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom ≫
          (𝒱.obj j₁).hom
      =
        (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
          pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫
            (𝒰.obj i).hom := by
              simpa [Category.assoc] using
                congrArg
                  (fun f ↦ ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫ f)
                  (member_base_change_refinement_component_w
                    (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁)
    _ = ((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom := by
          exact congrArg
            (fun f ↦ f ≫ (𝒰.obj i).hom)
            ((𝒱.memberBaseChange 𝒰 i).pr0_map j₁ j₂)

/-- Helper for Lemma 8.3.7: on the overlap of `𝒱_i`, the raw right outer leg to `V_{j₂}` also
lies over the common owner map to `U`. -/
private theorem member_base_change_source_right_raw_leg_map
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index, HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    (i : 𝒰.index) (j₁ j₂ : 𝒱.index) :
    ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
        pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom ≫
          (𝒱.obj j₂).hom =
      ((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom := by
  -- The right route is normalized in the same way, now using `pr1_map`.
  calc
    ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
        pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom ≫
          (𝒱.obj j₂).hom
      =
        (((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
          pullback.snd (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫
            (𝒰.obj i).hom := by
              simpa [Category.assoc] using
                congrArg
                  (fun f ↦ ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫ f)
                  (member_base_change_refinement_component_w
                    (𝒰 := 𝒰) (𝒱 := 𝒱) i j₂)
    _ = ((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom := by
          exact congrArg
            (fun f ↦ f ≫ (𝒰.obj i).hom)
            ((𝒱.memberBaseChange 𝒰 i).pr1_map j₁ j₂)

/-- Helper for Lemma 8.3.7: the inverse component of the fiber pseudofunctor's flexible
composition comparison is the chosen pullback-composition comparison in the fiber. -/
theorem fiberPseudofunctor_mapComp'_inv_app_eq_pullbackCompComponentIso_inv
    {U V W : C} {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (f : V ⟶ U) (g : W ⟶ V) (X : p.Fiber U) :
    ((hc.fiberPseudofunctor.mapComp' f.op.toLoc g.op.toLoc (f.op.toLoc ≫ g.op.toLoc)
        (by simp)).inv.toNatTrans.app X) =
      (hc.pullbackCompComponentIso f g X).inv := by
  -- The fiber pseudofunctor is built from `hc.pullbackCompIso`, and `mapComp'` reduces to
  -- `mapComp` on the canonical composite `(g ≫ f).op.toLoc`.
  simp [PullbackChoice.fiberPseudofunctor, PullbackChoice.pullbackCompIso,
    Pseudofunctor.mapComp'_eq_mapComp]

/-- Helper for Lemma 8.3.7: the hom component of the fiber pseudofunctor's flexible composition
comparison is the chosen pullback-composition comparison in the fiber. -/
theorem fiberPseudofunctor_mapComp'_hom_app_eq_pullbackCompComponentIso_hom
    {U V W : C} {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (f : V ⟶ U) (g : W ⟶ V) (X : p.Fiber U) :
    ((hc.fiberPseudofunctor.mapComp' f.op.toLoc g.op.toLoc (f.op.toLoc ≫ g.op.toLoc)
        (by simp)).hom.toNatTrans.app X) =
      (hc.pullbackCompComponentIso f g X).hom := by
  -- This is the hom-side version of the same packaged comparison isomorphism.
  simp [PullbackChoice.fiberPseudofunctor, PullbackChoice.pullbackCompIso,
    Pseudofunctor.mapComp'_eq_mapComp]

/-- Helper for Lemma 8.3.7: composing in `C` and then passing to the locally discrete opposite is
the same as composing the corresponding `toLoc` arrows in the order used by `mapComp'`. -/
private theorem comp_toLoc_eq_local
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf) :
    f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc := by
  simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
    congrArg Quiver.Hom.toLoc (congrArg Quiver.Hom.op hgf)

/-- Helper for Lemma 8.3.7: inverse pullback-composition comparisons are coherent
for three composable arrows, with the final composite supplied in the left-associated form used by
owner-side overlap maps. -/
private theorem pullbackCompComponentIso_inv_assoc_flexible
    {A B D E : C} {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (f : D ⟶ E) (g : B ⟶ D) (h : A ⟶ B) (X : p.Fiber E) :
    (hc.pullbackFunctor h).map ((hc.pullbackCompComponentIso f g X).inv) ≫
      ((hc.fiberPseudofunctor.mapComp' (g ≫ f).op.toLoc h.op.toLoc
        (((h ≫ g) ≫ f).op.toLoc)
        (comp_toLoc_eq_local (g ≫ f) h (gf := ((h ≫ g) ≫ f))
          (by simp [Category.assoc]))).inv.toNatTrans.app X) =
    (hc.pullbackCompComponentIso g h (f ^*[hc] X)).inv ≫
      (hc.pullbackCompComponentIso f (h ≫ g) X).inv := by
  simpa [PullbackChoice.fiberPseudofunctor, PullbackChoice.pullbackCompIso,
    Pseudofunctor.mapComp'_eq_mapComp, Category.assoc] using
    (hc.fiberPseudofunctor.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app
      f.op.toLoc g.op.toLoc h.op.toLoc (g ≫ f).op.toLoc (h ≫ g).op.toLoc
      (((h ≫ g) ≫ f).op.toLoc)
      (comp_toLoc_eq_local f g (gf := g ≫ f) rfl)
      (comp_toLoc_eq_local g h (gf := h ≫ g) rfl)
      (comp_toLoc_eq_local (g ≫ f) h (gf := ((h ≫ g) ≫ f))
        (by simp [Category.assoc])) X)

/-- Helper for Lemma 8.3.7: the hom component of a flexible pullback-composition comparison
factors as the chosen composite pullback arrow, even when the composite leg is supplied by an
equality proof. -/
private theorem fiberPseudofunctor_mapComp'_hom_app_fac
    {A B D : C} {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf)
    (X : p.Fiber D) :
    Functor.Fiber.fiberInclusion.map
        ((hc.fiberPseudofunctor.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq_local f g gf hgf)).hom.toNatTrans.app X) ≫
      hc.map g ((hc.fiberPseudofunctor.map f.op.toLoc).toFunctor.obj X) ≫
      hc.map f X =
    hc.map gf X := by
  subst gf
  simpa [PullbackChoice.fiberPseudofunctor, PullbackChoice.pullbackCompIso,
    Pseudofunctor.mapComp'_eq_mapComp, Category.assoc] using
    hc.pullbackCompComponentIso_fac f g X

private theorem fiberPseudofunctor_mapComp'_inv_app_fac
    {A B D : C} {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf)
    (X : p.Fiber D) :
    Functor.Fiber.fiberInclusion.map
        ((hc.fiberPseudofunctor.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq_local f g gf hgf)).inv.toNatTrans.app X) ≫
      hc.map gf X =
    hc.map g ((hc.fiberPseudofunctor.map f.op.toLoc).toFunctor.obj X) ≫
      hc.map f X := by
  subst gf
  simpa [PullbackChoice.fiberPseudofunctor, PullbackChoice.pullbackCompIso,
    Pseudofunctor.mapComp'_eq_mapComp, Category.assoc] using
    hc.pullbackCompComponentIso_inv_fac (f := f) (g := g) X

private theorem fiberPseudofunctor_map_postcompose_eq_pullHom
    {X₁ X₂ Y Y' : C} {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (g : Y' ⟶ Y)
    (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    {M₁ : p.Fiber X₁} {M₂ : p.Fiber X₂}
    (φ : (hc.fiberPseudofunctor.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (hc.fiberPseudofunctor.map f₂.op.toLoc).toFunctor.obj M₂) :
    Functor.Fiber.fiberInclusion.map
        ((hc.fiberPseudofunctor.map g.op.toLoc).toFunctor.map φ) ≫
      hc.map g ((hc.fiberPseudofunctor.map f₂.op.toLoc).toFunctor.obj M₂) ≫
      hc.map f₂ M₂ =
    Functor.Fiber.fiberInclusion.map
        ((hc.fiberPseudofunctor.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq_local f₁ g gf₁ hgf₁)).inv.toNatTrans.app M₁) ≫
      Functor.Fiber.fiberInclusion.map
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ g gf₁ gf₂ hgf₁ hgf₂) ≫
      hc.map gf₂ M₂ := by
  have hmap := congrArg Functor.Fiber.fiberInclusion.map
    (Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
      (F := hc.fiberPseudofunctor) φ g gf₁ gf₂ hgf₁ hgf₂)
  have hmap_split :
      Functor.Fiber.fiberInclusion.map
          ((hc.fiberPseudofunctor.map g.op.toLoc).toFunctor.map φ) =
        Functor.Fiber.fiberInclusion.map
            ((hc.fiberPseudofunctor.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
              (comp_toLoc_eq_local f₁ g gf₁ hgf₁)).inv.toNatTrans.app M₁) ≫
          Functor.Fiber.fiberInclusion.map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ g gf₁ gf₂ hgf₁ hgf₂) ≫
          Functor.Fiber.fiberInclusion.map
            ((hc.fiberPseudofunctor.mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
              (comp_toLoc_eq_local f₂ g gf₂ hgf₂)).hom.toNatTrans.app M₂) := by
    change
      Functor.Fiber.fiberInclusion.map
          ((hc.fiberPseudofunctor.map g.op.toLoc).toFunctor.map φ) =
        Functor.Fiber.fiberInclusion.map
          (((hc.fiberPseudofunctor.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
              (comp_toLoc_eq_local f₁ g gf₁ hgf₁)).inv.toNatTrans.app M₁) ≫
            Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ g gf₁ gf₂ hgf₁ hgf₂ ≫
            ((hc.fiberPseudofunctor.mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
              (comp_toLoc_eq_local f₂ g gf₂ hgf₂)).hom.toNatTrans.app M₂))
    exact hmap
  calc
    Functor.Fiber.fiberInclusion.map
        ((hc.fiberPseudofunctor.map g.op.toLoc).toFunctor.map φ) ≫
      hc.map g ((hc.fiberPseudofunctor.map f₂.op.toLoc).toFunctor.obj M₂) ≫
      hc.map f₂ M₂ =
        (Functor.Fiber.fiberInclusion.map
            ((hc.fiberPseudofunctor.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
              (comp_toLoc_eq_local f₁ g gf₁ hgf₁)).inv.toNatTrans.app M₁) ≫
          Functor.Fiber.fiberInclusion.map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ g gf₁ gf₂ hgf₁ hgf₂) ≫
          Functor.Fiber.fiberInclusion.map
            ((hc.fiberPseudofunctor.mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
              (comp_toLoc_eq_local f₂ g gf₂ hgf₂)).hom.toNatTrans.app M₂)) ≫
          hc.map g ((hc.fiberPseudofunctor.map f₂.op.toLoc).toFunctor.obj M₂) ≫
          hc.map f₂ M₂ := by
            exact
              congrArg
                (fun k ↦ k ≫
                  hc.map g ((hc.fiberPseudofunctor.map f₂.op.toLoc).toFunctor.obj M₂) ≫
                  hc.map f₂ M₂)
                hmap_split
    _ = Functor.Fiber.fiberInclusion.map
          ((hc.fiberPseudofunctor.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq_local f₁ g gf₁ hgf₁)).inv.toNatTrans.app M₁) ≫
        Functor.Fiber.fiberInclusion.map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ g gf₁ gf₂ hgf₁ hgf₂) ≫
        hc.map gf₂ M₂ := by
          have hfac :=
            fiberPseudofunctor_mapComp'_hom_app_fac (hc := hc) f₂ g gf₂ hgf₂ M₂
          simpa [Category.assoc] using
            congrArg
              (fun k ↦
                (Functor.Fiber.fiberInclusion.map
                    ((hc.fiberPseudofunctor.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
                      (comp_toLoc_eq_local f₁ g gf₁ hgf₁)).inv.toNatTrans.app M₁) ≫
                  Functor.Fiber.fiberInclusion.map
                    (Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ g gf₁ gf₂ hgf₁ hgf₂)) ≫ k)
              hfac

private theorem pullback_hom_ext_local
    {U V : C} {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p) (f : V ⟶ U)
    {x : p.Fiber U} {y : p.Fiber V} {ψ ψ' : y ⟶ f ^*[hc] x}
    (h : ψ.1 ≫ hc.map f x = ψ'.1 ≫ hc.map f x) : ψ = ψ' := by
  apply Functor.Fiber.hom_ext
  change ψ.1 = ψ'.1
  letI : p.IsHomLift (𝟙 V) ψ.1 := ψ.2
  letI : p.IsHomLift (𝟙 V) ψ'.1 := ψ'.2
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
      f (hc.map f x) inferInstance _ _ (𝟙 V) ψ.1 ψ'.1 inferInstance inferInstance h


/-- Helper for Lemma 8.3.7: the canonical transition in the descent datum attached to a single
fiber object becomes the equality of the two chosen cartesian routes after postcomposition back to
that object. -/
private theorem familyDescentFunctor_obj_hom_postcompose
    {U : C} (𝒰 : SemiRepresentableFamily.Over U) [HasDescentPullbacks 𝒰]
    {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (X : p.Fiber U) (i j : 𝒰.index) :
    Functor.Fiber.fiberInclusion.map (((familyDescentFunctor hc 𝒰).obj X).hom i j) ≫
        hc.map (𝒰.pr1 i j) (((familyDescentFunctor hc 𝒰).obj X).obj j) ≫
        hc.map (𝒰.obj j).hom X =
      hc.map (𝒰.pr0 i j) (((familyDescentFunctor hc 𝒰).obj X).obj i) ≫
        hc.map (𝒰.obj i).hom X := by
  let e := hc.pullbackCompComponentIso (𝒰.obj i).hom (𝒰.pr0 i j) X
  have hbase : (𝒰.pr1 i j) ≫ (𝒰.obj j).hom =
      (𝒰.pr0 i j) ≫ (𝒰.obj i).hom := by
    exact (𝒰.pr1_map i j).trans (𝒰.pr0_map i j).symm
  have hright :
      Functor.Fiber.fiberInclusion.map
          ((hc.fiberPseudofunctor.mapComp' (𝒰.obj j).hom.op.toLoc
            (𝒰.pr1 i j).op.toLoc
            ((𝒰.obj i).hom.op.toLoc ≫ (𝒰.pr0 i j).op.toLoc) (by
              simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
                congrArg Quiver.Hom.toLoc (congrArg Quiver.Hom.op hbase))).hom.toNatTrans.app X) ≫
        hc.map (𝒰.pr1 i j) (((familyDescentFunctor hc 𝒰).obj X).obj j) ≫
        hc.map (𝒰.obj j).hom X =
      hc.map ((𝒰.pr0 i j) ≫ (𝒰.obj i).hom) X := by
    simpa [familyDescentFunctor, comp_toLoc_eq_local, ← Quiver.Hom.comp_toLoc, ← op_comp] using
      fiberPseudofunctor_mapComp'_hom_app_fac (hc := hc)
        (f := (𝒰.obj j).hom) (g := 𝒰.pr1 i j)
        (gf := (𝒰.pr0 i j) ≫ (𝒰.obj i).hom) hbase X
  have hleft :
      e.inv.1 ≫ hc.map ((𝒰.pr0 i j) ≫ (𝒰.obj i).hom) X =
        hc.map (𝒰.pr0 i j) (((familyDescentFunctor hc 𝒰).obj X).obj i) ≫
          hc.map (𝒰.obj i).hom X := by
    simpa [e, familyDescentFunctor] using
      hc.pullbackCompComponentIso_inv_fac (𝒰.obj i).hom (𝒰.pr0 i j) X
  have hfirst :
      Functor.Fiber.fiberInclusion.map (((familyDescentFunctor hc 𝒰).obj X).hom i j) ≫
          hc.map (𝒰.pr1 i j) (((familyDescentFunctor hc 𝒰).obj X).obj j) ≫
          hc.map (𝒰.obj j).hom X =
        e.inv.1 ≫ hc.map ((𝒰.pr0 i j) ≫ (𝒰.obj i).hom) X := by
    dsimp [familyDescentFunctor]
    let α :=
      ((hc.fiberPseudofunctor.mapComp' (𝒰.obj i).hom.op.toLoc
        (pullback.fst (𝒰.obj i).hom (𝒰.obj j).hom).op.toLoc
        ((𝒰.obj i).hom.op.toLoc ≫
          (pullback.fst (𝒰.obj i).hom (𝒰.obj j).hom).op.toLoc)
        (by simp)).inv.toNatTrans.app X)
    let β :=
      ((hc.fiberPseudofunctor.mapComp' (𝒰.obj j).hom.op.toLoc
        (pullback.snd (𝒰.obj i).hom (𝒰.obj j).hom).op.toLoc
        ((𝒰.obj i).hom.op.toLoc ≫
          (pullback.fst (𝒰.obj i).hom (𝒰.obj j).hom).op.toLoc)
        (by
          simpa [SemiRepresentableFamily.Over.pr0, SemiRepresentableFamily.Over.pr1,
            SemiRepresentableFamily.Over.pairwisePullback, ← Quiver.Hom.comp_toLoc,
            ← op_comp] using
            congrArg Quiver.Hom.toLoc (congrArg Quiver.Hom.op hbase))).hom.toNatTrans.app X)
    change Functor.Fiber.fiberInclusion.map (α ≫ β) ≫
        hc.map (𝒰.pr1 i j) ((hc.fiberPseudofunctor.map (𝒰.obj j).hom.op.toLoc).toFunctor.obj X) ≫
        hc.map (𝒰.obj j).hom X =
      e.inv.1 ≫ hc.map ((𝒰.pr0 i j) ≫ (𝒰.obj i).hom) X
    rw [show Functor.Fiber.fiberInclusion.map (α ≫ β) =
        Functor.Fiber.fiberInclusion.map α ≫ Functor.Fiber.fiberInclusion.map β from
      Functor.map_comp Functor.Fiber.fiberInclusion α β]
    simpa [α, β, e, Category.assoc, SemiRepresentableFamily.Over.pr0,
      SemiRepresentableFamily.Over.pr1, SemiRepresentableFamily.Over.pairwisePullback,
      fiberPseudofunctor_mapComp'_inv_app_eq_pullbackCompComponentIso_inv] using
      congrArg (fun k ↦ e.inv.1 ≫ k) hright
  exact hfirst.trans hleft

/-- Helper for Lemma 8.3.7: after exposing the restricted datum's `.descentData.hom`, the
remaining `descentDataEquivalence.inverse` transport is exactly the raw owner-side
`pullFunctorObjHom` on the restricted family. -/
private theorem pullbackFamilyDescentDatum_descentData_hom_eq_pullFunctorObjHom
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index, HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (D : DescentDatum p hc 𝒰) (φ : 𝒱 ⟶ 𝒰) (i : 𝒰.index) (j₁ j₂ : 𝒱.index) :
    (pullbackFamilyDescentDatum hc (𝒰 := 𝒱.memberBaseChange 𝒰 i) (𝒱 := 𝒱) (𝒰.obj i).hom
        (member_base_change_refinement_adapter 𝒰 𝒱 i)
        ((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D)).descentData.hom
          ((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p
          ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
          ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
          ((𝒱.memberBaseChange 𝒰 i).pr0_map j₁ j₂)
          ((𝒱.memberBaseChange 𝒰 i).pr1_map j₁ j₂)
      =
    Pseudofunctor.DescentData.pullFunctorObjHom
      (F := hc.fiberPseudofunctor)
      (p := (𝒰.obj i).hom)
      (f := fun j : 𝒱.index ↦ (𝒱.obj j).hom)
      (f' := fun j : (𝒱.memberBaseChange 𝒰 i).index ↦
        ((𝒱.memberBaseChange 𝒰 i).obj j).hom)
      (α := fun j ↦ j)
      (p' := fun j ↦ pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)
      (w := member_base_change_refinement_component_w (𝒰 := 𝒰) (𝒱 := 𝒱) i)
      (Pseudofunctor.DescentData'.descentData
        ((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D))
      (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
        pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
      ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
      ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
      (by rfl)
      (by
        simpa [SemiRepresentableFamily.Over.memberBaseChange] using
          ((𝒱.memberBaseChange 𝒰 i).pr0_map_eq_pr1_map j₁ j₂).symm) := by
  -- Unfold only to the `descentDataEquivalence.inverse` boundary, then remove that packaging by
  -- the canonical owner theorem `pullHom'_ofDescentData_hom`.
  simpa only [pullbackFamilyDescentDatum, pullbackFamilyDescentFunctor,
    Pseudofunctor.DescentData'.descentData_hom] using
    (Pseudofunctor.DescentData'.pullHom'_ofDescentData_hom
      (sq := (𝒱.memberBaseChange 𝒰 i).pairwisePullback)
      (sq₃ := (𝒱.memberBaseChange 𝒰 i).triplePullback)
      (D := ((Pseudofunctor.DescentData.pullFunctor hc.fiberPseudofunctor
        (w := member_base_change_refinement_component_w (𝒰 := 𝒰) (𝒱 := 𝒱) i)).obj
          (Pseudofunctor.DescentData'.descentData
            ((pullbackFamilyDescentFunctor hc (𝟙 U)
              (identity_refinement_adapter φ)).obj D))))
      (q := (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
        pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom))
      (i₁ := j₁) (i₂ := j₂)
      (f₁ := (𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
      (f₂ := (𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
      (hf₁ := by rfl)
      (hf₂ := by
        simpa [SemiRepresentableFamily.Over.memberBaseChange] using
          ((𝒱.memberBaseChange 𝒰 i).pr0_map_eq_pr1_map j₁ j₂).symm))

/-- Helper for Lemma 8.3.7: after one explicit `pullFunctorObjHom_eq` specialization, the source
transition on the chosen overlap of `𝒱_i` is rewritten as the owner-side transition of the inner
refined datum on the same overlap. -/
private theorem member_base_change_source_transition_outer_normalize
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index, HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (D : DescentDatum p hc 𝒰) (φ : 𝒱 ⟶ 𝒰) (i : 𝒰.index) (j₁ j₂ : 𝒱.index) :
    (pullbackFamilyDescentDatum hc (𝒰 := 𝒱.memberBaseChange 𝒰 i) (𝒱 := 𝒱) (𝒰.obj i).hom
      (member_base_change_refinement_adapter 𝒰 𝒱 i)
      ((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D)).hom
        j₁ j₂
      =
    (hc.pullbackCompComponentIso
        (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
        ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
        (((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D).obj
          j₁)).inv ≫
      (((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D).descentData.hom
        (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
        (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
          pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
        (((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
          pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
        (by
          simpa [Category.assoc] using
            member_base_change_source_left_raw_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)
        (by
          simpa [Category.assoc] using
            member_base_change_source_right_raw_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)) ≫
      (hc.pullbackCompComponentIso
        (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
        ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
        (((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D).obj
          j₂)).hom := by
  -- Route correction: move from the packaged chosen-overlap morphism to the raw owner-side
  -- `pullFunctorObjHom`, then specialize that raw term with `pullFunctorObjHom_eq`.
  have h_source :
      (pullbackFamilyDescentDatum hc (𝒰 := 𝒱.memberBaseChange 𝒰 i) (𝒱 := 𝒱) (𝒰.obj i).hom
          (member_base_change_refinement_adapter 𝒰 𝒱 i)
          ((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D)).hom
            j₁ j₂
        =
      (pullbackFamilyDescentDatum hc (𝒰 := 𝒱.memberBaseChange 𝒰 i) (𝒱 := 𝒱) (𝒰.obj i).hom
          (member_base_change_refinement_adapter 𝒰 𝒱 i)
          ((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D)).descentData.hom
            ((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p
            ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
            ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
            ((𝒱.memberBaseChange 𝒰 i).pr0_map j₁ j₂)
            ((𝒱.memberBaseChange 𝒰 i).pr1_map j₁ j₂) := by
    -- The primed datum stores its chosen-overlap map as this owner-side `pullHom'`.
    exact (member_base_change_source_transition_hom
      (p := p) (hc := hc) D φ i j₁ j₂).symm
  have h_transport :
      (pullbackFamilyDescentDatum hc (𝒰 := 𝒱.memberBaseChange 𝒰 i) (𝒱 := 𝒱) (𝒰.obj i).hom
          (member_base_change_refinement_adapter 𝒰 𝒱 i)
          ((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D)).descentData.hom
            ((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p
            ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
            ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
            ((𝒱.memberBaseChange 𝒰 i).pr0_map j₁ j₂)
            ((𝒱.memberBaseChange 𝒰 i).pr1_map j₁ j₂)
        =
      Pseudofunctor.DescentData.pullFunctorObjHom
        (F := hc.fiberPseudofunctor)
        (p := (𝒰.obj i).hom)
        (f := fun j : 𝒱.index ↦ (𝒱.obj j).hom)
        (f' := fun j : (𝒱.memberBaseChange 𝒰 i).index ↦
          ((𝒱.memberBaseChange 𝒰 i).obj j).hom)
        (α := fun j ↦ j)
        (p' := fun j ↦ pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)
        (w := member_base_change_refinement_component_w (𝒰 := 𝒰) (𝒱 := 𝒱) i)
        (Pseudofunctor.DescentData'.descentData
          ((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D))
        (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
          pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
        ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
        ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
        (by rfl)
        (by
          simpa [SemiRepresentableFamily.Over.memberBaseChange] using
            ((𝒱.memberBaseChange 𝒰 i).pr0_map_eq_pr1_map j₁ j₂).symm) := by
    -- The new adapter lemma isolates the `descentDataEquivalence.inverse` transport once.
    simpa using
      pullbackFamilyDescentDatum_descentData_hom_eq_pullFunctorObjHom
        (p := p) (hc := hc) D φ i j₁ j₂
  have h_shell :
      Pseudofunctor.DescentData.pullFunctorObjHom
        (F := hc.fiberPseudofunctor)
        (p := (𝒰.obj i).hom)
        (f := fun j : 𝒱.index ↦ (𝒱.obj j).hom)
        (f' := fun j : (𝒱.memberBaseChange 𝒰 i).index ↦
          ((𝒱.memberBaseChange 𝒰 i).obj j).hom)
        (α := fun j ↦ j)
        (p' := fun j ↦ pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)
        (w := member_base_change_refinement_component_w (𝒰 := 𝒰) (𝒱 := 𝒱) i)
        (Pseudofunctor.DescentData'.descentData
          ((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D))
        (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
          pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
        ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
        ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
        (by rfl)
        (by
          simpa [SemiRepresentableFamily.Over.memberBaseChange] using
            ((𝒱.memberBaseChange 𝒰 i).pr0_map_eq_pr1_map j₁ j₂).symm)
        =
      (hc.pullbackCompComponentIso
          (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
          ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
          (((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D).obj
            j₁)).inv ≫
        (((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D).descentData.hom
          (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
          (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
            pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
          (((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
            pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
          (by
            simpa [Category.assoc] using
              member_base_change_source_left_raw_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)
          (by
            simpa [Category.assoc] using
              member_base_change_source_right_raw_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)) ≫
        (hc.pullbackCompComponentIso
          (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
          ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
          (((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D).obj
            j₂)).hom := by
    -- `pullFunctorObjHom_eq` produces the right owner-side shell; the two new bridge lemmas turn
    -- its `mapComp'` components into the chapter-level pullback-comparison components.
    simpa [fiberPseudofunctor_mapComp'_inv_app_eq_pullbackCompComponentIso_inv,
      fiberPseudofunctor_mapComp'_hom_app_eq_pullbackCompComponentIso_hom] using
      (Pseudofunctor.DescentData.pullFunctorObjHom_eq
        (F := hc.fiberPseudofunctor)
        (p := (𝒰.obj i).hom)
        (f := fun j : 𝒱.index ↦ (𝒱.obj j).hom)
        (f' := fun j : (𝒱.memberBaseChange 𝒰 i).index ↦
          ((𝒱.memberBaseChange 𝒰 i).obj j).hom)
        (α := fun j ↦ j)
        (p' := fun j ↦ pullback.fst (𝒱.obj j).hom (𝒰.obj i).hom)
        (w := member_base_change_refinement_component_w (𝒰 := 𝒰) (𝒱 := 𝒱) i)
        (D := Pseudofunctor.DescentData'.descentData
          ((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D))
        (q := (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
          pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom))
        (j₁ := j₁) (j₂ := j₂)
        (f₁ := (𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
        (f₂ := (𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
        (q' := ((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
        (f₁' := ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
          pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
        (f₂' := ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
          pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
        (hf₁ := by rfl)
        (hf₂ := by
          simpa [SemiRepresentableFamily.Over.memberBaseChange] using
            ((𝒱.memberBaseChange 𝒰 i).pr0_map_eq_pr1_map j₁ j₂).symm)
        (hq' := by
          simpa using
            congrArg
              (fun f ↦ f ≫ (𝒰.obj i).hom)
              ((𝒱.memberBaseChange 𝒰 i).pr0_map j₁ j₂))
        (hf₁' := by rfl)
        (hf₂' := by rfl))
  exact h_source.trans (h_transport.trans h_shell)

/-- Helper for Lemma 8.3.7: once the outer `pullFunctorObjHom_eq` shell is exposed, the middle
generic descent morphism is definitionally the primed chosen-overlap morphism of the inner datum. -/
private theorem pullbackFamilyDescentDatum_pullFunctorObjHom_to_pullHom'_shell
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index, HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (D : DescentDatum p hc 𝒰) (φ : 𝒱 ⟶ 𝒰) (i : 𝒰.index) (j₁ j₂ : 𝒱.index) :
    (hc.pullbackCompComponentIso
        (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
        ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
        (((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D).obj
          j₁)).inv ≫
      (((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D).descentData.hom
        (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
        (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
          pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
        (((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
          pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
        (by
          simpa [Category.assoc] using
            member_base_change_source_left_raw_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)
        (by
          simpa [Category.assoc] using
            member_base_change_source_right_raw_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)) ≫
      (hc.pullbackCompComponentIso
        (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
        ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
        (((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D).obj
          j₂)).hom
      =
    (hc.pullbackCompComponentIso
        (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
        ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
        (((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D).obj
          j₁)).inv ≫
      ((Pseudofunctor.DescentData'.descentData
          ((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D)).hom
        (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
        (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
          pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
        (((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
          pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
        (by
          simpa [Category.assoc] using
            member_base_change_source_left_raw_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)
        (by
          simpa [Category.assoc] using
            member_base_change_source_right_raw_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)) ≫
      (hc.pullbackCompComponentIso
        (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
        ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
        (((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D).obj
          j₂)).hom := by
  -- The packaged `descentData` on a primed datum is defined by this same chosen-overlap map.
  rfl

/-- Helper for Lemma 8.3.7: a second explicit normalization step rewrites the exposed middle term
to the primed chosen-overlap shell of the inner refined datum. -/
private theorem member_base_change_source_transition_inner_normalize
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index, HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (D : DescentDatum p hc 𝒰) (φ : 𝒱 ⟶ 𝒰) (i : 𝒰.index) (j₁ j₂ : 𝒱.index) :
    (pullbackFamilyDescentDatum hc (𝒰 := 𝒱.memberBaseChange 𝒰 i) (𝒱 := 𝒱) (𝒰.obj i).hom
      (member_base_change_refinement_adapter 𝒰 𝒱 i)
      ((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D)).hom
        j₁ j₂ =
      (hc.pullbackCompComponentIso
          (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
          ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
          (((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D).obj
            j₁)).inv ≫
        ((Pseudofunctor.DescentData'.descentData
            ((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D)).hom
            (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
            (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
              pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
            (((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
              pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
            (by
              simpa [Category.assoc] using
                member_base_change_source_left_raw_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)
            (by
              simpa [Category.assoc] using
                member_base_change_source_right_raw_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)) ≫
        (hc.pullbackCompComponentIso
          (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
          ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
            (((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D).obj
            j₂)).hom := by
  -- Route correction: the source proof first identifies the chosen overlap morphism with the
  -- generic owner-side pullback morphism, then exposes the outer pullback shell, and only then
  -- switches the middle term to the primed chosen-overlap view.
  have h_outer :
      (pullbackFamilyDescentDatum hc (𝒰 := 𝒱.memberBaseChange 𝒰 i) (𝒱 := 𝒱) (𝒰.obj i).hom
        (member_base_change_refinement_adapter 𝒰 𝒱 i)
        ((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D)).hom
          j₁ j₂
        =
      (hc.pullbackCompComponentIso
          (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
          ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
          (((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D).obj
            j₁)).inv ≫
        (((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D).descentData.hom
          (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
          (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
            pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
          (((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
            pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
          (by
            simpa [Category.assoc] using
              member_base_change_source_left_raw_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)
          (by
            simpa [Category.assoc] using
              member_base_change_source_right_raw_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)) ≫
        (hc.pullbackCompComponentIso
          (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
          ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
          (((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D).obj
            j₂)).hom :=
    member_base_change_source_transition_outer_normalize (p := p) (hc := hc) D φ i j₁ j₂
  have h_middle :
      (hc.pullbackCompComponentIso
          (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
          ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
          (((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D).obj
            j₁)).inv ≫
        (((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D).descentData.hom
          (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
          (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
            pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
          (((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
            pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
          (by
            simpa [Category.assoc] using
              member_base_change_source_left_raw_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)
          (by
            simpa [Category.assoc] using
              member_base_change_source_right_raw_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)) ≫
        (hc.pullbackCompComponentIso
          (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
          ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
          (((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D).obj
            j₂)).hom
        =
      (hc.pullbackCompComponentIso
          (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
          ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
          (((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D).obj
            j₁)).inv ≫
        ((Pseudofunctor.DescentData'.descentData
            ((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D)).hom
          (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
          (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
            pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
          (((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
            pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
          (by
            simpa [Category.assoc] using
              member_base_change_source_left_raw_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)
          (by
            simpa [Category.assoc] using
              member_base_change_source_right_raw_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)) ≫
        (hc.pullbackCompComponentIso
          (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
          ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
          (((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D).obj
            j₂)).hom :=
    pullbackFamilyDescentDatum_pullFunctorObjHom_to_pullHom'_shell
      (p := p) (hc := hc) D φ i j₁ j₂
  exact h_outer.trans h_middle

/-- Helper for Lemma 8.3.7: the target transition on the chosen overlap of `𝒱_i` is the owner-side
descent morphism of the descent datum attached to `D.obj i`. -/
private theorem member_base_change_target_transition_hom
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index, HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (D : DescentDatum p hc 𝒰) (i : 𝒰.index) (j₁ j₂ : 𝒱.index) :
    ((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).descentData.hom
        ((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p
        ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
        ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
        ((𝒱.memberBaseChange 𝒰 i).pr0_map j₁ j₂)
        ((𝒱.memberBaseChange 𝒰 i).pr1_map j₁ j₂)
      =
    ((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).hom j₁ j₂ := by
  -- The target datum is already a primed descent datum on `𝒱_i`, so its overlap morphism is
  -- the owner-side `pullHom'` comparison after unfolding the chosen restricted overlap data.
  simpa [SemiRepresentableFamily.Over.memberBaseChange, SemiRepresentableFamily.Over.pairwisePullback,
    SemiRepresentableFamily.Over.pr0, SemiRepresentableFamily.Over.pr1] using
    (Pseudofunctor.DescentData'.pullHom'_eq_hom
      ((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i))
      j₁ j₂)

/-- Helper for Lemma 8.3.7: on the overlap of `𝒱_i`, the two routes to `U_i` agree. This is the
middle-leg equality used to collapse the target transition to a self-comparison. -/
private theorem member_base_change_owner_middle_legs_eq
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index, HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    (i : 𝒰.index) (j₁ j₂ : 𝒱.index) :
    ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
        pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom =
      ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
        pullback.snd (𝒱.obj j₂).hom (𝒰.obj i).hom := by
  -- Both composites are the canonical overlap map to `U_i` for the restricted family `𝒱_i`.
  simpa [SemiRepresentableFamily.Over.memberBaseChange] using
    (𝒱.memberBaseChange 𝒰 i).pr0_map_eq_pr1_map j₁ j₂

/-- Helper for Lemma 8.3.7: the common middle leg from the overlap of `𝒱_i` to `U_i` lies over
the owner overlap map to `U`. -/
private theorem member_base_change_owner_middle_leg_map
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index, HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    (i : 𝒰.index) (j₁ j₂ : 𝒱.index) :
    (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
        pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫
        (𝒰.obj i).hom =
      ((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom := by
  -- The first overlap projection in the restricted family already maps to the chosen overlap
  -- object, and composing with `Uᵢ ⟶ U` preserves that owner-side equality.
  change
    ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
          ((𝒱.memberBaseChange 𝒰 i).obj j₁).hom) ≫
        (𝒰.obj i).hom =
      ((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
  -- This is just the restricted-family `pr0_map`, postcomposed with the fixed target map
  -- `Uᵢ ⟶ U`.
  exact congrArg
    (fun f ↦ f ≫ (𝒰.obj i).hom)
    ((𝒱.memberBaseChange 𝒰 i).pr0_map j₁ j₂)

/-- Helper for Lemma 8.3.7: the left owner-side leg from the overlap of `𝒱_i` to `U` factors
through the common middle map to `U_i`. -/
private theorem member_base_change_owner_left_leg_map
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index, HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    (φ : 𝒱 ⟶ 𝒰) (i : 𝒰.index) (j₁ j₂ : 𝒱.index) :
    ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
        pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫
        (φ.f j₁).left) ≫
        (𝒰.obj (φ.α j₁)).hom =
      ((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom := by
  -- First normalize the left owner-side route on `Uᵢ ×[U] V_{j₁}` to the middle map to `Uᵢ`,
  -- then collapse that middle map by the restricted-family overlap projection formula.
  calc
    ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
          pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫
          (φ.f j₁).left) ≫
          (𝒰.obj (φ.α j₁)).hom
        =
      (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
          pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫
          (𝒰.obj i).hom := by
            simpa [Category.assoc] using
              congrArg
                (fun f ↦ ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫ f)
                (member_base_change_comparison_component_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁)
    _ = ((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom :=
      member_base_change_owner_middle_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂

/-- Helper for Lemma 8.3.7: the right owner-side leg from the overlap of `𝒱_i` to `U` also
factors through the same middle map to `U_i`. -/
private theorem member_base_change_owner_right_leg_map
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index, HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    (φ : 𝒱 ⟶ 𝒰) (i : 𝒰.index) (j₁ j₂ : 𝒱.index) :
    ((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
        pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫
        (φ.f j₂).left) ≫
        (𝒰.obj (φ.α j₂)).hom =
      ((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom := by
  -- Normalize the right owner-side route on `Uᵢ ×[U] V_{j₂}` to the middle map to `Uᵢ`, switch
  -- to the left middle leg using the restricted overlap identity, and then collapse that leg.
  calc
    ((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
          pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫
          (φ.f j₂).left) ≫
          (𝒰.obj (φ.α j₂)).hom
        =
      (((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
          pullback.snd (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫
          (𝒰.obj i).hom := by
            simpa [Category.assoc] using
              congrArg
                (fun f ↦ ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫ f)
                (member_base_change_comparison_component_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₂)
    _ =
      (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
          pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫
          (𝒰.obj i).hom := by
            simpa [Category.assoc] using
              congrArg
                (fun f ↦ f ≫ (𝒰.obj i).hom)
                ((member_base_change_owner_middle_legs_eq (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂).symm)
    _ = ((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom :=
      member_base_change_owner_middle_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂

/-- Helper for Lemma 8.3.7: the right middle leg on the overlap of `𝒱_i` also maps to the common
owner overlap map to `U`. This is the right-hand variant needed when the ambient comparison is
postcomposed with the chosen cartesian arrow over the common middle map. -/
private theorem member_base_change_owner_right_middle_leg_map
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index, HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    (i : 𝒰.index) (j₁ j₂ : 𝒱.index) :
    (((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
        pullback.snd (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫
        (𝒰.obj i).hom =
      ((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom := by
  -- Swap the right middle leg to the left one by the overlap identity, then collapse with the
  -- existing left-middle owner map formula.
  calc
    (((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
          pullback.snd (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫
          (𝒰.obj i).hom
      =
        (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
          pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫
            (𝒰.obj i).hom := by
              simpa [Category.assoc] using
                congrArg (fun f ↦ f ≫ (𝒰.obj i).hom)
                  ((member_base_change_owner_middle_legs_eq (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂).symm)
    _ = ((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom :=
      member_base_change_owner_middle_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂

/-- Helper for Lemma 8.3.7: the normalized left and right owner-side comparison factors compose to
the direct owner-side comparison on the overlap by `D.comp_pullHom'`. -/
private theorem member_base_change_owner_comp_pullHom'
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index, HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (D : DescentDatum p hc 𝒰) (φ : 𝒱 ⟶ 𝒰) (i : 𝒰.index) (j₁ j₂ : 𝒱.index) :
    Functor.Fiber.fiberInclusion.map
        (Pseudofunctor.DescentData'.pullHom' D.hom
          (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
          ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
              pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫
            (φ.f j₁).left)
          (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
            pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
          (member_base_change_owner_left_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)
          (member_base_change_owner_middle_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)) ≫
      Functor.Fiber.fiberInclusion.map
        (Pseudofunctor.DescentData'.pullHom' D.hom
          (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
          (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
            pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
          ((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
              pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫
            (φ.f j₂).left)
          (member_base_change_owner_middle_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)
          (member_base_change_owner_right_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)) =
      Functor.Fiber.fiberInclusion.map
        (Pseudofunctor.DescentData'.pullHom' D.hom
          (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
          ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
              pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫
            (φ.f j₁).left)
          ((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
              pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫
            (φ.f j₂).left)
          (member_base_change_owner_left_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)
          (member_base_change_owner_right_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)) := by
  -- This is exactly the owner-side cocycle relation for the three normalized legs over the
  -- overlap object `((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p`.
  simpa [Functor.map_comp] using
    congrArg Functor.Fiber.fiberInclusion.map <|
      D.comp_pullHom'
        (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
        ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
            pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫
          (φ.f j₁).left)
        (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
          pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
        ((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
            pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫
          (φ.f j₂).left)
        (member_base_change_owner_left_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)
        (member_base_change_owner_middle_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)
        (member_base_change_owner_right_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)


/-- Helper for Lemma 8.3.7: the direct owner-side comparison followed by the right-to-middle
comparison is the left-to-middle comparison by `D.comp_pullHom'`. This is the orientation that
appears after the source overlap morphism is followed by the component comparison at `j₂`. -/
private theorem member_base_change_owner_comp_right_to_middle_pullHom'
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index, HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (D : DescentDatum p hc 𝒰) (φ : 𝒱 ⟶ 𝒰) (i : 𝒰.index) (j₁ j₂ : 𝒱.index) :
    Functor.Fiber.fiberInclusion.map
        (Pseudofunctor.DescentData'.pullHom' D.hom
          (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
          ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
              pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫
            (φ.f j₁).left)
          ((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
              pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫
            (φ.f j₂).left)
          (member_base_change_owner_left_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)
          (member_base_change_owner_right_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)) ≫
      Functor.Fiber.fiberInclusion.map
        (Pseudofunctor.DescentData'.pullHom' D.hom
          (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
          ((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
              pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫
            (φ.f j₂).left)
          (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
            pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
          (member_base_change_owner_right_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)
          (member_base_change_owner_middle_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)) =
      Functor.Fiber.fiberInclusion.map
        (Pseudofunctor.DescentData'.pullHom' D.hom
          (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
          ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
              pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫
            (φ.f j₁).left)
          (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
            pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
          (member_base_change_owner_left_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)
          (member_base_change_owner_middle_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)) := by
  -- This is `D.comp_pullHom'` for the three legs left, right, middle on the same owner overlap.
  simpa [Functor.map_comp] using
    congrArg Functor.Fiber.fiberInclusion.map <|
      D.comp_pullHom'
        (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
        ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
            pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫
          (φ.f j₁).left)
        ((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
            pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫
          (φ.f j₂).left)
        (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
          pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
        (member_base_change_owner_left_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)
        (member_base_change_owner_right_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)
        (member_base_change_owner_middle_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)

/-- Helper for Lemma 8.3.7: the owner-side cocycle comparison remains valid after any fixed
ambient postcomposition from the common right-leg codomain. -/
private theorem member_base_change_owner_comp_pullHom'_postcompose
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index, HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (D : DescentDatum p hc 𝒰) (φ : 𝒱 ⟶ 𝒰) (i : 𝒰.index) (j₁ j₂ : 𝒱.index)
    {Z : S}
    (m :
      (hc.obj
          ((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
                pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫
              (φ.f j₂).left)
          (D.obj (φ.α j₂))).1 ⟶ Z) :
    (Functor.Fiber.fiberInclusion.map
        (Pseudofunctor.DescentData'.pullHom' D.hom
          (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
          ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
              pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫
            (φ.f j₁).left)
          (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
            pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
          (member_base_change_owner_left_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)
          (member_base_change_owner_middle_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)) ≫
      Functor.Fiber.fiberInclusion.map
        (Pseudofunctor.DescentData'.pullHom' D.hom
          (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
          (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
            pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
          ((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
              pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫
            (φ.f j₂).left)
          (member_base_change_owner_middle_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)
          (member_base_change_owner_right_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)) ≫
      m) =
    Functor.Fiber.fiberInclusion.map
      (Pseudofunctor.DescentData'.pullHom' D.hom
        (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
        ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
            pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫
          (φ.f j₁).left)
        ((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
            pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫
          (φ.f j₂).left)
        (member_base_change_owner_left_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)
        (member_base_change_owner_right_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)) ≫
      m := by
  -- This is the owner-side cocycle equality with a fixed ambient postcomposition appended.
  rw [← Category.assoc]
  exact congrArg (fun k ↦ k ≫ m)
    (member_base_change_owner_comp_pullHom' (p := p) (hc := hc) D φ i j₁ j₂)

/-- Helper for Lemma 8.3.7: after normalizing to the common middle leg on the overlap of `𝒱_i`,
the remaining owner-side self-comparison is the identity by `D.pullHom'_self`. -/
private theorem member_base_change_owner_self_pullHom'_eq_refl
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index, HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (D : DescentDatum p hc 𝒰) (i : 𝒰.index) (j₁ j₂ : 𝒱.index) :
    Functor.Fiber.fiberInclusion.map
        (Pseudofunctor.DescentData'.pullHom' D.hom
          (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
          (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
            pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
          (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
            pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
          (member_base_change_owner_middle_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)
          (member_base_change_owner_middle_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)) =
      Functor.Fiber.fiberInclusion.map (𝟙 _) := by
  -- Once both legs are the same middle projection, this is the primed self-comparison identity.
  simpa using
    congrArg Functor.Fiber.fiberInclusion.map <|
      D.pullHom'_self
        (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
        (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
          pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)

/-- Helper for Lemma 8.3.7: after fixing the common middle-leg cartesian arrow to `D.obj i`, the
owner-side self-comparison on that middle leg collapses to the chosen cartesian arrow itself. This
is the exact postcomposed boundary left after the owner-side overlap shell is flattened. -/
private theorem member_base_change_comparison_owner_postcompose_middle_leg_normalize
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index, HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (D : DescentDatum p hc 𝒰) (i : 𝒰.index) (j₁ j₂ : 𝒱.index) :
    Functor.Fiber.fiberInclusion.map
        (Pseudofunctor.DescentData'.pullHom' D.hom
          (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
          (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
            pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
          (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
            pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
          (member_base_change_owner_middle_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)
          (member_base_change_owner_middle_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)) ≫
      hc.map
        (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
          pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
        (D.obj i) =
    hc.map
      (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
        pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
      (D.obj i) := by
  -- First rewrite the middle-leg self-comparison to the identity in the ambient category.
  have hpost :
      Functor.Fiber.fiberInclusion.map
          (Pseudofunctor.DescentData'.pullHom' D.hom
            (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
            (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
              pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
            (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
              pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
            (member_base_change_owner_middle_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)
            (member_base_change_owner_middle_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)) ≫
        hc.map
          (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
            pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
          (D.obj i)
        =
      Functor.Fiber.fiberInclusion.map (𝟙 _) ≫
        hc.map
          (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
            pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
          (D.obj i) := by
    exact congrArg
      (fun k ↦
        k ≫
          hc.map
            (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
              pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
            (D.obj i))
      (member_base_change_owner_self_pullHom'_eq_refl
        (p := p) (hc := hc) D i j₁ j₂)
  simpa using hpost

/-- Helper for Lemma 8.3.7: once both sides of the overlap comparison are postcomposed with the
chosen cartesian arrow out of their common codomain over the right overlap projection, the
remaining ambient-category calculation is the owner-side cocycle normalization for `D.hom`. -/
private theorem member_base_change_comparison_owner_postcompose
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index, HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (D : DescentDatum p hc 𝒰) (φ : 𝒱 ⟶ 𝒰) (i : 𝒰.index) (j₁ j₂ : 𝒱.index) :
    Functor.Fiber.fiberInclusion.map
        ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map
            ((member_base_change_comparison_component_iso hc D φ i j₁).hom) ≫
          ((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).hom j₁ j₂) ≫
      hc.map ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
        (((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).obj j₂) =
    Functor.Fiber.fiberInclusion.map
        ((pullbackFamilyDescentDatum hc (𝒰 := 𝒱.memberBaseChange 𝒰 i) (𝒱 := 𝒱) (𝒰.obj i).hom
            (member_base_change_refinement_adapter 𝒰 𝒱 i)
            ((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D)).hom
            j₁ j₂ ≫
          (hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)).map
            ((member_base_change_comparison_component_iso hc D φ i j₂).hom)) ≫
        hc.map ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
          (((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).obj j₂) := by
  let q := (𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂
  let r := pullback.snd (𝒱.obj j₂).hom (𝒰.obj i).hom
  let χ := hc.map r (D.obj i)
  let ψ :=
    Functor.Fiber.fiberInclusion.map
        ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map
            ((member_base_change_comparison_component_iso hc D φ i j₁).hom) ≫
          ((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).hom j₁ j₂) ≫
      hc.map ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
        (((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).obj j₂)
  let ψ' :=
    Functor.Fiber.fiberInclusion.map
        ((pullbackFamilyDescentDatum hc (𝒰 := 𝒱.memberBaseChange 𝒰 i) (𝒱 := 𝒱) (𝒰.obj i).hom
            (member_base_change_refinement_adapter 𝒰 𝒱 i)
            ((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D)).hom
            j₁ j₂ ≫
          (hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)).map
            ((member_base_change_comparison_component_iso hc D φ i j₂).hom)) ≫
        hc.map ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
          (((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).obj j₂)
  letI : p.IsHomLift q ψ := by
    let η :=
      ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map
          ((member_base_change_comparison_component_iso hc D φ i j₁).hom) ≫
        ((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).hom j₁ j₂)
    change p.IsHomLift ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
      (Functor.Fiber.fiberInclusion.map η ≫
        hc.map ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
          (((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).obj j₂))
    have hη : p.IsHomLift (𝟙 ((𝒱.memberBaseChange 𝒰 i).overlap j₁ j₂))
        (Functor.Fiber.fiberInclusion.map η) := η.2
    have hq : p.IsHomLift ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
        (hc.map ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
          (((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).obj j₂)) := by
      letI : p.IsStronglyCartesian ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
          (hc.map ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
            (((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).obj j₂)) :=
        hc.isStronglyCartesian ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
          (((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).obj j₂)
      infer_instance
    simpa using
      (@IsHomLift.comp _ _ _ _ p _ _ _ _ _ _
        (𝟙 ((𝒱.memberBaseChange 𝒰 i).overlap j₁ j₂))
        ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
        (Functor.Fiber.fiberInclusion.map η)
        (hc.map ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
          (((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).obj j₂))
        hη hq)
  letI : p.IsHomLift q ψ' := by
    let η :=
      ((pullbackFamilyDescentDatum hc (𝒰 := 𝒱.memberBaseChange 𝒰 i) (𝒱 := 𝒱)
          (𝒰.obj i).hom (member_base_change_refinement_adapter 𝒰 𝒱 i)
          ((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D)).hom
          j₁ j₂ ≫
        (hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)).map
          ((member_base_change_comparison_component_iso hc D φ i j₂).hom))
    change p.IsHomLift ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
      (Functor.Fiber.fiberInclusion.map η ≫
        hc.map ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
          (((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).obj j₂))
    have hη : p.IsHomLift (𝟙 ((𝒱.memberBaseChange 𝒰 i).overlap j₁ j₂))
        (Functor.Fiber.fiberInclusion.map η) := η.2
    have hq : p.IsHomLift ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
        (hc.map ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
          (((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).obj j₂)) := by
      letI : p.IsStronglyCartesian ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
          (hc.map ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
            (((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).obj j₂)) :=
        hc.isStronglyCartesian ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
          (((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).obj j₂)
      infer_instance
    simpa using
      (@IsHomLift.comp _ _ _ _ p _ _ _ _ _ _
        (𝟙 ((𝒱.memberBaseChange 𝒰 i).overlap j₁ j₂))
        ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
        (Functor.Fiber.fiberInclusion.map η)
        (hc.map ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
          (((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).obj j₂))
        hη hq)
  change ψ = ψ'
  have hψ : p.IsHomLift q ψ := inferInstance
  have hψ' : p.IsHomLift q ψ' := inferInstance
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ p _ _ _ _ r χ inferInstance _ _ q ψ ψ' hψ hψ'
      (by
        change ψ ≫ χ = ψ' ≫ χ
        simp only [ψ, ψ', χ, q, r]
        simp only [Functor.map_comp, Category.assoc]
        rw [member_base_change_source_transition_inner_normalize (p := p) (hc := hc) D φ i j₁ j₂]
        have htarget_post :
            Functor.Fiber.fiberInclusion.map
                (((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).hom j₁ j₂) ≫
              hc.map ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
                (((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).obj j₂) ≫
              hc.map (pullback.snd (𝒱.obj j₂).hom (𝒰.obj i).hom) (D.obj i) =
            hc.map ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
                (((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).obj j₁) ≫
              hc.map (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom) (D.obj i) := by
          simpa [SemiRepresentableFamily.Over.memberBaseChange] using
            familyDescentFunctor_obj_hom_postcompose (p := p) (hc := hc)
              (𝒰 := 𝒱.memberBaseChange 𝒰 i) (D.obj i) j₁ j₂
        simp only [Category.assoc]
        have htarget_prefixed :
            Functor.Fiber.fiberInclusion.map
                ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map
                  (member_base_change_comparison_component_iso hc D φ i j₁).hom) ≫
              Functor.Fiber.fiberInclusion.map
                  (((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).hom j₁ j₂) ≫
                hc.map ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
                    (((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).obj j₂) ≫
                  hc.map (pullback.snd (𝒱.obj j₂).hom (𝒰.obj i).hom) (D.obj i) =
            Functor.Fiber.fiberInclusion.map
                ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map
                  (member_base_change_comparison_component_iso hc D φ i j₁).hom) ≫
              hc.map ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
                  (((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).obj j₁) ≫
                hc.map (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom) (D.obj i) := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦
                Functor.Fiber.fiberInclusion.map
                    ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map
                      (member_base_change_comparison_component_iso hc D φ i j₁).hom) ≫ k)
              htarget_post
        rw [htarget_prefixed]
        let sourcePrefix :=
          Functor.Fiber.fiberInclusion.map
            ((hc.pullbackCompComponentIso
                (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
                ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
                (((identity_refinement_adapter φ).f j₁).left ^*[hc]
                  D.obj ((identity_refinement_adapter φ).α j₁))).inv ≫
              (hc.pullbackCompComponentIso
                ((identity_refinement_adapter φ).f j₁).left
                (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                  pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
                (D.obj ((identity_refinement_adapter φ).α j₁))).inv)
        have hleft_norm :
            Functor.Fiber.fiberInclusion.map
                ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map
                  ((member_base_change_comparison_component_iso hc D φ i j₁).hom)) ≫
              hc.map ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
                (((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).obj j₁) ≫
                hc.map (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom) (D.obj i) =
              sourcePrefix ≫
                Functor.Fiber.fiberInclusion.map
                  (Pseudofunctor.DescentData'.pullHom' D.hom
                    (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
                    ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                        pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫
                      (φ.f j₁).left)
                    (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                      pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
                    (member_base_change_owner_left_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)
                    (member_base_change_owner_middle_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)) ≫
                  hc.map (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                    pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom) (D.obj i) := by
          change
            Functor.Fiber.fiberInclusion.map
                ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map
                  ((member_base_change_comparison_component_iso hc D φ i j₁).hom)) ≫
              hc.map ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
                (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom ^*[hc] D.obj i) ≫
                hc.map (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom) (D.obj i) =
              sourcePrefix ≫
                Functor.Fiber.fiberInclusion.map
                  (Pseudofunctor.DescentData'.pullHom' D.hom
                    (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
                    ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                        pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫
                      (φ.f j₁).left)
                    (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                      pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
                    (member_base_change_owner_left_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)
                    (member_base_change_owner_middle_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)) ≫
                  hc.map (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                    pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom) (D.obj i)
          rw [member_base_change_comparison_component_iso_hom_to_owner_pullHom'
            (p := p) (hc := hc) D φ i j₁]
          let θ :=
            Pseudofunctor.DescentData'.pullHom' D.hom
              ((pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫ (φ.f j₁).left ≫ (𝒰.obj (φ.α j₁)).hom)
              ((pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫ (φ.f j₁).left)
              (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
              (by simp)
              (by
                simpa [Category.assoc] using
                  (member_base_change_comparison_component_map
                    (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁).symm)
          have htheta :=
            (fiberPseudofunctor_map_postcompose_eq_pullHom (hc := hc)
              ((pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫ (φ.f j₁).left)
              (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
              ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
              ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)) ≫ (φ.f j₁).left)
              (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom))
              (by simp [Category.assoc]) (by rfl) θ)
          have hprefix :
              Functor.Fiber.fiberInclusion.map
                  ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map
                    ((hc.pullbackCompComponentIso (φ.f j₁).left (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
                      (D.obj (φ.α j₁))).inv)) ≫
                Functor.Fiber.fiberInclusion.map
                  ((hc.fiberPseudofunctor.mapComp'
                    ((pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫ (φ.f j₁).left).op.toLoc
                    ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂).op.toLoc
                    (((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫ (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)) ≫ (φ.f j₁).left).op.toLoc)
                    (comp_toLoc_eq_local ((pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫ (φ.f j₁).left)
                      ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
                      (gf := ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫ (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)) ≫ (φ.f j₁).left))
                      (by simp [Category.assoc]))).inv.toNatTrans.app (D.obj (φ.α j₁))) =
              sourcePrefix := by
            simpa [sourcePrefix, Functor.map_comp, Category.assoc] using
              congrArg Functor.Fiber.fiberInclusion.map
                (pullbackCompComponentIso_inv_assoc_flexible (hc := hc)
                  (φ.f j₁).left (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) (D.obj (φ.α j₁)))
          let B := (hc.pullbackCompComponentIso (φ.f j₁).left
            (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
            (D.obj (φ.α j₁))).inv
          let F := (hc.fiberPseudofunctor.map
            ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂).op.toLoc).toFunctor
          have hmapG :
              Functor.Fiber.fiberInclusion.map
                  ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map (B ≫ θ)) =
                Functor.Fiber.fiberInclusion.map
                    ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map B) ≫
                  Functor.Fiber.fiberInclusion.map
                    ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map θ) := by
            calc
              Functor.Fiber.fiberInclusion.map
                  ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map (B ≫ θ)) =
                Functor.Fiber.fiberInclusion.map
                  (((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map B) ≫
                    ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map θ)) := by
                  exact congrArg Functor.Fiber.fiberInclusion.map
                    ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map_comp B θ)
              _ = Functor.Fiber.fiberInclusion.map
                    ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map B) ≫
                  Functor.Fiber.fiberInclusion.map
                    ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map θ) := by
                  simpa using
                    (Functor.Fiber.fiberInclusion.map_comp
                      ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map B)
                      ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map θ))
          have hthetaG :
              Functor.Fiber.fiberInclusion.map
                  ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map θ) ≫
                hc.map ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
                  ((pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom) ^*[hc] D.obj i) ≫
                hc.map (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom) (D.obj i) =
              Functor.Fiber.fiberInclusion.map
                  ((hc.fiberPseudofunctor.mapComp'
                    ((pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫ (φ.f j₁).left).op.toLoc
                    ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂).op.toLoc
                    (((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫ (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)) ≫ (φ.f j₁).left).op.toLoc)
                    (comp_toLoc_eq_local ((pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫ (φ.f j₁).left)
                      ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
                      (gf := ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫ (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)) ≫ (φ.f j₁).left))
                      (by simp [Category.assoc]))).inv.toNatTrans.app (D.obj (φ.α j₁))) ≫
                Functor.Fiber.fiberInclusion.map
                  (Pseudofunctor.LocallyDiscreteOpToCat.pullHom θ
                    ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
                    ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                      (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)) ≫ (φ.f j₁).left)
                    (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                      (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom))
                    (by simp [Category.assoc]) (by rfl)) ≫
                hc.map (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                  (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)) (D.obj i) := by
            rw [pullbackFunctor_map_eq_fiberPseudofunctor_map]
            change Functor.Fiber.fiberInclusion.map (F.map θ) ≫
                hc.map ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
                  ((pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom) ^*[hc] D.obj i) ≫
                hc.map (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom) (D.obj i) =
              Functor.Fiber.fiberInclusion.map
                  ((hc.fiberPseudofunctor.mapComp'
                    ((pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫ (φ.f j₁).left).op.toLoc
                    ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂).op.toLoc
                    (((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫ (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)) ≫ (φ.f j₁).left).op.toLoc)
                    (comp_toLoc_eq_local ((pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫ (φ.f j₁).left)
                      ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
                      (gf := ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫ (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)) ≫ (φ.f j₁).left))
                      (by simp [Category.assoc]))).inv.toNatTrans.app (D.obj (φ.α j₁))) ≫
                Functor.Fiber.fiberInclusion.map
                  (Pseudofunctor.LocallyDiscreteOpToCat.pullHom θ
                    ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
                    ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                      (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)) ≫ (φ.f j₁).left)
                    (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                      (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom))
                    (by simp [Category.assoc]) (by rfl)) ≫
                hc.map (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                  (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)) (D.obj i)
            simpa [F, Category.assoc] using htheta
          calc
            Functor.Fiber.fiberInclusion.map
                ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map (B ≫ θ)) ≫
              hc.map ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ((pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom) ^*[hc] D.obj i) ≫
              hc.map (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom) (D.obj i) =
                (Functor.Fiber.fiberInclusion.map
                    ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map B) ≫
                  Functor.Fiber.fiberInclusion.map
                    ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map θ)) ≫
                    (hc.map ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ((pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom) ^*[hc] D.obj i) ≫
                      hc.map (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom) (D.obj i)) := by
                    change Functor.Fiber.fiberInclusion.map
                        ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map (B ≫ θ)) ≫
                        (hc.map ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
                          ((pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom) ^*[hc] D.obj i) ≫
                          hc.map (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom) (D.obj i)) =
                      (Functor.Fiber.fiberInclusion.map
                          ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map B) ≫
                        Functor.Fiber.fiberInclusion.map
                          ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map θ)) ≫
                        (hc.map ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
                          ((pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom) ^*[hc] D.obj i) ≫
                          hc.map (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom) (D.obj i))
                    exact congrArg
                      (fun k ↦ k ≫
                        (hc.map ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
                          ((pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom) ^*[hc] D.obj i) ≫
                          hc.map (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom) (D.obj i)))
                      hmapG
            _ = Functor.Fiber.fiberInclusion.map
                    ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map B) ≫
                  (Functor.Fiber.fiberInclusion.map
                      ((hc.fiberPseudofunctor.mapComp'
                        ((pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫ (φ.f j₁).left).op.toLoc
                        ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂).op.toLoc
                        (((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫ (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)) ≫ (φ.f j₁).left).op.toLoc)
                        (comp_toLoc_eq_local ((pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫ (φ.f j₁).left)
                          ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
                          (gf := ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫ (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)) ≫ (φ.f j₁).left))
                          (by simp [Category.assoc]))).inv.toNatTrans.app (D.obj (φ.α j₁))) ≫
                    Functor.Fiber.fiberInclusion.map
                      (Pseudofunctor.LocallyDiscreteOpToCat.pullHom θ
                        ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
                        ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                          (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)) ≫ (φ.f j₁).left)
                        (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                          (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom))
                        (by simp [Category.assoc]) (by rfl)) ≫
                    hc.map (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫ (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)) (D.obj i)) := by
                    simpa [Category.assoc] using
                      congrArg
                        (fun k ↦ Functor.Fiber.fiberInclusion.map
                          ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map B) ≫ k)
                        hthetaG
            _ = sourcePrefix ≫
                  Functor.Fiber.fiberInclusion.map
                    (Pseudofunctor.LocallyDiscreteOpToCat.pullHom θ
                      ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
                      ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                        (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)) ≫ (φ.f j₁).left)
                      (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                        (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom))
                      (by simp [Category.assoc]) (by rfl)) ≫
                    hc.map (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                      (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)) (D.obj i) := by
                    simpa [B, Category.assoc] using
                      congrArg
                        (fun k ↦ k ≫
                          Functor.Fiber.fiberInclusion.map
                            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom θ
                              ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
                              ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                                (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)) ≫ (φ.f j₁).left)
                              (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                                (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom))
                              (by simp [Category.assoc]) (by rfl)) ≫
                          hc.map (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                            (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)) (D.obj i))
                        hprefix
            _ = sourcePrefix ≫
                  Functor.Fiber.fiberInclusion.map
                    (Pseudofunctor.DescentData'.pullHom' D.hom
                      (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
                      (((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫ (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)) ≫ (φ.f j₁).left))
                      (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫ (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom))
                      (member_base_change_owner_left_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)
                      (member_base_change_owner_middle_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)) ≫
                    hc.map (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫ (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)) (D.obj i) := by
                    have hpull :
                        Pseudofunctor.LocallyDiscreteOpToCat.pullHom θ
                          ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
                          ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                            (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)) ≫ (φ.f j₁).left)
                          (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                            (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom))
                          (by simp [Category.assoc]) (by rfl) =
                        Pseudofunctor.DescentData'.pullHom' D.hom
                          (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
                          ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                              (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)) ≫
                            (φ.f j₁).left)
                          (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                            (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
                          )
                          (member_base_change_owner_left_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)
                          (member_base_change_owner_middle_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂) := by
                      simpa [θ, Category.assoc] using
                        (Pseudofunctor.DescentData'.pullHom_pullHom'
                          (F := hc.fiberPseudofunctor) D.hom
                          ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
                          (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom ≫
                            (φ.f j₁).left ≫ (𝒰.obj (φ.α j₁)).hom)
                          (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
                          (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom ≫ (φ.f j₁).left)
                          (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
                          ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                              (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)) ≫
                            (φ.f j₁).left)
                          (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                            (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom))
                          (by
                            simpa only [Category.assoc] using
                              member_base_change_owner_left_leg_map
                                (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)
                          (by simp [Category.assoc])
                          (by
                            simpa [Category.assoc] using
                              (member_base_change_comparison_component_map
                                (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁).symm)
                          (by simp [Category.assoc])
                          (by rfl))
                    simpa [Category.assoc] using
                      congrArg
                        (fun k ↦ sourcePrefix ≫ Functor.Fiber.fiberInclusion.map k ≫
                          hc.map (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                            (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)) (D.obj i))
                        hpull
        rw [hleft_norm]
        simp only [Category.assoc,
          member_base_change_comparison_component_iso_hom_to_owner_pullHom',
          pullbackFunctor_map_eq_fiberPseudofunctor_map]
        let F₂ := (hc.fiberPseudofunctor.map
          ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂).op.toLoc).toFunctor
        let B₂ := (hc.pullbackCompComponentIso (φ.f j₂).left
          (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
          (D.obj (φ.α j₂))).inv
        let θ₂ :=
          Pseudofunctor.DescentData'.pullHom' D.hom
            (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom ≫
              (φ.f j₂).left ≫ (𝒰.obj (φ.α j₂)).hom)
            (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom ≫ (φ.f j₂).left)
            (pullback.snd (𝒱.obj j₂).hom (𝒰.obj i).hom)
            (by simp)
            (by
              simpa [Category.assoc] using
                (member_base_change_comparison_component_map
                  (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₂).symm)
        have hsplit_right :
            Functor.Fiber.fiberInclusion.map (F₂.map (B₂ ≫ θ₂)) =
              Functor.Fiber.fiberInclusion.map (F₂.map B₂) ≫
                Functor.Fiber.fiberInclusion.map (F₂.map θ₂) := by
          calc
            Functor.Fiber.fiberInclusion.map (F₂.map (B₂ ≫ θ₂)) =
                Functor.Fiber.fiberInclusion.map (F₂.map B₂ ≫ F₂.map θ₂) := by
              exact congrArg Functor.Fiber.fiberInclusion.map (F₂.map_comp B₂ θ₂)
            _ = Functor.Fiber.fiberInclusion.map (F₂.map B₂) ≫
                  Functor.Fiber.fiberInclusion.map (F₂.map θ₂) := by
              simpa using (Functor.Fiber.fiberInclusion.map_comp (F₂.map B₂) (F₂.map θ₂))
        dsimp [F₂, B₂, θ₂] at hsplit_right
        erw [hsplit_right]
        have htheta₂G :
            Functor.Fiber.fiberInclusion.map
                ((hc.fiberPseudofunctor.map ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂).op.toLoc).toFunctor.map
                  (Pseudofunctor.DescentData'.pullHom' D.hom
                    (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom ≫ (φ.f j₂).left ≫
                      (𝒰.obj (φ.α j₂)).hom)
                    (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom ≫ (φ.f j₂).left)
                    (pullback.snd (𝒱.obj j₂).hom (𝒰.obj i).hom)
                    (by simp)
                    (by
                      simpa [Category.assoc] using
                        (member_base_change_comparison_component_map
                          (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₂).symm))) ≫
              hc.map ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
                (((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).obj j₂) ≫
              hc.map (pullback.snd (𝒱.obj j₂).hom (𝒰.obj i).hom) (D.obj i) =
            Functor.Fiber.fiberInclusion.map
                ((hc.fiberPseudofunctor.mapComp'
                  ((pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫ (φ.f j₂).left).op.toLoc
                  ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂).op.toLoc
                  (((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫ (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)) ≫ (φ.f j₂).left).op.toLoc)
                  (comp_toLoc_eq_local ((pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫ (φ.f j₂).left)
                    ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
                    (gf := ((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫ (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)) ≫ (φ.f j₂).left))
                    (by simp [Category.assoc]))).inv.toNatTrans.app (D.obj (φ.α j₂))) ≫
              Functor.Fiber.fiberInclusion.map
                (Pseudofunctor.LocallyDiscreteOpToCat.pullHom θ₂
                  ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
                  ((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
                    (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)) ≫ (φ.f j₂).left)
                  (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                    (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom))
                  (by simp [Category.assoc])
                  (by
                    simpa [Category.assoc] using
                      (member_base_change_owner_middle_legs_eq
                        (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂).symm)) ≫
              hc.map (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)) (D.obj i) := by
          change Functor.Fiber.fiberInclusion.map (F₂.map θ₂) ≫
              hc.map ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
                ((pullback.snd (𝒱.obj j₂).hom (𝒰.obj i).hom) ^*[hc] D.obj i) ≫
              hc.map (pullback.snd (𝒱.obj j₂).hom (𝒰.obj i).hom) (D.obj i) =
            Functor.Fiber.fiberInclusion.map
                ((hc.fiberPseudofunctor.mapComp'
                  ((pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫ (φ.f j₂).left).op.toLoc
                  ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂).op.toLoc
                  (((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫ (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)) ≫ (φ.f j₂).left).op.toLoc)
                  (comp_toLoc_eq_local ((pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫ (φ.f j₂).left)
                    ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
                    (gf := ((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫ (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)) ≫ (φ.f j₂).left))
                    (by simp [Category.assoc]))).inv.toNatTrans.app (D.obj (φ.α j₂))) ≫
              Functor.Fiber.fiberInclusion.map
                (Pseudofunctor.LocallyDiscreteOpToCat.pullHom θ₂
                  ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
                  ((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
                    (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)) ≫ (φ.f j₂).left)
                  (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                    (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom))
                  (by simp [Category.assoc])
                  (by
                    simpa [Category.assoc] using
                      (member_base_change_owner_middle_legs_eq
                        (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂).symm)) ≫
              hc.map (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)) (D.obj i)
          simpa [F₂, θ₂, Category.assoc] using
            (fiberPseudofunctor_map_postcompose_eq_pullHom (hc := hc)
              ((pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫ (φ.f j₂).left)
              (pullback.snd (𝒱.obj j₂).hom (𝒰.obj i).hom)
              ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
              ((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
                (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)) ≫ (φ.f j₂).left)
              (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom))
              (by simp [Category.assoc])
              (by
                simpa [Category.assoc] using
                  (member_base_change_owner_middle_legs_eq
                    (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂).symm)
              θ₂)
        have htheta₂G_prefixed :=
          congrArg
            (fun k ↦
              Functor.Fiber.fiberInclusion.map
                ((hc.fiberPseudofunctor.map
                  ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂).op.toLoc).toFunctor.map
                  (hc.pullbackCompComponentIso (φ.f j₂).left
                    (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
                    (D.obj (φ.α j₂))).inv) ≫ k)
            htheta₂G
        simp only at htheta₂G_prefixed
        have hmbc : HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i) :=
          (inferInstance : ∀ i, HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)) i
        letI : HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i) := hmbc
        letI : HasPullback
            (Over.mk (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)).hom
            (Over.mk (pullback.snd (𝒱.obj j₂).hom (𝒰.obj i).hom)).hom := by
          change HasPullback ((𝒱.memberBaseChange 𝒰 i).obj j₁).hom
            ((𝒱.memberBaseChange 𝒰 i).obj j₂).hom
          exact hmbc.pairwise j₁ j₂
        have htheta₂G_prefixed₂ :=
          congrArg
            (fun k ↦
              Functor.Fiber.fiberInclusion.map
                (((pullbackFamilyDescentDatum hc (𝒰 := 𝒱.memberBaseChange 𝒰 i) (𝒱 := 𝒱)
                  (𝒰.obj i).hom (member_base_change_refinement_adapter 𝒰 𝒱 i)
                  ((pullbackFamilyDescentFunctor hc (𝟙 U)
                    (identity_refinement_adapter φ)).obj D)).hom j₁ j₂)) ≫ k)
            htheta₂G_prefixed
        have hsource_outer_map :=
          congrArg Functor.Fiber.fiberInclusion.map
            (member_base_change_source_transition_outer_normalize
              (p := p) (hc := hc) D φ i j₁ j₂)
        have hsource_outer_map_raw :
            Functor.Fiber.fiberInclusion.map
                ((pullbackFamilyDescentDatum hc (𝒰 := 𝒱.memberBaseChange 𝒰 i) (𝒱 := 𝒱)
                  (𝒰.obj i).hom (member_base_change_refinement_adapter 𝒰 𝒱 i)
                  ((pullbackFamilyDescentFunctor hc (𝟙 U)
                    (identity_refinement_adapter φ)).obj D)).hom j₁ j₂) =
              Functor.Fiber.fiberInclusion.map
                ((hc.pullbackCompComponentIso
                    (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
                    ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
                    (((pullbackFamilyDescentFunctor hc (𝟙 U)
                      (identity_refinement_adapter φ)).obj D).obj j₁)).inv ≫
                  (Pseudofunctor.DescentData'.descentData
                    ((pullbackFamilyDescentFunctor hc (𝟙 U)
                      (identity_refinement_adapter φ)).obj D)).hom
                    (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫
                      (𝒰.obj i).hom)
                    (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                      pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
                    (((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
                      pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
                    (by
                      simpa [Category.assoc] using
                        member_base_change_source_left_raw_leg_map
                          (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)
                    (by
                      simpa [Category.assoc] using
                        member_base_change_source_right_raw_leg_map
                          (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂) ≫
                  (hc.pullbackCompComponentIso
                    (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
                    ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
                    (((pullbackFamilyDescentFunctor hc (𝟙 U)
                      (identity_refinement_adapter φ)).obj D).obj j₂)).hom) := by
          simpa [pullbackFamilyDescentFunctor, SemiRepresentableFamily.Over.memberBaseChange] using
            hsource_outer_map
        erw [hsource_outer_map_raw] at htheta₂G_prefixed₂
        dsimp only at htheta₂G_prefixed₂
        let sourceOuterPacked :=
          Functor.Fiber.fiberInclusion.map
            ((hc.pullbackCompComponentIso
                (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
                ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
                (((pullbackFamilyDescentFunctor hc (𝟙 U)
                  (identity_refinement_adapter φ)).obj D).obj j₁)).inv ≫
              (Pseudofunctor.DescentData'.descentData
                ((pullbackFamilyDescentFunctor hc (𝟙 U)
                  (identity_refinement_adapter φ)).obj D)).hom
                (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫
                  (𝒰.obj i).hom)
                (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                  pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
                (((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
                  pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
                (by
                  simpa [Category.assoc] using
                    member_base_change_source_left_raw_leg_map
                      (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)
                (by
                  simpa [Category.assoc] using
                    member_base_change_source_right_raw_leg_map
                      (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂) ≫
              (hc.pullbackCompComponentIso
                (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
                ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
                (((pullbackFamilyDescentFunctor hc (𝟙 U)
                  (identity_refinement_adapter φ)).obj D).obj j₂)).hom)
        let sourceOuter :=
          Functor.Fiber.fiberInclusion.map
              (hc.pullbackCompComponentIso
                (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
                ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
                (((pullbackFamilyDescentFunctor hc (𝟙 U)
                  (identity_refinement_adapter φ)).obj D).obj j₁)).inv ≫
            Functor.Fiber.fiberInclusion.map
              ((Pseudofunctor.DescentData'.descentData
                ((pullbackFamilyDescentFunctor hc (𝟙 U)
                  (identity_refinement_adapter φ)).obj D)).hom
                (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫
                  (𝒰.obj i).hom)
                (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                  pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
                (((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
                  pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
                (by
                  simpa [Category.assoc] using
                    member_base_change_source_left_raw_leg_map
                      (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)
                (by
                  simpa [Category.assoc] using
                    member_base_change_source_right_raw_leg_map
                      (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)) ≫
            Functor.Fiber.fiberInclusion.map
              (hc.pullbackCompComponentIso
                (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
                ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
                (((pullbackFamilyDescentFunctor hc (𝟙 U)
                  (identity_refinement_adapter φ)).obj D).obj j₂)).hom
        let sourceMiddle :=
          (Pseudofunctor.DescentData'.descentData
            ((pullbackFamilyDescentFunctor hc (𝟙 U)
              (identity_refinement_adapter φ)).obj D)).hom
            (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫
              (𝒰.obj i).hom)
            (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
              pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
            (((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
              pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
            (by
              simpa [Category.assoc] using
                member_base_change_source_left_raw_leg_map
                  (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)
            (by
              simpa [Category.assoc] using
                member_base_change_source_right_raw_leg_map
                  (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂)
        let rightPrefix :=
          Functor.Fiber.fiberInclusion.map
            ((hc.fiberPseudofunctor.map
              ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂).op.toLoc).toFunctor.map B₂)
        let rightThetaTerm :=
          Functor.Fiber.fiberInclusion.map
            ((hc.fiberPseudofunctor.map
              ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂).op.toLoc).toFunctor.map θ₂)
        let rightPost :=
          hc.map ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
              (((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).obj j₂) ≫
            hc.map (pullback.snd (𝒱.obj j₂).hom (𝒰.obj i).hom) (D.obj i)
        let rightComp :=
          Functor.Fiber.fiberInclusion.map
            ((hc.fiberPseudofunctor.mapComp'
              ((pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫ (φ.f j₂).left).op.toLoc
              ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂).op.toLoc
              (((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
                pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫ (φ.f j₂).left).op.toLoc)
              (comp_toLoc_eq_local ((pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫
                (φ.f j₂).left)
                ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
                (gf := ((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
                  pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫ (φ.f j₂).left))
                (by simp [Category.assoc]))).inv.toNatTrans.app (D.obj (φ.α j₂)))
        let rightPull :=
          Functor.Fiber.fiberInclusion.map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom θ₂
              ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
              ((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
                pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫ (φ.f j₂).left)
              (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
              (by simp [Category.assoc])
              (by
                simpa [Category.assoc] using
                  (member_base_change_owner_middle_legs_eq
                    (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂).symm))
        let rightOwnerPost :=
          hc.map (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
            pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom) (D.obj i)
        let targetAfterTheta :=
          sourceOuter ≫ rightPrefix ≫ rightComp ≫ rightPull ≫ rightOwnerPost
        have hsourceOuter_fold : sourceOuterPacked = sourceOuter := by
          simp [sourceOuterPacked, sourceOuter, fiberInclusion_map_comp_local, Category.assoc]
        have htheta₂G_target_shape :
            sourceOuter ≫ rightPrefix ≫ rightThetaTerm ≫ rightPost = targetAfterTheta := by
          have h := htheta₂G_prefixed₂
          change sourceOuterPacked ≫ rightPrefix ≫ rightThetaTerm ≫ rightPost =
            sourceOuterPacked ≫ rightPrefix ≫ rightComp ≫ rightPull ≫ rightOwnerPost at h
          erw [hsourceOuter_fold] at h
          dsimp only [targetAfterTheta] at h ⊢
          simpa [Category.assoc] using h
        conv_rhs =>
          change sourceOuterPacked ≫ (rightPrefix ≫ rightThetaTerm) ≫ rightPost
          erw [hsourceOuter_fold]
          simp only [Category.assoc]
          change sourceOuter ≫ rightPrefix ≫ rightThetaTerm ≫ rightPost
          erw [htheta₂G_target_shape]
        let ownerLeftMiddle :=
          Functor.Fiber.fiberInclusion.map
            (Pseudofunctor.DescentData'.pullHom' D.hom
              (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
              ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                  pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫
                (φ.f j₁).left)
              (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
              (member_base_change_owner_left_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)
              (member_base_change_owner_middle_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂))
        let ownerLeftRight :=
          Functor.Fiber.fiberInclusion.map
            (Pseudofunctor.DescentData'.pullHom' D.hom
              (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
              ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                  pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫
                (φ.f j₁).left)
              ((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
                  pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫
                (φ.f j₂).left)
              (member_base_change_owner_left_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)
              (member_base_change_owner_right_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂))
        let ownerRightMiddle :=
          Functor.Fiber.fiberInclusion.map
            (Pseudofunctor.DescentData'.pullHom' D.hom
              (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
              ((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
                  pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫
                (φ.f j₂).left)
              (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
              (member_base_change_owner_right_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)
              (member_base_change_owner_middle_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂))
        let rightPrefixCompNorm :=
          Functor.Fiber.fiberInclusion.map
            ((hc.pullbackCompComponentIso
              (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
              ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
              (((identity_refinement_adapter φ).f j₂).left ^*[hc]
                D.obj ((identity_refinement_adapter φ).α j₂))).inv) ≫
          Functor.Fiber.fiberInclusion.map
            ((hc.pullbackCompComponentIso
              ((identity_refinement_adapter φ).f j₂).left
              (((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
                pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
              (D.obj ((identity_refinement_adapter φ).α j₂))).inv)
        have hright_prefix_comp : rightPrefix ≫ rightComp = rightPrefixCompNorm := by
          have h := congrArg Functor.Fiber.fiberInclusion.map
            (pullbackCompComponentIso_inv_assoc_flexible (hc := hc)
              (φ.f j₂).left
              (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
              ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
              (D.obj (φ.α j₂)))
          simpa [rightPrefix, rightComp, B₂, pullbackFunctor_map_eq_fiberPseudofunctor_map,
            Functor.map_comp, fiberInclusion_map_comp_local, Category.assoc]
            using h
        have hright_pull : rightPull = ownerRightMiddle := by
          have hpull :
              Pseudofunctor.LocallyDiscreteOpToCat.pullHom θ₂
                ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
                ((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
                  pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫ (φ.f j₂).left)
                (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                  pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
                (by simp [Category.assoc])
                (by
                  simpa [Category.assoc] using
                    (member_base_change_owner_middle_legs_eq
                      (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂).symm) =
              Pseudofunctor.DescentData'.pullHom' D.hom
                (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
                ((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
                    pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫
                  (φ.f j₂).left)
                (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                  pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
                (member_base_change_owner_right_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)
                (member_base_change_owner_middle_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂) := by
            simpa [θ₂, Category.assoc] using
              (Pseudofunctor.DescentData'.pullHom_pullHom'
                (F := hc.fiberPseudofunctor) D.hom
                ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
                (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom ≫
                  (φ.f j₂).left ≫ (𝒰.obj (φ.α j₂)).hom)
                (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
                (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom ≫ (φ.f j₂).left)
                (pullback.snd (𝒱.obj j₂).hom (𝒰.obj i).hom)
                ((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
                    pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫
                  (φ.f j₂).left)
                (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                  pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
                (by
                  simpa only [← Category.assoc] using
                    member_base_change_owner_right_leg_map
                      (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)
                (by simp [Category.assoc])
                (by
                  simpa [Category.assoc] using
                    (member_base_change_comparison_component_map
                      (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₂).symm)
                (by simp [Category.assoc])
                (by
                  simpa [Category.assoc] using
                    (member_base_change_owner_middle_legs_eq
                      (𝒰 := 𝒰) (𝒱 := 𝒱) i j₁ j₂).symm))
          simpa [rightPull, ownerRightMiddle] using
            congrArg Functor.Fiber.fiberInclusion.map hpull
        let leftOuterInv :=
          (hc.pullbackCompComponentIso
            (pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
            ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)
            (((identity_refinement_adapter φ).f j₁).left ^*[hc]
              D.obj ((identity_refinement_adapter φ).α j₁))).inv
        let leftInnerInv :=
          (hc.pullbackCompComponentIso
            ((identity_refinement_adapter φ).f j₁).left
            (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
              pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom)
            (D.obj ((identity_refinement_adapter φ).α j₁))).inv
        let ownerLeftRightFiber :=
          Pseudofunctor.DescentData'.pullHom' D.hom
            (((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫ (𝒰.obj i).hom)
            ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫
              (φ.f j₁).left)
            ((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
                pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫
              (φ.f j₂).left)
            (member_base_change_owner_left_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)
            (member_base_change_owner_right_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂)
        let rightInnerIso :=
          hc.pullbackCompComponentIso
            ((identity_refinement_adapter φ).f j₂).left
            (((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
              pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
            (D.obj ((identity_refinement_adapter φ).α j₂))
        let rightOuterIso :=
          hc.pullbackCompComponentIso
            (pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom)
            ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)
            (((identity_refinement_adapter φ).f j₂).left ^*[hc]
              D.obj ((identity_refinement_adapter φ).α j₂))
        have hsource_right_cancel :
            sourceOuter ≫ rightPrefixCompNorm = sourcePrefix ≫ ownerLeftRight := by
          have hcancel :=
            fiberInclusion_map_comp_two_iso_cancel
              (a := leftInnerInv) (m := ownerLeftRightFiber)
              (e := rightInnerIso) (e' := rightOuterIso)
          have hcancel_prefixed :
              Functor.Fiber.fiberInclusion.map leftOuterInv ≫
                  Functor.Fiber.fiberInclusion.map
                    (leftInnerInv ≫ ownerLeftRightFiber ≫ rightInnerIso.hom) ≫
                  Functor.Fiber.fiberInclusion.map rightOuterIso.hom ≫
                  Functor.Fiber.fiberInclusion.map rightOuterIso.inv ≫
                  Functor.Fiber.fiberInclusion.map rightInnerIso.inv =
                Functor.Fiber.fiberInclusion.map leftOuterInv ≫
                  Functor.Fiber.fiberInclusion.map leftInnerInv ≫
                  Functor.Fiber.fiberInclusion.map ownerLeftRightFiber := by
            simpa only [Category.assoc] using
              congrArg (fun k ↦ Functor.Fiber.fiberInclusion.map leftOuterInv ≫ k) hcancel
          letI : HasPullback
              (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
              (pullback.snd (𝒱.obj j₂).hom (𝒰.obj i).hom) := by
            change HasPullback
              ((𝒱.memberBaseChange 𝒰 i).obj j₁).hom
              ((𝒱.memberBaseChange 𝒰 i).obj j₂).hom
            exact ((inferInstance : ∀ i, HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)) i).pairwise j₁ j₂
          have hsource_owner_q :
              ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂ ≫
                    pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom ≫
                  (φ.f j₁).left ≫ (𝒰.obj (φ.α j₁)).hom) =
                ((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫
                  (𝒰.obj i).hom := by
            simpa [Category.assoc] using
              member_base_change_owner_left_leg_map (𝒰 := 𝒰) (𝒱 := 𝒱) φ i j₁ j₂
          have hsource_pairwise_q :
              pullback.fst
                    (pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
                    (pullback.snd (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫
                  pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom ≫
                  (𝒰.obj i).hom =
                ((𝒱.memberBaseChange 𝒰 i).pairwisePullback j₁ j₂).p ≫
                  (𝒰.obj i).hom := by
            simpa [SemiRepresentableFamily.Over.memberBaseChange,
              SemiRepresentableFamily.Over.pairwisePullback, Category.assoc] using
              congrArg (fun f ↦ f ≫ (𝒰.obj i).hom)
                ((𝒱.memberBaseChange 𝒰 i).pr0_map j₁ j₂)
          have hsourceMiddle :
              sourceMiddle = leftInnerInv ≫ ownerLeftRightFiber ≫ rightInnerIso.hom := by
            simp [sourceMiddle, leftInnerInv, ownerLeftRightFiber, rightInnerIso,
              Category.assoc, pullbackFamilyDescentFunctor,
              Pseudofunctor.DescentData'.descentData_hom,
              Pseudofunctor.DescentData'.pullHom'_ofDescentData_hom,
              Pseudofunctor.DescentData.pullFunctorObjHom,
              identity_refinement_adapter, PullbackChoice.fiberPseudofunctor,
              PullbackChoice.pullbackCompIso]
            have hpull_eq_owner
                (q' : (𝒱.memberBaseChange 𝒰 i).overlap j₁ j₂ ⟶ U)
                (hf₁ :
                  ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                      pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫
                    (φ.f j₁).left) ≫ (𝒰.obj (φ.α j₁)).hom = q')
                (hf₂ :
                  ((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
                      pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫
                    (φ.f j₂).left) ≫ (𝒰.obj (φ.α j₂)).hom = q') :
                Pseudofunctor.DescentData'.pullHom' D.hom q'
                    ((((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                        pullback.fst (𝒱.obj j₁).hom (𝒰.obj i).hom) ≫
                      (φ.f j₁).left)
                    ((((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂) ≫
                        pullback.fst (𝒱.obj j₂).hom (𝒰.obj i).hom) ≫
                      (φ.f j₂).left)
                    hf₁ hf₂ = ownerLeftRightFiber := by
              simp [ownerLeftRightFiber, Pseudofunctor.DescentData'.pullHom']
              rfl
            erw [hpull_eq_owner]
            rfl
          have hleft_expanded :
              sourceOuter ≫ rightPrefixCompNorm =
                Functor.Fiber.fiberInclusion.map leftOuterInv ≫
                  Functor.Fiber.fiberInclusion.map
                    (leftInnerInv ≫ ownerLeftRightFiber ≫ rightInnerIso.hom) ≫
                  Functor.Fiber.fiberInclusion.map rightOuterIso.hom ≫
                  Functor.Fiber.fiberInclusion.map rightOuterIso.inv ≫
                  Functor.Fiber.fiberInclusion.map rightInnerIso.inv := by
            simp only [sourceOuter, rightPrefixCompNorm, Category.assoc]
            change
              Functor.Fiber.fiberInclusion.map leftOuterInv ≫
                  Functor.Fiber.fiberInclusion.map sourceMiddle ≫
                  Functor.Fiber.fiberInclusion.map rightOuterIso.hom ≫
                  Functor.Fiber.fiberInclusion.map rightOuterIso.inv ≫
                  Functor.Fiber.fiberInclusion.map rightInnerIso.inv =
                Functor.Fiber.fiberInclusion.map leftOuterInv ≫
                  Functor.Fiber.fiberInclusion.map
                    (leftInnerInv ≫ ownerLeftRightFiber ≫ rightInnerIso.hom) ≫
                  Functor.Fiber.fiberInclusion.map rightOuterIso.hom ≫
                  Functor.Fiber.fiberInclusion.map rightOuterIso.inv ≫
                  Functor.Fiber.fiberInclusion.map rightInnerIso.inv
            rw [hsourceMiddle]
            rfl
          have hright_expanded :
              sourcePrefix ≫ ownerLeftRight =
                Functor.Fiber.fiberInclusion.map leftOuterInv ≫
                  Functor.Fiber.fiberInclusion.map leftInnerInv ≫
                  Functor.Fiber.fiberInclusion.map ownerLeftRightFiber := by
            change
              Functor.Fiber.fiberInclusion.map (leftOuterInv ≫ leftInnerInv) ≫
                  Functor.Fiber.fiberInclusion.map ownerLeftRightFiber =
                Functor.Fiber.fiberInclusion.map leftOuterInv ≫
                  Functor.Fiber.fiberInclusion.map leftInnerInv ≫
                  Functor.Fiber.fiberInclusion.map ownerLeftRightFiber
            rw [Functor.map_comp]
            simp [Category.assoc]
          exact hleft_expanded.trans (hcancel_prefixed.trans hright_expanded.symm)
        have htarget_owner_shape :
            targetAfterTheta = sourcePrefix ≫ ownerLeftRight ≫ ownerRightMiddle ≫ rightOwnerPost := by
          calc
            targetAfterTheta =
                ((sourceOuter ≫ (rightPrefix ≫ rightComp)) ≫ rightPull) ≫ rightOwnerPost := by
              simp [targetAfterTheta, Category.assoc]
            _ = ((sourceOuter ≫ rightPrefixCompNorm) ≫ rightPull) ≫ rightOwnerPost := by
              exact congrArg (fun k ↦ ((sourceOuter ≫ k) ≫ rightPull) ≫ rightOwnerPost)
                hright_prefix_comp
            _ = ((sourceOuter ≫ rightPrefixCompNorm) ≫ ownerRightMiddle) ≫ rightOwnerPost := by
              exact congrArg (fun k ↦ ((sourceOuter ≫ rightPrefixCompNorm) ≫ k) ≫ rightOwnerPost)
                hright_pull
            _ = sourcePrefix ≫ ownerLeftRight ≫ ownerRightMiddle ≫ rightOwnerPost := by
              simpa [← Category.assoc] using
                congrArg (fun k ↦ (k ≫ ownerRightMiddle) ≫ rightOwnerPost)
                  hsource_right_cancel
        rw [htarget_owner_shape]
        have howner :=
          congrArg
            (fun k ↦
              sourcePrefix ≫ k ≫ hc.map
                (((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂) ≫
                  pullback.snd (𝒱.obj j₁).hom (𝒰.obj i).hom)
                (D.obj i))
            (member_base_change_owner_comp_right_to_middle_pullHom'
              (p := p) (hc := hc) D φ i j₁ j₂).symm
        calc
          sourcePrefix ≫ ownerLeftMiddle ≫ rightOwnerPost =
              sourcePrefix ≫ (ownerLeftRight ≫ ownerRightMiddle) ≫ rightOwnerPost := by
            simpa only [ownerLeftMiddle, ownerLeftRight, ownerRightMiddle, rightOwnerPost,
              SemiRepresentableFamily.Over.memberBaseChange,
              SemiRepresentableFamily.Over.pairwisePullback] using howner
          _ = sourcePrefix ≫ ownerLeftRight ≫ ownerRightMiddle ≫ rightOwnerPost := by
            simp [Category.assoc])
/-- Helper for Lemma 8.3.7: the raw owner-side overlap comparison is recovered from the
postcomposed equality by uniqueness of morphisms into the chosen strongly cartesian arrow over the
common owner map. -/
private theorem member_base_change_comparison_postcompose_cancel
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index, HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (D : DescentDatum p hc 𝒰) (φ : 𝒱 ⟶ 𝒰) (i : 𝒰.index) (j₁ j₂ : 𝒱.index) :
    Functor.Fiber.fiberInclusion.map
        ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map
            ((member_base_change_comparison_component_iso hc D φ i j₁).hom) ≫
          ((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).hom j₁ j₂) =
      Functor.Fiber.fiberInclusion.map
        ((pullbackFamilyDescentDatum hc (𝒰 := 𝒱.memberBaseChange 𝒰 i) (𝒱 := 𝒱) (𝒰.obj i).hom
            (member_base_change_refinement_adapter 𝒰 𝒱 i)
            ((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D)).hom
            j₁ j₂ ≫
          (hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)).map
            ((member_base_change_comparison_component_iso hc D φ i j₂).hom)) := by
  let q := (𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂
  let m := hc.map q (((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).obj j₂)
  let ψ :=
    Functor.Fiber.fiberInclusion.map
      ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map
          ((member_base_change_comparison_component_iso hc D φ i j₁).hom) ≫
        ((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).hom j₁ j₂)
  let ψ' :=
    Functor.Fiber.fiberInclusion.map
      ((pullbackFamilyDescentDatum hc (𝒰 := 𝒱.memberBaseChange 𝒰 i) (𝒱 := 𝒱) (𝒰.obj i).hom
          (member_base_change_refinement_adapter 𝒰 𝒱 i)
          ((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D)).hom
          j₁ j₂ ≫
        (hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)).map
          ((member_base_change_comparison_component_iso hc D φ i j₂).hom))
  letI : p.IsHomLift (𝟙 ((𝒱.memberBaseChange 𝒰 i).overlap j₁ j₂)) ψ := by
    dsimp [ψ]
    exact
      (((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map
          ((member_base_change_comparison_component_iso hc D φ i j₁).hom)) ≫
        ((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).hom j₁ j₂).2
  letI : p.IsHomLift (𝟙 ((𝒱.memberBaseChange 𝒰 i).overlap j₁ j₂)) ψ' := by
    dsimp [ψ']
    exact
      (((pullbackFamilyDescentDatum hc (𝒰 := 𝒱.memberBaseChange 𝒰 i) (𝒱 := 𝒱) (𝒰.obj i).hom
          (member_base_change_refinement_adapter 𝒰 𝒱 i)
          ((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D)).hom
          j₁ j₂) ≫
        (hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)).map
          ((member_base_change_comparison_component_iso hc D φ i j₂).hom)).2
  -- Compare the two ambient arrows only after postcomposition with the chosen strongly cartesian
  -- map over the common owner arrow `q`.
  change ψ = ψ'
  have hψ : p.IsHomLift (𝟙 ((𝒱.memberBaseChange 𝒰 i).overlap j₁ j₂)) ψ := inferInstance
  have hψ' : p.IsHomLift (𝟙 ((𝒱.memberBaseChange 𝒰 i).overlap j₁ j₂)) ψ' := inferInstance
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
      q m inferInstance _ _ (𝟙 ((𝒱.memberBaseChange 𝒰 i).overlap j₁ j₂)) ψ ψ' hψ hψ'
      (by
        change ψ ≫ m = ψ' ≫ m
        have hpost :=
          member_base_change_comparison_owner_postcompose
            (p := p) (hc := hc) D φ i j₁ j₂
        simpa [q, m, ψ, ψ', Functor.map_comp, Category.assoc] using hpost)

/-- Helper for Lemma 8.3.7: after passing to the ambient category, the normalized owner-side
overlap calculation for the component comparison is exactly the cocycle identity coming from
`D.comp_pullHom'`, closed by the primed self-comparison `D.pullHom'_self`. -/
theorem member_base_change_comparison_owner_cocycle
    {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U}
    [HasDescentPullbacks 𝒰] [HasDescentPullbacks 𝒱]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index, HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index, HasDescentPullbacks (𝒱.memberBaseChange 𝒰 i)]
    {p : S ⥤ C} [p.IsFibered] (hc : PullbackChoice p)
    (D : DescentDatum p hc 𝒰) (φ : 𝒱 ⟶ 𝒰) (i : 𝒰.index) (j₁ j₂ : 𝒱.index) :
    Functor.Fiber.fiberInclusion.map
        ((hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr0 j₁ j₂)).map
            ((member_base_change_comparison_component_iso hc D φ i j₁).hom) ≫
          ((familyDescentFunctor hc (𝒱.memberBaseChange 𝒰 i)).obj (D.obj i)).hom j₁ j₂) =
    Functor.Fiber.fiberInclusion.map
        ((pullbackFamilyDescentDatum hc (𝒰 := 𝒱.memberBaseChange 𝒰 i) (𝒱 := 𝒱) (𝒰.obj i).hom
            (member_base_change_refinement_adapter 𝒰 𝒱 i)
            ((pullbackFamilyDescentFunctor hc (𝟙 U) (identity_refinement_adapter φ)).obj D)).hom
            j₁ j₂ ≫
          (hc.pullbackFunctor ((𝒱.memberBaseChange 𝒰 i).pr1 j₁ j₂)).map
            ((member_base_change_comparison_component_iso hc D φ i j₂).hom)) := by
  -- Route correction: recover the raw equality by cancelling the common postcomposition with the
  -- chosen cartesian arrow over the owner map fixed in the previous lemma.
  simpa using
    member_base_change_comparison_postcompose_cancel
      (p := p) (hc := hc) D φ i j₁ j₂


end CategoryTheory
