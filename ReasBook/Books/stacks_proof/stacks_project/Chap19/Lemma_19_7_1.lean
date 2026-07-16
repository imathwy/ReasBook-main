import Mathlib
import stacks_proof.stacks_project.Chap19.Proposition_19_6_1

open CategoryTheory
open CategoryTheory.SmallObject
open CategoryTheory.SmallObject.SuccStruct

universe u v

noncomputable section

namespace AbelianSheafTransfinite

section

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)
variable [HasWeakSheafify K AddCommGrpCat.{max u v}]

/- Domain-style sampling for Lemma 19.7.1:
- primary domain: the Section 19.6/19.7 transfinite injective-resolution construction for abelian
  sheaves, built from the presheaf owner `iℱ ⟶ J(iℱ)` and sheafification;
- sampled owner declarations:
  `HasFunctorialInjectiveEmbeddings.ι`,
  `HasFunctorialInjectiveEmbeddings.underMap`,
  `presheafToSheaf`,
  `toSheafify`,
  `SuccStruct.iterationFunctorObjSuccIso`;
- best owner abstraction: the source-facing transfinite family is most canonically owned by the
  ordinal-indexed iteration of the successor structure whose one-step functor is
  `J_1(ℱ) = J(iℱ)^#`, obtained from the Chapter 19.6 presheaf owner
  `HasFunctorialInjectiveEmbeddings (PAb(C))` and the canonical sheafification functor;
- primitive data: the presheaf embedding `iℱ ⟶ J(iℱ)` and the sheafification unit
  `J(iℱ) ⟶ J(iℱ)^#`;
- derived API: the ordinal-indexed transfinite family `J_α`, the actual successor-stage map
  `j_α : J_α ⟶ J_{α+1}`, the stage object `stage h ℱ` and canonical map
  `stageToTop h ℱ : stage h ℱ ⟶ J_β(ℱ)` inside a fixed truncated tower, the canonical identification
  `J_{α+1}(ℱ) ≅ J_1(J_α(ℱ))`, and the extension morphism across a monomorphism.

Source/core/bridge triage:
- `source-facing`: the recursively defined sheaf family `J_α(ℱ)` and the successor maps
  `J_α(ℱ) ⟶ J_{α+1}(ℱ)`;
- `core/canonical`: `HasFunctorialInjectiveEmbeddings` on `PAb(C)`, `Injective.factorThru`,
  `presheafToSheaf`, and `toSheafify`;
- `bridge/view`: the successor-extension square below, obtained by extending on underlying
  presheaves and then applying sheafification. -/

private noncomputable abbrev presheafJ :
    PAb(C) ⥤ PAb(C) :=
  HasFunctorialInjectiveEmbeddings.J ⋙ Arrow.rightFunc

private noncomputable def presheafι :
    𝟭 (PAb(C)) ⟶ presheafJ where
  app F := HasFunctorialInjectiveEmbeddings.ι F
  naturality {_ _} φ := HasFunctorialInjectiveEmbeddings.ι_naturality_w φ

private noncomputable abbrev JOneFunctor :
    Sheaf K AddCommGrpCat.{max u v} ⥤ Sheaf K AddCommGrpCat.{max u v} :=
  sheafToPresheaf K AddCommGrpCat.{max u v} ⋙
    presheafJ ⋙
      presheafToSheaf K AddCommGrpCat.{max u v}

private noncomputable def jOneNatTrans :
    𝟭 (Sheaf K AddCommGrpCat.{max u v}) ⟶ JOneFunctor K :=
  (sheafificationNatIso K AddCommGrpCat.{max u v}).hom ≫
    Functor.whiskerRight
      (Functor.whiskerLeft
        (sheafToPresheaf K AddCommGrpCat.{max u v})
        presheafι)
      (presheafToSheaf K AddCommGrpCat.{max u v})

/-- The one-step source-facing sheaf construction `J_1(ℱ) = J(iℱ)^#`. -/
noncomputable def JOne
    (ℱ : Sheaf K AddCommGrpCat.{max u v}) :
    Sheaf K AddCommGrpCat.{max u v} :=
  (JOneFunctor K).obj ℱ

/-- The canonical one-step map `ℱ ⟶ J_1(ℱ)` induced from `iℱ ⟶ J(iℱ)` and sheafification. -/
noncomputable def jOne
    (ℱ : Sheaf K AddCommGrpCat.{max u v}) :
    ℱ ⟶ JOne K ℱ :=
  (jOneNatTrans K).app ℱ

private noncomputable def succStruct
    (ℱ : Sheaf K AddCommGrpCat.{max u v}) :
    SuccStruct (Sheaf K AddCommGrpCat.{max u v}) where
  X₀ := ℱ
  succ X := JOne K X
  toSucc X := jOne K X

private abbrev shape (α : Ordinal) : Type _ :=
  Set.Iic α

private noncomputable abbrev tower
    (ℱ : Sheaf K AddCommGrpCat.{max u v}) (α : Ordinal) :
    shape α ⥤ Sheaf K AddCommGrpCat.{max u v} :=
  let _ :
      Limits.HasIterationOfShape (shape α) (Sheaf K AddCommGrpCat.{max u v}) :=
    { hasColimitsOfShape_of_isSuccLimit := fun _ _ ↦ by infer_instance
      hasColimitsOfShape := by infer_instance }
  (succStruct K ℱ).iterationFunctor (shape α)

private abbrev stageIndex (α : Ordinal) : shape α :=
  ⟨α, by simpa using (le_rfl : α ≤ α)⟩

/-- The transfinite source-facing sheaf object `J_α(ℱ)`. -/
noncomputable abbrev J
    (α : Ordinal) (ℱ : Sheaf K AddCommGrpCat.{max u v}) :
    Sheaf K AddCommGrpCat.{max u v} :=
  (tower K ℱ α).obj (stageIndex α)

scoped notation:max "J_[" K "," α "](" ℱ ")" =>
  J K α ℱ

/-- The `α`-stage of the `β`-truncated `J`-tower, viewed inside that fixed tower. -/
noncomputable abbrev stage {α β : Ordinal}
    (h : α ≤ β) (ℱ : Sheaf K AddCommGrpCat.{max u v}) :
    Sheaf K AddCommGrpCat.{max u v} :=
  (tower K ℱ β).obj ⟨α, h⟩

/-- The canonical transition map from the `α`-stage of the `β`-tower to its top object
`J_[K, β](ℱ)`. -/
noncomputable def stageToTop {α β : Ordinal}
    (h : α ≤ β) (ℱ : Sheaf K AddCommGrpCat.{max u v}) :
    stage K h ℱ ⟶ J_[K,β](ℱ) :=
  (tower K ℱ β).map (homOfLE (by simpa [stageIndex] using h))

/-- Helper for Lemma 19.7.1: flatten the nested initial segment
`Set.Iic (⟨α, h⟩ : Set.Iic β)` back to `Set.Iic α`. -/
private def stageShapeOrderIso {α β : Ordinal} (h : α ≤ β) :
    shape α ≃o Set.Iic (⟨α, h⟩ : shape β) where
  toEquiv :=
    { toFun := fun x ↦ ⟨⟨x.1, x.2.trans h⟩, x.2⟩
      invFun := fun x ↦ ⟨x.1.1, x.2⟩
      left_inv := by
        intro x
        cases x
        rfl
      right_inv := by
        intro x
        cases x
        rfl }
  map_rel_iff' := by
    intro x y
    rfl

/-- Helper for Lemma 19.7.1: the order isomorphism from the `α`-shape to the nested initial
segment over `⟨α, h⟩` sends the top stage of the smaller tower to the top stage of the larger
tower. -/
private theorem stageShapeOrderIso_top {α β : Ordinal}
    (h : α ≤ β) :
    stageShapeOrderIso h (stageIndex α) = ⟨(⟨α, h⟩ : shape β), by simp⟩ := by
  rfl

private theorem J_eq_stage {α β : Ordinal}
    (h : α ≤ β) (ℱ : Sheaf K AddCommGrpCat.{max u v}) :
    J_[K,α](ℱ) = stage K h ℱ := by
  -- The source-facing `J_[K, α](ℱ)` notation is just the stage object of the `β`-tower
  -- specialized at the index `⟨α, h⟩`, so the comparison is definitional.
  rfl

/-- The canonical transition map `J_[K, α](ℱ) ⟶ J_[K, β](ℱ)` in the transfinite `J`-tower. -/
noncomputable def transition {α β : Ordinal}
    (h : α ≤ β) (ℱ : Sheaf K AddCommGrpCat.{max u v}) :
    J_[K,α](ℱ) ⟶ J_[K,β](ℱ) :=
  eqToHom (J_eq_stage K h ℱ) ≫ stageToTop K h ℱ

private theorem towerObj_pred_eq_J
    (α : Ordinal) (ℱ : Sheaf K AddCommGrpCat.{max u v}) :
    (tower K ℱ (Order.succ α)).obj ⟨α, Order.le_succ α⟩ = J K α ℱ := by
  -- This is the predecessor-stage specialization of `J_eq_stage`.
  simpa using (J_eq_stage K (Order.le_succ α) ℱ).symm

/-- The canonical successor-stage identification `J_[K, α + 1](ℱ) ≅ J_1(J_[K, α](ℱ))`. -/
noncomputable def succIso
    (α : Ordinal) (ℱ : Sheaf K AddCommGrpCat.{max u v}) :
    J_[K,Order.succ α](ℱ) ≅ JOne K (J_[K,α](ℱ)) := by
  let _ :
      Limits.HasIterationOfShape (shape (Order.succ α)) (Sheaf K AddCommGrpCat.{max u v}) :=
    { hasColimitsOfShape_of_isSuccLimit := fun _ _ ↦ by infer_instance
      hasColimitsOfShape := by infer_instance }
  let j : shape (Order.succ α) := ⟨α, Order.le_succ α⟩
  have hj : ¬ IsMax j := by
    rw [not_isMax_iff_ne_top]
    intro h
    exact (Order.lt_succ_of_not_isMax (not_isMax α)).ne (congrArg Subtype.val h)
  have hsuccj : Order.succ j = stageIndex (Order.succ α) := by
    ext
    simp [j]
  exact
    eqToIso (congrArg ((tower K ℱ (Order.succ α)).obj) hsuccj).symm ≪≫
      (succStruct K ℱ).iterationFunctorObjSuccIso j hj ≪≫
      eqToIso (congrArg (JOne K) (towerObj_pred_eq_J K α ℱ))

/-- The canonical successor-stage map `j_α : J_α(ℱ) ⟶ J_{α+1}(ℱ)`. -/
noncomputable def j
    (α : Ordinal) (ℱ : Sheaf K AddCommGrpCat.{max u v}) :
    J K α ℱ ⟶ J K (Order.succ α) ℱ :=
  jOne K (J K α ℱ) ≫ (succIso K α ℱ).inv

scoped notation:max "j_[" K "," α "](" ℱ ")" =>
  j K α ℱ

private noncomputable def successorLift
    {𝒢₁ 𝒢₂ ℱ : Sheaf K AddCommGrpCat.{max u v}}
    (i : 𝒢₁ ⟶ 𝒢₂) [Mono i]
    (φ : 𝒢₁ ⟶ ℱ) :
    𝒢₂ ⟶ JOne K ℱ :=
  (sheafificationIso 𝒢₂).hom ≫
    ((sheafificationAdjunction K AddCommGrpCat.{max u v}).homEquiv _ _).symm
      (Injective.factorThru
          (φ.1 ≫ HasFunctorialInjectiveEmbeddings.ι ℱ.obj)
          i.1 ≫
        toSheafify K (presheafJ.obj ℱ.obj))

/-- Helper for Lemma 19.7.1: the one-step map `jOne` is the sheafification of the canonical
presheaf embedding into the chosen injective envelope. -/
private theorem jOne_eq_sheafified_presheaf_embedding
    (ℱ : Sheaf K AddCommGrpCat.{max u v}) :
    jOne K ℱ =
      (sheafificationIso ℱ).hom ≫
        (presheafToSheaf K AddCommGrpCat.{max u v}).map
          (HasFunctorialInjectiveEmbeddings.ι ℱ.obj) := by
  -- This is just the definition of `jOne` after unfolding the whiskered natural transformation.
  rfl

/-- Helper for Lemma 19.7.1: transporting a sheaf morphism across the source and target
sheafification isomorphisms recovers the induced map on sheafifications of the underlying
presheaf morphism. -/
private theorem sheafificationIso_inv_comp_hom_eq_map
    {𝒢₁ 𝒢₂ : Sheaf K AddCommGrpCat.{max u v}}
    (f : 𝒢₁ ⟶ 𝒢₂) :
    (sheafificationIso 𝒢₁).inv ≫ f ≫ (sheafificationIso 𝒢₂).hom =
      (presheafToSheaf K AddCommGrpCat.{max u v}).map f.hom := by
  -- Normalize the naturality square for `sheafificationNatIso` by precomposing with the inverse
  -- of the source sheafification isomorphism.
  have hpre :
      (sheafificationIso 𝒢₁).inv ≫ (f ≫ (sheafificationIso 𝒢₂).hom) =
        (sheafificationIso 𝒢₁).inv ≫
          ((sheafificationIso 𝒢₁).hom ≫
            (presheafToSheaf K AddCommGrpCat.{max u v}).map f.hom) := by
    exact
      congrArg
        (fun k ↦ (sheafificationIso 𝒢₁).inv ≫ k)
        ((sheafificationNatIso K AddCommGrpCat.{max u v}).hom.naturality f)
  -- Cancel the source sheafification isomorphism to isolate the sheafified presheaf map.
  simpa [Category.assoc] using
    hpre.trans
      (Iso.inv_hom_id_assoc
        (sheafificationIso 𝒢₁)
        ((presheafToSheaf K AddCommGrpCat.{max u v}).map f.hom))

/-- Helper for Lemma 19.7.1: transposing a morphism after identifying its source with the
sheafification of the underlying presheaf recovers the underlying presheaf morphism. -/
private theorem homEquivSheafificationIsoInv
    {𝒢 ℱ : Sheaf K AddCommGrpCat.{max u v}}
    (ψ : 𝒢 ⟶ ℱ) :
    ((sheafificationAdjunction K AddCommGrpCat.{max u v}).homEquiv _ _)
        ((sheafificationIso 𝒢).inv ≫ ψ) =
      ψ.1 := by
  -- Rewrite the transpose through the adjunction unit and identify the unit with the forward
  -- sheafification comparison on `𝒢`.
  rw [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app]
  -- After expanding the unit, the goal is exactly the underlying presheaf form of
  -- `(sheafificationIso 𝒢).hom ≫ (sheafificationIso 𝒢).inv ≫ ψ = ψ`.
  simpa [Category.assoc] using
    congrArg (fun f ↦ f.1) ((sheafificationIso 𝒢).hom_inv_id_assoc ψ)

/-- Helper for Lemma 19.7.1: the underlying presheaf map of `jOne` is the canonical injective
embedding followed by the sheafification unit of the target presheaf. -/
private theorem underlyingJOne_eq_embedding_toSheafify
    (ℱ : Sheaf K AddCommGrpCat.{max u v}) :
    (jOne K ℱ).1 =
      HasFunctorialInjectiveEmbeddings.ι ℱ.obj ≫
        toSheafify K (presheafJ.obj ℱ.obj) := by
  -- First rewrite `jOne` through the sheafification comparison, then normalize the induced
  -- sheafified presheaf map by naturality of `toSheafify`.
  have hjOne_hom :
      (jOne K ℱ).1 =
        (sheafificationIso ℱ).hom.1 ≫
          ((presheafToSheaf K AddCommGrpCat.{max u v}).map
            (HasFunctorialInjectiveEmbeddings.ι ℱ.obj)).1 := by
    exact congrArg (fun f ↦ f.1) (jOne_eq_sheafified_presheaf_embedding K ℱ)
  rw [hjOne_hom]
  -- The sheafified map underlying `jOne` is just the naturality square for the unit.
  simpa using (CategoryTheory.toSheafify_naturality K
    (HasFunctorialInjectiveEmbeddings.ι ℱ.obj)).symm

/-- Helper for Lemma 19.7.1: after transporting the source through its sheafification
isomorphism, the adjunction transpose of the composite through `jOne` is the underlying
presheaf embedding followed by the sheafification unit. -/
private theorem jOne_homEquiv_eq_presheaf_embedding
    {𝒢 ℱ : Sheaf K AddCommGrpCat.{max u v}}
    (ψ : 𝒢 ⟶ ℱ) :
    ((sheafificationAdjunction K AddCommGrpCat.{max u v}).homEquiv _ _)
        ((sheafificationIso 𝒢).inv ≫ ψ ≫ jOne K ℱ) =
      ψ.1 ≫ HasFunctorialInjectiveEmbeddings.ι ℱ.obj ≫
        toSheafify K (presheafJ.obj ℱ.obj) := by
  let adj := sheafificationAdjunction K AddCommGrpCat.{max u v}
  -- Apply right naturality once so the transpose splits into the source normalization and the
  -- literal underlying presheaf map of `jOne`.
  have hnat :
      (adj.homEquiv _ _) ((sheafificationIso 𝒢).inv ≫ ψ ≫ jOne K ℱ) =
        (adj.homEquiv _ _) ((sheafificationIso 𝒢).inv ≫ ψ) ≫
          (jOne K ℱ).1 := by
    simpa [adj, Category.assoc] using
      adj.homEquiv_naturality_right ((sheafificationIso 𝒢).inv ≫ ψ) (jOne K ℱ)
  rw [hnat, homEquivSheafificationIsoInv K ψ, underlyingJOne_eq_embedding_toSheafify K ℱ]
  -- The goal is now literally the normalized target presheaf composite.
  rfl

private theorem successorLift_comm
    {𝒢₁ 𝒢₂ ℱ : Sheaf K AddCommGrpCat.{max u v}}
    (i : 𝒢₁ ⟶ 𝒢₂) [Mono i]
    (φ : 𝒢₁ ⟶ ℱ) :
    CommSq φ i (jOne K ℱ) (successorLift K i φ) := by
  let adj := sheafificationAdjunction K AddCommGrpCat.{max u v}
  let q :
      𝒢₂.obj ⟶ (sheafToPresheaf K AddCommGrpCat.{max u v}).obj (JOne K ℱ) :=
    Injective.factorThru (φ.1 ≫ HasFunctorialInjectiveEmbeddings.ι ℱ.obj) i.1 ≫
      toSheafify K (presheafJ.obj ℱ.obj)
  refine ⟨?_⟩
  -- Compare the two sides after pulling the common source back across its sheafification
  -- isomorphism, where the adjunction transpose turns the square into a presheaf identity.
  have hpre :
      (sheafificationIso 𝒢₁).inv ≫ (φ ≫ jOne K ℱ) =
        (sheafificationIso 𝒢₁).inv ≫ (i ≫ successorLift K i φ) := by
    apply (adj.homEquiv _ _).injective
    have hright_transport :
        (sheafificationIso 𝒢₁).inv ≫ i =
          (presheafToSheaf K AddCommGrpCat.{max u v}).map i.hom ≫
            (sheafificationIso 𝒢₂).inv := by
      -- Move the sheaf morphism `i` to the presheaf side before applying left naturality.
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ k ≫ (sheafificationIso 𝒢₂).inv)
          (sheafificationIso_inv_comp_hom_eq_map K i)
    have hsuccessor :
        (adj.homEquiv _ _) ((sheafificationIso 𝒢₂).inv ≫ successorLift K i φ) = q := by
      -- Unfold the chosen lift once: after canceling the source sheafification comparison,
      -- `homEquiv` and its inverse are inverse equivalences.
      simpa [adj, q, successorLift, Category.assoc] using
        (Equiv.apply_symm_apply (adj.homEquiv 𝒢₂.obj (JOne K ℱ)) q)
    have hright_homEquiv :
        (adj.homEquiv _ _) ((sheafificationIso 𝒢₁).inv ≫ (i ≫ successorLift K i φ)) =
          φ.1 ≫ HasFunctorialInjectiveEmbeddings.ι ℱ.obj ≫
            toSheafify K (presheafJ.obj ℱ.obj) := by
      -- Normalize the right side to the chosen presheaf factorization and use the defining
      -- property of `Injective.factorThru`.
      calc
        (adj.homEquiv _ _) ((sheafificationIso 𝒢₁).inv ≫ (i ≫ successorLift K i φ)) =
            (adj.homEquiv _ _)
              (((presheafToSheaf K AddCommGrpCat.{max u v}).map i.hom) ≫
                ((sheafificationIso 𝒢₂).inv ≫ successorLift K i φ)) := by
                have hcompose :
                    (sheafificationIso 𝒢₁).inv ≫ (i ≫ successorLift K i φ) =
                      (((presheafToSheaf K AddCommGrpCat.{max u v}).map i.hom) ≫
                        (sheafificationIso 𝒢₂).inv) ≫ successorLift K i φ := by
                  simpa [Category.assoc] using
                    congrArg (fun k ↦ k ≫ successorLift K i φ) hright_transport
                have hassoc :
                    (((presheafToSheaf K AddCommGrpCat.{max u v}).map i.hom) ≫
                        (sheafificationIso 𝒢₂).inv) ≫ successorLift K i φ =
                      ((presheafToSheaf K AddCommGrpCat.{max u v}).map i.hom) ≫
                        ((sheafificationIso 𝒢₂).inv ≫ successorLift K i φ) := by
                  simp [Category.assoc]
                exact congrArg (fun k ↦ (adj.homEquiv _ _) k) (hcompose.trans hassoc)
        _ = i.hom ≫ (adj.homEquiv _ _)
              ((sheafificationIso 𝒢₂).inv ≫ successorLift K i φ) := by
                simpa [adj, Category.assoc] using
                  adj.homEquiv_naturality_left i.hom
                    ((sheafificationIso 𝒢₂).inv ≫ successorLift K i φ)
        _ = i.hom ≫ q := by
                rw [hsuccessor]
        _ = φ.1 ≫ HasFunctorialInjectiveEmbeddings.ι ℱ.obj ≫
              toSheafify K (presheafJ.obj ℱ.obj) := by
                dsimp [q]
                change
                  (i.hom ≫ Injective.factorThru
                      (φ.hom ≫ HasFunctorialInjectiveEmbeddings.ι ℱ.obj) i.hom) ≫
                    toSheafify K (presheafJ.obj ℱ.obj) =
                  φ.1 ≫ HasFunctorialInjectiveEmbeddings.ι ℱ.obj ≫
                    toSheafify K (presheafJ.obj ℱ.obj)
                rw [Injective.comp_factorThru]
                rfl
    have hleft_homEquiv :
        (adj.homEquiv _ _) ((sheafificationIso 𝒢₁).inv ≫ (φ ≫ jOne K ℱ)) =
          φ.1 ≫ HasFunctorialInjectiveEmbeddings.ι ℱ.obj ≫
            toSheafify K (presheafJ.obj ℱ.obj) := by
      simpa [Category.assoc] using jOne_homEquiv_eq_presheaf_embedding K φ
    exact hleft_homEquiv.trans hright_homEquiv.symm
  calc
    φ ≫ jOne K ℱ =
        (sheafificationIso 𝒢₁).hom ≫ ((sheafificationIso 𝒢₁).inv ≫ (φ ≫ jOne K ℱ)) := by
          symm
          simpa [Category.assoc] using
            (sheafificationIso 𝒢₁).hom_inv_id_assoc (φ ≫ jOne K ℱ)
    _ =
        (sheafificationIso 𝒢₁).hom ≫ ((sheafificationIso 𝒢₁).inv ≫ (i ≫ successorLift K i φ)) := by
          rw [hpre]
    _ = i ≫ successorLift K i φ := by
          simpa [Category.assoc] using
            (sheafificationIso 𝒢₁).hom_inv_id_assoc (i ≫ successorLift K i φ)

open scoped AbelianSheafTransfinite

-- Proof sketch: specialize the one-step extension square to the sheaf `J_α(ℱ)`. On underlying
-- presheaves, extend `𝒢₁.obj ⟶ J(i(J_α(ℱ).obj))` across `i.obj` using the canonical injective
-- presheaf `J(i(J_α(ℱ).obj))`, then compose with the sheafification unit
-- `J(i(J_α(ℱ).obj)) ⟶ J_{α+1}(ℱ).obj`.
/-- Lemma 19.7.1: every morphism `𝒢₁ ⟶ J_α(ℱ)` extends across a monomorphism
`i : 𝒢₁ ⟶ 𝒢₂` after composing with the canonical successor map
`J_α(ℱ) ⟶ J_{α+1}(ℱ)`. -/
@[stacks 01DM]
theorem extend_to_successor_stage
    {𝒢₁ 𝒢₂ ℱ : Sheaf K AddCommGrpCat.{max u v}}
    (α : Ordinal)
    (i : 𝒢₁ ⟶ 𝒢₂) [Mono i]
    (φ : 𝒢₁ ⟶ J_[K,α](ℱ)) :
    ∃ ψ : 𝒢₂ ⟶ J_[K,Order.succ α](ℱ), CommSq φ i (j_[K,α](ℱ)) ψ := by
  refine ⟨successorLift K i φ ≫ (succIso K α ℱ).inv, ?_⟩
  refine ⟨?_⟩
  simpa [Category.assoc, j] using
    congrArg (fun k ↦ k ≫ (succIso K α ℱ).inv) (successorLift_comm K i φ).w

end

end AbelianSheafTransfinite
