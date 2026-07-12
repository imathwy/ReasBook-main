import StacksProject_2024.Chap10.Definition_10_134_1
import StacksProject_2024.Chap10.Lemma_10_131_5

open Algebra
open Algebra.Generators
open Algebra.Extension
open CategoryTheory
open CategoryTheory.Limits
open scoped NaiveCotangent

universe u

noncomputable section

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {R S : I → Type u}
variable [∀ i, CommRing (R i)] [∀ i, CommRing (S i)] [∀ i, Algebra (R i) (S i)]
variable {ρ : ∀ i j, i ≤ j → R i →+* R j}
variable {σ : ∀ i j, i ≤ j → S i →+* S j}
variable (hcomm :
  ∀ ⦃i j : I⦄ (h : i ≤ j),
    (algebraMap (R j) (S j)).comp (ρ i j h) =
      (σ i j h).comp (algebraMap (R i) (S i)))

local notation "R∞" => Ring.DirectLimit R (fun i j h ↦ ρ i j h)
local notation "S∞" => Ring.DirectLimit S (fun i j h ↦ σ i j h)

/-!
Domain sampling:
* primary domain: naive cotangent complexes and directed filtered colimits of algebra maps;
* sampled owner declarations:
  - `Algebra.naiveCotangent`, the Chapter 10 owner `NL_{-⁄-}`;
  - `Generators.defaultHom`, the canonical morphism between self-presentations in a commuting
    square of algebras;
  - `Extension.CotangentSpace.map_comp_cotangentComplex`, the owner-level compatibility of the two
    terms and differential under presentation morphisms;
  - `ModuleCat.extendScalarsComp` and categorical `colimit`, the canonical way to transport the
    stagewise complexes to the common target category `ChainComplex (ModuleCat S∞) ℕ` and then
    form their filtered colimit.
* best owner abstraction:
  - `source-facing`: the filtered colimit of the stagewise owner complexes `NL_{S_i⁄R_i}` after
    extending scalars to `S∞`;
  - `core/canonical`: the target owner `NL_{S∞⁄R∞}`;
  - `bridge/view`: the scalar-extension diagram landing in `ChainComplex (ModuleCat S∞) ℕ`.

Primitive data are the directed system of algebra maps over a directed set together with the
induced morphisms between the stagewise canonical complexes. The colimit cocone and the comparison
to `NL_{S∞⁄R∞}` are derived categorical API; there is no separate public wrapper complex parallel
to the owner `NL_{-⁄-}`.
-/

private abbrev stageBaseMap (i : I) : R i →+* R∞ :=
  Ring.DirectLimit.of R (fun i j h ↦ ρ i j h) i

private abbrev stageTargetMap (i : I) : S i →+* S∞ :=
  Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i

private theorem stageTargetMap_comp {i j : I} (h : i ≤ j) :
    (Ring.DirectLimit.of S (fun i j h ↦ σ i j h) j).comp (σ i j h) =
      Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i := by
  ext x
  change Ring.DirectLimit.of S (fun i j h ↦ σ i j h) j (σ i j h x) =
    Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i x
  simp [Ring.DirectLimit.of_f h x]

private theorem directLimit_square
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) :
    (Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).comp
        (Ring.DirectLimit.of R (fun i j h ↦ ρ i j h) i) =
      (Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i).comp (algebraMap (R i) (S i)) := by
  ext x
  simp

private noncomputable abbrev targetNaiveCotangent :
    ChainComplex (ModuleCat.{u} S∞) ℕ := by
  let _ : Algebra R∞ S∞ :=
    (Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).toAlgebra
  exact NL_{S∞⁄R∞}

private noncomputable abbrev stageNaiveCotangentBaseChange (i : I) :
    ChainComplex (ModuleCat.{u} S∞) ℕ := by
  let C : ChainComplex (ModuleCat.{u} (S i)) ℕ :=
    Algebra.Extension.naiveCotangentChainComplex
      ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension)
  exact ((ModuleCat.extendScalars (stageTargetMap i)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj C

private noncomputable def restrictOfIso
    {B : Type u} {C : Type u} [CommRing B] [CommRing C] [Algebra B C]
    (M : Type u) [AddCommGroup M] [Module C M] [Module B M] [IsScalarTower B C M] :
    (ModuleCat.restrictScalars (algebraMap B C)).obj (ModuleCat.of C M) ≅ ModuleCat.of B M :=
  (show ↑((ModuleCat.restrictScalars (algebraMap B C)).obj (ModuleCat.of C M)) ≃ₗ[B] M from
      { __ := AddEquiv.refl _
        map_smul' _ _ := by simp }).toModuleIso

private noncomputable def stageNaiveCotangentTransitionBase
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) :
    (((ModuleCat.extendScalars (σ i j h)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Algebra.Extension.naiveCotangentChainComplex
        ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension))) ⟶
      (Algebra.Extension.naiveCotangentChainComplex
        ((Generators.self (R j) (S j) : Generators (R j) (S j) (S j)).toExtension)) := by
  let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
  let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
  let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
  let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  let C₁ :
      ChainComplex (ModuleCat (S j)) ℕ :=
    (((ModuleCat.extendScalars (σ i j h)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension))
  let C₂ : ChainComplex (ModuleCat (S j)) ℕ :=
    Algebra.Extension.naiveCotangentChainComplex Pj.toExtension
  let f : Pi.toExtension.Hom Pj.toExtension := (Generators.defaultHom Pi Pj).toExtensionHom
  let f₀' :
      (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 0 ⟶
        (ModuleCat.restrictScalars (σ i j h)).obj (C₂.X 0) :=
    ModuleCat.ofHom (Extension.CotangentSpace.map f) ≫
      (restrictOfIso Pj.toExtension.CotangentSpace).inv
  let f₀ : C₁.X 0 ⟶ C₂.X 0 :=
    ((ModuleCat.extendRestrictScalarsAdj (σ i j h)).homEquiv _ _).symm
      f₀'
  let liftf : ULift Pi.toExtension.Cotangent →ₗ[S i] ULift Pj.toExtension.Cotangent :=
    { toFun := fun x ↦ ULift.up (Extension.Cotangent.map f x.down)
      map_add' := by
        intro x y
        ext <;> simp
      map_smul' := by
        intro r x
        ext <;> simp }
  let f₁' :
      (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 1 ⟶
        (ModuleCat.restrictScalars (σ i j h)).obj (C₂.X 1) :=
    ModuleCat.ofHom liftf ≫
      (restrictOfIso (ULift Pj.toExtension.Cotangent)).inv
  let f₁ : C₁.X 1 ⟶ C₂.X 1 :=
    ((ModuleCat.extendRestrictScalarsAdj (σ i j h)).homEquiv _ _).symm
      f₁'
  refine ChainComplex.mkHom _ _ f₀ f₁ ?_ ?_
  · sorry
  · intro n
    sorry

private noncomputable def stageNaiveCotangentBaseChangeTransition
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) := by
  let Cᵢ : ChainComplex (ModuleCat (S i)) ℕ :=
    Algebra.Extension.naiveCotangentChainComplex
      ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension)
  let σij : S i →+* S j := σ i j h
  let σjLim : S j →+* S∞ := Ring.DirectLimit.of S (fun i j h ↦ σ i j h) j
  have hobj :
      (((ModuleCat.extendScalars (stageTargetMap i)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj Cᵢ) =
        (((ModuleCat.extendScalars (σjLim.comp σij)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj Cᵢ) := by
    simpa [Cᵢ, stageNaiveCotangentBaseChange] using
      congrArg
        (fun t ↦
          ((ModuleCat.extendScalars t).mapHomologicalComplex (ComplexShape.down ℕ)).obj Cᵢ)
        (stageTargetMap_comp h).symm
  exact
    eqToHom hobj ≫
      ((NatIso.mapHomologicalComplex
          (ModuleCat.extendScalarsComp σij σjLim)
        (ComplexShape.down ℕ)).hom.app Cᵢ) ≫
      ((ModuleCat.extendScalars σjLim).mapHomologicalComplex
        (ComplexShape.down ℕ)).map
        (stageNaiveCotangentTransitionBase hcomm h)

private noncomputable def stageNaiveCotangentToTarget
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) :
    @stageNaiveCotangentBaseChange I _ R S _ _ _ σ i ⟶
      @targetNaiveCotangent I _ R S _ _ _ ρ σ hcomm := by
  let σiLim : S i →+* S∞ := Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i
  let _ : Algebra (R i) R∞ := (stageBaseMap i).toAlgebra
  let _ : Algebra (S i) S∞ := σiLim.toAlgebra
  let _ : Algebra (R i) S∞ :=
    ((Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).comp
      (stageBaseMap i)).toAlgebra
  let _ : Algebra R∞ S∞ :=
    (Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).toAlgebra
  let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) S∞ :=
    IsScalarTower.of_algebraMap_eq' (directLimit_square hcomm i)
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  let C₁ : ChainComplex (ModuleCat S∞) ℕ :=
    (((ModuleCat.extendScalars σiLim).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
        (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension))
  let C₂ : ChainComplex (ModuleCat S∞) ℕ :=
    @targetNaiveCotangent I _ R S _ _ _ ρ σ hcomm
  let f : Pi.toExtension.Hom Pinf.toExtension :=
    (Generators.defaultHom Pi Pinf).toExtensionHom
  let f₀' :
      (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 0 ⟶
        (ModuleCat.restrictScalars σiLim).obj (C₂.X 0) :=
    ModuleCat.ofHom (Extension.CotangentSpace.map f) ≫
      (restrictOfIso Pinf.toExtension.CotangentSpace).inv
  let f₀ : C₁.X 0 ⟶ C₂.X 0 :=
    ((ModuleCat.extendRestrictScalarsAdj σiLim).homEquiv _ _).symm
      f₀'
  let liftf : ULift Pi.toExtension.Cotangent →ₗ[S i]
      ULift Pinf.toExtension.Cotangent :=
    { toFun := fun x ↦ ULift.up (Extension.Cotangent.map f x.down)
      map_add' := by
        intro x y
        ext <;> simp
      map_smul' := by
        intro r x
        ext <;> simp }
  let f₁' :
      (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 1 ⟶
        (ModuleCat.restrictScalars σiLim).obj (C₂.X 1) :=
    ModuleCat.ofHom liftf ≫
      (restrictOfIso (ULift Pinf.toExtension.Cotangent)).inv
  let f₁ : C₁.X 1 ⟶ C₂.X 1 :=
    ((ModuleCat.extendRestrictScalarsAdj σiLim).homEquiv _ _).symm
      f₁'
  refine ChainComplex.mkHom _ _ f₀ f₁ ?_ ?_
  · sorry
  · intro n
    sorry

private theorem stageNaiveCotangentToTarget_compatible
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) :
    stageNaiveCotangentBaseChangeTransition hcomm h ≫
        stageNaiveCotangentToTarget hcomm j =
      stageNaiveCotangentToTarget hcomm i := by
  sorry

private noncomputable def stageNaiveCotangentDiagram
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    I ⥤ ChainComplex (ModuleCat S∞) ℕ where
  obj i := stageNaiveCotangentBaseChange i
  map {i j} hij := stageNaiveCotangentBaseChangeTransition hcomm hij.le
  map_id i := by
    sorry
  map_comp hij hjk := by
    sorry

private noncomputable def stageNaiveCotangentTargetCocone
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    Cocone (stageNaiveCotangentDiagram hcomm) where
  pt := @targetNaiveCotangent I _ R S _ _ _ ρ σ hcomm
  ι.app i := stageNaiveCotangentToTarget hcomm i
  ι.naturality {i j} hij := stageNaiveCotangentToTarget_compatible
    hcomm hij.le

/-- The filtered-colimit source complex built from the stagewise canonical naive cotangent
complexes `NL_{S_i⁄R_i}` after extending scalars along `S_i → S∞`. This is the source-facing
`colim NL_{S_i⁄R_i}` object of Tag `07BQ`, expressed in the common ambient category
`ChainComplex (ModuleCat S∞) ℕ`. -/
noncomputable def naiveCotangentDirectLimitModel
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    ChainComplex (ModuleCat S∞) ℕ :=
  colimit (stageNaiveCotangentDiagram hcomm)

/-- The canonical comparison from the filtered-colimit source
`colim_i (S∞ ⊗[S_i] NL_{S_i⁄R_i})` to the canonical owner `NL_{S∞⁄R∞}`. -/
noncomputable def naiveCotangentDirectLimitComparison
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    naiveCotangentDirectLimitModel hcomm ⟶
      NL(CommRingCat.ofHom
        (Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h)) :=
  by
    simpa [targetNaiveCotangent] using
      (colimit.desc (stageNaiveCotangentDiagram hcomm) (stageNaiveCotangentTargetCocone hcomm) :
        naiveCotangentDirectLimitModel hcomm ⟶
          @targetNaiveCotangent I _ R S _ _ _ ρ σ hcomm)

-- Proof sketch: the source is now the actual filtered colimit of the stagewise owner complexes.
-- On degree `0`, this is exactly the filtered-colimit comparison for Kähler differentials, while
-- degree `1` is the parallel filtered-colimit comparison for the conormal terms of the canonical
-- self-presentations. The compatibility `Extension.CotangentSpace.map_comp_cotangentComplex`
-- identifies the differentials, so these degreewise isomorphisms assemble into an isomorphism of
-- chain complexes.
/-- Lemma 10.134.9: for a directed system of ring maps `R_i → S_i`, the canonical comparison from
the filtered colimit of the stagewise naive cotangent complexes `NL_{S_i⁄R_i}` to the canonical
naive cotangent complex `NL_{S∞⁄R∞}` is an isomorphism. -/
theorem naiveCotangentDirectLimitComparison_isIso :
    IsIso (naiveCotangentDirectLimitComparison hcomm) := by
  sorry

end
