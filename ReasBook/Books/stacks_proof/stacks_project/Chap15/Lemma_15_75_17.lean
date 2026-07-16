import Mathlib
import stacks_proof.stacks_project.Chap13.Definition_13_33_1
import stacks_proof.stacks_project.Chap13.Definition_13_34_1
import stacks_proof.stacks_project.Chap13.Remark_13_33_2
import stacks_proof.stacks_project.Chap15.Lemma_15_74_5
import stacks_proof.stacks_project.Chap15.Lemma_15_75_15

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open MonoidalClosed
open Opposite
open scoped DerivedInternalHom
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "RHomPkg" => MonoidalClosed DMod

/- Domain-style sampling for Lemma 15.75.17:
- primary domain: derived duality for perfect objects in `D(A)` together with the Chapter 13
  homotopy-colimit / derived-limit owners for sequential diagrams;
- sampled owner declarations:
  `CategoryTheory.SequentialInverseSystem`,
  `CategoryTheory.MonoidalClosed.internalHom`,
  `CategoryTheory.tensor_derivedDual_iso_derivedInternalHom`,
  `CategoryTheory.derivedDualMap`,
  `CategoryTheory.IsHomotopyColimitOf`,
  `CategoryTheory.IsDerivedLimit`;
- best owner abstraction:
  `source-facing`: the tensor-dual inverse system `n ↦ E ⊗_A^{\mathbf L} K_n^\vee` from the
    Stacks statement, now exposed directly as a `SequentialInverseSystem DMod`, together with the
    derived-limit conclusion for `RHom_A(K, E)`;
  `core/canonical`: the sequential inverse-system owner `SequentialInverseSystem DMod`, the
    source-variable internal-Hom owner `MonoidalClosed.internalHom.flip.obj E`, the notation
    `RHom[H](K, E)`, and the Chapter 13 predicates `IsHomotopyColimitOf` and `IsDerivedLimit`;
  `bridge/view`: the inverse-system isomorphism
    `derivedDualTensorInverseSystemIsoInternalHomTower`, whose components are the perfect-stage
    comparison isomorphisms from Lemma `15.75.15`.

Primitive data are only the sequential diagram `K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯`, the chosen monoidal-closed
owner `H`, and the fixed tensor target `E`. The source-facing tensor-dual inverse system is the
right owner for the textbook statement, while the canonical owner-level inverse system is the
source-variable internal-Hom tower `(Functor.ofSequence f).op ⋙
MonoidalClosed.internalHom.flip.obj E`. Lemma `15.75.15` supplies the stagewise bridge between
these two owners.
-/

/-- The source-facing inverse system
`\cdots \to E \otimes_A^{\mathbf L} K_{n + 1}^\vee \to E \otimes_A^{\mathbf L} K_n^\vee`
attached to a sequential diagram `K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯` in `D(A)`. -/
abbrev derivedDualTensorInverseSystem
    (H : RHomPkg) (E : DMod) (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1)) :
    SequentialInverseSystem DMod :=
  let X : ℕ → DMod := fun n ↦ E ⊗[A]^L (K n)ᵛ⟮H⟯
  Functor.ofOpSequence <| fun n ↦
    show X (n + 1) ⟶ X n from
      (derivedTensorProductMap H (derivedDualMap H (f n))).app E

/-- Helper for Lemma 15.75.17: the perfect-stage tensor/Hom comparison intertwines the successor
maps of the tensor-dual inverse system and the internal-Hom tower. -/
private theorem derivedDualTensorInverseSystem_component_naturality
    (H : RHomPkg) (E : DMod) (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1))
    (hperfect : ∀ n, DerivedCategory.IsPerfect (K n)) (n : ℕ) :
    (derivedDualTensorInverseSystem H E K f).stepMap n ≫
        (asIso (derivedDualTensorComparison H (K n))).app E =
      (asIso (derivedDualTensorComparison H (K (n + 1)))).app E ≫
        (((Functor.ofSequence f).op ⋙ (MonoidalClosed.internalHom).flip.obj E).map
          ((homOfLE (Nat.le_succ n)).op)) := by
  letI : RHomPkg := H
  letI : IsIso (derivedDualTensorComparison H (K n)) :=
    tensor_derivedDual_iso_derivedInternalHom H (hperfect n)
  letI : IsIso (derivedDualTensorComparison H (K (n + 1))) :=
    tensor_derivedDual_iso_derivedInternalHom H (hperfect (n + 1))
  -- Proof comment: reduce to the successor-square comparing the source-variable tensor/Hom
  -- comparison with contravariant functoriality in the source object.
  simpa [SequentialInverseSystem.stepMap, derivedDualTensorInverseSystem,
    Functor.ofSequence_map_homOfLE_succ, derivedDualMap, derivedDual, derivedInternalHomMap,
    Category.assoc] using
    (derivedInternalHom_tensor_left_comparison_natural_source H E ringSingle (f n)).w

/-- Helper for Lemma 15.75.17: the stagewise perfect comparison maps assemble into a morphism from
the tensor-dual inverse system to the owner-level internal-Hom tower. -/
private noncomputable def derivedDualTensorInverseSystemHomInternalHomTower
    (H : RHomPkg) (E : DMod) (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1))
    (hperfect : ∀ n, DerivedCategory.IsPerfect (K n)) :
    letI := H
    derivedDualTensorInverseSystem H E K f ⟶
      (Functor.ofSequence f).op ⋙ (MonoidalClosed.internalHom).flip.obj E :=
  NatTrans.ofOpSequence
    (fun n ↦
      letI : IsIso (derivedDualTensorComparison H (K n)) :=
        tensor_derivedDual_iso_derivedInternalHom H (hperfect n)
      (asIso (derivedDualTensorComparison H (K n))).app E)
    (derivedDualTensorInverseSystem_component_naturality H E K f hperfect)

/-- For a sequential diagram of perfect objects, the source-facing tensor-dual inverse system is
canonically isomorphic to the owner-level internal-Hom tower
`(Functor.ofSequence f).op ⋙ MonoidalClosed.internalHom.flip.obj E`. -/
noncomputable def derivedDualTensorInverseSystemIsoInternalHomTower
    (H : RHomPkg) (E : DMod) (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1))
    (hperfect : ∀ n, DerivedCategory.IsPerfect (K n)) :
    letI := H
    derivedDualTensorInverseSystem H E K f ≅
      (Functor.ofSequence f).op ⋙ (MonoidalClosed.internalHom).flip.obj E := by
  letI : RHomPkg := H
  refine NatIso.ofComponents
    (fun n ↦
      letI : IsIso (derivedDualTensorComparison H (K n.unop)) :=
        tensor_derivedDual_iso_derivedInternalHom H (hperfect n.unop)
      (asIso (derivedDualTensorComparison H (K n.unop))).app E)
    (fun {_ _} g ↦ by
      -- Proof comment: the successor-step compatibility has already been assembled into a tower
      -- morphism, so arbitrary-arrow naturality follows from the `ofOpSequence` constructor.
      simpa using
        (derivedDualTensorInverseSystemHomInternalHomTower H E K f hperfect).naturality g)

/-- Helper for Lemma 15.75.17: for fixed `E`, the source-variable internal-Hom functor
`RHom_A(-, E)` preserves countable products on the opposite derived category. -/
private theorem internalHomFlipObj_preservesLimitsOfShape
    (H : RHomPkg) (E : DMod) :
    PreservesLimitsOfShape (Discrete ℕ)
      ((MonoidalClosed.internalHom).flip.obj E : DModᵒᵖ ⥤ DMod) :=
  -- Proof comment: for a fixed target `E`, the source-variable internal-Hom owner is a right
  -- adjoint, so countable-product preservation is already available from instance search.
  infer_instance

/-- Helper for Lemma 15.75.17: `RHom_A(∐ K_n, E)` identifies with the product of the internal-Hom
tower `n ↦ RHom_A(K_n, E)`. -/
private noncomputable abbrev internalHom_coproduct_iso_product
    (H : RHomPkg) (E : DMod) (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1))
    [HasCoproduct (Functor.ofSequence f).obj] :
    RHom[H](∐ (Functor.ofSequence f).obj, E) ≅
      ∏ᶜ inverseSystemFamily (((Functor.ofSequence f).op ⋙ (MonoidalClosed.internalHom).flip.obj E)) :=
  let F : DModᵒᵖ ⥤ DMod := (MonoidalClosed.internalHom).flip.obj E
  letI : PreservesLimitsOfShape (Discrete ℕ) F :=
    internalHomFlipObj_preservesLimitsOfShape H E
  -- Proof comment: first rewrite the opposite of the chosen coproduct as the canonical product in
  -- `D(A)ᵒᵖ`, then apply the standard preserved-product comparison for `F`.
  F.mapIso (Limits.opCoproductIsoProduct (Functor.ofSequence f).obj) ≪≫
    PreservesProduct.iso F (fun n ↦ Opposite.op (K n))

/-- Helper for Lemma 15.75.17: the product comparison for `RHom_A(∐ K_n, E)` recovers the
projection to the `n`th stage `RHom_A(K_n, E)`. -/
private theorem internalHom_coproduct_iso_product_hom_comp_π
    (H : RHomPkg) (E : DMod) (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1))
    [HasCoproduct (Functor.ofSequence f).obj] (n : ℕ) :
    (internalHom_coproduct_iso_product H E K f).hom ≫
        Pi.π
          (inverseSystemFamily
            (((Functor.ofSequence f).op ⋙ (MonoidalClosed.internalHom).flip.obj E)))
          n =
      ((MonoidalClosed.internalHom).flip.obj E).map
        (Opposite.op (Sigma.ι (Functor.ofSequence f).obj n)) :=
  let F : DModᵒᵖ ⥤ DMod := (MonoidalClosed.internalHom).flip.obj E
  letI : PreservesLimitsOfShape (Discrete ℕ) F :=
    internalHomFlipObj_preservesLimitsOfShape H E
  -- Proof comment: expand the comparison into the opposite coproduct/product isomorphism
  -- followed by `PreservesProduct.iso`, then read off the `n`th projection.
  change
    ((F.mapIso (Limits.opCoproductIsoProduct (Functor.ofSequence f).obj) ≪≫
        PreservesProduct.iso F (fun m ↦ Opposite.op (K m))).hom) ≫
      Pi.π
        (inverseSystemFamily (((Functor.ofSequence f).op ⋙ (MonoidalClosed.internalHom).flip.obj E)))
        n =
      F.map (Opposite.op (Sigma.ι (Functor.ofSequence f).obj n))
  rw [Iso.trans_hom, Category.assoc]
  calc
    (F.mapIso (Limits.opCoproductIsoProduct (Functor.ofSequence f).obj)).hom ≫
        (PreservesProduct.iso F (fun m ↦ Opposite.op (K m))).hom ≫
          Pi.π
            (inverseSystemFamily
              (((Functor.ofSequence f).op ⋙ (MonoidalClosed.internalHom).flip.obj E)))
            n =
      (F.mapIso (Limits.opCoproductIsoProduct (Functor.ofSequence f).obj)).hom ≫
        F.map (Pi.π (fun m ↦ Opposite.op (K m)) n) := by
          simpa [PreservesProduct.iso_hom, inverseSystemFamily, F, Category.assoc] using
            (piComparison_comp_π F (fun m ↦ Opposite.op (K m)) n)
    _ =
      F.map
        ((Limits.opCoproductIsoProduct (Functor.ofSequence f).obj).hom ≫
          Pi.π (fun m ↦ Opposite.op (K m)) n) := by
            simp [Functor.map_comp, Category.assoc]
    _ = F.map (Opposite.op (Sigma.ι (Functor.ofSequence f).obj n)) := by
          rw [Limits.opCoproductIsoProduct_hom_comp_π]

/-- Helper for Lemma 15.75.17: under the coproduct/product comparison, the telescope endomorphism
of `∐ K_n` becomes the Milnor difference map of the internal-Hom tower. -/
private theorem internalHom_coproduct_iso_product_comm_telescope
    (H : RHomPkg) (E : DMod) (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1))
    [HasCoproduct (Functor.ofSequence f).obj] :
    ((MonoidalClosed.internalHom).flip.obj E).map
        (Opposite.op (sequentialTelescopeMap (Functor.ofSequence f))) ≫
      (internalHom_coproduct_iso_product H E K f).hom =
    (internalHom_coproduct_iso_product H E K f).hom ≫
      derivedLimitDifferenceMap
        (((Functor.ofSequence f).op ⋙ (MonoidalClosed.internalHom).flip.obj E)) :=
  let F : DModᵒᵖ ⥤ DMod := (MonoidalClosed.internalHom).flip.obj E
  -- Proof comment: compare both morphisms after the `n`th product projection; the telescope map
  -- on the coproduct becomes the Milnor difference map under the product comparison.
  apply Pi.hom_ext
  intro n
  calc
    (((MonoidalClosed.internalHom).flip.obj E).map
        (Opposite.op (sequentialTelescopeMap (Functor.ofSequence f))) ≫
      (internalHom_coproduct_iso_product H E K f).hom) ≫
        Pi.π
          (inverseSystemFamily
            (((Functor.ofSequence f).op ⋙ (MonoidalClosed.internalHom).flip.obj E)))
          n =
      F.map
        (Opposite.op
          (Sigma.ι (Functor.ofSequence f).obj n ≫
            sequentialTelescopeMap (Functor.ofSequence f))) := by
          simp [Category.assoc, internalHom_coproduct_iso_product_hom_comp_π, F,
            Functor.map_comp]
    _ =
      F.map
        (Opposite.op
          (Sigma.ι (Functor.ofSequence f).obj n -
            (Functor.ofSequence f).map (homOfLE (Nat.le_succ n)) ≫
              Sigma.ι (Functor.ofSequence f).obj (n + 1))) := by
          congr 1
          exact Sigma.ι_comp_sequentialTelescopeMap (K := Functor.ofSequence f) n
    _ =
      ((internalHom_coproduct_iso_product H E K f).hom ≫
        derivedLimitDifferenceMap
          (((Functor.ofSequence f).op ⋙ (MonoidalClosed.internalHom).flip.obj E))) ≫
          Pi.π
            (inverseSystemFamily
              (((Functor.ofSequence f).op ⋙ (MonoidalClosed.internalHom).flip.obj E)))
            n := by
          simp only [Category.assoc, internalHom_coproduct_iso_product_hom_comp_π,
            derivedLimitDifferenceMap_comp_π, Preadditive.comp_sub, Functor.map_sub,
            Functor.map_comp, Functor.ofSequence_map_homOfLE_succ, F]

/-- Helper for Lemma 15.75.17: instance search already supplies exactness for the fixed-target
source-variable internal-Hom owner on the opposite derived category. -/
private theorem internalHomFlipObj_isTriangulated
    (H : RHomPkg) (E : DMod) :
    (((MonoidalClosed.internalHom).flip.obj E : DModᵒᵖ ⥤ DMod).IsTriangulated) := by
  let F : DModᵒᵖ ⥤ DMod := (MonoidalClosed.internalHom).flip.obj E
  letI : F.CommShift ℤ := inferInstance
  -- Proof comment: once the shift-compatibility instance is available, the triangulated exactness
  -- of the fixed-target internal-Hom owner is also provided canonically.
  infer_instance

/-- Helper for Lemma 15.75.17: a source-style homotopy-colimit presentation of `Khocolim`
maps under `RHom_A(-, E)` to the Milnor triangle of the internal-Hom tower. -/
private theorem internalHomTower_withMap_of_presentation
    (H : RHomPkg) (E : DMod) (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1)) {Khocolim : DMod}
    [HasCoproduct (Functor.ofSequence f).obj]
    (ι : ∀ n, K n ⟶ Khocolim)
    (c : Khocolim ⟶ ∐ fun n ↦ K n⟦(1 : ℤ)⟧)
    (hcompat : ∀ n, (Functor.ofSequence f).map (homOfLE (Nat.le_succ n)) ≫ ι (n + 1) = ι n)
    (htriangle :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) (Limits.Sigma.desc ι)
        (c ≫
          (PreservesCoproduct.iso (shiftFunctor DMod (1 : ℤ)) (Functor.ofSequence f).obj).inv) ∈
            distTriang DMod) :
    HasMilnorTriangle.WithMap
      (((Functor.ofSequence f).op ⋙ (MonoidalClosed.internalHom).flip.obj E))
      (((MonoidalClosed.internalHom).flip.obj E).map (Opposite.op (Limits.Sigma.desc ι)) ≫
        (internalHom_coproduct_iso_product H E K f).hom) := by
  -- Route correction: the remaining blocker is no longer the coproduct/product bridge. The only
  -- missing step is to map the chosen telescope triangle through `internalHom.flip.obj E`,
  -- rewrite the two coproduct vertices by `internalHom_coproduct_iso_product`, and package the
  -- result as `HasMilnorTriangle.WithMap`.
  let F : DModᵒᵖ ⥤ DMod := (MonoidalClosed.internalHom).flip.obj E
  letI : F.IsTriangulated := internalHomFlipObj_isTriangulated H E
  let Tsrc : Triangle DMod :=
    Triangle.mk
      (sequentialTelescopeMap (Functor.ofSequence f))
      (Limits.Sigma.desc ι)
      (c ≫
        (PreservesCoproduct.iso (shiftFunctor DMod (1 : ℤ)) (Functor.ofSequence f).obj).inv)
  let Top : Triangle DModᵒᵖ :=
    (triangleOpEquivalence DMod).functor.obj (Opposite.op Tsrc)
  have hTop : Top ∈ distTriang DModᵒᵖ := by
    -- Proof comment: transport the chosen homotopy-colimit presentation triangle to the opposite
    -- category, which is the source category of the contravariant internal-Hom functor.
    simpa [Top, Tsrc] using
      (CategoryTheory.Pretriangulated.op_distinguished Tsrc htriangle)
  let δ₀ : RHom[H](∐ (Functor.ofSequence f).obj, E) ⟶ RHom[H](Khocolim, E)⟦(1 : ℤ)⟧ :=
    (F.mapTriangle.obj Top).mor₃
  let T : Triangle DMod :=
    Triangle.mk
      (F.map (Opposite.op (Limits.Sigma.desc ι)))
      (F.map (Opposite.op (sequentialTelescopeMap (Functor.ofSequence f))))
      δ₀
  have hT : T ∈ distTriang DMod := by
    -- Proof comment: apply `RHom_A(-, E)` to the opposite presentation triangle.
    simpa [T, Top, Tsrc, δ₀] using F.map_distinguished Top hTop
  let p : RHom[H](∐ (Functor.ofSequence f).obj, E) ≅
      ∏ᶜ inverseSystemFamily (((Functor.ofSequence f).op ⋙ F)) :=
    internalHom_coproduct_iso_product H E K f
  let δ : ∏ᶜ inverseSystemFamily (((Functor.ofSequence f).op ⋙ F)) ⟶
      RHom[H](Khocolim, E)⟦(1 : ℤ)⟧ :=
    p.inv ≫ δ₀
  let T' : Triangle DMod :=
    Triangle.mk
      (F.map (Opposite.op (Limits.Sigma.desc ι)) ≫ p.hom)
      (derivedLimitDifferenceMap (((Functor.ofSequence f).op ⋙ F)))
      δ
  have hIso : T ≅ T' := by
    -- Proof comment: rewrite both coproduct-valued vertices to the product tower and identify
    -- the mapped telescope endomorphism with the Milnor difference map.
    refine Triangle.isoMk _ _ (Iso.refl _) p p ?_ ?_ ?_
    · simp [T, T', δ]
    · simpa [T, T', p] using internalHom_coproduct_iso_product_comm_telescope H E K f
    · simp [T, T', δ]
  have hT' : T' ∈ distTriang DMod := by
    -- Proof comment: distinguishedness is invariant under triangle isomorphism.
    exact isomorphic_distinguished _ hT _ hIso.symm
  exact ⟨δ, by simpa [T', δ, p, F] using hT'⟩

/-- Helper for Lemma 15.75.17: the product isomorphism attached to an isomorphism of towers
intertwines the stage projections. -/
private noncomputable def tower_product_iso
    {Ksys Lsys : SequentialInverseSystem DMod}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) :
    (∏ᶜ inverseSystemFamily Ksys) ≅ ∏ᶜ inverseSystemFamily Lsys := by
  let eFamily :
      Discrete.functor (inverseSystemFamily Ksys) ≅
        Discrete.functor (inverseSystemFamily Lsys) :=
    Discrete.natIso fun n : Discrete ℕ ↦ e.app (Opposite.op n.as)
  -- Proof comment: transport the discrete product diagram stagewise along the tower isomorphism.
  exact HasLimit.isoOfNatIso eFamily

/-- Helper for Lemma 15.75.17: the product isomorphism attached to an isomorphism of towers
intertwines the stage projections. -/
private theorem tower_product_iso_hom_comp_π
    {Ksys Lsys : SequentialInverseSystem DMod}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) (n : ℕ) :
    (tower_product_iso e).hom ≫ Pi.π (inverseSystemFamily Lsys) n =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (Opposite.op n)).hom := by
  let eFamily :
      Discrete.functor (inverseSystemFamily Ksys) ≅
        Discrete.functor (inverseSystemFamily Lsys) :=
    Discrete.natIso fun m : Discrete ℕ ↦ e.app (Opposite.op m.as)
  -- Proof comment: `tower_product_iso` is the `HasLimit.isoOfNatIso` comparison, so its effect on
  -- each projection is the standard `limMap_π` formula.
  simpa [tower_product_iso, eFamily] using
    limMap_π (α := eFamily.hom) (j := Discrete.mk n)

/-- Helper for Lemma 15.75.17: the product isomorphism attached to a tower isomorphism
conjugates the Milnor difference maps. -/
private theorem tower_product_iso_hom_comm_difference
    {Ksys Lsys : SequentialInverseSystem DMod}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) :
    (tower_product_iso e).hom ≫ derivedLimitDifferenceMap Lsys =
      derivedLimitDifferenceMap Ksys ≫ (tower_product_iso e).hom := by
  apply Pi.hom_ext
  intro n
  -- Proof comment: compare both composites on the `n`th factor and use the stagewise naturality
  -- of the tower isomorphism.
  calc
    (tower_product_iso e).hom ≫ derivedLimitDifferenceMap Lsys ≫
        Pi.π (inverseSystemFamily Lsys) n =
      (tower_product_iso e).hom ≫
        (Pi.π (inverseSystemFamily Lsys) n -
          Pi.π (inverseSystemFamily Lsys) (n + 1) ≫
            Lsys.transitionMap (Nat.le_succ n)) := by
          rw [derivedLimitDifferenceMap_comp_π]
    _ =
      (tower_product_iso e).hom ≫ Pi.π (inverseSystemFamily Lsys) n -
        (tower_product_iso e).hom ≫
          Pi.π (inverseSystemFamily Lsys) (n + 1) ≫
            Lsys.transitionMap (Nat.le_succ n) := by
          rw [Preadditive.comp_sub]
    _ =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (Opposite.op n)).hom -
        Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          (e.app (Opposite.op (n + 1))).hom ≫
            Lsys.transitionMap (Nat.le_succ n) := by
          rw [tower_product_iso_hom_comp_π, tower_product_iso_hom_comp_π]
    _ =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (Opposite.op n)).hom -
        Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          Ksys.transitionMap (Nat.le_succ n) ≫
            (e.app (Opposite.op n)).hom := by
          congr 1
          rw [Category.assoc]
          exact congrArg
            (fun t ↦ Pi.π (inverseSystemFamily Ksys) (n + 1) ≫ t)
            (e.hom.naturality ((homOfLE (Nat.le_succ n)).op)).symm
    _ =
      (Pi.π (inverseSystemFamily Ksys) n -
        Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          Ksys.transitionMap (Nat.le_succ n)) ≫
        (e.app (Opposite.op n)).hom := by
          rw [Preadditive.sub_comp]
          simp [Category.assoc]
    _ =
      derivedLimitDifferenceMap Ksys ≫ Pi.π (inverseSystemFamily Ksys) n ≫
        (e.app (Opposite.op n)).hom := by
          rw [← derivedLimitDifferenceMap_comp_π_assoc]
    _ =
      ((derivedLimitDifferenceMap Ksys ≫ (tower_product_iso e).hom) ≫
        Pi.π (inverseSystemFamily Lsys) n) := by
          rw [Category.assoc, ← tower_product_iso_hom_comp_π, ← Category.assoc]

/-- Helper for Lemma 15.75.17: a derived-limit witness transports across an isomorphism of towers
when the limiting object is kept fixed. -/
private theorem isDerivedLimit_of_tower_iso
    {Ksys Lsys : SequentialInverseSystem DMod} {K : DMod}
    (e : Ksys ≅ Lsys)
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit Lsys K := by
  rcases hK with ⟨hP, ι, δ, hδ⟩
  letI : HasProduct (inverseSystemFamily Ksys) := hP
  let eFamily :
      Discrete.functor (inverseSystemFamily Ksys) ≅
        Discrete.functor (inverseSystemFamily Lsys) :=
    Discrete.natIso fun n : Discrete ℕ ↦ e.app (Opposite.op n.as)
  let hQ : HasProduct (inverseSystemFamily Lsys) := by
    exact hasLimit_of_iso eFamily
  letI : HasProduct (inverseSystemFamily Lsys) := hQ
  let p : (∏ᶜ inverseSystemFamily Ksys) ≅ ∏ᶜ inverseSystemFamily Lsys :=
    tower_product_iso e
  let T : Triangle DMod :=
    Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ
  let T' : Triangle DMod :=
    Triangle.mk (ι ≫ p.hom) (derivedLimitDifferenceMap Lsys) (p.inv ≫ δ)
  have hIso : T ≅ T' := by
    -- Proof comment: rewrite the original Milnor triangle through the product comparison
    -- isomorphism of the two towers.
    refine Triangle.isoMk _ _ (Iso.refl _) p p ?_ ?_ ?_
    · simp [T, T']
    · simpa [T, T'] using (tower_product_iso_hom_comm_difference e).symm
    · simp [T, T']
  have hT' : T' ∈ distTriang DMod := by
    exact isomorphic_distinguished _ hδ _ hIso.symm
  exact ⟨hQ, ι ≫ p.hom, p.inv ≫ δ, hT'⟩

/-- Lemma 15.75.17: if `K` is a chosen homotopy colimit of a sequential system of perfect objects
`K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯` in `D(A)`, then for every `E : D(A)` the derived internal Hom
`R\mathrm{Hom}_A(K,E)` is a derived limit of the source-facing inverse system
`n ↦ E \otimes_A^{\mathbf L} K_n^\vee`, where `K_n^\vee = R\mathrm{Hom}_A(K_n, A)`.
Lemma `15.75.15` supplies the stagewise bridge from this tensor-dual tower to the canonical
inverse system `n ↦ R\mathrm{Hom}_A(K_n, E)`. -/
-- Proof sketch: for each stage `n`, perfectness makes the canonical comparison
-- `E ⊗^L_A K_n^\vee ⟶ RHom_A(K_n, E)` an isomorphism by Lemma `15.75.15`. After replacing the
-- source-facing tower by the canonically isomorphic owner-level internal-Hom tower
-- `(Functor.ofSequence f).op ⋙ MonoidalClosed.internalHom.flip.obj E`, the source-variable
-- internal-Hom owner `MonoidalClosed.internalHom.flip.obj E` sends the homotopy-colimit triangle
-- for `K` to the Milnor triangle computing the derived limit of `RHom_A(K_n, E)`.
theorem derivedInternalHom_isDerivedLimit_of_homotopyColimit
    (H : RHomPkg) (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1)) {Khocolim : DMod}
    [HasCoproduct (Functor.ofSequence f).obj]
    (hperfect : ∀ n, DerivedCategory.IsPerfect (K n))
    (hKhocolim : IsHomotopyColimitOf (Functor.ofSequence f) Khocolim) (E : DMod) :
    IsDerivedLimit
      (derivedDualTensorInverseSystem H E K f)
      (RHom[H](Khocolim, E)) := by
  let F : DModᵒᵖ ⥤ DMod := (MonoidalClosed.internalHom).flip.obj E
  have hInternalHom :
      IsDerivedLimit
        (((Functor.ofSequence f).op ⋙ F))
        (RHom[H](Khocolim, E)) := by
    obtain ⟨ι, c, hcompat, htriangle⟩ :=
      IsHomotopyColimitOf.exists_presentation (S := Functor.ofSequence f) hKhocolim
    let _ : HasProduct (inverseSystemFamily (((Functor.ofSequence f).op ⋙ F))) := inferInstance
    have hWithMap :
        HasMilnorTriangle.WithMap
          (((Functor.ofSequence f).op ⋙ F))
          (F.map (Opposite.op (Limits.Sigma.desc ι)) ≫
            (internalHom_coproduct_iso_product H E K f).hom) :=
      internalHomTower_withMap_of_presentation H E K f ι c hcompat htriangle
    -- Proof comment: once the source-variable tower has its Milnor triangle, Definition 13.34.1
    -- packages `RHom_A(K,E)` as the derived limit of that tower.
    exact ⟨inferInstance, hWithMap.hasMilnorTriangle (((Functor.ofSequence f).op ⋙ F))⟩
  -- Proof comment: Lemma `15.75.15` identifies the source-facing tensor-dual tower with the
  -- owner-level internal-Hom tower, so the derived-limit witness transports across that tower
  -- isomorphism.
  exact
    isDerivedLimit_of_tower_iso
      (derivedDualTensorInverseSystemIsoInternalHomTower H E K f hperfect).symm
      hInternalHom

end

end CategoryTheory
