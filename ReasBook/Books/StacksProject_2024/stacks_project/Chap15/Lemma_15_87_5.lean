import Mathlib
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.Abelian.Exact
import StacksProject_2024.stacks_project.Chap13.Definition_13_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.SequentialInverseSystem
open Opposite

noncomputable section

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/- Domain-style sampling for Lemma 15.87.5:
- primary domain: the Milnor short exact sequence obtained by applying the represented Hom functor
  `Hom_D(L, -)` to a chosen Milnor triangle for a derived inverse limit in a triangulated
  category;
- sampled owner declarations:
  `CategoryTheory.HasMilnorTriangle.WithMap`,
  `preadditiveCoyonedaObj`,
  `CategoryTheory.derivedLimitDifferenceMap`,
  `CategoryTheory.IsDerivedLimit`,
  `SequentialInverseSystem.firstDerivedLimit`;
- best owner abstraction: the primitive source-facing data are the chosen Milnor triangle
  `K ⟶ ∏ K_n ⟶ ∏ K_n ⟶ K[1]`, while the intrinsic derived API is the Hom tower
  `n ↦ Hom_D(L, K_n)` and its shifted variant `n ↦ Hom_D(L, K_n[-1])`, together with their
  canonical Milnor owners `limit (Ksys ⋙ preadditiveCoyonedaObj L)` and
  `firstDerivedLimit ((Ksys ⋙ shiftFunctor D (-1 : ℤ)) ⋙ preadditiveCoyonedaObj L)`;
  the theorem surface should therefore expose those owners directly, with only the represented Hom
  functor itself appearing explicitly where no shorter ambient owner already exists;
- primitive-vs-derived split:
  primitive data are the chosen Milnor triangle and its relation `ι ≫ (1 - shift) = 0`;
  derived API are the owner-level `firstDerivedLimit` model for the shifted Hom tower
  `n ↦ Hom_D(L, K_n[-1])` and the
  comparison morphism from `Hom_D(L, K)` to `\varprojlim_n Hom_D(L, K_n)`.

Source/core/bridge triage:
- `source-facing`: the Milnor short exact sequence for `Hom_D(L, -)` attached to a chosen Milnor
  triangle;
- `core/canonical`: `derivedLimitDifferenceMap`, `IsDerivedLimit`, `preadditiveCoyonedaObj`,
  and `firstDerivedLimit`;
- `bridge/view`: the comparison morphism
  `Hom_D(L, K) ⟶ \varprojlim_n Hom_D(L, K_n)` induced by the first map of the chosen Milnor
  triangle. -/

/-- The sequential inverse system `n ↦ Hom_D(L, K_n)`. -/
private abbrev representedHomTower
    (Ksys : SequentialInverseSystem D) (L : D) :
    SequentialInverseSystem (ModuleCat (End L)ᵐᵒᵖ) :=
  Ksys ⋙ preadditiveCoyonedaObj L

/-- The sequential inverse system `n ↦ Hom_D(L, K_n[-1])`. -/
private abbrev shiftedRepresentedHomTower
    (Ksys : SequentialInverseSystem D) (L : D) :
    SequentialInverseSystem (ModuleCat (End L)ᵐᵒᵖ) :=
  (Ksys ⋙ shiftFunctor D (-1 : ℤ)) ⋙ preadditiveCoyonedaObj L

/-- Helper for Lemma 15.87.5: `Hom_D(L,-)` carries the tautological shift sequence needed for the
long exact sequence machinery. -/
private noncomputable instance preadditiveCoyonedaObj_shiftSequence (L : D) :
    (preadditiveCoyonedaObj L).ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ _

/-- Helper for Lemma 15.87.5: exactness of the represented-Hom image of a distinguished triangle
is reflected from the underlying additive-group-valued Yoneda functor. -/
private instance preadditiveCoyonedaObj_isHomological (L : D) :
    (preadditiveCoyonedaObj L).IsHomological where
  exact T hT := by
    let U : ModuleCat (End L)ᵐᵒᵖ ⥤ AddCommGrpCat := forget₂ _ _
    -- The additive-group-valued Yoneda functor is already known to be homological.
    have hExactU :
        (((shortComplexOfDistTriangle T hT).map (preadditiveCoyonedaObj L)).map U).Exact := by
      change ((shortComplexOfDistTriangle T hT).map (preadditiveCoyonedaObj L ⋙ U)).Exact
      simpa using ((preadditiveCoyoneda.obj (op L)).map_distinguished_exact T hT)
    -- The forgetful functor is faithful, so exactness in `ModuleCat` follows from exactness of
    -- the underlying sequence of additive groups.
    exact Functor.reflects_exact_of_faithful U
      ((shortComplexOfDistTriangle T hT).map (preadditiveCoyonedaObj L)) hExactU


/-- Helper for Lemma 15.87.5: the represented Hom module of a product is canonically the module
of tuples of represented Hom classes. -/
private abbrev preadditiveCoyonedaObj_product_tupleIso
    (L : D) (f : ℕ → D) [HasProduct f] :
    (preadditiveCoyonedaObj L).obj (∏ᶜ f) ≅
      ModuleCat.of (End L)ᵐᵒᵖ ((n : ℕ) → (L ⟶ f n)) :=
  -- Proof comment: the forward map records the stagewise projections, and bijectivity is the
  -- product universal property for morphisms `L ⟶ ∏ f_n`.
  (LinearEquiv.ofBijective
      (LinearMap.pi fun n ↦
        ModuleCat.Hom.hom ((preadditiveCoyonedaObj L).map (Pi.π f n))) <| by
        constructor
        · intro g h hgh
          -- Compare the two product morphisms after every projection.
          apply Pi.hom_ext
          intro n
          have hfun := congrArg (fun x : (n : ℕ) → (L ⟶ f n) ↦ x n) hgh
          simpa using hfun
        · intro x
          -- Reassemble a tuple of components into the unique map to the product.
          refine ⟨Pi.lift fun n ↦ x n, ?_⟩
          ext n
          change (Pi.lift fun n ↦ x n) ≫ Pi.π f n = x n
          rw [Pi.lift_π]).toModuleIso

/-- Helper for Lemma 15.87.5: applying `Hom_D(L, -)` to a product identifies it with the
product of the stagewise represented Hom modules. -/
private abbrev preadditiveCoyonedaObj_product_iso
    (L : D) (f : ℕ → D) [HasProduct f] :
    (preadditiveCoyonedaObj L).obj (∏ᶜ f) ≅
      ∏ᶜ (fun n ↦ (preadditiveCoyonedaObj L).obj (f n)) :=
  -- Proof comment: first move to the explicit tuple module, then use the standard `ModuleCat`
  -- product model.
  preadditiveCoyonedaObj_product_tupleIso L f ≪≫
    (ModuleCat.piIsoPi (fun n ↦ (preadditiveCoyonedaObj L).obj (f n))).symm

/-- Helper for Lemma 15.87.5: the canonical product identification for `Hom_D(L,-)` is
projectionwise the obvious represented-Hom map to the `n`-th factor. -/
private theorem preadditiveCoyonedaObj_product_iso_hom_comp_pi
    (L : D) (f : ℕ → D) [HasProduct f] (n : ℕ) :
    (preadditiveCoyonedaObj_product_iso L f).hom ≫
        Pi.π (fun n ↦ (preadditiveCoyonedaObj L).obj (f n)) n =
      (preadditiveCoyonedaObj L).map (Pi.π f n) := by
  let Z : ℕ → ModuleCat (End L)ᵐᵒᵖ := fun n ↦ (preadditiveCoyonedaObj L).obj (f n)
  have hpi :
      (ModuleCat.piIsoPi Z).symm.hom ≫ Pi.π Z n =
        ModuleCat.ofHom (LinearMap.proj n) := by
    -- The inverse of `ModuleCat.piIsoPi` is the standard product cone, so its `n`-th
    -- projection is the literal coordinate projection.
    simpa [ModuleCat.piIsoPi, Z] using
      (limit.isoLimitCone_inv_π
        (t := { cone := ModuleCat.productCone Z, isLimit := ModuleCat.productConeIsLimit Z })
        ⟨n⟩)
  -- Compare the product identification with the explicit tuple-valued linear equivalence.
  change
    (preadditiveCoyonedaObj_product_tupleIso L f).hom ≫
        (ModuleCat.piIsoPi Z).symm.hom ≫ Pi.π Z n =
      (preadditiveCoyonedaObj L).map (Pi.π f n)
  have hcomp :
      (preadditiveCoyonedaObj_product_tupleIso L f).hom ≫
          (ModuleCat.piIsoPi Z).symm.hom ≫ Pi.π Z n =
        (preadditiveCoyonedaObj_product_tupleIso L f).hom ≫
          ModuleCat.ofHom (LinearMap.proj n) := by
    let hcomp' :=
      congrArg
        (fun t ↦ (preadditiveCoyonedaObj_product_tupleIso L f).hom ≫ t)
        hpi
    simpa only [Category.assoc] using hcomp'
  rw [hcomp]
  ext g
  rfl

/-- Helper for Lemma 15.87.5: shifting an inverse-system product by `-1` still yields the
product of the shifted inverse system. -/
private theorem shiftedInverseSystem_hasProduct
    (Ksys : SequentialInverseSystem D)
    [HasProduct (inverseSystemFamily Ksys)] :
    HasProduct (inverseSystemFamily (Ksys ⋙ shiftFunctor D (-1 : ℤ))) := by
  -- Proof comment: the shift functor is an equivalence, so it preserves the chosen product and
  -- re-expresses it as the product of the shifted tower.
  refine HasLimit.mk ⟨
    Fan.mk
      ((shiftFunctor D (-1 : ℤ)).obj (∏ᶜ inverseSystemFamily Ksys))
      (fun n ↦ (shiftFunctor D (-1 : ℤ)).map (Pi.π (inverseSystemFamily Ksys) n)),
    ?_⟩
  simpa [inverseSystemFamily] using
    (isLimitOfHasProductOfPreservesLimit
      (shiftFunctor D (-1 : ℤ))
      (inverseSystemFamily Ksys))

/-- Helper for Lemma 15.87.5: the degree-zero shift of represented Hom is canonically the
original represented-Hom functor. -/
private abbrev preadditiveCoyonedaObj_shift_zero_iso
    (L : D) (X : D) :
    ((preadditiveCoyonedaObj L).shift (0 : ℤ)).obj X ≅
      (preadditiveCoyonedaObj L).obj X :=
  ((preadditiveCoyonedaObj L).isoShiftZero ℤ).app X

/-- Helper for Lemma 15.87.5: the degree-zero shift identification for represented Hom is natural
in the source morphism. -/
private theorem preadditiveCoyonedaObj_shift_zero_iso_hom_naturality
    (L : D) {X Y : D} (u : X ⟶ Y) :
    ((preadditiveCoyonedaObj L).shift (0 : ℤ)).map u ≫
        (preadditiveCoyonedaObj_shift_zero_iso L Y).hom =
      (preadditiveCoyonedaObj_shift_zero_iso L X).hom ≫
        (preadditiveCoyonedaObj L).map u := by
  -- Proof comment: this is exactly naturality of the canonical shift-zero isomorphism.
  simpa [preadditiveCoyonedaObj_shift_zero_iso] using
    (((preadditiveCoyonedaObj L).isoShiftZero ℤ).hom.naturality u)

/-- Helper for Lemma 15.87.5: the shifted Milnor product is canonically the product of the shifted
inverse system. -/
private noncomputable abbrev shiftedInverseSystem_product_iso
    (Ksys : SequentialInverseSystem D)
    [HasProduct (inverseSystemFamily Ksys)]
    [HasProduct (inverseSystemFamily (Ksys ⋙ shiftFunctor D (-1 : ℤ)))] :
    (∏ᶜ inverseSystemFamily Ksys)⟦(-1 : ℤ)⟧ ≅
      ∏ᶜ inverseSystemFamily (Ksys ⋙ shiftFunctor D (-1 : ℤ)) :=
  let G := shiftFunctor D (-1 : ℤ)
  letI : HasProduct (fun j ↦ G.obj (inverseSystemFamily Ksys j)) :=
    shiftedInverseSystem_hasProduct Ksys
  PreservesProduct.iso G (inverseSystemFamily Ksys)

/-- Helper for Lemma 15.87.5: represented Hom out of the shifted Milnor product is canonically the
ambient product of the shifted represented-Hom tower. -/
private noncomputable abbrev preadditiveCoyonedaObj_shifted_product_iso
    (Ksys : SequentialInverseSystem D) (L : D)
    [HasProduct (inverseSystemFamily Ksys)]
    [HasProduct (inverseSystemFamily (Ksys ⋙ shiftFunctor D (-1 : ℤ)))] :
    ((preadditiveCoyonedaObj L).shift (-1 : ℤ)).obj (∏ᶜ inverseSystemFamily Ksys) ≅
      ∏ᶜ inverseSystemFamily (shiftedRepresentedHomTower Ksys L) :=
  (preadditiveCoyonedaObj L).mapIso (shiftedInverseSystem_product_iso Ksys) ≪≫
    preadditiveCoyonedaObj_product_iso L
      (inverseSystemFamily (Ksys ⋙ shiftFunctor D (-1 : ℤ)))

private theorem homToDerivedLimit_comp_zero
    {Ksys : SequentialInverseSystem D} {K : D}
    [HasProduct (inverseSystemFamily Ksys)]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hι : HasMilnorTriangle.WithMap Ksys ι) :
    ι ≫ derivedLimitDifferenceMap Ksys = 0 := by
  rcases hι with ⟨δ, hδ⟩
  exact comp_distTriang_mor_zero₁₂ (Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ) hδ

private theorem homToDerivedLimitCone_naturality
    {Ksys : SequentialInverseSystem D} {K : D} (L : D)
    [HasProduct (inverseSystemFamily Ksys)]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hι : HasMilnorTriangle.WithMap Ksys ι)
    (n : ℕ) :
    (preadditiveCoyonedaObj L).map (ι ≫ Pi.π (inverseSystemFamily Ksys) n) =
      (preadditiveCoyonedaObj L).map
          (ι ≫ Pi.π (inverseSystemFamily Ksys) (n + 1)) ≫
        (Ksys ⋙ preadditiveCoyonedaObj L).map (homOfLE (Nat.le_succ n)).op := by
  let F := preadditiveCoyonedaObj L
  have hdiff : ι ≫ derivedLimitDifferenceMap Ksys = 0 :=
    homToDerivedLimit_comp_zero hι
  have hcomp : ι ≫ Pi.π (inverseSystemFamily Ksys) n =
      ι ≫ Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
        Ksys.map (homOfLE (Nat.le_succ n)).op := by
    have hπ :
        ι ≫ Pi.π (inverseSystemFamily Ksys) n -
            ι ≫ Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
              Ksys.map (homOfLE (Nat.le_succ n)).op = 0 := by
      have hπ'' :
          ι ≫ derivedLimitDifferenceMap Ksys ≫ Pi.π (inverseSystemFamily Ksys) n =
            ι ≫
              (Pi.π (inverseSystemFamily Ksys) n -
                Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
                  Ksys.map (homOfLE (Nat.le_succ n)).op) := by
        exact congrArg (fun f ↦ ι ≫ f) (derivedLimitDifferenceMap_comp_π Ksys n)
      have hπ' :
          0 =
            ι ≫ Pi.π (inverseSystemFamily Ksys) n -
              ι ≫ Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
                Ksys.map (homOfLE (Nat.le_succ n)).op := by
        rw [← Category.assoc] at hπ''
        rw [hdiff, zero_comp] at hπ''
        simpa [Preadditive.comp_sub] using hπ''
      exact hπ'.symm
    exact sub_eq_zero.mp hπ
  calc
    F.map (ι ≫ Pi.π (inverseSystemFamily Ksys) n) =
        F.map
          (ι ≫ Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
            Ksys.map (homOfLE (Nat.le_succ n)).op) := by
        exact congrArg F.map hcomp
    _ =
        F.map (ι ≫ Pi.π (inverseSystemFamily Ksys) (n + 1)) ≫
          (Ksys ⋙ F).map (homOfLE (Nat.le_succ n)).op := by
        simpa using
          (Functor.map_comp F
            (ι ≫ Pi.π (inverseSystemFamily Ksys) (n + 1))
            (Ksys.map (homOfLE (Nat.le_succ n)).op))

private def homToDerivedLimitCone
    {Ksys : SequentialInverseSystem D} {K : D} (L : D)
    [HasProduct (inverseSystemFamily Ksys)]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hι : HasMilnorTriangle.WithMap Ksys ι) :
    Cone (representedHomTower Ksys L) where
  pt := (preadditiveCoyonedaObj L).obj K
  π := NatTrans.ofOpSequence
    (fun n ↦ (preadditiveCoyonedaObj L).map (ι ≫ Pi.π (inverseSystemFamily Ksys) n))
    (fun n ↦ homToDerivedLimitCone_naturality L hι n)

private def homToDerivedLimitComparison
    {Ksys : SequentialInverseSystem D} {K : D} (L : D)
    [HasProduct (inverseSystemFamily Ksys)]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hι : HasMilnorTriangle.WithMap Ksys ι) :
    (preadditiveCoyonedaObj L).obj K ⟶
      limit (representedHomTower Ksys L) :=
  limit.lift _ (homToDerivedLimitCone L hι)

/-- Helper for Lemma 15.87.5: the canonical map from the inverse limit of a module-valued
sequential tower to its ambient product. -/
private abbrev moduleTowerLimitToProduct
    {R : Type v} [Ring R] (A : SequentialInverseSystem (ModuleCat.{v} R)) :
    limit A ⟶ ∏ᶜ inverseSystemFamily A :=
  Pi.lift fun n ↦ limit.π A (op n)

/-- Helper for Lemma 15.87.5: the canonical map from a module-valued inverse limit to its ambient
product is computed projectionwise. -/
private theorem moduleTowerLimitToProduct_π
    {R : Type v} [Ring R] (A : SequentialInverseSystem (ModuleCat.{v} R)) (n : ℕ) :
    moduleTowerLimitToProduct A ≫ Pi.π (inverseSystemFamily A) n =
      limit.π A (op n) := by
  -- The ambient product projection simply reads off the `n`-th limit projection.
  rw [moduleTowerLimitToProduct, Pi.lift_π]

/-- Helper for Lemma 15.87.5: precomposing the Milnor difference map of a module-valued tower with
any morphism into the product yields the expected projected difference formula. -/
private theorem moduleTowerDifferenceMap_π_preassoc
    {R : Type v} [Ring R] (A : SequentialInverseSystem (ModuleCat.{v} R))
    {T : ModuleCat.{v} R} (k : T ⟶ ∏ᶜ inverseSystemFamily A) (n : ℕ) :
    k ≫ derivedLimitDifferenceMap A ≫ Pi.π (inverseSystemFamily A) n =
      k ≫ Pi.π (inverseSystemFamily A) n -
        k ≫ Pi.π (inverseSystemFamily A) (n + 1) ≫
          A.transitionMap (Nat.le_succ n) := by
  -- This is the standard Milnor identity after postcomposing with the `n`-th projection.
  simpa [Category.assoc, Preadditive.comp_sub] using
    congrArg (fun t ↦ k ≫ t) (derivedLimitDifferenceMap_comp_π A n)

/-- Helper for Lemma 15.87.5: the inverse limit of a module-valued tower lies in the kernel of
its Milnor difference map. -/
private theorem moduleTowerLimitToProduct_comp_difference
    {R : Type v} [Ring R] (A : SequentialInverseSystem (ModuleCat.{v} R)) :
    moduleTowerLimitToProduct A ≫ derivedLimitDifferenceMap A = 0 := by
  -- Compare the Milnor relation after each projection of the ambient product.
  apply Pi.hom_ext
  intro n
  calc
    (moduleTowerLimitToProduct A ≫ derivedLimitDifferenceMap A) ≫
        Pi.π (inverseSystemFamily A) n =
      moduleTowerLimitToProduct A ≫ Pi.π (inverseSystemFamily A) n -
        moduleTowerLimitToProduct A ≫ Pi.π (inverseSystemFamily A) (n + 1) ≫
          A.transitionMap (Nat.le_succ n) := by
            simp [Category.assoc, derivedLimitDifferenceMap_comp_π]
    _ =
      limit.π A (op n) -
        moduleTowerLimitToProduct A ≫ Pi.π (inverseSystemFamily A) (n + 1) ≫
          A.transitionMap (Nat.le_succ n) := by
            rw [moduleTowerLimitToProduct_π]
    _ =
      limit.π A (op n) -
        limit.π A (op (n + 1)) ≫ A.transitionMap (Nat.le_succ n) := by
            have hπsucc :
                moduleTowerLimitToProduct A ≫ Pi.π (inverseSystemFamily A) (n + 1) ≫
                  A.transitionMap (Nat.le_succ n) =
                    limit.π A (op (n + 1)) ≫ A.transitionMap (Nat.le_succ n) := by
              simpa [Category.assoc] using
                congrArg
                  (fun t ↦ t ≫ A.transitionMap (Nat.le_succ n))
                  (moduleTowerLimitToProduct_π A (n + 1))
            rw [hπsucc]
    _ = 0 := by
          rw [limit.w A ((homOfLE (Nat.le_succ n)).op)]
          simp
    _ = 0 ≫ Pi.π (inverseSystemFamily A) n := by
          simp

/-- Helper for Lemma 15.87.5: the inverse-limit object of a module-valued tower is the kernel of
its Milnor difference map. -/
private noncomputable def moduleTowerLimitToProduct_is_kernel
    {R : Type v} [Ring R] (A : SequentialInverseSystem (ModuleCat.{v} R)) :
    IsLimit
      (KernelFork.ofι
        (moduleTowerLimitToProduct A)
        (moduleTowerLimitToProduct_comp_difference A)) := by
  -- A morphism into the Milnor product lies in the kernel exactly when its coordinates form a
  -- compatible cone over the tower.
  refine KernelFork.IsLimit.ofι (moduleTowerLimitToProduct A)
    (moduleTowerLimitToProduct_comp_difference A)
    (fun {W} s hs ↦
      let stageHom : ∀ n : ℕ, W ⟶ A.obj (op n) :=
        fun n ↦ s ≫ Pi.π (inverseSystemFamily A) n
      have hstageHom_naturality :
          ∀ n : ℕ,
            stageHom n = stageHom (n + 1) ≫ A.transitionMap (Nat.le_succ n) := by
        intro n
        have hproj :
            s ≫ Pi.π (inverseSystemFamily A) n -
              s ≫ Pi.π (inverseSystemFamily A) (n + 1) ≫
                A.transitionMap (Nat.le_succ n) = 0 := by
          have hproj' := congrArg (fun t ↦ t ≫ Pi.π (inverseSystemFamily A) n) hs
          simpa [moduleTowerDifferenceMap_π_preassoc] using hproj'
        simpa [SequentialInverseSystem.transitionMap] using (sub_eq_zero.mp hproj)
      let c : Cone A := {
        pt := W
        π := NatTrans.ofOpSequence stageHom hstageHom_naturality
      }
      limit.lift A c)
    (fun {W} s hs ↦ by
      let stageHom : ∀ n : ℕ, W ⟶ A.obj (op n) :=
        fun n ↦ s ≫ Pi.π (inverseSystemFamily A) n
      have hstageHom_naturality :
          ∀ n : ℕ,
            stageHom n = stageHom (n + 1) ≫ A.transitionMap (Nat.le_succ n) := by
        intro n
        have hproj :
            s ≫ Pi.π (inverseSystemFamily A) n -
              s ≫ Pi.π (inverseSystemFamily A) (n + 1) ≫
                A.transitionMap (Nat.le_succ n) = 0 := by
          have hproj' := congrArg (fun t ↦ t ≫ Pi.π (inverseSystemFamily A) n) hs
          simpa [moduleTowerDifferenceMap_π_preassoc] using hproj'
        simpa [SequentialInverseSystem.transitionMap] using (sub_eq_zero.mp hproj)
      let c : Cone A := {
        pt := W
        π := NatTrans.ofOpSequence stageHom hstageHom_naturality
      }
      -- Compare the lifted cone map after each ambient product projection.
      apply Pi.hom_ext
      intro n
      calc
        (limit.lift A c ≫ moduleTowerLimitToProduct A) ≫
            Pi.π (inverseSystemFamily A) n =
          limit.lift A c ≫ limit.π A (op n) := by
            rw [Category.assoc, moduleTowerLimitToProduct_π]
        _ = s ≫ Pi.π (inverseSystemFamily A) n := by
            simpa [c, stageHom] using limit.lift_π (F := A) (c := c) (j := op n))
    (fun {W} s hs m hm ↦ by
      let stageHom : ∀ n : ℕ, W ⟶ A.obj (op n) :=
        fun n ↦ s ≫ Pi.π (inverseSystemFamily A) n
      have hstageHom_naturality :
          ∀ n : ℕ,
            stageHom n = stageHom (n + 1) ≫ A.transitionMap (Nat.le_succ n) := by
        intro n
        have hproj :
            s ≫ Pi.π (inverseSystemFamily A) n -
              s ≫ Pi.π (inverseSystemFamily A) (n + 1) ≫
                A.transitionMap (Nat.le_succ n) = 0 := by
          have hproj' := congrArg (fun t ↦ t ≫ Pi.π (inverseSystemFamily A) n) hs
          simpa [moduleTowerDifferenceMap_π_preassoc] using hproj'
        simpa [SequentialInverseSystem.transitionMap] using (sub_eq_zero.mp hproj)
      let c : Cone A := {
        pt := W
        π := NatTrans.ofOpSequence stageHom hstageHom_naturality
      }
      apply limit.hom_ext
      intro n
      have hproj := congrArg (fun t ↦ t ≫ Pi.π (inverseSystemFamily A) n.unop) hm
      simpa [c, stageHom, Category.assoc, moduleTowerLimitToProduct_π] using hproj)

/-- Helper for Lemma 15.87.5: the Milnor comparison before factoring through the inverse limit is
the ambient product map with components `Hom_D(L, K) ⟶ Hom_D(L, K_n)`. -/
private def homToDerivedLimitAmbientMap
    {Ksys : SequentialInverseSystem D} {K : D} (L : D)
    [HasProduct (inverseSystemFamily Ksys)]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (_hι : HasMilnorTriangle.WithMap Ksys ι) :
    (preadditiveCoyonedaObj L).obj K ⟶
      ∏ᶜ inverseSystemFamily (representedHomTower Ksys L) :=
  Pi.lift fun n ↦
    (preadditiveCoyonedaObj L).map (ι ≫ Pi.π (inverseSystemFamily Ksys) n)

/-- Helper for Lemma 15.87.5: the ambient Milnor comparison is computed projectionwise. -/
private theorem homToDerivedLimitAmbientMap_π
    {Ksys : SequentialInverseSystem D} {K : D} (L : D)
    [HasProduct (inverseSystemFamily Ksys)]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hι : HasMilnorTriangle.WithMap Ksys ι) (n : ℕ) :
    homToDerivedLimitAmbientMap L hι ≫
        Pi.π (inverseSystemFamily (representedHomTower Ksys L)) n =
      (preadditiveCoyonedaObj L).map
        (ι ≫ Pi.π (inverseSystemFamily Ksys) n) := by
  -- The `n`-th product projection recovers the stagewise represented-Hom comparison.
  rw [homToDerivedLimitAmbientMap, Pi.lift_π]

/-- Helper for Lemma 15.87.5: the ambient Milnor comparison lands in the kernel of the represented
Milnor difference map. -/
private theorem homToDerivedLimitAmbientMap_comp_difference
    {Ksys : SequentialInverseSystem D} {K : D} (L : D)
    [HasProduct (inverseSystemFamily Ksys)]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hι : HasMilnorTriangle.WithMap Ksys ι) :
    homToDerivedLimitAmbientMap L hι ≫
        derivedLimitDifferenceMap (representedHomTower Ksys L) = 0 := by
  -- Compare after each stage projection and reduce to the cone naturality relation.
  apply Pi.hom_ext
  intro n
  have hnat :
      (preadditiveCoyonedaObj L).map (ι ≫ Pi.π (inverseSystemFamily Ksys) n) =
        (preadditiveCoyonedaObj L).map
            (ι ≫ Pi.π (inverseSystemFamily Ksys) (n + 1)) ≫
          (representedHomTower Ksys L).transitionMap (Nat.le_succ n) := by
    -- The represented Hom cone over the Milnor product is compatible with transition maps.
    simpa [representedHomTower, SequentialInverseSystem.transitionMap] using
      homToDerivedLimitCone_naturality L hι n
  have hcompat :
      homToDerivedLimitAmbientMap L hι ≫
          Pi.π (inverseSystemFamily (representedHomTower Ksys L)) n =
        homToDerivedLimitAmbientMap L hι ≫
            Pi.π (inverseSystemFamily (representedHomTower Ksys L)) (n + 1) ≫
          (representedHomTower Ksys L).transitionMap (Nat.le_succ n) := by
    exact
      (homToDerivedLimitAmbientMap_π L hι n).trans <|
        hnat.trans <|
          (by
            symm
            simpa [Category.assoc] using
              congrArg
                (fun t ↦ t ≫ (representedHomTower Ksys L).transitionMap (Nat.le_succ n))
                (homToDerivedLimitAmbientMap_π L hι (n + 1)))
  calc
    (homToDerivedLimitAmbientMap L hι ≫
        derivedLimitDifferenceMap (representedHomTower Ksys L)) ≫
          Pi.π (inverseSystemFamily (representedHomTower Ksys L)) n =
      homToDerivedLimitAmbientMap L hι ≫
        Pi.π (inverseSystemFamily (representedHomTower Ksys L)) n -
          homToDerivedLimitAmbientMap L hι ≫
            Pi.π (inverseSystemFamily (representedHomTower Ksys L)) (n + 1) ≫
              (representedHomTower Ksys L).transitionMap (Nat.le_succ n) := by
        simpa [Category.assoc, Preadditive.comp_sub, SequentialInverseSystem.transitionMap] using
          congrArg
            (fun t ↦ homToDerivedLimitAmbientMap L hι ≫ t)
            (derivedLimitDifferenceMap_comp_π (representedHomTower Ksys L) n)
    _ = 0 := by
        exact sub_eq_zero.mpr hcompat
    _ = 0 ≫ Pi.π (inverseSystemFamily (representedHomTower Ksys L)) n := by
        exact
          (zero_comp :
            (0 :
              (preadditiveCoyonedaObj L).obj K ⟶
                ∏ᶜ inverseSystemFamily (representedHomTower Ksys L)) ≫
                Pi.π (inverseSystemFamily (representedHomTower Ksys L)) n = 0).symm

/-- Helper for Lemma 15.87.5: the existing Milnor comparison map is the canonical factorization
of the ambient product map through the inverse-limit kernel object. -/
private theorem homToDerivedLimitComparison_comp_limitToProduct
    {Ksys : SequentialInverseSystem D} {K : D} (L : D)
    [HasProduct (inverseSystemFamily Ksys)]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hι : HasMilnorTriangle.WithMap Ksys ι) :
    homToDerivedLimitComparison L hι ≫
        moduleTowerLimitToProduct (R := (End L)ᵐᵒᵖ) (representedHomTower Ksys L) =
      homToDerivedLimitAmbientMap L hι := by
  -- Compare the two maps after each product projection of the ambient kernel object.
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, moduleTowerLimitToProduct_π, homToDerivedLimitAmbientMap_π]
  -- The comparison map was defined by the universal property of the inverse limit cone.
  simpa [homToDerivedLimitComparison, homToDerivedLimitCone] using
    (limit.lift_π
      (F := representedHomTower Ksys L)
      (c := homToDerivedLimitCone L hι)
      (j := op n))

/-- Helper for Lemma 15.87.5: the inverse product comparison for represented Hom conjugates the
Milnor difference map on a tower to the Milnor difference map on the represented-Hom tower. -/
private theorem preadditiveCoyonedaObj_product_iso_inv_comp_difference
    (L : D) (A : SequentialInverseSystem D)
    [HasProduct (inverseSystemFamily A)] :
    (preadditiveCoyonedaObj_product_iso L (inverseSystemFamily A)).inv ≫
        (preadditiveCoyonedaObj L).map (derivedLimitDifferenceMap A) =
      derivedLimitDifferenceMap (A ⋙ preadditiveCoyonedaObj L) ≫
        (preadditiveCoyonedaObj_product_iso L (inverseSystemFamily A)).inv := by
  let F := preadditiveCoyonedaObj L
  let e := preadditiveCoyonedaObj_product_iso L (inverseSystemFamily A)
  let Z : ℕ → ModuleCat (End L)ᵐᵒᵖ := fun n ↦ (preadditiveCoyonedaObj L).obj (inverseSystemFamily A n)
  -- Proof comment: move back to the ambient product of represented Hom modules and compare the
  -- two Milnor endomorphisms after each stage projection.
  apply (cancel_mono e.hom).1
  apply Pi.hom_ext
  intro n
  have hproj :
      (preadditiveCoyonedaObj_product_iso L (inverseSystemFamily A)).hom ≫
          Pi.π Z n =
        F.map (Pi.π (inverseSystemFamily A) n) := by
    simpa [Z] using
      preadditiveCoyonedaObj_product_iso_hom_comp_pi L (inverseSystemFamily A) n
  have hπ :
      e.inv ≫ F.map (Pi.π (inverseSystemFamily A) n) =
        Pi.π Z n := by
    -- Replace the represented-Hom projection with the owner-level product comparison, then
    -- cancel `e`.
    calc
      e.inv ≫ F.map (Pi.π (inverseSystemFamily A) n) =
        e.inv ≫ ((preadditiveCoyonedaObj_product_iso L (inverseSystemFamily A)).hom ≫ Pi.π Z n) := by
          rw [hproj.symm]
      _ = Pi.π Z n := by
          simpa [e, Category.assoc] using
            (Iso.inv_hom_id_assoc e (Pi.π Z n))
  have hproj_succ :
      (preadditiveCoyonedaObj_product_iso L (inverseSystemFamily A)).hom ≫
          Pi.π Z (n + 1) =
        F.map (Pi.π (inverseSystemFamily A) (n + 1)) := by
    simpa [Z] using
      preadditiveCoyonedaObj_product_iso_hom_comp_pi L (inverseSystemFamily A) (n + 1)
  have hπsucc :
      e.inv ≫ F.map (Pi.π (inverseSystemFamily A) (n + 1)) =
        Pi.π Z (n + 1) := by
    -- The same projection comparison works at the successor stage.
    calc
      e.inv ≫ F.map (Pi.π (inverseSystemFamily A) (n + 1)) =
        e.inv ≫ ((preadditiveCoyonedaObj_product_iso L (inverseSystemFamily A)).hom ≫
          Pi.π Z (n + 1)) := by
          rw [hproj_succ.symm]
      _ = Pi.π Z (n + 1) := by
          simpa [e, Category.assoc] using
            (Iso.inv_hom_id_assoc e (Pi.π Z (n + 1)))
  have hπsucc_assoc :
      e.inv ≫ F.map (Pi.π (inverseSystemFamily A) (n + 1)) ≫
          F.map (A.transitionMap (Nat.le_succ n)) =
        Pi.π Z (n + 1) ≫ F.map (A.transitionMap (Nat.le_succ n)) := by
    simpa [Category.assoc] using
      congrArg
        (fun t ↦ t ≫ F.map (A.transitionMap (Nat.le_succ n)))
        hπsucc
  calc
    ((e.inv ≫ F.map (derivedLimitDifferenceMap A)) ≫ e.hom) ≫
        Pi.π Z n =
      e.inv ≫ F.map (derivedLimitDifferenceMap A) ≫
        F.map (Pi.π (inverseSystemFamily A) n) := by
        rw [Category.assoc, Category.assoc]
        rw [hproj]
    _ = e.inv ≫ F.map (derivedLimitDifferenceMap A ≫ Pi.π (inverseSystemFamily A) n) := by
        rw [← Functor.map_comp]
    _ = e.inv ≫
          F.map
            (Pi.π (inverseSystemFamily A) n -
              Pi.π (inverseSystemFamily A) (n + 1) ≫
                A.transitionMap (Nat.le_succ n)) := by
        rw [derivedLimitDifferenceMap_comp_π]
    _ =
        (e.inv ≫ F.map (Pi.π (inverseSystemFamily A) n)) -
          (e.inv ≫
            (F.map (Pi.π (inverseSystemFamily A) (n + 1)) ≫
              F.map (A.transitionMap (Nat.le_succ n)))) := by
        rw [Functor.map_sub, Preadditive.comp_sub, Functor.map_comp]
    _ =
        Pi.π Z n -
          (Pi.π Z (n + 1) ≫
            F.map (A.transitionMap (Nat.le_succ n))) := by
        rw [hπ, hπsucc_assoc]
    _ = derivedLimitDifferenceMap (A ⋙ F) ≫ Pi.π Z n := by
        simpa [Z, SequentialInverseSystem.transitionMap] using
          (derivedLimitDifferenceMap_comp_π (A ⋙ F) n).symm
    _ = ((derivedLimitDifferenceMap (A ⋙ F) ≫ e.inv) ≫ e.hom) ≫
          Pi.π Z n := by
        simpa [Z, Category.assoc, e] using
          congrArg
            (fun t ↦ derivedLimitDifferenceMap (A ⋙ F) ≫ t)
            (Iso.inv_hom_id_assoc e (Pi.π Z n)).symm

/-- Helper for Lemma 15.87.5: the shifted-product comparison for the Milnor product is
projectionwise the shifted stage projection. -/
private theorem shiftedInverseSystem_product_iso_hom_comp_π
    (Ksys : SequentialInverseSystem D)
    [HasProduct (inverseSystemFamily Ksys)]
    [HasProduct (inverseSystemFamily (Ksys ⋙ shiftFunctor D (-1 : ℤ)))] (n : ℕ) :
    (shiftedInverseSystem_product_iso Ksys).hom ≫
        Pi.π (inverseSystemFamily (Ksys ⋙ shiftFunctor D (-1 : ℤ))) n =
      (shiftFunctor D (-1 : ℤ)).map (Pi.π (inverseSystemFamily Ksys) n) := by
  let G := shiftFunctor D (-1 : ℤ)
  letI : HasProduct (fun j ↦ G.obj (inverseSystemFamily Ksys j)) :=
    shiftedInverseSystem_hasProduct Ksys
  -- Proof comment: `shiftedInverseSystem_product_iso` is the standard preserved-product
  -- comparison for the shift functor, so its projections are given by `piComparison_comp_π`.
  change CategoryTheory.Limits.piComparison G (inverseSystemFamily Ksys) ≫
      Pi.π (fun j ↦ G.obj (inverseSystemFamily Ksys j)) n =
    G.map (Pi.π (inverseSystemFamily Ksys) n)
  simpa [G, inverseSystemFamily] using
    (CategoryTheory.Limits.piComparison_comp_π G (inverseSystemFamily Ksys) n)

/-- Helper for Lemma 15.87.5: after identifying represented Hom out of the Milnor product with
the ambient product tower, the map induced by `ι` is the ambient comparison morphism. -/
private theorem preadditiveCoyonedaObj_map_ι_comp_product_iso_hom
    {Ksys : SequentialInverseSystem D} {K : D} (L : D)
    [HasProduct (inverseSystemFamily Ksys)]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hι : HasMilnorTriangle.WithMap Ksys ι) :
    (preadditiveCoyonedaObj L).map ι ≫
        (preadditiveCoyonedaObj_product_iso L (inverseSystemFamily Ksys)).hom =
      homToDerivedLimitAmbientMap L hι := by
  -- Proof comment: compare both morphisms after each projection; both give precomposition by the
  -- component map `K ⟶ K_n` of the Milnor triangle.
  apply Pi.hom_ext
  intro n
  let Z : ℕ → ModuleCat (End L)ᵐᵒᵖ :=
    fun m ↦ (preadditiveCoyonedaObj L).obj (inverseSystemFamily Ksys m)
  have hambient :
      homToDerivedLimitAmbientMap L hι ≫ Pi.π Z n =
        (preadditiveCoyonedaObj L).map
          (ι ≫ Pi.π (inverseSystemFamily Ksys) n) := by
    simpa [Z, representedHomTower] using homToDerivedLimitAmbientMap_π L hι n
  -- Each stage projection is literally precomposition with the component `K ⟶ K_n`.
  calc
    ((preadditiveCoyonedaObj L).map ι ≫
        (preadditiveCoyonedaObj_product_iso L (inverseSystemFamily Ksys)).hom) ≫
          Pi.π Z n =
      (preadditiveCoyonedaObj L).map ι ≫
        (preadditiveCoyonedaObj L).map (Pi.π (inverseSystemFamily Ksys) n) := by
        simpa [Z] using
          congrArg
            (fun t ↦ (preadditiveCoyonedaObj L).map ι ≫ t)
            (preadditiveCoyonedaObj_product_iso_hom_comp_pi L (inverseSystemFamily Ksys) n)
    _ =
        (preadditiveCoyonedaObj L).map
          (ι ≫ Pi.π (inverseSystemFamily Ksys) n) := by
        simpa using
          (Functor.map_comp
            (preadditiveCoyonedaObj L)
            ι
            (Pi.π (inverseSystemFamily Ksys) n)).symm
    _ = homToDerivedLimitAmbientMap L hι ≫ Pi.π Z n := by
        simpa [Z] using hambient.symm

-- Proof sketch: apply the homological functor `Hom_D(L, -)` to the chosen Milnor triangle
-- `K ⟶ ∏ K_n ⟶ ∏ K_n ⟶ K[1]`. The first map gives the comparison morphism from `Hom_D(L, K)` to
-- the inverse limit of the Hom tower, while the left term is the standard cokernel model for
-- `R^1 \!\varprojlim_n Hom_D(L, K_n[-1])`, canonically exposed as
-- `(shiftedRepresentedHomTower Ksys L).firstDerivedLimit`.
private theorem homToDerivedLimit_shortExact_of_triangle
    {Ksys : SequentialInverseSystem D} {K : D}
    [HasProduct (inverseSystemFamily Ksys)]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hι : HasMilnorTriangle.WithMap Ksys ι)
    (L : D) :
    ∃ (ι' :
        (shiftedRepresentedHomTower Ksys L).firstDerivedLimit ⟶
          (preadditiveCoyonedaObj L).obj K)
      (h :
        ι' ≫ homToDerivedLimitComparison L hι = 0),
      (ShortComplex.mk ι' (homToDerivedLimitComparison L hι) h).ShortExact := by
  let hMilnor : HasMilnorTriangle.WithMap Ksys ι := hι
  rcases hι with ⟨δ, hδ⟩
  let b := homToDerivedLimitAmbientMap L hMilnor
  have hb :
      b ≫ derivedLimitDifferenceMap (representedHomTower Ksys L) = 0 :=
    homToDerivedLimitAmbientMap_comp_difference L hMilnor
  have hπ :
      homToDerivedLimitComparison L hMilnor ≫
          moduleTowerLimitToProduct (R := (End L)ᵐᵒᵖ) (representedHomTower Ksys L) = b :=
    homToDerivedLimitComparison_comp_limitToProduct L hMilnor
  have hkernel :
      IsLimit
        (KernelFork.ofι
          (moduleTowerLimitToProduct (R := (End L)ᵐᵒᵖ) (representedHomTower Ksys L))
          (moduleTowerLimitToProduct_comp_difference
            (R := (End L)ᵐᵒᵖ) (representedHomTower Ksys L))) :=
    moduleTowerLimitToProduct_is_kernel (R := (End L)ᵐᵒᵖ) (representedHomTower Ksys L)
  -- Route correction: the kernel side is now normalized canonically, so the remaining source
  -- proof step is exactly the degree `(-1,0)` long exact row and its descent through the cokernel
  -- owner `firstDerivedLimit`.
  -- TODO: normalize the degree `(-1,0)` five-term row of
  -- `Functor.homologySequenceComposableArrows₅_exact`. The stage-projection formula for the
  -- shifted product comparison is now available as
  -- `shiftedInverseSystem_product_iso_hom_comp_π`; the remaining blocker is the owner-level
  -- conjugation of the shifted Milnor difference map through
  -- `preadditiveCoyonedaObj_shifted_product_iso`, followed by packaging the transported row into
  -- the exact short complexes needed for the cokernel/kernel descent.
  sorry

-- Proof sketch: unpack the chosen Milnor triangle from `hK` and apply the previous bridge-level
-- result. The public surface keeps only the canonical owner hypothesis `IsDerivedLimit Ksys K`,
-- while the specific Milnor presentation remains internal.
/-- Lemma 15.87.5: if `K` is a derived limit of a sequential inverse system `(K_n)_n`, then for
every object `L` there is a short exact sequence
`0 ⟶ R^1 \!\varprojlim \operatorname{Hom}_D(L, K_n[-1]) ⟶ \operatorname{Hom}_D(L, K) ⟶
\varprojlim_n \operatorname{Hom}_D(L, K_n) ⟶ 0`. -/
theorem homToDerivedLimit_hasMilnorShortExactSequence
    (Ksys : SequentialInverseSystem D) {K : D}
    (hK : IsDerivedLimit Ksys K) (L : D) :
    ∃ (ι :
        (shiftedRepresentedHomTower Ksys L).firstDerivedLimit ⟶
          (preadditiveCoyonedaObj L).obj K)
      (π :
        (preadditiveCoyonedaObj L).obj K ⟶
          limit (representedHomTower Ksys L))
      (h :
        ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  rcases hK with ⟨_, ⟨ι, δ, hδ⟩⟩
  let hι : HasMilnorTriangle.WithMap Ksys ι := ⟨δ, hδ⟩
  rcases homToDerivedLimit_shortExact_of_triangle hι L with ⟨ι', h, hshort⟩
  exact ⟨ι', homToDerivedLimitComparison L hι, h, hshort⟩

end

end CategoryTheory
