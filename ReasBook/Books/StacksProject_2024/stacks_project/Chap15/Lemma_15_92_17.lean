import Mathlib
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Triangulated.Yoneda
import StacksProject_2024.stacks_project.Chap13.Lemma_13_35_7
import StacksProject_2024.stacks_project.Chap15.Situation_15_92_15
import StacksProject_2024.stacks_project.Chap15.Lemma_15_92_16
import StacksProject_2024.stacks_project.Chap15.«15_74_0_2»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.SequentialInverseSystem
open ComplexShape
open Opposite
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A] {r : ℕ}

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "DSeq" => DerivedCategory (SequentialInverseSystem (ModuleCat A))

/- Domain-style sampling for Lemma 15.92.17:
- primary domain: the canonical comparison from `K` to a chosen derived limit of the powered
  Koszul tensor tower in `D(A)`;
- sampled owner declarations:
  `derivedCompletionKoszulPowerTensorDerivedInverseSystem`,
  `CategoryTheory.IsDerivedLimit`,
  `CategoryTheory.HasMilnorTriangle.WithMap`,
  `K.IsDerivedCompleteWithRespectTo I`;
- best owner abstraction: the Chapter `13` owner
  `HasMilnorTriangle.WithMap
    (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) ι`, together with the
  source-facing stagewise equations asserting that a map `c : K ⟶ L` induces the canonical stage
  maps coming from the augmentation `A[0] ⟶ K_n^\bullet`;
- primitive data: the tower
  `derivedCompletionKoszulPowerTensorDerivedInverseSystem K f`, a chosen product map
  `ι : L ⟶ ∏ K_n`, a Milnor-triangle witness
  `HasMilnorTriangle.WithMap (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) ι`,
  a comparison morphism `c : K ⟶ L`, and the canonical stage maps from `K` into the tensor
  stages;
- derived API: the induced `IsDerivedLimit` witness and the isomorphism criterion for `c`.

Source/core/bridge triage:
- `source-facing`: the comparison predicate below for maps from `K` to a chosen derived limit of
  the powered Koszul tensor tower;
- `core/canonical`: `derivedCompletionKoszulPowerTensorDerivedInverseSystem K f`,
  `IsDerivedLimit`, `HasMilnorTriangle.WithMap`, and
  `K.IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f))`;
- `bridge/view`: the explicit stagewise formula against the canonical map
  `K ⟶ K_n^\bullet \otimes_A^{\mathbf L} K`. -/

/-- The canonical map from `K` to the `n`th stage
`K_n^\bullet \otimes_A^{\mathbf L} K` of the powered Koszul tensor tower. -/
abbrev derivedCompletionKoszulPowerTensorToStage
    (K : DMod) (f : Fin r → A) (n : ℕ) :
    K ⟶ (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f).obj (op n) :=
  (singleZeroDerivedTensorIso K).inv ≫
    (derivedTensorProduct K).map
      (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
          (ModuleCat.of A A)).hom ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.extendSingleIso embeddingDownNat (ModuleCat.of A A)
              (0 : ℕ) (0 : ℤ) rfl).inv ≫
            HomologicalComplex.extendMap (koszulPowerAugmentation f n) embeddingDownNat))

/-- A morphism `c : K ⟶ L` is the canonical comparison from `K` to a chosen derived limit of the
powered Koszul tensor tower if `L` sits in the Milnor triangle of that tower and the stage
projections recover the canonical maps
`K ⟶ K_n^\bullet \otimes_A^{\mathbf L} K`. -/
def IsDerivedCompletionKoszulPowerTensorComparison
    (f : Fin r → A) (K L : DMod) (c : K ⟶ L) : Prop :=
  ∃ _ : HasProduct
      (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)),
    ∃ ι :
        L ⟶
          ∏ᶜ inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f),
      HasMilnorTriangle.WithMap
          (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) ι ∧
        ∀ n : ℕ,
          c ≫ ι ≫
              Pi.π
                (inverseSystemFamily
                  (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
                n =
            derivedCompletionKoszulPowerTensorToStage K f n

/-- A derived-completion comparison presents its target as a derived limit of the powered Koszul
tensor tower. -/
theorem IsDerivedCompletionKoszulPowerTensorComparison.isDerivedLimit
    {f : Fin r → A} {K L : DMod} {c : K ⟶ L}
    (hc : IsDerivedCompletionKoszulPowerTensorComparison f K L c) :
    IsDerivedLimit (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) L := by
  rcases hc with ⟨hP, _, hι, _⟩
  let _ : HasProduct
      (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)) := hP
  exact ⟨hP, hι.hasMilnorTriangle (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)⟩

/-- Helper for Lemma 15.92.17: the canonical stage maps from `K` into the powered Koszul tensor
tower form a cone over the tower transitions. -/
private theorem derivedCompletionKoszulPowerTensorToStage_comp_transition
    (K : DMod) (f : Fin r → A) (n : ℕ) :
    derivedCompletionKoszulPowerTensorToStage K f (n + 1) ≫
        (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f).transitionMap (Nat.le_succ n) =
      derivedCompletionKoszulPowerTensorToStage K f n := by
  -- Proof comment: apply the derived tensor functor to the augmentation square from
  -- Situation `15.92.15`; the source leg is the identity on `A[0]`, so the stage maps are
  -- compatible with the successor transition in the tower.
  simpa [derivedCompletionKoszulPowerTensorToStage,
    derivedCompletionKoszulPowerTensorDerivedInverseSystem, SequentialInverseSystem.transitionMap,
    Functor.comp_obj, Functor.comp_map, Category.assoc] using
    congrArg
      (fun g ↦
        (singleZeroDerivedTensorIso K).inv ≫
          (derivedTensorProduct K).map
            (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
                (ModuleCat.of A A)).hom ≫
              DerivedCategory.Q.map
                ((HomologicalComplex.extendSingleIso embeddingDownNat (ModuleCat.of A A)
                    (0 : ℕ) (0 : ℤ) rfl).inv ≫
                  HomologicalComplex.extendMap g embeddingDownNat)))
      (koszulPowerAugmentation_naturality f n).w

/-- Helper for Lemma 15.92.17: the canonical map from `K` into the Milnor product of the powered
Koszul tensor tower satisfies the equalizer relation for the Milnor difference map. -/
private theorem derivedCompletionKoszulPowerTensor_product_map_comp_difference_zero
    (K : DMod) (f : Fin r → A)
    [HasProduct
      (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))] :
    Pi.lift (fun n ↦ derivedCompletionKoszulPowerTensorToStage K f n) ≫
        derivedLimitDifferenceMap
          (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) =
      0 := by
  -- Proof comment: compare both sides after each stage projection; the component formula for the
  -- Milnor difference map collapses because the stage maps already form a cone over the tower.
  apply Pi.hom_ext
  intro n
  calc
    Pi.lift (fun m ↦ derivedCompletionKoszulPowerTensorToStage K f m) ≫
        derivedLimitDifferenceMap
          (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) ≫
        Pi.π
          (inverseSystemFamily
            (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
          n =
      derivedCompletionKoszulPowerTensorToStage K f n -
        derivedCompletionKoszulPowerTensorToStage K f (n + 1) ≫
          (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f).transitionMap
            (Nat.le_succ n) := by
          simp [Category.assoc, derivedLimitDifferenceMap_comp_π]
    _ = derivedCompletionKoszulPowerTensorToStage K f n -
        derivedCompletionKoszulPowerTensorToStage K f n := by
          rw [derivedCompletionKoszulPowerTensorToStage_comp_transition]
    _ = 0 := by simp

/-- Helper for Lemma 15.92.17: any chosen Milnor model of the powered Koszul tensor tower admits
the canonical comparison map from `K`, obtained by exactness at the Milnor product. -/
private theorem exists_derivedCompletionKoszulPowerTensorComparison_of_isDerivedLimit
    (f : Fin r → A) (K : DMod) {L : DMod}
    (hL : IsDerivedLimit (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) L) :
    ∃ c : K ⟶ L, IsDerivedCompletionKoszulPowerTensorComparison f K L c := by
  rcases hL with ⟨hP, ⟨ι, δ, hT⟩⟩
  let _ :
      HasProduct
        (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)) := hP
  let α :
      K ⟶ ∏ᶜ inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) :=
    Pi.lift (fun n ↦ derivedCompletionKoszulPowerTensorToStage K f n)
  have hαzero :
      α ≫
          derivedLimitDifferenceMap
            (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) =
        0 := by
    -- Proof comment: the canonical cone satisfies the Milnor equalizer relation proved just
    -- above.
    simpa [α] using
      derivedCompletionKoszulPowerTensor_product_map_comp_difference_zero K f
  let T : Triangle DMod :=
    Triangle.mk ι
      (derivedLimitDifferenceMap
        (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
      δ
  obtain ⟨c, hc⟩ := Triangle.coyoneda_exact₂ (T := T) hT α (by simpa [T] using hαzero)
  refine ⟨c, ?_⟩
  refine ⟨hP, ι, ⟨δ, hT⟩, ?_⟩
  intro n
  -- Proof comment: project the equality `c ≫ ι = α` to the `n`th stage and unfold the product
  -- map `α`.
  have hproj :
      c ≫ ι ≫
          Pi.π
            (inverseSystemFamily
              (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
            n =
        α ≫
          Pi.π
            (inverseSystemFamily
              (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
            n := by
    simpa [T, α, Category.assoc] using
      congrArg
        (fun g ↦
          g ≫
            Pi.π
              (inverseSystemFamily
                (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
              n)
        hc
  simpa [α, Category.assoc] using hproj

/-- Helper for Lemma 15.92.17: derived completeness in the derived category is invariant under
isomorphism. -/
lemma isDerivedCompleteWithRespectTo_iff_of_iso
    {I : Ideal A} {K L : DMod} (e : K ≅ L) :
    K.IsDerivedCompleteWithRespectTo I ↔ L.IsDerivedCompleteWithRespectTo I := by
  constructor
  · intro hK
    -- Proof comment: postcompose with `e.inv` to move maps into `L` back to maps into `K`,
    -- where derived completeness gives a subsingleton hom-set.
    intro f hf E
    have hSub :
        Subsingleton
          ((((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory).obj
              E) ⟶ K) :=
      hK f hf E
    refine ⟨fun g₁ g₂ ↦ ?_⟩
    have hEq : g₁ ≫ e.inv = g₂ ≫ e.inv := @Subsingleton.elim _ hSub _ _
    simpa [Category.assoc] using congrArg (fun h ↦ h ≫ e.hom) hEq
  · intro hL
    -- Proof comment: the reverse implication is the same transport argument along `e.hom`.
    intro f hf E
    have hSub :
        Subsingleton
          ((((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory).obj
              E) ⟶ L) :=
      hL f hf E
    refine ⟨fun g₁ g₂ ↦ ?_⟩
    have hEq : g₁ ≫ e.hom = g₂ ≫ e.hom := @Subsingleton.elim _ hSub _ _
    simpa [Category.assoc] using congrArg (fun h ↦ h ≫ e.inv) hEq

/-- Helper for Lemma 15.92.17: the represented-Hom inverse system attached to a sequential tower
in `D(A)`. -/
private abbrev representedHomTower
    (Ksys : SequentialInverseSystem DMod) (L : DMod) :
    SequentialInverseSystem (ModuleCat (End L)ᵐᵒᵖ) :=
  Ksys ⋙ preadditiveCoyonedaObj L

/-- Helper for Lemma 15.92.17: a Milnor presentation forces the product map to satisfy the
standard equalizer relation. -/
private theorem homToDerivedLimit_comp_zero
    {Ksys : SequentialInverseSystem DMod} {K : DMod}
    [HasProduct (inverseSystemFamily Ksys)]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hι : HasMilnorTriangle.WithMap Ksys ι) :
    ι ≫ derivedLimitDifferenceMap Ksys = 0 := by
  rcases hι with ⟨δ, hδ⟩
  exact comp_distTriang_mor_zero₁₂ (Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ) hδ

/-- Helper for Lemma 15.92.17: the represented-Hom cone induced by a Milnor presentation is
compatible with the transition maps of the represented-Hom tower. -/
private theorem homToDerivedLimitCone_naturality
    {Ksys : SequentialInverseSystem DMod} {K : DMod} (L : DMod)
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
  have hcomp :
      ι ≫ Pi.π (inverseSystemFamily Ksys) n =
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
        exact congrArg (fun t ↦ ι ≫ t) (derivedLimitDifferenceMap_comp_π Ksys n)
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
  -- Proof comment: first recover the stagewise cone relation in `D(A)`, then apply the
  -- represented-Hom functor and rewrite functoriality of composition.
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

/-- Helper for Lemma 15.92.17: a Milnor presentation induces the canonical represented-Hom cone
over the tower `n ↦ Hom(L, K_n)`. -/
private def homToDerivedLimitCone
    {Ksys : SequentialInverseSystem DMod} {K : DMod} (L : DMod)
    [HasProduct (inverseSystemFamily Ksys)]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hι : HasMilnorTriangle.WithMap Ksys ι) :
    Cone (representedHomTower Ksys L) where
  pt := (preadditiveCoyonedaObj L).obj K
  π := NatTrans.ofOpSequence
    (fun n ↦ (preadditiveCoyonedaObj L).map (ι ≫ Pi.π (inverseSystemFamily Ksys) n))
    (fun n ↦ homToDerivedLimitCone_naturality L hι n)

/-- Helper for Lemma 15.92.17: the represented-Hom comparison from `Hom(L, K)` to the inverse
limit of `Hom(L, K_n)`. -/
private def homToDerivedLimitComparison
    {Ksys : SequentialInverseSystem DMod} {K : DMod} (L : DMod)
    [HasProduct (inverseSystemFamily Ksys)]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hι : HasMilnorTriangle.WithMap Ksys ι) :
    (preadditiveCoyonedaObj L).obj K ⟶
      limit (representedHomTower Ksys L) :=
  limit.lift _ (homToDerivedLimitCone L hι)

/-- Helper for Lemma 15.92.17: the canonical map from the inverse limit of a module-valued
sequential tower to its ambient product. -/
private abbrev moduleTowerLimitToProduct
    {R : Type u} [Ring R] (A : SequentialInverseSystem (ModuleCat.{u} R)) :
    limit A ⟶ ∏ᶜ inverseSystemFamily A :=
  Pi.lift fun n ↦ limit.π A (op n)

/-- Helper for Lemma 15.92.17: the ambient-product map of a module-valued inverse limit is read
off by its stage projections. -/
private theorem moduleTowerLimitToProduct_π
    {R : Type u} [Ring R] (A : SequentialInverseSystem (ModuleCat.{u} R)) (n : ℕ) :
    moduleTowerLimitToProduct A ≫ Pi.π (inverseSystemFamily A) n =
      limit.π A (op n) := by
  -- Proof comment: the ambient product projection simply recovers the `n`th limit projection.
  rw [moduleTowerLimitToProduct, Pi.lift_π]

/-- Helper for Lemma 15.92.17: precomposing the Milnor difference map with a map into the ambient
product yields the expected stagewise difference formula. -/
private theorem moduleTowerDifferenceMap_π_preassoc
    {R : Type u} [Ring R] (A : SequentialInverseSystem (ModuleCat.{u} R))
    {T : ModuleCat.{u} R} (k : T ⟶ ∏ᶜ inverseSystemFamily A) (n : ℕ) :
    k ≫ derivedLimitDifferenceMap A ≫ Pi.π (inverseSystemFamily A) n =
      k ≫ Pi.π (inverseSystemFamily A) n -
        k ≫ Pi.π (inverseSystemFamily A) (n + 1) ≫
          A.transitionMap (Nat.le_succ n) := by
  -- Proof comment: this is the standard Milnor identity after postcomposing with the `n`th
  -- projection.
  simpa [Category.assoc, Preadditive.comp_sub] using
    congrArg (fun t ↦ k ≫ t) (derivedLimitDifferenceMap_comp_π A n)

/-- Helper for Lemma 15.92.17: the canonical map from a module-valued inverse limit to its
ambient product lands in the kernel of the Milnor difference map. -/
private theorem moduleTowerLimitToProduct_comp_difference
    {R : Type u} [Ring R] (A : SequentialInverseSystem (ModuleCat.{u} R)) :
    moduleTowerLimitToProduct A ≫ derivedLimitDifferenceMap A = 0 := by
  -- Proof comment: compare the Milnor relation after each projection of the ambient product.
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

/-- Helper for Lemma 15.92.17: the inverse-limit object of a module-valued sequential tower is
the kernel of its Milnor difference map. -/
private theorem moduleTowerLimitToProduct_is_kernel
    {R : Type u} [Ring R] (A : SequentialInverseSystem (ModuleCat.{u} R)) :
    IsLimit
      (KernelFork.ofι
        (moduleTowerLimitToProduct A)
        (moduleTowerLimitToProduct_comp_difference A)) := by
  -- Proof comment: a morphism into the ambient product lies in the kernel precisely when its
  -- stage components form a compatible cone over the tower.
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
      -- Proof comment: compare the kernel lift with the original map after each product
      -- projection.
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
      -- Proof comment: uniqueness follows from the universal property of the inverse limit.
      apply limit.hom_ext
      intro n
      have hproj := congrArg (fun t ↦ t ≫ Pi.π (inverseSystemFamily A) n.unop) hm
      simpa [c, stageHom, Category.assoc, moduleTowerLimitToProduct_π] using hproj)

/-- Helper for Lemma 15.92.17: before factoring through the represented-Hom inverse limit, the
comparison map is simply the ambient product map with stagewise represented-Hom components. -/
private def homToDerivedLimitAmbientMap
    {Ksys : SequentialInverseSystem DMod} {K : DMod} (L : DMod)
    [HasProduct (inverseSystemFamily Ksys)]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (_hι : HasMilnorTriangle.WithMap Ksys ι) :
    (preadditiveCoyonedaObj L).obj K ⟶
      ∏ᶜ inverseSystemFamily (representedHomTower Ksys L) :=
  Pi.lift fun n ↦
    (preadditiveCoyonedaObj L).map (ι ≫ Pi.π (inverseSystemFamily Ksys) n)

/-- Helper for Lemma 15.92.17: the ambient represented-Hom comparison is computed projectionwise
by the stage maps `Hom(L, K) → Hom(L, K_n)`. -/
private theorem homToDerivedLimitAmbientMap_π
    {Ksys : SequentialInverseSystem DMod} {K : DMod} (L : DMod)
    [HasProduct (inverseSystemFamily Ksys)]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hι : HasMilnorTriangle.WithMap Ksys ι) (n : ℕ) :
    homToDerivedLimitAmbientMap L hι ≫
        Pi.π (inverseSystemFamily (representedHomTower Ksys L)) n =
      (preadditiveCoyonedaObj L).map
        (ι ≫ Pi.π (inverseSystemFamily Ksys) n) := by
  -- Proof comment: the `n`th projection of the ambient product comparison is the defining stage
  -- component.
  rw [homToDerivedLimitAmbientMap, Pi.lift_π]

/-- Helper for Lemma 15.92.17: the represented-Hom comparison is the unique factorization of the
ambient product map through the inverse-limit kernel object. -/
private theorem homToDerivedLimitComparison_comp_limitToProduct
    {Ksys : SequentialInverseSystem DMod} {K : DMod} (L : DMod)
    [HasProduct (inverseSystemFamily Ksys)]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hι : HasMilnorTriangle.WithMap Ksys ι) :
    homToDerivedLimitComparison L hι ≫
        moduleTowerLimitToProduct (R := (End L)ᵐᵒᵖ) (representedHomTower Ksys L) =
      homToDerivedLimitAmbientMap L hι := by
  -- Proof comment: compare the two maps after each ambient product projection of the kernel
  -- object; the inverse-limit factorization was defined by those very stage maps.
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, moduleTowerLimitToProduct_π, homToDerivedLimitAmbientMap_π]
  simpa [homToDerivedLimitComparison, homToDerivedLimitCone] using
    (limit.lift_π
      (F := representedHomTower Ksys L)
      (c := homToDerivedLimitCone L hι)
      (j := op n))

/-- Helper for Lemma 15.92.17: the stagewise formulas in a derived-completion comparison
reassemble to one equality into the Milnor product. -/
private theorem canonical_product_map_comp_π
    {f : Fin r → A} {K : DMod}
    [HasProduct
      (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))]
    (n : ℕ) :
    Pi.lift (fun m ↦ derivedCompletionKoszulPowerTensorToStage K f m) ≫
        Pi.π
          (inverseSystemFamily
            (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
          n =
      derivedCompletionKoszulPowerTensorToStage K f n := by
  -- Proof comment: the canonical product map was defined by the stage maps, so the `n`th
  -- projection is exactly the `n`th powered-Koszul comparison.
  simpa using
    (Pi.lift_π
      (f := fun m ↦ derivedCompletionKoszulPowerTensorToStage K f m)
      n)

/-- Helper for Lemma 15.92.17: the stagewise formulas in a derived-completion comparison
reassemble to one equality into the Milnor product. -/
private theorem comparison_comp_product_map_eq_canonical
    {f : Fin r → A} {K L : DMod} {c : K ⟶ L}
    [HasProduct
      (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))]
    {ι :
      L ⟶
        ∏ᶜ inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)}
    (hcomp : ∀ n : ℕ,
      c ≫ ι ≫
          Pi.π
            (inverseSystemFamily
              (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
            n =
        derivedCompletionKoszulPowerTensorToStage K f n) :
    c ≫ ι =
      Pi.lift (fun n ↦ derivedCompletionKoszulPowerTensorToStage K f n) := by
  -- Proof comment: the universal property of the fixed product reduces the map equality to the
  -- given stagewise compatibility formulas.
  apply Pi.hom_ext
  intro n
  -- Proof comment: project both sides to the `n`th stage and rewrite the right-hand side by the
  -- defining `Pi.lift` formula.
  rw [Category.assoc, canonical_product_map_comp_π]
  exact hcomp n

/-- Helper for Lemma 15.92.17: every nonempty monomial in the generators `f i` already lies in
the span ideal `(f_1, \ldots, f_r)`. -/
private lemma fin_monomial_mem_spanRange
    (f : Fin r → A) {d : ℕ} (hd : 0 < d) (g : Fin d → Fin r) :
    (∏ i, f (g i)) ∈ Ideal.span (Set.range f) := by
  classical
  cases d with
  | zero =>
      cases Nat.not_lt_zero _ hd
  | succ d =>
      have hgen : f (g 0) ∈ Ideal.span (Set.range f) :=
        Ideal.subset_span (Set.mem_range_self (g 0))
      -- Proof comment: split the monomial into its first generator and the remaining tail; the
      -- span ideal already contains the first factor and is closed under multiplication.
      simpa [Fin.prod_univ_succ] using
        Ideal.mul_mem_right (Ideal.span (Set.range f))
          (∏ i : Fin d, f (g i.succ)) hgen

/-- Helper for Lemma 15.92.17: derived completeness with respect to `(f_1, \ldots, f_r)` kills
the localization-away object attached to any nonempty monomial in the generators. -/
private theorem monomial_localizationAwayT_isZero_of_isDerivedComplete
    (f : Fin r → A) {K : DMod}
    (hK : K.IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f)))
    {d : ℕ} (hd : 0 < d) (g : Fin d → Fin r) :
    IsZero
      (CategoryTheory.DerivedCategory.localizationAwayT
        (H := inferInstance)
        (∏ i, f (g i))
        K) := by
  -- Proof comment: derived completeness applies to every element of the span ideal, and the
  -- previous helper places each nonempty monomial exactly in that ideal.
  rw [CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition_iff
    (H := inferInstance)]
  exact
    (CategoryTheory.DerivedCategory.isDerivedCompleteWithRespectTo_iff
      K (Ideal.span (Set.range f))).1 hK
      (∏ i, f (g i))
      (fin_monomial_mem_spanRange f hd g)

/-- Helper for Lemma 15.92.17: fix notation for one chosen product object of the powered Koszul
tensor tower. -/
private abbrev derivedCompletionKoszulPowerTensorProduct
    (K : DMod) (f : Fin r → A)
    [HasProduct
      (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))] :
    DMod :=
  ∏ᶜ inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)

/-- Helper for Lemma 15.92.17: any two chosen products of the powered Koszul tensor tower are
canonically isomorphic. -/
private noncomputable def derivedCompletionKoszulPowerTensorProductIso
    (K : DMod) (f : Fin r → A)
    [hP : HasProduct
      (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))]
    [hQ : HasProduct
      (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))] :
    @derivedCompletionKoszulPowerTensorProduct _ _ _ _ K f hP ≅
      @derivedCompletionKoszulPowerTensorProduct _ _ _ _ K f hQ := by
  letI := hP
  let c' :
      Fan
        (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)) :=
    Fan.mk
      (by
        letI := hQ
        exact ∏ᶜ inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
      (fun n ↦ by
        letI := hQ
        exact
          Pi.π
            (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
            n)
  let hc' : IsLimit c' := by
    letI := hQ
    simpa [c'] using
      productIsProduct
        (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
  exact hc'.conePointUniqueUpToIso
    (productIsProduct
      (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)))

/-- Helper for Lemma 15.92.17: the canonical product isomorphism preserves each stage projection
of the powered Koszul tensor tower. -/
private theorem derivedCompletionKoszulPowerTensorProductIso_hom_comp_π
    (K : DMod) (f : Fin r → A)
    [hP : HasProduct
      (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))]
    [hQ : HasProduct
      (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))]
    (n : ℕ) :
    (derivedCompletionKoszulPowerTensorProductIso K f).hom ≫
        (by
          letI := hQ
          exact
            Pi.π
              (inverseSystemFamily
                (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
              n) =
      (by
        letI := hP
        exact
          Pi.π
            (inverseSystemFamily
              (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
            n) := by
  letI := hP
  let c' :
      Fan
        (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)) :=
    Fan.mk
      (by
        letI := hQ
        exact ∏ᶜ inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
      (fun i ↦ by
        letI := hQ
        exact
          Pi.π
            (inverseSystemFamily
              (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
            i)
  let hc' : IsLimit c' := by
    letI := hQ
    simpa [c'] using
      productIsProduct
        (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
  -- Proof comment: both products represent the same fan, so the unique comparison isomorphism is
  -- characterized by preserving each projection.
  simpa [derivedCompletionKoszulPowerTensorProductIso, c'] using
    hc'.conePointUniqueUpToIso_hom_comp
      (productIsProduct
        (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)))
      ⟨n⟩

attribute [reassoc] derivedCompletionKoszulPowerTensorProductIso_hom_comp_π

/-- Helper for Lemma 15.92.17: the canonical product isomorphism intertwines the Milnor
difference map of the powered Koszul tensor tower. -/
private theorem derivedCompletionKoszulPowerTensorProductIso_hom_comm_difference
    (K : DMod) (f : Fin r → A)
    [hP : HasProduct
      (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))]
    [hQ : HasProduct
      (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))] :
    (derivedCompletionKoszulPowerTensorProductIso K f).hom ≫
        (by
          letI := hQ
          exact
            derivedLimitDifferenceMap
              (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)) =
      (by
        letI := hP
        exact
          derivedLimitDifferenceMap
            (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)) ≫
        (derivedCompletionKoszulPowerTensorProductIso K f).hom := by
  letI := hQ
  apply Pi.hom_ext
  intro n
  -- Proof comment: both composites have the same `n`th projection because the product
  -- comparison fixes the `n`th and `(n + 1)`st coordinates.
  have hleft :
      (derivedCompletionKoszulPowerTensorProductIso K f).hom ≫
          derivedLimitDifferenceMap
            (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) ≫
          Pi.π
            (inverseSystemFamily
              (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
            n =
        Pi.π
            (inverseSystemFamily
              (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
            n -
          Pi.π
              (inverseSystemFamily
                (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
              (n + 1) ≫
            (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f).transitionMap
              (Nat.le_succ n) := by
    have hπn := derivedCompletionKoszulPowerTensorProductIso_hom_comp_π K f n
    have hπsucc := derivedCompletionKoszulPowerTensorProductIso_hom_comp_π K f (n + 1)
    calc
      (derivedCompletionKoszulPowerTensorProductIso K f).hom ≫
          derivedLimitDifferenceMap
            (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) ≫
          Pi.π
            (inverseSystemFamily
              (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
            n =
        (derivedCompletionKoszulPowerTensorProductIso K f).hom ≫
            (Pi.π
                (inverseSystemFamily
                  (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
                n -
              Pi.π
                  (inverseSystemFamily
                    (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
                  (n + 1) ≫
                (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f).transitionMap
                  (Nat.le_succ n)) := by
            rw [derivedLimitDifferenceMap_comp_π]
      _ =
        (derivedCompletionKoszulPowerTensorProductIso K f).hom ≫
            Pi.π
              (inverseSystemFamily
                (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
              n -
          (derivedCompletionKoszulPowerTensorProductIso K f).hom ≫
            Pi.π
              (inverseSystemFamily
                (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
              (n + 1) ≫
            (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f).transitionMap
              (Nat.le_succ n) := by
            rw [Preadditive.comp_sub]
      _ =
        Pi.π
            (inverseSystemFamily
              (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
            n -
          Pi.π
              (inverseSystemFamily
                (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
              (n + 1) ≫
            (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f).transitionMap
              (Nat.le_succ n) := by
            rw [hπn]
            simpa [Category.assoc] using
              congrArg
                (fun g ↦
                  Pi.π
                      (inverseSystemFamily
                        (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
                      n -
                    g ≫
                      (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f).transitionMap
                        (Nat.le_succ n))
                hπsucc
  have hright :
      (by
        letI := hP
        exact
          derivedLimitDifferenceMap
            (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)) ≫
          (derivedCompletionKoszulPowerTensorProductIso K f).hom ≫
          Pi.π
            (inverseSystemFamily
              (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
            n =
        Pi.π
            (inverseSystemFamily
              (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
            n -
          Pi.π
              (inverseSystemFamily
                (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
              (n + 1) ≫
            (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f).transitionMap
              (Nat.le_succ n) := by
    letI := hP
    calc
      derivedLimitDifferenceMap
          (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) ≫
          (derivedCompletionKoszulPowerTensorProductIso K f).hom ≫
          Pi.π
            (inverseSystemFamily
              (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
            n =
        derivedLimitDifferenceMap
            (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) ≫
          Pi.π
            (inverseSystemFamily
              (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
            n := by
            simpa [Category.assoc] using
              congrArg
                (fun g ↦
                  derivedLimitDifferenceMap
                    (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) ≫ g)
                (derivedCompletionKoszulPowerTensorProductIso_hom_comp_π K f n)
      _ =
        Pi.π
            (inverseSystemFamily
              (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
            n -
          Pi.π
              (inverseSystemFamily
                (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
              (n + 1) ≫
            (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f).transitionMap
              (Nat.le_succ n) := by
            simpa using
              derivedLimitDifferenceMap_comp_π
                (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) n
  simpa [Category.assoc] using hleft.trans hright.symm

/-- Helper for Lemma 15.92.17: after fixing one product object of the powered Koszul tensor
tower, any comparison witness can be transported to that fixed product. -/
private theorem exists_fixed_product_comparison_of_comparison
    {f : Fin r → A} {K L : DMod} {c : K ⟶ L}
    [hP : HasProduct
      (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))]
    (hc : IsDerivedCompletionKoszulPowerTensorComparison f K L c) :
    ∃ ι :
        L ⟶
          ∏ᶜ inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f),
      HasMilnorTriangle.WithMap
          (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) ι ∧
        ∀ n : ℕ,
          c ≫ ι ≫
              Pi.π
                (inverseSystemFamily
                  (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
                n =
            derivedCompletionKoszulPowerTensorToStage K f n := by
  rcases hc with ⟨hP', ι', hι', hcomp⟩
  letI := hP'
  let e := derivedCompletionKoszulPowerTensorProductIso K f
  rcases hι' with ⟨δ', hδ'⟩
  refine ⟨ι' ≫ e.hom, ?_, ?_⟩
  · -- Proof comment: transport the distinguished Milnor triangle across the canonical product
    -- isomorphism so that the comparison lands in the fixed ambient product.
    refine ⟨e.inv ≫ δ', ?_⟩
    let T : Triangle DMod :=
      Triangle.mk ι'
        (derivedLimitDifferenceMap
          (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
        δ'
    let T' : Triangle DMod :=
      Triangle.mk
        (ι' ≫ e.hom)
        (by
          letI := hP
          exact
            derivedLimitDifferenceMap
              (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
        (e.inv ≫ δ')
    have hIso : T ≅ T' := by
      refine Triangle.isoMk _ _ (Iso.refl _) e e ?_ ?_ ?_
      · simp [T, T']
      · simpa [T, T'] using
          (derivedCompletionKoszulPowerTensorProductIso_hom_comm_difference K f).symm
      · simp [T, T']
    exact isomorphic_distinguished _ hδ' _ hIso.symm
  · intro n
    -- Proof comment: the transported comparison has the same stagewise formulas because the
    -- canonical product isomorphism fixes every projection.
    calc
      c ≫ (ι' ≫ e.hom) ≫
          Pi.π
            (inverseSystemFamily
              (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
            n =
        c ≫ ι' ≫
          (e.hom ≫
            Pi.π
              (inverseSystemFamily
                (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
              n) := by
            simp [Category.assoc]
      _ = c ≫ ι' ≫
          Pi.π
            (inverseSystemFamily
              (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
            n := by
            rw [derivedCompletionKoszulPowerTensorProductIso_hom_comp_π K f n]
      _ = derivedCompletionKoszulPowerTensorToStage K f n := hcomp n

/-- Helper for Lemma 15.92.17: two Milnor presentations of the same sequential tower over one
chosen product object are canonically isomorphic over that product. -/
private theorem milnor_presentation_iso_of_same_tower
    {Ksys : ℕᵒᵖ ⥤ DMod}
    [HasProduct (inverseSystemFamily Ksys)]
    {K L : DMod}
    {ιK : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    {ιL : L ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hK : HasMilnorTriangle.WithMap Ksys ιK)
    (hL : HasMilnorTriangle.WithMap Ksys ιL) :
    ∃ e : K ≅ L, e.hom ≫ ιL = ιK := by
  rcases hK with ⟨δK, hδK⟩
  rcases hL with ⟨δL, hδL⟩
  let T : Triangle DMod :=
    Triangle.mk ιK (derivedLimitDifferenceMap Ksys) δK
  let T' : Triangle DMod :=
    Triangle.mk ιL (derivedLimitDifferenceMap Ksys) δL
  -- Proof comment: complete the identity square on the common product terms to a morphism of
  -- distinguished triangles, then use two-out-of-three on its three components.
  obtain ⟨a, ha₁, ha₃⟩ :=
    complete_distinguished_triangle_morphism₁
      T T' hδK hδL (𝟙 _) (𝟙 _)
      (by simp [T, T'])
  let φ : T ⟶ T' :=
    Triangle.homMk T T' a (𝟙 _) (𝟙 _)
      (by simpa [T, T'] using ha₁)
      (by simp [T, T'])
      (by simpa [T, T'] using ha₃)
  have ha : IsIso a := by
    haveI : IsIso φ.hom₂ := by
      simpa [φ] using
        (show IsIso (𝟙 (∏ᶜ inverseSystemFamily Ksys)) by infer_instance)
    haveI : IsIso φ.hom₃ := by
      simpa [φ] using
        (show IsIso (𝟙 (∏ᶜ inverseSystemFamily Ksys)) by infer_instance)
    have : IsIso φ.hom₁ :=
      Pretriangulated.isIso₁_of_isIso₂₃ φ hδK hδL (by infer_instance) (by infer_instance)
    simpa using this
  exact ⟨asIso a, by simpa [T, T'] using ha₁.symm⟩

/-- Helper for Lemma 15.92.17: stagewise-equal maps into a fixed Milnor presentation define the
same compatible point of the represented-Hom inverse limit. -/
private theorem represented_hom_comparison_eq_of_stagewise
    {Ksys : ℕᵒᵖ ⥤ DMod}
    [HasProduct (inverseSystemFamily Ksys)]
    {K L : DMod}
    {ι : L ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hι : HasMilnorTriangle.WithMap Ksys ι)
    {u v : K ⟶ L}
    (hcomp : ∀ n : ℕ,
      u ≫ ι ≫ Pi.π (inverseSystemFamily Ksys) n =
        v ≫ ι ≫ Pi.π (inverseSystemFamily Ksys) n) :
    (homToDerivedLimitComparison K hι).hom u =
      (homToDerivedLimitComparison K hι).hom v := by
  let A : SequentialInverseSystem (ModuleCat (End K)ᵐᵒᵖ) :=
    representedHomTower Ksys K
  let ψ : limit A ⟶ ∏ᶜ inverseSystemFamily A :=
    moduleTowerLimitToProduct (R := (End K)ᵐᵒᵖ) A
  have hψinj : Function.Injective ψ.hom := by
    letI : Mono ψ := by
      exact mono_of_isLimit_fork
        (moduleTowerLimitToProduct_is_kernel (R := (End K)ᵐᵒᵖ) A)
    exact (ModuleCat.mono_iff_injective _).1 inferInstance
  apply hψinj
  -- Proof comment: compare the two inverse-limit points after the canonical mono into the ambient
  -- product, then project to each stage where the hypothesis gives the desired equality.
  ext n
  change
    (((homToDerivedLimitComparison K hι ≫ ψ) ≫ Pi.π (inverseSystemFamily A) n).hom u) =
      (((homToDerivedLimitComparison K hι ≫ ψ) ≫ Pi.π (inverseSystemFamily A) n).hom v)
  rw [Category.assoc, Category.assoc]
  rw [homToDerivedLimitComparison_comp_limitToProduct]
  rw [homToDerivedLimitAmbientMap_π]
  simpa [A, representedHomTower, Category.assoc] using hcomp n

/-- Helper for Lemma 15.92.17: if the represented-Hom comparison into a fixed Milnor
presentation is monic, then a morphism with the canonical stagewise composites is forced to be the
Milnor comparison isomorphism coming from the source-side canonical product map. -/
private theorem comparison_eq_milnor_iso_hom_of_canonical_source
    {f : Fin r → A} {K L : DMod}
    [HasProduct
      (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))]
    {ι :
      L ⟶
        ∏ᶜ inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)}
    (hα :
      HasMilnorTriangle.WithMap
        (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)
        (Pi.lift (fun n ↦ derivedCompletionKoszulPowerTensorToStage K f n)))
    (hι :
      HasMilnorTriangle.WithMap
        (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)
        ι)
    (hmono : Mono (homToDerivedLimitComparison K hι))
    {c : K ⟶ L}
    (hstage : ∀ n : ℕ,
      c ≫ ι ≫
          Pi.π
            (inverseSystemFamily
              (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
            n =
        derivedCompletionKoszulPowerTensorToStage K f n) :
    ∃ e : K ≅ L, c = e.hom := by
  obtain ⟨e, he⟩ :=
    milnor_presentation_iso_of_same_tower
      (Ksys := derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)
      (K := K) (L := L) hα hι
  have hstage' :
      ∀ n : ℕ,
        c ≫ ι ≫
            Pi.π
              (inverseSystemFamily
                (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
              n =
          e.hom ≫ ι ≫
            Pi.π
              (inverseSystemFamily
                (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
              n := by
    intro n
    -- Proof comment: both morphisms induce the same canonical map to the `n`th powered Koszul
    -- stage, one by hypothesis and one because the Milnor isomorphism is defined over the fixed
    -- product.
    calc
      c ≫ ι ≫
          Pi.π
            (inverseSystemFamily
              (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
            n =
        derivedCompletionKoszulPowerTensorToStage K f n := hstage n
      _ =
        Pi.lift (fun m ↦ derivedCompletionKoszulPowerTensorToStage K f m) ≫
          Pi.π
            (inverseSystemFamily
              (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
            n := by
            symm
            exact canonical_product_map_comp_π (f := f) (K := K) n
      _ =
        e.hom ≫ ι ≫
          Pi.π
            (inverseSystemFamily
              (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
            n := by
            simpa [Category.assoc] using
              congrArg
                (fun g ↦
                  g ≫
                    Pi.π
                      (inverseSystemFamily
                        (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
                      n)
                he.symm
  have hcompare :
      (homToDerivedLimitComparison K hι).hom c =
        (homToDerivedLimitComparison K hι).hom e.hom :=
    represented_hom_comparison_eq_of_stagewise
      (Ksys := derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)
      (K := K) (L := L) hι hstage'
  have hcompare_injective :
      Function.Injective (homToDerivedLimitComparison K hι).hom :=
    (ModuleCat.mono_iff_injective _).1 hmono
  exact ⟨e, hcompare_injective hcompare⟩

/-- Helper for Lemma 15.92.17: once the source-side canonical product map is known to carry a
Milnor witness and the represented-Hom comparison is injective, every normalized comparison map is
an isomorphism. -/
private theorem comparison_isIso_of_canonical_source_and_mono
    {f : Fin r → A} {K L : DMod}
    [HasProduct
      (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))]
    {ι :
      L ⟶
        ∏ᶜ inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)}
    (hα :
      HasMilnorTriangle.WithMap
        (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)
        (Pi.lift (fun n ↦ derivedCompletionKoszulPowerTensorToStage K f n)))
    (hι :
      HasMilnorTriangle.WithMap
        (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)
        ι)
    (hmono : Mono (homToDerivedLimitComparison K hι))
    {c : K ⟶ L}
    (hstage : ∀ n : ℕ,
      c ≫ ι ≫
          Pi.π
            (inverseSystemFamily
              (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
            n =
        derivedCompletionKoszulPowerTensorToStage K f n) :
    IsIso c := by
  obtain ⟨e, hc⟩ :=
    comparison_eq_milnor_iso_hom_of_canonical_source
      (f := f) (K := K) (L := L) (ι := ι) hα hι hmono hstage
  -- Proof comment: the previous helper identifies `c` with the hom of an isomorphism, so the
  -- isomorphism property transfers immediately.
  have he : IsIso e.hom := by infer_instance
  simpa [hc] using he

/-- Helper for Lemma 15.92.17: in any distinguished triangle, vanishing of the third object
forces the first morphism to be an isomorphism. This is the abstract step needed after each
source-faithful brutal-truncation quotient is shown to vanish. -/
private theorem isIso_mor₁_of_distinguished_of_isZero_obj₃
    {T : Triangle DMod} (hT : T ∈ distTriang DMod) (hzero : IsZero T.obj₃) :
    IsIso T.mor₁ := by
  -- Proof comment: this is exactly the standard zero-cone criterion for distinguished triangles.
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 hzero

/-- Helper for Lemma 15.92.17: the same zero-quotient criterion survives after replacing a
distinguished triangle by an isomorphic one. This is the transport step needed when the brutal
filtration quotient is first identified with a simpler source object. -/
private theorem isIso_mor₁_of_distinguished_of_triangleIso_isZero_obj₃
    {T T' : Triangle DMod} (hT : T ∈ distTriang DMod) (e : T ≅ T') (hzero : IsZero T'.obj₃) :
    IsIso T.mor₁ := by
  have hzeroT : IsZero T.obj₃ := IsZero.of_iso hzero (asIso e.symm.hom₃)
  -- Proof comment: move the zero statement back across the triangle isomorphism and apply the
  -- previous distinguished-triangle criterion.
  exact isIso_mor₁_of_distinguished_of_isZero_obj₃ hT hzeroT

/-- Helper for Lemma 15.92.17: if `K` is derived complete with respect to `I = (f_1, \ldots, f_r)`,
then the canonical comparison from `K` to a chosen derived limit of the powered Koszul tensor tower
is an isomorphism. -/
private theorem comparison_target_isDerivedComplete
    (f : Fin r → A) {K L : DMod} {c : K ⟶ L}
    (hc : IsDerivedCompletionKoszulPowerTensorComparison f K L c) :
    L.IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f)) := by
  -- Proof comment: a comparison target is, by definition, a chosen derived limit of the powered
  -- Koszul tensor tower, so Lemma `15.92.16` applies immediately.
  exact
    derivedLimitOfKoszulPowerTensor_isDerivedCompleteWithRespectTo_spanRange
      f K L hc.isDerivedLimit

/-- Helper for Lemma 15.92.17: normalize a comparison witness to the fixed Milnor product and
record that its target already lies in the derived-complete subcategory. -/
private theorem exists_fixed_product_comparison_with_complete_target
    {f : Fin r → A} {K L : DMod} {c : K ⟶ L}
    [HasProduct
      (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))]
    (hc : IsDerivedCompletionKoszulPowerTensorComparison f K L c) :
    ∃ ι :
        L ⟶
          ∏ᶜ inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f),
      HasMilnorTriangle.WithMap
          (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) ι ∧
        (∀ n : ℕ,
          c ≫ ι ≫
              Pi.π
                (inverseSystemFamily
                  (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
                n =
            derivedCompletionKoszulPowerTensorToStage K f n) ∧
        L.IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f)) := by
  rcases exists_fixed_product_comparison_of_comparison (f := f) hc with ⟨ι, hι, hstage⟩
  -- Proof comment: the fixed-product normalization from the existing helper does not change the
  -- comparison target, so the derived-completeness statement from Lemma `15.92.16` survives
  -- unchanged.
  exact ⟨ι, hι, hstage, comparison_target_isDerivedComplete f hc⟩

/-- Helper for Lemma 15.92.17: once the comparison has been normalized to the fixed Milnor
 product, the only remaining missing datum is a source-side Milnor presentation for the canonical
 product map `Pi.lift (fun n ↦ derivedCompletionKoszulPowerTensorToStage K f n)`. -/
-- TODO: prove the converse by the source-faithful filtration argument from the Stacks proof.
-- The equalizer relation for the canonical product map and the resulting
-- `Triangle.coyoneda_exact₂` comparison-existence step are now proved above. The remaining step
-- is therefore the two-piece source-faithful package:
-- 1. `canonical_product_withMap_of_isDerivedComplete`: under derived completeness of `K`, the
--    canonical product map `Pi.lift (fun n ↦ derivedCompletionKoszulPowerTensorToStage K f n)`
--    extends to a Milnor triangle for the powered Koszul tower;
-- 2. after comparing that source-side `WithMap` with the normalized target-side `WithMap` inside
--    `hc`, finish the endgame by identifying the supplied morphism `c` with the induced Milnor
--    comparison isomorphism over the fixed tower.
theorem derivedCompletionComparison_isIso_of_isDerivedComplete
    (f : Fin r → A) {K L : DMod} (c : K ⟶ L)
    (hc : IsDerivedCompletionKoszulPowerTensorComparison f K L c)
    (hK : K.IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f))) :
    IsIso c := by
  rcases hc with ⟨hP, _, _, _⟩
  let _ :
      HasProduct
        (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)) := hP
  rcases exists_fixed_product_comparison_with_complete_target (f := f) hc with
    ⟨ι, hι, hstage, hL⟩
  have hcι :
      c ≫ ι =
        Pi.lift (fun n ↦ derivedCompletionKoszulPowerTensorToStage K f n) :=
    comparison_comp_product_map_eq_canonical (f := f) (c := c) hstage
  -- Route correction: the earlier proof tried to replace the supplied comparison map `c` by an
  -- abstract isomorphism between two Milnor presentations of the same tower. That loses control
  -- of the specific morphism `c`, because the equality `c ≫ ι = Pi.lift (...)` does not by
  -- itself identify `c` inside `Hom(K, L)`.
  --
  -- Proof comment: after the fixed-product normalization, the frontier is now stable:
  -- `hι` is the chosen Milnor triangle over the fixed product, `hcι` pins down the specific map
  -- `c` against that product, and `hL` shows the target already lies in the derived-complete
  -- subcategory. The only missing source-facing ingredient is the brutal-truncation descent that
  -- upgrades the canonical product map on `K` to its own Milnor presentation; after that, one
  -- still has to identify `c` with the resulting Milnor comparison isomorphism.
  --
  -- TODO: implement the source-faithful brutal-truncation descent:
  -- 1. build the Milnor triangles for the truncation towers `σ_{≥ p} K_n^•`,
  -- 2. identify the negative graded pieces with finite sums of localization-away objects and kill
  --    them using derived completeness,
  -- 3. identify the `p = 0` truncation with the constant `A[0]` tower,
  -- 4. package the resulting theorem as the missing source-side witness
  --    `canonical_product_withMap_of_isDerivedComplete`,
  -- 5. compare that witness with `hι` via `milnor_presentation_iso_of_same_tower` and use the
  --    represented-Hom Milnor comparison to prove that the supplied map `c` is the induced
  --    isomorphism.
  let _hcomplete_pair :
      K.IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f)) ∧
        L.IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f)) :=
    ⟨hK, hL⟩
  sorry

-- Proof sketch: if `c` is a compatible comparison to a chosen derived limit of the powered Koszul
-- tensor tower, then the target is derived complete by Lemma `15.92.16`, so an isomorphism `c`
-- forces derived completeness of `K`. Conversely, assume `K` is derived complete with respect to
-- `I = (f_1, ..., f_r)`. Filter each powered Koszul complex by stupid truncations, apply the
-- exactness of `E ↦ R lim (K ⊗_A^L E)` from Lemma `15.88.11`, and use the vanishing of the
-- negative graded pieces supplied by derived completeness to deduce that the comparison map is an
-- isomorphism.
/-- Lemma 15.92.17: in Situation `15.92.15`, for any comparison morphism
`c : K ⟶ L` formalizing the canonical map
`K \to R\!\varprojlim (K \otimes_A^{\mathbf L} K_n^\bullet)`, the object `K` is derived complete
with respect to `I = (f_1, \ldots, f_r)` if and only if `c` is an isomorphism. -/
theorem isDerivedCompleteWithRespectTo_spanRange_iff_isIso_derivedCompletionComparison
    (f : Fin r → A) {K L : DMod} (c : K ⟶ L)
    (hc : IsDerivedCompletionKoszulPowerTensorComparison f K L c) :
    K.IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f)) ↔ IsIso c := by
  constructor
  · intro hK
    -- Proof comment: the converse direction is isolated in the dedicated helper so the remaining
    -- structural blocker is exactly the source-faithful filtration package.
    exact derivedCompletionComparison_isIso_of_isDerivedComplete f c hc hK
  · intro hIso
    -- Proof comment: a comparison map presents `L` as the required derived limit, so Lemma
    -- `15.92.16` makes `L` derived complete; then transport that property back across `c`.
    have hL :
        L.IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f)) :=
      derivedLimitOfKoszulPowerTensor_isDerivedCompleteWithRespectTo_spanRange
        f K L hc.isDerivedLimit
    exact (isDerivedCompleteWithRespectTo_iff_of_iso (I := Ideal.span (Set.range f)) (asIso c)).2 hL

end

end CategoryTheory
