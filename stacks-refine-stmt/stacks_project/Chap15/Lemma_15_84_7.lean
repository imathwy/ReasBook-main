import Mathlib
import stacks_project.Chap15.«15_60_1_1»
import stacks_project.Chap15.Lemma_15_84_2

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedTensorWithAlgebra
open scoped TensorProduct

universe u v

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace CategoryTheory

section

variable {I : Type v} [Preorder I] [IsFiltered I]
variable (F : I ⥤ CommRingCat.{u}) [HasColimit F] (i₀ : I)
variable (A₀ : Type u) [CommRing A₀] [Algebra (F.obj i₀) A₀]

/- Domain-style sampling for Lemma 15.84.7:
- primary domain: filtered-colimit descent and Hom comparison for derived scalar extension along
  `A₀ → A₀ ⊗[R₀] R_j` and `A₀ → A₀ ⊗[R₀] colim_i R_i`;
- sampled owner declarations in this domain:
  `DerivedCategory.IsPerfectOver`,
  `derivedTensorWithAlgebra`,
  `derivedTensorWithAlgebraCompIso`,
  `Lemma_15_75_18.stageToColimitHomMap`;
- best owner abstraction: the public source-facing layer here is the stagewise factorization and
  eventual-equality API for Homs after base change, while the iterated-vs-direct scalar-extension
  comparisons remain private bridges built from `derivedTensorWithAlgebraCompIso`;
- primitive vs. derived:
  primitive data are the filtered diagram `F`, the base stage `i₀`, the induced algebra maps
  `F.obj i₀ → F.obj j` and `F.obj j → colimit F`, and the canonical scalar-tower algebra maps
  they induce on `A₀ ⊗[F.obj i₀] F.obj j`;
  the Hom transition maps and descent/equality theorems are derived API over those canonical maps;
- source/core/bridge triage:
  `source-facing`: the three numbered descent/factorization/eventual-equality statements;
  `core/canonical`: `DerivedCategory.IsPerfectOver`, `derivedTensorWithAlgebra`, and
    `derivedTensorWithAlgebraCompIso`;
  `bridge/view`: the canonical scalar-tower / tensor-product transition maps and
    iterated-vs-direct comparison isomorphisms used to define the source-facing Hom maps. -/

private abbrev ringColimit : CommRingCat.{u} :=
  colimit F

instance stageAlgebra (j : Set.Ici i₀) : Algebra (F.obj i₀) (F.obj j.1) :=
  (F.map (homOfLE j.2)).hom.toAlgebra

instance colimitAlgebra : Algebra (F.obj i₀) (ringColimit F) :=
  (colimit.ι F i₀).hom.toAlgebra

private instance stageToColimitAlgebra (j : Set.Ici i₀) :
    Algebra (F.obj j.1) (ringColimit F) :=
  (colimit.ι F j.1).hom.toAlgebra

omit [IsFiltered I] in
private theorem stageToColimitRingHom_comp_eq (j : Set.Ici i₀) :
    (colimit.ι F j.1).hom.comp (F.map (homOfLE j.2)).hom = (colimit.ι F i₀).hom := by
  rw [← CommRingCat.hom_comp]
  simpa using congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE j.2))

omit [IsFiltered I] in
private theorem stageTransitionRingHom_comp_eq {j k : Set.Ici i₀} (h : j ⟶ k) :
    (F.map h).hom.comp (F.map (homOfLE j.2)).hom = (F.map (homOfLE k.2)).hom := by
  sorry

omit [IsFiltered I] in
private instance stageToColimitIsScalarTower (j : Set.Ici i₀) :
    IsScalarTower (F.obj i₀) (F.obj j.1) (ringColimit F) :=
  IsScalarTower.of_algebraMap_eq' (stageToColimitRingHom_comp_eq F i₀ j).symm

private abbrev stageTransitionTensorMap {j k : Set.Ici i₀} (h : j ⟶ k) :
    A₀ ⊗[F.obj i₀] F.obj j.1 →+* A₀ ⊗[F.obj i₀] F.obj k.1 :=
  letI : Algebra (F.obj j.1) (F.obj k.1) := (F.map h).hom.toAlgebra
  letI : IsScalarTower (F.obj i₀) (F.obj j.1) (F.obj k.1) :=
    IsScalarTower.of_algebraMap_eq' (stageTransitionRingHom_comp_eq F i₀ h).symm
  Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) A₀)
    (IsScalarTower.toAlgHom (F.obj i₀) (F.obj j.1) (F.obj k.1))

private abbrev stageToColimitTensorMap (j : Set.Ici i₀) :
    A₀ ⊗[F.obj i₀] F.obj j.1 →+* A₀ ⊗[F.obj i₀] ringColimit F :=
  Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) A₀)
    (IsScalarTower.toAlgHom (F.obj i₀) (F.obj j.1) (ringColimit F))

private theorem stageToColimitTensorMap_comp_eq (j : Set.Ici i₀) :
    (stageToColimitTensorMap F i₀ A₀ j).comp
      (algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj j.1)) =
        algebraMap A₀ (A₀ ⊗[F.obj i₀] ringColimit F) := sorry

private theorem stageTransitionTensorMap_comp_eq {j k : Set.Ici i₀} (h : j ⟶ k) :
    (stageTransitionTensorMap F i₀ A₀ h).comp
      (algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj j.1)) =
      algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj k.1) := sorry

local notation "DModA0" => DerivedCategory (ModuleCat A₀)

private instance stageToColimitTensorAlgebra (j : Set.Ici i₀) :
    Algebra (A₀ ⊗[F.obj i₀] F.obj j.1) (A₀ ⊗[F.obj i₀] ringColimit F) :=
  (stageToColimitTensorMap F i₀ A₀ j).toAlgebra

private abbrev stageBaseChange (j : Set.Ici i₀) :
    DModA0 ⥤ DerivedCategory (ModuleCat (A₀ ⊗[F.obj i₀] F.obj j.1)) :=
  derivedTensorWithAlgebra (algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj j.1))

private abbrev colimitBaseChange :
    DModA0 ⥤ DerivedCategory (ModuleCat (A₀ ⊗[F.obj i₀] ringColimit F)) :=
  derivedTensorWithAlgebra (algebraMap A₀ (A₀ ⊗[F.obj i₀] ringColimit F))

private abbrev stageToColimitBaseChange (j : Set.Ici i₀) :
    DerivedCategory (ModuleCat (A₀ ⊗[F.obj i₀] F.obj j.1)) ⥤
      DerivedCategory (ModuleCat (A₀ ⊗[F.obj i₀] ringColimit F)) :=
  derivedTensorWithAlgebra (stageToColimitTensorMap F i₀ A₀ j)

private abbrev stageTransitionBaseChange {j k : Set.Ici i₀} (h : j ⟶ k) :
    DerivedCategory (ModuleCat (A₀ ⊗[F.obj i₀] F.obj j.1)) ⥤
      DerivedCategory (ModuleCat (A₀ ⊗[F.obj i₀] F.obj k.1)) :=
  derivedTensorWithAlgebra (stageTransitionTensorMap F i₀ A₀ h)

private noncomputable abbrev stageToColimitBaseChangeIso (j : Set.Ici i₀) :
    stageBaseChange F i₀ A₀ j ⋙ stageToColimitBaseChange F i₀ A₀ j ≅
      colimitBaseChange F i₀ A₀ :=
  derivedTensorWithAlgebraCompIso
    (algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj j.1))
    (stageToColimitTensorMap F i₀ A₀ j)
    (algebraMap A₀ (A₀ ⊗[F.obj i₀] ringColimit F))
    (stageToColimitTensorMap_comp_eq F i₀ A₀ j)

private noncomputable abbrev stageTransitionBaseChangeIso {j k : Set.Ici i₀} (h : j ⟶ k) :
    stageBaseChange F i₀ A₀ j ⋙ stageTransitionBaseChange F i₀ A₀ h ≅
      stageBaseChange F i₀ A₀ k :=
  derivedTensorWithAlgebraCompIso
    (algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj j.1))
    (stageTransitionTensorMap F i₀ A₀ h)
    (algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj k.1))
    (stageTransitionTensorMap_comp_eq F i₀ A₀ h)

/-- The canonical image in the colimit Hom-set of a stagewise morphism. -/
noncomputable def stageToColimitHomMap (j : Set.Ici i₀)
    {K₀ L₀ : DModA0}
    (β :
      (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1]) ⟶
        (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1])) :
    (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] (colimit F : CommRingCat.{u})]) ⟶
      (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] (colimit F : CommRingCat.{u})]) :=
  let e := stageToColimitBaseChangeIso F i₀ A₀ j
  (e.app K₀).inv ≫ (stageToColimitBaseChange F i₀ A₀ j).map β ≫ (e.app L₀).hom

/-- The canonical image in a later-stage Hom-set of a stagewise morphism. -/
noncomputable def stageTransitionHomMap {j k : Set.Ici i₀} (h : j ⟶ k)
    {K₀ L₀ : DModA0}
    (β :
      (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1]) ⟶
        (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1])) :
    (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj k.1]) ⟶
      (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj k.1]) :=
  let e := stageTransitionBaseChangeIso F i₀ A₀ h
  (e.app K₀).inv ≫ (stageTransitionBaseChange F i₀ A₀ h).map β ≫ (e.app L₀).hom

-- Proof sketch: the cocone relation `R_j → R_k → colim F = R_j → colim F` induces the matching
-- equality for the tensor-product ring maps `A_j → A_k → A = A_j → A`. Naturality of the
-- iterated-vs-direct comparison isomorphisms then identifies the two induced maps on Hom-sets.
/-- The canonical images in the colimit Hom-set are compatible with transition to later stages.
This is the coherence needed for the source-facing filtered Hom-colimit comparison in
Lemma `15.84.7 (2)`. -/
theorem stageToColimitHomMap_transition
    {K₀ L₀ : DModA0} {j k : Set.Ici i₀} (h : j ⟶ k)
    (β :
      (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1]) ⟶
        (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1])) :
    stageToColimitHomMap F i₀ A₀ k (stageTransitionHomMap F i₀ A₀ h β) =
      stageToColimitHomMap F i₀ A₀ j β := by
  sorry

section

variable [Module.Flat (F.obj i₀) A₀] [Algebra.FinitePresentation (F.obj i₀) A₀]

-- Proof sketch: combine the finite-presentation descent for flat finitely presented modules with
-- the representative criterion for `R`-perfect objects from Lemma `15.84.4`, then descend the
-- finitely many terms of a bounded representative to some stage `j ≥ i₀`.
/-- Lemma 15.84.7 (1): for `A_j = A₀ ⊗[R₀] R_j` and
`A = A₀ ⊗[R₀] \operatorname{colim}_i R_i`, every object of `D(A)` that is perfect over the
colimit ring descends to some stage as an object of `D(A_j)` that is perfect over `R_j`. -/
theorem exists_stage_of_isPerfectOver_filtered_base_change
    (K : DerivedCategory (ModuleCat (A₀ ⊗[F.obj i₀] (colimit F : CommRingCat.{u}))))
    (hK : DerivedCategory.IsPerfectOver (colimit F : CommRingCat.{u}) K) :
    ∃ (j : Set.Ici i₀) (Kj : DerivedCategory (ModuleCat (A₀ ⊗[F.obj i₀] F.obj j.1))),
      DerivedCategory.IsPerfectOver (F.obj j.1) Kj ∧
        IsIsomorphic K
          (Kj ⊗[A₀ ⊗[F.obj i₀] F.obj j.1]^L[
            A₀ ⊗[F.obj i₀] (colimit F : CommRingCat.{u})]) := sorry

-- Proof sketch: represent the morphism group after base change to `A` by the bounded Hom complex
-- from Lemma `15.84.6`, descend the finitely presented terms of that complex to a sufficiently
-- large stage using filtered-colimit exactness, and read off a stage morphism inducing `α`.
/-- Lemma 15.84.7 (2): if `K₀, L₀ ∈ D(A₀)` with `K₀` pseudo-coherent and `L₀` of finite tor
dimension over `R₀`, then every morphism after base change to
`A = A₀ ⊗[R₀] \operatorname{colim}_i R_i` comes from some stage
`A_j = A₀ ⊗[R₀] R_j`. -/
theorem exists_stage_factorization_of_hom_of_pseudoCoherent_of_finiteTorDimension
    (K₀ L₀ : DModA0) (hK₀ : K₀.IsPseudoCoherent)
    (hL₀ :
      HasFiniteTorDimension
        (((ModuleCat.restrictScalars (algebraMap (F.obj i₀) A₀)).mapDerivedCategory).obj L₀))
    (α :
      (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] (colimit F : CommRingCat.{u})]) ⟶
        (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] (colimit F : CommRingCat.{u})])) :
    ∃ (j : Set.Ici i₀)
      (β :
        (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1]) ⟶
          (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1])),
      α = stageToColimitHomMap F i₀ A₀ j β := sorry

-- Proof sketch: compute equality in the final Hom group by the same descended Hom complex as in
-- part `(2)`; filtered-colimit exactness implies that two stage classes with equal image in the
-- colimit agree after passing to a sufficiently large later stage.
/-- Lemma 15.84.7 (3): under the same hypotheses on `K₀` and `L₀`, if two morphisms at some
stage `A_j` become equal after base change to `A`, then they already become equal after further
base change to a later stage `A_k` with `k ≥ j`. Together with part `(2)`, this is the Hom-side
filtered-colimit description from the lemma. -/
theorem eventually_eq_of_stage_morphisms_with_equal_colimit_images
    (K₀ L₀ : DModA0) (hK₀ : K₀.IsPseudoCoherent)
    (hL₀ :
      HasFiniteTorDimension
        (((ModuleCat.restrictScalars (algebraMap (F.obj i₀) A₀)).mapDerivedCategory).obj L₀))
    (j : Set.Ici i₀)
    (β₁ β₂ :
      (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1]) ⟶
        (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1]))
    (hβ :
      stageToColimitHomMap F i₀ A₀ j β₁ =
        stageToColimitHomMap F i₀ A₀ j β₂) :
    ∃ (k : Set.Ici i₀) (hjk : j ⟶ k),
      stageTransitionHomMap F i₀ A₀ hjk β₁ =
        stageTransitionHomMap F i₀ A₀ hjk β₂ := sorry

/- The three statements above give the essential-surjectivity and filtered Hom-colimit data
expressing that the triangulated category of `R`-perfect complexes over `A` is the filtered
colimit of the triangulated categories of `R_j`-perfect complexes over `A_j`. -/

end

end

end CategoryTheory
