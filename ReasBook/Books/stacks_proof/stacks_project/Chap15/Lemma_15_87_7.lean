import Mathlib
import Mathlib.CategoryTheory.Triangulated.Yoneda
import StacksProject_2024.Chap13.Definition_13_3_5
import StacksProject_2024.Chap13.«13_3_5_1»
import StacksProject_2024.Chap13.Definition_13_33_1
import StacksProject_2024.Chap13.Lemma_13_4_2
import StacksProject_2024.Chap15.Lemma_15_87_4

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

/- Domain-style sampling for Lemma 15.87.7:
- primary domain: triangulated-category homotopy colimits and the Milnor inverse-limit sequence
  for represented contravariant Hom functors;
- sampled owner declarations:
  `CategoryTheory.IsHomotopyColimitOf`,
  `preadditiveYoneda.obj`,
  `Functor.ofSequence`,
  `SequentialInverseSystem.firstDerivedLimit`,
  `CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₁₂`;
- best owner abstraction:
  `source-facing`: the Milnor short exact sequence attached to the owner predicate
    `IsHomotopyColimitOf (Functor.ofSequence f) Khocolim`;
  `core/canonical`: the represented functor `preadditiveYoneda.obj L`, its inverse-system image
    `(Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L`, together with
    `SequentialInverseSystem.firstDerivedLimit`;
  `bridge/view`: the comparison morphism
    `Hom_D(Khocolim, L) ⟶ \varprojlim_n Hom_D(K_n, L)` attached to that chosen telescope
    presentation.
- primitive data: the sequential system `K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯` together with the owner hypothesis
  `IsHomotopyColimitOf (Functor.ofSequence f) Khocolim`;
- derived API: the represented inverse system `(Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L`,
  its canonical owner-level `firstDerivedLimit`, and the presentation-dependent bridge
  `homFromHomotopyColimitComparison`.

Source/core/bridge triage:
- `source-facing`: the Milnor short exact sequence for `Hom_D(-, L)` evaluated on an object
  equipped with `IsHomotopyColimitOf (Functor.ofSequence f)`;
- `core/canonical`: `preadditiveYoneda.obj L`, `(Functor.ofSequence f).op`, and
  `SequentialInverseSystem.firstDerivedLimit`;
- `bridge/view`: `homFromHomotopyColimitComparison`, the comparison map supplied by that chosen
  telescope presentation. -/

private theorem homFromHomotopyColimitCone_naturality
    (L : D) {K : ℕ → D} (f : ∀ n, K n ⟶ K (n + 1))
    [HasCoproduct (Functor.ofSequence f).obj]
    {Khocolim : D} (g : ∐ (Functor.ofSequence f).obj ⟶ Khocolim)
    (h : Khocolim ⟶ (∐ (Functor.ofSequence f).obj)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D)
    (n : ℕ) :
    (preadditiveYoneda.obj L).map (op (Sigma.ι (Functor.ofSequence f).obj n ≫ g)) =
      (preadditiveYoneda.obj L).map (op (Sigma.ι (Functor.ofSequence f).obj (n + 1) ≫ g)) ≫
        ((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L).map
          (homOfLE (Nat.le_succ n)).op := by
  -- Proof comment: the distinguished telescope triangle forces the consecutive coproduct legs to
  -- agree after postcomposing with `g`, and contravariance of `preadditiveYoneda.obj L` turns this
  -- stagewise telescope relation into the cone compatibility.
  have hstage :
      Sigma.ι (Functor.ofSequence f).obj n ≫ g =
        f n ≫ Sigma.ι (Functor.ofSequence f).obj (n + 1) ≫ g := by
    have hzero :
        sequentialTelescopeMap (Functor.ofSequence f) ≫ g = 0 := by
      simpa [Triangle.mk] using comp_distTriang_mor_zero₁₂ _ hKhocolim
    have hproj :
        Sigma.ι (Functor.ofSequence f).obj n ≫ sequentialTelescopeMap (Functor.ofSequence f) ≫ g =
          0 := by
      simpa [Category.assoc] using congrArg (fun t ↦ Sigma.ι (Functor.ofSequence f).obj n ≫ t) hzero
    rw [Sigma.ι_comp_sequentialTelescopeMap_assoc, Preadditive.sub_comp, sub_eq_zero,
      Functor.ofSequence_map_homOfLE_succ, Category.assoc] at hproj
    exact hproj
  have hmap :=
    congrArg (fun t ↦ (preadditiveYoneda.obj L).map (op t)) hstage
  simpa [Functor.ofSequence_map_homOfLE_succ, Functor.comp_map, Functor.map_comp, Category.assoc]
    using hmap

private def homFromHomotopyColimitCone
    (L : D) {K : ℕ → D} (f : ∀ n, K n ⟶ K (n + 1))
    [HasCoproduct (Functor.ofSequence f).obj]
    {Khocolim : D} (g : ∐ (Functor.ofSequence f).obj ⟶ Khocolim)
    (h : Khocolim ⟶ (∐ (Functor.ofSequence f).obj)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D) :
    Cone ((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L) where
  pt := (preadditiveYoneda.obj L).obj (op Khocolim)
  π := NatTrans.ofOpSequence
    (fun n ↦ (preadditiveYoneda.obj L).map (op (Sigma.ι (Functor.ofSequence f).obj n ≫ g)))
    (fun n ↦ homFromHomotopyColimitCone_naturality L f g h hKhocolim n)

/-- The comparison morphism
`Hom_D(Khocolim, L) ⟶ \varprojlim_n Hom_D(K_n, L)` induced by a chosen distinguished telescope
triangle presenting `Khocolim` as a homotopy colimit of the sequence
`K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯`. -/
private def homFromHomotopyColimitComparison
    (L : D) {K : ℕ → D} (f : ∀ n, K n ⟶ K (n + 1))
    [HasCoproduct (Functor.ofSequence f).obj]
    {Khocolim : D} (g : ∐ (Functor.ofSequence f).obj ⟶ Khocolim)
    (h : Khocolim ⟶ (∐ (Functor.ofSequence f).obj)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D) :
    (preadditiveYoneda.obj L).obj (op Khocolim) ⟶
      limit ((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L) :=
  limit.lift _ (homFromHomotopyColimitCone L f g h hKhocolim)

end

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D] [IsTriangulated D]

/-- Helper for Lemma 15.87.7: for a fixed target `L`, the contravariant represented Hom functor
preserves countable products after passing to the opposite category. -/
private theorem preadditiveYoneda_obj_preserves_discrete_limits
    (L : D) :
    PreservesLimitsOfShape (Discrete ℕ) (preadditiveYoneda.obj L) := by
  -- Proof comment: after forgetting additivity, this is the ordinary Yoneda functor, which
  -- preserves all limits; the forgetful functor reflects limits back to `AddCommGrpCat`.
  let F : Dᵒᵖ ⥤ AddCommGrpCat.{v} := preadditiveYoneda.obj L
  letI : PreservesLimitsOfShape (Discrete ℕ) (F ⋙ forget AddCommGrpCat) := by
    simpa [F, whiskering_preadditiveYoneda, Functor.assoc] using
      (inferInstance : PreservesLimitsOfShape (Discrete ℕ) (yoneda.obj L))
  simpa [F] using
    (CategoryTheory.Limits.preservesLimitsOfShape_of_reflects_of_preserves
      F (forget AddCommGrpCat) : PreservesLimitsOfShape (Discrete ℕ) F)

/-- Helper for Lemma 15.87.7: `Hom_D(\bigoplus_n K_n, L)` identifies with the product of the
stagewise groups `Hom_D(K_n, L)` for the represented contravariant functor `preadditiveYoneda`. -/
private noncomputable def preadditiveYoneda_coproduct_obj_iso_product
    (L : D) {K : ℕ → D} (f : ∀ n, K n ⟶ K (n + 1))
    [HasCoproduct (Functor.ofSequence f).obj] :
    (preadditiveYoneda.obj L).obj (op (∐ (Functor.ofSequence f).obj)) ≅
      ∏ᶜ inverseSystemFamily (((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L)) :=
  -- TODO: make the opposite-side product owner explicit enough that `PreservesProduct.iso`
  -- elaborates against `inverseSystemFamily (((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L))`.
  sorry

/-- Helper for Lemma 15.87.7: under the coproduct/product comparison, the `n`th product
projection is exactly precomposition with the `n`th coproduct inclusion. -/
private theorem preadditiveYoneda_coproduct_obj_iso_product_hom_comp_π
    (L : D) {K : ℕ → D} (f : ∀ n, K n ⟶ K (n + 1))
    [HasCoproduct (Functor.ofSequence f).obj] (n : ℕ) :
    (preadditiveYoneda_coproduct_obj_iso_product L f).hom ≫
        Pi.π
          (inverseSystemFamily (((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L)))
          n =
      (preadditiveYoneda.obj L).map (op (Sigma.ι (Functor.ofSequence f).obj n)) := by
  -- TODO: after the product owner above is stabilized, this should follow by expanding the
  -- comparison into `opCoproductIsoProduct` followed by `PreservesProduct.iso` and reading off
  -- the `n`th projection with `piComparison_comp_π`.
  sorry

/-- Helper for Lemma 15.87.7: under the coproduct/product comparison, precomposition by the
telescope map becomes the Milnor difference map of the inverse system
`((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L)`. -/
private theorem preadditiveYoneda_sequentialTelescopeMap_under_product_iso
    (L : D) {K : ℕ → D} (f : ∀ n, K n ⟶ K (n + 1))
    [HasCoproduct (Functor.ofSequence f).obj] :
    (preadditiveYoneda.obj L).map (op (sequentialTelescopeMap (Functor.ofSequence f))) ≫
      (preadditiveYoneda_coproduct_obj_iso_product L f).hom =
    (preadditiveYoneda_coproduct_obj_iso_product L f).hom ≫
      derivedLimitDifferenceMap (((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L)) := by
  -- TODO: once the projection formula above compiles, compare both sides after `Pi.π n`; the
  -- telescope identity `Sigma.ι_comp_sequentialTelescopeMap` should then rewrite directly to
  -- `derivedLimitDifferenceMap_comp_π`.
  sorry

/-- Helper for Lemma 15.87.7: the inverse limit of an AddCommGrp-valued sequential tower maps
canonically to the ambient Milnor product by its stage projections. -/
private abbrev represented_hom_tower_limit_to_product
    (A : SequentialInverseSystem AddCommGrpCat.{v}) :
    limit A ⟶ ∏ᶜ inverseSystemFamily A :=
  Pi.lift fun n ↦ limit.π A (op n)

/-- Helper for Lemma 15.87.7: postcomposing the canonical map from the inverse limit to the
ambient product with the `n`th projection recovers the `n`th limit projection. -/
private theorem represented_hom_tower_limit_to_product_π
    (A : SequentialInverseSystem AddCommGrpCat.{v}) (n : ℕ) :
    represented_hom_tower_limit_to_product A ≫ Pi.π (inverseSystemFamily A) n =
      limit.π A (op n) := by
  rw [represented_hom_tower_limit_to_product, Pi.lift_π]

/-- Helper for Lemma 15.87.7: precomposing the Milnor difference map with a morphism into the
ambient product yields the expected componentwise difference formula. -/
private theorem represented_hom_tower_differenceMap_π_preassoc
    {A : SequentialInverseSystem AddCommGrpCat.{v}} {T : AddCommGrpCat.{v}}
    (k : T ⟶ ∏ᶜ inverseSystemFamily A) (n : ℕ) :
    k ≫ derivedLimitDifferenceMap A ≫ Pi.π (inverseSystemFamily A) n =
      k ≫ Pi.π (inverseSystemFamily A) n -
        k ≫ Pi.π (inverseSystemFamily A) (n + 1) ≫ A.transitionMap (Nat.le_succ n) := by
  simpa [Category.assoc, Preadditive.comp_sub] using
    congrArg (fun t ↦ k ≫ t) (derivedLimitDifferenceMap_comp_π A n)

/-- Helper for Lemma 15.87.7: the canonical map from the inverse limit to the ambient product
lands in the kernel of the Milnor difference map. -/
private theorem represented_hom_tower_limit_to_product_comp_difference
    (A : SequentialInverseSystem AddCommGrpCat.{v}) :
    represented_hom_tower_limit_to_product A ≫ derivedLimitDifferenceMap A = 0 := by
  -- Proof comment: the defining cone relation of the limit says that consecutive stage
  -- projections differ by the transition map, which is exactly the Milnor kernel condition.
  apply Pi.hom_ext
  intro n
  calc
    (represented_hom_tower_limit_to_product A ≫ derivedLimitDifferenceMap A) ≫
        Pi.π (inverseSystemFamily A) n =
      represented_hom_tower_limit_to_product A ≫ Pi.π (inverseSystemFamily A) n -
        represented_hom_tower_limit_to_product A ≫ Pi.π (inverseSystemFamily A) (n + 1) ≫
          A.transitionMap (Nat.le_succ n) := by
            simp [Category.assoc, derivedLimitDifferenceMap_comp_π]
    _ =
      limit.π A (op n) -
        represented_hom_tower_limit_to_product A ≫ Pi.π (inverseSystemFamily A) (n + 1) ≫
          A.transitionMap (Nat.le_succ n) := by
            rw [represented_hom_tower_limit_to_product_π]
    _ =
      limit.π A (op n) -
        limit.π A (op (n + 1)) ≫ A.transitionMap (Nat.le_succ n) := by
            have hπsucc :
                represented_hom_tower_limit_to_product A ≫
                    Pi.π (inverseSystemFamily A) (n + 1) ≫
                      A.transitionMap (Nat.le_succ n) =
                  limit.π A (op (n + 1)) ≫ A.transitionMap (Nat.le_succ n) := by
              simpa [Category.assoc] using
                congrArg
                  (fun t ↦ t ≫ A.transitionMap (Nat.le_succ n))
                  (represented_hom_tower_limit_to_product_π A (n + 1))
            rw [hπsucc]
    _ = 0 := by
          rw [limit.w A ((homOfLE (Nat.le_succ n)).op)]
          simp
    _ = 0 ≫ Pi.π (inverseSystemFamily A) n := by
          simp

/-- Helper for Lemma 15.87.7: a morphism into the Milnor product of a represented Hom tower lies
in the kernel of the difference map exactly when its stage components satisfy the transition
compatibility relation. -/
private theorem represented_hom_tower_kernel_condition
    {A : SequentialInverseSystem AddCommGrpCat.{v}} {W : AddCommGrpCat.{v}}
    (s : W ⟶ ∏ᶜ inverseSystemFamily A)
    (hs : s ≫ derivedLimitDifferenceMap A = 0) (n : ℕ) :
    s ≫ Pi.π (inverseSystemFamily A) n =
      s ≫ Pi.π (inverseSystemFamily A) (n + 1) ≫ A.transitionMap (Nat.le_succ n) := by
  -- Proof comment: projecting the kernel condition to the `n`th factor gives exactly the
  -- defining compatibility relation for a cone over the inverse system.
  have hproj :
      s ≫ Pi.π (inverseSystemFamily A) n -
        s ≫ Pi.π (inverseSystemFamily A) (n + 1) ≫
          A.transitionMap (Nat.le_succ n) = 0 := by
    have hproj' := congrArg (fun t ↦ t ≫ Pi.π (inverseSystemFamily A) n) hs
    simpa [represented_hom_tower_differenceMap_π_preassoc] using hproj'
  simpa [SequentialInverseSystem.transitionMap] using (sub_eq_zero.mp hproj)

/-- Helper for Lemma 15.87.7: the inverse limit of an AddCommGrp-valued sequential tower is the
kernel of its Milnor difference map. -/
private noncomputable def represented_hom_tower_limit_to_product_is_kernel
    (A : SequentialInverseSystem AddCommGrpCat.{v}) :
    IsLimit
      (KernelFork.ofι
        (represented_hom_tower_limit_to_product A)
        (represented_hom_tower_limit_to_product_comp_difference A)) := by
  -- Proof comment: a morphism into the Milnor product lies in the kernel precisely when its
  -- coordinates satisfy the cone relation for the sequential inverse system.
  refine KernelFork.IsLimit.ofι
      (represented_hom_tower_limit_to_product A)
      (represented_hom_tower_limit_to_product_comp_difference A)
      (fun {W} s hs ↦
        let stageHom : ∀ n : ℕ, W ⟶ A.obj (op n) :=
          fun n ↦ s ≫ Pi.π (inverseSystemFamily A) n
        have hstageHom_naturality :
            ∀ n : ℕ,
              stageHom n = stageHom (n + 1) ≫ A.transitionMap (Nat.le_succ n) := by
          intro n
          exact represented_hom_tower_kernel_condition s hs n
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
          exact represented_hom_tower_kernel_condition s hs n
        let c : Cone A := {
          pt := W
          π := NatTrans.ofOpSequence stageHom hstageHom_naturality
        }
        -- Proof comment: the induced lift agrees with the original kernel map after each product
        -- projection, hence agrees globally by product extensionality.
        apply Pi.hom_ext
        intro n
        calc
          (limit.lift A c ≫ represented_hom_tower_limit_to_product A) ≫
              Pi.π (inverseSystemFamily A) n =
            limit.lift A c ≫ limit.π A (op n) := by
              rw [Category.assoc, represented_hom_tower_limit_to_product_π]
          _ = s ≫ Pi.π (inverseSystemFamily A) n := by
              simpa [c, stageHom] using limit.lift_π (F := A) (c := c) (j := op n))
      (fun {W} s hs m hm ↦ by
        let stageHom : ∀ n : ℕ, W ⟶ A.obj (op n) :=
          fun n ↦ s ≫ Pi.π (inverseSystemFamily A) n
        have hstageHom_naturality :
            ∀ n : ℕ,
              stageHom n = stageHom (n + 1) ≫ A.transitionMap (Nat.le_succ n) := by
          intro n
          exact represented_hom_tower_kernel_condition s hs n
        let c : Cone A := {
          pt := W
          π := NatTrans.ofOpSequence stageHom hstageHom_naturality
        }
        -- Proof comment: uniqueness follows because a map into the inverse limit is determined by
        -- its composites with all limit projections.
        apply limit.hom_ext
        intro n
        have hproj := congrArg (fun t ↦ t ≫ Pi.π (inverseSystemFamily A) n.unop) hm
        simpa [c, stageHom, Category.assoc, represented_hom_tower_limit_to_product_π] using
          hproj)

/-- Helper for Lemma 15.87.7: the comparison map to the inverse limit is the canonical
factorization of the product-side map `Hom_D(Khocolim,L) ⟶ ∏_n Hom_D(K_n,L)` through the Milnor
kernel owner `limit`. -/
private theorem homFromHomotopyColimitComparison_comp_limit_to_product
    (L : D) {K : ℕ → D} (f : ∀ n, K n ⟶ K (n + 1))
    [HasCoproduct (Functor.ofSequence f).obj]
    {Khocolim : D} (g : ∐ (Functor.ofSequence f).obj ⟶ Khocolim)
    (h : Khocolim ⟶ (∐ (Functor.ofSequence f).obj)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D) :
    homFromHomotopyColimitComparison L f g h hKhocolim ≫
        represented_hom_tower_limit_to_product
          (((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L)) =
      (preadditiveYoneda.obj L).map (op g) ≫
        (preadditiveYoneda_coproduct_obj_iso_product L f).hom := by
  -- TODO: after the product-side projection formula compiles, project both sides to `Pi.π n`,
  -- use `limit.lift_π` for `homFromHomotopyColimitCone`, and rewrite the resulting stage map by
  -- `preadditiveYoneda_coproduct_obj_iso_product_hom_comp_π`.
  sorry

/-- Helper for Lemma 15.87.7: the raw product-side comparison map already lands in the Milnor
kernel, because it factors through the canonical inverse-limit owner. -/
private theorem homFromHomotopyColimit_raw_comp_difference
    (L : D) {K : ℕ → D} (f : ∀ n, K n ⟶ K (n + 1))
    [HasCoproduct (Functor.ofSequence f).obj]
    {Khocolim : D} (g : ∐ (Functor.ofSequence f).obj ⟶ Khocolim)
    (h : Khocolim ⟶ (∐ (Functor.ofSequence f).obj)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D) :
    ((preadditiveYoneda.obj L).map (op g) ≫
        (preadditiveYoneda_coproduct_obj_iso_product L f).hom) ≫
      derivedLimitDifferenceMap (((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L)) = 0 := by
  -- Proof comment: the raw product-side comparison factors through the inverse-limit kernel
  -- owner, so its composite with the Milnor difference map vanishes formally.
  calc
    ((preadditiveYoneda.obj L).map (op g) ≫
        (preadditiveYoneda_coproduct_obj_iso_product L f).hom) ≫
          derivedLimitDifferenceMap (((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L)) =
      (homFromHomotopyColimitComparison L f g h hKhocolim ≫
          represented_hom_tower_limit_to_product
            (((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L))) ≫
              derivedLimitDifferenceMap
                (((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L)) := by
            rw [homFromHomotopyColimitComparison_comp_limit_to_product]
    _ =
      homFromHomotopyColimitComparison L f g h hKhocolim ≫
        (represented_hom_tower_limit_to_product
          (((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L)) ≫
            derivedLimitDifferenceMap
              (((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L))) := by
          simp [Category.assoc]
    _ = 0 := by
          rw [represented_hom_tower_limit_to_product_comp_difference, comp_zero]

/-- Helper for Lemma 15.87.7: the represented contravariant Hom functor carries the tautological
shift sequence needed for the centered five-term cohomology row. -/
private noncomputable instance preadditiveYoneda_obj_rightOp_shiftSequence
    (L : D) :
    (preadditiveYoneda.obj L).rightOp.ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ _

/-- Helper for Lemma 15.87.7: the degree-`1` shift of `preadditiveYoneda.obj L` is objectwise
represented by `L⟦-1⟧`. -/
private def preadditiveYoneda_rightOp_shift_one_obj_iso
    (L X : D) :
    ((((preadditiveYoneda.obj L).rightOp.shift (1 : ℤ)).obj X).unop) ≅
      (preadditiveYoneda.obj (L⟦(-1 : ℤ)⟧)).obj (op X) :=
  ((preadditiveYoneda.obj L).mapIso
      ((shiftFunctorOpIso D (-1 : ℤ) (1 : ℤ) (neg_add_cancel (1 : ℤ))).app (op X))).symm ≪≫
    (((preadditiveYoneda.obj L).isoShift (-1 : ℤ)).app
      (op X))

/-- Helper for Lemma 15.87.7: the represented contravariant Hom functor is cohomological, written
as homologicality of its opposite-valued covariant view. -/
private instance preadditiveYoneda_obj_rightOp_isHomological
    (L : D) :
    (preadditiveYoneda.obj L).rightOp.IsHomological := by
  simpa using represented_yoneda_rightOp_is_homological (D := D) L

-- Proof sketch: apply the contravariant Hom functor `Hom_D(-, L)` to the opposite of the
-- distinguished telescope triangle presenting `Khocolim`. Lemma 13.4.2 identifies this as a
-- homological functor, so one gets a long exact sequence. The two terms
-- `Hom_D(\bigoplus_n K_n, L)` and `Hom_D(\bigoplus_n K_n, L⟦-1⟧)` identify with the products of
-- `Hom_D(K_n, L)` and `Hom_D(K_n, L⟦-1⟧)`, and Lemma 15.87.1 identifies the kernel and cokernel
-- of the Milnor difference maps with `\varprojlim` and `R^1 \!\varprojlim`. The left term is
-- therefore best exposed through the owner
-- `firstDerivedLimit ((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj _)`, not as
-- a raw cokernel of `derivedLimitDifferenceMap`.
/-- The bridge-level Milnor short exact sequence attached to a chosen distinguished telescope
triangle. The chosen presentation stays internal; the public source-facing theorem below is
phrased only over `IsHomotopyColimitOf (Functor.ofSequence f) Khocolim`. -/
private theorem hom_from_homotopyColimit_shortExact_of_triangle
    (L : D) {K : ℕ → D} (f : ∀ n, K n ⟶ K (n + 1))
    [HasCoproduct (Functor.ofSequence f).obj]
    {Khocolim : D} (g : ∐ (Functor.ofSequence f).obj ⟶ Khocolim)
    (h : Khocolim ⟶ (∐ (Functor.ofSequence f).obj)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D) :
    ∃ (ι :
        firstDerivedLimit ((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj (L⟦(-1 : ℤ)⟧)) ⟶
          (preadditiveYoneda.obj L).obj (op Khocolim))
      (hι :
        ι ≫ homFromHomotopyColimitComparison L f g h hKhocolim = 0),
      (ShortComplex.mk ι (homFromHomotopyColimitComparison L f g h hKhocolim) hι).ShortExact :=
  by
    -- Route correction: the source-faithful proof has already reduced the right endpoint to the
    -- Milnor kernel owner and isolated the remaining blocker to the shifted left endpoint.
    -- TODO: rewrite the degree-`1` coproduct term of the centered five-term row through
    -- `preadditiveYoneda_rightOp_shift_one_obj_iso`, descend the resulting connecting morphism
    -- through `cokernel.desc` to `firstDerivedLimit`, and then package exactness with the already
    -- normalized comparison map `homFromHomotopyColimitComparison`.
    sorry

/-- Lemma 15.87.7: if `Khocolim` is a homotopy colimit of a sequential system
`K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯`, then for every `L` there is a short exact sequence
`0 ⟶ R^1 \!\varprojlim Hom_D(K_n, L⟦-1⟧) ⟶ Hom_D(Khocolim, L) ⟶
\varprojlim_n Hom_D(K_n, L) ⟶ 0`. -/
@[stacks 0CQX]
theorem hom_from_homotopyColimit_shortExact
    (L : D) {K : ℕ → D} (f : ∀ n, K n ⟶ K (n + 1))
    [HasCoproduct (Functor.ofSequence f).obj]
    {Khocolim : D} (hKhocolim : IsHomotopyColimitOf (Functor.ofSequence f) Khocolim) :
    ∃ (ι :
        firstDerivedLimit ((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj (L⟦(-1 : ℤ)⟧)) ⟶
          (preadditiveYoneda.obj L).obj (op Khocolim))
      (π :
        (preadditiveYoneda.obj L).obj (op Khocolim) ⟶
          limit ((Functor.ofSequence f).op ⋙ preadditiveYoneda.obj L))
      (h :
        ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  obtain ⟨g, hδ, htriangle⟩ := hKhocolim
  rcases hom_from_homotopyColimit_shortExact_of_triangle L f g hδ htriangle with
    ⟨ι, hι, hshort⟩
  exact ⟨ι, homFromHomotopyColimitComparison L f g hδ htriangle, hι, hshort⟩

end

end CategoryTheory
