import Mathlib
import Mathlib.CategoryTheory.Idempotents.Basic
import StacksProject_2024.Chap04.Lemma_4_22_3
import StacksProject_2024.Chap12.Definition_12_31_2
import StacksProject_2024.Chap12.Lemma_12_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite
open CategoryTheory.Limits

universe u v

namespace CategoryTheory

namespace SequentialInverseSystem

variable {A : Type u} [Category.{v} A] [Preadditive A]

/- Domain-style sampling for Lemma 12.31.5 in the sequential inverse-system / split-limit domain:
- sampled owner-level declarations:
  * `SequentialInverseSystem` in `Definition_12_31_2`
  * `SequentialInverseSystem.transitionMap` in `Definition_12_31_2`
  * `SequentialInverseSystem.shift` in `Definition_12_31_2`
  * `HasEventuallySplitLimit` in `Lemma_12_30_1`
  * `essentiallyConstantCofilteredDiagram_iff_hasEventuallySplitLimit` in `Lemma_12_30_1`
  * `BinaryBiproductData` in mathlib's binary-biproduct API
- best owner abstractions:
  * primitive tail owners: `SequentialInverseSystem.shift` for the shifted tail of `F`, and
    `SequentialInverseSystem` for the complementary system
  * chapter bridge owner: `HasEventuallySplitLimit`

Primitive-vs-derived split:
- primitive source-facing data: an actual limit cone `c : LimitCone F`, a tail index `N`, the
  shifted tail owner `F.shift N`, and for each shifted stage `j` a direct-sum decomposition of
  `(F.shift N).obj (op j)` into the limit object `c.cone.pt` and the `j`-th object of a
  complementary sequential inverse system `Z`, together with the induced tail comparison maps read
  directly from `(F.shift N).transitionMap` and `Z.transitionMap`.
- derived API: the owner-level criterion `HasEventuallySplitLimit F`, and hence the canonical
  essential-constancy predicate on the cofiltered diagram `F`.

Source/core/bridge triage:
- `source-facing`: `HasLimitTailDecomposition`, which is the sequential tail decomposition stated
  in the Stacks lemma.
- `core/canonical`: `HasEventuallySplitLimit F` and `IsEssentiallyConstantCofilteredDiagram F`.
- `bridge/view`: `hasEventuallySplitLimit_iff` and
  `essentiallyConstant_iff_hasLimitTailDecomposition`, which identify the source-facing sequential
  criterion with the chapter owner abstractions. -/

private def tailDecompositionMap
    {X Y Z : A} (bY : BinaryBiproductData X Y) (bZ : BinaryBiproductData X Z) (f : Y ⟶ Z) :
    bY.bicone.pt ⟶ bZ.bicone.pt :=
  let hZ : IsLimit bZ.bicone.toCone := bZ.isBilimit.isLimit
  hZ.lift (BinaryFan.mk bY.bicone.fst (bY.bicone.snd ≫ f))

/-- Helper for Lemma 12.31.5: the transported map between two tail decompositions preserves the
stable summand coordinate. -/
private theorem tailDecompositionMap_fst
    {X Y Z : A} (bY : BinaryBiproductData X Y) (bZ : BinaryBiproductData X Z) (f : Y ⟶ Z) :
    tailDecompositionMap bY bZ f ≫ bZ.bicone.fst = bY.bicone.fst := by
  -- Read the first coordinate from the universal property used to define `tailDecompositionMap`.
  let hZ : IsLimit bZ.bicone.toCone := bZ.isBilimit.isLimit
  simpa [tailDecompositionMap, hZ] using
    hZ.fac (BinaryFan.mk bY.bicone.fst (bY.bicone.snd ≫ f)) ⟨WalkingPair.left⟩

/-- Helper for Lemma 12.31.5: the transported map between two tail decompositions carries the
complementary coordinate by the given morphism `f`. -/
private theorem tailDecompositionMap_snd
    {X Y Z : A} (bY : BinaryBiproductData X Y) (bZ : BinaryBiproductData X Z) (f : Y ⟶ Z) :
    tailDecompositionMap bY bZ f ≫ bZ.bicone.snd = bY.bicone.snd ≫ f := by
  -- Read the second coordinate from the same universal property.
  let hZ : IsLimit bZ.bicone.toCone := bZ.isBilimit.isLimit
  simpa [tailDecompositionMap, hZ] using
    hZ.fac (BinaryFan.mk bY.bicone.fst (bY.bicone.snd ≫ f)) ⟨WalkingPair.right⟩

/-- Helper for Lemma 12.31.5: the transition map to an earlier stage factors through every
intermediate stage. -/
private theorem transitionMap_comp
    (F : SequentialInverseSystem A) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    F.transitionMap (Nat.le_trans hij hjk) = F.transitionMap hjk ≫ F.transitionMap hij := by
  -- The unique morphism `k ⟶ i` in `ℕᵒᵖ` factors through the intermediate stage `j`.
  have hh :
      (homOfLE (Nat.le_trans hij hjk)).op = (homOfLE hjk).op ≫ (homOfLE hij).op := by
    subsingleton
  simpa [SequentialInverseSystem.transitionMap, Functor.map_comp] using congrArg F.map hh

/-- Helper for Lemma 12.31.5: a split mono `ι : A₀ ⟶ X` yields an on-the-nose binary biproduct
decomposition of `X` with stable summand `A₀`. -/
private theorem split_mono_complement_data [IsIdempotentComplete A]
    {A₀ X : A} {ι : A₀ ⟶ X} (σ : SplitMono ι) :
    ∃ Z : A, ∃ i : Z ⟶ X, ∃ e : X ⟶ Z,
      i ≫ e = 𝟙 Z ∧
        ι ≫ e = 0 ∧
          i ≫ σ.retraction = 0 ∧
            σ.retraction ≫ ι + e ≫ i = 𝟙 X := by
  let p : X ⟶ X := σ.retraction ≫ ι
  have hp : p ≫ p = p := by
    -- Proof comment: `p` is the projector onto the stable summand because `ι ≫ σ.retraction = 𝟙`.
    dsimp [p]
    calc
      (σ.retraction ≫ ι) ≫ (σ.retraction ≫ ι)
          = σ.retraction ≫ (ι ≫ σ.retraction) ≫ ι := by
              simp [Category.assoc]
      _ = σ.retraction ≫ ι := by
            simp [σ.id]
  rcases IsIdempotentComplete.idempotents_split X (𝟙 X - p) (Idempotents.idem_of_id_sub_idem p hp) with
    ⟨Z, i, e, hi, hei⟩
  refine ⟨Z, i, e, hi, ?_, ?_, ?_⟩
  · -- Proof comment: the complementary projection vanishes on the stable summand.
    have hzero : ι ≫ e ≫ i = 0 := by
      calc
        ι ≫ e ≫ i = ι ≫ (e ≫ i) := by
          rfl
        _ = ι ≫ (𝟙 X - p) := by
          rw [hei]
        _ = 0 := by
          dsimp [p]
          simp [sub_eq_add_neg]
    have hzero' := congrArg (fun f ↦ f ≫ e) hzero
    simpa [Category.assoc, hi] using hzero'
  · -- Proof comment: the complementary inclusion lands in the kernel of the stable retraction.
    have hzero : i ≫ p = 0 := by
      calc
        i ≫ p = i ≫ (σ.retraction ≫ ι) := by rfl
        _ = 0 := by
              have hcomp : i = i ≫ (𝟙 X - p) := by
                calc
                  i = (i ≫ e) ≫ i := by simp [hi]
                  _ = i ≫ (e ≫ i) := by simp [Category.assoc]
                  _ = i ≫ (𝟙 X - p) := by rw [hei]
              have hsum : i = i + -(i ≫ p) := by
                simpa [sub_eq_add_neg, Category.assoc] using hcomp
              have hcancel := congrArg (fun f ↦ -i + f) hsum
              simpa [add_assoc] using hcancel
    have hzeroι : i ≫ σ.retraction ≫ ι = 0 := by
      simpa [p, Category.assoc] using hzero
    have hzero' := congrArg (fun f ↦ f ≫ σ.retraction) hzeroι
    simpa [Category.assoc, σ.id] using hzero'
  · -- Proof comment: the stable projector and complementary projector sum to the identity.
    simpa [p, hei]

/-- Helper for Lemma 12.31.5: a split mono `ι : A₀ ⟶ X` yields an on-the-nose binary biproduct
decomposition of `X` with stable summand `A₀`. -/
private theorem binary_biproduct_data_of_split_mono [IsIdempotentComplete A]
    {A₀ X : A} {ι : A₀ ⟶ X} (σ : SplitMono ι) :
    ∃ Z : A, Nonempty (BinaryBiproductData A₀ Z) := by
  rcases split_mono_complement_data (A := A) (A₀ := A₀) (X := X) σ with
    ⟨Z, i, e, hi, hιe, hir, htotal⟩
  let b : BinaryBicone A₀ Z :=
    { pt := X
      fst := σ.retraction
      snd := e
      inl := ι
      inr := i
      inl_fst := σ.id
      inl_snd := hιe
      inr_fst := hir
      inr_snd := hi }
  let B : BinaryBiproductData A₀ Z :=
    { bicone := b
      isBilimit := isBinaryBilimitOfTotal b htotal }
  exact ⟨Z, ⟨B⟩⟩

/-- Helper for Lemma 12.31.5: the retractions induced from the distinguished split mono are
compatible with every transition map in the shifted tail. -/
private theorem tail_retraction_naturality
    {F : SequentialInverseSystem A} {c : LimitCone F} {N : ℕ}
    (σ : SplitMono (c.cone.π.app (op N))) {i j : ℕ} (hij : i ≤ j) :
    (F.shift N).transitionMap hij ≫
        (F.transitionMap (Nat.le_add_right N i) ≫ σ.retraction) =
      F.transitionMap (Nat.le_add_right N j) ≫ σ.retraction := by
  -- Rewrite the shifted transition map as a composite through the intermediate tail stage.
  have hcomp :=
    transitionMap_comp (F := F) (Nat.le_add_right N i) (Nat.add_le_add_left hij N)
  simpa [SequentialInverseSystem.shift_transitionMap, Category.assoc] using
    congrArg (fun k ↦ k ≫ σ.retraction) hcomp.symm

/-- Helper for Lemma 12.31.5: if a map between two chosen decompositions sends the stable
inclusion to the stable inclusion, then its right coordinate is read off from the source `inr` and
target `snd`. -/
private theorem snd_comp_eq_snd_tail_coordinate
    {X Y Z : A} (bY : BinaryBiproductData X Y) (bZ : BinaryBiproductData X Z)
    {g : bY.bicone.pt ⟶ bZ.bicone.pt}
    (hginl : bY.bicone.inl ≫ g = bZ.bicone.inl) :
    g ≫ bZ.bicone.snd =
      bY.bicone.snd ≫ (bY.bicone.inr ≫ g ≫ bZ.bicone.snd) := by
  -- Proof comment: expand the identity on the source stage into its two biproduct coordinates,
  -- then the left term vanishes because `g` preserves the stable inclusion.
  calc
    g ≫ bZ.bicone.snd = (𝟙 bY.bicone.pt) ≫ g ≫ bZ.bicone.snd := by simp
    _ =
        (bY.bicone.fst ≫ bY.bicone.inl + bY.bicone.snd ≫ bY.bicone.inr) ≫ g ≫
          bZ.bicone.snd := by
            rw [IsBilimit.binary_total bY.isBilimit]
    _ =
        bY.bicone.fst ≫ bY.bicone.inl ≫ g ≫ bZ.bicone.snd +
          bY.bicone.snd ≫ bY.bicone.inr ≫ g ≫ bZ.bicone.snd := by
            simp [Category.assoc]
    _ = bY.bicone.fst ≫ bZ.bicone.inl ≫ bZ.bicone.snd +
          bY.bicone.snd ≫ bY.bicone.inr ≫ g ≫ bZ.bicone.snd := by
            simpa [Category.assoc] using
              congrArg
                (fun f ↦ bY.bicone.fst ≫ f ≫ bZ.bicone.snd +
                  bY.bicone.snd ≫ bY.bicone.inr ≫ g ≫ bZ.bicone.snd)
                hginl
    _ = bY.bicone.snd ≫ (bY.bicone.inr ≫ g ≫ bZ.bicone.snd) := by
          simp

/-- Helper for Lemma 12.31.5: once a map preserves the stable retraction and stable inclusion, it
is the canonical `tailDecompositionMap` attached to its complementary coordinate. -/
private theorem eq_tailDecompositionMap_of_fst
    {X Y Z : A} (bY : BinaryBiproductData X Y) (bZ : BinaryBiproductData X Z)
    {g : bY.bicone.pt ⟶ bZ.bicone.pt}
    (hgfst : g ≫ bZ.bicone.fst = bY.bicone.fst)
    (hginl : bY.bicone.inl ≫ g = bZ.bicone.inl) :
    g = tailDecompositionMap bY bZ (bY.bicone.inr ≫ g ≫ bZ.bicone.snd) := by
  -- Proof comment: the target biproduct is a limit cone, so it suffices to compare the stable
  -- and complementary coordinates after postcomposing with `fst` and `snd`.
  apply BinaryFan.IsLimit.hom_ext bZ.isBilimit.isLimit
  · simpa [tailDecompositionMap_fst] using hgfst
  · simpa [tailDecompositionMap_snd] using
      snd_comp_eq_snd_tail_coordinate bY bZ hginl

/-- Helper for Lemma 12.31.5: a zero complementary map gives the pure stable-summand inclusion
between the two decomposed stages. -/
private theorem tailDecompositionMap_zero
    {X Y Z : A} (bY : BinaryBiproductData X Y) (bZ : BinaryBiproductData X Z) :
    tailDecompositionMap bY bZ 0 = bY.bicone.fst ≫ bZ.bicone.inl := by
  -- Compare the two maps by reading their coordinates on the target biproduct.
  apply BinaryFan.IsLimit.hom_ext bZ.isBilimit.isLimit
  · simp [tailDecompositionMap_fst]
  · simp [tailDecompositionMap_snd]

/-- Helper for Lemma 12.31.5: the canonical maps between tail decompositions compose by composing
their complementary coordinates. -/
private theorem tailDecompositionMap_comp
    {W X Y Z : A} (bW : BinaryBiproductData X W) (bY : BinaryBiproductData X Y)
    (bZ : BinaryBiproductData X Z) (f : W ⟶ Y) (g : Y ⟶ Z) :
    tailDecompositionMap bW bY f ≫ tailDecompositionMap bY bZ g =
      tailDecompositionMap bW bZ (f ≫ g) := by
  -- Proof comment: both composites have the same stable coordinate and the same complementary
  -- coordinate, so the target biproduct universal property identifies them.
  apply BinaryFan.IsLimit.hom_ext bZ.isBilimit.isLimit
  · simp [Category.assoc, tailDecompositionMap_fst]
  · calc
      (tailDecompositionMap bW bY f ≫ tailDecompositionMap bY bZ g) ≫ bZ.bicone.snd
          = tailDecompositionMap bW bY f ≫ (tailDecompositionMap bY bZ g ≫ bZ.bicone.snd) := by
              simp [Category.assoc]
      _ = tailDecompositionMap bW bY f ≫ (bY.bicone.snd ≫ g) := by
            rw [tailDecompositionMap_snd]
      _ = (tailDecompositionMap bW bY f ≫ bY.bicone.snd) ≫ g := by
            simp [Category.assoc]
      _ = bW.bicone.snd ≫ f ≫ g := by
            rw [tailDecompositionMap_snd]
            simp [Category.assoc]
      _ = tailDecompositionMap bW bZ (f ≫ g) ≫ bZ.bicone.snd := by
            rw [tailDecompositionMap_snd]

/-- Helper for Lemma 12.31.5: a tail decomposition identity immediately recovers the stable
projection formula by postcomposing with `fst`. -/
private theorem tail_transition_fst_of_decomposition
    {F : SequentialInverseSystem A} {c : LimitCone F} {N : ℕ} {Z : SequentialInverseSystem A}
    {B : ∀ j, BinaryBiproductData c.cone.pt (Z.obj (op j))}
    {e : ∀ j, (F.shift N).obj (op j) ≅ (B j).bicone.pt}
    (htrans : ∀ {i j : ℕ} (hij : i ≤ j),
      (F.shift N).transitionMap hij =
        (e j).hom ≫ tailDecompositionMap (B j) (B i) (Z.transitionMap hij) ≫ (e i).inv)
    {i j : ℕ} (hij : i ≤ j) :
    ((e j).inv ≫ (F.shift N).transitionMap hij ≫ (e i).hom) ≫ (B i).bicone.fst =
      (B j).bicone.fst := by
  -- Proof comment: transport the transition into the chosen biproduct models and read off its
  -- first coordinate.
  have h :=
    congrArg (fun k ↦ (e j).inv ≫ k ≫ (e i).hom ≫ (B i).bicone.fst) (htrans hij)
  simpa [Category.assoc, tailDecompositionMap_fst] using h

/-- Helper for Lemma 12.31.5: a pure stable map has zero right coordinate in any target
decomposition. -/
private theorem pure_stable_right_coordinate_zero
    {X Y Z : A} (bY : BinaryBiproductData X Y) (bZ : BinaryBiproductData X Z) :
    bY.bicone.inr ≫ (bY.bicone.fst ≫ bZ.bicone.inl) ≫ bZ.bicone.snd = 0 := by
  -- Proof comment: the stable part vanishes immediately after projecting to the complementary
  -- coordinate.
  simp [Category.assoc]

/-- Lemma 12.31.5: a sequential inverse system admits a split limit tail when, after shifting by
some index `N`, the shifted system `F.shift N` is identified stagewise with the direct sum of the
actual inverse limit `c.cone.pt` and a complementary sequential inverse system `Z`, the transition
maps preserve the limit summand, and the complementary transition maps are eventually zero. -/
def HasLimitTailDecomposition (F : SequentialInverseSystem A) : Prop :=
  ∃ c : LimitCone F,
    ∃ N : ℕ,
      ∃ Z : SequentialInverseSystem A,
        ∃ B : ∀ j, BinaryBiproductData c.cone.pt (Z.obj (op j)),
          ∃ e : ∀ j, (F.shift N).obj (op j) ≅ (B j).bicone.pt,
            (∀ j, c.cone.π.app (op (N + j)) = (B j).bicone.inl ≫ (e j).inv) ∧
              (∀ {i j : ℕ} (hij : i ≤ j),
                (F.shift N).transitionMap hij =
                  (e j).hom ≫ tailDecompositionMap (B j) (B i) (Z.transitionMap hij) ≫
                    (e i).inv) ∧
                ∀ i : ℕ, ∃ j : ℕ, ∃ hij : i ≤ j, Z.transitionMap hij = 0

-- Proof sketch: pass from the owner-level criterion `HasEventuallySplitLimit F` to a cofinal tail
-- of `ℕᵒᵖ`, identify an initial full subcategory with another sequential inverse system, and
-- rewrite the splitting data from Lemma 12.30.1 as explicit biproduct decompositions of the tail
-- stages. The eventual-vanishing clause is the translated form of the condition that the
-- complementary summand is killed by some earlier transition map.
/-- Bridge theorem for Lemma 12.31.5: the chapter owner `HasEventuallySplitLimit F` is equivalent
to the explicit sequential tail decomposition with actual limit object and eventually vanishing
complementary transition maps. -/
-- TODO: finish the stagewise packaging step by converting the split retractions obtained from
-- `isEssentiallyConstantCofilteredCone_iff` into the `BinaryBiproductData` witnesses required by
-- `HasLimitTailDecomposition`, then read the complementary transition maps through
-- `tailDecompositionMap_fst` and `tailDecompositionMap_snd`.
theorem hasEventuallySplitLimit_iff [IsIdempotentComplete A] (F : SequentialInverseSystem A) :
    HasEventuallySplitLimit F ↔ HasLimitTailDecomposition F := by
  sorry

/-- A sequential inverse system is essentially constant if and only if it admits the source-facing
tail decomposition from Lemma 12.31.5. -/
theorem essentiallyConstant_iff_hasLimitTailDecomposition [IsIdempotentComplete A]
    (F : SequentialInverseSystem A) :
    IsEssentiallyConstantCofilteredDiagram F ↔ HasLimitTailDecomposition F := by
  rw [essentiallyConstantCofilteredDiagram_iff_hasEventuallySplitLimit, hasEventuallySplitLimit_iff]

end SequentialInverseSystem

end CategoryTheory
