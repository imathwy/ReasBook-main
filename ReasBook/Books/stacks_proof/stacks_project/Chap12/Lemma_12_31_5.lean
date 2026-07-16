import Mathlib
import Mathlib.CategoryTheory.Idempotents.Basic
import stacks_proof.stacks_project.Chap04.Lemma_4_22_3
import stacks_proof.stacks_project.Chap12.Definition_12_31_2
import stacks_proof.stacks_project.Chap12.Lemma_12_30_1

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

/-- Helper for Lemma 12.31.5: the raw complementary coordinate of `tailDecompositionMap` is
exactly the map used to build it. -/
private theorem tailDecompositionMap_rightCoordinate
    {X Y Z : A} (bY : BinaryBiproductData X Y) (bZ : BinaryBiproductData X Z) (f : Y ⟶ Z) :
    bY.bicone.inr ≫ tailDecompositionMap bY bZ f ≫ bZ.bicone.snd = f := by
  -- Proof comment: first read the right coordinate from the target biproduct, then cancel the
  -- source complementary projector with `inr ≫ snd = 𝟙`.
  calc
    bY.bicone.inr ≫ tailDecompositionMap bY bZ f ≫ bZ.bicone.snd
        = bY.bicone.inr ≫ (tailDecompositionMap bY bZ f ≫ bZ.bicone.snd) := by
            simp
    _ = bY.bicone.inr ≫ (bY.bicone.snd ≫ f) := by
          rw [tailDecompositionMap_snd]
    _ = (bY.bicone.inr ≫ bY.bicone.snd) ≫ f := by
          simp
    _ = f := by
          simp

section

omit [Preadditive A]

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

/-- Helper for Lemma 12.31.5: cone legs compose with sequential transition maps by naturality. -/
private theorem coneLeg_transition
    {F : SequentialInverseSystem A} {c : Cone F} {i j : ℕ} (hij : i ≤ j) :
    c.π.app (op j) ≫ F.transitionMap hij = c.π.app (op i) := by
  -- Proof comment: this is exactly the naturality square of the cone at the unique map
  -- `op j ⟶ op i` induced by the inequality `i ≤ j`.
  simpa using c.π.naturality ((homOfLE hij).op)

end

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

section

omit [Preadditive A]

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

end

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

section

omit [Preadditive A]

/-- Helper for Lemma 12.31.5: the distinguished split mono at stage `N` induces a retraction
identity on every later tail stage by precomposing with the sequential transition map. -/
private theorem tailStageRetraction_id
    {F : SequentialInverseSystem A} {c : LimitCone F} {N j : ℕ}
    (σ : SplitMono (c.cone.π.app (op N))) :
    c.cone.π.app (op (N + j)) ≫ (F.transitionMap (Nat.le_add_right N j) ≫ σ.retraction) =
      𝟙 c.cone.pt := by
  -- Proof comment: cone naturality identifies the later cone leg with the distinguished leg
  -- followed by the transition map back to stage `N`.
  have hleg :
      c.cone.π.app (op (N + j)) ≫ F.transitionMap (Nat.le_add_right N j) =
        c.cone.π.app (op N) :=
    coneLeg_transition (F := F) (c := c.cone) (Nat.le_add_right N j)
  have hcomp :
      c.cone.π.app (op (N + j)) ≫ (F.transitionMap (Nat.le_add_right N j) ≫ σ.retraction) =
        c.cone.π.app (op N) ≫ σ.retraction := by
    simpa [Category.assoc] using congrArg (fun f ↦ f ≫ σ.retraction) hleg
  exact hcomp.trans (by simpa using σ.id)

end

/-- Helper for Lemma 12.31.5: each later tail stage inherits a raw complement package from the
distinguished split mono at stage `N`. -/
private theorem tailStageComplementPackage [IsIdempotentComplete A]
    {F : SequentialInverseSystem A} (c : LimitCone F) (N : ℕ)
    (σ : SplitMono (c.cone.π.app (op N))) (j : ℕ) :
    ∃ Zj : A, ∃ inr_j : Zj ⟶ F.obj (op (N + j)), ∃ snd_j : F.obj (op (N + j)) ⟶ Zj,
      inr_j ≫ snd_j = 𝟙 Zj ∧
        c.cone.π.app (op (N + j)) ≫ snd_j = 0 ∧
          inr_j ≫ (F.transitionMap (Nat.le_add_right N j) ≫ σ.retraction) = 0 ∧
            (F.transitionMap (Nat.le_add_right N j) ≫ σ.retraction) ≫
                c.cone.π.app (op (N + j)) + snd_j ≫ inr_j =
              𝟙 (F.obj (op (N + j))) := by
  -- Proof comment: the later cone leg remains split by composing the tail transition to stage `N`
  -- with the chosen retraction there, so `split_mono_complement_data` applies on the exact stage.
  let σj : SplitMono (c.cone.π.app (op (N + j))) :=
    { retraction := F.transitionMap (Nat.le_add_right N j) ≫ σ.retraction
      id := tailStageRetraction_id (F := F) (c := c) (N := N) (j := j) σ }
  exact split_mono_complement_data (A := A) σj

/-- Helper for Lemma 12.31.5: once a complementary transition map is zero, the corresponding tail
transition is the pure stable-summand map. -/
private theorem tailTransition_eq_pureStable_of_zero
    {F : SequentialInverseSystem A} {c : LimitCone F} {N : ℕ} {Z : SequentialInverseSystem A}
    {B : ∀ j, BinaryBiproductData c.cone.pt (Z.obj (op j))}
    {e : ∀ j, (F.shift N).obj (op j) ≅ (B j).bicone.pt}
    (htrans : ∀ {i j : ℕ} (hij : i ≤ j),
      (F.shift N).transitionMap hij =
        (e j).hom ≫ tailDecompositionMap (B j) (B i) (Z.transitionMap hij) ≫ (e i).inv)
    {i j : ℕ} (hij : i ≤ j) (hz : Z.transitionMap hij = 0) :
    (F.shift N).transitionMap hij =
      (e j).hom ≫ (B j).bicone.fst ≫ (B i).bicone.inl ≫ (e i).inv := by
  -- Proof comment: substitute the vanishing complementary coordinate and collapse the canonical
  -- decomposition map to the stable-summand component via `tailDecompositionMap_zero`.
  rw [htrans hij, hz, tailDecompositionMap_zero]
  simp [Category.assoc]

/-- Helper for Lemma 12.31.5: the raw complementary coordinates chosen from
`tailStageComplementPackage` already satisfy the sequential composition law before any
normalization through `tailDecompositionMap`. -/
private theorem tailComplementTransition_comp
    {F : SequentialInverseSystem A} {c : LimitCone F} {N : ℕ}
    (σ : SplitMono (c.cone.π.app (op N))) {Zobj : ℕ → A}
    (inr : ∀ j, Zobj j ⟶ F.obj (op (N + j)))
    (snd : ∀ j, F.obj (op (N + j)) ⟶ Zobj j)
    (hret_zero : ∀ j,
      inr j ≫ (F.transitionMap (Nat.le_add_right N j) ≫ σ.retraction) = 0)
    (htotal : ∀ j,
      (F.transitionMap (Nat.le_add_right N j) ≫ σ.retraction) ≫
          c.cone.π.app (op (N + j)) + snd j ≫ inr j =
        𝟙 (F.obj (op (N + j))))
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    inr k ≫ F.transitionMap (Nat.add_le_add_left (Nat.le_trans hij hjk) N) ≫ snd i =
      (inr k ≫ F.transitionMap (Nat.add_le_add_left hjk N) ≫ snd j) ≫
        (inr j ≫ F.transitionMap (Nat.add_le_add_left hij N) ≫ snd i) := by
  -- Proof comment: insert the biproduct identity at the intermediate exact stage `N + j`; the
  -- projector term dies after `inr k`, so only the raw complementary coordinate survives.
  have hkill :
      inr k ≫ F.transitionMap (Nat.add_le_add_left hjk N) ≫
          (F.transitionMap (Nat.le_add_right N j) ≫ σ.retraction) =
        0 := by
    calc
      inr k ≫ F.transitionMap (Nat.add_le_add_left hjk N) ≫
          (F.transitionMap (Nat.le_add_right N j) ≫ σ.retraction)
          =
            inr k ≫ (F.transitionMap (Nat.le_add_right N k) ≫ σ.retraction) := by
              simpa [Category.assoc] using
                congrArg (fun t ↦ inr k ≫ t)
                  (tail_retraction_naturality (F := F) (c := c) (N := N) σ hjk)
      _ = 0 := hret_zero k
  have hfirst :
      inr k ≫ F.transitionMap (Nat.add_le_add_left hjk N) ≫
          (((F.transitionMap (Nat.le_add_right N j) ≫ σ.retraction) ≫
              c.cone.π.app (op (N + j))) ≫ F.transitionMap (Nat.add_le_add_left hij N) ≫
            snd i) =
        0 := by
    calc
      inr k ≫ F.transitionMap (Nat.add_le_add_left hjk N) ≫
          (((F.transitionMap (Nat.le_add_right N j) ≫ σ.retraction) ≫
              c.cone.π.app (op (N + j))) ≫ F.transitionMap (Nat.add_le_add_left hij N) ≫
            snd i)
          =
            (inr k ≫ F.transitionMap (Nat.add_le_add_left hjk N) ≫
                (F.transitionMap (Nat.le_add_right N j) ≫ σ.retraction)) ≫
              (c.cone.π.app (op (N + j)) ≫ F.transitionMap (Nat.add_le_add_left hij N)) ≫
                snd i := by
                simp [Category.assoc]
      _ =
            (inr k ≫ F.transitionMap (Nat.add_le_add_left hjk N) ≫
                (F.transitionMap (Nat.le_add_right N j) ≫ σ.retraction)) ≫
              c.cone.π.app (op (N + i)) ≫ snd i := by
                simpa [Category.assoc] using
                  congrArg
                    (fun t ↦
                      (inr k ≫ F.transitionMap (Nat.add_le_add_left hjk N) ≫
                          (F.transitionMap (Nat.le_add_right N j) ≫ σ.retraction)) ≫
                        t ≫ snd i)
                    (coneLeg_transition (F := F) (c := c.cone) (Nat.add_le_add_left hij N))
      _ = 0 := by
            -- Proof comment: postcompose the already-vanishing projector term all the way to the
            -- target complementary coordinate, then normalize the resulting zero composite.
            have hkill_i :
                (inr k ≫ F.transitionMap (Nat.add_le_add_left hjk N) ≫
                    F.transitionMap (Nat.le_add_right N j) ≫ σ.retraction) ≫
                      c.cone.π.app (op (N + i)) ≫ snd i =
                    0 ≫ c.cone.π.app (op (N + i)) ≫ snd i := by
              simpa [Category.assoc] using
                congrArg
                  (fun t ↦ t ≫ c.cone.π.app (op (N + i)) ≫ snd i)
                  hkill
            calc
              (inr k ≫ F.transitionMap (Nat.add_le_add_left hjk N) ≫
                  F.transitionMap (Nat.le_add_right N j) ≫ σ.retraction) ≫
                    c.cone.π.app (op (N + i)) ≫ snd i =
                  0 ≫ c.cone.π.app (op (N + i)) ≫ snd i := hkill_i
              _ = 0 := by
                    rw [zero_comp]
  calc
    inr k ≫ F.transitionMap (Nat.add_le_add_left (Nat.le_trans hij hjk) N) ≫ snd i
        =
          inr k ≫ (F.transitionMap (Nat.add_le_add_left hjk N) ≫
            F.transitionMap (Nat.add_le_add_left hij N)) ≫ snd i := by
              rw [transitionMap_comp (F := F) (Nat.add_le_add_left hij N)
                (Nat.add_le_add_left hjk N)]
    _ =
          inr k ≫ F.transitionMap (Nat.add_le_add_left hjk N) ≫
            (𝟙 (F.obj (op (N + j)))) ≫ F.transitionMap (Nat.add_le_add_left hij N) ≫ snd i := by
              simp [Category.assoc]
    _ =
          inr k ≫ F.transitionMap (Nat.add_le_add_left hjk N) ≫
            (((F.transitionMap (Nat.le_add_right N j) ≫ σ.retraction) ≫
                c.cone.π.app (op (N + j))) + snd j ≫ inr j) ≫
              F.transitionMap (Nat.add_le_add_left hij N) ≫ snd i := by
              rw [← htotal j]
    _ =
          inr k ≫ F.transitionMap (Nat.add_le_add_left hjk N) ≫
            (((F.transitionMap (Nat.le_add_right N j) ≫ σ.retraction) ≫
                c.cone.π.app (op (N + j))) ≫ F.transitionMap (Nat.add_le_add_left hij N) ≫
              snd i) +
          inr k ≫ F.transitionMap (Nat.add_le_add_left hjk N) ≫
            ((snd j ≫ inr j) ≫ F.transitionMap (Nat.add_le_add_left hij N) ≫ snd i) := by
              simp [Preadditive.comp_add, Preadditive.add_comp, Category.assoc]
    _ =
          0 +
            inr k ≫ F.transitionMap (Nat.add_le_add_left hjk N) ≫
              ((snd j ≫ inr j) ≫ F.transitionMap (Nat.add_le_add_left hij N) ≫ snd i) := by
              rw [hfirst]
    _ =
          (inr k ≫ F.transitionMap (Nat.add_le_add_left hjk N) ≫ snd j) ≫
            (inr j ≫ F.transitionMap (Nat.add_le_add_left hij N) ≫ snd i) := by
              simp [Category.assoc]

/-- Helper for Lemma 12.31.5: in a tail decomposition, the transition back to the base stage,
followed by the base-stage stable projector, recovers the stable projector at every later stage. -/
private theorem transitionToBaseStage_eq_stableProjector
    {F : SequentialInverseSystem A} {c : LimitCone F} {N : ℕ} {Z : SequentialInverseSystem A}
    {B : ∀ j, BinaryBiproductData c.cone.pt (Z.obj (op j))}
    {e : ∀ j, (F.shift N).obj (op j) ≅ (B j).bicone.pt}
    (htrans : ∀ {i j : ℕ} (hij : i ≤ j),
      (F.shift N).transitionMap hij =
        (e j).hom ≫ tailDecompositionMap (B j) (B i) (Z.transitionMap hij) ≫ (e i).inv)
    (j : ℕ) :
    F.transitionMap (Nat.le_add_right N j) ≫ ((e 0).hom ≫ (B 0).bicone.fst) =
      (e j).hom ≫ (B j).bicone.fst := by
  -- Proof comment: the base-stage transition is the case `i = 0` of the tail decomposition, and
  -- postcomposing with `fst` reads off the stable projector at stage `j`.
  have hfst :=
    tail_transition_fst_of_decomposition (F := F) (c := c) (N := N) (Z := Z) (B := B) (e := e)
      htrans (i := 0) (j := j) (Nat.zero_le j)
  have h := congrArg (fun t ↦ (e j).hom ≫ t) hfst
  simpa [SequentialInverseSystem.shift_transitionMap, Category.assoc] using h

/-- Source-facing predicate for Lemma 12.31.5: a sequential inverse system admits a split limit
tail when, after shifting by
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
/-- Lemma 12.31.5: the chapter owner `HasEventuallySplitLimit F` is equivalent
to the explicit sequential tail decomposition with actual limit object and eventually vanishing
complementary transition maps. -/
theorem hasEventuallySplitLimit_iff [IsIdempotentComplete A] (F : SequentialInverseSystem A) :
    HasEventuallySplitLimit F ↔ HasLimitTailDecomposition F := by
  constructor
  · intro hF
    classical
    -- Pass from the owner-level split-limit criterion to an essentially constant limit cone.
    rw [← essentiallyConstantCofilteredDiagram_iff_hasEventuallySplitLimit] at hF
    rcases essentiallyConstantCofilteredDiagram_exists_essentiallyConstant_limitCone F hF with
      ⟨c, hc⟩
    rcases (isEssentiallyConstantCofilteredCone_iff c.cone).1 hc with ⟨i₀, σ, hfac⟩
    let N : ℕ := i₀.unop
    let σN : SplitMono (c.cone.π.app (op N)) := by
      simpa [N] using σ
    -- Choose the raw complement package on each literal stage `F.obj (op (N + j))`.
    choose Zobj inr snd hinr_snd hcone_zero hret_zero htotal using
      fun j : ℕ => tailStageComplementPackage (A := A) c N σN j
    let Z : SequentialInverseSystem A :=
      { obj := fun j ↦ Zobj j.unop
        map := by
          intro i j f
          exact inr i.unop ≫ (F.shift N).map f ≫ snd j.unop
        map_id := by
          intro j
          have hj : 𝟙 (op j.unop) = (homOfLE (Nat.le_refl j.unop)).op := by
            subsingleton
          rw [hj]
          simp [hinr_snd]
        map_comp := by
          -- Route correction: prove the complementary system law directly in the literal-stage
          -- spelling `F.obj (op (N + j))`, and defer all `tailDecompositionMap` normalization to
          -- the final adapter for `HasLimitTailDecomposition`.
          intro i j k f g
          let hij : k.unop ≤ j.unop := leOfHom g.unop
          let hjk : j.unop ≤ i.unop := leOfHom f.unop
          have hf : f = (homOfLE hjk).op := by
            subsingleton
          have hg : g = (homOfLE hij).op := by
            subsingleton
          have hfg : f ≫ g = (homOfLE (Nat.le_trans hij hjk)).op := by
            subsingleton
          simpa [hf, hg, hfg, SequentialInverseSystem.shift_transitionMap, Category.assoc] using
            tailComplementTransition_comp (F := F) (c := c) (N := N) σN inr snd hret_zero
              htotal hij hjk
        }
    let B : ∀ j, BinaryBiproductData c.cone.pt (Z.obj (op j)) := fun j ↦
      { bicone :=
          { pt := F.obj (op (N + j))
            fst := F.transitionMap (Nat.le_add_right N j) ≫ σN.retraction
            snd := snd j
            inl := c.cone.π.app (op (N + j))
            inr := inr j
            inl_fst := tailStageRetraction_id (F := F) (c := c) (N := N) (j := j) σN
            inl_snd := hcone_zero j
            inr_fst := hret_zero j
            inr_snd := hinr_snd j }
        isBilimit := isBinaryBilimitOfTotal _ (htotal j) }
    let e : ∀ j, (F.shift N).obj (op j) ≅ (B j).bicone.pt := fun j ↦ Iso.refl _
    refine ⟨c, N, Z, B, e, ?_, ?_, ?_⟩
    · intro j
      -- The chosen biproduct model lives on the literal tail stage itself.
      simp [B, e]
    · intro i j hij
      -- Compare the ambient tail transition with the canonical biproduct transport by its two
      -- coordinates.
      have hdecomp :
          (F.shift N).transitionMap hij =
            tailDecompositionMap (B j) (B i) ((B j).bicone.inr ≫
              (F.shift N).transitionMap hij ≫ (B i).bicone.snd) := by
        apply eq_tailDecompositionMap_of_fst (bY := B j) (bZ := B i)
        · dsimp [B]
          simpa [Category.assoc] using
            tail_retraction_naturality (F := F) (c := c) (N := N) σN hij
        · dsimp [B]
          simpa [SequentialInverseSystem.shift_transitionMap, Category.assoc] using
            coneLeg_transition (F := F) (c := c.cone) (Nat.add_le_add_left hij N)
      simpa [B, Z, e, Category.assoc] using hdecomp
    · intro i
      -- Reindex the owner witness to a literal stage `N + j`, then kill the complementary
      -- coordinate using the vanishing of the cone leg on `snd i`.
      rcases hfac (op (N + i)) with ⟨k, ki, kj, hk⟩
      have hNk : N ≤ k.unop := leOfHom ki.unop
      rcases Nat.exists_eq_add_of_le hNk with ⟨j, hjstage⟩
      have hkobj : k = op (N + j) := by
        simpa using congrArg op hjstage
      subst hkobj
      have hij : i ≤ j := by
        simpa using (leOfHom kj.unop : N + i ≤ N + j)
      refine ⟨j, hij, ?_⟩
      have hki : ki = (homOfLE (Nat.le_add_right N j)).op := by
        subsingleton
      have hkj : kj = (homOfLE (Nat.add_le_add_left hij N)).op := by
        subsingleton
      have hk' :
          F.transitionMap (Nat.add_le_add_left hij N) =
            F.transitionMap (Nat.le_add_right N j) ≫ σN.retraction ≫
              c.cone.π.app (op (N + i)) := by
        simpa [SequentialInverseSystem.transitionMap, hki, hkj] using hk
      calc
        Z.transitionMap hij
            = inr j ≫ F.transitionMap (Nat.add_le_add_left hij N) ≫ snd i := by
                rfl
        _ =
            inr j ≫
                (F.transitionMap (Nat.le_add_right N j) ≫ σN.retraction ≫
                  c.cone.π.app (op (N + i))) ≫
              snd i := by
                rw [hk']
        _ =
            inr j ≫ (F.transitionMap (Nat.le_add_right N j) ≫ σN.retraction) ≫
              (c.cone.π.app (op (N + i)) ≫ snd i) := by
                simp [Category.assoc]
        _ = 0 := by
              have hzeroi :
                  inr j ≫ (F.transitionMap (Nat.le_add_right N j) ≫ σN.retraction) ≫
                      (c.cone.π.app (op (N + i)) ≫ snd i) =
                    inr j ≫ (F.transitionMap (Nat.le_add_right N j) ≫ σN.retraction) ≫ 0 := by
                exact
                  congrArg
                    (fun t ↦
                      inr j ≫ (F.transitionMap (Nat.le_add_right N j) ≫ σN.retraction) ≫ t)
                    (hcone_zero i)
              calc
                inr j ≫ (F.transitionMap (Nat.le_add_right N j) ≫ σN.retraction) ≫
                    (c.cone.π.app (op (N + i)) ≫ snd i)
                    = inr j ≫ (F.transitionMap (Nat.le_add_right N j) ≫ σN.retraction) ≫ 0 :=
                      hzeroi
                _ = 0 := by
                      rw [comp_zero, comp_zero]
  · rintro ⟨c, N, Z, B, e, hπ, htrans, hzero⟩
    -- Repackage the explicit tail decomposition as the owner-level essential-constancy datum.
    rw [← essentiallyConstantCofilteredDiagram_iff_hasEventuallySplitLimit]
    refine ⟨c.cone, ?_⟩
    rw [isEssentiallyConstantCofilteredCone_iff]
    let σ0 : SplitMono (c.cone.π.app (op N)) :=
      { retraction := (e 0).hom ≫ (B 0).bicone.fst
        id := by
          -- The stage-zero cone leg is exactly the chosen stable inclusion in the biproduct
          -- model, so its retraction is read off from the `fst` projector there.
          simpa [Category.assoc] using
            congrArg (fun t ↦ t ≫ (e 0).hom ≫ (B 0).bicone.fst) (hπ 0) }
    refine ⟨op N, σ0, ?_⟩
    intro j
    -- Apply the eventual-zero witness at the shifted stage `j.unop`, then compose the pure stable
    -- tail map once with the cone leg back to the original stage `j`.
    rcases hzero j.unop with ⟨k, hjk, hzk⟩
    let hj' : j.unop ≤ N + j.unop := Nat.le_add_left j.unop N
    let hk' : j.unop ≤ N + k := Nat.le_trans hj' (Nat.add_le_add_left hjk N)
    refine ⟨op (N + k), (homOfLE (Nat.le_add_right N k)).op, (homOfLE hk').op, ?_⟩
    have hpure :
        (F.shift N).transitionMap hjk =
          (e k).hom ≫ (B k).bicone.fst ≫ (B j.unop).bicone.inl ≫ (e j.unop).inv := by
      simpa using
        tailTransition_eq_pureStable_of_zero (F := F) (c := c) (N := N) (Z := Z) (B := B)
          (e := e) htrans (i := j.unop) (j := k) hjk hzk
    have hconeLeg :
        c.cone.π.app (op (N + j.unop)) ≫ F.transitionMap hj' = c.cone.π.app j := by
      simpa [Category.assoc] using coneLeg_transition (F := F) (c := c.cone) hj'
    have hcone :
        (B j.unop).bicone.inl ≫ (e j.unop).inv ≫ F.transitionMap hj' = c.cone.π.app j := by
      simpa [hπ j.unop, Category.assoc] using hconeLeg
    have hstable :
        F.transitionMap hk' = (e k).hom ≫ (B k).bicone.fst ≫ c.cone.π.app j := by
      calc
        F.transitionMap hk'
            = (F.shift N).transitionMap hjk ≫ F.transitionMap hj' := by
                simpa [hk', hj', SequentialInverseSystem.shift_transitionMap] using
                  transitionMap_comp (F := F) hj' (Nat.add_le_add_left hjk N)
        _ =
            ((e k).hom ≫ (B k).bicone.fst ≫ (B j.unop).bicone.inl ≫ (e j.unop).inv) ≫
              F.transitionMap hj' := by
                rw [hpure]
        _ =
            (e k).hom ≫ (B k).bicone.fst ≫
              ((B j.unop).bicone.inl ≫ (e j.unop).inv ≫ F.transitionMap hj') := by
                simp [Category.assoc]
        _ = (e k).hom ≫ (B k).bicone.fst ≫ c.cone.π.app j := by
              rw [hcone]
    have hbase :
        F.transitionMap (Nat.le_add_right N k) ≫ σ0.retraction ≫ c.cone.π.app j =
          (e k).hom ≫ (B k).bicone.fst ≫ c.cone.π.app j := by
      simpa [σ0, Category.assoc] using
        congrArg (fun t ↦ t ≫ c.cone.π.app j)
          (transitionToBaseStage_eq_stableProjector (F := F) (c := c) (N := N) (Z := Z)
            (B := B) (e := e) htrans k)
    exact hstable.trans hbase.symm

/-- A sequential inverse system is essentially constant if and only if it admits the source-facing
tail decomposition from Lemma 12.31.5. -/
@[stacks 070C]
theorem essentiallyConstant_iff_hasLimitTailDecomposition [IsIdempotentComplete A]
    (F : SequentialInverseSystem A) :
    IsEssentiallyConstantCofilteredDiagram F ↔ HasLimitTailDecomposition F := by
  rw [essentiallyConstantCofilteredDiagram_iff_hasEventuallySplitLimit, hasEventuallySplitLimit_iff]

end SequentialInverseSystem

end CategoryTheory
