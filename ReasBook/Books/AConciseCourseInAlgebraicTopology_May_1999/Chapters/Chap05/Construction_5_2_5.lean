import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Order

open CategoryTheory
open CategoryTheory.Limits
open Set
open scoped Topology

universe u

variable {α : Type u} [TopologicalSpace α]

/-- The inclusion of the `i`-th stage into the union `⋃ n, X n`. -/
private def inclusionSequenceUnionMap (X : ℕ → Set α) (i : ℕ) : X i → (⋃ n, X n) :=
  fun x ↦ ⟨x.1, mem_iUnion.2 ⟨i, x.2⟩⟩

/-- The `i`-th stage in a monotone sequence of inclusions, viewed as an object of `TopCat`. -/
abbrev inclusionSequenceStage (X : ℕ → Set α) (i : ℕ) : TopCat :=
  TopCat.of (X i)

/-- The structure map `X i ⟶ X (i + 1)` in a monotone sequence of inclusions. -/
def inclusionSequenceStageMap (X : ℕ → Set α) (hX : Monotone X) (i : ℕ) :
    inclusionSequenceStage X i ⟶ inclusionSequenceStage X (i + 1) :=
  TopCat.ofHom <| ContinuousMap.inclusion (hX (Nat.le_succ i))

@[simp] theorem inclusionSequenceStageMap_apply (X : ℕ → Set α) (hX : Monotone X) (i : ℕ)
    (x : X i) :
    inclusionSequenceStageMap X hX i x = ⟨x.1, hX (Nat.le_succ i) x.2⟩ :=
  rfl

/-- The sequential diagram in `TopCat` determined by a monotone sequence of inclusions. -/
abbrev inclusionSequenceDiagram (X : ℕ → Set α) (hX : Monotone X) : ℕ ⥤ TopCat :=
  Functor.ofSequence (inclusionSequenceStageMap X hX)

@[simp] theorem inclusionSequenceDiagram_map_succ (X : ℕ → Set α) (hX : Monotone X) (i : ℕ) :
    (inclusionSequenceDiagram X hX).map (homOfLE (Nat.le_add_right i 1)) =
      inclusionSequenceStageMap X hX i := by
  exact Functor.ofSequence_map_homOfLE_succ (inclusionSequenceStageMap X hX) i

/-- The union `⋃ n, X n` endowed with the final topology for the stage inclusions `X i → ⋃ n, X n`.
-/
@[implicit_reducible]
def inclusionSequenceColimitTopology (X : ℕ → Set α) : TopologicalSpace (⋃ n, X n) :=
  ⨆ i : ℕ, TopologicalSpace.coinduced (inclusionSequenceUnionMap X i) inferInstance

/-- The topological space on the union `⋃ n, X n` used for the colimit of a sequence of inclusions.
-/
@[reducible]
def inclusionSequenceColimit (X : ℕ → Set α) : TopCat where
  carrier := ⋃ n, X n
  str := inclusionSequenceColimitTopology X

/-- `inclusionSequenceColimit X` carries the final topology from Construction 5.2.5. This
instance lets downstream files use the colimit object directly as a topological space. -/
instance inclusionSequenceColimit.instTopologicalSpace (X : ℕ → Set α) :
    TopologicalSpace (inclusionSequenceColimit X) :=
  (inclusionSequenceColimit X).str

/-- Each stage inclusion into `inclusionSequenceColimit X` is continuous. -/
private theorem continuous_inclusionSequenceColimitInclusion (X : ℕ → Set α) (i : ℕ) :
    Continuous[inferInstance, (inclusionSequenceColimit X).str]
      (inclusionSequenceUnionMap X i) := by
  change Continuous[inferInstance, inclusionSequenceColimitTopology X]
    (inclusionSequenceUnionMap X i)
  exact continuous_iSup_rng continuous_coinduced_rng

/-- The `i`-th stage inclusion as a morphism in `TopCat`. -/
def inclusionSequenceColimitHom (X : ℕ → Set α) (i : ℕ) :
    inclusionSequenceStage X i ⟶ inclusionSequenceColimit X :=
  let _ : TopologicalSpace (inclusionSequenceColimit X) := (inclusionSequenceColimit X).str
  TopCat.ofHom ⟨inclusionSequenceUnionMap X i,
    continuous_inclusionSequenceColimitInclusion X i⟩

/-- The `i`-th stage inclusion into `inclusionSequenceColimit X`, viewed as the underlying
function of `inclusionSequenceColimitHom X i`. -/
abbrev inclusionSequenceColimitInclusion (X : ℕ → Set α) (i : ℕ) :
    X i → inclusionSequenceColimit X :=
  (inclusionSequenceColimitHom X i).hom

@[simp] theorem inclusionSequenceColimitHom_apply (X : ℕ → Set α) (i : ℕ) (x : X i) :
    inclusionSequenceColimitHom X i x = inclusionSequenceUnionMap X i x :=
  rfl

@[simp] theorem inclusionSequenceColimitInclusion_apply (X : ℕ → Set α) (i : ℕ) (x : X i) :
    inclusionSequenceColimitInclusion X i x = inclusionSequenceUnionMap X i x :=
  rfl

/-- The stage inclusions into `inclusionSequenceColimit X` are compatible with the sequence maps. -/
theorem inclusionSequenceColimitHom_naturality (X : ℕ → Set α) (hX : Monotone X) (i : ℕ) :
    inclusionSequenceStageMap X hX i ≫ inclusionSequenceColimitHom X (i + 1) =
      inclusionSequenceColimitHom X i := by
  ext x
  rfl

/-- The cocone from the sequential inclusion diagram to `inclusionSequenceColimit X`. -/
def inclusionSequenceColimitCocone (X : ℕ → Set α) (hX : Monotone X) :
    Cocone (inclusionSequenceDiagram X hX) where
  pt := inclusionSequenceColimit X
  ι :=
    NatTrans.ofSequence (inclusionSequenceColimitHom X)
      (fun i ↦ by
        simpa using inclusionSequenceColimitHom_naturality X hX i)

@[simp] theorem inclusionSequenceColimitCocone_ι_app (X : ℕ → Set α) (hX : Monotone X) (i : ℕ) :
    (inclusionSequenceColimitCocone X hX).ι.app i = inclusionSequenceColimitHom X i :=
  rfl

/-- The set-theoretic descent map from `inclusionSequenceColimit X` to a cocone point. -/
private noncomputable def inclusionSequenceColimitDescFun {X : ℕ → Set α} (hX : Monotone X)
    (s : Cocone (inclusionSequenceDiagram X hX)) :
    inclusionSequenceColimit X → s.pt :=
  fun x ↦
    let i := Classical.choose (mem_iUnion.1 x.2)
    s.ι.app i ⟨x.1, Classical.choose_spec (mem_iUnion.1 x.2)⟩

/-- Helper for Construction 5.2.5: the cocone maps agree across one successor inclusion. -/
private theorem inclusionSequenceCoconeApp_succ {X : ℕ → Set α} (hX : Monotone X)
    (s : Cocone (inclusionSequenceDiagram X hX)) (i : ℕ) (x : X i) :
    s.ι.app (i + 1) ⟨x.1, hX (Nat.le_succ i) x.2⟩ = s.ι.app i x := by
  -- Evaluate the cocone relation on the successor arrow and then evaluate at `x`.
  have hs := s.w (homOfLE (Nat.le_add_right i 1))
  rw [inclusionSequenceDiagram_map_succ] at hs
  have hs' := congrArg TopCat.Hom.hom hs
  have hs'' := congrArg (fun f ↦ f x) hs'
  -- The remaining goal is exactly the pointwise form of that cocone equality.
  change
      (TopCat.Hom.hom (s.ι.app (i + 1))) ((TopCat.Hom.hom (inclusionSequenceStageMap X hX i)) x) =
      (TopCat.Hom.hom (s.ι.app i)) x
  exact hs''

/-- Helper for Construction 5.2.5: the cocone maps agree after transporting a point to any later
stage `j`. -/
private theorem inclusionSequenceCoconeApp_eq_of_le {X : ℕ → Set α} (hX : Monotone X)
    (s : Cocone (inclusionSequenceDiagram X hX)) {i j : ℕ} (hij : i ≤ j) (x : X i) :
    s.ι.app j ⟨x.1, hX hij x.2⟩ = s.ι.app i x := by
  -- Propagate the successor compatibility inductively along the chain `i ≤ j`.
  induction j, hij using Nat.le_induction with
  | base =>
      simp
  | succ j hij ih =>
      have hstep : s.ι.app (j + 1) ⟨x.1, hX (Nat.le_succ_of_le hij) x.2⟩ =
          s.ι.app j ⟨x.1, hX hij x.2⟩ := by
        simpa using inclusionSequenceCoconeApp_succ hX s j ⟨x.1, hX hij x.2⟩
      exact hstep.trans ih

/-- The descent map agrees with the given cocone map on each stage. -/
private theorem inclusionSequenceColimitDescFun_eq {X : ℕ → Set α} (hX : Monotone X)
    (s : Cocone (inclusionSequenceDiagram X hX)) (i : ℕ) (x : X i) :
    inclusionSequenceColimitDescFun hX s (inclusionSequenceColimitInclusion X i x) = s.ι.app i x :=
  by
  classical
  let j : ℕ := Classical.choose (mem_iUnion.1 (mem_iUnion.2 ⟨i, x.2⟩ : x.1 ∈ ⋃ n, X n))
  let hj : x.1 ∈ X j := Classical.choose_spec
    (mem_iUnion.1 (mem_iUnion.2 ⟨i, x.2⟩ : x.1 ∈ ⋃ n, X n))
  -- Unfold the chosen representative of the union point.
  have hdesc : inclusionSequenceColimitDescFun hX s (inclusionSequenceColimitInclusion X i x) =
      s.ι.app j ⟨x.1, hj⟩ := by
    dsimp [inclusionSequenceColimitDescFun, inclusionSequenceColimitInclusion,
      inclusionSequenceUnionMap, j, hj]
  -- Move both representatives to the common stage `max i j`.
  have hji : s.ι.app j ⟨x.1, hj⟩ =
      s.ι.app (max i j) ⟨x.1, hX (Nat.le_max_right i j) hj⟩ := by
    symm
    exact inclusionSequenceCoconeApp_eq_of_le hX s (Nat.le_max_right i j) ⟨x.1, hj⟩
  have himax : s.ι.app (max i j) ⟨x.1, hX (Nat.le_max_left i j) x.2⟩ = s.ι.app i x := by
    exact inclusionSequenceCoconeApp_eq_of_le hX s (Nat.le_max_left i j) x
  have hsub : (⟨x.1, hX (Nat.le_max_right i j) hj⟩ : X (max i j)) =
      ⟨x.1, hX (Nat.le_max_left i j) x.2⟩ := by
    exact Subtype.ext rfl
  have hsubeq : s.ι.app (max i j) ⟨x.1, hX (Nat.le_max_right i j) hj⟩ =
      s.ι.app (max i j) ⟨x.1, hX (Nat.le_max_left i j) x.2⟩ := by
    rw [hsub]
  exact hdesc.trans (hji.trans (hsubeq.trans himax))

/-- The descent map from the final-topology union is continuous. -/
private theorem continuous_inclusionSequenceColimitDescFun {X : ℕ → Set α} (hX : Monotone X)
    (s : Cocone (inclusionSequenceDiagram X hX)) :
    Continuous[(inclusionSequenceColimit X).str, s.pt.str]
      (inclusionSequenceColimitDescFun hX s) := by
  change Continuous[inclusionSequenceColimitTopology X, s.pt.str]
    (inclusionSequenceColimitDescFun hX s)
  refine continuous_iSup_dom.2 ?_
  intro i
  rw [continuous_coinduced_dom]
  have hcomp :
      inclusionSequenceColimitDescFun hX s ∘ inclusionSequenceUnionMap X i = s.ι.app i := by
    funext x
    simpa [inclusionSequenceColimitInclusion] using inclusionSequenceColimitDescFun_eq hX s i x
  rw [hcomp]
  exact (s.ι.app i).hom.continuous

/-- The comparison morphism from `inclusionSequenceColimit X` to any cocone point. -/
noncomputable def inclusionSequenceColimitDesc {X : ℕ → Set α} (hX : Monotone X)
    (s : Cocone (inclusionSequenceDiagram X hX)) :
    inclusionSequenceColimit X ⟶ s.pt :=
  let _ : TopologicalSpace (inclusionSequenceColimit X) := (inclusionSequenceColimit X).str
  let _ : TopologicalSpace s.pt := s.pt.str
  TopCat.ofHom
    ⟨inclusionSequenceColimitDescFun hX s, continuous_inclusionSequenceColimitDescFun hX s⟩

/-- The comparison morphism from `inclusionSequenceColimit X` factors the cocone. -/
theorem inclusionSequenceColimitDesc_fac {X : ℕ → Set α} (hX : Monotone X)
    (s : Cocone (inclusionSequenceDiagram X hX)) (i : ℕ) :
    inclusionSequenceColimitHom X i ≫ inclusionSequenceColimitDesc hX s = s.ι.app i := by
  ext x
  change inclusionSequenceColimitDesc hX s (inclusionSequenceColimitInclusion X i x) = s.ι.app i x
  simpa [inclusionSequenceColimitDesc] using inclusionSequenceColimitDescFun_eq hX s i x

/-- The comparison morphism from `inclusionSequenceColimit X` is unique. -/
theorem inclusionSequenceColimitDesc_uniq {X : ℕ → Set α} (hX : Monotone X)
    (s : Cocone (inclusionSequenceDiagram X hX)) (m : inclusionSequenceColimit X ⟶ s.pt)
    (hm : ∀ i, inclusionSequenceColimitHom X i ≫ m = s.ι.app i) :
    m = inclusionSequenceColimitDesc hX s := by
  ext x
  classical
  let i : ℕ := Classical.choose (mem_iUnion.1 x.2)
  let hi : x.1 ∈ X i := Classical.choose_spec (mem_iUnion.1 x.2)
  -- Compare both morphisms on a stage representative of `x`.
  have hm_i := congrArg (fun f ↦ f ⟨x.1, hi⟩) (congrArg TopCat.Hom.hom (hm i))
  have hdesc_i := congrArg (fun f ↦ f ⟨x.1, hi⟩)
      (congrArg TopCat.Hom.hom (inclusionSequenceColimitDesc_fac hX s i))
  have hmx_desc :
      m (inclusionSequenceColimitHom X i ⟨x.1, hi⟩) =
        inclusionSequenceColimitDesc hX s (inclusionSequenceColimitHom X i ⟨x.1, hi⟩) := by
    -- Both factorization equalities land at the same cocone value on the chosen representative.
    change (TopCat.Hom.hom m) ((TopCat.Hom.hom (inclusionSequenceColimitHom X i)) ⟨x.1, hi⟩) =
      (TopCat.Hom.hom (inclusionSequenceColimitDesc hX s))
        ((TopCat.Hom.hom (inclusionSequenceColimitHom X i)) ⟨x.1, hi⟩)
    exact hm_i.trans hdesc_i.symm
  have hx : inclusionSequenceColimitHom X i ⟨x.1, hi⟩ = x := by
    exact Subtype.ext rfl
  -- The stage inclusion of the chosen representative is exactly the original union point.
  simpa [hx] using hmx_desc

/-- Construction 5.2.5 (1). For a monotone sequence of inclusions `X i ⊆ X (i + 1)`, the colimit
is the union `⋃ i, X i` with the final topology induced by the stage inclusions. -/
noncomputable def inclusionSequenceColimitCoconeIsColimit {X : ℕ → Set α} (hX : Monotone X) :
    IsColimit (inclusionSequenceColimitCocone X hX) where
  desc s := inclusionSequenceColimitDesc hX s
  fac s i := inclusionSequenceColimitDesc_fac hX s i
  uniq s m hm := inclusionSequenceColimitDesc_uniq hX s m (fun i ↦ by
    simpa using hm i)

/-- Construction 5.2.5 (2). A subset of `inclusionSequenceColimit X` is closed if and only if its
intersection with each stage `X i`, viewed as a subset of that stage, is closed. -/
theorem isClosed_inclusionSequenceColimit_iff {X : ℕ → Set α} (hX : Monotone X)
    {s : Set (inclusionSequenceColimit X)} :
    IsClosed[(inclusionSequenceColimit X).str] s ↔
      ∀ i, IsClosed (inclusionSequenceColimitInclusion X i ⁻¹' s) := by
  change @IsClosed (↑((inclusionSequenceColimitCocone X hX).pt))
      ((inclusionSequenceColimitCocone X hX).pt.str) s ↔
    ∀ i, IsClosed (((inclusionSequenceColimitCocone X hX).ι.app i) ⁻¹' s)
  simpa using
    TopCat.isClosed_iff_of_isColimit
      (inclusionSequenceColimitCocone X hX)
      (inclusionSequenceColimitCoconeIsColimit hX)
      s
