import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Data.PNat.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Definition_22_2_5

open CategoryTheory
open scoped Topology Topology.Homotopy

universe u w

noncomputable section

-- Semantic recall via `lean_leansearch`: no canonical stable-homotopy-group owner surfaced in the
-- current environment. Chapter 22 already provides the source-faithful `Prespectrum` owner and
-- its adjoint structure maps `T n ⟶ Ω T (n + 1)`, so the colimit is formalized through
-- sequential diagrams of positive-degree homotopy groups, with the all-degrees owner obtained by
-- passing to a cofinal tail.

namespace Prespectrum

/-- The path in `Ω Y` induced by a based map `f : X ⟶ Y` on a loop in `X`. -/
private def loopPointedMapPath {X Y : PointedCompactlyGenerated.{u, w}} (f : X ⟶ Y)
    (γ : Path X.point X.point) : Path Y.point Y.point :=
  let g := CategoryTheory.ConcreteCategory.hom (PointedCompactlyGenerated.Hom.hom f)
  ((γ.map g.continuous).cast
    (show Y.point = g X.point from (PointedCompactlyGenerated.Hom.map_point f).symm)
    (show Y.point = g X.point from (PointedCompactlyGenerated.Hom.map_point f).symm))

/-- Helper for Definition 25.3.1: a continuous map out of a `UCompactlyGeneratedSpace` remains
continuous after replacing the codomain by its compactly generated topology. -/
private theorem continuousCompHausToCompactlyGenerated
    {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {Y : Type w} [TopologicalSpace Y] {f : K → Y} (hf : Continuous f) :
    @Continuous K Y ‹TopologicalSpace K› (TopologicalSpace.compactlyGenerated.{u, w} Y) f := by
  let F : (Σ (j : (S : CompHaus.{u}) × C(S, Y)), j.fst) → Y := fun x ↦ x.1.2 x.2
  let i : (S : CompHaus.{u}) × C(S, Y) := ⟨CompHaus.of K, ⟨f, hf⟩⟩
  -- The chosen compact-source map is one of the generators for the compactly generated topology.
  have hgenerator :
      ∀ j : (S : CompHaus.{u}) × C(S, Y),
        @Continuous j.fst Y inferInstance (TopologicalSpace.compactlyGenerated.{u, w} Y)
          (fun a : j.fst ↦ F ⟨j, a⟩) := by
    rw [TopologicalSpace.compactlyGenerated, ← @continuous_sigma_iff]
    exact continuous_coinduced_rng
  simpa [F, i] using hgenerator i

/-- Helper for Definition 25.3.1: a continuous map out of a `UCompactlyGeneratedSpace` remains
continuous after replacing the codomain by its compactly generated topology. -/
private theorem continuousToCompactlyGeneratedOfContinuousOfUCompactlyGenerated
    {X : Type w} [TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X]
    {Y : Type w} [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) :
    @Continuous X Y ‹TopologicalSpace X› (TopologicalSpace.compactlyGenerated.{u, w} Y) f := by
  -- Test continuity against compact Hausdorff probes into the compactly generated codomain.
  exact continuous_from_uCompactlyGeneratedSpace
    (tY := TopologicalSpace.compactlyGenerated.{u, w} Y) f fun S g ↦ by
      simpa [Function.comp] using
        (continuousCompHausToCompactlyGenerated (Y := Y) (f := f ∘ g)
          (hf := hf.comp g.continuous))

/-- The loop-space map induced by a based map is continuous. -/
private theorem loopPointedMapContinuous {X Y : PointedCompactlyGenerated.{u, w}}
    (f : X ⟶ Y) :
    Continuous fun γ : (Ω X).toCompactlyGenerated ↦
      (show (Ω Y).toCompactlyGenerated from loopPointedMapPath f γ) := by
  let g := CategoryTheory.ConcreteCategory.hom (PointedCompactlyGenerated.Hom.hom f)
  have hpath : Continuous fun γ : Path X.point X.point ↦ loopPointedMapPath f γ := by
    -- On raw path spaces, the induced map is just postcomposition by the underlying continuous map.
    rw [continuous_induced_rng]
    simpa [loopPointedMapPath, g] using
      (ContinuousMap.continuous_postcomp g).comp
        (continuous_induced_dom :
          Continuous fun γ : Path X.point X.point ↦ γ.toContinuousMap)
  have hraw :
      Continuous fun γ : (Ω X).toCompactlyGenerated ↦ loopPointedMapPath f γ := by
    -- Forget the compactly generated loop topology on the domain and reuse the raw continuity.
    refine continuous_from_compactlyGenerated
      (fun γ : Path X.point X.point ↦ loopPointedMapPath f γ) ?_
    intro S gS
    simpa [Function.comp] using hpath.comp gS.continuous
  -- Upgrade the codomain from the raw path topology to the compactly generated loop topology.
  simpa [loopPointedSpace] using
    (continuousToCompactlyGeneratedOfContinuousOfUCompactlyGenerated
      (Y := Path Y.point Y.point) hraw)

/-- The continuous map on loop spaces induced by a based map. -/
private def loopPointedMapContinuousMap {X Y : PointedCompactlyGenerated.{u, w}} (f : X ⟶ Y) :
    C((Ω X).toCompactlyGenerated, (Ω Y).toCompactlyGenerated) :=
  ⟨fun γ ↦ show (Ω Y).toCompactlyGenerated from loopPointedMapPath f γ,
    loopPointedMapContinuous f⟩

/-- Helper for Definition 25.3.1: the induced loop map sends the constant loop at `X.point` to
the constant loop at `Y.point`. -/
private theorem loopPointedMapPath_refl {X Y : PointedCompactlyGenerated.{u, w}} (f : X ⟶ Y) :
    loopPointedMapPath f (Path.refl X.point) = Path.refl Y.point := by
  -- Compare the two loops pointwise after reducing the casted image of the constant loop.
  ext t
  change CategoryTheory.ConcreteCategory.hom (PointedCompactlyGenerated.Hom.hom f) X.point = Y.point
  simpa using (PointedCompactlyGenerated.Hom.map_point f)

/-- The induced loop-space map preserves the distinguished basepoint loop. -/
private theorem loopPointedMap_w {X Y : PointedCompactlyGenerated.{u, w}} (f : X ⟶ Y) :
    CategoryTheory.CategoryStruct.comp (Ω X).hom
        (ConcreteCategory.ofHom (loopPointedMapContinuousMap f)) =
      (Ω Y).hom := by
  -- Both maps from the terminal source pick out the constant loop at the target basepoint.
  ext x
  cases x
  exact loopPointedMapPath_refl f

/-- The based map on loop spaces induced by a based map `f : X ⟶ Y`. -/
private def loopPointedMap {X Y : PointedCompactlyGenerated.{u, w}} (f : X ⟶ Y) :
    Ω X ⟶ Ω Y :=
  Under.homMk
    (ConcreteCategory.ofHom (loopPointedMapContinuousMap f))
    (loopPointedMap_w f)

/-- The `k`-fold iterated loop space of a pointed compactly generated space. -/
def iteratedLoopPointedSpace :
    ℕ → PointedCompactlyGenerated.{u, w} → PointedCompactlyGenerated.{u, w}
  | 0, X => X
  | k + 1, X => iteratedLoopPointedSpace k (Ω X)

/-- Zero iterated loops recover the original pointed space. -/
@[simp] theorem iteratedLoopPointedSpace_zero (X : PointedCompactlyGenerated.{u, w}) :
    iteratedLoopPointedSpace 0 X = X := rfl

/-- One more iterated loop is the ordinary pointed loop-space construction. -/
@[simp] theorem iteratedLoopPointedSpace_succ (k : ℕ) (X : PointedCompactlyGenerated.{u, w}) :
    iteratedLoopPointedSpace (k + 1) X =
      iteratedLoopPointedSpace k (Ω X) := rfl

/-- The map on `k`-fold iterated loop spaces induced by a based map.  This is public because
maps of prespectra use it degreewise to induce maps on stable homotopy groups. -/
def iteratedLoopMap (k : ℕ) {X Y : PointedCompactlyGenerated.{u, w}}
    (f : X ⟶ Y) : iteratedLoopPointedSpace k X ⟶ iteratedLoopPointedSpace k Y :=
  match k with
  | 0 => f
  | m + 1 => iteratedLoopMap m (loopPointedMap f)

/-- The homomorphism on a positive-degree homotopy group induced by a pointed continuous map.
This is exposed for the functorial stable-homotopy-group construction. -/
def homotopyGroupMonoidHom
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (hf : f a = b) (n : ℕ) :
    π_ (n + 1) A a →* π_ (n + 1) B b :=
  f.eStarMulHomOverEq n hf

/-- Helper for Definition 25.3.1: changing only the endpoint witness does not change the induced
map on positive-degree homotopy groups. -/
private theorem homotopyGroupMonoidHom_proofIrrel
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (h₁ h₂ : f a = b) (n : ℕ) :
    homotopyGroupMonoidHom f h₁ n = homotopyGroupMonoidHom f h₂ n := by
  -- The endpoint witness is proposition-valued, so the transported map is proof irrelevant.
  cases h₁
  cases h₂
  rfl

/-- The `k`th group in the positive-degree stable homotopy sequence of a prespectrum. It is the
`(n + 1)`st homotopy group of the `k`-fold iterated loop space of `T k`, modeling the source
term `π_ (n + 1 + k) (T k)`. -/
abbrev stableHomotopyGroupStage (T : Prespectrum.{u, w}) (n k : ℕ) : GrpCat :=
  GrpCat.of
    (π_ (n + 1)
      (iteratedLoopPointedSpace k (T k)).toCompactlyGenerated
      (iteratedLoopPointedSpace k (T k)).point)

/-- Unfolding `stableHomotopyGroupStage T n k` gives the `(n + 1)`st homotopy group of the
`k`-fold iterated loop space of `T k`. -/
@[simp] theorem stableHomotopyGroupStage_def (T : Prespectrum.{u, w}) (n k : ℕ) :
    stableHomotopyGroupStage T n k =
      GrpCat.of
        (π_ (n + 1)
          (iteratedLoopPointedSpace k (T k)).toCompactlyGenerated
          (iteratedLoopPointedSpace k (T k)).point) := rfl

/-- The successor map in the positive-degree stable homotopy sequence, induced by the `k`th
adjoint structure map of the prespectrum. -/
def stableHomotopyGroupStepMap (T : Prespectrum.{u, w}) (n k : ℕ) :
    stableHomotopyGroupStage T n k ⟶ stableHomotopyGroupStage T n (k + 1) :=
  let f := CategoryTheory.ConcreteCategory.hom
    (PointedCompactlyGenerated.Hom.hom (iteratedLoopMap k (adjointStructureMap T k)))
  GrpCat.ofHom <|
    homotopyGroupMonoidHom
      f
      (show f (iteratedLoopPointedSpace k (T k)).point =
          (iteratedLoopPointedSpace (k + 1) (T (k + 1))).point from
        PointedCompactlyGenerated.Hom.map_point (iteratedLoopMap k (adjointStructureMap T k)))
      n

/-- The sequential `GrpCat`-diagram whose filtered colimit defines the positive-degree stable
homotopy groups of a prespectrum. -/
def stableHomotopyGroupDiagram (T : Prespectrum.{u, w}) (n : ℕ) : ℕ ⥤ GrpCat :=
  Functor.ofSequence (stableHomotopyGroupStepMap T n)

/-- The successor morphism in `stableHomotopyGroupDiagram T n` is `stableHomotopyGroupStepMap T n`.
-/
@[simp] theorem stableHomotopyGroupDiagram_map_succ (T : Prespectrum.{u, w}) (n k : ℕ) :
    (stableHomotopyGroupDiagram T n).map (homOfLE (Nat.le_add_right k 1)) =
      stableHomotopyGroupStepMap T n k := by
  exact Functor.ofSequence_map_homOfLE_succ (stableHomotopyGroupStepMap T n) k

/-- The `k`th stage in degree `n` for the cofinal tail starting at `T 1`. It models
`π_ (n + k + 1) (T (k + 1))` by iterated loops, so every stage stays group-valued. -/
abbrev stableHomotopyGroupShiftedStage (T : Prespectrum.{u, w}) (n k : ℕ) : GrpCat :=
  GrpCat.of
    (π_ (n + 1)
      (iteratedLoopPointedSpace k (T (k + 1))).toCompactlyGenerated
      (iteratedLoopPointedSpace k (T (k + 1))).point)

/-- The successor map in the shifted stable homotopy sequence. -/
def stableHomotopyGroupShiftedStepMap (T : Prespectrum.{u, w}) (n k : ℕ) :
    stableHomotopyGroupShiftedStage T n k ⟶ stableHomotopyGroupShiftedStage T n (k + 1) :=
  let f := CategoryTheory.ConcreteCategory.hom
    (PointedCompactlyGenerated.Hom.hom (iteratedLoopMap k (adjointStructureMap T (k + 1))))
  GrpCat.ofHom <|
    homotopyGroupMonoidHom
      f
      (show f (iteratedLoopPointedSpace k (T (k + 1))).point =
          (iteratedLoopPointedSpace (k + 1) (T (k + 2))).point from
        PointedCompactlyGenerated.Hom.map_point (iteratedLoopMap k (adjointStructureMap T (k + 1))))
      n

/-- The sequential `GrpCat`-diagram whose filtered colimit defines the stable homotopy group in
degree `n` after shifting to the cofinal tail `k ↦ T (k + 1)`. -/
def stableHomotopyGroupShiftedDiagram (T : Prespectrum.{u, w}) (n : ℕ) : ℕ ⥤ GrpCat :=
  Functor.ofSequence (stableHomotopyGroupShiftedStepMap T n)

/-- The successor morphism in `stableHomotopyGroupShiftedDiagram T n` is
`stableHomotopyGroupShiftedStepMap T n`. -/
@[simp] theorem stableHomotopyGroupShiftedDiagram_map_succ
    (T : Prespectrum.{u, w}) (n k : ℕ) :
    (stableHomotopyGroupShiftedDiagram T n).map (homOfLE (Nat.le_add_right k 1)) =
      stableHomotopyGroupShiftedStepMap T n k := by
  exact Functor.ofSequence_map_homOfLE_succ (stableHomotopyGroupShiftedStepMap T n) k

/-- The first stage in the cofinal tail at which the homotopy degree is positive. -/
abbrev stableHomotopyGroupTailStart (n : ℤ) : ℕ :=
  Int.toNat (1 - n)

/-- The positive homotopy-degree offset used in the cofinal-tail model. -/
abbrev stableHomotopyGroupTailOffset (n : ℤ) : ℕ :=
  Int.toNat (n - 1)

/-- Helper for Definition 25.3.1: in successor degree, the cofinal tail starts immediately. -/
private theorem stableHomotopyGroupTailStart_succ (n : ℕ) :
    stableHomotopyGroupTailStart ((n : ℤ) + 1) = 0 := by
  unfold stableHomotopyGroupTailStart
  have hnonpos : 1 - ((n : ℤ) + 1) ≤ 0 := by
    omega
  rw [Int.toNat_of_nonpos hnonpos]

/-- Helper for Definition 25.3.1: in successor degree, the positive offset is `n`. -/
private theorem stableHomotopyGroupTailOffset_succ (n : ℕ) :
    stableHomotopyGroupTailOffset ((n : ℤ) + 1) = n := by
  unfold stableHomotopyGroupTailOffset
  have h : ((n : ℤ) + 1) - 1 = n := by
    omega
  rw [h]
  have hnonneg : 0 ≤ (n : ℤ) := by
    exact_mod_cast Nat.zero_le n
  simpa using Int.toNat_of_nonneg hnonneg

/-- Helper for Definition 25.3.1: in degree `0`, the cofinal tail starts at stage `1`. -/
private theorem stableHomotopyGroupTailStart_zero :
    stableHomotopyGroupTailStart 0 = 1 := by
  unfold stableHomotopyGroupTailStart
  norm_num

/-- Helper for Definition 25.3.1: in degree `0`, the positive offset is `0`. -/
private theorem stableHomotopyGroupTailOffset_zero :
    stableHomotopyGroupTailOffset 0 = 0 := by
  unfold stableHomotopyGroupTailOffset
  norm_num

/-- The `k`th group in the cofinal-tail diagram defining `π_n(T)`. It models the source term
`π_ (n + j) (T j)` at `j = stableHomotopyGroupTailStart n + k` using a positive-degree
homotopy group of an iterated loop space. -/
abbrev stableHomotopyGroupTailStage (T : Prespectrum.{u, w}) (n : ℤ) (k : ℕ) : GrpCat :=
  GrpCat.of
    (π_ (stableHomotopyGroupTailOffset n + 1)
      (iteratedLoopPointedSpace k (T (stableHomotopyGroupTailStart n + k))).toCompactlyGenerated
      (iteratedLoopPointedSpace k (T (stableHomotopyGroupTailStart n + k))).point)

/-- The successor map in the cofinal-tail diagram defining `π_n(T)`. -/
def stableHomotopyGroupTailStepMap (T : Prespectrum.{u, w}) (n : ℤ) (k : ℕ) :
    stableHomotopyGroupTailStage T n k ⟶ stableHomotopyGroupTailStage T n (k + 1) :=
  let f := CategoryTheory.ConcreteCategory.hom
    (PointedCompactlyGenerated.Hom.hom
      (iteratedLoopMap k
        (adjointStructureMap T (stableHomotopyGroupTailStart n + k))))
  GrpCat.ofHom <|
    homotopyGroupMonoidHom
      f
      (show f (iteratedLoopPointedSpace k (T (stableHomotopyGroupTailStart n + k))).point =
          (iteratedLoopPointedSpace (k + 1) (T (stableHomotopyGroupTailStart n + (k + 1)))).point
        from
          PointedCompactlyGenerated.Hom.map_point
            (iteratedLoopMap k
              (adjointStructureMap T (stableHomotopyGroupTailStart n + k))))
      (stableHomotopyGroupTailOffset n)

/-- The sequential `GrpCat`-diagram whose filtered colimit computes the stable homotopy group of
degree `n : ℤ` after passing to the cofinal tail where the source degree `n + k` is positive. -/
def stableHomotopyGroupTailDiagram (T : Prespectrum.{u, w}) (n : ℤ) : ℕ ⥤ GrpCat :=
  Functor.ofSequence (stableHomotopyGroupTailStepMap T n)

/-- The successor morphism in `stableHomotopyGroupTailDiagram T n` is
`stableHomotopyGroupTailStepMap T n`. -/
@[simp] private theorem stableHomotopyGroupTailDiagram_map_succ
    (T : Prespectrum.{u, w}) (n : ℤ) (k : ℕ) :
    (stableHomotopyGroupTailDiagram T n).map (homOfLE (Nat.le_add_right k 1)) =
      stableHomotopyGroupTailStepMap T n k := by
  -- `Functor.ofSequence` computes successor morphisms definitionally.
  exact Functor.ofSequence_map_homOfLE_succ (stableHomotopyGroupTailStepMap T n) k

/-- Helper for Definition 25.3.1: in successor degree, the cofinal-tail stage index is `k`. -/
private theorem stableHomotopyGroupTailIndex_succ (n k : ℕ) :
    stableHomotopyGroupTailStart ((n : ℤ) + 1) + k = k := by
  rw [stableHomotopyGroupTailStart_succ, Nat.zero_add]

/-- Helper for Definition 25.3.1: in successor degree, the positive homotopy degree is `n + 1`. -/
private theorem stableHomotopyGroupTailDegree_succ (n : ℕ) :
    stableHomotopyGroupTailOffset ((n : ℤ) + 1) + 1 = n + 1 := by
  rw [stableHomotopyGroupTailOffset_succ]

/-- Helper for Definition 25.3.1: in degree `0`, the cofinal-tail stage index is `k + 1`. -/
private theorem stableHomotopyGroupTailIndex_zero (k : ℕ) :
    stableHomotopyGroupTailStart 0 + k = k + 1 := by
  rw [stableHomotopyGroupTailStart_zero]
  simp [Nat.add_comm]

/-- Helper for Definition 25.3.1: in degree `0`, the positive homotopy degree is `1`. -/
private theorem stableHomotopyGroupTailDegree_zero :
    stableHomotopyGroupTailOffset 0 + 1 = 1 := by
  rw [stableHomotopyGroupTailOffset_zero]

/-- Definition 25.3.1: for a prespectrum `T`, `stableHomotopyGroup T n` is the stable homotopy
group in degree `n : ℤ`, formalized as the filtered colimit of a cofinal tail of the source
terms `π_ (n + k) (T k)` where `n + k` is positive. The existing positive-degree and shifted
diagrams are retained as helper presentations of this all-degrees owner. -/
abbrev stableHomotopyGroup (T : Prespectrum.{u, w}) (n : ℤ) : GrpCat :=
  GrpCat.FilteredColimits.colimit (stableHomotopyGroupTailDiagram T n)

/-- `stableHomotopyGroup T n` is the filtered colimit of the cofinal stable homotopy diagram in
integer degree `n`. -/
@[simp] theorem stableHomotopyGroup_def (T : Prespectrum.{u, w}) (n : ℤ) :
    stableHomotopyGroup T n =
      GrpCat.FilteredColimits.colimit (stableHomotopyGroupTailDiagram T n) := rfl

/-- The `k`th shifted stage in degree `n` is modeled by `π_ (n + 1)` of the `k`-fold iterated
loop space of `T (k + 1)`, corresponding to the cofinal tail of the source formula
`π_ (n + k) (T k)`. -/
@[simp] theorem stableHomotopyGroupShiftedStage_def (T : Prespectrum.{u, w}) (n k : ℕ) :
    stableHomotopyGroupShiftedStage T n k =
      GrpCat.of
        (π_ (n + 1)
          (iteratedLoopPointedSpace k (T (k + 1))).toCompactlyGenerated
          (iteratedLoopPointedSpace k (T (k + 1))).point) := rfl

/-- `stableHomotopyGroupSucc T n` is the helper presentation of the stable homotopy group in
degree `(n : ℤ) + 1`, written with a natural-number index to stay in the original
positive-degree range. -/
abbrev stableHomotopyGroupSucc (T : Prespectrum.{u, w}) (n : ℕ) : GrpCat :=
  GrpCat.FilteredColimits.colimit (stableHomotopyGroupDiagram T n)

/-- `stableHomotopyGroupSucc T n` agrees with the original positive-degree filtered-colimit
presentation. -/
@[simp] theorem stableHomotopyGroupSucc_def (T : Prespectrum.{u, w}) (n : ℕ) :
    stableHomotopyGroupSucc T n =
      GrpCat.FilteredColimits.colimit (stableHomotopyGroupDiagram T n)
      := rfl

/-- Helper for Definition 25.3.1: equal homotopy degree and pointed-space inputs give the same
bundled homotopy-group object in `GrpCat`. -/
private theorem homotopyGroupGrpCat_eq_of_eq
    {X Y : PointedCompactlyGenerated.{u, w}} {m n : ℕ}
    (hm : m = n) (hXY : X = Y) :
    GrpCat.of (π_ (m + 1) X.toCompactlyGenerated X.point) =
      GrpCat.of (π_ (n + 1) Y.toCompactlyGenerated Y.point) := by
  -- Reduce the bundled homotopy-group object to the reflexive case before any hidden transport
  -- on the ambient `Group` structure appears.
  cases hm
  cases hXY
  rfl

/-- Helper for Definition 25.3.1: in successor degree, the tail stage at `k` is the original
positive-degree stable homotopy stage at `k`. -/
private theorem stableHomotopyGroupTailStage_succ_eq
    (T : Prespectrum.{u, w}) (n k : ℕ) :
    stableHomotopyGroupTailStage T ((n : ℤ) + 1) k = stableHomotopyGroupStage T n k := by
  -- Route correction: bridge directly at the bundled `GrpCat.of (π_ ...)` level after the tail
  -- degree and tail index have both been normalized.
  have hOffset : stableHomotopyGroupTailOffset ((n : ℤ) + 1) = n :=
    stableHomotopyGroupTailOffset_succ n
  have hIndex : stableHomotopyGroupTailStart ((n : ℤ) + 1) + k = k :=
    stableHomotopyGroupTailIndex_succ n k
  have hSpace :
      iteratedLoopPointedSpace k
          (T (stableHomotopyGroupTailStart ((n : ℤ) + 1) + k)) =
        iteratedLoopPointedSpace k (T k) := by
    -- Convert the stage-index arithmetic into equality of the pointed loop spaces themselves.
    simpa using congrArg (fun l => iteratedLoopPointedSpace k (T l)) hIndex
  simpa [stableHomotopyGroupTailStage, stableHomotopyGroupStage] using
    homotopyGroupGrpCat_eq_of_eq
      (X :=
        iteratedLoopPointedSpace k
          (T (stableHomotopyGroupTailStart ((n : ℤ) + 1) + k)))
      (Y := iteratedLoopPointedSpace k (T k))
      hOffset hSpace

/-- Helper for Definition 25.3.1: in degree `0`, the tail stage at `k` is the shifted
positive-degree stable homotopy stage at `k`. -/
private theorem stableHomotopyGroupTailStage_zero_eq_shifted
    (T : Prespectrum.{u, w}) (k : ℕ) :
    stableHomotopyGroupTailStage T 0 k = stableHomotopyGroupShiftedStage T 0 k := by
  -- Route correction: normalize the degree-`0` tail arithmetic first, then compare the bundled
  -- homotopy-group objects directly.
  have hOffset : stableHomotopyGroupTailOffset 0 = 0 :=
    stableHomotopyGroupTailOffset_zero
  have hIndex : stableHomotopyGroupTailStart 0 + k = k + 1 :=
    stableHomotopyGroupTailIndex_zero k
  have hSpace :
      iteratedLoopPointedSpace k (T (stableHomotopyGroupTailStart 0 + k)) =
        iteratedLoopPointedSpace k (T (k + 1)) := by
    -- Turn the tail-index equality into equality of the shifted pointed stages.
    simpa using congrArg (fun l => iteratedLoopPointedSpace k (T l)) hIndex
  simpa [stableHomotopyGroupTailStage, stableHomotopyGroupShiftedStage] using
    homotopyGroupGrpCat_eq_of_eq
      (X := iteratedLoopPointedSpace k (T (stableHomotopyGroupTailStart 0 + k)))
      (Y := iteratedLoopPointedSpace k (T (k + 1)))
      hOffset hSpace

/-- Helper for Definition 25.3.1: once the raw tail source and target indices are identified with
`k` and `k + 1`, the tail successor map is definitionally the original successor map. -/
private theorem stableHomotopyGroupTailStepMap_succ_heq
    (T : Prespectrum.{u, w}) (n k j j' m : ℕ)
    (hStep : j' = j + 1) (hSource : j = k) (hm : m = n) :
    (let f := CategoryTheory.ConcreteCategory.hom
        (PointedCompactlyGenerated.Hom.hom (iteratedLoopMap k (adjointStructureMap T j)));
      GrpCat.ofHom <|
        homotopyGroupMonoidHom
          f
          (show f (iteratedLoopPointedSpace k (T j)).point =
              (iteratedLoopPointedSpace k (Ω (T (j + 1)))).point from
            PointedCompactlyGenerated.Hom.map_point
              (iteratedLoopMap k (adjointStructureMap T j)))
          m) ≍
      stableHomotopyGroupStepMap T n k := by
  -- Once the source and target indices are identified with `k` and `k + 1`, the raw tail map
  -- is definitionally the original successor map.
  cases hStep
  cases hSource
  cases hm
  rfl

/-- Helper for Definition 25.3.1: the successor map in the cofinal tail matches the original
positive-degree successor map after transporting along the stage identifications. -/
private theorem stableHomotopyGroupTailStepMap_succ_naturality
    (T : Prespectrum.{u, w}) (n k : ℕ) :
    stableHomotopyGroupTailStepMap T ((n : ℤ) + 1) k ≫
        eqToHom (stableHomotopyGroupTailStage_succ_eq T n (k + 1)) =
      eqToHom (stableHomotopyGroupTailStage_succ_eq T n k) ≫
        stableHomotopyGroupStepMap T n k := by
  -- Route correction: discharge the `eqToHom` transports through heterogeneous equality, then
  -- compare the normalized successor maps directly.
  rw [comp_eqToHom_iff, Category.assoc]
  -- Normalize the symbolic tail start and offset before comparing the raw maps.
  exact
    (conj_eqToHom_iff_heq
      (stableHomotopyGroupTailStepMap T ((n : ℤ) + 1) k)
      (stableHomotopyGroupStepMap T n k)
      (stableHomotopyGroupTailStage_succ_eq T n k)
      (stableHomotopyGroupTailStage_succ_eq T n (k + 1))).2 <|
      by
        simpa [stableHomotopyGroupTailStepMap, iteratedLoopPointedSpace_succ] using
          stableHomotopyGroupTailStepMap_succ_heq
            (T := T) (n := n) (k := k)
            (j := stableHomotopyGroupTailStart ((n : ℤ) + 1) + k)
            (j' := stableHomotopyGroupTailStart ((n : ℤ) + 1) + (k + 1))
            (m := stableHomotopyGroupTailOffset ((n : ℤ) + 1))
            (by omega)
            (stableHomotopyGroupTailIndex_succ n k)
            (stableHomotopyGroupTailOffset_succ n)

/-- Helper for Definition 25.3.1: once the raw degree-`0` tail source and target indices are
identified with `k + 1` and `k + 2`, the tail successor map is definitionally the shifted
successor map. -/
private theorem stableHomotopyGroupTailStepMap_zero_heq
    (T : Prespectrum.{u, w}) (k j j' m : ℕ)
    (hStep : j' = j + 1) (hSource : j = k + 1) (hm : m = 0) :
    (let f := CategoryTheory.ConcreteCategory.hom
        (PointedCompactlyGenerated.Hom.hom (iteratedLoopMap k (adjointStructureMap T j)));
      GrpCat.ofHom <|
        homotopyGroupMonoidHom
          f
          (show f (iteratedLoopPointedSpace k (T j)).point =
              (iteratedLoopPointedSpace k (Ω (T (j + 1)))).point from
            PointedCompactlyGenerated.Hom.map_point
              (iteratedLoopMap k (adjointStructureMap T j)))
          m) ≍
      stableHomotopyGroupShiftedStepMap T 0 k := by
  -- Once the source and target indices are identified with `k + 1` and `k + 2`, the raw tail
  -- map is definitionally the shifted successor map.
  cases hStep
  cases hSource
  cases hm
  rfl

/-- Helper for Definition 25.3.1: in degree `0`, the tail successor map matches the shifted
positive-degree successor map after transporting along the stage identifications. -/
private theorem stableHomotopyGroupTailStepMap_zero_naturality
    (T : Prespectrum.{u, w}) (k : ℕ) :
    stableHomotopyGroupTailStepMap T 0 k ≫
        eqToHom (stableHomotopyGroupTailStage_zero_eq_shifted T (k + 1)) =
      eqToHom (stableHomotopyGroupTailStage_zero_eq_shifted T k) ≫
        stableHomotopyGroupShiftedStepMap T 0 k := by
  -- Route correction: replace the transported equality by a heterogeneous one before
  -- normalizing the degree-`0` tail arithmetic.
  rw [comp_eqToHom_iff, Category.assoc]
  -- Normalize the symbolic degree-`0` tail start and offset before comparing the raw maps.
  exact
    (conj_eqToHom_iff_heq
      (stableHomotopyGroupTailStepMap T 0 k)
      (stableHomotopyGroupShiftedStepMap T 0 k)
      (stableHomotopyGroupTailStage_zero_eq_shifted T k)
      (stableHomotopyGroupTailStage_zero_eq_shifted T (k + 1))).2 <|
      by
        unfold stableHomotopyGroupTailStepMap
        simpa only [iteratedLoopPointedSpace_succ] using
          stableHomotopyGroupTailStepMap_zero_heq
            (T := T) (k := k)
            (j := stableHomotopyGroupTailStart 0 + k)
            (j' := stableHomotopyGroupTailStart 0 + (k + 1))
            (m := stableHomotopyGroupTailOffset 0)
            (by omega)
            (stableHomotopyGroupTailIndex_zero k)
            stableHomotopyGroupTailOffset_zero

/-- Helper for Definition 25.3.1: the successor-map naturality condition for the diagram
comparison in successor degree. -/
private theorem stableHomotopyGroupTailDiagram_succ_naturality
    (T : Prespectrum.{u, w}) (n k : ℕ) :
    (stableHomotopyGroupTailDiagram T ((n : ℤ) + 1)).map (homOfLE (Nat.le_add_right k 1)) ≫
        eqToHom (stableHomotopyGroupTailStage_succ_eq T n (k + 1)) =
      eqToHom (stableHomotopyGroupTailStage_succ_eq T n k) ≫
        (stableHomotopyGroupDiagram T n).map (homOfLE (Nat.le_add_right k 1)) := by
  -- Replace the diagram successor morphisms by their defining step maps.
  simpa only [stableHomotopyGroupTailDiagram_map_succ, stableHomotopyGroupDiagram_map_succ] using
    stableHomotopyGroupTailStepMap_succ_naturality T n k

/-- Helper for Definition 25.3.1: the successor-map naturality condition for the diagram
comparison in degree `0`. -/
private theorem stableHomotopyGroupTailDiagram_zero_naturality
    (T : Prespectrum.{u, w}) (k : ℕ) :
    (stableHomotopyGroupTailDiagram T 0).map (homOfLE (Nat.le_add_right k 1)) ≫
        eqToHom (stableHomotopyGroupTailStage_zero_eq_shifted T (k + 1)) =
      eqToHom (stableHomotopyGroupTailStage_zero_eq_shifted T k) ≫
        (stableHomotopyGroupShiftedDiagram T 0).map (homOfLE (Nat.le_add_right k 1)) := by
  -- Replace the diagram successor morphisms by their defining step maps.
  simpa only [stableHomotopyGroupTailDiagram_map_succ, stableHomotopyGroupShiftedDiagram_map_succ] using
    stableHomotopyGroupTailStepMap_zero_naturality T k

/-- Helper for Definition 25.3.1: in successor degree, the tail diagram is the original
positive-degree stable homotopy diagram. -/
private theorem stableHomotopyGroupTailDiagram_succ_eq
    (T : Prespectrum.{u, w}) (n : ℕ) :
    stableHomotopyGroupTailDiagram T ((n : ℤ) + 1) = stableHomotopyGroupDiagram T n := by
  let η :
      stableHomotopyGroupTailDiagram T ((n : ℤ) + 1) ⟶ stableHomotopyGroupDiagram T n :=
    NatTrans.ofSequence
      (fun k ↦ eqToHom (stableHomotopyGroupTailStage_succ_eq T n k))
      (stableHomotopyGroupTailDiagram_succ_naturality T n)
  haveI : ∀ k : ℕ, IsIso (η.app k) := fun k ↦ by
    dsimp [η]
    infer_instance
  haveI : IsIso η := NatIso.isIso_of_isIso_app η
  -- The natural isomorphism with componentwise `eqToHom` identifies the two sequential diagrams.
  exact Functor.ext_of_iso (asIso η)
    (stableHomotopyGroupTailStage_succ_eq T n)
    (fun k ↦ by
      dsimp [η])

/-- The positive-degree helper computes the stable homotopy group in successor integer degree. -/
theorem stableHomotopyGroupSucc_eq (T : Prespectrum.{u, w}) (n : ℕ) :
    stableHomotopyGroupSucc T n = stableHomotopyGroup T ((n : ℤ) + 1) := by
  -- Route correction: identify the tail diagram with the original positive diagram before taking colimits.
  have hdiag := stableHomotopyGroupTailDiagram_succ_eq T n
  -- Apply the filtered-colimit functor to the identified sequential diagrams.
  simpa [stableHomotopyGroupSucc, stableHomotopyGroup] using
    congrArg GrpCat.FilteredColimits.colimit hdiag.symm

/-- Helper for Definition 25.3.1: in degree `0`, the tail diagram is the shifted stable
homotopy diagram. -/
private theorem stableHomotopyGroupTailDiagram_zero_eq_shifted
    (T : Prespectrum.{u, w}) :
    stableHomotopyGroupTailDiagram T 0 = stableHomotopyGroupShiftedDiagram T 0 := by
  let η : stableHomotopyGroupTailDiagram T 0 ⟶ stableHomotopyGroupShiftedDiagram T 0 :=
    NatTrans.ofSequence
      (fun k ↦ eqToHom (stableHomotopyGroupTailStage_zero_eq_shifted T k))
      (stableHomotopyGroupTailDiagram_zero_naturality T)
  haveI : ∀ k : ℕ, IsIso (η.app k) := fun k ↦ by
    dsimp [η]
    infer_instance
  haveI : IsIso η := NatIso.isIso_of_isIso_app η
  -- The degree-`0` tail is the shifted diagram via the componentwise stage identifications.
  exact Functor.ext_of_iso (asIso η)
    (stableHomotopyGroupTailStage_zero_eq_shifted T)
    (fun k ↦ by
      dsimp [η])

/-- The shifted helper recovers the degree-`0` stable homotopy group after discarding the
initial stage of the source tail. -/
theorem stableHomotopyGroup_zero_eq (T : Prespectrum.{u, w}) :
    stableHomotopyGroup T 0 =
      GrpCat.FilteredColimits.colimit (stableHomotopyGroupShiftedDiagram T 0) := by
  have hdiag := stableHomotopyGroupTailDiagram_zero_eq_shifted T
  -- Rewrite the colimit along the diagram equality.
  simpa [stableHomotopyGroup] using
    congrArg GrpCat.FilteredColimits.colimit hdiag

/-- The initial object of the degree-`0` tail diagram is the initial shifted stage. -/
@[simp] theorem stableHomotopyGroupTailDiagram_obj_zero_eq_shiftedStage
    (T : Prespectrum.{u, w}) :
    (stableHomotopyGroupTailDiagram T 0).obj 0 = stableHomotopyGroupShiftedStage T 0 0 := by
  change
    GrpCat.of (π_ 1 (T 1).toCompactlyGenerated (T 1).point) =
      GrpCat.of (π_ 1 (T 1).toCompactlyGenerated (T 1).point)
  rfl

/-- The original positive-degree stage formula is recovered from the successor-degree helper. -/
theorem stableHomotopyGroupStage_pNat (T : Prespectrum.{u, w}) (n : ℕ+) (k : ℕ) :
    stableHomotopyGroupStage T ((n : ℕ) - 1) k =
      GrpCat.of
        (π_ (n : ℕ)
          (iteratedLoopPointedSpace k (T k)).toCompactlyGenerated
          (iteratedLoopPointedSpace k (T k)).point) := by
  rw [← PNat.succPNat_natPred n]
  simp [stableHomotopyGroupStage]

end Prespectrum
