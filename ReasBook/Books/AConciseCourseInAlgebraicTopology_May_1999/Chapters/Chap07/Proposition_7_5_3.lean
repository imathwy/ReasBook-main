import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_5_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Reformulation_7_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Lemma_7_2_5
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open TopCat
open unitInterval
open scoped ContinuousMap

universe u

variable {D E B : Type u}
variable [TopologicalSpace D] [TopologicalSpace E] [TopologicalSpace B]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} D]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} E]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} B]

-- Semantic recall via `lean_leansearch`: `Over (TopCat.of B)` is the canonical owner for maps
-- over a fixed base, and `Definition_7_5_1` exposes the source-facing bridge `SpaceOver B` used
-- in Chapter 7; `D ≃ₕ E` is the canonical owner for ordinary homotopy equivalences.

/-- Helper for Proposition 7.5.3: the commuting triangle carried by `f` rewrites to the
continuous-map equation `q.comp e.toFun = p`. -/
private theorem homotopyEquivToFun_comp_eq
    {p : C(D, B)} {q : C(E, B)}
    (f : SpaceOver.mk p ⟶ SpaceOver.mk q)
    (e : D ≃ₕ E) (he : e.toFun = f.left.hom) :
    q.comp e.toFun = p := by
  -- Rewrite the over-category square into the corresponding equality of continuous maps.
  have hw : q.comp f.left.hom = p := SpaceOver.w f
  simpa [he] using hw

/-- Helper for Proposition 7.5.3: a fibration corrects an ordinary map `g₀ : E ⟶ D` whose base
map is homotopic to `q` into an actual morphism over `B`, while recording the correcting
homotopy. -/
private theorem existsSpaceOverHom_homotopy_of_isFibration
    {p : C(D, B)} {q : C(E, B)}
    (hp : IsFibration.{u, u, u} p) {g₀ : C(E, D)}
    (H : (p.comp g₀).Homotopy q) :
    ∃ g : SpaceOver.mk q ⟶ SpaceOver.mk p,
      ∃ G : g₀.Homotopy g.left.hom,
        p.comp G.toContinuousMap = H.toContinuousMap := by
  -- Local instance justification (typeclass bridge): this helper keeps the fibration hypothesis
  -- explicit, but `IsFibration.exists_homotopyLift` is only exposed through instance search.
  letI : IsFibration.{u, u, u} p := hp
  -- Lift the base homotopy starting at the chosen ordinary inverse candidate `g₀`.
  obtain ⟨g₁, G, hG⟩ := IsFibration.exists_homotopyLift (p := p) (A := E) (H := H) (g₀ := g₀) rfl
  refine ⟨SpaceOver.homMk g₁ ?_, G, hG⟩
  -- Read the time-one endpoint of the lifted homotopy as the corrected over-map equation.
  ext x
  have h := ContinuousMap.congr_fun hG (1, x)
  simpa using h

/-- Helper for Proposition 7.5.3: two lifts of the same base homotopy through a fibration and
with the same initial map have endpoints that are homotopic over the endpoint base map. -/
private theorem pathSpaceLiftData_of_projectedHomotopy
    {X : Type u} [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    {r₀ r₁ : C(X, B)} {q : C(E, B)} {g₀ g₁ : C(X, E)}
    (H : r₀.Homotopy r₁)
    (F : g₀.Homotopy g₁)
    (hF : q.comp F.toContinuousMap = H.toContinuousMap) :
    (pathSpaceEvalAtZero E).comp F.toPathSpaceMap = g₀ ∧
      (pathSpacePostcompose q).comp F.toPathSpaceMap = H.toPathSpaceMap := by
  constructor
  · -- The path-space lift starts at the original map `g₀`.
    exact F.pathSpaceEvalAtZero_comp_toPathSpaceMap
  · -- Pointwise, the lifted path family projects to the original base homotopy.
    ext x t
    simpa using ContinuousMap.congr_fun hF (t, x)

/-- Helper for Proposition 7.5.3: a homotopy between two path-space lifts whose every time-slice
still projects to the same base path family yields a homotopy over the endpoint base map. -/
private theorem homotopicOver_of_pathSpaceLiftHomotopy
    {X : Type u} [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    {r₀ r₁ : C(X, B)} {q : C(E, B)}
    {u₁ u₂ : SpaceOver.mk r₁ ⟶ SpaceOver.mk q}
    {D₁ D₂ : C(X, C(I, E))}
    (H : r₀.Homotopy r₁)
    (K : D₁.Homotopy D₂)
    (hD₁ : (pathSpaceEvalAt 1 E).comp D₁ = u₁.left.hom)
    (hD₂ : (pathSpaceEvalAt 1 E).comp D₂ = u₂.left.hom)
    (hproj : ∀ t : I, (pathSpacePostcompose q).comp (K.curry t) = H.toPathSpaceMap) :
    HomotopicOver u₁ u₂ := by
  refine ⟨{
    toHomotopy := (((ContinuousMap.Homotopy.refl (pathSpaceEvalAt 1 E)).comp K).cast hD₁ hD₂)
    prop' := ?_
  }⟩
  intro t
  -- Evaluating the path-space homotopy at time `1` keeps every stage over the fixed endpoint map
  -- `r₁`.
  ext x
  have hprojOne :
      ((pathSpaceEvalAt 1 B).comp (pathSpacePostcompose q)).comp (K.curry t) = r₁ := by
    calc
      ((pathSpaceEvalAt 1 B).comp (pathSpacePostcompose q)).comp (K.curry t)
          = (pathSpaceEvalAt 1 B).comp ((pathSpacePostcompose q).comp (K.curry t)) := rfl
      _ = (pathSpaceEvalAt 1 B).comp H.toPathSpaceMap := by rw [hproj t]
      _ = H.curry 1 := H.pathSpaceEvalAt_comp_toPathSpaceMap 1
      _ = r₁ := H.curry_one
  calc
    q ((((ContinuousMap.Homotopy.refl (pathSpaceEvalAt 1 E)).comp K).cast hD₁ hD₂).curry t x)
        = (((pathSpaceEvalAt 1 B).comp (pathSpacePostcompose q)).comp (K.curry t)) x := by
          rfl
    _ = r₁ x := by
      simpa using ContinuousMap.congr_fun hprojOne x

private theorem homotopicOver_of_projectedHomotopyRelConst
    {X : Type u} [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    {r : C(X, B)} {q : C(E, B)}
    (hq : IsFibration.{u, u, u} q)
    {u₀ u₁ : SpaceOver.mk r ⟶ SpaceOver.mk q}
    (F : u₀.left.hom.Homotopy u₁.left.hom)
    (hFrel :
      (q.comp F.toContinuousMap).HomotopicRel
        ((ContinuousMap.Homotopy.refl r).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set X))) :
    HomotopicOver u₀ u₁ := by
  -- Route correction: instead of comparing two path-space lifts for literal equality, rectify the
  -- projected ordinary homotopy to the constant base homotopy and lift that 2-parameter square.
  letI : IsFibration.{u, u, u} q := hq
  letI : CompactlyGeneratedWeakHausdorffSpace.{u, u} (I × X) :=
    instCompactlyGeneratedWeakHausdorffSpaceProdUnitInterval X
  rcases hFrel with ⟨hFrel⟩
  rcases @IsFibration.exists_homotopyLift E B _ _ q (by infer_instance)
      (I × X) _ (instCompactlyGeneratedWeakHausdorffSpaceProdUnitInterval X)
      _ _ hFrel.toHomotopy F.toContinuousMap rfl with
    ⟨Graw, Kraw, hKraw⟩
  have hGraw : q.comp Graw = (ContinuousMap.Homotopy.refl r).toContinuousMap := by
    -- Evaluating the lifted comparison at `s = 1` reads off the rectified homotopy over `r`.
    ext tx
    calc
      q (Graw tx) = hFrel.toHomotopy (1, tx) := by
        rw [← Kraw.apply_one tx]
        exact ContinuousMap.congr_fun hKraw (1, tx)
      _ = r tx.2 := hFrel.toHomotopy.apply_one tx
  have hBaseZero : q.comp (Graw.curry 0) = r := by
    -- The `t = 0` endpoint of the rectified homotopy is a map over `r`.
    ext x
    simpa using ContinuousMap.congr_fun hGraw (0, x)
  have hBaseOne : q.comp (Graw.curry 1) = r := by
    -- The `t = 1` endpoint of the rectified homotopy is also a map over `r`.
    ext x
    simpa using ContinuousMap.congr_fun hGraw (1, x)
  let v₀ : SpaceOver.mk r ⟶ SpaceOver.mk q := SpaceOver.homMk (Graw.curry 0) hBaseZero
  let v₁ : SpaceOver.mk r ⟶ SpaceOver.mk q := SpaceOver.homMk (Graw.curry 1) hBaseOne
  let sourceFace : u₀.left.hom.Homotopy v₀.left.hom :=
    { toFun := fun sx ↦ Kraw (sx.1, (0, sx.2))
      continuous_toFun := by
        fun_prop
      map_zero_left := by
        intro x
        rw [Kraw.apply_zero (0, x)]
        simpa using F.apply_zero x
      map_one_left := by
        intro x
        rw [Kraw.apply_one (0, x)]
        rfl }
  have hSourceFace :
      HomotopicOver u₀ v₀ := by
    refine ⟨{ toHomotopy := sourceFace, prop' := ?_ }⟩
    intro s
    -- The `t = 0` face stays over `r` because the base comparison is fixed on that boundary.
    ext x
    have hLift := ContinuousMap.congr_fun hKraw (s, (0, x))
    calc
      q (sourceFace (s, x)) = hFrel.toHomotopy (s, (0, x)) := by
        simpa [sourceFace] using hLift
      _ = (q.comp F.toContinuousMap) (0, x) := by
        exact hFrel.eq_fst s ⟨by simp, by simp⟩
      _ = q (F (0, x)) := rfl
      _ = q (u₀.left.hom x) := by rw [F.apply_zero]
      _ = r x := by
        simpa using ContinuousMap.congr_fun (SpaceOver.w u₀) x
  let middleFace : v₀.left.hom.Homotopy v₁.left.hom :=
    { toContinuousMap := Graw
      map_zero_left := by
        intro x
        rfl
      map_one_left := by
        intro x
        rfl }
  have hMiddleFace :
      HomotopicOver v₀ v₁ := by
    refine ⟨{ toHomotopy := middleFace, prop' := ?_ }⟩
    intro t
    -- Every time-slice of the rectified lift is a map over the fixed base map `r`.
    ext x
    simpa [middleFace] using ContinuousMap.congr_fun hGraw (t, x)
  let targetFace : u₁.left.hom.Homotopy v₁.left.hom :=
    { toFun := fun sx ↦ Kraw (sx.1, (1, sx.2))
      continuous_toFun := by
        fun_prop
      map_zero_left := by
        intro x
        rw [Kraw.apply_zero (1, x)]
        simpa using F.apply_one x
      map_one_left := by
        intro x
        rw [Kraw.apply_one (1, x)]
        rfl }
  have hTargetFace :
      HomotopicOver u₁ v₁ := by
    refine ⟨{ toHomotopy := targetFace, prop' := ?_ }⟩
    intro s
    -- The `t = 1` face stays over `r` for the same boundary-fixed reason.
    ext x
    have hLift := ContinuousMap.congr_fun hKraw (s, (1, x))
    calc
      q (targetFace (s, x)) = hFrel.toHomotopy (s, (1, x)) := by
        simpa [targetFace] using hLift
      _ = (q.comp F.toContinuousMap) (1, x) := by
        exact hFrel.eq_fst s ⟨by simp, by simp⟩
      _ = q (F (1, x)) := rfl
      _ = q (u₁.left.hom x) := by rw [F.apply_one]
      _ = r x := by
        simpa using ContinuousMap.congr_fun (SpaceOver.w u₁) x
  exact HomotopicOver.trans hSourceFace <|
    HomotopicOver.trans hMiddleFace (HomotopicOver.symm hTargetFace)

/-- Helper for Proposition 7.5.3: the projected loop `H.symm.trans H` contracts relative to the
boundary `({0, 1} : Set I) ×ˢ Set.univ`. -/
private theorem homotopySymmTransHomotopicRelRefl
    {X : Type u} [TopologicalSpace X]
    {r₀ r₁ : C(X, B)}
    (H : r₀.Homotopy r₁) :
    (H.symm.trans H).toContinuousMap.HomotopicRel
      ((ContinuousMap.Homotopy.refl r₁).toContinuousMap)
      (({0, 1} : Set I) ×ˢ (Set.univ : Set X)) := by
  let loopParam : I × I → I := fun st ↦
    ⟨1 - Path.Homotopy.reflTransSymmAux (σ st.1, st.2), by
      have hmem := Path.Homotopy.reflTransSymmAux_mem_I (σ st.1, st.2)
      constructor
      · linarith [hmem.2]
      · linarith [hmem.1]⟩
  refine ⟨{
      toHomotopy :=
        { toFun := fun sx ↦ H (loopParam (sx.1, sx.2.1), sx.2.2)
          continuous_toFun := by
            fun_prop
          map_zero_left := by
            intro tx
            rcases tx with ⟨t, x⟩
            change H (loopParam (0, t), x) = (H.symm.trans H) (t, x)
            rw [ContinuousMap.Homotopy.trans_apply]
            split_ifs with ht
            · have hParam :
                loopParam (0, t) =
                  σ ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩ := by
                apply Subtype.ext
                have ht' : (t : ℝ) ≤ 1 / 2 := by
                  simpa using ht
                change (↑(loopParam (0, t)) : ℝ) = 1 - 2 * (t : ℝ)
                have hAux :
                    Path.Homotopy.reflTransSymmAux (σ 0, t) =
                      (if (t : ℝ) ≤ 1 / 2 then 2 * (t : ℝ) else 2 - 2 * (t : ℝ)) := by
                  simp [Path.Homotopy.reflTransSymmAux]
                rw [show (↑(loopParam (0, t)) : ℝ) = 1 - Path.Homotopy.reflTransSymmAux (σ 0, t) by
                  simp [loopParam]]
                rw [hAux, if_pos ht']
              exact congrArg (fun u : I => H (u, x)) hParam
            · have hParam :
                loopParam (0, t) = ⟨2 * t - 1,
                  unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩ := by
                apply Subtype.ext
                have ht' : ¬ (t : ℝ) ≤ 1 / 2 := by
                  simpa using ht
                change (↑(loopParam (0, t)) : ℝ) = 2 * (t : ℝ) - 1
                have hAux :
                    Path.Homotopy.reflTransSymmAux (σ 0, t) =
                      (if (t : ℝ) ≤ 1 / 2 then 2 * (t : ℝ) else 2 - 2 * (t : ℝ)) := by
                  simp [Path.Homotopy.reflTransSymmAux]
                rw [show (↑(loopParam (0, t)) : ℝ) = 1 - Path.Homotopy.reflTransSymmAux (σ 0, t) by
                  simp [loopParam]]
                rw [hAux, if_neg ht']
                ring
              exact congrArg (fun u : I => H (u, x)) hParam
          map_one_left := by
            intro tx
            rcases tx with ⟨t, x⟩
            simp [loopParam, Path.Homotopy.reflTransSymmAux] }
      prop' := ?_ }⟩
  intro s tx htx
  rcases tx with ⟨t, x⟩
  rcases Set.mem_insert_iff.mp htx.1 with ht | ht
  · subst ht
    norm_num [loopParam, Path.Homotopy.reflTransSymmAux]
  · have ht' : t = 1 := Set.mem_singleton_iff.mp ht
    subst ht'
    norm_num [loopParam, Path.Homotopy.reflTransSymmAux]

/-- Helper for Proposition 7.5.3: a continuous square with fixed vertical boundary packages to a
relative homotopy on `(({0, 1} : Set I) ×ˢ Set.univ)`. -/
private theorem homotopyRelOfBoundaryFixedSquare
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {F₀ F₁ : C(I × X, Y)}
    (S : C((I × X) × I, Y))
    (hZero : ∀ tx : I × X, S (tx, 0) = F₀ tx)
    (hOne : ∀ tx : I × X, S (tx, 1) = F₁ tx)
    (hLeft : ∀ s : I, ∀ x : X, S ((0, x), s) = F₀ (0, x))
    (hRight : ∀ s : I, ∀ x : X, S ((1, x), s) = F₀ (1, x)) :
    F₀.HomotopicRel F₁ (({0, 1} : Set I) ×ˢ (Set.univ : Set X)) := by
  refine ⟨{
    toHomotopy := {
      toContinuousMap := S.comp ContinuousMap.prodSwap
      map_zero_left := hZero
      map_one_left := hOne
    }
    prop' := ?_
  }⟩
  intro s tx htx
  rcases tx with ⟨t, x⟩
  rcases Set.mem_insert_iff.mp htx.1 with ht | ht
  · subst ht
    simpa using hLeft s x
  · have ht' : t = 1 := Set.mem_singleton_iff.mp ht
    subst ht'
    simpa using hRight s x

/-- Helper for Proposition 7.5.3: a relative homotopy can be read back as a square whose vertical
faces are fixed on the time-boundary. -/
private theorem boundaryFixedSquareOfHomotopyRel
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {F₀ F₁ : C(I × X, Y)}
    (hF :
      F₀.HomotopicRel F₁ (({0, 1} : Set I) ×ˢ (Set.univ : Set X))) :
    ∃ square : C((I × X) × I, Y),
      (∀ tx : I × X, square (tx, 0) = F₀ tx) ∧
      (∀ tx : I × X, square (tx, 1) = F₁ tx) ∧
      (∀ s : I, ∀ x : X, square ((0, x), s) = F₀ (0, x)) ∧
      (∀ s : I, ∀ x : X, square ((1, x), s) = F₀ (1, x)) := by
  rcases hF with ⟨hF⟩
  refine ⟨hF.toHomotopy.toContinuousMap.comp ContinuousMap.prodSwap, ?_, ?_, ?_, ?_⟩
  · -- Reading the square at `s = 0` recovers the source map of the relative homotopy.
    intro tx
    simpa using hF.toHomotopy.apply_zero tx
  · -- Reading the square at `s = 1` recovers the target map of the relative homotopy.
    intro tx
    simpa using hF.toHomotopy.apply_one tx
  · -- The `t = 0` face is fixed because the relative homotopy is constant on the boundary.
    intro s x
    exact hF.eq_fst s (x := (0, x)) (by simp)
  · -- The `t = 1` face is fixed for the same reason.
    intro s x
    exact hF.eq_fst s (x := (1, x)) (by simp)

/-- Helper for Proposition 7.5.3: projecting the corrected left-composite homotopy through `p`
normalizes it to the loop built from `hLeftInverseOnBase` and `e.left_inv.some`. -/
private theorem projectedLeftComposite_eq_normalized
    {p : C(D, B)} {q : C(E, B)}
    (f : SpaceOver.mk p ⟶ SpaceOver.mk q)
    (e : D ≃ₕ E) (he : e.toFun = f.left.hom)
    {g : SpaceOver.mk q ⟶ SpaceOver.mk p}
    (hg : e.symm.toFun.Homotopy g.left.hom)
    (hInverseOnBase : (p.comp e.symm.toFun).Homotopy q)
    (hLift : p.comp hg.toContinuousMap = hInverseOnBase.toContinuousMap) :
    let hcomp : q.comp e.toFun = p := homotopyEquivToFun_comp_eq f e he
    let FfgRaw : (e.symm.toFun.comp e.toFun).Homotopy (g.left.hom.comp e.toFun) :=
      ContinuousMap.Homotopy.comp hg (ContinuousMap.Homotopy.refl e.toFun)
    let Ffg : (e.symm.toFun.comp e.toFun).Homotopy (f ≫ g).left.hom :=
      FfgRaw.cast rfl (by
        ext x
        rw [he]
        rfl)
    let hLeftInverseOnBase : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
      (ContinuousMap.Homotopy.comp hInverseOnBase (ContinuousMap.Homotopy.refl e.toFun)).cast
        rfl hcomp
    let leftInverseProjected : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
      ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl p) e.left_inv.some
    p.comp (Ffg.symm.trans e.left_inv.some).toContinuousMap =
      (hLeftInverseOnBase.symm.trans leftInverseProjected).toContinuousMap := by
  have hcomp : q.comp e.toFun = p := homotopyEquivToFun_comp_eq f e he
  let FfgRaw : (e.symm.toFun.comp e.toFun).Homotopy (g.left.hom.comp e.toFun) :=
    ContinuousMap.Homotopy.comp hg (ContinuousMap.Homotopy.refl e.toFun)
  let Ffg : (e.symm.toFun.comp e.toFun).Homotopy (f ≫ g).left.hom :=
    FfgRaw.cast rfl (by
      ext x
      rw [he]
      rfl)
  let hLeftInverseOnBase : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
    (ContinuousMap.Homotopy.comp hInverseOnBase (ContinuousMap.Homotopy.refl e.toFun)).cast
      rfl hcomp
  let leftInverseProjected : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl p) e.left_inv.some
  have hFfg : p.comp Ffg.toContinuousMap = hLeftInverseOnBase.toContinuousMap := by
    -- Projecting the corrected inverse through `p` recovers the left-side base homotopy.
    ext tx
    simpa [hLeftInverseOnBase] using ContinuousMap.congr_fun hLift (tx.1, e.toFun tx.2)
  -- Compare the raw projected left composite with the normalized loop pointwise.
  ext tx
  change p ((Ffg.symm.trans e.left_inv.some) tx) =
    (hLeftInverseOnBase.symm.trans leftInverseProjected) tx
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs with ht
  · simpa [ContinuousMap.Homotopy.symm] using
      ContinuousMap.congr_fun hFfg
        (σ ⟨2 * tx.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨tx.1.2.1, ht⟩⟩, tx.2)
  · rfl

/-- Helper for Proposition 7.5.3: the corrected inverse `g` gives the right composite
`g ≫ f` a homotopy over `B` to the identity on `E`. -/
private theorem rightComposite_homotopicOver
    {p : C(D, B)} {q : C(E, B)}
    (hq : IsFibration.{u, u, u} q)
    (f : SpaceOver.mk p ⟶ SpaceOver.mk q)
    (e : D ≃ₕ E) (he : e.toFun = f.left.hom)
    {g : SpaceOver.mk q ⟶ SpaceOver.mk p}
    (hg : e.symm.toFun.Homotopy g.left.hom)
    (hInverseOnBase : (p.comp e.symm.toFun).Homotopy q)
    (hLift : p.comp hg.toContinuousMap = hInverseOnBase.toContinuousMap)
    (hRightInv : q.comp e.right_inv.some.toContinuousMap = hInverseOnBase.toContinuousMap) :
    HomotopicOver (g ≫ f) (𝟙 (SpaceOver.mk q)) := by
  let FgfRaw : (e.toFun.comp e.symm.toFun).Homotopy (e.toFun.comp g.left.hom) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hg
  let Fgf : (e.toFun.comp e.symm.toFun).Homotopy (g ≫ f).left.hom :=
    FgfRaw.cast rfl (by
      ext x
      rw [he]
      rfl)
  have hFgf : q.comp Fgf.toContinuousMap = hInverseOnBase.toContinuousMap := by
    -- The corrected inverse homotopy still projects to the chosen base homotopy.
    ext tx
    change q (e.toFun (hg tx)) = hInverseOnBase tx
    have hcompPoint :
        q (e.toFun (hg tx)) = p (hg tx) := by
      simpa using congrArg (fun m : C(D, B) => m (hg tx))
        (homotopyEquivToFun_comp_eq f e he)
    exact hcompPoint.trans (ContinuousMap.congr_fun hLift tx)
  have hProjected :
      q.comp (Fgf.symm.trans e.right_inv.some).toContinuousMap =
        (hInverseOnBase.symm.trans hInverseOnBase).toContinuousMap := by
    -- The projected right-composite homotopy is the standard loop `H.symm.trans H`.
    ext tx
    change q ((Fgf.symm.trans e.right_inv.some) tx) = (hInverseOnBase.symm.trans hInverseOnBase) tx
    rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · simpa [ContinuousMap.Homotopy.symm] using
        ContinuousMap.congr_fun hFgf
          (σ ⟨2 * tx.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨tx.1.2.1, ht⟩⟩, tx.2)
    · simpa using
        ContinuousMap.congr_fun hRightInv
          (⟨2 * tx.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, tx.1.2.2⟩⟩,
            tx.2)
  have hProjectedRel :
      (q.comp (Fgf.symm.trans e.right_inv.some).toContinuousMap).HomotopicRel
        ((ContinuousMap.Homotopy.refl q).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set E)) := by
    -- Contract the projected loop and then rewrite back to the concrete projected homotopy.
    exact hProjected ▸ homotopySymmTransHomotopicRelRefl hInverseOnBase
  -- Lift the rectified base loop and read off the resulting homotopy over `B`.
  exact homotopicOver_of_projectedHomotopyRelConst hq (Fgf.symm.trans e.right_inv.some)
    hProjectedRel

/-- Helper for Proposition 7.5.3: the corrected inverse `g` gives the left composite
`f ≫ g` a projected base loop whose only remaining obstruction is the coherence between the
right-inverse-derived base homotopy and `p.comp e.left_inv.some`. -/
private theorem projectedRightWhisker_eq_leftInverseOnBase
    {p : C(D, B)} {q : C(E, B)}
    (f : SpaceOver.mk p ⟶ SpaceOver.mk q)
    (e : D ≃ₕ E) (he : e.toFun = f.left.hom)
    (hInverseOnBase : (p.comp e.symm.toFun).Homotopy q)
    (hRightInv : q.comp e.right_inv.some.toContinuousMap = hInverseOnBase.toContinuousMap) :
    let hcomp : q.comp e.toFun = p := homotopyEquivToFun_comp_eq f e he
    let hLeftInverseOnBase : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
      (ContinuousMap.Homotopy.comp hInverseOnBase (ContinuousMap.Homotopy.refl e.toFun)).cast
        rfl hcomp
    q.comp (ContinuousMap.Homotopy.comp e.right_inv.some
        (ContinuousMap.Homotopy.refl e.toFun)).toContinuousMap =
      hLeftInverseOnBase.toContinuousMap := by
  have hcomp : q.comp e.toFun = p := homotopyEquivToFun_comp_eq f e he
  let hLeftInverseOnBase : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
    (ContinuousMap.Homotopy.comp hInverseOnBase (ContinuousMap.Homotopy.refl e.toFun)).cast
      rfl hcomp
  -- Postcomposing the right-inverse witness by `e.toFun` matches the projected base homotopy.
  ext tx
  simpa [hLeftInverseOnBase] using ContinuousMap.congr_fun hRightInv (tx.1, e.toFun tx.2)

/-- Helper for Proposition 7.5.3: the projected left-whiskered left-inverse homotopy is exactly
the downstream left-base homotopy `leftInverseProjected`. -/
private theorem projectedLeftWhisker_eq_leftInverseProjected
    {p : C(D, B)} {q : C(E, B)}
    (f : SpaceOver.mk p ⟶ SpaceOver.mk q)
    (e : D ≃ₕ E) (he : e.toFun = f.left.hom) :
    let leftInverseProjected : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
      ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl p) e.left_inv.some
    q.comp (ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun)
        e.left_inv.some).toContinuousMap =
      leftInverseProjected.toContinuousMap := by
  have hcomp : q.comp e.toFun = p := homotopyEquivToFun_comp_eq f e he
  let leftInverseProjected : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl p) e.left_inv.some
  -- Rewriting the over-map equation along the left-inverse homotopy gives the projected whisker.
  ext tx
  simpa [leftInverseProjected] using
    congrArg (fun m : C(D, B) => m (e.left_inv.some tx)) hcomp

/-- Helper for Proposition 7.5.3: lifting the left-side base homotopy through `p` produces a
controlled endpoint `u` over `p` and a homotopy from `e.symm.toFun.comp e.toFun` to `u.left.hom`
with the prescribed projection. -/
private theorem leftInverseWithPrescribedProjection
    {p : C(D, B)} {q : C(E, B)}
    (hp : IsFibration.{u, u, u} p)
    (f : SpaceOver.mk p ⟶ SpaceOver.mk q)
    (e : D ≃ₕ E) (he : e.toFun = f.left.hom)
    (hInverseOnBase : (p.comp e.symm.toFun).Homotopy q) :
    let hcomp : q.comp e.toFun = p := homotopyEquivToFun_comp_eq f e he
    let hLeftInverseOnBase : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
      (ContinuousMap.Homotopy.comp hInverseOnBase (ContinuousMap.Homotopy.refl e.toFun)).cast
        rfl hcomp
    ∃ u : SpaceOver.mk p ⟶ SpaceOver.mk p,
      ∃ R : (e.symm.toFun.comp e.toFun).Homotopy u.left.hom,
        p.comp R.toContinuousMap = hLeftInverseOnBase.toContinuousMap := by
  let hcomp : q.comp e.toFun = p := homotopyEquivToFun_comp_eq f e he
  let hLeftInverseOnBase : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
    (ContinuousMap.Homotopy.comp hInverseOnBase (ContinuousMap.Homotopy.refl e.toFun)).cast
      rfl hcomp
  -- Lift the left-side base homotopy starting from `e.symm ∘ e`.
  obtain ⟨u, R, hR⟩ := existsSpaceOverHom_homotopy_of_isFibration hp hLeftInverseOnBase
  exact ⟨u, R, by simpa [hcomp, hLeftInverseOnBase] using hR⟩

/-- Helper for Proposition 7.5.3: once the left-side endpoint is replaced by a controlled map
`u` over `p`, the corrected composite `f ≫ g` is homotopic over `B` to `u`. -/
private theorem leftComposite_homotopicOver_toControlledEndpoint
    {p : C(D, B)} {q : C(E, B)}
    (hp : IsFibration.{u, u, u} p)
    (f : SpaceOver.mk p ⟶ SpaceOver.mk q)
    (e : D ≃ₕ E) (he : e.toFun = f.left.hom)
    {g : SpaceOver.mk q ⟶ SpaceOver.mk p}
    (hg : e.symm.toFun.Homotopy g.left.hom)
    (hInverseOnBase : (p.comp e.symm.toFun).Homotopy q)
    (hLift : p.comp hg.toContinuousMap = hInverseOnBase.toContinuousMap)
    {u : SpaceOver.mk p ⟶ SpaceOver.mk p}
    (R : (e.symm.toFun.comp e.toFun).Homotopy u.left.hom)
    (hR :
      let hcomp : q.comp e.toFun = p := homotopyEquivToFun_comp_eq f e he
      let hLeftInverseOnBase : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
        (ContinuousMap.Homotopy.comp hInverseOnBase (ContinuousMap.Homotopy.refl e.toFun)).cast
          rfl hcomp
      p.comp R.toContinuousMap = hLeftInverseOnBase.toContinuousMap) :
    HomotopicOver (f ≫ g) u := by
  let hcomp : q.comp e.toFun = p := homotopyEquivToFun_comp_eq f e he
  let FfgRaw : (e.symm.toFun.comp e.toFun).Homotopy (g.left.hom.comp e.toFun) :=
    ContinuousMap.Homotopy.comp hg (ContinuousMap.Homotopy.refl e.toFun)
  let Ffg : (e.symm.toFun.comp e.toFun).Homotopy (f ≫ g).left.hom :=
    FfgRaw.cast rfl (by
      ext x
      rw [he]
      rfl)
  let hLeftInverseOnBase : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
    (ContinuousMap.Homotopy.comp hInverseOnBase (ContinuousMap.Homotopy.refl e.toFun)).cast
      rfl hcomp
  have hFfg : p.comp Ffg.toContinuousMap = hLeftInverseOnBase.toContinuousMap := by
    -- Projecting the corrected inverse through `p` recovers the chosen left-side base homotopy.
    ext tx
    simpa [hLeftInverseOnBase] using ContinuousMap.congr_fun hLift (tx.1, e.toFun tx.2)
  have hR' : p.comp R.toContinuousMap = hLeftInverseOnBase.toContinuousMap := by
    simpa [hcomp, hLeftInverseOnBase] using hR
  have hProjected :
      p.comp (Ffg.symm.trans R).toContinuousMap =
        (hLeftInverseOnBase.symm.trans hLeftInverseOnBase).toContinuousMap := by
    -- Both halves of the controlled loop project to the same base homotopy.
    ext tx
    change p ((Ffg.symm.trans R) tx) = (hLeftInverseOnBase.symm.trans hLeftInverseOnBase) tx
    rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · simpa [ContinuousMap.Homotopy.symm] using
        ContinuousMap.congr_fun hFfg
          (σ ⟨2 * tx.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨tx.1.2.1, ht⟩⟩, tx.2)
    · simpa using
        ContinuousMap.congr_fun hR'
          (⟨2 * tx.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, tx.1.2.2⟩⟩,
            tx.2)
  have hProjectedRel :
      (p.comp (Ffg.symm.trans R).toContinuousMap).HomotopicRel
        ((ContinuousMap.Homotopy.refl p).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set D)) := by
    -- After normalization, the controlled loop is the standard self-canceling loop.
    rw [hProjected]
    exact homotopySymmTransHomotopicRelRefl hLeftInverseOnBase
  exact homotopicOver_of_projectedHomotopyRelConst hp (Ffg.symm.trans R) hProjectedRel

/-- Helper for Proposition 7.5.3: the endpoint homotopy `R.symm.trans e.left_inv.some` projects to
the normalized left-side loop built from `hLeftInverseOnBase` and `leftInverseProjected`. -/
private theorem controlledLeftEndpointProjected_eq_normalized
    {p : C(D, B)} {q : C(E, B)}
    (f : SpaceOver.mk p ⟶ SpaceOver.mk q)
    (e : D ≃ₕ E) (he : e.toFun = f.left.hom)
    (hInverseOnBase : (p.comp e.symm.toFun).Homotopy q)
    {u : SpaceOver.mk p ⟶ SpaceOver.mk p}
    (R : (e.symm.toFun.comp e.toFun).Homotopy u.left.hom)
    (hR :
      let hcomp : q.comp e.toFun = p := homotopyEquivToFun_comp_eq f e he
      let hLeftInverseOnBase : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
        (ContinuousMap.Homotopy.comp hInverseOnBase (ContinuousMap.Homotopy.refl e.toFun)).cast
          rfl hcomp
      p.comp R.toContinuousMap = hLeftInverseOnBase.toContinuousMap) :
    let H : u.left.hom.Homotopy (ContinuousMap.id D) := R.symm.trans e.left_inv.some
    let hcomp : q.comp e.toFun = p := homotopyEquivToFun_comp_eq f e he
    let hLeftInverseOnBase : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
      (ContinuousMap.Homotopy.comp hInverseOnBase (ContinuousMap.Homotopy.refl e.toFun)).cast
        rfl hcomp
    let leftInverseProjected : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
      ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl p) e.left_inv.some
    p.comp H.toContinuousMap =
      (hLeftInverseOnBase.symm.trans leftInverseProjected).toContinuousMap := by
  let H : u.left.hom.Homotopy (ContinuousMap.id D) := R.symm.trans e.left_inv.some
  let hcomp : q.comp e.toFun = p := homotopyEquivToFun_comp_eq f e he
  let hLeftInverseOnBase : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
    (ContinuousMap.Homotopy.comp hInverseOnBase (ContinuousMap.Homotopy.refl e.toFun)).cast
      rfl hcomp
  let leftInverseProjected : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl p) e.left_inv.some
  have hR' : p.comp R.toContinuousMap = hLeftInverseOnBase.toContinuousMap := by
    simpa [hcomp, hLeftInverseOnBase] using hR
  -- Compare the projected endpoint homotopy pointwise with the normalized left loop.
  ext tx
  change p ((R.symm.trans e.left_inv.some) tx) =
    (hLeftInverseOnBase.symm.trans leftInverseProjected) tx
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs with ht
  · simpa [H, ContinuousMap.Homotopy.symm] using
      ContinuousMap.congr_fun hR'
        (σ ⟨2 * tx.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨tx.1.2.1, ht⟩⟩, tx.2)
  · rfl

/-- Helper for Proposition 7.5.3: a homotopy relative to `({0, 1} : Set I) ×ˢ Set.univ`
fixes the time-`0` and time-`1` boundary values of the underlying homotopies. -/
private theorem homotopyRel_eq_fst_boundary
    {X : Type u} [TopologicalSpace X]
    {F G : C(I × X, B)}
    (hFG :
      F.HomotopicRel G (({0, 1} : Set I) ×ˢ (Set.univ : Set X)))
    (x : X) :
    F (0, x) = G (0, x) ∧ F (1, x) = G (1, x) := by
  -- The two distinguished time slices are exactly the boundary subset recorded in `HomotopicRel`.
  constructor
  · exact hFG.fst_eq_snd (x := ⟨0, x⟩) ⟨by simp, by simp⟩
  · exact hFG.fst_eq_snd (x := ⟨1, x⟩) ⟨by simp, by simp⟩

/-- Helper for Proposition 7.5.3: reading the `t = 1` boundary on the symmetrized comparison
homotopy gives the common endpoint of `K`. -/
private theorem homotopyRelSymm_apply_one
    {X : Type u} [TopologicalSpace X]
    {r₀ r₁ : C(X, B)} {H K : r₀.Homotopy r₁}
    (hHK :
      H.toContinuousMap.HomotopyRel K.toContinuousMap
        (({0, 1} : Set I) ×ˢ (Set.univ : Set X)))
    (s : I) (x : X) :
    hHK.toHomotopy.symm (s, (1, x)) = K (1, x) := by
  -- The symmetrized relative homotopy is fixed on the endpoint boundary because `hHK` is.
  simpa [ContinuousMap.Homotopy.symm] using
    hHK.eq_snd (σ s) (x := (1, x)) (by simp)

/-- Helper for Proposition 7.5.3: whiskering a relative comparison by a fixed right factor
preserves the time-boundary conditions. -/
private theorem transCongrRight_homotopyRel
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f₀ f₁ f₂ : C(X, Y)}
    {L M : f₀.Homotopy f₁} (K : f₁.Homotopy f₂)
    (hLM :
      L.toContinuousMap.HomotopicRel M.toContinuousMap
        (({0, 1} : Set I) ×ˢ (Set.univ : Set X))) :
    (L.trans K).toContinuousMap.HomotopicRel
      (M.trans K).toContinuousMap
      (({0, 1} : Set I) ×ˢ (Set.univ : Set X)) := by
  rcases hLM with ⟨hLM⟩
  let leftBranch : C((I × X) × I, Y) :=
    { toFun := fun u ↦
        hLM.toHomotopy
          (u.2, (Set.projIcc 0 1 zero_le_one (2 * ((u.1).1 : ℝ)), (u.1).2))
      continuous_toFun := by
        fun_prop }
  let rightBranch : C((I × X) × I, Y) :=
    { toFun := fun u ↦
        K (Set.projIcc 0 1 zero_le_one (2 * ((u.1).1 : ℝ) - 1), (u.1).2)
      continuous_toFun := by
        fun_prop }
  let square : C((I × X) × I, Y) :=
    { toFun := fun u ↦
        if h : (((u.1).1 : I) : ℝ) ≤ 1 / 2 then leftBranch u else rightBranch u
      continuous_toFun := by
        refine continuous_if_le (by fun_prop) continuous_const
          leftBranch.continuous.continuousOn rightBranch.continuous.continuousOn ?_
        intro u hu
        rcases u with ⟨⟨t, x⟩, s⟩
        -- The two branches meet at the common `t = 1` endpoint of the left factor.
        have hLeftBranch :
            leftBranch ((t, x), s) = f₁ x := by
          have ht : (t : ℝ) = 1 / 2 := hu
          simpa [leftBranch, ht] using
            hLM.eq_snd s (x := (1, x)) (by simp)
        have hRightBranch :
            rightBranch ((t, x), s) = f₁ x := by
          have ht : (t : ℝ) = 1 / 2 := hu
          simp [rightBranch, ht]
        rw [hLeftBranch, hRightBranch] }
  -- Package the square by reading it as a relative homotopy between the two right-whiskered
  -- composites.
  refine homotopyRelOfBoundaryFixedSquare square ?_ ?_ ?_ ?_
  · intro tx
    rcases tx with ⟨t, x⟩
    rw [show square (⟨t, x⟩, 0) =
        if h : (t : ℝ) ≤ 1 / 2 then leftBranch (⟨t, x⟩, 0) else rightBranch (⟨t, x⟩, 0) by
      rfl]
    change (if h : (t : ℝ) ≤ 1 / 2 then leftBranch (⟨t, x⟩, 0) else rightBranch (⟨t, x⟩, 0)) =
      (L.trans K) (t, x)
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · have hmem : 2 * (t : ℝ) ∈ I := by
        constructor
        · nlinarith [t.2.1]
        · nlinarith [ht]
      simpa [leftBranch, Set.projIcc_of_mem _ hmem] using
        hLM.toHomotopy.apply_zero (⟨2 * t, hmem⟩, x)
    · have hmem : 2 * (t : ℝ) - 1 ∈ I := by
        constructor
        · nlinarith [(not_le.1 ht).le]
        · nlinarith [t.2.2]
      simpa [rightBranch, Set.projIcc_of_mem _ hmem]
  · intro tx
    rcases tx with ⟨t, x⟩
    rw [show square (⟨t, x⟩, 1) =
        if h : (t : ℝ) ≤ 1 / 2 then leftBranch (⟨t, x⟩, 1) else rightBranch (⟨t, x⟩, 1) by
      rfl]
    change (if h : (t : ℝ) ≤ 1 / 2 then leftBranch (⟨t, x⟩, 1) else rightBranch (⟨t, x⟩, 1)) =
      (M.trans K) (t, x)
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · have hmem : 2 * (t : ℝ) ∈ I := by
        constructor
        · nlinarith [t.2.1]
        · nlinarith [ht]
      simpa [leftBranch, Set.projIcc_of_mem _ hmem] using
        hLM.toHomotopy.apply_one (⟨2 * t, hmem⟩, x)
    · have hmem : 2 * (t : ℝ) - 1 ∈ I := by
        constructor
        · nlinarith [(not_le.1 ht).le]
        · nlinarith [t.2.2]
      simpa [rightBranch, Set.projIcc_of_mem _ hmem]
  · intro s x
    -- The `t = 0` face stays on the common start of the compared left factors.
    simpa [square, leftBranch] using
      hLM.eq_fst s (x := (0, x)) (by simp)
  · intro s x
    -- The `t = 1` face stays on the fixed endpoint of the right factor.
    have hproj :
        Set.projIcc 0 1 zero_le_one (2 * ((1 : I) : ℝ) - 1) = (1 : I) := by
      apply Subtype.ext
      norm_num
    have hFalse : ¬ (((1 : I) : ℝ) ≤ 1 / 2) := by
      norm_num
    change
      (if h : (((1 : I) : ℝ) ≤ 1 / 2) then leftBranch ((1, x), s) else rightBranch ((1, x), s)) =
        (L.trans K) (1, x)
    rw [dif_neg hFalse]
    rw [show rightBranch ((1, x), s) =
        K (Set.projIcc 0 1 zero_le_one (2 * ((1 : I) : ℝ) - 1), x) by
      rfl]
    rw [hproj]
    simpa using K.apply_one x

/-- Helper for Proposition 7.5.3: any endpoint-preserving reparametrization of a homotopy is
relative-homotopic to the original homotopy on `({0, 1} : Set I) ×ˢ Set.univ`. -/
private theorem homotopyReparamHomotopicRel
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f₀ f₁ : C(X, Y)}
    (H : f₀.Homotopy f₁) (r : I → I) (hr : Continuous r)
    (hr₀ : r 0 = 0) (hr₁ : r 1 = 1) :
    let Hreparam : f₀.Homotopy f₁ :=
      { toFun := fun tx ↦ H (r tx.1, tx.2)
        continuous_toFun := by
          have hpair : Continuous fun tx : I × X ↦ (r tx.1, tx.2) := by
            fun_prop
          simpa using H.continuous.comp hpair
        map_zero_left := by
          intro x
          simpa [hr₀] using H.apply_zero x
        map_one_left := by
          intro x
          simpa [hr₁] using H.apply_one x }
    H.toContinuousMap.HomotopicRel Hreparam.toContinuousMap
      (({0, 1} : Set I) ×ˢ (Set.univ : Set X)) := by
  let Hreparam : f₀.Homotopy f₁ :=
    { toFun := fun tx ↦ H (r tx.1, tx.2)
      continuous_toFun := by
        have hpair : Continuous fun tx : I × X ↦ (r tx.1, tx.2) := by
          fun_prop
        simpa using H.continuous.comp hpair
      map_zero_left := by
        intro x
        simpa [hr₀] using H.apply_zero x
      map_one_left := by
        intro x
        simpa [hr₁] using H.apply_one x }
  let squareTime : (I × X) × I → I := fun us ↦
    ⟨σ us.2 * us.1.1 + us.2 * r us.1.1,
      show (σ us.2 : ℝ) • (us.1.1 : ℝ) + (us.2 : ℝ) • (r us.1.1 : ℝ) ∈ I from
        convex_Icc _ _ us.1.1.2 (r us.1.1).2
          (by unit_interval) (by unit_interval) (by simp)⟩
  let square : C((I × X) × I, Y) :=
    { toFun := fun us ↦ H (squareTime us, us.1.2)
      continuous_toFun := by
        have hsquareTime : Continuous squareTime := by
          fun_prop
        have hpair : Continuous fun us : (I × X) × I ↦ (squareTime us, us.1.2) := by
          exact hsquareTime.prodMk continuous_fst.snd
        simpa using H.continuous.comp hpair }
  -- Interpolate linearly between the identity parameter and the chosen reparametrization.
  refine homotopyRelOfBoundaryFixedSquare square ?_ ?_ ?_ ?_
  · intro tx
    rcases tx with ⟨t, x⟩
    change H (squareTime ((t, x), 0), x) = H (t, x)
    have hTime : squareTime ((t, x), 0) = t := by
      apply Subtype.ext
      simp [squareTime]
    simpa [hTime]
  · intro tx
    rcases tx with ⟨t, x⟩
    change H (squareTime ((t, x), 1), x) = Hreparam (t, x)
    have hTime : squareTime ((t, x), 1) = r t := by
      apply Subtype.ext
      simp [squareTime]
    simpa [Hreparam] using congrArg (fun u : I ↦ H (u, x)) hTime
  · intro s x
    change H (squareTime ((0, x), s), x) = H (0, x)
    have hTime : squareTime ((0, x), s) = 0 := by
      apply Subtype.ext
      simp [squareTime, hr₀]
    simpa [hTime]
  · intro s x
    change H (squareTime ((1, x), s), x) = H (1, x)
    have hTime : squareTime ((1, x), s) = 1 := by
      apply Subtype.ext
      simp [squareTime, hr₁]
    simpa [hTime]

/-- Helper for Proposition 7.5.3: the reflexive left whisker of a homotopy contracts relative to
the time-boundary to the original homotopy. -/
private theorem symmTransCongrLeft_homotopyRel
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f₀ f₁ f₂ : C(X, Y)}
    (L : f₀.Homotopy f₁) {M N : f₀.Homotopy f₂}
    (hMN :
      M.toContinuousMap.HomotopicRel N.toContinuousMap
        (({0, 1} : Set I) ×ˢ (Set.univ : Set X))) :
    (L.symm.trans M).toContinuousMap.HomotopicRel
      (L.symm.trans N).toContinuousMap
      (({0, 1} : Set I) ×ˢ (Set.univ : Set X)) := by
  rcases hMN with ⟨hMN⟩
  let leftBranch : C((I × X) × I, Y) :=
    { toFun := fun u ↦
        L
          (σ (Set.projIcc 0 1 zero_le_one (2 * ((u.1).1 : ℝ))), (u.1).2)
      continuous_toFun := by
        fun_prop }
  let rightBranch : C((I × X) × I, Y) :=
    { toFun := fun u ↦
        hMN.toHomotopy
          (u.2, (Set.projIcc 0 1 zero_le_one (2 * ((u.1).1 : ℝ) - 1), (u.1).2))
      continuous_toFun := by
        fun_prop }
  let square : C((I × X) × I, Y) :=
    { toFun := fun u ↦
        if h : (((u.1).1 : I) : ℝ) ≤ 1 / 2 then leftBranch u else rightBranch u
      continuous_toFun := by
        refine continuous_if_le (by fun_prop) continuous_const
          leftBranch.continuous.continuousOn rightBranch.continuous.continuousOn ?_
        intro u hu
        rcases u with ⟨⟨t, x⟩, s⟩
        -- The two branches meet at the common `t = 0` endpoint of the right factor.
        have hLeftBranch :
            leftBranch ((t, x), s) = L (0, x) := by
          have ht : (t : ℝ) = 1 / 2 := hu
          simp [leftBranch, ht]
        have hRightBranch :
            rightBranch ((t, x), s) = L (0, x) := by
          have ht : (t : ℝ) = 1 / 2 := hu
          simpa [rightBranch, ht] using
            hMN.eq_fst s (x := (0, x)) (by simp)
        rw [hLeftBranch, hRightBranch] }
  -- Package the square as a relative homotopy between the two left-whiskered composites.
  refine homotopyRelOfBoundaryFixedSquare square ?_ ?_ ?_ ?_
  · intro tx
    rcases tx with ⟨t, x⟩
    rw [show square (⟨t, x⟩, 0) =
        if h : (t : ℝ) ≤ 1 / 2 then leftBranch (⟨t, x⟩, 0) else rightBranch (⟨t, x⟩, 0) by
      rfl]
    change (if h : (t : ℝ) ≤ 1 / 2 then leftBranch (⟨t, x⟩, 0) else rightBranch (⟨t, x⟩, 0)) =
      (L.symm.trans M) (t, x)
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · have hmem : 2 * (t : ℝ) ∈ I := by
        constructor
        · nlinarith [t.2.1]
        · nlinarith [ht]
      have hproj :
          Set.projIcc 0 1 zero_le_one (2 * (t : ℝ)) = (⟨2 * t, hmem⟩ : I) := by
        apply Subtype.ext
        simp [Set.projIcc_of_mem _ hmem]
      change leftBranch (⟨t, x⟩, 0) = (L.symm) (⟨2 * t, hmem⟩, x)
      change L (σ (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ))), x) =
        L (σ (⟨2 * t, hmem⟩ : I), x)
      exact congrArg (fun u : I ↦ L (σ u, x)) hproj
    · have hmem : 2 * (t : ℝ) - 1 ∈ I := by
        constructor
        · nlinarith [(not_le.1 ht).le]
        · nlinarith [t.2.2]
      simpa [rightBranch, Set.projIcc_of_mem _ hmem] using
        hMN.toHomotopy.apply_zero (⟨2 * t - 1, hmem⟩, x)
  · intro tx
    rcases tx with ⟨t, x⟩
    rw [show square (⟨t, x⟩, 1) =
        if h : (t : ℝ) ≤ 1 / 2 then leftBranch (⟨t, x⟩, 1) else rightBranch (⟨t, x⟩, 1) by
      rfl]
    change (if h : (t : ℝ) ≤ 1 / 2 then leftBranch (⟨t, x⟩, 1) else rightBranch (⟨t, x⟩, 1)) =
      (L.symm.trans N) (t, x)
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · have hmem : 2 * (t : ℝ) ∈ I := by
        constructor
        · nlinarith [t.2.1]
        · nlinarith [ht]
      have hproj :
          Set.projIcc 0 1 zero_le_one (2 * (t : ℝ)) = (⟨2 * t, hmem⟩ : I) := by
        apply Subtype.ext
        simp [Set.projIcc_of_mem _ hmem]
      change leftBranch (⟨t, x⟩, 1) = (L.symm) (⟨2 * t, hmem⟩, x)
      change L (σ (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ))), x) =
        L (σ (⟨2 * t, hmem⟩ : I), x)
      exact congrArg (fun u : I ↦ L (σ u, x)) hproj
    · have hmem : 2 * (t : ℝ) - 1 ∈ I := by
        constructor
        · nlinarith [(not_le.1 ht).le]
        · nlinarith [t.2.2]
      simpa [rightBranch, Set.projIcc_of_mem _ hmem] using
        hMN.toHomotopy.apply_one (⟨2 * t - 1, hmem⟩, x)
  · intro s x
    -- The `t = 0` face lies entirely on the common left endpoint `f₁`.
    simpa [square, leftBranch, ContinuousMap.Homotopy.symm] using
      (L.symm.trans M).apply_zero x
  · intro s x
    -- The `t = 1` face lies entirely on the common right endpoint `f₂`.
    have hFace :
        rightBranch ((1, x), s) = M (1, x) := by
      have hmem : 2 * ((1 : I) : ℝ) - 1 ∈ I := by
        norm_num
      have hproj :
          Set.projIcc 0 1 zero_le_one (2 * ((1 : I) : ℝ) - 1) = (1 : I) := by
        apply Subtype.ext
        norm_num
      change hMN.toHomotopy (s, (Set.projIcc 0 1 zero_le_one (2 * ((1 : I) : ℝ) - 1), x)) =
        M (1, x)
      rw [hproj]
      simpa using hMN.eq_fst s (x := (1, x)) (by simp)
    have hFalse : ¬ (((1 : I) : ℝ) ≤ 1 / 2) := by
      norm_num
    change
      (if h : (((1 : I) : ℝ) ≤ 1 / 2) then leftBranch ((1, x), s) else rightBranch ((1, x), s)) =
        (L.symm.trans M) (1, x)
    have hIf :
        (if h : (((1 : I) : ℝ) ≤ 1 / 2) then leftBranch ((1, x), s) else rightBranch ((1, x), s)) =
          rightBranch ((1, x), s) := by
      rw [dif_neg hFalse]
    rw [hIf]
    simpa using hFace

/-- Helper for Proposition 7.5.3: the reflexive left whisker of a homotopy contracts relative to
the time-boundary to the original homotopy. -/
private theorem reflTrans_homotopyRel
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f₀ f₁ : C(X, Y)}
    (K : f₀.Homotopy f₁) :
    (((ContinuousMap.Homotopy.refl f₀).trans K).toContinuousMap).HomotopicRel
      K.toContinuousMap
      (({0, 1} : Set I) ×ˢ (Set.univ : Set X)) := by
  let reflTransReparamAux : I → ℝ := fun t ↦
    if (t : ℝ) ≤ 1 / 2 then 0 else 2 * t - 1
  have hReflTransReparamAux : Continuous reflTransReparamAux := by
    refine continuous_if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) ?_
    intro t ht
    have ht' : (t : ℝ) = 1 / 2 := ht
    simp [reflTransReparamAux, ht']
  have hReflTransReparamAux_mem : ∀ t : I, reflTransReparamAux t ∈ I := by
    intro t
    dsimp [reflTransReparamAux]
    split_ifs with ht
    · constructor <;> norm_num
    · constructor
      · nlinarith [(not_le.1 ht).le]
      · nlinarith [t.2.2]
  let reflTransReparam : I → I := fun t ↦
    ⟨reflTransReparamAux t, hReflTransReparamAux_mem t⟩
  have hReflTransReparam : Continuous reflTransReparam := by
    exact Continuous.subtype_mk hReflTransReparamAux hReflTransReparamAux_mem
  let Hreparam : f₀.Homotopy f₁ :=
    { toFun := fun tx ↦ K (reflTransReparam tx.1, tx.2)
      continuous_toFun := by
        have hpair : Continuous fun tx : I × X ↦ (reflTransReparam tx.1, tx.2) := by
          exact (hReflTransReparam.comp continuous_fst).prodMk continuous_snd
        simpa using K.continuous.comp hpair
      map_zero_left := by
        intro x
        simp [reflTransReparam, reflTransReparamAux]
      map_one_left := by
        intro x
        have hEq : reflTransReparam 1 = (1 : I) := by
          apply Subtype.ext
          norm_num [reflTransReparam, reflTransReparamAux]
        simpa [hEq] using K.apply_one x }
  have hEq :
      Hreparam.toContinuousMap =
        (((ContinuousMap.Homotopy.refl f₀).trans K).toContinuousMap) := by
    ext tx
    rcases tx with ⟨t, x⟩
    change Hreparam (t, x) = ((ContinuousMap.Homotopy.refl f₀).trans K) (t, x)
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · have hZero : reflTransReparam t = 0 := by
        apply Subtype.ext
        have hZeroAux : reflTransReparamAux t = 0 := by
          dsimp [reflTransReparamAux]
          rw [if_pos ht]
        simpa [reflTransReparam, hZeroAux]
      have hTarget : ((ContinuousMap.Homotopy.refl f₀).trans K) (t, x) = f₀ x := by
        rw [ContinuousMap.Homotopy.trans_apply]
        split_ifs with h
        · rfl
        · exact False.elim (h ht)
      rw [hTarget]
      calc
        Hreparam (t, x) = K (reflTransReparam t, x) := rfl
        _ = K (0, x) := by rw [hZero]
        _ = f₀ x := by simpa using K.apply_zero x
    · have hmem : 2 * (t : ℝ) - 1 ∈ I := by
        constructor
        · nlinarith [(not_le.1 ht).le]
        · nlinarith [t.2.2]
      have hReparam :
          reflTransReparam t = ⟨2 * t - 1, hmem⟩ := by
        apply Subtype.ext
        have hAux : reflTransReparamAux t = 2 * (t : ℝ) - 1 := by
          dsimp [reflTransReparamAux]
          rw [if_neg ht]
        simpa [reflTransReparam, hAux]
      have hTarget :
          ((ContinuousMap.Homotopy.refl f₀).trans K) (t, x) = K (⟨2 * t - 1, hmem⟩, x) := by
        rw [ContinuousMap.Homotopy.trans_apply]
        split_ifs with h
        · exact False.elim (ht h)
        · rfl
      rw [hTarget]
      calc
        Hreparam (t, x) = K (reflTransReparam t, x) := rfl
        _ = K (⟨2 * t - 1, hmem⟩, x) := by rw [hReparam]
  -- Collapse the idle first half by the generic endpoint-preserving reparametrization lemma.
  have hReparam :
      K.toContinuousMap.HomotopicRel Hreparam.toContinuousMap
        (({0, 1} : Set I) ×ˢ (Set.univ : Set X)) := by
    exact
      homotopyReparamHomotopicRel
        K reflTransReparam
        hReflTransReparam
        (by
          apply Subtype.ext
          simp [reflTransReparam, reflTransReparamAux])
        (by
          apply Subtype.ext
          norm_num [reflTransReparam, reflTransReparamAux])
  rcases ContinuousMap.HomotopicRel.symm hReparam with ⟨hReparam⟩
  exact ⟨hReparam.cast hEq rfl⟩

/-- Helper for Proposition 7.5.3: after whiskering on the right, the standard contraction of
`L.symm.trans L` still produces a relative comparison to the corresponding reflexive whisker. -/
private theorem symmTransTransReflCongrRight_homotopyRel
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactlyGeneratedWeakHausdorffSpace.{u, u} Y]
    {f₀ f₁ f₂ : C(X, Y)}
    (L : f₀.Homotopy f₁) (K : f₁.Homotopy f₂) :
    ((L.symm.trans L).trans K).toContinuousMap.HomotopicRel
      (((ContinuousMap.Homotopy.refl f₁).trans K).toContinuousMap)
      (({0, 1} : Set I) ×ˢ (Set.univ : Set X)) := by
  -- Whisker the standard relative contraction of `L.symm.trans L` by the fixed trailing factor.
  exact transCongrRight_homotopyRel K (homotopySymmTransHomotopicRelRefl L)

/-- Helper for Proposition 7.5.3: rebracketing `L.symm.trans (L.trans K)` changes only the time
parameter, so the two bracketings are relative-homotopic on the time-boundary. -/
private theorem symmTransTrans_assoc_homotopyRel
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f₀ f₁ f₂ : C(X, Y)}
    (L : f₀.Homotopy f₁) (K : f₁.Homotopy f₂) :
    (L.symm.trans (L.trans K)).toContinuousMap.HomotopicRel
      (((L.symm.trans L).trans K).toContinuousMap)
      (({0, 1} : Set I) ×ˢ (Set.univ : Set X)) := by
  let assocReparam : I → I := fun t ↦
    ⟨Path.Homotopy.transAssocReparamAux t, Path.Homotopy.transAssocReparamAux_mem_I t⟩
  let Hreparam : f₁.Homotopy f₂ :=
    { toFun := fun tx ↦ (L.symm.trans (L.trans K)) (assocReparam tx.1, tx.2)
      continuous_toFun := by
        have hpair : Continuous fun tx : I × X ↦ (assocReparam tx.1, tx.2) := by
          fun_prop
        simpa using (L.symm.trans (L.trans K)).continuous.comp hpair
      map_zero_left := by
        intro x
        simpa [assocReparam, Path.Homotopy.transAssocReparamAux_zero] using
          (L.symm.trans (L.trans K)).apply_zero x
      map_one_left := by
        intro x
        simpa [assocReparam, Path.Homotopy.transAssocReparamAux_one] using
          (L.symm.trans (L.trans K)).apply_one x }
  have hEq :
      Hreparam.toContinuousMap = (((L.symm.trans L).trans K).toContinuousMap) := by
    ext tx
    rcases tx with ⟨t, x⟩
    let p : Path (f₁ x) (f₀ x) := (L.symm).evalAt x
    let q : Path (f₀ x) (f₁ x) := L.evalAt x
    let r : Path (f₁ x) (f₂ x) := K.evalAt x
    have hPath := Path.Homotopy.trans_assoc_reparam p q r
    have hAt := congrArg (fun γ : Path (f₁ x) (f₂ x) => γ t) hPath.symm
    simpa [p, q, r, Hreparam, assocReparam, ContinuousMap.Homotopy.evalAt] using hAt
  -- Compare the two bracketings by the generic reparametrization principle, then cast the target
  -- to the normalized triple composite used in the cancellation step.
  have hReparam :
      (L.symm.trans (L.trans K)).toContinuousMap.HomotopicRel
        Hreparam.toContinuousMap
        (({0, 1} : Set I) ×ˢ (Set.univ : Set X)) := by
    exact
      homotopyReparamHomotopicRel
        (L.symm.trans (L.trans K)) assocReparam
        (by
          fun_prop)
        (by
          apply Subtype.ext
          exact Path.Homotopy.transAssocReparamAux_zero)
        (by
          apply Subtype.ext
          exact Path.Homotopy.transAssocReparamAux_one)
  rcases hReparam with ⟨hReparam⟩
  exact ⟨hReparam.cast rfl hEq⟩

/-- Helper for Proposition 7.5.3: the exact cancellation
`L.symm.trans (L.trans K) ~ rel K` is obtained by rebracketing, contracting `L.symm.trans L`,
and then collapsing the reflexive prefix. -/
private theorem symmTransTransCancel_homotopyRel
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactlyGeneratedWeakHausdorffSpace.{u, u} Y]
    {f₀ f₁ f₂ : C(X, Y)}
    (L : f₀.Homotopy f₁) (K : f₁.Homotopy f₂) :
    (L.symm.trans (L.trans K)).toContinuousMap.HomotopicRel
      K.toContinuousMap
      (({0, 1} : Set I) ×ˢ (Set.univ : Set X)) := by
  -- Reassociate first so the existing `L.symm.trans L` contraction applies in the exact shape.
  refine ContinuousMap.HomotopicRel.trans
    (symmTransTrans_assoc_homotopyRel L K) ?_
  -- After contracting `L.symm.trans L`, only the reflexive left whisker of `K` remains.
  refine ContinuousMap.HomotopicRel.trans
    (symmTransTransReflCongrRight_homotopyRel L K) ?_
  -- Collapse the remaining reflexive prefix by reparametrizing away the idle initial segment.
  exact reflTrans_homotopyRel K

/-- Helper for Proposition 7.5.3: a relative homotopy between the right factors of
`H.symm.trans _` transports to a relative homotopy between the resulting loops. -/
private theorem symmTransCongrRight_homotopyRel
    {X : Type u} [TopologicalSpace X]
    {r₀ r₁ : C(X, B)}
    (H K : r₀.Homotopy r₁)
    (hHK :
      H.toContinuousMap.HomotopicRel K.toContinuousMap
        (({0, 1} : Set I) ×ˢ (Set.univ : Set X))) :
    (H.symm.trans K).toContinuousMap.HomotopicRel
      (H.symm.trans H).toContinuousMap
      (({0, 1} : Set I) ×ˢ (Set.univ : Set X)) := by
  rcases hHK with ⟨hHK⟩
  let leftBranch : C((I × X) × I, B) :=
    { toFun := fun u ↦
        H
          (σ (Set.projIcc 0 1 zero_le_one (2 * ((u.1).1 : ℝ))), (u.1).2)
      continuous_toFun := by
        fun_prop }
  let rightBranch : C((I × X) × I, B) :=
    { toFun := fun u ↦
        hHK.toHomotopy.symm
          (u.2, (Set.projIcc 0 1 zero_le_one (2 * ((u.1).1 : ℝ) - 1), (u.1).2))
      continuous_toFun := by
        fun_prop }
  let square : C((I × X) × I, B) :=
    { toFun := fun u ↦
        if h : (((u.1).1 : I) : ℝ) ≤ 1 / 2 then leftBranch u else rightBranch u
      continuous_toFun := by
        refine continuous_if_le (by fun_prop) continuous_const
          leftBranch.continuous.continuousOn rightBranch.continuous.continuousOn ?_
        intro u hu
        rcases u with ⟨⟨t, x⟩, s⟩
        -- The branch point is exactly the common `t = 0` boundary of the right factor.
        have hLeft :
            leftBranch ((t, x), s) = H (0, x) := by
          have ht : (t : ℝ) = 1 / 2 := hu
          simp [leftBranch, ht]
        have hRight :
            rightBranch ((t, x), s) = H (0, x) := by
          have ht : (t : ℝ) = 1 / 2 := hu
          simpa [rightBranch, ht, ContinuousMap.Homotopy.symm] using
            hHK.eq_fst (σ s) (x := (0, x)) (by simp)
        rw [hLeft, hRight] }
  refine homotopyRelOfBoundaryFixedSquare square ?_ ?_ ?_ ?_
  · intro tx
    rcases tx with ⟨t, x⟩
    -- At `s = 0`, the right branch reads the original right factor `K`.
    rw [show square (⟨t, x⟩, 0) =
        if h : (t : ℝ) ≤ 1 / 2 then leftBranch (⟨t, x⟩, 0) else rightBranch (⟨t, x⟩, 0) by
      rfl]
    change (if h : (t : ℝ) ≤ 1 / 2 then leftBranch (⟨t, x⟩, 0) else rightBranch (⟨t, x⟩, 0)) =
      (H.symm.trans K) (t, x)
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · have hmem : 2 * (t : ℝ) ∈ I := by
        constructor
        · nlinarith [t.2.1]
        · nlinarith [ht]
      have hproj :
          Set.projIcc 0 1 zero_le_one (2 * (t : ℝ)) = (⟨2 * t, hmem⟩ : I) := by
        apply Subtype.ext
        simp [Set.projIcc_of_mem _ hmem]
      change leftBranch (⟨t, x⟩, 0) = (H.symm) (⟨2 * t, hmem⟩, x)
      change H (σ (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ))), x) =
        H (σ (⟨2 * t, hmem⟩ : I), x)
      exact congrArg (fun u : I => H (σ u, x)) hproj
    · have hmem : 2 * (t : ℝ) - 1 ∈ I := by
        constructor
        · nlinarith [(not_le.1 ht).le]
        · nlinarith [t.2.2]
      simpa [rightBranch, ContinuousMap.Homotopy.symm, Set.projIcc_of_mem _ hmem] using
        hHK.toHomotopy.apply_one (⟨2 * t - 1, hmem⟩, x)
  · intro tx
    rcases tx with ⟨t, x⟩
    -- At `s = 1`, the right branch reads the fixed homotopy `H`.
    rw [show square (⟨t, x⟩, 1) =
        if h : (t : ℝ) ≤ 1 / 2 then leftBranch (⟨t, x⟩, 1) else rightBranch (⟨t, x⟩, 1) by
      rfl]
    change (if h : (t : ℝ) ≤ 1 / 2 then leftBranch (⟨t, x⟩, 1) else rightBranch (⟨t, x⟩, 1)) =
      (H.symm.trans H) (t, x)
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · have hmem : 2 * (t : ℝ) ∈ I := by
        constructor
        · nlinarith [t.2.1]
        · nlinarith [ht]
      have hproj :
          Set.projIcc 0 1 zero_le_one (2 * (t : ℝ)) = (⟨2 * t, hmem⟩ : I) := by
        apply Subtype.ext
        simp [Set.projIcc_of_mem _ hmem]
      change leftBranch (⟨t, x⟩, 1) = (H.symm) (⟨2 * t, hmem⟩, x)
      change H (σ (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ))), x) =
        H (σ (⟨2 * t, hmem⟩ : I), x)
      exact congrArg (fun u : I => H (σ u, x)) hproj
    · have hmem : 2 * (t : ℝ) - 1 ∈ I := by
        constructor
        · nlinarith [(not_le.1 ht).le]
        · nlinarith [t.2.2]
      simpa [rightBranch, ContinuousMap.Homotopy.symm, Set.projIcc_of_mem _ hmem] using
        hHK.toHomotopy.apply_zero (⟨2 * t - 1, hmem⟩, x)
  · intro s x
    -- The `t = 0` face lies entirely on the common left endpoint `r₁`.
    simpa [square, leftBranch, ContinuousMap.Homotopy.symm] using
      (H.symm.trans K).apply_zero x
  · intro s x
    -- The `t = 1` face lies entirely on the common right endpoint `r₁`.
    have hFace :
        rightBranch ((1, x), s) = K (1, x) := by
      have hmem : 2 * ((1 : I) : ℝ) - 1 ∈ I := by
        norm_num
      have hproj :
          Set.projIcc 0 1 zero_le_one (2 * ((1 : I) : ℝ) - 1) = (1 : I) := by
        apply Subtype.ext
        norm_num
      change hHK.toHomotopy.symm (s, (Set.projIcc 0 1 zero_le_one (2 * ((1 : I) : ℝ) - 1), x)) =
        K (1, x)
      rw [hproj]
      simpa using homotopyRelSymm_apply_one hHK s x
    have hFalse : ¬ (((1 : I) : ℝ) ≤ 1 / 2) := by
      norm_num
    change
      (if h : (((1 : I) : ℝ) ≤ 1 / 2) then leftBranch ((1, x), s) else rightBranch ((1, x), s)) =
        (H.symm.trans K) (1, x)
    have hIf :
        (if h : (((1 : I) : ℝ) ≤ 1 / 2) then leftBranch ((1, x), s) else rightBranch ((1, x), s)) =
          rightBranch ((1, x), s) := by
      rw [dif_neg hFalse]
    rw [hIf]
    simpa using hFace

/-- Helper for Proposition 7.5.3: the normalized left endpoint loop
`hLeftInverseOnBase` and `leftInverseProjected` are the two canonical projected left-side
homotopies that still need to be compared rel boundary. -/
private theorem whiskeredInverseHomotopies_eq_boundary
    (e : D ≃ₕ E) (x : D) :
    let rightWhisker :
        (e.toFun.comp (e.symm.toFun.comp e.toFun)).Homotopy e.toFun :=
      ContinuousMap.Homotopy.comp e.right_inv.some (ContinuousMap.Homotopy.refl e.toFun)
    let leftWhisker :
        (e.toFun.comp (e.symm.toFun.comp e.toFun)).Homotopy e.toFun :=
      ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) e.left_inv.some
    rightWhisker (0, x) = leftWhisker (0, x) ∧
      rightWhisker (1, x) = leftWhisker (1, x) := by
  let rightWhisker :
      (e.toFun.comp (e.symm.toFun.comp e.toFun)).Homotopy e.toFun :=
    ContinuousMap.Homotopy.comp e.right_inv.some (ContinuousMap.Homotopy.refl e.toFun)
  let leftWhisker :
      (e.toFun.comp (e.symm.toFun.comp e.toFun)).Homotopy e.toFun :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) e.left_inv.some
  constructor
  · -- At time `0`, both whiskered homotopies start at the common map `e ∘ e.symm ∘ e`.
    change e.right_inv.some (0, e.toFun x) = e.toFun (e.left_inv.some (0, x))
    rw [e.right_inv.some.apply_zero, e.left_inv.some.apply_zero]
    rfl
  · -- At time `1`, both whiskered homotopies end at the common map `e`.
    change e.right_inv.some (1, e.toFun x) = e.toFun (e.left_inv.some (1, x))
    rw [e.right_inv.some.apply_one, e.left_inv.some.apply_one]
    rfl

/-- Helper for Proposition 7.5.3: every time-slice of the whiskered over-homotopy `K` is still a
map over the base map `p`. -/
private theorem projectedOverHomotopyStage_comp_eq
    {p : C(D, B)} {q : C(E, B)}
    (f : SpaceOver.mk p ⟶ SpaceOver.mk q)
    (e : D ≃ₕ E) (he : e.toFun = f.left.hom)
    {g : SpaceOver.mk q ⟶ SpaceOver.mk p}
    (K : OverHomotopy (g ≫ f) (𝟙 (SpaceOver.mk q))) :
    ∀ t : I, q.comp ((K.toHomotopy.curry t).comp e.toFun) = p := by
  intro t
  have hcomp : q.comp e.toFun = p := homotopyEquivToFun_comp_eq f e he
  have hKt : q.comp (K.toHomotopy.curry t) = q := by
    -- Each `K`-slice is already a map over `q`.
    simpa using congrArg TopCat.Hom.hom (OverHomotopy.w K t)
  -- Postcomposing the stagewise over-map equation with `e` keeps the same base map.
  calc
    q.comp ((K.toHomotopy.curry t).comp e.toFun)
        = (q.comp (K.toHomotopy.curry t)).comp e.toFun := rfl
    _ = q.comp e.toFun := by
      ext x
      simpa using ContinuousMap.congr_fun hKt (e.toFun x)
    _ = p := hcomp

/-- Helper for Proposition 7.5.3: the corrected inverse homotopy `hg` together with the fixed
right-branch witness `K` rebuilds an ordinary right-inverse homotopy for `e`. -/
private theorem correctedRightInverseHomotopic
    {p : C(D, B)} {q : C(E, B)}
    (f : SpaceOver.mk p ⟶ SpaceOver.mk q)
    (e : D ≃ₕ E) (he : e.toFun = f.left.hom)
    {g : SpaceOver.mk q ⟶ SpaceOver.mk p}
    (hg : e.symm.toFun.Homotopy g.left.hom)
    (K : OverHomotopy (g ≫ f) (𝟙 (SpaceOver.mk q))) :
    (e.toFun.comp e.symm.toFun).Homotopic (ContinuousMap.id E) := by
  let mid : C(E, E) := e.toFun.comp g.left.hom
  -- First replace `e.symm` by the corrected inverse `g`, then use the over-homotopy witness.
  refine ContinuousMap.Homotopic.trans (g := mid) ?_ ?_
  · simpa [mid, he] using
      (ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl e.toFun) ⟨hg⟩)
  · simpa [mid, he] using
      (show (g ≫ f).left.hom.Homotopic (ContinuousMap.id E) from ⟨K.toHomotopy⟩)

/-- Helper for Proposition 7.5.3: the projected right and left whiskers already agree on the
boundary `t = 0, 1`. -/
private theorem projectedWhiskers_eq_boundary
    {p : C(D, B)} {q : C(E, B)}
    (f : SpaceOver.mk p ⟶ SpaceOver.mk q)
    (e : D ≃ₕ E) (he : e.toFun = f.left.hom)
    (hInverseOnBase : (p.comp e.symm.toFun).Homotopy q)
    (hRightInv : q.comp e.right_inv.some.toContinuousMap = hInverseOnBase.toContinuousMap)
    (x : D) :
    let hcomp : q.comp e.toFun = p := homotopyEquivToFun_comp_eq f e he
    let hLeftInverseOnBase : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
      (ContinuousMap.Homotopy.comp hInverseOnBase (ContinuousMap.Homotopy.refl e.toFun)).cast
        rfl hcomp
    let leftInverseProjected : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
      ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl p) e.left_inv.some
    hLeftInverseOnBase (0, x) = leftInverseProjected (0, x) ∧
      hLeftInverseOnBase (1, x) = leftInverseProjected (1, x) := by
  let hcomp : q.comp e.toFun = p := homotopyEquivToFun_comp_eq f e he
  let hLeftInverseOnBase : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
    (ContinuousMap.Homotopy.comp hInverseOnBase (ContinuousMap.Homotopy.refl e.toFun)).cast
      rfl hcomp
  let leftInverseProjected : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl p) e.left_inv.some
  have hProjectedRight :
      q.comp (ContinuousMap.Homotopy.comp e.right_inv.some
          (ContinuousMap.Homotopy.refl e.toFun)).toContinuousMap =
        hLeftInverseOnBase.toContinuousMap := by
    -- The right whisker projects to the normalized left-base homotopy.
    simpa [hcomp, hLeftInverseOnBase] using
      projectedRightWhisker_eq_leftInverseOnBase f e he hInverseOnBase hRightInv
  have hProjectedLeft :
      q.comp (ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun)
          e.left_inv.some).toContinuousMap =
        leftInverseProjected.toContinuousMap := by
    -- The left whisker projects to the downstream left-base homotopy.
    simpa [hcomp, leftInverseProjected] using
      projectedLeftWhisker_eq_leftInverseProjected f e he
  obtain ⟨hZero, hOne⟩ := whiskeredInverseHomotopies_eq_boundary e x
  constructor
  · -- At `t = 0`, both projected whiskers come from the common source endpoint.
    calc
      hLeftInverseOnBase (0, x)
          = q ((ContinuousMap.Homotopy.comp e.right_inv.some
              (ContinuousMap.Homotopy.refl e.toFun)) (0, x)) := by
              symm
              simpa using ContinuousMap.congr_fun hProjectedRight (0, x)
      _ = q ((ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun)
              e.left_inv.some) (0, x)) := by
              exact congrArg q hZero
      _ = leftInverseProjected (0, x) := by
            simpa using ContinuousMap.congr_fun hProjectedLeft (0, x)
  · -- At `t = 1`, both projected whiskers come from the common target endpoint.
    calc
      hLeftInverseOnBase (1, x)
          = q ((ContinuousMap.Homotopy.comp e.right_inv.some
              (ContinuousMap.Homotopy.refl e.toFun)) (1, x)) := by
              symm
              simpa using ContinuousMap.congr_fun hProjectedRight (1, x)
      _ = q ((ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun)
              e.left_inv.some) (1, x)) := by
              exact congrArg q hOne
      _ = leftInverseProjected (1, x) := by
            simpa using ContinuousMap.congr_fun hProjectedLeft (1, x)

/-- Helper for Proposition 7.5.3: concatenating the corrected inverse branch with the over-homotopy
`K`, then whiskering by `e`, projects to the normalized homotopy
`hLeftInverseOnBase.trans (ContinuousMap.Homotopy.refl p)`. -/
private theorem projectedCorrectedRightWhisker_eq_leftBaseTransRefl
    {p : C(D, B)} {q : C(E, B)}
    (f : SpaceOver.mk p ⟶ SpaceOver.mk q)
    (e : D ≃ₕ E) (he : e.toFun = f.left.hom)
    {g : SpaceOver.mk q ⟶ SpaceOver.mk p}
    (hg : e.symm.toFun.Homotopy g.left.hom)
    (K : OverHomotopy (g ≫ f) (𝟙 (SpaceOver.mk q)))
    (hInverseOnBase : (p.comp e.symm.toFun).Homotopy q)
    (hLift : p.comp hg.toContinuousMap = hInverseOnBase.toContinuousMap) :
    let hcomp : q.comp e.toFun = p := homotopyEquivToFun_comp_eq f e he
    let hLeftInverseOnBase : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
      (ContinuousMap.Homotopy.comp hInverseOnBase (ContinuousMap.Homotopy.refl e.toFun)).cast
        rfl hcomp
    let FgfRaw : (e.toFun.comp e.symm.toFun).Homotopy (e.toFun.comp g.left.hom) :=
      ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hg
    let Fgf : (e.toFun.comp e.symm.toFun).Homotopy (g ≫ f).left.hom :=
      FgfRaw.cast rfl (by
        ext y
        rw [he]
        rfl)
    q.comp ((Fgf.trans K.toHomotopy).comp (ContinuousMap.Homotopy.refl e.toFun)).toContinuousMap =
      (hLeftInverseOnBase.trans (ContinuousMap.Homotopy.refl p)).toContinuousMap := by
  let hcomp : q.comp e.toFun = p := homotopyEquivToFun_comp_eq f e he
  let hLeftInverseOnBase : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
    (ContinuousMap.Homotopy.comp hInverseOnBase (ContinuousMap.Homotopy.refl e.toFun)).cast
      rfl hcomp
  let FgfRaw : (e.toFun.comp e.symm.toFun).Homotopy (e.toFun.comp g.left.hom) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hg
  let Fgf : (e.toFun.comp e.symm.toFun).Homotopy (g ≫ f).left.hom :=
    FgfRaw.cast rfl (by
      ext y
      rw [he]
      rfl)
  have hProjectedFgf :
      q.comp (Fgf.comp (ContinuousMap.Homotopy.refl e.toFun)).toContinuousMap =
        hLeftInverseOnBase.toContinuousMap := by
    -- The corrected inverse branch projects to the chosen left-side base homotopy.
    ext tx
    have hcompPoint :
        q (e.toFun (hg (tx.1, e.toFun tx.2))) = p (hg (tx.1, e.toFun tx.2)) := by
      simpa using congrArg (fun m : C(D, B) => m (hg (tx.1, e.toFun tx.2))) hcomp
    calc
      q ((Fgf.comp (ContinuousMap.Homotopy.refl e.toFun)) tx)
          = q (e.toFun (hg (tx.1, e.toFun tx.2))) := by
              rfl
      _ = p (hg (tx.1, e.toFun tx.2)) := hcompPoint
      _ = hInverseOnBase (tx.1, e.toFun tx.2) := by
            simpa using ContinuousMap.congr_fun hLift (tx.1, e.toFun tx.2)
      _ = hLeftInverseOnBase tx := by
            rfl
  have hKstage :
      ∀ t : I, q.comp ((K.toHomotopy.curry t).comp e.toFun) = p := by
    -- Each stage of the fixed over-homotopy stays over `p` after whiskering by `e`.
    exact projectedOverHomotopyStage_comp_eq f e he K
  -- Compare the projected concatenation pointwise with the normalized homotopy followed by the
  -- constant branch at `p`.
  ext tx
  change q ((Fgf.trans K.toHomotopy) (tx.1, e.toFun tx.2)) =
    (hLeftInverseOnBase.trans (ContinuousMap.Homotopy.refl p)) tx
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs with ht
  · simpa using
      ContinuousMap.congr_fun hProjectedFgf
        (⟨2 * tx.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨tx.1.2.1, ht⟩⟩, tx.2)
  · simpa using
      ContinuousMap.congr_fun
        (hKstage
          ⟨2 * tx.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 ht).le, tx.1.2.2⟩⟩) tx.2

/-- Helper for Proposition 7.5.3: rewriting `e.toFun` as the underlying map of `f` identifies the
raw corrected left composite `g ∘ e` with `(f ≫ g).left.hom`. -/
private theorem leftCompositeUnderlying_eq
    {p : C(D, B)} {q : C(E, B)}
    (f : SpaceOver.mk p ⟶ SpaceOver.mk q)
    (e : D ≃ₕ E) (he : e.toFun = f.left.hom)
    {g : SpaceOver.mk q ⟶ SpaceOver.mk p}
    : g.left.hom.comp e.toFun = (f ≫ g).left.hom := by
  -- Expand the composite once and rewrite the forward map of `e` through the map over `B`.
  ext x
  rw [he]
  rfl

/-- Helper for Proposition 7.5.3: the corrected inverse branch `hg` still gives an ordinary left
homotopy from `g ∘ e` to the identity on `D`. -/
private noncomputable def correctedLeftInverseHomotopy
    {p : C(D, B)} {q : C(E, B)}
    (f : SpaceOver.mk p ⟶ SpaceOver.mk q)
    (e : D ≃ₕ E) (he : e.toFun = f.left.hom)
    {g : SpaceOver.mk q ⟶ SpaceOver.mk p}
    (hg : e.symm.toFun.Homotopy g.left.hom) :
    (f ≫ g).left.hom.Homotopy (ContinuousMap.id D) :=
  let FfgRaw : (e.symm.toFun.comp e.toFun).Homotopy (g.left.hom.comp e.toFun) :=
    ContinuousMap.Homotopy.comp hg (ContinuousMap.Homotopy.refl e.toFun)
  let Ffg : (e.symm.toFun.comp e.toFun).Homotopy (f ≫ g).left.hom :=
    FfgRaw.cast rfl (leftCompositeUnderlying_eq f e he)
  Ffg.symm.trans e.left_inv.some

/-- Helper for Proposition 7.5.3: the projected left whisker is relatively homotopic to the
normalized corrected right branch in the exact `p`-world needed for cancellation. -/
private theorem projectedLeftWhiskerComparison
    {p : C(D, B)} {q : C(E, B)}
    (f : SpaceOver.mk p ⟶ SpaceOver.mk q)
    (e : D ≃ₕ E) (he : e.toFun = f.left.hom)
    {g : SpaceOver.mk q ⟶ SpaceOver.mk p}
    (hg : e.symm.toFun.Homotopy g.left.hom)
    (K : OverHomotopy (g ≫ f) (𝟙 (SpaceOver.mk q)))
    (hInverseOnBase : (p.comp e.symm.toFun).Homotopy q)
    (hLift : p.comp hg.toContinuousMap = hInverseOnBase.toContinuousMap)
    (hRightInv : q.comp e.right_inv.some.toContinuousMap = hInverseOnBase.toContinuousMap) :
    let hcomp : q.comp e.toFun = p := homotopyEquivToFun_comp_eq f e he
    let hLeftInverseOnBase : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
      (ContinuousMap.Homotopy.comp hInverseOnBase (ContinuousMap.Homotopy.refl e.toFun)).cast
        rfl hcomp
    let leftInverseProjected : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
      ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl p) e.left_inv.some
    leftInverseProjected.toContinuousMap.HomotopicRel
      ((hLeftInverseOnBase.trans (ContinuousMap.Homotopy.refl p)).toContinuousMap)
      (({0, 1} : Set I) ×ˢ (Set.univ : Set D)) := by
  let hcomp : q.comp e.toFun = p := homotopyEquivToFun_comp_eq f e he
  let hLeftInverseOnBase : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
    (ContinuousMap.Homotopy.comp hInverseOnBase (ContinuousMap.Homotopy.refl e.toFun)).cast
      rfl hcomp
  let leftInverseProjected : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl p) e.left_inv.some
  let FgfRaw : (e.toFun.comp e.symm.toFun).Homotopy (e.toFun.comp g.left.hom) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hg
  let Fgf : (e.toFun.comp e.symm.toFun).Homotopy (g ≫ f).left.hom :=
    FgfRaw.cast rfl (by
      ext y
      rw [he]
      rfl)
  let correctedRightWhisker :
      ((e.toFun.comp e.symm.toFun).comp e.toFun).Homotopy e.toFun :=
    ((Fgf.trans K.toHomotopy).comp (ContinuousMap.Homotopy.refl e.toFun)).cast rfl (by
      ext y
      rfl)
  -- TODO: construct the direct relative comparison by building the `B`-valued square whose
  -- `s = 0` face is `leftInverseProjected`, whose `s = 1` face is
  -- `q.comp correctedRightWhisker.toContinuousMap`, and whose vertical faces are fixed using
  -- `projectedWhiskers_eq_boundary f e he hInverseOnBase hRightInv`; then rewrite the target
  -- once with `projectedCorrectedRightWhisker_eq_leftBaseTransRefl`.
  sorry

/-- Helper for Proposition 7.5.3: once the direct left-whisker comparison is available, it can be
read back as the explicit boundary-fixed square used for debugging the normalization. -/
private theorem projectedLeftWhiskerComparisonSquare
    {p : C(D, B)} {q : C(E, B)}
    (f : SpaceOver.mk p ⟶ SpaceOver.mk q)
    (e : D ≃ₕ E) (he : e.toFun = f.left.hom)
    {g : SpaceOver.mk q ⟶ SpaceOver.mk p}
    (hg : e.symm.toFun.Homotopy g.left.hom)
    (K : OverHomotopy (g ≫ f) (𝟙 (SpaceOver.mk q)))
    (hInverseOnBase : (p.comp e.symm.toFun).Homotopy q)
    (hLift : p.comp hg.toContinuousMap = hInverseOnBase.toContinuousMap)
    (hRightInv : q.comp e.right_inv.some.toContinuousMap = hInverseOnBase.toContinuousMap) :
    let hcomp : q.comp e.toFun = p := homotopyEquivToFun_comp_eq f e he
    let hLeftInverseOnBase : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
      (ContinuousMap.Homotopy.comp hInverseOnBase (ContinuousMap.Homotopy.refl e.toFun)).cast
        rfl hcomp
    let leftInverseProjected : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
      ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl p) e.left_inv.some
    let FgfRaw : (e.toFun.comp e.symm.toFun).Homotopy (e.toFun.comp g.left.hom) :=
      ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hg
    let Fgf : (e.toFun.comp e.symm.toFun).Homotopy (g ≫ f).left.hom :=
      FgfRaw.cast rfl (by
        ext y
        rw [he]
        rfl)
    let correctedRightWhisker :
        ((e.toFun.comp e.symm.toFun).comp e.toFun).Homotopy e.toFun :=
      ((Fgf.trans K.toHomotopy).comp (ContinuousMap.Homotopy.refl e.toFun)).cast rfl (by
        ext y
        rfl)
    ∃ square : C((I × D) × I, B),
      (∀ tx : I × D, square (tx, 0) = leftInverseProjected tx) ∧
      (∀ tx : I × D,
        square (tx, 1) = (q.comp correctedRightWhisker.toContinuousMap) tx) ∧
      (∀ s : I, ∀ x : D, square ((0, x), s) = leftInverseProjected (0, x)) ∧
      (∀ s : I, ∀ x : D, square ((1, x), s) = leftInverseProjected (1, x)) := by
  let hcomp : q.comp e.toFun = p := homotopyEquivToFun_comp_eq f e he
  let hLeftInverseOnBase : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
    (ContinuousMap.Homotopy.comp hInverseOnBase (ContinuousMap.Homotopy.refl e.toFun)).cast
      rfl hcomp
  let leftInverseProjected : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl p) e.left_inv.some
  let FgfRaw : (e.toFun.comp e.symm.toFun).Homotopy (e.toFun.comp g.left.hom) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) hg
  let Fgf : (e.toFun.comp e.symm.toFun).Homotopy (g ≫ f).left.hom :=
    FgfRaw.cast rfl (by
      ext y
      rw [he]
      rfl)
  let correctedRightWhisker :
      ((e.toFun.comp e.symm.toFun).comp e.toFun).Homotopy e.toFun :=
    ((Fgf.trans K.toHomotopy).comp (ContinuousMap.Homotopy.refl e.toFun)).cast rfl (by
      ext y
      rfl)
  have hCompare :
      leftInverseProjected.toContinuousMap.HomotopicRel
        ((hLeftInverseOnBase.trans (ContinuousMap.Homotopy.refl p)).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set D)) := by
    -- Route correction: the square is now just an adapter that reads back the direct comparison.
    simpa [hcomp, hLeftInverseOnBase, leftInverseProjected] using
      projectedLeftWhiskerComparison f e he hg K hInverseOnBase hLift hRightInv
  have hTarget :
      (hLeftInverseOnBase.trans (ContinuousMap.Homotopy.refl p)).toContinuousMap =
        q.comp correctedRightWhisker.toContinuousMap := by
    -- Rewrite the normalized target back to the projected corrected right branch.
    symm
    simpa [hcomp, hLeftInverseOnBase, FgfRaw, Fgf, correctedRightWhisker] using
      projectedCorrectedRightWhisker_eq_leftBaseTransRefl f e he hg K hInverseOnBase hLift
  rcases hCompare with ⟨hCompare⟩
  exact boundaryFixedSquareOfHomotopyRel ⟨hCompare.cast rfl hTarget⟩

/-- Helper for Proposition 7.5.3: the remaining left-side frontier is to show that the projection
of the coherent ordinary left homotopy contracts relative to the time-boundary. -/
private theorem projectedCorrectedLeftInverse_homotopicRelRefl
    {p : C(D, B)} {q : C(E, B)}
    (f : SpaceOver.mk p ⟶ SpaceOver.mk q)
    (e : D ≃ₕ E) (he : e.toFun = f.left.hom)
    {g : SpaceOver.mk q ⟶ SpaceOver.mk p}
    (hg : e.symm.toFun.Homotopy g.left.hom)
    (K : OverHomotopy (g ≫ f) (𝟙 (SpaceOver.mk q)))
    (hInverseOnBase : (p.comp e.symm.toFun).Homotopy q)
    (hLift : p.comp hg.toContinuousMap = hInverseOnBase.toContinuousMap)
    (hRightInv : q.comp e.right_inv.some.toContinuousMap = hInverseOnBase.toContinuousMap) :
    (p.comp (correctedLeftInverseHomotopy f e he hg).toContinuousMap).HomotopicRel
      ((ContinuousMap.Homotopy.refl p).toContinuousMap)
      (({0, 1} : Set I) ×ˢ (Set.univ : Set D)) := by
  -- Route correction: the old endpoint-rectification lemma asked for a comparison with the
  -- arbitrary witness `e.left_inv.some`. The actual frontier is the branch-local comparison
  -- between `leftInverseProjected` and the normalized corrected right branch.
  let hcomp : q.comp e.toFun = p := homotopyEquivToFun_comp_eq f e he
  let hLeftInverseOnBase : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
    (ContinuousMap.Homotopy.comp hInverseOnBase (ContinuousMap.Homotopy.refl e.toFun)).cast
      rfl hcomp
  let leftInverseProjected : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl p) e.left_inv.some
  have hNormalized :
      p.comp (correctedLeftInverseHomotopy f e he hg).toContinuousMap =
        (hLeftInverseOnBase.symm.trans leftInverseProjected).toContinuousMap := by
    -- First normalize the projected corrected left homotopy into the standard two-factor loop.
    simpa [correctedLeftInverseHomotopy, hcomp, hLeftInverseOnBase, leftInverseProjected] using
      projectedLeftComposite_eq_normalized f e he hg hInverseOnBase hLift
  rw [hNormalized]
  have hCompare :
      leftInverseProjected.toContinuousMap.HomotopicRel
        ((hLeftInverseOnBase.trans (ContinuousMap.Homotopy.refl p)).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set D)) := by
    -- The only non-cancellation input is the branch-local comparison proved above.
    simpa [hcomp, hLeftInverseOnBase, leftInverseProjected] using
      projectedLeftWhiskerComparison f e he hg K hInverseOnBase hLift hRightInv
  refine ContinuousMap.HomotopicRel.trans
    (symmTransCongrLeft_homotopyRel hLeftInverseOnBase hCompare) ?_
  -- Once the right factor is normalized, the generic self-cancellation lemma finishes.
  simpa using
    symmTransTransCancel_homotopyRel hLeftInverseOnBase (ContinuousMap.Homotopy.refl p)

/-- Helper for Proposition 7.5.3: if both endpoint homotopies project to the same base homotopy,
their concatenation projects to the standard self-canceling loop. -/
private theorem controlledLeftEndpointProjected_eq_selfCanceling
    {p : C(D, B)} {q : C(E, B)}
    (f : SpaceOver.mk p ⟶ SpaceOver.mk q)
    (e : D ≃ₕ E) (he : e.toFun = f.left.hom)
    (hInverseOnBase : (p.comp e.symm.toFun).Homotopy q)
    {u : SpaceOver.mk p ⟶ SpaceOver.mk p}
    (R : (e.symm.toFun.comp e.toFun).Homotopy u.left.hom)
    (hR :
      let hcomp : q.comp e.toFun = p := homotopyEquivToFun_comp_eq f e he
      let hLeftInverseOnBase : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
        (ContinuousMap.Homotopy.comp hInverseOnBase (ContinuousMap.Homotopy.refl e.toFun)).cast
          rfl hcomp
      p.comp R.toContinuousMap = hLeftInverseOnBase.toContinuousMap)
    (L : (e.symm.toFun.comp e.toFun).Homotopy (ContinuousMap.id D))
    (hL :
      let hcomp : q.comp e.toFun = p := homotopyEquivToFun_comp_eq f e he
      let hLeftInverseOnBase : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
        (ContinuousMap.Homotopy.comp hInverseOnBase (ContinuousMap.Homotopy.refl e.toFun)).cast
          rfl hcomp
      p.comp L.toContinuousMap = hLeftInverseOnBase.toContinuousMap) :
    let hcomp : q.comp e.toFun = p := homotopyEquivToFun_comp_eq f e he
    let hLeftInverseOnBase : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
      (ContinuousMap.Homotopy.comp hInverseOnBase (ContinuousMap.Homotopy.refl e.toFun)).cast
        rfl hcomp
    p.comp (R.symm.trans L).toContinuousMap =
      (hLeftInverseOnBase.symm.trans hLeftInverseOnBase).toContinuousMap := by
  let hcomp : q.comp e.toFun = p := homotopyEquivToFun_comp_eq f e he
  let hLeftInverseOnBase : (p.comp (e.symm.toFun.comp e.toFun)).Homotopy p :=
    (ContinuousMap.Homotopy.comp hInverseOnBase (ContinuousMap.Homotopy.refl e.toFun)).cast
      rfl hcomp
  have hR' : p.comp R.toContinuousMap = hLeftInverseOnBase.toContinuousMap := by
    simpa [hcomp, hLeftInverseOnBase] using hR
  have hL' : p.comp L.toContinuousMap = hLeftInverseOnBase.toContinuousMap := by
    simpa [hcomp, hLeftInverseOnBase] using hL
  -- Normalize the concatenated endpoint homotopy by comparing each branch with the shared base
  -- homotopy `hLeftInverseOnBase`.
  ext tx
  change p ((R.symm.trans L) tx) = (hLeftInverseOnBase.symm.trans hLeftInverseOnBase) tx
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs with ht
  · simpa [ContinuousMap.Homotopy.symm] using
      ContinuousMap.congr_fun hR'
        (σ ⟨2 * tx.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨tx.1.2.1, ht⟩⟩, tx.2)
  · simpa using
      ContinuousMap.congr_fun hL'
        (⟨2 * tx.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, tx.1.2.2⟩⟩,
          tx.2)

/-- Helper for Proposition 7.5.3: the corrected inverse `g` gives the left composite
`f ≫ g` a homotopy over `B` to the identity on `D`. -/
private theorem leftComposite_homotopicOver
    {p : C(D, B)} {q : C(E, B)}
    (hp : IsFibration.{u, u, u} p)
    (hq : IsFibration.{u, u, u} q)
    (f : SpaceOver.mk p ⟶ SpaceOver.mk q)
    (e : D ≃ₕ E) (he : e.toFun = f.left.hom)
    {g : SpaceOver.mk q ⟶ SpaceOver.mk p}
    (hg : e.symm.toFun.Homotopy g.left.hom)
    (hInverseOnBase : (p.comp e.symm.toFun).Homotopy q)
    (hLift : p.comp hg.toContinuousMap = hInverseOnBase.toContinuousMap)
    (hRightInv : q.comp e.right_inv.some.toContinuousMap = hInverseOnBase.toContinuousMap) :
    HomotopicOver (f ≫ g) (𝟙 (SpaceOver.mk p)) := by
  rcases rightComposite_homotopicOver hq f e he hg hInverseOnBase hLift hRightInv with ⟨K⟩
  let H : (f ≫ g).left.hom.Homotopy (ContinuousMap.id D) :=
    correctedLeftInverseHomotopy f e he hg
  have hProjectedRel :
      (p.comp H.toContinuousMap).HomotopicRel
        ((ContinuousMap.Homotopy.refl p).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set D)) := by
    -- Route correction: prove the projection of the coherent left witness contracts directly,
    -- instead of inserting a second controlled endpoint and comparing arbitrary witnesses.
    simpa [H] using
      projectedCorrectedLeftInverse_homotopicRelRefl f e he hg K hInverseOnBase hLift hRightInv
  exact homotopicOver_of_projectedHomotopyRelConst hp H hProjectedRel

/-- Proposition 7.5.3. If `p : D → B` and `q : E → B` are fibrations and `f : D → E` is a map
over `B` that is an ordinary homotopy equivalence, then `f` is a fiber homotopy equivalence. -/
theorem isFiberHomotopyEquivalence_of_homotopyEquiv
    {p : C(D, B)} {q : C(E, B)}
    (hp : IsFibration.{u, u, u} p) (hq : IsFibration.{u, u, u} q)
    (f : SpaceOver.mk p ⟶ SpaceOver.mk q)
    (e : D ≃ₕ E) (he : e.toFun = f.left.hom) :
    IsFiberHomotopyEquivalence f := by
  -- Rewrite the over-category square into the continuous-map shape required by CHP.
  have hcomp : q.comp e.toFun = p := homotopyEquivToFun_comp_eq f e he
  let hInverseOnBase : (p.comp e.symm.toFun).Homotopy q := by
    -- Compose the ordinary right-inverse homotopy with `q` and rewrite its left endpoint.
    refine (ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl q) e.right_inv.some).cast ?_ ?_
    · ext x
      change q (e.toFun (e.symm.toFun x)) = p (e.symm.toFun x)
      simpa using congrArg (fun m : C(D, B) => m (e.symm.toFun x)) hcomp
    · rfl
  -- Correct the ordinary inverse into an actual over-map using the covering homotopy property.
  obtain ⟨g, hg, hLift⟩ := existsSpaceOverHom_homotopy_of_isFibration hp hInverseOnBase
  have hRightInv : q.comp e.right_inv.some.toContinuousMap = hInverseOnBase.toContinuousMap := by
    -- Unfold the chosen base homotopy: it was defined by projecting `e.right_inv.some` through `q`.
    ext tx
    change q (e.right_inv.some tx) = hInverseOnBase tx
    simp [hInverseOnBase]
  have hgfOrd : (g ≫ f).left.hom.Homotopic (ContinuousMap.id E) := by
    -- Compare the corrected inverse with `e.symm`, then close with the ordinary right-inverse
    -- homotopy of the homotopy equivalence `e`.
    simpa [he] using
      ContinuousMap.Homotopic.trans
        (ContinuousMap.Homotopic.symm
          (ContinuousMap.Homotopic.comp
            (ContinuousMap.Homotopic.refl e.toFun)
            ⟨hg⟩))
        e.right_inv
  have hfgOrd : (f ≫ g).left.hom.Homotopic (ContinuousMap.id D) := by
    -- The other composite is handled analogously using the ordinary left-inverse homotopy.
    simpa [he] using
      ContinuousMap.Homotopic.trans
        (ContinuousMap.Homotopic.symm
          (ContinuousMap.Homotopic.comp
            ⟨hg⟩
            (ContinuousMap.Homotopic.refl e.toFun)))
        e.left_inv
  refine (isFiberHomotopyEquivalence_iff).2 ?_
  refine ⟨g, ?_, ?_⟩
  · -- Upgrade the right ordinary homotopy to a homotopy over `B` via the lift comparison helper.
    exact rightComposite_homotopicOver hq f e he hg hInverseOnBase hLift hRightInv
  · -- Upgrade the left ordinary homotopy by the analogous comparison-of-lifts argument over `p`.
    exact leftComposite_homotopicOver hp hq f e he hg hInverseOnBase hLift hRightInv

/-- Existence-only restatement of Proposition 7.5.3 for callers that only know that the
underlying map of `f` is an ordinary homotopy equivalence. -/
theorem isFiberHomotopyEquivalence_of_exists_homotopyEquiv
    {p : C(D, B)} {q : C(E, B)}
    (hp : IsFibration.{u, u, u} p) (hq : IsFibration.{u, u, u} q)
    (f : SpaceOver.mk p ⟶ SpaceOver.mk q)
    (hf : ∃ e : D ≃ₕ E, e.toFun = f.left.hom) :
    IsFiberHomotopyEquivalence f := by
  rcases hf with ⟨e, he⟩
  exact isFiberHomotopyEquivalence_of_homotopyEquiv hp hq f e he
