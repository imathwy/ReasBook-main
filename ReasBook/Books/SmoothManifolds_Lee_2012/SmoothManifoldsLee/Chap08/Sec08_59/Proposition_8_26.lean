import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_59.Definition_8_59_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open VectorField

universe uH uM

noncomputable section

section

-- Domain sampling pass:
-- * primary domain: smooth vector fields on manifolds, expressed in local coordinates;
-- * source-facing layer: the coordinate formula for Lee's Lie bracket in an arbitrary smooth
--   local chart from the maximal atlas;
-- * core/canonical bracket owner: `VectorField.mlieBracket`, exposed via `⁅X, Y⁆`;
-- * canonical chart-side vector-field owner: `VectorField.mpullbackWithin`;
-- * chart-side coordinate bracket owner: `lieBracketWithin`.
-- Primitive data is only the vector fields `X`, `Y` and a chosen smooth local chart `e`. The
-- chart-side vector fields and scalar coordinates are derived from `mpullbackWithin` applied to
-- `e.extend I`, so the proposition stays source-facing while using the canonical chart-pullback
-- owner directly.

variable {n : ℕ}
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

omit [ChartedSpace H M] [IsManifold I ∞ M] in
/-- Helper for Proposition 8.26: the natural target of `e.extend I` inherits unique
differentiability from `Set.range I`. -/
private lemma uniqueMDiffOn_extendTarget
    (e : OpenPartialHomeomorph M H) :
    UniqueMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (e.extend I).target := by
  let u : Set (EuclideanSpace ℝ (Fin n)) := I.symm ⁻¹' e.target
  have hu : IsOpen u := e.open_target.preimage I.continuous_symm
  simpa [u, OpenPartialHomeomorph.extend_target, Set.inter_assoc, Set.inter_left_comm,
    Set.inter_comm] using
    (ModelWithCorners.uniqueMDiffOn I).inter hu

omit [ChartedSpace H M] [IsManifold I ∞ M] in
/-- Helper for Proposition 8.26: every point of the chart target lies in the closure of the
interior of that target. -/
private lemma extendTarget_subset_closure_interior
    (e : OpenPartialHomeomorph M H) :
    (e.extend I).target ⊆ closure (interior (e.extend I).target) := by
  intro y hy
  rw [mem_closure_iff_nhds]
  intro t ht
  have htarget_union : (e.extend I).target ∪ (Set.range I)ᶜ ∈ nhds y := by
    rw [← nhdsWithin_univ, ← Set.union_compl_self (Set.range I), nhdsWithin_union]
    refine Filter.union_mem_sup ?_ self_mem_nhdsWithin
    have hy_source : (e.extend I).symm y ∈ e.source := by
      simpa [OpenPartialHomeomorph.extend_source] using (e.extend I).map_target hy
    rw [← (e.extend I).right_inv hy]
    simpa [OpenPartialHomeomorph.extend_source] using
      e.extend_target_mem_nhdsWithin (I := I) hy_source
  have hy_closure_range : y ∈ closure (interior (Set.range I)) := by
    exact I.range_subset_closure_interior ((e.extend_target_subset_range (I := I)) hy)
  have htarget_nhds : t ∩ ((e.extend I).target ∪ (Set.range I)ᶜ) ∈ nhds y :=
    Filter.inter_mem ht htarget_union
  obtain ⟨z, ⟨tz, hz_target_or_compl⟩, hz_range⟩ :
      (t ∩ ((e.extend I).target ∪ (Set.range I)ᶜ) ∩ interior (Set.range I)).Nonempty :=
    mem_closure_iff_nhds.1 hy_closure_range _ htarget_nhds
  refine ⟨z, ⟨tz, ?_⟩⟩
  have hz_target : z ∈ (e.extend I).target := by
    simpa [interior_subset hz_range] using hz_target_or_compl
  have hz_source : (e.extend I).symm z ∈ e.source := by
    simpa using (e.extend I).map_target hz_target
  have htarget_eq :
      (e.extend I).target =ᶠ[nhds z] Set.range I := by
    rw [← (e.extend I).right_inv hz_target]
    exact e.extend_target_eventuallyEq (I := I) hz_source
  exact htarget_eq.symm.mem_interior hz_range

omit [IsManifold I ∞ M] in
/-- Helper for Proposition 8.26: the chart inverse has invertible within-derivative on the chart
target because `e.extend I` and its inverse form a smooth local diffeomorphism. -/
private lemma extendSymm_mfderivWithin_isInvertible
    (e : OpenPartialHomeomorph M H)
    (he : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (e.extend I) e.source)
    (he_symm : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ (e.extend I).symm
      (e.extend I).target)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ (e.extend I).target) :
    (mfderiv[(e.extend I).target] (e.extend I).symm y).IsInvertible := by
  let x : M := (e.extend I).symm y
  have hx_source : x ∈ e.source := by
    simpa [x, OpenPartialHomeomorph.extend_source] using (e.extend I).map_target hy
  have hsource_unique : UniqueMDiffWithinAt I e.source x :=
    e.open_source.uniqueMDiffWithinAt hx_source
  have htarget_unique :
      UniqueMDiffWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (e.extend I).target y :=
    uniqueMDiffOn_extendTarget (I := I) e y hy
  have hchart :
      MDifferentiableWithinAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (e.extend I) e.source x := by
    exact (he x hx_source).mdifferentiableWithinAt (by simp)
  have hsymm :
      MDifferentiableWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I (e.extend I).symm
        (e.extend I).target y := by
    exact (he_symm y hy).mdifferentiableWithinAt (by simp)
  have hleft :
      (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I (e.extend I).symm (e.extend I).target y).comp
        (mfderivWithin I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (e.extend I) e.source x) =
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
    rw [← mfderivWithin_comp_of_eq hsymm hchart]
    · rw [← mfderivWithin_id hsource_unique]
      apply Filter.EventuallyEq.mfderivWithin_eq_of_mem
      · refine Filter.eventuallyEq_of_mem self_mem_nhdsWithin ?_
        intro z hz
        simpa [Function.comp] using e.extend_left_inv (I := I) hz
      · exact hx_source
    · intro z hz
      exact (e.extend I).map_source <| by simpa [OpenPartialHomeomorph.extend_source] using hz
    · exact hsource_unique
    · simpa [x] using (e.extend I).right_inv hy
  have hright :
      (mfderivWithin I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (e.extend I) e.source x).comp
        (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I (e.extend I).symm (e.extend I).target y) =
      ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) y) := by
    rw [← mfderivWithin_comp_of_eq hchart hsymm]
    · rw [← mfderivWithin_id htarget_unique]
      apply Filter.EventuallyEq.mfderivWithin_eq_of_mem
      · refine Filter.eventuallyEq_of_mem self_mem_nhdsWithin ?_
        intro z hz
        simpa [Function.comp] using (e.extend I).right_inv hz
      · exact hy
    · intro z hz
      simpa [OpenPartialHomeomorph.extend_source] using (e.extend I).map_target hz
    · exact htarget_unique
    · rfl
  exact ContinuousLinearMap.IsInvertible.of_inverse hleft hright

/-- Helper for Proposition 8.26: pulling a smooth vector field back by the chart inverse yields a
chart-side vector field differentiable within the chart target. -/
private lemma chartPullbackDifferentiableWithin
    {V : Π x : M, TangentSpace I x}
    (hV : ContMDiff I I.tangent ∞ (T% V))
    (p : M) (e : OpenPartialHomeomorph M H) (hp : p ∈ e.source)
    (he : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (e.extend I) e.source)
    (he_symm : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ (e.extend I).symm
      (e.extend I).target) :
    DifferentiableWithinAt ℝ
      (mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I (e.extend I).symm V (e.extend I).target)
      (e.extend I).target ((e.extend I) p) := by
  have hp_source : p ∈ (e.extend I).source := by
    simpa [OpenPartialHomeomorph.extend_source] using hp
  have hp_target : (e.extend I) p ∈ (e.extend I).target := by
    simpa using (e.extend I).map_source hp_source
  have hPullback :
      ContMDiffWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)).tangent 1
        (T%
          (mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I (e.extend I).symm V
            (e.extend I).target))
        (e.extend I).target ((e.extend I) p) := by
    apply ContMDiffWithinAt.mpullbackWithin_vectorField_of_eq
      (m := (1 : ℕ∞ω)) (n := (∞ : ℕ∞ω)) (t := (Set.univ : Set M)) (y₀ := p)
    · simpa using ((hV.contMDiffAt (x := p)).of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).contMDiffWithinAt
    · simpa using he_symm ((e.extend I) p) hp_target
    · exact
        extendSymm_mfderivWithin_isInvertible
          (n := n) (I := I) e he he_symm hp_target
    · exact hp_target
    · exact uniqueMDiffOn_extendTarget (I := I) e
    · exact (by decide : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω))
    · intro y hy
      simp
    · simpa using (e.extend I).left_inv hp_source
  exact
    (contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.mp hPullback).differentiableWithinAt
      one_ne_zero

/-- Helper for Proposition 8.26: the chart pullback of the manifold Lie bracket agrees with the
Euclidean `lieBracketWithin` of the chart pullbacks. -/
private lemma pullbackBracket_eq_lieBracketWithin
    {X Y : Π x : M, TangentSpace I x}
    (hX : ContMDiff I I.tangent ∞ (T% X))
    (hY : ContMDiff I I.tangent ∞ (T% Y))
    (p : M) (e : OpenPartialHomeomorph M H) (hp : p ∈ e.source)
    (he_symm : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ (e.extend I).symm
      (e.extend I).target) :
    mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I (e.extend I).symm ⁅X, Y⁆ (e.extend I).target
      ((e.extend I) p) =
    lieBracketWithin ℝ
      (mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I (e.extend I).symm X (e.extend I).target)
      (mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I (e.extend I).symm Y (e.extend I).target)
      (e.extend I).target ((e.extend I) p) := by
  haveI : IsManifold I (minSmoothness ℝ 2) M :=
    IsManifold.of_le (m := minSmoothness ℝ 2) (n := (∞ : ℕ∞ω)) <| by
      simpa using (by decide : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  let c := e.extend I
  let x : EuclideanSpace ℝ (Fin n) := c p
  have hp_source : p ∈ c.source := by
    simpa [c, OpenPartialHomeomorph.extend_source] using hp
  have hx : x ∈ c.target := by
    simpa [x] using c.map_source hp_source
  have hs : UniqueMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c.target :=
    uniqueMDiffOn_extendTarget (I := I) e
  have hx_closure : x ∈ closure (interior c.target) :=
    extendTarget_subset_closure_interior (I := I) e hx
  have hx_symm : c.symm x = p := by
    simpa [x] using c.left_inv hp_source
  calc
    mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I c.symm ⁅X, Y⁆ c.target x =
        mlieBracketWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          (mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I c.symm X c.target)
          (mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I c.symm Y c.target)
          c.target x := by
      simpa [c, x, VectorField.bracket_eq_mlieBracket] using
        VectorField.mpullbackWithin_mlieBracketWithin
          (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (I' := I)
          (f := c.symm) (V := X) (W := Y) (x₀ := x) (s := c.target)
          (t := Set.univ)
          (by simpa [hx_symm] using hX.mdifferentiableWithinAt (s := Set.univ) (x := p) <| by simp)
          (by simpa [hx_symm] using hY.mdifferentiableWithinAt (s := Set.univ) (x := p) <| by simp)
          hs
          ((he_symm x hx))
          hx
          (by simpa using (by decide : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω)))
          (by simp)
          hx_closure
    _ =
        lieBracketWithin ℝ
          (mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I c.symm X c.target)
          (mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I c.symm Y c.target)
          c.target x := by
      rw [VectorField.mlieBracketWithin_eq_lieBracketWithin]

/-- Helper for Proposition 8.26: differentiating a chart coordinate projection within a
unique-differentiability set just evaluates the input vector at that coordinate. -/
private lemma fderivWithin_coord_apply
    {s : Set (EuclideanSpace ℝ (Fin n))} {x v : EuclideanSpace ℝ (Fin n)}
    (hs : UniqueDiffWithinAt ℝ s x) (j : Fin n) :
    fderivWithin ℝ (fun z : EuclideanSpace ℝ (Fin n) ↦ z.ofLp j) s x v = v.ofLp j := by
  rw [fderivWithin_eq_fderiv hs]
  · rw [(PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin n ↦ ℝ) x j).fderiv]
    rfl
  · simpa using
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin n ↦ ℝ) x j).differentiableAt

/-- Helper for Proposition 8.26: the `j`th coordinate of `lieBracketWithin` is the commutator of
the directional derivatives of the `j`th coordinate functions. -/
private lemma lieBracketWithin_coordinateComponent
    {s : Set (EuclideanSpace ℝ (Fin n))}
    {x : EuclideanSpace ℝ (Fin n)}
    {V W : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (j : Fin n)
    (hs : UniqueDiffOn ℝ s) (hx_closure : x ∈ closure (interior s)) (hx : x ∈ s)
    (hW : DifferentiableWithinAt ℝ W s x) (hV : DifferentiableWithinAt ℝ V s x) :
    (lieBracketWithin ℝ V W s x).ofLp j =
      fderivWithin ℝ (fun y ↦ (W y).ofLp j) s x (V x) -
      fderivWithin ℝ (fun y ↦ (V y).ofLp j) s x (W x) := by
  have hcoord :
      ContDiffWithinAt ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) ↦ y.ofLp j) s x := by
    simpa using
      (contDiffWithinAt_piLp_apply (𝕜 := ℝ) (n := (∞ : ℕ∞ω)) (i := j)
        (t := s) (y := x))
  have hWcomponent :
      fderivWithin ℝ
          (fun y ↦ fderivWithin ℝ (fun z : EuclideanSpace ℝ (Fin n) ↦ z.ofLp j) s y (W y))
          s x =
        fderivWithin ℝ (fun y ↦ (W y).ofLp j) s x := by
    apply Filter.EventuallyEq.fderivWithin_eq_of_mem _ hx
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp [fderivWithin_coord_apply (n := n) (s := s) (x := y) (j := j) (v := W y) (hs y hy)]
  have hVcomponent :
      fderivWithin ℝ
          (fun y ↦ fderivWithin ℝ (fun z : EuclideanSpace ℝ (Fin n) ↦ z.ofLp j) s y (V y))
          s x =
        fderivWithin ℝ (fun y ↦ (V y).ofLp j) s x := by
    apply Filter.EventuallyEq.fderivWithin_eq_of_mem _ hx
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp [fderivWithin_coord_apply (n := n) (s := s) (x := y) (j := j) (v := V y) (hs y hy)]
  calc
    (lieBracketWithin ℝ V W s x).ofLp j =
        fderivWithin ℝ (fun y : EuclideanSpace ℝ (Fin n) ↦ y.ofLp j) s x
          (lieBracketWithin ℝ V W s x) := by
      symm
      exact
        fderivWithin_coord_apply
          (n := n) (s := s) (x := x) (j := j) (v := lieBracketWithin ℝ V W s x) (hs x hx)
    _ =
        fderivWithin ℝ
            (fun y ↦ fderivWithin ℝ (fun z : EuclideanSpace ℝ (Fin n) ↦ z.ofLp j) s y (W y))
            s x (V x) -
          fderivWithin ℝ
            (fun y ↦ fderivWithin ℝ (fun z : EuclideanSpace ℝ (Fin n) ↦ z.ofLp j) s y (V y))
            s x (W x) := by
      simpa using
        (VectorField.fderivWithin_apply_lieBracket (𝕜 := ℝ)
          (f := fun y : EuclideanSpace ℝ (Fin n) ↦ y.ofLp j) (V := V) (W := W)
          (n := (∞ : ℕ∞ω)) hcoord
          (by simpa using (by decide : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω)))
          hs hx_closure hx hW hV)
    _ =
        fderivWithin ℝ (fun y ↦ (W y).ofLp j) s x (V x) -
          fderivWithin ℝ (fun y ↦ (V y).ofLp j) s x (W x) := by
      rw [hWcomponent, hVcomponent]

/-- Proposition 8.26 (Coordinate Formula for the Lie Bracket): for smooth vector fields `X` and
`Y`, the `j`th coordinate of `⁅X, Y⁆` in any smooth local coordinates around `p` is
`X (Y^j) - Y (X^j)`. -/
-- Semantic recall note: `lean_leansearch` confirmed the canonical manifold bracket owner
-- `VectorField.mlieBracket` and the chart-side pullback owner `VectorField.mpullbackWithin`; this
-- proposition keeps Lee's source-facing local-coordinate statement by parameterizing over a smooth
-- local chart `e`.
theorem lie_bracket_coordinate_formula
    {X Y : Π x : M, TangentSpace I x}
    (hX : ContMDiff I I.tangent ∞ (T% X))
    (hY : ContMDiff I I.tangent ∞ (T% Y))
    (p : M) (e : OpenPartialHomeomorph M H) (hp : p ∈ e.source)
    (he : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (e.extend I) e.source)
    (he_symm : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ (e.extend I).symm
      (e.extend I).target)
    (j : Fin n) :
    let c := e.extend I
    let x := c p
    let X' := mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I c.symm X c.target
    let Y' := mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I c.symm Y c.target
    let bracket' := mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I c.symm ⁅X, Y⁆ c.target
    (bracket' x).ofLp j =
      fderivWithin ℝ (fun y ↦ (Y' y).ofLp j) c.target x (X' x) -
      fderivWithin ℝ (fun y ↦ (X' y).ofLp j) c.target x (Y' x) := by
  dsimp
  let c := e.extend I
  let x : EuclideanSpace ℝ (Fin n) := c p
  let X' := mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I c.symm X c.target
  let Y' := mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I c.symm Y c.target
  let bracket' := mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I c.symm ⁅X, Y⁆ c.target
  have hp_source : p ∈ c.source := by
    simpa [c, OpenPartialHomeomorph.extend_source] using hp
  have hx : x ∈ c.target := by
    simpa [x] using c.map_source hp_source
  have hs : UniqueDiffOn ℝ c.target := (uniqueMDiffOn_extendTarget (I := I) e).uniqueDiffOn
  have hx_closure : x ∈ closure (interior c.target) := by
    simpa [x, c] using (extendTarget_subset_closure_interior (I := I) e (by simpa [x, c] using hx))
  have hXdiff :
      DifferentiableWithinAt ℝ X' c.target x := by
    -- Pull `X` back to the chart and use the chart inverse smoothness to get differentiability.
    simpa [X', c, x] using
      chartPullbackDifferentiableWithin (n := n) (I := I) hX p e hp he he_symm
  have hYdiff :
      DifferentiableWithinAt ℝ Y' c.target x := by
    -- The same pullback argument applies to `Y`.
    simpa [Y', c, x] using
      chartPullbackDifferentiableWithin (n := n) (I := I) hY p e hp he he_symm
  -- Route correction: first transport the manifold bracket into the chart-side Euclidean bracket,
  -- then apply the scalar-coordinate Lie-bracket identity there.
  calc
    (bracket' x).ofLp j = (lieBracketWithin ℝ X' Y' c.target x).ofLp j := by
      simpa [bracket', X', Y', c, x] using
        congrArg (fun v : EuclideanSpace ℝ (Fin n) ↦ v.ofLp j)
          (pullbackBracket_eq_lieBracketWithin (n := n) (I := I) hX hY p e hp he_symm)
    _ =
        fderivWithin ℝ (fun y ↦ (Y' y).ofLp j) c.target x (X' x) -
          fderivWithin ℝ (fun y ↦ (X' y).ofLp j) c.target x (Y' x) := by
      exact lieBracketWithin_coordinateComponent (n := n) j hs hx_closure hx hYdiff hXdiff

end
