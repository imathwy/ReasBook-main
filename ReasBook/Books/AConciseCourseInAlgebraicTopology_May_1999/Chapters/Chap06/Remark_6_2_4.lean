import Mathlib.Topology.Maps.Basic
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Lemma_5_1_8
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Proposition_5_1_18
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Remark_5_1_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Assumption_6_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Criterion_6_2_3

noncomputable section

universe u v

variable {A X : Type u} [TopologicalSpace A] [TopologicalSpace X]

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.Types
open scoped ContinuousMap unitInterval

-- Semantic recall via `lean_leansearch`: the relevant bundled point-set owner in mathlib is
-- `Topology.IsClosedEmbedding`, and local Chapter 6 precedent packages cofibrations under
-- `IsCofibration`.

/-- Helper for Remark 6.2.4: the time-`1` slice of the cylinder inclusion. -/
private def mappingCylinderEndpoint (i : C(A, X)) : C(A, i.mappingCylinder) :=
  (ContinuousMap.mappingCylinderCylinderInclusion i).comp
    ((ContinuousMap.id A).prodMk (ContinuousMap.const A (1 : I)))

/-- Helper for Remark 6.2.4: the endpoint map is evaluation of the cylinder inclusion at `1`. -/
@[simp] private theorem mappingCylinderEndpoint_apply (i : C(A, X)) (a : A) :
    mappingCylinderEndpoint i a =
      (ContinuousMap.mappingCylinderCylinderInclusion i) (a, 1) := by
  -- This is just the defining evaluation of the endpoint slice.
  simp [mappingCylinderEndpoint, ContinuousMap.comp_apply]

/-- Helper for Remark 6.2.4: the time-`0` inclusion `A → A × I` is injective. -/
private theorem mappingCylinderTimeZeroInclusion_injective (A : Type u) [TopologicalSpace A] :
    Function.Injective (ContinuousMap.mappingCylinderTimeZeroInclusion A : A → A × I) := by
  -- The first coordinate recovers the original point.
  intro a b h
  simpa [ContinuousMap.mappingCylinderTimeZeroInclusion] using congrArg Prod.fst h

/-- Helper for Remark 6.2.4: the underlying square of the mapping-cylinder construction is a
pushout square in `Type`. -/
private theorem mappingCylinderIsPushout (i : C(A, X)) :
    @IsPushout (Type u) inferInstance A X (A × I) i.mappingCylinder
      (i : A → X)
      (ContinuousMap.mappingCylinderTimeZeroInclusion A : A → A × I)
      (ContinuousMap.mappingCylinderTargetInclusion i : X → i.mappingCylinder)
      (ContinuousMap.mappingCylinderCylinderInclusion i : A × I → i.mappingCylinder) := by
  -- Forgetting the topological structure preserves the canonical pushout square.
  let hTop : IsPushout
      (TopCat.ofHom i)
      (TopCat.ofHom (ContinuousMap.mappingCylinderTimeZeroInclusion A))
      (TopCat.ofHom (ContinuousMap.mappingCylinderTargetInclusion i))
      (TopCat.ofHom (ContinuousMap.mappingCylinderCylinderInclusion i)) :=
    IsPushout.of_hasPushout _ _
  simpa using hTop.map (forget TopCat)

/-- Helper for Remark 6.2.4: target-side points of the mapping cylinder never equal endpoint
points `mappingCylinderEndpoint i a`. -/
private theorem mappingCylinderTargetInclusion_ne_endpoint (i : C(A, X)) (x : X) (a : A) :
    (ContinuousMap.mappingCylinderTargetInclusion i) x ≠ mappingCylinderEndpoint i a := by
  -- Flip the pushout so the mono leg is the time-`0` inclusion, then rule out a gluing witness by
  -- comparing second coordinates.
  intro hEq
  let hFlip := (mappingCylinderIsPushout i).flip
  have h :=
    (pushoutCocone_inl_eq_inr_iff_of_isColimit
      hFlip.isColimit
      (mappingCylinderTimeZeroInclusion_injective A)
      (a, 1) x).1 (by
        simpa [hFlip, mappingCylinderEndpoint_apply] using hEq.symm)
  rcases h with ⟨b, hb, _⟩
  have hTime : ((1 : I) : ℝ) = 0 := by
    simpa [ContinuousMap.mappingCylinderTimeZeroInclusion] using congrArg Prod.snd hb
  norm_num at hTime

/-- Helper for Remark 6.2.4: a point on the cylinder side hits the endpoint slice exactly at the
corresponding time-`1` point. -/
private theorem mappingCylinderCylinderInclusion_eq_endpoint_iff (i : C(A, X)) (z : A × I)
    (a : A) :
    (ContinuousMap.mappingCylinderCylinderInclusion i) z = mappingCylinderEndpoint i a ↔
      z = (a, 1) := by
  constructor
  · intro hEq
    -- Route correction: transport once to the canonical `Type` pushout, where equality of two
    -- left-leg points is governed by `Pushout.quot_mk_eq_iff`.
    let hCanon : @IsPushout (Type u) inferInstance A (A × I) X
        (Pushout
          (ContinuousMap.mappingCylinderTimeZeroInclusion A : A → A × I) (i : A → X))
        (ContinuousMap.mappingCylinderTimeZeroInclusion A : A → A × I)
        (i : A → X)
        (Pushout.inl
          (ContinuousMap.mappingCylinderTimeZeroInclusion A : A → A × I) (i : A → X))
        (Pushout.inr
          (ContinuousMap.mappingCylinderTimeZeroInclusion A : A → A × I) (i : A → X)) :=
      IsPushout.of_isColimit
        (Pushout.isColimitCocone
          (ContinuousMap.mappingCylinderTimeZeroInclusion A : A → A × I) (i : A → X))
    let e := (mappingCylinderIsPushout i).flip.isoIsPushout (A × I) X hCanon
    -- First identify both sides with canonical `Pushout.inl` points.
    have hz :
        e.hom ((ContinuousMap.mappingCylinderCylinderInclusion i) z) =
          Pushout.inl
            (ContinuousMap.mappingCylinderTimeZeroInclusion A : A → A × I) (i : A → X) z := by
      simpa [e] using
        congrArg (fun f ↦ f z)
          ((mappingCylinderIsPushout i).flip.inl_isoIsPushout_hom (A × I) X hCanon)
    have ha :
        e.hom ((ContinuousMap.mappingCylinderCylinderInclusion i) (a, 1)) =
          Pushout.inl
            (ContinuousMap.mappingCylinderTimeZeroInclusion A : A → A × I) (i : A → X) (a, 1) := by
      simpa [e] using
        congrArg (fun f ↦ f (a, 1))
          ((mappingCylinderIsPushout i).flip.inl_isoIsPushout_hom (A × I) X hCanon)
    have hCanonEq :
        Pushout.inl
            (ContinuousMap.mappingCylinderTimeZeroInclusion A : A → A × I) (i : A → X) z =
          Pushout.inl
            (ContinuousMap.mappingCylinderTimeZeroInclusion A : A → A × I) (i : A → X) (a, 1) := by
      exact hz.symm.trans
        ((congrArg e.hom (by simpa [mappingCylinderEndpoint_apply] using hEq)).trans ha)
    -- Then the canonical quotient description shows the only remaining possibility is equality.
    have hMono : Mono (ContinuousMap.mappingCylinderTimeZeroInclusion A : A → A × I) :=
      (mono_iff_injective _).2 (mappingCylinderTimeZeroInclusion_injective A)
    have hRel :=
      (@Pushout.quot_mk_eq_iff _ _ _
        (ContinuousMap.mappingCylinderTimeZeroInclusion A : A → A × I) (i : A → X) hMono
        (Sum.inl z) (Sum.inl (a, 1))).1 hCanonEq
    rw [Pushout.inl_rel'_inl_iff] at hRel
    rcases hRel with rfl | ⟨x, y, hxy, hx, hy⟩
    · rfl
    · rcases z with ⟨z₀, z₁⟩
      -- The off-gluing endpoint `(a, 1)` cannot lie in the time-`0` range.
      have hTime : ((1 : I) : ℝ) = 0 := by
        simpa [ContinuousMap.mappingCylinderTimeZeroInclusion] using congrArg Prod.snd hy.symm
      norm_num at hTime
  · rintro rfl
    -- The endpoint map was defined as the cylinder inclusion evaluated at time `1`.
    simp [mappingCylinderEndpoint_apply]

/-- Helper for Remark 6.2.4: the target inclusion misses every endpoint image, so the endpoint
slice stays entirely on the cylinder side of the pushout. -/
private theorem mappingCylinderEndpoint_image_preimage_targetInclusion
    (i : C(A, X)) (s : Set A) :
    (ContinuousMap.mappingCylinderTargetInclusion i) ⁻¹'
        ((mappingCylinderEndpoint i) '' s) = ∅ := by
  -- A target-side point can never equal an endpoint point in the mapping cylinder.
  ext x
  constructor
  · rintro ⟨a, ha, hxa⟩
    exact (mappingCylinderTargetInclusion_ne_endpoint i x a hxa.symm).elim
  · intro hx
    simp at hx

/-- Helper for Remark 6.2.4: pulling an endpoint image back along the cylinder inclusion cuts out
exactly the time-`1` slice over the source subset. -/
private theorem mappingCylinderEndpoint_image_preimage_cylinderInclusion
    (i : C(A, X)) (s : Set A) :
    (ContinuousMap.mappingCylinderCylinderInclusion i) ⁻¹' ((mappingCylinderEndpoint i) '' s) =
      { z : A × I | z.1 ∈ s ∧ z.2 = 1 } := by
  -- The earlier endpoint-identification lemma reduces the pullback to literal coordinates.
  ext z
  constructor
  · rintro ⟨a, ha, hza⟩
    have hz : z = (a, 1) := (mappingCylinderCylinderInclusion_eq_endpoint_iff i z a).1 hza.symm
    rcases z with ⟨z₀, z₁⟩
    cases hz
    exact ⟨ha, rfl⟩
  · intro hz
    rcases z with ⟨z₀, z₁⟩
    refine ⟨z₀, hz.1, ?_⟩
    rw [show z₁ = (1 : I) by exact hz.2]
    simp [mappingCylinderEndpoint_apply]

/-- Helper for Remark 6.2.4: the endpoint map is injective because the pushout only identifies
the cylinder at time `0`, never at time `1`. -/
private theorem mappingCylinderEndpoint_injective (i : C(A, X)) :
    Function.Injective (mappingCylinderEndpoint i) := by
  -- Compare two endpoint points on the cylinder side and read off the first coordinate.
  intro a b hab
  have hPair :
      ((a, (1 : I)) : A × I) = ((b, (1 : I)) : A × I) :=
    (mappingCylinderCylinderInclusion_eq_endpoint_iff i (a, 1) b).1 (by
      simpa [mappingCylinderEndpoint_apply] using hab)
  exact congrArg Prod.fst hPair

/-- Helper for Remark 6.2.4: the endpoint map is a closed map because closed subsets of the
source slice remain closed when tested against the pushout cocone. -/
private theorem mappingCylinderEndpoint_isClosedMap (i : C(A, X)) :
    IsClosedMap (mappingCylinderEndpoint i) := by
  intro s hs
  let c :
      PushoutCocone
        (TopCat.ofHom i)
        (TopCat.ofHom (ContinuousMap.mappingCylinderTimeZeroInclusion A)) :=
    PushoutCocone.mk
      (TopCat.ofHom (ContinuousMap.mappingCylinderTargetInclusion i))
      (TopCat.ofHom (ContinuousMap.mappingCylinderCylinderInclusion i))
      (by simpa using congrArg TopCat.ofHom (ContinuousMap.mappingCylinderTargetInclusion_comp i))
  have hc : IsColimit c := (IsPushout.of_hasPushout _ _).isColimit
  refine (TopCat.isClosed_iff_of_isColimit (c := c) hc ((mappingCylinderEndpoint i) '' s)).2 ?_
  intro j
  rcases j with (_ | (_ | _))
  · -- First pull back along the zero object using the target leg of the pushout.
    have hTarget :
        IsClosed
          ((ContinuousMap.mappingCylinderTargetInclusion i) ⁻¹'
            ((mappingCylinderEndpoint i) '' s)) := by
      rw [mappingCylinderEndpoint_image_preimage_targetInclusion]
      simp
    simpa [c.condition_zero, Set.preimage_comp] using
      hTarget.preimage i.continuous
  · -- The target leg sees no endpoint points at all.
    have hTarget :
        IsClosed
          ((ContinuousMap.mappingCylinderTargetInclusion i) ⁻¹'
            ((mappingCylinderEndpoint i) '' s)) := by
      rw [mappingCylinderEndpoint_image_preimage_targetInclusion]
      simp
    simpa [c] using hTarget
  · -- On the cylinder leg the image is just the closed time-`1` slice over `s`.
    have hPullback :
        IsClosed
          ((ContinuousMap.mappingCylinderCylinderInclusion i) ⁻¹'
            ((mappingCylinderEndpoint i) '' s)) := by
      rw [mappingCylinderEndpoint_image_preimage_cylinderInclusion]
      have hfst : IsClosed ((Prod.fst : A × I → A) ⁻¹' s) := hs.preimage continuous_fst
      have hsnd : IsClosed ((Prod.snd : A × I → I) ⁻¹' ({1} : Set I)) :=
        isClosed_singleton.preimage continuous_snd
      have hSet :
          { z : A × I | z.1 ∈ s ∧ z.2 = 1 } =
            (Prod.fst : A × I → A) ⁻¹' s ∩ (Prod.snd : A × I → I) ⁻¹' ({1} : Set I) := by
        ext z
        simp
      rw [hSet]
      exact hfst.inter hsnd
    simpa [c] using hPullback

/-- Helper for Remark 6.2.4: the endpoint slice `A → M_i` is a closed embedding. -/
private theorem mappingCylinderEndpoint_isClosedEmbedding (i : C(A, X)) :
    Topology.IsClosedEmbedding (mappingCylinderEndpoint i) := by
  -- Closed-map plus injectivity packages the endpoint slice as a closed embedding.
  refine Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      (mappingCylinderEndpoint i).continuous
      (mappingCylinderEndpoint_injective i)
      (mappingCylinderEndpoint_isClosedMap i)

/-- Helper for Remark 6.2.4: the canonical map `M_i → X × I` sends the endpoint slice to the
time-`1` inclusion of `i`. -/
private theorem mappingCylinderCanonicalMap_comp_endpoint (i : C(A, X)) :
    (ContinuousMap.mappingCylinderCanonicalMap i).comp (mappingCylinderEndpoint i) =
      (((ContinuousMap.id X).prodMk (ContinuousMap.const X (1 : I))).comp i) := by
  -- Evaluate the canonical map on the cylinder-side endpoint and simplify.
  ext a
  · simpa [mappingCylinderEndpoint, ContinuousMap.comp_apply,
      ContinuousMap.mappingCylinderCylinderMap_apply] using
      congrArg Prod.fst <|
        congrArg (fun f : C(A × I, X × I) => f (a, 1))
          (ContinuousMap.mappingCylinderCanonicalMap_comp_cylinderInclusion i)
  · simpa [mappingCylinderEndpoint, ContinuousMap.comp_apply,
      ContinuousMap.mappingCylinderCylinderMap_apply] using
      congrArg Prod.snd <|
        congrArg (fun f : C(A × I, X × I) => f (a, 1))
          (ContinuousMap.mappingCylinderCanonicalMap_comp_cylinderInclusion i)

/-- Helper for Remark 6.2.4: the fixed time-`1` inclusion `X → X × I` is a closed embedding. -/
private theorem timeOneInclusion_isClosedEmbedding (X : Type u) [TopologicalSpace X] :
    Topology.IsClosedEmbedding
      (((ContinuousMap.id X).prodMk (ContinuousMap.const X (1 : I))) : C(X, X × I)) := by
  -- The first projection recovers the source point, and the singleton `{1}` is closed in `I`.
  refine Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      (((ContinuousMap.id X).prodMk (ContinuousMap.const X (1 : I))).continuous) ?_ ?_
  · intro x y hxy
    simpa using congrArg Prod.fst hxy
  · simpa using
      (isClosedMap_prodMk_right (X := X) (y := (1 : I)) :
        IsClosedMap fun x : X ↦ (x, (1 : I)))

/-- Helper for Remark 6.2.4: a mapping-cylinder retract makes the canonical map `M_i → X × I`
an embedding. -/
private theorem mappingCylinderCanonicalMap_isEmbedding {i : C(A, X)}
    (r : C(X × I, i.mappingCylinder)) (hr : IsMappingCylinderRetract r) :
    Topology.IsEmbedding (ContinuousMap.mappingCylinderCanonicalMap i) := by
  -- The retract equation is exactly a continuous left inverse for the canonical map.
  let hLeft :
      Function.LeftInverse r (ContinuousMap.mappingCylinderCanonicalMap i) := fun z ↦ by
        have hz := congrArg (fun f : C(i.mappingCylinder, i.mappingCylinder) ↦ f z) hr.left_inv
        simpa [ContinuousMap.comp_apply] using hz
  exact hLeft.isEmbedding r.continuous (ContinuousMap.mappingCylinderCanonicalMap i).continuous

/-- Helper for Remark 6.2.4: the retract criterion already shows that `i` is an embedding by
comparing the closed endpoint slice in `M_i` with the standard time-`1` slice in `X × I`. -/
private theorem cofibrationEmbeddingFromEndpoint [CompactlyGeneratedWeakHausdorffSpace A]
    [CompactlyGeneratedWeakHausdorffSpace X] {i : C(A, X)}
    (r : C(X × I, i.mappingCylinder)) (hr : IsMappingCylinderRetract r) :
    Topology.IsEmbedding i := by
  have hCanonical :
      Topology.IsEmbedding (ContinuousMap.mappingCylinderCanonicalMap i) :=
    mappingCylinderCanonicalMap_isEmbedding r hr
  have hEndpoint :
      Topology.IsEmbedding (mappingCylinderEndpoint i) :=
    (mappingCylinderEndpoint_isClosedEmbedding i).isEmbedding
  have hComp :
      Topology.IsEmbedding
        ((ContinuousMap.mappingCylinderCanonicalMap i).comp (mappingCylinderEndpoint i)) := by
    -- Compose the two embedding steps already established in the endpoint model.
    exact hCanonical.comp hEndpoint
  have hTimeOne :
      Topology.IsEmbedding
        (((ContinuousMap.id X).prodMk (ContinuousMap.const X (1 : I))) : C(X, X × I)) :=
    (timeOneInclusion_isClosedEmbedding X).isEmbedding
  -- Rewrite the composed endpoint model into the ordinary time-`1` inclusion of `i`.
  rw [mappingCylinderCanonicalMap_comp_endpoint] at hComp
  exact hTimeOne.of_comp_iff.mp hComp

/-- Helper for Remark 6.2.4: the retract criterion should force `Set.range i` to be closed via
the time-`1` fixed-point locus of `(ContinuousMap.mappingCylinderCanonicalMap i).comp r`. -/
private theorem mappingCylinderPoint_eq_endpoint_of_canonicalMap_eq_timeOne (i : C(A, X))
    {z : i.mappingCylinder} {x : X}
    (hz : (ContinuousMap.mappingCylinderCanonicalMap i) z = (x, 1)) :
    ∃ a : A, z = mappingCylinderEndpoint i a := by
  -- Route correction: move once to the canonical `Type` pushout and classify the representative
  -- of `z` there, instead of repeating endpoint transport in the closed-range argument.
  let hCanon : @IsPushout (Type u) inferInstance A (A × I) X
      (Pushout
        (ContinuousMap.mappingCylinderTimeZeroInclusion A : A → A × I) (i : A → X))
      (ContinuousMap.mappingCylinderTimeZeroInclusion A : A → A × I)
      (i : A → X)
      (Pushout.inl
        (ContinuousMap.mappingCylinderTimeZeroInclusion A : A → A × I) (i : A → X))
      (Pushout.inr
        (ContinuousMap.mappingCylinderTimeZeroInclusion A : A → A × I) (i : A → X)) :=
    IsPushout.of_isColimit
      (Pushout.isColimitCocone
        (ContinuousMap.mappingCylinderTimeZeroInclusion A : A → A × I) (i : A → X))
  let e := (mappingCylinderIsPushout i).flip.isoIsPushout (A × I) X hCanon
  let q :
      Pushout
        (ContinuousMap.mappingCylinderTimeZeroInclusion A : A → A × I) (i : A → X) :=
    e.hom z
  have hHomInjective : Function.Injective e.hom := by
    intro z₁ z₂ hzEq
    simpa using congrArg e.inv hzEq
  obtain ⟨rep, hrep⟩ := Quot.exists_rep q
  cases rep with
  | inl y =>
      have hzRep :
          z =
            e.inv
              (Pushout.inl
                (ContinuousMap.mappingCylinderTimeZeroInclusion A : A → A × I) (i : A → X) y) := by
        apply hHomInjective
        simpa [q, e] using hrep.symm
      have hyInv :
          e.inv
              (Pushout.inl
                (ContinuousMap.mappingCylinderTimeZeroInclusion A : A → A × I) (i : A → X) y) =
            (ContinuousMap.mappingCylinderCylinderInclusion i) y := by
        apply hHomInjective
        simpa [e] using
          congrArg (fun f ↦ f y)
            ((mappingCylinderIsPushout i).flip.inl_isoIsPushout_hom (A × I) X hCanon).symm
      have hyImage :
          (ContinuousMap.mappingCylinderCanonicalMap i)
              ((ContinuousMap.mappingCylinderCylinderInclusion i) y) =
            (x, 1) := by
        calc
          (ContinuousMap.mappingCylinderCanonicalMap i)
              ((ContinuousMap.mappingCylinderCylinderInclusion i) y) =
            (ContinuousMap.mappingCylinderCanonicalMap i)
              (e.inv
                (Pushout.inl
                  (ContinuousMap.mappingCylinderTimeZeroInclusion A : A → A × I) (i : A → X) y)) := by
                rw [hyInv.symm]
          _ = (x, 1) := by simpa [hzRep] using hz
      have hyMap :
          (ContinuousMap.mappingCylinderCylinderMap i) y = (x, 1) := by
        calc
          (ContinuousMap.mappingCylinderCylinderMap i) y =
              (ContinuousMap.mappingCylinderCanonicalMap i)
                ((ContinuousMap.mappingCylinderCylinderInclusion i) y) := by
                simpa [ContinuousMap.comp_apply] using
                  congrArg (fun f : C(A × I, X × I) ↦ f y)
                    (ContinuousMap.mappingCylinderCanonicalMap_comp_cylinderInclusion i).symm
          _ = (x, 1) := hyImage
      rcases y with ⟨a, t⟩
      have ht : t = (1 : I) := by
        simpa [ContinuousMap.mappingCylinderCylinderMap_apply] using congrArg Prod.snd hyMap
      refine ⟨a, ?_⟩
      calc
        z = (ContinuousMap.mappingCylinderCylinderInclusion i) (a, t) := by
          simpa [hzRep, hyInv]
        _ = mappingCylinderEndpoint i a := by
          exact (mappingCylinderCylinderInclusion_eq_endpoint_iff i (a, t) a).2 (by simpa [ht])
  | inr x₀ =>
      have hzRep :
          z =
            e.inv
              (Pushout.inr
                (ContinuousMap.mappingCylinderTimeZeroInclusion A : A → A × I) (i : A → X) x₀) := by
        apply hHomInjective
        simpa [q, e] using hrep.symm
      have hxInv :
          e.inv
              (Pushout.inr
                (ContinuousMap.mappingCylinderTimeZeroInclusion A : A → A × I) (i : A → X) x₀) =
            (ContinuousMap.mappingCylinderTargetInclusion i) x₀ := by
        apply hHomInjective
        simpa [e] using
          congrArg (fun f ↦ f x₀)
            ((mappingCylinderIsPushout i).flip.inr_isoIsPushout_hom (A × I) X hCanon).symm
      have hxImage :
          (ContinuousMap.mappingCylinderCanonicalMap i)
              ((ContinuousMap.mappingCylinderTargetInclusion i) x₀) =
            (x, 1) := by
        calc
          (ContinuousMap.mappingCylinderCanonicalMap i)
              ((ContinuousMap.mappingCylinderTargetInclusion i) x₀) =
            (ContinuousMap.mappingCylinderCanonicalMap i)
              (e.inv
                (Pushout.inr
                  (ContinuousMap.mappingCylinderTimeZeroInclusion A : A → A × I) (i : A → X) x₀)) := by
                rw [hxInv.symm]
          _ = (x, 1) := by simpa [hzRep] using hz
      have hxMap :
          (ContinuousMap.mappingCylinderTimeZeroInclusion X) x₀ = (x, 1) := by
        calc
          (ContinuousMap.mappingCylinderTimeZeroInclusion X) x₀ =
              (ContinuousMap.mappingCylinderCanonicalMap i)
                ((ContinuousMap.mappingCylinderTargetInclusion i) x₀) := by
                simpa [ContinuousMap.comp_apply] using
                  congrArg (fun f : C(X, X × I) ↦ f x₀)
                    (ContinuousMap.mappingCylinderCanonicalMap_comp_targetInclusion i).symm
          _ = (x, 1) := hxImage
      have hTime : ((0 : I) : ℝ) = 1 := by
        simpa [ContinuousMap.mappingCylinderTimeZeroInclusion] using congrArg Prod.snd hxMap
      norm_num at hTime

/-- Helper for Remark 6.2.4: the canonical map hits a time-`1` point exactly on the endpoint
slice, with first coordinate in the range of `i`. -/
private theorem mappingCylinderCanonicalMap_eq_timeOne_iff (i : C(A, X))
    {z : i.mappingCylinder} {x : X} :
    (ContinuousMap.mappingCylinderCanonicalMap i) z = (x, 1) ↔
      ∃ a : A, z = mappingCylinderEndpoint i a ∧ i a = x := by
  constructor
  · intro hz
    rcases mappingCylinderPoint_eq_endpoint_of_canonicalMap_eq_timeOne i hz with ⟨a, rfl⟩
    -- Once the point is on the endpoint slice, the canonical map computes by the endpoint formula.
    have hEndpoint :
        (ContinuousMap.mappingCylinderCanonicalMap i) (mappingCylinderEndpoint i a) =
          (((ContinuousMap.id X).prodMk (ContinuousMap.const X (1 : I))).comp i) a := by
      simpa [ContinuousMap.comp_apply] using
        congrArg (fun f : C(A, X × I) ↦ f a) (mappingCylinderCanonicalMap_comp_endpoint i)
    refine ⟨a, rfl, ?_⟩
    have hImage :
        (((ContinuousMap.id X).prodMk (ContinuousMap.const X (1 : I))).comp i) a = (x, 1) := by
      exact hEndpoint.symm.trans hz
    simpa [ContinuousMap.comp_apply] using congrArg Prod.fst hImage
  · rintro ⟨a, rfl, rfl⟩
    -- The endpoint restriction of the canonical map is exactly the time-`1` inclusion of `i`.
    simpa [ContinuousMap.comp_apply] using
      congrArg (fun f : C(A, X × I) ↦ f a) (mappingCylinderCanonicalMap_comp_endpoint i)

/-- Helper for Remark 6.2.4: membership in `Set.range i` is equivalent to the fixed-point
equation for `(ContinuousMap.mappingCylinderCanonicalMap i).comp r` on the time-`1` slice. -/
private theorem mem_range_iff_timeOneFixed
    [CompactlyGeneratedWeakHausdorffSpace A] [CompactlyGeneratedWeakHausdorffSpace X]
    {i : C(A, X)} (r : C(X × I, i.mappingCylinder)) (hr : IsMappingCylinderRetract r) (x : X) :
    x ∈ Set.range i ↔ ((ContinuousMap.mappingCylinderCanonicalMap i).comp r) (x, 1) = (x, 1) := by
  constructor
  · rintro ⟨a, rfl⟩
    -- The retract sends `(i a, 1)` to the endpoint slice, and the canonical map sends that slice
    -- straight back to `(i a, 1)`.
    have hCylinder :
        r (i a, 1) = mappingCylinderEndpoint i a := by
      simpa [mappingCylinderEndpoint_apply, ContinuousMap.comp_apply,
        ContinuousMap.mappingCylinderCylinderMap_apply] using
        congrArg (fun f : C(A × I, i.mappingCylinder) ↦ f (a, 1)) hr.cylinder
    calc
      ((ContinuousMap.mappingCylinderCanonicalMap i).comp r) (i a, 1) =
          (ContinuousMap.mappingCylinderCanonicalMap i) (mappingCylinderEndpoint i a) := by
            simp [ContinuousMap.comp_apply, hCylinder]
      _ = (i a, 1) := by
            simpa [ContinuousMap.comp_apply] using
              congrArg (fun f : C(A, X × I) ↦ f a) (mappingCylinderCanonicalMap_comp_endpoint i)
  · intro hFixed
    -- The time-`1` classification turns the fixed-point equation back into a point of `Set.range i`.
    rcases (mappingCylinderCanonicalMap_eq_timeOne_iff i
        (z := r (x, 1)) (x := x)).1 (by simpa [ContinuousMap.comp_apply] using hFixed) with
      ⟨a, _, ha⟩
    exact ⟨a, ha⟩

/-- Helper for Remark 6.2.4: compact test equalizers into a weak Hausdorff space are closed. -/
private theorem isClosed_eq_of_compactTest
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {Y : Type u} [TopologicalSpace Y]
    [WeaklyHausdorffSpace.{u, v} Y] (f g : C(K, Y)) :
    IsClosed {k : K | f k = g k} := by
  let fRange : C(K, Set.range f) :=
    ⟨fun k ↦ ⟨f k, ⟨k, rfl⟩⟩, f.continuous.subtype_mk fun k ↦ ⟨k, rfl⟩⟩
  let gRange : C(K, Set.range g) :=
    ⟨fun k ↦ ⟨g k, ⟨k, rfl⟩⟩, g.continuous.subtype_mk fun k ↦ ⟨k, rfl⟩⟩
  let pairedRanges : C(K, Set.range f × Set.range g) := fRange.prodMk gRange
  let commonRange : Set Y := Set.range f ∩ Set.range g
  have hCommonCompact : IsCompact commonRange := by
    -- Intersect the compact range of `f` with the closed range of `g`.
    have hgClosed : IsClosed (Set.range g) := g.continuous.isClosed_range
    simpa [commonRange] using (isCompact_range f.continuous).inter_right hgClosed
  let _ : CompactSpace commonRange := isCompact_iff_compactSpace.mp hCommonCompact
  let _ : CompactSpace (Set.range f) := isCompact_iff_compactSpace.mp (isCompact_range f.continuous)
  let _ : CompactSpace (Set.range g) := isCompact_iff_compactSpace.mp (isCompact_range g.continuous)
  let _ : T2Space (Set.range f) :=
    range_t2Space_of_compactHausdorffMap (g := f) f.continuous
  let _ : T2Space (Set.range g) :=
    range_t2Space_of_compactHausdorffMap (g := g) g.continuous
  let diagonalRange : C(commonRange, Set.range f × Set.range g) :=
    ⟨fun y ↦ (⟨y.1, y.2.1⟩, ⟨y.1, y.2.2⟩),
      (continuous_subtype_val.subtype_mk fun y ↦ y.2.1).prodMk
        (continuous_subtype_val.subtype_mk fun y ↦ y.2.2)⟩
  have hDiagonalClosed : IsClosed (Set.range diagonalRange) :=
    (isCompact_range diagonalRange.continuous).isClosed
  have hEq :
      {k : K | f k = g k} = pairedRanges ⁻¹' Set.range diagonalRange := by
    ext k
    constructor
    · intro hk
      refine ⟨⟨f k, ⟨⟨k, rfl⟩, ?_⟩⟩, ?_⟩
      · exact ⟨k, hk ▸ rfl⟩
      · apply Prod.ext
        · apply Subtype.ext
          rfl
        · apply Subtype.ext
          exact hk
    · rintro ⟨y, hy⟩
      have hf : y.1 = f k := by
        simpa [pairedRanges, diagonalRange, fRange, gRange] using
          congrArg (fun p ↦ ((p.1 : Set.range f) : Y)) hy
      have hg : y.1 = g k := by
        simpa [pairedRanges, diagonalRange, fRange, gRange] using
          congrArg (fun p ↦ ((p.2 : Set.range g) : Y)) hy
      exact hf.symm.trans hg
  -- Pull the closed diagonal image back along the paired range map.
  simpa [hEq] using hDiagonalClosed.preimage pairedRanges.continuous

private theorem range_isClosed_of_mappingCylinderRetract
    [CompactlyGeneratedWeakHausdorffSpace A] [CompactlyGeneratedWeakHausdorffSpace X]
    {i : C(A, X)} (r : C(X × I, i.mappingCylinder)) (hr : IsMappingCylinderRetract r) :
    IsClosed (Set.range i) := by
  -- Use the compactly-generated closed-set criterion and reduce each compact test pullback to a
  -- coordinatewise fixed-point condition on the time-`1` slice.
  refine UCompactlyGeneratedSpace.isClosed fun K g ↦ ?_
  let timeOne : C(K, X × I) :=
    (((ContinuousMap.id X).prodMk (ContinuousMap.const X (1 : I))).comp g)
  let fixedTest : C(K, X × I) :=
    ((ContinuousMap.mappingCylinderCanonicalMap i).comp r).comp timeOne
  let firstCoordinate : C(K, X) := ContinuousMap.fst.comp fixedTest
  let secondCoordinate : C(K, I) := ContinuousMap.snd.comp fixedTest
  have hPreimage :
      g ⁻¹' Set.range i = {k : K | fixedTest k = timeOne k} := by
    ext k
    simpa [timeOne, fixedTest, ContinuousMap.comp_apply] using
      (mem_range_iff_timeOneFixed r hr (g k))
  have hSplit :
      {k : K | fixedTest k = timeOne k} =
        {k : K | firstCoordinate k = g k} ∩ {k : K | secondCoordinate k = (1 : I)} := by
    ext k
    constructor
    · intro hk
      exact ⟨congrArg Prod.fst hk, congrArg Prod.snd hk⟩
    · rintro ⟨hk₁, hk₂⟩
      exact Prod.ext hk₁ hk₂
  have hFirstClosed : IsClosed {k : K | firstCoordinate k = g k} :=
    isClosed_eq_of_compactTest (Y := X) firstCoordinate g
  have hSecondClosed : IsClosed {k : K | secondCoordinate k = (1 : I)} := by
    simpa [secondCoordinate] using
      (isClosed_singleton.preimage secondCoordinate.continuous)
  rw [hPreimage, hSplit]
  exact hFirstClosed.inter hSecondClosed

/-- Helper for Remark 6.2.4: a mapping-cylinder retract forces the original map `i` to be
injective by comparing endpoint points at time `1`. -/
private theorem cofibrationInjectiveFromEndpoint {i : C(A, X)}
    (r : C(X × I, i.mappingCylinder)) (hr : IsMappingCylinderRetract r) :
    Function.Injective i := by
  -- Evaluate the cylinder restriction at time `1` and use endpoint uniqueness in the pushout.
  intro a b hab
  have ha :=
    congrArg (fun f : C(A × I, i.mappingCylinder) => f (a, 1)) hr.cylinder
  have hb :=
    congrArg (fun f : C(A × I, i.mappingCylinder) => f (b, 1)) hr.cylinder
  have hEndpoint : mappingCylinderEndpoint i a = mappingCylinderEndpoint i b := by
    calc
      mappingCylinderEndpoint i a = r (i a, 1) := by
        simpa [mappingCylinderEndpoint_apply, ContinuousMap.comp_apply] using ha.symm
      _ = r (i b, 1) := by simp [hab]
      _ = mappingCylinderEndpoint i b := by
        simpa [mappingCylinderEndpoint_apply, ContinuousMap.comp_apply] using hb
  exact mappingCylinderEndpoint_injective i hEndpoint

/-- Remark 6.2.4. A cofibration `i : C(A, X)` is a closed embedding, hence an inclusion with
closed image. -/
theorem IsCofibration.isClosedEmbedding [CompactlyGeneratedWeakHausdorffSpace A]
    [CompactlyGeneratedWeakHausdorffSpace X] {i : C(A, X)}
    (hi : IsCofibration.{u, u, u} i) :
    Topology.IsClosedEmbedding i := by
  obtain ⟨r, hr⟩ := (isCofibration_iff_exists_mappingCylinderRetract).mp hi
  -- Route correction: use the retract only to embed `M_i` into `X × I`; the remaining work is
  -- then the closed-range statement for `i`, treated separately via the time-`1` fixed-point
  -- locus of `j ∘ r`.
  exact ⟨cofibrationEmbeddingFromEndpoint r hr, range_isClosed_of_mappingCylinderRetract r hr⟩

/-- A cofibration is injective. -/
theorem IsCofibration.injective [CompactlyGeneratedWeakHausdorffSpace A]
    [CompactlyGeneratedWeakHausdorffSpace X] {i : C(A, X)}
    (hi : IsCofibration.{u, u, u} i) :
    Function.Injective i :=
  hi.isClosedEmbedding.injective

/-- The image of a cofibration is closed in its codomain. -/
theorem IsCofibration.isClosed_range [CompactlyGeneratedWeakHausdorffSpace A]
    [CompactlyGeneratedWeakHausdorffSpace X] {i : C(A, X)}
    (hi : IsCofibration.{u, u, u} i) :
    IsClosed (Set.range i) :=
  hi.isClosedEmbedding.isClosed_range
