import stacks_project.Chap04.Definition_4_35_1
import stacks_project.Chap04.Lemma_4_33_7
import stacks_project.Chap07.Definition_7_8_2
import stacks_project.Chap07.Definition_7_13_1
import stacks_project.Chap08.Lemma_8_2_3
import stacks_project.Chap08.Lemma_8_10_1

noncomputable section

universe u v

namespace CategoryTheory

namespace FibredCategoryOver

variable {C : Type u} [Category.{v} C]

open CategoryTheory.Limits

/-- Helper for Lemma 8.10.4: local alias for the topology on the total category inherited from
the base site. -/
private abbrev inheritedTopologyLocal
    (J : GrothendieckTopology C) (X : FibredCategoryOver C) :
    GrothendieckTopology X.S :=
  (stronglyCartesianLiftPrecoverage J.toPrecoverage X.p).toGrothendieck

/-- Helper for Lemma 8.10.4: the componentwise image of a fixed-target family under the
projection functor. -/
private def imageFamilyLocal
    (X : FibredCategoryOver C) {y : X.S} (S : SemiRepresentableFamily.Over y) :
    SemiRepresentableFamily.Over (X.p.obj y) where
  index := S.index
  obj := fun i ↦ (Over.post X.p).obj (S.obj i)

/-- Helper for Lemma 8.10.4: a represented family of strongly cartesian arrows over `y` is an
inherited cover once its image family downstairs is `J`-covering. -/
private theorem strongly_cartesian_family_mem_inheritedTopology_of_base_cover
    (J : GrothendieckTopology C) (X : FibredCategoryOver C)
    {ι : Type (max u v)} (y : X.S) (Y : ι → X.S) (g : ∀ i, Y i ⟶ y)
    (hgstrong : ∀ i, X.p.IsStronglyCartesian (X.p.map (g i)) (g i))
    (hbaseCover :
      Sieve.ofArrows (fun i ↦ X.p.obj (Y i)) (fun i ↦ X.p.map (g i)) ∈ J (X.p.obj y)) :
    Sieve.ofArrows Y g ∈ inheritedTopologyLocal J X y := by
  have hbasePrecover :
      Presieve.ofArrows (fun i ↦ X.p.obj (Y i)) (fun i ↦ X.p.map (g i)) ∈
        J.toPrecoverage (X.p.obj y) := by
    -- Rewrite the downstairs Grothendieck cover into the precoverage owner used by the inherited
    -- generators.
    rw [GrothendieckTopology.mem_toPrecoverage_iff]
    simpa [Sieve.ofArrows] using hbaseCover
  -- Unfold the inherited topology once and apply the generating-family criterion for strong lifts.
  rw [inheritedTopologyLocal]
  let Y' : ULift.{max u v} ι → X.S := fun i ↦ Y i.down
  let g' : ∀ i, Y' i ⟶ y := fun i ↦ g i.down
  have hbasePrecover' :
      Presieve.ofArrows (fun i ↦ X.p.obj (Y' i)) (fun i ↦ X.p.map (g' i)) ∈
        J.toPrecoverage (X.p.obj y) := by
    have hEq :
        Presieve.ofArrows (fun i : ULift.{max u v} ι ↦ X.p.obj (Y i.down))
            (fun i ↦ X.p.map (g i.down)) =
          Presieve.ofArrows (fun i ↦ X.p.obj (Y i)) (fun i ↦ X.p.map (g i)) := by
      simpa using
        (Presieve.ofArrows_comp_eq_of_surjective (fun i : ι ↦ X.p.map (g i))
          ULift.down_surjective)
    rw [hEq]
    exact hbasePrecover
  have hcover :
      Presieve.ofArrows Y' g' ∈ stronglyCartesianLiftPrecoverage J.toPrecoverage X.p y := by
    exact
      (ofArrows_mem_stronglyCartesianLiftPrecoverage_iff
        (J := J.toPrecoverage) (p := X.p) Y' g').2
        ⟨(fun i ↦ hgstrong i.down), hbasePrecover'⟩
  simpa [Sieve.ofArrows, Y', g'] using
    (Precoverage.generate_mem_toGrothendieck
      (J := stronglyCartesianLiftPrecoverage J.toPrecoverage X.p)
      (R := Presieve.ofArrows Y' g') hcover)

/-- Helper for Lemma 8.10.4: pulling back a covering sieve on `X.p.obj y` along the projection
still gives an inherited covering sieve upstairs. -/
theorem lifted_covering_sieve_mem_inheritedTopology_aux
    (J : GrothendieckTopology C) (X : FibredCategoryOver C) [IsFibredInGroupoids X.p]
    {y : X.S} {S : Sieve (X.p.obj y)}
    (hS : S ∈ J (X.p.obj y)) :
    S.functorPullback X.p ∈ inheritedTopologyLocal J X y := by
  obtain ⟨ι, U, f, rfl⟩ := S.exists_eq_ofArrows
  let yFiber : X.p.Fiber (X.p.obj y) := ⟨y, rfl⟩
  let Y : ι → X.S := fun i ↦ (f i ^*[canonicalPullbackChoice X.p] yFiber).1
  let g : ∀ i, Y i ⟶ y := fun i ↦ (canonicalPullbackChoice X.p).map (f i) yFiber
  have hgstrong : ∀ i, X.p.IsStronglyCartesian (X.p.map (g i)) (g i) := by
    intro i
    infer_instance
  have hgi :
      ∀ i, X.p.map (g i) =
        eqToHom ((f i ^*[canonicalPullbackChoice X.p] yFiber).2) ≫ f i := by
    intro i
    letI : X.p.IsHomLift (f i) (g i) := by
      simpa [g] using
        (show X.p.IsHomLift (f i) ((canonicalPullbackChoice X.p).map (f i) yFiber) from
          by
            let _ :
                X.p.IsStronglyCartesian (f i) ((canonicalPullbackChoice X.p).map (f i) yFiber) :=
              (canonicalPullbackChoice X.p).isStronglyCartesian (f i) yFiber
            infer_instance)
    simpa [Y, g] using (IsHomLift.fac' X.p (f i) (g i))
  have hbaseCover :
      Sieve.ofArrows (fun i ↦ X.p.obj (Y i)) (fun i ↦ X.p.map (g i)) ∈ J (X.p.obj y) := by
    refine J.superset_covering ?_ hS
    rw [Sieve.generate_le_iff]
    intro Z k hk
    rcases hk with ⟨i⟩
    rw [Sieve.mem_ofArrows_iff]
    refine ⟨i, eqToHom ((f i ^*[canonicalPullbackChoice X.p] yFiber).2).symm, ?_⟩
    simpa [Category.assoc] using
      (congrArg
        (eqToHom ((f i ^*[canonicalPullbackChoice X.p] yFiber).2).symm ≫ ·)
        (hgi i)).symm
  have hfamily :
      Sieve.ofArrows Y g ∈ inheritedTopologyLocal J X y :=
    strongly_cartesian_family_mem_inheritedTopology_of_base_cover J X y Y g hgstrong hbaseCover
  refine (inheritedTopologyLocal J X).superset_covering ?_ hfamily
  rw [Sieve.generate_le_iff]
  intro Z k hk
  rcases hk with ⟨i⟩
  change (Sieve.ofArrows U f) (X.p.map (g i))
  rw [Sieve.mem_ofArrows_iff]
  refine ⟨i, eqToHom ((f i ^*[canonicalPullbackChoice X.p] yFiber).2), ?_⟩
  simpa using hgi i

/-- Helper for Lemma 8.10.4: an inherited covering family maps to a covering family downstairs.
The source proof first refines the inherited cover by a generating strongly cartesian family, then
enlarges that downstairs generator to the actual image family. -/
private theorem image_family_isCovering_of_inherited_cover
    (J : GrothendieckTopology C) (X : FibredCategoryOver C) [IsFibredInGroupoids X.p]
    {y : X.S} (S : SemiRepresentableFamily.Over y)
    (hS : SemiRepresentableFamily.Over.IsCovering (inheritedTopologyLocal J X).toPrecoverage S) :
    SemiRepresentableFamily.Over.IsCovering J.toPrecoverage (imageFamilyLocal X S) := by
  have hS' : S.toSieve ∈ inheritedTopologyLocal J X y := by
    simpa [SemiRepresentableFamily.Over.IsCovering, SemiRepresentableFamily.Over.toSieve,
      GrothendieckTopology.mem_toPrecoverage_iff] using hS
  obtain ⟨R, hR, hRle⟩ :=
    (Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition
      (J := stronglyCartesianLiftPrecoverage J.toPrecoverage X.p)
      (X := y) (S := S.toSieve)).1 <| by
        simpa [inheritedTopologyLocal] using hS'
  rcases hR with ⟨ι, Y, g, hR_eq, hgstrong, hbasePrecover⟩
  have hRle' : Presieve.ofArrows Y g ≤ S.toSieve := by
    simpa [hR_eq] using hRle
  have hbaseCover :
      Sieve.ofArrows (fun i ↦ X.p.obj (Y i)) (fun i ↦ X.p.map (g i)) ∈ J (X.p.obj y) := by
    -- Promote the downstairs precoverage witness to the ambient Grothendieck topology.
    rw [GrothendieckTopology.mem_toPrecoverage_iff] at hbasePrecover
    simpa [Sieve.ofArrows] using hbasePrecover
  have hImageCover : (imageFamilyLocal X S).toSieve ∈ J (X.p.obj y) := by
    refine J.superset_covering ?_ hbaseCover
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    intro Z k hk
    rcases hk with ⟨i⟩
    have hkSieve : S.toSieve (g i) := by
      exact hRle' (Presieve.ofArrows.mk i)
    rw [SemiRepresentableFamily.Over.toSieve] at hkSieve ⊢
    rcases hkSieve with ⟨W, a, b, hb, hab⟩
    refine ⟨X.p.obj W, X.p.map a, X.p.map b, ?_, ?_⟩
    · -- A generator of `S.toSieve` maps to a generator of the image-family presieve.
      simpa [imageFamilyLocal, SemiRepresentableFamily.Over.toPresieve] using
        (Presieve.map_map (F := X.p) hb)
    · -- Mapping the factorization upstairs gives the required factorization downstairs.
      simpa [Functor.map_comp] using congrArg (X.p.map) hab
  -- Convert the sieve-level cover back to the family-level `IsCovering` predicate.
  simpa [SemiRepresentableFamily.Over.IsCovering, SemiRepresentableFamily.Over.toSieve,
    GrothendieckTopology.mem_toPrecoverage_iff] using hImageCover

/-- Helper for Lemma 8.10.4: because every arrow in a category fibred in groupoids is strongly
cartesian, the projection preserves pullbacks along arbitrary arrows. -/
private theorem projection_preservesPullback_of_arrow
    (X : FibredCategoryOver C) [IsFibredInGroupoids X.p]
    {y z t : X.S} (i : z ⟶ y) (f : t ⟶ y)
    [HasPullback f i] :
    PreservesLimit (cospan f i) X.p := by
  have hiStrong : X.p.IsStronglyCartesian (X.p.map i) i := by
    infer_instance
  -- Route correction: the pullback-comparison isomorphism is now derived from a global
  -- pullback-preservation fact, not from cover-specific transport.
  exact preservesLimit_of_preserves_limit_cone (IsPullback.of_hasPullback f i).isLimit <| by
    apply (isLimitMapConePullbackConeEquiv X.p pullback.condition).symm.toFun
    -- Map the canonical upstairs pullback square and use strong cartesianness of the right leg.
    exact
      (mapped_square_isPullback_of_isPullback_of_isStronglyCartesian
        (p := X.p) (hφ := hiStrong) (h := IsPullback.of_hasPullback f i)).isLimit

/-- Helper for Lemma 8.10.4: the canonical pullback-comparison morphism for the projection is an
isomorphism along every arrow. -/
private theorem projection_pullbackComparison_isIso_of_arrow
    (X : FibredCategoryOver C) [IsFibredInGroupoids X.p]
    {y z t : X.S} (i : z ⟶ y) (f : t ⟶ y)
    [HasPullback f i] [HasPullback (X.p.map f) (X.p.map i)] :
    IsIso (pullbackComparison X.p f i) := by
  -- Once pullbacks are preserved, mathlib's standard comparison morphism is automatically an iso.
  let _ : PreservesLimit (cospan f i) X.p := projection_preservesPullback_of_arrow X i f
  infer_instance

/-- Helper for Lemma 8.10.4: the projection functor satisfies the source-facing continuity data
for the inherited precoverage on the total category. This packages the same two source-proof
inputs as the direct Chapter 7 continuity owner already available in the workspace. -/
instance projection_isContinuousSiteFunctor_of_isFibredInGroupoids
    (J : GrothendieckTopology C) (X : FibredCategoryOver C) [IsFibredInGroupoids X.p] :
    Functor.IsContinuousSiteFunctor X.p (inheritedTopologyLocal J X).toPrecoverage J.toPrecoverage where
  toLeComap := by
    intro y R hR
    obtain ⟨ι, Y, g, rfl⟩ := R.exists_eq_ofArrows
    let S : SemiRepresentableFamily.Over y := SemiRepresentableFamily.Over.ofArrows Y g
    have hS :
        SemiRepresentableFamily.Over.IsCovering (inheritedTopologyLocal J X).toPrecoverage S := by
      -- Repackage the covering presieve as the corresponding represented family.
      simpa [S, SemiRepresentableFamily.Over.IsCovering, SemiRepresentableFamily.Over.toPresieve]
        using hR
    -- The image family itself is covering downstairs, so the mapped presieve is covering too.
    simpa [S, imageFamilyLocal, SemiRepresentableFamily.Over.IsCovering,
      SemiRepresentableFamily.Over.toPresieve, Presieve.map_ofArrows] using
      image_family_isCovering_of_inherited_cover J X S hS
  preservesPullback {V} {R} _hR {Y} {i} _hi {T} f := by
    intro
    -- Route correction: pullback preservation is global for arrows, so only the local pullback
    -- instance matters in the closing step.
    exact projection_preservesPullback_of_arrow X i f

/-- Helper for Lemma 8.10.4: the projection functor is cocontinuous for the inherited topology on
the total category. -/
instance projection_isCocontinuous_of_isFibredInGroupoids
    (J : GrothendieckTopology C) (X : FibredCategoryOver C) [IsFibredInGroupoids X.p] :
    X.p.IsCocontinuous (inheritedTopologyLocal J X) J where
  cover_lift {y} S hS := by
    -- Lift a covering sieve downstairs by the represented family of chosen cartesian pullbacks.
    exact lifted_covering_sieve_mem_inheritedTopology_aux J X hS

end FibredCategoryOver

end CategoryTheory
