import StacksProject_2024.Chap08.Lemma_8_11_3.InheritedTopologyAndLocalLifting

open CategoryTheory
open BasedFunctor
open Functor
open Functor.Fiber
open Functor.IsStronglyCartesian
open FibredCategoryOver

universe w v₁ u₁ v₂ u₂

namespace CategoryTheory

namespace StackInGroupoidsOver.Hom

section

variable {C : Type u₁} [Category.{v₁} C]
variable {J : GrothendieckTopology C}
variable {Xₛ Yₛ : StackInGroupoidsOver.{u₁, v₁, max u₁ v₁, v₁} J}

/- Domain-style sampling for the main gerbe characterization in Lemma 8.11.3:
- primary domain: gerbes over morphisms of stacks in groupoids, compared across different
  factorizations of the same morphism through a functor fibred in groupoids over the target;
- inspected owner-level declarations:
  `exists_equivalence_over_target_between_fibred_groupoid_factorizations`,
  `isStackInGroupoids_iff_of_equivalence_over_base`,
  `isGerbe_iff_of_equivalence_over_base`,
  `fibredInGroupoidsFactorizationToTarget`;
- best owner abstraction: the source-facing gerbe predicate
  `IsGerbe (inheritedTopology J Yₛ) F'.toFunctor` on an arbitrary factorization of `F`
  through a functor `F'` fibred in groupoids over `Yₛ`;
- primitive data: a factorization `a ⋙ F' = toBasedFunctor F` with `a` an equivalence over `C`;
- derived API: the canonical explicit-factorization specialization below.

Source/core/bridge triage:
- `source-facing`: the factorization-independent equivalence below for an arbitrary factorization
  `a ⋙ F' = toBasedFunctor F`;
- `core/canonical`: `IsGerbe (inheritedTopology J Yₛ) F'.toFunctor`,
  `exists_equivalence_over_target_between_fibred_groupoid_factorizations`, and the transport
  lemmas `isStackInGroupoids_iff_of_equivalence_over_base` and
  `isGerbe_iff_of_equivalence_over_base`;
- `bridge/view`: the canonical explicit factorization
  `fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)`. -/

/-- Helper for Lemma 8.11.3: a strongly cartesian family over a base covering sieve generates an
inherited covering sieve upstairs. -/
theorem stronglyCartesianFamily_mem_inheritedTopology_of_baseCover
    {ι : Type (max u₁ v₁)} {y : Yₛ.S} (Y : ι → Yₛ.S) (g : ∀ i, Y i ⟶ y)
    (hgstrong : ∀ i, Yₛ.p.IsStronglyCartesian (Yₛ.p.map (g i)) (g i))
    (hbaseCover :
      Sieve.ofArrows (fun i ↦ Yₛ.p.obj (Y i)) (fun i ↦ Yₛ.p.map (g i)) ∈
        J (Yₛ.p.obj y)) :
    Sieve.ofArrows Y g ∈ inheritedTopology J Yₛ y := by
  have hbasePrecover :
      Presieve.ofArrows (fun i ↦ Yₛ.p.obj (Y i)) (fun i ↦ Yₛ.p.map (g i)) ∈
        J.toPrecoverage (Yₛ.p.obj y) := by
    -- Move the base covering sieve to the precoverage owner used by the inherited generators.
    rw [GrothendieckTopology.mem_toPrecoverage_iff]
    simpa [Sieve.ofArrows] using hbaseCover
  -- Route correction: use only the first-half `ProjectionSite` construction here; importing that
  -- file would also import its still-broken later generated-precoverage proof.
  rw [inheritedTopology]
  have hcover :
      Presieve.ofArrows Y g ∈ stronglyCartesianLiftPrecoverage J.toPrecoverage Yₛ.p y := by
    -- The lifted family is strongly cartesian and its projected family is the given base cover.
    exact
      (ofArrows_mem_stronglyCartesianLiftPrecoverage_iff
        (J := J.toPrecoverage) (p := Yₛ.p) Y g).2
        ⟨hgstrong, hbasePrecover⟩
  simpa [Sieve.ofArrows] using
    (Precoverage.generate_mem_toGrothendieck
      (J := stronglyCartesianLiftPrecoverage J.toPrecoverage Yₛ.p)
      (R := Presieve.ofArrows Y g) hcover)

/-- Helper for Lemma 8.11.3: a base cover pulls back to an inherited cover on the target total
category. -/
theorem baseCover_liftedPullbackCover_mem_inheritedTopology
    {y : Yₛ.S} (S : J.Cover (Yₛ.p.obj y)) :
    ((S : Sieve (Yₛ.p.obj y)).functorPullback Yₛ.p) ∈ inheritedTopology J Yₛ y := by
  obtain ⟨ι, U, f, hS_eq⟩ := (S : Sieve (Yₛ.p.obj y)).exists_eq_ofArrows
  rw [hS_eq]
  let yFiber : Yₛ.p.Fiber (Yₛ.p.obj y) := ⟨y, rfl⟩
  let Y : ι → Yₛ.S := fun i ↦ (f i ^*[canonicalPullbackChoice Yₛ.p] yFiber).1
  let g : ∀ i, Y i ⟶ y := fun i ↦ (canonicalPullbackChoice Yₛ.p).map (f i) yFiber
  have hgstrong : ∀ i, Yₛ.p.IsStronglyCartesian (Yₛ.p.map (g i)) (g i) := by
    -- Chosen cartesian lifts give the strongly cartesian family above the base cover.
    intro i
    infer_instance
  have hgi :
      ∀ i, Yₛ.p.map (g i) =
        eqToHom ((f i ^*[canonicalPullbackChoice Yₛ.p] yFiber).2) ≫ f i := by
    intro i
    letI : Yₛ.p.IsHomLift (f i) (g i) := by
      simpa [g] using
        (show Yₛ.p.IsHomLift (f i) ((canonicalPullbackChoice Yₛ.p).map (f i) yFiber) from
          by
            let _ :
                Yₛ.p.IsStronglyCartesian (f i) ((canonicalPullbackChoice Yₛ.p).map (f i) yFiber) :=
              (canonicalPullbackChoice Yₛ.p).isStronglyCartesian (f i) yFiber
            infer_instance)
    -- Record the base map of each chosen lift in the canonical `eqToHom ≫ f i` form.
    simpa [Y, g] using (IsHomLift.fac' Yₛ.p (f i) (g i))
  have hbaseCover :
      Sieve.ofArrows (fun i ↦ Yₛ.p.obj (Y i)) (fun i ↦ Yₛ.p.map (g i)) ∈
        J (Yₛ.p.obj y) := by
    refine J.superset_covering
      (S := Sieve.ofArrows U f)
      ?_ ?_
    · rw [Sieve.generate_le_iff]
      intro Z k hk
      rcases hk with ⟨i⟩
      rw [Sieve.mem_ofArrows_iff]
      refine ⟨i, eqToHom ((f i ^*[canonicalPullbackChoice Yₛ.p] yFiber).2).symm, ?_⟩
      simpa [Category.assoc] using
        (congrArg
          (eqToHom ((f i ^*[canonicalPullbackChoice Yₛ.p] yFiber).2).symm ≫ ·)
          (hgi i)).symm
    · have hS_condition :
          Sieve.ofArrows U f ∈ J (Yₛ.p.obj y) := by
        simpa [hS_eq] using S.condition
      exact hS_condition
  have hfamily :
      Sieve.ofArrows Y g ∈ inheritedTopology J Yₛ y :=
    stronglyCartesianFamily_mem_inheritedTopology_of_baseCover
      (J := J) (Yₛ := Yₛ) Y g hgstrong hbaseCover
  refine (inheritedTopology J Yₛ).superset_covering ?_ hfamily
  rw [Sieve.generate_le_iff]
  intro Z k hk
  rcases hk with ⟨i⟩
  change (Sieve.ofArrows U f) (Yₛ.p.map (g i))
  rw [Sieve.mem_ofArrows_iff]
  refine ⟨i, eqToHom ((f i ^*[canonicalPullbackChoice Yₛ.p] yFiber).2), ?_⟩
  -- The represented family of chosen lifts is contained in the literal functor pullback sieve.
  simpa using hgi i

/-- Helper for Lemma 8.11.3: the projection from the inherited target site to the base site is
cocontinuous. -/
instance targetProjection_isCocontinuous_inheritedTopology :
    Yₛ.p.IsCocontinuous (inheritedTopology J Yₛ) J where
  cover_lift {U} {S} hS :=
    baseCover_liftedPullbackCover_mem_inheritedTopology (J := J) (Yₛ := Yₛ) (y := U) ⟨S, hS⟩

/-- Helper for Lemma 8.11.3: the target projection preserves pullbacks along arbitrary arrows. -/
theorem targetProjection_preservesPullback_of_arrow
    {y z t : Yₛ.S} (i : z ⟶ y) (f : t ⟶ y)
    [Limits.HasPullback f i] :
    Limits.PreservesLimit (Limits.cospan f i) Yₛ.p := by
  have hiStrong : Yₛ.p.IsStronglyCartesian (Yₛ.p.map i) i := by
    infer_instance
  -- A pullback square in the total category maps to a base pullback because the right leg is
  -- strongly cartesian.
  exact
    Limits.preservesLimit_of_preserves_limit_cone
      (IsPullback.of_hasPullback f i).isLimit <| by
        apply (Limits.isLimitMapConePullbackConeEquiv Yₛ.p Limits.pullback.condition).symm.toFun
        exact
          (mapped_square_isPullback_of_isPullback_of_isStronglyCartesian
            (p := Yₛ.p) (hφ := hiStrong) (h := IsPullback.of_hasPullback f i)).isLimit

/-- Helper for Lemma 8.11.3: inherited covering presieves for the target projection project to
covering presieves on the base site. -/
theorem targetProjection_toLeComap_inheritedTopology :
    (inheritedTopology J Yₛ).toPrecoverage ≤ J.toPrecoverage.comap Yₛ.p := by
  intro y R hR
  obtain ⟨ι, Y, g, rfl⟩ := R.exists_eq_ofArrows
  let S : CategoryTheory.SemiRepresentableFamily.Over y :=
    CategoryTheory.SemiRepresentableFamily.Over.ofArrows Y g
  have hS :
      Presieve.ofArrows (fun i ↦ (S.obj i).left) (fun i ↦ (S.obj i).hom) ∈
        ((stronglyCartesianLiftPrecoverage J.toPrecoverage Yₛ.p).toGrothendieck.toPrecoverage)
          y := by
    -- Repackage the inherited precover as its represented family.
    simpa [S, CategoryTheory.SemiRepresentableFamily.Over.ofArrows] using hR
  have hImage :
      Presieve.ofArrows (fun i ↦ Yₛ.p.obj ((S.obj i).left))
          (fun i ↦ Yₛ.p.map ((S.obj i).hom)) ∈
        J.toPrecoverage (Yₛ.p.obj y) :=
    FibredCategoryOver.image_family_isCovering_of_inherited_family_covering
      (J := J) (X := Yₛ) S hS
  rw [Precoverage.mem_comap_iff]
  simpa [S, CategoryTheory.SemiRepresentableFamily.Over.ofArrows, Presieve.map_ofArrows] using
    hImage

/-- Helper for Lemma 8.11.3: the pullback-preservation field for continuity of the inherited
target projection is independent of the selected cover arrow. -/
theorem targetProjection_preservesPullback_inheritedTopology
    {V : Yₛ.S} {R : Presieve V}
    (_hR : R ∈ (inheritedTopology J Yₛ).toPrecoverage V)
    {Y : Yₛ.S} {i : Y ⟶ V} (_hi : R i)
    {T : Yₛ.S} (f : T ⟶ V) [Limits.HasPullback f i] :
    Limits.PreservesLimit (Limits.cospan f i) Yₛ.p :=
  by
    simpa [StackInGroupoidsOver.p, StackInGroupoidsOver.toFibredCategoryOver,
      FibredInGroupoidsOver.p] using
      (targetProjection_preservesPullback_of_arrow (J := J) (Yₛ := Yₛ) i f)

/-- Helper for Lemma 8.11.3: the target projection is continuous from the inherited topology to
the original base topology. -/
instance targetProjection_isContinuousSiteFunctor_inheritedTopology :
    Functor.IsContinuousSiteFunctor Yₛ.p
      (inheritedTopology J Yₛ).toPrecoverage J.toPrecoverage where
  toLeComap := targetProjection_toLeComap_inheritedTopology (J := J) (Yₛ := Yₛ)
  preservesPullback :=
    targetProjection_preservesPullback_inheritedTopology (J := J) (Yₛ := Yₛ)

/-- Helper for Lemma 8.11.3: the canonical arrow family of an inherited cover projects to a
covering family in the base topology. -/
theorem inheritedCover_arrowFamily_baseCovering
    {y : Yₛ.S} (T : (inheritedTopology J Yₛ).Cover y) :
    Sieve.ofArrows (fun I : T.Arrow ↦ Yₛ.p.obj I.Y) (fun I ↦ Yₛ.p.map I.f) ∈
      J (Yₛ.p.obj y) := by
  have hpre :
      Presieve.ofArrows (fun I : T.Arrow ↦ I.Y) (fun I ↦ I.f) ∈
        (inheritedTopology J Yₛ).toPrecoverage y := by
    rw [GrothendieckTopology.mem_toPrecoverage_iff]
    change Sieve.ofArrows (fun I : T.Arrow ↦ I.Y) (fun I ↦ I.f) ∈ inheritedTopology J Yₛ y
    simpa using (GrothendieckTopology.Cover.ofArrows_eq T).symm ▸ T.condition
  have hmap :
      (Presieve.ofArrows (fun I : T.Arrow ↦ I.Y) (fun I ↦ I.f)).map Yₛ.p ∈
        J.toPrecoverage (Yₛ.p.obj y) :=
    targetProjection_toLeComap_inheritedTopology (J := J) (Yₛ := Yₛ) y hpre
  rw [GrothendieckTopology.mem_toPrecoverage_iff] at hmap
  simpa [Presieve.map_ofArrows, Sieve.ofArrows] using hmap

/-- Helper for Lemma 8.11.3: an arrow of a cover transported along an equality gives an arrow
of the original cover after postcomposing with the inverse equality arrow. -/
theorem coverCast_arrow_mem_original
    {A B : C} (h : A = B) (S : J.Cover A)
    (I : (h ▸ S : J.Cover B).Arrow) :
    (S : Sieve A) (I.f ≫ eqToHom h.symm) := by
  -- Prove the transport formula once in a context with no dependent source-fiber data.
  cases h
  simpa using I.hf

end

end StackInGroupoidsOver.Hom

end CategoryTheory
