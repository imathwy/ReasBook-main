import stacks_project.Chap10.Lemma_10_127_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

open Polynomial

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Helper for Lemma 10.127.15: throughout this file we view `S` as an `R`-algebra via the
ambient ring map `f`. -/
private noncomputable instance instAlgebraOfRingHom (f : R →+* S) : Algebra R S :=
  f.toAlgebra

/-- Helper for Lemma 10.127.15: a compatible family of stage maps is surjective on the direct
limit once every ambient element already appears on some stage. -/
private theorem directLimit_lift_surjective_of_stagewise_cover
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {A : ι → Type*} [∀ i, CommRing (A i)]
    {map : ∀ i j, i ≤ j → A i →+* A j}
    [DirectedSystem A (fun i j h ↦ map i j h)]
    {B : Type*} [CommRing B]
    (g : ∀ i, A i →+* B)
    (hg : ∀ i j hij x, g j (map i j hij x) = g i x)
    (hcover : ∀ b : B, ∃ i x, g i x = b) :
    Function.Surjective (Ring.DirectLimit.lift A (fun i j h ↦ map i j h) B g hg) := by
  intro b
  -- Represent the ambient element by one stage element and then evaluate the universal lift.
  rcases hcover b with ⟨i, x, rfl⟩
  refine ⟨Ring.DirectLimit.of A (fun i j h ↦ map i j h) i x, ?_⟩
  simp [Ring.DirectLimit.lift_of]

/-- Helper for Lemma 10.127.15: stagewise injectivity together with stagewise cover makes the
ambient comparison map from the direct limit bijective. -/
private theorem directLimit_lift_bijective_of_stagewise_injective_cover
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {A : ι → Type*} [∀ i, CommRing (A i)]
    {map : ∀ i j, i ≤ j → A i →+* A j}
    [DirectedSystem A (fun i j h ↦ map i j h)]
    {B : Type*} [CommRing B]
    (g : ∀ i, A i →+* B)
    (hg : ∀ i j hij x, g j (map i j hij x) = g i x)
    (hinj : ∀ i, Function.Injective (g i))
    (hcover : ∀ b : B, ∃ i x, g i x = b) :
    Function.Bijective (Ring.DirectLimit.lift A (fun i j h ↦ map i j h) B g hg) := by
  refine ⟨?_, ?_⟩
  · -- Injectivity is the standard direct-limit criterion for stagewise injective maps.
    exact Ring.DirectLimit.lift_injective
      (G := A)
      (f := fun i j hij ↦ map i j hij)
      (P := B)
      (g := g)
      (Hg := hg)
      hinj
  · -- Surjectivity comes from the cover hypothesis proved above.
    exact directLimit_lift_surjective_of_stagewise_cover g hg hcover

/- 
Domain sampling:
* Primary domain: directed approximation systems for commutative ring homomorphisms.
* Owner declarations inspected in this domain:
  - `DirectedFiniteTypeHomApproximation`
  - `RingHom.Finite`
  - `RingHom.Finite.to_finiteType`
  - `finite_tfae_isIntegral_finiteType_exists_integral_generators`
* Best owner abstraction: `DirectedFiniteTypeHomApproximation f`.
* Layer targeted here: `bridge/view`. The source-facing content of this item is not a new
  approximation owner, but the stronger stagewise finiteness property on the existing owner.
* Primitive vs. derived: the directed index set, stage rings, transition maps, colimit
  identifications, and stagewise finite-type hypotheses already belong to
  `DirectedFiniteTypeHomApproximation`; this lemma adds only the stronger condition that each stage
  map is finite.
-/

/-- Helper for Lemma 10.127.15: an index records finitely many source elements, finitely many
target generators, and integrality of each chosen target generator over the corresponding source
stage. -/
private structure IntegralStageIndex (f : R →+* S) where
  source : Finset R
  target : Finset S
  integral_target :
    ∀ x ∈ (target : Set S),
      (f.comp (Algebra.adjoin ℤ (source : Set R)).val.toRingHom).IsIntegralElem x

namespace IntegralStageIndex

variable {f : R →+* S}

instance : LE (IntegralStageIndex f) where
  le i j := i.source ⊆ j.source ∧ i.target ⊆ j.target

instance : Preorder (IntegralStageIndex f) where
  le_refl i := ⟨by intro x hx; exact hx, by intro x hx; exact hx⟩
  le_trans i j k hij hjk := ⟨hij.1.trans hjk.1, hij.2.trans hjk.2⟩

/-- Helper for Lemma 10.127.15: the empty source and target data define a trivial index. -/
private instance : Nonempty (IntegralStageIndex f) :=
  ⟨{ source := ∅
     target := ∅
     integral_target := by
       intro x hx
       simpa using hx }⟩

/-- Helper for Lemma 10.127.15: enlarging the chosen source generators preserves integrality of a
target generator. -/
private theorem isIntegral_mono_source
    {si sj : Finset R} (hij : si ⊆ sj) {x : S}
    (hx : (f.comp (Algebra.adjoin ℤ (si : Set R)).val.toRingHom).IsIntegralElem x) :
    (f.comp (Algebra.adjoin ℤ (sj : Set R)).val.toRingHom).IsIntegralElem x := by
  let inc :
      Algebra.adjoin ℤ (si : Set R) →+* Algebra.adjoin ℤ (sj : Set R) :=
    (Subalgebra.inclusion (Algebra.adjoin_mono hij)).toRingHom
  rcases hx with ⟨p, hp, hpx⟩
  refine ⟨p.map inc, hp.map inc, ?_⟩
  -- Map the integral equation along the source-stage inclusion.
  rw [Polynomial.eval₂_map]
  simpa [inc, RingHom.comp_assoc] using hpx

/-- Helper for Lemma 10.127.15: the index set is directed by taking unions of the finite source
and target data. -/
private instance : IsDirectedOrder (IntegralStageIndex f) := by
  classical
  refine ⟨?_⟩
  intro i j
  refine ⟨
    { source := i.source ∪ j.source
      target := i.target ∪ j.target
      integral_target := ?_ },
    ?_,
    ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · -- Elements already integral over the left stage remain integral over the union stage.
      exact isIntegral_mono_source (f := f) (si := i.source) (sj := i.source ∪ j.source)
        Finset.subset_union_left (i.integral_target x hx)
    · -- The same holds for elements coming from the right stage.
      exact isIntegral_mono_source (f := f) (si := j.source) (sj := i.source ∪ j.source)
        Finset.subset_union_right (j.integral_target x hx)
  · refine ⟨?_, ?_⟩
    · intro x hx
      exact Finset.mem_union.mpr <| Or.inl hx
    · intro x hx
      exact Finset.mem_union.mpr <| Or.inl hx
  · refine ⟨?_, ?_⟩
    · intro x hx
      exact Finset.mem_union.mpr <| Or.inr hx
    · intro x hx
      exact Finset.mem_union.mpr <| Or.inr hx

end IntegralStageIndex

namespace IntegralStageData

variable (f : R →+* S)

/-- Helper for Lemma 10.127.15: the source stage is the `ℤ`-subalgebra generated by the chosen
finite source set. -/
private abbrev sourceStage (i : IntegralStageIndex f) : Subalgebra ℤ R :=
  Algebra.adjoin ℤ (i.source : Set R)

/-- Helper for Lemma 10.127.15: the ambient map from a source stage to `S` is induced by `f`. -/
private abbrev sourceStageToTargetAmbient (i : IntegralStageIndex f) :
    sourceStage f i →+* S :=
  f.comp (sourceStage f i).val.toRingHom

/-- Helper for Lemma 10.127.15: each source stage inherits its ambient `S`-algebra structure from
`f`. -/
private noncomputable instance instAlgebraSourceStage (i : IntegralStageIndex f) :
    Algebra (sourceStage f i) S :=
  (sourceStageToTargetAmbient f i).toAlgebra

/-- Helper for Lemma 10.127.15: the target stage is generated over the source stage by the chosen
finite target set, then viewed again as a `ℤ`-subalgebra of `S`. -/
private abbrev targetStage (i : IntegralStageIndex f) : Subalgebra ℤ S :=
  let _ : Algebra (sourceStage f i) S := (sourceStageToTargetAmbient f i).toAlgebra
  (Algebra.adjoin (sourceStage f i) (i.target : Set S)).restrictScalars ℤ

/-- Helper for Lemma 10.127.15: the source stages form a monotone family under coordinatewise
enlargement of the source finsets. -/
private theorem sourceStage_mono {i j : IntegralStageIndex f} (hij : i ≤ j) :
    sourceStage f i ≤ sourceStage f j :=
  Algebra.adjoin_mono hij.1

/-- Helper for Lemma 10.127.15: the image of a smaller source stage inside `S` is contained in the
image of any larger source stage. -/
private theorem sourceStageRange_mono {i j : IntegralStageIndex f} (hij : i ≤ j) :
    ((IsScalarTower.toAlgHom ℤ (sourceStage f i) S).range : Set S) ⊆
      ((IsScalarTower.toAlgHom ℤ (sourceStage f j) S).range : Set S) := by
  rintro x ⟨y, rfl⟩
  -- Reuse the canonical inclusion of the smaller source stage into the larger one.
  exact ⟨Subalgebra.inclusion (sourceStage_mono (f := f) hij) y, rfl⟩

/-- Helper for Lemma 10.127.15: after restricting scalars back to `ℤ`, the target stage is the
`ℤ`-subalgebra generated by the source-stage image in `S` together with the chosen target set. -/
private theorem targetStage_eq_adjoin_union (i : IntegralStageIndex f) :
    targetStage f i =
      Algebra.adjoin ℤ
        (((IsScalarTower.toAlgHom ℤ (sourceStage f i) S).range : Set S) ∪ (i.target : Set S)) := by
  let _ : Algebra (sourceStage f i) S := (sourceStageToTargetAmbient f i).toAlgebra
  have hrange :
      targetStage f i =
        (Algebra.adjoin
          (IsScalarTower.toAlgHom ℤ (sourceStage f i) S).range
          (i.target : Set S)).restrictScalars ℤ := by
    -- Route correction: rewrite through the image subalgebra in `S`, not through the source stage
    -- viewed as a subset of `R`.
    simpa [targetStage] using
      (IsScalarTower.adjoin_range_toAlgHom
        (R := ℤ) (S := sourceStage f i) (A := S) (t := (i.target : Set S))).symm
  rw [hrange, Algebra.restrictScalars_adjoin]

/-- Helper for Lemma 10.127.15: the target stages are monotone under enlargement of both source
and target data. -/
private theorem targetStage_mono {i j : IntegralStageIndex f} (hij : i ≤ j) :
    targetStage f i ≤ targetStage f j := by
  -- Rewrite both stages in terms of the ambient `ℤ`-subalgebras and apply monotonicity of adjoin.
  rw [targetStage_eq_adjoin_union (f := f) i, targetStage_eq_adjoin_union (f := f) j]
  refine Algebra.adjoin_mono ?_
  exact Set.union_subset
    (fun x hx ↦ Or.inl <| sourceStageRange_mono (f := f) hij hx)
    (fun x hx ↦ Or.inr <| hij.2 hx)

/-- Helper for Lemma 10.127.15: the transition maps on source stages are the obvious inclusions. -/
private abbrev sourceTransition {i j : IntegralStageIndex f} (hij : i ≤ j) :
    sourceStage f i →+* sourceStage f j :=
  Subalgebra.inclusion (sourceStage_mono (f := f) hij)

/-- Helper for Lemma 10.127.15: the transition maps on target stages are the obvious inclusions. -/
private abbrev targetTransition {i j : IntegralStageIndex f} (hij : i ≤ j) :
    targetStage f i →+* targetStage f j :=
  Subalgebra.inclusion (targetStage_mono (f := f) hij)

/-- Helper for Lemma 10.127.15: the source stage maps form a directed system because inclusions of
subalgebras compose strictly. -/
private instance sourceDirectedSystem :
    DirectedSystem
      (fun i : IntegralStageIndex f ↦ sourceStage f i)
      (fun i j hij ↦ sourceTransition (f := f) (i := i) (j := j) hij) := by
  refine ⟨?_, ?_⟩
  · intro i x
    rfl
  · intro k j i hij hjk x
    -- Composition of source-stage inclusions is the canonical inclusion to the top stage.
    simpa using
      (Subalgebra.inclusion_inclusion
        (sourceStage_mono (f := f) hij)
        (sourceStage_mono (f := f) hjk)
        x)

/-- Helper for Lemma 10.127.15: the target stage maps form a directed system because inclusions of
subalgebras compose strictly. -/
private instance targetDirectedSystem :
    DirectedSystem
      (fun i : IntegralStageIndex f ↦ targetStage f i)
      (fun i j hij ↦ targetTransition (f := f) (i := i) (j := j) hij) := by
  refine ⟨?_, ?_⟩
  · intro i x
    rfl
  · intro k j i hij hjk x
    -- Composition of target-stage inclusions is again the canonical inclusion.
    simpa using
      (Subalgebra.inclusion_inclusion
        (targetStage_mono (f := f) hij)
        (targetStage_mono (f := f) hjk)
        x)

/-- Helper for Lemma 10.127.15: each stage map is the algebra map from the source stage into the
corresponding target stage. -/
private abbrev stageMap (i : IntegralStageIndex f) :
    sourceStage f i →+* targetStage f i :=
  let _ : Algebra (sourceStage f i) S := (sourceStageToTargetAmbient f i).toAlgebra
  algebraMap (sourceStage f i) (Algebra.adjoin (sourceStage f i) (i.target : Set S))

/-- Helper for Lemma 10.127.15: the ambient source-stage inclusions are pointwise compatible with
the source transition maps. -/
private theorem sourceStageToAmbient_compatible {i j : IntegralStageIndex f} (hij : i ≤ j)
    (x : sourceStage f i) :
    (sourceStage f j).val.toRingHom
        (sourceTransition (f := f) (i := i) (j := j) hij x) =
      (sourceStage f i).val.toRingHom x := by
  -- The source transition is just the subtype inclusion between nested source subalgebras.
  change ((sourceTransition (f := f) (i := i) (j := j) hij x : sourceStage f j) : R) = (x : R)
  rfl

/-- Helper for Lemma 10.127.15: the ambient target-stage inclusions are pointwise compatible with
the target transition maps. -/
private theorem targetStageToAmbient_compatible {i j : IntegralStageIndex f} (hij : i ≤ j)
    (x : targetStage f i) :
    (targetStage f j).val.toRingHom
        (targetTransition (f := f) (i := i) (j := j) hij x) =
      (targetStage f i).val.toRingHom x := by
  -- The target transition is likewise the subtype inclusion between nested target subalgebras.
  change ((targetTransition (f := f) (i := i) (j := j) hij x : targetStage f j) : S) = (x : S)
  rfl

/-- Helper for Lemma 10.127.15: after mapping a stage to the ambient target ring, the stage map is
the original ambient ring map `f` restricted to the source stage. -/
private theorem stage_to_ambient_commutes (i : IntegralStageIndex f) :
    (targetStage f i).val.toRingHom.comp (stageMap f i) =
      f.comp (sourceStage f i).val.toRingHom := by
  -- The stage map is the ambient algebra map into the target-stage subalgebra.
  ext x
  rfl

/-- Helper for Lemma 10.127.15: each chosen target generator is integral over its source stage by
construction of the index. -/
private theorem chosen_target_isIntegral (i : IntegralStageIndex f) {x : S}
    (hx : x ∈ (i.target : Set S)) : IsIntegral (sourceStage f i) x := by
  -- Reinterpret the stored ring-hom integrality statement as the usual algebra integrality.
  simpa [IsIntegral, sourceStageToTargetAmbient, RingHom.algebraMap_toAlgebra] using
    (i.integral_target x hx)

/-- Helper for Lemma 10.127.15: the stage map is finite because the target stage is generated by a
finite set of elements integral over the source stage. -/
private theorem stageMap_finite (i : IntegralStageIndex f) : RingHom.Finite (stageMap f i) := by
  let _ : Algebra (sourceStage f i) S := (sourceStageToTargetAmbient f i).toAlgebra
  -- View the target stage as the adjoin of the finite target set over the source stage.
  change RingHom.Finite (algebraMap (sourceStage f i)
    (Algebra.adjoin (sourceStage f i) (i.target : Set S)))
  rw [RingHom.finite_algebraMap]
  -- Apply the finite-adjoin theorem to the finitely many integral generators.
  exact Algebra.finite_adjoin_of_finite_of_isIntegral i.target.finite_toSet
    (fun x hx ↦ chosen_target_isIntegral (f := f) i hx)

/-- Helper for Lemma 10.127.15: the stage map is of finite type because finite maps are of finite
type. -/
private theorem stageMap_finiteType (i : IntegralStageIndex f) :
    RingHom.FiniteType (stageMap f i) :=
  (stageMap_finite (f := f) i).to_finiteType

/-- Helper for Lemma 10.127.15: each source stage is of finite type over `ℤ` because it is
generated by a finite set. -/
private theorem sourceStage_finiteType (i : IntegralStageIndex f) :
    (Int.castRingHom (sourceStage f i)).FiniteType := by
  exact RingHom.finiteType_algebraMap.mpr <|
    by
      simpa [sourceStage] using
        (Algebra.FiniteType.adjoin_of_finite (R := ℤ) (A := R) (t := (i.source : Set R))
          i.source.finite_toSet)

/-- Helper for Lemma 10.127.15: the stage square commutes because all maps are induced by ambient
subalgebra inclusions. -/
private theorem stage_square_left_to_ambient_apply {i j : IntegralStageIndex f} (hij : i ≤ j)
    (x : sourceStage f i) :
    (targetStage f j).val.toRingHom
        ((stageMap f j) (sourceTransition (f := f) (i := i) (j := j) hij x)) =
      f ((sourceStage f i).val.toRingHom x) := by
  -- First evaluate the stage-`j` square in the ambient ring `S`.
  have hstage :
      ((targetStage f j).val.toRingHom.comp (stageMap f j))
          (sourceTransition (f := f) (i := i) (j := j) hij x) =
        (f.comp (sourceStage f j).val.toRingHom)
          (sourceTransition (f := f) (i := i) (j := j) hij x) := by
    simpa using
      congrArg
        (fun g : sourceStage f j →+* S =>
          g (sourceTransition (f := f) (i := i) (j := j) hij x))
        (stage_to_ambient_commutes (f := f) j)
  -- Then rewrite the source-stage inclusion back to the original element of `R`.
  calc
    (targetStage f j).val.toRingHom
        ((stageMap f j) (sourceTransition (f := f) (i := i) (j := j) hij x)) =
      (f.comp (sourceStage f j).val.toRingHom)
        (sourceTransition (f := f) (i := i) (j := j) hij x) := by
          simpa [RingHom.comp_apply] using hstage
    _ = f ((sourceStage f i).val.toRingHom x) := by
      rw [RingHom.comp_apply,
        sourceStageToAmbient_compatible (f := f) (i := i) (j := j) hij x]

/-- Helper for Lemma 10.127.15: the right path around the stage square has the expected ambient
value on each source-stage element. -/
private theorem stage_square_right_to_ambient_apply {i j : IntegralStageIndex f} (hij : i ≤ j)
    (x : sourceStage f i) :
    (targetStage f j).val.toRingHom
        ((targetTransition (f := f) (i := i) (j := j) hij) ((stageMap f i) x)) =
      f ((sourceStage f i).val.toRingHom x) := by
  -- First rewrite the target transition as the ambient inclusion on target stages.
  calc
    (targetStage f j).val.toRingHom
        ((targetTransition (f := f) (i := i) (j := j) hij) ((stageMap f i) x)) =
      (targetStage f i).val.toRingHom ((stageMap f i) x) := by
          simpa using
            targetStageToAmbient_compatible (f := f) (i := i) (j := j) hij ((stageMap f i) x)
    _ = f ((sourceStage f i).val.toRingHom x) := by
      -- Now evaluate the stage-`i` square in the ambient ring `S`.
      simpa [RingHom.comp_apply] using
        congrArg
          (fun g : sourceStage f i →+* S => g x)
          (stage_to_ambient_commutes (f := f) i)

/-- Helper for Lemma 10.127.15: the stage square commutes because both composites have the same
ambient value on every source-stage element. -/
private theorem stage_square_commutes {i j : IntegralStageIndex f} (hij : i ≤ j) :
    (stageMap f j).comp (sourceTransition (f := f) (i := i) (j := j) hij) =
      (targetTransition (f := f) (i := i) (j := j) hij).comp (stageMap f i) := by
  -- Route correction: compare both composites only after evaluating in the ambient ring `S`.
  ext x
  have hleft :
      (targetStage f j).val.toRingHom
          (((stageMap f j).comp (sourceTransition (f := f) (i := i) (j := j) hij)) x) =
        f ((sourceStage f i).val.toRingHom x) := by
    simpa [RingHom.comp_apply] using
      stage_square_left_to_ambient_apply (f := f) (i := i) (j := j) hij x
  have hright :
      f ((sourceStage f i).val.toRingHom x) =
        (targetStage f j).val.toRingHom
          (((targetTransition (f := f) (i := i) (j := j) hij).comp (stageMap f i)) x) := by
    simpa [RingHom.comp_apply] using
      (stage_square_right_to_ambient_apply (f := f) (i := i) (j := j) hij x).symm
  -- Both composites evaluate to the same ambient element `f x`.
  exact hleft.trans hright

/-- Helper for Lemma 10.127.15: every element of `R` already occurs on a singleton source stage. -/
private theorem source_stage_cover (r : R) :
    ∃ i : IntegralStageIndex f, r ∈ sourceStage f i := by
  classical
  refine ⟨{ source := {r}, target := ∅, integral_target := ?_ }, ?_⟩
  · intro x hx
    simpa using hx
  · exact Algebra.subset_adjoin (by simp)

/-- Helper for Lemma 10.127.15: every coefficient of a polynomial lies in the source stage
generated by its coefficient list. -/
private theorem coeff_mem_sourceStage (p : R[X]) (n : ℕ) :
    p.coeff n ∈ Algebra.adjoin ℤ ((p.coeffs : Finset R) : Set R) := by
  classical
  by_cases hzero : p.coeff n = 0
  · simpa [hzero]
  · exact Algebra.subset_adjoin (by
      exact Polynomial.coeff_mem_coeffs hzero)

/-- Helper for Lemma 10.127.15: a single monic integral equation over `R` already has all its
coefficients in the coefficient source stage, so it witnesses integrality over that stage. -/
private theorem integral_over_coeff_source_stage {s : S}
    (hs : f.IsIntegralElem s) :
    RingHom.IsIntegralElem
      (f.comp (Algebra.adjoin ℤ (((Classical.choose hs) : R[X]).coeffs : Set R)).val.toRingHom)
      s := by
  classical
  let p : R[X] := Classical.choose hs
  let A : Subalgebra ℤ R := Algebra.adjoin ℤ (p.coeffs : Set R)
  have hpmonic : p.Monic := (Classical.choose_spec hs).1
  have hpeval : Polynomial.eval₂ f s p = 0 := (Classical.choose_spec hs).2
  have hp_lifts : p ∈ Polynomial.lifts A.val.toRingHom := by
    -- Every coefficient of the chosen monic equation already lies in the adjoined coefficient
    -- stage, so the whole polynomial lifts along the subtype map.
    refine (Polynomial.lifts_iff_coeffs_subset_range (f := A.val.toRingHom) p).2 ?_
    intro x hx
    exact ⟨⟨x, Algebra.subset_adjoin hx⟩, rfl⟩
  rcases (Polynomial.mem_lifts (f := A.val.toRingHom) p).1 hp_lifts with ⟨q, hqmap⟩
  refine ⟨q, ?_, ?_⟩
  · -- Monicity descends through the injective subtype map from the coefficient stage into `R`.
    have hqmap_monic : (Polynomial.map A.val.toRingHom q).Monic := by
      rw [hqmap]
      exact hpmonic
    refine Polynomial.monic_of_injective (f := A.val.toRingHom) Subtype.val_injective ?_
    exact hqmap_monic
  · -- Rewriting the chosen equation through the lifted polynomial gives the desired integral
    -- equation over the coefficient stage.
    have hqeval : Polynomial.eval₂ f s (Polynomial.map A.val.toRingHom q) = 0 := by
      rw [hqmap]
      exact hpeval
    simpa [A, p, Polynomial.eval₂_map] using hqeval

/-- Helper for Lemma 10.127.15: every element of `S` appears on a singleton target stage built
from one monic integral equation over `R`. -/
private theorem target_stage_cover (hInt : f.IsIntegral) (s : S) :
    ∃ i : IntegralStageIndex f, s ∈ targetStage f i := by
  classical
  let p : R[X] := Classical.choose (hInt s)
  let i : IntegralStageIndex f :=
    { source := p.coeffs
      target := {s}
      integral_target := by
        intro x hx
        have hx' : x = s := by simpa using hx
        cases hx'
        exact integral_over_coeff_source_stage (f := f) (hInt s) }
  refine ⟨i, ?_⟩
  -- The chosen target element is one of the adjoined generators at this stage.
  let _ : Algebra (sourceStage f i) S := (sourceStageToTargetAmbient f i).toAlgebra
  simpa [i, targetStage] using
    (Algebra.subset_adjoin (R := sourceStage f i) (x := s) (Set.mem_singleton s))

/-- Helper for Lemma 10.127.15: the canonical source-stage inclusion into `R` is the ambient map
used to compare the source direct limit with `R`. -/
private abbrev sourceStageToAmbient (i : IntegralStageIndex f) : sourceStage f i →+* R :=
  (sourceStage f i).val.toRingHom

/-- Helper for Lemma 10.127.15: the canonical target-stage inclusion into `S` is the ambient map
used to compare the target direct limit with `S`. -/
private abbrev targetStageToAmbient (i : IntegralStageIndex f) : targetStage f i →+* S :=
  (targetStage f i).val.toRingHom

/-- Helper for Lemma 10.127.15: the source direct-limit comparison map is the lift of the ambient
stage inclusions. -/
-- TODO: package the ambient subtype maps with `Ring.DirectLimit.lift` using the stabilized source
-- directed system once the kernel no longer times out on this direct-limit term.
private noncomputable def sourceColimitToAmbient :
    Ring.DirectLimit
        (fun i : IntegralStageIndex f ↦ sourceStage f i)
        (fun i j hij ↦ sourceTransition (f := f) (i := i) (j := j) hij) →+* R :=
  -- Package the compatible ambient source-stage inclusions into the universal direct-limit map.
  Ring.DirectLimit.lift
    (fun i : IntegralStageIndex f ↦ sourceStage f i)
    (fun i j hij ↦ sourceTransition (f := f) (i := i) (j := j) hij)
    R
    (fun i ↦ sourceStageToAmbient (f := f) i)
    (fun i j hij x ↦ sourceStageToAmbient_compatible (f := f) (i := i) (j := j) hij x)

/-- Helper for Lemma 10.127.15: the target direct-limit comparison map is the lift of the ambient
stage inclusions. -/
-- TODO: define the target direct-limit comparison by the same universal-property lift once the
-- target-side direct-limit term is in a kernel-stable normal form.
private noncomputable def targetColimitToAmbient :
    Ring.DirectLimit
        (fun i : IntegralStageIndex f ↦ targetStage f i)
        (fun i j hij ↦ targetTransition (f := f) (i := i) (j := j) hij) →+* S :=
  -- Package the compatible ambient target-stage inclusions into the universal direct-limit map.
  Ring.DirectLimit.lift
    (fun i : IntegralStageIndex f ↦ targetStage f i)
    (fun i j hij ↦ targetTransition (f := f) (i := i) (j := j) hij)
    S
    (fun i ↦ targetStageToAmbient (f := f) i)
    (fun i j hij x ↦ targetStageToAmbient_compatible (f := f) (i := i) (j := j) hij x)

/-- Helper for Lemma 10.127.15: the source direct-limit comparison is bijective because every
ambient source element is already present on some singleton stage. -/
private theorem sourceColimitToAmbient_bijective :
    Function.Bijective (sourceColimitToAmbient (f := f)) := by
  -- Combine injectivity of each source-stage subtype map with the singleton-stage cover of `R`.
  simpa [sourceColimitToAmbient] using
    (directLimit_lift_bijective_of_stagewise_injective_cover
      (A := fun i : IntegralStageIndex f ↦ sourceStage f i)
      (map := fun i j hij ↦ sourceTransition (f := f) (i := i) (j := j) hij)
      (B := R)
      (g := fun i ↦ sourceStageToAmbient (f := f) i)
      (hg := fun i j hij x ↦
        sourceStageToAmbient_compatible (f := f) (i := i) (j := j) hij x)
      (hinj := fun _ ↦ Subtype.val_injective)
      (hcover := fun r ↦ by
        rcases source_stage_cover (f := f) r with ⟨i, hr⟩
        exact ⟨i, ⟨r, hr⟩, rfl⟩))

/-- Helper for Lemma 10.127.15: the target direct-limit comparison is bijective because every
ambient target element is already present on a singleton target stage. -/
private theorem targetColimitToAmbient_bijective (hInt : f.IsIntegral) :
    Function.Bijective (targetColimitToAmbient (f := f)) := by
  -- The target-side comparison is treated identically, now using integrality to cover `S`.
  simpa [targetColimitToAmbient] using
    (directLimit_lift_bijective_of_stagewise_injective_cover
      (A := fun i : IntegralStageIndex f ↦ targetStage f i)
      (map := fun i j hij ↦ targetTransition (f := f) (i := i) (j := j) hij)
      (B := S)
      (g := fun i ↦ targetStageToAmbient (f := f) i)
      (hg := fun i j hij x ↦
        targetStageToAmbient_compatible (f := f) (i := i) (j := j) hij x)
      (hinj := fun _ ↦ Subtype.val_injective)
      (hcover := fun s ↦ by
        rcases target_stage_cover (f := f) hInt s with ⟨i, hs⟩
        exact ⟨i, ⟨s, hs⟩, rfl⟩))

/-- Helper for Lemma 10.127.15: the source direct limit identifies with `R` via the ambient
subtype maps. -/
private noncomputable def sourceColimitIso :
    Ring.DirectLimit
        (fun i : IntegralStageIndex f ↦ sourceStage f i)
        (fun i j hij ↦ sourceTransition (f := f) (i := i) (j := j) hij) ≃+* R :=
  -- Upgrade the bijective source comparison map to a ring equivalence.
  RingEquiv.ofBijective
    (sourceColimitToAmbient (f := f))
    (sourceColimitToAmbient_bijective (f := f))

/-- Helper for Lemma 10.127.15: the target direct limit identifies with `S` via the ambient
subtype maps. -/
private noncomputable def targetColimitIso (hInt : f.IsIntegral) :
    Ring.DirectLimit
        (fun i : IntegralStageIndex f ↦ targetStage f i)
        (fun i j hij ↦ targetTransition (f := f) (i := i) (j := j) hij) ≃+* S :=
  -- Upgrade the bijective target comparison map to a ring equivalence.
  RingEquiv.ofBijective
    (targetColimitToAmbient (f := f))
    (targetColimitToAmbient_bijective (f := f) hInt)

/-- Helper for Lemma 10.127.15: the induced map on colimits agrees with the ambient map `f` on
every canonical source-stage generator before passing to the chosen colimit isomorphisms. -/
private theorem colimit_comm_toAmbient_on_generators (i : IntegralStageIndex f)
    (x : sourceStage f i) :
    ((targetColimitToAmbient (f := f)).comp
        (Ring.DirectLimit.map
          (fun j ↦ stageMap f j)
          (fun j k hjk ↦ stage_square_commutes (f := f) (i := j) (j := k) hjk)))
      (Ring.DirectLimit.of
        (fun j : IntegralStageIndex f ↦ sourceStage f j)
        (fun j k hjk ↦ sourceTransition (f := f) (i := j) (j := k) hjk)
        i x) =
      ((f.comp (sourceColimitToAmbient (f := f)))
        (Ring.DirectLimit.of
          (fun j : IntegralStageIndex f ↦ sourceStage f j)
          (fun j k hjk ↦ sourceTransition (f := f) (i := j) (j := k) hjk)
          i x)) := by
  -- Evaluate both colimit maps on the same stage generator and read off the ambient stage square.
  rw [RingHom.comp_apply, Ring.DirectLimit.map_apply_of, targetColimitToAmbient,
    Ring.DirectLimit.lift_of, sourceColimitToAmbient, RingHom.comp_apply, Ring.DirectLimit.lift_of]
  simpa [RingHom.comp_apply] using
    congrArg
      (fun g : sourceStage f i →+* S => g x)
      (stage_to_ambient_commutes (f := f) i)

/-- Helper for Lemma 10.127.15: before identifying the direct limits with `R` and `S`, the map on
colimits induced by the stage maps is exactly the ambient map `f`. -/
private theorem colimit_comm_toAmbient :
    (targetColimitToAmbient (f := f)).comp
        (Ring.DirectLimit.map
          (fun i ↦ stageMap f i)
          (fun i j hij ↦ stage_square_commutes (f := f) (i := i) (j := j) hij)) =
      f.comp (sourceColimitToAmbient (f := f)) := by
  -- Direct-limit ring homomorphisms agree once they agree on each canonical stage generator.
  apply Ring.DirectLimit.hom_ext
  intro i
  ext x
  exact colimit_comm_toAmbient_on_generators (f := f) i x

/-- Helper for Lemma 10.127.15: the induced map on colimits agrees with the ambient map `f` on
every canonical stage generator. -/
private theorem colimit_comm_on_generators (hInt : f.IsIntegral) (i : IntegralStageIndex f)
    (x : sourceStage f i) :
    ((targetColimitIso (f := f) hInt).toRingHom.comp
        (Ring.DirectLimit.map
          (fun j ↦ stageMap f j)
          (fun j k hjk ↦ stage_square_commutes (f := f) (i := j) (j := k) hjk)))
      (Ring.DirectLimit.of
        (fun j : IntegralStageIndex f ↦ sourceStage f j)
        (fun j k hjk ↦ sourceTransition (f := f) (i := j) (j := k) hjk)
        i x) =
      ((f.comp (sourceColimitIso (f := f)).toRingHom)
        (Ring.DirectLimit.of
          (fun j : IntegralStageIndex f ↦ sourceStage f j)
          (fun j k hjk ↦ sourceTransition (f := f) (i := j) (j := k) hjk)
          i x)) := by
  -- The chosen colimit isomorphisms are definitionally the ambient comparison maps.
  simpa [sourceColimitIso, targetColimitIso] using
    (colimit_comm_toAmbient_on_generators (f := f) i x)

/-- Helper for Lemma 10.127.15: after identifying both directed colimits with the ambient rings,
the induced colimit map is exactly `f`. -/
private theorem colimit_comm (hInt : f.IsIntegral) :
    (targetColimitIso (f := f) hInt).toRingHom.comp
        (Ring.DirectLimit.map
          (fun i ↦ stageMap f i)
          (fun i j hij ↦ stage_square_commutes (f := f) (i := i) (j := j) hij)) =
      f.comp (sourceColimitIso (f := f)).toRingHom := by
  -- The iso-level comparison is just the ambient one rewritten through `RingEquiv.ofBijective`.
  simpa [sourceColimitIso, targetColimitIso] using
    (colimit_comm_toAmbient (f := f))

end IntegralStageData

-- Proof sketch: let `Λ` be the directed set of finite subsets of `R` and `S` that are stable
-- under the given ring map `f`. For each stage, take the `ℤ`-subalgebra of `R` generated by the
-- chosen source elements and the `R_λ`-subalgebra of `S` generated by the chosen target elements.
-- These stage rings are finite type in the required sense, the transition maps come from
-- inclusions, and the filtered unions recover `R` and `S`, giving the direct-limit description of
-- `f`.
/-- Lemma 10.127.15: if `f : R →+* S` is integral, then `f` is the direct limit of a directed
system of finite ring maps `R_λ → S_λ` in which every `R_λ` is of finite type over `ℤ`. -/
theorem exists_directedIntegralHomApproximation (f : R →+* S) (hInt : f.IsIntegral) :
    ∃ A : DirectedFiniteTypeHomApproximation.{u, v, max u v} f,
      ∀ i : A.Λ, RingHom.Finite (A.stageMap i) := by
  classical
  let A : DirectedFiniteTypeHomApproximation f :=
    { Λ := IntegralStageIndex f
      instPreorder := inferInstance
      instNonempty := inferInstance
      instDirectedOrder := inferInstance
      RStage := fun i ↦ IntegralStageData.sourceStage f i
      SStage := fun i ↦ IntegralStageData.targetStage f i
      instCommRingRStage := fun _ ↦ inferInstance
      instCommRingSStage := fun _ ↦ inferInstance
      RMap := fun i j hij ↦ IntegralStageData.sourceTransition (f := f) (i := i) (j := j) hij
      SMap := fun i j hij ↦ IntegralStageData.targetTransition (f := f) (i := i) (j := j) hij
      instDirectedSystemRStage := IntegralStageData.sourceDirectedSystem (f := f)
      instDirectedSystemSStage := IntegralStageData.targetDirectedSystem (f := f)
      stageMap := IntegralStageData.stageMap f
      comm := fun {i j} hij ↦ IntegralStageData.stage_square_commutes (f := f) (i := i) (j := j) hij
      source_finiteType := IntegralStageData.sourceStage_finiteType (f := f)
      target_finiteType := IntegralStageData.stageMap_finiteType (f := f)
      colimitSource := IntegralStageData.sourceColimitIso (f := f)
      colimitTarget := IntegralStageData.targetColimitIso (f := f) hInt
      colimit_comm := IntegralStageData.colimit_comm (f := f) hInt }
  refine ⟨A, ?_⟩
  intro i
  -- Each packaged stage map is finite by the finite-adjoin argument established above.
  exact IntegralStageData.stageMap_finite (f := f) i

end
