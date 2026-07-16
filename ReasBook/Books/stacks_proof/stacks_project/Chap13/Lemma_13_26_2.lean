import stacks_proof.stacks_project.Chap13.Definition_13_26_1

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory ZeroObject

noncomputable section

universe v u

namespace CategoryTheory

section IntervalSplit

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜] [HasZeroObject 𝒜]
  [HasFiniteBiproducts 𝒜]
variable (a b : ℤ) (J : Set.Icc a b → 𝒜)

/-- Helper for Lemma 13.26.2: the canonical interval-tail inclusion is split by the corresponding
projection onto the same subtype biproduct. -/
private theorem intervalTailSubobject_splitMono (p : ℤ) :
    IsSplitMono (biproduct.fromSubtype J fun i : Set.Icc a b ↦ p ≤ i.1) := by
  -- Proof comment: the canonical projection onto the same subtype is a retraction.
  exact IsSplitMono.mk'
    { retraction := biproduct.toSubtype J fun i : Set.Icc a b ↦ p ≤ i.1
      id := biproduct.fromSubtype_toSubtype J fun i : Set.Icc a b ↦ p ≤ i.1 }

/-- The tail direct sum stage inside the interval-indexed biproduct. -/
@[reducible]
private noncomputable def intervalTailSubobject (p : ℤ) :
    Subobject (⨁ J) :=
  letI := intervalTailSubobject_splitMono a b J p
  Subobject.mk (biproduct.fromSubtype J fun i : Set.Icc a b ↦ p ≤ i.1)

/-- Helper for Lemma 13.26.2: the carrier of the `p`-tail subobject is canonically the
corresponding subtype biproduct. -/
@[reducible]
private noncomputable def intervalTailSubobjectIsoSubtypeBiproduct (p : ℤ) :
    (((intervalTailSubobject a b J p : Subobject (⨁ J)) : 𝒜)) ≅
      (⨁ fun i : { i : Set.Icc a b // p ≤ i.1 } ↦ J i.1) :=
  letI := intervalTailSubobject_splitMono a b J p
  Subobject.underlyingIso (biproduct.fromSubtype J fun i : Set.Icc a b ↦ p ≤ i.1)

/-- Helper for Lemma 13.26.2: under the canonical tail-carrier identification, the subobject
arrow is the expected `biproduct.fromSubtype`. -/
private theorem intervalTailSubobjectIsoSubtypeBiproduct_hom_comp_fromSubtype (p : ℤ) :
    (intervalTailSubobjectIsoSubtypeBiproduct a b J p).hom ≫
        biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1) =
      (intervalTailSubobject a b J p).arrow := by
  -- Proof comment: `intervalTailSubobject` is defined by the same split mono, so the canonical
  -- underlying isomorphism composes back to the defining subobject arrow.
  letI := intervalTailSubobject_splitMono a b J p
  change
    ((Subobject.underlyingIso (biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1))).hom ≫
        biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1)) =
      (intervalTailSubobject a b J p).arrow
  rw [Subobject.underlyingIso_hom_comp_eq_mk]

/-- Helper for Lemma 13.26.2: in the same canonical tail-carrier identification, the inverse map
followed by the stage arrow is again the canonical `biproduct.fromSubtype` inclusion. -/
private theorem intervalTailSubobjectIsoSubtypeBiproduct_inv_comp_arrow (p : ℤ) :
    (intervalTailSubobjectIsoSubtypeBiproduct a b J p).inv ≫
        (intervalTailSubobject a b J p).arrow =
      biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1) := by
  -- Proof comment: compose the previous arrow formula on the left with the inverse of the
  -- canonical carrier identification.
  calc
    (intervalTailSubobjectIsoSubtypeBiproduct a b J p).inv ≫
        (intervalTailSubobject a b J p).arrow
        =
          (intervalTailSubobjectIsoSubtypeBiproduct a b J p).inv ≫
            ((intervalTailSubobjectIsoSubtypeBiproduct a b J p).hom ≫
              biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1)) := by
                rw [intervalTailSubobjectIsoSubtypeBiproduct_hom_comp_fromSubtype]
    _ = biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1) := by
          simp [Category.assoc]

/-- Helper for Lemma 13.26.2: increasing the cutoff index shrinks the interval tail subobject. -/
private theorem intervalTailSubobject_antitone {p q : ℤ} (hpq : p ≤ q) :
    intervalTailSubobject a b J q ≤ intervalTailSubobject a b J p := by
  -- Proof comment: every `q`-tail summand also satisfies the weaker bound `p ≤ i.1`, so the
  -- `q`-tail inclusion factors through the `p`-tail by the larger-tail projection.
  letI := intervalTailSubobject_splitMono a b J p
  letI := intervalTailSubobject_splitMono a b J q
  refine Subobject.mk_le_mk_of_comm
    (biproduct.fromSubtype J (fun i : Set.Icc a b ↦ q ≤ i.1) ≫
      biproduct.toSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1)) ?_
  ext i
  by_cases hqi : q ≤ i.1
  · have hpi : p ≤ i.1 := le_trans hpq hqi
    simp [biproduct.fromSubtype_π, biproduct.toSubtype_π, hqi, hpi, Category.assoc]
  · by_cases hpi : p ≤ i.1
    · simp [biproduct.fromSubtype_π, biproduct.toSubtype_π, hqi, hpi, Category.assoc]
    · simp [biproduct.fromSubtype_π, biproduct.toSubtype_π, hqi, hpi, Category.assoc]

/-- Helper for Lemma 13.26.2: a morphism into the interval biproduct factors through the `p`-tail
exactly when all components strictly below `p` vanish. -/
private theorem intervalTailSubobject_factors_iff_componentZero
    {W : 𝒜} {p : ℤ} (g : W ⟶ ⨁ J) :
    (intervalTailSubobject a b J p).Factors g ↔
      ∀ i : Set.Icc a b, ¬ p ≤ i.1 → g ≫ biproduct.π J i = 0 := by
  letI := intervalTailSubobject_splitMono a b J p
  change (Subobject.mk (biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1))).Factors g ↔ _
  constructor
  · intro hg i hip
    rcases (Subobject.mk_factors_iff
        (biproduct.fromSubtype J (fun j : Set.Icc a b ↦ p ≤ j.1)) g).1 hg with
      ⟨gTail, hgTail⟩
    -- Proof comment: once `g` factors through the tail inclusion, every excluded component dies
    -- by the `fromSubtype_π` formula.
    calc
      g ≫ biproduct.π J i
          = gTail ≫ biproduct.fromSubtype J (fun j : Set.Icc a b ↦ p ≤ j.1) ≫
              biproduct.π J i := by
                rw [← hgTail]
                simp [Category.assoc]
      _ = 0 := by
            simp [biproduct.fromSubtype_π, hip, Category.assoc]
  · intro hg
    rw [Subobject.mk_factors_iff]
    let gTail : W ⟶ ⨁ fun j : { i : Set.Icc a b // p ≤ i.1 } ↦ J j.1 :=
      biproduct.lift (fun j : { i : Set.Icc a b // p ≤ i.1 } ↦ g ≫ biproduct.π J j.1)
    refine ⟨gTail, ?_⟩
    -- Proof comment: rebuild the factorization by keeping exactly the surviving components of
    -- `g` on the subtype-indexed tail biproduct.
    apply biproduct.hom_ext
    intro i
    by_cases hip : p ≤ i.1
    · let j : { i : Set.Icc a b // p ≤ i.1 } := ⟨i, hip⟩
      have hπbase :
          biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1) ≫ biproduct.π J i =
            biproduct.π (Subtype.restrict (fun i : Set.Icc a b ↦ p ≤ i.1) J) j := by
        simpa [biproduct.fromSubtype_π, j, hip]
      have hπ :
          (gTail ≫ biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1)) ≫
              biproduct.π J i =
            gTail ≫ biproduct.π (Subtype.restrict (fun i : Set.Icc a b ↦ p ≤ i.1) J) j := by
        rw [Category.assoc]
        exact congrArg (fun k ↦ gTail ≫ k) hπbase
      have hLift :
          gTail ≫ biproduct.π (Subtype.restrict (fun i : Set.Icc a b ↦ p ≤ i.1) J) j =
            g ≫ biproduct.π J i := by
        dsimp [gTail]
        simpa [j] using
          (show
            (biproduct.lift
                (fun j : { i : Set.Icc a b // p ≤ i.1 } ↦ g ≫ biproduct.π J j.1)) ≫
                biproduct.π (Subtype.restrict (fun i : Set.Icc a b ↦ p ≤ i.1) J) j =
              g ≫ biproduct.π J i from
            biproduct.lift_π
              (fun j : { i : Set.Icc a b // p ≤ i.1 } ↦ g ≫ biproduct.π J j.1)
              j)
      exact hπ.trans hLift
    · simp [biproduct.fromSubtype_π, hip, hg i hip, Category.assoc]

/-- The tail filtration on the biproduct indexed by the interval `[a, b]` is monotone on `ℤᵒᵈ`.
-/
private theorem intervalTailFiltration_monotone :
    Monotone (fun p : ℤᵒᵈ ↦ intervalTailSubobject a b J p) := by
  intro p q hpq
  -- Proof comment: monotonicity on `ℤᵒᵈ` is exactly antitonicity on `ℤ`.
  simpa using
    intervalTailSubobject_antitone (a := a) (b := b) (J := J)
      (show OrderDual.ofDual q ≤ OrderDual.ofDual p from hpq)

/-- The decreasing filtration on the interval biproduct whose `p`-th stage is the tail direct sum
over indices `q ≥ p`. -/
noncomputable def intervalTailFiltration :
    DecreasingFiltration (⨁ J) :=
  { toFun := fun p ↦ intervalTailSubobject a b J p
    monotone' := intervalTailFiltration_monotone a b J }

/-- Helper for Lemma 13.26.2: every stage weakly to the left of the interval is the whole
interval biproduct. -/
private theorem intervalTailSubobject_eq_top_of_le_left {p : ℤ} (hp : p ≤ a) :
    intervalTailSubobject a b J p = ⊤ := by
  -- Proof comment: every index in `[a, b]` satisfies `p ≤ i.1`, so the tail inclusion is an
  -- isomorphism with inverse the corresponding subtype projection.
  letI := intervalTailSubobject_splitMono a b J p
  change Subobject.mk (biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1)) = ⊤
  apply le_antisymm le_top
  refine Subobject.mk_le_mk_of_comm
    (biproduct.toSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1)) ?_
  ext i
  have hi : p ≤ i.1 := le_trans hp i.2.1
  simp [hi, Category.assoc]

/-- Helper for Lemma 13.26.2: every stage strictly to the right of the interval is zero. -/
private theorem intervalTailSubobject_eq_bot_of_right_lt {p : ℤ} (hp : b < p) :
    intervalTailSubobject a b J p = ⊥ := by
  -- Proof comment: no index in `[a, b]` survives beyond the right endpoint, so the tail
  -- inclusion is the zero morphism and hence defines the bottom subobject.
  letI := intervalTailSubobject_splitMono a b J p
  change Subobject.mk (biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1)) = ⊥
  apply (Subobject.mk_eq_bot_iff_zero).2
  apply biproduct.hom_ext
  intro i
  have hi : ¬ p ≤ i.1 := by
    omega
  simp [biproduct.fromSubtype_π, hi]

/-- Helper for Lemma 13.26.2: if the cutoff lies weakly to the left of the interval, the tail
inclusion already is an isomorphism onto the whole biproduct. -/
private theorem intervalTailSubobject_fromSubtype_isIso_of_le_left {p : ℤ} (hp : p ≤ a) :
    IsIso (biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1)) := by
  -- Proof comment: the defining subobject is `⊤`, so its arrow is an isomorphism.
  letI := intervalTailSubobject_splitMono a b J p
  change IsIso (intervalTailSubobject a b J p).arrow
  exact (Subobject.isIso_arrow_iff_eq_top _).2
    (intervalTailSubobject_eq_top_of_le_left (a := a) (b := b) (J := J) hp)

/-- The interval-split filtered object has finite filtration. -/
private theorem intervalSplitFilteredObject_isFinite :
    ({ obj := ⨁ J
       filtration := intervalTailFiltration a b J } : FilteredObject 𝒜).IsFinite := by
  refine ⟨a, b + 1, ?_, ?_⟩
  · -- Proof comment: the left endpoint already contains every interval summand.
    simpa [intervalTailFiltration] using
      intervalTailSubobject_eq_top_of_le_left (a := a) (b := b) (J := J) le_rfl
  · -- Proof comment: the stage immediately to the right of the window is the empty tail.
    simpa [intervalTailFiltration] using
      intervalTailSubobject_eq_bot_of_right_lt (a := a) (b := b) (J := J) (by omega)

/-- The finite filtered object attached to an interval-indexed family of summands. -/
noncomputable def intervalSplitFilteredObject :
    Fil^f(𝒜) :=
  ⟨{ obj := ⨁ J
     filtration := intervalTailFiltration a b J },
    intervalSplitFilteredObject_isFinite a b J⟩

/-- Helper for Lemma 13.26.2: the `p`-th stage of `intervalSplitFilteredObject a b J` is the
canonical `p`-tail subobject of the interval-indexed biproduct. -/
theorem intervalSplitFilteredObject_filtration_obj (p : ℤ) :
    (intervalSplitFilteredObject a b J).obj.filtration.obj p = intervalTailSubobject a b J p := by
  -- Proof comment: the public interval-split filtration is defined from the interval tails.
  rfl

/-- Helper for Lemma 13.26.2: the `p`-th stage of the public interval-split object is canonically
the expected tail biproduct, and under this identification its arrow is the canonical tail
inclusion. -/
private theorem intervalSplitFilteredObject_stageArrow_hom_comp_fromSubtype (p : ℤ) :
    (intervalTailSubobjectIsoSubtypeBiproduct a b J p).hom ≫
        biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1) =
      ((intervalSplitFilteredObject a b J).obj.filtration.obj p).arrow := by
  -- Proof comment: the public interval-split object uses the same tail subobject definition, so
  -- the stage arrow formula is exactly the tail-subobject arrow formula after unfolding names.
  simpa [intervalSplitFilteredObject, intervalTailFiltration] using
    intervalTailSubobjectIsoSubtypeBiproduct_hom_comp_fromSubtype
      (a := a) (b := b) (J := J) p

/-- Helper for Lemma 13.26.2: the `p`-th stage of the public interval-split object is canonically
the expected tail biproduct, and under this identification its arrow is the canonical tail
inclusion. -/
@[reducible]
noncomputable def intervalSplitFilteredObject_stageIso (p : ℤ) :
    (((intervalSplitFilteredObject a b J).obj.filtration.obj p : Subobject _ ) : 𝒜) ≅
      (⨁ fun i : { i : Set.Icc a b // p ≤ i.1 } ↦ J i.1) :=
  intervalTailSubobjectIsoSubtypeBiproduct a b J p

/-- Helper for Lemma 13.26.2: under the canonical stage identification, the stage arrow of
`intervalSplitFilteredObject a b J` is the expected `biproduct.fromSubtype` inclusion. -/
theorem intervalSplitFilteredObject_stage_arrow_eq_fromSubtype (p : ℤ) :
    (intervalSplitFilteredObject_stageIso a b J p).hom ≫
        biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1) =
      ((intervalSplitFilteredObject a b J).obj.filtration.obj p).arrow := by
  -- Proof comment: this is the public stage-arrow formula consumed by later interval-split
  -- arguments.
  simpa [intervalSplitFilteredObject_stageIso] using
    intervalSplitFilteredObject_stageArrow_hom_comp_fromSubtype
      (a := a) (b := b) (J := J) p

/-- Helper for Lemma 13.26.2: the `p`-th stage of the public interval-split object is canonically
the expected tail biproduct, and under this identification its arrow is the canonical tail
inclusion. -/
theorem intervalSplitFilteredObject_stage_arrow_exists_iso_fromSubtype (p : ℤ) :
    ∃ e :
      (((intervalSplitFilteredObject a b J).obj.filtration.obj p : Subobject _ ) : 𝒜) ≅
        (⨁ fun i : { i : Set.Icc a b // p ≤ i.1 } ↦ J i.1),
      e.hom ≫ biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1) =
        ((intervalSplitFilteredObject a b J).obj.filtration.obj p).arrow := by
  -- Proof comment: package the canonical stage isomorphism together with its arrow formula.
  exact ⟨intervalSplitFilteredObject_stageIso a b J p,
    intervalSplitFilteredObject_stage_arrow_eq_fromSubtype (a := a) (b := b) (J := J) p⟩

end IntervalSplit

section FilteredInjective

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- The interval-split model in Lemma 13.26.2 uses finite biproducts, which are available in any
abelian category. -/
local instance filteredInjective_hasFiniteBiproducts : HasFiniteBiproducts 𝒜 :=
  Abelian.hasFiniteBiproducts

/-- Helper for Lemma 13.26.2: a finite filtered object admits an ordered window `[a, b]` whose
left endpoint is already top and whose successor to the right endpoint is already bottom. -/
private theorem orderedWindowOfFiniteFiltration (I : Fil^f(𝒜)) :
    ∃ a b : ℤ, a ≤ b ∧ I.obj.filtration a = ⊤ ∧ I.obj.filtration (b + 1) = ⊥ := by
  rcases I.property with ⟨t, m, htop, hbot⟩
  refine ⟨min t m, max t m, min_le_max _ _, ?_, ?_⟩
  · -- Proof comment: moving left from a top stage keeps the filtration equal to `⊤`.
    exact filtration_eq_top_of_le (X := I.obj) (min_le_left _ _) htop
  · -- Proof comment: moving right from a bottom stage keeps the filtration equal to `⊥`.
    exact filtration_eq_bot_of_le (X := I.obj) (le_trans (le_max_right _ _) (by omega)) hbot

/-- Helper for Lemma 13.26.2: the canonical stage row
`0 ⟶ F^(p + 1) I ⟶ F^p I ⟶ gr^p(I) ⟶ 0` splits by injectivity of `gr^p(I)`, so `F^p(I)` is the
binary biproduct of `gr^p(I)` and `F^(p + 1)I`. -/
private theorem succStageSplitIso
    (I : Fil^f(𝒜)) [IsFilteredInjective I] (p : ℤ) :
    ∃ eStage : F^{p} I.obj ≅ gr^{p} I.obj ⊞ F^{p + 1} I.obj,
      I.obj.filtration.stageInclusion p ≫ eStage.hom = biprod.inr ∧
        eStage.hom ≫ biprod.fst = cokernel.π (I.obj.filtration.stageInclusion p) := by
  let S : ShortComplex 𝒜 := FilteredObject.Hom.stageShortComplex I.obj p
  have hS : S.ShortExact := by
    -- Proof comment: the consecutive-stage row is the standard short exact sequence attached to
    -- the graded quotient.
    simpa [S] using FilteredObject.Hom.stage_shortExact I.obj p
  let s : S.Splitting := hS.splittingOfInjective
  let e₀ : F^{p} I.obj ≅ F^{p + 1} I.obj ⊞ gr^{p} I.obj := by
    -- Proof comment: `ShortComplex.ShortExact.splittingOfInjective` gives the raw split form
    -- `F^p(I) ≅ F^(p + 1)I ⊞ gr^p(I)`.
    simpa [S, FilteredObject.Hom.stageShortComplex] using
      (ShortComplex.Splitting.isoBinaryBiproduct (S := S) s)
  let eStage : F^{p} I.obj ≅ gr^{p} I.obj ⊞ F^{p + 1} I.obj :=
    e₀ ≪≫ biprod.braiding _ _
  refine ⟨eStage, ?_, ?_⟩
  · -- Proof comment: after swapping the two summands, the next filtration stage is the right
    -- biproduct inclusion.
    calc
      I.obj.filtration.stageInclusion p ≫ eStage.hom
          = I.obj.filtration.stageInclusion p ≫ e₀.hom ≫ (biprod.braiding _ _).hom := by
              simp [eStage, Category.assoc]
      _ = biprod.inl ≫ (biprod.braiding _ _).hom := by
            simpa [e₀, s, S, FilteredObject.Hom.stageShortComplex, Category.assoc]
      _ = biprod.inr := by
            simp
  · -- Proof comment: the left projection of the braided split form is still the canonical stage
    -- quotient map to `gr^p(I)`.
    calc
      eStage.hom ≫ biprod.fst
          = e₀.hom ≫ (biprod.braiding _ _).hom ≫ biprod.fst := by
              simp [eStage, Category.assoc]
      _ = e₀.hom ≫ biprod.snd := by
            simp [Category.assoc]
      _ = cokernel.π (I.obj.filtration.stageInclusion p) := by
            simpa [e₀, s, S, FilteredObject.Hom.stageShortComplex, Category.assoc]

/-- Helper for Lemma 13.26.2: adjoining the distinguished index `p` to the `(p + 1)`-tail gives
exactly the `p`-tail of the interval `[a, b]`. -/
private noncomputable def tailIndexSuccEquiv {a b p : ℤ} (hap : a ≤ p) (hpb : p ≤ b) :
    Sum PUnit {i : Set.Icc a b // p + 1 ≤ i.1} ≃ {i : Set.Icc a b // p ≤ i.1} where
  toFun
    | Sum.inl _ => ⟨⟨p, ⟨hap, hpb⟩⟩, le_rfl⟩
    | Sum.inr i => ⟨i.1, by omega⟩
  invFun j :=
    if hj : j.1.1 = p then
      Sum.inl PUnit.unit
    else
      Sum.inr ⟨j.1, by omega⟩
  left_inv x := by
    -- Proof comment: the distinguished `p`-index and every strictly larger tail index are sent
    -- back to their defining summands.
    cases x with
    | inl u =>
        rfl
    | inr i =>
        rcases i with ⟨i, hi⟩
        dsimp
        have hi_ne : i.1 ≠ p := by
          omega
        simp [hi_ne]
  right_inv j := by
    -- Proof comment: any element of the `p`-tail is either the distinguished index `p` or lies
    -- in the `(p + 1)`-tail.
    rcases j with ⟨j, hj⟩
    dsimp
    by_cases h : j.1 = p
    · subst h
      rfl
    · have hj_succ : p + 1 ≤ j.1 := by
        omega
      simp [h, hj_succ]

-- Use the shared Chapter 13 owner `IsFilteredInjective` recalled in `Definition_13_26_1` rather
-- than reintroducing a local duplicate owner in this file.

-- Statement-repair note: the source-facing statement below is already faithful to Stacks tag
-- `05TP`. The failed proof-attempt scaffolding is intentionally omitted here so the file remains
-- at statement scope.

/-- Helper for Lemma 13.26.2: if a filtered morphism is an isomorphism on underlying objects and
both `p`-th stages are already `⊤`, then the induced stage map is an isomorphism. -/
private theorem stageMap_isIso_of_eq_top
    {X Y : FilteredObject 𝒜} (g : X ⟶ Y) (p : ℤ)
    (hX : X.filtration p = ⊤) (hY : Y.filtration p = ⊤) [IsIso g.hom] :
    IsIso (FilteredObject.Hom.stageMap g p) := by
  letI : IsIso (X.filtration.obj p).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 hX
  letI : IsIso (Y.filtration.obj p).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 hY
  have hstage :
      FilteredObject.Hom.stageMap g p =
        (X.filtration.obj p).arrow ≫ g.hom ≫ inv (Y.filtration.obj p).arrow := by
    -- Proof comment: on a top stage, the stage arrow is an isomorphism, so the induced stage map
    -- is just the underlying morphism conjugated by those stage arrows.
    apply (cancel_mono (Y.filtration.obj p).arrow).1
    calc
      FilteredObject.Hom.stageMap g p ≫ (Y.filtration.obj p).arrow
          = (X.filtration.obj p).arrow ≫ g.hom := by
              rw [FilteredObject.Hom.stageMap_comm]
      _ = ((X.filtration.obj p).arrow ≫ g.hom ≫ inv (Y.filtration.obj p).arrow) ≫
            (Y.filtration.obj p).arrow := by
              simp [Category.assoc]
  rw [hstage]
  infer_instance

/-- Helper for Lemma 13.26.2: if the `(p + 1)`-st filtration stage is already the whole object,
then the `p`-th graded piece vanishes. -/
private theorem gradedPieceIsZeroOfSuccEqTop
    (X : FilteredObject 𝒜) (p : ℤ) (h : X.filtration (p + 1) = ⊤) :
    IsZero (gr^{p} X) := by
  have hp : X.filtration p = ⊤ := filtration_eq_top_of_le (by omega) h
  letI : IsIso (X.filtration.obj p).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 hp
  letI : IsIso (X.filtration.obj (p + 1)).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 h
  have hstage :
      X.filtration.stageInclusion p =
        (X.filtration.obj (p + 1)).arrow ≫ inv (X.filtration.obj p).arrow := by
    -- Proof comment: compare both candidates after composing with the ambient monomorphism of
    -- the `p`-th stage.
    apply (cancel_mono (X.filtration.obj p).arrow).1
    calc
      X.filtration.stageInclusion p ≫ (X.filtration.obj p).arrow =
          (X.filtration.obj (p + 1)).arrow := by
            exact Subobject.ofLE_arrow _
      _ =
          ((X.filtration.obj (p + 1)).arrow ≫ inv (X.filtration.obj p).arrow) ≫
            (X.filtration.obj p).arrow := by
              simp
  rw [hstage]
  letI : Epi ((X.filtration.obj (p + 1)).arrow ≫ inv (X.filtration.obj p).arrow) := by
    infer_instance
  -- Proof comment: once the stage inclusion is an isomorphism, the graded piece is the
  -- cokernel of an epimorphism and therefore vanishes.
  simpa [FilteredObject.gradedPiece, DecreasingFiltration.gradedPiece] using
    (Limits.isZero_cokernel_of_epi
      ((X.filtration.obj (p + 1)).arrow ≫ inv (X.filtration.obj p).arrow))

/-- Helper for Lemma 13.26.2: if the `p`-th filtration stage is already zero, then the `p`-th
graded piece vanishes. -/
private theorem gradedPieceIsZeroOfEqBot
    (X : FilteredObject 𝒜) (p : ℤ) (h : X.filtration p = ⊥) :
    IsZero (gr^{p} X) := by
  have hp1 : X.filtration (p + 1) = ⊥ := filtration_eq_bot_of_le (by omega) h
  let hzeroSucc : IsZero (F^{p + 1} X) := stage_isZero_of_eq_bot X (p + 1) hp1
  let hzero : IsZero (F^{p} X) := stage_isZero_of_eq_bot X p h
  letI : IsIso (X.filtration.stageInclusion p) := hzeroSucc.isIso hzero _
  -- Proof comment: both adjacent stages are zero, so the stage inclusion is an isomorphism and
  -- its cokernel vanishes.
  simpa [FilteredObject.gradedPiece, DecreasingFiltration.gradedPiece] using
    (Limits.isZero_cokernel_of_epi (X.filtration.stageInclusion p))

/-- Helper for Lemma 13.26.2: inside the interval window, the `p`-th graded piece of the
interval-split object is canonically the distinguished `p`-summand. -/
private noncomputable def intervalSplitFilteredObject_gradedPieceIsoComponent
    {a b p : ℤ} (J : Set.Icc a b → 𝒜) (hp : p ∈ Set.Icc a b) :
    gr^{p} ((intervalSplitFilteredObject a b J).obj) ≅ J ⟨p, hp⟩ := by
  -- Route correction: work directly with the public stage-arrow formula on `F^p` rather than
  -- trying to push additional raw subtype-tail transport lemmas through the proof.
  let X : FilteredObject 𝒜 := (intervalSplitFilteredObject a b J).obj
  let jp : Subtype.restrict (fun i : Set.Icc a b ↦ p ≤ i.1) J :=
    ⟨⟨p, hp⟩, le_rfl⟩
  let πp : F^{p} X ⟶ J ⟨p, hp⟩ :=
    (X.filtration.obj p).arrow ≫ biproduct.π J ⟨p, hp⟩
  let ip : J ⟨p, hp⟩ ⟶ F^{p} X :=
    biproduct.ι (Subtype.restrict (fun i : Set.Icc a b ↦ p ≤ i.1) J) jp
  let rp : F^{p} X ⟶ F^{p + 1} X :=
    (X.filtration.obj p).arrow ≫
      biproduct.toSubtype J (fun i : Set.Icc a b ↦ p + 1 ≤ i.1)
  have hipπ : ip ≫ πp = 𝟙 _ := by
    -- Proof comment: the distinguished summand survives in `F^p` and the `p`-projection picks
    -- it out exactly.
    simp [ip, πp, jp, X, intervalSplitFilteredObject_stage_arrow_eq_fromSubtype, Category.assoc]
  have hipr : ip ≫ rp = 0 := by
    -- Proof comment: the distinguished `p`-summand does not lie in the `(p + 1)`-tail.
    have hpfalse : ¬ p + 1 ≤ (⟨p, hp⟩ : Set.Icc a b).1 := by
      omega
    simp [ip, rp, jp, X, intervalSplitFilteredObject_stage_arrow_eq_fromSubtype,
      hpfalse, Category.assoc]
  have hstageπ : X.filtration.stageInclusion p ≫ πp = 0 := by
    -- Proof comment: the next filtration stage only sees summands with index at least `p + 1`,
    -- so the `p`-projection kills it.
    have hpfalse : ¬ p + 1 ≤ (⟨p, hp⟩ : Set.Icc a b).1 := by
      omega
    calc
      X.filtration.stageInclusion p ≫ πp
          = X.filtration.stageInclusion p ≫ (X.filtration.obj p).arrow ≫
              biproduct.π J ⟨p, hp⟩ := by
                simp [πp, Category.assoc]
      _ = (X.filtration.obj (p + 1)).arrow ≫ biproduct.π J ⟨p, hp⟩ := by
            rw [Subobject.ofLE_arrow]
      _ = 0 := by
            simp [X, intervalSplitFilteredObject_stage_arrow_eq_fromSubtype, hpfalse]
  have hstager : X.filtration.stageInclusion p ≫ rp = 𝟙 _ := by
    -- Proof comment: projecting the `p`-tail onto the `(p + 1)`-tail is the canonical
    -- retraction of the tail inclusion.
    apply (cancel_mono (X.filtration.obj (p + 1)).arrow).1
    calc
      X.filtration.stageInclusion p ≫ rp ≫ (X.filtration.obj (p + 1)).arrow
          = X.filtration.stageInclusion p ≫ (X.filtration.obj p).arrow ≫
              biproduct.toSubtype J (fun i : Set.Icc a b ↦ p + 1 ≤ i.1) ≫
                (X.filtration.obj (p + 1)).arrow := by
                  simp [rp, Category.assoc]
      _ = (X.filtration.obj (p + 1)).arrow ≫
            biproduct.toSubtype J (fun i : Set.Icc a b ↦ p + 1 ≤ i.1) ≫
              (X.filtration.obj (p + 1)).arrow := by
                rw [Subobject.ofLE_arrow]
      _ = (X.filtration.obj (p + 1)).arrow := by
            simp [X, intervalSplitFilteredObject_stage_arrow_eq_fromSubtype, Category.assoc]
  have htotal : πp ≫ ip + rp ≫ X.filtration.stageInclusion p = 𝟙 _ := by
    -- Proof comment: every summand of the `p`-tail is either the distinguished `p`-summand or
    -- already lies in the `(p + 1)`-tail, so these two projectors add up to the identity.
    apply (cancel_mono (X.filtration.obj p).arrow).1
    ext j
    by_cases hj : j = jp
    · subst hj
      have hpfalse : ¬ p + 1 ≤ (⟨p, hp⟩ : Set.Icc a b).1 := by
        omega
      simp [πp, ip, rp, X, intervalSplitFilteredObject_stage_arrow_eq_fromSubtype,
        hpfalse, Category.assoc]
    · have hjne : j.1.1 ≠ p := by
        intro hEq
        apply hj
        ext
        simp [jp, hEq]
      have hjgt : p + 1 ≤ j.1.1 := by
        omega
      simp [πp, ip, rp, X, intervalSplitFilteredObject_stage_arrow_eq_fromSubtype,
        hj, hjgt, Category.assoc]
  let eStage : F^{p} X ≅ J ⟨p, hp⟩ ⊞ F^{p + 1} X :=
    { hom := biprod.lift πp rp
      inv := biprod.desc ip (X.filtration.stageInclusion p)
      hom_inv_id := by
        -- Proof comment: the two complementary projectors on the `p`-tail sum to the identity.
        apply (cancel_mono (X.filtration.obj p).arrow).1
        calc
          (biprod.lift πp rp ≫ biprod.desc ip (X.filtration.stageInclusion p)) ≫
              (X.filtration.obj p).arrow
              =
                (πp ≫ ip + rp ≫ X.filtration.stageInclusion p) ≫
                  (X.filtration.obj p).arrow := by
                    simp [Preadditive.add_comp, Category.assoc]
          _ = (X.filtration.obj p).arrow := by
                rw [htotal]
                simp
      inv_hom_id := by
        -- Proof comment: the distinguished summand and the tail inclusion give the two standard
        -- injections into the binary biproduct decomposition.
        ext
        · simp [hipπ, hstageπ, Category.assoc]
        · simp [hipr, hstager, Category.assoc] }
  let s : CokernelCofork (X.filtration.stageInclusion p) :=
    CokernelCofork.ofπ πp hstageπ
  have hs : IsColimit s := by
    -- Proof comment: after identifying `F^p` with `J_p ⊞ F^(p + 1)`, the stage inclusion is the
    -- standard coprojection `biprod.inr`, whose cokernel is the first projection `biprod.fst`.
    refine IsCokernel.ofIso
      (biprod.inr : F^{p + 1} X ⟶ J ⟨p, hp⟩ ⊞ F^{p + 1} X)
      (biprod.isCokernelInrCokernelFork (J ⟨p, hp⟩) (F^{p + 1} X))
      s
      (Iso.refl _)
      eStage.symm
      (Iso.refl _)
      ?_
      ?_
    · simp [eStage, Category.assoc]
    · simp [s, eStage, πp, Category.assoc]
  -- Proof comment: both the canonical cokernel and the explicit descended `p`-projection are
  -- cokernels of the same stage inclusion, so their points are canonically isomorphic.
  exact IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (X.filtration.stageInclusion p))
    hs

/-- Helper for Lemma 13.26.2: the interval-split model is filtered injective as soon as each
chosen summand is injective. -/
private theorem intervalSplitFilteredObject_isFilteredInjective
    {a b : ℤ} (J : Set.Icc a b → 𝒜) (hJ : ∀ i, Injective (J i)) :
    IsFilteredInjective (intervalSplitFilteredObject a b J) := by
  refine ⟨fun p ↦ ?_⟩
  by_cases hp : p ∈ Set.Icc a b
  · let e := intervalSplitFilteredObject_gradedPieceIsoComponent (J := J) hp
    -- Proof comment: inside the interval, the `p`-th graded piece is exactly the chosen
    -- `p`-summand.
    exact Injective.of_iso e.symm (hJ ⟨p, hp⟩)
  · have hp' : p < a ∨ b < p := by
      -- Proof comment: being outside the interval means lying strictly left or strictly right of
      -- the finite support window.
      by_contra h
      push_neg at h
      exact hp ⟨h.1, h.2⟩
    rcases hp' with hpa | hbp
    · have htop :
        (intervalSplitFilteredObject a b J).obj.filtration (p + 1) = ⊤ := by
        rw [intervalSplitFilteredObject_filtration_obj]
        exact intervalTailSubobject_eq_top_of_le_left (a := a) (b := b) (J := J) (by omega)
      -- Proof comment: weakly left of the interval, the next stage is already top, so the
      -- graded piece vanishes.
      exact (gradedPieceIsZeroOfSuccEqTop
        ((intervalSplitFilteredObject a b J).obj) p htop).injective
    · have hbot :
        (intervalSplitFilteredObject a b J).obj.filtration p = ⊥ := by
        rw [intervalSplitFilteredObject_filtration_obj]
        exact intervalTailSubobject_eq_bot_of_right_lt (a := a) (b := b) (J := J) hbp
      -- Proof comment: strictly right of the interval, the `p`-tail is empty, so the graded
      -- piece again vanishes.
      exact (gradedPieceIsZeroOfEqBot
        ((intervalSplitFilteredObject a b J).obj) p hbot).injective

/-- Helper for Lemma 13.26.2: the literal one-stage filtered object supported in degrees
`q ≤ p` with underlying object `X`. -/
private theorem topStageFiltration_monotone (p : ℤ) (X : 𝒜) :
    Monotone (fun q : ℤᵒᵈ ↦ if (q : ℤ) ≤ p then (⊤ : Subobject X) else ⊥) := by
  intro q r hqr
  by_cases hq : (q : ℤ) ≤ p
  · have hr : (r : ℤ) ≤ p := by
      exact le_trans (show (r : ℤ) ≤ (q : ℤ) from hqr) hq
    simp [hq, hr]
  · have hr : ¬ (r : ℤ) ≤ p := by
      intro hr
      exact hq (le_trans (show (r : ℤ) ≤ (q : ℤ) from hqr) hr)
    simp [hq, hr]

/-- Helper for Lemma 13.26.2: the filtered object with a single nonzero top stage in degree `p`.
-/
private def topStageFilteredObject (p : ℤ) (X : 𝒜) : FilteredObject 𝒜 :=
  { obj := X
    filtration :=
      { toFun := fun q ↦ if (q : ℤ) ≤ p then (⊤ : Subobject X) else ⊥
        monotone' := topStageFiltration_monotone p X } }

/-- Helper for Lemma 13.26.2: the canonical inclusion of the top surviving stage `F^p(I)` into
`I`, viewed as a morphism from the literal one-stage filtered object. -/
private theorem topStageInclusion_preserves {I : FilteredObject 𝒜} (p q : ℤ) :
    (I.filtration.obj q).Factors
      ((((topStageFilteredObject p (F^{p} I)).filtration.obj q).arrow) ≫
        (I.filtration.obj p).arrow) := by
  -- Proof comment: below degree `p` the source stage is all of `F^p(I)`, while above degree `p`
  -- it is already zero.
  by_cases hq : q ≤ p
  · rw [show (topStageFilteredObject p (F^{p} I)).filtration.obj q = ⊤ by
        simp [topStageFilteredObject, hq]]
    refine (Subobject.factors_iff (I.filtration.obj q) ((I.filtration.obj p).arrow)).2 ?_
    refine ⟨Subobject.ofLE (I.filtration.obj p) (I.filtration.obj q)
      (I.filtration.antitone_obj hq), ?_⟩
    simpa using
      (Subobject.ofLE_arrow (h := I.filtration.antitone_obj hq) :
        Subobject.ofLE (I.filtration.obj p) (I.filtration.obj q)
            (I.filtration.antitone_obj hq) ≫ (I.filtration.obj q).arrow =
          (I.filtration.obj p).arrow)
  · rw [show (topStageFilteredObject p (F^{p} I)).filtration.obj q = ⊥ by
        simp [topStageFilteredObject, hq]]
    simpa [Subobject.bot_eq_zero] using
      (Subobject.factors_zero :
        (I.filtration.obj q).Factors (0 : (0 : 𝒜) ⟶ I.obj))

/-- Helper for Lemma 13.26.2: the filtered inclusion of the top surviving stage into the ambient
filtered object. -/
private def topStageInclusion {I : FilteredObject 𝒜} (p : ℤ) :
    topStageFilteredObject p (F^{p} I) ⟶ I :=
  { hom := (I.filtration.obj p).arrow
    preserves := topStageInclusion_preserves p }

/-- Helper for Lemma 13.26.2: the induced map on a filtration stage preserves identities. -/
private theorem filteredStageMap_id (X : FilteredObject 𝒜) (p : ℤ) :
    FilteredObject.Hom.stageMap (𝟙 X) p = 𝟙 (F^{p} X) := by
  -- Proof comment: compare both stage maps after postcomposing with the mono stage inclusion.
  apply (cancel_mono (X.filtration.obj p).arrow).1
  rw [FilteredObject.Hom.stageMap_comm]
  simp

/-- Helper for Lemma 13.26.2: the induced map on filtration stages preserves composition. -/
private theorem filteredStageMap_comp
    {X Y Z : FilteredObject 𝒜} (f : X ⟶ Y) (g : Y ⟶ Z) (p : ℤ) :
    FilteredObject.Hom.stageMap (f ≫ g) p =
      FilteredObject.Hom.stageMap f p ≫ FilteredObject.Hom.stageMap g p := by
  -- Proof comment: compare both candidates after the target stage inclusion.
  apply (cancel_mono (Z.filtration.obj p).arrow).1
  calc
    FilteredObject.Hom.stageMap (f ≫ g) p ≫ (Z.filtration.obj p).arrow
        = (X.filtration.obj p).arrow ≫ (f ≫ g).hom := by
            rw [FilteredObject.Hom.stageMap_comm]
    _ = ((X.filtration.obj p).arrow ≫ f.hom) ≫ g.hom := by
          simp [Category.assoc]
    _ = (FilteredObject.Hom.stageMap f p ≫ (Y.filtration.obj p).arrow) ≫ g.hom := by
          rw [FilteredObject.Hom.stageMap_comm]
    _ = FilteredObject.Hom.stageMap f p ≫
          (FilteredObject.Hom.stageMap g p ≫ (Z.filtration.obj p).arrow) := by
            rw [FilteredObject.Hom.stageMap_comm]
            simp [Category.assoc]
    _ = (FilteredObject.Hom.stageMap f p ≫ FilteredObject.Hom.stageMap g p) ≫
          (Z.filtration.obj p).arrow := by
            simp [Category.assoc]

/-- Helper for Lemma 13.26.2: on the top surviving degree, the literal top-stage inclusion
induces the identity on stages. -/
private theorem topStageInclusion_stageMap {I : FilteredObject 𝒜} (p : ℤ) :
    FilteredObject.Hom.stageMap (topStageInclusion (I := I) p) p = 𝟙 (F^{p} I) := by
  -- Proof comment: at degree `p`, the source stage is the whole object `F^p(I)`, so cancelling
  -- the ambient stage inclusion identifies the induced stage map with the identity.
  apply (cancel_mono (I.filtration.obj p).arrow).1
  calc
    FilteredObject.Hom.stageMap (topStageInclusion (I := I) p) p ≫
        (I.filtration.obj p).arrow
        = (((topStageFilteredObject p (F^{p} I)).filtration.obj p).arrow) ≫
            (topStageInclusion (I := I) p).hom := by
              rw [FilteredObject.Hom.stageMap_comm]
    _ = (𝟙 (F^{p} I)) ≫ (I.filtration.obj p).arrow := by
          simp [topStageInclusion, topStageFilteredObject]
    _ = (I.filtration.obj p).arrow := by simp

/-- Helper for Lemma 13.26.2: an injective ambient object splits any monomorphism into it. -/
private theorem sectionOfMonoIntoInjective {X Y : 𝒜} [Injective X] (f : X ⟶ Y) [Mono f] :
    ∃ s : Y ⟶ X, f ≫ s = 𝟙 X := by
  -- Proof comment: injectivity of `X` extends the identity morphism across the monomorphism `f`.
  refine ⟨Injective.factorThru (𝟙 X) f, ?_⟩
  simpa using (Injective.comp_factorThru (g := 𝟙 X) (f := f))

/-- Helper for Lemma 13.26.2: if the `(p + 1)`-st stage is zero, any ambient retraction onto
`F^p(I)` packages into a filtered retraction onto the literal one-stage filtered object. -/
private theorem topStageRetraction_preserves
    {I : FilteredObject 𝒜} {p q : ℤ}
    (hp : I.filtration.obj (p + 1) = ⊥) (s : I.obj ⟶ F^{p} I) :
    ((topStageFilteredObject p (F^{p} I)).filtration.obj q).Factors
      ((I.filtration.obj q).arrow ≫ s) := by
  -- Proof comment: below degree `p` the target stage is all of `F^p(I)`, while above degree `p`
  -- the source stage is already zero by finiteness of the ordered window.
  by_cases hq : q ≤ p
  · rw [show (topStageFilteredObject p (F^{p} I)).filtration.obj q = ⊤ by
        simp [topStageFilteredObject, hq]]
    refine (Subobject.factors_iff (⊤ : Subobject (F^{p} I)) _).2 ?_
    exact ⟨(I.filtration.obj q).arrow ≫ s, by simp⟩
  · have hbotq : I.filtration.obj q = ⊥ := by
      exact filtration_eq_bot_of_le (X := I) (by omega) hp
    rw [show (topStageFilteredObject p (F^{p} I)).filtration.obj q = ⊥ by
        simp [topStageFilteredObject, hq], hbotq]
    simpa [Subobject.bot_eq_zero, Category.assoc] using
      (Subobject.factors_zero :
        (⊥ : Subobject (F^{p} I)).Factors (0 : (0 : 𝒜) ⟶ F^{p} I))

/-- Helper for Lemma 13.26.2: package an ambient retraction onto `F^p(I)` as a filtered
retraction onto the literal one-stage filtered object. -/
private def topStageRetraction
    {I : FilteredObject 𝒜} (p : ℤ) (hp : I.filtration.obj (p + 1) = ⊥) (s : I.obj ⟶ F^{p} I) :
    I ⟶ topStageFilteredObject p (F^{p} I) :=
  { hom := s
    preserves := topStageRetraction_preserves hp s }

/-- Helper for Lemma 13.26.2: the filtered top-stage inclusion followed by the packaged
retraction is the identity. -/
private theorem topStageInclusion_comp_topStageRetraction
    {I : FilteredObject 𝒜} {p : ℤ} (hp : I.filtration.obj (p + 1) = ⊥) (s : I.obj ⟶ F^{p} I)
    (hs : (I.filtration.obj p).arrow ≫ s = 𝟙 (F^{p} I)) :
    topStageInclusion (I := I) p ≫ topStageRetraction p hp s =
      𝟙 (topStageFilteredObject p (F^{p} I)) := by
  -- Proof comment: on underlying objects this is exactly the chosen retraction of the stage
  -- inclusion.
  apply FilteredObject.Hom.ext
  simpa [topStageInclusion, topStageRetraction] using hs

/-- Helper for Lemma 13.26.2: once a filtered morphism has a section, the filtered kernel is a
retract of the source. -/
private theorem kernelRetractOfSection {X T : FilteredObject 𝒜} (f : X ⟶ T) (j : T ⟶ X)
    (hfj : j ≫ f = 𝟙 T) :
    ∃ ρ : X ⟶ FilteredObject.Hom.kernelFilteredObject f,
      FilteredObject.Hom.kernelι f ≫ ρ = 𝟙 _ := by
  have hcomp : (𝟙 X - f ≫ j) ≫ f = 0 := by
    -- Proof comment: `𝟙 - f ≫ j` kills the split summand because `j ≫ f = 𝟙`.
    calc
      (𝟙 X - f ≫ j) ≫ f = f - (f ≫ j ≫ f) := by
        simp [Category.assoc, sub_comp]
      _ = f - f := by
        simp [hfj, Category.assoc]
      _ = 0 := by simp
  refine ⟨FilteredObject.Hom.liftToKernel f (𝟙 X - f ≫ j) hcomp, ?_⟩
  -- Proof comment: compare after postcomposing with the kernel inclusion; the split identity
  -- forces the lifted endomorphism of the kernel to be the identity.
  apply (cancel_mono (FilteredObject.Hom.kernelι f)).1
  calc
    (FilteredObject.Hom.kernelι f ≫
        FilteredObject.Hom.liftToKernel f (𝟙 X - f ≫ j) hcomp) ≫
          FilteredObject.Hom.kernelι f
        =
          FilteredObject.Hom.kernelι f ≫
            (FilteredObject.Hom.liftToKernel f (𝟙 X - f ≫ j) hcomp ≫
              FilteredObject.Hom.kernelι f) := by
              simp [Category.assoc]
    _ = FilteredObject.Hom.kernelι f ≫ (𝟙 X - f ≫ j) := by
          rw [FilteredObject.Hom.liftToKernel_kernelι]
    _ = FilteredObject.Hom.kernelι f := by
          simp [sub_eq_add_neg, Category.assoc, FilteredObject.Hom.kernelι_comp]
    _ = 𝟙 _ ≫ FilteredObject.Hom.kernelι f := by simp

/-- Helper for Lemma 13.26.2: a split filtered retraction exhibits the source as the binary
biproduct of its kernel and the split top-stage summand. -/
private noncomputable theorem filteredIsoOfSection
    {X T : FilteredObject 𝒜} (f : X ⟶ T) (j : T ⟶ X) (hfj : j ≫ f = 𝟙 T) :
    (FilteredObject.Hom.kernelFilteredObject f) ⊞ T ≅ X := by
  obtain ⟨ρ, hρ⟩ := kernelRetractOfSection f j hfj
  let eHom : (FilteredObject.Hom.kernelFilteredObject f) ⊞ T ⟶ X :=
    biprod.desc (FilteredObject.Hom.kernelι f) j
  let eInv : X ⟶ (FilteredObject.Hom.kernelFilteredObject f) ⊞ T :=
    biprod.lift ρ f
  refine
    { hom := eHom
      inv := eInv
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · -- Proof comment: compare the endomorphism of the biproduct after the two coproduct
    -- injections; the kernel summand retracts and the split summand is fixed.
    apply FilteredObject.forget.map_injective
    apply biprod.hom_ext'
    · calc
        biprod.inl ≫ eHom.hom ≫ eInv.hom
            = (FilteredObject.Hom.kernelι f).hom ≫ ρ.hom := by
                simp [eHom, eInv, Category.assoc]
        _ = biprod.inl ≫ biprod.fst := by
              simpa using congrArg FilteredObject.Hom.hom hρ
        _ = biprod.inl := by simp
    · have hjρ : j ≫ ρ = 0 := by
        apply (cancel_mono (FilteredObject.Hom.kernelι f)).1
        calc
          (j ≫ ρ) ≫ FilteredObject.Hom.kernelι f
              = j ≫ (ρ ≫ FilteredObject.Hom.kernelι f) := by
                  simp [Category.assoc]
          _ = j ≫ (𝟙 X - f ≫ j) := by
                rw [FilteredObject.Hom.liftToKernel_kernelι]
          _ = 0 := by
                simp [sub_eq_add_neg, hfj, Category.assoc]
        -- `simp` above closes the postcomposition with the kernel inclusion.
      calc
        biprod.inr ≫ eHom.hom ≫ eInv.hom
            = j.hom ≫ biprod.lift ρ f.hom := by
                simp [eHom, eInv, Category.assoc]
        _ = biprod.inr := by
              apply biprod.hom_ext
              · simpa [Category.assoc] using congrArg FilteredObject.Hom.hom hjρ
              · simpa using congrArg FilteredObject.Hom.hom hfj
  · -- Proof comment: the split kernel projector and the split quotient projector add up to the
    -- identity endomorphism of `X`.
    apply FilteredObject.Hom.ext
    calc
      eInv.hom ≫ eHom.hom
          = ρ.hom ≫ (FilteredObject.Hom.kernelι f).hom + f.hom ≫ j.hom := by
              simp [eHom, eInv, biprod.lift_desc, Category.assoc]
      _ = 𝟙 X.obj := by
            rw [FilteredObject.Hom.liftToKernel_kernelι]
            simp [sub_eq_add_neg, hfj, Category.assoc]

/-- Helper for Lemma 13.26.2: the singleton interval `[a, a]` has one index. -/
private noncomputable def intervalSingletonEquiv (a : ℤ) : PUnit.{1} ≃ Set.Icc a a where
  toFun _ := ⟨a, le_rfl, le_rfl⟩
  invFun _ := PUnit.unit
  left_inv _ := rfl
  right_inv i := by
    rcases i with ⟨i, hi⟩
    apply Subtype.ext
    change a = i
    exact (le_antisymm hi.2 hi.1).symm

/-- Helper for Lemma 13.26.2: a filtered object supported in a single degree is the corresponding
singleton interval-split model. -/
private noncomputable theorem singleStageIsoIntervalSplit
    (X : FilteredObject 𝒜) (a : ℤ)
    (ha : X.filtration.obj a = ⊤) (hb : X.filtration.obj (a + 1) = ⊥) :
    X ≅ (intervalSplitFilteredObject a a (fun _ : Set.Icc a a ↦ F^{a} X)).obj := by
  let J : Set.Icc a a → 𝒜 := fun _ ↦ F^{a} X
  let Y : Fil^f(𝒜) := intervalSplitFilteredObject a a J
  letI : IsIso (X.filtration.obj a).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 ha
  let eTop : F^{a} X ≅ X.obj := asIso (X.filtration.obj a).arrow
  let eIndex : PUnit.{1} ≃ Set.Icc a a := intervalSingletonEquiv a
  let F0 : PUnit.{1} → 𝒜 := J ∘ eIndex
  let eUnique : ⨁ F0 ≅ F0 PUnit.unit := biproductUniqueIso F0
  let eReindex : ⨁ F0 ≅ ⨁ J := biproduct.reindex eIndex J
  have hEval : J (eIndex PUnit.unit) = F^{a} X := rfl
  let eSingleObj : F^{a} X ≅ ⨁ J := (eqToIso hEval).symm ≪≫ eUnique.symm ≪≫ eReindex
  let eObj : X.obj ≅ Y.obj.obj := eTop.symm ≪≫ eSingleObj
  let eHom : X ⟶ Y.obj :=
    { hom := eObj.hom
      preserves := by
        intro q
        by_cases hq : q ≤ a
        · -- Proof comment: at or below the support degree, the target stage is already `⊤`.
          have hYq : Y.obj.filtration.obj q = ⊤ := by
            simpa [Y, intervalSplitFilteredObject_filtration_obj] using
              intervalTailSubobject_eq_top_of_le_left
                (a := a) (b := a) (J := J) hq
          rw [hYq]
          refine (Subobject.factors_iff (⊤ : Subobject Y.obj.obj) _).2 ?_
          exact ⟨(X.filtration.obj q).arrow ≫ eObj.hom, by simp⟩
        · -- Proof comment: strictly above the support degree, the source stage is already zero.
          have hXq : X.filtration.obj q = ⊥ := by
            exact filtration_eq_bot_of_le (X := X) (by omega) hb
          rw [hXq]
          simpa [Subobject.bot_eq_zero] using
            (Subobject.factors_zero :
              (Y.obj.filtration.obj q).Factors (0 : (0 : 𝒜) ⟶ Y.obj.obj)) }
  let eInv : Y.obj ⟶ X :=
    { hom := eObj.inv
      preserves := by
        intro q
        by_cases hq : q ≤ a
        · -- Proof comment: at or below the support degree, the source stage is already `⊤`.
          have hXq : X.filtration.obj q = ⊤ := filtration_eq_top_of_le (X := X) hq ha
          rw [hXq]
          refine (Subobject.factors_iff (⊤ : Subobject X.obj) _).2 ?_
          exact ⟨(Y.obj.filtration.obj q).arrow ≫ eObj.inv, by simp⟩
        · -- Proof comment: strictly above the support degree, the singleton interval stage is
          -- empty, so its arrow is zero.
          have hYq : Y.obj.filtration.obj q = ⊥ := by
            simpa [Y, intervalSplitFilteredObject_filtration_obj] using
              intervalTailSubobject_eq_bot_of_right_lt
                (a := a) (b := a) (J := J) (show a < q by omega)
          rw [hYq]
          simpa [Subobject.bot_eq_zero] using
            (Subobject.factors_zero :
              (X.filtration.obj q).Factors (0 : (0 : 𝒜) ⟶ X.obj)) }
  refine
    { hom := eHom
      inv := eInv
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · -- Proof comment: the filtered inverse candidate was built from the underlying object
    -- isomorphism `eObj`.
    apply FilteredObject.Hom.ext
    simpa [eHom, eInv] using eObj.hom_inv_id
  · -- Proof comment: the same object-level inverse identity gives the filtered one.
    apply FilteredObject.Hom.ext
    simpa [eHom, eInv] using eObj.inv_hom_id

/-- Helper for Lemma 13.26.2: if the `p`-th stage of a filtered object is top, then that stage
is canonically isomorphic to the underlying object. -/
private noncomputable def stageIsoToUnderlyingOfEqTop
    (X : FilteredObject 𝒜) (p : ℤ) (hp : X.filtration.obj p = ⊤) :
    F^{p} X ≅ X.obj := by
  -- Proof comment: a top filtration stage has arrow an isomorphism onto the ambient object.
  letI : IsIso (X.filtration.obj p).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 hp
  exact asIso (X.filtration.obj p).arrow

/-- Helper for Lemma 13.26.2: at the left endpoint of the interval, the public interval-split
stage is canonically the whole underlying biproduct object. -/
private noncomputable def intervalSplitLeftStageIsoToUnderlying
    {a b : ℤ} (J : Set.Icc a b → 𝒜) :
    F^{a} (intervalSplitFilteredObject a b J).obj ≅
      (intervalSplitFilteredObject a b J).obj.obj := by
  -- Proof comment: the left endpoint sees every interval summand, so the corresponding stage is
  -- already top.
  refine stageIsoToUnderlyingOfEqTop ((intervalSplitFilteredObject a b J).obj) a ?_
  simpa [intervalSplitFilteredObject_filtration_obj] using
    intervalTailSubobject_eq_top_of_le_left (a := a) (b := b) (J := J) le_rfl

/-- Lemma 13.26.2: a finite filtered object is filtered injective if and only if it is
isomorphic to a finite direct sum of injective objects indexed by an interval, equipped with the
tail filtration.
-/
@[stacks 05TP]
theorem isFilteredInjective_iff_exists_iso_intervalSplitFilteredObject
    (I : Fil^f(𝒜)) :
    IsFilteredInjective I ↔
      ∃ a b : ℤ,
        a ≤ b ∧
          ∃ J : Set.Icc a b → 𝒜,
            ∃ e : I ≅ intervalSplitFilteredObject a b J, ∀ n, Injective (J n) := sorry

end FilteredInjective

end CategoryTheory
