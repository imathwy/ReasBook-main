import Mathlib
import stacks_proof.stacks_project.Chap13.Definition_13_34_1
import stacks_proof.stacks_project.Chap13.Lemma_13_29_3
import stacks_proof.stacks_project.Chap13.Lemma_13_31_4
import stacks_proof.stacks_project.Chap13.Lemma_13_31_8
import stacks_proof.stacks_project.Chap13.Lemma_13_34_2
import stacks_proof.stacks_project.Chap13.Remark_13_34_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DerivedCategory

noncomputable section

universe w v u

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
  [HasCountableProducts 𝒜]

/- 
Domain-style sampling for Lemma `13.34.6`.
- primary domain: sequential inverse systems in the derived category arising from the lower
  truncation tower of a cochain complex, together with the canonical comparison map from the source
  complex into the inverse limit of an injective resolution system;
- sampled owner declarations:
  `CategoryTheory.IsDerivedLimit`,
  `CategoryTheory.isInjective`,
  `LowerTruncationResolutionSystem.intoLimit`,
  `LowerTruncationResolutionSystem.intoLimit_comp_π`,
  `Remark_13_34_5.IsTruncationDerivedLimitComparison` as the nearby comparison-owner pattern for
    truncation towers in the derived category;
- best owner abstraction: the source-facing comparison to the inverse limit of the chosen injective
  system is already owned by `LowerTruncationResolutionSystem.intoLimit`; the inverse-limit object
  itself is canonically `limit S.diagram`, not a separate local wrapper;
- primitive-vs-derived split:
  primitive data: a lower truncation resolution system `S` and the canonical derived-limit
    comparison predicate `IsLowerTruncationDerivedLimitComparison`;
  derived API: K-injectivity of `limit S.diagram`, the derived-limit witness for
    `Q.obj (limit S.diagram)`, and the comparison theorem for the canonical map `S.intoLimit`.

Source/core/bridge triage:
- `source-facing`: the comparison from `K^•` to the inverse limit of the chosen lower truncation
  injective system;
- `core/canonical`: `IsDerivedLimit` and `LowerTruncationResolutionSystem.intoLimit`;
- `bridge/view`: the proof that `Q.map S.intoLimit` is a compatible derived-limit comparison.
-/

/-- The shifted truncation tower `n ↦ τ_{\ge -(n + 1)} K^•` of a cochain complex, viewed in the
derived category. -/
noncomputable abbrev derivedLowerTruncationTower (K : CochainComplex 𝒜 ℤ) :
    SequentialInverseSystem (DerivedCategory 𝒜) :=
  lowerTruncationDiagram K ⋙ Q

/-- The canonical morphism from `K^•` to the `n`th stage `τ_{\ge -(n + 1)} K^•` of its shifted
lower truncation tower in the derived category. -/
noncomputable abbrev derivedLowerTruncationToStage (K : CochainComplex 𝒜 ℤ) (n : ℕ) :
    Q.obj K ⟶ (derivedLowerTruncationTower K).obj (Opposite.op n) :=
  Q.map (K.πTruncGE (-(((n + 1 : ℕ)) : ℤ)))

/-- A lower truncation resolution system by injective complexes has an inverse limit in the
category of cochain complexes. -/
private noncomputable instance lowerTruncationResolutionSystem_hasLimit_eval
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) (i : ℤ) :
    HasLimit (S.diagram ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i) := by
  let F := S.diagram ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i
  let _ : HasLimit (Discrete.functor F.obj) := inferInstance
  let _ : HasLimit
      (Discrete.functor fun f : Σ p : ℕᵒᵖ × ℕᵒᵖ, p.1 ⟶ p.2 ↦ F.obj f.1.2) := inferInstance
  exact hasLimit_of_equalizer_and_product F

/-- A lower truncation resolution system by injective complexes has an inverse limit in the
category of cochain complexes. -/
private noncomputable instance lowerTruncationResolutionSystem_hasLimit
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) :
    HasLimit S.diagram := inferInstance

-- Proof sketch: identify the inverse limit degreewise with a countable product of injective
-- objects and apply Lemma 13.31.5 to deduce K-injectivity from the K-injectivity of the bounded
-- below stages provided by Lemma 13.31.4.
/-- Helper for Lemma 13.34.6: each stage of the lower truncation injective system is
K-injective. -/
private theorem lowerTruncationResolutionSystem_stage_isKInjective
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) (n : ℕ) :
    (S.stage n).IsKInjective := by
  -- Proof comment: `S.isResolutionStage n` packages the stage as a bounded-below complex with
  -- injective terms, so its associated `PlusWithTermsIn` model carries the standard
  -- K-injective instance.
  let hstage := S.isResolutionStage n
  let Iplus : CochainComplex.PlusWithTermsIn (isInjective 𝒜) := hstage.toPlusWithTermsIn
  change (Iplus : CochainComplex 𝒜 ℤ).IsKInjective
  infer_instance

/-- Helper for Lemma 13.34.6: each stage comparison becomes an isomorphism in the derived
category. -/
private theorem lowerTruncationResolutionSystem_comparison_isIso
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) (n : ℕ) :
    IsIso (Q.map (S.comparison.app (op n))) := by
  -- Proof comment: the resolution-system data already record each comparison as a quasi-
  -- isomorphism, and localization sends quasi-isomorphisms to isomorphisms.
  rw [isIso_Q_map_iff_quasiIso]
  exact (S.isResolutionStage n).quasiIso

/-- Helper for Lemma 13.34.6: the termwise product of the resolution stages realizes the fixed
product of the shifted lower truncation tower in the derived category. -/
theorem lowerTruncation_resolution_stage_product_isLimit
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) :
    IsLimit
      (Fan.mk (Q.obj (∏ᶜ fun n ↦ S.stage n)) fun n ↦
        Q.map (Pi.π (fun n ↦ S.stage n) n) ≫
          (asIso (Q.map (S.comparison.app (op n)))).symm.hom) := by
  -- Proof comment: apply Lemma 13.34.2 to the K-injective stage representatives and transport
  -- the product cone along the stagewise derived isomorphisms coming from `S.comparison`.
  letI : ∀ n : ℕ, (S.stage n).IsKInjective := fun n ↦
    lowerTruncationResolutionSystem_stage_isKInjective S n
  let eK : ∀ n : ℕ, Q.obj (S.stage n) ≅ inverseSystemFamily (derivedLowerTruncationTower K) n :=
    fun n ↦ by
      -- Proof comment: `S.comparison.app (op n)` identifies `S.stage n` with the `n`th shifted
      -- lower truncation after passing to the derived category.
      letI : IsIso (Q.map (S.comparison.app (op n))) :=
        lowerTruncationResolutionSystem_comparison_isIso S n
      exact (asIso (Q.map (S.comparison.app (op n)))).symm
  simpa [derivedLowerTruncationTower, inverseSystemFamily] using
    (termwise_product_represents_product
      (𝒜 := 𝒜)
      (X := inverseSystemFamily (derivedLowerTruncationTower K))
      (K := fun n ↦ S.stage n)
      eK)

/-- Helper for Lemma 13.34.6: fix the source-faithful product object for the shifted lower
truncation tower by using the termwise product of the resolution stages. -/
private noncomputable def lowerTruncation_resolution_stage_product
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) :
    HasProduct (inverseSystemFamily (derivedLowerTruncationTower K)) :=
  HasLimit.mk
    ⟨Fan.mk (Q.obj (∏ᶜ fun n ↦ S.stage n)) fun n ↦
        Q.map (Pi.π (fun n ↦ S.stage n) n) ≫
          (asIso (Q.map (S.comparison.app (op n)))).symm.hom,
      lowerTruncation_resolution_stage_product_isLimit (𝒜 := 𝒜) S⟩

/-- The inverse limit of the injective lower truncation resolution system is K-injective. -/
theorem isKInjective_lowerTruncationResolutionSystemLimit
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) :
    (limit S.diagram).IsKInjective := by
  -- Proof comment: each stage of the lower truncation resolution system is bounded below with
  -- injective terms, hence K-injective by Lemma 13.31.4.
  letI : ∀ n : ℕ, (S.stage n).IsKInjective := fun n ↦
    lowerTruncationResolutionSystem_stage_isKInjective S n
  -- Proof comment: the successor transition maps are termwise split epimorphisms by definition,
  -- so Lemma 13.31.8 applies directly to the inverse system `S.diagram`.
  exact SequentialInverseSystem.isKInjective_limit_of_termwiseSplitEpi S.diagram
    (fun n i ↦ by
      simpa [LowerTruncationResolutionSystem.stage, LowerTruncationResolutionSystem.step] using
        S.termwiseSplitEpi n i)

/-- A morphism from `K^•` to a derived object `L` is a compatible comparison with a chosen
derived limit of the shifted lower truncation tower `(τ_{\ge -(n + 1)} K^•)_n` if `L` fits into
the Milnor triangle of that tower and its stage projections recover the canonical maps from
`K^•`. -/
def IsLowerTruncationDerivedLimitComparison
    (K : CochainComplex 𝒜 ℤ) (L : DerivedCategory 𝒜) (c : Q.obj K ⟶ L) : Prop :=
  ∃ _ : HasProduct (inverseSystemFamily (derivedLowerTruncationTower K)),
    ∃ ι : L ⟶ ∏ᶜ inverseSystemFamily (derivedLowerTruncationTower K),
      HasMilnorTriangle.WithMap (derivedLowerTruncationTower K) ι ∧
        ∀ n : ℕ, c ≫ ι ≫ Pi.π (inverseSystemFamily (derivedLowerTruncationTower K)) n =
          derivedLowerTruncationToStage K n

section

omit [HasCountableProducts 𝒜] in
/-- A compatible lower-truncation comparison presents its target as a derived limit of the
shifted lower truncation tower. -/
theorem IsLowerTruncationDerivedLimitComparison.isDerivedLimit
    {K : CochainComplex 𝒜 ℤ} {L : DerivedCategory 𝒜} {c : Q.obj K ⟶ L}
    (hc : IsLowerTruncationDerivedLimitComparison K L c) :
    IsDerivedLimit (derivedLowerTruncationTower K) L := by
  rcases hc with ⟨hP, _, hι, _⟩
  let _ : HasProduct (inverseSystemFamily (derivedLowerTruncationTower K)) := hP
  exact ⟨hP, hι.hasMilnorTriangle (derivedLowerTruncationTower K)⟩

end

-- Proof sketch: compare the two compatible maps on each shifted truncation stage and then on
-- each cohomology object, exactly as in Remark 13.34.5; the criterion for being an isomorphism is
-- independent of the chosen compatible derived-limit model.
section

omit [HasCountableProducts 𝒜] in
/-- Any two compatible comparison morphisms from `K^•` to derived limits of its shifted lower
truncation tower are simultaneously isomorphisms. -/
theorem lowerTruncationDerivedLimitComparison_isIso_iff
    {K : CochainComplex 𝒜 ℤ}
    {L L' : DerivedCategory 𝒜} {c : Q.obj K ⟶ L} {c' : Q.obj K ⟶ L'}
    (hc : IsLowerTruncationDerivedLimitComparison K L c)
    (hc' : IsLowerTruncationDerivedLimitComparison K L' c') :
    IsIso c ↔ IsIso c' := by
  -- Proof comment: the shifted lower-truncation tower is exactly the truncation tower of
  -- `Q.obj K`, so the comparison theorem of Remark 13.34.5 applies without further changes.
  simpa [IsLowerTruncationDerivedLimitComparison, derivedLowerTruncationTower,
    derivedLowerTruncationToStage, derivedTruncationGETower, derivedTruncationGEToStage] using
    (derivedTruncationLimitComparison_isIso_iff (K := Q.obj K) hc hc')

end

/-- Helper for Lemma 13.34.6: the inverse-limit complex maps to the product of the chosen
resolution stages by the universal projections. -/
private noncomputable def lowerTruncation_resolution_limit_to_product
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) :
    limit S.diagram ⟶ ∏ᶜ fun n ↦ S.stage n :=
  Pi.lift fun n ↦ limit.π S.diagram (op n)

/-- Helper for Lemma 13.34.6: the limit-to-product map has the expected `n`th projection. -/
private theorem lowerTruncation_resolution_limit_to_product_comp_π
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) (n : ℕ) :
    lowerTruncation_resolution_limit_to_product S ≫ Pi.π (fun n ↦ S.stage n) n =
      limit.π S.diagram (op n) := by
  -- Proof comment: this is the defining projection formula for `Pi.lift`.
  simp [lowerTruncation_resolution_limit_to_product]

/-- Helper for Lemma 13.34.6: the source-faithful Milnor difference morphism on the product of the
resolution stages is `1 - shift(step)`. -/
private noncomputable def lowerTruncation_resolution_stage_difference
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) :
    ∏ᶜ fun n ↦ S.stage n ⟶ ∏ᶜ fun n ↦ S.stage n :=
  𝟙 _ - Pi.map' Nat.succ (fun n ↦ S.step n)

/-- Helper for Lemma 13.34.6: after projecting the product-row difference map to stage `n`, one
recovers the expected component formula `x_n - f_n(x_{n+1})`. -/
private theorem lowerTruncation_resolution_stage_difference_comp_π
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) (n : ℕ) :
    lowerTruncation_resolution_stage_difference S ≫ Pi.π (fun n ↦ S.stage n) n =
      Pi.π (fun n ↦ S.stage n) n -
        Pi.π (fun n ↦ S.stage n) (n + 1) ≫ S.step n := by
  -- Proof comment: this is the standard projection formula for `1 - shift(step)`.
  simp [lowerTruncation_resolution_stage_difference, Preadditive.sub_comp]

/-- Helper for Lemma 13.34.6: the limit-to-product map annihilates the Milnor difference map. -/
private theorem lowerTruncation_resolution_limit_to_product_comp_difference
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) :
    lowerTruncation_resolution_limit_to_product S ≫
        lowerTruncation_resolution_stage_difference S =
      0 := by
  -- Proof comment: compare after every degree and stage projection, then use the limit relation.
  ext i
  apply Pi.hom_ext
  intro n
  calc
    ((lowerTruncation_resolution_limit_to_product S ≫
          lowerTruncation_resolution_stage_difference S).f i) ≫
        Pi.π (fun n ↦ (S.stage n).X i) n =
      (limit.π S.diagram (op n)).f i -
        (limit.π S.diagram (op (n + 1))).f i ≫ (S.step n).f i := by
          simp [Category.assoc, lowerTruncation_resolution_limit_to_product_comp_π,
            lowerTruncation_resolution_stage_difference_comp_π]
    _ = 0 := by
      have hlimit :=
        congrArg (fun k : limit S.diagram ⟶ S.stage n ↦ k.f i)
          (limit.w (F := S.diagram) ((homOfLE (Nat.le_add_right n 1)).op))
      simpa [LowerTruncationResolutionSystem.step, SequentialInverseSystem.stepMap,
        Category.assoc] using sub_eq_zero.mpr hlimit.symm

/-- Helper for Lemma 13.34.6: after fixing the source-faithful product object, the derived image
of the concrete difference map is the canonical Milnor difference map of the shifted lower
truncation tower. -/
private theorem q_map_stage_difference_eq_derivedLimitDifferenceMap
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) :
    letI : HasProduct (inverseSystemFamily (derivedLowerTruncationTower K)) :=
      lowerTruncation_resolution_stage_product (𝒜 := 𝒜) S
    Q.map (lowerTruncation_resolution_stage_difference S) =
      derivedLimitDifferenceMap (derivedLowerTruncationTower K) := by
  -- Proof comment: compare both morphisms after every projection of the fixed product cone.
  letI : HasProduct (inverseSystemFamily (derivedLowerTruncationTower K)) :=
    lowerTruncation_resolution_stage_product (𝒜 := 𝒜) S
  apply Pi.hom_ext
  intro n
  calc
    Q.map (lowerTruncation_resolution_stage_difference S) ≫
        Pi.π (inverseSystemFamily (derivedLowerTruncationTower K)) n =
      Q.map (lowerTruncation_resolution_stage_difference S) ≫
          Q.map (Pi.π (fun n ↦ S.stage n) n) ≫
            (asIso (Q.map (S.comparison.app (op n)))).symm.hom := by
          rfl
    _ =
      Q.map
          (lowerTruncation_resolution_stage_difference S ≫
            Pi.π (fun n ↦ S.stage n) n) ≫
        (asIso (Q.map (S.comparison.app (op n)))).symm.hom := by
          simp [Functor.map_comp, Category.assoc]
    _ =
      (Q.map (Pi.π (fun n ↦ S.stage n) n) -
          Q.map (Pi.π (fun n ↦ S.stage n) (n + 1)) ≫ Q.map (S.step n)) ≫
        (asIso (Q.map (S.comparison.app (op n)))).symm.hom := by
          rw [lowerTruncation_resolution_stage_difference_comp_π]
          simp [Functor.map_sub, Functor.map_comp, Category.assoc]
    _ =
      Q.map (Pi.π (fun n ↦ S.stage n) n) ≫
          (asIso (Q.map (S.comparison.app (op n)))).symm.hom -
        Q.map (Pi.π (fun n ↦ S.stage n) (n + 1)) ≫
          (asIso (Q.map (S.comparison.app (op (n + 1))))).symm.hom ≫
            (derivedLowerTruncationTower K).transitionMap (Nat.le_succ n) := by
          rw [Preadditive.sub_comp]
          have hstep :
              Q.map (S.step n) ≫
                  (asIso (Q.map (S.comparison.app (op n)))).symm.hom =
                (asIso (Q.map (S.comparison.app (op (n + 1))))).symm.hom ≫
                  (derivedLowerTruncationTower K).transitionMap (Nat.le_succ n) := by
            -- Proof comment: transport the stagewise square `S.comparison_comp_step` through `Q`.
            have hcomp := congrArg Q.map (S.comparison_comp_step n).w
            simpa [derivedLowerTruncationTower, lowerTruncationDiagram, Functor.ofOpSequence,
              SequentialInverseSystem.transitionMap, Functor.map_comp, Category.assoc] using
              (IsIso.eq_comp_inv_iff_comp_eq (Q.map (S.comparison.app (op n)))).2 hcomp
          simp [Category.assoc, hstep]
    _ =
      Pi.π (inverseSystemFamily (derivedLowerTruncationTower K)) n -
        Pi.π (inverseSystemFamily (derivedLowerTruncationTower K)) (n + 1) ≫
          (derivedLowerTruncationTower K).transitionMap (Nat.le_succ n) := by
          rfl
    _ = derivedLimitDifferenceMap (derivedLowerTruncationTower K) ≫
          Pi.π (inverseSystemFamily (derivedLowerTruncationTower K)) n := by
          symm
          simpa using derivedLimitDifferenceMap_comp_π (derivedLowerTruncationTower K) n

/-- Helper for Lemma 13.34.6: after fixing the source-faithful product object, the derived image
of the limit-to-product map has the expected `n`th stage projection. -/
private theorem q_map_limit_to_product_comp_π
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) (n : ℕ) :
    letI : HasProduct (inverseSystemFamily (derivedLowerTruncationTower K)) :=
      lowerTruncation_resolution_stage_product (𝒜 := 𝒜) S
    Q.map (lowerTruncation_resolution_limit_to_product S) ≫
      Pi.π (inverseSystemFamily (derivedLowerTruncationTower K)) n =
        Q.map (limit.π S.diagram (op n)) ≫
          (asIso (Q.map (S.comparison.app (op n)))).symm.hom := by
  -- Proof comment: this is the derived version of the `Pi.lift` projection formula.
  letI : HasProduct (inverseSystemFamily (derivedLowerTruncationTower K)) :=
    lowerTruncation_resolution_stage_product (𝒜 := 𝒜) S
  simp [lowerTruncation_resolution_limit_to_product, Functor.map_comp, Category.assoc]

/-- Helper for Lemma 13.34.6: the degree-`i` kernel row of the source product construction is
realized by the evaluated limit object. -/
private theorem lowerTruncation_resolution_limit_product_degreewise_is_kernel
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) (i : ℤ) :
    IsLimit
      (KernelFork.ofι
        ((lowerTruncation_resolution_limit_to_product S).f i)
        (by
          simpa using
            congrArg (fun k : limit S.diagram ⟶ ∏ᶜ fun n ↦ S.stage n ↦ k.f i)
              (lowerTruncation_resolution_limit_to_product_comp_difference S))) := by
  -- Proof comment: a morphism into the kernel corresponds exactly to a cone over the evaluated
  -- inverse system, and evaluation preserves the chosen limit of complexes.
  let F := S.diagram ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i
  have hlimitEval :
      IsLimit ((HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i).mapCone (limit.cone S.diagram)) :=
    isLimitOfPreserves (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i) (limit.isLimit S.diagram)
  refine KernelFork.IsLimit.ofι _ _ ?_ ?_ ?_
  · intro W g hg
    let c : Cone F where
      pt := W
      π :=
        NatTrans.ofOpSequence
          (fun n ↦ g ≫ Pi.π (fun n ↦ (S.stage n).X i) n)
          (fun n ↦ by
            have hproj := congrArg
              (fun t : W ⟶ ∏ᶜ fun n ↦ (S.stage n).X i ↦
                t ≫ Pi.π (fun n ↦ (S.stage n).X i) n)
              hg
            simp [lowerTruncation_resolution_stage_difference, Preadditive.comp_sub,
              Category.assoc] at hproj
            simpa [F, LowerTruncationResolutionSystem.step, SequentialInverseSystem.stepMap,
              sub_eq_zero] using hproj)
    exact hlimitEval.lift c
  · intro W g hg
    apply Pi.hom_ext
    intro n
    simpa [F, lowerTruncation_resolution_limit_to_product, Category.assoc] using
      hlimitEval.fac
        (Cone.mk W <|
          NatTrans.ofOpSequence
            (fun n ↦ g ≫ Pi.π (fun n ↦ (S.stage n).X i) n)
            (fun n ↦ by
              have hproj := congrArg
                (fun t : W ⟶ ∏ᶜ fun n ↦ (S.stage n).X i ↦
                  t ≫ Pi.π (fun n ↦ (S.stage n).X i) n)
                hg
              simp [lowerTruncation_resolution_stage_difference, Preadditive.comp_sub,
                Category.assoc] at hproj
              simpa [F, LowerTruncationResolutionSystem.step, SequentialInverseSystem.stepMap,
                sub_eq_zero] using hproj))
        (op n)
  · intro W g hg m hm
    apply hlimitEval.hom_ext
    intro n
    have hπ := congrArg
      (fun t : W ⟶ ∏ᶜ fun n ↦ (S.stage n).X i ↦
        t ≫ Pi.π (fun n ↦ (S.stage n).X i) n)
      hm
    simpa [F, lowerTruncation_resolution_limit_to_product, Category.assoc] using hπ

/-- Helper for Lemma 13.34.6: the recursive section built from the chosen termwise split
epimorphisms produces a degreewise splitting of the source product row. -/
private noncomputable def lowerTruncation_resolution_stage_difference_section_aux
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) (i : ℤ) :
    ∀ n : ℕ, (∏ᶜ fun n ↦ (S.stage n).X i) ⟶ (S.stage n).X i
  | 0 => 0
  | n + 1 =>
      letI : IsSplitEpi ((S.step n).f i) := S.termwiseSplitEpi n i
      (lowerTruncation_resolution_stage_difference_section_aux S i n -
          Pi.π (fun n ↦ (S.stage n).X i) n) ≫
        section_ ((S.step n).f i)

/-- Helper for Lemma 13.34.6: the recursive section satisfies the expected one-step relation with
the transition maps. -/
private theorem lowerTruncation_resolution_stage_difference_section_aux_comp_step
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) (i : ℤ) (n : ℕ) :
    lowerTruncation_resolution_stage_difference_section_aux S i (n + 1) ≫ (S.step n).f i =
      lowerTruncation_resolution_stage_difference_section_aux S i n -
        Pi.π (fun n ↦ (S.stage n).X i) n := by
  -- Proof comment: this is the defining recursion together with the section property of each
  -- degreewise split epimorphism.
  letI : IsSplitEpi ((S.step n).f i) := S.termwiseSplitEpi n i
  simp [lowerTruncation_resolution_stage_difference_section_aux, Category.assoc]

/-- Helper for Lemma 13.34.6: the recursive degreewise section assembles into a section of the
Milnor difference map on the product row. -/
private noncomputable def lowerTruncation_resolution_stage_difference_section
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) (i : ℤ) :
    (∏ᶜ fun n ↦ (S.stage n).X i) ⟶ ∏ᶜ fun n ↦ (S.stage n).X i :=
  Pi.lift (lowerTruncation_resolution_stage_difference_section_aux S i)

/-- Helper for Lemma 13.34.6: the recursively defined degreewise section is indeed a right inverse
to the product-row difference map. -/
private theorem lowerTruncation_resolution_stage_difference_section_comp
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) (i : ℤ) :
    lowerTruncation_resolution_stage_difference_section S i ≫
        (lowerTruncation_resolution_stage_difference S).f i =
      𝟙 _ := by
  -- Proof comment: compare after each projection and unwind the recursive section formula.
  apply Pi.hom_ext
  intro n
  calc
    lowerTruncation_resolution_stage_difference_section S i ≫
        (lowerTruncation_resolution_stage_difference S).f i ≫
        Pi.π (fun n ↦ (S.stage n).X i) n =
      lowerTruncation_resolution_stage_difference_section_aux S i n -
        lowerTruncation_resolution_stage_difference_section_aux S i (n + 1) ≫
          (S.step n).f i := by
          simp [lowerTruncation_resolution_stage_difference_section,
            lowerTruncation_resolution_stage_difference, Preadditive.comp_sub, Category.assoc]
    _ = Pi.π (fun n ↦ (S.stage n).X i) n := by
      rw [lowerTruncation_resolution_stage_difference_section_aux_comp_step]
      abel
    _ = (𝟙 _ : (∏ᶜ fun n ↦ (S.stage n).X i) ⟶ _) ≫
          Pi.π (fun n ↦ (S.stage n).X i) n := by simp

/-- Helper for Lemma 13.34.6: evaluating the source product row at any degree yields a split
short exact sequence. -/
private theorem lowerTruncation_resolution_limit_product_degreewise_shortExact
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) (i : ℤ) :
    (ShortComplex.mk
      ((lowerTruncation_resolution_limit_to_product S).f i)
      ((lowerTruncation_resolution_stage_difference S).f i)
      (by
        simpa using
          congrArg (fun k : limit S.diagram ⟶ ∏ᶜ fun n ↦ S.stage n ↦ k.f i)
            (lowerTruncation_resolution_limit_to_product_comp_difference S))).ShortExact := by
  -- Proof comment: the evaluated limit map is the kernel of the evaluated difference map, and the
  -- recursive section from the chosen termwise split epimorphisms splits the row.
  let T : ShortComplex 𝒜 :=
    ShortComplex.mk
      ((lowerTruncation_resolution_limit_to_product S).f i)
      ((lowerTruncation_resolution_stage_difference S).f i)
      (by
        simpa using
          congrArg (fun k : limit S.diagram ⟶ ∏ᶜ fun n ↦ S.stage n ↦ k.f i)
            (lowerTruncation_resolution_limit_to_product_comp_difference S))
  have hkernel :
      IsLimit (KernelFork.ofι T.f T.zero) := by
    simpa [T] using lowerTruncation_resolution_limit_product_degreewise_is_kernel S i
  have hexact : T.Exact := T.exact_of_f_is_kernel hkernel
  have hmono : Mono T.f := mono_of_isLimit_fork hkernel
  let σ : T.Splitting :=
    ShortComplex.Splitting.ofExactOfSection T hexact
      (lowerTruncation_resolution_stage_difference_section S i)
      (lowerTruncation_resolution_stage_difference_section_comp S i) hmono
  exact σ.shortExact

-- Proof sketch: `S.intoLimit_comp_π` identifies the canonical map into `lim I_n^•` with the
-- stagewise comparison maps of the lower truncation resolution system, so `Q.map S.intoLimit` is
-- a compatible comparison from `Q.obj K` to the derived-limit model `Q.obj (lim I_n^•)`.
/-- The canonical map `K^• ⟶ lim I_n^•` attached to the chosen injective lower truncation system
induces a compatible derived-limit comparison in the derived category. -/
theorem intoLimit_isLowerTruncationDerivedLimitComparison
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) :
    IsLowerTruncationDerivedLimitComparison K
      (Q.obj (limit S.diagram)) (Q.map S.intoLimit) := by
  -- Route correction: first fix the same product object as in the source proof, namely
  -- `Q.obj (∏ S.stage n)`, before packaging the split short exact sequence into a Milnor
  -- triangle.
  letI : HasProduct (inverseSystemFamily (derivedLowerTruncationTower K)) :=
    lowerTruncation_resolution_stage_product (𝒜 := 𝒜) S
  let ιprod := lowerTruncation_resolution_limit_to_product S
  let δprod := lowerTruncation_resolution_stage_difference S
  let Tprod : ShortComplex (CochainComplex 𝒜 ℤ) :=
    ShortComplex.mk ιprod δprod (lowerTruncation_resolution_limit_to_product_comp_difference S)
  refine ⟨inferInstance, Q.map ιprod, ?_, ?_⟩
  · -- Proof comment: the source split short exact row of complexes yields the required Milnor
    -- distinguished triangle after passing to the derived category.
    have hTprod : Tprod.ShortExact := by
      exact HomologicalComplex.shortExact_of_degreewise_shortExact Tprod
        (fun i ↦ by
          simpa [Tprod] using
            lowerTruncation_resolution_limit_product_degreewise_shortExact S i)
    refine ⟨DerivedCategory.triangleOfSESδ hTprod, ?_⟩
    -- Proof comment: rewrite the middle morphism of the derived triangle to the canonical Milnor
    -- difference map for the fixed product object.
    simpa [Tprod, DerivedCategory.triangleOfSES,
      q_map_stage_difference_eq_derivedLimitDifferenceMap (𝒜 := 𝒜) S] using
      DerivedCategory.triangleOfSES_distinguished hTprod
  · intro n
    -- Proof comment: compute the `n`th stage projection of the canonical comparison map and then
    -- cancel the derived isomorphism coming from the stagewise resolution comparison.
    calc
      Q.map S.intoLimit ≫ Q.map ιprod ≫
          Pi.π (inverseSystemFamily (derivedLowerTruncationTower K)) n =
        Q.map S.intoLimit ≫
          (Q.map (limit.π S.diagram (op n)) ≫
            (asIso (Q.map (S.comparison.app (op n)))).symm.hom) := by
              rw [Category.assoc, q_map_limit_to_product_comp_π (𝒜 := 𝒜) S n]
      _ =
        Q.map (S.intoLimit ≫ limit.π S.diagram (op n)) ≫
          (asIso (Q.map (S.comparison.app (op n)))).symm.hom := by
              simp [Functor.map_comp, Category.assoc]
      _ = Q.map (S.fromSource n) ≫
          (asIso (Q.map (S.comparison.app (op n)))).symm.hom := by
              rw [S.intoLimit_comp_π]
      _ = Q.map (K.πTruncGE (-(((n + 1 : ℕ)) : ℤ))) ≫
          (Q.map (S.comparison.app (op n)) ≫
            (asIso (Q.map (S.comparison.app (op n)))).symm.hom) := by
              simp [LowerTruncationResolutionSystem.fromSource, Functor.map_comp, Category.assoc]
      _ = Q.map (K.πTruncGE (-(((n + 1 : ℕ)) : ℤ))) := by
              simp [Category.assoc]
      _ = derivedLowerTruncationToStage K n := rfl

-- Proof sketch: the previous comparison theorem already packages the inverse-limit complex as a
-- compatible Milnor-model for the shifted lower truncation tower, so its target is a derived
-- limit by the owner-bridge above.
/-- The inverse limit complex of the chosen injective system represents the derived limit of the
shifted lower truncation tower `(τ_{\ge -(n + 1)} K^•)_n`. -/
theorem lowerTruncationResolutionSystemLimit_isDerivedLimit
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) :
    IsDerivedLimit (derivedLowerTruncationTower K)
      (Q.obj (limit S.diagram)) := by
  simpa using
    (intoLimit_isLowerTruncationDerivedLimitComparison S).isDerivedLimit

-- Proof sketch: `Q.map S.intoLimit` is a compatible comparison for the same shifted derived limit
-- as `c`, so `lowerTruncationDerivedLimitComparison_isIso_iff` reduces the claim to
-- `IsIso (Q.map S.intoLimit)`. The latter is equivalent to `S.intoLimit` being a quasi-isomorph-
-- ism by `DerivedCategory.isIso_Q_map_iff_quasiIso`.
/-- Lemma 13.34.6: if `K^• ⟶ \varprojlim I_n^•` is the canonical map to the inverse limit of the
injective lower truncation system and `c : K^• ⟶ R\!\varprojlim_n τ_{\ge -(n + 1)} K^•` is any
compatible derived-limit comparison morphism, then that canonical map is a quasi-isomorphism if
and only if `c` is an isomorphism in the derived category. -/
@[stacks 070M]
theorem lowerTruncationResolutionLimit_quasiIso_iff_isIso_derivedComparison
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K)
    {L : DerivedCategory 𝒜} {c : Q.obj K ⟶ L}
    (hc : IsLowerTruncationDerivedLimitComparison K L c) :
    QuasiIso S.intoLimit ↔ IsIso c := by
  -- Proof comment: compare `Q.map S.intoLimit` with the given compatible comparison `c`, then
  -- translate isomorphisms of `Q`-images back to quasi-isomorphisms of complexes.
  have hcomp :
      IsIso (Q.map S.intoLimit) ↔ IsIso c :=
    lowerTruncationDerivedLimitComparison_isIso_iff
      (intoLimit_isLowerTruncationDerivedLimitComparison S) hc
  rw [isIso_Q_map_iff_quasiIso] at hcomp
  exact hcomp

end

end CategoryTheory
