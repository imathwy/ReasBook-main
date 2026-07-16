import Mathlib
import stacks_proof.stacks_project.Chap12.Definition_12_24_1
import stacks_proof.stacks_project.Chap12.Lemma_12_19_12

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜]

/-
Domain-style sampling for Definition `12.24.5`.
- primary domain: filtered cochain complexes over a category with zero morphisms and, in the
  abelian case, the induced filtration on their cohomology;
- sampled core/canonical declarations in this domain:
  `FilteredComplex 𝒜`,
  `FilteredObject.stageFunctor`,
  `FilteredObject.stageFunctorToForget`,
  `FilteredObject.stageFunctorMapOfLE`,
  `FilteredObject.quotientFunctor`,
  `FilteredObject.associatedGradedFunctor`,
  `GradedObject.eval`;
- best owner abstraction: the canonical cochain-complex object
  `FilteredComplex 𝒜`, recalled in Definition `12.24.1`;
- primitive data: a filtered cochain complex `K : FilteredComplex 𝒜`;
- derived API: forgetting filtration, evaluating stages, graded pieces, the stagewise cohomology
  maps, the textbook notation `F^{p} K^•` and `gr^{p} K^•`, and the induced decreasing
  filtration on `H^n(K^•)`;
- source/core/bridge triage:
  `source-facing`: `inducedCohomologyFiltration`;
  `core/canonical`: the owner type `FilteredComplex 𝒜` and the filtered-object
  stage functors together with `associatedGradedFunctor ⋙ GradedObject.eval p`;
  `bridge/view`: `underlying`, `underlyingMap`, `stage`, `stageMap`, `stageInclusion`,
    `stageMapOfLE`, `gradedPiece`, and `cohomologyMap`. -/

namespace FilteredComplex

open FilteredObject

/-- Bridge/view layer: forget the filtration on the owner object of filtered cochain complexes. -/
abbrev underlying (K : FilteredComplex 𝒜) : CochainComplex 𝒜 ℤ :=
  (FilteredObject.forget.mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- Bridge/view layer: the morphism on underlying cochain complexes induced by a morphism of
filtered complexes. -/
abbrev underlyingMap {K L : FilteredComplex 𝒜} (α : K ⟶ L) :
    K.underlying ⟶ L.underlying :=
  (FilteredObject.forget.mapHomologicalComplex (ComplexShape.up ℤ)).map α

/-- Bridge/view layer: evaluate a filtered cochain complex at the `p`-th filtration stage. -/
abbrev stage (K : FilteredComplex 𝒜) (p : ℤ) : CochainComplex 𝒜 ℤ :=
  ((stageFunctor p).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- Textbook notation for the `p`-th filtration stage complex `F^p K^•`. -/
notation:max "F^{" p "} " K:max => FilteredComplex.stage K p

/-- Bridge/view layer: the morphism on `p`-th stage complexes induced by a morphism of filtered
complexes. -/
abbrev stageMap {K L : FilteredComplex 𝒜} (α : K ⟶ L) (p : ℤ) :
    K.stage p ⟶ L.stage p :=
  ((stageFunctor p).mapHomologicalComplex (ComplexShape.up ℤ)).map α

/-- Bridge/view layer: the canonical inclusion of the `p`-th filtration stage complex into the
underlying complex. -/
abbrev stageInclusion (K : FilteredComplex 𝒜) (p : ℤ) :
    K.stage p ⟶ K.underlying :=
  (NatTrans.mapHomologicalComplex (stageFunctorToForget p) (ComplexShape.up ℤ)).app K

/-- The canonical map from the `q`-th filtration stage complex to the `p`-th stage complex for
`p ≤ q`. -/
abbrev stageMapOfLE (K : FilteredComplex 𝒜) {p q : ℤ}
    (hpq : p ≤ q) : K.stage q ⟶ K.stage p :=
  (NatTrans.mapHomologicalComplex (stageFunctorMapOfLE hpq)
    (ComplexShape.up ℤ)).app K

/-- The canonical comparison map `F^p K^• ⟶ F^p K^•` is the identity. -/
theorem stageMapOfLE_refl (K : FilteredComplex 𝒜) (p : ℤ) :
    K.stageMapOfLE (show p ≤ p by rfl) = 𝟙 (K.stage p) := by
  ext n
  change
    Subobject.ofLE
        ((show FilteredObject 𝒜 from K.X n).filtration.obj p)
        ((show FilteredObject 𝒜 from K.X n).filtration.obj p)
        _ =
      𝟙 (Subobject.underlying.obj ((show FilteredObject 𝒜 from K.X n).filtration.obj p))
  rw [Subobject.ofLE_refl]

/-- Successive stage comparisons compose to the direct comparison. -/
theorem stageMapOfLE_comp (K : FilteredComplex 𝒜) {p q r : ℤ}
    (hpq : p ≤ q) (hqr : q ≤ r) :
    K.stageMapOfLE hqr ≫ K.stageMapOfLE hpq = K.stageMapOfLE (le_trans hpq hqr) := by
  have h :=
    congrArg
      (fun α ↦ (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K)
      (stageFunctorMapOfLE_comp hpq hqr)
  simpa [stageMapOfLE, NatTrans.mapHomologicalComplex_comp] using h

-- Proof sketch: check the equality degreewise after postcomposing with the inclusion
-- `((K.X n).filtration.obj q).arrow`; use `Subobject.ofLE_arrow`.
/-- The inclusion `F^q K^• ⟶ K^•` factors through `F^p K^• ⟶ K^•` whenever `p ≤ q`. -/
theorem stageMapOfLE_comp_stageInclusion (K : FilteredComplex 𝒜) {p q : ℤ}
    (hpq : p ≤ q) :
    stageMapOfLE K hpq ≫ stageInclusion K p = stageInclusion K q := by
  have h :=
    congrArg
      (fun α ↦ (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K)
      (stageFunctorMapOfLE_comp_stageFunctorToForget hpq)
  simpa [stageMapOfLE, stageInclusion, NatTrans.mapHomologicalComplex_comp] using h

section Graded

variable [HasZeroMorphisms 𝒜] [HasCokernels 𝒜]

/-- The associated graded complex `gr(K^•)` of a filtered complex. -/
noncomputable abbrev associatedGraded (K : FilteredComplex 𝒜) :
    CochainComplex (GradedObject ℤ 𝒜) ℤ :=
  (associatedGradedFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- The morphism on associated graded complexes induced by a morphism of filtered complexes. -/
noncomputable abbrev associatedGradedMap {K L : FilteredComplex 𝒜} (α : K ⟶ L) :
    K.associatedGraded ⟶ L.associatedGraded :=
  (associatedGradedFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).map α

section GradedHomology

variable [CategoryWithHomology (GradedObject ℤ 𝒜)]

noncomputable instance associatedGraded_hasHomology (K : FilteredComplex 𝒜) (n : ℤ) :
    HomologicalComplex.HasHomology K.associatedGraded n :=
  inferInstanceAs
    (HomologicalComplex.HasHomology
      ((associatedGradedFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n)

end GradedHomology

/-- The `p`-th graded piece `gr^p(K^•) = F^p K^• / F^{p + 1} K^•` of a filtered complex. -/
noncomputable abbrev gradedPiece (K : FilteredComplex 𝒜) (p : ℤ) :
    CochainComplex 𝒜 ℤ :=
  ((associatedGradedFunctor ⋙ GradedObject.eval p).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K

/-- Textbook notation for the graded-piece complex `gr^p(K^•)`. -/
notation:max "gr^{" p "} " K:max => FilteredComplex.gradedPiece K p

/-- The morphism induced on the `p`-th graded-piece complexes by a morphism of filtered
complexes. -/
noncomputable abbrev gradedPieceMap {K L : FilteredComplex 𝒜} (α : K ⟶ L) (p : ℤ) :
    gradedPiece K p ⟶ gradedPiece L p :=
  ((associatedGradedFunctor ⋙ GradedObject.eval p).mapHomologicalComplex
    (ComplexShape.up ℤ)).map α

end Graded

section CohomologyMap

variable [CategoryWithHomology 𝒜]

private noncomputable instance stage_hasHomology (K : FilteredComplex 𝒜) (p n : ℤ) :
    HomologicalComplex.HasHomology (stage K p) n :=
  inferInstanceAs
    (HomologicalComplex.HasHomology
      (((stageFunctor p).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n)

private noncomputable instance underlying_hasHomology (K : FilteredComplex 𝒜) (n : ℤ) :
    HomologicalComplex.HasHomology (underlying K) n :=
  inferInstanceAs
    (HomologicalComplex.HasHomology
      ((FilteredObject.forget.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n)

/-- The map on degree-`n` cohomology induced by the inclusion `F^p K^• ⟶ K^•`. -/
noncomputable abbrev cohomologyMap (K : FilteredComplex 𝒜) (p n : ℤ) :
    (stage K p).homology n ⟶ (underlying K).homology n :=
  HomologicalComplex.homologyMap (stageInclusion K p) n

-- Proof sketch: apply `HomologicalComplex.homologyMap_comp` to
-- `stageMapOfLE_comp_inclusion`.
/-- The cohomology map from `F^q K^•` to `H^n(K^•)` factors through the one from `F^p K^•` when
`p ≤ q`. -/
private theorem cohomologyMap_factorization (K : FilteredComplex 𝒜) {p q n : ℤ}
    (hpq : p ≤ q) :
    K.cohomologyMap q n =
      HomologicalComplex.homologyMap (K.stageMapOfLE hpq) n ≫ K.cohomologyMap p n := by
  rw [cohomologyMap, ← HomologicalComplex.homologyMap_comp, stageMapOfLE_comp_stageInclusion]

end CohomologyMap

section CohomologyFiltration

variable [HasImages 𝒜] [CategoryWithHomology 𝒜]

-- Proof sketch: use `cohomologyMap_factorization` and `Limits.imageSubobject_comp_le` to compare
-- the images for `q` and `p`.
/-- The images of the stagewise cohomology maps form a decreasing filtration. -/
private theorem inducedCohomologyFiltration_antitone (K : FilteredComplex 𝒜)
    (n : ℤ) : Antitone (fun p : ℤ ↦ imageSubobject (K.cohomologyMap p n)) := by
  intro p q hpq
  change imageSubobject (K.cohomologyMap q n) ≤ imageSubobject (K.cohomologyMap p n)
  rw [cohomologyMap_factorization K hpq]
  exact imageSubobject_comp_le _ _

/-- Definition 12.24.5: for a filtered complex `(K^•, F)` in an abelian category, the induced
filtration on `H^n(K^•)` is the decreasing filtration defined by
`F^p H^n(K^•) = \operatorname{Im}(H^n(F^p K^•) \to H^n(K^•))`. -/
@[stacks 012P]
noncomputable def inducedCohomologyFiltration (K : FilteredComplex 𝒜)
    (n : ℤ) : DecreasingFiltration (K.underlying.homology n) where
  toFun p := imageSubobject (K.cohomologyMap p n)
  monotone' := by
    intro p q hpq
    exact inducedCohomologyFiltration_antitone K n hpq

-- Proof sketch: unfold `inducedCohomologyFiltration`; the statement is exactly its defining
-- formula.
/-- The `p`-th stage of the induced cohomology filtration is the image of the map
`H^n(F^p K^•) ⟶ H^n(K^•)`. -/
theorem inducedCohomologyFiltration_obj (K : FilteredComplex 𝒜) (n p : ℤ) :
    (K.inducedCohomologyFiltration n).obj p = imageSubobject (K.cohomologyMap p n) := rfl

end CohomologyFiltration

end FilteredComplex

/-- Chapter `15` source-facing vocabulary: a filtered cochain complex is the same owner object as
the chapter-level filtered complex. This stable abbreviation is kept because it is used
pervasively downstream when the cochain-complex viewpoint is primary. -/
abbrev FilteredCochainComplex (𝒜 : Type u) [Category.{v} 𝒜] [HasZeroMorphisms 𝒜] :=
  FilteredComplex 𝒜

namespace FilteredCochainComplex

/-- Bridge/view layer: forget the source-facing name and return the canonical owner object from
Chapter `12`. -/
abbrev toFilteredComplex {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜]
    (K : FilteredCochainComplex 𝒜) : FilteredComplex 𝒜 :=
  K

/-- Bridge/view layer: forget the filtration on a filtered cochain complex. -/
abbrev underlying {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜]
    (K : FilteredCochainComplex 𝒜) : CochainComplex 𝒜 ℤ :=
  FilteredComplex.underlying K

/-- Bridge/view layer: evaluate a filtered cochain complex at the `p`-th filtration stage. -/
abbrev stage {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜]
    (K : FilteredCochainComplex 𝒜) (p : ℤ) : CochainComplex 𝒜 ℤ :=
  FilteredComplex.stage K p

/-- Bridge/view layer: the canonical inclusion of the `p`-th stage into the underlying cochain
complex. -/
abbrev stageInclusion {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜]
    (K : FilteredCochainComplex 𝒜) (p : ℤ) : K.stage p ⟶ K.underlying :=
  FilteredComplex.stageInclusion K p

/-- Bridge/view layer: the canonical comparison map `F^q K^• ⟶ F^p K^•` for `p ≤ q`. -/
abbrev stageMapOfLE {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜]
    (K : FilteredCochainComplex 𝒜) {p q : ℤ} (hpq : p ≤ q) : K.stage q ⟶ K.stage p :=
  FilteredComplex.stageMapOfLE K hpq

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜] [HasCokernels 𝒜]

/-- Bridge/view layer: the `p`-th graded-piece cochain complex of a filtered cochain complex. -/
noncomputable abbrev gradedPiece (K : FilteredCochainComplex 𝒜) (p : ℤ) :
    CochainComplex 𝒜 ℤ :=
  FilteredComplex.gradedPiece K p

end

end FilteredCochainComplex

end CategoryTheory
