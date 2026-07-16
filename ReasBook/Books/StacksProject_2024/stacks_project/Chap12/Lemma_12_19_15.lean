import Mathlib.Tactic.Recall
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import StacksProject_2024.stacks_project.Chap12.Definition_12_19_3

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe v u

noncomputable section

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

namespace ShortComplex

open FilteredObject FilteredObject.Hom

section MinimalFunctorAPI

-- Route correction: `Lemma_12_19_12` is currently not buildable in this workspace, but this item
-- only needs the stage/quotient/associated-graded functorial API from its first half. We inline
-- that minimal owner API here so the current entry remains compilable while the proof plan for the
-- five source-facing consequences is stabilized.

section Quotients

variable [HasZeroMorphisms 𝒜] [HasCokernels 𝒜]

/-- Helper for Lemma 12.19.15: the quotient object `A / F^p A`. -/
private abbrev filteredQuotient (A : FilteredObject 𝒜) (p : ℤ) : 𝒜 :=
  cokernel (A.filtration.obj p).arrow

end Quotients

section StageMaps

variable [HasZeroMorphisms 𝒜]

/-- Helper for Lemma 12.19.15: the stage map induced by the identity filtered morphism is the
identity on the stage. -/
private theorem stageMap_id (A : FilteredObject 𝒜) (p : ℤ) :
    stageMap (𝟙 A) p = 𝟙 (F^{p} A) := by
  -- Compare both candidates after postcomposing with the mono stage inclusion.
  exact (cancel_mono (A.filtration.obj p).arrow).1 (by
    rw [stageMap_comm]
    simp)

/-- Helper for Lemma 12.19.15: stage maps respect composition of filtered morphisms. -/
private theorem stageMap_comp {A B D : FilteredObject 𝒜} (f : A ⟶ B) (g : B ⟶ D) (p : ℤ) :
    stageMap (f ≫ g) p = stageMap f p ≫ stageMap g p := by
  -- Reduce the comparison to the underlying ambient composite by cancelling the target inclusion.
  exact (cancel_mono (D.filtration.obj p).arrow).1 (by
    calc
      stageMap (f ≫ g) p ≫ (D.filtration.obj p).arrow
          = (A.filtration.obj p).arrow ≫ (f ≫ g).hom := by
              rw [stageMap_comm]
      _ = ((A.filtration.obj p).arrow ≫ f.hom) ≫ g.hom := by
            simp [Category.assoc]
      _ = (stageMap f p ≫ (B.filtration.obj p).arrow) ≫ g.hom := by
            rw [stageMap_comm]
      _ = stageMap f p ≫ (stageMap g p ≫ (D.filtration.obj p).arrow) := by
            rw [stageMap_comm]
            simp [Category.assoc]
      _ = (stageMap f p ≫ stageMap g p) ≫ (D.filtration.obj p).arrow := by
            simp [Category.assoc])

/-- Helper for Lemma 12.19.15: the zero filtered morphism induces the zero map on every stage. -/
private theorem stageMap_zero (A B : FilteredObject 𝒜) (p : ℤ) :
    stageMap (0 : A ⟶ B) p = 0 := by
  -- Cancel the mono stage inclusion and reduce to the ambient zero composite.
  exact (cancel_mono (B.filtration.obj p).arrow).1 (by
    rw [stageMap_comm]
    simp)

end StageMaps

section GradedMaps

variable [HasZeroMorphisms 𝒜] [HasCokernels 𝒜]

/-- Helper for Lemma 12.19.15: the map induced on the `p`-th graded piece by a filtered
morphism. -/
abbrev gradedPieceMap {A B : FilteredObject 𝒜} (f : A ⟶ B) (p : ℤ) :
    gr^{p} A ⟶ gr^{p} B :=
  cokernel.map (A.filtration.stageInclusion p) (B.filtration.stageInclusion p)
    (stageMap f (p + 1)) (stageMap f p)
    (stageInclusion_naturality f p)

/-- Helper for Lemma 12.19.15: the map on associated graded objects induced by a filtered
morphism. -/
def associatedGradedMap {A B : FilteredObject 𝒜} (f : A ⟶ B) :
    A.associatedGraded ⟶ B.associatedGraded :=
  fun p ↦ gradedPieceMap f p

/-- Helper for Lemma 12.19.15: graded-piece maps preserve identities. -/
private theorem gradedPieceMap_id (A : FilteredObject 𝒜) (p : ℤ) :
    gradedPieceMap (𝟙 A) p = 𝟙 (gr^{p} A) := by
  -- Compare after precomposing with the defining cokernel projection.
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [gradedPieceMap, stageMap_id])

/-- Helper for Lemma 12.19.15: graded-piece maps respect composition. -/
private theorem gradedPieceMap_comp {A B D : FilteredObject 𝒜} (f : A ⟶ B) (g : B ⟶ D) (p : ℤ) :
    gradedPieceMap (f ≫ g) p = gradedPieceMap f p ≫ gradedPieceMap g p := by
  -- Compare after precomposing with the same cokernel projection and use stage-map functoriality.
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [gradedPieceMap, Category.assoc, stageMap_comp])

/-- Helper for Lemma 12.19.15: graded-piece maps send zero morphisms to zero. -/
private theorem gradedPieceMap_zero (A B : FilteredObject 𝒜) (p : ℤ) :
    gradedPieceMap (0 : A ⟶ B) p = 0 := by
  -- The graded map of zero vanishes once the source cokernel projection is cancelled.
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [gradedPieceMap, stageMap_zero])

/-- Helper for Lemma 12.19.15: associated-graded maps preserve identities. -/
private theorem associatedGradedMap_id (A : FilteredObject 𝒜) :
    associatedGradedMap (𝟙 A) = 𝟙 A.associatedGraded := by
  -- Equality of graded-object morphisms is degreewise equality on graded pieces.
  ext p
  simpa using gradedPieceMap_id A p

/-- Helper for Lemma 12.19.15: associated-graded maps respect composition. -/
private theorem associatedGradedMap_comp {A B D : FilteredObject 𝒜} (f : A ⟶ B) (g : B ⟶ D) :
    associatedGradedMap (f ≫ g) = associatedGradedMap f ≫ associatedGradedMap g := by
  -- Again, reduce to the degreewise statement on graded pieces.
  ext p
  simpa using gradedPieceMap_comp f g p

/-- Helper for Lemma 12.19.15: associated-graded maps preserve zero morphisms. -/
private theorem associatedGradedMap_zero (A B : FilteredObject 𝒜) :
    associatedGradedMap (0 : A ⟶ B) = 0 := by
  -- Pointwise zero follows from the graded-piece zero comparison.
  ext p
  simpa using gradedPieceMap_zero A B p

end GradedMaps

section QuotientMaps

variable [HasZeroMorphisms 𝒜] [HasCokernels 𝒜]

/-- Helper for Lemma 12.19.15: the morphism on the quotients `A / F^p A ⟶ B / F^p B` induced by
a filtered morphism. -/
abbrev quotientMap {A B : FilteredObject 𝒜} (f : A ⟶ B) (p : ℤ) :
    filteredQuotient A p ⟶ filteredQuotient B p :=
  cokernel.map (A.filtration.obj p).arrow (B.filtration.obj p).arrow (stageMap f p) f.hom
    (stageMap_comm f p).symm

/-- Helper for Lemma 12.19.15: quotient maps commute with the cokernel projections. -/
theorem quotientMap_comm {A B : FilteredObject 𝒜} (f : A ⟶ B) (p : ℤ) :
    cokernel.π (A.filtration.obj p).arrow ≫ quotientMap f p =
      f.hom ≫ cokernel.π (B.filtration.obj p).arrow := by
  -- This is the defining commutative square of `cokernel.map`.
  simp [quotientMap]

/-- Helper for Lemma 12.19.15: quotient maps preserve identities. -/
private theorem quotientMap_id (A : FilteredObject 𝒜) (p : ℤ) :
    quotientMap (𝟙 A) p = 𝟙 (filteredQuotient A p) := by
  -- Compare after precomposing with the quotient projection from `A`.
  refine (cancel_epi (cokernel.π (A.filtration.obj p).arrow)).1 ?_
  have h₁ :
      cokernel.π (A.filtration.obj p).arrow ≫ quotientMap (𝟙 A) p =
        cokernel.π (A.filtration.obj p).arrow := by
    rw [quotientMap_comm]
    simp
  have h₂ :
      cokernel.π (A.filtration.obj p).arrow =
        cokernel.π (A.filtration.obj p).arrow ≫ 𝟙 (filteredQuotient A p) := by
    simp
  exact h₁.trans h₂

/-- Helper for Lemma 12.19.15: quotient maps respect composition. -/
private theorem quotientMap_comp {A B D : FilteredObject 𝒜} (f : A ⟶ B) (g : B ⟶ D) (p : ℤ) :
    quotientMap (f ≫ g) p = quotientMap f p ≫ quotientMap g p := by
  -- Reduce the comparison to the universal quotient projections.
  refine (cancel_epi (cokernel.π (A.filtration.obj p).arrow)).1 ?_
  have h₁ :
      cokernel.π (A.filtration.obj p).arrow ≫ quotientMap (f ≫ g) p =
        (f ≫ g).hom ≫ cokernel.π (D.filtration.obj p).arrow :=
    quotientMap_comm (f ≫ g) p
  have h₂ :
      (f ≫ g).hom ≫ cokernel.π (D.filtration.obj p).arrow =
        f.hom ≫ (cokernel.π (B.filtration.obj p).arrow ≫ quotientMap g p) := by
    rw [quotientMap_comm]
    simp [Category.assoc]
  have h₃ :
      f.hom ≫ (cokernel.π (B.filtration.obj p).arrow ≫ quotientMap g p) =
        cokernel.π (A.filtration.obj p).arrow ≫ (quotientMap f p ≫ quotientMap g p) := by
    calc
      f.hom ≫ (cokernel.π (B.filtration.obj p).arrow ≫ quotientMap g p)
          = (f.hom ≫ cokernel.π (B.filtration.obj p).arrow) ≫ quotientMap g p := by
              simp [Category.assoc]
      _ = (cokernel.π (A.filtration.obj p).arrow ≫ quotientMap f p) ≫ quotientMap g p := by
            exact congrArg (fun k ↦ k ≫ quotientMap g p) (quotientMap_comm f p).symm
      _ = cokernel.π (A.filtration.obj p).arrow ≫ (quotientMap f p ≫ quotientMap g p) := by
            simp [Category.assoc]
  exact h₁.trans (h₂.trans h₃)

/-- Helper for Lemma 12.19.15: quotient maps send zero morphisms to zero. -/
private theorem quotientMap_zero (A B : FilteredObject 𝒜) (p : ℤ) :
    quotientMap (0 : A ⟶ B) p = 0 := by
  -- The quotient projection from `A` detects equality, so reduce to the ambient zero composite.
  refine (cancel_epi (cokernel.π (A.filtration.obj p).arrow)).1 ?_
  calc
    cokernel.π (A.filtration.obj p).arrow ≫ quotientMap (0 : A ⟶ B) p
        = (0 : A.obj ⟶ B.obj) ≫ cokernel.π (B.filtration.obj p).arrow := quotientMap_comm 0 p
    _ = 0 := by simp
    _ = cokernel.π (A.filtration.obj p).arrow ≫ 0 := by simp

end QuotientMaps

section FunctorAPI

variable [HasZeroMorphisms 𝒜] [HasCokernels 𝒜]

/-- Helper for Lemma 12.19.15: the `p`-th filtration-stage functor on filtered objects. -/
def stageFunctor (p : ℤ) : FilteredObject 𝒜 ⥤ 𝒜 where
  obj A := F^{p} A
  map f := stageMap f p
  map_id A := stageMap_id A p
  map_comp f g := stageMap_comp f g p

/-- Helper for Lemma 12.19.15: the quotient-by-`F^p` functor on filtered objects. -/
def quotientFunctor (p : ℤ) : FilteredObject 𝒜 ⥤ 𝒜 where
  obj A := filteredQuotient A p
  map f := quotientMap f p
  map_id A := quotientMap_id A p
  map_comp f g := quotientMap_comp f g p

/-- Helper for Lemma 12.19.15: the associated graded functor on filtered objects. -/
def associatedGradedFunctor : FilteredObject 𝒜 ⥤ GradedObject ℤ 𝒜 where
  obj A := A.associatedGraded
  map f := associatedGradedMap f
  map_id A := associatedGradedMap_id A
  map_comp f g := associatedGradedMap_comp f g

instance (p : ℤ) : ((stageFunctor p : FilteredObject 𝒜 ⥤ 𝒜)).PreservesZeroMorphisms where
  map_zero A B := stageMap_zero A B p

instance (p : ℤ) : ((quotientFunctor p : FilteredObject 𝒜 ⥤ 𝒜)).PreservesZeroMorphisms where
  map_zero A B := quotientMap_zero A B p

instance :
    ((associatedGradedFunctor : FilteredObject 𝒜 ⥤ GradedObject ℤ 𝒜)).PreservesZeroMorphisms where
  map_zero A B := associatedGradedMap_zero A B

end FunctorAPI

section ZeroMorphismInstances

variable [HasZeroMorphisms 𝒜]

/-- Helper for Lemma 12.19.15: evaluation at a fixed graded degree preserves zero morphisms. -/
instance gradedObject_eval_preservesZeroMorphisms (p : ℤ) :
    (GradedObject.eval p : GradedObject ℤ 𝒜 ⥤ 𝒜).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- Helper for Lemma 12.19.15: the forgetful functor on filtered objects preserves zero
morphisms. -/
instance filteredObject_forget_preservesZeroMorphisms :
    (FilteredObject.forget : FilteredObject 𝒜 ⥤ 𝒜).PreservesZeroMorphisms where
  map_zero _ _ := rfl

end ZeroMorphismInstances

end MinimalFunctorAPI

/- Domain-style sampling for Lemma 12.19.15:
- primary domain: filtered objects in an abelian category, viewed through short-complex exactness
- sampled owner declarations:
  `FilteredObject.IsFinite`,
  `FilteredObject.Hom.Strict`,
  `associatedGradedFunctor`,
  `GradedObject.eval`,
  `ShortComplex.Exact.map`
- owner abstraction used here: exactness of a short complex after applying the canonical filtered
  functors `associatedGradedFunctor`, `stageFunctor`, and `quotientFunctor`
- primitive data: a short complex `S : ShortComplex (FilteredObject 𝒜)` and finiteness of its
  three filtered terms
- derived API: degreewise exactness, stage exactness, quotient exactness, strictness, and
  exactness of the underlying short complex
- source/core/bridge triage:
  `(1)` is a `source-facing` bridge theorem obtained from the canonical owner
  `ShortComplex.Exact.map` by evaluating the associated graded short complex in degree `p`;
  `(2)` through `(5)` are `source-facing` bridge theorems for filtered short complexes. 
-/

variable {S : ShortComplex (FilteredObject 𝒜)}

/-- Lemma 12.19.15 (1): if the associated graded complex is exact, then
`gr^p(A) ⟶ gr^p(B) ⟶ gr^p(C)` is exact for every `p`. This is the source-facing specialization of
the owner theorem `ShortComplex.Exact.map` along the evaluation functor `GradedObject.eval p`. -/
theorem gradedPiece_exact_of_associatedGraded_exact
    (hgr : ShortComplex.Exact (S.map associatedGradedFunctor)) (p : ℤ) :
    ShortComplex.Exact (S.map (associatedGradedFunctor ⋙ GradedObject.eval p)) := by
  let E := piEquivalenceFunctorDiscrete ℤ 𝒜
  letI : Functor.PreservesHomology (GradedObject.eval p : GradedObject ℤ 𝒜 ⥤ 𝒜) :=
    { preservesKernels := by
        intro X Y f
        simpa [E, GradedObject.eval] using
          (inferInstance : PreservesLimit (parallelPair f 0)
            (E.functor ⋙ (evaluation (Discrete ℤ) 𝒜).obj (Discrete.mk p)))
      preservesCokernels := by
        intro X Y f
        simpa [E, GradedObject.eval] using
          (inferInstance : PreservesColimit (parallelPair f 0)
            (E.functor ⋙ (evaluation (Discrete ℤ) 𝒜).obj (Discrete.mk p))) }
  simpa using hgr.map (GradedObject.eval p : GradedObject ℤ 𝒜 ⥤ 𝒜)

section FiniteFiltrations

/-- Helper for Lemma 12.19.15: once a filtration stage is zero, all later stages are zero. -/
private theorem filtration_eq_bot_of_le {X : FilteredObject 𝒜} {p q : ℤ}
    (hpq : p ≤ q) (hp : X.filtration.obj p = ⊥) :
    X.filtration.obj q = ⊥ := by
  -- Antitonicity pushes the zero stage forward along the decreasing filtration.
  apply bot_unique
  simpa [hp] using X.filtration.antitone_obj hpq

/-- Helper for Lemma 12.19.15: once a filtration stage is the whole object, all earlier stages are
also the whole object. -/
private theorem filtration_eq_top_of_le {X : FilteredObject 𝒜} {p q : ℤ}
    (hpq : p ≤ q) (hq : X.filtration.obj q = ⊤) :
    X.filtration.obj p = ⊤ := by
  -- Antitonicity pulls the top stage backward along the decreasing filtration.
  apply top_unique
  simpa [hq] using X.filtration.antitone_obj hpq

/-- Helper for Lemma 12.19.15: a zero filtration stage is the explicit zero subobject. -/
private theorem stage_eq_mk_zero_of_eq_bot (X : FilteredObject 𝒜) (p : ℤ)
    (hp : X.filtration.obj p = ⊥) :
    X.filtration.obj p = Subobject.mk (0 : (0 : 𝒜) ⟶ X.obj) := by
  -- Rewrite the bottom subobject into the canonical zero-arrow model.
  simpa [Subobject.bot_eq_zero] using hp

/-- Helper for Lemma 12.19.15: a zero filtration stage has zero underlying object. -/
private theorem stage_isZero_of_eq_bot (X : FilteredObject 𝒜) (p : ℤ)
    (hp : X.filtration.obj p = ⊥) :
    IsZero (F^{p} X) := by
  -- Transport the zero-object witness across the canonical identification with `0`.
  let e : F^{p} X ≅ 0 :=
    Subobject.isoOfEqMk (X.filtration.obj p) (0 : (0 : 𝒜) ⟶ X.obj)
      (stage_eq_mk_zero_of_eq_bot X p hp)
  exact Limits.IsZero.of_iso (Limits.isZero_zero 𝒜) e

/-- Helper for Lemma 12.19.15: the canonical stage row
`0 ⟶ F^(p + 1) X ⟶ F^p X ⟶ gr^p X ⟶ 0` is short exact. -/
private theorem stage_row_shortExact (X : FilteredObject 𝒜) (p : ℤ) :
    (ShortComplex.mk
      (X.filtration.stageInclusion p)
      (cokernel.π (X.filtration.stageInclusion p))
      (cokernel.condition _)).ShortExact := by
  -- This is the universal short exact sequence attached to the cokernel of a monomorphism.
  refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
  exact ShortComplex.exact_cokernel (X.filtration.stageInclusion p)

/-- Helper for Lemma 12.19.15: a morphism into the codomain of an epimorphism lifts after
refining the source by an epimorphism. -/
private theorem exists_refinement_lift_of_epi {X Y A : 𝒜} (e : X ⟶ Y) [Epi e] (y : A ⟶ Y) :
    ∃ (A' : 𝒜) (π : A' ⟶ A) (_ : Epi π) (x : A' ⟶ X), π ≫ y = x ≫ e := by
  -- Realize the lift on the pullback of `e` along `y`; the projection to `A` is epi.
  refine ⟨pullback e y, pullback.snd e y, inferInstance, pullback.fst e y, ?_⟩
  simpa using (pullback.condition (f := e) (g := y)).symm

/-- Helper for Lemma 12.19.15: the transition map
`X / F^(p + 1) X ⟶ X / F^p X`. -/
private abbrev quotientTransition (X : FilteredObject 𝒜) (p : ℤ) :
    filteredQuotient X (p + 1) ⟶ filteredQuotient X p :=
  cokernel.desc (X.filtration.obj (p + 1)).arrow
    (cokernel.π (X.filtration.obj p).arrow)
    (by
      -- The quotient by `F^p X` already kills the smaller stage `F^(p + 1) X`.
      have hstageArrow :
          X.filtration.stageInclusion p ≫ (X.filtration.obj p).arrow =
            (X.filtration.obj (p + 1)).arrow := by
        exact Subobject.ofLE_arrow (X.filtration.succ_le p)
      rw [← hstageArrow, Category.assoc, cokernel.condition]
      simp)

/-- Helper for Lemma 12.19.15: the transition map out of `X / F^(p + 1) X` is induced by the
canonical quotient projection from `X`. -/
private theorem quotientTransition_comm (X : FilteredObject 𝒜) (p : ℤ) :
    cokernel.π (X.filtration.obj (p + 1)).arrow ≫ quotientTransition X p =
      cokernel.π (X.filtration.obj p).arrow := by
  -- This is the defining equation of the quotient transition map.
  simp [quotientTransition]

/-- Helper for Lemma 12.19.15: the transition map `X / F^(p + 1) X ⟶ X / F^p X` is epic. -/
private theorem quotientTransition_epi (X : FilteredObject 𝒜) (p : ℤ) :
    Epi (quotientTransition X p) := by
  -- The canonical quotient projection to `X / F^p X` factors through `quotientTransition X p`.
  exact epi_of_epi_fac (quotientTransition_comm X p)

/-- Helper for Lemma 12.19.15: the degree-`p` graded piece maps canonically to
`X / F^(p + 1) X`. -/
private abbrev gradedToQuotient (X : FilteredObject 𝒜) (p : ℤ) :
    gr^{p} X ⟶ filteredQuotient X (p + 1) :=
  cokernel.desc (X.filtration.stageInclusion p)
    ((X.filtration.obj p).arrow ≫ cokernel.π (X.filtration.obj (p + 1)).arrow)
    (by
      -- The quotient by `F^(p + 1) X` kills the image of the consecutive stage inclusion.
      simp [DecreasingFiltration.stageInclusion, Category.assoc])

/-- Helper for Lemma 12.19.15: the map `gr^p X ⟶ X / F^(p + 1) X` is induced from the ambient
stage inclusion `F^p X ⟶ X`. -/
private theorem gradedToQuotient_comm (X : FilteredObject 𝒜) (p : ℤ) :
    cokernel.π (X.filtration.stageInclusion p) ≫ gradedToQuotient X p =
      (X.filtration.obj p).arrow ≫ cokernel.π (X.filtration.obj (p + 1)).arrow := by
  -- This is the defining equation of the graded-to-quotient map.
  simp [gradedToQuotient]

/-- Helper for Lemma 12.19.15: the consecutive quotient-transition maps are natural in filtered
morphisms. -/
private theorem quotientTransition_naturality
    {A B : FilteredObject 𝒜} (f : A ⟶ B) (p : ℤ) :
    quotientMap f (p + 1) ≫ quotientTransition B p =
      quotientTransition A p ≫ quotientMap f p := by
  -- Compare both composites after precomposing with the quotient projection from `A / F^(p + 1)A`.
  refine (cancel_epi (cokernel.π (A.filtration.obj (p + 1)).arrow)).1 ?_
  calc
    cokernel.π (A.filtration.obj (p + 1)).arrow ≫ quotientMap f (p + 1) ≫ quotientTransition B p
        = (cokernel.π (A.filtration.obj (p + 1)).arrow ≫ quotientMap f (p + 1)) ≫
            quotientTransition B p := by
              simp [Category.assoc]
    _ = (f.hom ≫ cokernel.π (B.filtration.obj (p + 1)).arrow) ≫ quotientTransition B p := by
          rw [quotientMap_comm]
    _ = f.hom ≫ cokernel.π (B.filtration.obj (p + 1)).arrow ≫ quotientTransition B p := by
          simp [Category.assoc]
    _ = f.hom ≫ cokernel.π (B.filtration.obj p).arrow := by
          rw [quotientTransition_comm]
    _ = cokernel.π (A.filtration.obj p).arrow ≫ quotientMap f p := by
          rw [quotientMap_comm]
    _ = cokernel.π (A.filtration.obj (p + 1)).arrow ≫
          (quotientTransition A p ≫ quotientMap f p) := by
          calc
            cokernel.π (A.filtration.obj p).arrow ≫ quotientMap f p
                = (cokernel.π (A.filtration.obj (p + 1)).arrow ≫ quotientTransition A p) ≫
                    quotientMap f p := by rw [quotientTransition_comm]
            _ = cokernel.π (A.filtration.obj (p + 1)).arrow ≫
                  (quotientTransition A p ≫ quotientMap f p) := by
                    simp [Category.assoc]

/-- Helper for Lemma 12.19.15: the graded-to-quotient comparison maps are natural in filtered
morphisms. -/
private theorem gradedToQuotient_naturality
    {A B : FilteredObject 𝒜} (f : A ⟶ B) (p : ℤ) :
    gradedPieceMap f p ≫ gradedToQuotient B p =
      gradedToQuotient A p ≫ quotientMap f (p + 1) := by
  -- Compare both composites after precomposing with the source graded-piece projection.
  refine (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 ?_
  calc
    cokernel.π (A.filtration.stageInclusion p) ≫ gradedPieceMap f p ≫ gradedToQuotient B p
        = stageMap f p ≫ cokernel.π (B.filtration.stageInclusion p) ≫ gradedToQuotient B p := by
            simp [gradedPieceMap, Category.assoc]
    _ = stageMap f p ≫ (B.filtration.obj p).arrow ≫
          cokernel.π (B.filtration.obj (p + 1)).arrow := by
          rw [gradedToQuotient_comm]
    _ = (A.filtration.obj p).arrow ≫ f.hom ≫ cokernel.π (B.filtration.obj (p + 1)).arrow := by
          calc
            stageMap f p ≫ (B.filtration.obj p).arrow ≫ cokernel.π (B.filtration.obj (p + 1)).arrow
                = (stageMap f p ≫ (B.filtration.obj p).arrow) ≫
                    cokernel.π (B.filtration.obj (p + 1)).arrow := by
                      simp [Category.assoc]
            _ = ((A.filtration.obj p).arrow ≫ f.hom) ≫
                  cokernel.π (B.filtration.obj (p + 1)).arrow := by
                    rw [stageMap_comm]
            _ = (A.filtration.obj p).arrow ≫ f.hom ≫
                  cokernel.π (B.filtration.obj (p + 1)).arrow := by
                    simp [Category.assoc]
    _ = (A.filtration.obj p).arrow ≫ cokernel.π (A.filtration.obj (p + 1)).arrow ≫
          quotientMap f (p + 1) := by
          calc
            (A.filtration.obj p).arrow ≫ f.hom ≫ cokernel.π (B.filtration.obj (p + 1)).arrow
                = (A.filtration.obj p).arrow ≫
                    (f.hom ≫ cokernel.π (B.filtration.obj (p + 1)).arrow) := by
                      simp [Category.assoc]
            _ = (A.filtration.obj p).arrow ≫
                  (cokernel.π (A.filtration.obj (p + 1)).arrow ≫ quotientMap f (p + 1)) := by
                    rw [quotientMap_comm]
            _ = (A.filtration.obj p).arrow ≫ cokernel.π (A.filtration.obj (p + 1)).arrow ≫
                  quotientMap f (p + 1) := by
                    simp [Category.assoc]
    _ = cokernel.π (A.filtration.stageInclusion p) ≫ gradedToQuotient A p ≫
          quotientMap f (p + 1) := by
          calc
            (A.filtration.obj p).arrow ≫ cokernel.π (A.filtration.obj (p + 1)).arrow ≫
                quotientMap f (p + 1)
                = (cokernel.π (A.filtration.stageInclusion p) ≫ gradedToQuotient A p) ≫
                    quotientMap f (p + 1) := by
                      rw [gradedToQuotient_comm]
                      simp [Category.assoc]
            _ = cokernel.π (A.filtration.stageInclusion p) ≫ gradedToQuotient A p ≫
                  quotientMap f (p + 1) := by
                    simp [Category.assoc]

/-- Helper for Lemma 12.19.15: the quotient row
`gr^p X ⟶ X / F^(p + 1) X ⟶ X / F^p X` is exact. -/
private theorem quotient_row_exact (X : FilteredObject 𝒜) (p : ℤ) :
    (ShortComplex.mk
      (gradedToQuotient X p)
      (quotientTransition X p)
      (by
        -- The composite factors through the quotient by `F^p X`, so it is zero.
        refine (cancel_epi (cokernel.π (X.filtration.stageInclusion p))).1 ?_
        calc
          cokernel.π (X.filtration.stageInclusion p) ≫
              gradedToQuotient X p ≫ quotientTransition X p
              =
                (X.filtration.obj p).arrow ≫
                  cokernel.π (X.filtration.obj (p + 1)).arrow ≫ quotientTransition X p := by
                    simpa [Category.assoc] using
                      congrArg (fun t ↦ t ≫ quotientTransition X p) (gradedToQuotient_comm X p)
          _ = (X.filtration.obj p).arrow ≫ cokernel.π (X.filtration.obj p).arrow := by
                simpa [Category.assoc] using
                  congrArg (fun t ↦ (X.filtration.obj p).arrow ≫ t) (quotientTransition_comm X p)
          _ = 0 := by
                simpa using (cokernel.condition ((X.filtration.obj p).arrow))
          _ = cokernel.π (X.filtration.stageInclusion p) ≫ 0 := by
                symm
                simp)).Exact := by
  let T : ShortComplex 𝒜 :=
    ShortComplex.mk
      ((X.filtration.obj p).arrow)
      (cokernel.π (X.filtration.obj p).arrow)
      (cokernel.condition _)
  have hT : T.Exact := by
    -- The standard row `F^p X ⟶ X ⟶ X / F^p X` is exact.
    simpa [T] using ShortComplex.exact_cokernel ((X.filtration.obj p).arrow)
  -- Rewrite exactness in the refinement-lifting form and lift first to `X`, then to `F^p X`.
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  obtain ⟨A₁, π₁, hπ₁, y, hy⟩ :=
    exists_refinement_lift_of_epi (e := cokernel.π (X.filtration.obj (p + 1)).arrow) x₂
  have hy_zero : y ≫ cokernel.π (X.filtration.obj p).arrow = 0 := by
    -- After the first lift, the vanishing against the transition map says `y` lands in `F^p X`.
    calc
      y ≫ cokernel.π (X.filtration.obj p).arrow
          = y ≫ cokernel.π (X.filtration.obj (p + 1)).arrow ≫ quotientTransition X p := by
              simpa [Category.assoc] using
                congrArg (fun t ↦ y ≫ t) (quotientTransition_comm X p).symm
      _ = π₁ ≫ x₂ ≫ quotientTransition X p := by
            simpa [Category.assoc] using
              congrArg (fun t ↦ t ≫ quotientTransition X p) hy.symm
      _ = 0 := by
            simpa [Category.assoc] using congrArg (fun t ↦ π₁ ≫ t) hx₂
  obtain ⟨A₂, ρ, hρ, z, hz⟩ := hT.exact_up_to_refinements y hy_zero
  refine ⟨A₂, ρ ≫ π₁, inferInstance, z ≫ cokernel.π (X.filtration.stageInclusion p), ?_⟩
  -- Compose the two refinements and read the resulting lift through `gr^p X`.
  calc
    (ρ ≫ π₁) ≫ x₂ = ρ ≫ (π₁ ≫ x₂) := by simp [Category.assoc]
    _ = ρ ≫ (y ≫ cokernel.π (X.filtration.obj (p + 1)).arrow) := by rw [hy]
    _ = (ρ ≫ y) ≫ cokernel.π (X.filtration.obj (p + 1)).arrow := by simp [Category.assoc]
    _ = (z ≫ (X.filtration.obj p).arrow) ≫ cokernel.π (X.filtration.obj (p + 1)).arrow := by
          rw [hz]
    _ = z ≫ ((X.filtration.obj p).arrow ≫ cokernel.π (X.filtration.obj (p + 1)).arrow) := by
          simp [Category.assoc]
    _ =
        z ≫ (cokernel.π (X.filtration.stageInclusion p) ≫ gradedToQuotient X p) := by
          rw [gradedToQuotient_comm]
    _ = (z ≫ cokernel.π (X.filtration.stageInclusion p)) ≫ gradedToQuotient X p := by
          simp [Category.assoc]

/-- Helper for Lemma 12.19.15: the quotient projection is an isomorphism once the filtered stage is
already zero. -/
private instance quotient_projection_isIso_of_eq_bot (X : FilteredObject 𝒜) (p : ℤ)
    (hp : X.filtration.obj p = ⊥) :
    IsIso (cokernel.π (X.filtration.obj p).arrow) := by
  -- A zero filtration stage has a unique map into the ambient object, so its cokernel is `X`.
  let hZ : IsZero (F^{p} X) := stage_isZero_of_eq_bot X p hp
  have hArrow : (X.filtration.obj p).arrow = 0 := hZ.eq_of_src _ _
  rw [hArrow]
  infer_instance

/-- Helper for Lemma 12.19.15: quotienting by a zero filtration stage identifies with the
underlying object. -/
private noncomputable abbrev underlyingToQuotientIsoOfEqBot (X : FilteredObject 𝒜) (p : ℤ)
    (hp : X.filtration.obj p = ⊥) :
    X.obj ≅ filteredQuotient X p :=
  letI := quotient_projection_isIso_of_eq_bot X p hp
  asIso (cokernel.π (X.filtration.obj p).arrow)

/-- Helper for Lemma 12.19.15: the zero-stage quotient identification is given by the canonical
quotient projection. -/
private theorem underlyingToQuotientIsoOfEqBot_hom (X : FilteredObject 𝒜) (p : ℤ)
    (hp : X.filtration.obj p = ⊥) :
    (underlyingToQuotientIsoOfEqBot X p hp).hom = cokernel.π (X.filtration.obj p).arrow := by
  -- The quotient identification was defined as `asIso` of the quotient projection itself.
  rfl

/-- Helper for Lemma 12.19.15: the zero-stage quotient identifications are natural in filtered
morphisms. -/
private theorem underlyingToQuotientIsoOfEqBot_hom_naturality
    {A B : FilteredObject 𝒜} (f : A ⟶ B) (p : ℤ)
    (hpA : A.filtration.obj p = ⊥) (hpB : B.filtration.obj p = ⊥) :
    (underlyingToQuotientIsoOfEqBot A p hpA).hom ≫ quotientMap f p =
      f.hom ≫ (underlyingToQuotientIsoOfEqBot B p hpB).hom := by
  -- After expanding the two zero-stage identifications, this is exactly `quotientMap_comm`.
  simpa [underlyingToQuotientIsoOfEqBot_hom] using quotientMap_comm f p

/-- Helper for Lemma 12.19.15: finite filtrations admit a common top stage across the short
complex. -/
private theorem exists_common_top_stage
    (hX₁fin : S.X₁.IsFinite) (hX₂fin : S.X₂.IsFinite) (hX₃fin : S.X₃.IsFinite) :
    ∃ nTop : ℤ,
      S.X₁.filtration.obj nTop = ⊤ ∧
      S.X₂.filtration.obj nTop = ⊤ ∧
      S.X₃.filtration.obj nTop = ⊤ := by
  -- Take the minimum of the three top witnesses so every earlier stage is still top.
  rcases hX₁fin with ⟨n₁, _, hn₁, _⟩
  rcases hX₂fin with ⟨n₂, _, hn₂, _⟩
  rcases hX₃fin with ⟨n₃, _, hn₃, _⟩
  refine ⟨min n₁ (min n₂ n₃), ?_, ?_, ?_⟩
  · exact filtration_eq_top_of_le (X := S.X₁) (by omega) hn₁
  · exact filtration_eq_top_of_le (X := S.X₂) (by omega) hn₂
  · exact filtration_eq_top_of_le (X := S.X₃) (by omega) hn₃

/-- Helper for Lemma 12.19.15: finite filtrations admit a common zero stage across the short
complex. -/
private theorem exists_common_zero_stage
    (hX₁fin : S.X₁.IsFinite) (hX₂fin : S.X₂.IsFinite) (hX₃fin : S.X₃.IsFinite) :
    ∃ mBot : ℤ,
      S.X₁.filtration.obj mBot = ⊥ ∧
      S.X₂.filtration.obj mBot = ⊥ ∧
      S.X₃.filtration.obj mBot = ⊥ := by
  -- Take the maximum of the three zero witnesses so every later stage is still zero.
  rcases hX₁fin with ⟨_, m₁, _, hm₁⟩
  rcases hX₂fin with ⟨_, m₂, _, hm₂⟩
  rcases hX₃fin with ⟨_, m₃, _, hm₃⟩
  refine ⟨max m₁ (max m₂ m₃), ?_, ?_, ?_⟩
  · exact filtration_eq_bot_of_le (X := S.X₁) (by omega) hm₁
  · exact filtration_eq_bot_of_le (X := S.X₂) (by omega) hm₂
  · exact filtration_eq_bot_of_le (X := S.X₃) (by omega) hm₃

/-- Helper for Lemma 12.19.15: if a filtration stage is the whole object, its inclusion into the
ambient object is an isomorphism. -/
private instance stage_inclusion_isIso_of_eq_top (X : FilteredObject 𝒜) (p : ℤ)
    (hp : X.filtration.obj p = ⊤) :
    IsIso (X.filtration.obj p).arrow := by
  -- Rewriting to the top subobject reduces the stage inclusion to the identity.
  rw [hp]
  infer_instance

/-- Helper for Lemma 12.19.15: a top filtration stage identifies canonically with the underlying
object. -/
private noncomputable abbrev stageToUnderlyingIsoOfEqTop (X : FilteredObject 𝒜) (p : ℤ)
    (hp : X.filtration.obj p = ⊤) :
    F^{p} X ≅ X.obj :=
  letI := stage_inclusion_isIso_of_eq_top X p hp
  asIso (X.filtration.obj p).arrow

/-- Helper for Lemma 12.19.15: quotienting by a top filtration stage yields the zero object. -/
private theorem quotient_isZero_of_eq_top (X : FilteredObject 𝒜) (p : ℤ)
    (hp : X.filtration.obj p = ⊤) :
    IsZero (filteredQuotient X p) := by
  -- Rewriting the stage inclusion to the top subobject makes the quotient a cokernel of an epi.
  letI := stage_inclusion_isIso_of_eq_top X p hp
  simpa [filteredQuotient] using Limits.isZero_cokernel_of_epi ((X.filtration.obj p).arrow)

/-- Helper for Lemma 12.19.15: exactness at a common top stage is exactness of the underlying
row. -/
private theorem underlying_exact_of_stage_exact_at_common_top
    (p : ℤ)
    (hp₁ : S.X₁.filtration.obj p = ⊤)
    (hp₂ : S.X₂.filtration.obj p = ⊤)
    (hp₃ : S.X₃.filtration.obj p = ⊤)
    (hstage : ShortComplex.Exact (S.map (stageFunctor p))) :
    ShortComplex.Exact (S.map FilteredObject.forget) := by
  let i : S.map (stageFunctor p) ≅ S.map FilteredObject.forget :=
    ShortComplex.isoMk
      (stageToUnderlyingIsoOfEqTop S.X₁ p hp₁)
      (stageToUnderlyingIsoOfEqTop S.X₂ p hp₂)
      (stageToUnderlyingIsoOfEqTop S.X₃ p hp₃)
      (by
        change (S.X₁.filtration.obj p).arrow ≫ S.f.hom =
          stageMap S.f p ≫ (S.X₂.filtration.obj p).arrow
        simpa using (stageMap_comm S.f p).symm)
      (by
        change (S.X₂.filtration.obj p).arrow ≫ S.g.hom =
          stageMap S.g p ≫ (S.X₃.filtration.obj p).arrow
        simpa using (stageMap_comm S.g p).symm)
  -- Transport exactness from the top stage row back to the underlying row.
  exact (ShortComplex.exact_iff_of_iso i).1 hstage

/-- Helper for Lemma 12.19.15: a stage-level class with zero image in `gr^p` refines to the next
filtration stage. -/
private theorem stage_remainder_refines_to_stage_succ
    {A : 𝒜} (X : FilteredObject 𝒜) (p : ℤ) (x : A ⟶ F^{p} X)
    (hx : x ≫ cokernel.π (X.filtration.stageInclusion p) = 0) :
    ∃ (A' : 𝒜) (π : A' ⟶ A) (_ : Epi π) (y : A' ⟶ F^{p + 1} X),
      π ≫ x = y ≫ X.filtration.stageInclusion p := by
  let T : ShortComplex 𝒜 :=
    ShortComplex.mk
      (X.filtration.stageInclusion p)
      (cokernel.π (X.filtration.stageInclusion p))
      (cokernel.condition _)
  have hT : T.Exact := by
    -- The canonical stage row is exact, so the vanishing graded class lifts one step lower.
    simpa [T] using (stage_row_shortExact X p).exact
  exact hT.exact_up_to_refinements x hx

/-- Helper for Lemma 12.19.15: a quotient-level remainder killed by the transition to
`X / F^p X` refines to the graded piece `gr^p X`. -/
private theorem quotient_remainder_refines_to_graded
    {A : 𝒜} (X : FilteredObject 𝒜) (p : ℤ) (x : A ⟶ filteredQuotient X (p + 1))
    (hx : x ≫ quotientTransition X p = 0) :
    ∃ (A' : 𝒜) (π : A' ⟶ A) (_ : Epi π) (y : A' ⟶ gr^{p} X),
      π ≫ x = y ≫ gradedToQuotient X p := by
  let T : ShortComplex 𝒜 :=
    ShortComplex.mk
      (gradedToQuotient X p)
      (quotientTransition X p)
      (by
        -- The quotient row is the canonical exact row `gr^p X ⟶ X / F^(p + 1) X ⟶ X / F^p X`.
        refine (cancel_epi (cokernel.π (X.filtration.stageInclusion p))).1 ?_
        calc
          cokernel.π (X.filtration.stageInclusion p) ≫
              gradedToQuotient X p ≫ quotientTransition X p
              =
                (X.filtration.obj p).arrow ≫
                  cokernel.π (X.filtration.obj (p + 1)).arrow ≫ quotientTransition X p := by
                    simpa [Category.assoc] using
                      congrArg (fun t ↦ t ≫ quotientTransition X p) (gradedToQuotient_comm X p)
          _ = (X.filtration.obj p).arrow ≫ cokernel.π (X.filtration.obj p).arrow := by
                simpa [Category.assoc] using
                  congrArg (fun t ↦ (X.filtration.obj p).arrow ≫ t) (quotientTransition_comm X p)
          _ = 0 := by
                simpa using (cokernel.condition ((X.filtration.obj p).arrow))
          _ = cokernel.π (X.filtration.stageInclusion p) ≫ 0 := by
                symm
                simp)
  have hT : T.Exact := by
    -- Reuse the previously established quotient row exactness in the refinement form.
    simpa [T] using quotient_row_exact X p
  exact hT.exact_up_to_refinements x hx

/-- Helper for Lemma 12.19.15: exactness at stage `p + 1` together with exactness of `gr^p`
implies exactness at stage `p`. -/
private theorem stage_exact_step_of_stage_succ_exact_and_graded_exact
    (p : ℤ)
    (hstageSucc : ShortComplex.Exact (S.map (stageFunctor (p + 1))))
    (hgr_p : ShortComplex.Exact (S.map (associatedGradedFunctor ⋙ GradedObject.eval p))) :
    ShortComplex.Exact (S.map (stageFunctor p)) := by
  -- TODO: work under `exact_iff_exact_up_to_refinements`, use
  -- `stage_remainder_refines_to_stage_succ` to push the corrected remainder from `F^p` down to
  -- `F^(p + 1)`, and then finish with `hstageSucc`. The current blocker is purely algebraic:
  -- packaging the additive correction term so the refined remainder and the stage-`p + 1` lift
  -- reassemble without introducing brittle coercion rewrites.
  sorry

/-- Helper for Lemma 12.19.15: exactness at quotient level `p` together with exactness of `gr^p`
implies exactness at quotient level `p + 1`. -/
private theorem quotient_exact_step_of_quotient_exact_and_graded_exact
    (p : ℤ)
    (hquot : ShortComplex.Exact (S.map (quotientFunctor p)))
    (hgr_p : ShortComplex.Exact (S.map (associatedGradedFunctor ⋙ GradedObject.eval p))) :
    ShortComplex.Exact (S.map (quotientFunctor (p + 1))) := by
  -- TODO: lift a quotient-level `p + 1` cycle down to quotient level `p`, solve it there,
  -- then correct the remainder through `gr^p`. The remaining blocker is turning the corrected
  -- graded remainder into a genuine graded cycle without introducing a larger row package.
  sorry

/-- Helper for Lemma 12.19.15: at a common zero filtration stage, exactness of the quotient row
is exactly exactness of the underlying row. -/
private theorem underlying_exact_of_quotient_exact_at_common_zero
    (p : ℤ)
    (hp₁ : S.X₁.filtration.obj p = ⊥)
    (hp₂ : S.X₂.filtration.obj p = ⊥)
    (hp₃ : S.X₃.filtration.obj p = ⊥)
    (hquot : ShortComplex.Exact (S.map (quotientFunctor p))) :
    ShortComplex.Exact (S.map FilteredObject.forget) := by
  let i : S.map FilteredObject.forget ≅ S.map (quotientFunctor p) :=
    ShortComplex.isoMk
      (underlyingToQuotientIsoOfEqBot S.X₁ p hp₁)
      (underlyingToQuotientIsoOfEqBot S.X₂ p hp₂)
      (underlyingToQuotientIsoOfEqBot S.X₃ p hp₃)
      (by
        -- The first square is the quotient-map commutativity transported through the zero-stage
        -- quotient identifications.
        have hMap :
            cokernel.π (S.X₁.filtration.obj p).arrow ≫ (quotientFunctor p).map S.f =
              cokernel.π (S.X₁.filtration.obj p).arrow ≫ quotientMap S.f p := by
          rfl
        have hForget :
            S.f.hom ≫ cokernel.π (S.X₂.filtration.obj p).arrow =
              FilteredObject.forget.map S.f ≫ cokernel.π (S.X₂.filtration.obj p).arrow := by
          rfl
        exact hMap.trans <| (quotientMap_comm S.f p).trans hForget)
      (by
        -- The second square is the same naturality statement for `S.g`.
        have hMap :
            cokernel.π (S.X₂.filtration.obj p).arrow ≫ (quotientFunctor p).map S.g =
              cokernel.π (S.X₂.filtration.obj p).arrow ≫ quotientMap S.g p := by
          rfl
        have hForget :
            S.g.hom ≫ cokernel.π (S.X₃.filtration.obj p).arrow =
              FilteredObject.forget.map S.g ≫ cokernel.π (S.X₃.filtration.obj p).arrow := by
          rfl
        exact hMap.trans <| (quotientMap_comm S.g p).trans hForget)
  -- Transport exactness back along the canonical zero-stage quotient identification.
  exact (ShortComplex.exact_iff_of_iso i).2 hquot

-- Proof sketch: argue by induction on the common finite length of the filtrations, peeling off the
-- top nonzero step and applying the short exact sequence relating `F^p` to the associated graded
-- piece and the quotient filtration.
/-- Lemma 12.19.15 (2): if the filtrations are finite and the associated graded complex is exact,
then `F^p(A) ⟶ F^p(B) ⟶ F^p(C)` is exact for every `p`. -/
theorem stage_exact_of_associatedGraded_exact
    (hX₁fin : S.X₁.IsFinite) (hX₂fin : S.X₂.IsFinite) (hX₃fin : S.X₃.IsFinite)
    (hgr : ShortComplex.Exact (S.map associatedGradedFunctor))
    (p : ℤ) :
    ShortComplex.Exact (S.map (stageFunctor p)) := by
  rcases exists_common_zero_stage (S := S) hX₁fin hX₂fin hX₃fin with ⟨mBot, _, hm₂, _⟩
  by_cases hp : mBot ≤ p
  · -- Once the middle stage vanishes, the stage row is automatically exact.
    apply ShortComplex.exact_of_isZero_X₂
    exact stage_isZero_of_eq_bot S.X₂ p (filtration_eq_bot_of_le (X := S.X₂) hp hm₂)
  · have hpm : p ≤ mBot := by omega
    let n : ℕ := Int.toNat (mBot - p)
    have hn : (n : ℤ) = mBot - p := by
      simpa [n] using Int.toNat_of_nonneg (show 0 ≤ mBot - p by omega)
    have hdesc :
        ∀ k : ℕ, ShortComplex.Exact (S.map (stageFunctor (mBot - (k : ℤ)))) := by
      intro k
      induction k with
      | zero =>
          -- The common zero stage supplies the base exact row for the downward induction.
          have hEq : mBot - (0 : ℤ) = mBot := by simp
          apply ShortComplex.exact_of_isZero_X₂
          simpa [hEq] using stage_isZero_of_eq_bot S.X₂ mBot hm₂
      | succ k ih =>
          -- Descend one stage using the exact graded piece at the current index.
          let q : ℤ := mBot - ((k.succ : ℕ) : ℤ)
          have hs :
              ShortComplex.Exact (S.map (stageFunctor (q + 1))) := by
            have hEq : q + 1 = mBot - (k : ℤ) := by
              dsimp [q]
              omega
            rw [hEq]
            exact ih
          have hgr_k :
              ShortComplex.Exact (S.map (associatedGradedFunctor ⋙ GradedObject.eval q)) :=
            gradedPiece_exact_of_associatedGraded_exact (S := S) hgr q
          simpa [q] using
            stage_exact_step_of_stage_succ_exact_and_graded_exact
              (S := S) (p := q) hs hgr_k
    have hp_eq : p = mBot - (n : ℤ) := by omega
    simpa [hp_eq] using hdesc n

-- Proof sketch: perform the same finite-length induction on the quotient filtrations
-- `A / F^n A`, `B / F^n B`, and `C / F^n C`, using exactness of the graded pieces to identify the
-- successive quotients.
/-- Lemma 12.19.15 (3): if the filtrations are finite and the associated graded complex is exact,
then `A / F^p(A) ⟶ B / F^p(B) ⟶ C / F^p(C)` is exact for every `p`. -/
theorem quotient_exact_of_associatedGraded_exact
    (hX₁fin : S.X₁.IsFinite) (hX₂fin : S.X₂.IsFinite) (hX₃fin : S.X₃.IsFinite)
    (hgr : ShortComplex.Exact (S.map associatedGradedFunctor))
    (p : ℤ) :
    ShortComplex.Exact (S.map (quotientFunctor p)) := by
  rcases exists_common_top_stage (S := S) hX₁fin hX₂fin hX₃fin with ⟨nTop, _, hn₂, _⟩
  by_cases hp : p ≤ nTop
  · -- At or below the common top stage, the middle quotient object is already zero.
    apply ShortComplex.exact_of_isZero_X₂
    exact quotient_isZero_of_eq_top S.X₂ p (filtration_eq_top_of_le (X := S.X₂) hp hn₂)
  · have hnp : nTop ≤ p := by omega
    have hascend :
        ∀ q : ℤ, nTop ≤ q → ShortComplex.Exact (S.map (quotientFunctor q)) := by
      intro q hq
      induction q, hq using Int.le_induction with
      | base =>
          -- The common top stage supplies the base exact row for the upward induction.
          apply ShortComplex.exact_of_isZero_X₂
          exact quotient_isZero_of_eq_top S.X₂ nTop hn₂
      | succ q hq ih =>
          -- Ascend one stage using the exact graded piece at the current quotient level.
          exact quotient_exact_step_of_quotient_exact_and_graded_exact
            (S := S) (p := q) ih
            (gradedPiece_exact_of_associatedGraded_exact (S := S) hgr q)
    -- Ascend from the common top stage one quotient step at a time.
    exact hascend p hnp

-- Proof sketch: apply the stage exactness and the underlying exactness to identify the images of
-- `S.f` and `S.g` on each filtration level with the intersections required in the
-- definition of strictness.
/-- Lemma 12.19.15 (4): if the filtrations are finite and the associated graded complex is exact,
then both maps of filtered objects are strict. -/
theorem strict_of_associatedGraded_exact
    (hX₁fin : S.X₁.IsFinite) (hX₂fin : S.X₂.IsFinite) (hX₃fin : S.X₃.IsFinite)
    (hgr : ShortComplex.Exact (S.map associatedGradedFunctor)) :
    Strict S.f ∧ Strict S.g := by
  -- TODO: once the stage and quotient induction theorems are closed, combine them with
  -- `underlying_exact_of_associatedGraded_exact` and the strictness criterion
  -- `strict_iff_quotient_eq_inf` to run the two source chases.
  sorry

-- Proof sketch: apply the quotient exactness at a stage above the top nonzero filtration step, so
-- the quotients identify with the original objects and the quotient complex becomes the underlying
-- short complex.
/-- Lemma 12.19.15 (5): if the filtrations are finite and the associated graded complex is exact,
then the underlying sequence `A.obj ⟶ B.obj ⟶ C.obj` is exact. -/
theorem underlying_exact_of_associatedGraded_exact
    (hX₁fin : S.X₁.IsFinite) (hX₂fin : S.X₂.IsFinite) (hX₃fin : S.X₃.IsFinite)
    (hgr : ShortComplex.Exact (S.map associatedGradedFunctor)) :
    ShortComplex.Exact (S.map FilteredObject.forget) := by
  -- Route correction: recover the underlying row from a common zero stage on the quotient side,
  -- which matches the source proof more directly than detouring through the stage theorem.
  rcases exists_common_zero_stage (S := S) hX₁fin hX₂fin hX₃fin with ⟨p, hp₁, hp₂, hp₃⟩
  exact underlying_exact_of_quotient_exact_at_common_zero (S := S) p hp₁ hp₂ hp₃
    (quotient_exact_of_associatedGraded_exact (S := S) hX₁fin hX₂fin hX₃fin hgr p)

end FiniteFiltrations

end ShortComplex

end CategoryTheory
