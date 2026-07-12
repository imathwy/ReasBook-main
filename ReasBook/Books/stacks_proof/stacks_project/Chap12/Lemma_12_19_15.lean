import Mathlib.Tactic.Recall
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import StacksProject_2024.Chap12.Definition_12_19_3
import Mathlib.Tactic.StacksAttribute

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

/-- The degreewise exactness bridge for Chap12 Lemma 12 19 15: if the associated graded complex is
exact, then `gr^p(A) ⟶ gr^p(B) ⟶ gr^p(C)` is exact for every `p`. This is the source-facing
specialization of the owner theorem `ShortComplex.Exact.map` along the evaluation functor
`GradedObject.eval p`. -/
@[stacks 05QH]
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
      simp [DecreasingFiltration.stageInclusion])

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
                    simp

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
                      simp
            _ = (A.filtration.obj p).arrow ≫
                  (cokernel.π (A.filtration.obj (p + 1)).arrow ≫ quotientMap f (p + 1)) := by
                    rw [quotientMap_comm]
            _ = (A.filtration.obj p).arrow ≫ cokernel.π (A.filtration.obj (p + 1)).arrow ≫
                  quotientMap f (p + 1) := by
                    simp
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

/-- Helper for Lemma 12.19.15: an ambient morphism whose quotient class in `X / F^p X` vanishes
refines to the stage `F^p X`. -/
private theorem quotientZeroRefinesToStage
    {A : 𝒜} (X : FilteredObject 𝒜) (p : ℤ) (x : A ⟶ X.obj)
    (hx : x ≫ cokernel.π (X.filtration.obj p).arrow = 0) :
    ∃ (A' : 𝒜) (π : A' ⟶ A) (_ : Epi π) (y : A' ⟶ F^{p} X),
      π ≫ x = y ≫ (X.filtration.obj p).arrow := by
  let T : ShortComplex 𝒜 :=
    ShortComplex.mk
      (X.filtration.obj p).arrow
      (cokernel.π (X.filtration.obj p).arrow)
      (cokernel.condition _)
  have hT : T.Exact := by
    -- The standard row `F^p X ⟶ X ⟶ X / F^p X` is exact.
    simpa [T] using ShortComplex.exact_cokernel ((X.filtration.obj p).arrow)
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

/-- Helper for Lemma 12.19.15: the canonical map `gr^p X ⟶ X / F^(p + 1) X` is mono. -/
private theorem gradedToQuotient_mono (X : FilteredObject 𝒜) (p : ℤ) :
    Mono (gradedToQuotient X p) := by
  let T : ShortComplex 𝒜 :=
    ShortComplex.mk
      (X.filtration.stageInclusion p)
      ((X.filtration.obj p).arrow ≫ cokernel.π (X.filtration.obj (p + 1)).arrow)
      (by
        -- The quotient by `F^(p + 1) X` kills the smaller stage `F^(p + 1) X`.
        simp [DecreasingFiltration.stageInclusion])
  have hT : T.Exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro A x hx
    -- Push the stage morphism into `X.obj`, lift it one stage lower, then cancel the ambient mono.
    obtain ⟨A', π, hπ, y, hy⟩ :=
      quotientZeroRefinesToStage (X := X) (p := p + 1)
        (x := x ≫ (X.filtration.obj p).arrow) (by simpa [T, Category.assoc] using hx)
    refine ⟨A', π, hπ, y, ?_⟩
    apply (cancel_mono (X.filtration.obj p).arrow).1
    calc
      (π ≫ x) ≫ (X.filtration.obj p).arrow = π ≫ (x ≫ (X.filtration.obj p).arrow) := by
        simp [Category.assoc]
      _ = y ≫ (X.filtration.obj (p + 1)).arrow := hy
      _ = y ≫ (X.filtration.stageInclusion p ≫ (X.filtration.obj p).arrow) := by
            rw [Subobject.ofLE_arrow (X.filtration.succ_le p)]
      _ = (y ≫ X.filtration.stageInclusion p) ≫ (X.filtration.obj p).arrow := by
            simp [Category.assoc]
  -- `gradedToQuotient X p` is the cokernel descent morphism of the exact row above.
  simpa [T, gradedToQuotient] using
    (ShortComplex.Exact.mono_cokernelDesc (S := T) hT)

/-- Helper for Lemma 12.19.15: exactness at stage `p + 1` together with exactness of `gr^p`
implies exactness at stage `p`. -/
private theorem stage_exact_step_of_stage_succ_exact_and_graded_exact
    (p : ℤ)
    (hstageSucc : ShortComplex.Exact (S.map (stageFunctor (p + 1))))
    (hgr_p : ShortComplex.Exact (S.map (associatedGradedFunctor ⋙ GradedObject.eval p))) :
    ShortComplex.Exact (S.map (stageFunctor p)) := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x hx
  change A ⟶ F^{p} S.X₂ at x
  change x ≫ stageMap S.g p = 0 at hx
  have hgrComm :
      cokernel.π (S.X₂.filtration.stageInclusion p) ≫ gradedPieceMap S.g p =
        stageMap S.g p ≫ cokernel.π (S.X₃.filtration.stageInclusion p) := by
    -- This is the defining square for the graded-piece map of `S.g`.
    simp [gradedPieceMap]
  have hxGr :
      (x ≫ cokernel.π (S.X₂.filtration.stageInclusion p)) ≫ gradedPieceMap S.g p = 0 := by
    -- The class of `x` in `gr^p(S.X₂)` is a cycle because `x` already vanishes under `S.g`.
    calc
      (x ≫ cokernel.π (S.X₂.filtration.stageInclusion p)) ≫ gradedPieceMap S.g p
          = x ≫ (cokernel.π (S.X₂.filtration.stageInclusion p) ≫ gradedPieceMap S.g p) := by
              simp [Category.assoc]
      _ = x ≫ (stageMap S.g p ≫ cokernel.π (S.X₃.filtration.stageInclusion p)) := by
            rw [hgrComm]
      _ = (x ≫ stageMap S.g p) ≫ cokernel.π (S.X₃.filtration.stageInclusion p) := by
            simp [Category.assoc]
      _ = 0 := by rw [hx, zero_comp]
  -- Solve the graded cycle, then lift the graded source representative back to `F^p(S.X₁)`.
  obtain ⟨A₁, π₁, hπ₁, y, hy⟩ := hgr_p.exact_up_to_refinements
    (x ≫ cokernel.π (S.X₂.filtration.stageInclusion p)) hxGr
  have hy' : π₁ ≫ x ≫ cokernel.π (S.X₂.filtration.stageInclusion p) = y ≫ gradedPieceMap S.f p := by
    simpa using hy
  obtain ⟨A₀, ρ, hρ, z, hz⟩ :=
    exists_refinement_lift_of_epi (e := cokernel.π (S.X₁.filtration.stageInclusion p)) y
  have hz' : ρ ≫ y = z ≫ cokernel.π (S.X₁.filtration.stageInclusion p) := by
    simpa using hz
  let d := (ρ ≫ π₁ ≫ x : A₀ ⟶ F^{p} S.X₂) - z ≫ stageMap S.f p
  have hdGrEq :
      ρ ≫ π₁ ≫ x ≫ cokernel.π (S.X₂.filtration.stageInclusion p) =
        z ≫ stageMap S.f p ≫ cokernel.π (S.X₂.filtration.stageInclusion p) := by
    -- Naturality of the graded map rewrites the solved graded class back into the stage row.
    calc
      ρ ≫ π₁ ≫ x ≫ cokernel.π (S.X₂.filtration.stageInclusion p)
          = ρ ≫ (π₁ ≫ (x ≫ cokernel.π (S.X₂.filtration.stageInclusion p))) := by
              simp
      _ = ρ ≫ (y ≫ gradedPieceMap S.f p) := by
            rw [hy']
      _ = (ρ ≫ y) ≫ gradedPieceMap S.f p := by
            simp [Category.assoc]
      _ = (z ≫ cokernel.π (S.X₁.filtration.stageInclusion p)) ≫ gradedPieceMap S.f p := by
            exact congrArg (fun t ↦ t ≫ gradedPieceMap S.f p) hz'
      _ = z ≫ stageMap S.f p ≫ cokernel.π (S.X₂.filtration.stageInclusion p) := by
            simp [gradedPieceMap, Category.assoc]
  have hdGr : d ≫ cokernel.π (S.X₂.filtration.stageInclusion p) = 0 := by
    -- The defect has trivial graded class, so it comes from the next filtration stage.
    dsimp [d]
    simpa [Category.assoc, Preadditive.sub_comp, sub_eq_zero] using hdGrEq
  obtain ⟨A₂, σ, hσ, w, hw⟩ :=
    stage_remainder_refines_to_stage_succ (X := S.X₂) (p := p) d hdGr
  have hdStage : d ≫ stageMap S.g p = 0 := by
    -- After correcting by the graded witness, the remaining defect is still a cycle one level up.
    have hfg_zero_p : stageMap S.f p ≫ stageMap S.g p = 0 := by
      calc
        stageMap S.f p ≫ stageMap S.g p = stageMap (S.f ≫ S.g) p := by
              rw [← stageMap_comp]
        _ = 0 := by rw [S.zero, stageMap_zero]
    calc
      d ≫ stageMap S.g p =
          ρ ≫ π₁ ≫ (x ≫ stageMap S.g p) -
            z ≫ (stageMap S.f p ≫ stageMap S.g p) := by
              dsimp [d]
              simp [Category.assoc, Preadditive.sub_comp]
      _ = 0 := by
            rw [hx, hfg_zero_p]
            simp
  have hwCycle : w ≫ stageMap S.g (p + 1) = 0 := by
    -- Move the corrected defect into `F^(p + 1)(S.X₂)` and cancel the mono stage inclusion.
    have hw' : σ ≫ d ≫ stageMap S.g p = w ≫ S.X₂.filtration.stageInclusion p ≫ stageMap S.g p := by
      simpa [Category.assoc] using congrArg (fun t ↦ t ≫ stageMap S.g p) hw
    have hw'' :
        σ ≫ d ≫ stageMap S.g p =
          w ≫ stageMap S.g (p + 1) ≫ S.X₃.filtration.stageInclusion p := by
      simpa [Category.assoc, stageInclusion_naturality S.g p] using hw'
    have hzero :
        w ≫ stageMap S.g (p + 1) ≫ S.X₃.filtration.stageInclusion p = 0 := by
      rw [← hw'']
      simpa [Category.assoc] using congrArg (fun t ↦ σ ≫ t) hdStage
    apply (cancel_mono (S.X₃.filtration.stageInclusion p)).1
    simpa [Category.assoc] using hzero
  -- The stage-`p + 1` exactness now kills the remaining correction term.
  obtain ⟨A₃, τ, hτ, u, hu⟩ := hstageSucc.exact_up_to_refinements w hwCycle
  refine ⟨A₃, τ ≫ σ ≫ ρ ≫ π₁, inferInstance,
    u ≫ S.X₁.filtration.stageInclusion p + τ ≫ σ ≫ z, ?_⟩
  have hdSplit : ρ ≫ π₁ ≫ x = d + z ≫ stageMap S.f p := by
    -- Re-expand the defect once so the final correction splits into the graded and stage parts.
    dsimp [d]
    exact (sub_add_cancel (ρ ≫ π₁ ≫ x) (z ≫ stageMap S.f p)).symm
  have hcorr :
      τ ≫ σ ≫ d =
        u ≫ S.X₁.filtration.stageInclusion p ≫ stageMap S.f p := by
    -- The corrected defect is exactly the image of the stage-`p + 1` source witness.
    have hu' : τ ≫ w = u ≫ stageMap S.f (p + 1) := by
      simpa using hu
    have hnatf :
        u ≫ stageMap S.f (p + 1) ≫ S.X₂.filtration.stageInclusion p =
          u ≫ S.X₁.filtration.stageInclusion p ≫ stageMap S.f p := by
      simpa [Category.assoc] using
        congrArg (fun t ↦ u ≫ t) (stageInclusion_naturality S.f p).symm
    calc
      τ ≫ σ ≫ d = τ ≫ (σ ≫ d) := by
            simp
      _ = τ ≫ (w ≫ S.X₂.filtration.stageInclusion p) := by
            rw [hw]
      _ = (τ ≫ w) ≫ S.X₂.filtration.stageInclusion p := by
            simp [Category.assoc]
      _ = (u ≫ stageMap S.f (p + 1)) ≫ S.X₂.filtration.stageInclusion p := by
            rw [hu']
      _ = u ≫ (stageMap S.f (p + 1) ≫ S.X₂.filtration.stageInclusion p) := by
            simp [Category.assoc]
      _ = u ≫ S.X₁.filtration.stageInclusion p ≫ stageMap S.f p := by
            exact hnatf
  -- Assemble the lifted graded source term and the stage-`p + 1` correction.
  calc
    (τ ≫ σ ≫ ρ ≫ π₁) ≫ x = τ ≫ σ ≫ (ρ ≫ π₁ ≫ x) := by
          simp [Category.assoc]
    _ = τ ≫ σ ≫ (d + z ≫ stageMap S.f p) := by
          rw [hdSplit]
    _ = τ ≫ σ ≫ d + τ ≫ σ ≫ (z ≫ stageMap S.f p) := by
          simp [Preadditive.comp_add]
    _ = u ≫ S.X₁.filtration.stageInclusion p ≫ stageMap S.f p +
          (τ ≫ σ ≫ z) ≫ stageMap S.f p := by
            rw [hcorr]
            simp [Category.assoc]
    _ = (u ≫ S.X₁.filtration.stageInclusion p + τ ≫ σ ≫ z) ≫ stageMap S.f p := by
          simp [Category.assoc, Preadditive.add_comp]

/-- Helper for Lemma 12.19.15: exactness at quotient level `p` together with exactness of `gr^p`
implies exactness at quotient level `p + 1`. -/
private theorem quotient_exact_step_of_quotient_exact_and_graded_exact
    (p : ℤ)
    (hquot : ShortComplex.Exact (S.map (quotientFunctor p)))
    (hgr_p : ShortComplex.Exact (S.map (associatedGradedFunctor ⋙ GradedObject.eval p))) :
    ShortComplex.Exact (S.map (quotientFunctor (p + 1))) := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x hx
  change A ⟶ filteredQuotient S.X₂ (p + 1) at x
  change x ≫ quotientMap S.g (p + 1) = 0 at hx
  have hxPrev :
      (x ≫ quotientTransition S.X₂ p) ≫ quotientMap S.g p = 0 := by
    -- Push the quotient-level cycle down one step using naturality of the transition morphisms.
    calc
      (x ≫ quotientTransition S.X₂ p) ≫ quotientMap S.g p
          = x ≫ (quotientTransition S.X₂ p ≫ quotientMap S.g p) := by
              simp [Category.assoc]
      _ = x ≫ (quotientMap S.g (p + 1) ≫ quotientTransition S.X₃ p) := by
            rw [(quotientTransition_naturality S.g p).symm]
      _ = (x ≫ quotientMap S.g (p + 1)) ≫ quotientTransition S.X₃ p := by
            simp [Category.assoc]
      _ = 0 := by rw [hx, zero_comp]
  -- Solve the cycle in the lower quotient row, then lift the source quotient witness back up.
  obtain ⟨A₁, π₁, hπ₁, y, hy⟩ := hquot.exact_up_to_refinements
    (x ≫ quotientTransition S.X₂ p) hxPrev
  have hy' : π₁ ≫ x ≫ quotientTransition S.X₂ p = y ≫ quotientMap S.f p := by
    simpa using hy
  obtain ⟨A₀, ρ, hρ, z, hz⟩ :=
    exists_refinement_lift_of_epi (e := quotientTransition S.X₁ p) y
  have hz' : ρ ≫ y = z ≫ quotientTransition S.X₁ p := by
    simpa using hz
  let d := (ρ ≫ π₁ ≫ x : A₀ ⟶ filteredQuotient S.X₂ (p + 1)) -
    z ≫ quotientMap S.f (p + 1)
  have hdPrevEq :
      ρ ≫ π₁ ≫ x ≫ quotientTransition S.X₂ p =
        z ≫ quotientMap S.f (p + 1) ≫ quotientTransition S.X₂ p := by
    -- The lifted lower-quotient solution identifies the remaining defect after one transition.
    calc
      ρ ≫ π₁ ≫ x ≫ quotientTransition S.X₂ p
          = ρ ≫ (π₁ ≫ (x ≫ quotientTransition S.X₂ p)) := by
              simp
      _ = ρ ≫ (y ≫ quotientMap S.f p) := by
            rw [hy']
      _ = (ρ ≫ y) ≫ quotientMap S.f p := by
            simp [Category.assoc]
      _ = (z ≫ quotientTransition S.X₁ p) ≫ quotientMap S.f p := by
            exact congrArg (fun t ↦ t ≫ quotientMap S.f p) hz'
      _ = z ≫ quotientMap S.f (p + 1) ≫ quotientTransition S.X₂ p := by
            rw [quotientTransition_naturality S.f p]
            simp [Category.assoc]
  have hdPrev : d ≫ quotientTransition S.X₂ p = 0 := by
    -- The residual quotient defect dies after applying the transition to level `p`.
    dsimp [d]
    simpa [Category.assoc, Preadditive.sub_comp, sub_eq_zero] using hdPrevEq
  obtain ⟨A₂, σ, hσ, r, hr⟩ :=
    quotient_remainder_refines_to_graded (X := S.X₂) (p := p) d hdPrev
  have hfg_zero : quotientMap S.f (p + 1) ≫ quotientMap S.g (p + 1) = 0 := by
    -- The quotient functor preserves the zero composite `S.f ≫ S.g = 0`.
    calc
      quotientMap S.f (p + 1) ≫ quotientMap S.g (p + 1) =
          quotientMap (S.f ≫ S.g) (p + 1) := by
            rw [← quotientMap_comp]
      _ = 0 := by rw [S.zero, quotientMap_zero]
  have hdNext : d ≫ quotientMap S.g (p + 1) = 0 := by
    -- The corrected defect remains a cycle in the upper quotient row.
    calc
      d ≫ quotientMap S.g (p + 1) =
          ρ ≫ π₁ ≫ (x ≫ quotientMap S.g (p + 1)) -
            z ≫ (quotientMap S.f (p + 1) ≫ quotientMap S.g (p + 1)) := by
              dsimp [d]
              simp [Category.assoc, Preadditive.sub_comp]
      _ = 0 := by
            rw [hx, hfg_zero]
            simp
  have hrCycleComp :
      (r ≫ gradedPieceMap S.g p) ≫ gradedToQuotient S.X₃ p = 0 := by
    -- Postcompose the graded defect with the mono bridge `gr^p(S.X₃) ⟶ S.X₃ / F^(p + 1)`.
    have hr' : σ ≫ d = r ≫ gradedToQuotient S.X₂ p := by
      simpa using hr
    calc
      (r ≫ gradedPieceMap S.g p) ≫ gradedToQuotient S.X₃ p
          = r ≫ (gradedPieceMap S.g p ≫ gradedToQuotient S.X₃ p) := by
              simp [Category.assoc]
      _ = r ≫ (gradedToQuotient S.X₂ p ≫ quotientMap S.g (p + 1)) := by
            rw [(gradedToQuotient_naturality S.g p).symm]
      _ = (r ≫ gradedToQuotient S.X₂ p) ≫ quotientMap S.g (p + 1) := by
            simp [Category.assoc]
      _ = σ ≫ d ≫ quotientMap S.g (p + 1) := by
            rw [← hr']
            simp [Category.assoc]
      _ = 0 := by
            simpa [Category.assoc] using congrArg (fun t ↦ σ ≫ t) hdNext
  have hmonoGradedToQuotient : Mono (gradedToQuotient S.X₃ p) := gradedToQuotient_mono S.X₃ p
  letI : Mono (gradedToQuotient S.X₃ p) := hmonoGradedToQuotient
  have hrCycle : r ≫ gradedPieceMap S.g p = 0 := by
    -- Cancel the mono bridge to turn the corrected graded remainder into a genuine cycle.
    have hcompEq :
        (r ≫ gradedPieceMap S.g p) ≫ gradedToQuotient S.X₃ p =
          (0 : A₂ ⟶ gr^{p} S.X₃) ≫ gradedToQuotient S.X₃ p := by
      rw [zero_comp]
      exact hrCycleComp
    exact (cancel_mono (gradedToQuotient S.X₃ p)).1 hcompEq
  obtain ⟨A₃, τ, hτ, r₁, hr₁⟩ := hgr_p.exact_up_to_refinements r hrCycle
  refine ⟨A₃, τ ≫ σ ≫ ρ ≫ π₁, inferInstance,
    r₁ ≫ gradedToQuotient S.X₁ p + τ ≫ σ ≫ z, ?_⟩
  have hdSplit : ρ ≫ π₁ ≫ x = d + z ≫ quotientMap S.f (p + 1) := by
    -- Re-expand the upper-quotient defect so the final correction can be assembled in one `calc`.
    dsimp [d]
    exact (sub_add_cancel (ρ ≫ π₁ ≫ x) (z ≫ quotientMap S.f (p + 1))).symm
  have hcorr :
      τ ≫ σ ≫ d =
        r₁ ≫ gradedToQuotient S.X₁ p ≫ quotientMap S.f (p + 1) := by
    -- Rewrite the graded correction back into the quotient row through the naturality bridge.
    have hr₁' : τ ≫ r = r₁ ≫ gradedPieceMap S.f p := by
      simpa using hr₁
    have hnatf :
        (r₁ ≫ gradedPieceMap S.f p) ≫ gradedToQuotient S.X₂ p =
          r₁ ≫ gradedToQuotient S.X₁ p ≫ quotientMap S.f (p + 1) := by
      simpa [Category.assoc] using
        congrArg (fun t ↦ r₁ ≫ t) (gradedToQuotient_naturality S.f p)
    calc
      τ ≫ σ ≫ d = τ ≫ (σ ≫ d) := by
            simp
      _ = τ ≫ (r ≫ gradedToQuotient S.X₂ p) := by
            rw [hr]
      _ = (τ ≫ r) ≫ gradedToQuotient S.X₂ p := by
            simp [Category.assoc]
      _ = (r₁ ≫ gradedPieceMap S.f p) ≫ gradedToQuotient S.X₂ p := by
            rw [hr₁']
      _ = r₁ ≫ gradedToQuotient S.X₁ p ≫ quotientMap S.f (p + 1) := by
            exact hnatf
  -- Assemble the lifted lower-quotient solution and the graded correction in the source quotient.
  calc
    (τ ≫ σ ≫ ρ ≫ π₁) ≫ x = τ ≫ σ ≫ (ρ ≫ π₁ ≫ x) := by
          simp [Category.assoc]
    _ = τ ≫ σ ≫ (d + z ≫ quotientMap S.f (p + 1)) := by
          rw [hdSplit]
    _ = τ ≫ σ ≫ d + τ ≫ σ ≫ (z ≫ quotientMap S.f (p + 1)) := by
          simp [Preadditive.comp_add]
    _ = r₁ ≫ gradedToQuotient S.X₁ p ≫ quotientMap S.f (p + 1) +
          (τ ≫ σ ≫ z) ≫ quotientMap S.f (p + 1) := by
            rw [hcorr]
            simp [Category.assoc]
    _ = (r₁ ≫ gradedToQuotient S.X₁ p + τ ≫ σ ≫ z) ≫ quotientMap S.f (p + 1) := by
          simp [Category.assoc, Preadditive.add_comp]

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
@[stacks 05QH]
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
@[stacks 05QH]
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

/-- Helper for Lemma 12.19.15: mapping an image subobject through a monomorphism agrees with the
image subobject of the composite. -/
private theorem imageSubobject_comp_eq_map_of_mono {X Y Z : 𝒜}
    (u : X ⟶ Y) (v : Y ⟶ Z) [Mono v] :
    imageSubobject (u ≫ v) = (Subobject.map v).obj (imageSubobject u) := by
  -- Rewrite the composite image through the restriction to `im(u)`, then use monicity of `v`.
  calc
    imageSubobject (u ≫ v) = imageSubobject ((imageSubobject u).arrow ≫ v) := by
      rw [Limits.imageSubobject_comp_eq_imageSubobject_restriction u v]
    _ = Subobject.mk ((imageSubobject u).arrow ≫ v) := by
          simpa using (Limits.imageSubobject_mono ((imageSubobject u).arrow ≫ v))
    _ = (Subobject.map v).obj (Subobject.mk (imageSubobject u).arrow) := by
          rw [Subobject.map_mk]
    _ = (Subobject.map v).obj (imageSubobject u) := by
          rw [Subobject.mk_arrow]

/-- Helper for Lemma 12.19.15: postcomposing an epimorphism does not change the image subobject.
-/
private theorem imageSubobject_comp_eq_of_epi {X Y Z : 𝒜} (u : X ⟶ Y) [Epi u] (v : Y ⟶ Z) :
    imageSubobject (u ≫ v) = imageSubobject v := by
  -- Rewrite the composite image through the restriction to `im(u)`, then collapse `im(u)` to `⊤`.
  calc
    imageSubobject (u ≫ v) = imageSubobject ((imageSubobject u).arrow ≫ v) := by
      rw [Limits.imageSubobject_comp_eq_imageSubobject_restriction u v]
    _ = imageSubobject (((⊤ : Subobject Y)).arrow ≫ v) := by
          simpa using congrArg (fun S : Subobject Y ↦ imageSubobject (S.arrow ≫ v))
            (Limits.imageSubobject_eq_top_of_epi u)
    _ = imageSubobject v := by
          simpa using Limits.imageSubobject_iso_comp ((⊤ : Subobject Y).arrow) v

/-- Helper for Lemma 12.19.15: the kernel of a composite is the pullback of the later kernel
along the earlier morphism. -/
private theorem kernelSubobject_comp_eq_pullback {X Y Z : 𝒜} (u : X ⟶ Y) (v : Y ⟶ Z) :
    kernelSubobject (u ≫ v) = (Subobject.pullback u).obj (kernelSubobject v) := by
  -- The pullback square gives one inclusion, and the kernel condition gives the reverse one.
  apply le_antisymm
  · refine Subobject.le_of_comm
      (((Subobject.pullback u).obj (kernelSubobject v)).factorThru
        (kernelSubobject (u ≫ v)).arrow ?_)
      ?_
    · exact
        (pullback_factors_iff u (kernelSubobject v) (kernelSubobject (u ≫ v)).arrow).2 <| by
          rw [kernelSubobject_factors_iff, Category.assoc]
          exact kernelSubobject_arrow_comp (u ≫ v)
    · exact Subobject.factorThru_arrow _ _ _
  · exact le_kernelSubobject _ _ <| by
      have hpb := (Subobject.isPullback u (kernelSubobject v)).w
      rw [← reassoc_of% hpb, kernelSubobject_arrow_comp, comp_zero]

/-- Helper for Lemma 12.19.15: stagewise exactness together with exactness of the underlying row
forces the left map to be strict. -/
private theorem strictLeftMapOfStageExactAndUnderlyingExact
    (hunder : ShortComplex.Exact (S.map FilteredObject.forget))
    (hstage : ∀ p : ℤ, ShortComplex.Exact (S.map (stageFunctor p))) :
    Strict S.f := by
  refine (strict_iff_quotient_eq_inf S.f).2 ?_
  intro p
  have hstage_image :
      imageSubobject (stageMap S.f p) = kernelSubobject (stageMap S.g p) := by
    -- Exactness of the stage row identifies the stagewise image of `S.f` with the stagewise
    -- kernel of `S.g`.
    simpa using
      (ShortComplex.exact_iff_image_eq_kernel (S := S.map (stageFunctor p))).1 (hstage p)
  have hunder_image :
      imageSubobject S.f.hom = kernelSubobject S.g.hom := by
    -- Exactness of the underlying row gives the ambient image-kernel identity.
    simpa using
      (ShortComplex.exact_iff_image_eq_kernel (S := S.map FilteredObject.forget)).1 hunder
  have hstageKernelPullback :
      kernelSubobject (stageMap S.g p) =
        (Subobject.pullback (S.X₂.filtration.obj p).arrow).obj (kernelSubobject S.g.hom) := by
    -- The kernel of the stage map is the pullback of the ambient kernel along the stage inclusion.
    calc
      kernelSubobject (stageMap S.g p) =
          kernelSubobject (stageMap S.g p ≫ (S.X₃.filtration.obj p).arrow) := by
            symm
            simpa using
              Limits.kernelSubobject_comp_mono (stageMap S.g p) ((S.X₃.filtration.obj p).arrow)
      _ = (Subobject.pullback (S.X₂.filtration.obj p).arrow).obj (kernelSubobject S.g.hom) := by
            simpa [stageMap_comm S.g p] using
              (kernelSubobject_comp_eq_pullback
                ((S.X₂.filtration.obj p).arrow) S.g.hom)
  have hmapPullback :
      (Subobject.map (S.X₂.filtration.obj p).arrow).obj
          ((Subobject.pullback (S.X₂.filtration.obj p).arrow).obj (kernelSubobject S.g.hom))
        = imageSubobject (S.X₂.filtration.obj p).arrow ⊓ kernelSubobject S.g.hom := by
    -- Mapping the pullback back into `S.X₂` gives the expected intersection.
    rw [Limits.imageSubobject_mono (S.X₂.filtration.obj p).arrow]
    exact
      (Subobject.inf_eq_map_pullback' (MonoOver.mk (S.X₂.filtration.obj p).arrow)
        (kernelSubobject S.g.hom)).symm
  -- Transport the stagewise kernel identity from `F^p(S.X₂)` back into `S.X₂`.
  calc
    S.X₁.filtration.quotient S.f.hom p
        = imageSubobject ((S.X₁.filtration.obj p).arrow ≫ S.f.hom) := by
            rw [DecreasingFiltration.quotient_eq_imageSubobject_comp]
    _ = (Subobject.map (S.X₂.filtration.obj p).arrow).obj (imageSubobject (stageMap S.f p)) := by
          rw [← stageMap_comm S.f p, imageSubobject_comp_eq_map_of_mono]
    _ = (Subobject.map (S.X₂.filtration.obj p).arrow).obj (kernelSubobject (stageMap S.g p)) := by
          rw [hstage_image]
    _ = (Subobject.map (S.X₂.filtration.obj p).arrow).obj
          ((Subobject.pullback (S.X₂.filtration.obj p).arrow).obj (kernelSubobject S.g.hom)) := by
            rw [hstageKernelPullback]
    _ = imageSubobject (S.X₂.filtration.obj p).arrow ⊓ kernelSubobject S.g.hom := by
          rw [hmapPullback]
    _ = S.X₂.filtration.obj p ⊓ imageSubobject S.f.hom := by
          rw [hunder_image, Limits.imageSubobject_mono (S.X₂.filtration.obj p).arrow,
            Subobject.mk_arrow]
    _ = imageSubobject S.f.hom ⊓ S.X₂.filtration.obj p := by
          rw [inf_comm]

/-- Helper for Lemma 12.19.15: exactness of every quotient row forces the right map to be strict.
-/
private theorem strictRightMapOfQuotientExact
    (hquot : ∀ p : ℤ, ShortComplex.Exact (S.map (quotientFunctor p))) :
    Strict S.g := by
  refine (strict_iff_quotient_eq_inf S.g).2 ?_
  intro p
  refine le_antisymm ?_ ?_
  · -- The stage image of `S.g` obviously lands inside the total image and inside the target stage.
    refine le_inf ?_ ?_
    · simpa [DecreasingFiltration.quotient_eq_imageSubobject_comp, Category.assoc] using
        imageSubobject_comp_le (S.X₂.filtration.obj p).arrow S.g.hom
    · rw [DecreasingFiltration.quotient_eq_imageSubobject_comp]
      exact imageSubobject_le _ _ (Subobject.factorThru_arrow _ _ (S.g.preserves p))
  · -- Route correction: use quotient exactness to kill the ambient quotient class, then refine the
    -- resulting defect back into `F^p(S.X₂)` so the desired subobject lands in the stage image.
    let P : Subobject S.X₃.obj := imageSubobject S.g.hom ⊓ S.X₃.filtration.obj p
    let P₀ : 𝒜 := P
    have hPImage : P ≤ imageSubobject S.g.hom := inf_le_left
    have hPStage : P ≤ S.X₃.filtration.obj p := inf_le_right
    let ιimg : P₀ ⟶ imageSubobject S.g.hom := Subobject.ofLE P _ hPImage
    obtain ⟨A₁, π₁, hπ₁, a, ha⟩ :=
      exists_refinement_lift_of_epi (e := factorThruImageSubobject S.g.hom) ιimg
    have haArrow : π₁ ≫ P.arrow = a ≫ S.g.hom := by
      -- Reattach the image inclusion to turn the refined factorization into an ambient equality.
      calc
        π₁ ≫ P.arrow = π₁ ≫ ιimg ≫ (imageSubobject S.g.hom).arrow := by
              simp [ιimg]
        _ = (a ≫ factorThruImageSubobject S.g.hom) ≫ (imageSubobject S.g.hom).arrow := by
              simpa [Category.assoc] using
                congrArg (fun t ↦ t ≫ (imageSubobject S.g.hom).arrow) ha
        _ = a ≫ S.g.hom := by
              simpa [Category.assoc] using imageSubobject_arrow_comp S.g.hom
    have hPQuotientZero : P.arrow ≫ cokernel.π (S.X₃.filtration.obj p).arrow = 0 := by
      -- Because `P` is contained in the stage `F^p(S.X₃)`, its quotient class is zero.
      have hPFactor :
          P.arrow = (Subobject.ofLE P _ hPStage) ≫ (S.X₃.filtration.obj p).arrow := by
        exact (Subobject.ofLE_arrow hPStage).symm
      rw [hPFactor, Category.assoc, cokernel.condition]
      simp
    have haQuotientZero :
        (a ≫ cokernel.π (S.X₂.filtration.obj p).arrow) ≫ quotientMap S.g p = 0 := by
      -- The refined ambient lift still lands inside `F^p(S.X₃)`, so its quotient image vanishes.
      calc
        (a ≫ cokernel.π (S.X₂.filtration.obj p).arrow) ≫ quotientMap S.g p =
            a ≫ (cokernel.π (S.X₂.filtration.obj p).arrow ≫ quotientMap S.g p) := by
              simp [Category.assoc]
        _ = a ≫ (S.g.hom ≫ cokernel.π (S.X₃.filtration.obj p).arrow) := by
              rw [quotientMap_comm]
        _ = a ≫ S.g.hom ≫ cokernel.π (S.X₃.filtration.obj p).arrow := by
              simp
        _ = π₁ ≫ P.arrow ≫ cokernel.π (S.X₃.filtration.obj p).arrow := by
              simpa [Category.assoc] using
                congrArg (fun t ↦ t ≫ cokernel.π (S.X₃.filtration.obj p).arrow) haArrow.symm
        _ = 0 := by
              rw [hPQuotientZero]
              simp
    obtain ⟨A₂, π₂, hπ₂, y, hy⟩ := (hquot p).exact_up_to_refinements
      (a ≫ cokernel.π (S.X₂.filtration.obj p).arrow) haQuotientZero
    have hy' :
        π₂ ≫ a ≫ cokernel.π (S.X₂.filtration.obj p).arrow = y ≫ quotientMap S.f p := by
      simpa using hy
    obtain ⟨A₃, π₃, hπ₃, z, hz⟩ :=
      exists_refinement_lift_of_epi (e := cokernel.π (S.X₁.filtration.obj p).arrow) y
    have hz' : π₃ ≫ y = z ≫ cokernel.π (S.X₁.filtration.obj p).arrow := by
      simpa using hz
    let d := (π₃ ≫ π₂ ≫ a : A₃ ⟶ S.X₂.obj) - z ≫ S.f.hom
    have hdQuotientZero : d ≫ cokernel.π (S.X₂.filtration.obj p).arrow = 0 := by
      -- The quotient exactness witness leaves a defect whose quotient class is zero.
      have hdEq :
          π₃ ≫ π₂ ≫ a ≫ cokernel.π (S.X₂.filtration.obj p).arrow =
            z ≫ S.f.hom ≫ cokernel.π (S.X₂.filtration.obj p).arrow := by
        calc
          π₃ ≫ π₂ ≫ a ≫ cokernel.π (S.X₂.filtration.obj p).arrow
              = π₃ ≫ (π₂ ≫ a ≫ cokernel.π (S.X₂.filtration.obj p).arrow) := by
                  simp
          _ = π₃ ≫ (y ≫ quotientMap S.f p) := by
                rw [hy']
          _ = (π₃ ≫ y) ≫ quotientMap S.f p := by
                simp [Category.assoc]
          _ = (z ≫ cokernel.π (S.X₁.filtration.obj p).arrow) ≫ quotientMap S.f p := by
                exact congrArg (fun t ↦ t ≫ quotientMap S.f p) hz'
          _ = z ≫ (cokernel.π (S.X₁.filtration.obj p).arrow ≫ quotientMap S.f p) := by
                simp [Category.assoc]
          _ = z ≫ (S.f.hom ≫ cokernel.π (S.X₂.filtration.obj p).arrow) := by
                rw [quotientMap_comm]
          _ = z ≫ S.f.hom ≫ cokernel.π (S.X₂.filtration.obj p).arrow := by
                simp
      dsimp [d]
      simpa [Category.assoc, Preadditive.sub_comp, sub_eq_zero] using hdEq
    obtain ⟨A₄, π₄, hπ₄, w, hw⟩ :=
      quotientZeroRefinesToStage (X := S.X₂) (p := p) d hdQuotientZero
    let ε : A₄ ⟶ P₀ := π₄ ≫ π₃ ≫ π₂ ≫ π₁
    have hdSplit : π₃ ≫ π₂ ≫ a = d + z ≫ S.f.hom := by
      -- Re-expand the defect once so the exact quotient lift and the stage correction recombine.
      dsimp [d]
      exact (sub_add_cancel (π₃ ≫ π₂ ≫ a) (z ≫ S.f.hom)).symm
    have hεArrow :
        ε ≫ P.arrow = w ≫ (S.X₂.filtration.obj p).arrow ≫ S.g.hom := by
      -- After quotient exactness kills the ambient class, the residual term comes from `F^p(S.X₂)`.
      calc
        ε ≫ P.arrow = π₄ ≫ π₃ ≫ π₂ ≫ (π₁ ≫ P.arrow) := by
              simp [ε, Category.assoc]
        _ = π₄ ≫ π₃ ≫ π₂ ≫ (a ≫ S.g.hom) := by
              rw [haArrow]
        _ = π₄ ≫ (π₃ ≫ π₂ ≫ a) ≫ S.g.hom := by
              simp [Category.assoc]
        _ = π₄ ≫ (d + z ≫ S.f.hom) ≫ S.g.hom := by
              rw [hdSplit]
        _ = π₄ ≫ d ≫ S.g.hom + π₄ ≫ (z ≫ S.f.hom) ≫ S.g.hom := by
              simp [Category.assoc, Preadditive.comp_add]
        _ = (w ≫ (S.X₂.filtration.obj p).arrow) ≫ S.g.hom + 0 := by
              have hwd : π₄ ≫ d ≫ S.g.hom = (w ≫ (S.X₂.filtration.obj p).arrow) ≫ S.g.hom := by
                simpa [Category.assoc] using congrArg (fun t ↦ t ≫ S.g.hom) hw
              have hfgZero : S.f.hom ≫ S.g.hom = 0 := by
                exact congrArg FilteredObject.Hom.hom S.zero
              have hzg : π₄ ≫ (z ≫ S.f.hom) ≫ S.g.hom = 0 := by
                simpa [Category.assoc, hfgZero]
              rw [hwd, hzg]
        _ = w ≫ (S.X₂.filtration.obj p).arrow ≫ S.g.hom := by
              simp [Category.assoc]
    have hPImageEq : imageSubobject (ε ≫ P.arrow) = P := by
      -- Refining the source by an epimorphism does not change the image of `P.arrow`.
      calc
        imageSubobject (ε ≫ P.arrow) = imageSubobject P.arrow := by
              exact imageSubobject_comp_eq_of_epi ε P.arrow
        _ = P := by
              rw [Limits.imageSubobject_mono P.arrow, Subobject.mk_arrow]
    calc
      P = imageSubobject (ε ≫ P.arrow) := hPImageEq.symm
      _ = imageSubobject (w ≫ (S.X₂.filtration.obj p).arrow ≫ S.g.hom) := by
            rw [hεArrow]
      _ ≤ imageSubobject ((S.X₂.filtration.obj p).arrow ≫ S.g.hom) := by
            simpa [Category.assoc] using
              imageSubobject_comp_le w ((S.X₂.filtration.obj p).arrow ≫ S.g.hom)
      _ = S.X₂.filtration.quotient S.g.hom p := by
            simpa [DecreasingFiltration.quotient_eq_imageSubobject_comp]

-- Proof sketch: apply the stage exactness and the underlying exactness to identify the images of
-- `S.f` and `S.g` on each filtration level with the intersections required in the
-- definition of strictness.
/-- Chap12 Lemma 12 19 15. Lemma 12.19.15 (4): if the filtrations are finite and the associated
graded complex is exact, then both maps of filtered objects are strict. -/
@[stacks 05QH]
theorem strict_of_associatedGraded_exact
    (hX₁fin : S.X₁.IsFinite) (hX₂fin : S.X₂.IsFinite) (hX₃fin : S.X₃.IsFinite)
    (hgr : ShortComplex.Exact (S.map associatedGradedFunctor)) :
    Strict S.f ∧ Strict S.g := by
  -- The left strictness already follows from the proven stagewise exactness bridge.
  have hunder :
      ShortComplex.Exact (S.map FilteredObject.forget) := by
    rcases exists_common_top_stage (S := S) hX₁fin hX₂fin hX₃fin with ⟨p, hp₁, hp₂, hp₃⟩
    exact underlying_exact_of_stage_exact_at_common_top (S := S) p hp₁ hp₂ hp₃
      (stage_exact_of_associatedGraded_exact (S := S) hX₁fin hX₂fin hX₃fin hgr p)
  have hStrictLeft : Strict S.f :=
    strictLeftMapOfStageExactAndUnderlyingExact (S := S) hunder
      (stage_exact_of_associatedGraded_exact (S := S) hX₁fin hX₂fin hX₃fin hgr)
  have hquot :
      ∀ p : ℤ, ShortComplex.Exact (S.map (quotientFunctor p)) :=
    quotient_exact_of_associatedGraded_exact
      (S := S) hX₁fin hX₂fin hX₃fin hgr
  -- The quotient exactness bridge gives the stagewise image identity required for right strictness.
  exact ⟨hStrictLeft, strictRightMapOfQuotientExact (S := S) hquot⟩

-- Proof sketch: apply the quotient exactness at a stage above the top nonzero filtration step, so
-- the quotients identify with the original objects and the quotient complex becomes the underlying
-- short complex.
/-- Lemma 12.19.15 (5): if the filtrations are finite and the associated graded complex is exact,
then the underlying sequence `A.obj ⟶ B.obj ⟶ C.obj` is exact. -/
@[stacks 05QH]
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
