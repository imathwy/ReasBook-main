import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap10.Lemma_10_127_2
import StacksProject_2024.Chap10.Lemma_10_6_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

universe u

section

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

-- Source/core/bridge triage:
-- * source-facing: the TFAE between finite presentation, preservation of filtered colimits by
--   `Hom_R(S, -)`, and stagewise factorization through a filtered colimit.
-- * core/canonical: `CommRingCat.preservesFilteredColimits_coyoneda` for
--   `Under.mk (CommRingCat.ofHom f)`.
-- * bridge/view: the factorization clause, which is the surjectivity part of the canonical
--   filtered-colimit comparison for the represented functor.

-- Proof sketch: apply the preserved `coyoneda` colimit comparison. Surjectivity of that
-- comparison map is exactly the desired stagewise factorization statement.
/-- Helper for Chap10 Lemma 10 127 3: preservation of filtered colimits by `Hom_R(S, -)`
implies that any map from `S` into a filtered colimit of `R`-algebras factors through some
stage. -/
theorem factorsThroughStage_of_preservesFilteredColimits_coyoneda
    (h :
      PreservesFilteredColimits (coyoneda.obj (.op (Under.mk (CommRingCat.ofHom f))))) :
    ∀ {J : Type u} [Category.{u} J] [IsFiltered J] (F : J ⥤ Under (CommRingCat.of R))
      (c : Cocone F) (_hc : IsColimit c) (g : Under.mk (CommRingCat.ofHom f) ⟶ c.pt),
        ∃ (j : J) (g' : Under.mk (CommRingCat.ofHom f) ⟶ F.obj j), g = g' ≫ c.ι.app j := by
  intro J _ _ F c hc g
  -- The preserved representable functor is the canonical finite-presentability condition for the
  -- under-object `R → S`.
  letI : IsFinitelyPresentable.{u} (Under.mk (CommRingCat.ofHom f)) :=
    (isFinitelyPresentable_iff_preservesFilteredColimits).2 h
  -- Finite presentability says exactly that every map into a filtered colimit comes from a stage.
  obtain ⟨j, g', hg'⟩ :=
    IsFinitelyPresentable.exists_hom_of_isColimit
      (X := Under.mk (CommRingCat.ofHom f)) hc g
  exact ⟨j, g', hg'.symm⟩

/-- Helper for Chap10 Lemma 10 127 3: a finitely presented map `R → S` factors through some
stage of any filtered colimit in `Under (CommRingCat.of R)`. -/
theorem factorsThroughStage_of_finitePresentation
    (hf : f.FinitePresentation) :
    ∀ {J : Type u} [Category.{u} J] [IsFiltered J] (F : J ⥤ Under (CommRingCat.of R))
      (c : Cocone F) (_hc : IsColimit c) (g : Under.mk (CommRingCat.ofHom f) ⟶ c.pt),
        ∃ (j : J) (g' : Under.mk (CommRingCat.ofHom f) ⟶ F.obj j), g = g' ≫ c.ι.app j := by
  -- Transfer finite presentation to preservation of the represented functor, then use stagewise
  -- surjectivity of the filtered-colimit comparison.
  apply factorsThroughStage_of_preservesFilteredColimits_coyoneda (f := f)
  simpa using
    (CommRingCat.preservesFilteredColimits_coyoneda
      (CommRingCat.of R) (Under.mk (CommRingCat.ofHom f)) hf)

/-- Helper for Chap10 Lemma 10 127 3: if the identity of `S` factors through a finitely
presented stage in a directed presentation of `S`, then `R → S` is of finite presentation. -/
lemma finitePresentation_of_retract_finitelyPresented_stage
    [Algebra R S] {A : Type u} [CommRing A] [Algebra R A]
    (τ : A →ₐ[R] S) (hA : (algebraMap R A).FinitePresentation)
    (σ : S →ₐ[R] A) (hστ : τ.comp σ = AlgHom.id R S) :
    (algebraMap R S).FinitePresentation := by
  -- First descend finite type along `R → S → A` from the finitely presented stage `A`.
  have hσ : σ.toRingHom.FiniteType := by
    have hcomp : (σ.toRingHom.comp (algebraMap R S)).FiniteType := by
      simpa using (RingHom.FiniteType.of_finitePresentation hA)
    exact RingHom.FiniteType.of_comp_finiteType hcomp
  -- Then apply the retract argument to `S → A → S`, whose composite is the identity on `S`.
  have hτ : τ.toRingHom.FinitePresentation := by
    have hid : (τ.comp σ).FinitePresentation := by
      simpa [hστ] using (AlgHom.FinitePresentation.id R S)
    exact AlgHom.FinitePresentation.of_comp_finiteType σ hid hσ
  -- Finally compose finite presentation back over `R`.
  simpa using RingHom.FinitePresentation.comp hτ hA

/-- Helper for Chap10 Lemma 10 127 3: the right component of an under-morphism respects the
structure maps from the base ring. -/
lemma underRight_hom_commutes
    {A B : Under (CommRingCat.of R)} (m : A ⟶ B) (r : R) :
    m.right.hom (A.hom.hom r) = B.hom.hom r := by
  -- Move the defining triangle identity of the under-morphism down to elements.
  have h : A.hom ≫ m.right = B.hom := by simpa using m.w.symm
  simpa [CommRingCat.comp_apply] using
    congrArg (fun φ : CommRingCat.of R ⟶ B.right => φ.hom r) h

/-- Helper for Chap10 Lemma 10 127 3: the right component preserves the chosen ambient
`R`-algebra maps when they are the under-structure maps. -/
lemma underRightAlgHom_commutes
    {A B : Under (CommRingCat.of R)}
    [Algebra R A.right] [Algebra R B.right]
    (hA : algebraMap R A.right = A.hom.hom)
    (hB : algebraMap R B.right = B.hom.hom)
    (m : A ⟶ B) (r : R) :
    m.right.hom (algebraMap R A.right r) = algebraMap R B.right r := by
  -- Rewrite both ambient algebra maps to the maps displayed by the under-category.
  simpa [hA, hB] using underRight_hom_commutes (R := R) m r

/-- Helper for Chap10 Lemma 10 127 3: an under-morphism is an algebra homomorphism for any
ambient algebra structures whose algebra maps are the displayed under-structure maps. -/
def underRightAlgHom
    {A B : Under (CommRingCat.of R)}
    [Algebra R A.right] [Algebra R B.right]
    (hA : algebraMap R A.right = A.hom.hom)
    (hB : algebraMap R B.right = B.hom.hom)
    (m : A ⟶ B) : A.right →ₐ[R] B.right where
  __ := m.right.hom
  commutes' := underRightAlgHom_commutes (R := R) hA hB m

/-- Helper for Chap10 Lemma 10 127 3: a same-universe skeleton for finitely presented
`R`-algebras equipped with a map to `S`. -/
structure FinitelyPresentedAlgebraOverSkeleton [Algebra R S] where
  /-- The number of polynomial generators. -/
  n : ℕ
  /-- The finitely generated ideal of relations. -/
  I : Ideal (MvPolynomial (Fin n) R)
  /-- The relation ideal is finitely generated. -/
  hI : I.FG
  /-- The structure map from the quotient stage to the target algebra. -/
  toTarget : (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] S

namespace FinitelyPresentedAlgebraOverSkeleton

/-- Helper for Chap10 Lemma 10 127 3: a skeleton quotient stage is finitely presented over
`R`. -/
lemma eval_finitePresentation [Algebra R S]
    (P : FinitelyPresentedAlgebraOverSkeleton (R := R) (S := S)) :
    finitelyPresentedAlgebrasOverProperty R S
      (Over.mk (CommAlgCat.ofHom P.toTarget)) := by
  -- The object property is exactly finite presentation of the quotient polynomial algebra.
  simpa using
    (Algebra.FinitePresentation.quotient (R := R) (A := MvPolynomial (Fin P.n) R) P.hI)

/-- Helper for Chap10 Lemma 10 127 3: realize a skeleton presentation as an object of the
category of finitely presented `R`-algebras over `S`. -/
noncomputable def eval [Algebra R S]
    (P : FinitelyPresentedAlgebraOverSkeleton (R := R) (S := S)) :
    finitelyPresentedAlgebrasOver R S :=
  ⟨Over.mk (CommAlgCat.ofHom P.toTarget), P.eval_finitePresentation⟩

end FinitelyPresentedAlgebraOverSkeleton

/-- Helper for Chap10 Lemma 10 127 3: every finitely presented `R`-algebra over `S` is
isomorphic to a quotient-polynomial skeleton object. -/
lemma exists_finitelyPresentedAlgebraOverSkeleton_iso [Algebra R S]
    (A : finitelyPresentedAlgebrasOver R S) :
    ∃ P : FinitelyPresentedAlgebraOverSkeleton (R := R) (S := S),
      Nonempty (P.eval ≅ A) := by
  -- Choose a finite presentation of the source algebra of the over-object.
  obtain ⟨n, I, e, hI⟩ :=
    (Algebra.FinitePresentation.iff (R := R) (A := A.obj.left)).mp A.property
  let P : FinitelyPresentedAlgebraOverSkeleton (R := R) (S := S) :=
    { n := n, I := I, hI := hI, toTarget := A.obj.hom.hom.comp e.toAlgHom }
  refine ⟨P, ⟨?_⟩⟩
  -- The chosen presentation isomorphism is compatible with the displayed map to `S` by
  -- construction of `P.toTarget`.
  refine CategoryTheory.ObjectProperty.isoMk _ (Over.isoMk (CommAlgCat.isoMk e) ?_)
  apply CommAlgCat.hom_ext
  ext x
  rfl

/-- Helper for Chap10 Lemma 10 127 3: the category of finitely presented `R`-algebras over a
fixed same-universe target is essentially small in that same universe. -/
lemma finitelyPresentedAlgebrasOver_essentiallySmall_sameUniverse [Algebra R S] :
    EssentiallySmall.{u, u, u + 1} (finitelyPresentedAlgebrasOver R S) := by
  -- It suffices to show that the skeleton is covered by the quotient-presentation skeleton above.
  rw [essentiallySmall_iff]
  refine ⟨?_, inferInstance⟩
  let toSkel := toSkeleton ∘ FinitelyPresentedAlgebraOverSkeleton.eval (R := R) (S := S)
  refine small_of_surjective (f := toSkel) fun A ↦ ?_
  simp only [Function.comp_apply, toSkel, toSkeleton_eq_iff]
  exact exists_finitelyPresentedAlgebraOverSkeleton_iso (R := R) (S := S)
    ((fromSkeleton (finitelyPresentedAlgebrasOver R S)).obj A)

/-- Helper for Chap10 Lemma 10 127 3: choose a same-universe directed final functor into the
category of finitely presented `R`-algebras over `S`. -/
lemma exists_final_directed_finitelyPresentedAlgebrasOver_sameUniverse [Algebra R S] :
    ∃ (I : Type u) (_ : PartialOrder I) (_ : Nonempty I) (_ : IsDirectedOrder I)
      (F : I ⥤ finitelyPresentedAlgebrasOver R S), F.Final := by
  classical
  -- Use the same-universe smallness witness to invoke the directed final-refinement theorem.
  let _ : EssentiallySmall.{u, u, u + 1} (finitelyPresentedAlgebrasOver R S) :=
    finitelyPresentedAlgebrasOver_essentiallySmall_sameUniverse (R := R) (S := S)
  let _ : FinallySmall.{u, u, u + 1} (finitelyPresentedAlgebrasOver R S) :=
    CategoryTheory.finallySmall_of_essentiallySmall.{u, u, u + 1}
      (J := finitelyPresentedAlgebrasOver R S)
  obtain ⟨I, hI, hInonempty, hIdir, F, hF⟩ :=
    CategoryTheory.exists_final_from_directed.{u, u, u + 1}
      (finitelyPresentedAlgebrasOver R S)
  exact ⟨I, hI, hInonempty, hIdir, F, hF⟩

/-- Helper for Chap10 Lemma 10 127 3: an equivalence from `CommAlgCat R` to the under-category
transports colimiting cocones. -/
noncomputable def underColimit_of_commAlgColimit {J : Type u} [Category.{u} J]
    {D : J ⥤ CommAlgCat R} {c : Cocone D} (hc : IsColimit c) :
    IsColimit (((commAlgCatEquivUnder (CommRingCat.of R)).functor).mapCocone c) :=
  isColimitOfPreserves ((commAlgCatEquivUnder (CommRingCat.of R)).functor) hc

/-- Helper for Chap10 Lemma 10 127 3: every `R`-algebra admits a same-universe filtered colimit
presentation by finitely presented `R`-algebras in `Under (CommRingCat.of R)`. -/
lemma existsSameUniverseFinitelyPresentedStageCocone
    [Algebra R S] :
    ∃ (J : Type u) (_ : Category.{u} J) (_ : IsFiltered J)
      (F : J ⥤ Under (CommRingCat.of R)) (c : Cocone F),
        Nonempty (IsColimit c) ∧
          Nonempty (c.pt ≅ Under.mk (CommRingCat.ofHom (algebraMap R S))) ∧
          ∀ j : J, (F.obj j).hom.hom.FinitePresentation := by
  classical
  -- Route correction: the previous direct use of Lemma `10.127.2` produced an index in
  -- `Type (u + 1)`.  We first reindex the canonical finitely-presented-over category by a
  -- same-universe final directed functor, then transport the canonical cocone to `Under R`.
  obtain ⟨J, instOrder, instNonempty, instDirected, Ffp, hFfp⟩ :=
    exists_final_directed_finitelyPresentedAlgebrasOver_sameUniverse (R := R) (S := S)
  letI : PartialOrder J := instOrder
  letI : Nonempty J := instNonempty
  letI : IsDirectedOrder J := instDirected
  letI : Ffp.Final := hFfp
  let E := commAlgCatEquivUnder (CommRingCat.of R)
  let D : J ⥤ CommAlgCat R := Ffp ⋙ finitelyPresentedAlgebrasOverDiagram R S
  let cComm : Cocone D := (finitelyPresentedAlgebrasOverCocone R S).whisker Ffp
  let G : J ⥤ Under (CommRingCat.of R) := D ⋙ E.functor
  let cUnder : Cocone G := E.functor.mapCocone cComm
  refine ⟨J, inferInstance, inferInstance, G, cUnder, ?_, ?_, ?_⟩
  · -- Finality of `Ffp` preserves the canonical colimit, and the equivalence transports it.
    refine ⟨?_⟩
    exact underColimit_of_commAlgColimit (R := R)
      (directed_whisker_isColimit (R := R) (A := S) Ffp)
  · -- The transported cocone has point the displayed under-object `R → S`.
    exact ⟨Iso.refl _⟩
  · intro j
    -- The stage property is the finite-presentation field of the corresponding object.
    have hp : (algebraMap R (Ffp.obj j).obj.left).FinitePresentation := by
      simpa [RingHom.finitePresentation_algebraMap, finitelyPresentedAlgebrasOverProperty] using
        (Ffp.obj j).property
    change (algebraMap R (Ffp.obj j).obj.left).FinitePresentation
    exact hp

/-- Helper for Chap10 Lemma 10 127 3: the factorization hypothesis on filtered colimits yields a
retraction of `S` through one finitely presented stage in a directed presentation of `S`. -/
lemma exists_finitelyPresented_stage_retract_of_factorization
    [Algebra R S]
    (hfalg : algebraMap R S = f)
    (hfactor :
      ∀ {J : Type u} [Category.{u} J] [IsFiltered J] (F : J ⥤ Under (CommRingCat.of R))
        (c : Cocone F) (_hc : IsColimit c) (g : Under.mk (CommRingCat.ofHom f) ⟶ c.pt),
          ∃ (j : J) (g' : Under.mk (CommRingCat.ofHom f) ⟶ F.obj j),
            g = g' ≫ c.ι.app j) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (τ : A →ₐ[R] S),
      (algebraMap R A).FinitePresentation ∧
        ∃ σ : S →ₐ[R] A, τ.comp σ = AlgHom.id R S := by
  subst f
  -- Use the same-universe finite-presentation colimit and apply the source-facing factorization
  -- hypothesis to the inverse of its point isomorphism.
  obtain ⟨J, instJ, instFiltered, F, c, ⟨hc⟩, ⟨e⟩, hstagefp⟩ :=
    existsSameUniverseFinitelyPresentedStageCocone (R := R) (S := S)
  letI : Category.{u} J := instJ
  letI : IsFiltered J := instFiltered
  let g : Under.mk (CommRingCat.ofHom (algebraMap R S)) ⟶ c.pt := e.inv
  obtain ⟨j, g', hg'⟩ := hfactor F c hc g
  -- The stage map to `S` and the factor map from `S` are the algebra maps attached to the
  -- corresponding morphisms in the under category.
  letI : Algebra R (F.obj j).right := RingHom.toAlgebra (F.obj j).hom.hom
  letI : Algebra R (Under.mk (CommRingCat.ofHom (algebraMap R S))).right :=
    inferInstanceAs (Algebra R S)
  have hStageAlg : algebraMap R (F.obj j).right = (F.obj j).hom.hom := by
    ext r
    rfl
  have hTargetAlg :
      algebraMap R S =
        (Under.mk (CommRingCat.ofHom (algebraMap R S))).hom.hom := by
    ext r
    rfl
  let τ : (F.obj j).right →ₐ[R] S :=
    underRightAlgHom (R := R) hStageAlg hTargetAlg (c.ι.app j ≫ e.hom)
  let σ : S →ₐ[R] (F.obj j).right :=
    underRightAlgHom (R := R) hTargetAlg hStageAlg g'
  refine ⟨(F.obj j).right, inferInstance, inferInstance, τ, ?_, ?_⟩
  · simpa using hstagefp j
  · refine ⟨σ, ?_⟩
    have hUnder : g' ≫ c.ι.app j ≫ e.hom =
        𝟙 (Under.mk (CommRingCat.ofHom (algebraMap R S))) := by
      rw [← Category.assoc, ← hg']
      exact e.inv_hom_id
    -- Translating the under-category identity through right components gives the desired
    -- retraction of `S`.
    ext x
    have hRight :=
      congrArg
        (fun k : Under.mk (CommRingCat.ofHom (algebraMap R S)) ⟶
            Under.mk (CommRingCat.ofHom (algebraMap R S)) => k.right.hom x)
        hUnder
    simpa [τ, σ, underRightAlgHom, Category.assoc] using hRight

/-- Helper for Chap10 Lemma 10 127 3: the factorization hypothesis on filtered colimits yields a
retraction of `S` through one finitely presented stage in a directed presentation of `S`. -/
lemma exists_finitelyPresented_stage_retract_of_preservesFilteredColimits
    [Algebra R S]
    (hfalg : algebraMap R S = f)
    (h :
      PreservesFilteredColimits (coyoneda.obj (.op (Under.mk (CommRingCat.ofHom f))))) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (τ : A →ₐ[R] S),
      (algebraMap R A).FinitePresentation ∧
        ∃ σ : S →ₐ[R] A, τ.comp σ = AlgHom.id R S := by
  -- Convert preservation into the explicit source-style factorization property, then extract the
  -- retract through one finitely presented stage.
  exact exists_finitelyPresented_stage_retract_of_factorization (f := f) hfalg
    (factorsThroughStage_of_preservesFilteredColimits_coyoneda (f := f) h)

-- Proof sketch: the forward implication is the mathlib owner theorem
-- `CommRingCat.preservesFilteredColimits_coyoneda`. For the converse, preservation of filtered
-- colimits gives the factorization property, and the source argument then factors the identity of
-- `S` through one finitely presented stage from Lemma `10.127.2`.
/-- Helper for Chap10 Lemma 10 127 3: a ring map `R → S` is of finite presentation if and
only if the represented functor `Hom_R(S, -)` preserves filtered colimits. -/
theorem finitePresentation_iff_preservesFilteredColimits_coyoneda :
    f.FinitePresentation ↔
      PreservesFilteredColimits (coyoneda.obj (.op (Under.mk (CommRingCat.ofHom f)))) := by
  constructor
  · intro hf
    -- The forward implication is the owner theorem for finitely presented algebras in `Under R`.
    simpa using
      (CommRingCat.preservesFilteredColimits_coyoneda
        (CommRingCat.of R) (Under.mk (CommRingCat.ofHom f)) hf)
  · intro h
    letI : Algebra R S := f.toAlgebra
    -- Route correction: the converse now follows the source proof by factoring `𝟙_S` through one
    -- finitely presented stage in the directed presentation from Lemma `10.127.2`.
    obtain ⟨A, _instA, _instAlg, τ, hA, σ, hστ⟩ :=
      exists_finitelyPresented_stage_retract_of_preservesFilteredColimits (f := f) rfl h
    simpa using
      finitePresentation_of_retract_finitelyPresented_stage
        (R := R) (S := S) τ hA σ hστ

-- Proof sketch: `(1) → (2)` is the canonical mathlib theorem that a finitely presented
-- `R`-algebra is finitely presentable in `Under R`, equivalently preservation of filtered
-- colimits by `Hom_R(S, -)`. `(2) → (3)` is surjectivity of the comparison map for filtered
-- colimits. For `(3) → (1)`, write `S` as a filtered colimit of finitely
-- presented `R`-algebras using Lemma `10.127.2`; apply the factorization hypothesis to the
-- identity of `S`, deduce that `S` is finitely presented over some finitely presented stage by
-- Lemma `10.6.2`, and then compose finite presentation back over `R`.
/-- Chap10 Lemma 10 127 3: for a ring map `R → S`, the following are equivalent:
`R → S` is of finite presentation, `Hom_R(S, -)` preserves filtered colimits, and every
morphism from `S` to a filtered colimit of `R`-algebras factors through some stage. -/
@[stacks 00QO]
theorem finitePresentation_tfae :
    List.TFAE
      [f.FinitePresentation,
        PreservesFilteredColimits (coyoneda.obj (.op (Under.mk (CommRingCat.ofHom f)))),
        ∀ {J : Type u} [Category.{u} J] [IsFiltered J] (F : J ⥤ Under (CommRingCat.of R))
          (c : Cocone F) (_hc : IsColimit c) (g : Under.mk (CommRingCat.ofHom f) ⟶ c.pt),
            ∃ (j : J) (g' : Under.mk (CommRingCat.ofHom f) ⟶ F.obj j), g = g' ≫ c.ι.app j] := by
  -- The source proof is exactly the three-step cycle `(1) ↔ (2) → (3) → (1)`.
  tfae_have 1 ↔ 2 := finitePresentation_iff_preservesFilteredColimits_coyoneda (f := f)
  tfae_have 2 → 3 := by
    intro h
    -- The middle clause is exactly the stagewise surjectivity consequence of preservation.
    exact factorsThroughStage_of_preservesFilteredColimits_coyoneda (f := f) h
  tfae_have 3 → 1 := by
    intro h
    letI : Algebra R S := f.toAlgebra
    -- Reuse the stage-retract extraction from Lemma `10.127.2`, then close via permanence.
    obtain ⟨A, _instA, _instAlg, τ, hA, σ, hστ⟩ :=
      exists_finitelyPresented_stage_retract_of_factorization (f := f) rfl h
    simpa using
      finitePresentation_of_retract_finitelyPresented_stage
        (R := R) (S := S) τ hA σ hστ
  tfae_finish

end
