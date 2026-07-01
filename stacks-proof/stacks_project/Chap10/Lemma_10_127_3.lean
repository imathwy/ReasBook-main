import Mathlib
import Mathlib.Data.List.TFAE
import stacks_project.Chap10.Lemma_10_127_2
import stacks_project.Chap10.Lemma_10_6_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

universe u vJ uJ

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
/-- Helper for Lemma 10.127.3: preservation of filtered colimits by `Hom_R(S, -)` implies that any
map from `S` into a filtered colimit of `R`-algebras factors through some stage. -/
theorem factorsThroughStage_of_preservesFilteredColimits_coyoneda
    (h :
      PreservesFilteredColimits (coyoneda.obj (.op (Under.mk (CommRingCat.ofHom f))))) :
    ∀ {J : Type uJ} [Category.{vJ} J] [IsFiltered J] (F : J ⥤ Under (CommRingCat.of R))
      (c : Cocone F) (_hc : IsColimit c) (g : Under.mk (CommRingCat.ofHom f) ⟶ c.pt),
        ∃ (j : J) (g' : Under.mk (CommRingCat.ofHom f) ⟶ F.obj j), g = g' ≫ c.ι.app j := by
  -- TODO: derive the required stage factorization from `h` after repairing the universe bridge
  -- from `PreservesFilteredColimits` to the arbitrary `(uJ, vJ)`-sized filtered diagram used
  -- here. The current obstacle is that `h` only synthesizes the owner `u`-sized instance, while
  -- this helper is stated for all shape universes.
  sorry

/-- Helper for Lemma 10.127.3: a finitely presented map `R → S` factors through some stage of any
filtered colimit in `Under (CommRingCat.of R)`. -/
theorem factorsThroughStage_of_finitePresentation
    (hf : f.FinitePresentation) :
    ∀ {J : Type uJ} [Category.{vJ} J] [IsFiltered J] (F : J ⥤ Under (CommRingCat.of R))
      (c : Cocone F) (_hc : IsColimit c) (g : Under.mk (CommRingCat.ofHom f) ⟶ c.pt),
        ∃ (j : J) (g' : Under.mk (CommRingCat.ofHom f) ⟶ F.obj j), g = g' ≫ c.ι.app j := by
  -- Transfer finite presentation to preservation of the represented functor, then use stagewise
  -- surjectivity of the filtered-colimit comparison.
  apply factorsThroughStage_of_preservesFilteredColimits_coyoneda (f := f)
  simpa using
    (CommRingCat.preservesFilteredColimits_coyoneda
      (CommRingCat.of R) (Under.mk (CommRingCat.ofHom f)) hf)

/-- Helper for Lemma 10.127.3: if the identity of `S` factors through a finitely presented stage
in a directed presentation of `S`, then `R → S` is of finite presentation. -/
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

/-- Helper for Lemma 10.127.3: the factorization hypothesis on filtered colimits yields a
retraction of `S` through one finitely presented stage in a directed presentation of `S`. -/
lemma exists_finitelyPresented_stage_retract_of_factorization
    [Algebra R S]
    (hfalg : algebraMap R S = f)
    (hfactor :
      ∀ {J : Type uJ} [Category.{vJ} J] [IsFiltered J] (F : J ⥤ Under (CommRingCat.of R))
        (c : Cocone F) (_hc : IsColimit c) (g : Under.mk (CommRingCat.ofHom f) ⟶ c.pt),
          ∃ (j : J) (g' : Under.mk (CommRingCat.ofHom f) ⟶ F.obj j),
            g = g' ≫ c.ι.app j) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (τ : A →ₐ[R] S),
      (algebraMap R A).FinitePresentation ∧
        ∃ σ : S →ₐ[R] A, τ.comp σ = AlgHom.id R S := by
  -- Route correction: the intended source-faithful proof is to apply `hfactor` to the directed
  -- finitely presented presentation from Lemma `10.127.2` and read the retract off the equality in
  -- `Under`. The current blocker is a universe mismatch: Lemma `10.127.2` produces an index type in
  -- `Type (u + 1)`, but `hfactor` is stated only for the fixed universe `Type uJ`.
  sorry

/-- Helper for Lemma 10.127.3: the factorization hypothesis on filtered colimits yields a
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
  -- TODO: combine the filtered-colimit factorization theorem above with the stage-retract
  -- extraction once the shared universe mismatch on arbitrary shape sizes has been repaired.
  sorry

-- Proof sketch: the forward implication is the mathlib owner theorem
-- `CommRingCat.preservesFilteredColimits_coyoneda`. For the converse, preservation of filtered
-- colimits gives the factorization property, and the source argument then factors the identity of
-- `S` through one finitely presented stage from Lemma `10.127.2`.
/-- A ring map `R → S` is of finite presentation if and only if the represented functor
`Hom_R(S, -)` preserves filtered colimits. -/
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
/-- Lemma 10.127.3: for a ring map `R → S`, the following are equivalent: `R → S` is of finite
presentation, `Hom_R(S, -)` preserves filtered colimits, and every morphism from `S` to a filtered
colimit of `R`-algebras factors through some stage. -/
theorem finitePresentation_tfae :
    List.TFAE
      [f.FinitePresentation,
        PreservesFilteredColimits (coyoneda.obj (.op (Under.mk (CommRingCat.ofHom f)))),
        ∀ {J : Type uJ} [Category.{vJ} J] [IsFiltered J] (F : J ⥤ Under (CommRingCat.of R))
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
