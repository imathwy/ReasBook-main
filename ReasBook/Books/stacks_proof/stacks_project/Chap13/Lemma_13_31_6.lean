import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import StacksProject_2024.Chap13.Definition_13_14_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

universe v₁ v₂ u₁ u₂

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒜] [Abelian 𝒜]
  [Category.{v₂} 𝒟']

/- Domain-style sampling for Lemma 13.31.6:
- primary domain: pointwise right derived functors on the homotopy category `K(\mathcal A)`,
  computed on K-injective complexes and transported along quasi-isomorphisms;
- sampled owner declarations:
  `Functor.ComputesRightDerivedAt`,
  `Functor.HasPointwiseRightDerivedFunctorAt`,
  `Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem`,
  `DerivedCategory.Qh`,
  `CochainComplex.IsKInjective.Qh_map_bijective`;
- best owner abstractions:
  `source-facing`: the statement that a K-injective complex computes the right derived functor;
  `core/canonical`: `Functor.ComputesRightDerivedAt` and the transport owner
    `Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem`;
  `bridge/view`: the downstream use of the canonical transport theorem for objects
    quasi-isomorphic to a K-injective one.
- primitive data: the functor `F` and the K-injective complex `I`.
- derived API: downstream pointwise-definedness statements are obtained by transporting the
  computation theorem at `(HomotopyCategory.quotient 𝒜 (up ℤ)).obj I` along a quasi-isomorphism
  using `Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem`.

The main owner-level theorem here is therefore the computation statement at a K-injective object.
The pointwise-existence statement for an arbitrary quasi-isomorphic object should therefore be
handled downstream by the canonical transport API, not by a separate local wrapper theorem.
-/

variable (F : HomotopyCategory 𝒜 (up ℤ) ⥤ 𝒟')

local notation "KQ" => HomotopyCategory.quotient 𝒜 (up ℤ)
local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)

-- Proof sketch: `IsKInjective.Qh_map_bijective` says every arrow into a K-injective complex is
-- uniquely determined by its image in the derived category. Applied to the costructured-arrow
-- category over `DerivedCategory.Qh.obj ((KQ).obj I)`, this makes the identity denominator
-- terminal, so the
-- pointwise right derived value is just `F.obj ((KQ).obj I)` and the canonical unit is an
-- isomorphism.
/-- Helper for Lemma 13.31.6: morphisms into a K-injective complex are already determined after
passing to the abstract localization at quasi-isomorphisms. -/
private lemma q_map_bijective_of_isKInjective
    (K : HomotopyCategory 𝒜 (up ℤ)) (I : CochainComplex 𝒜 ℤ) [I.IsKInjective] :
    Function.Bijective
      ((MorphismProperty.Q Qis).map :
        (K ⟶ (KQ).obj I) →
          ((MorphismProperty.Q Qis).obj K ⟶ (MorphismProperty.Q Qis).obj ((KQ).obj I))) := by
  let Q := MorphismProperty.Q Qis
  let e := Localization.homEquiv Qis Q DerivedCategory.Qh (X := K) (Y := (KQ).obj I)
  have heq :
      e ∘ (Q.map : (K ⟶ (KQ).obj I) → (Q.obj K ⟶ Q.obj ((KQ).obj I))) =
        (DerivedCategory.Qh.map :
          (K ⟶ (KQ).obj I) → (DerivedCategory.Qh.obj K ⟶ DerivedCategory.Qh.obj ((KQ).obj I))) := by
    funext f
    simpa [e, Function.comp] using
      (Localization.homEquiv_map (W := Qis) (L₁ := Q) (L₂ := DerivedCategory.Qh) f)
  have hcomp :
      Function.Bijective (e ∘ (Q.map : (K ⟶ (KQ).obj I) → _)) := by
    rw [heq]
    exact CochainComplex.IsKInjective.Qh_map_bijective K I
  exact (Function.Bijective.of_comp_iff' e.bijective _).mp hcomp

/-- Helper for Lemma 13.31.6: the identity denominator is terminal in the pointwise
costructured-arrow category over a K-injective complex. -/
private noncomputable def identity_denominator_isTerminal_of_isKInjective
    (I : CochainComplex 𝒜 ℤ) [I.IsKInjective] :
    IsTerminal
      (CostructuredArrow.mk (𝟙 ((MorphismProperty.Q Qis).obj ((KQ).obj I))) :
        CostructuredArrow (MorphismProperty.Q Qis)
          ((MorphismProperty.Q Qis).obj ((KQ).obj I))) := by
  let Q := MorphismProperty.Q Qis
  refine IsTerminal.ofUniqueHom (fun g ↦ ?_) ?_
  · -- Proof comment: the localization morphism into `Q.obj I` has a unique homotopy-category
    -- lift because `I` is K-injective.
    let hBij := q_map_bijective_of_isKInjective (𝒜 := 𝒜) g.left I
    refine CostructuredArrow.homMk (hBij.surjective g.hom |>.choose) ?_
    exact (hBij.surjective g.hom |>.choose_spec)
  · intro g m
    -- Proof comment: uniqueness reduces to injectivity of the abstract localization map on homs
    -- into the K-injective target.
    apply CostructuredArrow.hom_ext
    let hBij := q_map_bijective_of_isKInjective (𝒜 := 𝒜) g.left I
    have hm : Q.map m.left = g.hom := by simpa using m.w
    exact hBij.injective <| hm.trans (hBij.surjective g.hom |>.choose_spec).symm

/-- Helper for Lemma 13.31.6: the pointwise right-derived indexing diagram at a K-injective
complex has a colimit because its identity denominator is terminal. -/
private lemma hasPointwiseRightDerivedFunctorAt_of_isKInjective
    (I : CochainComplex 𝒜 ℤ) [I.IsKInjective] :
    F.HasPointwiseRightDerivedFunctorAt Qis ((KQ).obj I) := by
  let Q := MorphismProperty.Q Qis
  let T := identity_denominator_isTerminal_of_isKInjective (𝒜 := 𝒜) I
  let D := CostructuredArrow.proj Q (Q.obj ((KQ).obj I)) ⋙ F
  -- Proof comment: a terminal object in the indexing category gives the required pointwise
  -- colimit immediately.
  refine ⟨?_⟩
  change HasColimit D
  exact ⟨⟨coconeOfDiagramTerminal T D, colimitOfDiagramTerminal T D⟩⟩

/-- Lemma 13.31.6: every K-injective complex computes the right derived functor of
`F : K(\mathcal A) ⥤ \mathcal D'` with respect to quasi-isomorphisms. -/
@[stacks 070Y]
theorem kInjective_computesRightDerivedFunctorAt
    (I : CochainComplex 𝒜 ℤ) [I.IsKInjective] :
    F.ComputesRightDerivedAt Qis ((KQ).obj I) := by
  -- Proof comment: the source proof shows the identity denominator is terminal for a
  -- K-injective complex, so the pointwise colimit exists and its identity leg is an isomorphism.
  letI := hasPointwiseRightDerivedFunctorAt_of_isKInjective (𝒜 := 𝒜) (F := F) I
  have hIso :
      IsIso
        (rightDerivedValueLeg Qis F (𝟙 ((KQ).obj I))
          (MorphismProperty.id_mem Qis ((KQ).obj I))) := by
    let Q := MorphismProperty.Q Qis
    let T := identity_denominator_isTerminal_of_isKInjective (𝒜 := 𝒜) I
    let D := CostructuredArrow.proj Q (Q.obj ((KQ).obj I)) ⋙ F
    letI : HasColimit D := Functor.HasPointwiseRightDerivedFunctorAt.hasColimit F Q Qis ((KQ).obj I)
    -- Proof comment: rewriting the identity denominator to the literal identity arrow turns the
    -- right-derived value leg into the colimit inclusion at the terminal object.
    rw [rightDerivedValueLeg, Localization.isoOfHom_id_inv Q Qis ((KQ).obj I)
      (MorphismProperty.id_mem Qis ((KQ).obj I))]
    simpa [D] using (Limits.isIso_ι_of_isTerminal T D)
  exact
    { isIso_rightDerivedValueLeg := hIso }

end

end CategoryTheory
