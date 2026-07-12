import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap07.Lemma_7_11_2
import StacksProject_2024.Chap07.Definition_7_15_1_Topoi

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped MorphismOfTopoiIn

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

namespace MorphismOfTopoiIn

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (f : MorphismOfTopoiIn J K)

/-
Domain-style sampling for Lemma 7.41.1:
- primary domain: adjunction criteria for faithful and fully faithful right adjoints, together
  with the chapter's source-facing surjectivity predicate for sheaf morphisms and the standard
  functor classes for preserving and reflecting epis, monos, and isomorphisms;
- sampled owner API:
  `Sheaf.IsLocallySurjective`,
  `Sheaf.isLocallySurjective_iff_epi`,
  `Adjunction.faithful_R_of_epi_counit_app`,
  `Adjunction.counit_isIso_of_R_fully_faithful`,
  `Adjunction.fullyFaithfulROfIsIsoCounit`,
  `Functor.ReflectsMonomorphisms`,
  `Functor.ReflectsEpimorphisms`,
  `Functor.FullyFaithful.reflectsIsomorphisms`;
- source/core/bridge triage:
  `source-facing`: the numbered Stacks surjectivity clauses for a morphism of topoi, expressed
  by `Sheaf.IsLocallySurjective`;
  `core/canonical`: the owner properties on `(f _*)`, the inverse-image functor `f⁻¹`, and the
  counit of `f.adjunction`;
  `bridge/view`: the extra source-level lifting predicate
  `surjectionLiftingAlongInverseImage`.

Primitive data are only the morphism of topoi `f` and its adjunction. Faithfulness, full
faithfulness, and reflection of monos, epis, and isomorphisms are derived owner-level API of
`f _*`, so the declarations below should reuse that notation layer directly rather than rebuild
parallel local interfaces. For the textbook surjectivity clauses, the source-facing owner is
already `Sheaf.IsLocallySurjective`, with `Sheaf.isLocallySurjective_iff_epi` providing the
bridge to categorical `Epi` statements. The only genuinely new source-facing predicate here is
the surjection-lifting condition.
-/

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- Surjections onto inverse images lift along a surjective cover in the target topos. -/
def surjectionLiftingAlongInverseImage : Prop :=
  ∀ {ℱ : Sheaf K (Type w)} {𝒢 : Sheaf J (Type w)} (φ : ℱ ⟶ f⁻¹.obj 𝒢),
    Sheaf.IsLocallySurjective φ →
      ∃ (𝒢' : Sheaf J (Type w)) (π : 𝒢' ⟶ 𝒢),
        Sheaf.IsLocallySurjective π ∧
          ∃ ι : (f⁻¹).obj 𝒢' ⟶ ℱ,
            ι ≫ φ = (f⁻¹).map π

-- Proof sketch: a fully faithful functor is faithful after forgetting the fullness data.
/- Canonical companion: property (2) implies property (1), so a fully faithful pushforward is
faithful. This is the exact owner theorem `Functor.FullyFaithful.faithful` specialized to
`f _*`. -/
#check (show (f _*).FullyFaithful → (f _*).Faithful from Functor.FullyFaithful.faithful)

-- Proof sketch: if every counit map is surjective, equality of morphisms can be checked after
-- applying `f_*` and then pulling back along the surjective counit map.
/-- Lemma 7.41.1 (1): property (3) implies property (1), so surjective counit maps force `f_*`
to be faithful. -/
theorem counitIsLocallySurjective_implies_pushforwardFaithful
    (h₃ : ∀ ℱ : Sheaf K (Type w), Sheaf.IsLocallySurjective ((f.adjunction.counit).app ℱ)) :
    (f _*).Faithful := sorry

/-- Owner-level companion to Lemma 7.41.1 (2): epic counit maps force `f_*` to be faithful. -/
theorem counitEpi_implies_pushforwardFaithful
    (h₃ : ∀ ℱ : Sheaf K (Type w), Epi ((f.adjunction.counit).app ℱ)) :
    (f _*).Faithful := by
  letI (ℱ : Sheaf K (Type w)) : Epi ((f.adjunction.counit).app ℱ) := h₃ ℱ
  exact f.adjunction.faithful_R_of_epi_counit_app

-- Proof sketch: an isomorphism is in particular an epimorphism, so this follows from the previous
-- implication.
/-- Lemma 7.41.1 (2): property (7) implies property (1), so an isomorphic counit makes `f_*`
faithful. -/
theorem counitIsIso_implies_pushforwardFaithful
    (h₇ : IsIso f.adjunction.counit) :
    (f _*).Faithful :=
  letI := h₇
  (f.adjunction.fullyFaithfulROfIsIsoCounit).faithful

/- Canonical companion: property (7) implies property (2), so if every counit map is an
isomorphism, then `f_*` is fully faithful. This is the exact canonical adjunction owner theorem
`Adjunction.fullyFaithfulROfIsIsoCounit` applied to `f.adjunction`. -/
recall Adjunction.fullyFaithfulROfIsIsoCounit

-- Proof sketch: every isomorphism is in particular surjective.
/-- Lemma 7.41.1 (3): property (7) implies property (3), so an isomorphic counit is in
particular surjective. -/
theorem counitIsIso_implies_counitIsLocallySurjective
    (h₇ : IsIso f.adjunction.counit) :
    ∀ ℱ : Sheaf K (Type w), Sheaf.IsLocallySurjective ((f.adjunction.counit).app ℱ) := sorry

/-- Owner-level companion to Lemma 7.41.1 (5): an isomorphic counit is in particular
epimorphic. -/
theorem counitIsIso_implies_counitEpi
    (h₇ : IsIso f.adjunction.counit) :
    ∀ ℱ : Sheaf K (Type w), Epi ((f.adjunction.counit).app ℱ) := by
  letI := h₇
  intro ℱ
  infer_instance

-- Proof sketch: transport monomorphism of `f_* φ` across the counit isomorphisms on source and
-- target and conclude that `φ` is monic.
/-- Lemma 7.41.1 (4): property (7) implies property (8), so if every counit map is an
isomorphism, then `f_*` reflects injections. -/
theorem counitIsIso_implies_pushforwardReflectsMonomorphisms
    (h₇ : IsIso f.adjunction.counit) :
    (f _*).ReflectsMonomorphisms := by
  letI : (f _*).Faithful := counitIsIso_implies_pushforwardFaithful f h₇
  infer_instance

-- Proof sketch: exactness of `f⁻¹` and the counit isomorphisms let one descend epimorphy from
-- `f_* φ` to `φ`.
/-- Lemma 7.41.1 (5): property (7) implies property (9), so if every counit map is an
isomorphism, then `f_*` reflects surjections. -/
theorem counitIsIso_implies_pushforwardReflectsEpimorphisms
    (h₇ : IsIso f.adjunction.counit) :
    (f _*).ReflectsEpimorphisms := by
  letI : (f _*).Faithful := counitIsIso_implies_pushforwardFaithful f h₇
  infer_instance

-- Proof sketch: transport an isomorphism of `f_* φ` across the counit isomorphisms and conclude
-- that `φ` itself is an isomorphism.
/-- Lemma 7.41.1 (6): property (7) implies property (10), so if every counit map is an
isomorphism, then `f_*` reflects bijections. -/
theorem counitIsIso_implies_pushforwardReflectsIsomorphisms
    (h₇ : IsIso f.adjunction.counit) :
    (f _*).ReflectsIsomorphisms := by
  letI := h₇
  exact (f.adjunction.fullyFaithfulROfIsIsoCounit).reflectsIsomorphisms

-- Proof sketch: for `(3) → (9)`, apply the exact left adjoint `f⁻¹` to an epic image and use the
-- epic counit to descend epimorphy. For `(9) → (3)`, the counit becomes split epic after
-- applying `f_*`, and reflection of epimorphisms brings this back to the source.
/-- Lemma 7.41.1 (7): property (3) is equivalent to property (9), i.e. the counit is surjective
on all sheaves exactly when `f_*` reflects surjections. -/
theorem counitIsLocallySurjective_iff_pushforwardReflectsEpimorphisms :
    (∀ ℱ : Sheaf K (Type w), Sheaf.IsLocallySurjective ((f.adjunction.counit).app ℱ)) ↔
      (f _*).ReflectsEpimorphisms := sorry

/-- Owner-level companion to Lemma 7.41.1 (9): using
`Sheaf.isLocallySurjective_iff_epi`, the source-facing counit-surjectivity clause can be read as
the usual `Epi` reformulation. -/
theorem counitEpi_iff_pushforwardReflectsEpimorphisms
    [HasSheafify K (Type w)] :
    (∀ ℱ : Sheaf K (Type w), Epi ((f.adjunction.counit).app ℱ)) ↔
      (f _*).ReflectsEpimorphisms := by
  constructor
  · intro h₃
    have h₃' : ∀ ℱ : Sheaf K (Type w), Sheaf.IsLocallySurjective ((f.adjunction.counit).app ℱ) :=
      fun ℱ ↦ (Sheaf.isLocallySurjective_iff_epi _).2 (h₃ ℱ)
    exact (counitIsLocallySurjective_iff_pushforwardReflectsEpimorphisms f).1 h₃'
  · intro h₉ ℱ
    exact (Sheaf.isLocallySurjective_iff_epi _).1
      ((counitIsLocallySurjective_iff_pushforwardReflectsEpimorphisms f).2 h₉ ℱ)

-- Proof sketch: a surjection can be characterized by the pushout square with identical codomain
-- legs, so preservation of pushouts carries surjections to surjections.
/-- Lemma 7.41.1 (8): property (6) implies property (4), so preserving pushouts forces `f_*` to
send surjections to surjections. -/
theorem pushforwardPreservesPushouts_implies_pushforwardMapsLocallySurjective
    (h₆ : PreservesColimitsOfShape WalkingSpan (f _*)) :
    ∀ {ℱ 𝒢 : Sheaf K (Type w)} (φ : ℱ ⟶ 𝒢),
      Sheaf.IsLocallySurjective φ →
        Sheaf.IsLocallySurjective ((f _*).map φ) := sorry

/-- Owner-level companion to Lemma 7.41.1 (10): preserving pushouts makes `f_*` preserve
epimorphisms. -/
theorem pushforwardPreservesPushouts_implies_pushforwardPreservesEpimorphisms
    (h₆ : PreservesColimitsOfShape WalkingSpan (f _*)) :
    (f _*).PreservesEpimorphisms := by
  letI := h₆
  infer_instance

-- Proof sketch: a surjection is the coequalizer of its kernel pair, so preservation of
-- coequalizers makes the pushforward of a surjection epic.
/-- Lemma 7.41.1 (9): property (5) implies property (4), so preserving coequalizers forces
`f_*` to send surjections to surjections. -/
theorem pushforwardPreservesCoequalizers_implies_pushforwardMapsLocallySurjective
    (h₅ : PreservesColimitsOfShape WalkingParallelPair (f _*)) :
    ∀ {ℱ 𝒢 : Sheaf K (Type w)} (φ : ℱ ⟶ 𝒢),
      Sheaf.IsLocallySurjective φ →
        Sheaf.IsLocallySurjective ((f _*).map φ) := sorry

/-- Owner-level companion to Lemma 7.41.1 (11): using
`Sheaf.isLocallySurjective_iff_epi`, preserving coequalizers makes `f_*` preserve
epimorphisms. -/
theorem pushforwardPreservesCoequalizers_implies_pushforwardPreservesEpimorphisms
    [HasSheafify J (Type w)] [HasSheafify K (Type w)]
    (h₅ : PreservesColimitsOfShape WalkingParallelPair (f _*)) :
    (f _*).PreservesEpimorphisms := sorry

-- Proof sketch: for `(4) → (11)`, push forward an epic map to `f⁻¹ 𝒢`, pull back along the unit,
-- and use preservation of epimorphisms to build the desired cover of `𝒢`. For `(11) → (4)`,
-- apply the lifting property to the pullback of the counit and push the resulting factorization
-- forward.
/-- Lemma 7.41.1 (10): property (4) is equivalent to property (11), i.e. `f_*` sends surjections
to surjections exactly when surjections onto inverse images lift after a surjective cover. -/
theorem pushforwardMapsLocallySurjective_iff_surjectionLiftingAlongInverseImage :
    (∀ {ℱ 𝒢 : Sheaf K (Type w)} (φ : ℱ ⟶ 𝒢),
      Sheaf.IsLocallySurjective φ →
        Sheaf.IsLocallySurjective ((f _*).map φ)) ↔
      f.surjectionLiftingAlongInverseImage := sorry

/-- Owner-level companion to Lemma 7.41.1 (12): using
`Sheaf.isLocallySurjective_iff_epi`, the source-facing preservation-of-surjections clause is
equivalent to the categorical statement that `f_*` preserves epimorphisms. -/
theorem pushforwardPreservesEpimorphisms_iff_surjectionLiftingAlongInverseImage
    [HasSheafify J (Type w)] [HasSheafify K (Type w)] :
    (f _*).PreservesEpimorphisms ↔ f.surjectionLiftingAlongInverseImage := sorry

-- Proof sketch: if `f_* φ` is monic, then the induced diagonal map becomes an epimorphism after
-- pushforward; reflection of epimorphisms shows the original diagonal map is epic, hence `φ` is
-- monic.
/-- Lemma 7.41.1 (11): property (9) implies property (8), so if `f_*` reflects surjections then
it also reflects injections. -/
theorem pushforwardReflectsEpimorphisms_implies_pushforwardReflectsMonomorphisms
    (h₉ : (f _*).ReflectsEpimorphisms) :
    (f _*).ReflectsMonomorphisms := sorry

-- Proof sketch: in a balanced sheaf category, a morphism is an isomorphism as soon as it is both
-- monic and epic; combine the previous implication with reflection of epimorphisms.
/-- Lemma 7.41.1 (12): property (9) implies property (10), so if `f_*` reflects surjections then
it reflects bijections. -/
theorem pushforwardReflectsEpimorphisms_implies_pushforwardReflectsIsomorphisms
    (h₉ : (f _*).ReflectsEpimorphisms) :
    (f _*).ReflectsIsomorphisms := sorry

-- Proof sketch: the forward direction is the standard implication from a fully faithful right
-- adjoint to an isomorphic counit; the reverse direction is already the earlier canonical recall
-- `Adjunction.fullyFaithfulROfIsIsoCounit`, so no extra `Full ∧ Faithful` wrapper is needed.
/- Canonical companion: the direction from full faithfulness of `f_*` to invertibility of the
counit `f⁻¹ f_* ℱ ⟶ ℱ` is the exact canonical adjunction owner theorem
`Adjunction.counit_isIso_of_R_fully_faithful` applied to `f.adjunction`. Together with the
earlier recall `Adjunction.fullyFaithfulROfIsIsoCounit`, this already gives the source
equivalence in canonical owner form. -/
recall Adjunction.counit_isIso_of_R_fully_faithful

end

end MorphismOfTopoiIn

end CategoryTheory
