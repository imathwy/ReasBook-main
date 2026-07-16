import Mathlib
import stacks_proof.stacks_project.Chap08.Definition_8_4_1
import stacks_proof.stacks_project.Chap08.Lemma_8_4_2
import stacks_proof.stacks_project.Chap08.Lemma_8_12_1

open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology.Cover

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)

/-- Helper for Lemma 8.12.2: a continuous functor of sites sends covering sieves to covering
sieves. This ports the closed-sieves argument under the exact hypothesis needed here. -/
theorem coverPreserving_of_isContinuous_basic
    [Functor.IsContinuous u J K] :
    CoverPreserving J K u := by
  refine ⟨?_⟩
  intro X S hS
  classical
  let R : Sieve (u.obj X) := S.functorPushforward u
  let Q : Sieve (u.obj X) := K.close R
  have hQclosed : K.IsClosed Q := by
    simpa [Q] using K.close_isClosed R
  let P : Cᵒᵖ ⥤ Type (max uD vD) := u.op ⋙ (Functor.closedSieves K).toFunctor
  have hP : Presheaf.IsSheaf J P := by
    have hclosed : Presheaf.IsSheaf K (Functor.closedSieves K).toFunctor := by
      rw [isSheaf_iff_isSheaf_of_type]
      exact CategoryTheory.classifier_isSheaf K
    exact u.op_comp_isSheaf_of_isSheaf J K (Functor.closedSieves K).toFunctor hclosed
  let s : P.obj (Opposite.op X) := ⟨Q, hQclosed⟩
  let Ttop : Sieve (u.obj X) := ⊤
  let t : P.obj (Opposite.op X) := ⟨Ttop, by
    intro Y f hf
    trivial⟩
  have hs_eq_top : s = t := by
    -- On the original cover, the closure of the image sieve restricts to the top sieve.
    have hsep := ((CategoryTheory.isSheaf_iff_isSheaf_of_type J P).1 hP).isSeparated S hS
    apply hsep.ext
    intro Y f hf
    apply Subtype.ext
    apply Sieve.ext
    intro Z g
    constructor
    · intro _
      trivial
    · intro _
      dsimp [P, s, t, Q, R]
      have hmemR : R (u.map f) := by
        exact Sieve.image_mem_functorPushforward (F := u) (R := S) hf
      have hmemQ : Q (u.map f) := K.le_close R (u.map f) hmemR
      exact Q.downward_closed hmemQ g
  have hidQ : Q (𝟙 (u.obj X)) := by
    -- The separatedness comparison identifies the closed image sieve with the top closed sieve.
    have htopQ : Q = ⊤ := by
      simpa [s, t, P] using congrArg Subtype.val hs_eq_top
    rw [htopQ]
    trivial
  have hQtop : Q = ⊤ := by
    -- A sieve containing the identity is the top sieve, so the image sieve has top closure.
    apply eq_top_iff.2
    intro Y f _
    simpa using Q.downward_closed hidQ f
  exact (K.close_eq_top_iff_mem R).1 hQtop

/-- Helper for Lemma 8.12.2: the image of the arrows of a `J`-cover under a continuous functor
forms a `K`-covering family. -/
theorem imageCover_of_isContinuous
    [Functor.IsContinuous u J K] {U : C} (S : J.Cover U) :
    Sieve.ofArrows (fun I : S.Arrow ↦ u.obj I.Y) (fun I ↦ u.map I.f) ∈ K (u.obj U) := by
  have hpush :=
    (coverPreserving_of_isContinuous_basic (J := J) (K := K) u).cover_preserve
      (S := (S : Sieve U)) S.condition
  have hSgen :
      Sieve.generate (Presieve.ofArrows Arrow.Y (fun I : S.Arrow ↦ I.f)) =
        (S : Sieve U) := by
    simpa [Sieve.ofArrows] using S.ofArrows_eq
  -- Rewrite the pushforward of the generated cover arrows into the image family.
  have hbase :
      Sieve.generate
          (Presieve.map u (Presieve.ofArrows Arrow.Y (fun I : S.Arrow ↦ I.f))) ∈
        K (u.obj U) := by
    rw [Sieve.generate_map_eq_functorPushforward, hSgen]
    exact hpush
  simpa [Presieve.map_ofArrows, Sieve.ofArrows] using hbase

/-- Helper for Lemma 8.12.2: coverwise effectiveness of canonical descent data gives the stack
condition for the pullback projection. -/
theorem pullbackProjection_isStack_of_coverwise_descent
    [Functor.IsContinuous u J K]
    (p : S ⥤ D) [IsStackOnSite K p]
    (hcover : ∀ (U : C) (S : J.Cover U),
        ((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).toDescentData
          (fun I : S.Arrow ↦ I.f)).IsEquivalence) :
    Pseudofunctor.IsStack (canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)) J := by
  -- The pullback projection is already fibred by Lemma 8.12.1, so Lemma 8.4.2 converts the
  -- cover-indexed descent condition into the site-level stack owner.
  letI : (CategoricalPullback.π₁ u p).IsFibered := inferInstance
  have hsite : IsStackOnSite J (CategoricalPullback.π₁ u p) :=
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence J
      (CategoricalPullback.π₁ u p)).2 hcover
  exact hsite.toIsStack

/-- Helper for Lemma 8.12.2: a stack over `(D, K)` has effective canonical descent for every
`K`-cover. -/
theorem targetStack_canonicalDescentFunctor_isEquivalence
    (p : S ⥤ D) [IsStackOnSite K p] {V : D} (T : K.Cover V) :
    ((canonicalFiberPseudofunctor p).toDescentData (fun I : T.Arrow ↦ I.f)).IsEquivalence := by
  -- This is the forward direction of the coverwise characterization from Lemma 8.4.2.
  exact
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence K p).1
      inferInstance V T

/-- Helper for Lemma 8.12.2: the target stack has effective descent for the image family of a
`J`-cover under the continuous functor. -/
theorem targetStack_imageDescentFunctor_isEquivalence
    [Functor.IsContinuous u J K]
    (p : S ⥤ D) [IsStackOnSite K p] {U : C} (S : J.Cover U) :
    ((canonicalFiberPseudofunctor p).toDescentData
      (fun I : S.Arrow ↦ u.map I.f)).IsEquivalence := by
  -- The previous helper proves that this image family generates a covering sieve in `K`.
  have hImageCover :
      Sieve.ofArrows (fun I : S.Arrow ↦ u.obj I.Y) (fun I ↦ u.map I.f) ∈ K (u.obj U) :=
    imageCover_of_isContinuous (J := J) (K := K) u S
  exact
    Pseudofunctor.isEquivalence_toDescentData
      (canonicalFiberPseudofunctor p) (fun I : S.Arrow ↦ u.map I.f) hImageCover

end

end CategoryTheory
