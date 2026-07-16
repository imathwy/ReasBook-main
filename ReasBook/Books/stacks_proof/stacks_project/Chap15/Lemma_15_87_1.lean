import Mathlib
import stacks_proof.stacks_project.Chap12.Definition_12_19_3
import stacks_proof.stacks_project.Chap12.Definition_12_31_2
import stacks_proof.stacks_project.Chap12.Lemma_12_31_3
import stacks_proof.stacks_project.Chap13.Lemma_13_32_2
import stacks_proof.stacks_project.Chap13.Lemma_13_20_1
import stacks_proof.stacks_project.Chap13.Lemma_13_15_6
import stacks_proof.stacks_project.Chap13.Definition_13_34_1
import stacks_proof.stacks_project.Chap19.Proposition_19_6_1
import stacks_proof.stacks_project.Chap15.«15_87_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ComplexShape
open Opposite

noncomputable section

attribute [local instance] HasDerivedCategory.standard

local notation "Ab" => AddCommGrpCat
local notation "AbSeq" => SequentialInverseSystem Ab
local notation "DAb" => DerivedCategory Ab
local notation "DAbSeq" => DerivedCategory AbSeq
local notation "Qish" => HomotopyCategory.quasiIso AbSeq (up ℤ)
local notation "KtoD" => mapHomotopyCategoryToDerived (lim : AbSeq ⥤ Ab)
local notation "RightAcyclic" =>
  IsRightAcyclicForAdditiveFunctor (lim : AbSeq ⥤ Ab)

-- Proof sketch: apply the explicit embedding of an arbitrary inverse system into a
-- Mittag-Leffler inverse system from the Stacks Project argument, and use the preceding
-- Mittag-Leffler acyclicity statement to see that the target of that monomorphism is right
-- acyclic for `lim`.
/-- The Chapter `13` right-acyclicity owner for inverse limit on sequential inverse systems of
abelian groups has monomorphic envelopes. -/
instance abelianGroupLimit_rightAcyclic_hasMonoEmbedding :
    HasMonoEmbedding RightAcyclic where
  exists_mono A := by
    -- Use any chosen injective presentation of `A` inside the Grothendieck abelian category `AbSeq`.
    let p := (EnoughInjectives.presentation A).some
    refine ⟨p.J, ?_, p.f, inferInstance⟩
    -- Injective objects are right acyclic for any additive functor.
    exact injective_isRightAcyclicForAdditiveFunctor (F := (lim : AbSeq ⥤ Ab)) p.J

/-- Helper for Lemma 15.87.1: the finite prefix family
`(A_0, \dots, A_n)` attached to a sequential inverse system `A`. -/
private abbrev prefixProductFamily (A : AbSeq) (n : ℕ) : Fin (n + 1) → Ab :=
  fun i ↦ A.obj (op i.1)

/-- Helper for Lemma 15.87.1: the product of the first `n + 1` stages of `A`. -/
private abbrev prefixProductObject (A : AbSeq) (n : ℕ) : Ab :=
  ∏ᶜ prefixProductFamily A n

/-- Helper for Lemma 15.87.1: the successor transition on finite prefixes forgets the last
coordinate. -/
private abbrev prefixProductDrop (A : AbSeq) (n : ℕ) :
    prefixProductObject A (n + 1) ⟶ prefixProductObject A n :=
  Pi.lift fun i : Fin (n + 1) ↦
    Pi.π (prefixProductFamily A (n + 1)) (Fin.castSucc i)

/-- Helper for Lemma 15.87.1: the finite-prefix tower of `A`, whose `n`-th stage is
`\prod_{i \le n} A_i`. -/
private abbrev prefixProductSystem (A : AbSeq) : AbSeq :=
  @Functor.ofOpSequence Ab _
    (fun n ↦ prefixProductObject A n)
    (fun n ↦ prefixProductDrop A n)

/-- Helper for Lemma 15.87.1: appending a zero last coordinate splits the prefix-forgetting map. -/
private abbrev prefixProductZeroSection (A : AbSeq) (n : ℕ) :
    prefixProductObject A n ⟶ prefixProductObject A (n + 1) :=
  Pi.lift <| Fin.lastCases 0 fun i : Fin (n + 1) ↦
    Pi.π (prefixProductFamily A n) i

/-- Helper for Lemma 15.87.1: the zero section agrees with the original coordinate on every
non-last projection. -/
private theorem prefixProductZeroSection_comp_castSucc (A : AbSeq) (n : ℕ) (i : Fin (n + 1)) :
    prefixProductZeroSection A n ≫
        Pi.π (prefixProductFamily A (n + 1)) (Fin.castSucc i) =
      Pi.π (prefixProductFamily A n) i := by
  -- The `castSucc` coordinates are exactly the retained coordinates in `Fin.lastCases`.
  rw [prefixProductZeroSection, Pi.lift_π]
  simp only [Fin.lastCases_castSucc]

private theorem prefixProductZeroSection_comp_drop (A : AbSeq) (n : ℕ) :
    prefixProductZeroSection A n ≫ prefixProductDrop A n = 𝟙 _ := by
  -- Compare both maps after each projection of the shorter prefix product.
  apply Pi.hom_ext
  intro i
  rw [Category.assoc, prefixProductDrop, Pi.lift_π]
  simpa using prefixProductZeroSection_comp_castSucc A n i

/-- Helper for Lemma 15.87.1: each successor map in the prefix-product tower is split epic. -/
private instance prefixProductDrop_splitEpi (A : AbSeq) (n : ℕ) :
    SplitEpi (prefixProductDrop A n) where
  section_ := prefixProductZeroSection A n
  id := prefixProductZeroSection_comp_drop A n

/-- Helper for Lemma 15.87.1: a split successor map in the prefix-product tower is epic. -/
private instance prefixProductDrop_epi (A : AbSeq) (n : ℕ) :
    Epi (prefixProductDrop A n) where
  left_cancellation := by
    intro Z g h hgh
    -- Compose with the chosen section to cancel the split epic.
    have hsection := congrArg (fun t ↦ prefixProductZeroSection A n ≫ t) hgh
    calc
      g = (prefixProductZeroSection A n ≫ prefixProductDrop A n) ≫ g := by
        simp [prefixProductZeroSection_comp_drop A n]
      _ = (prefixProductZeroSection A n ≫ prefixProductDrop A n) ≫ h := by
        simpa [Category.assoc] using hsection
      _ = h := by
        simp [prefixProductZeroSection_comp_drop A n]

/-- Helper for Lemma 15.87.1: the transition from stage `k + 1` to stage `i` factors through the
last successor map. -/
private theorem prefixProduct_transitionMap_succ
    (A : AbSeq) {i k : ℕ} (hik : i ≤ k) :
    (prefixProductSystem A).transitionMap (Nat.le_succ_of_le hik) =
      (prefixProductSystem A).stepMap k ≫ (prefixProductSystem A).transitionMap hik := by
  -- In `ℕᵒᵖ`, the longer transition uniquely factors through the final successor map.
  have hh :
      (homOfLE (Nat.le_succ_of_le hik)).op =
        (homOfLE (Nat.le_succ k)).op ≫ (homOfLE hik).op := by
    subsingleton
  simpa [SequentialInverseSystem.transitionMap, SequentialInverseSystem.stepMap] using
    congrArg (prefixProductSystem A).map hh

/-- Helper for Lemma 15.87.1: every transition map in the prefix-product tower is epic. -/
private theorem prefixProduct_transitionMap_epi
    (A : AbSeq) {i k : ℕ} (hik : i ≤ k) :
    Epi ((prefixProductSystem A).transitionMap hik) := by
  -- Induct along the unique factorization through the successor maps.
  induction hik with
  | refl =>
      simpa [prefixProductSystem, SequentialInverseSystem.transitionMap] using
        (inferInstance : Epi (𝟙 (prefixProductObject A i)))
  | @step k hik ih =>
      rw [prefixProduct_transitionMap_succ A hik]
      haveI : Epi ((prefixProductSystem A).stepMap k) := by
        simpa [prefixProductSystem, SequentialInverseSystem.stepMap,
          SequentialInverseSystem.transitionMap] using prefixProductDrop_epi A k
      letI : Epi ((prefixProductSystem A).transitionMap hik) := ih
      infer_instance

/-- Helper for Lemma 15.87.1: the finite-prefix tower is Mittag-Leffler because all of its
transition maps are epic. -/
private theorem prefixProductSystem_isMittagLeffler (A : AbSeq) :
    SequentialInverseSystem.IsMittagLeffler (prefixProductSystem A) := by
  -- Choose the stabilization index `c = i`; every later transition already has full image.
  intro i
  refine ⟨i, le_rfl, ?_⟩
  intro k hik
  letI : Epi ((prefixProductSystem A).transitionMap hik) :=
    prefixProduct_transitionMap_epi A hik
  calc
    imageSubobject ((prefixProductSystem A).transitionMap hik)
        = (⊤ : Subobject ((prefixProductSystem A).obj (op i))) :=
          Limits.imageSubobject_eq_top_of_epi _
    _ = imageSubobject ((prefixProductSystem A).transitionMap (show i ≤ i from le_rfl)) := by
          simpa [SequentialInverseSystem.transitionMap] using
            (Limits.imageSubobject_eq_top_of_epi
              (𝟙 ((prefixProductSystem A).obj (op i))) :
                imageSubobject (𝟙 ((prefixProductSystem A).obj (op i))) =
                  (⊤ : Subobject ((prefixProductSystem A).obj (op i)))).symm

/-- Helper for Lemma 15.87.1: the canonical map `A_n → \prod_{i \le n} A_i` records the compatible
prefix of an element in the last stage. -/
private abbrev prefixProductEnvelopeApp (A : AbSeq) (n : ℕ) :
    A.obj (op n) ⟶ prefixProductObject A n :=
  Pi.lift fun i : Fin (n + 1) ↦
    A.transitionMap (Nat.le_of_lt_succ i.2)

/-- Helper for Lemma 15.87.1: the last coordinate of the canonical prefix tuple is the original
element. -/
private theorem prefixProductEnvelopeApp_comp_last (A : AbSeq) (n : ℕ) :
    prefixProductEnvelopeApp A n ≫ Pi.π (prefixProductFamily A n) (Fin.last n) = 𝟙 _ := by
  -- The last projection picks out the identity transition `A_n ⟶ A_n`.
  rw [prefixProductEnvelopeApp, Pi.lift_π]
  simp [SequentialInverseSystem.transitionMap]

/-- Helper for Lemma 15.87.1: each component of the canonical prefix map is split monic. -/
private instance prefixProductEnvelopeApp_isSplitMono (A : AbSeq) (n : ℕ) :
    IsSplitMono (prefixProductEnvelopeApp A n) :=
  IsSplitMono.mk' ⟨Pi.π (prefixProductFamily A n) (Fin.last n),
    prefixProductEnvelopeApp_comp_last A n⟩

/-- Helper for Lemma 15.87.1: the `castSucc` coordinates of the envelope map are the earlier
transition maps from the current stage. -/
private theorem prefixProductEnvelopeApp_comp_castSucc
    (A : AbSeq) (n : ℕ) (i : Fin (n + 1)) :
    prefixProductEnvelopeApp A (n + 1) ≫
        Pi.π (prefixProductFamily A (n + 1)) (Fin.castSucc i) =
      A.transitionMap (Nat.le_of_lt_succ (Nat.lt_succ_of_lt i.2)) := by
  -- The retained coordinates of the prefix tuple are defined by the obvious transition maps.
  rw [prefixProductEnvelopeApp, Pi.lift_π]
  simp [SequentialInverseSystem.transitionMap]

/-- Helper for Lemma 15.87.1: a finite prefix splits as the previous prefix together with the
last coordinate. This is the first structural step toward the source proof's triangular
decomposition of the boundary map. -/
private noncomputable def prefixProduct_previous_last_iso (A : AbSeq) (n : ℕ) :
    prefixProductObject A (n + 1) ≅ prefixProductObject A n ⨯ A.obj (op (n + 1)) := by
  refine
    ⟨Limits.prod.lift (prefixProductDrop A n)
        (Pi.π (prefixProductFamily A (n + 1)) (Fin.last (n + 1))),
      Pi.lift <| Fin.lastCases Limits.prod.snd fun i : Fin (n + 1) ↦
        Limits.prod.fst ≫ Pi.π (prefixProductFamily A n) i,
      ?_,
      ?_⟩
  · -- Proof comment: the reconstruction map remembers exactly the old coordinates and the last
    -- coordinate, so after projecting to the binary product we recover the original pair.
    apply Limits.prod.hom_ext
    · apply Pi.hom_ext
      intro i
      rw [Category.assoc, Pi.lift_π]
      simp only [Fin.lastCases_castSucc]
    · rw [Category.assoc, Pi.lift_π]
      simp only [Fin.lastCases_last]
  · -- Proof comment: projecting the split pair back to each coordinate of the full prefix gives
    -- either the retained old coordinate or the last coordinate itself.
    apply Pi.hom_ext
    intro i
    refine Fin.lastCases ?_ ?_ i
    · rw [Category.assoc, Limits.prod.lift_snd]
      rw [Pi.lift_π]
      simp only [Fin.lastCases_last]
    · intro j
      rw [Category.assoc, Limits.prod.lift_fst]
      rw [Category.assoc, Pi.lift_π]
      simp only [Fin.lastCases_castSucc]

/-- Helper for Lemma 15.87.1: the successor map in the prefix-product tower is definitionally the
concrete coordinate-forgetting map. -/
private theorem prefixProductSystem_map_succ (A : AbSeq) (n : ℕ) :
    (prefixProductSystem A).map (homOfLE (Nat.le_succ n)).op = prefixProductDrop A n := by
  -- Expose the `Functor.ofOpSequence` successor map once so later proofs can rewrite through it.
  simpa [prefixProductSystem, Functor.ofOpSequence_map_homOfLE_succ]

/-- Helper for Lemma 15.87.1: after one successor step in the prefix-product tower, projecting to
an old coordinate is the same as projecting to the corresponding retained coordinate. -/
private theorem prefixProductSystem_stepMap_comp_projection
    (A : AbSeq) (n : ℕ) (i : Fin (n + 1)) :
    ((prefixProductSystem A).map (homOfLE (Nat.le_succ n)).op) ≫
        Pi.π (prefixProductFamily A n) i =
      Pi.π (prefixProductFamily A (n + 1)) (Fin.castSucc i) := by
  -- Rewrite the abstract successor map to the explicit drop map and read off the projection.
  rw [prefixProductSystem_map_succ]
  rw [prefixProductDrop]
  simpa using
    (Pi.lift_π
      (fun j : Fin (n + 1) ↦
        Pi.π (prefixProductFamily A (n + 1)) (Fin.castSucc j))
      i)

/-- Helper for Lemma 15.87.1: the shorter finite prefix family `(A_0, \dots, A_{n-1})`. -/
private abbrev prefixTruncatedFamily (A : AbSeq) (n : ℕ) : Fin n → Ab :=
  fun i ↦ A.obj (op i.1)

/-- Helper for Lemma 15.87.1: the product of the first `n` stages of `A`. -/
private abbrev prefixTruncatedObject (A : AbSeq) (n : ℕ) : Ab :=
  ∏ᶜ prefixTruncatedFamily A n

/-- Helper for Lemma 15.87.1: the shorter-prefix tower also drops the last coordinate. -/
private abbrev prefixTruncatedDrop (A : AbSeq) (n : ℕ) :
    prefixTruncatedObject A (n + 1) ⟶ prefixTruncatedObject A n :=
  Pi.lift fun i : Fin n ↦
    Pi.π (prefixTruncatedFamily A (n + 1)) (Fin.castSucc i)

/-- Helper for Lemma 15.87.1: the target tower for the prefix boundary map remembers only the
strictly shorter prefixes. -/
private abbrev prefixTruncatedSystem (A : AbSeq) : AbSeq :=
  @Functor.ofOpSequence Ab _
    (fun n ↦ prefixTruncatedObject A n)
    (fun n ↦ prefixTruncatedDrop A n)

/-- Helper for Lemma 15.87.1: the successor map in the shorter-prefix tower is the concrete
coordinate-forgetting map. -/
private theorem prefixTruncatedSystem_map_succ (A : AbSeq) (n : ℕ) :
    (prefixTruncatedSystem A).map (homOfLE (Nat.le_succ n)).op = prefixTruncatedDrop A n := by
  -- As for the full prefix tower, expose the `Functor.ofOpSequence` map once for later rewrites.
  simpa [prefixTruncatedSystem, Functor.ofOpSequence_map_homOfLE_succ]

/-- Helper for Lemma 15.87.1: after one successor step in the shorter-prefix tower, projecting to
an old coordinate is the same as projecting to the retained coordinate. -/
private theorem prefixTruncatedSystem_stepMap_comp_projection
    (A : AbSeq) (n : ℕ) (i : Fin n) :
    ((prefixTruncatedSystem A).map (homOfLE (Nat.le_succ n)).op) ≫
        Pi.π (prefixTruncatedFamily A n) i =
      Pi.π (prefixTruncatedFamily A (n + 1)) (Fin.castSucc i) := by
  -- Rewrite the abstract successor map to the explicit shorter-prefix drop map.
  rw [prefixTruncatedSystem_map_succ]
  rw [prefixTruncatedDrop]
  simpa using
    (Pi.lift_π
      (fun j : Fin n ↦
        Pi.π (prefixTruncatedFamily A (n + 1)) (Fin.castSucc j))
      i)

/-- Helper for Lemma 15.87.1: the stagewise boundary on finite prefixes records the consecutive
differences `x_i - f_{i+1}(x_{i+1})`, landing in the shorter prefix product. -/
private abbrev prefixProductBoundaryApp (A : AbSeq) (n : ℕ) :
    prefixProductObject A n ⟶ prefixTruncatedObject A n :=
  Pi.lift fun i : Fin n ↦
    (show prefixProductObject A n ⟶ A.obj (op i.1) from
      Pi.π (prefixProductFamily A n) (Fin.castSucc i)) -
      Pi.π (prefixProductFamily A n) (Fin.succ i) ≫
        A.map (homOfLE (Nat.le_succ i.1)).op

/-- Helper for Lemma 15.87.1: each boundary projection is the expected consecutive difference. -/
private theorem prefixProductBoundaryApp_comp_π
    (A : AbSeq) (n : ℕ) (i : Fin n) :
    prefixProductBoundaryApp A n ≫ Pi.π (prefixTruncatedFamily A n) i =
      (show prefixProductObject A n ⟶ A.obj (op i.1) from
        Pi.π (prefixProductFamily A n) (Fin.castSucc i)) -
        Pi.π (prefixProductFamily A n) (Fin.succ i) ≫
          A.map (homOfLE (Nat.le_succ i.1)).op := by
  -- Each projection simply reads off the corresponding boundary component.
  rw [prefixProductBoundaryApp, Pi.lift_π]

/-- Helper for Lemma 15.87.1: the finite-prefix boundary maps are natural in `n` once the target
is corrected to the shorter-prefix tower. -/
private theorem prefixProductBoundary_naturality (A : AbSeq) (n : ℕ) :
    (prefixProductSystem A).map (homOfLE (Nat.le_succ n)).op ≫ prefixProductBoundaryApp A n =
      prefixProductBoundaryApp A (n + 1) ≫
        (prefixTruncatedSystem A).map (homOfLE (Nat.le_succ n)).op := by
  -- Compare both maps after every shorter-prefix projection.
  apply Pi.hom_ext
  intro i
  calc
    ((prefixProductSystem A).map (homOfLE (Nat.le_succ n)).op ≫
        prefixProductBoundaryApp A n) ≫
          Pi.π (prefixTruncatedFamily A n) i =
      ((prefixProductSystem A).map (homOfLE (Nat.le_succ n)).op ≫
          Pi.π (prefixProductFamily A n) (Fin.castSucc i)) -
        ((prefixProductSystem A).map (homOfLE (Nat.le_succ n)).op ≫
          Pi.π (prefixProductFamily A n) (Fin.succ i)) ≫
            A.map (homOfLE (Nat.le_succ i.1)).op := by
          -- Expand the projected boundary component and distribute composition over subtraction.
          rw [Category.assoc, prefixProductBoundaryApp_comp_π, Preadditive.comp_sub]
          simp [Category.assoc]
    _ =
      Pi.π (prefixProductFamily A (n + 1)) (Fin.castSucc (Fin.castSucc i)) -
        Pi.π (prefixProductFamily A (n + 1)) (Fin.castSucc (Fin.succ i)) ≫
          A.map (homOfLE (Nat.le_succ i.1)).op := by
          -- The source successor map simply forgets the last coordinate.
          rw [prefixProductSystem_stepMap_comp_projection A n (Fin.castSucc i)]
          rw [prefixProductSystem_stepMap_comp_projection A n (Fin.succ i)]
    _ =
      Pi.π (prefixProductFamily A (n + 1)) (Fin.castSucc (Fin.castSucc i)) -
        Pi.π (prefixProductFamily A (n + 1)) (Fin.succ (Fin.castSucc i)) ≫
          A.map (homOfLE (Nat.le_succ i.1)).op := by
          -- Normalize the two ways of shifting a retained coordinate once.
          simp [Fin.succ_castSucc]
    _ =
      prefixProductBoundaryApp A (n + 1) ≫
        (prefixTruncatedSystem A).map (homOfLE (Nat.le_succ n)).op ≫
          Pi.π (prefixTruncatedFamily A n) i := by
          -- Read the right-hand side through the truncated successor map and the explicit
          -- boundary formula at the retained coordinate `i.castSucc`.
          rw [Category.assoc, prefixTruncatedSystem_stepMap_comp_projection A n i]
          rw [← Category.assoc, prefixProductBoundaryApp_comp_π A (n + 1) (Fin.castSucc i)]
          simp [Fin.succ_castSucc, Category.assoc]

/-- Helper for Lemma 15.87.1: the corrected boundary map from full finite prefixes to shorter
finite prefixes. -/
private abbrev prefixProductBoundary (A : AbSeq) :
    prefixProductSystem A ⟶ prefixTruncatedSystem A :=
  NatTrans.ofOpSequence
    (fun n ↦ prefixProductBoundaryApp A n)
    (prefixProductBoundary_naturality A)

/-- Helper for Lemma 15.87.1: stagewise, the canonical prefix tuple is killed by the corrected
finite-prefix boundary map. -/
private theorem prefixProductEnvelopeApp_comp_boundaryApp (A : AbSeq) (n : ℕ) :
    prefixProductEnvelopeApp A n ≫ prefixProductBoundaryApp A n = 0 := by
  -- Compare both sides after every shorter-prefix projection.
  apply Pi.hom_ext
  intro i
  rw [zero_comp]
  have hleft :
      prefixProductEnvelopeApp A n ≫
          Pi.π (prefixProductFamily A n) (Fin.castSucc i) =
        A.transitionMap (Nat.le_of_lt_succ i.2) := by
    -- The `castSucc` coordinate of the envelope is the direct transition to stage `i`.
    rw [prefixProductEnvelopeApp, Pi.lift_π]
    simp [SequentialInverseSystem.transitionMap]
  have hright :
      prefixProductEnvelopeApp A n ≫
          Pi.π (prefixProductFamily A n) (Fin.succ i) ≫
            A.map (homOfLE (Nat.le_succ i.1)).op =
        A.transitionMap (Nat.le_of_lt_succ i.2) := by
    -- The successor coordinate followed by the transition `A_{i+1} ⟶ A_i` is the same direct
    -- transition from stage `n` to stage `i`.
    rw [Category.assoc, prefixProductEnvelopeApp, Pi.lift_π]
    have hh :
        (homOfLE (Nat.le_of_lt_succ (Nat.lt_succ_of_lt i.2))).op ≫
            (homOfLE (Nat.le_succ i.1)).op =
          (homOfLE (Nat.le_of_lt_succ i.2)).op := by
      subsingleton
    simpa [SequentialInverseSystem.transitionMap, Category.assoc] using congrArg A.map hh
  -- After identifying the two summands, the boundary component is `a - a`.
  rw [Category.assoc, prefixProductBoundaryApp_comp_π, Preadditive.comp_sub]
  rw [hleft, hright, sub_self]

/-- Helper for Lemma 15.87.1: the canonical prefix maps are natural in `n`. -/
private theorem prefixProductEnvelope_naturality (A : AbSeq) (n : ℕ) :
    A.map (homOfLE (Nat.le_succ n)).op ≫ prefixProductEnvelopeApp A n =
      prefixProductEnvelopeApp A (n + 1) ≫ (prefixProductSystem A).map (homOfLE (Nat.le_succ n)).op := by
  -- Compare both sides after every projection of the shorter prefix product.
  apply Pi.hom_ext
  intro i
  have hh :
      (homOfLE (Nat.le_succ n)).op ≫ (homOfLE (Nat.le_of_lt_succ i.2)).op =
        (homOfLE (Nat.le_of_lt_succ (Nat.lt_succ_of_lt i.2))).op := by
    subsingleton
  -- Both projected composites equal the direct transition map `A_{n + 1} ⟶ A_i`.
  have hleft :
      A.map (homOfLE (Nat.le_succ n)).op ≫
          prefixProductEnvelopeApp A n ≫
            Pi.π (prefixProductFamily A n) i =
        A.transitionMap (Nat.le_of_lt_succ (Nat.lt_succ_of_lt i.2)) := by
    -- The left projection is the composite of two transition maps in `ℕᵒᵖ`.
    rw [prefixProductEnvelopeApp, Pi.lift_π]
    simpa [SequentialInverseSystem.transitionMap, Category.assoc] using
      congrArg A.map hh
  have hright₁ :
      A.transitionMap (Nat.le_of_lt_succ (Nat.lt_succ_of_lt i.2)) =
        prefixProductEnvelopeApp A (n + 1) ≫
          Pi.π (prefixProductFamily A (n + 1)) (Fin.castSucc i) := by
    -- The projected envelope at stage `n + 1` is the same direct transition map.
    exact (prefixProductEnvelopeApp_comp_castSucc A n i).symm
  have hright₂ :
      prefixProductEnvelopeApp A (n + 1) ≫
          Pi.π (prefixProductFamily A (n + 1)) (Fin.castSucc i) =
        (prefixProductEnvelopeApp A (n + 1) ≫
          (prefixProductSystem A).map (homOfLE (Nat.le_succ n)).op) ≫
            Pi.π (prefixProductFamily A n) i := by
    -- Transport the concrete projection identity through postcomposition by the envelope.
    simpa [Category.assoc] using
      congrArg (fun t ↦ prefixProductEnvelopeApp A (n + 1) ≫ t)
        (prefixProductSystem_stepMap_comp_projection A n i).symm
  simpa [Category.assoc] using hleft.trans (hright₁.trans hright₂)

/-- Helper for Lemma 15.87.1: the canonical monomorphism from `A` into its finite-prefix tower. -/
private abbrev prefixProductEnvelope (A : AbSeq) :
    A ⟶ prefixProductSystem A :=
  NatTrans.ofOpSequence
    (fun n ↦ prefixProductEnvelopeApp A n)
    (prefixProductEnvelope_naturality A)

/-- Helper for Lemma 15.87.1: the canonical prefix envelope lands in the kernel of the corrected
finite-prefix boundary map. -/
private theorem prefixProductEnvelope_comp_boundary (A : AbSeq) :
    prefixProductEnvelope A ≫ prefixProductBoundary A = 0 := by
  -- Upgrade the stagewise telescoping identity to a natural-transformation identity.
  ext n x
  exact congrArg (fun f : A.obj (Opposite.op (Opposite.unop n)) ⟶ prefixTruncatedObject A (Opposite.unop n) ↦
      f.hom x) (prefixProductEnvelopeApp_comp_boundaryApp A (Opposite.unop n))

/-- Helper for Lemma 15.87.1: the canonical prefix map is monic stagewise, hence monic as a
morphism of inverse systems. -/
private theorem prefixProductEnvelope_mono (A : AbSeq) :
    Mono (prefixProductEnvelope A) := by
  -- A natural transformation in a functor category is monic exactly when it is monic objectwise.
  rw [NatTrans.mono_iff_mono_app]
  intro n
  simpa [prefixProductEnvelope] using
    (inferInstance : Mono (prefixProductEnvelopeApp A (Opposite.unop n)))

/-- Helper for Lemma 15.87.1: Mittag-Leffler towers are closed under quotients in short exact
sequences of sequential inverse systems of abelian groups. -/
private instance isMittagLeffler_isClosedUnderQuotients :
    ObjectProperty.IsClosedUnderQuotients
      (fun A : AbSeq ↦ SequentialInverseSystem.IsMittagLeffler A) := by
  refine { prop_of_epi := ?_ }
  intro X Y f _ hX
  let S : ShortComplex AbSeq := ShortComplex.mk (kernel.ι f) f (by simp)
  have hS_exact_mono : S.Exact ∧ Mono S.f := by
    exact (S.exact_and_mono_f_iff_f_is_kernel).2 ⟨kernelIsKernel f⟩
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' hS_exact_mono.1 hS_exact_mono.2 inferInstance
  -- Realize an epimorphism as the quotient term of its kernel short exact sequence.
  simpa [S] using
    SequentialInverseSystem.isMittagLeffler_right_of_shortExact (S := S) hS hX

/-- Helper for Lemma 15.87.1: the prefix-product envelope route should first prove bounded-below
right acyclicity for a Mittag-Leffler inverse system, before passing to the unbounded degree-zero
complex. -/
private theorem boundedBelowRightAcyclic_of_isMittagLeffler
    (A : AbSeq) (hA : SequentialInverseSystem.IsMittagLeffler A) :
    IsBoundedBelowRightAcyclicForAdditiveFunctor (lim : AbSeq ⥤ Ab) A := by
  -- Route correction: now that the finite-prefix envelope package is available, apply the
  -- Chapter `13` bounded-below acyclicity owner to the Mittag-Leffler object property.
  letI : HasMonoEmbedding (fun X : AbSeq ↦ SequentialInverseSystem.IsMittagLeffler X) :=
    { exists_mono := fun X ↦ by
        -- Package the finite-prefix envelope directly at the owner call site.
        exact ⟨prefixProductSystem X, prefixProductSystem_isMittagLeffler X,
          prefixProductEnvelope X, prefixProductEnvelope_mono X⟩ }
  exact
    isBoundedBelowRightAcyclicForAdditiveFunctor_of_mem
      (F := (lim : AbSeq ⥤ Ab))
      (P := fun X : AbSeq ↦ SequentialInverseSystem.IsMittagLeffler X)
      (fun {S} hS h₁ _ ↦
        SequentialInverseSystem.inverseLimit_shortExact_of_isMittagLeffler_left S hS h₁)
      A hA

/-- Helper for Lemma 15.87.1: the `n`th stage of the stagewise derived tower of the degree-zero
inverse system `A[0]` is canonically the degree-zero derived object `A_n[0]`. -/
private noncomputable def stagewise_single_tower_component_iso
    (A : AbSeq) (n : ℕ) :
    (CategoryTheory.stagewiseDerivedInverseLimitTower
        (A := Ab) ((DerivedCategory.singleFunctor AbSeq 0).obj A)).obj (op n) ≅
      (A ⋙ DerivedCategory.singleFunctor Ab 0).obj (op n) :=
  -- First evaluate the degree-zero single complex stagewise, then rewrite the strict single
  -- complex back to the canonical degree-zero object in the derived category of abelian groups.
  (((evaluation ℕᵒᵖ Ab).obj (op n)).mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor AbSeq (0 : ℤ)).obj A)) ≪≫
    DerivedCategory.Q.mapIso
      (((HomologicalComplex.singleMapHomologicalComplex
          (((evaluation ℕᵒᵖ Ab).obj (op n)) : AbSeq ⥤ Ab)
          (ComplexShape.up ℤ) 0).app A)) ≪≫
    (DerivedCategory.singleFunctorIsoCompQ Ab (0 : ℤ)).app
      (A.obj (op n))

/-- Helper for Lemma 15.87.1: evaluating the degree-zero single complex of an inverse system at
two consecutive stages commutes strictly with the canonical single-complex transport. -/
private theorem single_stage_transition_comm
    (A : AbSeq) (n : ℕ) :
    let τ :
        (((evaluation ℕᵒᵖ Ab).obj (op (n + 1))).mapHomologicalComplex
          (ComplexShape.up ℤ)) ⟶
          (((evaluation ℕᵒᵖ Ab).obj (op n)).mapHomologicalComplex
            (ComplexShape.up ℤ)) :=
      NatTrans.mapHomologicalComplex
        ((evaluation ℕᵒᵖ Ab).map ((homOfLE (Nat.le_succ n)).op))
        (ComplexShape.up ℤ)
    τ.app ((CochainComplex.singleFunctor AbSeq (0 : ℤ)).obj A) ≫
        (((HomologicalComplex.singleMapHomologicalComplex
          (((evaluation ℕᵒᵖ Ab).obj (op n)) : AbSeq ⥤ Ab)
          (ComplexShape.up ℤ) 0).app A).hom) =
      (((HomologicalComplex.singleMapHomologicalComplex
          (((evaluation ℕᵒᵖ Ab).obj (op (n + 1))) : AbSeq ⥤ Ab)
          (ComplexShape.up ℤ) 0).app A).hom) ≫
        ((CochainComplex.singleFunctor Ab (0 : ℤ)).map
          (A.map ((homOfLE (Nat.le_succ n)).op))) := by
  let τ :
      (((evaluation ℕᵒᵖ Ab).obj (op (n + 1))).mapHomologicalComplex
        (ComplexShape.up ℤ)) ⟶
        (((evaluation ℕᵒᵖ Ab).obj (op n)).mapHomologicalComplex
          (ComplexShape.up ℤ)) :=
    NatTrans.mapHomologicalComplex
      ((evaluation ℕᵒᵖ Ab).map ((homOfLE (Nat.le_succ n)).op))
      (ComplexShape.up ℤ)
  -- Proof comment: both sides are morphisms between degree-zero single complexes, so it is enough
  -- to compare their components in each cochain degree.
  ext i x
  by_cases hi : i = 0
  · subst i
    simp [τ]
  · simp [τ, hi]

/-- Helper for Lemma 15.87.1: the componentwise stagewise comparisons respect the successor maps
of the actual stagewise derived tower and the degree-zero tower `A ⋙ singleFunctor Ab 0`. -/
private theorem stagewise_single_tower_component_naturality
    (A : AbSeq) (n : ℕ) :
    (CategoryTheory.stagewiseDerivedInverseLimitTower
        (A := Ab) ((DerivedCategory.singleFunctor AbSeq 0).obj A)).stepMap n ≫
      (stagewise_single_tower_component_iso A n).hom =
        (stagewise_single_tower_component_iso A (n + 1)).hom ≫
          (A ⋙ DerivedCategory.singleFunctor Ab 0).map ((homOfLE (Nat.le_succ n)).op) := by
  let X := ((CochainComplex.singleFunctor AbSeq (0 : ℤ)).obj A)
  let a : ∀ m : ℕ,
      (((evaluation ℕᵒᵖ Ab).obj (op m)).mapDerivedCategory).obj
          (DerivedCategory.Q.obj X) ≅
        DerivedCategory.Q.obj
          ((((evaluation ℕᵒᵖ Ab).obj (op m)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj X) :=
    fun m ↦
      ((evaluation ℕᵒᵖ Ab).obj (op m)).mapDerivedCategoryFactors.app X
  let τ :
      (((evaluation ℕᵒᵖ Ab).obj (op (n + 1))).mapHomologicalComplex
        (ComplexShape.up ℤ)) ⟶
        (((evaluation ℕᵒᵖ Ab).obj (op n)).mapHomologicalComplex
          (ComplexShape.up ℤ)) :=
    NatTrans.mapHomologicalComplex
      ((evaluation ℕᵒᵖ Ab).map ((homOfLE (Nat.le_succ n)).op))
      (ComplexShape.up ℤ)
  let δ :
      (((evaluation ℕᵒᵖ Ab).obj (op (n + 1))).mapDerivedCategory : DAbSeq ⥤ DAb) ⟶
        (((evaluation ℕᵒᵖ Ab).obj (op n)).mapDerivedCategory : DAbSeq ⥤ DAb) :=
    Functor.rightDerivedNatTrans
      (((evaluation ℕᵒᵖ Ab).obj (op (n + 1))).mapDerivedCategory)
      (((evaluation ℕᵒᵖ Ab).obj (op n)).mapDerivedCategory)
      (((evaluation ℕᵒᵖ Ab).obj (op (n + 1))).mapDerivedCategoryFactors.inv)
      (((evaluation ℕᵒᵖ Ab).obj (op n)).mapDerivedCategoryFactors.inv)
      (HomologicalComplex.quasiIso AbSeq (ComplexShape.up ℤ))
      (Functor.whiskerRight τ DerivedCategory.Q)
  let s :
      ∀ m : ℕ,
        ((((evaluation ℕᵒᵖ Ab).obj (op m)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj X) ≅
          ((CochainComplex.singleFunctor Ab (0 : ℤ)).obj
            (A.obj (op m))) :=
    fun m ↦
      ((HomologicalComplex.singleMapHomologicalComplex
        (((evaluation ℕᵒᵖ Ab).obj (op m)) : AbSeq ⥤ Ab)
        (ComplexShape.up ℤ) 0).app A)
  let b : ∀ m : ℕ,
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor Ab (0 : ℤ)).obj
        (A.obj (op m))) ≅
        (A ⋙ DerivedCategory.singleFunctor Ab 0).obj (op m) :=
    fun m ↦ (DerivedCategory.singleFunctorIsoCompQ Ab (0 : ℤ)).app
      (A.obj (op m))
  have hstep :=
    Functor.rightDerivedNatTrans_app
      (((evaluation ℕᵒᵖ Ab).obj (op (n + 1))).mapDerivedCategory)
      (((evaluation ℕᵒᵖ Ab).obj (op n)).mapDerivedCategory)
      (((evaluation ℕᵒᵖ Ab).obj (op (n + 1))).mapDerivedCategoryFactors.inv)
      (((evaluation ℕᵒᵖ Ab).obj (op n)).mapDerivedCategoryFactors.inv)
      (HomologicalComplex.quasiIso AbSeq (ComplexShape.up ℤ))
      (Functor.whiskerRight τ DerivedCategory.Q)
      X
  have hstep_inv :
      δ.app (DerivedCategory.Q.obj X) ≫ (a n).hom =
        (a (n + 1)).hom ≫ DerivedCategory.Q.map (τ.app X) := by
    -- Proof comment: postcompose the defining right-derived comparison and cancel the inverse
    -- `mapDerivedCategoryFactors` comparison on the left.
    have hstep_post_raw :
        ((a (n + 1)).inv ≫ δ.app (DerivedCategory.Q.obj X)) ≫ (a n).hom =
          (DerivedCategory.Q.map (τ.app X) ≫ (a n).inv) ≫ (a n).hom := by
      simpa [a, δ, X, Category.assoc] using
        congrArg (fun k ↦ k ≫ (a n).hom) hstep
    have hstep_post :
        (a (n + 1)).inv ≫ (δ.app (DerivedCategory.Q.obj X) ≫ (a n).hom) =
          DerivedCategory.Q.map (τ.app X) := by
      calc
        (a (n + 1)).inv ≫ (δ.app (DerivedCategory.Q.obj X) ≫ (a n).hom) =
            ((a (n + 1)).inv ≫ δ.app (DerivedCategory.Q.obj X)) ≫ (a n).hom := by
              simp [Category.assoc]
        _ = (DerivedCategory.Q.map (τ.app X) ≫ (a n).inv) ≫ (a n).hom := hstep_post_raw
        _ = DerivedCategory.Q.map (τ.app X) := by
              simp [Category.assoc]
    apply (cancel_epi (a (n + 1)).inv).1
    calc
      (a (n + 1)).inv ≫ (δ.app (DerivedCategory.Q.obj X) ≫ (a n).hom) =
          DerivedCategory.Q.map (τ.app X) := hstep_post
      _ =
          (a (n + 1)).inv ≫ ((a (n + 1)).hom ≫ DerivedCategory.Q.map (τ.app X)) := by
            simp
  have hτ :
      DerivedCategory.Q.map (τ.app X) ≫ DerivedCategory.Q.map (s n).hom =
        DerivedCategory.Q.map (s (n + 1)).hom ≫
          DerivedCategory.Q.map
            ((CochainComplex.singleFunctor Ab (0 : ℤ)).map
              (A.map ((homOfLE (Nat.le_succ n)).op))) := by
    -- Proof comment: this is the strict chain-level stage-transition square, now lifted by `Q`.
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg DerivedCategory.Q.map (single_stage_transition_comm A n)
  have hsingle :
      DerivedCategory.Q.map
          ((CochainComplex.singleFunctor Ab (0 : ℤ)).map
            (A.map ((homOfLE (Nat.le_succ n)).op))) ≫
        (b n).hom =
      (b (n + 1)).hom ≫ (A ⋙ DerivedCategory.singleFunctor Ab 0).map
        ((homOfLE (Nat.le_succ n)).op) := by
    -- Proof comment: naturality of `singleFunctorIsoCompQ` identifies the residual `Q`-image
    -- of the strict degree-zero map with the derived stage transition.
    simpa [Functor.comp_map] using
      ((DerivedCategory.singleFunctorIsoCompQ Ab (0 : ℤ)).hom.naturality
        (A.map ((homOfLE (Nat.le_succ n)).op)))
  have hcomponent :
      δ.app (DerivedCategory.Q.obj X) ≫ (a n).hom ≫ DerivedCategory.Q.map (s n).hom ≫
          (b n).hom =
        (a (n + 1)).hom ≫ DerivedCategory.Q.map (s (n + 1)).hom ≫
          (b (n + 1)).hom ≫ (A ⋙ DerivedCategory.singleFunctor Ab 0).map
            ((homOfLE (Nat.le_succ n)).op) := by
    -- Proof comment: combine the derived evaluation comparison, the strict single-complex square,
    -- and the naturality of `singleFunctorIsoCompQ`.
    calc
      δ.app (DerivedCategory.Q.obj X) ≫ (a n).hom ≫ DerivedCategory.Q.map (s n).hom ≫
          (b n).hom =
          ((a (n + 1)).hom ≫ DerivedCategory.Q.map (τ.app X)) ≫
            DerivedCategory.Q.map (s n).hom ≫ (b n).hom := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ DerivedCategory.Q.map (s n).hom ≫ (b n).hom) hstep_inv
      _ =
          (a (n + 1)).hom ≫ DerivedCategory.Q.map (s (n + 1)).hom ≫
            DerivedCategory.Q.map
              ((CochainComplex.singleFunctor Ab (0 : ℤ)).map
                (A.map ((homOfLE (Nat.le_succ n)).op))) ≫
              (b n).hom := by
                simpa [Category.assoc] using
                  congrArg (fun k ↦ (a (n + 1)).hom ≫ k ≫ (b n).hom) hτ
      _ =
          (a (n + 1)).hom ≫ DerivedCategory.Q.map (s (n + 1)).hom ≫
            ((b (n + 1)).hom ≫ (A ⋙ DerivedCategory.singleFunctor Ab 0).map
              ((homOfLE (Nat.le_succ n)).op)) := by
                simpa [Category.assoc] using
                  congrArg
                    (fun k ↦ (a (n + 1)).hom ≫ DerivedCategory.Q.map (s (n + 1)).hom ≫ k)
                    hsingle
      _ =
          (a (n + 1)).hom ≫ DerivedCategory.Q.map (s (n + 1)).hom ≫
            (b (n + 1)).hom ≫ (A ⋙ DerivedCategory.singleFunctor Ab 0).map
              ((homOfLE (Nat.le_succ n)).op) := by
              simp [Category.assoc]
  simpa [SequentialInverseSystem.stepMap, CategoryTheory.stagewiseDerivedInverseLimitTower,
    stagewise_single_tower_component_iso, X, a, τ, δ, s, b, Category.assoc] using
    hcomponent

/-- Helper for Lemma 15.87.1: the stagewise comparison components assemble into a morphism from
the actual stagewise derived tower of `A[0]` to the degree-zero tower `A ⋙ singleFunctor Ab 0`. -/
private noncomputable def stagewise_single_tower_hom
    (A : AbSeq) :
    CategoryTheory.stagewiseDerivedInverseLimitTower
        (A := Ab) ((DerivedCategory.singleFunctor AbSeq 0).obj A) ⟶
      A ⋙ DerivedCategory.singleFunctor Ab 0 :=
  NatTrans.ofOpSequence
    (fun n ↦ (stagewise_single_tower_component_iso A n).hom)
    (stagewise_single_tower_component_naturality A)

/-- Helper for Lemma 15.87.1: the stagewise derived tower of the degree-zero object `A[0]` is
canonically isomorphic to the degree-zero tower `n ↦ A_n[0]`. -/
private def stagewise_single_tower_iso
    (A : AbSeq) :
    CategoryTheory.stagewiseDerivedInverseLimitTower
        (A := Ab) ((DerivedCategory.singleFunctor AbSeq 0).obj A) ≅
      A ⋙ DerivedCategory.singleFunctor Ab 0 :=
  -- Assemble the stagewise comparisons into an isomorphism of towers.
  NatIso.ofComponents
    (fun n ↦ stagewise_single_tower_component_iso A (Opposite.unop n))
    (fun {_ _} f ↦ by
      simpa using (stagewise_single_tower_hom A).naturality f)

/-- Helper for Lemma 15.87.1: an isomorphism of derived-limit towers induces an isomorphism of the
chosen countable products of their stages. -/
private noncomputable def tower_product_iso
    {Ksys Lsys : SequentialInverseSystem DAb}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) :
    (∏ᶜ inverseSystemFamily Ksys) ≅ ∏ᶜ inverseSystemFamily Lsys := by
  let eFamily :
      Discrete.functor (inverseSystemFamily Ksys) ≅
        Discrete.functor (inverseSystemFamily Lsys) :=
    Discrete.natIso fun n : Discrete ℕ ↦ e.app (op n.as)
  exact HasLimit.isoOfNatIso eFamily

/-- Helper for Lemma 15.87.1: the product isomorphism induced by a tower isomorphism preserves
each stage projection. -/
private theorem tower_product_iso_hom_comp_π
    {Ksys Lsys : SequentialInverseSystem DAb}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) (n : ℕ) :
    (tower_product_iso e).hom ≫ Pi.π (inverseSystemFamily Lsys) n =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (op n)).hom := by
  let eFamily :
      Discrete.functor (inverseSystemFamily Ksys) ≅
        Discrete.functor (inverseSystemFamily Lsys) :=
    Discrete.natIso fun m : Discrete ℕ ↦ e.app (op m.as)
  simpa [tower_product_iso, eFamily] using
    limMap_π (α := eFamily.hom) (j := Discrete.mk n)

/-- Helper for Lemma 15.87.1: the product isomorphism induced by a tower isomorphism intertwines
the Milnor difference maps. -/
private theorem tower_product_iso_hom_comm_difference
    {Ksys Lsys : SequentialInverseSystem DAb}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) :
    (tower_product_iso e).hom ≫ derivedLimitDifferenceMap Lsys =
      derivedLimitDifferenceMap Ksys ≫ (tower_product_iso e).hom := by
  -- Proof comment: compare the two Milnor endomorphisms after each projection and use tower
  -- naturality to identify the successor-transition term.
  apply Pi.hom_ext
  intro n
  calc
    ((tower_product_iso e).hom ≫ derivedLimitDifferenceMap Lsys) ≫
        Pi.π (inverseSystemFamily Lsys) n =
      (tower_product_iso e).hom ≫
        (Pi.π (inverseSystemFamily Lsys) n -
          Pi.π (inverseSystemFamily Lsys) (n + 1) ≫
            Lsys.transitionMap (Nat.le_succ n)) := by
        rw [Category.assoc, derivedLimitDifferenceMap_comp_π]
    _ =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (op n)).hom -
        (Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          (e.app (op (n + 1))).hom ≫ Lsys.transitionMap (Nat.le_succ n)) := by
        rw [Preadditive.comp_sub]
        rw [tower_product_iso_hom_comp_π]
        simpa [Category.assoc] using
          congrArg (fun t ↦ t ≫ Lsys.transitionMap (Nat.le_succ n))
            (tower_product_iso_hom_comp_π e (n + 1))
    _ =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (op n)).hom -
        (Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          Ksys.transitionMap (Nat.le_succ n) ≫ (e.app (op n)).hom) := by
        congr 1
        simpa [Category.assoc] using
          congrArg
            (fun t ↦ Pi.π (inverseSystemFamily Ksys) (n + 1) ≫ t)
            (e.hom.naturality ((homOfLE (Nat.le_succ n)).op)).symm
    _ =
      (Pi.π (inverseSystemFamily Ksys) n -
        Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          Ksys.transitionMap (Nat.le_succ n)) ≫
        (e.app (op n)).hom := by
        rw [Preadditive.sub_comp]
        simp [Category.assoc]
    _ =
      derivedLimitDifferenceMap Ksys ≫ Pi.π (inverseSystemFamily Ksys) n ≫
        (e.app (op n)).hom := by
        rw [← derivedLimitDifferenceMap_comp_π_assoc]
    _ =
      ((derivedLimitDifferenceMap Ksys ≫ (tower_product_iso e).hom) ≫
        Pi.π (inverseSystemFamily Lsys) n) := by
        rw [Category.assoc, ← tower_product_iso_hom_comp_π, ← Category.assoc]

/-- Helper for Lemma 15.87.1: a derived-limit witness transports across an isomorphism of towers
when the limiting object is kept fixed. -/
private theorem isDerivedLimit_of_tower_iso
    {Ksys Lsys : SequentialInverseSystem DAb} {K : DAb}
    (e : Ksys ≅ Lsys)
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit Lsys K := by
  rcases hK with ⟨hP, ι, δ, hδ⟩
  letI : HasProduct (inverseSystemFamily Ksys) := hP
  let eFamily :
      Discrete.functor (inverseSystemFamily Ksys) ≅
        Discrete.functor (inverseSystemFamily Lsys) :=
    Discrete.natIso fun n : Discrete ℕ ↦ e.app (op n.as)
  let hQ : HasProduct (inverseSystemFamily Lsys) := by
    exact hasLimit_of_iso eFamily
  letI : HasProduct (inverseSystemFamily Lsys) := hQ
  let p : (∏ᶜ inverseSystemFamily Ksys) ≅ ∏ᶜ inverseSystemFamily Lsys :=
    tower_product_iso e
  let T : Triangle DAb :=
    Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ
  let T' : Triangle DAb :=
    Triangle.mk (ι ≫ p.hom) (derivedLimitDifferenceMap Lsys) (p.inv ≫ δ)
  have hIso : T ≅ T' := by
    -- Proof comment: repackage the original Milnor triangle through the product comparison
    -- isomorphism induced by the tower isomorphism.
    refine Triangle.isoMk _ _ (Iso.refl _) p p ?_ ?_ ?_
    · simp [T, T']
    · simpa [T, T'] using (tower_product_iso_hom_comm_difference e).symm
    · simp [T, T']
  have hT' : T' ∈ distTriang DAb := by
    exact isomorphic_distinguished _ hδ _ hIso.symm
  exact ⟨hQ, ι ≫ p.hom, p.inv ≫ δ, hT'⟩

/-- Helper for Lemma 15.87.1: the countable product of the degree-zero tower
`n ↦ A_n[0]` is itself concentrated in degree `0`. -/
private theorem product_single_isZero_homology_of_ne
    (A : AbSeq) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor Ab i).obj
      (∏ᶜ inverseSystemFamily (A ⋙ DerivedCategory.singleFunctor Ab 0))) := by
  let hsingle :
      IsZero ((DerivedCategory.homologyFunctor Ab i).obj
        ((DerivedCategory.singleFunctor Ab 0).obj (∏ᶜ fun n ↦ A.obj (op n)))) := by
    -- Proof comment: the homology of a degree-zero single complex vanishes away from degree `0`.
    let K := (HomotopyCategory.quotient Ab (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor Ab 0).obj (∏ᶜ fun n ↦ A.obj (op n)))
    change IsZero ((DerivedCategory.Qh ⋙ DerivedCategory.homologyFunctor Ab i).obj K)
    exact
      (((DerivedCategory.homologyFunctorFactorsh Ab i).app K).isZero_iff).2
        (by
          simpa [K] using
            (HomologicalComplex.isZero_single_obj_homology
              (ComplexShape.up ℤ) (0 : ℤ) (∏ᶜ fun n ↦ A.obj (op n)) i hi))
  let e :
      (DerivedCategory.singleFunctor Ab 0).obj (∏ᶜ fun n ↦ A.obj (op n)) ≅
        ∏ᶜ inverseSystemFamily (A ⋙ DerivedCategory.singleFunctor Ab 0) :=
    asIso (piComparison (DerivedCategory.singleFunctor Ab 0)
      (fun n ↦ A.obj (op n)))
  exact hsingle.of_iso ((DerivedCategory.homologyFunctor Ab i).mapIso e)

/-- Helper for Lemma 15.87.1: in `D(Ab)`, if the first morphism of a distinguished triangle is an
isomorphism on homology above `m` and an epimorphism in degree `m`, then the cone is concentrated
in degrees `≤ m - 1`. -/
private theorem abelianGroup_approximation_cone_isLE_pred
    (T : Triangle DAb) (hT : T ∈ distTriang DAb) (m : ℤ)
    (hαiso : ∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor Ab i).map T.mor₁))
    (hαepi : Epi ((DerivedCategory.homologyFunctor Ab m).map T.mor₁)) :
    T.obj₃.IsLE (m - 1) := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  have him : m ≤ i := by
    omega
  have hmor₁_epi :
      Epi ((DerivedCategory.homologyFunctor Ab i).map T.mor₁) := by
    by_cases him_eq : i = m
    · subst him_eq
      exact hαepi
    · have him_lt : m < i := lt_of_le_of_ne him fun h ↦ him_eq h.symm
      letI : IsIso ((DerivedCategory.homologyFunctor Ab i).map T.mor₁) := hαiso i him_lt
      infer_instance
  have hmor₁_mono :
      Mono ((DerivedCategory.homologyFunctor Ab (i + 1)).map T.mor₁) := by
    letI : IsIso ((DerivedCategory.homologyFunctor Ab (i + 1)).map T.mor₁) :=
      hαiso (i + 1) (by omega)
    infer_instance
  -- Proof comment: exactness first kills the middle homology map once the left one is epi.
  have hmor₂_zero : (DerivedCategory.homologyFunctor Ab i).map T.mor₂ = 0 := by
    exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).1 hmor₁_epi
  -- Proof comment: the next homology isomorphism forces the connecting map to vanish.
  have hδ_zero : DerivedCategory.HomologySequence.δ T i (i + 1) rfl = 0 := by
    exact (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
      T hT i (i + 1) rfl).1 hmor₁_mono
  have hmor₂_epi : Epi ((DerivedCategory.homologyFunctor Ab i).map T.mor₂) := by
    exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff
      T hT i (i + 1) rfl).2 hδ_zero
  -- Proof comment: a zero epimorphism has zero codomain, which is the desired vanishing.
  exact IsZero.of_epi_eq_zero ((DerivedCategory.homologyFunctor Ab i).map T.mor₂) hmor₂_zero

-- Proof sketch: the Stacks Project identifies the degree-zero object `A[0]` in the derived
-- category with the standard Milnor triangle built from the two products `∏ A_n` and the
-- difference map `(x_n) ↦ (x_n - f_{n+1}(x_{n+1}))`.
/-- Applying `R lim` to an inverse system of abelian groups viewed in degree `0` yields the
standard derived-limit object characterized by the Milnor triangle, equivalently by the two-term
complex `\prod A_n \to \prod A_n` in degrees `0` and `1`. -/
theorem abelianGroupDerivedInverseLimit_isDerivedLimit_of_inverseSystem
    (A : AbSeq) :
    CategoryTheory.IsDerivedLimit
      (A ⋙ DerivedCategory.singleFunctor Ab 0)
      (R lim((DerivedCategory.singleFunctor AbSeq 0).obj A)) :=
  by
  let F : DAbSeq ⥤ DAb :=
    CategoryTheory.additiveFunctorTotalRightDerived
      (CategoryTheory.Limits.lim : AbSeq ⥤ Ab)
  change IsDerivedLimit
    (A ⋙ DerivedCategory.singleFunctor Ab 0)
    (F.obj ((DerivedCategory.singleFunctor AbSeq 0).obj A))
  have hBase :
      IsDerivedLimit
        (CategoryTheory.stagewiseDerivedInverseLimitTower
          (A := Ab) ((DerivedCategory.singleFunctor AbSeq 0).obj A))
        (F.obj ((DerivedCategory.singleFunctor AbSeq 0).obj A)) :=
    CategoryTheory.derivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation
      (A := Ab)
      ((DerivedCategory.singleFunctor AbSeq 0).obj A)
  -- Proof comment: the imported stagewise derived-limit theorem already computes `R lim(A[0])`
  -- for the canonical stagewise-evaluation tower, and the local stagewise comparison identifies
  -- that tower with the source-facing degree-zero tower `n ↦ A_n[0]`.
  exact isDerivedLimit_of_tower_iso (stagewise_single_tower_iso A) hBase

-- Proof sketch: this is the Stacks Project vanishing statement `R^p lim = 0` for `p > 1`,
-- expressed as vanishing of the positive cohomology of `R lim(A[0])`.
/-- For an inverse system of abelian groups, the cohomology objects `H^p(R lim(A[0]))` vanish in
degrees strictly greater than `1`. -/
theorem abelianGroupInverseLimit_rightDerived_isZero_of_one_lt
    (A : AbSeq) (p : ℕ) (hp : 1 < p) :
    IsZero (R^p lim((DerivedCategory.singleFunctor AbSeq 0).obj A)) :=
  by
  let K : DAb := R lim((DerivedCategory.singleFunctor AbSeq 0).obj A)
  let H := DerivedCategory.homologyFunctor Ab
  have hK :
      IsDerivedLimit
        (A ⋙ DerivedCategory.singleFunctor Ab 0)
        K :=
    abelianGroupDerivedInverseLimit_isDerivedLimit_of_inverseSystem A
  rcases hK with ⟨hP, ι, δ, hδ⟩
  letI : HasProduct (inverseSystemFamily (A ⋙ DerivedCategory.singleFunctor Ab 0)) := hP
  let T : Triangle DAb :=
    Triangle.mk ι (derivedLimitDifferenceMap (A ⋙ DerivedCategory.singleFunctor Ab 0)) δ
  have hTrot : T.rotate ∈ distTriang DAb := by
    exact Pretriangulated.rot_of_distTriang _ hδ
  have hαiso :
      ∀ i : ℤ, 1 < i → IsIso ((H i).map (T.rotate.mor₁)) := by
    intro i hi
    let hsrc :
        IsZero ((H i).obj (T.rotate.obj₁)) := by
      simpa [T] using product_single_isZero_homology_of_ne A i (by omega)
    let htgt :
        IsZero ((H i).obj (T.rotate.obj₂)) := by
      simpa [T] using product_single_isZero_homology_of_ne A i (by omega)
    exact IsZero.isIso hsrc htgt ((H i).map (T.rotate.mor₁))
  have hαepi : Epi ((H 1).map (T.rotate.mor₁)) := by
    let hsrc :
        IsZero ((H 1).obj (T.rotate.obj₁)) := by
      simpa [T] using product_single_isZero_homology_of_ne A (1 : ℤ) (by omega)
    let htgt :
        IsZero ((H 1).obj (T.rotate.obj₂)) := by
      simpa [T] using product_single_isZero_homology_of_ne A (1 : ℤ) (by omega)
    letI : IsIso ((H 1).map (T.rotate.mor₁)) :=
      IsZero.isIso hsrc htgt ((H 1).map (T.rotate.mor₁))
    infer_instance
  have hshift_le : T.rotate.obj₃.IsLE 0 := by
    -- Proof comment: the rotated Milnor triangle has first map the difference endomorphism
    -- between two degree-zero product objects, so its cone is concentrated in degrees `≤ 0`.
    exact abelianGroup_approximation_cone_isLE_pred T.rotate hTrot 1 hαiso hαepi
  have hshift_zero :
      IsZero ((H ((p : ℤ) - 1)).obj (K⟦(1 : ℤ)⟧)) := by
    -- Proof comment: once `K⟦1⟧` is `IsLE 0`, every positive cohomology group vanishes.
    simpa [T] using
      DerivedCategory.isZero_of_isLE (T.rotate.obj₃) 0 ((p : ℤ) - 1) (by omega)
  let eShift :
      (H ((p : ℤ) - 1)).obj (K⟦(1 : ℤ)⟧) ≅ (H (p : ℤ)).obj K :=
    ((H ((p : ℤ) - 1)).shiftIso (1 : ℤ) ((p : ℤ) - 1) (p : ℤ) (by omega)).app K
  simpa [K] using hshift_zero.of_iso eShift

-- Proof sketch: for a Mittag-Leffler inverse system, the Stacks Project identifies the
-- obstruction group `R^1 lim` with zero; the higher derived functors already vanish above degree
-- `1`, so all positive right-derived functors vanish and the system is right acyclic for `lim`.
/-- A Mittag-Leffler inverse system of abelian groups is right acyclic for inverse limit. -/
theorem abelianGroupLimit_rightAcyclic_of_isMittagLeffler
    (A : AbSeq) (hA : SequentialInverseSystem.IsMittagLeffler A) :
    RightAcyclic A := by
  -- First import the bounded-below acyclicity supplied by the prefix-product envelope route.
  have hbounded :
      IsBoundedBelowRightAcyclicForAdditiveFunctor (lim : AbSeq ⥤ Ab) A :=
    boundedBelowRightAcyclic_of_isMittagLeffler A hA
  -- Then pass from the bounded-below degree-zero complex to the unbounded degree-zero complex.
  change IsRightAcyclicForAdditiveFunctor (lim : AbSeq ⥤ Ab) A
  simpa [IsRightAcyclicForAdditiveFunctor, IsBoundedBelowRightAcyclicForAdditiveFunctor] using
    (computes_right_derived_functor_at_iff_bounded_below
      (F := (lim : AbSeq ⥤ Ab))
      ((single0Plus AbSeq).obj A)).2 hbounded

-- Proof sketch: specialize Lemma 13.32.2 to the inverse-limit functor, using the preceding
-- `HasMonoEmbedding RightAcyclic` instance together with the vanishing of `R^2 lim`.
/-- Every cochain complex of inverse systems of abelian groups is quasi-isomorphic to one whose
terms are right acyclic for inverse limit. -/
theorem exists_quasiIso_to_termwise_abelianGroupLimit_rightAcyclic
    (K : CochainComplex AbSeq ℤ) :
    ∃ (L : CochainComplex AbSeq ℤ) (α : K ⟶ L), QuasiIso α ∧ ∀ i : ℤ, RightAcyclic (L.X i) :=
  by
  -- The Chapter `13` owner theorem already packages the vanishing hypothesis needed to produce
  -- an unbounded right derived functor and a termwise right-acyclic replacement.
  letI : Functor.HasRightDerivedFunctor KtoD Qish :=
    has_unbounded_rightDerivedFunctor_of_mono_into_higherRightDerivedVanishes
      (F := (lim : AbSeq ⥤ Ab))
  -- With the unbounded right derived functor in place, apply the canonical termwise-acyclic
  -- replacement theorem.
  exact
    exists_quasiIso_to_termwise_higherRightDerivedVanishes
      (F := (lim : AbSeq ⥤ Ab)) K

-- Proof sketch: this is Lemma 13.32.2 specialized to the inverse-limit functor. Once each term
-- `K.X i` is right acyclic for `lim`, the ordinary termwise inverse-limit complex computes the
-- chosen derived inverse limit in the canonical Chapter 13 sense
-- `Functor.ComputesRightDerivedAt`.
/-- Lemma 15.87.1: if each degree `K^p = (K_n^p)` of a cochain complex of inverse systems of
abelian groups is right acyclic for inverse limit, then the homotopy-category class of `K`
computes `R lim(K)`, formalized by the canonical Chapter `13` owner
`Functor.ComputesRightDerivedAt` for `mapHomotopyCategoryToDerived`. Equivalently, the canonical
comparison map from the ordinary termwise inverse-limit complex to the chosen derived inverse
limit is an isomorphism, so `R lim(K)` is represented by the complex whose degree-`p` term is
`\varprojlim_n K_n^p`. -/
@[stacks 07KW]
theorem abelianGroupDerivedInverseLimit_computes_of_termwise_rightAcyclic
    (K : CochainComplex AbSeq ℤ) (hK : ∀ i : ℤ, RightAcyclic (K.X i)) :
    Functor.ComputesRightDerivedAt KtoD Qish
      ((HomotopyCategory.quotient AbSeq (up ℤ)).obj K) :=
  by
  -- Reuse the same unbounded right derived functor owner as in the replacement theorem.
  letI : Functor.HasRightDerivedFunctor KtoD Qish :=
    has_unbounded_rightDerivedFunctor_of_mono_into_higherRightDerivedVanishes
      (F := (lim : AbSeq ⥤ Ab))
  -- Once every term is right acyclic, Lemma `13.32.2 (2)` says the ordinary termwise inverse
  -- limit complex computes the chosen unbounded derived inverse limit.
  exact
    computes_unbounded_rightDerived_of_termwise_higherRightDerivedVanishes
      (F := (lim : AbSeq ⥤ Ab)) K hK
