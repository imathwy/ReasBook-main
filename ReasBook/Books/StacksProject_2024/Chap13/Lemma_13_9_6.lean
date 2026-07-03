import Mathlib
import StacksProject_2024.Chap13.Definition_13_8_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {K L : CochainComplex C ℤ}

/- Domain-style sampling for Lemma 13.9.6:
- primary domain: homological algebra of cochain complexes, mapping cones, homotopies, and
  boundedness conditions on cochain complexes;
- inspected owner declarations:
  `CochainComplex.mappingCone`,
  `CochainComplex.mappingCone.homotopyToZeroOfId`,
  `HomotopyEquiv`,
  `ShortComplex`,
  `ShortComplex.Splitting`,
  `CochainComplex.minus`,
  `CochainComplex.bounded`;
- best owner abstraction: the source-facing middle object is the canonical biproduct
  `L ⊞ mappingCone (𝟙 K)`, and the boundedness statements should reuse the canonical bounded-above
  and bounded owners `CochainComplex.minus` and `CochainComplex.bounded` rather than restating
  them as raw existential or conjunction predicates. The degreewise split short complex attached to
  the factorization should also be exposed directly as a `ShortComplex` together with its
  canonical `ShortComplex.Splitting`, rather than recreated downstream from raw maps;
- layer: `source-facing` for the factorization statement, with `HomotopyEquiv`,
  `ShortComplex`, `ShortComplex.Splitting`, `CochainComplex.minus`, and
  `CochainComplex.bounded` providing the `core/canonical` owners;
- primitive data: the canonical middle complex `L ⊞ mappingCone (𝟙 K)` and the morphism
  `biprod.lift α (mappingCone.inr (𝟙 K)) : K ⟶ L ⊞ mappingCone (𝟙 K)`;
- derived API: the projection `biprod.fst`, the section `biprod.inl`, the induced homotopy
  equivalence to `L`, the canonical short complex
  `K ⟶ splitMonoFactorizationObj K L ⟶ mappingCone α`, its degreewise splitting, and boundedness
  properties inherited from `mappingCone` and biproducts.
-/

/-- The canonical middle complex `L^• ⊞ C(1_{K^•})` used in the split-monomorphic factorization
of a morphism `α : K^• ⟶ L^•`. -/
abbrev splitMonoFactorizationObj (K L : CochainComplex C ℤ) : CochainComplex C ℤ :=
  L ⊞ mappingCone (𝟙 K)

/-- The canonical map `K^• ⟶ L^• ⊞ C(1_{K^•})` used in the split-monomorphic factorization of
`α : K^• ⟶ L^•`. -/
abbrev splitMonoFactorizationι (α : K ⟶ L) : K ⟶ splitMonoFactorizationObj K L :=
  biprod.lift α (mappingCone.inr (𝟙 K))

/-- The canonical map from `L^• ⊞ C(1_{K^•})` to the mapping cone `C(α)^•`. Together with
`splitMonoFactorizationι α`, it forms the degreewise split short complex attached to `α`. -/
def splitMonoFactorizationπ (α : K ⟶ L) :
    splitMonoFactorizationObj K L ⟶ mappingCone α :=
  biprod.desc (mappingCone.inr α)
    (-mappingCone.map (𝟙 K) α (𝟙 K) α (by simp))

@[simp] theorem splitMonoFactorizationι_comp_π (α : K ⟶ L) :
    splitMonoFactorizationι α ≫ splitMonoFactorizationπ α = 0 := by
  rw [splitMonoFactorizationπ, splitMonoFactorizationι]
  simp only [biprod.lift_desc, add_eq_zero_iff_eq_neg]
  rw [← neg_inj, neg_neg, mappingCone.map_eq_mapOfHomotopy]
  simpa using (mappingCone.triangleMapOfHomotopy_comm₂
    (Homotopy.ofEq (by simp : (𝟙 K) ≫ α = (𝟙 K) ≫ α))).symm

/-- The canonical short complex `K^• ⟶ L^• ⊞ C(1_{K^•}) ⟶ C(α)^•` attached to a morphism
`α : K^• ⟶ L^•`. -/
abbrev splitMonoFactorizationShortComplex (α : K ⟶ L) : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk
    (splitMonoFactorizationι α)
    (splitMonoFactorizationπ α)
    (splitMonoFactorizationι_comp_π α)

/-- The projection `L^• ⊞ C(1_{K^•}) ⟶ L^•` is a homotopy equivalence, with inverse the left
biproduct inclusion. -/
noncomputable def splitMonoFactorizationProjectionHomotopyEquiv (K L : CochainComplex C ℤ) :
    HomotopyEquiv (splitMonoFactorizationObj K L) L :=
  let p : splitMonoFactorizationObj K L ⟶ L := biprod.fst
  let i : L ⟶ splitMonoFactorizationObj K L := biprod.inl
  let q : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K) := biprod.snd
  let j : mappingCone (𝟙 K) ⟶ splitMonoFactorizationObj K L := biprod.inr
  { hom := p
    inv := i
    homotopyHomInvId := by
      let h₀ : Homotopy (𝟙 (mappingCone (𝟙 K))) 0 := mappingCone.homotopyToZeroOfId K
      let h₁ : Homotopy (q ≫ j) 0 := by
        simpa using (h₀.compRight j).compLeft q
      let h₂ : Homotopy (p ≫ i + q ≫ j) (p ≫ i) := by
        simpa using Homotopy.add (Homotopy.refl (p ≫ i)) h₁
      exact h₂.symm.trans (Homotopy.ofEq (by simp [p, i, q, j]))
    homotopyInvHomId := by
      simpa [p, i] using Homotopy.refl (𝟙 L : L ⟶ L) }

/-- Each component of the canonical factorization map `K^• ⟶ L^• ⊞ C(1_{K^•})` is a split
monomorphism. -/
theorem splitMonoFactorizationι_f_isSplitMono (α : K ⟶ L) (n : ℤ) :
    IsSplitMono ((splitMonoFactorizationι α).f n) := by
  refine IsSplitMono.mk' ⟨(biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n ≫
      (mappingCone.snd (𝟙 K)).v n n (add_zero n), ?_⟩
  simp [splitMonoFactorizationι]

@[simp] theorem splitMonoFactorizationι_comp_fst (α : K ⟶ L) :
    splitMonoFactorizationι α ≫ (biprod.fst : splitMonoFactorizationObj K L ⟶ L) = α := by
  simp [splitMonoFactorizationObj, splitMonoFactorizationι]

private def splitTriangleSection (α : K ⟶ L) (n : ℤ) :
    (mappingCone α).X n ⟶ (splitMonoFactorizationObj K L).X n :=
  (mappingCone.snd α).v n n (add_zero n) ≫
      (biprod.inl : L ⟶ splitMonoFactorizationObj K L).f n -
    (mappingCone.fst α).1.v n (n + 1) rfl ≫
      (mappingCone.inl (𝟙 K)).v (n + 1) n (by lia) ≫
        (biprod.inr : mappingCone (𝟙 K) ⟶ splitMonoFactorizationObj K L).f n

private lemma splitTriangleMap_to_mappingCone_inl (α : K ⟶ L) (n : ℤ) :
    (mappingCone.inl (𝟙 K)).v (n + 1) n (by lia) ≫
      (mappingCone.map (𝟙 K) α (𝟙 K) α (by simp)).f n =
    (mappingCone.inl α).v (n + 1) n (by lia) := by
  simp [mappingCone.map]

private lemma splitTriangleMap_to_mappingCone_snd (α : K ⟶ L) (n : ℤ) :
    (mappingCone.map (𝟙 K) α (𝟙 K) α (by simp)).f n ≫
      (mappingCone.snd α).v n n (add_zero n) =
    (mappingCone.snd (𝟙 K)).v n n (add_zero n) ≫ α.f n := by
  rw [mappingCone.ext_from_iff (𝟙 K) (n + 1) n rfl]
  constructor
  · simp [mappingCone.map]
  · have h :
        mappingCone.inr (𝟙 K) ≫ mappingCone.map (𝟙 K) α (𝟙 K) α (by simp) =
          α ≫ mappingCone.inr α := by
      rw [mappingCone.map_eq_mapOfHomotopy, mappingCone.triangleMapOfHomotopy_comm₂]
    have h' := congrArg (fun k ↦ k.f n) h
    simpa [Category.assoc] using congrArg
      (fun m ↦ m ≫ (mappingCone.snd α).v n n (add_zero n)) h'

private lemma splitTriangleMap_to_mappingCone_fst (α : K ⟶ L) (n : ℤ) :
    (mappingCone.map (𝟙 K) α (𝟙 K) α (by simp)).f n ≫
      (mappingCone.fst α).1.v n (n + 1) rfl =
    (mappingCone.fst (𝟙 K)).1.v n (n + 1) rfl := by
  rw [mappingCone.ext_from_iff (𝟙 K) (n + 1) n rfl]
  constructor
  · have h := splitTriangleMap_to_mappingCone_inl α n
    simpa [Category.assoc] using congrArg
      (fun m ↦ m ≫ (mappingCone.fst α).1.v n (n + 1) rfl) h
  · have h :
        mappingCone.inr (𝟙 K) ≫ mappingCone.map (𝟙 K) α (𝟙 K) α (by simp) =
          α ≫ mappingCone.inr α := by
      rw [mappingCone.map_eq_mapOfHomotopy, mappingCone.triangleMapOfHomotopy_comm₂]
    have h' := congrArg (fun k ↦ k.f n) h
    simpa [Category.assoc] using congrArg
      (fun m ↦ m ≫ (mappingCone.fst α).1.v n (n + 1) rfl) h'

/-- The canonical degreewise splitting of the short complex
`K^• ⟶ splitMonoFactorizationObj K L ⟶ C(α)^•`. -/
def splitMonoFactorizationSplitting (α : K ⟶ L) (n : ℤ) :
    ((splitMonoFactorizationShortComplex α).map (eval C _ n)).Splitting where
  r := (biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n ≫
    (mappingCone.snd (𝟙 K)).v n n (add_zero n)
  s := splitTriangleSection α n
  f_r := by
    simp [splitMonoFactorizationι]
  s_g := by
    change splitTriangleSection α n ≫ (splitMonoFactorizationπ α).f n =
      𝟙 ((mappingCone α).X n)
    rw [show splitTriangleSection α n ≫ (splitMonoFactorizationπ α).f n =
        𝟙 ((mappingCone α).X n) by
      rw [mappingCone.ext_to_iff α n (n + 1) rfl]
      constructor
      · have h := splitTriangleMap_to_mappingCone_fst α n
        simpa [splitTriangleSection, splitMonoFactorizationπ, Category.assoc] using congrArg
          (fun m ↦ (mappingCone.fst α).1.v n (n + 1) rfl ≫
            (mappingCone.inl (𝟙 K)).v (n + 1) n (by lia) ≫ m) h
      · simp [splitTriangleSection, splitMonoFactorizationπ, Category.assoc,
          splitTriangleMap_to_mappingCone_snd]]
  id := by
    let r' :
        (splitMonoFactorizationObj K L).X n ⟶ K.X n :=
      (biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n ≫
        (mappingCone.snd (𝟙 K)).v n n (add_zero n)
    let s' :
        (mappingCone α).X n ⟶ (splitMonoFactorizationObj K L).X n :=
      splitTriangleSection α n
    have hsnd :
        (splitMonoFactorizationπ α).f n ≫ (mappingCone.snd α).v n n (add_zero n) =
          (biprod.fst : splitMonoFactorizationObj K L ⟶ L).f n -
            (biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n ≫
              (mappingCone.snd (𝟙 K)).v n n (add_zero n) ≫ α.f n := by
      refine (isColimitOfPreserves (eval C (ComplexShape.up ℤ) n)
        (BinaryBiproduct.isColimit L (mappingCone (𝟙 K)))).hom_ext ?_
      intro j
      fin_cases j
      · change
          (biprod.inl : L ⟶ splitMonoFactorizationObj K L).f n ≫
              (splitMonoFactorizationπ α).f n ≫
            (mappingCone.snd α).v n n (add_zero n) =
          (biprod.inl : L ⟶ splitMonoFactorizationObj K L).f n ≫
            ((biprod.fst : splitMonoFactorizationObj K L ⟶ L).f n -
              (biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n ≫
                (mappingCone.snd (𝟙 K)).v n n (add_zero n) ≫ α.f n)
        simp [splitMonoFactorizationπ]
      · change
          (biprod.inr : mappingCone (𝟙 K) ⟶ splitMonoFactorizationObj K L).f n ≫
              (splitMonoFactorizationπ α).f n ≫ (mappingCone.snd α).v n n (add_zero n) =
          (biprod.inr : mappingCone (𝟙 K) ⟶ splitMonoFactorizationObj K L).f n ≫
            ((biprod.fst : splitMonoFactorizationObj K L ⟶ L).f n -
              (biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n ≫
                (mappingCone.snd (𝟙 K)).v n n (add_zero n) ≫ α.f n)
        simp [splitMonoFactorizationπ, splitTriangleMap_to_mappingCone_snd, sub_eq_add_neg]
    have hfst :
        (splitMonoFactorizationπ α).f n ≫ (mappingCone.fst α).1.v n (n + 1) rfl =
          -((biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n ≫
            (mappingCone.fst (𝟙 K)).1.v n (n + 1) rfl) := by
      refine (isColimitOfPreserves (eval C (ComplexShape.up ℤ) n)
        (BinaryBiproduct.isColimit L (mappingCone (𝟙 K)))).hom_ext ?_
      intro j
      fin_cases j
      · change
          (biprod.inl : L ⟶ splitMonoFactorizationObj K L).f n ≫
              (splitMonoFactorizationπ α).f n ≫
            (mappingCone.fst α).1.v n (n + 1) rfl =
          (biprod.inl : L ⟶ splitMonoFactorizationObj K L).f n ≫
            (-((biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n ≫
              (mappingCone.fst (𝟙 K)).1.v n (n + 1) rfl))
        simp [splitMonoFactorizationπ]
      · change
          (biprod.inr : mappingCone (𝟙 K) ⟶ splitMonoFactorizationObj K L).f n ≫
              (splitMonoFactorizationπ α).f n ≫ (mappingCone.fst α).1.v n (n + 1) rfl =
          (biprod.inr : mappingCone (𝟙 K) ⟶ splitMonoFactorizationObj K L).f n ≫
            (-((biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n ≫
              (mappingCone.fst (𝟙 K)).1.v n (n + 1) rfl))
        simp [splitMonoFactorizationπ, splitTriangleMap_to_mappingCone_fst]
    refine (isLimitOfPreserves (eval C (ComplexShape.up ℤ) n)
      (BinaryBiproduct.isLimit L (mappingCone (𝟙 K)))).hom_ext ?_
    intro j
    fin_cases j
    · change
        ((r' ≫ (splitMonoFactorizationι α).f n) + (splitMonoFactorizationπ α).f n ≫ s') ≫
            (biprod.fst : splitMonoFactorizationObj K L ⟶ L).f n =
          (𝟙 ((splitMonoFactorizationObj K L).X n)) ≫
            (biprod.fst : splitMonoFactorizationObj K L ⟶ L).f n
      dsimp [r', s', splitTriangleSection]
      simp [Preadditive.add_comp, splitMonoFactorizationι, hsnd, Category.assoc, sub_eq_add_neg]
    · change
        ((r' ≫ (splitMonoFactorizationι α).f n) + (splitMonoFactorizationπ α).f n ≫ s') ≫
            (biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n =
          (𝟙 ((splitMonoFactorizationObj K L).X n)) ≫
            (biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n
      dsimp [r', s', splitTriangleSection]
      simp only [Category.assoc, Int.reduceNeg, Preadditive.comp_sub, Preadditive.add_comp,
        biprod_lift_snd_f, Preadditive.sub_comp, biprod_inl_snd_f, comp_zero,
        biprod_inr_snd_f, Category.comp_id, zero_sub, Category.id_comp]
      have hfst' := congrArg
        (fun m ↦ -m ≫ (mappingCone.inl (𝟙 K)).v (n + 1) n (by lia)) hfst
      have hfst'' :
          -(splitMonoFactorizationπ α).f n ≫
              (mappingCone.fst α).1.v n (n + 1) rfl ≫
              (mappingCone.inl (𝟙 K)).v (n + 1) n (by lia) =
            (biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n ≫
              (mappingCone.fst (𝟙 K)).1.v n (n + 1) rfl ≫
              (mappingCone.inl (𝟙 K)).v (n + 1) n (by lia) := by
        simpa only [Category.assoc, Preadditive.neg_comp, neg_neg] using hfst'
      rw [hfst'']
      change
        (biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n ≫
            ((mappingCone.snd (𝟙 K)).v n n (add_zero n) ≫ (mappingCone.inr (𝟙 K)).f n) +
          (biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n ≫
            ((mappingCone.fst (𝟙 K)).1.v n (n + 1) rfl ≫
              (mappingCone.inl (𝟙 K)).v (n + 1) n (by lia)) =
          (biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n
      rw [← Preadditive.comp_add]
      simpa [add_comm] using congrArg
        (fun m ↦
          (biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n ≫ m)
        (mappingCone.id_X (𝟙 K) n (n + 1) rfl)

-- Proof sketch: take `\tilde L^• = L^• ⊞ C(1_{K^•})`, let `\tilde α` be the pair consisting of
-- `α` and the canonical cone inclusion `mappingCone.inr (𝟙 K)`. The termwise split monomorphism
-- is witnessed degreewise by the cone projection `mappingCone.snd (𝟙 K)`, while the projection
-- `biprod.fst : L ⊞ mappingCone (𝟙 K) ⟶ L` has section `biprod.inl`, with
-- `biprod.fst ≫ biprod.inl` homotopic to the identity because the cone summand is contractible
-- by `mappingCone.homotopyToZeroOfId`.
/-- Lemma 13.9.6: every morphism `α : K^• ⟶ L^•` factors through the canonical complex
`L^• ⊞ C(1_{K^•})` by a termwise split injection, and the projection to `L^•` has a section whose
composite with that projection is homotopic to the identity. -/
theorem splitMono_factorization_through_biproduct_mappingCone_id
    (α : K ⟶ L) :
    ∃ _ : Homotopy
        ((biprod.fst : splitMonoFactorizationObj K L ⟶ L) ≫
          (biprod.inl : L ⟶ splitMonoFactorizationObj K L))
        (𝟙 (splitMonoFactorizationObj K L)),
      (∀ n : ℤ, IsSplitMono ((splitMonoFactorizationι α).f n)) ∧
        splitMonoFactorizationι α ≫
            (biprod.fst : splitMonoFactorizationObj K L ⟶ L) = α ∧
        (biprod.inl : L ⟶ splitMonoFactorizationObj K L) ≫
            (biprod.fst : splitMonoFactorizationObj K L ⟶ L) = 𝟙 L := by
  refine ⟨(splitMonoFactorizationProjectionHomotopyEquiv K L).homotopyHomInvId, ?_⟩
  refine ⟨splitMonoFactorizationι_f_isSplitMono α, ?_, ?_⟩
  · exact splitMonoFactorizationι_comp_fst α
  · simp

lemma mappingCone_id_plus (hK : CochainComplex.plus C K) :
    CochainComplex.plus C (mappingCone (𝟙 K)) := by
  obtain ⟨n, hn⟩ := (CochainComplex.plus_iff C K).1 hK
  refine (CochainComplex.plus_iff C (mappingCone (𝟙 K))).2 ⟨n - 1, ?_⟩
  rw [isStrictlyGE_iff]
  intro i hi
  letI := hn
  rw [mappingCone.isZero_X_iff]
  exact ⟨K.isZero_of_isStrictlyGE n (i + 1) (by lia), K.isZero_of_isStrictlyGE n i (by lia)⟩

lemma mappingCone_id_boundedAbove (hK : CochainComplex.minus C K) :
    CochainComplex.minus C (mappingCone (𝟙 K)) := by
  obtain ⟨n, hn⟩ := (CochainComplex.minus_iff C K).1 hK
  refine (CochainComplex.minus_iff C (mappingCone (𝟙 K))).2 ⟨n, ?_⟩
  rw [isStrictlyLE_iff]
  intro i hi
  letI := hn
  rw [mappingCone.isZero_X_iff]
  exact ⟨K.isZero_of_isStrictlyLE n (i + 1) (by lia), K.isZero_of_isStrictlyLE n i (by lia)⟩

-- Proof sketch: if `K` and `L` are bounded below, choose lower bounds for both; the cone of the
-- identity on `K` is again bounded below, and binary biproducts of bounded-below complexes remain
-- bounded below.
/-- The canonical factorization object is bounded below whenever both source and target complexes
are bounded below. -/
theorem splitMonoFactorizationObj_plus
    (hK : CochainComplex.plus C K) (hL : CochainComplex.plus C L) :
    CochainComplex.plus C (splitMonoFactorizationObj K L) := by
  simpa [splitMonoFactorizationObj] using
    (CochainComplex.plus C).prop_of_isColimit_binaryCofan
      (BinaryBiproduct.isColimit L (mappingCone (𝟙 K))) hL (mappingCone_id_plus hK)

-- Proof sketch: choose upper bounds for `K` and `L`; the mapping cone of the identity on `K` is
-- still bounded above, and the biproduct with `L` preserves this bounded-above property.
/-- The canonical factorization object is bounded above whenever both source and target complexes
are bounded above. -/
theorem splitMonoFactorizationObj_boundedAbove
    (hK : CochainComplex.minus C K) (hL : CochainComplex.minus C L) :
    CochainComplex.minus C (splitMonoFactorizationObj K L) := by
  simpa [splitMonoFactorizationObj] using
    (CochainComplex.minus C).prop_of_isLimit_binaryFan
      (BinaryBiproduct.isLimit L (mappingCone (𝟙 K))) hL
      (mappingCone_id_boundedAbove hK)

-- Proof sketch: combine the bounded-below statement for `K^+` with the bounded-above statement
-- for `K^-`; this gives the boundedness assertion for the canonical factorization object.
/-- The canonical factorization object is bounded whenever both source and target complexes are
bounded. -/
theorem splitMonoFactorizationObj_bounded
    (hK : CochainComplex.bounded C K) (hL : CochainComplex.bounded C L) :
    CochainComplex.bounded C (splitMonoFactorizationObj K L) := by
  rcases (CochainComplex.bounded_iff C K).1 hK with ⟨hKplus, hKminus⟩
  rcases (CochainComplex.bounded_iff C L).1 hL with ⟨hLplus, hLminus⟩
  exact (CochainComplex.bounded_iff C (splitMonoFactorizationObj K L)).2
    ⟨splitMonoFactorizationObj_plus hKplus hLplus,
      splitMonoFactorizationObj_boundedAbove hKminus hLminus⟩

end CochainComplex
