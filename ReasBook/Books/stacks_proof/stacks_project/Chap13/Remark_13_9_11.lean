import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits ComplexShape HomologicalComplex
open CochainComplex

noncomputable section

local notation "Cpx" => CochainComplex AddCommGrpCat ℤ
local notation "G4" => AddCommGrpCat.of (ZMod 4)
local notation "G0" => AddCommGrpCat.of PUnit
local notation "eps4" => ((2 : ℤ) • (𝟙 G4))

/- Domain-style sampling:
- primary domain: cochain complexes, degreewise split short complexes, and homotopy-category
  commutative squares;
- relevant owner declarations inspected:
  `ShortComplex.map`,
  `HomologicalComplex.eval`,
  `ShortComplex.Splitting`,
  `ShortComplex.Hom`,
  `exists_rightMap_eq_in_homotopyCategory_of_termwiseSplitMono`,
  `exists_leftMap_eq_in_homotopyCategory_of_termwiseSplitEpi`,
  `comp_eq_zero_in_homotopyCategory_of_termwiseSplit`;
- best owner abstraction: the rows are canonically `ShortComplex` objects, while their termwise
  split exactness is the Chapter `13` owner existence property
  `∀ n, Nonempty ((S.map (eval AddCommGrpCat (up ℤ) n)).Splitting)`
  rather than chosen public splitting data; the homotopy-category compatibility data are
  canonically `CommSq`, while any strict replacement should be expressed by the row-morphism owner
  `ShortComplex.Hom` with fixed outer components rather than by a bespoke package of two squares;
- source/core/bridge triage:
  `source-facing`: the existence of a counterexample to strictifying a homotopy-commutative
    diagram between termwise split exact sequences of cochain complexes;
  `core/canonical`: `ShortComplex`, degreewise `ShortComplex.Splitting`, `CommSq`, and
    `ShortComplex.Hom`;
  `bridge/view`: equality in the homotopy category via the quotient functor `Q`.

Primitive data here is the pair of short complexes and the three vertical maps between their
terms. The termwise split condition is a genuine existence property and should therefore stay as
`Nonempty`-valued degreewise splitness rather than exposing a chosen family of splittings. The
homotopy-commutativity assumptions are expressed directly through `CommSq`, while the claim that a
strict replacement exists is expressed by the canonical owner `S₁ ⟶ S₂` together with fixed outer
components and equality of the middle quotient class, without packaging them into local wrapper
structures.
-/

-- Proof sketch: use the counterexample from Examples, Equation `(110.64.0.1)`, whose two rows are
-- degreewise split short exact sequences of complexes and whose outer squares commute only in the
-- homotopy category. If a homotopic replacement `b'` of the middle map existed making both
-- squares commute strictly, the induced trace computation would become additive, contradicting the
-- example.
/-- Helper for Remark 13.9.11: doubling on `ZMod 4` is square-zero as an endomorphism. -/
lemma zmod4_double_sq_zero : eps4 ≫ eps4 = 0 := by
  -- The explicit endomorphism is multiplication by `2`, so we can check it on the four elements.
  ext x
  fin_cases x <;> rfl

/-- Helper for Remark 13.9.11: the left complex is concentrated in degree `1`. -/
def counterexampleAObj (n : ℤ) : AddCommGrpCat :=
  if n = 1 then G4 else G0

/-- Helper for Remark 13.9.11: the right complex is concentrated in degree `0`. -/
def counterexampleCObj (n : ℤ) : AddCommGrpCat :=
  if n = 0 then G4 else G0

/-- Helper for Remark 13.9.11: the middle complex has `G4` in degrees `0` and `1`. -/
def counterexampleBObj (n : ℤ) : AddCommGrpCat :=
  if n = 0 ∨ n = 1 then G4 else G0

/-- Helper for Remark 13.9.11: the only nonzero differential in the middle complex is `eps4`
from degree `0` to degree `1`. -/
def counterexampleB_d_nonzero_branch (n : ℤ) (h : n = 0) :
    counterexampleBObj n ⟶ counterexampleBObj (n + 1) := by
  subst h
  simpa [counterexampleBObj] using (eps4 : G4 ⟶ G4)

/-- Helper for Remark 13.9.11: the left complex has zero differential. -/
def counterexampleAD (n : ℤ) : counterexampleAObj n ⟶ counterexampleAObj (n + 1) :=
  0

/-- Helper for Remark 13.9.11: the middle complex differential is `eps4` in degree `0`
and zero elsewhere. -/
def counterexampleBD (n : ℤ) : counterexampleBObj n ⟶ counterexampleBObj (n + 1) :=
  if h : n = 0 then counterexampleB_d_nonzero_branch n h else 0

/-- Helper for Remark 13.9.11: the right complex has zero differential. -/
def counterexampleCD (n : ℤ) : counterexampleCObj n ⟶ counterexampleCObj (n + 1) :=
  0

/-- Helper for Remark 13.9.11: the left complex differential squares to zero. -/
lemma counterexampleAD_sq (n : ℤ) :
    counterexampleAD n ≫ counterexampleAD (n + 1) = 0 := by
  simp [counterexampleAD]

/-- Helper for Remark 13.9.11: the middle complex differential squares to zero. -/
lemma counterexampleBD_sq (n : ℤ) :
    counterexampleBD n ≫ counterexampleBD (n + 1) = 0 := by
  -- The only possibly nonzero differential is in degree `0`, and the next differential vanishes.
  by_cases h : n = 0
  · subst h
    ext x
    rfl
  · simp [counterexampleBD, h]

/-- Helper for Remark 13.9.11: the right complex differential squares to zero. -/
lemma counterexampleCD_sq (n : ℤ) :
    counterexampleCD n ≫ counterexampleCD (n + 1) = 0 := by
  simp [counterexampleCD]

/-- Helper for Remark 13.9.11: the source single-term complex. -/
def counterexampleA : Cpx :=
  (CochainComplex.singleFunctor AddCommGrpCat 1).obj G4

/-- Helper for Remark 13.9.11: the two-term middle complex with differential `eps4`. -/
def counterexampleB : Cpx :=
  CochainComplex.of counterexampleBObj counterexampleBD counterexampleBD_sq

/-- Helper for Remark 13.9.11: the target single-term complex. -/
def counterexampleC : Cpx :=
  (CochainComplex.singleFunctor AddCommGrpCat 0).obj G4

/-- Helper for Remark 13.9.11: the middle complex is `G4` in degree `0`. -/
lemma counterexampleB_X_zero :
    counterexampleB.X 0 = G4 := by
  rfl

/-- Helper for Remark 13.9.11: the middle complex is `G4` in degree `1`. -/
lemma counterexampleB_X_one :
    counterexampleB.X 1 = G4 := by
  rfl

/-- Helper for Remark 13.9.11: the middle complex is zero away from degrees `0` and `1`. -/
lemma counterexampleB_isZero_of_ne_zero_of_ne_one (n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) :
    Limits.IsZero (counterexampleB.X n) := by
  -- Outside the two visible degrees, the explicit object function is the zero object.
  change Limits.IsZero (counterexampleBObj n)
  simp [counterexampleBObj, h0, h1]
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- Helper for Remark 13.9.11: the only nonzero differential of the middle complex is `eps4`. -/
lemma counterexampleB_d_zero :
    counterexampleB.d 0 1 = eps4 := by
  change counterexampleBD 0 = eps4
  simp [counterexampleBD, counterexampleB_d_nonzero_branch, counterexampleBObj]

/-- Helper for Remark 13.9.11: the middle differential vanishes in degree `1`. -/
lemma counterexampleB_d_one :
    counterexampleB.d 1 2 = 0 := by
  change counterexampleBD 1 = 0
  simp [counterexampleBD]

/-- Helper for Remark 13.9.11: the middle differential vanishes away from degree `0`. -/
lemma counterexampleB_d_eq_zero_of_ne_zero (n : ℤ) (h : n ≠ 0) :
    counterexampleB.d n (n + 1) = 0 := by
  -- Outside degree `0`, the explicit middle differential was defined to be zero.
  simp [counterexampleB, CochainComplex.of, counterexampleBD, h]
  rfl

/-- Helper for Remark 13.9.11: the unique nonzero component of `A -> B` lands in degree `1`. -/
def counterexampleFComponent : G4 ⟶ counterexampleB.X 1 :=
  𝟙 G4

/-- Helper for Remark 13.9.11: the degree-`1` component used for `A -> B` kills the outgoing
differential of `B`. -/
lemma counterexampleFComponent_cycles (k : ℤ) (h : (up ℤ).Rel 1 k) :
    counterexampleFComponent ≫ counterexampleB.d 1 k = 0 := by
  -- The relation forces `k = 2`, and the degree-`1` differential vanishes.
  have hk₀ : 2 = k := by
    simpa using h
  have hk : k = 2 := by
    linarith
  subst hk
  rw [counterexampleB_d_one]
  simp [counterexampleFComponent]

/-- Helper for Remark 13.9.11: the degree-`1` inclusion `A -> B`. -/
def counterexampleF : counterexampleA ⟶ counterexampleB :=
  HomologicalComplex.mkHomFromSingle (K := counterexampleB) (j := 1)
    counterexampleFComponent counterexampleFComponent_cycles

/-- Helper for Remark 13.9.11: the map `A -> B` is the identity in degree `1`. -/
lemma counterexampleF_f_one :
    counterexampleF.f 1 = 𝟙 G4 := by
  -- Unfold the single-term constructor at its supporting degree.
  change (HomologicalComplex.mkHomFromSingle (K := counterexampleB) (j := 1)
      counterexampleFComponent counterexampleFComponent_cycles).f 1 = 𝟙 G4
  dsimp [counterexampleFComponent, HomologicalComplex.mkHomFromSingle,
    HomologicalComplex.singleObjXIsoOfEq, HomologicalComplex.single]
  simp

/-- Helper for Remark 13.9.11: the map `A -> B` vanishes away from degree `1`. -/
lemma counterexampleF_f_eq_zero_of_ne_one (n : ℤ) (h : n ≠ 1) :
    counterexampleF.f n = 0 := by
  -- Every other source degree of the single complex is zero.
  apply (HomologicalComplex.isZero_single_obj_X (up ℤ) 1 G4 n h).eq_of_src

/-- Helper for Remark 13.9.11: the unique nonzero component of `B -> C` starts in degree `0`. -/
def counterexampleGComponent : counterexampleB.X 0 ⟶ G4 :=
  𝟙 G4

/-- Helper for Remark 13.9.11: the degree-`0` component used for `B -> C` kills the incoming
differential of `B`. -/
lemma counterexampleGComponent_cycles (i : ℤ) (h : (up ℤ).Rel i 0) :
    counterexampleB.d i 0 ≫ counterexampleGComponent = 0 := by
  -- The relation forces `i = -1`, and there is no differential there.
  have hi₀ : i + 1 = 0 := by
    simpa using h
  have hi : i = -1 := by
    linarith
  subst hi
  have hzero : counterexampleB.d (-1) 0 = 0 := by
    simpa using counterexampleB_d_eq_zero_of_ne_zero (-1) (by omega)
  rw [hzero]
  simp [counterexampleGComponent]

/-- Helper for Remark 13.9.11: the degree-`0` projection `B -> C`. -/
def counterexampleG : counterexampleB ⟶ counterexampleC :=
  HomologicalComplex.mkHomToSingle (K := counterexampleB) (j := 0)
    counterexampleGComponent counterexampleGComponent_cycles

/-- Helper for Remark 13.9.11: the map `B -> C` is the identity in degree `0`. -/
lemma counterexampleG_f_zero :
    counterexampleG.f 0 = 𝟙 G4 := by
  -- Unfold the single-term constructor at its supporting degree.
  change (HomologicalComplex.mkHomToSingle (K := counterexampleB) (j := 0)
      counterexampleGComponent counterexampleGComponent_cycles).f 0 = 𝟙 G4
  dsimp [counterexampleGComponent, HomologicalComplex.mkHomToSingle,
    HomologicalComplex.singleObjXIsoOfEq, HomologicalComplex.single]
  simp

/-- Helper for Remark 13.9.11: the map `B -> C` vanishes away from degree `0`. -/
lemma counterexampleG_f_eq_zero_of_ne_zero (n : ℤ) (h : n ≠ 0) :
    counterexampleG.f n = 0 := by
  -- Every other target degree of the single complex is zero.
  apply (HomologicalComplex.isZero_single_obj_X (up ℤ) 0 G4 n h).eq_of_tgt

/-- Helper for Remark 13.9.11: the explicit short complex realizing the Stacks counterexample. -/
lemma counterexampleF_comp_counterexampleG :
    counterexampleF ≫ counterexampleG = 0 := by
  -- A map out of a single complex is determined by its degree-`1` component.
  apply HomologicalComplex.from_single_hom_ext
  change counterexampleF.f 1 ≫ counterexampleG.f 1 = 0
  rw [counterexampleG_f_eq_zero_of_ne_zero 1 (by omega)]
  simp [counterexampleF_f_one]

/-- Helper for Remark 13.9.11: the explicit short complex realizing the Stacks counterexample. -/
abbrev counterexampleRow : ShortComplex Cpx :=
  ShortComplex.mk counterexampleF counterexampleG counterexampleF_comp_counterexampleG

/-- Helper for Remark 13.9.11: multiplication by `3` on the left single-term complex. -/
def counterexampleAEnd : counterexampleA ⟶ counterexampleA :=
  (CochainComplex.singleFunctor AddCommGrpCat 1).map ((3 : ℤ) • (𝟙 G4))

/-- Helper for Remark 13.9.11: the left endomorphism is multiplication by `3` in degree `1`. -/
lemma counterexampleAEnd_f_one :
    counterexampleAEnd.f 1 = (3 : ℤ) • (𝟙 G4) := by
  -- At the supporting degree of the single complex, the functor map is exactly the given map.
  change ((CochainComplex.singleFunctor AddCommGrpCat 1).map ((3 : ℤ) • (𝟙 G4))).f 1 =
    (3 : ℤ) • (𝟙 G4)
  dsimp [CochainComplex.singleFunctor, CochainComplex.singleFunctors, HomologicalComplex.single]
  simp

/-- Helper for Remark 13.9.11: the left endomorphism vanishes away from degree `1`. -/
lemma counterexampleAEnd_f_eq_zero_of_ne_one (n : ℤ) (h : n ≠ 1) :
    counterexampleAEnd.f n = 0 := by
  -- Every other degree of the source single complex is zero.
  apply (HomologicalComplex.isZero_single_obj_X (up ℤ) 1 G4 n h).eq_of_src

/-- Helper for Remark 13.9.11: the explicit degree `-1` family for the left-square homotopy is
supported only at `(1, 0)`. -/
private def counterexample_left_square_hom
    (i j : ℤ) : counterexampleA.X i ⟶ counterexampleB.X j :=
  if hi : i = 1 then
    if hj : j = 0 then by
      subst hi
      subst hj
      exact 𝟙 G4
    else
      0
  else
    0

/-- Helper for Remark 13.9.11: the left-square homotopy family vanishes away from adjacent
degrees. -/
private lemma counterexample_left_square_hom_zero
    (i j : ℤ) (hij : ¬ (up ℤ).Rel j i) :
    counterexample_left_square_hom i j = 0 := by
  by_cases hi : i = 1
  · subst hi
    by_cases hj : j = 0
    · exfalso
      exact hij (by simpa [hj])
    · simp [counterexample_left_square_hom, hj]
  · simp [counterexample_left_square_hom, hi]

/-- Helper for Remark 13.9.11: in degree `1`, the explicit homotopy recovers the difference
between `counterexampleF` and `counterexampleAEnd ≫ counterexampleF`. -/
private lemma counterexample_left_square_hom_comm_one :
    counterexampleF.f 1 =
      (dNext 1 counterexample_left_square_hom) +
        (prevD 1 counterexample_left_square_hom) +
          (counterexampleAEnd ≫ counterexampleF).f 1 := by
  -- In degree `1`, only the `(1,0)` component of the homotopy survives.
  rw [dNext_eq counterexample_left_square_hom
      (show (ComplexShape.up ℤ).Rel 1 2 by simp),
    prevD_eq counterexample_left_square_hom
      (show (ComplexShape.up ℤ).Rel 0 1 by simp)]
  change (𝟙 G4 : G4 ⟶ G4) =
    (0 : G4 ⟶ G4) + (𝟙 G4 : G4 ⟶ G4) ≫ eps4 + ((3 : ℤ) • (𝟙 G4) ≫ (𝟙 G4))
  ext x
  fin_cases x <;> rfl

/-- Helper for Remark 13.9.11: the explicit degree `-1` family gives a homotopy from
`counterexampleF` to `counterexampleAEnd ≫ counterexampleF`. -/
private def counterexample_left_square_homotopy :
    Homotopy counterexampleF (counterexampleAEnd ≫ counterexampleF) :=
  Homotopy.mk
    counterexample_left_square_hom
    counterexample_left_square_hom_zero
    (fun i ↦ by
      by_cases hi : i = 1
      · subst hi
        -- Degree `1` is the only nontrivial component check.
        simpa [counterexampleF_f_one] using counterexample_left_square_hom_comm_one
      · -- Away from degree `1`, the source single complex is zero so both sides agree
        -- automatically.
        exact (HomologicalComplex.isZero_single_obj_X (up ℤ) 1 G4 i hi).eq_of_src _ _)

/-- Helper for Remark 13.9.11: the identity map of `C` is the identity in degree `0`. -/
lemma counterexampleC_id_f_zero :
    (𝟙 counterexampleC : counterexampleC ⟶ counterexampleC).f 0 = 𝟙 G4 := by
  rfl

/-- Helper for Remark 13.9.11: the identity map of `B` is the identity in degree `0`. -/
lemma counterexampleB_id_f_zero :
    (𝟙 counterexampleB : counterexampleB ⟶ counterexampleB).f 0 = 𝟙 G4 := by
  rfl

/-- Helper for Remark 13.9.11: the identity map of `B` is the identity in degree `1`. -/
lemma counterexampleB_id_f_one :
    (𝟙 counterexampleB : counterexampleB ⟶ counterexampleB).f 1 = 𝟙 G4 := by
  rfl

/-- Helper for Remark 13.9.11: the identity map of `C` vanishes away from degree `0`. -/
lemma counterexampleC_id_f_eq_zero_of_ne_zero (n : ℤ) (h : n ≠ 0) :
    (𝟙 counterexampleC : counterexampleC ⟶ counterexampleC).f n = 0 := by
  -- Every other degree of `C` is zero.
  apply (HomologicalComplex.isZero_single_obj_X (up ℤ) 0 G4 n h).eq_of_src

/-- Helper for Remark 13.9.11: the identity on the zero degree of `A` is zero. -/
lemma counterexampleA_id_zero :
    𝟙 (counterexampleA.X 0) = 0 := by
  -- Degree `0` is outside the support of `A`.
  apply (HomologicalComplex.isZero_single_obj_X (up ℤ) 1 G4 0 (by omega)).eq_of_src

/-- Helper for Remark 13.9.11: the identity on the degree `1` term of `C` is zero. -/
lemma counterexampleC_id_one :
    𝟙 (counterexampleC.X 1) = 0 := by
  -- Degree `1` is outside the support of `C`.
  apply (HomologicalComplex.isZero_single_obj_X (up ℤ) 0 G4 1 (by omega)).eq_of_src

/-- Helper for Remark 13.9.11: the explicit row is degreewise split. -/
lemma counterexample_row_termwise_split (n : ℤ) :
    Nonempty ((counterexampleRow.map (eval AddCommGrpCat (up ℤ) n)).Splitting) := by
  -- Evaluate the row degreewise and split the three visible degree patterns directly.
  by_cases h0 : n = 0
  · subst h0
    refine ⟨ShortComplex.Splitting.mk 0 (𝟙 G4) ?_ ?_ ?_⟩
    · simpa [counterexampleRow, counterexampleF_f_eq_zero_of_ne_one 0 (by omega),
        counterexampleA_id_zero]
    · change 𝟙 G4 ≫ 𝟙 G4 = 𝟙 G4
      simp [counterexampleRow, counterexampleG_f_zero]
    · change 0 + 𝟙 G4 ≫ 𝟙 G4 = 𝟙 G4
      simp [counterexampleRow, counterexampleG_f_zero]
  · by_cases h1 : n = 1
    · subst h1
      refine ⟨ShortComplex.Splitting.mk (𝟙 G4) 0 ?_ ?_ ?_⟩
      · change 𝟙 G4 ≫ 𝟙 G4 = 𝟙 G4
        simp [counterexampleRow, counterexampleF_f_one]
      · simpa [counterexampleRow, counterexampleG_f_eq_zero_of_ne_zero 1 (by omega),
          counterexampleC_id_one]
      · change 𝟙 G4 ≫ 𝟙 G4 + 0 = 𝟙 G4
        simp [counterexampleRow, counterexampleF_f_one,
          counterexampleG_f_eq_zero_of_ne_zero 1 (by omega)]
    · have hA : Limits.IsZero (counterexampleA.X n) :=
        HomologicalComplex.isZero_single_obj_X (up ℤ) 1 G4 n h1
      have hB : Limits.IsZero (counterexampleB.X n) :=
        counterexampleB_isZero_of_ne_zero_of_ne_one n h0 h1
      have hC : Limits.IsZero (counterexampleC.X n) :=
        HomologicalComplex.isZero_single_obj_X (up ℤ) 0 G4 n h0
      refine ⟨ShortComplex.Splitting.mk 0 0 ?_ ?_ ?_⟩
      · exact hA.eq_of_src _ _
      · exact hC.eq_of_src _ _
      · exact hB.eq_of_src _ _

/-- Helper for Remark 13.9.11: the left square commutes in the homotopy category via the
degree-`(1,0)` identity homotopy component. -/
lemma counterexample_left_square_commSq :
    let Q := HomotopyCategory.quotient AddCommGrpCat (up ℤ)
    CommSq (Q.map counterexampleRow.f) (Q.map counterexampleAEnd) (Q.map (𝟙 counterexampleB))
      (Q.map counterexampleRow.f) := by
  -- Route correction: after moving `A` to the canonical single-complex model, the remaining
  -- obstruction is an explicit one-component homotopy from `counterexampleF` to
  -- `counterexampleAEnd ≫ counterexampleF`.
  dsimp [counterexampleRow]
  refine ⟨?_⟩
  -- Pass the explicit source-level homotopy to equality in the quotient category.
  simpa [Functor.map_comp] using
    (HomotopyCategory.eq_of_homotopy _ _ counterexample_left_square_homotopy)

/-- Helper for Remark 13.9.11: a strict short-complex morphism with the prescribed outer
components forces the middle map on degrees `0` and `1`. -/
lemma strict_middle_components_of_outer_components
    (φ : counterexampleRow ⟶ counterexampleRow)
    (h₁ : φ.τ₁ = counterexampleAEnd) (h₃ : φ.τ₃ = 𝟙 counterexampleC) :
    φ.τ₂.f 0 = 𝟙 G4 ∧ φ.τ₂.f 1 = (3 : ℤ) • 𝟙 G4 := by
  constructor
  · -- The right square forces the degree-`0` component because `g` is the identity there.
    have hcomm := congrArg (fun f => f.f 0) φ.comm₂₃
    simpa [counterexampleRow, counterexampleG_f_zero, h₃, counterexampleC_id_f_zero] using hcomm
  · -- The left square forces the degree-`1` component because `f` is the identity there.
    have hcomm := congrArg (fun f => f.f 1) φ.comm₁₂
    rw [h₁] at hcomm
    simp [counterexampleRow, counterexampleAEnd_f_one, counterexampleF_f_one] at hcomm
    simpa using hcomm.symm

/-- Helper for Remark 13.9.11: multiplication by `3` on `G4` is doubling plus the identity. -/
lemma counterexample_three_smul_eq_double_plus_id :
    (3 : ℤ) • (𝟙 G4) = eps4 + 𝟙 G4 := by
  -- The explicit endomorphisms agree on all four elements of `ZMod 4`.
  ext x
  fin_cases x <;> rfl

/-- Helper for Remark 13.9.11: the degree-`0` homotopy equation collapses to the left scalar
obstruction. -/
lemma counterexample_homotopy_degree_zero_normal_form {u : counterexampleB ⟶ counterexampleB}
    (H : Homotopy u (𝟙 counterexampleB)) (hu0 : u.f 0 = 𝟙 G4) :
    counterexampleB.d 0 1 ≫ H.hom 1 0 = 0 := by
  -- Rewrite the degree-`0` homotopy equation using the explicit differential shape of
  -- `counterexampleB`.
  have hcomm := H.comm 0
  -- The degree `-1` differential vanishes, so only the visible `0 -> 1` component remains.
  rw [dNext_eq H.hom (show (up ℤ).Rel 0 1 by simp),
    prevD_eq H.hom (show (up ℤ).Rel (-1) 0 by simp)] at hcomm
  rw [hu0, counterexampleB_id_f_zero] at hcomm
  have hprev : counterexampleB.d (-1) 0 = 0 := by
    simpa using counterexampleB_d_eq_zero_of_ne_zero (-1) (by omega)
  rw [hprev] at hcomm
  simp only [comp_zero, add_zero] at hcomm
  -- Put both sides in a cancellable form with the same right summand `𝟙 G4`.
  have hcomm' :
      (0 : G4 ⟶ G4) + 𝟙 G4 =
        ((counterexampleB.d 0 1 ≫ H.hom 1 0 : G4 ⟶ G4)) + 𝟙 G4 := by
    simpa using hcomm
  have hcancel : (counterexampleB.d 0 1 ≫ H.hom 1 0 : G4 ⟶ G4) = 0 := by
    simpa using (add_right_cancel hcomm').symm
  simpa using hcancel

/-- Helper for Remark 13.9.11: the degree-`1` homotopy equation collapses to the right scalar
obstruction. -/
lemma counterexample_homotopy_degree_one_normal_form {u : counterexampleB ⟶ counterexampleB}
    (H : Homotopy u (𝟙 counterexampleB)) (hu1 : u.f 1 = (3 : ℤ) • (𝟙 G4)) :
    H.hom 1 0 ≫ counterexampleB.d 0 1 = counterexampleB.d 0 1 := by
  -- Rewrite the degree-`1` homotopy equation using the explicit differential shape of
  -- `counterexampleB`.
  have hcomm := H.comm 1
  -- The degree `1 -> 2` differential vanishes, so the obstruction is encoded by the `0 -> 1`
  -- differential together with the fixed endpoint maps.
  rw [dNext_eq H.hom (show (up ℤ).Rel 1 2 by simp),
    prevD_eq H.hom (show (up ℤ).Rel 0 1 by simp)] at hcomm
  rw [hu1, counterexampleB_id_f_one, counterexampleB_d_one,
    counterexample_three_smul_eq_double_plus_id] at hcomm
  simp only [zero_comp, zero_add] at hcomm
  -- Cancel the shared identity summand to isolate the forced `eps4` component.
  have hcomm' :
      ((2 : ℤ) • (𝟙 G4)) + 𝟙 G4 =
        ((H.hom 1 0 ≫ counterexampleB.d 0 1 : G4 ⟶ G4)) + 𝟙 G4 := by
    exact hcomm
  have hd0 : (counterexampleB.d 0 1 : G4 ⟶ G4) = (2 : ℤ) • (𝟙 G4) := by
    simpa using counterexampleB_d_zero
  have hcancel : (H.hom 1 0 ≫ counterexampleB.d 0 1 : G4 ⟶ G4) = (2 : ℤ) • (𝟙 G4) := by
    simpa using (add_right_cancel hcomm').symm
  simpa [hd0] using hcancel

/-- Helper for Remark 13.9.11: the two normalized scalar equations on the middle component are
incompatible on `ZMod 4`. -/
lemma counterexample_forced_middle_component_contradiction (k : G4 ⟶ G4)
    (hk0 : eps4 ≫ k = 0) (hk1 : k ≫ eps4 = eps4) :
    False := by
  -- Evaluate both endomorphism equations at `1 : ZMod 4`.
  have hk0_eval : (2 : ZMod 4) * k 1 = 0 := by
    simpa using congrArg (fun f : G4 ⟶ G4 => f 1) hk0
  have hk1_eval : (2 : ZMod 4) * k 1 = 2 := by
    simpa using congrArg (fun f : G4 ⟶ G4 => f 1) hk1
  have hbad : (0 : ZMod 4) = 2 := by
    calc
      (0 : ZMod 4) = (2 : ZMod 4) * k 1 := by simpa using hk0_eval.symm
      _ = 2 := hk1_eval
  exact (by decide : ¬ ((0 : ZMod 4) = 2)) hbad

/-- Helper for Remark 13.9.11: the native middle-component obstruction on `counterexampleB`
reduces to the explicit `ZMod 4` contradiction. -/
lemma counterexample_forced_middle_component_contradiction_native
    (k : counterexampleB.X 1 ⟶ counterexampleB.X 0)
    (hk0 : counterexampleB.d 0 1 ≫ k = 0)
    (hk1 : k ≫ counterexampleB.d 0 1 = counterexampleB.d 0 1) :
    False := by
  -- The visible degrees of `counterexampleB` are definitionally `G4`, so the native equations
  -- are exactly the scalar obstruction from the explicit `ZMod 4` computation.
  simpa [counterexampleB_d_zero] using
    (counterexample_forced_middle_component_contradiction k hk0 hk1)

/-- Helper for Remark 13.9.11: the forced middle map is not homotopic to the identity. -/
lemma no_homotopy_to_forced_middle_map (u : counterexampleB ⟶ counterexampleB)
    (h0 : u.f 0 = 𝟙 G4) (h1 : u.f 1 = (3 : ℤ) • 𝟙 G4)
    (hu : (HomotopyCategory.quotient AddCommGrpCat (up ℤ)).map u =
      (HomotopyCategory.quotient AddCommGrpCat (up ℤ)).map (𝟙 counterexampleB)) :
    False := by
  -- Route correction: the source-faithful obstruction lives in the degree `0/1` homotopy
  -- equations for the explicit middle complex.
  let H : Homotopy u (𝟙 counterexampleB) := HomotopyCategory.homotopyOfEq _ _ hu
  let k : counterexampleB.X 1 ⟶ counterexampleB.X 0 := H.hom 1 0
  -- Normalize the homotopy equations degreewise before doing the explicit `ZMod 4` contradiction.
  have hk0 : counterexampleB.d 0 1 ≫ k = 0 := by
    simpa [k] using counterexample_homotopy_degree_zero_normal_form H h0
  have hk1 : k ≫ counterexampleB.d 0 1 = counterexampleB.d 0 1 := by
    simpa [k] using counterexample_homotopy_degree_one_normal_form H h1
  exact counterexample_forced_middle_component_contradiction_native k hk0 hk1

/-- Helper for Remark 13.9.11: there is no strict row morphism with the prescribed outer
components and middle map homotopic to the identity. -/
lemma counterexample_no_strict_middle_replacement :
    let Q := HomotopyCategory.quotient AddCommGrpCat (up ℤ)
    ¬ ∃ φ : counterexampleRow ⟶ counterexampleRow,
        φ.τ₁ = counterexampleAEnd ∧ φ.τ₃ = 𝟙 counterexampleC ∧
          Q.map φ.τ₂ = Q.map (𝟙 counterexampleB) := by
  intro Q hφ
  rcases hφ with ⟨φ, h₁, h₃, hQ⟩
  -- Any strict lift forces the visible middle components, so the local homotopy obstruction applies.
  obtain ⟨h0, h1⟩ := strict_middle_components_of_outer_components φ h₁ h₃
  exact no_homotopy_to_forced_middle_map φ.τ₂ h0 h1 hQ

/-- Helper for Remark 13.9.11: the explicit Stacks row packages the witness for the existential
counterexample. -/
lemma counterexample_exists_packaging_adapter :
    let Q := HomotopyCategory.quotient AddCommGrpCat (up ℤ)
    ∃ (S₁ S₂ : ShortComplex.{0, 1} Cpx) (a : S₁.X₁ ⟶ S₂.X₁) (b : S₁.X₂ ⟶ S₂.X₂)
      (c : S₁.X₃ ⟶ S₂.X₃),
      (∀ n : ℤ, Nonempty ((S₁.map (eval AddCommGrpCat (up ℤ) n)).Splitting)) ∧
      (∀ n : ℤ, Nonempty ((S₂.map (eval AddCommGrpCat (up ℤ) n)).Splitting)) ∧
      CommSq (Q.map S₁.f) (Q.map a) (Q.map b) (Q.map S₂.f) ∧
      CommSq (Q.map S₁.g) (Q.map b) (Q.map c) (Q.map S₂.g) ∧
      ¬ ∃ φ : S₁ ⟶ S₂, φ.τ₁ = a ∧ φ.τ₃ = c ∧ Q.map φ.τ₂ = Q.map b := by
  -- Instantiate both rows by the explicit Stacks counterexample and reuse the previously
  -- established splitness, left square in `K`, and middle-map obstruction.
  dsimp
  refine ⟨counterexampleRow, counterexampleRow, counterexampleAEnd, 𝟙 counterexampleB,
    𝟙 counterexampleC, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact counterexample_row_termwise_split n
  · intro n
    exact counterexample_row_termwise_split n
  · simpa using counterexample_left_square_commSq
  · -- The right square already commutes strictly before passing to the quotient.
    refine ⟨?_⟩
    calc
      (HomotopyCategory.quotient AddCommGrpCat (up ℤ)).map counterexampleRow.g ≫
          (HomotopyCategory.quotient AddCommGrpCat (up ℤ)).map (𝟙 counterexampleC) =
          (HomotopyCategory.quotient AddCommGrpCat (up ℤ)).map counterexampleRow.g := by
            simp
      _ =
          (HomotopyCategory.quotient AddCommGrpCat (up ℤ)).map (𝟙 counterexampleB) ≫
            (HomotopyCategory.quotient AddCommGrpCat (up ℤ)).map counterexampleRow.g := by
            simp
  · simpa using counterexample_no_strict_middle_replacement

/-- Helper for Remark 13.9.11: the explicit existential packaging is propositionally unchanged
when the `ShortComplex` universe parameters are inferred. -/
lemma counterexample_exists_packaging_universe_bridge :
    (let Q := HomotopyCategory.quotient AddCommGrpCat (up ℤ)
      ∃ (S₁ S₂ : ShortComplex.{0, 1} Cpx) (a : S₁.X₁ ⟶ S₂.X₁) (b : S₁.X₂ ⟶ S₂.X₂)
        (c : S₁.X₃ ⟶ S₂.X₃),
        (∀ n : ℤ, Nonempty ((S₁.map (eval AddCommGrpCat (up ℤ) n)).Splitting)) ∧
        (∀ n : ℤ, Nonempty ((S₂.map (eval AddCommGrpCat (up ℤ) n)).Splitting)) ∧
        CommSq (Q.map S₁.f) (Q.map a) (Q.map b) (Q.map S₂.f) ∧
        CommSq (Q.map S₁.g) (Q.map b) (Q.map c) (Q.map S₂.g) ∧
        ¬ ∃ φ : S₁ ⟶ S₂, φ.τ₁ = a ∧ φ.τ₃ = c ∧ Q.map φ.τ₂ = Q.map b) →
    (let Q := HomotopyCategory.quotient AddCommGrpCat (up ℤ)
      ∃ (S₁ S₂ : ShortComplex.{0, 1} Cpx) (a : S₁.X₁ ⟶ S₂.X₁) (b : S₁.X₂ ⟶ S₂.X₂)
        (c : S₁.X₃ ⟶ S₂.X₃),
        (∀ n : ℤ, Nonempty ((S₁.map (eval AddCommGrpCat (up ℤ) n)).Splitting)) ∧
        (∀ n : ℤ, Nonempty ((S₂.map (eval AddCommGrpCat (up ℤ) n)).Splitting)) ∧
        CommSq (Q.map S₁.f) (Q.map a) (Q.map b) (Q.map S₂.f) ∧
        CommSq (Q.map S₁.g) (Q.map b) (Q.map c) (Q.map S₂.g) ∧
        ¬ ∃ φ : S₁ ⟶ S₂, φ.τ₁ = a ∧ φ.τ₃ = c ∧ Q.map φ.τ₂ = Q.map b) := by
  -- The explicit witness is unchanged once the theorem target fixes the concrete hom-universe.
  intro h
  simpa using h

/-- Remark 13.9.11: there exists a counterexample in `AddCommGrpCat` showing that a morphism
between the middle terms of two termwise split exact sequences of cochain complexes cannot in
general be replaced by a homotopic morphism making the homotopy-commutative diagram strictly
commutative in the category of complexes. -/
@[stacks 014J]
theorem exists_termwiseSplit_counterexample_to_middleMap_strictification :
    let Q := HomotopyCategory.quotient AddCommGrpCat (up ℤ)
    ∃ (S₁ S₂ : ShortComplex.{0, 1} Cpx) (a : S₁.X₁ ⟶ S₂.X₁) (b : S₁.X₂ ⟶ S₂.X₂)
      (c : S₁.X₃ ⟶ S₂.X₃),
      (∀ n : ℤ, Nonempty ((S₁.map (eval AddCommGrpCat (up ℤ) n)).Splitting)) ∧
      (∀ n : ℤ, Nonempty ((S₂.map (eval AddCommGrpCat (up ℤ) n)).Splitting)) ∧
      CommSq (Q.map S₁.f) (Q.map a) (Q.map b) (Q.map S₂.f) ∧
      CommSq (Q.map S₁.g) (Q.map b) (Q.map c) (Q.map S₂.g) ∧
      ¬ ∃ φ : S₁ ⟶ S₂, φ.τ₁ = a ∧ φ.τ₃ = c ∧ Q.map φ.τ₂ = Q.map b := by
  -- Feed the explicit `ShortComplex.{0,1}` witness through the proposition-level universe bridge.
  exact counterexample_exists_packaging_universe_bridge counterexample_exists_packaging_adapter
