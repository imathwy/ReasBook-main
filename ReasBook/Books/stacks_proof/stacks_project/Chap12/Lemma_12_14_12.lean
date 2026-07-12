import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open ComplexShape HomologicalComplex

universe u v

namespace CategoryTheory
namespace CochainComplex

section

variable {V : Type u} [Category.{v} V] [Preadditive V]
variable (S : ShortComplex (CochainComplex V ℤ))

/- Domain-style sampling:
- primary domain: degreewise split short complexes of cochain complexes and the homotopies
  comparing the owner connecting morphisms `CochainComplex.homOfDegreewiseSplit`.
- inspected owner declarations: `CochainComplex.homOfDegreewiseSplit`,
  `CochainComplex.homOfDegreewiseSplit_f`,
  `CochainComplex.shiftFunctorObjXIso`,
  `ChainComplex.degreewiseShortComplex` from `Lemma_12_14_4`.
- best owner abstraction: `CochainComplex.homOfDegreewiseSplit`.
- primitive data in this file: the degreewise short complex, two degreewise splittings, and the
  section-difference family `h`.
- derived API in this file: the induced homotopy between the two owner connecting morphisms and
  its degreewise component formula. -/

/-- The short complex obtained by evaluating a short complex of cochain complexes in degree `n`.
-/
abbrev degreewiseShortComplex (S : ShortComplex (CochainComplex V ℤ)) (n : ℤ) :=
  S.map (HomologicalComplex.eval V (up ℤ) n)

variable
  (spl spl' : ∀ n : ℤ, (degreewiseShortComplex S n).Splitting)
  (h : ∀ n : ℤ, (degreewiseShortComplex S n).X₃ ⟶ (degreewiseShortComplex S n).X₁)

/-- The second degreewise splitting differs from the first by the section corrections `h^n`. -/
abbrev sectionDifference : Prop :=
  ∀ n : ℤ, (spl' n).s = (spl n).s + h n ≫ (degreewiseShortComplex S n).f

/-- Helper for Lemma 12.14.12: the corrected retraction still retracts the degreewise map `f`. -/
private theorem corrected_degreewise_retraction_f_r
    (n : ℤ) :
    (degreewiseShortComplex S n).f ≫
        ((spl n).r - (degreewiseShortComplex S n).g ≫ h n) = 𝟙 _ := by
  -- The correction term dies because consecutive maps in a short complex compose to zero.
  rw [Preadditive.comp_sub, (spl n).f_r, (degreewiseShortComplex S n).zero_assoc]
  have hzero : (0 : (degreewiseShortComplex S n).X₁ ⟶ (degreewiseShortComplex S n).X₃) ≫ h n = 0 := by
    simpa using (CategoryTheory.Limits.zero_comp (X := (degreewiseShortComplex S n).X₁) (f := h n))
  rw [hzero, sub_zero]

/-- Helper for Lemma 12.14.12: the corrected section and corrected retraction still sum to the
identity in degree `n`. -/
private theorem corrected_degreewise_identity
    (hs : sectionDifference S spl spl' h)
    (n : ℤ) :
    ((spl n).r - (degreewiseShortComplex S n).g ≫ h n) ≫ (degreewiseShortComplex S n).f +
        (degreewiseShortComplex S n).g ≫ (spl' n).s = 𝟙 _ := by
  -- Rewrite the new section using `hs n`, then cancel the correction terms additively.
  calc
    ((spl n).r - (degreewiseShortComplex S n).g ≫ h n) ≫ (degreewiseShortComplex S n).f +
        (degreewiseShortComplex S n).g ≫ (spl' n).s =
      (spl n).r ≫ (degreewiseShortComplex S n).f +
        (degreewiseShortComplex S n).g ≫ (spl n).s := by
        rw [hs n, Preadditive.sub_comp, Preadditive.comp_add, Category.assoc]
        abel
    _ = 𝟙 _ := (spl n).id

/-- Helper for Lemma 12.14.12: modifying the degreewise section by `h^n ≫ f` modifies the
degreewise retraction by `- g ≫ h^n` and still yields a splitting. -/
private abbrev corrected_degreewise_splitting
    (hs : sectionDifference S spl spl' h)
    (n : ℤ) :
    (degreewiseShortComplex S n).Splitting where
  r := (spl n).r - (degreewiseShortComplex S n).g ≫ h n
  s := (spl' n).s
  f_r := corrected_degreewise_retraction_f_r (S := S) (spl := spl) (h := h) n
  s_g := (spl' n).s_g
  id := corrected_degreewise_identity (S := S) (spl := spl) (spl' := spl') (h := h) hs n

private theorem retraction_eq_sub_section_correction
    (hs : sectionDifference S spl spl' h)
    (n : ℤ) :
    (spl' n).r = (spl n).r - (degreewiseShortComplex S n).g ≫ h n := by
  -- Compare the given splitting with the corrected splitting via equality of their sections.
  let τ := corrected_degreewise_splitting (S := S) (spl := spl) (spl' := spl') (h := h) hs n
  have hsτ : τ.s = (spl' n).s := rfl
  have hτ : τ = spl' n := ShortComplex.Splitting.ext_s τ (spl' n) hsτ
  simpa [τ] using (congrArg ShortComplex.Splitting.r hτ).symm

-- Proof sketch: use that each degreewise splitting satisfies `r ≫ s = 0`. Expanding
-- `(spl' n).r = (spl n).r + g^n ≫ q^n` and the derived formula
-- `(spl' n).r = (spl n).r - q^n ≫ h^n` coming from `ShortComplex.Splitting.ext_s`, then precompose
-- with `(spl n).s`. The identities `(spl n).s ≫ (spl n).r = 0` and `(spl n).s ≫ q^n = 𝟙`
-- leave exactly `g^n + h^n = 0`.
/-- Lemma 12.14.12 (1): if a second degreewise splitting differs from the first one by correction
maps `h^n` on the section side and `g^n` on the retraction side, then these corrections satisfy
`g^n = -h^n` in every degree. -/
@[stacks 011L]
theorem retraction_correction_eq_neg_section_correction
    (k : ∀ n : ℤ, (degreewiseShortComplex S n).X₃ ⟶ (degreewiseShortComplex S n).X₁)
    (hs : sectionDifference S spl spl' h)
    (hr' : ∀ n : ℤ,
      (spl' n).r = (spl n).r + (degreewiseShortComplex S n).g ≫ k n)
    (n : ℤ) :
    k n = -h n := by
  -- Compare the two retraction formulas and precompose with the original section.
  have hcompare := hr' n
  rw [retraction_eq_sub_section_correction (S := S) (spl := spl) (spl' := spl') (h := h) hs n] at hcompare
  have hpre := congrArg ((spl n).s ≫ ·) hcompare
  -- The common `s^n ≫ π^n` term vanishes, while `s^n ≫ β^n = 𝟙`.
  change (spl n).s ≫ ((spl n).r - (degreewiseShortComplex S n).g ≫ h n) =
      (spl n).s ≫ ((spl n).r + (degreewiseShortComplex S n).g ≫ k n) at hpre
  rw [Preadditive.comp_sub, Preadditive.comp_add] at hpre
  rw [(spl n).s_r, (spl n).s_g_assoc, (spl n).s_g_assoc, zero_sub, zero_add] at hpre
  simpa using hpre.symm

/-- Helper for Lemma 12.14.12: unshifting the degree-`(n-1,n)` differential on `A^•[1]` gives
the negative of the original differential `d_A^n`. -/
private theorem shift_prevD_component_neg
    (n : ℤ) :
    (S.X₁.shiftFunctorObjXIso 1 (n - 1) n (Int.sub_add_cancel n 1).symm).inv ≫
      (S.X₁⟦(1 : ℤ)⟧).d (n - 1) n ≫
      (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom =
        -S.X₁.d n (n + 1) := by
  -- The cochain shift contributes the expected sign on differentials.
  change (S.X₁.XIsoOfEq (Int.sub_add_cancel n 1)).inv ≫
      (S.X₁⟦(1 : ℤ)⟧).d (n - 1) n ≫ (S.X₁.XIsoOfEq rfl).hom =
        -S.X₁.d n (n + 1)
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, CochainComplex.shiftFunctor_obj_d',
    Int.negOnePow_one, Units.neg_smul, one_smul]
  have hshift :
      (S.X₁.XIsoOfEq (Int.sub_add_cancel n 1)).inv ≫ S.X₁.d (n - 1 + 1) (n + 1) =
        S.X₁.d n (n + 1) :=
    HomologicalComplex.XIsoOfEq_inv_comp_d (K := S.X₁) (h := Int.sub_add_cancel n 1) (p₃ := n + 1)
  simpa [Preadditive.comp_neg] using congrArg Neg.neg hshift

/-- Helper for Lemma 12.14.12: the degree-`n` component of the owner connecting morphism is the
textbook composite `s^n ≫ d_B^n ≫ π^{n+1}`. -/
private theorem homOfDegreewiseSplit_component
    (σ : ∀ n : ℤ, (degreewiseShortComplex S n).Splitting)
    (n : ℤ) :
    (CochainComplex.homOfDegreewiseSplit S σ).f n =
      (σ n).s ≫ S.X₂.d n (n + 1) ≫ (σ (n + 1)).r := by
  -- Unfold the owner cocycle once; its diagonal component is exactly the source formula.
  simpa [CochainComplex.cocycleOfDegreewiseSplit, CochainComplex.HomComplex.Cochain.mk_v,
    Category.assoc] using (CochainComplex.homOfDegreewiseSplit_f S σ n)

/-- Helper for Lemma 12.14.12: package the correction family `-h^n` as the canonical `(-1)`-cochain
used by `Cochain.equivHomotopy`. -/
private abbrev splitting_difference_cochain :
    CochainComplex.HomComplex.Cochain S.X₃ (S.X₁⟦(1 : ℤ)⟧) (-1) :=
  CochainComplex.HomComplex.Cochain.mk fun p q hpq ↦
    (-h p) ≫
      (S.X₁.shiftFunctorObjXIso 1 (p - 1) p (Int.sub_add_cancel p 1).symm).inv ≫
        ((S.X₁⟦(1 : ℤ)⟧).XIsoOfEq (by omega)).hom

/-- Helper for Lemma 12.14.12: in the successor diagonal term, the intermediate transport from
degree `n + 1 - 1` to degree `n` cancels against the two canonical shift identifications. -/
private theorem shiftFunctorObjXIso_transport_cancel
    (n : ℤ) :
    (S.X₁.shiftFunctorObjXIso 1 (n + 1 - 1) (n + 1) (by omega)).inv ≫
        ((S.X₁⟦(1 : ℤ)⟧).XIsoOfEq (show n + 1 - 1 = n by omega)).hom ≫
        (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom =
      𝟙 _ := by
  -- Unfold the displayed isomorphisms and compose the resulting equality transports explicitly.
  let p : (S.X₁⟦(1 : ℤ)⟧).X (n + 1 - 1) = S.X₁.X (n + 1) :=
    (CochainComplex.shiftFunctor_obj_X V 1 S.X₁ (n + 1 - 1)).trans (by simp)
  let q : (S.X₁⟦(1 : ℤ)⟧).X (n + 1 - 1) = (S.X₁⟦(1 : ℤ)⟧).X n :=
    congrArg (fun i ↦ (S.X₁⟦(1 : ℤ)⟧).X i) (show n + 1 - 1 = n by omega)
  let r : (S.X₁⟦(1 : ℤ)⟧).X n = S.X₁.X (n + 1) :=
    (CochainComplex.shiftFunctor_obj_X V 1 S.X₁ n).trans rfl
  change eqToHom p.symm ≫ eqToHom q ≫ eqToHom r = 𝟙 _
  calc
    eqToHom p.symm ≫ eqToHom q ≫ eqToHom r =
        eqToHom (p.symm.trans q) ≫ eqToHom r := by
          rw [CategoryTheory.eqToHom_trans_assoc]
    _ = eqToHom ((p.symm.trans q).trans r) := by
          rw [CategoryTheory.eqToHom_trans]
    _ = 𝟙 _ := by
          simpa using CategoryTheory.eqToHom_refl (S.X₁.X (n + 1)) ((p.symm.trans q).trans r)

/-- Helper for Lemma 12.14.12: after translating the predecessor term of the correction cochain
back to degree `n + 1`, it is the textbook summand `h^n ≫ d_A^n`. -/
private theorem splitting_difference_cochain_prev_diag
    (n : ℤ) :
    (splitting_difference_cochain (S := S) (h := h)).v n (n - 1) (by omega) ≫
        (S.X₁⟦(1 : ℤ)⟧).d (n - 1) n ≫
        (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom =
      h n ≫ S.X₁.d n (n + 1) := by
  -- Collapse the harmless index transport on the cochain entry, then rewrite the shifted
  -- differential by the sign rule for cochain shifts.
  rw [CochainComplex.HomComplex.Cochain.mk_v]
  -- The specialized comparison `XIsoOfEq` is the identity on degree `n`.
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.assoc]
  -- After transport normalization, the predecessor piece is exactly the shifted differential.
  calc
    (-h n) ≫
        (S.X₁.shiftFunctorObjXIso 1 (n - 1) n (Int.sub_add_cancel n 1).symm).inv ≫
          𝟙 (((S.X₁⟦(1 : ℤ)⟧).X (n - 1))) ≫
            (S.X₁⟦(1 : ℤ)⟧).d (n - 1) n ≫
            (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom =
      (-h n) ≫
        ((S.X₁.shiftFunctorObjXIso 1 (n - 1) n (Int.sub_add_cancel n 1).symm).inv ≫
          (S.X₁⟦(1 : ℤ)⟧).d (n - 1) n ≫
          (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom) := by
            simp
    _ = (-h n) ≫ (-S.X₁.d n (n + 1)) := by
          simpa using
            congrArg (fun k ↦ (-h n) ≫ k) (shift_prevD_component_neg (S := S) (n := n))
    _ = h n ≫ S.X₁.d n (n + 1) := by
          calc
            (-h n) ≫ (-S.X₁.d n (n + 1)) = -((-h n) ≫ S.X₁.d n (n + 1)) := by
              exact CategoryTheory.Preadditive.comp_neg (-h n) (S.X₁.d n (n + 1))
            _ = -(-(h n ≫ S.X₁.d n (n + 1))) := by
              exact congrArg Neg.neg
                (CategoryTheory.Preadditive.neg_comp (h n) (S.X₁.d n (n + 1)))
            _ = h n ≫ S.X₁.d n (n + 1) := by
              simpa using neg_neg (h n ≫ S.X₁.d n (n + 1))

/-- Helper for Lemma 12.14.12: after translating the successor term of the correction cochain
back to degree `n + 1`, it is the textbook summand `- d_C^n ≫ h^{n + 1}`. -/
private theorem splitting_difference_cochain_next_diag
    (n : ℤ) :
    S.X₃.d n (n + 1) ≫
        (splitting_difference_cochain (S := S) (h := h)).v (n + 1) n (by omega) ≫
        (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom =
      -(S.X₃.d n (n + 1) ≫ h (n + 1)) := by
  -- Collapse the index transport on the cochain entry and cancel the shift isomorphism pair.
  rw [CochainComplex.HomComplex.Cochain.mk_v]
  -- Normalize the comparison from degree `n + 1 - 1` to degree `n` before canceling the shift
  -- isomorphism pair.
  -- The remaining term is the source-side correction from the textbook computation.
  calc
    S.X₃.d n (n + 1) ≫
        ((-h (n + 1)) ≫
            (S.X₁.shiftFunctorObjXIso 1 (n + 1 - 1) (n + 1) (by omega)).inv ≫
              ((S.X₁⟦(1 : ℤ)⟧).XIsoOfEq (show n + 1 - 1 = n by omega)).hom) ≫
          (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom =
      S.X₃.d n (n + 1) ≫
        (-h (n + 1)) ≫
          ((S.X₁.shiftFunctorObjXIso 1 (n + 1 - 1) (n + 1) (by omega)).inv ≫
            ((S.X₁⟦(1 : ℤ)⟧).XIsoOfEq (show n + 1 - 1 = n by omega)).hom ≫
            (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom) := by
              simp
    _ = S.X₃.d n (n + 1) ≫ (-h (n + 1)) := by
          simpa using
            congrArg
              (fun k ↦ S.X₃.d n (n + 1) ≫ (-h (n + 1)) ≫ k)
              (shiftFunctorObjXIso_transport_cancel (S := S) (n := n))
    _ = -(S.X₃.d n (n + 1) ≫ h (n + 1)) := by
          simpa using CategoryTheory.Preadditive.comp_neg (S.X₃.d n (n + 1)) (h (n + 1))

/-- Helper for Lemma 12.14.12: the diagonal component of the coboundary of the correction cochain
is the sum of the two textbook homotopy terms. -/
private theorem homOfDegreewiseSplit_difference_delta_diag
    (n : ℤ) :
    (CochainComplex.HomComplex.δ (-1) 0 (splitting_difference_cochain (S := S) (h := h))).v n n
        (by simp) ≫
        (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom =
      (-(show S.X₃.X n ⟶ S.X₁.X (n + 1) by
          simpa using (S.X₃.d n (n + 1) ≫ h (n + 1))) +
        (show S.X₃.X n ⟶ S.X₁.X (n + 1) by
          simpa using (h n ≫ S.X₁.d n (n + 1)))) := by
  -- Expand the diagonal coboundary component into its predecessor and successor pieces.
  rw [CochainComplex.HomComplex.δ_v (-1) 0 rfl
    (splitting_difference_cochain (S := S) (h := h)) n n (by simp) (n - 1) (n + 1) (by omega)
    (by omega)]
  -- Route correction: use the normalized predecessor/successor diagonal terms instead of
  -- expanding the shift transport inline once more.
  rw [CategoryTheory.Preadditive.add_comp]
  simp only [Int.negOnePow_zero, one_smul]
  have hprev := splitting_difference_cochain_prev_diag (S := S) (h := h) n
  have hnext := splitting_difference_cochain_next_diag (S := S) (h := h) n
  have hprev' :
      ((splitting_difference_cochain (S := S) (h := h)).v n (n - 1) (by omega) ≫
          (S.X₁⟦(1 : ℤ)⟧).d (n - 1) n) ≫
          (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom =
        h n ≫ S.X₁.d n (n + 1) := by
    simpa [Category.assoc] using hprev
  have hnext' :
      (S.X₃.d n (n + 1) ≫
          (splitting_difference_cochain (S := S) (h := h)).v (n + 1) n (by omega)) ≫
          (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom =
        -(S.X₃.d n (n + 1) ≫ h (n + 1)) := by
    simpa [Category.assoc] using hnext
  rw [hprev', hnext']
  abel

/-- Helper for Lemma 12.14.12: postcomposing the zero morphism with the standard shift
identification still gives zero. -/
private theorem zero_postcompose_shift
    (n : ℤ) :
    (0 : S.X₃.X n ⟶ (S.X₁⟦(1 : ℤ)⟧).X n) ≫
        (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom = 0 := by
  -- This is the canonical zero-composition fact used when the mixed correction vanishes.
  simpa using
    (CategoryTheory.Limits.zero_comp
      (f := (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom))

/-- Helper for Lemma 12.14.12: after postcomposing with the standard shift identification, the
`g`-linear correction term becomes `d_C^n ≫ h^{n+1}`. -/
private theorem postcompose_right_linearized_g_comm
    (n : ℤ) :
    ((spl n).s ≫ S.X₂.d n (n + 1) ≫ (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1)) ≫
        (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom =
      S.X₃.d n (n + 1) ≫ h (n + 1) := by
  -- Reassociate to expose the `g`-chain map commutativity and then use `s ≫ g = 𝟙`.
  have hshift :
      ((spl n).s ≫ S.X₂.d n (n + 1) ≫ (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1)) ≫
          (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom =
        (spl n).s ≫ S.X₂.d n (n + 1) ≫ (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1) := by
    simp
  have hcomm :
      (spl n).s ≫ S.X₂.d n (n + 1) ≫ (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1) =
        (spl n).s ≫ (degreewiseShortComplex S n).g ≫ S.X₃.d n (n + 1) ≫ h (n + 1) := by
    simpa [Category.assoc] using congrArg
      (fun k ↦ (spl n).s ≫ k ≫ h (n + 1))
      (S.g.comm n (n + 1))
  have hs_g :
      (spl n).s ≫ (degreewiseShortComplex S n).g ≫ S.X₃.d n (n + 1) ≫ h (n + 1) =
        S.X₃.d n (n + 1) ≫ h (n + 1) := by
    simpa [Category.assoc] using congrArg
      (fun k ↦ k ≫ S.X₃.d n (n + 1) ≫ h (n + 1))
      ((spl n).s_g)
  exact hshift.trans (hcomm.trans hs_g)

/-- Helper for Lemma 12.14.12: after postcomposing with the standard shift identification, the
`f`-linear correction term becomes `h^n ≫ d_A^n`. -/
private theorem postcompose_right_linearized_f_comm
    (n : ℤ) :
    (h n ≫ (degreewiseShortComplex S n).f ≫ S.X₂.d n (n + 1) ≫ (spl (n + 1)).r) ≫
        (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom =
      h n ≫ S.X₁.d n (n + 1) := by
  -- Reassociate to expose the `f`-chain map commutativity and then use `f ≫ r = 𝟙`.
  have hshift :
      (h n ≫ (degreewiseShortComplex S n).f ≫ S.X₂.d n (n + 1) ≫ (spl (n + 1)).r) ≫
          (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom =
        h n ≫ (degreewiseShortComplex S n).f ≫ S.X₂.d n (n + 1) ≫ (spl (n + 1)).r := by
    simp
  have hcomm :
      h n ≫ (degreewiseShortComplex S n).f ≫ S.X₂.d n (n + 1) ≫ (spl (n + 1)).r =
        h n ≫ S.X₁.d n (n + 1) ≫ (degreewiseShortComplex S (n + 1)).f ≫ (spl (n + 1)).r := by
    simpa [Category.assoc] using congrArg
      (fun k ↦ h n ≫ k ≫ (spl (n + 1)).r)
      ((S.f.comm n (n + 1)).symm)
  have hf_r :
      h n ≫ S.X₁.d n (n + 1) ≫ (degreewiseShortComplex S (n + 1)).f ≫ (spl (n + 1)).r =
        h n ≫ S.X₁.d n (n + 1) := by
    simpa [Category.assoc] using congrArg
      (fun k ↦ h n ≫ S.X₁.d n (n + 1) ≫ k)
      ((spl (n + 1)).f_r)
  exact hshift.trans (hcomm.trans hf_r)

/-- Helper for Lemma 12.14.12: the bilinear mixed correction term in the owner-side expansion
vanishes because `f ≫ d_B` rewrites to `d_A ≫ f`, and then `f ≫ g = 0`. -/
private theorem homOfDegreewiseSplit_mixed_correction_term_vanishes
    (n : ℤ) :
    h n ≫ (degreewiseShortComplex S n).f ≫ S.X₂.d n (n + 1) ≫
        (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1) ≫
        (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom = 0 := by
  -- Reassociate first so that `S.f.comm` rewrites the middle composite to `d_A ≫ f`.
  have hcomm :
      h n ≫ (degreewiseShortComplex S n).f ≫ S.X₂.d n (n + 1) ≫
          (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1) ≫
            (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom =
        h n ≫ S.X₁.d n (n + 1) ≫ (degreewiseShortComplex S (n + 1)).f ≫
          (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1) ≫
            (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom := by
    simpa [Category.assoc] using congrArg
      (fun k ↦ h n ≫ k ≫ (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1) ≫
        (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom)
      ((S.f.comm n (n + 1)).symm)
  -- Then the short-complex relation `f ≫ g = 0` collapses the whole term to zero.
  calc
    h n ≫ (degreewiseShortComplex S n).f ≫ S.X₂.d n (n + 1) ≫
        (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1) ≫
        (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom =
      h n ≫ S.X₁.d n (n + 1) ≫ (degreewiseShortComplex S (n + 1)).f ≫
        (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1) ≫
        (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom := hcomm
    _ = h n ≫ S.X₁.d n (n + 1) ≫ 0 ≫ h (n + 1) ≫
        (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom := by
          simpa [Category.assoc] using congrArg
            (fun k ↦ h n ≫ S.X₁.d n (n + 1) ≫ k ≫ h (n + 1) ≫
              (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom)
            ((degreewiseShortComplex S (n + 1)).zero)
    _ = 0 := by
          have hzero :
              ((h n ≫ S.X₁.d n (n + 1)) ≫
                  (0 : S.X₁.X (n + 1) ⟶ S.X₃.X (n + 1))) = 0 := by
            simpa using
              (CategoryTheory.Limits.comp_zero
                (f := h n ≫ S.X₁.d n (n + 1)))
          calc
            h n ≫ S.X₁.d n (n + 1) ≫
                (0 : S.X₁.X (n + 1) ⟶ S.X₃.X (n + 1)) ≫ h (n + 1) ≫
                (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom =
              (0 : S.X₃.X n ⟶ S.X₃.X (n + 1)) ≫ h (n + 1) ≫
                (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom := by
                  simpa [Category.assoc] using congrArg
                    (fun k ↦ k ≫ h (n + 1) ≫
                      (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom)
                    hzero
            _ = 0 := by
                  simp

/-- Helper for Lemma 12.14.12: expanding the corrected owner composite in the ambient morphism
type yields the old owner term, the two linear correction terms, and the mixed term. -/
private theorem corrected_owner_component_ambient_expansion
    (n : ℤ) :
    (((spl n).s + h n ≫ (degreewiseShortComplex S n).f) ≫ S.X₂.d n (n + 1) ≫
        ((spl (n + 1)).r - (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1))) =
      ((spl n).s ≫ S.X₂.d n (n + 1) ≫ (spl (n + 1)).r) -
        ((spl n).s ≫ S.X₂.d n (n + 1) ≫
          (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1)) +
        (h n ≫ (degreewiseShortComplex S n).f ≫ S.X₂.d n (n + 1) ≫
          (spl (n + 1)).r) -
        (h n ≫ (degreewiseShortComplex S n).f ≫ S.X₂.d n (n + 1) ≫
          (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1)) := by
  -- Route correction: expand before the final shift postcomposition so every summand stays in the
  -- ambient owner type `S.X₃.X n ⟶ S.X₁.X (n + 1)` throughout the additive normalization.
  calc
    (((spl n).s + h n ≫ (degreewiseShortComplex S n).f) ≫ S.X₂.d n (n + 1) ≫
        ((spl (n + 1)).r - (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1))) =
      ((((spl n).s + h n ≫ (degreewiseShortComplex S n).f) ≫ S.X₂.d n (n + 1) ≫
          (spl (n + 1)).r) -
        (((spl n).s + h n ≫ (degreewiseShortComplex S n).f) ≫ S.X₂.d n (n + 1) ≫
          (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1))) := by
            simpa [Category.assoc] using
              (Preadditive.comp_sub
                (((spl n).s + h n ≫ (degreewiseShortComplex S n).f) ≫ S.X₂.d n (n + 1))
                (spl (n + 1)).r
                ((degreewiseShortComplex S (n + 1)).g ≫ h (n + 1)))
    _ =
      (((spl n).s ≫ S.X₂.d n (n + 1) ≫ (spl (n + 1)).r) +
        (h n ≫ (degreewiseShortComplex S n).f ≫ S.X₂.d n (n + 1) ≫ (spl (n + 1)).r)) -
        (((spl n).s ≫ S.X₂.d n (n + 1) ≫
            (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1)) +
          (h n ≫ (degreewiseShortComplex S n).f ≫ S.X₂.d n (n + 1) ≫
            (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1))) := by
              rw [Preadditive.add_comp, Preadditive.add_comp]
              simp only [Category.assoc]
    _ =
      ((spl n).s ≫ S.X₂.d n (n + 1) ≫ (spl (n + 1)).r) -
        ((spl n).s ≫ S.X₂.d n (n + 1) ≫
          (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1)) +
        (h n ≫ (degreewiseShortComplex S n).f ≫ S.X₂.d n (n + 1) ≫
          (spl (n + 1)).r) -
        (h n ≫ (degreewiseShortComplex S n).f ≫ S.X₂.d n (n + 1) ≫
          (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1)) := by
            abel

/-- Helper for Lemma 12.14.12: expanding the corrected owner component produces the old owner
term, the two linear correction terms, and the mixed term in a fixed additive order. -/
private theorem homOfDegreewiseSplit_postcompose_bilinear_expansion
    (n : ℤ) :
    (((((spl n).s + h n ≫ (degreewiseShortComplex S n).f) ≫ S.X₂.d n (n + 1)) ≫
        ((spl (n + 1)).r - (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1))) ≫
        (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom) =
      (((spl n).s ≫ S.X₂.d n (n + 1) ≫ (spl (n + 1)).r) ≫
          (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom) -
        (((spl n).s ≫ S.X₂.d n (n + 1) ≫
            (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1)) ≫
          (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom) +
        ((h n ≫ (degreewiseShortComplex S n).f ≫ S.X₂.d n (n + 1) ≫
            (spl (n + 1)).r) ≫
          (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom) -
        (h n ≫ (degreewiseShortComplex S n).f ≫ S.X₂.d n (n + 1) ≫
          (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1) ≫
          (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom) := by
  -- First expand the corrected owner composite before introducing the shift transport.
  have hambient :=
    corrected_owner_component_ambient_expansion (S := S) (spl := spl) (h := h) n
  -- Then postcompose with the shift isomorphism and distribute over the additive decomposition.
  have hpost := congrArg
    (fun k ↦ k ≫ (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom)
    hambient
  calc
    (((((spl n).s + h n ≫ (degreewiseShortComplex S n).f) ≫ S.X₂.d n (n + 1)) ≫
        ((spl (n + 1)).r - (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1))) ≫
        (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom) =
      ((((spl n).s ≫ S.X₂.d n (n + 1) ≫ (spl (n + 1)).r) -
          ((spl n).s ≫ S.X₂.d n (n + 1) ≫
            (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1)) +
          (h n ≫ (degreewiseShortComplex S n).f ≫ S.X₂.d n (n + 1) ≫
            (spl (n + 1)).r) -
          (h n ≫ (degreewiseShortComplex S n).f ≫ S.X₂.d n (n + 1) ≫
            (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1))) ≫
          (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom) := by
            simpa [Category.assoc] using hpost
    _ =
      (((spl n).s ≫ S.X₂.d n (n + 1) ≫ (spl (n + 1)).r) ≫
          (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom) -
        (((spl n).s ≫ S.X₂.d n (n + 1) ≫
            (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1)) ≫
          (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom) +
        ((h n ≫ (degreewiseShortComplex S n).f ≫ S.X₂.d n (n + 1) ≫
            (spl (n + 1)).r) ≫
          (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom) -
        (h n ≫ (degreewiseShortComplex S n).f ≫ S.X₂.d n (n + 1) ≫
          (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1) ≫
          (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom) := by
            rw [Preadditive.sub_comp, Preadditive.add_comp, Preadditive.sub_comp]
            simp only [Category.assoc]

/-- Helper for Lemma 12.14.12: after postcomposing with the standard shift identification, the
corrected owner component is the old one plus the two textbook homotopy summands. -/
private theorem homOfDegreewiseSplit_component_postcompose_correction
    (hs : sectionDifference S spl spl' h)
    (n : ℤ) :
    (CochainComplex.homOfDegreewiseSplit S spl').f n ≫
        (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom =
      (-(show (degreewiseShortComplex S n).X₃ ⟶ S.X₁.X (n + 1) by
          simpa using (S.X₃.d n (n + 1) ≫ h (n + 1))) +
        (show (degreewiseShortComplex S n).X₃ ⟶ S.X₁.X (n + 1) by
          simpa using (h n ≫ S.X₁.d n (n + 1)))) +
        (((spl n).s ≫ S.X₂.d n (n + 1) ≫ (spl (n + 1)).r) ≫
          (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom) := by
  have hold_old_owner :
      (((spl n).s ≫ S.X₂.d n (n + 1) ≫ (spl (n + 1)).r) ≫
          (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom) =
        (CochainComplex.homOfDegreewiseSplit S spl).f n ≫
          (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom := by
    -- Rewrite the unchanged owner term once so later additive substitutions stay type-stable.
    exact congrArg
      (fun k ↦ k ≫ (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom)
      (homOfDegreewiseSplit_component (S := S) (σ := spl) n).symm
  -- Rewrite the corrected owner component using the corrected section and retraction formulas.
  calc
    (CochainComplex.homOfDegreewiseSplit S spl').f n ≫
        (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom =
      (((((spl n).s + h n ≫ (degreewiseShortComplex S n).f) ≫ S.X₂.d n (n + 1)) ≫
          ((spl (n + 1)).r - (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1))) ≫
          (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom) := by
            rw [homOfDegreewiseSplit_component (S := S) (σ := spl') n, hs n,
              retraction_eq_sub_section_correction (S := S) (spl := spl) (spl' := spl')
                (h := h) hs (n + 1)]
            simpa [Category.assoc]
    _ =
      (((spl n).s ≫ S.X₂.d n (n + 1) ≫ (spl (n + 1)).r) ≫
          (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom) -
        (((spl n).s ≫ S.X₂.d n (n + 1) ≫
            (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1)) ≫
          (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom) +
        ((h n ≫ (degreewiseShortComplex S n).f ≫ S.X₂.d n (n + 1) ≫
            (spl (n + 1)).r) ≫
          (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom) -
        (h n ≫ (degreewiseShortComplex S n).f ≫ S.X₂.d n (n + 1) ≫
          (degreewiseShortComplex S (n + 1)).g ≫ h (n + 1) ≫
          (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom) := by
            simpa using
              homOfDegreewiseSplit_postcompose_bilinear_expansion
                (S := S) (spl := spl) (h := h) n
    _ =
      (((spl n).s ≫ S.X₂.d n (n + 1) ≫ (spl (n + 1)).r) ≫
        (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom) -
        (show (degreewiseShortComplex S n).X₃ ⟶ S.X₁.X (n + 1) by
          simpa using (S.X₃.d n (n + 1) ≫ h (n + 1))) +
        (show (degreewiseShortComplex S n).X₃ ⟶ S.X₁.X (n + 1) by
          simpa using (h n ≫ S.X₁.d n (n + 1))) - 0 := by
            rw [postcompose_right_linearized_g_comm (S := S) (spl := spl) (h := h) n,
              postcompose_right_linearized_f_comm (S := S) (spl := spl) (h := h) n,
              homOfDegreewiseSplit_mixed_correction_term_vanishes (S := S) (h := h) n]
            simpa [Category.assoc]
    _ =
      (-(show (degreewiseShortComplex S n).X₃ ⟶ S.X₁.X (n + 1) by
          simpa using (S.X₃.d n (n + 1) ≫ h (n + 1))) +
        (show (degreewiseShortComplex S n).X₃ ⟶ S.X₁.X (n + 1) by
          simpa using (h n ≫ S.X₁.d n (n + 1)))) +
        (((spl n).s ≫ S.X₂.d n (n + 1) ≫ (spl (n + 1)).r) ≫
          (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom) := by
            abel

/-- Helper for Lemma 12.14.12: after postcomposing the diagonal coboundary component with the
standard shift identification, adjoining the unchanged owner term gives the final additive normal
form used in the comparison proof. -/
private theorem homOfDegreewiseSplit_difference_delta_diag_with_old_term
    (n : ℤ) :
    (show (degreewiseShortComplex S n).X₃ ⟶ S.X₁.X (n + 1) by
      simpa [Category.assoc] using
        ((CochainComplex.HomComplex.δ (-1) 0 (splitting_difference_cochain (S := S) (h := h))).v n n
          (by simp) ≫
          (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom)) +
      (((spl n).s ≫ S.X₂.d n (n + 1) ≫ (spl (n + 1)).r) ≫
        (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom) =
      (-(show (degreewiseShortComplex S n).X₃ ⟶ S.X₁.X (n + 1) by
          simpa using (S.X₃.d n (n + 1) ≫ h (n + 1))) +
        (show (degreewiseShortComplex S n).X₃ ⟶ S.X₁.X (n + 1) by
          simpa using (h n ≫ S.X₁.d n (n + 1)))) +
        (((spl n).s ≫ S.X₂.d n (n + 1) ≫ (spl (n + 1)).r) ≫
          (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom) := by
  -- Reuse the diagonal coboundary formula and then append the unchanged owner term.
  simpa [Category.assoc] using congrArg
    (fun k ↦ k +
      (((spl n).s ≫ S.X₂.d n (n + 1) ≫ (spl (n + 1)).r) ≫
        (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom))
    (homOfDegreewiseSplit_difference_delta_diag (S := S) (h := h) n)

/-- Helper for Lemma 12.14.12: the difference of the two owner connecting morphisms is the
HomComplex coboundary of the correction cochain `-h`. -/
private theorem homOfDegreewiseSplit_difference_delta
    (hs : sectionDifference S spl spl' h) :
    CochainComplex.HomComplex.Cochain.ofHom (CochainComplex.homOfDegreewiseSplit S spl') =
      CochainComplex.HomComplex.δ (-1) 0 (splitting_difference_cochain (S := S) (h := h)) +
        CochainComplex.HomComplex.Cochain.ofHom (CochainComplex.homOfDegreewiseSplit S spl) := by
  apply CochainComplex.HomComplex.Cochain.ext₀
  intro n
  -- Compare the diagonal components after postcomposing with the shift identification.
  apply (cancel_mono (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom).1
  simpa [Category.assoc, Preadditive.add_comp,
    homOfDegreewiseSplit_component (S := S) (σ := spl) n] using
    (homOfDegreewiseSplit_component_postcompose_correction
      (S := S) (spl := spl) (spl' := spl') (h := h) hs n).trans
      (homOfDegreewiseSplit_difference_delta_diag_with_old_term
        (S := S) (spl := spl) (h := h) n).symm

-- Proof sketch: the retraction correction is canonically `-h^n`, so these maps, viewed in the
-- shifted target `A^•[1]`, form the degreewise components of a homotopy from the connecting
-- morphism attached to `spl'` to the one attached to `spl`. The homotopy relation is exactly the
-- standard textbook identity for the two connecting morphisms.
/- Source/core/bridge triage:
- source-facing: correction maps comparing two degreewise splittings of the same short complex.
- core/canonical owner: `homOfDegreewiseSplit`.
- target item here: a bridge/view giving the induced homotopy between the two owner maps. -/
/-- Lemma 12.14.12: the correction maps between two degreewise splittings define a homotopy from
the connecting morphism attached to `spl'` to the one attached to `spl`. -/
@[stacks 011L]
def homOfDegreewiseSplit_homotopy_of_splitting_difference
    (hs : sectionDifference S spl spl' h) :
    Homotopy
      (CochainComplex.homOfDegreewiseSplit S spl')
      (CochainComplex.homOfDegreewiseSplit S spl) :=
  ((CochainComplex.HomComplex.Cochain.equivHomotopy
      (CochainComplex.homOfDegreewiseSplit S spl')
      (CochainComplex.homOfDegreewiseSplit S spl)).symm
    ⟨splitting_difference_cochain (S := S) (h := h),
      homOfDegreewiseSplit_difference_delta (S := S) (spl := spl) (spl' := spl') (h := h) hs⟩)

/-- The degree-`n` component of the homotopy from Lemma 12.14.12 is the correction map
`-h^n : C^n ⟶ A^n`, viewed inside the shifted target `A^•[1]`. -/
theorem homOfDegreewiseSplit_homotopy_of_splitting_difference_hom
    (hs : sectionDifference S spl spl' h)
    (n : ℤ) :
    (homOfDegreewiseSplit_homotopy_of_splitting_difference S spl spl' h hs).hom n (n - 1) ≫
        (S.X₁.shiftFunctorObjXIso 1 (n - 1) n (Int.sub_add_cancel n 1).symm).hom =
      -h n := by
  -- The homotopy is the inverse image of the correction cochain under `equivHomotopy`.
  dsimp [homOfDegreewiseSplit_homotopy_of_splitting_difference,
    CochainComplex.HomComplex.Cochain.equivHomotopy]
  split_ifs with hEq
  · simpa using Iso.inv_hom_id_assoc
      (S.X₁.shiftFunctorObjXIso 1 (n - 1) n (Int.sub_add_cancel n 1).symm)
      (-h n)
  · exfalso
    exact hEq (by omega)

end

end CochainComplex
end CategoryTheory
