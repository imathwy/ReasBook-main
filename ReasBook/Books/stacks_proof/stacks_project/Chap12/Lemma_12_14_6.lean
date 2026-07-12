import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape HomologicalComplex

universe v u

namespace ChainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜]

/-- The degree-`n` short complex attached to a short complex of chain complexes. -/
abbrev degreewiseShortComplex (S : ShortComplex (ChainComplex 𝒜 ℤ)) (n : ℤ) :=
  S.map (eval 𝒜 (ComplexShape.down ℤ) n)

variable (S : ShortComplex (ChainComplex 𝒜 ℤ))
variable (σ σ' : ∀ n : ℤ, (degreewiseShortComplex S n).Splitting)
variable
  (h : ∀ n : ℤ, (degreewiseShortComplex S n).X₃ ⟶ (degreewiseShortComplex S n).X₁)

noncomputable section

private abbrev transportedShortComplex :
    ShortComplex (CochainComplex 𝒜 ℤ) :=
  ((cochainComplexEquivalence 𝒜).functor).mapShortComplex.obj S

private abbrev transportedSplitting
    (σ : ∀ n : ℤ, (degreewiseShortComplex S n).Splitting) :
    ∀ n : ℤ, ((transportedShortComplex S).map (eval 𝒜 (up ℤ) n)).Splitting :=
  fun n ↦ show ((transportedShortComplex S).map (eval 𝒜 (up ℤ) n)).Splitting from σ (-n)

private def shiftMinusOneComparison :
    (((cochainComplexEquivalence 𝒜).functor.obj S.X₁)⟦(1 : ℤ)⟧) ⟶
      (cochainComplexEquivalence 𝒜).functor.obj (S.X₁⟦(-1 : ℤ)⟧) :=
  let hEq : (((cochainComplexEquivalence 𝒜).functor.obj S.X₁)⟦(1 : ℤ)⟧) =
      (shiftFunctor (PullbackShift (CochainComplex 𝒜 ℤ) (negAddMonoidHom : ℤ →+ ℤ))
        (-1 : ℤ)).obj (((cochainComplexEquivalence 𝒜).functor).obj S.X₁) :=
    rfl
  eqToHom hEq ≫ (((cochainComplexEquivalence 𝒜).functor.commShiftIso (-1 : ℤ)).app S.X₁).symm.hom

/-- Helper for Lemma 12.14.6: the comparison from the cochain shift `[1]` to the chain shift
`[-1]` has the expected degreewise component. -/
private theorem shiftMinusOneComparison_component
    (n : ℤ) :
    (shiftMinusOneComparison (S := S)).f (-n) ≫
        ((S.X₁⟦(-1 : ℤ)⟧).XIsoOfEq (by simp)).hom ≫
        (shiftMinusOneXIso S.X₁ n).hom =
      (((cochainComplexEquivalence 𝒜).functor.obj S.X₁).shiftFunctorObjXIso 1
        (-n) (-n + 1) (by omega)).hom := by
  simp only [shiftMinusOneComparison, transportedShortComplex, Category.assoc]

/-- The canonical degree isomorphism from `(K⟦-1⟧).X n` to `K.X (n - 1)`. -/
abbrev shiftMinusOneXIso (K : ChainComplex 𝒜 ℤ) (n : ℤ) :
    (K⟦(-1 : ℤ)⟧).X n ≅ K.X (n - 1) :=
  eqToIso (by simp)

/-- The canonical degree isomorphism from `(K⟦-1⟧).X (n + 1)` to `K.X n`. -/
abbrev shiftMinusOneSuccXIso (K : ChainComplex 𝒜 ℤ) (n : ℤ) :
    (K⟦(-1 : ℤ)⟧).X (n + 1) ≅ K.X n :=
  eqToIso (by simp)

/-- Helper for Lemma 12.14.6: the degreewise split connecting morphism for chain complexes is
obtained by transporting the cochain owner construction through `cochainComplexEquivalence`. -/
def homOfDegreewiseSplit
    (σ : ∀ n : ℤ, (degreewiseShortComplex S n).Splitting) :
    S.X₃ ⟶ S.X₁⟦(-1 : ℤ)⟧ :=
  let F : ChainComplex 𝒜 ℤ ⥤ PullbackShift (CochainComplex 𝒜 ℤ)
      (negAddMonoidHom : ℤ →+ ℤ) :=
    show ChainComplex 𝒜 ℤ ⥤ PullbackShift (CochainComplex 𝒜 ℤ)
        (negAddMonoidHom : ℤ →+ ℤ) from
      (cochainComplexEquivalence 𝒜).functor
  let T := ((cochainComplexEquivalence 𝒜).functor).mapShortComplex.obj S
  let τ : ∀ m : ℤ, (T.map (eval 𝒜 (up ℤ) m)).Splitting :=
    fun m ↦ show (T.map (eval 𝒜 (up ℤ) m)).Splitting from σ (-m)
  let hEq : (((cochainComplexEquivalence 𝒜).functor.obj S.X₁)⟦(1 : ℤ)⟧) =
      (shiftFunctor (PullbackShift (CochainComplex 𝒜 ℤ) (negAddMonoidHom : ℤ →+ ℤ))
        (-1 : ℤ)).obj (F.obj S.X₁) :=
    rfl
  let e :
      (((cochainComplexEquivalence 𝒜).functor.obj S.X₁)⟦(1 : ℤ)⟧) ⟶
        (cochainComplexEquivalence 𝒜).functor.obj (S.X₁⟦(-1 : ℤ)⟧) :=
    eqToHom hEq ≫
      ((show shiftFunctor (ChainComplex 𝒜 ℤ) (-1 : ℤ) ⋙ F ≅
          F ⋙
            shiftFunctor (PullbackShift (CochainComplex 𝒜 ℤ)
              (negAddMonoidHom : ℤ →+ ℤ)) (-1 : ℤ)
        from
          F.commShiftIso (-1 : ℤ)).app S.X₁).symm.hom
  ((cochainComplexEquivalence 𝒜).functor).preimage <|
    (show T.X₃ ⟶ (((cochainComplexEquivalence 𝒜).functor.obj S.X₁)⟦(1 : ℤ)⟧) from
      CochainComplex.homOfDegreewiseSplit T τ) ≫ e

/-- Helper for Lemma 12.14.6: after identifying `(A⟦-1⟧).X n` with `A.X (n - 1)`, the
degree-`n` component of `homOfDegreewiseSplit` is `s_n ≫ d_B ≫ r_{n-1}`. -/
@[simp] theorem homOfDegreewiseSplit_f
    (σ : ∀ n : ℤ, (degreewiseShortComplex S n).Splitting)
    (n : ℤ) :
    (homOfDegreewiseSplit (S := S) σ).f n ≫
        (shiftMinusOneXIso S.X₁ n).hom =
      (σ n).s ≫ S.X₂.d n (n - 1) ≫ (σ (n - 1)).r := by
  let T := transportedShortComplex (S := S)
  let τ := transportedSplitting (S := S) σ
  let e := shiftMinusOneComparison (S := S)
  calc
    (homOfDegreewiseSplit (S := S) σ).f n ≫ (shiftMinusOneXIso S.X₁ n).hom =
      ((cochainComplexEquivalence 𝒜).functor.map (homOfDegreewiseSplit (S := S) σ)).f (-n) ≫
          ((S.X₁⟦(-1 : ℤ)⟧).XIsoOfEq (by simp)).hom ≫
          (shiftMinusOneXIso S.X₁ n).hom := by
            rfl
    _ = (CochainComplex.homOfDegreewiseSplit T τ).f (-n) ≫
          (((cochainComplexEquivalence 𝒜).functor.obj S.X₁).shiftFunctorObjXIso 1
            (-n) (-n + 1) (by omega)).hom := by
          simp only [homOfDegreewiseSplit, T, τ, e, Functor.map_preimage, Functor.map_comp,
            HomologicalComplex.comp_f, Category.assoc]
          rw [shiftMinusOneComparison_component (S := S)]
    _ = (σ n).s ≫ S.X₂.d n (n - 1) ≫ (σ (n - 1)).r := by
          simpa [T, τ, Category.assoc] using
            (CochainComplex.homOfDegreewiseSplit_f T τ (-n))

/-- Helper for Lemma 12.14.6: the corrected retraction still retracts the degreewise map `f`. -/
private theorem corrected_degreewise_retraction_f_r
    (n : ℤ) :
    (degreewiseShortComplex S n).f ≫
        ((σ n).r - (degreewiseShortComplex S n).g ≫ h n) = 𝟙 _ := by
  rw [Preadditive.comp_sub, (σ n).f_r, (degreewiseShortComplex S n).zero_assoc]
  rw [sub_zero]

/-- Helper for Lemma 12.14.6: the corrected section and retraction still split the degreewise
short complex. -/
private theorem corrected_degreewise_identity
    (hs_eq : ∀ n : ℤ, (σ' n).s = (σ n).s + h n ≫ (degreewiseShortComplex S n).f)
    (n : ℤ) :
    ((σ n).r - (degreewiseShortComplex S n).g ≫ h n) ≫ (degreewiseShortComplex S n).f +
        (degreewiseShortComplex S n).g ≫ (σ' n).s = 𝟙 _ := by
  calc
    ((σ n).r - (degreewiseShortComplex S n).g ≫ h n) ≫ (degreewiseShortComplex S n).f +
        (degreewiseShortComplex S n).g ≫ (σ' n).s =
      (σ n).r ≫ (degreewiseShortComplex S n).f +
        (degreewiseShortComplex S n).g ≫ (σ n).s := by
          rw [hs_eq n, Preadditive.sub_comp, Preadditive.comp_add, Category.assoc]
          abel
    _ = 𝟙 _ := (σ n).id

/-- Helper for Lemma 12.14.6: modifying the degreewise section by `h_n ≫ f_n` changes the
degreewise retraction by `- g_n ≫ h_n`. -/
private abbrev corrected_degreewise_splitting
    (hs_eq : ∀ n : ℤ, (σ' n).s = (σ n).s + h n ≫ (degreewiseShortComplex S n).f)
    (n : ℤ) :
    (degreewiseShortComplex S n).Splitting where
  r := (σ n).r - (degreewiseShortComplex S n).g ≫ h n
  s := (σ' n).s
  f_r := corrected_degreewise_retraction_f_r (S := S) (σ := σ) (h := h) n
  s_g := (σ' n).s_g
  id := corrected_degreewise_identity (S := S) (σ := σ) (σ' := σ') (h := h) hs_eq n

/-- Helper for Lemma 12.14.6: the retraction attached to the second splitting is
`r_n - g_n ≫ h_n`. -/
private theorem retraction_eq_sub_section_correction
    (hs_eq : ∀ n : ℤ, (σ' n).s = (σ n).s + h n ≫ (degreewiseShortComplex S n).f)
    (n : ℤ) :
    (σ' n).r = (σ n).r - (degreewiseShortComplex S n).g ≫ h n := by
  let τ := corrected_degreewise_splitting (S := S) (σ := σ) (σ' := σ') (h := h) hs_eq n
  have hτ : τ = σ' n := ShortComplex.Splitting.ext_s τ (σ' n) rfl
  simpa [τ] using (congrArg ShortComplex.Splitting.r hτ).symm

/-- Helper for Lemma 12.14.6: the homotopy family is `h_n`, viewed in the shifted target
`A[-1]_{n + 1}`. -/
private abbrev splitting_difference_homotopy_hom :
    ∀ n m, (ComplexShape.down ℤ).Rel m n →
      S.X₃.X n ⟶ (S.X₁⟦(-1 : ℤ)⟧).X m :=
  fun n m hnm ↦
    h n ≫
      (shiftMinusOneSuccXIso S.X₁ n).inv ≫
      eqToHom (congrArg (fun i ↦ (S.X₁⟦(-1 : ℤ)⟧).X i) (ChainComplex.prev ℤ n).symm) ≫
      ((S.X₁⟦(-1 : ℤ)⟧).xPrevIso hnm).hom

/-- Helper for Lemma 12.14.6: on the canonical successor relation, the homotopy family is
exactly `h_n` into the shifted target. -/
@[simp] private theorem splitting_difference_homotopy_hom_apply
    (n : ℤ) :
    splitting_difference_homotopy_hom S h n (n + 1) (ComplexShape.down_mk (n + 1) n rfl) =
      h n ≫ (shiftMinusOneSuccXIso S.X₁ n).inv := by
  simp [splitting_difference_homotopy_hom]

/-- Helper for Lemma 12.14.6: the predecessor component of the homotopy family recovers
`h_{n-1}` after the standard shift identification. -/
private theorem splitting_difference_homotopy_hom_prev
    (n : ℤ) :
    splitting_difference_homotopy_hom S h (n - 1) n
        (ComplexShape.down_mk n (n - 1) (Int.sub_add_cancel n 1)) ≫
        (shiftMinusOneXIso S.X₁ n).hom =
      h (n - 1) := by
  simp [splitting_difference_homotopy_hom, shiftMinusOneSuccXIso, Category.assoc]

/-- Helper for Lemma 12.14.6: the successor component of the homotopy family followed by the
shifted differential is `- h_n ≫ d_A`. -/
private theorem splitting_difference_homotopy_hom_next
    (n : ℤ) :
    splitting_difference_homotopy_hom S h n (n + 1)
        (ComplexShape.down_mk (n + 1) n rfl) ≫
        (S.X₁⟦(-1 : ℤ)⟧).d (n + 1) n ≫
        (shiftMinusOneXIso S.X₁ n).hom =
      -(h n ≫ S.X₁.d n (n - 1)) := by
  simp [splitting_difference_homotopy_hom, shiftMinusOneSuccXIso, shiftMinusOneXIso,
    Category.assoc]

/-- Helper for Lemma 12.14.6: the mixed correction term vanishes because `f ≫ g = 0`. -/
private theorem homOfDegreewiseSplit_mixed_correction_term_vanishes
    (n : ℤ) :
    h n ≫ (degreewiseShortComplex S n).f ≫ S.X₂.d n (n - 1) ≫
        (degreewiseShortComplex S (n - 1)).g ≫ h (n - 1) = 0 := by
  have hcomm :
      h n ≫ (degreewiseShortComplex S n).f ≫ S.X₂.d n (n - 1) ≫
          (degreewiseShortComplex S (n - 1)).g ≫ h (n - 1) =
        h n ≫ S.X₁.d n (n - 1) ≫ (degreewiseShortComplex S (n - 1)).f ≫
          (degreewiseShortComplex S (n - 1)).g ≫ h (n - 1) := by
    simpa [Category.assoc] using congrArg
      (fun k ↦ h n ≫ k ≫ (degreewiseShortComplex S (n - 1)).g ≫ h (n - 1))
      ((S.f.comm n (n - 1)).symm)
  calc
    h n ≫ (degreewiseShortComplex S n).f ≫ S.X₂.d n (n - 1) ≫
        (degreewiseShortComplex S (n - 1)).g ≫ h (n - 1) =
      h n ≫ S.X₁.d n (n - 1) ≫ (degreewiseShortComplex S (n - 1)).f ≫
        (degreewiseShortComplex S (n - 1)).g ≫ h (n - 1) := hcomm
    _ = h n ≫ S.X₁.d n (n - 1) ≫ 0 ≫ h (n - 1) := by
          simpa [Category.assoc] using congrArg
            (fun k ↦ h n ≫ S.X₁.d n (n - 1) ≫ k ≫ h (n - 1))
            ((degreewiseShortComplex S (n - 1)).zero)
    _ = 0 := by simp [Category.assoc]

/-- Helper for Lemma 12.14.6: after postcomposing with the standard shift identification, the
difference `δ(σ) - δ(σ')` is the usual null-homotopic expression. -/
private theorem homOfDegreewiseSplit_sub_component
    (hs_eq : ∀ n : ℤ, (σ' n).s = (σ n).s + h n ≫ (degreewiseShortComplex S n).f)
    (n : ℤ) :
    ((homOfDegreewiseSplit S σ - homOfDegreewiseSplit S σ').f n) ≫
        (shiftMinusOneXIso S.X₁ n).hom =
      S.X₃.d n (n - 1) ≫ h (n - 1) - h n ≫ S.X₁.d n (n - 1) := by
  have hsection :
      (σ n).s ≫ S.X₂.d n (n - 1) ≫
          (degreewiseShortComplex S (n - 1)).g ≫ h (n - 1) =
        S.X₃.d n (n - 1) ≫ h (n - 1) := by
    simpa [Category.assoc] using congrArg
      (fun k ↦ (σ n).s ≫ k ≫ h (n - 1))
      (S.g.comm n (n - 1))
  have hretraction :
      h n ≫ (degreewiseShortComplex S n).f ≫
          S.X₂.d n (n - 1) ≫ (σ (n - 1)).r =
        h n ≫ S.X₁.d n (n - 1) := by
    simpa [Category.assoc] using congrArg
      (fun k ↦ h n ≫ k ≫ (σ (n - 1)).r)
      ((S.f.comm n (n - 1)).symm)
  rw [HomologicalComplex.sub_f, Preadditive.sub_comp]
  rw [homOfDegreewiseSplit_f, homOfDegreewiseSplit_f]
  rw [hs_eq n]
  rw [retraction_eq_sub_section_correction (S := S) (σ := σ) (σ' := σ') (h := h) hs_eq (n - 1)]
  calc
    (σ n).s ≫ S.X₂.d n (n - 1) ≫ (σ (n - 1)).r -
        ((σ n).s + h n ≫ (degreewiseShortComplex S n).f) ≫
          S.X₂.d n (n - 1) ≫
          ((σ (n - 1)).r - (degreewiseShortComplex S (n - 1)).g ≫ h (n - 1)) =
      (σ n).s ≫ S.X₂.d n (n - 1) ≫
          (degreewiseShortComplex S (n - 1)).g ≫ h (n - 1) -
        h n ≫ (degreewiseShortComplex S n).f ≫ S.X₂.d n (n - 1) ≫
          (σ (n - 1)).r +
        h n ≫ (degreewiseShortComplex S n).f ≫ S.X₂.d n (n - 1) ≫
          (degreewiseShortComplex S (n - 1)).g ≫ h (n - 1) := by
            simp [Category.assoc, Preadditive.comp_add, Preadditive.add_comp,
              Preadditive.comp_sub, Preadditive.sub_comp]
            abel
    _ = S.X₃.d n (n - 1) ≫ h (n - 1) - h n ≫ S.X₁.d n (n - 1) := by
          rw [hsection, hretraction,
            homOfDegreewiseSplit_mixed_correction_term_vanishes
              (S := S) (σ := σ) (h := h) n]
          abel

/-- Helper for Lemma 12.14.6: the standard `nullHomotopicMap'` built from the correction family
has the same components as `δ(σ) - δ(σ')`. -/
private theorem nullHomotopicMap_component
    (n : ℤ) :
    (Homotopy.nullHomotopicMap' (splitting_difference_homotopy_hom S h)).f n ≫
        (shiftMinusOneXIso S.X₁ n).hom =
      S.X₃.d n (n - 1) ≫ h (n - 1) - h n ≫ S.X₁.d n (n - 1) := by
  rw [Homotopy.nullHomotopicMap'_f
    (ComplexShape.down_mk (n + 1) n rfl)
    (ComplexShape.down_mk n (n - 1) (Int.sub_add_cancel n 1))]
  rw [Preadditive.add_comp]
  rw [Category.assoc]
  rw [splitting_difference_homotopy_hom_prev (S := S) (h := h) n]
  rw [splitting_difference_homotopy_hom_next (S := S) (h := h) n]
  abel

/-- Helper for Lemma 12.14.6: the difference of the two connecting morphisms is the canonical
null-homotopic map built from the family `h_n`. -/
private theorem homOfDegreewiseSplit_sub_eq_nullHomotopicMap
    (hs_eq : ∀ n : ℤ, (σ' n).s = (σ n).s + h n ≫ (degreewiseShortComplex S n).f) :
    homOfDegreewiseSplit S σ - homOfDegreewiseSplit S σ' =
      Homotopy.nullHomotopicMap' (splitting_difference_homotopy_hom S h) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply (cancel_mono ((shiftMinusOneXIso S.X₁ n).hom)).1
  simpa [Category.assoc] using
    (homOfDegreewiseSplit_sub_component (S := S) (σ := σ) (σ' := σ') (h := h) hs_eq n).trans
      (nullHomotopicMap_component (S := S) (h := h) n).symm

-- Proof sketch: write `δ(σ) - δ(σ')` as the null-homotopic map determined by the degreewise
-- family `h_n : C_n ⟶ A_n`, viewed in the shifted target `A[-1]`.
/-- Lemma 12.14.6: if a second degreewise splitting differs from the first by maps
`h_n : C_n ⟶ A_n`, then these maps, viewed as morphisms `C_n ⟶ A[-1]_{n + 1}`, give a chain
homotopy between the associated connecting morphisms. -/
@[stacks 011F]
def homOfDegreewiseSplit_homotopy_of_splitting_difference
    (hs_eq : ∀ n : ℤ, (σ' n).s = (σ n).s + h n ≫ (degreewiseShortComplex S n).f) :
    Homotopy
      (homOfDegreewiseSplit S σ)
      (homOfDegreewiseSplit S σ') := by
  refine (Homotopy.equivSubZero
    (f := homOfDegreewiseSplit S σ)
    (g := homOfDegreewiseSplit S σ')).symm ?_
  refine (Homotopy.ofEq
    (homOfDegreewiseSplit_sub_eq_nullHomotopicMap
      (S := S) (σ := σ) (σ' := σ') (h := h) hs_eq)).trans ?_
  exact Homotopy.nullHomotopy' (splitting_difference_homotopy_hom S h)

/-- The homotopy of Lemma 12.14.6 has degree-`n` component given by the correction map
`h_n : C_n ⟶ A_n`, viewed in the shifted target `A[-1]`. -/
theorem homOfDegreewiseSplit_homotopy_of_splitting_difference_hom
    (hs_eq : ∀ n : ℤ, (σ' n).s = (σ n).s + h n ≫ (degreewiseShortComplex S n).f)
    (n : ℤ) :
    (homOfDegreewiseSplit_homotopy_of_splitting_difference
        S σ σ' h hs_eq).hom n (n + 1) ≫
        (shiftMinusOneSuccXIso S.X₁ n).hom =
      h n := by
  simp [homOfDegreewiseSplit_homotopy_of_splitting_difference,
    splitting_difference_homotopy_hom_apply, Category.assoc]

end

end ChainComplex
