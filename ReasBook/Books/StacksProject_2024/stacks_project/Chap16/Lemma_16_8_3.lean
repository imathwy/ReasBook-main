import Mathlib
import StacksProject_2024.stacks_project.Chap16.Definition_16_2_3
import StacksProject_2024.stacks_project.Chap16.Lemma_16_3_4
import StacksProject_2024.stacks_project.Chap16.Lemma_16_3_7
import StacksProject_2024.stacks_project.Chap16.Lemma_16_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalization
open scoped BigOperators

universe u v w

namespace Algebra

section

variable {R : Type u} {A : Type v} {Λ : Type w}
variable [CommRing R] [CommRing A] [CommRing Λ]
variable [Algebra R A] [Algebra R Λ] [Algebra A Λ] [IsScalarTower R A Λ]
variable [FinitePresentation R A]

section

variable (S : Submonoid R)

local notation:max "Rₛ" => Localization S
local notation:max "Aₛ" => Localization (Algebra.algebraMapSubmonoid A S)
local notation:max "Λₛ" => Localization (Algebra.algebraMapSubmonoid Λ S)
local notation:max "φ" => IsScalarTower.toAlgHom R A Λ
local notation:max "φₛ" =>
  IsLocalization.mapₐ S Rₛ Aₛ Λₛ φ

/- Domain-style sampling:
- primary domain: localized smooth commutative algebra and descent from standard smooth
  localizations to elementary standard global elements;
- sampled owner declarations:
  `Smooth`,
  `IsLocalization.mapₐ`,
  `Algebra.Smooth.exists_span_eq_top_isStandardSmooth`,
  `IsStandardSmooth`,
  `IsStandardSmooth.exists_submersivePresentation_with_prescribed_generators`;
- best owner abstraction:
  `IsElementaryStandard R` is the source-facing owner for the descended Jacobian element, while
  the localized comparison map and the standard-smooth chart on the smooth localization should be
  expressed directly by the canonical owners `IsLocalization.mapₐ` and
  `Algebra.Smooth.exists_span_eq_top_isStandardSmooth`;
- primitive vs. derived:
  primitive public data are the localized smooth factorization and the descended global
  factorization with an elementary standard element. The standard smooth refinement and
  normalized submersive presentation are proof-level bridge data extracted from the owner theorems
  `Algebra.Smooth.exists_span_eq_top_isStandardSmooth` and
  `IsStandardSmooth.exists_submersivePresentation_with_prescribed_generators`, and should not
  appear as parallel wrapper structure in the public API.

Source/core/bridge triage:
- `source-facing`: the existence of a factorization `A → B → Λ` whose distinguished element from
  `S` becomes elementary standard in `B`;
- `core/canonical`: `Smooth`, `IsElementaryStandard`, and the localized comparison morphism
  `IsLocalization.mapₐ`, together with the standard-smooth chart owner
  `Algebra.Smooth.exists_span_eq_top_isStandardSmooth`;
- `bridge/view`: the chosen standard-smooth localization chart of `B'` and the normalized
  submersive presentation used to descend the Jacobian data from the localized factorization.
-/
-- Proof sketch: apply `Algebra.Smooth.exists_span_eq_top_isStandardSmooth` to the smooth
-- `Localization S`-algebra `B'`, choose a standard-smooth localization chart whose denominator
-- comes from the image of some `s ∈ S`, and compose the given factorization through that chart.
-- Then use `IsStandardSmooth.exists_submersivePresentation_with_prescribed_generators` to choose a
-- normalized submersive presentation whose first generators come from `A`, clear denominators in
-- the extra generators, the defining equations, and the Jacobian relation, and descend the
-- presentation to a quotient `B` of a polynomial algebra over `R`. The resulting `s ∈ S` maps to
-- an elementary standard element of `B` over `R`.
/-- Helper for Lemma 16.8.3: a localized smooth factorization can first be refined through a
localized standard-smooth algebra by applying the smooth-to-standard-smooth retraction theorem
over `Localization S`. -/
lemma exists_standardSmooth_factorization_of_localized_smooth_factorization
    {B' : Type (max u v w)} [CommRing B'] [Algebra Rₛ B'] [Smooth Rₛ B']
    (f' : Aₛ →ₐ[Rₛ] B') (g' : B' →ₐ[Rₛ] Λₛ)
    (hfactor : g'.comp f' = φₛ) :
    ∃ (C : Type (max u v w)) (_ : CommRing C) (_ : Algebra Rₛ C)
      (f'' : Aₛ →ₐ[Rₛ] C) (g'' : C →ₐ[Rₛ] Λₛ),
      g''.comp f'' = φₛ ∧ IsStandardSmooth Rₛ C := by
  -- First replace the smooth localized algebra by a standard-smooth retract over `Rₛ`.
  obtain ⟨C, _, _, _, _, _, r, hstd⟩ :=
    exists_smooth_retraction_standardSmooth_of_smooth (R := Rₛ) (A := B')
  let i : B' →ₐ[Rₛ] C := IsScalarTower.toAlgHom Rₛ B' C
  let r' : C →ₐ[Rₛ] B' := AlgHom.restrictScalars Rₛ r
  have hri : r'.comp i = AlgHom.id Rₛ B' := by
    -- The retraction is `B'`-linear, so it is the identity on the image of `B'`.
    ext x
    simp [i, r']
  refine ⟨C, inferInstance, inferInstance, i.comp f', g'.comp r', ?_, hstd⟩
  -- Compose the refined factorization with the verified retraction identity.
  ext x
  simp [hri, hfactor, i, r']

/-- Helper for Lemma 16.8.3: once a descended factorization is standard smooth away from the image
of `s`, a sufficiently large power of `s` gives the required elementary-standard witness. -/
lemma exists_elementaryStandard_submonoid_power_of_standardSmoothAway
    {B : Type (max u v w)} [CommRing B] [Algebra R B]
    (s : S) (hstd : IsStandardSmooth R B[algebraMap R B s]) :
    ∃ t : S, IsElementaryStandard R (algebraMap R B t) := by
  -- Apply the away-localization theorem to the image of `s` in `B`.
  obtain ⟨e0, he0⟩ :=
    standardSmoothAway_eventually_elementaryStandard_pow (R := R) (A := B)
      (a := algebraMap R B s) hstd
  refine ⟨s ^ e0, ?_⟩
  -- Repackage the eventual elementary-standard witness as an element of the original submonoid.
  simpa [map_pow] using he0 e0 le_rfl

/-- Helper for Lemma 16.8.3: after freezing the finite presentation of `A`, a standard-smooth
`Localization S`-algebra admits a normalized submersive presentation whose first distinguished
generators are exactly the images of those frozen generators under the localized factorization. -/
lemma exists_normalizedLocalizedSubmersivePresentation
    {C : Type (max u v w)} [CommRing C] [Algebra Rₛ C] [IsStandardSmooth Rₛ C]
    (f'' : Aₛ →ₐ[Rₛ] C) :
    ∃ (c m : ℕ) (Q : SubmersivePresentation Rₛ C (Fin c ⊕ Fin m) (Fin c))
      (h : Presentation.ofFinitePresentationVars R A ≤ c),
      Q.map = Sum.inl ∧
        ∀ i : Fin (Presentation.ofFinitePresentationVars R A),
          Q.val (.inl (Fin.castLE h i)) =
            f'' (algebraMap A Aₛ ((Presentation.ofFinitePresentation R A).val i)) := by
  -- Freeze the generator family coming from the chosen finite presentation of `A`.
  simpa using
    (IsStandardSmooth.exists_submersivePresentation_with_prescribed_family
      (R := Rₛ) (A := C)
      (β := fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
        f'' (algebraMap A Aₛ ((Presentation.ofFinitePresentation R A).val i))))

/-- Helper for Lemma 16.8.3: a finite family of elements in a scalar localization admits one
common denominator from `S`. This is the denominator package needed for the extra-generator images
and later for the finitely many coefficient families coming from the localized chart data. -/
lemma exists_commonDenominator_of_fintype_scalarLocalizationFamily
    {T : Type*} [CommRing T] [Algebra R T]
    {Tₛ : Type*} [CommRing Tₛ] [Algebra R Tₛ] [Algebra T Tₛ] [IsScalarTower R T Tₛ]
    [IsLocalization (Algebra.algebraMapSubmonoid T S) Tₛ]
    {ι : Type*} [Fintype ι] (x : ι → Tₛ) :
    ∃ s : S, ∃ num : ι → T,
      ∀ i, algebraMap T Tₛ (num i) = algebraMap R Tₛ (s : R) * x i := by
  classical
  let frac : ι → T × Algebra.algebraMapSubmonoid T S := fun i ↦
    Classical.choose (IsLocalization.surj (Algebra.algebraMapSubmonoid T S) (x i))
  have hfracMem : ∀ i, ((frac i).2 : T) ∈ Algebra.algebraMapSubmonoid T S := fun i ↦
    (frac i).2.2
  let den : ι → S := fun i ↦
    ⟨Classical.choose ((Submonoid.mem_map).1 (hfracMem i)),
      (Classical.choose_spec ((Submonoid.mem_map).1 (hfracMem i))).1⟩
  have hden : ∀ i, algebraMap R T (den i : R) = ((frac i).2 : T) := fun i ↦
    (Classical.choose_spec ((Submonoid.mem_map).1 (hfracMem i))).2
  let s : S := ∏ i, den i
  refine ⟨s, fun i ↦ (frac i).1 *
      algebraMap R T (((Finset.univ.erase i).prod fun j ↦ (den j : R))), ?_⟩
  intro i
  -- First rewrite the chosen local denominator as the image of an element of `S`.
  have hfrac :
      x i * algebraMap T Tₛ ((frac i).2 : T) = algebraMap T Tₛ ((frac i).1) :=
    Classical.choose_spec (IsLocalization.surj (Algebra.algebraMapSubmonoid T S) (x i))
  have hdenMap :
      algebraMap T Tₛ ((frac i).2 : T) = algebraMap R Tₛ (den i : R) := by
    rw [← hden i]
    simp [IsScalarTower.algebraMap_eq R T Tₛ]
  have hprod :
      algebraMap T Tₛ ((frac i).2 : T) *
          ((Finset.univ.erase i).prod fun j ↦ algebraMap R Tₛ (den j : R)) =
        algebraMap R Tₛ (s : R) := by
    calc
      algebraMap T Tₛ ((frac i).2 : T) *
          ((Finset.univ.erase i).prod fun j ↦ algebraMap R Tₛ (den j : R))
          = algebraMap R Tₛ (den i : R) *
              ((Finset.univ.erase i).prod fun j ↦ algebraMap R Tₛ (den j : R)) := by
              rw [hdenMap]
      _ = ∏ j, algebraMap R Tₛ (den j : R) := by
            exact
              Finset.mul_prod_erase Finset.univ
                (fun j ↦ algebraMap R Tₛ (den j : R)) (by simp)
      _ = algebraMap R Tₛ (s : R) := by
            simp [s, map_prod]
  -- Then multiply the individual denominator formula by the complementary product.
  calc
    algebraMap T Tₛ
        ((frac i).1 * algebraMap R T (((Finset.univ.erase i).prod fun j ↦ (den j : R)))) =
        algebraMap T Tₛ ((frac i).1) *
          ((Finset.univ.erase i).prod fun j ↦ algebraMap R Tₛ (den j : R)) := by
            simp [map_prod, IsScalarTower.algebraMap_eq R T Tₛ]
    _ = (x i * algebraMap T Tₛ ((frac i).2 : T)) *
          ((Finset.univ.erase i).prod fun j ↦ algebraMap R Tₛ (den j : R)) := by
            rw [← hfrac]
    _ = x i * algebraMap R Tₛ (s : R) := by
          rw [mul_assoc, hprod]
    _ = algebraMap R Tₛ (s : R) * x i := by
          rw [mul_comm]

/-- Helper for Lemma 16.8.3: a finite family of localized multivariable polynomials admits one
common denominator from `S`. This is the coefficientwise version of the scalar denominator
package needed to clear the finitely many localized chart equations at once. -/
lemma exists_commonDenominator_of_fintype_localizedPolynomialFamily
    {σ ι : Type*} [Fintype ι] (u : ι → MvPolynomial σ Rₛ) :
    ∃ s : S, ∃ uLift : ι → MvPolynomial σ R,
      ∀ i, MvPolynomial.map (algebraMap R Rₛ) (uLift i) =
        algebraMap R (MvPolynomial σ Rₛ) (s : R) * u i := by
  -- View `MvPolynomial σ Rₛ` as the localization of `MvPolynomial σ R` at the image of `S`.
  simpa using
    (exists_commonDenominator_of_fintype_scalarLocalizationFamily
      (R := R) (S := S) (T := MvPolynomial σ R) (Tₛ := MvPolynomial σ Rₛ) u)

/-- Helper for Lemma 16.8.3: applying a localized target map after evaluating a polynomial in a
normalized localized chart agrees with evaluating directly at the mapped chart values. -/
lemma map_submersivePresentation_aeval
    {C : Type*} [CommRing C] [Algebra Rₛ C]
    {σ τ : Type*} (Q : SubmersivePresentation Rₛ C σ τ) (g : C →ₐ[Rₛ] Λₛ) :
    ∀ p : MvPolynomial σ Rₛ,
      MvPolynomial.aeval (fun i ↦ g (Q.val i)) p = g (MvPolynomial.aeval Q.val p) := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C a =>
      -- Constants commute with the localized target map because `g` is an `Rₛ`-algebra map.
      simpa using g.commutes a
  | add p q hp hq =>
      -- Addition is preserved by both multivariable evaluation and the target algebra map.
      simpa [map_add] using congrArg₂ (fun x y ↦ x + y) hp hq
  | mul_X p i hp =>
      -- Multiplication by a variable evaluates at the chosen chart value `g (Q.val i)`.
      simpa [MvPolynomial.aeval_def, map_mul] using
        congrArg (fun x ↦ x * g (Q.val i)) hp

/-- Helper for Lemma 16.8.3: once the localized chart relations are cleared coefficientwise, they
already vanish in `Λₛ` under evaluation at the normalized chart values. -/
lemma relationLift_aeval_eq_zero_in_localizedTarget
    {C : Type*} [CommRing C] [Algebra Rₛ C]
    (g : C →ₐ[Rₛ] Λₛ)
    {c m : ℕ} (Q : SubmersivePresentation Rₛ C (Fin c ⊕ Fin m) (Fin c))
    (sRelation : S)
    (relationLift : Fin c → MvPolynomial (Fin c ⊕ Fin m) R)
    (hRelationLift :
      ∀ i, MvPolynomial.map (algebraMap R Rₛ) (relationLift i) =
        algebraMap R (MvPolynomial (Fin c ⊕ Fin m) Rₛ) (sRelation : R) * Q.relation i) :
    ∀ i : Fin c, MvPolynomial.aeval (fun j ↦ g (Q.val j)) (relationLift i) = 0 := by
  intro i
  have hQrel :
      MvPolynomial.aeval (fun j ↦ g (Q.val j)) (Q.relation i) = 0 := by
    -- First collapse evaluation through `g`, then use that each defining relation is already in
    -- the kernel of the chart quotient map.
    calc
      MvPolynomial.aeval (fun j ↦ g (Q.val j)) (Q.relation i) =
          g (MvPolynomial.aeval Q.val (Q.relation i)) := by
            simpa using
              map_submersivePresentation_aeval
                (R := R) (A := A) (Λ := Λ) (S := S) Q g (Q.relation i)
      _ = 0 := by
            have hker : MvPolynomial.aeval Q.val (Q.relation i) = 0 := by
              simpa [Q.algebraMap_apply, RingHom.mem_ker] using Q.relation_mem_ker i
            simp [hker]
  have hlocal :
      MvPolynomial.aeval (fun j ↦ g (Q.val j))
          (MvPolynomial.map (algebraMap R Rₛ) (relationLift i)) = 0 := by
    -- Rewrite the cleared lift as a scalar multiple of the original relation and use the
    -- vanishing of `Q.relation i` at the chart values.
    calc
      MvPolynomial.aeval (fun j ↦ g (Q.val j))
          (MvPolynomial.map (algebraMap R Rₛ) (relationLift i)) =
        MvPolynomial.aeval (fun j ↦ g (Q.val j))
          (algebraMap R (MvPolynomial (Fin c ⊕ Fin m) Rₛ) (sRelation : R) * Q.relation i) := by
            rw [hRelationLift i]
      _ = algebraMap R Λₛ (sRelation : R) *
            MvPolynomial.aeval (fun j ↦ g (Q.val j)) (Q.relation i) := by
            simp [MvPolynomial.aeval_def, map_mul]
      _ = 0 := by simp [hQrel]
  -- Finally forget the intermediate coefficient localization on the cleared relation lift.
  exact
    (MvPolynomial.aeval_map_algebraMap
      (R := R) (A := Rₛ) (B := Λₛ) (x := fun j ↦ g (Q.val j)) (relationLift i)).symm.trans
      hlocal

/-- Helper for Lemma 16.8.3: the ideal generated by the cleared localized chart relations is sent
to zero in `Λₛ` under evaluation at the normalized chart values. -/
lemma clearedChartRelationIdeal_le_ker_localizedTargetEval
    {C : Type*} [CommRing C] [Algebra Rₛ C]
    (g : C →ₐ[Rₛ] Λₛ)
    {c m : ℕ} (Q : SubmersivePresentation Rₛ C (Fin c ⊕ Fin m) (Fin c))
    (sRelation : S)
    (relationLift : Fin c → MvPolynomial (Fin c ⊕ Fin m) R)
    (hRelationLift :
      ∀ i, MvPolynomial.map (algebraMap R Rₛ) (relationLift i) =
        algebraMap R (MvPolynomial (Fin c ⊕ Fin m) Rₛ) (sRelation : R) * Q.relation i) :
    Ideal.span (Set.range relationLift) ≤
      RingHom.ker
        ((MvPolynomial.aeval (fun j ↦ g (Q.val j)) :
          MvPolynomial (Fin c ⊕ Fin m) R →ₐ[R] Λₛ).toRingHom) := by
  -- The span is generated by the finitely many cleared relations, and each generator already
  -- vanishes by the previous helper.
  refine Ideal.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  simpa [RingHom.mem_ker] using
    relationLift_aeval_eq_zero_in_localizedTarget
      (R := R) (A := A) (Λ := Λ) (S := S) g Q sRelation relationLift hRelationLift i

/-- Helper for Lemma 16.8.3: the cleared localized chart quotient still carries a canonical map to
`Λₛ` through the normalized chart values. -/
noncomputable def clearedChartQuotientToLocalizedTarget
    {C : Type*} [CommRing C] [Algebra Rₛ C]
    (g : C →ₐ[Rₛ] Λₛ)
    {c m : ℕ} (Q : SubmersivePresentation Rₛ C (Fin c ⊕ Fin m) (Fin c))
    (sRelation : S)
    (relationLift : Fin c → MvPolynomial (Fin c ⊕ Fin m) R)
    (hRelationLift :
      ∀ i, MvPolynomial.map (algebraMap R Rₛ) (relationLift i) =
        algebraMap R (MvPolynomial (Fin c ⊕ Fin m) Rₛ) (sRelation : R) * Q.relation i) :
    (MvPolynomial (Fin c ⊕ Fin m) R ⧸ Ideal.span (Set.range relationLift)) →ₐ[R] Λₛ :=
  Ideal.Quotient.liftₐ (R₁ := R) (I := Ideal.span (Set.range relationLift))
    (MvPolynomial.aeval (fun j ↦ g (Q.val j)))
    (clearedChartRelationIdeal_le_ker_localizedTargetEval
      (R := R) (A := A) (Λ := Λ) (S := S) g Q sRelation relationLift hRelationLift)

/-- Helper for Lemma 16.8.3: the cleared global chart quotient cut out only by the lifted local
relations. -/
noncomputable abbrev clearedChartQuotient {c m : ℕ}
    (relationLift : Fin c → MvPolynomial (Fin c ⊕ Fin m) R) : Type u :=
  MvPolynomial (Fin c ⊕ Fin m) R ⧸ Ideal.span (Set.range relationLift)

/-- Helper for Lemma 16.8.3: the naive presentation of the cleared global chart quotient, using
the first `c` variables as the distinguished Jacobian block. -/
noncomputable def clearedChartPresentation {c m : ℕ}
    (relationLift : Fin c → MvPolynomial (Fin c ⊕ Fin m) R) :
    PreSubmersivePresentation R
      (clearedChartQuotient (R := R) relationLift)
      (Fin c ⊕ Fin m) (Fin c) :=
  PreSubmersivePresentation.naive Sum.inl Sum.inl_injective
    (Function.surjInv Ideal.Quotient.mk_surjective)
    (Function.surjInv_eq Ideal.Quotient.mk_surjective)

/-- Helper for Lemma 16.8.3: localizing the cleared chart quotient away from its Jacobian class is
standard smooth over `R`. -/
lemma standardSmoothAway_of_clearedChartPresentation
    {c m : ℕ} (relationLift : Fin c → MvPolynomial (Fin c ⊕ Fin m) R) :
    IsStandardSmooth R
      (Localization.Away
        (clearedChartPresentation (R := R) relationLift).jacobian) := by
  classical
  let P := clearedChartPresentation (R := R) relationLift
  -- Localizing away from the Jacobian adjoins the inverse needed for the standard-smooth chart.
  let Q :
      SubmersivePresentation
        (clearedChartQuotient (R := R) relationLift)
        (Localization.Away P.jacobian) Unit Unit :=
    SubmersivePresentation.localizationAway (Localization.Away P.jacobian) P.jacobian
  let PQ :
      SubmersivePresentation R (Localization.Away P.jacobian)
        (Sum Unit (Fin c ⊕ Fin m)) (Sum Unit (Fin c)) :=
    { toPreSubmersivePresentation :=
        PreSubmersivePresentation.comp Q.toPreSubmersivePresentation P
      jacobian_isUnit := by
        -- The old Jacobian is invertible after adjoining its inverse.
        have hP :
            IsUnit
              (algebraMap (clearedChartQuotient (R := R) relationLift)
                (Localization.Away P.jacobian) P.jacobian) :=
          IsLocalization.map_units _ (⟨P.jacobian, 1, by simp⟩ : Submonoid.powers P.jacobian)
        have hQ : IsUnit (hP.unit • Q.jacobian) :=
          Q.jacobian_isUnit.smul hP.unit
        show IsUnit
          (PreSubmersivePresentation.comp Q.toPreSubmersivePresentation P).jacobian
        rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian]
        convert hQ using 1
        exact Algebra.smul_def P.jacobian Q.jacobian }
  -- The composed presentation is the canonical standard-smooth chart over `R`.
  simpa [P] using PQ.isStandardSmooth

/-- Helper for Lemma 16.8.3: once an ideal of an `R`-algebra dies after localizing away from
`g`, the away localization identifies with the away localization of the quotient by that ideal. -/
noncomputable lemma localizationAway_quotient_algEquiv_of_map_eq_bot
    {B : Type*} [CommRing B] [Algebra R B] (I : Ideal B) (g : B)
    (hbot : Ideal.map (algebraMap B (Localization.Away g)) I = ⊥) :
    Localization.Away g ≃ₐ[R] Localization.Away (Ideal.Quotient.mk I g) := by
  classical
  let eQuot := Classical.choice <|
    Ideal.quotient_localizationAway_algEquiv (R := B) (I := I) (g := g)
  let eBot :
      Localization.Away g ≃ₐ[B]
        ((Localization.Away g) ⧸ Ideal.map (algebraMap B (Localization.Away g)) I) := by
    -- Once the extended ideal is zero, quotienting by it is the identity quotient.
    exact hbot ▸ (AlgEquiv.quotientBot B (Localization.Away g)).symm
  let eBotR :
      Localization.Away g ≃ₐ[R]
        ((Localization.Away g) ⧸ Ideal.map (algebraMap B (Localization.Away g)) I) :=
    AlgEquiv.restrictScalars R eBot
  let eQuotR :
      ((Localization.Away g) ⧸ Ideal.map (algebraMap B (Localization.Away g)) I) ≃ₐ[R]
        Localization.Away (Ideal.Quotient.mk I g) :=
    AlgEquiv.restrictScalars R eQuot
  -- Compose the quotient-by-`⊥` collapse with the canonical quotient/localization comparison.
  exact eBotR.trans eQuotR

/-- Helper for Lemma 16.8.3: on the frozen presentation generators of `A`, the normalized
localized chart values agree with the canonical localized target map `Aₛ → Λₛ`. -/
lemma normalizedChartValue_eq_localizedTarget_of_sourceGenerator
    {C : Type (max u v w)} [CommRing C] [Algebra Rₛ C]
    (f'' : Aₛ →ₐ[Rₛ] C) (g'' : C →ₐ[Rₛ] Λₛ)
    (hfactor : g''.comp f'' = φₛ)
    {c m : ℕ} (Q : SubmersivePresentation Rₛ C (Fin c ⊕ Fin m) (Fin c))
    (hQ : Presentation.ofFinitePresentationVars R A ≤ c)
    (hQval :
      ∀ i : Fin (Presentation.ofFinitePresentationVars R A),
        Q.val (.inl (Fin.castLE hQ i)) =
          f'' (algebraMap A Aₛ ((Presentation.ofFinitePresentation R A).val i))) :
    ∀ i : Fin (Presentation.ofFinitePresentationVars R A),
      g'' (Q.val (.inl (Fin.castLE hQ i))) =
        algebraMap Aₛ Λₛ (algebraMap A Aₛ ((Presentation.ofFinitePresentation R A).val i)) := by
  intro i
  -- First rewrite the frozen chart coordinate through the chosen source generator.
  rw [hQval i]
  -- Then collapse the composed factorization `Aₛ → C → Λₛ` back to the canonical map.
  exact congrArg
    (fun h : Aₛ →ₐ[Rₛ] Λₛ =>
      h (algebraMap A Aₛ ((Presentation.ofFinitePresentation R A).val i)))
    hfactor

/-- Helper for Lemma 16.8.3: the defining relations of the frozen presentation of `A` already
vanish in `Λₛ` when evaluated at the normalized localized chart values. -/
lemma sourcePresentationRelation_aeval_eq_zero_in_localizedTarget
    {C : Type (max u v w)} [CommRing C] [Algebra Rₛ C]
    (f'' : Aₛ →ₐ[Rₛ] C) (g'' : C →ₐ[Rₛ] Λₛ)
    (hfactor : g''.comp f'' = φₛ)
    {c m : ℕ} (Q : SubmersivePresentation Rₛ C (Fin c ⊕ Fin m) (Fin c))
    (hQ : Presentation.ofFinitePresentationVars R A ≤ c)
    (hQval :
      ∀ i : Fin (Presentation.ofFinitePresentationVars R A),
        Q.val (.inl (Fin.castLE hQ i)) =
          f'' (algebraMap A Aₛ ((Presentation.ofFinitePresentation R A).val i))) :
    ∀ j : Fin (Presentation.ofFinitePresentationRels R A),
      MvPolynomial.aeval
          (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
            g'' (Q.val (.inl (Fin.castLE hQ i))))
          ((Presentation.ofFinitePresentation R A).relation j) = 0 := by
  intro j
  let P_A :
      Presentation R A
        (Fin (Presentation.ofFinitePresentationVars R A))
        (Fin (Presentation.ofFinitePresentationRels R A)) :=
    Presentation.ofFinitePresentation R A
  have hvals :
      (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
        g'' (Q.val (.inl (Fin.castLE hQ i)))) =
      (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
        algebraMap Aₛ Λₛ (algebraMap A Aₛ (P_A.val i))) := by
    -- The frozen chart coordinates are exactly the localized source generators.
    funext i
    simpa [P_A] using
      normalizedChartValue_eq_localizedTarget_of_sourceGenerator
        (R := R) (A := A) (Λ := Λ) (S := S) f'' g'' hfactor Q hQ hQval i
  -- Rewrite evaluation through the canonical localized image of the fixed presentation.
  rw [hvals]
  calc
    MvPolynomial.aeval
        (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
          algebraMap Aₛ Λₛ (algebraMap A Aₛ (P_A.val i)))
        (P_A.relation j)
        =
      algebraMap Aₛ Λₛ
        (MvPolynomial.aeval (fun i ↦ algebraMap A Aₛ (P_A.val i)) (P_A.relation j)) := by
          symm
          simpa [P_A, IsScalarTower.algebraMap_eq R A Aₛ] using
            (MvPolynomial.aeval_map_algebraMap
              (R := R) (A := Aₛ) (B := Λₛ)
              (x := fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
                algebraMap A Aₛ (P_A.val i))
              (P_A.relation j))
    _ = 0 := by
          -- The frozen presentation relations already lie in the kernel of the presentation map.
          have hker :
              MvPolynomial.aeval (fun i ↦ algebraMap A Aₛ (P_A.val i)) (P_A.relation j) = 0 := by
            simpa [P_A.algebraMap_apply, RingHom.mem_ker] using P_A.relation_mem_ker j
          simp [hker]

/-- Helper for Lemma 16.8.3: after renaming the frozen presentation relations of `A` into the
full normalized chart variable set, they still vanish in `Λₛ`. -/
lemma renamedSourcePresentationRelation_aeval_eq_zero_in_localizedTarget
    {C : Type (max u v w)} [CommRing C] [Algebra Rₛ C]
    (f'' : Aₛ →ₐ[Rₛ] C) (g'' : C →ₐ[Rₛ] Λₛ)
    (hfactor : g''.comp f'' = φₛ)
    {c m : ℕ} (Q : SubmersivePresentation Rₛ C (Fin c ⊕ Fin m) (Fin c))
    (hQ : Presentation.ofFinitePresentationVars R A ≤ c)
    (hQval :
      ∀ i : Fin (Presentation.ofFinitePresentationVars R A),
        Q.val (.inl (Fin.castLE hQ i)) =
          f'' (algebraMap A Aₛ ((Presentation.ofFinitePresentation R A).val i))) :
    ∀ j : Fin (Presentation.ofFinitePresentationRels R A),
      MvPolynomial.aeval (fun i : Fin c ⊕ Fin m ↦ g'' (Q.val i))
          (MvPolynomial.rename (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
            Sum.inl (Fin.castLE hQ i))
            ((Presentation.ofFinitePresentation R A).relation j)) = 0 := by
  intro j
  -- Evaluating a renamed frozen relation on the big chart matches evaluation on the frozen block.
  rw [MvPolynomial.aeval_rename]
  exact
    sourcePresentationRelation_aeval_eq_zero_in_localizedTarget
      (R := R) (A := A) (Λ := Λ) (S := S) f'' g'' hfactor Q hQ hQval j

/-- Helper for Lemma 16.8.3: after renaming the frozen presentation relations of `A` into a
larger global chart, they already vanish in `Λ` as soon as the frozen block is identified with
the actual images of the fixed presentation generators. -/
lemma renamedSourcePresentationRelation_aeval_eq_zero_in_target
    {c m : ℕ}
    (λDesc : Fin c ⊕ Fin m → Λ)
    (hQ : Presentation.ofFinitePresentationVars R A ≤ c)
    (hFrozen :
      ∀ i : Fin (Presentation.ofFinitePresentationVars R A),
        λDesc (.inl (Fin.castLE hQ i)) =
          algebraMap A Λ ((Presentation.ofFinitePresentation R A).val i)) :
    ∀ j : Fin (Presentation.ofFinitePresentationRels R A),
      MvPolynomial.aeval λDesc
          (MvPolynomial.rename (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
            Sum.inl (Fin.castLE hQ i))
            ((Presentation.ofFinitePresentation R A).relation j)) = 0 := by
  intro j
  let P_A :
      Presentation R A
        (Fin (Presentation.ofFinitePresentationVars R A))
        (Fin (Presentation.ofFinitePresentationRels R A)) :=
    Presentation.ofFinitePresentation R A
  -- Evaluating the renamed frozen relation on the big chart is the same as evaluating it on the
  -- frozen source-generator block.
  rw [MvPolynomial.aeval_rename]
  have hvals :
      (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
        λDesc (.inl (Fin.castLE hQ i))) =
      (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
        algebraMap A Λ (P_A.val i)) := by
    -- The frozen coordinates are exactly the images of the fixed presentation generators of `A`.
    funext i
    simpa [P_A] using hFrozen i
  rw [hvals]
  calc
    MvPolynomial.aeval
        (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
          algebraMap A Λ (P_A.val i))
        (P_A.relation j) =
      algebraMap A Λ
        (MvPolynomial.aeval (fun i ↦ P_A.val i) (P_A.relation j)) := by
          symm
          simpa [P_A] using
            (MvPolynomial.aeval_map_algebraMap
              (R := R) (A := A) (B := Λ)
              (x := fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦ P_A.val i)
              (P_A.relation j))
    _ = 0 := by
          -- The defining relations of the chosen finite presentation already lie in the kernel of
          -- its presentation algebra map.
          have hker :
              MvPolynomial.aeval (fun i ↦ P_A.val i) (P_A.relation j) = 0 := by
            simpa [P_A.algebraMap_apply, RingHom.mem_ker] using P_A.relation_mem_ker j
          simp [hker]

/-- Helper for Lemma 16.8.3: after cutting out the cleared chart relations, the renamed source
relations of the frozen finite presentation of `A` generate a canonical second quotient ideal. -/
noncomputable def sourceRelationIdealInClearedChart
    {c m : ℕ} (hQ : Presentation.ofFinitePresentationVars R A ≤ c)
    (relationLift : Fin c → MvPolynomial (Fin c ⊕ Fin m) R) :
    Ideal (clearedChartQuotient (R := R) relationLift) :=
  Ideal.span (Set.range fun j : Fin (Presentation.ofFinitePresentationRels R A) ↦
    Ideal.Quotient.mk (Ideal.span (Set.range relationLift))
      (MvPolynomial.rename (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
        Sum.inl (Fin.castLE hQ i))
        ((Presentation.ofFinitePresentation R A).relation j)))

/-- Helper for Lemma 16.8.3: the canonical localized target map on the cleared chart quotient also
kills the renamed source relations, so it descends through the second quotient. -/
lemma sourceRelationIdealInClearedChart_le_ker_localizedTarget
    {C : Type (max u v w)} [CommRing C] [Algebra Rₛ C]
    (f'' : Aₛ →ₐ[Rₛ] C) (g'' : C →ₐ[Rₛ] Λₛ)
    (hfactor : g''.comp f'' = φₛ)
    {c m : ℕ} (Q : SubmersivePresentation Rₛ C (Fin c ⊕ Fin m) (Fin c))
    (hQ : Presentation.ofFinitePresentationVars R A ≤ c)
    (hQval :
      ∀ i : Fin (Presentation.ofFinitePresentationVars R A),
        Q.val (.inl (Fin.castLE hQ i)) =
          f'' (algebraMap A Aₛ ((Presentation.ofFinitePresentation R A).val i)))
    (sRelation : S)
    (relationLift : Fin c → MvPolynomial (Fin c ⊕ Fin m) R)
    (hRelationLift :
      ∀ i, MvPolynomial.map (algebraMap R Rₛ) (relationLift i) =
        algebraMap R (MvPolynomial (Fin c ⊕ Fin m) Rₛ) (sRelation : R) * Q.relation i) :
    sourceRelationIdealInClearedChart (R := R) (A := A) hQ relationLift ≤
      RingHom.ker
        ((clearedChartQuotientToLocalizedTarget
          (R := R) (A := A) (Λ := Λ) (S := S) g'' Q sRelation
          relationLift hRelationLift).toRingHom) := by
  -- The second quotient is generated by the renamed frozen source relations, and each such
  -- generator already vanishes under the localized target evaluation on the normalized chart.
  refine Ideal.span_le.2 ?_
  rintro _ ⟨j, rfl⟩
  rw [RingHom.mem_ker]
  -- Expand the descended map once, then reuse the frozen-source vanishing lemma.
  rw [clearedChartQuotientToLocalizedTarget, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  simpa using
    renamedSourcePresentationRelation_aeval_eq_zero_in_localizedTarget
      (R := R) (A := A) (Λ := Λ) (S := S) f'' g'' hfactor Q hQ hQval j

/-- Helper for Lemma 16.8.3: the localized target map on the cleared chart quotient descends
through the additional quotient by the renamed source relations of `A`. -/
noncomputable def descendedChartQuotientToLocalizedTarget
    {C : Type (max u v w)} [CommRing C] [Algebra Rₛ C]
    (f'' : Aₛ →ₐ[Rₛ] C) (g'' : C →ₐ[Rₛ] Λₛ)
    (hfactor : g''.comp f'' = φₛ)
    {c m : ℕ} (Q : SubmersivePresentation Rₛ C (Fin c ⊕ Fin m) (Fin c))
    (hQ : Presentation.ofFinitePresentationVars R A ≤ c)
    (hQval :
      ∀ i : Fin (Presentation.ofFinitePresentationVars R A),
        Q.val (.inl (Fin.castLE hQ i)) =
          f'' (algebraMap A Aₛ ((Presentation.ofFinitePresentation R A).val i)))
    (sRelation : S)
    (relationLift : Fin c → MvPolynomial (Fin c ⊕ Fin m) R)
    (hRelationLift :
      ∀ i, MvPolynomial.map (algebraMap R Rₛ) (relationLift i) =
        algebraMap R (MvPolynomial (Fin c ⊕ Fin m) Rₛ) (sRelation : R) * Q.relation i) :
    (clearedChartQuotient (R := R) relationLift ⧸
      sourceRelationIdealInClearedChart (R := R) (A := A) hQ relationLift) →ₐ[R] Λₛ :=
  Ideal.Quotient.liftₐ
    (R₁ := R)
    (I := sourceRelationIdealInClearedChart (R := R) (A := A) hQ relationLift)
    (clearedChartQuotientToLocalizedTarget
      (R := R) (A := A) (Λ := Λ) (S := S) g'' Q sRelation relationLift hRelationLift)
    (fun x hx ↦
      RingHom.mem_ker.mp <|
        sourceRelationIdealInClearedChart_le_ker_localizedTarget
          (R := R) (A := A) (Λ := Λ) (S := S) f'' g'' hfactor Q hQ hQval
          sRelation relationLift hRelationLift hx)

/-- Lemma 16.8.3: from a factorization of the localized map `S⁻¹A → S⁻¹Λ` through a smooth
`Localization S`-algebra, one can descend to a factorization `A → B → Λ` such that some
`s ∈ S` maps to an elementary standard element of `B` over `R`. -/
theorem exists_factorization_with_elementaryStandard_of_localized_smooth_factorization
    {B' : Type (max u v w)} [CommRing B'] [Algebra Rₛ B'] [Smooth Rₛ B']
    (f' : Aₛ →ₐ[Rₛ] B') (g' : B' →ₐ[Rₛ] Λₛ)
    (hfactor : g'.comp f' = φₛ) :
    ∃ (B : Type (max u v w)) (_ : CommRing B) (_ : Algebra R B)
      (f : A →ₐ[R] B) (g : B →ₐ[R] Λ) (s : S),
      g.comp f = φ ∧
      IsElementaryStandard R (algebraMap R B s) := by
  -- First reduce to the case where the localized target is already standard smooth.
  obtain ⟨C, _, _, f'', g'', hfactor'', hstdC⟩ :=
    exists_standardSmooth_factorization_of_localized_smooth_factorization
      (R := R) (A := A) (Λ := Λ) (S := S) f' g' hfactor
  obtain ⟨c, m, Q, hQ, hQmap, hQval⟩ :=
    exists_normalizedLocalizedSubmersivePresentation
      (R := R) (A := A) (Λ := Λ) (S := S) (f'' := f'')
  let chartValue : Fin c ⊕ Fin m → Λₛ := fun i ↦ g'' (Q.val i)
  obtain ⟨sChart, chartLift, hChartLift⟩ :=
    exists_commonDenominator_of_fintype_scalarLocalizationFamily
      (R := R) (S := S) (T := Λ) chartValue
  obtain ⟨sRelation, relationLift, hRelationLift⟩ :=
    exists_commonDenominator_of_fintype_localizedPolynomialFamily
      (R := R) (S := S) (u := Q.relation)
  -- Route correction: the localized target is now normalized against the frozen presentation of
  -- `A`, so the remaining work is the finite denominator-clearing/global quotient step.
  -- All chart variables now have one common denominator `sChart`, so the residual generator lifts
  -- needed for the quotient map `B →ₐ[R] Λ` are frozen explicitly in `chartLift`.
  -- The localized chart equations also have one common denominator `sRelation`, recorded by
  -- `relationLift`; this is the first exact polynomial package needed for the descended quotient.
  have hRelationEval :
      ∀ i : Fin c, MvPolynomial.aeval chartValue (relationLift i) = 0 := by
    -- The coefficient-cleared localized chart relations already vanish in `Λₛ`.
    simpa [chartValue] using
      relationLift_aeval_eq_zero_in_localizedTarget
        (R := R) (A := A) (Λ := Λ) (S := S) g'' Q sRelation relationLift hRelationLift
  let localizedQuotientToTarget :
      (MvPolynomial (Fin c ⊕ Fin m) R ⧸ Ideal.span (Set.range relationLift)) →ₐ[R] Λₛ :=
    clearedChartQuotientToLocalizedTarget
      (R := R) (A := A) (Λ := Λ) (S := S) g'' Q sRelation relationLift hRelationLift
  have hRenamedSourceEval :
      ∀ j : Fin (Presentation.ofFinitePresentationRels R A),
        MvPolynomial.aeval chartValue
            (MvPolynomial.rename (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
              Sum.inl (Fin.castLE hQ i))
              ((Presentation.ofFinitePresentation R A).relation j)) = 0 := by
    -- The frozen presentation relations of `A` already vanish on the normalized localized chart.
    simpa [chartValue] using
      renamedSourcePresentationRelation_aeval_eq_zero_in_localizedTarget
        (R := R) (A := A) (Λ := Λ) (S := S) f'' g'' hfactor'' Q hQ hQval
  have hstdCleared :
      IsStandardSmooth R
        (Localization.Away (clearedChartPresentation (R := R) relationLift).jacobian) := by
    -- The intermediate quotient cut out only by the cleared chart relations is standard smooth
    -- after inverting its Jacobian class.
    simpa using
      standardSmoothAway_of_clearedChartPresentation
        (R := R) (relationLift := relationLift)
  have hSourceRelationIdeal :
      sourceRelationIdealInClearedChart (R := R) (A := A) hQ relationLift ≤
        RingHom.ker (localizedQuotientToTarget.toRingHom) := by
    -- The localized target map on the cleared chart quotient already kills the renamed source
    -- relations, so it descends one quotient further.
    simpa [localizedQuotientToTarget] using
      sourceRelationIdealInClearedChart_le_ker_localizedTarget
        (R := R) (A := A) (Λ := Λ) (S := S) f'' g'' hfactor'' Q hQ hQval
        sRelation relationLift hRelationLift
  let descendedQuotientToTarget :
      (clearedChartQuotient (R := R) relationLift ⧸
        sourceRelationIdealInClearedChart (R := R) (A := A) hQ relationLift) →ₐ[R] Λₛ :=
    descendedChartQuotientToLocalizedTarget
      (R := R) (A := A) (Λ := Λ) (S := S) f'' g'' hfactor'' Q hQ hQval
      sRelation relationLift hRelationLift
  let _ := hRelationEval
  let _ := localizedQuotientToTarget
  let _ := hRenamedSourceEval
  let _ := hstdCleared
  let _ := hSourceRelationIdeal
  let _ := descendedQuotientToTarget
  let _ := sChart
  let _ := chartLift
  let _ := hChartLift
  let _ := hQmap
  let _ := hstdC
  have hRenamedSourceEvalTarget :
      ∀ λDesc : Fin c ⊕ Fin m → Λ,
        (∀ i : Fin (Presentation.ofFinitePresentationVars R A),
          λDesc (.inl (Fin.castLE hQ i)) =
            algebraMap A Λ ((Presentation.ofFinitePresentation R A).val i)) →
        ∀ j : Fin (Presentation.ofFinitePresentationRels R A),
          MvPolynomial.aeval λDesc
              (MvPolynomial.rename (fun i : Fin (Presentation.ofFinitePresentationVars R A) ↦
                Sum.inl (Fin.castLE hQ i))
                ((Presentation.ofFinitePresentation R A).relation j)) = 0 := by
    intro λDesc hFrozen
    -- The source relations already vanish in `Λ` once the frozen source block is fixed there.
    exact
      renamedSourcePresentationRelation_aeval_eq_zero_in_target
        (R := R) (A := A) (Λ := Λ) (S := S) λDesc hQ hFrozen
  let _ := hRenamedSourceEvalTarget
  -- The verified frontier is now the canonical localized quotient map built from the cleared
  -- chart equations, the frozen source relations already vanish on the same localized chart, the
  -- localized target map descends through the extra quotient by those raw source relations, and
  -- the intermediate cleared quotient is standard smooth away from its Jacobian class.
  -- Route correction: the remaining gap is no longer target-side well-definedness for the raw
  -- source relations; that quotient step is now isolated by
  -- `sourceRelationIdealInClearedChart_le_ker_localizedTarget` and
  -- `descendedChartQuotientToLocalizedTarget`. The only missing step is the rescaled descent of
  -- the localized chart equations and Jacobian identity from `Λₛ` back to `Λ`.
  -- TODO: the remaining blocker is the genuinely global descent step. One still has to
  -- homogenize the `Λₛ`-valued chart data to a quotient over `R` mapping to `Λ`, clear one
  -- Jacobian inverse relation from `Q.jacobian_isUnit` using a denominator from `S`, prove that
  -- the second quotient ideal dies after localizing away that denominator, and transport the
  -- standard-smooth-away chart across the resulting quotient-away equivalence before applying
  -- `exists_elementaryStandard_submonoid_power_of_standardSmoothAway` to the descended quotient.
  sorry

end

end

end Algebra
