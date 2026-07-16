import stacks_proof.stacks_project.Chap13.Definition_13_8_1
import stacks_proof.stacks_project.Chap13.Lemma_13_35_7
import stacks_proof.stacks_project.Chap10.Lemma_10_75_8
import stacks_proof.stacks_project.Chap15.Definition_15_59_1
import stacks_proof.stacks_project.Chap15.Definition_15_67_1
import stacks_proof.stacks_project.Chap15.Lemma_15_66_6
import stacks_proof.stacks_project.Chap15.Lemma_15_59_14
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open DerivedCategory
open ModuleCat.MonoidalCategory
open scoped DerivedTensorProduct

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "Q" => (DerivedCategory.Q : CochainComplex (ModuleCat R) ℤ ⥤ DMod)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/-- Helper for Lemma 15.67.2: the quotient functor `Q` carries its standard monoidal structure. -/
private noncomputable instance quotientFunctorMonoidal :
    (DerivedCategory.Q : CochainComplex (ModuleCat R) ℤ ⥤ DMod).Monoidal := by
  change (((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)) ⋙
      (DerivedCategory.Qh :
        HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ) ⥤ DMod))).Monoidal
  infer_instance

namespace CochainComplex

/- Domain-style sampling:
- primary domain: lower-bounded tor-amplitude in `D(R)` and the source-facing flatness of the
  syzygy `cokernel (K.dFrom (a - 1))` of a bounded-above flat cochain representative;
- sampled owner declarations:
  `HasTorAmplitudeGE`,
  `CochainComplex.IsKFlat`,
  `CochainComplex.IsTermwiseFlat`,
  `CochainComplex.minus`;
- source/core/bridge triage:
  `source-facing`: flatness of `cokernel (K.dFrom (a - 1))` under the source hypotheses on `K`;
  `core/canonical`: the chapter owners `HasTorAmplitudeGE (Q.obj K) a`, `K.IsKFlat`,
    `K.IsTermwiseFlat`, and `CochainComplex.minus (ModuleCat R) K`;
  `bridge/view`: exactness of the degree-zero tensor complexes computing lower tor-amplitude once
    `K` is known to be K-flat.

Primitive data are the bounded-above hypothesis on `K`, its termwise flatness, and the canonical
derived owner `HasTorAmplitudeGE (Q.obj K) a`. The exactness statements after tensoring with
degree-zero modules are derived bridge data, while representative-level K-flatness is supplied by
the existing bridge theorem `CochainComplex.isKFlat_of_boundedAbove_of_flat` rather than by any
parallel local wrapper.
-/

-- Proof sketch: apply `CochainComplex.isKFlat_of_boundedAbove_of_flat` to compute the derived
-- tensor products on the representative `K`. The tor-amplitude hypothesis gives vanishing of the
-- degree-`a - 1` tensor homology after tensoring with each quotient `R ⧸ I`. The remaining
-- source-faithful step is to identify that homology with `Tor₁` of
-- `cokernel (K.dFrom (a - 1))`; once this is done, Lemma `10.75.8` finishes the flatness proof
-- from the quotient-ideal criterion.
/-- Helper for Lemma 15.67.2: vanishing of `Tor_1^R(C, R ⧸ I)` for every ideal `I` forces `C`
to be flat. -/
lemma flat_of_tor_one_quotient_vanishing
    (C : ModuleCat R)
    (hTor : ∀ I : Ideal R,
      IsZero ((((Tor (ModuleCat R) 1).obj C).obj (ModuleCat.of R (R ⧸ I))))) :
    Module.Flat R (C : Type u) := by
  -- Repackage the quotient-side `Tor₁`-vanishing into the Chapter 10 flatness criterion.
  have hTFAE :
      List.TFAE
        [ Module.Flat R (C : Type u),
          ∀ i : ℕ, 0 < i → ∀ N : ModuleCat R,
            IsZero ((((Tor (ModuleCat R) i).obj C).obj N)),
          ∀ N : ModuleCat R, IsZero ((((Tor (ModuleCat R) 1).obj C).obj N)),
          ∀ I : Ideal R,
            IsZero ((((Tor (ModuleCat R) 1).obj C).obj (ModuleCat.of R (R ⧸ I)))),
          ∀ I : Ideal R, I.FG →
            IsZero ((((Tor (ModuleCat R) 1).obj C).obj (ModuleCat.of R (R ⧸ I)))) ] := by
    simpa using flat_tfae_tor_vanishing_criteria (R := R) (M := (C : Type u))
  -- The fourth clause of the `TFAE` is exactly the quotient-ideal hypothesis.
  exact (hTFAE.out 0 3).2 hTor

/-- Helper for Lemma 15.67.2: lower tor-amplitude gives vanishing of the degree-`i` homology of
`K \otimes_R^{\mathbf L} M[0]` whenever `i < a`. -/
lemma tensor_homology_isZero_of_hasTorAmplitudeGE
    (K : DerivedCategory (ModuleCat R)) (a i : ℤ)
    (hTor : HasTorAmplitudeGE K a) (M : ModuleCat R) (hi : i < a) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      (K ⊗[R]^L ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M))) := by
  -- Unfold the tor-amplitude owner and translate `IsGE` into homology vanishing below `a`.
  have hGE :
      (K ⊗[R]^L ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)).IsGE a :=
    hTor M
  rw [DerivedCategory.isGE_iff] at hGE
  exact hGE i hi

/-- Helper for Lemma 15.67.2: after tensoring with a degree-zero module, shifting the left factor
by `n` shifts the homology degree by `n`. -/
noncomputable def homology_tensor_single_shift_iso
    (K : DMod) (M : ModuleCat R) (i n : ℤ) :
    (H i).obj ((K⟦n⟧) ⊗[R]^L (single₀).obj M) ≅
      (H (i + n)).obj (K ⊗[R]^L (single₀).obj M) :=
  let e₁ :
      ((K⟦n⟧) ⊗[R]^L (single₀).obj M) ≅
        (K ⊗[R]^L (single₀).obj M)⟦n⟧ :=
    ((derivedTensorProduct_commShift ((single₀).obj M)).commShiftIso n).app K
  let e₂ :
      (H i).obj ((K ⊗[R]^L (single₀).obj M)⟦n⟧) ≅
        (H (i + n)).obj (K ⊗[R]^L (single₀).obj M) :=
    ((H 0).shiftIso n i (i + n) (add_comm n i)).app
      (K ⊗[R]^L (single₀).obj M)
  -- Compare tensoring after shift with shifting after tensoring, then rewrite homology of a shift.
  (H i).mapIso e₁ ≪≫ e₂

/-- Helper for Lemma 15.67.2: the degree-`a - 1` tensor homology of `C[a]` against `N[0]` is the
degree-`-1` tensor homology of `C[0]` against `N[0]`. -/
noncomputable def single_shifted_tensor_homology_iso
    (C N : ModuleCat R) (a : ℤ) :
    (H (a - 1)).obj
        (((DerivedCategory.singleFunctor (ModuleCat R) a).obj C) ⊗[R]^L (single₀).obj N) ≅
      (H (-1)).obj
        (((single₀).obj C) ⊗[R]^L (single₀).obj N) :=
  let eShift :
      (H (-1)).obj
          ((((DerivedCategory.singleFunctor (ModuleCat R) a).obj C)⟦a⟧) ⊗[R]^L
            (single₀).obj N) ≅
        (H (a - 1)).obj
          (((DerivedCategory.singleFunctor (ModuleCat R) a).obj C) ⊗[R]^L
            (single₀).obj N) := by
    -- Normalize the shifted homology degree from `-1 + a` to `a - 1`.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      homology_tensor_single_shift_iso (R := R)
        ((DerivedCategory.singleFunctor (ModuleCat R) a).obj C) N (-1) a
  let eSingle :
      (((DerivedCategory.singleFunctor (ModuleCat R) a).obj C)⟦a⟧) ≅
        (single₀).obj C :=
    ((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso a 0 a (by simp)).app C
  -- Route correction: isolate the shift transport first, so the remaining Tor comparison only has
  -- to handle the degree-zero single complex `C[0]`.
  eShift.symm ≪≫
    (H (-1)).mapIso ((derivedTensorProduct ((single₀).obj N)).mapIso eSingle)

/-- Helper for Lemma 15.67.2: a degree `i ≤ a` lies in the image of the upper truncation embedding
`n ↦ a - n`. -/
private theorem embeddingUpIntLE_toNat_sub_eq
    (a i : ℤ) (hi : i ≤ a) :
    (ComplexShape.embeddingUpIntLE a).f (Int.toNat (a - i)) = i := by
  -- The difference `a - i` is nonnegative on the retained upper-truncation range.
  dsimp [ComplexShape.embeddingUpIntLE]
  rw [Int.toNat_of_nonneg]
  · omega
  · omega

/-- Helper for Lemma 15.67.2: in a cochain complex, the predecessor of degree `i` is `i - 1`. -/
private theorem cochain_prev_eq (i : ℤ) :
    (ComplexShape.up ℤ).prev i = i - 1 :=
  ComplexShape.prev_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])

/-- Helper for Lemma 15.67.2: in a cochain complex, the successor of degree `i` is `i + 1`. -/
private theorem cochain_next_eq (i : ℤ) :
    (ComplexShape.up ℤ).next i = i + 1 :=
  ComplexShape.next_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])

/-- Helper for Lemma 15.67.2: on each retained degree of the upper stupid truncation, the stage
term canonically identifies with the original term of `K`. -/
noncomputable def upper_stupid_truncation_x_iso
    (K : CochainComplex (ModuleCat R) ℤ) (a : ℤ) {i : ℤ} (hi : i ≤ a) :
    (K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).X i ≅ K.X i := by
  let j : ℕ := Int.toNat (a - i)
  have hj : (ComplexShape.embeddingUpIntLE a).f j = i :=
    embeddingUpIntLE_toNat_sub_eq a i hi
  -- On the retained upper range, `stupidTrunc` is just the original complex.
  exact K.stupidTruncXIso (ComplexShape.embeddingUpIntLE a) hj

/-- Helper for Lemma 15.67.2: after identifying retained degrees with the source terms of `K`,
the top differential of the upper stupid truncation is the original differential of `K`. -/
lemma upper_stupid_truncation_d_via_x_iso
    (K : CochainComplex (ModuleCat R) ℤ) (a : ℤ) {i j : ℤ}
    (hi : i ≤ a) (hj : j ≤ a) :
    (upper_stupid_truncation_x_iso (R := R) K a hi).inv ≫
      (K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).d i j ≫
      (upper_stupid_truncation_x_iso (R := R) K a hj).hom =
        K.d i j := by
  let e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ) :=
    ComplexShape.embeddingUpIntLE a
  let i₀ : ℕ := Int.toNat (a - i)
  let j₀ : ℕ := Int.toNat (a - j)
  have hi₀ : e.f i₀ = i := embeddingUpIntLE_toNat_sub_eq a i hi
  have hj₀ : e.f j₀ = j := embeddingUpIntLE_toNat_sub_eq a j hj
  -- First peel off the `extend` differential, then the `restriction` differential.
  change (upper_stupid_truncation_x_iso (R := R) K a hi).inv ≫
      ((K.restriction e).extend e).d i j ≫
      (upper_stupid_truncation_x_iso (R := R) K a hj).hom =
        K.d i j
  rw [HomologicalComplex.extend_d_eq (K := K.restriction e) (e := e) hi₀ hj₀]
  rw [HomologicalComplex.restriction_d_eq (K := K) (e := e) hi₀ hj₀]
  simp [upper_stupid_truncation_x_iso, HomologicalComplex.stupidTrunc,
    HomologicalComplex.stupidTruncXIso, HomologicalComplex.restrictionXIso,
    e, i₀, j₀]

/-- Helper for Lemma 15.67.2: below the cutoff, the degree-`i` short complex of the upper stupid
truncation is canonically the same short complex as the degree-`i` short complex of `K`. -/
private noncomputable def upper_stupid_truncation_sc_iso_of_lt_aux
    (K : CochainComplex (ModuleCat R) ℤ) (a i : ℤ) (hia : i < a) :
    (K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).sc i ≅ K.sc i := by
  have hi_prev : i - 1 ≤ a := by omega
  have hi_mid : i ≤ a := le_of_lt hia
  have hi_next : i + 1 ≤ a := by omega
  -- The source proof works degreewise on the three-term short complex around `i`.
  refine ShortComplex.isoMk
    (by
      simpa [HomologicalComplex.sc, CochainComplex.prev, cochain_prev_eq] using
        (upper_stupid_truncation_x_iso (R := R) (K := K) (a := a) (i := i - 1) hi_prev))
    (upper_stupid_truncation_x_iso (R := R) K a hi_mid)
    (by
      simpa [HomologicalComplex.sc, CochainComplex.next, cochain_next_eq] using
        (upper_stupid_truncation_x_iso (R := R) (K := K) (a := a) (i := i + 1) hi_next))
    ?_ ?_
  · -- The left differential is unchanged after transporting through the retained-degree
    -- identifications.
    have hd :
        (K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).d (i - 1) i ≫
            (upper_stupid_truncation_x_iso (R := R) K a hi_mid).hom =
          (upper_stupid_truncation_x_iso (R := R) (K := K) (a := a) (i := i - 1) hi_prev).hom ≫
            K.d (i - 1) i := by
      calc
        (K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).d (i - 1) i ≫
            (upper_stupid_truncation_x_iso (R := R) K a hi_mid).hom =
          (upper_stupid_truncation_x_iso (R := R) (K := K) (a := a) (i := i - 1) hi_prev).hom ≫
            ((upper_stupid_truncation_x_iso (R := R) (K := K) (a := a) (i := i - 1) hi_prev).inv ≫
              (K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).d (i - 1) i ≫
              (upper_stupid_truncation_x_iso (R := R) K a hi_mid).hom) := by
                simp
        _ = (upper_stupid_truncation_x_iso (R := R) (K := K) (a := a) (i := i - 1) hi_prev).hom ≫
              K.d (i - 1) i := by
              have h :=
                upper_stupid_truncation_d_via_x_iso
                  (R := R) (K := K) (a := a) (i := i - 1) (j := i) hi_prev hi_mid
              simpa [Category.assoc] using
                congrArg
                  (fun f ↦
                    (upper_stupid_truncation_x_iso
                      (R := R) (K := K) (a := a) (i := i - 1) hi_prev).hom ≫ f)
                  h
    cases cochain_prev_eq i
    simpa [HomologicalComplex.sc, CochainComplex.prev] using hd.symm
  · -- The right differential is handled by the same transported-differential computation.
    have hd :
        (K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).d i (i + 1) ≫
            (upper_stupid_truncation_x_iso (R := R) (K := K) (a := a) (i := i + 1) hi_next).hom =
          (upper_stupid_truncation_x_iso (R := R) K a hi_mid).hom ≫ K.d i (i + 1) := by
      calc
        (K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).d i (i + 1) ≫
            (upper_stupid_truncation_x_iso (R := R) (K := K) (a := a) (i := i + 1) hi_next).hom =
          (upper_stupid_truncation_x_iso (R := R) K a hi_mid).hom ≫
            ((upper_stupid_truncation_x_iso (R := R) K a hi_mid).inv ≫
              (K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).d i (i + 1) ≫
              (upper_stupid_truncation_x_iso (R := R) (K := K) (a := a) (i := i + 1) hi_next).hom) := by
                simp
        _ = (upper_stupid_truncation_x_iso (R := R) K a hi_mid).hom ≫ K.d i (i + 1) := by
              have h :=
                upper_stupid_truncation_d_via_x_iso
                  (R := R) (K := K) (a := a) (i := i) (j := i + 1) hi_mid hi_next
              simpa [Category.assoc] using
                congrArg
                  (fun f ↦
                    (upper_stupid_truncation_x_iso (R := R) K a hi_mid).hom ≫ f)
                  h
    cases cochain_next_eq i
    simpa [HomologicalComplex.sc, CochainComplex.next] using hd.symm

/-- Helper for Lemma 15.67.2: below the cutoff, the degree-`i` short complex of `K` is
canonically the same short complex as the degree-`i` short complex of the upper stupid
truncation. -/
private noncomputable def upper_stupid_truncation_sc_iso_of_lt
    (K : CochainComplex (ModuleCat R) ℤ) (a i : ℤ) (hia : i < a) :
    K.sc i ≅ (K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).sc i := by
  -- Work first in the truncation-to-source orientation, where the differential transport matches
  -- the retained-degree identifications directly, and then invert the resulting isomorphism.
  exact (upper_stupid_truncation_sc_iso_of_lt_aux (R := R) K a i hia).symm

/-- Helper for Lemma 15.67.2: the upper stupid truncation carries its canonical projection from
the original complex. -/
private noncomputable def upper_stupid_truncation_projection
    (K : CochainComplex (ModuleCat R) ℤ) (a : ℤ) :
    K ⟶ K.stupidTrunc (ComplexShape.embeddingUpIntLE a) where
  f i :=
    if hi : i ≤ a then
      (upper_stupid_truncation_x_iso (R := R) K a hi).inv
    else
      0
  comm' i j hij := by
    have hij' : j = i + 1 := by
      simpa [ComplexShape.up, eq_comm] using hij
    by_cases hi : i ≤ a
    · by_cases hj : j ≤ a
      · -- On retained degrees, the projection is the identity after transporting through the
        -- canonical truncation term identifications.
        rw [dif_pos hi, dif_pos hj]
        have hdiff :
            (upper_stupid_truncation_x_iso (R := R) K a hi).inv ≫
                (K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).d i j =
              K.d i j ≫ (upper_stupid_truncation_x_iso (R := R) K a hj).inv := by
          have h :=
            upper_stupid_truncation_d_via_x_iso
              (R := R) (K := K) (a := a) (i := i) (j := j) hi hj
          have h' := congrArg
            (fun f ↦ f ≫ (upper_stupid_truncation_x_iso (R := R) K a hj).inv) h
          simpa [Category.assoc] using h'
        simpa [Category.assoc] using hdiff
      · rw [dif_pos hi, dif_neg hj]
        have hz : IsZero ((K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).X j) := by
          refine HomologicalComplex.isZero_stupidTrunc_X
            (K := K) (e := ComplexShape.embeddingUpIntLE a) j ?_
          intro k hk
          dsimp [ComplexShape.embeddingUpIntLE] at hk
          exact hj (by omega)
        have hdzero :
            (K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).d i j = 0 :=
          hz.eq_of_tgt _ _
        simpa [hdzero, Category.assoc]
    · have hj : ¬ j ≤ a := by
        omega
      simp [hi, hj]

/-- Helper for Lemma 15.67.2: on retained degrees, the canonical upper-truncation projection is
the transported identity map. -/
private theorem upper_stupid_truncation_projection_f_of_le
    (K : CochainComplex (ModuleCat R) ℤ) (a : ℤ) {i : ℤ} (hi : i ≤ a) :
    (upper_stupid_truncation_projection (R := R) K a).f i =
      (upper_stupid_truncation_x_iso (R := R) K a hi).inv := by
  -- Unfold the canonical projection and keep only the retained-degree branch.
  simp [upper_stupid_truncation_projection, hi]

/-- Helper for Lemma 15.67.2: below the cutoff, the canonical projection to the upper stupid
truncation induces an isomorphism on homology. -/
private theorem homologyMap_upper_stupid_truncation_projection_isIso_below
    (K : CochainComplex (ModuleCat R) ℤ) (a i : ℤ) (hia : i < a) :
    IsIso (HomologicalComplex.homologyMap
      (upper_stupid_truncation_projection (R := R) K a) i) := by
  let φ :
      K.sc i ⟶ (K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).sc i :=
    ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) i).map
      (upper_stupid_truncation_projection (R := R) K a))
  have hi_prev : i - 1 ≤ a := by omega
  have hi_mid : i ≤ a := le_of_lt hia
  have hi_next : i + 1 ≤ a := by omega
  have hφ : φ = (upper_stupid_truncation_sc_iso_of_lt (R := R) K a i hia).hom := by
    -- All three components are the retained-degree projection maps.
    ext
    · cases cochain_prev_eq i
      simp [φ, upper_stupid_truncation_sc_iso_of_lt, upper_stupid_truncation_sc_iso_of_lt_aux,
        HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
        HomologicalComplex.shortComplexFunctor', CochainComplex.prev,
        upper_stupid_truncation_projection, hi_prev]
    · simp [φ, upper_stupid_truncation_sc_iso_of_lt, upper_stupid_truncation_sc_iso_of_lt_aux,
        HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
        HomologicalComplex.shortComplexFunctor', upper_stupid_truncation_projection, hi_mid]
    · cases cochain_next_eq i
      simp [φ, upper_stupid_truncation_sc_iso_of_lt, upper_stupid_truncation_sc_iso_of_lt_aux,
        HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
        HomologicalComplex.shortComplexFunctor', CochainComplex.next,
        upper_stupid_truncation_projection, hi_next]
  -- Transport invertibility along the canonical short-complex isomorphism.
  change IsIso (ShortComplex.homologyMap φ)
  rw [hφ]
  exact
    (show IsIso
      (ShortComplex.homologyMap
        (upper_stupid_truncation_sc_iso_of_lt (R := R) K a i hia).hom) by
          infer_instance)

/-- Helper for Lemma 15.67.2: the differential cokernel at the cutoff degree of the upper stupid
truncation is the source cokernel `cokernel (K.dFrom (a - 1))`. -/
noncomputable def upper_stupid_truncation_differential_cokernel_iso
    (K : CochainComplex (ModuleCat R) ℤ) (a : ℤ) :
    differentialCokernel
        (R := R)
        (E := K.stupidTrunc (ComplexShape.embeddingUpIntLE a))
        a ≅
      cokernel (K.dFrom (a - 1)) := by
  let B := K.stupidTrunc (ComplexShape.embeddingUpIntLE a)
  let ePrev :
      B.X (a - 1) ≅ K.X (a - 1) :=
    upper_stupid_truncation_x_iso (R := R) K a (by omega)
  let eCurr :
      B.X a ≅ K.xNext (a - 1) :=
    (upper_stupid_truncation_x_iso (R := R) K a le_rfl) ≪≫
      (K.xNextIso (by simp)).symm
  -- The upper stupid truncation keeps the source differential `K.dFrom (a - 1)` unchanged.
  refine cokernel.mapIso (B.d (a - 1) a) (K.dFrom (a - 1)) ePrev eCurr ?_
  have hdiff :
      ePrev.inv ≫ B.d (a - 1) a ≫
        (upper_stupid_truncation_x_iso (R := R) K a le_rfl).hom =
          K.d (a - 1) a :=
    upper_stupid_truncation_d_via_x_iso
      (R := R) (K := K) (a := a) (i := a - 1) (j := a) (by omega) le_rfl
  -- Rewrite the truncation differential comparison into the commutative square format for
  -- `cokernel.mapIso`.
  have hdiff' :
      ePrev.inv ≫ B.d (a - 1) a ≫ eCurr.hom = K.dFrom (a - 1) := by
    have hrel : (ComplexShape.up ℤ).Rel (a - 1) a := by simp
    change ePrev.inv ≫ B.d (a - 1) a ≫
        (upper_stupid_truncation_x_iso (R := R) K a le_rfl).hom ≫
          (K.xNextIso hrel).inv = K.dFrom (a - 1)
    have htmp :
        ePrev.inv ≫ B.d (a - 1) a ≫
            (upper_stupid_truncation_x_iso (R := R) K a le_rfl).hom ≫
              (K.xNextIso hrel).inv =
          K.d (a - 1) a ≫ (K.xNextIso hrel).inv :=
      congrArg (fun f ↦ f ≫ (K.xNextIso hrel).inv) hdiff
    simpa [K.dFrom_eq hrel, Category.assoc] using htmp
  simpa [B, ePrev, eCurr, Category.assoc] using
    congrArg (fun f ↦ ePrev.hom ≫ f) hdiff'

/-- Helper for Lemma 15.67.2: the top homology of the upper stupid truncation is the cokernel of
the cutoff differential. -/
noncomputable def upper_stupid_truncation_homology_iso_at_cutoff
    (K : CochainComplex (ModuleCat R) ℤ) (a : ℤ) :
    (K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).homology a ≅
      cokernel (K.dFrom (a - 1)) := by
  let B := K.stupidTrunc (ComplexShape.embeddingUpIntLE a)
  have hzero : B.d a (a + 1) = 0 := by
    let hz : IsZero (B.X (a + 1)) :=
      HomologicalComplex.isZero_stupidTrunc_X
        (K := K) (e := ComplexShape.embeddingUpIntLE a) (a + 1) (by
          intro i hi
          dsimp [ComplexShape.embeddingUpIntLE] at hi
          omega)
    -- The truncation has no term above degree `a`, so the outgoing differential is zero.
    exact hz.eq_of_tgt _ _
  let eHomology :
      B.homology a ≅ B.opcycles a :=
    B.isoHomologyι a (a + 1) (by simp) hzero
  let eOpcycles :
      B.opcycles a ≅ differentialCokernel (R := R) (E := B) a := by
    let hOpcycles :
        IsColimit (CokernelCofork.ofπ (B.pOpcycles a) (B.d_pOpcycles (a - 1) a)) := by
      simpa [B] using B.opcyclesIsCokernel (i := a - 1) (j := a) (by simp)
    -- Compare the standard categorical cokernel with the homological-complex cokernel owner.
    exact (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (B.d (a - 1) a)) hOpcycles).symm
  -- First identify the top homology with the truncation-side cokernel, then rewrite to the
  -- source cokernel via the previously computed differential comparison.
  exact eHomology ≪≫ eOpcycles ≪≫
    upper_stupid_truncation_differential_cokernel_iso (R := R) K a

/-- Helper for Lemma 15.67.2: the universal property of `tensorObj` can be postcomposed without
changing its componentwise description. -/
@[reassoc]
private theorem iTensorObj_mapBifunctorDesc_assoc
    {K L : CochainComplex (ModuleCat R) ℤ} (n : ℤ) {A B : ModuleCat R}
    (f : ∀ p q
      (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
      ((curriedTensor (ModuleCat R)).obj (K.X p)).obj (L.X q) ⟶ A)
    (u : A ⟶ B) (p q : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫
        HomologicalComplex.mapBifunctorDesc
          (K₁ := K) (K₂ := L) (F := curriedTensor (ModuleCat R))
          (c := ComplexShape.up ℤ) (A := A) (j := n) f ≫ u =
      f p q h ≫ u := by
  -- Cross the `tensorObj` abbreviation once, then postcompose the owner universal-property
  -- formula `ι_mapBifunctorDesc`.
  simpa only [HomologicalComplex.ιTensorObj] using
    congrArg (fun t ↦ t ≫ u)
      (HomologicalComplex.ι_mapBifunctorDesc
        (K₁ := K) (K₂ := L) (F := curriedTensor (ModuleCat R))
        (c := ComplexShape.up ℤ) (A := A) (j := n) (f := f) p q h)

/-- Helper for Lemma 15.67.2: away from degree `0`, the single complex contributes a zero summand
to the tensor totalization. -/
private theorem tensor_single0_off_diagonal_isZero
    (E : CochainComplex (ModuleCat R) ℤ) (N : ModuleCat R) (p q : ℤ) (hq : q ≠ 0) :
    IsZero (((curriedTensor (ModuleCat R)).obj (E.X p)).obj
      (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N).X q)) := by
  -- Apply `tensorLeft (E.X p)` to the zero object occurring in the single complex away from
  -- degree `0`.
  exact
    CategoryTheory.Functor.map_isZero ((curriedTensor (ModuleCat R)).obj (E.X p))
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) N q hq)

/-- Helper for Lemma 15.67.2: on the surviving degree-`0` summand, tensoring with the single
complex is exactly right tensoring by the underlying module. -/
private noncomputable def tensor_single0_diagonal_iso
    (E : CochainComplex (ModuleCat R) ℤ) (N : ModuleCat R) (n : ℤ) :
    ((curriedTensor (ModuleCat R)).obj (E.X n)).obj
      (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N).X 0) ≅
      (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E).X n := by
  -- The right-tensor complex is defined degreewise, so only the canonical identification of the
  -- degree-`0` term of the single complex with `N` remains.
  simpa using
    CategoryTheory.Functor.mapIso ((curriedTensor (ModuleCat R)).obj (E.X n))
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) N)

/-- Helper for Lemma 15.67.2: the forward degreewise comparison keeps only the unique diagonal
summand of the tensor totalization. -/
private noncomputable def tensor_single0_component_hom
    (E : CochainComplex (ModuleCat R) ℤ) (N : ModuleCat R) (n : ℤ) :
    (HomologicalComplex.tensorObj E
      ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)).X n ⟶
      (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E).X n :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := E)
    (K₂ := (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)
    (F := curriedTensor (ModuleCat R))
    (c := ComplexShape.up ℤ)
    (A := (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E).X n)
    (j := n)
    (fun p q h ↦ by
      by_cases hq : q = 0
      · subst hq
        have hp : p = n := by simpa using h
        subst p
        exact (tensor_single0_diagonal_iso E N n).hom
      · exact 0)

/-- Helper for Lemma 15.67.2: on the surviving diagonal summand, the forward comparison is the
canonical degreewise tensor identification. -/
@[reassoc]
private theorem tensor_single0_component_hom_diag
    (E : CochainComplex (ModuleCat R) ℤ) (N : ModuleCat R) (n : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, 0) = n) :
    HomologicalComplex.ιTensorObj E
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N) n 0 n h ≫
      tensor_single0_component_hom E N n =
        (tensor_single0_diagonal_iso E N n).hom := by
  let A :
      ModuleCat R :=
    (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E).X n
  let f : ∀ p q
      (h' : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
      ((curriedTensor (ModuleCat R)).obj (E.X p)).obj
        (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N).X q) ⟶ A :=
    fun p q h' ↦ by
      by_cases hq : q = 0
      · subst hq
        have hp : p = n := by simpa using h'
        subst p
        exact (tensor_single0_diagonal_iso E N n).hom
      · exact 0
  -- Evaluate the descended tensor map on the unique surviving `(n, 0)` summand.
  simpa [tensor_single0_component_hom, A, f] using
    (iTensorObj_mapBifunctorDesc_assoc
      (K := E)
      (L := (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)
      (n := n) (A := A) (B := A) f (𝟙 A) n 0 h)

/-- Helper for Lemma 15.67.2: away from the diagonal summand, the forward comparison vanishes. -/
@[reassoc]
private theorem tensor_single0_component_hom_off_diagonal
    (E : CochainComplex (ModuleCat R) ℤ) (N : ModuleCat R) (n p q : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n)
    (hq : q ≠ 0) :
    HomologicalComplex.ιTensorObj E
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N) p q n h ≫
      tensor_single0_component_hom E N n =
        0 := by
  let A :
      ModuleCat R :=
    (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E).X n
  let f : ∀ p' q'
      (h' : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p', q') = n),
      ((curriedTensor (ModuleCat R)).obj (E.X p')).obj
        (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N).X q') ⟶ A :=
    fun p' q' h' ↦ by
      by_cases hq' : q' = 0
      · subst hq'
        have hp' : p' = n := by simpa using h'
        subst p'
        exact (tensor_single0_diagonal_iso E N n).hom
      · exact 0
  -- Off the diagonal, the defining branch of the descended map is literally zero.
  simpa [tensor_single0_component_hom, A, f, hq] using
    (iTensorObj_mapBifunctorDesc_assoc
      (K := E)
      (L := (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)
      (n := n) (A := A) (B := A) f (𝟙 A) p q h)

/-- Helper for Lemma 15.67.2: the inverse degreewise comparison reinserts the surviving diagonal
summand into the tensor totalization. -/
private noncomputable def tensor_single0_component_inv
    (E : CochainComplex (ModuleCat R) ℤ) (N : ModuleCat R) (n : ℤ) :
    (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E).X n ⟶
      (HomologicalComplex.tensorObj E
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)).X n :=
  (tensor_single0_diagonal_iso E N n).inv ≫
    HomologicalComplex.ιTensorObj E
      ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N) n 0 n
      (by simpa using (show n + 0 = n by simp))

/-- Helper for Lemma 15.67.2: in each total degree, tensoring with a degree-zero single complex
collapses to the unique surviving diagonal summand. -/
private noncomputable def tensor_single0_component_iso
    (E : CochainComplex (ModuleCat R) ℤ) (N : ModuleCat R) (n : ℤ) :
    (HomologicalComplex.tensorObj E
      ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)).X n ≅
      (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E).X n :=
  { hom := tensor_single0_component_hom E N n
    inv := tensor_single0_component_inv E N n
    hom_inv_id := by
      -- Check the identity on the tensor totalization summandwise.
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p q h
      by_cases hq : q = 0
      · subst hq
        have hp : p = n := by simpa using h
        subst p
        -- The surviving diagonal summand is sent out and then reinserted unchanged.
        change
          ((HomologicalComplex.ιTensorObj E
                ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N) n 0 n h ≫
              tensor_single0_component_hom E N n) ≫
            tensor_single0_component_inv E N n) =
            HomologicalComplex.ιTensorObj E
              ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N) n 0 n h ≫
                𝟙 ((HomologicalComplex.tensorObj E
                  ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)).X n)
        simpa [tensor_single0_component_inv, Category.assoc] using
          congrArg (fun k ↦ k ≫ tensor_single0_component_inv E N n)
            (tensor_single0_component_hom_diag E N n h)
      · -- Off the diagonal, the forward map is zero and the source summand is already zero.
        change
          ((HomologicalComplex.ιTensorObj E
                ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N) p q n h ≫
              tensor_single0_component_hom E N n) ≫
            tensor_single0_component_inv E N n) =
            HomologicalComplex.ιTensorObj E
              ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N) p q n h ≫
                𝟙 ((HomologicalComplex.tensorObj E
                  ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)).X n)
        rw [tensor_single0_component_hom_off_diagonal E N n p q h hq]
        simp only [zero_comp, Category.comp_id]
        symm
        exact (tensor_single0_off_diagonal_isZero E N p q hq).eq_of_src _ _
    inv_hom_id := by
      let h0 : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, 0) = n := by
        simpa using (show n + 0 = n by simp)
      -- Rewrite the middle composite to the diagonal isomorphism and cancel it immediately.
      change
        ((tensor_single0_diagonal_iso E N n).inv ≫
            HomologicalComplex.ιTensorObj E
              ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N) n 0 n h0) ≫
          tensor_single0_component_hom E N n =
            𝟙 ((((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E).X n)
      calc
        ((tensor_single0_diagonal_iso E N n).inv ≫
            HomologicalComplex.ιTensorObj E
              ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N) n 0 n h0) ≫
          tensor_single0_component_hom E N n
            = (tensor_single0_diagonal_iso E N n).inv ≫
                (HomologicalComplex.ιTensorObj E
                  ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N) n 0 n h0 ≫
                    tensor_single0_component_hom E N n) := by
                      simp [Category.assoc]
        _ = (tensor_single0_diagonal_iso E N n).inv ≫
              (tensor_single0_diagonal_iso E N n).hom := by
                simpa using
                  congrArg (fun k ↦ (tensor_single0_diagonal_iso E N n).inv ≫ k)
                    (tensor_single0_component_hom_diag E N n h0)
        _ = 𝟙 _ := by simp }

/-- Helper for Lemma 15.67.2: the diagonal tensor comparison is natural in the differential of
the left cochain complex. -/
private theorem tensor_single0_diagonal_iso_hom_naturality
    (E : CochainComplex (ModuleCat R) ℤ) (N : ModuleCat R) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    (tensor_single0_diagonal_iso E N i).hom ≫
        (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj E).d i j =
      (((curriedTensor (ModuleCat R)).map (E.d i j)).app
          (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N).X 0)) ≫
        (tensor_single0_diagonal_iso E N j).hom := by
  -- The degreewise comparison is obtained by applying the tensor functor to `singleObjXSelf`.
  simpa [tensor_single0_diagonal_iso,
    CategoryTheory.Functor.mapHomologicalComplex_obj_d] using
    (((curriedTensor (ModuleCat R)).map (E.d i j)).naturality
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) N).hom)

/-- Helper for Lemma 15.67.2: the inverse diagonal tensor comparison satisfies the same
naturality square rewritten for the chain-level inverse map. -/
private theorem tensor_single0_diagonal_iso_inv_naturality
    (E : CochainComplex (ModuleCat R) ℤ) (N : ModuleCat R) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    (tensor_single0_diagonal_iso E N i).inv ≫
        (((curriedTensor (ModuleCat R)).map (E.d i j)).app
          (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N).X 0)) =
      (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E).d i j ≫
        (tensor_single0_diagonal_iso E N j).inv := by
  -- Cancel the target diagonal isomorphism and reuse the forward naturality square.
  apply (cancel_mono (tensor_single0_diagonal_iso E N j).hom).1
  simpa [Category.assoc] using
    calc
      (tensor_single0_diagonal_iso E N i).inv ≫
          (((curriedTensor (ModuleCat R)).map (E.d i j)).app
            (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N).X 0)) ≫
          (tensor_single0_diagonal_iso E N j).hom
        = (tensor_single0_diagonal_iso E N i).inv ≫
            ((tensor_single0_diagonal_iso E N i).hom ≫
              (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj E).d i j) := by
            rw [tensor_single0_diagonal_iso_hom_naturality E N i j hij]
      _ =
          (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj E).d i j := by
            simp [Category.assoc]

/-- Helper for Lemma 15.67.2: the inverse degreewise tensor comparison already respects the
cochain differential. -/
private theorem tensor_single0_component_inv_comm
    (E : CochainComplex (ModuleCat R) ℤ) (N : ModuleCat R) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    tensor_single0_component_inv E N i ≫
        (HomologicalComplex.tensorObj E
          ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)).d i j =
      (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E).d i j ≫
        tensor_single0_component_inv E N j := by
  have hj : j = i + 1 := by
    simpa [ComplexShape.up, eq_comm] using hij
  subst hj
  -- Expand the total differential into its horizontal and vertical pieces; the vertical part is
  -- zero because the degree-zero single complex has zero outgoing differential.
  simp only [tensor_single0_component_inv, Category.assoc,
    HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq
      (K₁ := E)
      (K₂ := (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)
      (F := curriedTensor (ModuleCat R))
      (c := ComplexShape.up ℤ)
      (h := (show (ComplexShape.up ℤ).Rel i (i + 1) by simp))
      (i₂ := 0)
      (j := i + 1)
      (h' := by simp)]
  rw [HomologicalComplex.mapBifunctor.d₂_eq
      (K₁ := E)
      (K₂ := (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)
      (F := curriedTensor (ModuleCat R))
      (c := ComplexShape.up ℤ)
      (i₁ := i)
      (h := (show (ComplexShape.up ℤ).Rel 0 (0 + 1) by simp))
      (j := i + 1)
      (h' := by simp)]
  have hsingle :
      (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N).d 0 (0 + 1)) = 0 := rfl
  rw [hsingle, Functor.map_zero, CategoryTheory.Limits.zero_comp, smul_zero,
    CategoryTheory.Limits.comp_zero, add_zero]
  rw [show ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i, 0) = 1 by
      rfl, one_smul]
  rw [← Category.assoc]
  rw [tensor_single0_diagonal_iso_inv_naturality
      (E := E)
      (N := N)
      (i := i)
      (j := i + 1)
      (hij := (show (ComplexShape.up ℤ).Rel i (i + 1) by simp))]
  simp [HomologicalComplex.ιTensorObj, Category.assoc]

/-- Helper for Lemma 15.67.2: tensoring a cochain complex with a degree-zero single complex is
canonically the same as tensoring on the right by the underlying module. -/
private noncomputable def tensor_single0_complex_iso
    (E : CochainComplex (ModuleCat R) ℤ) (N : ModuleCat R) :
    HomologicalComplex.tensorObj E
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N) ≅
      ((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ tensor_single0_component_iso E N n)
    (fun i j hij ↦ by
      -- Rewrite the inverse chain-map square into the forward orientation expected by
      -- `isoOfComponents`.
      apply (cancel_mono (tensor_single0_component_iso E N j).inv).1
      apply (cancel_epi (tensor_single0_component_iso E N i).inv).1
      simpa [Category.assoc] using
        (tensor_single0_component_inv_comm E N i j hij).symm)

/-- Helper for Lemma 15.67.2: in degree `i`, the tensor-with-single short complex is canonically
the short complex obtained by right tensoring with the underlying module. -/
noncomputable def tensor_single0_shortComplex_iso
    (E : CochainComplex (ModuleCat R) ℤ) (N : ModuleCat R) (i : ℤ) :
    (HomologicalComplex.tensorObj E
      ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)).sc i ≅
      (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E).sc i :=
  (HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) i).mapIso
    (tensor_single0_complex_iso E N)

/-- Helper for Lemma 15.67.2: ordinary homology of the tensor complex with `N[0]` is the same as
the derived tensor homology after localizing the tensor complex. -/
noncomputable def tensorObj_single0_homology_iso_derivedTensor
    (E : CochainComplex (ModuleCat R) ℤ) (i : ℤ) (N : ModuleCat R) :
    (HomologicalComplex.tensorObj E
      ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)).homology i ≅
      (H i).obj ((Q.obj E) ⊗[R]^L (single₀).obj N) := by
  let singleZeroCpx :
      CochainComplex (ModuleCat R) ℤ :=
    (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N
  let eTensor :
      Q.obj (HomologicalComplex.tensorObj E singleZeroCpx) ≅
        (Q.obj E) ⊗[R]^L (single₀).obj N :=
    (Functor.Monoidal.μIso (DerivedCategory.Q : CochainComplex (ModuleCat R) ℤ ⥤ DMod)
      E singleZeroCpx).symm ≪≫
      ((Iso.refl _) ⊗ᵢ
        (DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app N) ≪≫
        derivedCategory_tensorObj_iso_derivedTensorProduct
          (Q.obj E) ((single₀).obj N)
  -- First pass to the localized tensor complex, then transport the object to the derived tensor
  -- product by the monoidal comparison for `Q`.
  exact
    ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app
      (HomologicalComplex.tensorObj E singleZeroCpx)).symm ≪≫
        (H i).mapIso eTensor

/-- Helper for Lemma 15.67.2: after tensoring on the right by `N`, the retained-degree
differential of the upper stupid truncation is still the original differential of `K`. -/
private theorem tensorRight_upper_stupid_truncation_d_via_x_iso
    (K : CochainComplex (ModuleCat R) ℤ) (N : ModuleCat R) (a : ℤ) {i j : ℤ}
    (hi : i ≤ a) (hj : j ≤ a) :
    (CategoryTheory.MonoidalCategory.tensorRight N).map
        (upper_stupid_truncation_x_iso (R := R) K a hi).inv ≫
      (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (K.stupidTrunc (ComplexShape.embeddingUpIntLE a))).d i j ≫
      (CategoryTheory.MonoidalCategory.tensorRight N).map
        (upper_stupid_truncation_x_iso (R := R) K a hj).hom =
        (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K).d i j := by
  -- Apply the right-tensor functor to the previously computed differential comparison.
  simpa [CategoryTheory.Functor.mapHomologicalComplex_obj_d, Category.assoc] using
    congrArg (CategoryTheory.MonoidalCategory.tensorRight N).map
      (upper_stupid_truncation_d_via_x_iso
        (R := R) (K := K) (a := a) (i := i) (j := j) hi hj)

/-- Helper for Lemma 15.67.2: below the cutoff, right tensoring with `N` preserves the canonical
short-complex identification between the upper stupid truncation and the original complex. -/
private noncomputable def tensorRight_upper_stupid_truncation_sc_iso_of_lt
    (K : CochainComplex (ModuleCat R) ℤ) (N : ModuleCat R) (a i : ℤ) (hi : i < a) :
    (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
      (K.stupidTrunc (ComplexShape.embeddingUpIntLE a))).sc i ≅
      (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).sc i := by
  have hi_prev : i - 1 ≤ a := by omega
  have hi_mid : i ≤ a := le_of_lt hi
  have hi_next : i + 1 ≤ a := by omega
  -- Reuse the retained-degree identifications after applying the exact degreewise tensor functor.
  refine ShortComplex.isoMk
    (by
      simpa [HomologicalComplex.sc, CochainComplex.prev, cochain_prev_eq] using
        ((CategoryTheory.MonoidalCategory.tensorRight N).mapIso
          (upper_stupid_truncation_x_iso
            (R := R) (K := K) (a := a) (i := i - 1) hi_prev)))
    ((CategoryTheory.MonoidalCategory.tensorRight N).mapIso
      (upper_stupid_truncation_x_iso (R := R) K a hi_mid))
    (by
      simpa [HomologicalComplex.sc, CochainComplex.next, cochain_next_eq] using
        ((CategoryTheory.MonoidalCategory.tensorRight N).mapIso
          (upper_stupid_truncation_x_iso
            (R := R) (K := K) (a := a) (i := i + 1) hi_next)))
    ?_ ?_
  · -- The left differential comparison is just the mapped retained-degree differential identity.
    have hd :
        (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (K.stupidTrunc (ComplexShape.embeddingUpIntLE a))).d (i - 1) i ≫
            ((CategoryTheory.MonoidalCategory.tensorRight N).mapIso
              (upper_stupid_truncation_x_iso
                (R := R) K a hi_mid)).hom =
          ((CategoryTheory.MonoidalCategory.tensorRight N).mapIso
              (upper_stupid_truncation_x_iso
                (R := R) (K := K) (a := a) (i := i - 1) hi_prev)).hom ≫
            (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K).d (i - 1) i := by
      calc
        (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (K.stupidTrunc (ComplexShape.embeddingUpIntLE a))).d (i - 1) i ≫
            ((CategoryTheory.MonoidalCategory.tensorRight N).mapIso
              (upper_stupid_truncation_x_iso (R := R) K a hi_mid)).hom =
          ((CategoryTheory.MonoidalCategory.tensorRight N).mapIso
              (upper_stupid_truncation_x_iso
                (R := R) (K := K) (a := a) (i := i - 1) hi_prev)).hom ≫
            (((CategoryTheory.MonoidalCategory.tensorRight N).mapIso
                (upper_stupid_truncation_x_iso
                  (R := R) (K := K) (a := a) (i := i - 1) hi_prev)).inv ≫
              (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj
                (K.stupidTrunc (ComplexShape.embeddingUpIntLE a))).d (i - 1) i ≫
              ((CategoryTheory.MonoidalCategory.tensorRight N).mapIso
                (upper_stupid_truncation_x_iso (R := R) K a hi_mid)).hom) := by
                  simp
        _ = ((CategoryTheory.MonoidalCategory.tensorRight N).mapIso
              (upper_stupid_truncation_x_iso
                (R := R) (K := K) (a := a) (i := i - 1) hi_prev)).hom ≫
            (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K).d (i - 1) i := by
              have h :=
                tensorRight_upper_stupid_truncation_d_via_x_iso
                  (R := R) (K := K) (N := N) (a := a) (i := i - 1) (j := i) hi_prev hi_mid
              simpa [Category.assoc] using
                congrArg
                  (fun f ↦
                    ((CategoryTheory.MonoidalCategory.tensorRight N).mapIso
                      (upper_stupid_truncation_x_iso
                        (R := R) (K := K) (a := a) (i := i - 1) hi_prev)).hom ≫ f)
                  h
    cases cochain_prev_eq i
    simpa [HomologicalComplex.sc, CochainComplex.prev,
      CategoryTheory.Functor.mapHomologicalComplex_obj_d] using hd.symm
  · -- The right differential is handled by the same mapped differential comparison.
    have hd :
        (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (K.stupidTrunc (ComplexShape.embeddingUpIntLE a))).d i (i + 1) ≫
            ((CategoryTheory.MonoidalCategory.tensorRight N).mapIso
              (upper_stupid_truncation_x_iso
                (R := R) (K := K) (a := a) (i := i + 1) hi_next)).hom =
          ((CategoryTheory.MonoidalCategory.tensorRight N).mapIso
              (upper_stupid_truncation_x_iso (R := R) K a hi_mid)).hom ≫
            (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K).d i (i + 1) := by
      calc
        (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (K.stupidTrunc (ComplexShape.embeddingUpIntLE a))).d i (i + 1) ≫
            ((CategoryTheory.MonoidalCategory.tensorRight N).mapIso
              (upper_stupid_truncation_x_iso
                (R := R) (K := K) (a := a) (i := i + 1) hi_next)).hom =
          ((CategoryTheory.MonoidalCategory.tensorRight N).mapIso
              (upper_stupid_truncation_x_iso (R := R) K a hi_mid)).hom ≫
            (((CategoryTheory.MonoidalCategory.tensorRight N).mapIso
                (upper_stupid_truncation_x_iso (R := R) K a hi_mid)).inv ≫
              (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj
                (K.stupidTrunc (ComplexShape.embeddingUpIntLE a))).d i (i + 1) ≫
              ((CategoryTheory.MonoidalCategory.tensorRight N).mapIso
                (upper_stupid_truncation_x_iso
                  (R := R) (K := K) (a := a) (i := i + 1) hi_next)).hom) := by
                  simp
        _ = ((CategoryTheory.MonoidalCategory.tensorRight N).mapIso
              (upper_stupid_truncation_x_iso (R := R) K a hi_mid)).hom ≫
            (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K).d i (i + 1) := by
              have h :=
                tensorRight_upper_stupid_truncation_d_via_x_iso
                  (R := R) (K := K) (N := N) (a := a) (i := i) (j := i + 1) hi_mid hi_next
              simpa [Category.assoc] using
                congrArg
                  (fun f ↦
                    ((CategoryTheory.MonoidalCategory.tensorRight N).mapIso
                      (upper_stupid_truncation_x_iso
                        (R := R) K a hi_mid)).hom ≫ f)
                  h
    cases cochain_next_eq i
    simpa [HomologicalComplex.sc, CochainComplex.next,
      CategoryTheory.Functor.mapHomologicalComplex_obj_d] using hd.symm

/-- Helper for Lemma 15.67.2: an object of `D(R)` concentrated in degree `n` is canonically the
single object on its degree-`n` cohomology. -/
private noncomputable def singleFunctor_iso_of_isGE_of_isLE_local
    (X : DMod) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    X ≅ (DerivedCategory.singleFunctor (ModuleCat R) n).obj ((H n).obj X) :=
  singleFunctorIso_of_isGE_of_isLE (A := ModuleCat R) X n

/-- Helper for Lemma 15.67.2: testing lower tor-amplitude against the tensor unit shows that the
representative `K` itself has no homology below degree `a`. -/
private theorem isZero_homology_of_hasTorAmplitudeGE_below
    (K : CochainComplex (ModuleCat R) ℤ) (a i : ℤ)
    (hTor : HasTorAmplitudeGE (Q.obj K) a) (hi : i < a) :
    IsZero (K.homology i) := by
  let eUnit :
      (single₀).obj (ModuleCat.of R R) ≅ 𝟙_ DMod :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app
        (ModuleCat.of R R)) ≪≫
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app
          ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj
            (ModuleCat.of R R))).symm
  let eRing :
      (Q.obj K) ⊗[R]^L (single₀).obj (ModuleCat.of R R) ≅ Q.obj K :=
    (derivedTensorProduct_comm (Q.obj K) ((single₀).obj (ModuleCat.of R R))) ≪≫
      (derivedCategory_tensorObj_iso_derivedTensorProduct
        ((single₀).obj (ModuleCat.of R R)) (Q.obj K)).symm ≪≫
        whiskerRightIso eUnit (Q.obj K) ≪≫ λ_ (Q.obj K)
  have hzero_tensor :
      IsZero ((H i).obj ((Q.obj K) ⊗[R]^L (single₀).obj (ModuleCat.of R R))) := by
    simpa using
      tensor_homology_isZero_of_hasTorAmplitudeGE
        (R := R) (K := Q.obj K) a i hTor (ModuleCat.of R R) hi
  have hzero_Q : IsZero ((H i).obj (Q.obj K)) :=
    hzero_tensor.of_iso ((H i).mapIso eRing.symm)
  -- Compute cohomology of `Q.obj K` on the chosen representative.
  exact ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app K).isZero_iff.1 hzero_Q

/-- Helper for Lemma 15.67.2: the upper stupid truncation is concentrated in degree `a` on the
cutoff cokernel once `Q.obj K` has lower tor-amplitude `≥ a`. -/
private noncomputable def upper_stupid_truncation_iso_single_cokernel_of_hasTorAmplitudeGE
    (K : CochainComplex (ModuleCat R) ℤ) (a : ℤ)
    (hTor : HasTorAmplitudeGE (Q.obj K) a) :
    Q.obj (K.stupidTrunc (ComplexShape.embeddingUpIntLE a)) ≅
      (DerivedCategory.singleFunctor (ModuleCat R) a).obj
        (cokernel (K.dFrom (a - 1))) := by
  let B := K.stupidTrunc (ComplexShape.embeddingUpIntLE a)
  have hBge : ∀ n : ℤ, n < a → IsZero (B.homology n) := by
    intro n hn
    let π : K ⟶ B := upper_stupid_truncation_projection (R := R) K a
    haveI : IsIso (HomologicalComplex.homologyMap π n) :=
      homologyMap_upper_stupid_truncation_projection_isIso_below (R := R) K a n hn
    let eH : K.homology n ≅ B.homology n :=
      asIso (HomologicalComplex.homologyMap π n)
    -- Below the cutoff, the truncation has the same homology as `K`, and tor-amplitude kills it.
    exact eH.isZero_iff.1
      (isZero_homology_of_hasTorAmplitudeGE_below (R := R) K a n hTor hn)
  have hBle : ∀ n : ℤ, a < n → IsZero (B.homology n) := by
    intro n hn
    have hX : IsZero (B.X n) := by
      -- Above the cutoff, the upper stupid truncation has no terms.
      refine K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntLE a) n ?_
      intro i hi
      dsimp [ComplexShape.embeddingUpIntLE] at hi
      omega
    -- With zero middle term, the short complex computing degree-`n` homology is exact.
    simpa using
      (ShortComplex.isZero_homology_of_isZero_X₂
        (S := B.sc n)
        (by simpa using hX))
  have hQge :
      (Q.obj B).IsGE a := by
    rw [DerivedCategory.isGE_iff]
    intro n hn
    let e :
        (H n).obj (Q.obj B) ≅ B.homology n :=
      (DerivedCategory.homologyFunctorFactors (ModuleCat R) n).app B
    exact e.isZero_iff.2 (hBge n hn)
  have hQle :
      (Q.obj B).IsLE a := by
    rw [DerivedCategory.isLE_iff]
    intro n hn
    let e :
        (H n).obj (Q.obj B) ≅ B.homology n :=
      (DerivedCategory.homologyFunctorFactors (ModuleCat R) n).app B
    exact e.isZero_iff.2 (hBle n hn)
  letI : (Q.obj B).IsGE a := hQge
  letI : (Q.obj B).IsLE a := hQle
  let eSingle :
      Q.obj B ≅
        (DerivedCategory.singleFunctor (ModuleCat R) a).obj
          ((H a).obj (Q.obj B)) :=
    singleFunctor_iso_of_isGE_of_isLE_local (R := R) (X := Q.obj B) a
  let eHomology :
      (H a).obj (Q.obj B) ≅ cokernel (K.dFrom (a - 1)) :=
    (DerivedCategory.homologyFunctorFactors (ModuleCat R) a).app B ≪≫
      upper_stupid_truncation_homology_iso_at_cutoff (R := R) (K := K) a
  -- Once the truncation is known to have cohomology only in degree `a`, the standard single-object
  -- comparison identifies it with the cutoff cokernel placed in degree `a`.
  exact eSingle ≪≫
    (DerivedCategory.singleFunctor (ModuleCat R) a).mapIso eHomology

/-- Helper for Lemma 15.67.2: the upper stupid truncation carries a canonical map to the single
complex in degree `a` on `cokernel (K.dFrom (a - 1))`. -/
noncomputable def upper_stupid_truncation_to_single_cokernel
    (K : CochainComplex (ModuleCat R) ℤ) (a : ℤ) :
    K.stupidTrunc (ComplexShape.embeddingUpIntLE a) ⟶
      (CochainComplex.singleFunctor (ModuleCat R) a).obj
        (cokernel (K.dFrom (a - 1))) :=
  to_single_of_differential_cokernel
      (R := R)
      (E := K.stupidTrunc (ComplexShape.embeddingUpIntLE a))
      a ≫
    (CochainComplex.singleFunctor (ModuleCat R) a).map
      (upper_stupid_truncation_differential_cokernel_iso (R := R) K a).hom

/-- Helper for Lemma 15.67.2: at the cutoff degree `a`, the canonical map from the upper stupid
truncation to the single complex on `cokernel (K.dFrom (a - 1))` induces a monomorphism on
homology. -/
lemma homologyMap_upper_stupid_truncation_to_single_cokernel_mono
    (K : CochainComplex (ModuleCat R) ℤ) (a : ℤ) :
    Mono ((K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).homologyMap
      (upper_stupid_truncation_to_single_cokernel (R := R) K a) a) := by
  let B := K.stupidTrunc (ComplexShape.embeddingUpIntLE a)
  let β := to_single_of_differential_cokernel (R := R) (E := B) a
  let e := upper_stupid_truncation_differential_cokernel_iso (R := R) K a
  have hβ :
      Mono (B.homologyMap β a) := by
    -- The raw differential-cokernel map is already known to be monic on cutoff homology.
    simpa [B, β] using
      (homologyMap_to_single_of_differential_cokernel_mono (R := R) (E := B) a)
  -- Unfold the canonical truncation map into the basic cokernel map followed by the target
  -- isomorphism, then compose the two monomorphisms.
  change Mono (B.homologyMap
    (β ≫ (CochainComplex.singleFunctor (ModuleCat R) a).map e.hom) a)
  rw [HomologicalComplex.homologyMap_comp]
  exact mono_comp' hβ (by infer_instance)

/-- Helper for Lemma 15.67.2: below the cutoff, tensoring the upper stupid truncation with a
degree-zero module has the same homology as tensoring the original complex. -/
noncomputable def upper_stupid_truncation_tensor_homology_iso_below_cutoff
    (K : CochainComplex (ModuleCat R) ℤ) (a : ℤ)
    (hbounded : CochainComplex.minus (ModuleCat R) K)
    (hFlat : K.IsTermwiseFlat)
    (N : ModuleCat R) (i : ℤ) (hi : i < a) :
    (H i).obj
        ((Q.obj (K.stupidTrunc (ComplexShape.embeddingUpIntLE a))) ⊗[R]^L (single₀).obj N) ≅
      (H i).obj ((Q.obj K) ⊗[R]^L (single₀).obj N) := by
  let B := K.stupidTrunc (ComplexShape.embeddingUpIntLE a)
  let eOrd :
      (HomologicalComplex.tensorObj B
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)).homology i ≅
        (HomologicalComplex.tensorObj K
          ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)).homology i :=
    ShortComplex.homologyMapIso
      (tensor_single0_shortComplex_iso (R := R) B N i ≪≫
        tensorRight_upper_stupid_truncation_sc_iso_of_lt (R := R) K N a i hi ≪≫
        (tensor_single0_shortComplex_iso (R := R) K N i).symm)
  -- Route correction: compare the degree-`i` tensor short complexes first, then transport the
  -- resulting ordinary homology isomorphism to the derived tensor product.
  let _ := hbounded
  let _ := hFlat
  exact
    (tensorObj_single0_homology_iso_derivedTensor (R := R) B i N).symm ≪≫
      eOrd ≪≫
      tensorObj_single0_homology_iso_derivedTensor (R := R) K i N

/-- Helper for Lemma 15.67.2: `Tor₁(C, N)` is the `(-1)`-st homology of
`C[0] ⊗_R^{\mathbf L} N[0]`. -/
noncomputable def tor_one_projective_resolution_homology_iso
    (C N : ModuleCat R) :
    ((((Tor (ModuleCat R) 1).obj C).obj N)) ≅
      (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 1).obj
        (((tensorRight C).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (CategoryTheory.projectiveResolution N).complex) := by
  let eFlip :
      ((((Tor (ModuleCat R) 1).obj C).obj N)) ≅
        ((((Functor.flip (Tor' (ModuleCat R) 1)).obj C).obj N)) :=
    asIso (((tor_flip_iso (ModuleCat R) 1).app C).hom.app N)
  let eResolution :
      ((((Functor.flip (Tor' (ModuleCat R) 1)).obj C).obj N)) ≅
        (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 1).obj
          (((tensorRight C).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (CategoryTheory.projectiveResolution N).complex) := by
    -- Compute the flipped `Tor₁` term from the projective resolution of `N`.
    simpa [Tor', Functor.flip] using
      ((CategoryTheory.projectiveResolution N).isoLeftDerivedObj (tensorRight C) 1)
  -- First flip `Tor`, then evaluate the left-derived functor on the projective resolution of `N`.
  exact eFlip ≪≫ eResolution

/-- Helper for Lemma 15.67.2: the degree-`1` homology of the tensor-right chain-resolution model
is the degree-`-1` homology of the corresponding cochain-resolution model. -/
noncomputable def projective_resolution_tensorRight_cochain_homology_iso_neg_one
    (C N : ModuleCat R) :
    (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 1).obj
        (((tensorRight C).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (CategoryTheory.projectiveResolution N).complex) ≅
      ((((tensorRight C).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (CategoryTheory.ProjectiveResolution.cochainComplex
            (CategoryTheory.projectiveResolution N))).homology (-1)) := by
  let eCochain :
      ((tensorRight C).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (CategoryTheory.ProjectiveResolution.cochainComplex
            (CategoryTheory.projectiveResolution N)) ≅
        ((((tensorRight C).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (CategoryTheory.projectiveResolution N).complex).extend
          ComplexShape.embeddingDownNat) :=
    eqToIso rfl
  -- Route correction: isolate the public chain-to-cochain transport here, so the remaining Tor
  -- comparison only has to move from the cochain-resolution tensor model to derived tensor.
  exact
    (((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) (-1)).mapIso
        eCochain) ≪≫
      ((((tensorRight C).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (CategoryTheory.projectiveResolution N).complex).extendHomologyIso
        ComplexShape.embeddingDownNat (by simp))).symm

/-- Helper for Lemma 15.67.2: the cochain projective resolution of `N` represents the derived
degree-zero single object `N[0]`. -/
noncomputable def projective_resolution_single0_iso
    (N : ModuleCat R) :
    Q.obj (CategoryTheory.ProjectiveResolution.cochainComplex
      (CategoryTheory.projectiveResolution N)) ≅
      (single₀).obj N := by
  let f :
      Q.obj (CategoryTheory.ProjectiveResolution.cochainComplex
          (CategoryTheory.projectiveResolution N)) ⟶
        Q.obj ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N) :=
    Q.map (CategoryTheory.ProjectiveResolution.π'
      (CategoryTheory.projectiveResolution N))
  let _ : IsIso
      (Q.map (CategoryTheory.ProjectiveResolution.π'
        (CategoryTheory.projectiveResolution N))) := by
    infer_instance
  have hf : IsIso f := by
    -- The projective-resolution augmentation is a quasi-isomorphism, hence becomes an isomorphism
    -- after passing to the derived category.
    simpa [f]
  let e :
      Q.obj (CategoryTheory.ProjectiveResolution.cochainComplex
          (CategoryTheory.projectiveResolution N)) ≅
        Q.obj ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N) :=
    asIso f
  -- Finish by rewriting the localized degree-zero single complex to the canonical derived object
  -- `N[0]`.
  exact e ≪≫ ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app N).symm

/-- Helper for Lemma 15.67.2: `Tor₁(C, N)` is the `(-1)`-st homology of
`C[0] ⊗_R^{\mathbf L} N[0]`. -/
noncomputable def tor_one_single0_tensor_homology_iso
    (C N : ModuleCat R) :
    ((((Tor (ModuleCat R) 1).obj C).obj N)) ≅
      (H (-1)).obj (((single₀).obj C) ⊗[R]^L (single₀).obj N) := by
  -- Route correction: follow the Chapter 10 projective-resolution computation of `Tor₁`, then
  -- transport the resulting ordinary tensor-complex homology to the derived tensor product.
  let P :=
    CategoryTheory.ProjectiveResolution.cochainComplex
      (CategoryTheory.projectiveResolution N)
  let eResolution :
      ((((Tor (ModuleCat R) 1).obj C).obj N)) ≅
        ((((tensorRight C).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homology (-1)) :=
    tor_one_projective_resolution_homology_iso (R := R) C N ≪≫
      projective_resolution_tensorRight_cochain_homology_iso_neg_one (R := R) C N
  let eTensor :
      ((((tensorRight C).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homology (-1)) ≅
        (HomologicalComplex.tensorObj P
          ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj C)).homology (-1) :=
    (HomologicalComplex.homologyMapIso
      (tensor_single0_complex_iso (R := R) P C).symm (-1))
  let eDerived :
      (HomologicalComplex.tensorObj P
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj C)).homology (-1) ≅
        (H (-1)).obj ((Q.obj P) ⊗[R]^L (single₀).obj C) :=
    tensorObj_single0_homology_iso_derivedTensor (R := R) P (-1) C
  let eSingle :
      (H (-1)).obj ((Q.obj P) ⊗[R]^L (single₀).obj C) ≅
        (H (-1)).obj (((single₀).obj N) ⊗[R]^L (single₀).obj C) :=
    (H (-1)).mapIso
      ((derivedTensorProduct ((single₀).obj C)).mapIso
        (projective_resolution_single0_iso (R := R) N))
  let eComm :
      (H (-1)).obj (((single₀).obj N) ⊗[R]^L (single₀).obj C) ≅
        (H (-1)).obj (((single₀).obj C) ⊗[R]^L (single₀).obj N) :=
    (H (-1)).mapIso
      (derivedTensorProduct_comm ((single₀).obj N) ((single₀).obj C))
  -- Compose the projective-resolution computation, the tensor-with-single comparison, the passage
  -- to the derived tensor product, and finally the canonical swap of tensor factors.
  exact eResolution ≪≫ eTensor ≪≫ eDerived ≪≫ eSingle ≪≫ eComm

/-- Helper for Lemma 15.67.2: the source-faithful upper stupid truncation route identifies the
quotient-side `Tor₁` of `cokernel (K.dFrom (a - 1))` with degree-`a - 1` homology of the derived
tensor product represented by `K`. -/
noncomputable def tor_one_cokernel_dFrom_quotient_iso_tensor_homology
    (K : CochainComplex (ModuleCat R) ℤ) (a : ℤ)
    (hbounded : CochainComplex.minus (ModuleCat R) K)
    (hFlat : K.IsTermwiseFlat)
    (hTor : HasTorAmplitudeGE (Q.obj K) a)
    (I : Ideal R) :
    ((((Tor (ModuleCat R) 1).obj (cokernel (K.dFrom (a - 1)) : ModuleCat R)).obj
      (ModuleCat.of R (R ⧸ I)))) ≅
        (H (a - 1)).obj
          ((Q.obj K) ⊗[R]^L (single₀).obj (ModuleCat.of R (R ⧸ I))) := by
  let B := K.stupidTrunc (ComplexShape.embeddingUpIntLE a)
  let N : ModuleCat R := ModuleCat.of R (R ⧸ I)
  let eTor :
      ((((Tor (ModuleCat R) 1).obj (cokernel (K.dFrom (a - 1)) : ModuleCat R)).obj N)) ≅
        (H (-1)).obj (((single₀).obj (cokernel (K.dFrom (a - 1)) : ModuleCat R)) ⊗[R]^L
          (single₀).obj N) :=
    tor_one_single0_tensor_homology_iso
      (R := R) (cokernel (K.dFrom (a - 1)) : ModuleCat R) N
  let eShift :
      (H (-1)).obj (((single₀).obj (cokernel (K.dFrom (a - 1)) : ModuleCat R)) ⊗[R]^L
          (single₀).obj N) ≅
        (H (a - 1)).obj
          (((DerivedCategory.singleFunctor (ModuleCat R) a).obj
              (cokernel (K.dFrom (a - 1)) : ModuleCat R)) ⊗[R]^L
            (single₀).obj N) :=
    (single_shifted_tensor_homology_iso
      (R := R) (cokernel (K.dFrom (a - 1)) : ModuleCat R) N a).symm
  let eSingle :
      (H (a - 1)).obj
          (((DerivedCategory.singleFunctor (ModuleCat R) a).obj
              (cokernel (K.dFrom (a - 1)) : ModuleCat R)) ⊗[R]^L
            (single₀).obj N) ≅
        (H (a - 1)).obj ((Q.obj B) ⊗[R]^L (single₀).obj N) :=
    (H (a - 1)).mapIso
      ((derivedTensorProduct ((single₀).obj N)).mapIso
        (upper_stupid_truncation_iso_single_cokernel_of_hasTorAmplitudeGE
          (R := R) K a hTor).symm)
  let eBelow :
      (H (a - 1)).obj ((Q.obj B) ⊗[R]^L (single₀).obj N) ≅
        (H (a - 1)).obj ((Q.obj K) ⊗[R]^L (single₀).obj N) :=
    upper_stupid_truncation_tensor_homology_iso_below_cutoff
      (R := R) K a hbounded hFlat N (a - 1) (by omega)
  -- Compose the four source-faithful comparison isomorphisms: `Tor₁`, the shift from `-1` to
  -- `a - 1`, concentration of the upper truncation in degree `a`, and the below-cutoff tensor
  -- comparison from the truncation back to `K`.
  exact eTor ≪≫ eShift ≪≫ eSingle ≪≫ eBelow

/-- Helper for Lemma 15.67.2: once the source-faithful `Tor₁`/tensor-homology bridge is in place,
lower tor-amplitude kills the quotient-side `Tor₁` of the cutoff cokernel. -/
lemma isZero_tor_one_cokernel_dFrom_quotient_of_boundedAbove_of_termwiseFlat_of_hasTorAmplitudeGE
    (K : CochainComplex (ModuleCat R) ℤ) (a : ℤ)
    (hbounded : CochainComplex.minus (ModuleCat R) K)
    (hFlat : K.IsTermwiseFlat)
    (hTor : HasTorAmplitudeGE (Q.obj K) a)
    (I : Ideal R) :
    IsZero ((((Tor (ModuleCat R) 1).obj (cokernel (K.dFrom (a - 1)) : ModuleCat R)).obj
      (ModuleCat.of R (R ⧸ I)))) := by
  -- Transport the goal to degree-`a - 1` tensor homology of `Q.obj K` against `(R ⧸ I)[0]`.
  have hZeroHomology :
      IsZero ((H (a - 1)).obj
        ((Q.obj K) ⊗[R]^L (single₀).obj (ModuleCat.of R (R ⧸ I)))) := by
    -- The tor-amplitude hypothesis kills exactly these homology groups below degree `a`.
    simpa using
      tensor_homology_isZero_of_hasTorAmplitudeGE
        (R := R) (K := Q.obj K) a (a - 1) hTor (ModuleCat.of R (R ⧸ I)) (by omega)
  exact hZeroHomology.of_iso
    (tor_one_cokernel_dFrom_quotient_iso_tensor_homology
      (R := R) K a hbounded hFlat hTor I)

/-- Lemma 15.67.2: if the derived object represented by a bounded above cochain complex of flat
`R`-modules has tor-amplitude in `[a, ∞]`, then the cokernel of
`K.dFrom (a - 1) : K^(a - 1) ⟶ K^a` is flat. -/

@[stacks 0653]
theorem flat_cokernel_dFrom_of_boundedAbove_of_termwiseFlat_of_hasTorAmplitudeGE
    (K : CochainComplex (ModuleCat R) ℤ) (a : ℤ)
    (hbounded : CochainComplex.minus (ModuleCat R) K)
    (hFlat : K.IsTermwiseFlat)
    (hTor : HasTorAmplitudeGE (Q.obj K) a) :
    Module.Flat R ↑((cokernel (K.dFrom (a - 1)) : ModuleCat R)) := by
  -- The main reduction is now the quotient-ideal flatness criterion from Lemma `10.75.8`.
  apply flat_of_tor_one_quotient_vanishing
  intro I
  -- The remaining source-faithful comparison turns the tor-amplitude vanishing into this
  -- quotient-side `Tor₁`-vanishing statement.
  exact
    isZero_tor_one_cokernel_dFrom_quotient_of_boundedAbove_of_termwiseFlat_of_hasTorAmplitudeGE
      K a hbounded hFlat hTor I

end CochainComplex

end

end CategoryTheory
