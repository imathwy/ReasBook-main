import Mathlib
import stacks_proof.stacks_project.Chap15.Lemma_15_6_2
import stacks_proof.stacks_project.Chap15.Lemma_15_92_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.DerivedCategory

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)

namespace CategoryTheory.DerivedCategory

/- Domain-style sampling:
- primary domain: localization-away vanishing loci in the derived category of `A`-modules;
- sampled owner-side declarations:
  `localizationAwayDerivedHomVanishingCondition`,
  `Ideal`,
  `Ideal.IsRadical`,
  the downstream containment owner `IsDerivedCompleteWithRespectTo`;
- best owner abstraction: the source-facing ideal
  `K.localizationAwayDerivedHomVanishingIdeal`, built from the primitive predicate
  `localizationAwayDerivedHomVanishingCondition f K`;
- primitive data: `K : DMod` and the vanishing predicate in the scalar `f : A`;
- derived API: membership rewriting and the downstream containment formulation of derived
  completeness.

Layer triage:
- `source-facing`: `K.localizationAwayDerivedHomVanishingIdeal`;
- `core/canonical`: the primitive predicate `localizationAwayDerivedHomVanishingCondition`;
- `bridge/view`: the membership iff and the derived-completeness containment API. -/

/-- Helper for Lemma 15.92.2: restricting scalars commutes with homology on derived categories of
modules. -/
noncomputable def restrictScalars_homology_iso
    {B : Type u} [CommRing B] (φ : A →+* B)
    (L : DerivedCategory (ModuleCat B)) (i : ℤ) :
    (H i).obj (((ModuleCat.restrictScalars φ).mapDerivedCategory).obj L) ≅
      (ModuleCat.restrictScalars φ).obj
        ((DerivedCategory.homologyFunctor (ModuleCat B) i).obj L) := by
  let K := DerivedCategory.Q.objPreimage L
  let FK := ((ModuleCat.restrictScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let eB :
      (DerivedCategory.homologyFunctor (ModuleCat B) i).obj L ≅ K.homology i :=
    ((DerivedCategory.homologyFunctor (ModuleCat B) i).mapIso
      (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat B) i).app K
  -- Proof comment: compute homology on a chosen cochain representative and compare strict
  -- homology before and after restriction of scalars.
  exact
    (H i).mapIso
        ((((ModuleCat.restrictScalars φ).mapDerivedCategory).mapIso
            (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
          ((ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.app K)) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat A) i).app FK ≪≫
      (K.sc i).mapHomologyIso (ModuleCat.restrictScalars φ) ≪≫
      (ModuleCat.restrictScalars φ).mapIso eB.symm

/-- Helper for Lemma 15.92.2: a derived `A`-module object is zero once all of its homology
objects vanish. -/
lemma isZero_of_all_homology_isZero
    (K : DMod) (hK : ∀ i : ℤ, IsZero ((H i).obj K)) :
    IsZero K := by
  -- Proof comment: vanishing in every degree places `K` simultaneously in `D^{≤ 0}` and
  -- `D^{≥ 1}`, so the standard t-structure forces `K` to be zero.
  have hLE : K.IsLE 0 := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact hK i
  have hGE : K.IsGE 1 := by
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact hK i
  letI : K.IsLE 0 := hLE
  letI : K.IsGE 1 := hGE
  exact t.isZero K 0 1 (by omega)

/-- Helper for Lemma 15.92.2: after restricting scalars from `A_0` to `A`, every object of
`D(A_0)` becomes zero. -/
lemma localizationAway_zero_restricted_object_isZero
    (E : DerivedCategory (ModuleCat (Localization.Away (0 : A)))) :
    IsZero
      (((ModuleCat.restrictScalars
          (algebraMap A (Localization.Away (0 : A)))).mapDerivedCategory.obj E)) := by
  letI : Subsingleton (Localization.Away (0 : A)) :=
    SurjectiveRingPullbackSituation.localizationAway_subsingleton_of_eq_zero
      (R := A) (r := (0 : A)) rfl
  -- Proof comment: restriction of scalars commutes with homology, and every `A_0`-module is a
  -- zero object because `A_0` is the zero ring.
  refine isZero_of_all_homology_isZero (A := A) _ ?_
  intro i
  let M : ModuleCat (Localization.Away (0 : A)) :=
    (DerivedCategory.homologyFunctor (ModuleCat (Localization.Away (0 : A))) i).obj E
  have hMzero :
      IsZero
        ((ModuleCat.restrictScalars
          (algebraMap A (Localization.Away (0 : A)))).obj M) := by
    letI : Subsingleton ↑M := inferInstance
    exact ModuleCat.isZero_of_subsingleton _
  exact
    (restrictScalars_homology_iso
      (A := A) (φ := algebraMap A (Localization.Away (0 : A))) E i).isZero_iff.2 hMzero

-- Proof sketch: for `f = 0`, the localization `A_0` is the zero ring, so `D(A_0)` is the zero
-- derived category and every morphism out of an object of `D(A_0)` is zero.
/-- The vanishing condition holds for the zero element. -/
theorem localizationAwayDerivedHomVanishingCondition_zero (K : DMod) :
    localizationAwayDerivedHomVanishingCondition 0 K := by
  intro E
  -- Proof comment: once the restricted source object is zero, the corresponding Hom set is
  -- identified with the Hom set out of `0`, which is automatically subsingleton.
  let hEzero :=
    localizationAway_zero_restricted_object_isZero (A := A) E
  let e :
      (((ModuleCat.restrictScalars
          (algebraMap A (Localization.Away (0 : A)))).mapDerivedCategory.obj E) ⟶ K) ≅
        ((0 : DMod) ⟶ K) :=
    hEzero.isoZero.homCongr (Iso.refl K)
  exact e.injective.subsingleton

/-- Helper for Lemma 15.92.2: a comparison map of away-localizations over `A` transports the
derived-Hom vanishing condition to the target localization. -/
theorem localizationAwayDerivedHomVanishingCondition_of_comparison
    {f g : A} {K : DMod}
    (σ : Localization.Away f →+* Localization.Away g)
    (hσ : σ.comp (algebraMap A (Localization.Away f)) = algebraMap A (Localization.Away g))
    (hf : localizationAwayDerivedHomVanishingCondition f K) :
    localizationAwayDerivedHomVanishingCondition g K := by
  intro E
  let L := DerivedCategory.Q.objPreimage E
  let Eσ :
      DerivedCategory (ModuleCat (Localization.Away f)) :=
    DerivedCategory.Q.obj
      (((ModuleCat.restrictScalars σ).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
  let hsub :
      Subsingleton
        (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
          Eσ) ⟶ K) :=
    hf Eσ
  let eg :
      ((ModuleCat.restrictScalars (algebraMap A (Localization.Away g))).mapDerivedCategory.obj E) ≅
        DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars
              (algebraMap A (Localization.Away g))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            L) :=
    ((ModuleCat.restrictScalars (algebraMap A (Localization.Away g))).mapDerivedCategory).mapIso
        (DerivedCategory.Q.objObjPreimageIso E).symm ≪≫
      (ModuleCat.restrictScalars
        (algebraMap A (Localization.Away g))).mapDerivedCategoryFactors.app L
  let e :
      ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
        Eσ) ≅
        ((ModuleCat.restrictScalars (algebraMap A (Localization.Away g))).mapDerivedCategory.obj E) :=
    calc
      ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
          Eσ) ≅
          DerivedCategory.Q.obj
            (((ModuleCat.restrictScalars
                (algebraMap A (Localization.Away f))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (((ModuleCat.restrictScalars σ).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) :=
        (ModuleCat.restrictScalars
          (algebraMap A (Localization.Away f))).mapDerivedCategoryFactors.app
            (((ModuleCat.restrictScalars σ).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
      _ ≅
          DerivedCategory.Q.obj
            (((ModuleCat.restrictScalars
                (algebraMap A (Localization.Away g))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              L) :=
        DerivedCategory.Q.mapIso
          ((NatIso.mapHomologicalComplex
            (ModuleCat.restrictScalarsComp'
              (algebraMap A (Localization.Away f))
              σ
              (algebraMap A (Localization.Away g))
              hσ).symm
            (ComplexShape.up ℤ)).app L)
      _ ≅
          ((ModuleCat.restrictScalars (algebraMap A (Localization.Away g))).mapDerivedCategory.obj
            E) :=
        eg.symm
  -- Transport the subsingleton Hom-set across the derived restriction comparison.
  letI :
      Subsingleton
        (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
          Eσ) ⟶ K) := hsub
  exact ((e.homCongr (Iso.refl K)).injective.subsingleton)

/-- Helper for Lemma 15.92.2: in `A_(f + g)`, the images of `f` and `g` add up to a unit. -/
lemma localizationAway_sum_isUnit (f g : A) :
    IsUnit
      (algebraMap A (Localization.Away (f + g)) f +
        algebraMap A (Localization.Away (f + g)) g) := by
  -- Proof comment: in the localization away from `f + g`, the element `f + g` itself is
  -- invertible, and the displayed sum is exactly its image.
  simpa [map_add] using
    (IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away (f + g)) (x := f + g))

/-- Helper for Lemma 15.92.2: if the outer terms of a distinguished triangle admit only one map
into `K`, then the middle term also admits only one map into `K`. -/
lemma subsingleton_hom_of_distinguished_middle
    {X Y Z K : DMod} {a : X ⟶ Y} {b : Y ⟶ Z} {c : Z ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk a b c ∈ distTriang DMod)
    [Subsingleton (X ⟶ K)] [Subsingleton (Z ⟶ K)] :
    Subsingleton (Y ⟶ K) := by
  -- Proof comment: exactness of `coyoneda` shows that a difference of two maps into the middle
  -- term factors through the left term once its composite with the right term vanishes.
  refine ⟨fun u v ↦ ?_⟩
  have hcomp : (u - v) ≫ b = 0 := by
    have huv : u ≫ b = v ≫ b := Subsingleton.elim _ _
    rw [sub_comp, huv, sub_self]
  obtain ⟨w, hw⟩ := Triangle.coyoneda_exact₂ (T := Triangle.mk a b c) hT (u - v) hcomp
  have hw_zero : w = 0 := Subsingleton.elim _ _
  apply sub_eq_zero.mp
  calc
    u - v = w ≫ a := hw
    _ = 0 := by simpa [hw_zero]

/-- Helper for Lemma 15.92.2: if both summands admit only one map into `K`, then so does their
biproduct. -/
lemma subsingleton_hom_from_biprod
    {X Y K : DMod} [Subsingleton (X ⟶ K)] [Subsingleton (Y ⟶ K)] :
    Subsingleton ((X ⊞ Y) ⟶ K) := by
  -- Proof comment: a map out of a biproduct is determined by its restrictions to the two
  -- summands, and each restricted Hom-set is already subsingleton.
  refine ⟨fun u v ↦ ?_⟩
  apply Limits.biprod.hom_ext'
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _

-- Proof sketch: use the standard Mayer-Vietoris short exact sequence
-- `0 → A_{f + g} → A_{f(f + g)} ⊕ A_{g(f + g)} → A_{fg(f + g)} → 0`, then apply the long exact
-- sequence of derived `Hom` groups and the multiplicative stability of the vanishing condition.
/-- The vanishing condition is stable under addition of elements. -/
theorem localizationAwayDerivedHomVanishingCondition_add
    {f g : A} {K : DMod}
    (hf : localizationAwayDerivedHomVanishingCondition f K)
    (hg : localizationAwayDerivedHomVanishingCondition g K) :
    localizationAwayDerivedHomVanishingCondition (f + g) K := by
  -- Route correction: the previous route asked for one oversized Ext-transport package. The
  -- source-faithful route instead tensorizes the Mayer-Vietoris row over `A_(f + g)` by an
  -- arbitrary source object and then applies the distinguished-middle subsingleton lemma above.
  let B := Localization.Away (f + g)
  let _hunit : IsUnit
      (algebraMap A B f + algebraMap A B g) := localizationAway_sum_isUnit (A := A) f g
  have hffg : localizationAwayDerivedHomVanishingCondition (f * (f + g)) K := by
    simpa [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
      localizationAwayDerivedHomVanishingCondition_smul (A := A) (K := K) (f + g) hf
  have hgfg : localizationAwayDerivedHomVanishingCondition (g * (f + g)) K := by
    simpa [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
      localizationAwayDerivedHomVanishingCondition_smul (A := A) (K := K) (f + g) hg
  have hfgfg : localizationAwayDerivedHomVanishingCondition (f * g * (f + g)) K := by
    simpa [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
      localizationAwayDerivedHomVanishingCondition_smul (A := A) (K := K) g hffg
  have hBiprod :
      ∀ {X Y : DMod}, Subsingleton (X ⟶ K) → Subsingleton (Y ⟶ K) →
        Subsingleton ((X ⊞ Y) ⟶ K) := by
    intro X Y hX hY
    letI : Subsingleton (X ⟶ K) := hX
    letI : Subsingleton (Y ⟶ K) := hY
    -- Proof comment: this packages the two overlap vanishings into the single biproduct
    -- vanishing hypothesis required by the distinguished-triangle step.
    exact subsingleton_hom_from_biprod (X := X) (Y := Y) (K := K)
  -- TODO: keep the textbook Mayer-Vietoris route over `B = A_(f + g)`: package
  -- `0 → B → B_f ⊕ B_g → B_fg → 0`, tensor that triangle by an arbitrary
  -- `E : D(B)`, compare the two outer vertices with the already closed conditions `hffg`,
  -- `hgfg`, and `hfgfg`, and then apply
  -- `subsingleton_hom_of_distinguished_middle` to the inverse-rotated triangle.
  let _ := hffg
  let _ := hgfg
  let _ := hfgfg
  let _ := hBiprod
  sorry

-- Proof sketch: `A_{r • f}` is an `A_f`-module via the localization map, so restriction of
-- scalars from `D(A_{r • f})` factors through `D(A_f)`. The vanishing for `f` therefore implies
-- vanishing for `r • f`.
/-- The vanishing condition is stable under multiplication by arbitrary elements of `A`. -/
theorem localizationAwayDerivedHomVanishingCondition_smul
    (r : A) {f : A} {K : DMod}
    (hf : localizationAwayDerivedHomVanishingCondition f K) :
    localizationAwayDerivedHomVanishingCondition (r • f) K := by
  let σ : Localization.Away f →+* Localization.Away (f * r) :=
    IsLocalization.Away.awayToAwayRight
      (S := Localization.Away f) (P := Localization.Away (f * r)) f r
  have hσ : σ.comp (algebraMap A (Localization.Away f)) =
      algebraMap A (Localization.Away (f * r)) := by
    ext a
    simpa [σ] using
      (IsLocalization.Away.awayToAwayRight_eq
        (S := Localization.Away f) (P := Localization.Away (f * r)) f r a)
  -- Restrict scalars from `A_(fr)` to `A_f`, then apply the given vanishing hypothesis.
  simpa [smul_eq_mul, mul_comm] using
    localizationAwayDerivedHomVanishingCondition_of_comparison
      (K := K) σ hσ hf

/-- The ideal of elements `f ∈ A` such that the textbook object `T(K, f)` vanishes, expressed via
the equivalent derived-Hom vanishing condition from Lemma `15.92.1`. -/
def localizationAwayDerivedHomVanishingIdeal (K : DMod) : Ideal A where
  carrier := {f : A | localizationAwayDerivedHomVanishingCondition f K}
  zero_mem' := localizationAwayDerivedHomVanishingCondition_zero K
  add_mem' := fun hf hg ↦ localizationAwayDerivedHomVanishingCondition_add hf hg
  smul_mem' := fun r _ hf ↦ localizationAwayDerivedHomVanishingCondition_smul r hf

-- Proof sketch: this is immediate from the definition of
-- `localizationAwayDerivedHomVanishingIdeal`.
/-- Membership in `K.localizationAwayDerivedHomVanishingIdeal` is exactly the localization-away
derived-Hom vanishing condition. -/
theorem mem_localizationAwayDerivedHomVanishingIdeal_iff (K : DMod) (f : A) :
    f ∈ K.localizationAwayDerivedHomVanishingIdeal ↔
      localizationAwayDerivedHomVanishingCondition f K := Iff.rfl

/-- Helper for Lemma 15.92.2: vanishing after inverting a power of `f` already implies vanishing
after inverting `f` itself. -/
theorem localizationAwayDerivedHomVanishingCondition_of_pow
    {f : A} {n : ℕ} {K : DMod}
    (_hn : 0 < n)
    (hf : localizationAwayDerivedHomVanishingCondition (f ^ n) K) :
    localizationAwayDerivedHomVanishingCondition f K := by
  let σ : Localization.Away (f ^ n) →+* Localization.Away f :=
    IsLocalization.Away.lift
      (S := Localization.Away (f ^ n))
      (P := Localization.Away f)
      (f ^ n)
      (IsLocalization.Away.algebraMap_pow_isUnit
        (S := Localization.Away f) (x := f) n)
  have hσ : σ.comp (algebraMap A (Localization.Away (f ^ n))) =
      algebraMap A (Localization.Away f) := by
    simpa [σ] using
      (IsLocalization.Away.lift_comp
        (S := Localization.Away (f ^ n))
        (P := Localization.Away f)
        (g := algebraMap A (Localization.Away f))
        (x := f ^ n)
        (IsLocalization.Away.algebraMap_pow_isUnit
          (S := Localization.Away f) (x := f) n))
  -- Compare the two away-localizations by the canonical map `A_(f^n) → A_f`.
  exact localizationAwayDerivedHomVanishingCondition_of_comparison
    (K := K) σ hσ hf

-- Proof sketch: the multiplicative closure above shows ideal membership. For radicality, if
-- `f^n` lies in the ideal with `n > 0`, then `A_f ≅ A_{f^n}`, so the vanishing condition for
-- `f^n` is equivalent to the vanishing condition for `f`. This proves that the radical is
-- contained in the ideal.
/-- Lemma 15.92.2: for a commutative ring `A` and `K ∈ D(A)`, the set of elements `f ∈ A` such
that `T(K, f) = 0` is a radical ideal of `A`, formalized through the equivalent localization-away
derived-Hom vanishing condition of Lemma `15.92.1`. -/
@[stacks 091Q]
theorem localizationAwayDerivedHomVanishingIdeal_isRadical (K : DMod) :
    K.localizationAwayDerivedHomVanishingIdeal.IsRadical := by
  intro f hf
  rcases Ideal.mem_radical_iff.mp hf with ⟨n, hn⟩
  by_cases hzero : n = 0
  · -- If `n = 0`, then `1 ∈ I`, hence the ideal is the whole ring.
    have hone : (1 : A) ∈ K.localizationAwayDerivedHomVanishingIdeal := by
      simpa [hzero] using hn
    simpa using Ideal.eq_top_of_isUnit_mem K.localizationAwayDerivedHomVanishingIdeal
      (isUnit_one) hone
  · -- Otherwise apply the power-comparison lemma to the membership statement for `f ^ n`.
    have hnpos : 0 < n := Nat.pos_iff_ne_zero.mpr hzero
    rw [mem_localizationAwayDerivedHomVanishingIdeal_iff] at hn ⊢
    exact localizationAwayDerivedHomVanishingCondition_of_pow hnpos hn

end CategoryTheory.DerivedCategory

end
