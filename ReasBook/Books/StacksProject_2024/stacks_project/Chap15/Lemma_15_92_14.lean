import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import StacksProject_2024.stacks_project.Chap13.Definition_13_34_1
import StacksProject_2024.stacks_project.Chap15.Definition_15_92_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Opposite
open CategoryTheory.SequentialInverseSystem

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)

/-- Helper for Lemma 15.92.14: the product of a stagewise zero family of modules is zero. -/
private theorem module_pi_isZero_of_stagewise_isZero
    {R : Type*} [Ring R] (X : ℕ → ModuleCat R)
    (hX : ∀ n : ℕ, IsZero (X n)) :
    IsZero (∏ᶜ X) := by
  -- The identity on the product vanishes because every projection lands in a zero object.
  refine (IsZero.iff_id_eq_zero _).2 ?_
  apply Pi.hom_ext
  intro n
  exact (hX n).eq_of_tgt _ _

/-- Helper for Lemma 15.92.14: the inverse limit of a stagewise zero sequential system of
modules is zero. -/
private theorem module_limit_isZero_of_stagewise_isZero
    {R : Type*} [Ring R] (Msys : ℕᵒᵖ ⥤ ModuleCat R)
    (hMsys : ∀ n : ℕ, IsZero (Msys.obj (op n))) :
    IsZero (limit Msys) := by
  -- The limit object is zero once all of its projections factor through zero objects.
  refine (IsZero.iff_id_eq_zero _).2 ?_
  apply limit.hom_ext
  intro n
  have hzero : IsZero (Msys.obj n) := by
    simpa using hMsys n.unop
  exact hzero.eq_of_tgt _ _

/-- Helper for Lemma 15.92.14: the first derived inverse limit of a stagewise zero sequential
system of modules is zero. -/
private theorem module_firstDerivedLimit_isZero_of_stagewise_isZero
    {R : Type*} [Ring R] (Msys : ℕᵒᵖ ⥤ ModuleCat R)
    (hMsys : ∀ n : ℕ, IsZero (Msys.obj (op n))) :
    IsZero (SequentialInverseSystem.firstDerivedLimit Msys) := by
  -- The Milnor product object is zero, hence the difference map is automatically epi.
  have hprod : IsZero (∏ᶜ inverseSystemFamily Msys) := by
    refine (IsZero.iff_id_eq_zero _).2 ?_
    apply Pi.hom_ext
    intro n
    exact (hMsys n).eq_of_tgt _ _
  have hEpi : Epi (derivedLimitDifferenceMap Msys) := by
    refine ⟨fun g h _ ↦ hprod.eq_of_src g h⟩
  letI : Epi (derivedLimitDifferenceMap Msys) := hEpi
  simpa [SequentialInverseSystem.firstDerivedLimit] using
    (isZero_cokernel_of_epi (derivedLimitDifferenceMap Msys))

/-- Helper for Lemma 15.92.14: shifting a chosen product yields a chosen product of the shifted
family. -/
private theorem hasProduct_shift {ι : Type*} (X : ι → DMod) [HasProduct X] (n : ℤ) :
    HasProduct (fun i ↦ (X i)⟦n⟧) := by
  let t :
      IsLimit
        (Fan.mk ((∏ᶜ X)⟦n⟧) (fun i ↦ (Pi.π X i)⟦n⟧')) := by
    simpa using
      (Limits.isLimitOfHasProductOfPreservesLimit (shiftFunctor DMod n) X)
  exact ⟨⟨_, t⟩⟩

/-- Helper for Lemma 15.92.14: applying represented Hom to a product identifies it with the
product of the stagewise represented Hom modules. -/
private noncomputable abbrev preadditiveCoyonedaObj_product_iso
    (L : DMod) (X : ℕ → DMod) [HasProduct X] :
    (preadditiveCoyonedaObj L).obj (∏ᶜ X) ≅
      ∏ᶜ fun n ↦ (preadditiveCoyonedaObj L).obj (X n) :=
  let Z : ℕ → ModuleCat (End L)ᵐᵒᵖ := fun n ↦ (preadditiveCoyonedaObj L).obj (X n)
  (LinearEquiv.ofBijective
      (LinearMap.pi fun n ↦
        ModuleCat.Hom.hom ((preadditiveCoyonedaObj L).map (Pi.π X n))) <| by
        constructor
        · intro f g hfg
          apply Pi.hom_ext
          intro n
          have hfg' := congrArg (fun t : (n : ℕ) → (L ⟶ X n) ↦ t n) hfg
          simpa using hfg'
        · intro x
          refine ⟨Pi.lift fun n ↦ x n, ?_⟩
          ext n
          change (Pi.lift fun n ↦ x n) ≫ Pi.π X n = x n
          rw [Pi.lift_π]).toModuleIso ≪≫
    (ModuleCat.piIsoPi Z).symm

/-- Helper for Lemma 15.92.14: multiplication by a unit scalar on an object is an isomorphism. -/
private theorem isIso_units_smul_id
    {R : Type*} [CommRing R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
    (r : Rˣ) (X : C) :
    IsIso ((r : R) • 𝟙 X) := by
  -- The inverse is multiplication by the inverse unit.
  refine ⟨⟨((↑(r⁻¹) : R) • 𝟙 X), ?_, ?_⟩⟩
  · simpa [smul_smul, Linear.comp_units_smul]
  · simpa [smul_smul, Linear.units_smul_comp]

/-- Helper for Lemma 15.92.14: after restricting scalars from `A_(g^e)` to `A`, the endomorphism
`(g^e) • 𝟙` remains an isomorphism. Since localization away from `g` inverts every power of `g`,
this is the exact source-side bridge needed for the textbook argument. -/
private theorem localizationAway_power_restrictScalars_smul_id_isIso
    (g : A) (e : ℕ) (E : DerivedCategory (ModuleCat (Localization.Away g))) :
    IsIso
      ((g ^ e : A) •
        𝟙 (((ModuleCat.restrictScalars
          (algebraMap A (Localization.Away g))).mapDerivedCategory.obj E))) := by
  let F :=
    (ModuleCat.restrictScalars (algebraMap A (Localization.Away g))).mapDerivedCategory
  let F₀ :=
    (ModuleCat.restrictScalars (algebraMap A (Localization.Away g))).mapHomologicalComplex
      (ComplexShape.up ℤ)
  let C := DerivedCategory.Q.objPreimage E
  let eE : DerivedCategory.Q.obj C ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let eX : F.obj E ≅ DerivedCategory.Q.obj (F₀.obj C) :=
    F.mapIso eE.symm ≪≫ (ModuleCat.restrictScalars
      (algebraMap A (Localization.Away g))).mapDerivedCategoryFactors.app C
  let u : (Localization.Away g)ˣ :=
    (IsLocalization.Away.algebraMap_isUnit g).unit ^ e
  have hcomplex_map :
      F₀.map (((u : Localization.Away g) • 𝟙 C) : C ⟶ C) =
        ((g ^ e : A) • 𝟙 (F₀.obj C)) := by
    -- On cochain complexes, restriction of scalars acts componentwise on the scalar map.
    ext i x
    rw [Functor.mapHomologicalComplex_map_f]
    let y : C.X i := x
    change (((algebraMap A (Localization.Away g)) g ^ e : Localization.Away g) • y = g ^ e • x)
    rw [← map_pow]
    rfl
  have hsource_iso :
      IsIso (((u : Localization.Away g) • 𝟙 C) : C ⟶ C) := by
    -- Multiplication by a unit is invertible on the concrete preimage complex.
    simpa using
      (isIso_units_smul_id (R := Localization.Away g) u C)
  have hcomplex_iso :
      IsIso (((g ^ e : A) • 𝟙 (F₀.obj C)) : F₀.obj C ⟶ F₀.obj C) := by
    -- The localized scalar action is invertible before passing to the derived category.
    simpa [hcomplex_map] using
      (Functor.map_isIso F₀
        (((u : Localization.Away g) • 𝟙 C) : C ⟶ C))
  have hderived_iso :
      IsIso
        (((g ^ e : A) • 𝟙 (DerivedCategory.Q.obj (F₀.obj C))) :
          DerivedCategory.Q.obj (F₀.obj C) ⟶ DerivedCategory.Q.obj (F₀.obj C)) := by
    -- Applying `Q` preserves the isomorphism coming from the complex-level scalar action.
    simpa [Functor.map_smul] using
      (Functor.map_isIso DerivedCategory.Q
        (((g ^ e : A) • 𝟙 (F₀.obj C)) : F₀.obj C ⟶ F₀.obj C))
  have hconj :
      eX.hom ≫ ((g ^ e : A) • 𝟙 (DerivedCategory.Q.obj (F₀.obj C))) ≫ eX.inv =
        ((g ^ e : A) • 𝟙 (F.obj E)) := by
    -- Scalar multiplication commutes with the comparison isomorphism to the concrete complex.
    apply (cancel_mono eX.hom).1
    calc
      (eX.hom ≫ ((g ^ e : A) • 𝟙 (DerivedCategory.Q.obj (F₀.obj C))) ≫ eX.inv) ≫ eX.hom =
          eX.hom ≫ ((g ^ e : A) • 𝟙 (DerivedCategory.Q.obj (F₀.obj C))) := by
            simp
      _ =
          (g ^ e : A) • eX.hom := by
            simp [CategoryTheory.Linear.comp_smul]
      _ = ((g ^ e : A) • 𝟙 (F.obj E)) ≫ eX.hom := by
            simp [CategoryTheory.Linear.smul_comp]
  -- Conjugating the concrete isomorphism back across `eX` gives the desired source action.
  simpa [hconj] using
    (show IsIso
      (eX.hom ≫ ((g ^ e : A) • 𝟙 (DerivedCategory.Q.obj (F₀.obj C))) ≫ eX.inv) by
        infer_instance)

/-- Helper for Lemma 15.92.14: if `(g^e) • 𝟙` acts by zero on `K`, then every morphism from an
object of `D(A_g)` to `K` vanishes after restriction of scalars. This follows because
localization away from `g` already makes `g^e` invertible on the source. -/
private theorem localizationAwayDerivedHomVanishingCondition_of_power_zero_action
    (g : A) (e : ℕ) (K : DMod)
    (hzero : (g ^ e : A) • 𝟙 K = 0) :
    localizationAwayDerivedHomVanishingCondition g K := by
  intro E
  let F :=
    (ModuleCat.restrictScalars (algebraMap A (Localization.Away g))).mapDerivedCategory
  let X : DMod := F.obj E
  have hsourceIso :
      IsIso ((g ^ e : A) • 𝟙 X) :=
    localizationAway_power_restrictScalars_smul_id_isIso g e E
  refine ⟨fun φ ψ ↦ ?_⟩
  have hφ : φ = 0 := by
    -- Route correction: prove vanishing for the annihilating power `g ^ e`, where the source
    -- action is canonically invertible after localization, and only later descend to `g`.
    have hφzero : ((g ^ e : A) • 𝟙 X) ≫ φ = 0 := by
      calc
        ((g ^ e : A) • 𝟙 X) ≫ φ = (g ^ e : A) • φ := by
          simp [CategoryTheory.Linear.smul_comp]
        _ = φ ≫ ((g ^ e : A) • 𝟙 K) := by
          simp [CategoryTheory.Linear.comp_smul]
        _ = 0 := by
          rw [hzero]
          simp
    have hcancel :
        inv ((g ^ e : A) • 𝟙 X) ≫ (((g ^ e : A) • 𝟙 X) ≫ φ) = φ := by
      simpa [Category.assoc] using
        (IsIso.inv_hom_id_assoc ((g ^ e : A) • 𝟙 X) φ)
    calc
      φ = inv ((g ^ e : A) • 𝟙 X) ≫ (((g ^ e : A) • 𝟙 X) ≫ φ) := by
        exact hcancel.symm
      _ = inv ((g ^ e : A) • 𝟙 X) ≫ 0 := by
        rw [hφzero]
      _ = 0 := by simp
  have hψ : ψ = 0 := by
    have hψzero : ((g ^ e : A) • 𝟙 X) ≫ ψ = 0 := by
      calc
        ((g ^ e : A) • 𝟙 X) ≫ ψ = (g ^ e : A) • ψ := by
          simp [CategoryTheory.Linear.smul_comp]
        _ = ψ ≫ ((g ^ e : A) • 𝟙 K) := by
          simp [CategoryTheory.Linear.comp_smul]
        _ = 0 := by
          rw [hzero]
          simp
    have hcancel :
        inv ((g ^ e : A) • 𝟙 X) ≫ (((g ^ e : A) • 𝟙 X) ≫ ψ) = ψ := by
      simpa [Category.assoc] using
        (IsIso.inv_hom_id_assoc ((g ^ e : A) • 𝟙 X) ψ)
    calc
      ψ = inv ((g ^ e : A) • 𝟙 X) ≫ (((g ^ e : A) • 𝟙 X) ≫ ψ) := by
        exact hcancel.symm
      _ = inv ((g ^ e : A) • 𝟙 X) ≫ 0 := by
        rw [hψzero]
      _ = 0 := by simp
  simpa [hφ, hψ]

/-- Helper for Lemma 15.92.14: a complex annihilated by powers of each `f ∈ I` is derived
complete with respect to `I`. -/
private theorem stage_isDerivedCompleteWithRespectTo_of_power_zero
    (I : Ideal A) (K : DMod)
    (hpow : ∀ f ∈ I, ∃ e : ℕ, (f ^ e : A) • 𝟙 K = 0) :
    K.IsDerivedCompleteWithRespectTo I := by
  -- Test derived completeness against each `f ∈ I`. The source proof localizes away from `f`
  -- itself, using that `f^e` is invertible on any `A_f`-object.
  rw [DerivedCategory.isDerivedCompleteWithRespectTo_iff]
  intro f hf
  rcases hpow f hf with ⟨e, he⟩
  exact localizationAwayDerivedHomVanishingCondition_of_power_zero_action f e K he

/-- Helper for Lemma 15.92.14: a derived-complete target has zero represented-Hom module from
any source obtained by restricting scalars from `D(A_f)`. -/
private theorem localized_source_represented_hom_isZero_of_isDerivedCompleteWithRespectTo
    (I : Ideal A) (f : A) (hf : f ∈ I) (K : DMod)
    (hK : K.IsDerivedCompleteWithRespectTo I)
    (E : DerivedCategory (ModuleCat (Localization.Away f))) :
    let F := (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory
    let L : DMod := F.obj E
    IsZero ((preadditiveCoyonedaObj L).obj K) := by
  let F := (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory
  let L : DMod := F.obj E
  -- Proof comment: derived completeness gives a subsingleton Hom-set from the localized source.
  have hsub : Subsingleton (L ⟶ K) := by
    simpa [F, L] using
      ((DerivedCategory.isDerivedCompleteWithRespectTo_iff K I).1 hK f hf E)
  -- Proof comment: the represented Hom module is zero because its underlying type is subsingleton.
  change IsZero (ModuleCat.of (End L)ᵐᵒᵖ (L ⟶ K))
  letI : Subsingleton (L ⟶ K) := hsub
  exact ModuleCat.isZero_of_subsingleton _

/-- Helper for Lemma 15.92.14: derived completeness also kills the shifted represented-Hom module
from any source obtained by restricting scalars from `D(A_f)`. -/
private theorem localized_source_shifted_represented_hom_isZero_of_isDerivedCompleteWithRespectTo
    (I : Ideal A) (f : A) (hf : f ∈ I) (K : DMod)
    (hK : K.IsDerivedCompleteWithRespectTo I)
    (E : DerivedCategory (ModuleCat (Localization.Away f))) :
    let F := (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory
    let L : DMod := F.obj E
    IsZero ((preadditiveCoyonedaObj L).obj (K⟦(-1 : ℤ)⟧)) := by
  let F := (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory
  let L : DMod := F.obj E
  -- Proof comment: apply derived completeness to the shifted source object `E⟦1⟧`.
  have hshift_source :
      Subsingleton (F.obj (E⟦(1 : ℤ)⟧) ⟶ K) := by
    exact ((DerivedCategory.isDerivedCompleteWithRespectTo_iff K I).1 hK f hf (E⟦(1 : ℤ)⟧))
  have hshifted : Subsingleton (L⟦(1 : ℤ)⟧ ⟶ K) := by
    let e : F.obj (E⟦(1 : ℤ)⟧) ≅ L⟦(1 : ℤ)⟧ := (F.commShiftIso (1 : ℤ)).app E
    -- Proof comment: transport the subsingleton statement across the functorial shift comparison.
    refine ⟨fun g h ↦ ?_⟩
    exact (cancel_epi e.hom).1 (hshift_source.elim (e.hom ≫ g) (e.hom ≫ h))
  have hsub : Subsingleton (L ⟶ K⟦(-1 : ℤ)⟧) := by
    let e :
        (L ⟶ K⟦(-1 : ℤ)⟧) ≃ (L⟦(1 : ℤ)⟧ ⟶ K) :=
      (((shiftEquiv DMod (-1 : ℤ)).symm.toAdjunction.homEquiv L K).symm)
    -- Proof comment: the standard shift adjunction identifies the desired Hom-set with the
    -- already-vanishing shifted-source Hom-set.
    refine ⟨fun g h ↦ e.injective (hshifted.elim (e g) (e h))⟩
  -- Proof comment: pass from subsingleton morphisms to the zero represented-Hom module.
  change IsZero (ModuleCat.of (End L)ᵐᵒᵖ (L ⟶ K⟦(-1 : ℤ)⟧))
  letI : Subsingleton (L ⟶ K⟦(-1 : ℤ)⟧) := hsub
  exact ModuleCat.isZero_of_subsingleton _

/-- Helper for Lemma 15.92.14: if every stage is derived complete, then the ordinary represented
Hom tower from a localized source is stagewise zero. -/
private theorem stagewise_represented_hom_isZero_of_stagewise_complete
    (I : Ideal A) (Ksys : ℕᵒᵖ ⥤ DMod) (f : A) (hf : f ∈ I)
    (E : DerivedCategory (ModuleCat (Localization.Away f)))
    (hstage : ∀ n : ℕ, (Ksys.obj (op n)).IsDerivedCompleteWithRespectTo I)
    (n : ℕ) :
    let L : DMod :=
      ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E)
    IsZero (((Ksys ⋙ preadditiveCoyonedaObj L).obj (op n))) := by
  -- Proof comment: apply the object-level represented-Hom vanishing to the `n`-th stage.
  let L : DMod :=
    ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E)
  simpa [L] using
    localized_source_represented_hom_isZero_of_isDerivedCompleteWithRespectTo
      I f hf (Ksys.obj (op n)) (hstage n) E

/-- Helper for Lemma 15.92.14: if every stage is derived complete, then the shifted represented
Hom tower from a localized source is stagewise zero. -/
private theorem stagewise_shifted_represented_hom_isZero_of_stagewise_complete
    (I : Ideal A) (Ksys : ℕᵒᵖ ⥤ DMod) (f : A) (hf : f ∈ I)
    (E : DerivedCategory (ModuleCat (Localization.Away f)))
    (hstage : ∀ n : ℕ, (Ksys.obj (op n)).IsDerivedCompleteWithRespectTo I)
    (n : ℕ) :
    let L : DMod :=
      ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E)
    IsZero ((((Ksys ⋙ shiftFunctor DMod (-1 : ℤ)) ⋙ preadditiveCoyonedaObj L).obj (op n))) := by
  -- Proof comment: apply the shifted object-level vanishing to the `n`-th stage.
  let L : DMod :=
    ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E)
  simpa [L] using
    localized_source_shifted_represented_hom_isZero_of_isDerivedCompleteWithRespectTo
      I f hf (Ksys.obj (op n)) (hstage n) E

/-
Domain-style sampling:
- primary domain: derived completeness in `D(A)` and its behavior under sequential derived limits;
- sampled owner-side declarations:
  `DerivedCategory.IsDerivedCompleteWithRespectTo`,
  `DerivedCategory.isDerivedCompleteWithRespectTo_iff`,
  `CategoryTheory.IsDerivedLimit`,
  `CategoryTheory.DerivedCategory.localizationAwayT_isDerivedLimit`;
- best owner abstraction: the canonical predicate `K.IsDerivedCompleteWithRespectTo I` together
  with the ambient derived-limit owner `IsDerivedLimit Ksys K'`;
- primitive data: the ideal `I`, the inverse system `Ksys`, a stagewise derived-completeness
  witness, and a chosen derived-limit witness;
- derived API: the stronger source-facing bridge where stagewise derived completeness is produced
  from the textbook power-zero hypothesis.

Layer triage:
- `source-facing`: the power-zero formulation from the Stacks-project statement;
- `core/canonical`: derived completeness of each stage and the owner predicate `IsDerivedLimit`;
- `bridge/view`: the passage from stagewise power-zero actions to stagewise derived completeness. -/

-- Proof sketch: derived completeness with respect to `I` is defined by vanishing of the
-- localization-away objects `T(-, f)` for `f ∈ I`. For a fixed `f`, Lemma `15.92.1` realizes
-- `T(-, f)` as a derived limit of the tower with transition map `f • 𝟙`, so applying it to a
-- Milnor triangle for `Ksys` reduces the claim to the fact that zero objects are preserved under
-- sequential derived limits when every stage already satisfies the vanishing condition.
/-- Any derived limit of a sequential inverse system of `I`-derived-complete objects is again
derived complete with respect to `I`. -/
theorem isDerivedCompleteWithRespectTo_of_isDerivedLimit_of_stagewise
    (I : Ideal A) (Ksys : ℕᵒᵖ ⥤ DMod) (K' : DMod)
    (hstage :
      ∀ n : ℕ, (Ksys.obj (op n)).IsDerivedCompleteWithRespectTo I)
    (hlim : IsDerivedLimit Ksys K') :
    K'.IsDerivedCompleteWithRespectTo I := by
  -- We test derived completeness against a fixed localization-away object and apply exactness to
  -- the inverse-rotated Milnor triangle. The two outer represented-Hom terms are zero because
  -- products preserve stagewise vanishing for the ordinary and shifted towers.
  rw [DerivedCategory.isDerivedCompleteWithRespectTo_iff]
  intro f hf E
  let F := (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory
  let L : DMod := F.obj E
  let Fadd := preadditiveCoyoneda.obj (Opposite.op L)
  rcases hlim with ⟨hprodKsys, ⟨ι, δ, hδ⟩⟩
  letI : HasProduct (inverseSystemFamily Ksys) := hprodKsys
  have hright_stage :
      ∀ n : ℕ, IsZero (((Ksys ⋙ preadditiveCoyonedaObj L).obj (op n))) := by
    -- Proof comment: the ordinary represented-Hom tower vanishes stagewise by derived completeness.
    intro n
    simpa [F, L] using
      stagewise_represented_hom_isZero_of_stagewise_complete I Ksys f hf E hstage n
  have hleft_stage :
      ∀ n : ℕ,
        IsZero ((((Ksys ⋙ shiftFunctor DMod (-1 : ℤ)) ⋙ preadditiveCoyonedaObj L).obj (op n))) := by
    -- Proof comment: the shifted represented-Hom tower vanishes by the dedicated transport helper.
    intro n
    simpa [F, L] using
      stagewise_shifted_represented_hom_isZero_of_stagewise_complete I Ksys f hf E hstage n
  have hright_product_module :
      IsZero ((preadditiveCoyonedaObj L).obj (∏ᶜ inverseSystemFamily Ksys)) := by
    have hpi :
        IsZero
          (∏ᶜ fun n ↦ (preadditiveCoyonedaObj L).obj (Ksys.obj (op n))) :=
      by
        refine (IsZero.iff_id_eq_zero _).2 ?_
        apply Pi.hom_ext
        intro n
        exact (hright_stage n).eq_of_tgt _ _
    exact hpi.of_iso
      (preadditiveCoyonedaObj_product_iso L (inverseSystemFamily Ksys))
  let shiftedFamily : ℕ → DMod := fun n ↦ (Ksys.obj (op n))⟦(-1 : ℤ)⟧
  letI : HasProduct shiftedFamily := hasProduct_shift (inverseSystemFamily Ksys) (-1 : ℤ)
  have hleft_product_module :
      IsZero ((preadditiveCoyonedaObj L).obj ((∏ᶜ inverseSystemFamily Ksys)⟦(-1 : ℤ)⟧)) := by
    have hpi :
        IsZero (∏ᶜ fun n ↦ (preadditiveCoyonedaObj L).obj (shiftedFamily n)) :=
      by
        refine (IsZero.iff_id_eq_zero _).2 ?_
        apply Pi.hom_ext
        intro n
        exact (hleft_stage n).eq_of_tgt _ _
    have hshifted_product :
        IsZero ((preadditiveCoyonedaObj L).obj (∏ᶜ shiftedFamily)) := by
      exact hpi.of_iso
        (preadditiveCoyonedaObj_product_iso L shiftedFamily)
    let e :
        ((∏ᶜ inverseSystemFamily Ksys)⟦(-1 : ℤ)⟧) ≅
          ∏ᶜ shiftedFamily :=
      PreservesProduct.iso (shiftFunctor DMod (-1 : ℤ)) (inverseSystemFamily Ksys)
    exact hshifted_product.of_iso ((preadditiveCoyonedaObj L).mapIso e)
  have hright_product :
      IsZero (Fadd.obj (∏ᶜ inverseSystemFamily Ksys)) := by
    simpa [Fadd] using
      (forget₂ (ModuleCat (End L)ᵐᵒᵖ) AddCommGrpCat).map_isZero hright_product_module
  have hleft_product :
      IsZero (Fadd.obj ((∏ᶜ inverseSystemFamily Ksys)⟦(-1 : ℤ)⟧)) := by
    simpa [Fadd] using
      (forget₂ (ModuleCat (End L)ᵐᵒᵖ) AddCommGrpCat).map_isZero hleft_product_module
  let T : Triangle DMod := Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ
  let S :=
    (shortComplexOfDistTriangle T.invRotate (inv_rot_of_distTriang _ hδ)).map Fadd
  have hmiddle_add : IsZero S.X₂ := by
    have hexact : S.Exact := by
      simpa [S] using Fadd.map_distinguished_exact T.invRotate (inv_rot_of_distTriang _ hδ)
    refine hexact.isZero_X₂ ?_ ?_
    · exact hleft_product.eq_of_src _ _
    · exact hright_product.eq_of_tgt _ _
  letI : Subsingleton (L ⟶ K') := by
    simpa [Fadd, S, T] using AddCommGrpCat.subsingleton_of_isZero hmiddle_add
  simpa [L]

-- Proof sketch: for each stage `K_n` and each `f ∈ I`, if some power `f^e` acts by zero on
-- `K_n`, then after inverting `f` the identity of `K_n` vanishes, so `K_n` is derived complete
-- with respect to `I`. Apply the canonical stagewise derived-completeness theorem above to the
-- resulting tower.
/-- Lemma 15.92.14: if `(K_n)` is a sequential inverse system in `D(A)` such that for every
`f ∈ I` and every `n` some power `f^e` acts by zero on `K_n`, then any derived limit of `(K_n)`
is derived complete with respect to `I`. The textbook object
`R \!\varprojlim_n (K \otimes_A^{\mathbf L} K_n)` is the intended application, since its stages
inherit the same annihilation property. -/
theorem isDerivedCompleteWithRespectTo_of_isDerivedLimit_of_stagewise_power_zero
    (I : Ideal A) (Ksys : ℕᵒᵖ ⥤ DMod) (K' : DMod)
    (hpow :
      ∀ f ∈ I, ∀ n : ℕ, ∃ e : ℕ, (f ^ e : A) • 𝟙 (Ksys.obj (op n)) = 0)
    (hlim : IsDerivedLimit Ksys K') :
    K'.IsDerivedCompleteWithRespectTo I := by
  -- Reduce the textbook power-zero hypothesis to stagewise derived completeness.
  apply isDerivedCompleteWithRespectTo_of_isDerivedLimit_of_stagewise I Ksys K'
  · intro n
    exact stage_isDerivedCompleteWithRespectTo_of_power_zero I (Ksys.obj (op n))
      (fun f hf ↦ hpow f hf n)
  · exact hlim

end

end CategoryTheory
