import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import StacksProject_2024.stacks_project.Chap10.Proposition_10_89_3
import StacksProject_2024.stacks_project.Chap13.Lemma_13_19_8
import StacksProject_2024.stacks_project.Chap13.Definition_13_18_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_34_7
import StacksProject_2024.stacks_project.Chap15.Definition_15_65_1
import StacksProject_2024.stacks_project.Chap15.Definition_15_70_1
import StacksProject_2024.stacks_project.Chap15.Definition_15_75_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_70_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_72_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_74_3
import StacksProject_2024.stacks_project.Chap15.«15_74_0_2»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "Mod" => ModuleCat R
local notation "DMod" => DerivedCategory Mod
local notation "RHomPkg" => MonoidalClosed DMod
local notation "KQ" => HomotopyCategory.quotient Mod (ComplexShape.up ℤ)

open CochainComplex.HomComplex.CohomologyClass
open scoped DerivedInternalHom

/- Domain-style sampling for 15.99.1:
- primary domain: isomorphism criteria for the tensor-right/internal-Hom comparison in `D(R)`;
- sampled owner declarations:
  `CategoryTheory.derivedInternalHom_tensor_right_comparison`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsPerfect`,
  `DerivedCategory.IsPseudoCoherent`,
  `HasFiniteInjectiveDimension`;
- best owner abstraction:
  `source-facing`: the textbook isomorphism criterion for the canonical comparison morphism from
    Lemma `15.74.3`;
  `core/canonical`: the chosen monoidal-closed owner `H : MonoidalClosed DMod`, the comparison
    morphism `derivedInternalHom_tensor_right_comparison H K L M`, and the Chapter 15 owners
    `K.IsPerfect`, `K.IsPseudoCoherent`, and `HasFiniteInjectiveDimension M`;
  `bridge/view`: the bounded-below branch hypothesis `∃ n : ℤ, L.IsGE n`, which expresses the
    source condition without forcing a global `D⁺(R)` owner on the perfect branch.
- primitive vs. derived:
  the primitive input is the comparison owner `H`, the object `L : D(R)`, and the branch-level
  hypotheses on `K`, `L`, and `M`; a bounded-below owner object `L : D⁺(R)` is derived data, so
  it should not be built into the theorem header when only one disjunct needs it.
-/

-- Proof sketch: choose the bounded-above finite-projective representative of `K` supplied either
-- by perfectness or by pseudo-coherence, and compute the comparison on cochain complexes as in
-- Lemma `15.72.6`. In the perfect case the boundedness of the representative makes the degreewise
-- tensor-Hom comparison a finite direct-sum argument; in the pseudo-coherent case, combine the
-- bounded-above representative of `K` with a bounded-below representative of `L` and a bounded
-- injective representative of `M` coming from finite injective dimension to get the same finiteness
-- on the relevant total-complex degrees.
-- Route correction: the Chapter 15 import DAG has been repaired so the proof now genuinely
-- stops at the source-faithful comparison layer inside this file, not at the duplicated
-- monoidal-owner instances from Lemma `15.58.3`.
/-- Helper for Lemma 15.99.1: finite injective dimension provides an injective-amplitude witness. -/
lemma exists_injective_amplitude_of_hasFiniteInjectiveDimension
    (M : DMod) (hM : HasFiniteInjectiveDimension M) :
    ∃ a b : ℤ, HasInjectiveAmplitudeIn M a b := by
  -- This is exactly the source-facing definition of finite injective dimension.
  exact hM

/-- Helper for Lemma 15.99.1: a perfect object admits a bounded finite-projective cochain model. -/
lemma exists_perfect_representation
    (K : DMod) (hK : K.IsPerfect) :
    ∃ P : Cpx, CochainComplex.IsBoundedFiniteProjective P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ K) := by
  -- Unpack the defining perfect representative and reorient the isomorphism toward `K`.
  rcases hK with ⟨P, hP, hPerfect⟩
  exact ⟨P, hPerfect, ⟨hP.symm⟩⟩

/-- Helper for Lemma 15.99.1: a pseudo-coherent object admits a bounded-above finite-free
cochain model. -/
lemma exists_pseudoCoherent_representation
    (K : DMod) (hK : K.IsPseudoCoherent) :
    ∃ (E : Cpx) (b : ℤ), E.IsStrictlyLE b ∧
      CochainComplex.IsTermwiseFiniteFree E ∧
      Nonempty (DerivedCategory.Q.obj E ≅ K) := by
  -- Unpack the defining pseudo-coherent representative and upgrade the comparison morphism to an
  -- isomorphism in the derived category.
  rcases hK with ⟨E, ⟨b, hE⟩, hFree, α, hα⟩
  let _ : IsIso α := hα
  exact ⟨E, b, hE, hFree, ⟨asIso α⟩⟩

/-- Helper for Lemma 15.99.1: a bounded-below derived object admits a bounded-below cochain
representative obtained from the canonical preimage by lower truncation. -/
lemma exists_boundedBelow_representation
    (L : DMod) (hL : ∃ n : ℤ, L.IsGE n) :
    ∃ (A : Cpx) (n : ℤ), A.IsStrictlyGE n ∧ Nonempty (DerivedCategory.Q.obj A ≅ L) := by
  rcases hL with ⟨n, hn⟩
  -- Transport the lower-vanishing statement from `L` to the chosen cochain preimage.
  have hPreimageGE : (DerivedCategory.Q.objPreimage L).IsGE n := by
    rw [CochainComplex.isGE_iff]
    intro i hi
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    rw [DerivedCategory.isGE_iff] at hn
    exact (objPreimage_homology_iso (R := R) L i).isZero_iff.1 (hn i hi)
  let _ : (DerivedCategory.Q.objPreimage L).IsGE n := hPreimageGE
  have hπ :
      IsIso (DerivedCategory.Q.map ((DerivedCategory.Q.objPreimage L).πTruncGE n)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  let _ : IsIso (DerivedCategory.Q.map ((DerivedCategory.Q.objPreimage L).πTruncGE n)) := hπ
  -- The lower truncation now gives a bounded-below model whose image is still `L`.
  refine ⟨(DerivedCategory.Q.objPreimage L).truncGE n, n, inferInstance, ?_⟩
  exact ⟨(asIso (DerivedCategory.Q.map ((DerivedCategory.Q.objPreimage L).πTruncGE n))).symm ≪≫
    DerivedCategory.Q.objObjPreimageIso L⟩

/-- Helper for Lemma 15.99.1: finite injective dimension gives a bounded injective cochain model
of the derived object. -/
lemma exists_bounded_injective_representation
    (M : DMod) (hM : HasFiniteInjectiveDimension M) :
    ∃ (I : Cpx) (a b : ℤ), I.IsStrictlyGE a ∧ I.IsStrictlyLE b ∧
      (∀ i : ℤ, Injective (I.X i)) ∧ Nonempty (DerivedCategory.Q.obj I ≅ M) := by
  rcases exists_injective_amplitude_of_hasFiniteInjectiveDimension M hM with ⟨a, b, hAmp⟩
  -- Unpack the amplitude witness and reorient the derived isomorphism toward `M`.
  rcases hAmp with ⟨I, hIge, hIle, hIinj, ⟨eI⟩⟩
  exact ⟨I, a, b, hIge, hIle, hIinj, ⟨eI.symm⟩⟩

/-- Helper for Lemma 15.99.1: the bounded injective model supplied by finite injective dimension
is already K-injective. -/
lemma exists_kInjective_representation_of_hasFiniteInjectiveDimension
    (M : DMod) (hM : HasFiniteInjectiveDimension M) :
    ∃ (I : Cpx) (_ : I.IsKInjective), Nonempty (DerivedCategory.Q.obj I ≅ M) := by
  obtain ⟨I, a, b, hIge, hIle, hIinj, hI⟩ := exists_bounded_injective_representation M hM
  -- A bounded-below complex of injectives is K-injective by the chapter owner from
  -- Definition `13.18.1`.
  let _ : I.IsStrictlyGE a := hIge
  let _ : ∀ i : ℤ, Injective (I.X i) := hIinj
  let _ : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  let _ := hIle
  exact ⟨I, inferInstance, hI⟩

/-- Helper for Lemma 15.99.1: specialize the Chapter 13 K-injective replacement theorem to
cochain complexes of `R`-modules. -/
lemma exists_quasiIso_to_kInjective_moduleCat
    (K : Cpx) :
    ∃ (I : Cpx) (_ : I.IsKInjective) (f : K ⟶ I), QuasiIso f := by
  -- The Chapter 13 existence theorem already applies to `ModuleCat R` through the imported
  -- abelian, exact-product, and enough-injectives instances.
  exact CategoryTheory.exists_quasiIso_to_kInjective K

/-- Helper for Lemma 15.99.1: every derived object admits a K-injective cochain representative. -/
lemma exists_kInjective_representation
    (M : DMod) :
    ∃ (I : Cpx) (_ : I.IsKInjective), Nonempty (DerivedCategory.Q.obj I ≅ M) := by
  obtain ⟨I, hI, f, hf⟩ :=
    exists_quasiIso_to_kInjective_moduleCat (DerivedCategory.Q.objPreimage M)
  let _ : I.IsKInjective := hI
  let _ : QuasiIso f := hf
  -- The quasi-isomorphism becomes an isomorphism after passing to the derived category.
  have hQf : IsIso (DerivedCategory.Q.map f) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  let _ : IsIso (DerivedCategory.Q.map f) := hQf
  -- Compose the transported preimage comparison with `Q.objObjPreimageIso` to recover `M`.
  refine ⟨I, hI, ?_⟩
  exact ⟨(asIso (DerivedCategory.Q.map f)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso M⟩

/-- Helper for Lemma 15.99.1: transport across source and target isomorphisms acts additively on
Hom groups in `D(R)`. -/
private theorem iso_hom_congr_add_equiv_map_add
    {X Y X₁ Y₁ : DMod} (α : X ≅ X₁) (β : Y ≅ Y₁) (f g : X ⟶ Y) :
    α.homCongr β (f + g) = α.homCongr β f + α.homCongr β g := by
  -- This is just bilinearity of composition rewritten through `Iso.homCongr`.
  simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp]

/-- Helper for Lemma 15.99.1: isomorphisms on source and target induce an additive equivalence on
Hom groups. -/
private noncomputable def iso_hom_congr_add_equiv
    {X Y X₁ Y₁ : DMod} (α : X ≅ X₁) (β : Y ≅ Y₁) :
    (X ⟶ Y) ≃+ (X₁ ⟶ Y₁) :=
  { toEquiv := α.homCongr β
    map_add' := iso_hom_congr_add_equiv_map_add α β }

/-- Helper for Lemma 15.99.1: a bounded-above projective source computes shifted derived morphisms
by passing from the homotopy category to the derived category and then across the canonical shift
comparison. -/
private noncomputable def projective_source_shifted_hom_add_equiv
    (P : CochainComplex.ProjectiveMinus Mod) (A : Cpx) (n : ℤ) :
    ((KQ).obj P ⟶ (KQ).obj (A⟦n⟧)) ≃+
      ShiftedHom (DerivedCategory.Q.obj (P : Cpx)) (DerivedCategory.Q.obj A) n :=
  let e₁ :
      ((KQ).obj P ⟶ (KQ).obj (A⟦n⟧)) ≃+
        (DerivedCategory.Q.obj (P : Cpx) ⟶ DerivedCategory.Q.obj (A⟦n⟧)) :=
    AddEquiv.ofBijective
      (DerivedCategory.Qh.mapAddHom :
        ((KQ).obj P ⟶ (KQ).obj (A⟦n⟧)) →+
          (DerivedCategory.Q.obj (P : Cpx) ⟶ DerivedCategory.Q.obj (A⟦n⟧)))
      (CochainComplex.homotopyCategory_to_derived_bijective_of_boundedAbove_projective P (A⟦n⟧))
  let e₂ :
      (DerivedCategory.Q.obj (P : Cpx) ⟶ DerivedCategory.Q.obj (A⟦n⟧)) ≃+
        ShiftedHom (DerivedCategory.Q.obj (P : Cpx)) (DerivedCategory.Q.obj A) n :=
    iso_hom_congr_add_equiv (Iso.refl _) ((DerivedCategory.Q.commShiftIso n).app A)
  e₁.trans e₂

/-- Helper for Lemma 15.99.1: for a bounded-above projective source model, the canonical
`CochainComplex.HomComplex` cohomology already matches the cohomology of the chosen derived
internal-Hom object degreewise. -/
noncomputable def projective_source_homology_add_equiv_derivedHom
    (H : RHomPkg)
    (P : CochainComplex.ProjectiveMinus Mod) (A : Cpx) (n : ℤ) :
    (CochainComplex.HomComplex (P : Cpx) A).homology n ≃+
      ((DerivedCategory.homologyFunctor Mod n).obj
        (RHom[H](DerivedCategory.Q.obj (P : Cpx), DerivedCategory.Q.obj A))) := by
  -- The projective model computes shifted morphisms from `P` directly.
  let e₁ :
      (CochainComplex.HomComplex (P : Cpx) A).homology n ≃+
        ((KQ).obj P ⟶ (KQ).obj (A⟦n⟧)) :=
    (CochainComplex.HomComplex.homologyAddEquiv (P : Cpx) A n).trans homAddEquiv
  let e₂ :
      ((KQ).obj P ⟶ (KQ).obj (A⟦n⟧)) ≃+
        ShiftedHom (DerivedCategory.Q.obj (P : Cpx)) (DerivedCategory.Q.obj A) n :=
    projective_source_shifted_hom_add_equiv P A n
  -- The chosen `RHom` object has the same degree-`n` cohomology by the Chapter `15.74.0.2`
  -- cohomology-to-shifted-Hom bridge.
  let e₃ :
      ((DerivedCategory.homologyFunctor Mod n).obj
        (RHom[H](DerivedCategory.Q.obj (P : Cpx), DerivedCategory.Q.obj A))) ≃+
        ShiftedHom (DerivedCategory.Q.obj (P : Cpx)) (DerivedCategory.Q.obj A) n :=
      (derivedHom_cohomology_iso_shiftedHom (R := R) H
      (DerivedCategory.Q.obj (P : Cpx)) (DerivedCategory.Q.obj A) n).toAddEquiv
  exact (e₁.trans e₂).trans e₃.symm

/-- Helper for Lemma 15.99.1: the projective-source cohomology comparison is bijective in every
degree. -/
theorem projective_source_homology_add_equiv_derivedHom_bijective
    (H : RHomPkg)
    (P : CochainComplex.ProjectiveMinus Mod) (A : Cpx) (n : ℤ) :
    Function.Bijective (projective_source_homology_add_equiv_derivedHom (R := R) H P A n) := by
  -- Record the already proved additive equivalence as a bijection for later transport into
  -- `derivedCategory_isIso_iff_homology_map_isIso`.
  exact (projective_source_homology_add_equiv_derivedHom (R := R) H P A n).bijective

/-- Helper for Lemma 15.99.1: for a K-injective target model, the canonical
`CochainComplex.HomComplex` cohomology already matches the cohomology of the chosen derived
internal-Hom object degreewise. -/
noncomputable def k_injective_target_homology_add_equiv_derivedHom
    (H : RHomPkg)
    (A I : Cpx) [I.IsKInjective] (n : ℤ) :
    (CochainComplex.HomComplex A I).homology n ≃+
      ((DerivedCategory.homologyFunctor Mod n).obj
        (RHom[H](DerivedCategory.Q.obj A, DerivedCategory.Q.obj I))) := by
  -- First rewrite Hom-complex cohomology as homotopy morphisms into the shifted target.
  let e₁ :
      (CochainComplex.HomComplex A I).homology n ≃+
        ((KQ).obj A ⟶ (KQ).obj (I⟦n⟧)) :=
    (CochainComplex.HomComplex.homologyAddEquiv A I n).trans homAddEquiv
  -- K-injectivity upgrades those homotopy morphisms to derived morphisms.
  let e₂ :
      ((KQ).obj A ⟶ (KQ).obj (I⟦n⟧)) ≃+
        (DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj (I⟦n⟧)) :=
    AddEquiv.ofBijective
      (DerivedCategory.Qh.mapAddHom :
        ((KQ).obj A ⟶ (KQ).obj (I⟦n⟧)) →+
          (DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj (I⟦n⟧)))
      (CochainComplex.IsKInjective.Qh_map_bijective ((KQ).obj A) (I⟦n⟧))
  -- Then use the canonical shift comparison in the derived category.
  let e₃ :
      (DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj (I⟦n⟧)) ≃+
        ShiftedHom (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj I) n :=
    iso_hom_congr_add_equiv (Iso.refl _) ((DerivedCategory.Q.commShiftIso n).app I)
  -- Finally identify the cohomology of the chosen `RHom` object with the same shifted Hom group.
  let e₄ :
      ((DerivedCategory.homologyFunctor Mod n).obj
        (RHom[H](DerivedCategory.Q.obj A, DerivedCategory.Q.obj I))) ≃+
        ShiftedHom (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj I) n :=
      (derivedHom_cohomology_iso_shiftedHom (R := R) H
      (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj I) n).toAddEquiv
  exact (e₁.trans (e₂.trans e₃)).trans e₄.symm

/-- Helper for Lemma 15.99.1: the K-injective-target cohomology comparison is bijective in every
degree. -/
theorem k_injective_target_homology_add_equiv_derivedHom_bijective
    (H : RHomPkg)
    (A I : Cpx) [I.IsKInjective] (n : ℤ) :
    Function.Bijective (k_injective_target_homology_add_equiv_derivedHom (R := R) H A I n) := by
  -- This packages the existing additive equivalence as a bijection, which is the homology-side
  -- input needed once the actual comparison morphism to `RHom` is constructed.
  exact (k_injective_target_homology_add_equiv_derivedHom (R := R) H A I n).bijective

/-- Helper for Lemma 15.99.1: the chapter internal-Hom complex is definitionally the standard
`CochainComplex.HomComplex`. -/
private theorem module_complex_internal_hom_eq_hom_complex
    (K L : Cpx) :
    module_complex_internal_hom K L = CochainComplex.HomComplex K L :=
  rfl

/-- Helper for Lemma 15.99.1: the public complex evaluation map from the Hom complex of a
projective source model. -/
private noncomputable abbrev projective_source_hom_complex_evaluation
    (P : CochainComplex.ProjectiveMinus Mod) (A : Cpx) :
    CochainComplex.HomComplex (P : Cpx) A ⊗ (P : Cpx) ⟶ A :=
  (β_ (CochainComplex.HomComplex (P : Cpx) A) (P : Cpx)).hom ≫
    (ihom.ev (P : Cpx)).app A

/-- Helper for Lemma 15.99.1: after passing the projective-source evaluation map through `Q` and
the tensor comparison, we obtain a derived evaluation morphism. -/
private noncomputable def projective_source_hom_complex_evaluation_derived
    (P : CochainComplex.ProjectiveMinus Mod) (A : Cpx) :
    DerivedCategory.Q.obj (CochainComplex.HomComplex (P : Cpx) A) ⊗[R]^L
        DerivedCategory.Q.obj (P : Cpx) ⟶
      DerivedCategory.Q.obj A :=
  (derivedCategory_tensorObj_iso_derivedTensorProduct
      (DerivedCategory.Q.obj (CochainComplex.HomComplex (P : Cpx) A))
      (DerivedCategory.Q.obj (P : Cpx))).inv ≫
    (Functor.Monoidal.μIso
      (DerivedCategory.Q : Cpx ⥤ DMod)
      (CochainComplex.HomComplex (P : Cpx) A)
      (P : Cpx)).hom ≫
        DerivedCategory.Q.map (projective_source_hom_complex_evaluation P A)

/-- Helper for Lemma 15.99.1: the projective-source Hom complex comparison with the chosen
derived internal-Hom object, obtained by transposing the derived evaluation map. -/
private noncomputable def projective_source_hom_complex_comparison
    (H : RHomPkg)
    (P : CochainComplex.ProjectiveMinus Mod) (A : Cpx) :
    DerivedCategory.Q.obj (CochainComplex.HomComplex (P : Cpx) A) ⟶
      RHom[H](DerivedCategory.Q.obj (P : Cpx), DerivedCategory.Q.obj A) :=
  (H.derivedTensorAdj (DerivedCategory.Q.obj (P : Cpx))).homEquiv _ _
    (projective_source_hom_complex_evaluation_derived (R := R) P A)

/-- Helper for Lemma 15.99.1: by construction, the mate of the projective-source comparison is the
derived evaluation morphism coming from the concrete Hom complex. -/
private theorem projective_source_hom_complex_comparison_def
    (H : RHomPkg)
    (P : CochainComplex.ProjectiveMinus Mod) (A : Cpx) :
    ((H.derivedTensorAdj (DerivedCategory.Q.obj (P : Cpx))).homEquiv _ _).symm
        (projective_source_hom_complex_comparison (R := R) H P A) =
      projective_source_hom_complex_evaluation_derived (R := R) P A := by
  -- Proof comment: this is the defining cancellation for the chosen adjoint transpose.
  simp [projective_source_hom_complex_comparison]

/-- Helper for Lemma 15.99.1: every cohomology map induced by the projective-source comparison is
bijection, because the Hom complex already computes `RHom` degreewise. -/
private theorem projective_source_hom_complex_comparison_homology_bijective
    (H : RHomPkg)
    (P : CochainComplex.ProjectiveMinus Mod) (A : Cpx) (n : ℤ) :
    Function.Bijective
      ((DerivedCategory.homologyFunctor Mod n).map
        (projective_source_hom_complex_comparison (R := R) H P A)) := by
  -- Proof comment: rewrite the induced homology map to the explicit additive equivalence already
  -- computed for bounded-above projective sources.
  simpa [projective_source_hom_complex_comparison, projective_source_hom_complex_evaluation_derived,
    projective_source_hom_complex_evaluation, module_complex_internal_hom_eq_hom_complex] using
    (projective_source_homology_add_equiv_derivedHom (R := R) H P A n).bijective

/-- Helper for Lemma 15.99.1: the concrete Hom complex of a bounded-above projective model
represents the chosen derived internal-Hom object. -/
theorem projective_source_module_complex_internal_hom_represents_derivedInternalHom
    (H : RHomPkg)
    (P : CochainComplex.ProjectiveMinus Mod) (A : Cpx) :
    DerivedCategory.Q.obj (CochainComplex.HomComplex (P : Cpx) A) ≅
      RHom[H](DerivedCategory.Q.obj (P : Cpx), DerivedCategory.Q.obj A) := by
  -- Proof comment: detect the projective-source comparison on all cohomology groups and then
  -- package the resulting isomorphism in the derived category.
  have hcomparison :
      IsIso (projective_source_hom_complex_comparison (R := R) H P A) := by
    refine
      (derivedCategory_isIso_iff_homology_map_isIso
        (ℬ := Mod)
        (projective_source_hom_complex_comparison (R := R) H P A)).2 ?_
    intro n
    refine (CategoryTheory.isIso_iff_bijective _).2 ?_
    exact projective_source_hom_complex_comparison_homology_bijective (R := R) H P A n
  exact asIso (projective_source_hom_complex_comparison (R := R) H P A)

/-- Helper for Lemma 15.99.1: the public complex evaluation map from a Hom complex into a
K-injective target model. -/
private noncomputable abbrev k_injective_target_hom_complex_evaluation
    (A I : Cpx) :
    CochainComplex.HomComplex A I ⊗ A ⟶ I :=
  (β_ (CochainComplex.HomComplex A I) A).hom ≫ (ihom.ev A).app I

/-- Helper for Lemma 15.99.1: after passing the target-side evaluation map through `Q` and the
tensor bridge, we obtain the derived evaluation morphism used to define the comparison. -/
private noncomputable def k_injective_target_hom_complex_evaluation_derived
    (A I : Cpx) :
    DerivedCategory.Q.obj (CochainComplex.HomComplex A I) ⊗[R]^L
        DerivedCategory.Q.obj A ⟶
      DerivedCategory.Q.obj I :=
  (derivedCategory_tensorObj_iso_derivedTensorProduct
      (DerivedCategory.Q.obj (CochainComplex.HomComplex A I))
      (DerivedCategory.Q.obj A)).inv ≫
    (Functor.Monoidal.μIso
      (DerivedCategory.Q : Cpx ⥤ DMod)
      (CochainComplex.HomComplex A I)
      A).hom ≫
        DerivedCategory.Q.map (k_injective_target_hom_complex_evaluation (R := R) A I)

/-- Helper for Lemma 15.99.1: the target-side Hom complex comparison with the chosen derived
internal-Hom object, obtained by transposing the derived evaluation map. -/
private noncomputable def k_injective_target_hom_complex_comparison
    (H : RHomPkg)
    (A I : Cpx) :
    DerivedCategory.Q.obj (CochainComplex.HomComplex A I) ⟶
      RHom[H](DerivedCategory.Q.obj A, DerivedCategory.Q.obj I) :=
  (H.derivedTensorAdj (DerivedCategory.Q.obj A)).homEquiv _ _
    (k_injective_target_hom_complex_evaluation_derived (R := R) A I)

/-- Helper for Lemma 15.99.1: by construction, the mate of the target-side comparison is the
derived evaluation morphism coming from the concrete Hom complex. -/
private theorem k_injective_target_hom_complex_comparison_def
    (H : RHomPkg)
    (A I : Cpx) :
    ((H.derivedTensorAdj (DerivedCategory.Q.obj A)).homEquiv _ _).symm
        (k_injective_target_hom_complex_comparison (R := R) H A I) =
      k_injective_target_hom_complex_evaluation_derived (R := R) A I := by
  -- Proof comment: this is the defining `homEquiv`/`symm` cancellation for the chosen mate.
  simp [k_injective_target_hom_complex_comparison]

/-- Helper for Lemma 15.99.1: every cohomology map induced by the target-side comparison is
bijection, because a K-injective target model computes `RHom` degreewise. -/
private theorem k_injective_target_hom_complex_comparison_homology_bijective
    (H : RHomPkg)
    (A I : Cpx) [I.IsKInjective] (n : ℤ) :
    Function.Bijective
      ((DerivedCategory.homologyFunctor Mod n).map
        (k_injective_target_hom_complex_comparison (R := R) H A I)) := by
  -- Proof comment: rewrite the induced homology map to the explicit additive equivalence already
  -- computed for K-injective targets.
  simpa [k_injective_target_hom_complex_comparison,
    k_injective_target_hom_complex_evaluation_derived, k_injective_target_hom_complex_evaluation,
    module_complex_internal_hom_eq_hom_complex] using
    (k_injective_target_homology_add_equiv_derivedHom (R := R) H A I n).bijective

/-- Helper for Lemma 15.99.1: the concrete Hom complex into a K-injective model represents the
chosen derived internal-Hom object. -/
theorem k_injective_target_module_complex_internal_hom_represents_derivedInternalHom
    (H : RHomPkg)
    (A I : Cpx) [I.IsKInjective] :
    DerivedCategory.Q.obj (CochainComplex.HomComplex A I) ≅
      RHom[H](DerivedCategory.Q.obj A, DerivedCategory.Q.obj I) := by
  -- Proof comment: detect the target-side comparison on all cohomology groups and package the
  -- resulting derived-category isomorphism.
  have hcomparison :
      IsIso (k_injective_target_hom_complex_comparison (R := R) H A I) := by
    refine
      (derivedCategory_isIso_iff_homology_map_isIso
        (ℬ := Mod)
        (k_injective_target_hom_complex_comparison (R := R) H A I)).2 ?_
    intro n
    refine (CategoryTheory.isIso_iff_bijective _).2 ?_
    exact k_injective_target_hom_complex_comparison_homology_bijective (R := R) H A I n
  exact asIso (k_injective_target_hom_complex_comparison (R := R) H A I)

/-- Helper for Lemma 15.99.1: a bounded-above complex is a `minus` complex. -/
private theorem minus_of_isStrictlyLE
    (K : Cpx) {b : ℤ} (hK : K.IsStrictlyLE b) :
    CochainComplex.minus (ModuleCat R) K :=
  (CochainComplex.minus_iff (ModuleCat R) K).2 ⟨b, hK⟩

/-- Helper for Lemma 15.99.1: a bounded finite-projective complex canonically defines a
bounded-above projective model. -/
private theorem projectiveMinus_of_isBoundedFiniteProjective
    (P : Cpx) [hP : CochainComplex.IsBoundedFiniteProjective P] :
    CochainComplex.ProjectiveMinus (ModuleCat R) := by
  -- Proof comment: the upper support bound gives the `minus` owner, and termwise projectivity is
  -- already built into `IsBoundedFiniteProjective`.
  obtain ⟨_, b, _, hPle⟩ := hP.bounded
  refine ⟨⟨P, (CochainComplex.minus_iff (ModuleCat R) P).2 ⟨b, hPle⟩⟩, fun i ↦ ?_⟩
  infer_instance

/-- Helper for Lemma 15.99.1: a bounded-above termwise finite-free complex canonically defines a
bounded-above projective model. -/
private theorem projectiveMinus_of_isStrictlyLE_termwiseFiniteFree
    (E : Cpx) {b : ℤ}
    (hE : E.IsStrictlyLE b) [E.IsTermwiseFiniteFree] :
    CochainComplex.ProjectiveMinus (ModuleCat R) := by
  -- Proof comment: the source proof uses a bounded-above finite-free model, and finite free
  -- terms are projective.
  refine ⟨⟨E, (CochainComplex.minus_iff (ModuleCat R) E).2 ⟨b, hE⟩⟩, fun i ↦ ?_⟩
  rcases CochainComplex.IsTermwiseFiniteFree.out (E := E) i with ⟨hFree, _⟩
  let _ : Module.Free R (E.X i) := hFree
  infer_instance

/-- Helper for Lemma 15.99.1: the internal-Hom projection reads off the stored cochain
component. -/
private theorem module_complex_internal_hom_piProj_hom_eq_cochain_component
    (K L : Cpx) (n p : ℤ) (z : (module_complex_internal_hom K L).X n) :
    (module_complex_internal_hom_piProj K L n p).hom z = z.v p (n + p) (by omega) := by
  -- Proof comment: the projection was defined by unpacking the degree-`n` cochain family.
  rfl

/-- Helper for Lemma 15.99.1: after restricting the tensor-total degree map to one `(t, r)`
summand and then projecting to the `p`-th target factor, one recovers the textbook component
map `c_{p,r,s}`. -/
private theorem tensor_internal_hom_to_iterated_internal_hom_projected_to_component
    (K L M : Cpx) [HomologicalComplex.HasTensor (module_complex_internal_hom L M) K]
    (t r n p : ℤ) (h : t + r = n) :
    HomologicalComplex.ιTensorObj (module_complex_internal_hom L M) K t r n h ≫
        (tensor_internal_hom_to_iterated_internal_hom K L M).f n ≫
        module_complex_internal_hom_piProj (module_complex_internal_hom K L) M n p =
      tensor_internal_hom_to_iterated_internal_hom_component K L M t r n p h := by
  -- Proof comment: remove the target product isomorphism, then evaluate the tensor descender on
  -- the chosen source summand and target projection.
  unfold tensor_internal_hom_to_iterated_internal_hom
  rw [Category.assoc]
  have hdesc := congrArg
    (fun u ↦ u ≫ Pi.π (fun q : ℤ ↦ (ihom ((module_complex_internal_hom K L).X q)).obj (M.X (n + q))) p)
    (HomologicalComplex.ι_mapBifunctorDesc
      (K₁ := module_complex_internal_hom L M) (K₂ := K)
      (F := MonoidalCategory.curriedTensor (ModuleCat R))
      (c := ComplexShape.up ℤ)
      (A := ∏ᶜ fun q : ℤ ↦ (ihom ((module_complex_internal_hom K L).X q)).obj (M.X (n + q)))
      (j := n)
      (f := fun t r h ↦
        Pi.lift fun p ↦ tensor_internal_hom_to_iterated_internal_hom_component K L M t r n p h)
      t r h)
  simpa [Category.assoc, HomologicalComplex.ιTensorObj, CategoryTheory.Limits.Pi.lift_π,
    module_complex_internal_hom_piIso, module_complex_internal_hom_piProj] using hdesc

/-- Helper for Lemma 15.99.1: on a pure tensor and a fixed target cochain, the textbook
component map is given by nested evaluation along the two internal-Hom projections. -/
private theorem tensor_internal_hom_to_iterated_internal_hom_component_apply_tmul_local
    (K L M : Cpx) (t r n p : ℤ) (h : t + r = n)
    (g : (module_complex_internal_hom L M).X t) (k : K.X r)
    (φ : (module_complex_internal_hom K L).X p) :
    (ModuleCat.Hom.hom
        ((tensor_internal_hom_to_iterated_internal_hom_component K L M t r n p h).hom
          (TensorProduct.tmul R g k))) φ =
      (r * p).negOnePow •
        (ModuleCat.Hom.hom
            (eqToHom (congrArg (fun z : ℤ ↦ M.X z)
              (by
                have : t + (p + r) = n + p := by omega
                exact this)))
          ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj L M t (p + r)).hom g))
            ((ModuleCat.Hom.hom ((module_complex_internal_hom_piProj K L p r).hom φ)) k)) := by
  -- Proof comment: the currying, braiding, and evaluation maps in `ModuleCat R` reduce to direct
  -- nested application on the chosen pure tensor and target cochain.
  unfold tensor_internal_hom_to_iterated_internal_hom_component
  simp only [Category.assoc, ModuleCat.hom_smul, LinearMap.smul_apply,
    ModuleCat.MonoidalCategory.braiding_hom_apply, ModuleCat.monoidalClosed_curry,
    ModuleCat.ihom_map_apply, module_complex_internal_hom_piProj_hom_eq_cochain_component]

/-- Helper for Lemma 15.99.1: in the bounded-window branch, the source-proof bounds on `E`, `A`,
and `I` force the textbook `(p,r)` component to vanish whenever one of the four window
inequalities fails. -/
private theorem tensor_internal_hom_component_eq_zero_of_out_of_window
    (E A I : Cpx)
    {b n a c : ℤ}
    (hE : E.IsStrictlyLE b)
    (hA : A.IsStrictlyGE n)
    (hIge : I.IsStrictlyGE a)
    (hIle : I.IsStrictlyLE c)
    (m p r : ℤ)
    (hout : b < r ∨ p + r < n ∨ m + p < a ∨ c < m + p) :
    tensor_internal_hom_to_iterated_internal_hom_component E A I (m - r) r m p
      (by omega) = 0 := by
  letI : E.IsStrictlyLE b := hE
  letI : A.IsStrictlyGE n := hA
  letI : I.IsStrictlyGE a := hIge
  letI : I.IsStrictlyLE c := hIle
  -- Proof comment: evaluate the component on pure tensors and target cochains, then use the
  -- source-proof support bounds to force one of the two nested evaluations to be zero.
  ext x φ
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro g k
    rw [tensor_internal_hom_to_iterated_internal_hom_component_apply_tmul_local
      (R := R) E A I (m - r) r m p (by omega)]
    rcases hout with hr | hr | hr | hr
    · -- If `E.X r = 0`, then every pure tensor with right factor in degree `r` is already zero.
      have hk : k = 0 := (E.isZero_of_isStrictlyLE b r hr).eq_of_src k
      subst hk
      simp
    · -- If `A.X (p + r) = 0`, the inner cochain component of `φ` vanishes.
      have hproj :
          (module_complex_internal_hom_piProj E A p r).hom φ = 0 := by
        exact (A.isZero_of_isStrictlyGE n (p + r) hr).eq_of_tgt _
      simp [hproj]
    · -- If `I.X (m + p) = 0` from the lower bound, the outer evaluation vanishes.
      have hproj :
          (module_complex_internal_hom_piProj A I (m - r) (p + r)).hom g = 0 := by
        refine (I.isZero_of_isStrictlyGE a ((m - r) + (p + r)) ?_).eq_of_tgt _
        omega
      simp [hproj]
    · -- If `I.X (m + p) = 0` from the upper bound, the same outer evaluation vanishes.
      have hproj :
          (module_complex_internal_hom_piProj A I (m - r) (p + r)).hom g = 0 := by
        refine (I.isZero_of_isStrictlyLE c ((m - r) + (p + r)) ?_).eq_of_tgt _
        omega
      simp [hproj]
  · intro x y hx hy
    simp [hx, hy]

/-- Helper for Lemma 15.99.1: if the right tensor term in degree `r` is zero, then every
`(p,r)`-component of the strict tensor/Hom comparison vanishes. -/
private theorem tensor_internal_hom_component_eq_zero_of_right_term_isZero
    (K A I : Cpx)
    (t r n p : ℤ) (h : t + r = n)
    (hKr : IsZero (K.X r)) :
    tensor_internal_hom_to_iterated_internal_hom_component K A I t r n p h = 0 := by
  -- Proof comment: every pure tensor with right factor in the zero object already vanishes, so
  -- the component map is zero by tensor induction.
  ext x φ
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro g k
    have hk : k = 0 := hKr.eq_of_src k
    subst hk
    simp [tensor_internal_hom_to_iterated_internal_hom_component_apply_tmul_local]
  · intro x y hx hy
    simp [hx, hy]

/-- Helper for Lemma 15.99.1: in the bounded-window branch, an `r`-index outside the explicit
interval `[n + m - c, b]` forces every `(p,r)`-component to vanish. -/
private theorem tensor_internal_hom_component_eq_zero_of_r_outside_window
    (E A I : Cpx)
    {b n a c : ℤ}
    (hE : E.IsStrictlyLE b)
    (hA : A.IsStrictlyGE n)
    (hIge : I.IsStrictlyGE a)
    (hIle : I.IsStrictlyLE c)
    (m r p : ℤ)
    (hout : r < n + m - c ∨ b < r) :
    tensor_internal_hom_to_iterated_internal_hom_component E A I (m - r) r m p
      (by omega) = 0 := by
  -- Proof comment: outside the source-proof `r`-window, either the right tensor term already
  -- vanishes (`r > b`) or one of the middle/target window inequalities forces the component to
  -- be zero for every `p`.
  rcases hout with hr | hr
  · refine tensor_internal_hom_component_eq_zero_of_out_of_window
      (R := R) E A I hE hA hIge hIle m p r ?_
    left
    omega
  · refine tensor_internal_hom_component_eq_zero_of_out_of_window
      (R := R) E A I hE hA hIge hIle m p r ?_
    exact Or.inl hr

/-- Helper for Lemma 15.99.1: the corrected fixed-`r` block lands in the `r`-projected family of
the degree-`m` target. -/
private abbrev tensor_internal_hom_r_block_target
    (K A I : Cpx)
    (m r : ℤ) (p : ℤ) : Mod :=
  (ihom ((ihom (K.X r)).obj (A.X (p + r)))).obj (I.X (m + p))

/-- Helper for Lemma 15.99.1: the fixed-`r` block of the strict degree-`m` comparison is obtained
by packaging all `p`-components into the `r`-projected target family. -/
private noncomputable def tensor_internal_hom_r_block
    (K A I : Cpx)
    (m r : ℤ) :
    ((module_complex_internal_hom A I).X (m - r) ⊗ K.X r) ⟶
      ∏ᶜ fun p : ℤ ↦ tensor_internal_hom_r_block_target K A I m r p :=
  Pi.lift fun p ↦
    tensor_internal_hom_to_iterated_internal_hom_component K A I (m - r) r m p (by omega)

/-- Helper for Lemma 15.99.1: if the degree-`m` comparison is assembled from finitely many
contributing `r`-blocks and each such block is an isomorphism, then the full degree map is an
isomorphism. -/
private theorem tensor_internal_hom_degree_iso_of_interval_support
    (K A I : Cpx)
    [HomologicalComplex.HasTensor (module_complex_internal_hom A I) K]
    (m lo hi : ℤ)
    (hblock : ∀ r : ℤ, lo ≤ r → r ≤ hi →
      IsIso (tensor_internal_hom_r_block (R := R) K A I m r))
    (hzero : ∀ r p : ℤ, r < lo ∨ hi < r →
      tensor_internal_hom_to_iterated_internal_hom_component K A I (m - r) r m p
        (by omega) = 0) :
    IsIso ((tensor_internal_hom_to_iterated_internal_hom K A I).f m) := by
  -- TODO: follow the projection-based finite-interval assembly from Lemma `15.73.2`. Expand the
  -- degree-`m` source by tensor summands indexed by `r`, use `hzero` to kill all off-interval
  -- blocks, and use `hblock` on each surviving `r` to reconstruct the inverse degree map.
  sorry

/-- Helper for Lemma 15.99.1: if the right tensor term `K.X r` is finite projective, then the
entire fixed-`r` block of the strict comparison is an isomorphism. -/
private theorem tensor_internal_hom_r_block_isIso_of_finite_projective_term
    (K A I : Cpx)
    (m r : ℤ)
    [Module.Finite R (K.X r)] [Module.Projective R (K.X r)] :
    IsIso (tensor_internal_hom_r_block (R := R) K A I m r) := by
  -- TODO: identify `tensor_internal_hom_r_block` with the categorical module map underlying
  -- `TensorProduct.piRightHom` after the degree decomposition
  -- `module_complex_internal_hom_piIso (module_complex_internal_hom K A) I m`, then use finite
  -- projectivity of `K.X r` to commute tensor with the full product over `p`.
  sorry

/-- Helper for Lemma 15.99.1: once the degree maps of the strict comparison are isomorphisms, the
whole chain map is an isomorphism. -/
private theorem tensor_internal_hom_to_iterated_internal_hom_isIso_of_degreewise
    (K L M : Cpx)
    [HomologicalComplex.HasTensor (module_complex_internal_hom L M) K]
    (hdeg : ∀ n : ℤ, IsIso ((tensor_internal_hom_to_iterated_internal_hom K L M).f n)) :
    IsIso (tensor_internal_hom_to_iterated_internal_hom K L M) := by
  -- Proof comment: upgrade the degreewise component isomorphisms to a chain-level isomorphism.
  letI : ∀ n : ℤ, IsIso ((tensor_internal_hom_to_iterated_internal_hom K L M).f n) := hdeg
  exact HomologicalComplex.Hom.isIso_of_components
    (tensor_internal_hom_to_iterated_internal_hom K L M)

/-- Helper for Lemma 15.99.1: after transporting the public tensor-right comparison along the
chosen strict Hom-complex models on the source and target sides, one recovers the concrete chain
map from Lemma `15.72.6`. -/
private theorem tensor_right_comparison_transport_square
    (H : RHomPkg)
    (P : CochainComplex.ProjectiveMinus Mod)
    (A I : Cpx) [I.IsKInjective] :
    (derivedCategory_tensorObj_iso_derivedTensorProduct
        (DerivedCategory.Q.obj (CochainComplex.HomComplex A I))
        (DerivedCategory.Q.obj (P : Cpx))).hom ≫
      (derivedTensorProduct (DerivedCategory.Q.obj (P : Cpx))).map
        (k_injective_target_module_complex_internal_hom_represents_derivedInternalHom
          (R := R) H A I).hom ≫
      derivedInternalHom_tensor_right_comparison H
        (DerivedCategory.Q.obj (P : Cpx)) (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj I) ≫
      derivedInternalHomMap H
        (projective_source_module_complex_internal_hom_represents_derivedInternalHom
          (R := R) H P A).hom
        (𝟙 (DerivedCategory.Q.obj I)) ≫
      (k_injective_target_module_complex_internal_hom_represents_derivedInternalHom
        (R := R) H (CochainComplex.HomComplex (P : Cpx) A) I).inv =
    DerivedCategory.Q.map
      (tensor_internal_hom_to_iterated_internal_hom (P : Cpx) A I) := by
  -- TODO: apply the fixed adjunction
  -- `- ⊗[R]^L RHom_R(Q(P), Q(A)) ⊣ RHom_R(RHom_R(Q(P), Q(A)), -)` to both sides, rewrite only
  -- with `derivedInternalHom_tensor_right_comparison_def`,
  -- `projective_source_hom_complex_comparison_def`, and
  -- `k_injective_target_hom_complex_comparison_def`, and check that both mates are the same
  -- explicit evaluation composite.
  sorry

/-- Helper for Lemma 15.99.1: in the bounded finite-projective case, the degree-`m` component of
the strict comparison map is an isomorphism. -/
private theorem tensor_internal_hom_to_iterated_internal_hom_degree_iso_of_boundedFiniteProjective
    (P A I : Cpx)
    [CochainComplex.IsBoundedFiniteProjective P]
    (m : ℤ) :
    IsIso ((tensor_internal_hom_to_iterated_internal_hom P A I).f m) := by
  let hP : CochainComplex.IsBoundedFiniteProjective P := inferInstance
  obtain ⟨a, b, hPge, hPle⟩ := hP.bounded
  -- Proof comment: boundedness gives an explicit interval of source degrees `r`; on that interval,
  -- finite projectivity of `P.X r` gives the block isomorphisms, and outside it the right tensor
  -- term vanishes.
  exact tensor_internal_hom_degree_iso_of_interval_support (R := R) P A I m a b
    (fun r hrlo hrhi ↦ by
      let _ : Module.Finite R (P.X r) := inferInstance
      let _ : Module.Projective R (P.X r) := inferInstance
      exact tensor_internal_hom_r_block_isIso_of_finite_projective_term (R := R) P A I m r)
    (fun r p hr ↦ by
      rcases hr with hr | hr
      · exact tensor_internal_hom_component_eq_zero_of_right_term_isZero
          (R := R) P A I (m - r) r m p (by omega) (P.isZero_of_isStrictlyGE a r hr)
      · exact tensor_internal_hom_component_eq_zero_of_right_term_isZero
          (R := R) P A I (m - r) r m p (by omega) (P.isZero_of_isStrictlyLE b r hr))

/-- Helper for Lemma 15.99.1: in the bounded-window case, the degree-`m` component of the strict
comparison map is an isomorphism. -/
private theorem tensor_internal_hom_to_iterated_internal_hom_degree_iso_of_bounded_window
    (E A I : Cpx)
    {b n a c : ℤ}
    (hE : E.IsStrictlyLE b)
    [E.IsTermwiseFiniteFree]
    (hA : A.IsStrictlyGE n)
    (hIge : I.IsStrictlyGE a)
    (hIle : I.IsStrictlyLE c)
    (m : ℤ) :
    IsIso ((tensor_internal_hom_to_iterated_internal_hom E A I).f m) := by
  -- Proof comment: the source proof supplies the explicit `r`-window
  -- `[n + m - c, b]`. Inside that interval the fixed-`r` block isomorphisms come from finite free
  -- terms, and outside it the new `r`-window vanishing lemma kills every component.
  exact tensor_internal_hom_degree_iso_of_interval_support (R := R) E A I m (n + m - c) b
    (fun r hrlo hrhi ↦ by
      let _ : Module.Finite R (E.X r) := inferInstance
      let _ : Module.Projective R (E.X r) := inferInstance
      exact tensor_internal_hom_r_block_isIso_of_finite_projective_term (R := R) E A I m r)
    (fun r p hr ↦
      tensor_internal_hom_component_eq_zero_of_r_outside_window
        (R := R) E A I hE hA hIge hIle m r p hr)

/-- Helper for Lemma 15.99.1: once the tensor-right comparison is known on chosen cochain
representatives, naturality transports the isomorphism to the represented derived objects. -/
private theorem tensor_right_comparison_isIso_of_representatives
    (H : RHomPkg)
    (K₀ L₀ M₀ : Cpx)
    {K L M : DMod}
    (eK : DerivedCategory.Q.obj K₀ ≅ K)
    (eL : DerivedCategory.Q.obj L₀ ≅ L)
    (eM : DerivedCategory.Q.obj M₀ ≅ M)
    (hmodel :
      IsIso
        (derivedInternalHom_tensor_right_comparison H
          (DerivedCategory.Q.obj K₀) (DerivedCategory.Q.obj L₀) (DerivedCategory.Q.obj M₀))) :
    IsIso (derivedInternalHom_tensor_right_comparison H K L M) := by
  let hModel :=
    derivedInternalHom_tensor_right_comparison H
      (DerivedCategory.Q.obj K₀) (DerivedCategory.Q.obj L₀) (DerivedCategory.Q.obj M₀)
  let hTarget :=
    derivedInternalHom_tensor_right_comparison H
      (DerivedCategory.Q.obj K₀) (DerivedCategory.Q.obj L₀) M
  let hSource :=
    derivedInternalHom_tensor_right_comparison H
      (DerivedCategory.Q.obj K₀) L M
  let hFinal := derivedInternalHom_tensor_right_comparison H K L M
  let mapM :=
    derivedInternalHomMap H (𝟙 (DerivedCategory.Q.obj L₀)) eM.hom
  let mapL :=
    derivedInternalHomMap H (derivedInternalHomMap H (𝟙 (DerivedCategory.Q.obj K₀)) eL.hom) (𝟙 M)
  let mapK :=
    derivedInternalHomMap H (derivedInternalHomMap H eK.hom (𝟙 L)) (𝟙 M)
  let tensorMapM :=
    (derivedTensorProduct (DerivedCategory.Q.obj K₀)).map
      (derivedInternalHomMap H (𝟙 (DerivedCategory.Q.obj L₀)) eM.hom)
  let tensorMapL :=
    (derivedTensorProduct (DerivedCategory.Q.obj K₀)).map
      (derivedInternalHomMap H eL.hom (𝟙 M))
  let tensorMapK := (derivedTensorProductMap H eK.hom).app (RHom[H](L, M))
  have hmapM : IsIso mapM := by
    -- Proof comment: changing only the target variable of `RHom` by an isomorphism preserves the
    -- represented internal-Hom object.
    dsimp [mapM, derivedInternalHomMap]
    infer_instance
  have htensorMapM : IsIso tensorMapM := by
    -- Proof comment: right derived tensoring preserves isomorphisms of the left factor.
    dsimp [tensorMapM]
    infer_instance
  have htarget_comp : IsIso (hTarget ≫ mapM) := by
    -- Proof comment: the target-variable naturality square identifies this composite with the
    -- already solved model comparison after an isomorphism on the tensor source.
    rw [show tensorMapM ≫ hModel = hTarget ≫ mapM from
      (derivedInternalHom_tensor_right_comparison_natural_target H
        (DerivedCategory.Q.obj K₀) (DerivedCategory.Q.obj L₀) eM.hom).w]
    dsimp [tensorMapM]
    infer_instance
  have htarget : IsIso hTarget := by
    -- Proof comment: cancel the target-side internal-Hom isomorphism from the naturality square.
    exact IsIso.of_isIso_comp_right hTarget mapM
  have hInnerL :
      IsIso (derivedInternalHomMap H (𝟙 (DerivedCategory.Q.obj K₀)) eL.hom) := by
    -- Proof comment: the inner source-variable change is just contravariant/covariant functoriality
    -- of `RHom` applied to an isomorphism.
    dsimp [derivedInternalHomMap]
    infer_instance
  have hmapL : IsIso mapL := by
    -- Proof comment: postcomposing the outer internal Hom by an isomorphism again preserves
    -- isomorphisms.
    let _ :
        IsIso (derivedInternalHomMap H (𝟙 (DerivedCategory.Q.obj K₀)) eL.hom) := hInnerL
    dsimp [mapL, derivedInternalHomMap]
    infer_instance
  have htensorMapL : IsIso tensorMapL := by
    -- Proof comment: the source-variable naturality square changes the left `RHom` factor by an
    -- isomorphism, so the tensor source changes by an isomorphism too.
    dsimp [tensorMapL]
    infer_instance
  have hsource_comp : IsIso (hSource ≫ mapL) := by
    -- Proof comment: identify the transported source comparison with the previous target-transported
    -- one via the source-variable naturality square.
    rw [show tensorMapL ≫ hTarget = hSource ≫ mapL from
      (derivedInternalHom_tensor_right_comparison_natural_source H
        (DerivedCategory.Q.obj K₀) eL.hom).w]
    dsimp [tensorMapL]
    infer_instance
  have hsource : IsIso hSource := by
    -- Proof comment: cancel the outer internal-Hom isomorphism coming from `eL`.
    exact IsIso.of_isIso_comp_right hSource mapL
  have hInnerK : IsIso (derivedInternalHomMap H eK.hom (𝟙 L)) := by
    -- Proof comment: changing the inner source object by an isomorphism preserves the inner
    -- internal-Hom object.
    dsimp [derivedInternalHomMap]
    infer_instance
  have hmapK : IsIso mapK := by
    -- Proof comment: functoriality of the outer internal Hom turns the inner representative change
    -- into an isomorphism on the final target object.
    let _ : IsIso (derivedInternalHomMap H eK.hom (𝟙 L)) := hInnerK
    dsimp [mapK, derivedInternalHomMap]
    infer_instance
  have htensorNatIso : IsIso (derivedTensorProductMap H eK.hom) := by
    -- Proof comment: the mate of an isomorphism under the tensor/internal-Hom adjunction is again
    -- an isomorphism, so the induced natural transformation on derived tensor functors is a natural
    -- isomorphism.
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    have hpre : IsIso (MonoidalClosed.pre eK.hom) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro Y
      infer_instance
    dsimp [derivedTensorProductMap]
    infer_instance
  have htensorMapK : IsIso tensorMapK := by
    -- Proof comment: evaluate the natural isomorphism from the previous step at the required left
    -- tensor factor.
    exact (NatTrans.isIso_iff_isIso_app (derivedTensorProductMap H eK.hom)).1
      htensorNatIso (RHom[H](L, M))
  have hfinal_comp : IsIso (hFinal ≫ mapK) := by
    -- Proof comment: the tensor-variable naturality square identifies the final comparison composed
    -- with the target isomorphism with the already transported source comparison.
    rw [show tensorMapK ≫ hSource = hFinal ≫ mapK from
      (derivedInternalHom_tensor_right_comparison_natural_tensor H eK.hom).w]
    dsimp [tensorMapK]
    infer_instance
  -- Proof comment: cancel the final target-side representative isomorphism to conclude.
  exact IsIso.of_isIso_comp_right hFinal mapK

/-- Helper for Lemma 15.99.1: for a bounded finite-projective source model and a K-injective
target model, the tensor-right comparison on the corresponding derived objects is an isomorphism. -/
private theorem model_tensor_right_comparison_isIso_of_boundedFiniteProjective
    (H : RHomPkg)
    (P A I : Cpx)
    [CochainComplex.IsBoundedFiniteProjective P]
    [I.IsKInjective] :
    IsIso
      (derivedInternalHom_tensor_right_comparison H
        (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj I)) := by
  let P' : CochainComplex.ProjectiveMinus (ModuleCat R) :=
    projectiveMinus_of_isBoundedFiniteProjective (R := R) P
  let eSource :=
    derivedCategory_tensorObj_iso_derivedTensorProduct
      (DerivedCategory.Q.obj (CochainComplex.HomComplex A I))
      (DerivedCategory.Q.obj (P' : Cpx))
  let mapSource :=
    (derivedTensorProduct (DerivedCategory.Q.obj (P' : Cpx))).map
      (k_injective_target_module_complex_internal_hom_represents_derivedInternalHom
        (R := R) H A I).hom
  let mapTarget :=
    derivedInternalHomMap H
      (projective_source_module_complex_internal_hom_represents_derivedInternalHom
        (R := R) H P' A).hom
      (𝟙 (DerivedCategory.Q.obj I))
  let eTarget :=
    k_injective_target_module_complex_internal_hom_represents_derivedInternalHom
      (R := R) H (CochainComplex.HomComplex (P' : Cpx) A) I
  have hStrict :
      IsIso (tensor_internal_hom_to_iterated_internal_hom (P' : Cpx) A I) := by
    -- Proof comment: the source proof shows every degree map is the finite-support tensor/Hom
    -- isomorphism, so the whole chain map is an isomorphism.
    exact tensor_internal_hom_to_iterated_internal_hom_isIso_of_degreewise (R := R)
      (P' : Cpx) A I
      (tensor_internal_hom_to_iterated_internal_hom_degree_iso_of_boundedFiniteProjective
        (R := R) (P' : Cpx) A I)
  let _ : IsIso (tensor_internal_hom_to_iterated_internal_hom (P' : Cpx) A I) := hStrict
  have hComposite :
      IsIso
        (eSource.hom ≫
          mapSource ≫
          derivedInternalHom_tensor_right_comparison H
            (DerivedCategory.Q.obj (P' : Cpx)) (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj I) ≫
          mapTarget ≫
          eTarget.inv) := by
    -- Proof comment: after the source-faithful transport square, the composite is exactly
    -- `Q.map` of the strict comparison.
    rw [tensor_right_comparison_transport_square (R := R) H P' A I]
    infer_instance
  have hBeforeTarget :
      IsIso
        (eSource.hom ≫
          mapSource ≫
          derivedInternalHom_tensor_right_comparison H
            (DerivedCategory.Q.obj (P' : Cpx)) (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj I) ≫
          mapTarget) := by
    exact IsIso.of_isIso_comp_right _ eTarget.inv
  have hBeforeSource :
      IsIso
        (eSource.hom ≫
          mapSource ≫
          derivedInternalHom_tensor_right_comparison H
            (DerivedCategory.Q.obj (P' : Cpx)) (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj I)) := by
    exact IsIso.of_isIso_comp_right _ mapTarget
  have hPre :
      IsIso (eSource.hom ≫ mapSource) := by
    infer_instance
  -- Proof comment: cancel the source-side tensor isomorphism and the target-side internal-Hom
  -- isomorphism to recover the public comparison.
  simpa [eSource, mapSource, Category.assoc] using
    (IsIso.of_isIso_comp_left
      (derivedInternalHom_tensor_right_comparison H
        (DerivedCategory.Q.obj (P' : Cpx)) (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj I))
      (eSource.hom ≫ mapSource))

/-- Helper for Lemma 15.99.1: for a bounded-above finite-free source model, a bounded-below middle
model, and a bounded injective target model, the tensor-right comparison on the corresponding
derived objects is an isomorphism. -/
private theorem model_tensor_right_comparison_isIso_of_bounded_window
    (H : RHomPkg)
    (E A I : Cpx)
    {b n a c : ℤ}
    (hE : E.IsStrictlyLE b)
    [E.IsTermwiseFiniteFree]
    (hA : A.IsStrictlyGE n)
    (hIge : I.IsStrictlyGE a)
    (hIle : I.IsStrictlyLE c)
    [I.IsKInjective] :
    IsIso
      (derivedInternalHom_tensor_right_comparison H
        (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj I)) := by
  let E' : CochainComplex.ProjectiveMinus (ModuleCat R) :=
    projectiveMinus_of_isStrictlyLE_termwiseFiniteFree (R := R) E hE
  let eSource :=
    derivedCategory_tensorObj_iso_derivedTensorProduct
      (DerivedCategory.Q.obj (CochainComplex.HomComplex A I))
      (DerivedCategory.Q.obj (E' : Cpx))
  let mapSource :=
    (derivedTensorProduct (DerivedCategory.Q.obj (E' : Cpx))).map
      (k_injective_target_module_complex_internal_hom_represents_derivedInternalHom
        (R := R) H A I).hom
  let mapTarget :=
    derivedInternalHomMap H
      (projective_source_module_complex_internal_hom_represents_derivedInternalHom
        (R := R) H E' A).hom
      (𝟙 (DerivedCategory.Q.obj I))
  let eTarget :=
    k_injective_target_module_complex_internal_hom_represents_derivedInternalHom
      (R := R) H (CochainComplex.HomComplex (E' : Cpx) A) I
  have hStrict :
      IsIso (tensor_internal_hom_to_iterated_internal_hom (E' : Cpx) A I) := by
    -- Proof comment: in the bounded-window branch, the same strict comparison becomes degreewise
    -- bijective because the support bounds on `E`, `A`, and `I` force only finitely many
    -- contributing source degrees in each total degree.
    exact tensor_internal_hom_to_iterated_internal_hom_isIso_of_degreewise (R := R)
      (E' : Cpx) A I
      (tensor_internal_hom_to_iterated_internal_hom_degree_iso_of_bounded_window
        (R := R) (E' : Cpx) A I hE hA hIge hIle)
  let _ : IsIso (tensor_internal_hom_to_iterated_internal_hom (E' : Cpx) A I) := hStrict
  have hComposite :
      IsIso
        (eSource.hom ≫
          mapSource ≫
          derivedInternalHom_tensor_right_comparison H
            (DerivedCategory.Q.obj (E' : Cpx)) (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj I) ≫
          mapTarget ≫
          eTarget.inv) := by
    -- Proof comment: the same transport square as in the perfect branch identifies the public
    -- comparison with `Q.map` of the strict textbook map.
    rw [tensor_right_comparison_transport_square (R := R) H E' A I]
    infer_instance
  have hBeforeTarget :
      IsIso
        (eSource.hom ≫
          mapSource ≫
          derivedInternalHom_tensor_right_comparison H
            (DerivedCategory.Q.obj (E' : Cpx)) (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj I) ≫
          mapTarget) := by
    exact IsIso.of_isIso_comp_right _ eTarget.inv
  have hBeforeSource :
      IsIso
        (eSource.hom ≫
          mapSource ≫
          derivedInternalHom_tensor_right_comparison H
            (DerivedCategory.Q.obj (E' : Cpx)) (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj I)) := by
    exact IsIso.of_isIso_comp_right _ mapTarget
  have hPre :
      IsIso (eSource.hom ≫ mapSource) := by
    infer_instance
  -- Proof comment: cancel the same source-side and target-side transport isomorphisms as in the
  -- bounded finite-projective branch.
  simpa [eSource, mapSource, Category.assoc] using
    (IsIso.of_isIso_comp_left
      (derivedInternalHom_tensor_right_comparison H
        (DerivedCategory.Q.obj (E' : Cpx)) (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj I))
      (eSource.hom ≫ mapSource))

/-- Helper for Lemma 15.99.1: the perfect branch reduces to the explicit projective/K-injective
model comparison from Lemmas `15.72.6` and `15.74.3`. -/
lemma perfect_tensor_right_comparison_isIso
    (H : RHomPkg)
    (K L M : DMod)
    (hK : K.IsPerfect) :
    IsIso (derivedInternalHom_tensor_right_comparison H K L M) := by
  -- Route correction: keep the source-faithful model-computation route rather than switching to an
  -- abstract duality argument that would require unavailable built API in this workspace.
  obtain ⟨P, hP, ⟨eP⟩⟩ := exists_perfect_representation K hK
  obtain ⟨I, hI, ⟨eI⟩⟩ := exists_kInjective_representation M
  let _ : I.IsKInjective := hI
  let A : Cpx := DerivedCategory.Q.objPreimage L
  -- Proof comment: reduce first to the represented model comparison at `(P, A, I)`, and only then
  -- transport the resulting isomorphism back along the chosen derived identifications.
  have hModel :
      IsIso
        (derivedInternalHom_tensor_right_comparison H
          (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj I)) := by
    -- TODO: the remaining model-level blocker is the source-faithful identification with
    -- `DerivedCategory.Q.map (tensor_internal_hom_to_iterated_internal_hom P A I)` and the
    -- bounded finite-projective support argument on the chain map.
    exact model_tensor_right_comparison_isIso_of_boundedFiniteProjective H P A I
  exact tensor_right_comparison_isIso_of_representatives
    H P A I eP (DerivedCategory.Q.objObjPreimageIso L) eI hModel

/-- Helper for Lemma 15.99.1: the pseudo-coherent/bounded-below/finite-injective branch reduces
to the same explicit model comparison after choosing bounded-above, bounded-below, and bounded
injective representatives. -/
lemma pseudo_coherent_boundedBelow_finiteInjective_tensor_right_comparison_isIso
    (H : RHomPkg)
    (K L M : DMod)
    (hK : K.IsPseudoCoherent)
    (hL : ∃ n : ℤ, L.IsGE n)
    (hM : HasFiniteInjectiveDimension M) :
    IsIso (derivedInternalHom_tensor_right_comparison H K L M) := by
  obtain ⟨E, b, hE, hFree, ⟨eE⟩⟩ := exists_pseudoCoherent_representation K hK
  obtain ⟨A, n, hA, ⟨eA⟩⟩ := exists_boundedBelow_representation L hL
  obtain ⟨I, a, c, hIge, hIle, hIinj, ⟨eI⟩⟩ :=
    exists_bounded_injective_representation M hM
  let _ : E.IsTermwiseFiniteFree := hFree
  let _ := hE
  let _ := hA
  let _ := hIge
  let _ := hIle
  let _ := hIinj
  let _ : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  -- Proof comment: as in the perfect branch, isolate the concrete model comparison first and only
  -- then transport the isomorphism back to the original derived objects.
  have hModel :
      IsIso
        (derivedInternalHom_tensor_right_comparison H
          (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj I)) := by
    -- TODO: the remaining model-level blocker is the same comparison square as above, combined
    -- with the bounded-window support argument from the source proof for `(b, n, a, c)`.
    exact model_tensor_right_comparison_isIso_of_bounded_window
      H E A I hE hA hIge hIle
  exact tensor_right_comparison_isIso_of_representatives
    H E A I eE eA eI hModel

/-- Lemma 15.99.1: for the tensor-right comparison map
`R\mathrm{Hom}_R(L, M) \otimes_R^{\mathbf L} K \to
R\mathrm{Hom}_R(R\mathrm{Hom}_R(K, L), M)`, the morphism is an isomorphism whenever either `K`
is perfect, or `K` is pseudo-coherent, `L` is bounded below, and `M` has finite injective
dimension. -/
theorem derivedInternalHomTensorRightComparison_hom_isIso_of_isPerfect_or_of_pseudoCoherent_boundedBelow_finiteInjectiveDimension
    (H : RHomPkg)
    (K L M : DMod)
    (hcases : K.IsPerfect ∨
      K.IsPseudoCoherent ∧ (∃ n : ℤ, L.IsGE n) ∧ HasFiniteInjectiveDimension M) :
    IsIso (derivedInternalHom_tensor_right_comparison H K L M) := by
  -- Split into the two source-faithful branches stated in the textbook.
  rcases hcases with hK | ⟨hK, hL, hM⟩
  · -- The perfect branch is handled by the bounded finite-projective model computation.
    exact perfect_tensor_right_comparison_isIso H K L M hK
  · -- The second branch keeps the bounded-below and finite-injective hypotheses explicit.
    exact pseudo_coherent_boundedBelow_finiteInjective_tensor_right_comparison_isIso
      H K L M hK hL hM

end

end CategoryTheory
