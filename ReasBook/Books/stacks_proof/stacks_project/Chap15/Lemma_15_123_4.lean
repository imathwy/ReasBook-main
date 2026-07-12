import Mathlib
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Definition_15_75_1
import StacksProject_2024.Chap15.Definition_15_118_1
import StacksProject_2024.Chap13.Definition_13_19_1
import StacksProject_2024.Chap13.Lemma_13_19_8
import StacksProject_2024.Chap15.Lemma_15_75_2
import StacksProject_2024.Chap15.Lemma_15_79_1
import StacksProject_2024.Chap15.Lemma_15_66_3
import StacksProject_2024.Chap15.Lemma_15_123_1
import StacksProject_2024.Chap15.Lemma_15_123_2
import StacksProject_2024.Chap15.Lemma_15_123_3

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.ObjectProperty
open TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
private abbrev Q : Cpx ⥤ DMod := DerivedCategory.Q

/- Domain-style sampling for Stacks tag `0FJM` / Lemma `15.123.4`:
- primary domain: the determinant functor on the groupoid of perfect derived `R`-complexes with
  tor-amplitude in `[-1, 0]`, together with its canonical comparison isomorphisms and rank-zero
  determinant elements;
- sampled owner declarations:
  `DPerf`,
  `CategoryTheory.Core`,
  `DerivedCategory.IsPerfect`,
  `HasTorAmplitudeIn`,
  `CochainComplex.determinantIso`;
- best owner abstraction:
  `source-facing`: the full subcategory of `D(R)` cut out by perfectness and tor-amplitude in
    `[-1, 0]`, its determinant line, the comparison isomorphism for an isomorphism, the canonical
    rank-zero determinant element, and the functor `det` from its core to the core of invertible
    modules;
  `core/canonical`: `DerivedCategory.IsPerfect`, `HasTorAmplitudeIn`, `DPerf`, and the complex
    determinant owners from Lemmas `15.123.1`–`15.123.3`, together with the core of the
    invertible-module subcategory of `ModuleCat R`;
  `bridge/view`: two-term finite-projective representatives and good diagrams, which are only the
    comparison devices used in the proof.
- primitive vs. derived:
  primitive data are the derived object, its perfectness and tor-amplitude hypotheses, and
  isomorphisms in `D(R)`;
  the good complexes and admissible comparison diagrams are derived bridge data and should stay
  private rather than forming the public API.

This file therefore restores the source-facing owner/API: a direct determinant-line construction on
the tor-amplitude `[-1, 0]` perfect subcategory, direct comparison isomorphisms on isomorphisms,
the canonical rank-zero determinant element, and the functor `det` from the core of that
subcategory to the core of invertible modules. The good-complex machinery remains internal bridge
data.
-/

namespace CochainComplex

/-- A good complex in the proof of Stacks Lemma `15.123.4`: a cochain complex concentrated in
degrees `-1` and `0` with finite projective terms there. -/
private structure IsGood (P : Cpx) : Prop where
  isStrictlyGE : P.IsStrictlyGE (-1)
  isStrictlyLE : P.IsStrictlyLE 0
  finite_negOne : Module.Finite R (P.X (-1))
  projective_negOne : Module.Projective R (P.X (-1))
  finite_zero : Module.Finite R (P.X 0)
  projective_zero : Module.Projective R (P.X 0)

attribute [instance] IsGood.isStrictlyGE IsGood.isStrictlyLE
attribute [instance] IsGood.finite_negOne IsGood.projective_negOne
attribute [instance] IsGood.finite_zero IsGood.projective_zero

/-- The determinant line of a good two-term complex, viewed as an object of `ModuleCat R`. -/
private abbrev determinantModule (P : Cpx) (hP : IsGood P) : ModuleCat R :=
  let _ : P.IsStrictlyGE (-1) := hP.isStrictlyGE
  let _ : P.IsStrictlyLE 0 := hP.isStrictlyLE
  let _ : Module.Finite R (P.X (-1)) := hP.finite_negOne
  let _ : Module.Projective R (P.X (-1)) := hP.projective_negOne
  let _ : Module.Finite R (P.X 0) := hP.finite_zero
  let _ : Module.Projective R (P.X 0) := hP.projective_zero
  ModuleCat.of R (CochainComplex.determinantLine P)

/-- Admissibility for a morphism between good complexes, with the support and finite-projective
hypotheses supplied by the two good-complex structures. -/
private abbrev IsGoodAdmissible {K L : Cpx} (hK : IsGood K) (hL : IsGood L) (a : K ⟶ L) : Prop :=
  let _ : K.IsStrictlyGE (-1) := hK.isStrictlyGE
  let _ : K.IsStrictlyLE 0 := hK.isStrictlyLE
  let _ : Module.Finite R (K.X (-1)) := hK.finite_negOne
  let _ : Module.Projective R (K.X (-1)) := hK.projective_negOne
  let _ : Module.Finite R (K.X 0) := hK.finite_zero
  let _ : Module.Projective R (K.X 0) := hK.projective_zero
  let _ : L.IsStrictlyGE (-1) := hL.isStrictlyGE
  let _ : L.IsStrictlyLE 0 := hL.isStrictlyLE
  let _ : Module.Finite R (L.X (-1)) := hL.finite_negOne
  let _ : Module.Projective R (L.X (-1)) := hL.projective_negOne
  let _ : Module.Finite R (L.X 0) := hL.finite_zero
  let _ : Module.Projective R (L.X 0) := hL.projective_zero
  CochainComplex.IsAdmissible a

/-- The determinant isomorphism of an admissible morphism between good complexes. -/
private abbrev determinantIsoOfGood {K L : Cpx} (hK : IsGood K) (hL : IsGood L) (a : K ⟶ L)
    (ha : IsGoodAdmissible hK hL a) :
    determinantModule K hK ≅ determinantModule L hL :=
  let _ : K.IsStrictlyGE (-1) := hK.isStrictlyGE
  let _ : K.IsStrictlyLE 0 := hK.isStrictlyLE
  let _ : Module.Finite R (K.X (-1)) := hK.finite_negOne
  let _ : Module.Projective R (K.X (-1)) := hK.projective_negOne
  let _ : Module.Finite R (K.X 0) := hK.finite_zero
  let _ : Module.Projective R (K.X 0) := hK.projective_zero
  let _ : L.IsStrictlyGE (-1) := hL.isStrictlyGE
  let _ : L.IsStrictlyLE 0 := hL.isStrictlyLE
  let _ : Module.Finite R (L.X (-1)) := hL.finite_negOne
  let _ : Module.Projective R (L.X (-1)) := hL.projective_negOne
  let _ : Module.Finite R (L.X 0) := hL.finite_zero
  let _ : Module.Projective R (L.X 0) := hL.projective_zero
  (CochainComplex.determinantIso a ha).toModuleIso

private def goodOfData (P : Cpx)
    (hPge : P.IsStrictlyGE (-1)) (hPle : P.IsStrictlyLE 0)
    (hPfiniteNegOne : Module.Finite R (P.X (-1)))
    (hPprojectiveNegOne : Module.Projective R (P.X (-1)))
    (hPfiniteZero : Module.Finite R (P.X 0))
    (hPprojectiveZero : Module.Projective R (P.X 0)) :
    IsGood P where
  isStrictlyGE := hPge
  isStrictlyLE := hPle
  finite_negOne := hPfiniteNegOne
  projective_negOne := hPprojectiveNegOne
  finite_zero := hPfiniteZero
  projective_zero := hPprojectiveZero

private abbrev goodOfInstances (P : Cpx)
    [P.IsStrictlyGE (-1)] [P.IsStrictlyLE 0]
    [Module.Finite R (P.X (-1))] [Module.Projective R (P.X (-1))]
    [Module.Finite R (P.X 0)] [Module.Projective R (P.X 0)] :
    IsGood P :=
  goodOfData P inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance

end CochainComplex

open CochainComplex

/-- Bridge/view: every perfect object of `D(R)` with tor-amplitude in `[-1, 0]` admits a good
two-term finite-projective representative. -/
private theorem exists_twoTermFiniteProjectiveRepresentative
    (K : DPerf R) (hamp : HasTorAmplitudeIn K.obj (-1) 0) :
    ∃ P : Cpx, ∃ _ : K.obj ≅ Q.obj P, CochainComplex.IsGood P := by
  have hKpc :=
    (isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension K.obj).1 K.property |>.1
  obtain ⟨E, eK, hEGE, hELE⟩ :=
    exists_strictlySupported_finiteProjective_complex_of_isPseudoCoherent_of_hasTorAmplitudeIn
      hKpc hamp
  refine ⟨(E : Cpx), eK, ?_⟩
  exact
    { isStrictlyGE := hEGE
      isStrictlyLE := hELE
      finite_negOne := by simpa using (E.term_mem (-1)).1
      projective_negOne := by simpa using (E.term_mem (-1)).2
      finite_zero := by simpa using (E.term_mem 0).1
      projective_zero := by simpa using (E.term_mem 0).2 }

namespace DPerf

/-- The full subcategory of perfect derived `R`-complexes whose tor-amplitude is contained in
`[-1, 0]`. -/
abbrev TorNegOneZero (R : Type u) [CommRing R] : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    (fun K : DPerf R ↦ HasTorAmplitudeIn K.obj (-1) 0)

end DPerf

namespace DPerf.TorNegOneZero

open CochainComplex

local notation "PerfTor" => DPerf.TorNegOneZero R
private abbrev perfectObjectProperty : ObjectProperty DMod :=
  (DerivedCategory.IsPerfect : ObjectProperty DMod)

private abbrev perfTorProperty : ObjectProperty (DPerf R) :=
  (fun K : DPerf R ↦ HasTorAmplitudeIn K.obj (-1) 0 : ObjectProperty (DPerf R))

private structure Representative (K : PerfTor) where
  P : Cpx
  e : K.obj.obj ≅ Q.obj P
  hP : IsGood P

namespace Representative

instance {K : PerfTor} (rep : Representative K) : rep.P.IsStrictlyGE (-1) :=
  rep.hP.isStrictlyGE

instance {K : PerfTor} (rep : Representative K) : rep.P.IsStrictlyLE 0 :=
  rep.hP.isStrictlyLE

instance {K : PerfTor} (rep : Representative K) : Module.Finite R (rep.P.X (-1)) :=
  rep.hP.finite_negOne

instance {K : PerfTor} (rep : Representative K) : Module.Projective R (rep.P.X (-1)) :=
  rep.hP.projective_negOne

instance {K : PerfTor} (rep : Representative K) : Module.Finite R (rep.P.X 0) :=
  rep.hP.finite_zero

instance {K : PerfTor} (rep : Representative K) : Module.Projective R (rep.P.X 0) :=
  rep.hP.projective_zero

/-- The determinant line of a specific two-term finite-projective representative. -/
private abbrev determinantLine {K : PerfTor} (rep : Representative K) : ModuleCat R :=
  determinantModule rep.P rep.hP

end Representative

private noncomputable def chosenGoodRepresentative (K : PerfTor) : Cpx :=
  Classical.choose
    (exists_twoTermFiniteProjectiveRepresentative K.obj K.property)

private theorem chosenGoodRepresentative_spec (K : PerfTor) :
    ∃ _ : K.obj.obj ≅ Q.obj (chosenGoodRepresentative K),
      IsGood (chosenGoodRepresentative K) :=
  Classical.choose_spec
    (exists_twoTermFiniteProjectiveRepresentative K.obj K.property)

private noncomputable def chosenGoodRepresentativeIso (K : PerfTor) :
    K.obj.obj ≅ Q.obj (chosenGoodRepresentative K) :=
  Classical.choose (chosenGoodRepresentative_spec K)

private theorem chosenGoodRepresentative_isGood (K : PerfTor) :
    IsGood (chosenGoodRepresentative K) :=
  Classical.choose_spec (chosenGoodRepresentative_spec K)

private instance chosenGoodRepresentative_isStrictlyGE (K : PerfTor) :
    (chosenGoodRepresentative K).IsStrictlyGE (-1) :=
  (chosenGoodRepresentative_isGood K).isStrictlyGE

private instance chosenGoodRepresentative_isStrictlyLE (K : PerfTor) :
    (chosenGoodRepresentative K).IsStrictlyLE 0 :=
  (chosenGoodRepresentative_isGood K).isStrictlyLE

private instance chosenGoodRepresentative_finite_negOne (K : PerfTor) :
    Module.Finite R ((chosenGoodRepresentative K).X (-1)) :=
  (chosenGoodRepresentative_isGood K).finite_negOne

private instance chosenGoodRepresentative_projective_negOne (K : PerfTor) :
    Module.Projective R ((chosenGoodRepresentative K).X (-1)) :=
  (chosenGoodRepresentative_isGood K).projective_negOne

private instance chosenGoodRepresentative_finite_zero (K : PerfTor) :
    Module.Finite R ((chosenGoodRepresentative K).X 0) :=
  (chosenGoodRepresentative_isGood K).finite_zero

private instance chosenGoodRepresentative_projective_zero (K : PerfTor) :
    Module.Projective R ((chosenGoodRepresentative K).X 0) :=
  (chosenGoodRepresentative_isGood K).projective_zero

private noncomputable def someRepresentative (K : PerfTor) : Representative K where
  P := chosenGoodRepresentative K
  e := chosenGoodRepresentativeIso K
  hP := chosenGoodRepresentative_isGood K

/-- The determinant line of a good representative is invertible. -/
private theorem representative_negOneDeterminant_isEquivalence
    {K : PerfTor} (rep : Representative K) :
    (tensorLeft (ModuleCat.of R (Module.det R (rep.P.X (-1))))).IsEquivalence := by
  -- Proof comment: the degree `-1` term is finite projective, so its determinant module is
  -- invertible by the Chapter 15 determinant-line API.
  letI : Module.Invertible R (Module.det R (rep.P.X (-1))) := inferInstance
  exact (ModuleCat.tensorLeft_isEquivalence_iff_moduleInvertible _).2 inferInstance

/-- Helper for Lemma 15.123.4: the degree `0` determinant module of a good representative is
invertible. -/
private theorem representative_zeroDeterminant_isEquivalence
    {K : PerfTor} (rep : Representative K) :
    (tensorLeft (ModuleCat.of R (Module.det R (rep.P.X 0)))).IsEquivalence := by
  -- Proof comment: the same determinant-line invertibility applies in degree `0`.
  letI : Module.Invertible R (Module.det R (rep.P.X 0)) := inferInstance
  exact (ModuleCat.tensorLeft_isEquivalence_iff_moduleInvertible _).2 inferInstance

/-- Helper for Lemma 15.123.4: the tensor model for the determinant line is already invertible
once the two degreewise determinant factors are invertible. -/
private theorem representative_dualTensorDeterminant_isEquivalence
    {K : PerfTor} (rep : Representative K) :
    (tensorLeft (ModuleCat.of R
      (TensorProduct R (Module.Dual R (Module.det R (rep.P.X (-1))))
        (Module.det R (rep.P.X 0))))).IsEquivalence := by
  -- Proof comment: tensor products and duals of invertible modules stay invertible, so the
  -- source proof's tensor-model determinant line is invertible before identifying it with `Hom`.
  letI : Module.Invertible R (Module.det R (rep.P.X (-1))) := inferInstance
  letI : Module.Invertible R (Module.Dual R (Module.det R (rep.P.X (-1)))) := inferInstance
  letI : Module.Invertible R (Module.det R (rep.P.X 0)) := inferInstance
  letI : Module.Invertible R
      (TensorProduct R (Module.Dual R (Module.det R (rep.P.X (-1))))
        (Module.det R (rep.P.X 0))) := inferInstance
  exact (ModuleCat.tensorLeft_isEquivalence_iff_moduleInvertible _).2 inferInstance

/-- Helper for Lemma 15.123.4: the determinant line of a good representative identifies with the
source proof's dual-tensor model via the standard Hom-tensor comparison. -/
private noncomputable def representativeDeterminantLine_iso_dualTensor
    {K : PerfTor} (rep : Representative K) :
    rep.determinantLine ≅ ModuleCat.of R
      (TensorProduct R (Module.Dual R (Module.det R (rep.P.X (-1))))
        (Module.det R (rep.P.X 0))) :=
  -- Proof comment: normalize `Hom(det(P⁻¹), det(P⁰))` by first inserting the tensor unit on the
  -- codomain side, then apply the standard `Hom ⊗ L ≅ Hom(-, - ⊗ L)` comparison, and finally
  -- rewrite `Hom(det(P⁻¹), R)` as the usual linear dual.
  let homTensorIso :
      ModuleCat.of R
          ((Module.det R (rep.P.X (-1))) →ₗ[R]
            TensorProduct R R (Module.det R (rep.P.X 0))) ≅
        ModuleCat.of R
          (TensorProduct R
            ((ModuleCat.of R (Module.det R (rep.P.X (-1)))) ⟶ (ModuleCat.of R R))
            (Module.det R (rep.P.X 0))) := by
      let f :=
        homTensorComparisonHom
          (ModuleCat.of R (Module.det R (rep.P.X (-1))))
          (ModuleCat.of R R)
          (ModuleCat.of R (Module.det R (rep.P.X 0)))
      letI : IsIso f :=
        homTensorComparison_isIso_of_finitePresentation
          (ModuleCat.of R (Module.det R (rep.P.X (-1))))
          (ModuleCat.of R R)
          (ModuleCat.of R (Module.det R (rep.P.X 0)))
      exact (asIso f).symm
  representativeDeterminantLine_homTensorUnitIso rep ≪≫
    homTensorIso ≪≫
    representativeDualTensor_sourceIso rep

/-- The determinant line of a good representative is invertible. -/
private theorem representativeDeterminantLine_isEquivalence
    {K : PerfTor} (rep : Representative K) :
    (tensorLeft rep.determinantLine).IsEquivalence := by
  -- Proof comment: the source proof first replaces `Hom(det(P⁻¹), det(P⁰))` by the tensor model
  -- `det(P⁰) ⊗ det(P⁻¹)ᵛ`, whose invertibility is already isolated above.
  let e := representativeDeterminantLine_iso_dualTensor rep
  have hTensor :
      (tensorLeft (ModuleCat.of R
        (TensorProduct R (Module.Dual R (Module.det R (rep.P.X (-1))))
          (Module.det R (rep.P.X 0))))).IsEquivalence :=
    representative_dualTensorDeterminant_isEquivalence rep
  let hIso := (tensoringLeft (ModuleCat R)).mapIso e
  exact Functor.isEquivalence_of_iso hIso.symm

/-- Helper for Lemma 15.123.4: the tensor-model source object is obtained from the categorical
`Hom` into the tensor unit by rewriting those morphisms as ordinary linear duals. -/
private noncomputable def representativeDualTensor_sourceIso
    {K : PerfTor} (rep : Representative K) :
    ModuleCat.of R
        (TensorProduct R
          ((ModuleCat.of R (Module.det R (rep.P.X (-1)))) ⟶ (ModuleCat.of R R))
          (Module.det R (rep.P.X 0))) ≅
      ModuleCat.of R
        (TensorProduct R (Module.Dual R (Module.det R (rep.P.X (-1))))
          (Module.det R (rep.P.X 0))) :=
  -- Proof comment: this is the domain-side normalization for the source proof's
  -- `Hom(det(P⁻¹), R) ⊗ det(P⁰)` tensor model.
  (LinearEquiv.rTensor (Module.det R (rep.P.X 0))
    (ModuleCat.homLinearEquiv :
      ((ModuleCat.of R (Module.det R (rep.P.X (-1)))) ⟶ (ModuleCat.of R R)) ≃ₗ[R]
        Module.Dual R (Module.det R (rep.P.X (-1))))).toModuleIso

/-- Helper for Lemma 15.123.4: the determinant-line `Hom` object can be normalized by inserting
the tensor unit on the codomain side before the final `Hom`-to-dual-tensor comparison. -/
private noncomputable def representativeDeterminantLine_homTensorUnitIso
    {K : PerfTor} (rep : Representative K) :
    rep.determinantLine ≅ ModuleCat.of R
      ((Module.det R (rep.P.X (-1))) →ₗ[R]
        TensorProduct R R (Module.det R (rep.P.X 0))) :=
  -- Proof comment: this is the codomain-side normalization for the source proof's
  -- `Hom(det(P⁻¹), det(P⁰)) ≅ Hom(det(P⁻¹), R ⊗ det(P⁰))` step.
  (LinearEquiv.arrowCongr
    (LinearEquiv.refl R (Module.det R (rep.P.X (-1))))
    (TensorProduct.lid R (Module.det R (rep.P.X 0))).symm).toModuleIso

private structure ComparisonWitness {K L : DMod} (a : K ≅ L)
    (PK : Cpx) (eK : K ≅ Q.obj PK) (hPK : IsGood PK)
    (PL : Cpx) (eL : L ≅ Q.obj PL) (hPL : IsGood PL) where
  middle : Cpx
  middleGood : IsGood middle
  b : middle ⟶ PK
  hb : IsGoodAdmissible middleGood hPK b
  c : middle ⟶ PL
  hc : IsGoodAdmissible middleGood hPL c
  comm : Q.map b ≫ eK.inv ≫ a.hom = Q.map c ≫ eL.inv

namespace ComparisonWitness

def determinantIso {K L : DMod} {a : K ≅ L}
    {PK : Cpx} {eK : K ≅ Q.obj PK} {hPK : IsGood PK}
    {PL : Cpx} {eL : L ≅ Q.obj PL} {hPL : IsGood PL}
    (w : ComparisonWitness a PK eK hPK PL eL hPL) :
    determinantModule PK hPK ≅ determinantModule PL hPL :=
  (determinantIsoOfGood w.middleGood hPK w.b w.hb).symm ≪≫
    determinantIsoOfGood w.middleGood hPL w.c w.hc

end ComparisonWitness

/-- Helper for Lemma 15.123.4: a good two-term complex is bounded above, so it defines a
`ProjectiveMinus` complex. -/
private theorem good_complex_minus (P : Cpx) (hP : IsGood P) :
    CochainComplex.minus (ModuleCat R) P := by
  -- Proof comment: a good complex is zero in degrees above `0`, which is exactly the bounded-above
  -- condition required by `CochainComplex.minus`.
  exact (CochainComplex.minus_iff (ModuleCat R) P).2 ⟨0, hP.isStrictlyLE⟩

/-- Helper for Lemma 15.123.4: every term of a good two-term complex is projective, with the
off-range terms identified with `0`. -/
private theorem good_complex_projective_term (P : Cpx) (hP : IsGood P) (i : ℤ) :
    Projective (P.X i) := by
  -- Proof comment: the two visible terms are part of the good-complex data; outside `[-1, 0]`
  -- the support bounds make the term zero, and the zero module is projective.
  by_cases hi_negOne : i = -1
  · letI : Module.Projective R (P.X i) := by
        simpa [hi_negOne] using hP.projective_negOne
    infer_instance
  by_cases hi_zero : i = 0
  · letI : Module.Projective R (P.X i) := by
        simpa [hi_zero] using hP.projective_zero
    infer_instance
  have hi_outside : i < -1 ∨ 0 < i := by
    omega
  cases hi_outside with
  | inl hi_lt =>
      letI : Limits.IsZero (P.X i) := P.isZero_of_isStrictlyGE (-1) i hi_lt
      infer_instance
  | inr hi_gt =>
      letI : Limits.IsZero (P.X i) := P.isZero_of_isStrictlyLE 0 i hi_gt
      infer_instance

/-- Helper for Lemma 15.123.4: package a good two-term complex as a bounded-above projective
complex so the Chapter 13 `Qh`/`Q` comparison applies. -/
private noncomputable def good_projective_minus (P : Cpx) (hP : IsGood P) :
    CochainComplex.ProjectiveMinus (ModuleCat R) :=
  ⟨⟨P, good_complex_minus P hP⟩, good_complex_projective_term P hP⟩

/-- Helper for Lemma 15.123.4: conjugating a `Qh`-image along `quotientCompQhIso` recovers the
corresponding `Q`-image of a cochain map. -/
private theorem quotientCompQhIso_homCongr_map
    {K L : Cpx} (f : K ⟶ L) :
    (Iso.homCongr ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app K)
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app L))
      (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).map f)) =
      DerivedCategory.Q.map f := by
  -- Proof comment: this is the naturality square of `quotientCompQhIso`, rewritten as a
  -- conjugation identity between the homotopy-level and cochain-level localizations.
  have hnat :
      DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).map f) ≫
          (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app L =
        (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app K ≫
          DerivedCategory.Q.map f := by
    simpa [Functor.comp_map] using
      (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.naturality f
  calc
    (Iso.homCongr ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app K)
        ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app L))
        (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).map f)) =
      (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app K ≫
          DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).map f) ≫
          (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app L := by
        rfl
    _ =
      (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app K ≫
          ((DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app K ≫
            DerivedCategory.Q.map f) := by
        exact congrArg
          (fun k ↦ (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app K ≫ k) hnat
    _ = DerivedCategory.Q.map f := by
      simpa [Category.assoc] using
        (Iso.inv_hom_id_assoc ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app K)
          (DerivedCategory.Q.map f))

/-- Helper for Lemma 15.123.4: a derived isomorphism between good representatives can be
represented by an actual cochain map. -/
private theorem exists_chainMap_of_goodRepresentative_iso
    {K L : DMod} (a : K ≅ L)
    (PK : Cpx) (eK : K ≅ Q.obj PK) (hPK : IsGood PK)
    (PL : Cpx) (eL : L ≅ Q.obj PL) (hPL : IsGood PL) :
    ∃ f : PK ⟶ PL, DerivedCategory.Q.map f = eK.inv ≫ a.hom ≫ eL.hom := by
  -- Route correction: the remaining source-faithful work starts by lifting the derived arrow to
  -- a literal chain map; only after that should the proof return to the stabilization witness.
  let Ho := HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)
  let Pproj : CochainComplex.ProjectiveMinus (ModuleCat R) := good_projective_minus PK hPK
  let ePK := (DerivedCategory.quotientCompQhIso (ModuleCat R)).app PK
  let ePL := (DerivedCategory.quotientCompQhIso (ModuleCat R)).app PL
  let δ : DerivedCategory.Qh.obj (Ho.obj Pproj) ⟶ DerivedCategory.Qh.obj (Ho.obj PL) :=
    ePK.hom ≫ eK.inv ≫ a.hom ≫ eL.hom ≫ ePL.inv
  obtain ⟨fh, hfh⟩ :=
    (CochainComplex.homotopyCategory_to_derived_bijective_of_boundedAbove_projective Pproj PL)
      .surjective δ
  obtain ⟨f, hf⟩ := Ho.map_surjective fh
  refine ⟨f, ?_⟩
  have hQh :
      DerivedCategory.Qh.map (Ho.map f) = δ := by
    simpa [hf] using hfh
  calc
    DerivedCategory.Q.map f =
      (Iso.homCongr ePK ePL) (DerivedCategory.Qh.map (Ho.map f)) := by
        simpa using (quotientCompQhIso_homCongr_map (R := R) f).symm
    _ = (Iso.homCongr ePK ePL) δ := by
        rw [hQh]
    _ = eK.inv ≫ a.hom ≫ eL.hom := by
        change ePK.inv ≫ (ePK.hom ≫ eK.inv ≫ a.hom ≫ eL.hom ≫ ePL.inv) ≫ ePL.hom =
          eK.inv ≫ a.hom ≫ eL.hom
        simp [Category.assoc]

private theorem exists_comparisonWitness
    {K L : DMod}
    (a : K ≅ L)
    (PK : Cpx) (eK : K ≅ Q.obj PK) (hPK : IsGood PK)
    (PL : Cpx) (eL : L ≅ Q.obj PL) (hPL : IsGood PL) :
    Nonempty (ComparisonWitness a PK eK hPK PL eL hPL) := by
  -- Proof comment: the first source-faithful step is to replace the derived isomorphism by a
  -- literal chain map between the good representatives.
  obtain ⟨f, hf⟩ := exists_chainMap_of_goodRepresentative_iso a PK eK hPK PL eL hPL
  -- TODO: follow the stabilization paragraph of Lemma 15.123.4: choose a finite free surjection
  -- onto `PL.X (-1)`, build the middle complex `PK⁻¹ ⊕ F → PK⁰ ⊕ F`, define the admissible maps
  -- to `PK` and `PL`, and verify the derived commutativity using `hf`.
  sorry

private theorem ComparisonWitness.determinantIso_eq
    {K L : DMod} {a : K ≅ L}
    {PK : Cpx} {eK : K ≅ Q.obj PK} {hPK : IsGood PK}
    {PL : Cpx} {eL : L ≅ Q.obj PL} {hPL : IsGood PL}
    (w₁ w₂ : ComparisonWitness a PK eK hPK PL eL hPL) :
    w₁.determinantIso = w₂.determinantIso := by
  sorry

/-- Helper for Lemma 15.123.4: the identity map on a good complex is admissible, because it is
surjective in degrees `-1` and `0` and its kernel complex is zero. -/
private theorem isGoodAdmissible_id
    (P : Cpx) (hP : IsGood P) :
    IsGoodAdmissible hP hP (𝟙 P) := by
  -- Proof comment: the degreewise identity maps are surjective, and the two kernel modules are
  -- subsingletons because membership in the kernel forces the underlying vector to vanish.
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact ⟨x, rfl⟩
  · intro x
    exact ⟨x, rfl⟩
  · have hker_negOne : Subsingleton (LinearMap.ker ((𝟙 P).f (-1)).hom) := by
      refine ⟨?_⟩
      intro x y
      ext
      have hx : x.1 = 0 := by
        simpa using x.2
      have hy : y.1 = 0 := by
        simpa using y.2
      simpa [hx, hy]
    have hker_zero : Subsingleton (LinearMap.ker ((𝟙 P).f 0).hom) := by
      refine ⟨?_⟩
      intro x y
      ext
      have hx : x.1 = 0 := by
        simpa using x.2
      have hy : y.1 = 0 := by
        simpa using y.2
      simpa [hx, hy]
    constructor
    · intro x y hxy
      exact Subsingleton.elim _ _
    · intro y
      exact ⟨0, Subsingleton.elim _ _⟩

/-- Helper for Lemma 15.123.4: the tautological good diagram for the identity on a fixed good
representative uses that representative itself as the middle term. -/
private noncomputable def reflComparisonWitness
    {K : DMod} {P : Cpx} {e : K ≅ Q.obj P} {hP : IsGood P} :
    ComparisonWitness (Iso.refl K) P e hP P e hP where
  middle := P
  middleGood := hP
  b := 𝟙 P
  hb := isGoodAdmissible_id P hP
  c := 𝟙 P
  hc := isGoodAdmissible_id P hP
  comm := by simp

/-- Helper for Lemma 15.123.4: any witness for the identity on a fixed representative induces the
identity determinant comparison. -/
private theorem comparisonWitness_refl_sameRepresentative_determinantIso
    {K : DMod} {P : Cpx} {e : K ≅ Q.obj P} {hP : IsGood P}
    (w : ComparisonWitness (Iso.refl K) P e hP P e hP) :
    w.determinantIso = Iso.refl _ := by
  -- Proof comment: compare `w` with the tautological identity witness on the same representative;
  -- witness-independence reduces the claim to an explicit cancellation of an isomorphism with its
  -- inverse.
  have hw :
      w.determinantIso =
        (reflComparisonWitness (K := K) (P := P) (e := e) (hP := hP)).determinantIso :=
    w.determinantIso_eq
      (reflComparisonWitness (K := K) (P := P) (e := e) (hP := hP))
  refine hw.trans ?_
  simp [ComparisonWitness.determinantIso, reflComparisonWitness]

private def IsComparisonIso
    {K L : DMod} (a : K ≅ L)
    (PK : Cpx) (eK : K ≅ Q.obj PK) (hPK : IsGood PK)
    (PL : Cpx) (eL : L ≅ Q.obj PL) (hPL : IsGood PL)
    (e : determinantModule PK hPK ≅ determinantModule PL hPL) : Prop :=
  ∃ w : ComparisonWitness a PK eK hPK PL eL hPL, w.determinantIso = e

private theorem existsUnique_isComparisonIso
    {K L : DMod}
    (a : K ≅ L)
    (PK : Cpx) (eK : K ≅ Q.obj PK) (hPK : IsGood PK)
    (PL : Cpx) (eL : L ≅ Q.obj PL) (hPL : IsGood PL) :
    ∃! e : determinantModule PK hPK ≅ determinantModule PL hPL,
      IsComparisonIso a PK eK hPK PL eL hPL e := by
  refine (exists_comparisonWitness a PK eK hPK PL eL hPL).elim ?_
  intro w
  refine ⟨w.determinantIso, ?_, ?_⟩
  · exact ⟨w, rfl⟩
  · intro e he
    rcases he with ⟨w', rfl⟩
    exact (w.determinantIso_eq w').symm

private noncomputable def comparisonIso
    {K L : DMod}
    (a : K ≅ L)
    (PK : Cpx) (eK : K ≅ Q.obj PK) (hPK : IsGood PK)
    (PL : Cpx) (eL : L ≅ Q.obj PL) (hPL : IsGood PL) :
    determinantModule PK hPK ≅ determinantModule PL hPL :=
  Classical.choose
    (ExistsUnique.exists (existsUnique_isComparisonIso a PK eK hPK PL eL hPL))

private theorem comparisonIso_spec
    {K L : DMod}
    (a : K ≅ L)
    (PK : Cpx) (eK : K ≅ Q.obj PK) (hPK : IsGood PK)
    (PL : Cpx) (eL : L ≅ Q.obj PL) (hPL : IsGood PL) :
    IsComparisonIso a PK eK hPK PL eL hPL (comparisonIso a PK eK hPK PL eL hPL) :=
  Classical.choose_spec
    (ExistsUnique.exists (existsUnique_isComparisonIso a PK eK hPK PL eL hPL))

/-- The determinant line attached to a perfect derived `R`-complex of tor-amplitude in
`[-1, 0]`. -/
private noncomputable def rawDeterminantLine (K : PerfTor) : ModuleCat R :=
  determinantModule (chosenGoodRepresentative K) (chosenGoodRepresentative_isGood K)

/-- The canonical comparison isomorphism from the determinant line of `K` to the determinant line
of any two-term finite-projective representative of `K`. -/
private noncomputable def rawDeterminantLineIso (K : PerfTor)
    (P : Cpx) (e : K.obj.obj ≅ Q.obj P)
    [P.IsStrictlyGE (-1)] [P.IsStrictlyLE 0]
    [Module.Finite R (P.X (-1))] [Module.Projective R (P.X (-1))]
    [Module.Finite R (P.X 0)] [Module.Projective R (P.X 0)] :
    rawDeterminantLine K ≅ ModuleCat.of R det(P^•) :=
  comparisonIso (Iso.refl K.obj.obj)
    (chosenGoodRepresentative K) (chosenGoodRepresentativeIso K) (chosenGoodRepresentative_isGood K)
    P e (goodOfInstances P)

/-- The determinant line of a tor-amplitude `[-1, 0]` perfect complex is invertible. -/
private theorem rawDeterminantLine_isEquivalence (K : PerfTor) :
    (tensorLeft (rawDeterminantLine K)).IsEquivalence := by
  exact representativeDeterminantLine_isEquivalence (someRepresentative K)

/-- The underlying isomorphism in `D(R)` induced by an isomorphism in the tor-amplitude full
subcategory of `D_{perf}(R)`. -/
private abbrev underlyingIso {K L : PerfTor} (a : K ≅ L) :
    K.obj.obj ≅ L.obj.obj :=
  perfectObjectProperty.ι.mapIso (perfTorProperty.ι.mapIso a)

/-- The determinant comparison isomorphism attached to an isomorphism of tor-amplitude `[-1, 0]`
perfect complexes on the chosen bridge objects. -/
private noncomputable def rawDeterminantIso {K L : PerfTor} (a : K ≅ L) :
    rawDeterminantLine K ≅ rawDeterminantLine L :=
  comparisonIso
    (underlyingIso a)
    (chosenGoodRepresentative K) (chosenGoodRepresentativeIso K) (chosenGoodRepresentative_isGood K)
    (chosenGoodRepresentative L) (chosenGoodRepresentativeIso L) (chosenGoodRepresentative_isGood L)

/-- The determinant functor on the groupoid of perfect derived `R`-complexes with tor-amplitude in
`[-1, 0]`. -/
private noncomputable def detToModule : Core PerfTor ⥤ ModuleCat R where
  obj K := rawDeterminantLine K.of
  map f := (rawDeterminantIso f.iso).hom
  map_id := by
    intro K
    -- Proof comment: for the identity isomorphism, both chosen representatives agree, so the
    -- source proof's identity paragraph is realized by the tautological witness on that single
    -- good representative.
    let w :
        ComparisonWitness (Iso.refl K.of.obj.obj)
          (chosenGoodRepresentative K.of) (chosenGoodRepresentativeIso K.of)
          (chosenGoodRepresentative_isGood K.of)
          (chosenGoodRepresentative K.of) (chosenGoodRepresentativeIso K.of)
          (chosenGoodRepresentative_isGood K.of) :=
      reflComparisonWitness (K := K.of.obj.obj) (P := chosenGoodRepresentative K.of)
        (e := chosenGoodRepresentativeIso K.of) (hP := chosenGoodRepresentative_isGood K.of)
    have h_refl :
        IsComparisonIso (Iso.refl K.of.obj.obj)
          (chosenGoodRepresentative K.of) (chosenGoodRepresentativeIso K.of)
          (chosenGoodRepresentative_isGood K.of)
          (chosenGoodRepresentative K.of) (chosenGoodRepresentativeIso K.of)
          (chosenGoodRepresentative_isGood K.of)
          (Iso.refl (rawDeterminantLine K.of)) := by
      refine ⟨w, ?_⟩
      simpa [rawDeterminantLine] using
        comparisonWitness_refl_sameRepresentative_determinantIso
          (K := K.of.obj.obj) (P := chosenGoodRepresentative K.of)
          (e := chosenGoodRepresentativeIso K.of)
          (hP := chosenGoodRepresentative_isGood K.of) w
    obtain ⟨e, he, huniq⟩ :=
      existsUnique_isComparisonIso
        (Iso.refl K.of.obj.obj)
        (chosenGoodRepresentative K.of) (chosenGoodRepresentativeIso K.of)
        (chosenGoodRepresentative_isGood K.of)
        (chosenGoodRepresentative K.of) (chosenGoodRepresentativeIso K.of)
        (chosenGoodRepresentative_isGood K.of)
    have hcomparison :
        comparisonIso
            (Iso.refl K.of.obj.obj)
            (chosenGoodRepresentative K.of) (chosenGoodRepresentativeIso K.of)
            (chosenGoodRepresentative_isGood K.of)
            (chosenGoodRepresentative K.of) (chosenGoodRepresentativeIso K.of)
            (chosenGoodRepresentative_isGood K.of) = e :=
      huniq _ <|
        comparisonIso_spec
          (Iso.refl K.of.obj.obj)
          (chosenGoodRepresentative K.of) (chosenGoodRepresentativeIso K.of)
          (chosenGoodRepresentative_isGood K.of)
          (chosenGoodRepresentative K.of) (chosenGoodRepresentativeIso K.of)
          (chosenGoodRepresentative_isGood K.of)
    have hid :
        Iso.refl (rawDeterminantLine K.of) = e :=
      huniq _ h_refl
    simpa [rawDeterminantIso, underlyingIso] using
      congrArg Iso.hom (hcomparison.trans hid.symm)
  map_comp := by
    intro X Y Z f g
    sorry

/-- The determinant functor on the groupoid of perfect derived `R`-complexes with tor-amplitude in
`[-1, 0]`, landing in the full subcategory of invertible `R`-modules. -/
private noncomputable def detToInvertible :
    Core PerfTor ⥤ ModuleCat.InvertibleSubcategory R :=
  ObjectProperty.lift
    ((fun M : ModuleCat R ↦ (tensorLeft M).IsEquivalence) : ObjectProperty (ModuleCat R))
    detToModule
    (fun K ↦ rawDeterminantLine_isEquivalence K.of)

/-- The determinant line attached to a perfect derived `R`-complex of tor-amplitude in
`[-1, 0]`. -/
abbrev determinantLine (K : PerfTor) : ModuleCat R :=
  rawDeterminantLine K

private theorem determinantLine_eq_rawDeterminantLine (K : PerfTor) :
    K.determinantLine = rawDeterminantLine K :=
  rfl

/-- The determinant line of a tor-amplitude `[-1, 0]` perfect complex is invertible. -/
theorem determinantLine_isEquivalence (K : PerfTor) :
    (tensorLeft K.determinantLine).IsEquivalence :=
  rawDeterminantLine_isEquivalence K

/-- The canonical comparison isomorphism from the determinant line of `K` to the determinant line
of any two-term finite-projective representative of `K`. -/
noncomputable abbrev determinantLineIso (K : PerfTor)
    (P : Cpx) (e : K.obj.obj ≅ Q.obj P)
    [P.IsStrictlyGE (-1)] [P.IsStrictlyLE 0]
    [Module.Finite R (P.X (-1))] [Module.Projective R (P.X (-1))]
    [Module.Finite R (P.X 0)] [Module.Projective R (P.X 0)] :
    K.determinantLine ≅ ModuleCat.of R det(P^•) :=
  (eqToIso (K.determinantLine_eq_rawDeterminantLine)).symm ≪≫
    rawDeterminantLineIso K P e

/-- Rank `0` for a tor-amplitude `[-1, 0]` perfect complex, computed on any two-term finite
projective representative in degrees `-1` and `0`. The comparison theorem below identifies this
with the rank-zero condition on every such representative. -/
def IsRankZero (K : PerfTor) : Prop :=
  ∀ (P : Cpx) (_ : K.obj.obj ≅ Q.obj P)
    [P.IsStrictlyGE (-1)] [P.IsStrictlyLE 0]
    [Module.Finite R (P.X (-1))] [Module.Projective R (P.X (-1))]
    [Module.Finite R (P.X 0)] [Module.Projective R (P.X 0)],
      CochainComplex.IsRankZero P

/-- Helper for Lemma 15.123.4: an admissible map between good complexes preserves the rank-zero
condition from source to target. -/
private theorem isGoodAdmissible_target_of_rankZero_source
    {K L : Cpx} (hK : IsGood K) (hL : IsGood L) {a : K ⟶ L}
    (ha : IsGoodAdmissible hK hL a) (hK0 : CochainComplex.IsRankZero K) :
    CochainComplex.IsRankZero L := by
  let _ : K.IsStrictlyGE (-1) := hK.isStrictlyGE
  let _ : K.IsStrictlyLE 0 := hK.isStrictlyLE
  let _ : Module.Finite R (K.X (-1)) := hK.finite_negOne
  let _ : Module.Projective R (K.X (-1)) := hK.projective_negOne
  let _ : Module.Finite R (K.X 0) := hK.finite_zero
  let _ : Module.Projective R (K.X 0) := hK.projective_zero
  let _ : L.IsStrictlyGE (-1) := hL.isStrictlyGE
  let _ : L.IsStrictlyLE 0 := hL.isStrictlyLE
  let _ : Module.Finite R (L.X (-1)) := hL.finite_negOne
  let _ : Module.Projective R (L.X (-1)) := hL.projective_negOne
  let _ : Module.Finite R (L.X 0) := hL.finite_zero
  let _ : Module.Projective R (L.X 0) := hL.projective_zero
  intro p
  let eker :
      LinearMap.ker (a.f (-1)).hom ≃ₗ[R] LinearMap.ker (a.f 0).hom :=
    LinearEquiv.ofBijective (CochainComplex.kernelDifferential a)
      ha.kernelDifferential_bijective
  have hker :
      Module.rankAtStalk (LinearMap.ker (a.f (-1)).hom) p =
        Module.rankAtStalk (LinearMap.ker (a.f 0).hom) p :=
    Module.rankAtStalk_eq_of_linearEquiv eker p
  have hsum :
      Module.rankAtStalk (LinearMap.ker (a.f (-1)).hom) p +
          Module.rankAtStalk (L.X (-1)) p =
        Module.rankAtStalk (LinearMap.ker (a.f (-1)).hom) p +
          Module.rankAtStalk (L.X 0) p := by
    -- Proof comment: rewrite both source ranks by the short exact kernel rows and then cancel the
    -- equal kernel ranks supplied by admissibility.
    calc
      Module.rankAtStalk (LinearMap.ker (a.f (-1)).hom) p +
          Module.rankAtStalk (L.X (-1)) p =
        Module.rankAtStalk (K.X (-1)) p := by
          symm
          exact Module.rankAtStalk_eq_ker_add_of_surjective
            (f := (a.f (-1)).hom) ha.mapNegOne_surjective p
      _ = Module.rankAtStalk (K.X 0) p := hK0 p
      _ = Module.rankAtStalk (LinearMap.ker (a.f 0).hom) p +
            Module.rankAtStalk (L.X 0) p := by
          exact Module.rankAtStalk_eq_ker_add_of_surjective
            (f := (a.f 0).hom) ha.mapZero_surjective p
      _ = Module.rankAtStalk (LinearMap.ker (a.f (-1)).hom) p +
            Module.rankAtStalk (L.X 0) p := by
          rw [hker]
  exact Nat.add_left_cancel hsum

/-- Helper for Lemma 15.123.4: a comparison witness identifies the rank-zero condition on its two
endpoint representatives. -/
private theorem ComparisonWitness.isRankZero_iff
    {K L : DMod} {a : K ≅ L}
    {PK : Cpx} {eK : K ≅ Q.obj PK} {hPK : IsGood PK}
    {PL : Cpx} {eL : L ≅ Q.obj PL} {hPL : IsGood PL}
    (w : ComparisonWitness a PK eK hPK PL eL hPL) :
    CochainComplex.IsRankZero PK ↔ CochainComplex.IsRankZero PL := by
  let _ : PK.IsStrictlyGE (-1) := hPK.isStrictlyGE
  let _ : PK.IsStrictlyLE 0 := hPK.isStrictlyLE
  let _ : Module.Finite R (PK.X (-1)) := hPK.finite_negOne
  let _ : Module.Projective R (PK.X (-1)) := hPK.projective_negOne
  let _ : Module.Finite R (PK.X 0) := hPK.finite_zero
  let _ : Module.Projective R (PK.X 0) := hPK.projective_zero
  let _ : PL.IsStrictlyGE (-1) := hPL.isStrictlyGE
  let _ : PL.IsStrictlyLE 0 := hPL.isStrictlyLE
  let _ : Module.Finite R (PL.X (-1)) := hPL.finite_negOne
  let _ : Module.Projective R (PL.X (-1)) := hPL.projective_negOne
  let _ : Module.Finite R (PL.X 0) := hPL.finite_zero
  let _ : Module.Projective R (PL.X 0) := hPL.projective_zero
  let _ : w.middle.IsStrictlyGE (-1) := w.middleGood.isStrictlyGE
  let _ : w.middle.IsStrictlyLE 0 := w.middleGood.isStrictlyLE
  let _ : Module.Finite R (w.middle.X (-1)) := w.middleGood.finite_negOne
  let _ : Module.Projective R (w.middle.X (-1)) := w.middleGood.projective_negOne
  let _ : Module.Finite R (w.middle.X 0) := w.middleGood.finite_zero
  let _ : Module.Projective R (w.middle.X 0) := w.middleGood.projective_zero
  constructor
  · intro hPK0
    -- Proof comment: pass rank zero from `PK` to the middle complex along `b`, then descend it to
    -- `PL` along `c`.
    have hMiddle :
        CochainComplex.IsRankZero w.middle :=
      CochainComplex.isRankZero_source_of_rankZero_target w.b w.hb hPK0
    exact isGoodAdmissible_target_of_rankZero_source w.middleGood hPL w.hc hMiddle
  · intro hPL0
    -- Proof comment: the same argument with the two admissible maps exchanged gives the converse.
    have hMiddle :
        CochainComplex.IsRankZero w.middle :=
      CochainComplex.isRankZero_source_of_rankZero_target w.c w.hc hPL0
    exact isGoodAdmissible_target_of_rankZero_source w.middleGood hPK w.hb hMiddle

/-- Helper for Lemma 15.123.4: a comparison witness transports the canonical determinant element
of a rank-zero target representative back to the canonical determinant element of the source
representative. -/
private theorem ComparisonWitness.determinantIso_hom_canonicalElement
    {K L : DMod} {a : K ≅ L}
    {PK : Cpx} {eK : K ≅ Q.obj PK} {hPK : IsGood PK}
    {PL : Cpx} {eL : L ≅ Q.obj PL} {hPL : IsGood PL}
    (w : ComparisonWitness a PK eK hPK PL eL hPL)
    (hPL0 : CochainComplex.IsRankZero PL) :
    w.determinantIso.hom (δ(PK^•; (w.isRankZero_iff).2 hPL0)) = δ(PL^•; hPL0) := by
  let hMiddle :
      CochainComplex.IsRankZero w.middle :=
    CochainComplex.isRankZero_source_of_rankZero_target w.c w.hc hPL0
  have hb_inv :
      (determinantIsoOfGood w.middleGood hPK w.b w.hb).inv
        (δ(PK^•; (w.isRankZero_iff).2 hPL0)) =
      δ(w.middle^•; hMiddle) := by
    -- Proof comment: the admissible map `b` is contravariant on canonical elements, so its
    -- inverse determinant map recovers the canonical element on the middle complex.
    simpa [determinantIsoOfGood] using
      (CochainComplex.determinantMap_maps_canonicalElement_of_rankZero_target
        w.b w.hb ((w.isRankZero_iff).2 hPL0))
  have hc_hom :
      (determinantIsoOfGood w.middleGood hPL w.c w.hc).hom
        (δ(w.middle^•; hMiddle)) =
      δ(PL^•; hPL0) := by
    -- Proof comment: the admissible map `c` carries the middle canonical element forward to the
    -- canonical element on the target representative.
    simpa [determinantIsoOfGood] using
      (CochainComplex.determinantIso_maps_canonicalElement_of_rankZero_target
        w.c w.hc hPL0)
  -- Proof comment: by definition, `w.determinantIso` first inverts the determinant comparison for
  -- `b` and then applies the determinant comparison for `c`.
  change
    (determinantIsoOfGood w.middleGood hPL w.c w.hc).hom
      ((determinantIsoOfGood w.middleGood hPK w.b w.hb).inv
        (δ(PK^•; (w.isRankZero_iff).2 hPL0))) =
      δ(PL^•; hPL0)
  rw [hb_inv]
  exact hc_hom

/-- Bridge/view: the intrinsic rank-zero condition on a tor-amplitude `[-1, 0]` perfect complex is
computed by any two-term finite-projective representative. -/
theorem isRankZero_iff
    (K : PerfTor) (P : Cpx) (e : K.obj.obj ≅ Q.obj P)
    [P.IsStrictlyGE (-1)] [P.IsStrictlyLE 0]
    [Module.Finite R (P.X (-1))] [Module.Projective R (P.X (-1))]
    [Module.Finite R (P.X 0)] [Module.Projective R (P.X 0)] :
    K.IsRankZero ↔ CochainComplex.IsRankZero P := by
  constructor
  · intro hK
    -- Proof comment: the intrinsic owner is quantified over all good representatives, so this
    -- direction is just evaluation at the chosen representative `(P, e)`.
    exact hK P e
  · intro hP0
    -- Proof comment: compare any other good representative of `K` with `(P, e)` via a good
    -- diagram; the witness transports the rank-zero condition in both directions.
    intro P' e'
    let hP : IsGood P := goodOfInstances P
    let hP' : IsGood P' := goodOfInstances P'
    obtain ⟨w⟩ :=
      exists_comparisonWitness (Iso.refl K.obj.obj) P' e' hP' P e hP
    exact (w.isRankZero_iff).2 hP0

/-- The determinant comparison isomorphism attached to an isomorphism of tor-amplitude `[-1, 0]`
perfect complexes. -/
noncomputable abbrev determinantIso {K L : PerfTor} (a : K ≅ L) :
    K.determinantLine ≅ L.determinantLine :=
  rawDeterminantIso a

/-- The chosen good representative stays internal. Its determinant-line comparison isomorphism is
the bridge used to prove the representative-independent canonical-element characterization. -/
private noncomputable abbrev chosenDeterminantLineIso (K : PerfTor) :
    K.determinantLine ≅ ModuleCat.of R det((chosenGoodRepresentative K)^•) :=
  K.determinantLineIso (chosenGoodRepresentative K) (chosenGoodRepresentativeIso K)

/-- Helper for Lemma 15.123.4: the determinant-line comparison from the chosen representative to
itself is the identity isomorphism. -/
private theorem chosenDeterminantLineIso_refl (K : PerfTor) :
    chosenDeterminantLineIso K = Iso.refl K.determinantLine := by
  let w :
      ComparisonWitness (Iso.refl K.obj.obj)
        (chosenGoodRepresentative K) (chosenGoodRepresentativeIso K)
        (chosenGoodRepresentative_isGood K)
        (chosenGoodRepresentative K) (chosenGoodRepresentativeIso K)
        (chosenGoodRepresentative_isGood K) :=
    reflComparisonWitness (K := K.obj.obj) (P := chosenGoodRepresentative K)
      (e := chosenGoodRepresentativeIso K) (hP := chosenGoodRepresentative_isGood K)
  have h_refl :
      IsComparisonIso (Iso.refl K.obj.obj)
        (chosenGoodRepresentative K) (chosenGoodRepresentativeIso K)
        (chosenGoodRepresentative_isGood K)
        (chosenGoodRepresentative K) (chosenGoodRepresentativeIso K)
        (chosenGoodRepresentative_isGood K)
        (Iso.refl (rawDeterminantLine K)) := by
    refine ⟨w, ?_⟩
    -- Proof comment: the tautological witness realizes the identity comparison on the chosen
    -- representative.
    simpa [rawDeterminantLine] using
      comparisonWitness_refl_sameRepresentative_determinantIso
        (K := K.obj.obj) (P := chosenGoodRepresentative K)
        (e := chosenGoodRepresentativeIso K)
        (hP := chosenGoodRepresentative_isGood K) w
  obtain ⟨e, he, huniq⟩ :=
    existsUnique_isComparisonIso
      (Iso.refl K.obj.obj)
      (chosenGoodRepresentative K) (chosenGoodRepresentativeIso K)
      (chosenGoodRepresentative_isGood K)
      (chosenGoodRepresentative K) (chosenGoodRepresentativeIso K)
      (chosenGoodRepresentative_isGood K)
  have hcomparison :
      comparisonIso
          (Iso.refl K.obj.obj)
          (chosenGoodRepresentative K) (chosenGoodRepresentativeIso K)
          (chosenGoodRepresentative_isGood K)
          (chosenGoodRepresentative K) (chosenGoodRepresentativeIso K)
          (chosenGoodRepresentative_isGood K) = e :=
    huniq _ <|
      comparisonIso_spec
        (Iso.refl K.obj.obj)
        (chosenGoodRepresentative K) (chosenGoodRepresentativeIso K)
        (chosenGoodRepresentative_isGood K)
        (chosenGoodRepresentative K) (chosenGoodRepresentativeIso K)
        (chosenGoodRepresentative_isGood K)
  have hid :
      Iso.refl (rawDeterminantLine K) = e :=
    huniq _ h_refl
  -- Proof comment: `chosenDeterminantLineIso` is the public wrapper around this self-comparison,
  -- and the wrapper contributes only the definitional identification `determinantLine = raw...`.
  simpa [chosenDeterminantLineIso, determinantLineIso, rawDeterminantLineIso,
    determinantLine_eq_rawDeterminantLine] using
    congrArg
      (fun i ↦ (eqToIso (K.determinantLine_eq_rawDeterminantLine)).symm ≪≫ i)
      (hcomparison.trans hid.symm)

/-- A determinant-line element is canonical if every two-term finite-projective representative
evaluates to the canonical complex-level determinant element. The companion theorem
`isCanonicalElementValue_iff` re-expresses this criterion at any single representative. -/
def IsCanonicalElementValue (K : PerfTor) (hK : K.IsRankZero) (δ : K.determinantLine) : Prop :=
  ∀ (P : Cpx) (e : K.obj.obj ≅ Q.obj P)
    [P.IsStrictlyGE (-1)] [P.IsStrictlyLE 0]
    [Module.Finite R (P.X (-1))] [Module.Projective R (P.X (-1))]
    [Module.Finite R (P.X 0)] [Module.Projective R (P.X 0)],
      (K.determinantLineIso P e).hom δ = δ(P^•; (K.isRankZero_iff P e).1 hK)

theorem isCanonicalElementValue_iff
    (K : PerfTor) (hK : K.IsRankZero) (δ : K.determinantLine)
    (P : Cpx) (e : K.obj.obj ≅ Q.obj P)
    [P.IsStrictlyGE (-1)] [P.IsStrictlyLE 0]
    [Module.Finite R (P.X (-1))] [Module.Projective R (P.X (-1))]
    [Module.Finite R (P.X 0)] [Module.Projective R (P.X 0)] :
    K.IsCanonicalElementValue hK δ ↔
      (K.determinantLineIso P e).hom δ = δ(P^•; (K.isRankZero_iff P e).1 hK) := by
  sorry

private theorem existsUnique_isCanonicalElementValue
    (K : PerfTor) (hK : K.IsRankZero) :
    ∃! δ : K.determinantLine, K.IsCanonicalElementValue hK δ := by
  let hChosen :
      CochainComplex.IsRankZero (chosenGoodRepresentative K) :=
    (K.isRankZero_iff (chosenGoodRepresentative K) (chosenGoodRepresentativeIso K)).1 hK
  let δ0 : K.determinantLine :=
    (chosenDeterminantLineIso K).inv (δ((chosenGoodRepresentative K)^•; hChosen))
  refine ⟨δ0, ?_, ?_⟩
  · -- Proof comment: it suffices to check the defining condition on the chosen representative,
    -- because `isCanonicalElementValue_iff` reduces the global criterion to any single good one.
    refine
      (K.isCanonicalElementValue_iff hK δ0
        (chosenGoodRepresentative K) (chosenGoodRepresentativeIso K)).2 ?_
    simp [δ0, chosenDeterminantLineIso, hChosen]
  · intro δ hδ
    -- Proof comment: two canonical elements have the same image in the chosen representative, and
    -- the chosen determinant-line comparison is an isomorphism, so that image determines `δ`.
    have hδ_image :
        (chosenDeterminantLineIso K).hom δ =
          δ((chosenGoodRepresentative K)^•; hChosen) :=
      (K.isCanonicalElementValue_iff hK δ
        (chosenGoodRepresentative K) (chosenGoodRepresentativeIso K)).1 hδ
    have hδ0_image :
        (chosenDeterminantLineIso K).hom δ0 =
          δ((chosenGoodRepresentative K)^•; hChosen) :=
      by
        simp [δ0, chosenDeterminantLineIso, hChosen]
    exact (chosenDeterminantLineIso K).hom.injective (hδ_image.trans hδ0_image.symm)

/-- The canonical determinant element attached to a rank-zero tor-amplitude `[-1, 0]` perfect
complex. -/
noncomputable def canonicalElement (K : PerfTor) (hK : K.IsRankZero) :
    K.determinantLine :=
  Classical.choose (ExistsUnique.exists (existsUnique_isCanonicalElementValue K hK))

/-- The canonical determinant element satisfies its defining representative-independent
characterization. -/
theorem canonicalElement_spec
    (K : PerfTor) (hK : K.IsRankZero) :
    K.IsCanonicalElementValue hK (K.canonicalElement hK) := by
  exact Classical.choose_spec (ExistsUnique.exists (existsUnique_isCanonicalElementValue K hK))

/-- The canonical determinant element is computed by any rank-zero two-term finite-projective
representative. -/
theorem determinantLineIso_hom_canonicalElement
    (K : PerfTor) (hK : K.IsRankZero)
    (P : Cpx) (e : K.obj.obj ≅ Q.obj P)
    [P.IsStrictlyGE (-1)] [P.IsStrictlyLE 0]
    [Module.Finite R (P.X (-1))] [Module.Projective R (P.X (-1))]
    [Module.Finite R (P.X 0)] [Module.Projective R (P.X 0)] :
    (K.determinantLineIso P e).hom (K.canonicalElement hK) =
      δ(P^•; (K.isRankZero_iff P e).1 hK) :=
  (K.isCanonicalElementValue_iff hK (K.canonicalElement hK) P e).1
    (K.canonicalElement_spec hK)

/-- An isomorphism preserves the rank-zero condition. -/
theorem isRankZero_of_iso {K L : PerfTor} (a : K ≅ L) (hL : L.IsRankZero) :
    K.IsRankZero := by
  intro P e
  -- Proof comment: compare the arbitrary representative `(P, e)` of `K` with the chosen good
  -- representative of `L` through the derived isomorphism `a`; rank zero on `L` then transfers
  -- across the resulting good diagram.
  let hP : IsGood P := goodOfInstances P
  let hChosenL : IsGood (chosenGoodRepresentative L) := chosenGoodRepresentative_isGood L
  have hRankChosenL :
      CochainComplex.IsRankZero (chosenGoodRepresentative L) :=
    hL (chosenGoodRepresentative L) (chosenGoodRepresentativeIso L)
  obtain ⟨w⟩ :=
    exists_comparisonWitness (underlyingIso a) P e hP
      (chosenGoodRepresentative L) (chosenGoodRepresentativeIso L) hChosenL
  exact (w.isRankZero_iff).2 hRankChosenL

/-- The determinant comparison isomorphism carries canonical rank-zero determinant elements to
canonical rank-zero determinant elements. -/
theorem determinantIso_hom_canonicalElement
    {K L : PerfTor} (a : K ≅ L) (hL : L.IsRankZero) :
    (determinantIso a).hom (K.canonicalElement (isRankZero_of_iso a hL)) =
      L.canonicalElement hL := by
  let hK : K.IsRankZero := isRankZero_of_iso a hL
  let hChosenK :
      CochainComplex.IsRankZero (chosenGoodRepresentative K) :=
    (K.isRankZero_iff (chosenGoodRepresentative K) (chosenGoodRepresentativeIso K)).1 hK
  let hChosenL :
      CochainComplex.IsRankZero (chosenGoodRepresentative L) :=
    (L.isRankZero_iff (chosenGoodRepresentative L) (chosenGoodRepresentativeIso L)).1 hL
  obtain ⟨w⟩ :=
    exists_comparisonWitness (underlyingIso a)
      (chosenGoodRepresentative K) (chosenGoodRepresentativeIso K)
      (chosenGoodRepresentative_isGood K)
      (chosenGoodRepresentative L) (chosenGoodRepresentativeIso L)
      (chosenGoodRepresentative_isGood L)
  rcases
    comparisonIso_spec
      (underlyingIso a)
      (chosenGoodRepresentative K) (chosenGoodRepresentativeIso K)
      (chosenGoodRepresentative_isGood K)
      (chosenGoodRepresentative L) (chosenGoodRepresentativeIso L)
      (chosenGoodRepresentative_isGood L) with
    ⟨w', hw'⟩
  have hwIso :
      w.determinantIso = determinantIso a := by
    -- Proof comment: any witness for the chosen representatives computes the same determinant
    -- comparison isomorphism by witness-independence.
    calc
      w.determinantIso = w'.determinantIso := w.determinantIso_eq w'
      _ = determinantIso a := by
        simpa [determinantIso, rawDeterminantIso] using hw'
  have hKspec :
      K.canonicalElement hK = δ((chosenGoodRepresentative K)^•; hChosenK) := by
    -- Proof comment: on the chosen representative, the public comparison isomorphism is the
    -- identity, so the defining criterion for `canonicalElement` simplifies to equality itself.
    have hspec :=
      (K.canonicalElement_spec hK)
        (chosenGoodRepresentative K) (chosenGoodRepresentativeIso K)
    simpa [chosenDeterminantLineIso_refl K] using hspec
  have hLspec :
      L.canonicalElement hL = δ((chosenGoodRepresentative L)^•; hChosenL) := by
    -- Proof comment: the same self-comparison simplification identifies the chosen representative
    -- value of `L.canonicalElement`.
    have hspec :=
      (L.canonicalElement_spec hL)
        (chosenGoodRepresentative L) (chosenGoodRepresentativeIso L)
    simpa [chosenDeterminantLineIso_refl L] using hspec
  have hwMap :
      w.determinantIso.hom (δ((chosenGoodRepresentative K)^•; hChosenK)) =
        δ((chosenGoodRepresentative L)^•; hChosenL) := by
    -- Proof comment: once the rank-zero condition is read on the chosen representatives, the
    -- witness-level canonical-element transport theorem applies directly.
    simpa [hChosenK, hChosenL] using
      w.determinantIso_hom_canonicalElement hChosenL
  calc
    (determinantIso a).hom (K.canonicalElement hK) =
      (determinantIso a).hom (δ((chosenGoodRepresentative K)^•; hChosenK)) := by
        rw [hKspec]
    _ = w.determinantIso.hom (δ((chosenGoodRepresentative K)^•; hChosenK)) := by
        rw [hwIso]
    _ = δ((chosenGoodRepresentative L)^•; hChosenL) := hwMap
    _ = L.canonicalElement hL := by
        rw [hLspec]

end DPerf.TorNegOneZero

end

namespace DPerf.TorNegOneZero

variable {R : Type u} [CommRing R]

/-- The determinant functor on the groupoid of perfect derived `R`-complexes with tor-amplitude in
`[-1, 0]`, presented canonically as a functor to the core of invertible `R`-modules. -/
noncomputable abbrev det :
    Core (DPerf.TorNegOneZero R) ⥤ ModuleCat.InvertibleCore R :=
  let F : Core (DPerf.TorNegOneZero R) ⥤ ModuleCat.InvertibleSubcategory R :=
    detToInvertible
  Core.functorToCore F

@[simp] theorem det_obj (K : DPerf.TorNegOneZero R) :
    (det.obj ⟨K⟩).of.obj = K.determinantLine :=
  rfl

end DPerf.TorNegOneZero

end CategoryTheory
