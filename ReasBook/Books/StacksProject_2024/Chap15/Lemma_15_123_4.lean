import Mathlib
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Definition_15_75_1
import StacksProject_2024.Chap15.Definition_15_118_1
import StacksProject_2024.Chap15.Lemma_15_75_2
import StacksProject_2024.Chap15.Lemma_15_79_1
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
private theorem representativeDeterminantLine_isEquivalence
    {K : PerfTor} (rep : Representative K) :
    (tensorLeft rep.determinantLine).IsEquivalence := by
  sorry

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

private theorem exists_comparisonWitness
    {K L : DMod}
    (a : K ≅ L)
    (PK : Cpx) (eK : K ≅ Q.obj PK) (hPK : IsGood PK)
    (PL : Cpx) (eL : L ≅ Q.obj PL) (hPL : IsGood PL) :
    Nonempty (ComparisonWitness a PK eK hPK PL eL hPL) := by
  sorry

private theorem ComparisonWitness.determinantIso_eq
    {K L : DMod} {a : K ≅ L}
    {PK : Cpx} {eK : K ≅ Q.obj PK} {hPK : IsGood PK}
    {PL : Cpx} {eL : L ≅ Q.obj PL} {hPL : IsGood PL}
    (w₁ w₂ : ComparisonWitness a PK eK hPK PL eL hPL) :
    w₁.determinantIso = w₂.determinantIso := by
  sorry

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
    sorry
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

/-- Bridge/view: the intrinsic rank-zero condition on a tor-amplitude `[-1, 0]` perfect complex is
computed by any two-term finite-projective representative. -/
theorem isRankZero_iff
    (K : PerfTor) (P : Cpx) (e : K.obj.obj ≅ Q.obj P)
    [P.IsStrictlyGE (-1)] [P.IsStrictlyLE 0]
    [Module.Finite R (P.X (-1))] [Module.Projective R (P.X (-1))]
    [Module.Finite R (P.X 0)] [Module.Projective R (P.X 0)] :
    K.IsRankZero ↔ CochainComplex.IsRankZero P := by
  sorry

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
  sorry

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
  sorry

/-- The determinant comparison isomorphism carries canonical rank-zero determinant elements to
canonical rank-zero determinant elements. -/
theorem determinantIso_hom_canonicalElement
    {K L : PerfTor} (a : K ≅ L) (hL : L.IsRankZero) :
    (determinantIso a).hom (K.canonicalElement (isRankZero_of_iso a hL)) =
      L.canonicalElement hL := by
  sorry

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
