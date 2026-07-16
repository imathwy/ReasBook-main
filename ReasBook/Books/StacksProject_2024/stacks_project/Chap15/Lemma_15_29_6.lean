import StacksProject_2024.stacks_project.Chap15.Lemma_15_29_1
import StacksProject_2024.stacks_project.Chap15.Situation_15_92_15

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open RingTheory.Sequence
open ModuleCat
open ModuleCat.exteriorPower
open Set
open scoped KoszulComplex

/-
Domain-style sampling for the powered Koszul description of the extended alternating Čech complex:
- owner abstractions inspected:
  `extendedAlternatingCechComplex`
  `awayLocalizationFamilyMap`
  `koszulPowerStepLinearMap`
  `koszulPowerInverseSystem`
  `Functor.ofSequence`
  `K^•[n](f)`

Layer triage:
- `source-facing`: the realization of the extended alternating Čech complex of a finite family
  `f : Fin r → R` as a sequential colimit of the cohomologically reindexed powered Koszul stages,
  with the direct-system maps from the source proof
- `core/canonical`: the module-valued owner `extendedAlternatingCechComplex`, specialized here to
  `extendedAlternatingCechComplex f R`
  together with the powered Koszul owners `koszulPowerStepLinearMap` and
  `koszulPowerInverseSystem` from `15.92.15`
- `bridge/view`: the bounded cochain reindexing of the powered Koszul stages, and the source-facing
  direct-system maps on those stages used to compute the Čech colimit

Primitive data belongs to the owner construction from `15.31.1`: the canonical localization-family
map, its Čech conerve, and the degree-zero augmentation. The powered Koszul stages and their
diagonal transition map are already owned by `koszulPowerInverseSystem` and
`koszulPowerStepLinearMap`; this file only adds the source-facing cochain bridge needed for the
direct-limit computation.
-/

section

variable {R : Type u} [CommRing R]
variable {r : ℕ}
variable (f : Fin r → R)

private abbrev ringArrow : Arrow (ModuleCat R) :=
  Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap R f))

private noncomputable abbrev koszulPowerCochainStage (n : ℕ) :
    CochainComplex (ModuleCat R) ℕ :=
  (((K^•[n](f)).extend (embeddingUpIntLE (r : ℤ))).restriction embeddingUpNat)

private theorem koszulPowerCochainIndex_eq (p : ℕ) (hp : p ≤ r) :
    (embeddingUpIntLE (r : ℤ)).f (r - p) = (p : ℤ) := by
  dsimp [embeddingUpIntLE]
  omega

/-- Helper for Lemma 15.29.6: on the exterior-power basis indexed by an `(r-p)`-subset, the
source-faithful direct-system map multiplies by the product of the complementary generators. -/
private noncomputable def koszulPowerComplementStepLinearMap (p : ℕ) :
    ⋀[R]^(r - p) (Fin r → R) →ₗ[R] ⋀[R]^(r - p) (Fin r → R) :=
  let b := (Pi.basisFun R (Fin r)).exteriorPower (r - p)
  Module.Basis.constr b R fun s ↦ (Finset.prod s.1ᶜ f) • b s

/-- The degree-`p` component of the source-facing direct-system map on the cohomologically
reindexed powered Koszul stages. In basis coordinates, this is the complementary-product map from
the Stacks proof. -/
private noncomputable def koszulPowerCochainStepComponent (n p : ℕ) :
    (koszulPowerCochainStage f n).X p ⟶ (koszulPowerCochainStage f (n + 1)).X p :=
  if hp : p ≤ r then
    let hq := koszulPowerCochainIndex_eq p hp
    ((((K^•[n](f)).extend (embeddingUpIntLE (r : ℤ))).restrictionXIso embeddingUpNat rfl).hom ≫
        (((K^•[n](f)).extendXIso (embeddingUpIntLE (r : ℤ)) hq).hom ≫
          (ModuleCat.ofHom (koszulPowerComplementStepLinearMap (f := f) p) ≫
            (((K^•[n + 1](f)).extendXIso (embeddingUpIntLE (r : ℤ)) hq).inv ≫
              (((K^•[n + 1](f)).extend (embeddingUpIntLE (r : ℤ))).restrictionXIso
                embeddingUpNat rfl).inv))))
  else
    0

private theorem koszulPowerCochainStep_comm (n p : ℕ) :
    koszulPowerCochainStepComponent f n p ≫
        (koszulPowerCochainStage f (n + 1)).d p (p + 1) =
      (koszulPowerCochainStage f n).d p (p + 1) ≫
        koszulPowerCochainStepComponent f n (p + 1) := by
  -- Route correction: the source-facing direct-system map is the complementary-product basis map,
  -- not the owner inverse-system map on the diagonal linear operator. The remaining proof should
  -- compare both sides on `koszulExteriorBasis (r - p)` and use the textbook deletion formula for
  -- the Koszul differential.
  sorry

private theorem koszulComplement_card_eq (p : ℕ) (hp : p ≤ r) :
    p + (r - p) = Fintype.card (Fin r) := by
  simp
  omega

private noncomputable abbrev koszulExteriorBasis (p : ℕ) :
    Module.Basis (powersetCard (Fin r) p) R (⋀[R]^p (Fin r → R)) :=
  (Pi.basisFun R (Fin r)).exteriorPower p

private noncomputable def koszulPowerCochainStageXIso (n p : ℕ) (hp : p ≤ r) :
    (koszulPowerCochainStage f n).X p ≅ ModuleCat.of R (⋀[R]^(r - p) (Fin r → R)) :=
  (((K^•[n](f)).extend (embeddingUpIntLE (r : ℤ))).restrictionXIso embeddingUpNat rfl) ≪≫
    ((K^•[n](f)).extendXIso (embeddingUpIntLE (r : ℤ)) (koszulPowerCochainIndex_eq p hp))

private noncomputable def koszulPowerDegreeZeroLinearMap :
    ⋀[R]^r (Fin r → R) →ₗ[R] R :=
  (koszulExteriorBasis r).constr R (fun _ ↦ (1 : R))

private noncomputable def koszulComplementSubset (p : ℕ) (hp : p ≤ r)
    (s : powersetCard (Fin r) (r - p)) :
    powersetCard (Fin r) p :=
  powersetCard.compl (koszulComplement_card_eq p hp) s

private noncomputable abbrev cechConerveTerm (p : ℕ) : ModuleCat R :=
  (ringArrow f).cechConerve.obj (SimplexCategory.mk p)

private noncomputable def koszulCechBranchNumerator (n p : ℕ)
    (s : powersetCard (Fin r) p) (k : Fin p) : R :=
  Finset.prod (Finset.univ.erase k) fun l ↦ f (powersetCard.ofFinEmbEquiv.symm s l) ^ (n + 1)

private noncomputable def koszulCechBranchVector (n p : ℕ)
    (s : powersetCard (Fin r) p) (k : Fin p) :
    ∀ i : Fin r, Localization.Away (f i) :=
  fun i ↦
    dite (i = powersetCard.ofFinEmbEquiv.symm s k)
      (fun h ↦ h.rec <|
        LocalizedModule.mk (koszulCechBranchNumerator f n p s k)
          ⟨f (powersetCard.ofFinEmbEquiv.symm s k) ^ (n + 1), by
            refine ⟨n + 1, by simpa [h]⟩⟩)
      (fun _ ↦ 0)

private noncomputable abbrev cechConerveBranchHom (p : ℕ) (k : Fin (p + 1)) :
    ModuleCat.of R (∀ i : Fin r, Localization.Away (f i)) ⟶ cechConerveTerm f p :=
  show ModuleCat.of R (∀ i : Fin r, Localization.Away (f i)) ⟶
      widePushout (ModuleCat.of R R)
        (fun _ : Fin (p + 1) ↦ ModuleCat.of R (∀ i : Fin r, Localization.Away (f i)))
        (fun _ ↦ ModuleCat.ofHom (awayLocalizationFamilyMap R f)) from
    WidePushout.ι (fun _ : Fin (p + 1) ↦ ModuleCat.ofHom (awayLocalizationFamilyMap R f)) k

private noncomputable def koszulAlternatingBasisImage (n p : ℕ) (hp : p + 1 ≤ r)
    (s : powersetCard (Fin r) (r - (p + 1))) :
    cechConerveTerm f p :=
  let t := koszulComplementSubset (p + 1) hp s
  ∑ k : Fin (p + 1),
    (-1 : ℤ) ^ (k : ℕ) •
      (cechConerveBranchHom f p k).hom (koszulCechBranchVector f n (p + 1) t k)

private noncomputable def koszulAlternatingLinearMap (n p : ℕ) (hp : p + 1 ≤ r) :
    ⋀[R]^(r - (p + 1)) (Fin r → R) →ₗ[R] cechConerveTerm f p :=
  (koszulExteriorBasis (r - (p + 1))).constr R
    (koszulAlternatingBasisImage f n p hp)

private theorem extendedAlternatingCechComplex_X_zero :
    (extendedAlternatingCechComplex f R).X 0 = ModuleCat.of R R := by
  simp [extendedAlternatingCechComplex, alternatingCechComplexAugmentation,
    CochainComplex.fromSingle₀AsComplex]

private theorem extendedAlternatingCechComplex_X_succ (p : ℕ) :
    (extendedAlternatingCechComplex f R).X (p + 1) = cechConerveTerm f p := by
  change (extendedAlternatingCechComplex f R).X (p + 1) =
    (ringArrow f).cechConerve.obj (SimplexCategory.mk p)
  simp [extendedAlternatingCechComplex, alternatingCechComplexAugmentation,
    CochainComplex.fromSingle₀AsComplex]
  rfl

private noncomputable def koszulPowerToExtendedComponent (n p : ℕ) :
    (koszulPowerCochainStage f n).X p ⟶ (extendedAlternatingCechComplex f R).X p :=
  if hp : p ≤ r then
    match p with
    | 0 =>
        (koszulPowerCochainStageXIso f n 0 hp).hom ≫
          ModuleCat.ofHom koszulPowerDegreeZeroLinearMap ≫
            eqToHom (extendedAlternatingCechComplex_X_zero f).symm
    | q + 1 =>
        (koszulPowerCochainStageXIso f n (q + 1) hp).hom ≫
          ModuleCat.ofHom (koszulAlternatingLinearMap f n q hp) ≫
            eqToHom (extendedAlternatingCechComplex_X_succ f q).symm
  else
    0

private theorem koszulPowerToExtendedComponent_comm (n p : ℕ) :
    koszulPowerToExtendedComponent f n p ≫ (extendedAlternatingCechComplex f R).d p (p + 1) =
      (koszulPowerCochainStage f n).d p (p + 1) ≫ koszulPowerToExtendedComponent f n (p + 1) := by
  -- The degree-zero branch should reduce to the augmentation cocycle from `Lemma_15_29_1`, while
  -- the positive-degree branches should be checked on `koszulExteriorBasis` against the
  -- alternating coface formula in the Čech complex.
  sorry

private noncomputable abbrev koszulPowerToExtendedMap (n : ℕ) :
    koszulPowerCochainStage f n ⟶ extendedAlternatingCechComplex f R :=
  { f := koszulPowerToExtendedComponent f n
    comm' := fun p q hpq ↦ by
      subst hpq
      simpa using koszulPowerToExtendedComponent_comm f n p }

/- The source-facing direct-system map
`K(f₁^(n+1), ..., fᵣ^(n+1)) ⟶ K(f₁^(n+2), ..., fᵣ^(n+2))`
between the cohomologically reindexed powered Koszul stages. On degree `p`, this is the
complementary-product map from the Stacks proof. -/
private noncomputable abbrev koszulPowerCochainStep (n : ℕ) :
    koszulPowerCochainStage f n ⟶ koszulPowerCochainStage f (n + 1) :=
  { f := koszulPowerCochainStepComponent f n
    comm' := fun p q hpq ↦ by
      subst hpq
      simpa using koszulPowerCochainStep_comm f n p }

/-- Helper for Lemma 15.29.6: the degree-`p` comparison map from the powered Koszul stage to the
extended alternating Čech complex is natural in the stage index. -/
private theorem koszulPowerToExtended_naturality_component (n p : ℕ) :
    koszulPowerCochainStepComponent f n p ≫
        koszulPowerToExtendedComponent f (n + 1) p =
      koszulPowerToExtendedComponent f n p := by
  -- Proof comment: evaluate the source-faithful transition map and the comparison map on the same
  -- exterior basis generators, then identify the localization classes after one denominator shift.
  sorry

private theorem koszulPowerToExtended_naturality (n : ℕ) :
    koszulPowerCochainStep f n ≫ koszulPowerToExtendedMap f (n + 1) =
      koszulPowerToExtendedMap f n := by
  -- Proof comment: equality of cochain maps is degreewise, so reduce to the component identity
  -- proved on the source-faithful basis generators.
  ext p x
  exact congrArg (fun φ ↦ φ.hom x) <|
    koszulPowerToExtended_naturality_component (f := f) n p

/-- The sequential direct system of the cohomologically reindexed powered Koszul complexes
`K^•(f₁^(n+1), …, fᵣ^(n+1))`, with transition maps induced by the canonical diagonal step map on
the finite free module `Fin r → R`. This is the source-facing bridge object in Lemma `15.29.6`. -/
noncomputable def koszulPowerCochainSystem :
    ℕ ⥤ CochainComplex (ModuleCat R) ℕ :=
  Functor.ofSequence (koszulPowerCochainStep f)

-- Proof sketch: compute the degreewise colimit of `koszulPowerCochainSystem f`
-- direct-limit description of `Localization.Away (Finset.prod s.1 f)`. In the reindexed
-- cohomological grading, the differentials on the powered Koszul stages become the alternating
-- Čech coboundaries, so the colimit identifies with `extendedAlternatingCechComplex f`.
/-- The comparison cocone on the powered Koszul cochain system used to define the colimit map in
Lemma `15.29.6`. -/
private noncomputable abbrev koszulPowerCochainSystemCocone :
    Cocone (koszulPowerCochainSystem f) where
  pt := extendedAlternatingCechComplex f R
  ι := NatTrans.ofSequence
    (fun n ↦ koszulPowerToExtendedMap f n)
    (fun n ↦ by
      simpa [koszulPowerCochainSystem, Functor.ofSequence_map_homOfLE_succ] using
        koszulPowerToExtended_naturality f n)

/-- The comparison morphism from the colimit of the powered Koszul cochain system to the extended
alternating Čech complex. -/
private noncomputable abbrev colimit_koszulPowerCochainSystem_to_extendedAlternatingCechComplex :
    colimit (koszulPowerCochainSystem f) ⟶ extendedAlternatingCechComplex f R :=
  colimit.desc _ (koszulPowerCochainSystemCocone f)

/-- Helper for Lemma 15.29.6: each degree of the comparison from the colimit of the powered
Koszul system to the extended alternating Čech complex is an isomorphism. -/
private theorem colimit_koszulPowerCochainSystem_component_isIso (p : ℕ) :
    IsIso ((colimit_koszulPowerCochainSystem_to_extendedAlternatingCechComplex f).f p) := by
  -- Proof comment: evaluate the colimit in degree `p`, transport the powered Koszul term through
  -- the exterior-power basis indexed by complementary subsets, and compute each resulting scalar
  -- sequence as a principal-power localization.
  sorry

/-- The comparison from the colimit of the powered Koszul cochain system to the extended
alternating Čech complex is an isomorphism. -/
private theorem colimit_koszulPowerCochainSystem_to_extendedAlternatingCechComplex_isIso :
    IsIso (colimit_koszulPowerCochainSystem_to_extendedAlternatingCechComplex f) := by
  let hcomp : ∀ p : ℕ,
      IsIso ((colimit_koszulPowerCochainSystem_to_extendedAlternatingCechComplex f).f p) :=
    fun p ↦ colimit_koszulPowerCochainSystem_component_isIso (f := f) p
  letI : ∀ p : ℕ,
      IsIso ((colimit_koszulPowerCochainSystem_to_extendedAlternatingCechComplex f).f p) :=
    hcomp
  -- Proof comment: once each degreewise comparison is an isomorphism, the whole cochain map is
  -- an isomorphism by the standard componentwise criterion for homological complexes.
  exact HomologicalComplex.Hom.isIso_of_components
    (colimit_koszulPowerCochainSystem_to_extendedAlternatingCechComplex f)

/-- Lemma 15.29.6: the extended alternating Čech complex of a finite family `f : Fin r → R` is
canonically isomorphic to the colimit of the sequential cochain system of powered Koszul
complexes. -/
noncomputable def extendedAlternatingCechComplex_iso_colimit_koszulPowerCochainSystem
    :
    extendedAlternatingCechComplex f R ≅
      colimit (koszulPowerCochainSystem f) :=
  let _ := colimit_koszulPowerCochainSystem_to_extendedAlternatingCechComplex_isIso f
  (asIso (colimit_koszulPowerCochainSystem_to_extendedAlternatingCechComplex f)).symm

end
