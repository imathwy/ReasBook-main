import Mathlib
import Mathlib.CategoryTheory.Functor.OfSequence
import stacks_proof.stacks_project.Chap04.Example_4_22_6
import stacks_proof.stacks_project.Chap10.Lemma_10_51_2_Artin_Rees
import stacks_proof.stacks_project.Chap10.Lemma_10_51_3
import stacks_proof.stacks_project.Chap12.Definition_12_31_2
import stacks_proof.stacks_project.Chap15.Lemma_15_87_4
import stacks_proof.stacks_project.Chap15.Lemma_15_98_6_Koll_r_Kov_cs

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open SequentialInverseSystem
open SequentialProObjectMorphismRep

universe u v

section

variable {A : Type u} [CommRing A]

local notation "Mod" => ModuleCat A
local notation "SeqMod" => SequentialInverseSystem Mod

/- Domain-style sampling for Lemma 15.101.1:
- primary domain: quotient short complexes of module-valued short complexes, their left-homology
  towers, and the induced comparison on inverse limits;
- sampled owner declarations:
  `ShortComplex.leftHomology`,
  `ShortComplex.leftHomologyMap`,
  `ShortComplex.map`,
  `ShortComplex.mapNatTrans`,
  `ShortComplex.homMk`,
  `idealPowerModuleQuotient`,
  `Submodule.mkQ`,
  `AdicCompletion.transitionMap`,
  `SequentialProObjectMorphismRep.IsProIsomorphism`,
  `SequentialProObjectMorphismRep.toProObjectHom`,
  `CategoryTheory.inducedLimitMap`,
  `CategoryTheory.inducedLimitMap_isIso_of_isIso`,
  `SequentialInverseSystem.IsMittagLeffler`;
- best owner abstraction: the ambient short complex `S : ShortComplex (ModuleCat A)` is the
  canonical owner; its quotient stages are obtained by applying the chapter owner
  `idealPowerModuleQuotient` componentwise, and the tower comparison is controlled by a
  sequential representative `r : SequentialProObjectMorphismRep ...`, whose associated
  pro-object morphism `r.toProObjectHom` is the canonical owner-level comparison;
- primitive data: the short complex `S` and the stagewise comparison maps
  `S.leftHomology / I^(n+1) S.leftHomology ⟶ H_{n+1}` and
  `H_{n+c+1} ⟶ S.leftHomology / I^(n+1) S.leftHomology`;
- derived API: the owner-level quotient stages, their homology towers, the pro-object
  isomorphism, and the induced inverse-limit isomorphism, with representative-level witnesses kept
  internal to the existence statements.

Source/core/bridge triage:
- `source-facing`: the Artin-Rees comparison maps between the left homology of `S` and the
  homology of the quotient stages;
- `core/canonical`: `S.leftHomology`, `S.leftHomologyMap`,
  `SequentialProObjectMorphismRep ...`, `.toProObjectHom`, and the canonical inverse-limit
  comparison attached to an isomorphism in the sequential pro-category;
- `bridge/view`: the explicit representative-level witnesses for those pro-object comparisons. -/

namespace CategoryTheory.ShortComplex

variable {S : ShortComplex Mod}
variable {I : Ideal A}

/-- The endofunctor on `Mod_A` given by quotienting by `I^(n+1)`. -/
private abbrev idealPowerQuotientFunctor (I : Ideal A) (n : ℕ) : Mod ⥤ Mod where
  obj M := ModuleCat.of A (idealPowerModuleQuotient I M n)
  map f := ModuleCat.ofHom <| f.hom.reduceModIdeal (I ^ (n + 1))
  map_id M := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

private instance (I : Ideal A) (n : ℕ) :
    (idealPowerQuotientFunctor I n).PreservesZeroMorphisms where
  map_zero X Y := by
    ext x
    rfl

/-- The natural transition
`(-) / I^(n+2) (-) ⟶ (-) / I^(n+1) (-)` on `Mod_A`. -/
private abbrev idealPowerQuotientTransitionNatTrans
    (I : Ideal A) (n : ℕ) :
    idealPowerQuotientFunctor I (n + 1) ⟶ idealPowerQuotientFunctor I n where
  app M := ModuleCat.ofHom (AdicCompletion.transitionMap I M (Nat.le_succ (n + 1)))
  naturality {X} {Y} f := by
    ext x
    rfl

/-- The quotient short complex `S / I^(n+1) S`. -/
private abbrev idealPowerQuotientStageComplex
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    ShortComplex Mod :=
  S.map (idealPowerQuotientFunctor I n)

private instance idealPowerQuotientStageComplex_hasLeftHomology
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    (S.idealPowerQuotientStageComplex I n).HasLeftHomology := by
  dsimp [idealPowerQuotientStageComplex]
  infer_instance

/-- The homology module `H_{n+1}` of the quotient complex modulo `I^(n+1)`. -/
abbrev idealPowerHomologyStage
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    Mod :=
  (S.idealPowerQuotientStageComplex I n).leftHomology

-- Proof sketch: the quotient maps `K → K / I^(n+1) K`, `L → L / I^(n+1) L`, and
-- `M → M / I^(n+1) M` commute with the differentials of `S` by construction.
/-- The natural quotient map `𝟭 ⟶ (-) / I^(n+1) (-)` on `Mod_A`. -/
private abbrev toIdealPowerQuotientNatTrans
    (I : Ideal A) (n : ℕ) :
    𝟭 Mod ⟶ idealPowerQuotientFunctor I n where
  app M := ModuleCat.ofHom (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule A M)))
  naturality {X} {Y} f := by
    ext x
    rfl

/-- The canonical map `H ⟶ H_{n+1}` induced by quotienting the original complex modulo
`I^(n+1)`. -/
abbrev leftHomologyToIdealPowerStage
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    S.leftHomology ⟶ S.idealPowerHomologyStage I n :=
  leftHomologyMap <| S.mapNatTrans (toIdealPowerQuotientNatTrans I n)

/-- Helper for Lemma 15.101.1: every element of `M / I^(n+1) M` is annihilated by each scalar in
`I^(n+1)`. -/
private theorem idealPowerModuleQuotient_smul_eq_zero_of_mem_pow
    {M : Type v} [AddCommGroup M] [Module A M] {n : ℕ} {r : A}
    (hr : r ∈ I ^ (n + 1)) (x : idealPowerModuleQuotient I M n) :
    r • x = 0 := by
  obtain ⟨m, rfl⟩ :=
    (Submodule.mkQ_surjective (I ^ (n + 1) • (⊤ : Submodule A M))) x
  -- Reduction modulo `I^(n+1)` kills every `I^(n+1)`-multiple upstairs.
  change Submodule.Quotient.mk (r • m) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul hr (by simp)

-- Route correction: the descent `H → H_n` becomes routine once we first expose that
-- `I^(n+1)` annihilates the quotient-stage homology.
/-- Helper for Lemma 15.101.1: every element of the quotient-stage left homology `H_{n+1}` is
annihilated by each scalar in `I^(n+1)`. -/
private theorem idealPowerHomologyStage_smul_eq_zero_of_mem_pow
    (S : ShortComplex Mod) (I : Ideal A) {n : ℕ} {r : A}
    (hr : r ∈ I ^ (n + 1)) (y : S.idealPowerHomologyStage I n) :
    r • y = 0 := by
  let T : ShortComplex Mod := S.idealPowerQuotientStageComplex I n
  have hsurj : Function.Surjective T.leftHomologyπ.hom :=
    (ModuleCat.epi_iff_surjective T.leftHomologyπ).1 inferInstance
  obtain ⟨z, rfl⟩ := hsurj y
  rw [← T.leftHomologyπ.hom.map_smul]
  -- We test equality in the cycle object after the injective cycle inclusion.
  have hinj : Function.Injective T.iCycles.hom :=
    (ModuleCat.mono_iff_injective T.iCycles).1 inferInstance
  have hz : r • z = 0 := by
    apply hinj
    rw [LinearMap.map_smul, LinearMap.map_zero]
    simpa [T] using
      idealPowerModuleQuotient_smul_eq_zero_of_mem_pow (I := I) (n := n) hr (T.iCycles.hom z)
  simpa [hz]

-- Proof sketch: the map on homology induced by reduction modulo `I^(n+1)` kills
-- `I^(n+1) H`, so it descends canonically to the quotient `H / I^(n+1) H`.
private theorem leftHomologyToIdealPowerStage_condition
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    I ^ (n + 1) • (⊤ : Submodule A S.leftHomology) ≤
      LinearMap.ker (S.leftHomologyToIdealPowerStage I n).hom := by
  -- The target stage is annihilated by `I^(n+1)`, so the induced map kills the whole smul
  -- submodule `I^(n+1) • H`.
  refine Submodule.smul_le.mpr ?_
  intro r hr x hx
  change (S.leftHomologyToIdealPowerStage I n).hom (r • x) = 0
  rw [LinearMap.map_smul]
  simpa using
    idealPowerHomologyStage_smul_eq_zero_of_mem_pow
      (S := S) (I := I) (n := n) hr ((S.leftHomologyToIdealPowerStage I n).hom x)

/-- The canonical comparison map `H / I^(n+1) H ⟶ H_{n+1}`. -/
abbrev leftHomologyQuotientComparison
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    ModuleCat.of A (idealPowerModuleQuotient I S.leftHomology n) ⟶
      S.idealPowerHomologyStage I n :=
  ModuleCat.ofHom <|
    Submodule.liftQ
      (I ^ (n + 1) • (⊤ : Submodule A S.leftHomology))
      (S.leftHomologyToIdealPowerStage I n).hom
      (leftHomologyToIdealPowerStage_condition S I n)

-- Proof sketch: `leftHomologyQuotientComparison` is defined by descending
-- `leftHomologyToIdealPowerStage` along the quotient map `H ↠ H / I^(n+1) H`.
/-- Helper for Lemma 15.101.1: precomposing the quotient comparison with the canonical quotient map
recovers the original map `H ⟶ H_{n+1}`. -/
private theorem leftHomologyQuotientComparison_comp_mkQ
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    ModuleCat.ofHom
        (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule A S.leftHomology))) ≫
      S.leftHomologyQuotientComparison I n =
        S.leftHomologyToIdealPowerStage I n := by
  ext x
  -- The defining property of `liftQ` identifies the descended map on representatives.
  simp only [leftHomologyQuotientComparison, leftHomologyToIdealPowerStage]
  rw [← LinearMap.comp_apply, Submodule.liftQ_mkQ]
  rfl

-- Route correction: we model `H / I^(n+1) H` through the cycle quotient
-- `Z = ker(β) ↠ H` before attempting the Artin-Rees descent on lifted cycles.
/-- Helper for Lemma 15.101.1: the preimage of `I^(n+1) H` under the quotient map
`Z = ker(β) ↠ H` is exactly `B_Z + I^(n+1) Z`, where `B_Z = im(α)` viewed inside `Z`. -/
private theorem leftHomologyQuotientStage_preimage_pow_eq_boundary_sup_pow
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    Submodule.comap S.leftHomologyπ.hom (I ^ (n + 1) • (⊤ : Submodule A S.leftHomology)) =
      LinearMap.range S.moduleCatToCycles ⊔
        I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom)) := by
  have hmap :
      Submodule.map S.leftHomologyπ.hom
          (I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom))) =
        I ^ (n + 1) • (⊤ : Submodule A S.leftHomology) := by
    rw [Submodule.map_smul'', Submodule.map_top]
    -- The quotient map on cycles is surjective, hence its range is all of `H`.
    ext x
    constructor
    · intro _
      simp
    · intro _
      obtain ⟨z, rfl⟩ :=
        (ModuleCat.epi_iff_surjective S.leftHomologyπ).1 inferInstance x
      exact ⟨z, rfl⟩
  -- After rewriting `π` as the quotient map by `B_Z`, this is the standard `comap_map_mkQ`
  -- identity from the quotient-submodule correspondence.
  change
    Submodule.comap
      (Submodule.mkQ (LinearMap.range S.moduleCatToCycles))
      (I ^ (n + 1) • (⊤ : Submodule A S.leftHomology)) =
      LinearMap.range S.moduleCatToCycles ⊔
        I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom))
  rw [← hmap, Submodule.comap_map_mkQ]

/-- Helper for Lemma 15.101.1: under the quotient map `Z = ker(β) ↠ H`, the denominator
`B_Z + I^(n+1) Z` maps onto `I^(n+1) H`. -/
private theorem leftHomologyQuotientStage_map_boundary_sup_pow_eq_pow
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    Submodule.map S.leftHomologyπ.hom
      (LinearMap.range S.moduleCatToCycles ⊔
        I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom))) =
      I ^ (n + 1) • (⊤ : Submodule A S.leftHomology) := by
  have hmap :
      Submodule.map S.leftHomologyπ.hom
          (I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom))) =
        I ^ (n + 1) • (⊤ : Submodule A S.leftHomology) := by
    rw [Submodule.map_smul'', Submodule.map_top]
    -- Surjectivity again identifies the range of the quotient map with the whole homology.
    ext x
    constructor
    · intro _
      simp
    · intro _
      obtain ⟨z, rfl⟩ :=
        (ModuleCat.epi_iff_surjective S.leftHomologyπ).1 inferInstance x
      exact ⟨z, rfl⟩
  -- The boundary term is killed by the quotient map, and the `I^(n+1)`-term maps onto
  -- `I^(n+1) H`.
  change
    Submodule.map
      (Submodule.mkQ (LinearMap.range S.moduleCatToCycles))
      (LinearMap.range S.moduleCatToCycles ⊔
        I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom))) =
      I ^ (n + 1) • (⊤ : Submodule A S.leftHomology)
  rw [Submodule.map_sup]
  simp [hmap]

-- Route correction: the quotient-stage target is now modeled explicitly as
-- `Z / (B_Z ⊔ I^(n+1) Z)` before any shifted Artin-Rees lifting is attempted.
/-- Helper for Lemma 15.101.1: the quotient `H / I^(n+1) H` is canonically the quotient of
cycles `Z = ker(β)` by the denominator `B_Z + I^(n+1) Z`, where `B_Z = im(α)` inside `Z`. -/
private theorem leftHomologyQuotientStage_iso_cycles_boundary_pow_quotient
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    ((LinearMap.ker S.g.hom) ⧸
        (LinearMap.range S.moduleCatToCycles ⊔
          I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom)))) ≃ₗ[A]
      idealPowerModuleQuotient I S.leftHomology n := by
  let Z := LinearMap.ker S.g.hom
  let B : Submodule A Z := LinearMap.range S.moduleCatToCycles
  let P : Submodule A Z := I ^ (n + 1) • (⊤ : Submodule A Z)
  let Q : Submodule A S.leftHomology := I ^ (n + 1) • (⊤ : Submodule A S.leftHomology)
  let D : Submodule A Z := B ⊔ P
  have hpreimage : Submodule.comap S.leftHomologyπ.hom Q = D := by
    simpa [Z, B, P, Q, D] using
      leftHomologyQuotientStage_preimage_pow_eq_boundary_sup_pow (S := S) (I := I) n
  have hkillB : B ≤ D := by
    intro z hz
    exact show z ∈ D from le_sup_left hz
  let fromHomology : S.leftHomology →ₗ[A] Z ⧸ D := by
    change (Z ⧸ B) →ₗ[A] Z ⧸ D
    exact Submodule.liftQ B (Submodule.mkQ D) hkillB
  -- The quotient map on cycles followed by the quotient by `D` is the defining map on `Z / B`.
  have hfromHomology_comp :
      fromHomology.comp S.leftHomologyπ.hom = Submodule.mkQ D := by
    change
      (Submodule.liftQ B (Submodule.mkQ D) hkillB).comp (Submodule.mkQ B) =
        Submodule.mkQ D
    simpa using
      (Submodule.liftQ_mkQ (p := B) (f := Submodule.mkQ D) (h := hkillB))
  have hmapToPow : D ≤ Submodule.comap S.leftHomologyπ.hom Q := by
    rw [hpreimage]
  let toStage : (Z ⧸ D) →ₗ[A] idealPowerModuleQuotient I S.leftHomology n :=
    Submodule.mapQ D Q S.leftHomologyπ.hom hmapToPow
  have hfromHomology_ker : Q ≤ LinearMap.ker fromHomology := by
    intro y hy
    obtain ⟨z, rfl⟩ :=
      (ModuleCat.epi_iff_surjective S.leftHomologyπ).1 inferInstance y
    -- Membership in the preimage denominator means the class already vanishes in `Z / D`.
    change fromHomology (S.leftHomologyπ.hom z) = 0
    rw [← LinearMap.comp_apply, hfromHomology_comp]
    exact (Submodule.Quotient.mk_eq_zero D).2 <| by
      have hz : z ∈ Submodule.comap S.leftHomologyπ.hom Q := by
        simpa using hy
      simpa [hpreimage] using hz
  let fromStage : idealPowerModuleQuotient I S.leftHomology n →ₗ[A] Z ⧸ D :=
    Submodule.liftQ Q fromHomology hfromHomology_ker
  refine
    { toFun := toStage
      invFun := fromStage
      map_add' := toStage.map_add
      map_smul' := toStage.map_smul
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective D x
    -- Both quotient descents compute on the representative `z`.
    change
      fromStage
          ((Submodule.mapQ D Q S.leftHomologyπ.hom hmapToPow)
            (Submodule.Quotient.mk z)) =
        (Submodule.Quotient.mk z : Z ⧸ D)
    rw [show
        (Submodule.mapQ D Q S.leftHomologyπ.hom hmapToPow)
            (Submodule.Quotient.mk z) =
          (Submodule.Quotient.mk (S.leftHomologyπ.hom z) :
            idealPowerModuleQuotient I S.leftHomology n) by
          simp [Submodule.mapQ_apply]]
    rw [Submodule.liftQ_apply, ← LinearMap.comp_apply, hfromHomology_comp]
    rfl
  · intro x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective Q x
    obtain ⟨z, rfl⟩ :=
      (ModuleCat.epi_iff_surjective S.leftHomologyπ).1 inferInstance y
    -- Surjectivity of `Z ↠ H` reduces the right inverse to the same representative computation.
    change
      toStage
          (fromStage
            (Submodule.Quotient.mk (S.leftHomologyπ.hom z))) =
        (Submodule.Quotient.mk (S.leftHomologyπ.hom z) :
          idealPowerModuleQuotient I S.leftHomology n)
    rw [Submodule.liftQ_apply, ← LinearMap.comp_apply, hfromHomology_comp]
    simp [toStage, Submodule.mapQ_apply]

/-- Helper for Lemma 15.101.1: two cycle representatives define the same class in the quotient
model `Z / (B_Z ⊔ I^(n+1) Z)` once their difference lies in the denominator. -/
private theorem ambient_precycle_reduction_eq_mod_boundary_sup_pow
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ)
    {z₁ z₂ : LinearMap.ker S.g.hom}
    (hsub :
      z₁ - z₂ ∈
        LinearMap.range S.moduleCatToCycles ⊔
          I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom))) :
    (Submodule.Quotient.mk z₁ :
        ((LinearMap.ker S.g.hom) ⧸
          (LinearMap.range S.moduleCatToCycles ⊔
            I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom))))) =
      Submodule.Quotient.mk z₂ := by
  -- Equality in a submodule quotient is exactly membership of the difference in the denominator.
  exact (Submodule.Quotient.eq _).2 hsub

/-- The inverse system `(H_{n+1})_n` attached to the quotient complexes modulo powers of `I`. -/
abbrev idealPowerHomologyStep
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    S.idealPowerHomologyStage I (n + 1) ⟶ S.idealPowerHomologyStage I n :=
  leftHomologyMap <| S.mapNatTrans (idealPowerQuotientTransitionNatTrans I n)

/-- The inverse system `(H / I^(n+2) H)_n ⟶ (H / I^(n+1) H)_n` on the ambient left homology
module `H = S.leftHomology`. -/
abbrev leftHomologyQuotientStage
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    Mod :=
  idealPowerQuotientStage I S.leftHomology n

/-- The inverse system `(H / I^(n+2) H)_n ⟶ (H / I^(n+1) H)_n` on the ambient left homology
module `H = S.leftHomology`. -/
abbrev leftHomologyQuotientStep
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    S.leftHomologyQuotientStage I (n + 1) ⟶
      S.leftHomologyQuotientStage I n :=
  idealPowerQuotientStep I S.leftHomology n

/-- Helper for Lemma 15.101.1: every transition map between ideal-power quotients is surjective.
-/
private theorem idealPowerTransition_surjective
    {M : Type v} [AddCommGroup M] [Module A M] {i j : ℕ} (hij : i ≤ j) :
    Function.Surjective (AdicCompletion.transitionMap I M hij) := by
  intro x
  obtain ⟨m, rfl⟩ :=
    (Submodule.mkQ_surjective (I ^ (i + 1) • (⊤ : Submodule A M))) x
  -- The higher quotient stage represented by the same element maps to the prescribed lower-stage
  -- class.
  refine ⟨Submodule.Quotient.mk m, rfl⟩

/-- The inverse system `(H_{n+1})_n` attached to the quotient complexes modulo powers of `I`. -/
abbrev idealPowerHomologyTower
    (S : ShortComplex Mod) (I : Ideal A) :
    SeqMod :=
  Functor.ofOpSequence (S.idealPowerHomologyStep I)

/-- The inverse system `(H / I^(n+1) H)_n` attached to the left homology module `H`. -/
abbrev leftHomologyQuotientTower
    (S : ShortComplex Mod) (I : Ideal A) :
    SeqMod :=
  idealPowerQuotientInverseSystem I S.leftHomology

/-- A shifted tower comparison `(H_{n+c+1})_n ⟶ (H / I^(n+1) H)_n`. -/
abbrev idealPowerHomologyShiftComparison
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ) :
    Type _ :=
  NatTrans
    (SequentialInverseSystem.shift (S.idealPowerHomologyTower I) c)
    (S.leftHomologyQuotientTower I)

/-- Helper for Lemma 15.101.1: if the first map in a composite is epi, then the image of the
composite agrees with the image of the second map. -/
private theorem imageSubobject_comp_eq_of_epi
    {X Y Z : Mod} (f : X ⟶ Y) [Epi f] (g : Y ⟶ Z) :
    imageSubobject (f ≫ g) = imageSubobject g := by
  calc
    imageSubobject (f ≫ g) = imageSubobject ((imageSubobject f).arrow ≫ g) := by
      rw [CategoryTheory.Limits.imageSubobject_comp_eq_imageSubobject_restriction f g]
    _ = imageSubobject (((⊤ : Subobject Y)).arrow ≫ g) := by
      simpa using congrArg (fun S : Subobject Y ↦ imageSubobject (S.arrow ≫ g))
        (Limits.imageSubobject_eq_top_of_epi f)
    _ = imageSubobject g := by
      simpa using
        (CategoryTheory.Limits.imageSubobject_iso_comp ((⊤ : Subobject Y).arrow) g)

/-- The image of the shifted transition map `H_{n+c+1} ⟶ H_{n+1}` agrees with the image of the
canonical map `H ⟶ H_{n+1}`. -/
def idealPowerHomologyImageStabilizes
    (S : ShortComplex Mod) (I : Ideal A) (c n : ℕ) : Prop :=
  imageSubobject ((S.idealPowerHomologyTower I).transitionMap (Nat.le_add_right n c)) =
    imageSubobject (leftHomologyToIdealPowerStage S I n)

/-- The kernel of `H / I^(n+1) H ⟶ H_{n+1}` is annihilated by `I^c`. -/
def leftHomologyComparisonKernelAnnihilated
    (S : ShortComplex Mod) (I : Ideal A) (c n : ℕ) : Prop :=
  I ^ c •
      (⊤ :
        Submodule A
          ↥(LinearMap.ker (leftHomologyQuotientComparison S I n).hom)) =
    (⊥ :
      Submodule A
        ↥(LinearMap.ker (leftHomologyQuotientComparison S I n).hom))

/-- The cokernel of `H / I^(n+1) H ⟶ H_{n+1}` is annihilated by `I^c`. -/
def leftHomologyComparisonCokernelAnnihilated
    (S : ShortComplex Mod) (I : Ideal A) (c n : ℕ) : Prop :=
  I ^ c •
      (⊤ :
        Submodule A
          (S.idealPowerHomologyStage I n ⧸
            LinearMap.range (leftHomologyQuotientComparison S I n).hom)) =
    (⊥ :
      Submodule A
        (S.idealPowerHomologyStage I n ⧸
          LinearMap.range (leftHomologyQuotientComparison S I n).hom))

/-- The shifted comparison `H_{n+c+1} ⟶ H / I^(n+1) H` agrees on `I^c H_{n+c+1}` with reduction
modulo `I^(n+1)` after postcomposing with the canonical map to
`H_{n+c+1} / I^(n+1) H_{n+c+1}`. -/
def idealPowerHomologyPowCompatibility
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (comparison : S.idealPowerHomologyShiftComparison I c)
    (n : ℕ) : Prop :=
  let Hstage := idealPowerHomologyStage S I (c + n)
  let comparisonMap :
      S.idealPowerHomologyStage I (c + n) ⟶ S.leftHomologyQuotientStage I n :=
    comparison.app (Opposite.op n)
  ((((ModuleCat.ofHom <|
        (S.leftHomologyToIdealPowerStage I (c + n)).hom.reduceModIdeal (I ^ (n + 1))) :
        S.leftHomologyQuotientStage I n ⟶
          ModuleCat.of A (idealPowerModuleQuotient I Hstage n)).hom) ∘ₗ
      comparisonMap.hom ∘ₗ
      Submodule.subtype (I ^ c • (⊤ : Submodule A Hstage))) =
    (((ModuleCat.ofHom <|
        (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule A Hstage))) :
        ModuleCat.of A Hstage ⟶
          ModuleCat.of A (idealPowerModuleQuotient I Hstage n)).hom) ∘ₗ
      Submodule.subtype (I ^ c • (⊤ : Submodule A Hstage)))

/-- Helper for Lemma 15.101.1: every `I^c`-multiple in `H / I^(n+1) H` already comes from the
`(n + c)`th quotient stage by the canonical transition map. -/
private theorem idealPowerQuotient_pow_le_transition_range
    (S : ShortComplex Mod) (I : Ideal A) (n c : ℕ) :
    I ^ c • (⊤ : Submodule A (S.leftHomologyQuotientStage I n)) ≤
      LinearMap.range
        (((S.leftHomologyQuotientTower I).transitionMap (Nat.le_add_right n c)).hom) := by
  -- The quotient-stage transition maps are surjective, so their ranges are all of the target.
  have hsurj :
      Function.Surjective
        (((S.leftHomologyQuotientTower I).transitionMap (Nat.le_add_right n c)).hom) := by
    simpa [leftHomologyQuotientTower, idealPowerQuotientInverseSystem] using
      idealPowerTransition_surjective (I := I) (M := S.leftHomology)
        (Nat.le_add_right n c)
  rw [LinearMap.range_eq_top.2 hsurj]
  exact le_top

/-- Helper for Lemma 15.101.1: if `I^c`-multiples in a module land in the range of `f`, then the
quotient by `range(f)` is annihilated by `I^c`. -/
private theorem quotientByRange_pow_smul_top_eq_bot
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) (c : ℕ)
    (hpow : I ^ c • (⊤ : Submodule A N) ≤ LinearMap.range f) :
    I ^ c • (⊤ : Submodule A (N ⧸ LinearMap.range f)) = ⊥ := by
  apply le_antisymm
  · -- It suffices to show every `I^c`-multiple in the quotient is represented by an element of
    -- `range(f)`, hence vanishes.
    rw [Submodule.smul_le]
    intro r hr x hx
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range f) x
    change Submodule.Quotient.mk (r • y) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hpow <| Submodule.smul_mem_smul hr (by simp)
  · exact bot_le

section Comparison

variable (S : ShortComplex Mod) (I : Ideal A)

-- Proof sketch: the canonical map `H ⟶ H_{n+2}` factors through `H_{n+1}` because the quotient
-- maps of short complexes are compatible with the transition maps modulo powers of `I`.
/- Auxiliary tower-compatibility statement for Lemma 15.101.1: the canonical maps
`H ⟶ \cdots \to H_3 \to H_2 \to H_1`. The Lean indexing starts at `n = 0`, so stage `n`
corresponds to the textbook module `H_{n+1}`. -/
private theorem leftHomologyToIdealPowerStage_comp_step (n : ℕ) :
    leftHomologyToIdealPowerStage S I (n + 1) ≫
        SequentialInverseSystem.stepMap (S.idealPowerHomologyTower I) n =
      S.leftHomologyToIdealPowerStage I n := by
  -- The componentwise quotient maps commute strictly with the transition
  -- `(-) / I^(n+2) (-) ⟶ (-) / I^(n+1) (-)`, so the induced maps on left homology compose.
  change
    leftHomologyMap
        (S.mapNatTrans (toIdealPowerQuotientNatTrans I (n + 1))) ≫
      leftHomologyMap
        (S.mapNatTrans (idealPowerQuotientTransitionNatTrans I n)) =
      leftHomologyMap (S.mapNatTrans (toIdealPowerQuotientNatTrans I n))
  rw [← ShortComplex.leftHomologyMap_comp]
  congr 1
  apply ShortComplex.hom_ext <;> ext x <;> rfl

/-- Helper for Lemma 15.101.1: transition maps in any sequential inverse system compose in the
expected order after refining the index. -/
private theorem transitionMap_comp
    (F : SeqMod) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    F.transitionMap (hij.trans hjk) = F.transitionMap hjk ≫ F.transitionMap hij := by
  -- This is just the functoriality of the inverse-system functor on the unique order morphisms.
  simpa [SequentialInverseSystem.transitionMap] using
    (F.map_comp ((homOfLE hjk).op) ((homOfLE hij).op))

section

variable [IsNoetherianRing A]
variable [Module.Finite A S.X₁] [Module.Finite A S.X₂] [Module.Finite A S.X₃]

/-- Arithmetic helper for the common refinement in Lemma 15.101.1. -/
private theorem shiftComparison_le (n c : ℕ) :
    n ≤ c + (c + n) := by
  exact (Nat.le_add_left n c).trans (Nat.le_add_left (c + n) c)

/-- Helper for Lemma 15.101.1: after a fixed Artin-Rees shift, every quotient-stage cycle can be
replaced by an actual ambient cycle modulo a shallower ideal power. -/
private theorem exists_cycle_preimage_artin_rees_shift
    (S : ShortComplex Mod) (I : Ideal A) [Module.Finite A S.X₃] :
    ∃ c : ℕ, ∀ n : ℕ,
      Submodule.comap S.g.hom (I ^ (c + n + 1) • (⊤ : Submodule A S.X₃)) ≤
        LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂) := by
  -- Route correction: we first freeze the owner-level Artin-Rees equality for the exact sequence
  -- `0 → ker(S.g) → S.X₂ → S.X₃`, then bound the deeper preimage term by `⊤`.
  obtain ⟨c, hpreimage, _⟩ :=
    Ideal.exists_artin_rees_constant_of_exact I
      (LinearMap.exact_subtype_ker_map S.g.hom)
  refine ⟨c, ?_⟩
  intro n
  calc
    Submodule.comap S.g.hom (I ^ (c + n + 1) • (⊤ : Submodule A S.X₃)) =
        LinearMap.ker S.g.hom ⊔
          I ^ (n + 1) • Submodule.comap S.g.hom (I ^ c • (⊤ : Submodule A S.X₃)) := by
      simpa [Nat.add_assoc, show c + n + 1 - c = n + 1 by omega] using
        hpreimage (c + n + 1) (Nat.le_add_right c (n + 1))
    _ ≤ LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂) := by
      exact sup_le_sup_left (smul_mono_right _ le_top) _

/-- Helper for Lemma 15.101.1: after a fixed Artin-Rees shift, every deep ambient boundary inside
`ker(S.g)` already comes from an `I^(n+1)`-multiple upstairs in `S.X₁`. -/
private theorem exists_boundary_artin_rees_shift
    (S : ShortComplex Mod) (I : Ideal A) [Module.Finite A S.X₂] :
    ∃ c : ℕ, ∀ n : ℕ,
      LinearMap.range S.moduleCatToCycles ⊓
          I ^ (c + n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom)) ≤
        Submodule.map S.moduleCatToCycles (I ^ (n + 1) • (⊤ : Submodule A S.X₁)) := by
  -- We convert the exact preimage statement for `S.moduleCatToCycles : S.X₁ → ker(S.g)` into the
  -- corresponding owner Artin-Rees range containment.
  let _ : Module.Finite A (LinearMap.ker S.g.hom) := by
    infer_instance
  obtain ⟨c, hpreimage⟩ := Ideal.exists_exact_preimage_pow_smul_eq I S.moduleCatToCycles
  have hbound : S.moduleCatToCycles.IsArtinReesBound I c :=
    LinearMap.isArtinReesBound_of_preimage_pow_smul_eq (I := I) hpreimage
  refine ⟨c, ?_⟩
  intro n
  simpa [Nat.add_assoc, show c + n + 1 - c = n + 1 by omega] using
    hbound (c + n + 1) (Nat.le_add_right c (n + 1))

/-- Helper for Lemma 15.101.1: the source proof uses three separate Artin-Rees buffers, one each
for reducing precycles to cycles, pushing deep cycle errors into `I^(n+1) ker(S.g)`, and
descending deep boundaries to `I^(n+1)` upstairs. -/
private theorem exists_buffered_artin_rees_data_for_shifted_comparison
    (S : ShortComplex Mod) (I : Ideal A)
    [Module.Finite A S.X₂] [Module.Finite A S.X₃] :
    ∃ cZ cK cB : ℕ,
      (∀ n : ℕ,
        Submodule.comap S.g.hom (I ^ (cZ + n + 1) • (⊤ : Submodule A S.X₃)) ≤
          LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂)) ∧
      (∀ n : ℕ,
        Submodule.comap (LinearMap.ker S.g.hom).subtype
          (I ^ (cK + n + 1) • (⊤ : Submodule A S.X₂)) ≤
            I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom))) ∧
      (∀ n : ℕ,
        LinearMap.range S.moduleCatToCycles ⊓
            I ^ (cB + n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom)) ≤
          Submodule.map S.moduleCatToCycles (I ^ (n + 1) • (⊤ : Submodule A S.X₁))) := by
  -- Route correction: we keep the three Artin-Rees bounds separate so the source proof's spare
  -- depth survives until the stage-homology descent is defined.
  rcases exists_cycle_preimage_artin_rees_shift S I with ⟨cZ, hcycles⟩
  rcases exists_cycle_subtype_artin_rees_shift (S := S) (I := I) with ⟨cK, hcycleSubtype⟩
  rcases exists_boundary_artin_rees_shift S I with ⟨cB, hboundaries⟩
  exact ⟨cZ, cK, cB, hcycles, hcycleSubtype, hboundaries⟩

/-- Helper for Lemma 15.101.1: one positive Artin-Rees constant simultaneously controls the
cycle-lifting, deep cycle intersection, and boundary-descent steps in the quotient-cycle model of
`H / I^(n+1) H`. -/
private theorem exists_artin_rees_constant_for_quotient_cycles_and_boundaries
    (S : ShortComplex Mod) (I : Ideal A)
    [Module.Finite A S.X₂] [Module.Finite A S.X₃] :
    ∃ c : ℕ, 0 < c ∧
      (∀ n : ℕ,
        Submodule.comap S.g.hom (I ^ (c + n + 1) • (⊤ : Submodule A S.X₃)) ≤
          LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂)) ∧
      (∀ n : ℕ,
        Submodule.comap (LinearMap.ker S.g.hom).subtype
            (I ^ (c + n + 1) • (⊤ : Submodule A S.X₂)) ≤
          I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom))) ∧
      (∀ n : ℕ,
        LinearMap.range S.moduleCatToCycles ⊓
            I ^ (c + n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom)) ≤
          Submodule.map S.moduleCatToCycles (I ^ (n + 1) • (⊤ : Submodule A S.X₁))) := by
  -- Route correction: the owner-level Artin-Rees bounds are already stable, so this wrapper only
  -- synchronizes them to a single positive shift and weakens the deeper powers to `n + 1`.
  rcases exists_buffered_artin_rees_data_for_shifted_comparison (S := S) (I := I) with
    ⟨cZ, cK, cB, hcycles, hcycleSubtype, hboundaries⟩
  refine ⟨cZ + cK + cB + 1, Nat.succ_pos _, ?_, ?_, ?_⟩
  · intro n
    have hshift :
        Submodule.comap S.g.hom (I ^ (cZ + cK + cB + n + 2) • (⊤ : Submodule A S.X₃)) ≤
          LinearMap.ker S.g.hom ⊔
            I ^ (cK + cB + n + 2) • (⊤ : Submodule A S.X₂) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcycles (cK + cB + n + 1)
    have hpow :
        I ^ (cK + cB + n + 2) • (⊤ : Submodule A S.X₂) ≤
          I ^ (n + 1) • (⊤ : Submodule A S.X₂) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Submodule.pow_smul_top_le I S.X₂ (Nat.le_add_left (n + 1) (cK + cB + 1)))
    exact hshift.trans <| sup_le_sup_left hpow _
  · intro n
    have hshift :
        Submodule.comap (LinearMap.ker S.g.hom).subtype
            (I ^ (cZ + cK + cB + n + 2) • (⊤ : Submodule A S.X₂)) ≤
          I ^ (cZ + cB + n + 2) • (⊤ : Submodule A (LinearMap.ker S.g.hom)) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        hcycleSubtype (cZ + cB + n + 1)
    have hpow :
        I ^ (cZ + cB + n + 2) • (⊤ : Submodule A (LinearMap.ker S.g.hom)) ≤
          I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom)) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Submodule.pow_smul_top_le I (LinearMap.ker S.g.hom)
          (Nat.le_add_left (n + 1) (cZ + cB + 1)))
    exact hshift.trans hpow
  · intro n
    have hshift :
        LinearMap.range S.moduleCatToCycles ⊓
            I ^ (cZ + cK + cB + n + 2) • (⊤ : Submodule A (LinearMap.ker S.g.hom)) ≤
          Submodule.map S.moduleCatToCycles
            (I ^ (cZ + cK + n + 2) • (⊤ : Submodule A S.X₁)) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        hboundaries (cZ + cK + n + 1)
    have hpow :
        I ^ (cZ + cK + n + 2) • (⊤ : Submodule A S.X₁) ≤
          I ^ (n + 1) • (⊤ : Submodule A S.X₁) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Submodule.pow_smul_top_le I S.X₁ (Nat.le_add_left (n + 1) (cZ + cK + 1)))
    exact hshift.trans <| Submodule.map_mono hpow

/-- Helper for Lemma 15.101.1: the ambient precycles at stage `m` are those `x : S.X₂` whose
image under `S.g` already lands in `I^(m+1) S.X₃`. -/
private abbrev ambientPrecycles
    (S : ShortComplex Mod) (I : Ideal A) (m : ℕ) : Submodule A S.X₂ :=
  Submodule.comap S.g.hom (I ^ (m + 1) • (⊤ : Submodule A S.X₃))

/-- Helper for Lemma 15.101.1: reducing an ambient precycle modulo `I^(m+1)` produces a cycle in
the stage-`m` quotient complex. -/
private abbrev ambientPrecycleToStageCycles
    (S : ShortComplex Mod) (I : Ideal A) (m : ℕ) :
    S.ambientPrecycles I m →ₗ[A]
      LinearMap.ker ((S.idealPowerQuotientStageComplex I m).g.hom) where
  toFun x :=
    ⟨Submodule.Quotient.mk x.1, by
      -- The defining precycle condition says precisely that the quotient-stage differential
      -- vanishes on the reduced class of `x`.
      change Submodule.Quotient.mk (S.g.hom x.1) = 0
      exact (Submodule.Quotient.mk_eq_zero _).2 x.2⟩
  map_add' x y := by
    -- The map is induced by the quotient map on `S.X₂`, so additivity is definitional.
    ext
    rfl
  map_smul' r x := by
    -- Scalar compatibility is equally inherited from the ambient quotient map.
    ext
    rfl

/-- Helper for Lemma 15.101.1: every quotient-stage cycle admits an ambient representative whose
boundary already lies in `I^(m+1) S.X₃`. -/
private theorem ambientPrecycleToStageCycles_surjective
    (S : ShortComplex Mod) (I : Ideal A) (m : ℕ) :
    Function.Surjective (S.ambientPrecycleToStageCycles I m) := by
  intro z
  obtain ⟨x, hx⟩ :=
    Submodule.mkQ_surjective (I ^ (m + 1) • (⊤ : Submodule A S.X₂))
      ((S.idealPowerQuotientStageComplex I m).iCycles.hom z)
  refine ⟨⟨x, ?_⟩, ?_⟩
  · -- The cycle equation downstairs says that `S.g x` vanishes modulo `I^(m+1)`.
    change Submodule.Quotient.mk (S.g.hom x) = 0
    simpa [idealPowerQuotientStageComplex, idealPowerQuotientFunctor, hx] using z.2
  · -- The chosen ambient representative reduces to the original quotient-stage cycle.
    ext
    simpa [ambientPrecycleToStageCycles] using hx

-- Route correction: the first descent target is the raw sup-quotient
-- `(\ker g + I^(n+1) X₂) / I^(n+1) X₂`, where the kernel of
-- `ambientPrecycleToStageCycles` is already visibly zero.
/-- Helper for Lemma 15.101.1: the raw intermediate quotient
`(\ker g + I^(n+1) X₂) / I^(n+1) X₂` used for the first descent from ambient precycles. -/
private abbrev ambient_precycle_sup_quotient_model
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :=
  ((LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂)) ⧸
    (I ^ (n + 1) • (⊤ : Submodule A S.X₂)).submoduleOf
      (LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂)))

/-- Helper for Lemma 15.101.1: actual cycles map canonically to the raw sup-quotient by
including `ker(S.g)` into `ker(S.g) + I^(n+1) X₂` and then quotienting by `I^(n+1) X₂`. -/
private abbrev cycles_to_ambient_precycle_sup_quotient
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    LinearMap.ker S.g.hom →ₗ[A] ambient_precycle_sup_quotient_model S I n :=
  (Submodule.mkQ
      ((I ^ (n + 1) • (⊤ : Submodule A S.X₂)).submoduleOf
        (LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂)))).comp
    (Submodule.inclusion
      (show LinearMap.ker S.g.hom ≤
          LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂) from
        le_sup_left))

/-- Helper for Lemma 15.101.1: every class in the raw sup-quotient admits a representative from
the actual cycle module `ker(S.g)`. -/
private theorem cycles_to_ambient_precycle_sup_quotient_surjective
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    Function.Surjective (cycles_to_ambient_precycle_sup_quotient (S := S) (I := I) n) := by
  intro y
  obtain ⟨x, rfl⟩ :=
    Submodule.mkQ_surjective
      ((I ^ (n + 1) • (⊤ : Submodule A S.X₂)).submoduleOf
        (LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂))) y
  rcases Submodule.mem_sup.1 x.2 with ⟨z, hz, u, hu, hxu⟩
  refine ⟨⟨z, hz⟩, ?_⟩
  -- Splitting a representative as `z + u` shows that its quotient class is already represented by
  -- the cycle part `z`, because the error term `u` lies in the denominator.
  symm
  exact (Submodule.Quotient.eq _).2 <| by
    change
      x -
          (Submodule.inclusion
              (show LinearMap.ker S.g.hom ≤
                  LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂) from
                le_sup_left)
              ⟨z, hz⟩) ∈
        (I ^ (n + 1) • (⊤ : Submodule A S.X₂)).submoduleOf
          (LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂))
    change x.1 - z ∈ I ^ (n + 1) • (⊤ : Submodule A S.X₂)
    have hdiff : x.1 - z = u := by
      rw [hxu, add_sub_cancel_left]
    simpa [hdiff] using hu

/-- Helper for Lemma 15.101.1: an ambient precycle at stage `c + n` maps canonically to the raw
sup-quotient `(\ker g + I^(n+1) X₂) / I^(n+1) X₂` using the Artin-Rees cycle decomposition. -/
private abbrev ambient_precycle_to_sup_quotient
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (hcycles : ∀ n : ℕ,
      Submodule.comap S.g.hom (I ^ (c + n + 1) • (⊤ : Submodule A S.X₃)) ≤
        LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂))
    (n : ℕ) :
    S.ambientPrecycles I (c + n) →ₗ[A]
      ambient_precycle_sup_quotient_model S I n :=
  (Submodule.mkQ
      ((I ^ (n + 1) • (⊤ : Submodule A S.X₂)).submoduleOf
        (LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂)))).comp
    (Submodule.inclusion (hcycles n))

/-- Helper for Lemma 15.101.1: the raw sup-quotient map kills the kernel of
`ambientPrecycleToStageCycles`, so it descends canonically to quotient-stage cycles. -/
private theorem ambient_precycle_to_sup_quotient_ker_le
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (hcycles : ∀ n : ℕ,
      Submodule.comap S.g.hom (I ^ (c + n + 1) • (⊤ : Submodule A S.X₃)) ≤
        LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂))
    (n : ℕ) :
    LinearMap.ker (S.ambientPrecycleToStageCycles I (c + n)) ≤
      LinearMap.ker (ambient_precycle_to_sup_quotient (S := S) (I := I) (c := c) hcycles n) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  change
    (Submodule.mkQ
        ((I ^ (n + 1) • (⊤ : Submodule A S.X₂)).submoduleOf
          (LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂))))
      ((Submodule.inclusion (hcycles n)) x) = 0
  -- Zero in the quotient-stage cycle object means the ambient representative already lies in the
  -- deeper ideal-power stage of `S.X₂`.
  have hxdeep :
      x.1 ∈ I ^ (c + n + 1) • (⊤ : Submodule A S.X₂) := by
    change (Submodule.Quotient.mk x.1 :
        idealPowerModuleQuotient I S.X₂ (c + n)) = 0 at hx
    exact (Submodule.Quotient.mk_eq_zero _).1 hx
  have hxshallow :
      x.1 ∈ I ^ (n + 1) • (⊤ : Submodule A S.X₂) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (Submodule.pow_smul_top_le I S.X₂ (Nat.le_add_left (n + 1) c)) hxdeep
  -- That shallower ideal-power membership is exactly the zero criterion in the raw sup-quotient.
  exact (Submodule.Quotient.mk_eq_zero _).2 <| by
    change ((Submodule.inclusion (hcycles n) x :
        LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂)) : S.X₂) ∈
      I ^ (n + 1) • (⊤ : Submodule A S.X₂)
    simpa using hxshallow

/-- Helper for Lemma 15.101.1: the raw sup-quotient map descends canonically from ambient
precycles to quotient-stage cycles after the Artin-Rees shift. -/
private noncomputable abbrev stage_cycles_to_sup_quotient_descends
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (hcycles : ∀ n : ℕ,
      Submodule.comap S.g.hom (I ^ (c + n + 1) • (⊤ : Submodule A S.X₃)) ≤
        LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂))
    (n : ℕ) :
    LinearMap.ker ((S.idealPowerQuotientStageComplex I (c + n)).g.hom) →ₗ[A]
      ambient_precycle_sup_quotient_model S I n := by
  let f := S.ambientPrecycleToStageCycles I (c + n)
  let g := ambient_precycle_to_sup_quotient (S := S) (I := I) (c := c) hcycles n
  let desc :
      (S.ambientPrecycles I (c + n) ⧸ LinearMap.ker f) →ₗ[A]
        ambient_precycle_sup_quotient_model S I n :=
    Submodule.liftQ (LinearMap.ker f) g
      (ambient_precycle_to_sup_quotient_ker_le (S := S) (I := I) (c := c) hcycles n)
  have hrange : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact S.ambientPrecycleToStageCycles_surjective I (c + n)
  let e :
      (S.ambientPrecycles I (c + n) ⧸ LinearMap.ker f) ≃ₗ[A]
        LinearMap.ker ((S.idealPowerQuotientStageComplex I (c + n)).g.hom) :=
    (f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange)).trans Submodule.topEquiv
  -- We first descend to the quotient by `ker f`, then identify that quotient with the full stage
  -- cycle object via surjectivity of `ambientPrecycleToStageCycles`.
  exact desc.comp e.symm.toLinearMap

/-- Helper for Lemma 15.101.1: the codomain ambiguity remaining after the first Artin-Rees cycle
descent is exactly the image of stage boundaries inside the raw sup-quotient. -/
private abbrev sup_boundary_image
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (hcycles : ∀ n : ℕ,
      Submodule.comap S.g.hom (I ^ (c + n + 1) • (⊤ : Submodule A S.X₃)) ≤
        LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂))
    (n : ℕ) :
    Submodule A (ambient_precycle_sup_quotient_model S I n) :=
  Submodule.map
    (stage_cycles_to_sup_quotient_descends (S := S) (I := I) (c := c) hcycles n)
    (LinearMap.range ((S.idealPowerQuotientStageComplex I (c + n)).moduleCatToCycles))

-- Route correction: we do not transport the raw sup-quotient directly to `quotientModel n`.
-- We first quotient by the image of stage boundaries, so the homology descent becomes tautological.
/-- Helper for Lemma 15.101.1: after quotienting the raw sup-quotient by the stage-boundary image,
the Artin-Rees cycle descent factors canonically through the stage left homology. -/
private noncomputable abbrev stage_homology_to_sup_quotient_mod_boundary
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (hcycles : ∀ n : ℕ,
      Submodule.comap S.g.hom (I ^ (c + n + 1) • (⊤ : Submodule A S.X₃)) ≤
        LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂))
    (n : ℕ) :
    S.idealPowerHomologyStage I (c + n) →ₗ[A]
      ((ambient_precycle_sup_quotient_model S I n) ⧸
        sup_boundary_image (S := S) (I := I) (c := c) hcycles n) := by
  let T : ShortComplex Mod := S.idealPowerQuotientStageComplex I (c + n)
  change
    (LinearMap.ker T.g.hom ⧸ LinearMap.range T.moduleCatToCycles) →ₗ[A]
      ((ambient_precycle_sup_quotient_model S I n) ⧸
        sup_boundary_image (S := S) (I := I) (c := c) hcycles n)
  refine
    Submodule.liftQ
      (LinearMap.range T.moduleCatToCycles)
      ((Submodule.mkQ (sup_boundary_image (S := S) (I := I) (c := c) hcycles n)).comp
        (stage_cycles_to_sup_quotient_descends (S := S) (I := I) (c := c) hcycles n))
      ?_
  intro x hx
  rw [LinearMap.mem_ker]
  change
    (Submodule.mkQ (sup_boundary_image (S := S) (I := I) (c := c) hcycles n))
        ((stage_cycles_to_sup_quotient_descends (S := S) (I := I) (c := c) hcycles n) x) = 0
  -- Membership in the mapped boundary image is exactly the zero criterion in the codomain
  -- quotient.
  rw [Submodule.Quotient.mk_eq_zero]
  exact Submodule.mem_map_of_mem
    (stage_cycles_to_sup_quotient_descends (S := S) (I := I) (c := c) hcycles n) hx

/-- Helper for Lemma 15.101.1: the descended cycle-to-sup-quotient map computes on an explicit
ambient precycle representative by forgetting the quotient by `ker(ambientPrecycleToStageCycles)`.
-/
private theorem stage_cycles_to_sup_quotient_descends_apply_ambient_precycle
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (hcycles : ∀ n : ℕ,
      Submodule.comap S.g.hom (I ^ (c + n + 1) • (⊤ : Submodule A S.X₃)) ≤
        LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂))
    (n : ℕ) (x : S.ambientPrecycles I (c + n)) :
    stage_cycles_to_sup_quotient_descends (S := S) (I := I) (c := c) hcycles n
        (S.ambientPrecycleToStageCycles I (c + n) x) =
      ambient_precycle_to_sup_quotient (S := S) (I := I) (c := c) hcycles n x := by
  let f := S.ambientPrecycleToStageCycles I (c + n)
  let g := ambient_precycle_to_sup_quotient (S := S) (I := I) (c := c) hcycles n
  let desc :
      (S.ambientPrecycles I (c + n) ⧸ LinearMap.ker f) →ₗ[A]
        ambient_precycle_sup_quotient_model S I n :=
    Submodule.liftQ (LinearMap.ker f) g
      (ambient_precycle_to_sup_quotient_ker_le (S := S) (I := I) (c := c) hcycles n)
  have hrange : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact S.ambientPrecycleToStageCycles_surjective I (c + n)
  let e :
      (S.ambientPrecycles I (c + n) ⧸ LinearMap.ker f) ≃ₗ[A]
        LinearMap.ker ((S.idealPowerQuotientStageComplex I (c + n)).g.hom) :=
    (f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange)).trans Submodule.topEquiv
  -- The quotient equivalence sends the class of `x` to its stage-cycle image, so evaluating the
  -- descended map there is just the defining `liftQ` computation.
  change desc (e.symm (f x)) = g x
  have hsymm : e.symm (f x) = Submodule.Quotient.mk x := by
    apply e.injective
    simp [e, f]
  rw [hsymm]
  simp [desc]

/-- Helper for Lemma 15.101.1: the first cycle descent sends a stage boundary generator to the raw
sup-quotient class of the corresponding ambient boundary. -/
private theorem stage_cycles_to_sup_quotient_on_boundary
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (hcycles : ∀ n : ℕ,
      Submodule.comap S.g.hom (I ^ (c + n + 1) • (⊤ : Submodule A S.X₃)) ≤
        LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂))
    (n : ℕ) (a : S.X₁) :
    let T : ShortComplex Mod := S.idealPowerQuotientStageComplex I (c + n)
    stage_cycles_to_sup_quotient_descends (S := S) (I := I) (c := c) hcycles n
        (T.moduleCatToCycles (Submodule.Quotient.mk a)) =
      cycles_to_ambient_precycle_sup_quotient (S := S) (I := I) n (S.moduleCatToCycles a) := by
  let T : ShortComplex Mod := S.idealPowerQuotientStageComplex I (c + n)
  let x : S.ambientPrecycles I (c + n) := by
    refine ⟨S.f.hom a, ?_⟩
    have hfg : S.g.hom (S.f.hom a) = 0 := by
      simpa using LinearMap.congr_fun (congrArg ModuleCat.Hom.hom S.zero) a
    simpa [hfg] using
      (show (0 : S.X₃) ∈ I ^ (c + n + 1) • (⊤ : Submodule A S.X₃) by simp)
  have hstage :
      S.ambientPrecycleToStageCycles I (c + n) x =
        T.moduleCatToCycles (Submodule.Quotient.mk a) := by
    -- Both constructions reduce the same ambient boundary `S.f a` modulo `I^(c+n+1)`.
    apply Subtype.ext
    rfl
  rw [← hstage]
  rw [stage_cycles_to_sup_quotient_descends_apply_ambient_precycle
    (S := S) (I := I) (c := c) hcycles n x]
  -- The raw sup-quotient only remembers the ambient boundary representative, so the two classes
  -- agree once we identify their common underlying element of `S.X₂`.
  change
    (Submodule.mkQ
        ((I ^ (n + 1) • (⊤ : Submodule A S.X₂)).submoduleOf
          (LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂))))
        ((Submodule.inclusion (hcycles n)) x) =
      (Submodule.mkQ
        ((I ^ (n + 1) • (⊤ : Submodule A S.X₂)).submoduleOf
          (LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂))))
        ((Submodule.inclusion
            (show LinearMap.ker S.g.hom ≤
                LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂) from
              le_sup_left))
          (S.moduleCatToCycles a))
  congr
  apply Subtype.ext
  rfl

/-- Helper for Lemma 15.101.1: after the Artin-Rees shift, every ambient precycle at stage
`c + n` is congruent modulo `I^(n+1)` to an actual ambient cycle. -/
private theorem ambient_precycle_has_cycle_reduction
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (hcycles : ∀ n : ℕ,
      Submodule.comap S.g.hom (I ^ (c + n + 1) • (⊤ : Submodule A S.X₃)) ≤
        LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂))
    (n : ℕ) (x : S.ambientPrecycles I (c + n)) :
    ∃ z : LinearMap.ker S.g.hom,
      x.1 - z.1 ∈ I ^ (n + 1) • (⊤ : Submodule A S.X₂) := by
  have hx :
      x.1 ∈
        LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂) :=
    hcycles n x.2
  rcases Submodule.mem_sup.1 hx with ⟨z, hz, u, hu, hxu⟩
  refine ⟨⟨z, hz⟩, ?_⟩
  -- The Artin-Rees decomposition `x = z + u` identifies the required quotient error term with `u`.
  simpa [hxu] using hu

/-- Helper for Lemma 15.101.1: on any short complex of `A`-modules, a left-homology class
vanishes exactly when its cycle representative comes from the concrete boundary map
`moduleCatToCycles`. -/
private theorem shortComplex_leftHomologyπ_eq_zero_iff_exists_boundary
    (T : ShortComplex Mod) (q : T.cycles) :
    T.leftHomologyπ.hom q = 0 ↔
      ∃ b : T.X₁, T.moduleCatToCycles b = T.moduleCatCyclesIso.hom q := by
  have hcomm :
      T.leftHomologyπ ≫ T.moduleCatLeftHomologyData.leftHomologyIso.hom =
        T.moduleCatCyclesIso.hom ≫ T.moduleCatLeftHomologyData.π := by
    -- Compare the abstract left-homology quotient with the concrete quotient by boundaries before
    -- evaluating at the chosen cycle.
    simpa using
      (ShortComplex.leftHomologyMapData
        (𝟙 T) T.leftHomologyData T.moduleCatLeftHomologyData).commπ
  constructor
  · intro hq
    -- Pushing the zero class to the concrete quotient turns vanishing into membership in the
    -- boundary range.
    have hπ := congrArg (fun f : T.cycles ⟶ T.moduleCatLeftHomologyData.H ↦ f.hom q) hcomm
    change
      T.moduleCatLeftHomologyData.leftHomologyIso.hom.hom (T.leftHomologyπ.hom q) =
        T.moduleCatLeftHomologyData.π.hom (T.moduleCatCyclesIso.hom q)
      at hπ
    rw [hq, LinearMap.map_zero] at hπ
    have hmem :
        T.moduleCatCyclesIso.hom q ∈ LinearMap.range T.moduleCatToCycles := by
      simpa using
        (Submodule.Quotient.mk_eq_zero (LinearMap.range T.moduleCatToCycles)).1 hπ.symm
    exact LinearMap.mem_range.mp hmem
  · rintro ⟨b, hb⟩
    -- An explicit boundary witness is zero in the concrete quotient, hence also in left homology.
    have hπ : T.moduleCatLeftHomologyData.π.hom (T.moduleCatCyclesIso.hom q) = 0 := by
      exact (Submodule.Quotient.mk_eq_zero (LinearMap.range T.moduleCatToCycles)).2
        (LinearMap.mem_range.mpr ⟨b, hb⟩)
    have hzero := congrArg (fun f : T.cycles ⟶ T.moduleCatLeftHomologyData.H ↦ f.hom q) hcomm
    change
      T.moduleCatLeftHomologyData.leftHomologyIso.hom.hom (T.leftHomologyπ.hom q) =
        T.moduleCatLeftHomologyData.π.hom (T.moduleCatCyclesIso.hom q)
      at hzero
    rw [hπ] at hzero
    have hinj :
        Function.Injective T.moduleCatLeftHomologyData.leftHomologyIso.hom.hom :=
      (ModuleCat.mono_iff_injective T.moduleCatLeftHomologyData.leftHomologyIso.hom).1
        inferInstance
    have h0 : 0 = T.moduleCatLeftHomologyData.leftHomologyIso.hom.hom 0 := by
      simpa using (T.moduleCatLeftHomologyData.leftHomologyIso.hom.hom.map_zero).symm
    exact hinj (hzero.trans h0)

/-- Helper for Lemma 15.101.1: a zero class in the quotient-stage left homology can be witnessed
by an ambient boundary before reduction modulo `I^(m+1)`. -/
private theorem quotientStage_leftHomologyπ_eq_zero_iff_exists_boundary_lift
    (S : ShortComplex Mod) (I : Ideal A) (m : ℕ)
    (q : (S.idealPowerQuotientStageComplex I m).cycles) :
    ((S.idealPowerQuotientStageComplex I m).leftHomologyπ).hom q = 0 ↔
      ∃ a : S.X₁,
        ((S.idealPowerQuotientStageComplex I m).moduleCatCyclesIso.hom q).1 =
          Submodule.Quotient.mk (S.f.hom a) := by
  let T : ShortComplex Mod := S.idealPowerQuotientStageComplex I m
  constructor
  · intro hq
    rcases (shortComplex_leftHomologyπ_eq_zero_iff_exists_boundary (T := T) q).1 hq with
      ⟨b, hb⟩
    obtain ⟨a, rfl⟩ :=
      Submodule.mkQ_surjective (I ^ (m + 1) • (⊤ : Submodule A S.X₁)) b
    refine ⟨a, ?_⟩
    -- Lifting the quotient-stage boundary representative to `S.X₁` exposes the ambient boundary
    -- whose reduction is the given stage cycle.
    simpa [T, idealPowerQuotientStageComplex, idealPowerQuotientFunctor] using
      congrArg Subtype.val hb.symm
  · rintro ⟨a, ha⟩
    apply (shortComplex_leftHomologyπ_eq_zero_iff_exists_boundary (T := T) q).2
    refine ⟨Submodule.Quotient.mk a, ?_⟩
    -- The chosen ambient boundary reduces to the prescribed quotient-stage cycle representative.
    apply Subtype.ext
    simpa [T, idealPowerQuotientStageComplex, idealPowerQuotientFunctor] using ha.symm

/-- Helper for Lemma 15.101.1: transporting a cycle through `moduleCatCyclesIso.hom` forgets to
the same ambient middle-term element. -/
private theorem moduleCatCyclesIso_hom_iCycles
    (S : ShortComplex Mod) (z : S.cycles) :
    (S.moduleCatCyclesIso.hom z).1 = S.iCycles.hom z := by
  -- The cycles object is definitionally the kernel used by `moduleCatCyclesIso`.
  rfl

/-- Helper for Lemma 15.101.1: the categorical boundary map becomes the concrete kernel-level
boundary map after transporting through `moduleCatCyclesIso.hom`. -/
private theorem moduleCatCyclesIso_hom_toCycles
    (S : ShortComplex Mod) (a : S.X₁) :
    S.moduleCatCyclesIso.hom (S.toCycles.hom a) = S.moduleCatToCycles a := by
  -- Compare both kernel elements through their ambient images in `S.X₂`.
  apply Subtype.ext
  change S.iCycles.hom (S.toCycles.hom a) = (S.moduleCatToCycles a).1
  have hto :
      S.iCycles.hom (S.toCycles.hom a) = S.f.hom a := by
    have hto' :=
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (ShortComplex.toCycles_i S)) a
    change ((S.toCycles ≫ S.iCycles).hom a) = S.f.hom a at hto'
    exact hto'
  simpa [ShortComplex.moduleCatToCycles] using hto

/-- Helper for Lemma 15.101.1: the `I^(n+1)`-power stage inside the concrete cycle kernel is the
image of the corresponding `I^(n+1)`-power stage inside the abstract cycles object. -/
private theorem moduleCatCyclesIso_map_cycle_pow_eq_pow
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    Submodule.map S.moduleCatCyclesIso.hom.hom
      (I ^ (n + 1) • (⊤ : Submodule A S.cycles)) =
      I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom)) := by
  -- Surjectivity of the cycles isomorphism turns `map_smul''` into the expected ideal-power stage.
  have hsurj : Function.Surjective S.moduleCatCyclesIso.hom.hom :=
    (ModuleCat.epi_iff_surjective S.moduleCatCyclesIso.hom).1 inferInstance
  rw [Submodule.map_smul'', Submodule.map_top]
  rw [LinearMap.range_eq_top.2 hsurj]
  rfl

/-- Helper for Lemma 15.101.1: the quotient map from cycles to left homology sends the
`I^(n+1)`-power stage of cycles onto `I^(n+1)` times left homology. -/
private theorem leftHomologyπ_map_cycle_pow_eq_pow
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    Submodule.map S.leftHomologyπ.hom
      (I ^ (n + 1) • (⊤ : Submodule A S.cycles)) =
      I ^ (n + 1) • (⊤ : Submodule A S.leftHomology) := by
  -- Surjectivity of `S.leftHomologyπ` makes the ideal-power stage map onto the full target stage.
  have hsurj : Function.Surjective S.leftHomologyπ.hom :=
    (ModuleCat.epi_iff_surjective S.leftHomologyπ).1 inferInstance
  rw [Submodule.map_smul'', Submodule.map_top]
  rw [LinearMap.range_eq_top.2 hsurj]
  rfl

/-- Helper for Lemma 15.101.1: the kernel cycle inclusion `ker(S.g) ↪ S.X₂` satisfies a shifted
Artin-Rees containment for the ambient `I`-adic filtration. -/
private theorem exists_cycle_subtype_artin_rees_shift
    (S : ShortComplex Mod) (I : Ideal A) [Module.Finite A S.X₂] :
    ∃ c : ℕ, ∀ n : ℕ,
      Submodule.comap (LinearMap.ker S.g.hom).subtype
        (I ^ (c + n + 1) • (⊤ : Submodule A S.X₂)) ≤
        I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom)) := by
  -- Route correction: kernel annihilation only needs Artin-Rees for the cycle inclusion
  -- `ker(S.g) ↪ S.X₂`, so we freeze that owner statement separately from the quotient comparison.
  let _ : Module.Finite A ↥S.X₂ := by
    simpa using (inferInstance : Module.Finite A S.X₂)
  obtain ⟨c, hpreimage, _⟩ :=
    Ideal.exists_artin_rees_constant_of_exact I
      (LinearMap.exact_subtype_ker_map (LinearMap.ker S.g.hom).subtype)
  refine ⟨c, ?_⟩
  intro n
  have hker : LinearMap.ker (LinearMap.ker S.g.hom).subtype = ⊥ := by
    ext x
    simp
  -- The Artin-Rees equality for the subtype map collapses because that map has zero kernel.
  calc
    Submodule.comap (LinearMap.ker S.g.hom).subtype
        (I ^ (c + n + 1) • (⊤ : Submodule A S.X₂)) =
      I ^ (n + 1) •
        Submodule.comap (LinearMap.ker S.g.hom).subtype
          (I ^ c • (⊤ : Submodule A S.X₂)) := by
        simpa [hker, show c + n + 1 - c = n + 1 by omega] using
          hpreimage (c + n + 1) (Nat.le_add_right c (n + 1))
    _ ≤ I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom)) :=
      smul_mono_right _ le_top

/-- Helper for Lemma 15.101.1: every `I`-multiple in `H_{n+1}` comes from the next quotient-stage
homology group `H_{n+2}`. -/
private theorem idealPowerHomology_one_pow_le_step_range
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    I • (⊤ : Submodule A (S.idealPowerHomologyStage I n)) ≤
      LinearMap.range (S.idealPowerHomologyStep I n).hom := by
  -- We lift a homology class to a quotient-stage cycle, multiply an ambient representative by a
  -- scalar in `I`, and check that it becomes a cycle one stage deeper.
  rw [Submodule.smul_le]
  intro r hr y hy
  let T₀ : ShortComplex Mod := S.idealPowerQuotientStageComplex I n
  let T₁ : ShortComplex Mod := S.idealPowerQuotientStageComplex I (n + 1)
  let φ : T₁ ⟶ T₀ := S.mapNatTrans (idealPowerQuotientTransitionNatTrans I n)
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective T₀.leftHomologyπ).1 inferInstance y
  obtain ⟨x, hx⟩ :=
    Submodule.mkQ_surjective (I ^ (n + 1) • (⊤ : Submodule A S.X₂)) (T₀.iCycles.hom z)
  have hz_cycle : T₀.g.hom (Submodule.Quotient.mk x) = 0 := by
    simpa [T₀, hx] using z.2
  have hx_cycle :
      S.g.hom x ∈ I ^ (n + 1) • (⊤ : Submodule A S.X₃) := by
    change Submodule.Quotient.mk (S.g.hom x) = 0 at hz_cycle
    exact (Submodule.Quotient.mk_eq_zero _).1 hz_cycle
  have hrx_cycle :
      T₁.g.hom (Submodule.Quotient.mk (r • x)) = 0 := by
    change Submodule.Quotient.mk (S.g.hom (r • x)) = 0
    rw [LinearMap.map_smul, Submodule.Quotient.mk_eq_zero]
    simpa [pow_succ, smul_assoc, mul_comm, mul_left_comm, mul_assoc] using
      Submodule.smul_mem_smul hr hx_cycle
  let w : LinearMap.ker T₁.g.hom := ⟨Submodule.Quotient.mk (r • x), hrx_cycle⟩
  have hw_cycles :
      T₀.cyclesMap φ w = r • z := by
    apply (ModuleCat.mono_iff_injective T₀.iCycles).1 inferInstance
    have hi :=
      congrArg (fun f : T₁.cycles ⟶ T₀.X₂ ↦ f.hom w) (ShortComplex.cyclesMap_i φ)
    simpa [φ, T₀, T₁, hx] using hi
  refine LinearMap.mem_range.mpr ⟨T₁.leftHomologyπ.hom w, ?_⟩
  have hπ :=
    congrArg
      (fun f : T₁.leftHomology ⟶ T₀.leftHomology ↦ f.hom (T₁.leftHomologyπ.hom w))
      (ShortComplex.homologyπ_naturality φ)
  simpa [idealPowerHomologyStep, φ, hw_cycles, T₀.leftHomologyπ.hom.map_smul] using hπ

/-- Helper for Lemma 15.101.1: every `I^c`-multiple in `H_{n+1}` already comes from the
transition map `H_{n+c+1} ⟶ H_{n+1}`. -/
private theorem idealPowerHomology_pow_le_transition_range
    (S : ShortComplex Mod) (I : Ideal A) (n c : ℕ) :
    I ^ c • (⊤ : Submodule A (S.idealPowerHomologyStage I n)) ≤
      LinearMap.range
        (((S.idealPowerHomologyTower I).transitionMap (Nat.le_add_right n c)).hom) := by
  induction c with
  | zero =>
      -- The zero-shift transition is the identity, so its range is all of `H_{n+1}`.
      simp [SequentialInverseSystem.transitionMap]
  | succ c ih =>
      -- First reach stage `n + c`, then lift the extra `I`-multiple one more step and compose
      -- the two transition maps.
      rw [pow_succ, Submodule.smul_le]
      intro r hr y hy
      rcases LinearMap.mem_range.mp (ih hy) with ⟨x, rfl⟩
      rcases LinearMap.mem_range.mp
          ((idealPowerHomology_one_pow_le_step_range (S := S) (I := I) (n := n + c))
            (Submodule.smul_mem_smul hr (show x ∈ (⊤ : Submodule A (S.idealPowerHomologyStage I (n + c))) by
              simp))) with ⟨z, hz⟩
      refine LinearMap.mem_range.mpr ⟨z, ?_⟩
      have hcomp :
          (S.idealPowerHomologyTower I).transitionMap (Nat.le_add_right n (c + 1)) =
            (S.idealPowerHomologyTower I).transitionMap (Nat.le_succ (n + c)) ≫
              (S.idealPowerHomologyTower I).transitionMap (Nat.le_add_right n c) := by
        simpa [Nat.add_assoc] using
          transitionMap_comp
            (F := S.idealPowerHomologyTower I)
            (Nat.le_add_right n c)
            (Nat.le_succ (n + c))
      change
        ((S.idealPowerHomologyTower I).transitionMap (Nat.le_add_right n (c + 1))).hom z =
          r • (((S.idealPowerHomologyTower I).transitionMap (Nat.le_add_right n c)).hom x)
      rw [hcomp, Category.assoc]
      simp [hz, LinearMap.map_smul]

/-- Helper for Lemma 15.101.1: the canonical map `H ⟶ H_{i+1}` factors through every later stage
`H_{j+1}` via the transition morphism `H_{j+1} ⟶ H_{i+1}`. -/
private theorem leftHomologyToIdealPowerStage_comp_transition
    {i j : ℕ} (hij : i ≤ j) :
    S.leftHomologyToIdealPowerStage I j ≫
        (S.idealPowerHomologyTower I).transitionMap hij =
      S.leftHomologyToIdealPowerStage I i := by
  -- We induct over the length of the refinement and use the one-step compatibility already
  -- proved above.
  refine Nat.le_induction ?_ ?_ hij
  · simp [SequentialInverseSystem.transitionMap]
  · intro k hik hk
    have hstep :
        (S.idealPowerHomologyTower I).transitionMap (Nat.succ_le_succ hik) =
          SequentialInverseSystem.stepMap (S.idealPowerHomologyTower I) k ≫
            (S.idealPowerHomologyTower I).transitionMap hik := by
      have hproof :
          Nat.succ_le_succ hik = hik.trans (Nat.le_succ k) := by
        apply Subsingleton.elim
      simpa [hproof, SequentialInverseSystem.stepMap] using
        transitionMap_comp (F := S.idealPowerHomologyTower I) hik (Nat.le_succ k)
    calc
      S.leftHomologyToIdealPowerStage I (k + 1) ≫
          (S.idealPowerHomologyTower I).transitionMap (Nat.succ_le_succ hik) =
        S.leftHomologyToIdealPowerStage I (k + 1) ≫
          SequentialInverseSystem.stepMap (S.idealPowerHomologyTower I) k ≫
            (S.idealPowerHomologyTower I).transitionMap hik := by
              rw [hstep, Category.assoc]
      _ = S.leftHomologyToIdealPowerStage I k ≫
            (S.idealPowerHomologyTower I).transitionMap hik := by
              rw [leftHomologyToIdealPowerStage_comp_step (S := S) (I := I) k]
      _ = S.leftHomologyToIdealPowerStage I i := hk

-- Proof sketch: both composites out of `H / I^(n+2) H` are quotient lifts of the same map
-- `H ⟶ H_n`, namely the step compatibility already proved for `H ⟶ H_{n+1}`.
/-- Helper for Lemma 15.101.1: the forward quotient comparisons form a morphism of inverse
systems. -/
private theorem leftHomologyQuotientComparison_step_comm (n : ℕ) :
    S.leftHomologyQuotientStep I n ≫ S.leftHomologyQuotientComparison I n =
      S.leftHomologyQuotientComparison I (n + 1) ≫ S.idealPowerHomologyStep I n := by
  ext x
  obtain ⟨y, rfl⟩ :=
    (Submodule.mkQ_surjective (I ^ (n + 2) • (⊤ : Submodule A S.leftHomology))) x
  -- Evaluate both quotient lifts on a representative and reduce to the step-compatibility
  -- relation `H ⟶ H_{n+2} ⟶ H_{n+1} = H ⟶ H_{n+1}`.
  change
      ((S.leftHomologyQuotientComparison I n).hom
          ((S.leftHomologyQuotientStep I n).hom (Submodule.Quotient.mk y))) =
        ((S.idealPowerHomologyStep I n).hom
          ((S.leftHomologyQuotientComparison I (n + 1)).hom (Submodule.Quotient.mk y)))
  simp only [leftHomologyQuotientComparison, leftHomologyQuotientStep, idealPowerHomologyStep]
  rw [Submodule.liftQ_apply, Submodule.liftQ_apply]
  simpa using
    congrArg (fun f : S.leftHomology ⟶ S.idealPowerHomologyStage I n ↦ f.hom y)
      (leftHomologyToIdealPowerStage_comp_step (S := S) (I := I) n).symm

/-- The canonical maps `H / I^(n+1) H ⟶ H_{n+1}` assemble into a morphism of inverse systems. -/
private abbrev leftHomologyQuotientComparisonNatTrans :
    S.leftHomologyQuotientTower I ⟶ S.idealPowerHomologyTower I :=
  NatTrans.ofOpSequence
    (fun n ↦ S.leftHomologyQuotientComparison I n)
    (fun n ↦ by
      simpa [leftHomologyQuotientStep, idealPowerHomologyStep] using
        leftHomologyQuotientComparison_step_comm (S := S) (I := I) n)

/-- Helper for Lemma 15.101.1: the forward quotient comparisons commute with every refined
transition map, not just the successor step. -/
private theorem leftHomologyQuotientComparison_comp_transition
    {i j : ℕ} (hij : i ≤ j) :
    (S.leftHomologyQuotientTower I).transitionMap hij ≫
        S.leftHomologyQuotientComparison I i =
      S.leftHomologyQuotientComparison I j ≫
        (S.idealPowerHomologyTower I).transitionMap hij := by
  -- This is the naturality square of the already-packaged tower morphism evaluated on `homOfLE`.
  simpa [SequentialInverseSystem.transitionMap] using
    (leftHomologyQuotientComparisonNatTrans (S := S) (I := I)).naturality ((homOfLE hij).op)

-- Proof sketch: once the forward maps are assembled into a shifted representative, the two
-- composite identities from the Artin-Rees comparison are exactly the equivalence data required
-- by `SequentialProObjectMorphismRep.IsProIsomorphism`.
/-- Helper for Lemma 15.101.1: the stagewise comparison identities package the shifted comparison
into a pro-isomorphism witness. -/
private theorem shifted_idealPowerHomology_comparison_isProIsomorphism
    (c : ℕ)
    (comparison : S.idealPowerHomologyShiftComparison I c)
    (hleft : ∀ n : ℕ,
      S.leftHomologyQuotientComparison I (c + n) ≫ comparison.app (op n) =
        SequentialInverseSystem.transitionMap (S.leftHomologyQuotientTower I)
          (Nat.le_add_left n c))
    (hright : ∀ n : ℕ,
      ((comparison.app (op n)) :
          S.idealPowerHomologyStage I (c + n) ⟶ S.leftHomologyQuotientStage I n) ≫
        S.leftHomologyQuotientComparison I n =
          SequentialInverseSystem.transitionMap (S.idealPowerHomologyTower I)
            (Nat.le_add_left n c)) :
    (ofShiftNatTrans c comparison).IsProIsomorphism := by
  let homologyComp :=
    compRep (ofShiftNatTrans c comparison)
      (ofShiftNatTrans c (leftHomologyQuotientComparisonNatTrans (S := S) (I := I)))
  let quotientComp :=
    compRep (ofShiftNatTrans c (leftHomologyQuotientComparisonNatTrans (S := S) (I := I)))
      (ofShiftNatTrans c comparison)
  refine
    ⟨ofShiftNatTrans c (leftHomologyQuotientComparisonNatTrans (S := S) (I := I)), ?_, ?_⟩
  · -- Route correction: instead of reopening Artin-Rees, we compare both composites with the
    -- canonical transition map on the homology tower after refining to the common shift
    -- `n ↦ c + (c + n)`.
    refine ⟨homologyComp.reindex, fun n ↦ le_rfl, ?_, ?_⟩
    · intro n
      simpa [homologyComp, SequentialProObjectMorphismRep.compRep,
        SequentialProObjectMorphismRep.ofShiftNatTrans] using shiftComparison_le n c
    · intro n
      simpa [homologyComp, SequentialInverseSystem.transitionMap] using hright (c + n)
  · -- The same common refinement identifies the reverse composite with the canonical transition
    -- map on the quotient tower.
    refine ⟨quotientComp.reindex, fun n ↦ le_rfl, ?_, ?_⟩
    · intro n
      simpa [quotientComp, SequentialProObjectMorphismRep.compRep,
        SequentialProObjectMorphismRep.ofShiftNatTrans] using shiftComparison_le n c
    · intro n
      simpa [quotientComp, SequentialInverseSystem.transitionMap] using hleft (c + n)

/-- Helper for Lemma 15.101.1: once the shifted reverse comparison is available, the cokernel of
`H / I^(n+1) H ⟶ H_{n+1}` is annihilated by the same Artin-Rees power. -/
private theorem leftHomologyComparison_cokernel_annihilated_of_comparison
    (c : ℕ)
    (comparison : S.idealPowerHomologyShiftComparison I c)
    (hright : ∀ n : ℕ,
      ((comparison.app (op n)) :
          S.idealPowerHomologyStage I (c + n) ⟶ S.leftHomologyQuotientStage I n) ≫
        S.leftHomologyQuotientComparison I n =
          SequentialInverseSystem.transitionMap (S.idealPowerHomologyTower I)
            (Nat.le_add_left n c))
    (n : ℕ) :
    S.leftHomologyComparisonCokernelAnnihilated I c n := by
  unfold leftHomologyComparisonCokernelAnnihilated
  refine quotientByRange_pow_smul_top_eq_bot (I := I)
    (S.leftHomologyQuotientComparison I n).hom c ?_
  have hrange_transition :
      LinearMap.range
          (((S.idealPowerHomologyTower I).transitionMap (Nat.le_add_left n c)).hom) ≤
        LinearMap.range (S.leftHomologyQuotientComparison I n).hom := by
    intro y hy
    rcases LinearMap.mem_range.mp hy with ⟨x, rfl⟩
    refine LinearMap.mem_range.mpr ⟨((comparison.app (op n)).hom x, ?_)⟩
    -- The right composite identity rewrites the transition map through the quotient comparison.
    have hx :=
      congrArg
        (fun f :
          S.idealPowerHomologyStage I (c + n) ⟶ S.idealPowerHomologyStage I n ↦ f.hom x)
        (hright n)
    simpa using hx
  exact
    (idealPowerHomology_pow_le_transition_range (S := S) (I := I) n c).trans hrange_transition

/-- Helper for Lemma 15.101.1: the kernel of `H / I^(n+1) H ⟶ H_{n+1}` is annihilated by any
Artin-Rees shift controlling deep ambient cycles inside `ker(S.g)`. -/
private theorem leftHomologyComparison_kernel_annihilated_of_cycle_subtype_bound
    (c : ℕ)
    (hcycles :
      ∀ n : ℕ,
        Submodule.comap (LinearMap.ker S.g.hom).subtype
          (I ^ (c + n + 1) • (⊤ : Submodule A S.X₂)) ≤
          I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom)))
    (n : ℕ) :
    S.leftHomologyComparisonKernelAnnihilated I c n := by
  unfold leftHomologyComparisonKernelAnnihilated
  apply le_antisymm
  · rw [Submodule.smul_le]
    intro r hr x hx
    obtain ⟨y, rfl⟩ :=
      Submodule.mkQ_surjective (I ^ (n + 1) • (⊤ : Submodule A S.leftHomology)) x.1
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective S.leftHomologyπ).1 inferInstance y
    let T : ShortComplex Mod := S.idealPowerQuotientStageComplex I n
    let φ : S ⟶ T := S.mapNatTrans (toIdealPowerQuotientNatTrans I n)
    have hcomp :
        (S.leftHomologyQuotientComparison I n).hom
            (Submodule.Quotient.mk (S.leftHomologyπ.hom z)) =
          (S.leftHomologyToIdealPowerStage I n).hom (S.leftHomologyπ.hom z) := by
      simpa using
        congrArg
          (fun f : S.leftHomology ⟶ S.idealPowerHomologyStage I n ↦
            f.hom (S.leftHomologyπ.hom z))
          (leftHomologyQuotientComparison_comp_mkQ (S := S) (I := I) n)
    have hz_stage_zero :
        T.leftHomologyπ.hom (T.cyclesMap φ z) = 0 := by
      have hz0 :
          (S.leftHomologyToIdealPowerStage I n).hom (S.leftHomologyπ.hom z) = 0 := by
        rw [← hcomp]
        exact x.2
      have hnat :=
        congrArg
          (fun f : S.leftHomology ⟶ T.leftHomology ↦ f.hom (S.leftHomologyπ.hom z))
          (ShortComplex.homologyπ_naturality φ)
      simpa [T, φ, idealPowerHomologyStage, leftHomologyToIdealPowerStage] using
        hz0.trans hnat
    rcases
        (quotientStage_leftHomologyπ_eq_zero_iff_exists_boundary_lift
          (S := S) (I := I) (m := n) (q := T.cyclesMap φ z)).1 hz_stage_zero with
      ⟨a, ha⟩
    have hz_reduced :
        (Submodule.Quotient.mk ((S.moduleCatCyclesIso.hom z).1) :
            idealPowerModuleQuotient I S.X₂ n) =
          Submodule.Quotient.mk (S.f.hom a) := by
      calc
        (Submodule.Quotient.mk ((S.moduleCatCyclesIso.hom z).1) :
            idealPowerModuleQuotient I S.X₂ n) =
          (T.moduleCatCyclesIso.hom (T.cyclesMap φ z)).1 := by
            calc
              (Submodule.Quotient.mk ((S.moduleCatCyclesIso.hom z).1) :
                  idealPowerModuleQuotient I S.X₂ n) =
                Submodule.Quotient.mk (S.iCycles.hom z) := by
                  rw [moduleCatCyclesIso_hom_iCycles]
              _ = T.iCycles.hom (T.cyclesMap φ z) := by
                  symm
                  exact congrArg
                    (fun f : S.cycles ⟶ T.X₂ ↦ f.hom z)
                    (ShortComplex.cyclesMap_i φ)
              _ = (T.moduleCatCyclesIso.hom (T.cyclesMap φ z)).1 := by
                  rw [moduleCatCyclesIso_hom_iCycles]
        _ = Submodule.Quotient.mk (S.f.hom a) := ha
    let w : LinearMap.ker S.g.hom :=
      S.moduleCatCyclesIso.hom z - S.moduleCatToCycles a
    have hw_mem :
        w ∈ Submodule.comap (LinearMap.ker S.g.hom).subtype
          (I ^ (n + 1) • (⊤ : Submodule A S.X₂)) := by
      change ((S.moduleCatCyclesIso.hom z).1 - (S.moduleCatToCycles a).1) ∈
        I ^ (n + 1) • (⊤ : Submodule A S.X₂)
      have hEq :
          (Submodule.Quotient.mk ((S.moduleCatCyclesIso.hom z).1) :
              idealPowerModuleQuotient I S.X₂ n) =
            Submodule.Quotient.mk ((S.moduleCatToCycles a).1) := by
        simpa [ShortComplex.moduleCatToCycles] using hz_reduced
      simpa using (Submodule.Quotient.eq _).1 hEq
    have hrw_mem :
        r • w ∈ Submodule.comap (LinearMap.ker S.g.hom).subtype
          (I ^ (c + n + 1) • (⊤ : Submodule A S.X₂)) := by
      change r • w.1 ∈ I ^ (c + n + 1) • (⊤ : Submodule A S.X₂)
      have hw_val : w.1 ∈ I ^ (n + 1) • (⊤ : Submodule A S.X₂) := hw_mem
      simpa [pow_add, pow_succ, smul_smul, Nat.add_assoc, mul_assoc, mul_left_comm, mul_comm] using
        Submodule.smul_mem_smul hr hw_val
    have hrw_cycle :
        r • w ∈ I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom)) :=
      hcycles n hrw_mem
    have hrw_in_map :
        r • w ∈ Submodule.map S.moduleCatCyclesIso.hom.hom
          (I ^ (n + 1) • (⊤ : Submodule A S.cycles)) := by
      rw [moduleCatCyclesIso_map_cycle_pow_eq_pow (S := S) (I := I) (n := n)]
      exact hrw_cycle
    rcases Submodule.mem_map.1 hrw_in_map with ⟨q, hq, hqeq⟩
    let b : S.cycles := S.moduleCatCyclesIso.inv.hom (S.moduleCatToCycles a)
    have hq_repr : q = r • (z - b) := by
      have hinj : Function.Injective S.moduleCatCyclesIso.hom.hom :=
        (ModuleCat.mono_iff_injective S.moduleCatCyclesIso.hom).1 inferInstance
      apply hinj
      calc
        S.moduleCatCyclesIso.hom q = r • w := hqeq
        _ = r • (S.moduleCatCyclesIso.hom z - S.moduleCatCyclesIso.hom b) := by
            simp [w, b, moduleCatCyclesIso_hom_toCycles]
        _ = S.moduleCatCyclesIso.hom (r • (z - b)) := by
            simp [map_sub]
    have hb_zero : S.leftHomologyπ.hom b = 0 := by
      apply
        (shortComplex_leftHomologyπ_eq_zero_iff_exists_boundary (T := S) (q := b)).2
      refine ⟨a, ?_⟩
      simpa [b] using (S.moduleCatCyclesIso.inv_hom_id_apply (S.moduleCatToCycles a))
    have hq_homology :
        S.leftHomologyπ.hom q = r • S.leftHomologyπ.hom z := by
      calc
        S.leftHomologyπ.hom q = S.leftHomologyπ.hom (r • (z - b)) := by
          rw [hq_repr]
        _ = r • (S.leftHomologyπ.hom z - S.leftHomologyπ.hom b) := by
          simp
        _ = r • S.leftHomologyπ.hom z := by
          rw [hb_zero, sub_zero]
    have hq_stage :
        S.leftHomologyπ.hom q ∈ I ^ (n + 1) • (⊤ : Submodule A S.leftHomology) := by
      rw [← leftHomologyπ_map_cycle_pow_eq_pow (S := S) (I := I) (n := n)]
      exact Submodule.mem_map_of_mem S.leftHomologyπ.hom hq
    apply Subtype.ext
    change (Submodule.Quotient.mk (r • S.leftHomologyπ.hom z) :
        idealPowerModuleQuotient I S.leftHomology n) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    simpa [hq_homology] using hq_stage
  · exact bot_le

/-- Helper for Lemma 15.101.1: enlarging the annihilating ideal power preserves kernel
annihilation. -/
private theorem leftHomologyComparisonKernelAnnihilated_mono
    {c d n : ℕ} (hcd : c ≤ d)
    (hker : S.leftHomologyComparisonKernelAnnihilated I c n) :
    S.leftHomologyComparisonKernelAnnihilated I d n := by
  unfold leftHomologyComparisonKernelAnnihilated at hker ⊢
  apply le_antisymm
  · calc
      I ^ d •
          (⊤ :
            Submodule A
              ↥(LinearMap.ker (leftHomologyQuotientComparison S I n).hom)) ≤
        I ^ c •
          (⊤ :
            Submodule A
              ↥(LinearMap.ker (leftHomologyQuotientComparison S I n).hom)) := by
              simpa using
                (Submodule.pow_smul_top_le I
                  ↥(LinearMap.ker (leftHomologyQuotientComparison S I n).hom) hcd)
      _ = ⊥ := hker
  · exact bot_le

/-- Helper for Lemma 15.101.1: enlarging the annihilating ideal power preserves cokernel
annihilation. -/
private theorem leftHomologyComparisonCokernelAnnihilated_mono
    {c d n : ℕ} (hcd : c ≤ d)
    (hcok : S.leftHomologyComparisonCokernelAnnihilated I c n) :
    S.leftHomologyComparisonCokernelAnnihilated I d n := by
  unfold leftHomologyComparisonCokernelAnnihilated at hcok ⊢
  apply le_antisymm
  · calc
      I ^ d •
          (⊤ :
            Submodule A
              (S.idealPowerHomologyStage I n ⧸
                LinearMap.range (leftHomologyQuotientComparison S I n).hom)) ≤
        I ^ c •
          (⊤ :
            Submodule A
              (S.idealPowerHomologyStage I n ⧸
                LinearMap.range (leftHomologyQuotientComparison S I n).hom)) := by
              simpa using
                (Submodule.pow_smul_top_le I
                  (S.idealPowerHomologyStage I n ⧸
                    LinearMap.range (leftHomologyQuotientComparison S I n).hom) hcd)
      _ = ⊥ := hcok
  · exact bot_le

/-- Helper for Lemma 15.101.1: an ambient precycle and any cycle reduction determine the same raw
sup-quotient class modulo `I^(n+1)`. -/
private theorem ambient_precycle_to_sup_quotient_eq_cycle_reduction
    (S : ShortComplex Mod) (I : Ideal A) (c n : ℕ)
    (hcycles : ∀ n : ℕ,
      Submodule.comap S.g.hom (I ^ (c + n + 1) • (⊤ : Submodule A S.X₃)) ≤
        LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂))
    (x : S.ambientPrecycles I (c + n)) {z : LinearMap.ker S.g.hom}
    (hz : x.1 - z.1 ∈ I ^ (n + 1) • (⊤ : Submodule A S.X₂)) :
    ambient_precycle_to_sup_quotient (S := S) (I := I) (c := c) hcycles n x =
      cycles_to_ambient_precycle_sup_quotient (S := S) (I := I) n z := by
  -- Equality in the raw sup-quotient is exactly congruence modulo the denominator
  -- `I^(n+1) S.X₂`.
  exact (Submodule.Quotient.eq _).2 <| by
    change
      ((Submodule.inclusion (hcycles n) x : _).1 -
          (Submodule.inclusion
              (show LinearMap.ker S.g.hom ≤
                  LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂) from
                le_sup_left)
              z).1) ∈
        I ^ (n + 1) • (⊤ : Submodule A S.X₂)
    simpa using hz

/-- Helper for Lemma 15.101.1: the concrete cycle quotient model maps to
`H / I^(n+1) H` by applying the quotient map `ker(β) ↠ H` to cycle representatives. -/
private abbrev quotientModel_to_leftHomologyQuotientStage
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    ((LinearMap.ker S.g.hom) ⧸
      (LinearMap.range S.moduleCatToCycles ⊔
        I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom)))) →ₗ[A]
      idealPowerModuleQuotient I S.leftHomology n := by
  let D : Submodule A (LinearMap.ker S.g.hom) :=
    LinearMap.range S.moduleCatToCycles ⊔
      I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom))
  let Q : Submodule A S.leftHomology := I ^ (n + 1) • (⊤ : Submodule A S.leftHomology)
  have hD : D ≤ Submodule.comap S.leftHomologyπ.hom Q := by
    rw [leftHomologyQuotientStage_preimage_pow_eq_boundary_sup_pow (S := S) (I := I) n]
  exact Submodule.mapQ D Q S.leftHomologyπ.hom hD

/-- Helper for Lemma 15.101.1: the concrete quotient model computes on a cycle representative by
taking its homology class modulo `I^(n+1) H`. -/
private theorem quotientModel_to_leftHomologyQuotientStage_apply_mk
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) (z : LinearMap.ker S.g.hom) :
    quotientModel_to_leftHomologyQuotientStage (S := S) (I := I) n (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (S.leftHomologyπ.hom z) := by
  -- The descended map is the canonical quotient map induced by `S.leftHomologyπ`.
  simp [quotientModel_to_leftHomologyQuotientStage, Submodule.mapQ_apply]

/-- Helper for Lemma 15.101.1: the cycle quotient model maps into the quotient of the raw
sup-quotient by stage boundaries by forgetting to the ambient raw sup-quotient. -/
private abbrev quotientModel_to_sup_boundary_quotient
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (hcycles : ∀ n : ℕ,
      Submodule.comap S.g.hom (I ^ (c + n + 1) • (⊤ : Submodule A S.X₃)) ≤
        LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂))
    (n : ℕ) :
    ((LinearMap.ker S.g.hom) ⧸
      (LinearMap.range S.moduleCatToCycles ⊔
        I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom)))) →ₗ[A]
      ((ambient_precycle_sup_quotient_model S I n) ⧸
        sup_boundary_image (S := S) (I := I) (c := c) hcycles n) := by
  let D : Submodule A (LinearMap.ker S.g.hom) :=
    LinearMap.range S.moduleCatToCycles ⊔
      I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom))
  refine
    Submodule.liftQ D
      ((Submodule.mkQ (sup_boundary_image (S := S) (I := I) (c := c) hcycles n)).comp
        (cycles_to_ambient_precycle_sup_quotient (S := S) (I := I) n))
      ?_
  intro z hz
  rw [LinearMap.mem_ker]
  rw [Submodule.Quotient.mk_eq_zero]
  rcases Submodule.mem_sup.1 hz with ⟨b, hb, p, hp, rfl⟩
  have hb_mem :
      cycles_to_ambient_precycle_sup_quotient (S := S) (I := I) n b ∈
        sup_boundary_image (S := S) (I := I) (c := c) hcycles n := by
    let T : ShortComplex Mod := S.idealPowerQuotientStageComplex I (c + n)
    rcases LinearMap.mem_range.mp hb with ⟨a, rfl⟩
    -- Actual boundaries in the ambient cycle module map to the image of stage boundaries.
    refine Submodule.mem_map.2 ?_
    refine ⟨T.moduleCatToCycles (Submodule.Quotient.mk a), ?_, ?_⟩
    · exact LinearMap.mem_range.mpr ⟨Submodule.Quotient.mk a, rfl⟩
    · simpa [T] using
        stage_cycles_to_sup_quotient_on_boundary
          (S := S) (I := I) (c := c) hcycles n a
  have hp_zero :
      cycles_to_ambient_precycle_sup_quotient (S := S) (I := I) n p = 0 := by
    -- Elements of `I^(n+1) ker(S.g)` already vanish in the raw sup-quotient.
    rw [LinearMap.mem_ker]
    change
      (Submodule.mkQ
          ((I ^ (n + 1) • (⊤ : Submodule A S.X₂)).submoduleOf
            (LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂))))
          ((Submodule.inclusion
              (show LinearMap.ker S.g.hom ≤
                  LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂) from
                le_sup_left))
            p) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    change p.1 ∈ I ^ (n + 1) • (⊤ : Submodule A S.X₂)
    simpa using hp
  -- The boundary part lands in the quotient denominator, and the `I^(n+1)`-part already vanishes
  -- in the raw sup-quotient.
  have hsum :
      cycles_to_ambient_precycle_sup_quotient (S := S) (I := I) n (b + p) ∈
        sup_boundary_image (S := S) (I := I) (c := c) hcycles n := by
    rw [LinearMap.map_add, hp_zero, add_zero]
    exact hb_mem
  simpa using hsum

/-- Helper for Lemma 15.101.1: the transport from the concrete cycle quotient model to the
quotient of the raw sup-quotient computes on representatives by applying the raw quotient map. -/
private theorem quotientModel_to_sup_boundary_quotient_apply_mk
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (hcycles : ∀ n : ℕ,
      Submodule.comap S.g.hom (I ^ (c + n + 1) • (⊤ : Submodule A S.X₃)) ≤
        LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂))
    (n : ℕ) (z : LinearMap.ker S.g.hom) :
    quotientModel_to_sup_boundary_quotient
        (S := S) (I := I) (c := c) hcycles n (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk
        (cycles_to_ambient_precycle_sup_quotient (S := S) (I := I) n z) := by
  -- The quotient transport is the quotient lift of `cycles_to_ambient_precycle_sup_quotient`.
  simp [quotientModel_to_sup_boundary_quotient, Submodule.liftQ_apply]

/-- Helper for Lemma 15.101.1: two cycle representatives define the same quotient-model class once
their difference is deep enough for the Artin-Rees cycle-subtype bound to push it into
`I^(n+1) ker(S.g)`. -/
private theorem deep_cycle_eq_in_quotientModel
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (hcycleSubtype : ∀ n : ℕ,
      Submodule.comap (LinearMap.ker S.g.hom).subtype
        (I ^ (c + n + 1) • (⊤ : Submodule A S.X₂)) ≤
        I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom)))
    (n : ℕ) {z₁ z₂ : LinearMap.ker S.g.hom}
    (hdeep :
      z₁ - z₂ ∈
        Submodule.comap (LinearMap.ker S.g.hom).subtype
          (I ^ (c + n + 1) • (⊤ : Submodule A S.X₂))) :
    (Submodule.Quotient.mk z₁ :
        ((LinearMap.ker S.g.hom) ⧸
          (LinearMap.range S.moduleCatToCycles ⊔
            I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom))))) =
      Submodule.Quotient.mk z₂ := by
  -- The Artin-Rees bound upgrades the deep ambient error to the explicit denominator
  -- `I^(n+1) ker(S.g)` of the quotient model.
  apply ambient_precycle_reduction_eq_mod_boundary_sup_pow (S := S) (I := I) (n := n)
  have hshallow :
      z₁ - z₂ ∈ I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom)) :=
    hcycleSubtype n hdeep
  exact Submodule.mem_sup.2 ⟨0, by simp, z₁ - z₂, hshallow, by simp⟩

/-- Helper for Lemma 15.101.1: if one fixed ambient representative admits two buffered cycle
reductions with the same deep error bound, then those two reductions define the same class in the
quotient model `ker(S.g) / (im α + I^(n+1) ker(S.g))`. -/
private theorem ambient_precycle_buffered_reduction_eq_in_quotientModel
    (S : ShortComplex Mod) (I : Ideal A) (cK n : ℕ)
    (hcycleSubtype : ∀ n : ℕ,
      Submodule.comap (LinearMap.ker S.g.hom).subtype
        (I ^ (cK + n + 1) • (⊤ : Submodule A S.X₂)) ≤
        I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom)))
    {y : S.X₂} {z z' : LinearMap.ker S.g.hom}
    (hz : y - z.1 ∈ I ^ (cK + n + 1) • (⊤ : Submodule A S.X₂))
    (hz' : y - z'.1 ∈ I ^ (cK + n + 1) • (⊤ : Submodule A S.X₂)) :
    (Submodule.Quotient.mk z :
        ((LinearMap.ker S.g.hom) ⧸
          (LinearMap.range S.moduleCatToCycles ⊔
            I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom))))) =
      Submodule.Quotient.mk z' := by
  -- The two buffered reductions differ by a deep cycle error, so the cycle-subtype Artin-Rees
  -- bound pushes their difference into the denominator of `quotientModel n`.
  apply deep_cycle_eq_in_quotientModel (S := S) (I := I) (c := cK) hcycleSubtype n
  change z.1 - z'.1 ∈ I ^ (cK + n + 1) • (⊤ : Submodule A S.X₂)
  have hdiff : z.1 - z'.1 = (y - z'.1) - (y - z.1) := by
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  simpa [hdiff] using sub_mem hz' hz

/-- Helper for Lemma 15.101.1: keeping the three Artin-Rees buffers separate, an ambient
precycle at stage `cZ + cK + cB + 1 + n` admits a cycle reduction whose error already lands in
the deeper stage `I^(cK + cB + n + 2) X₂`. -/
private theorem ambient_precycle_has_buffered_cycle_reduction
    (S : ShortComplex Mod) (I : Ideal A) (cZ cK cB : ℕ)
    (hcycles : ∀ n : ℕ,
      Submodule.comap S.g.hom (I ^ (cZ + n + 1) • (⊤ : Submodule A S.X₃)) ≤
        LinearMap.ker S.g.hom ⊔ I ^ (n + 1) • (⊤ : Submodule A S.X₂))
    (n : ℕ) (x : S.ambientPrecycles I (cZ + cK + cB + 1 + n)) :
    ∃ z : LinearMap.ker S.g.hom,
      x.1 - z.1 ∈ I ^ (cK + cB + n + 2) • (⊤ : Submodule A S.X₂) := by
  -- The source proof spends the `cZ` buffer first, leaving the `cK + cB + 1` slack untouched
  -- for the later descent from cycles to homology.
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    ambient_precycle_has_cycle_reduction
      (S := S) (I := I) (c := cZ) hcycles (cK + cB + n + 1) x

/-- Helper for Lemma 15.101.1: two ambient precycles representing the same quotient-stage cycle
already differ by an element of the stage denominator upstairs. -/
private theorem ambient_precycles_eq_mod_pow_of_same_stage_cycle
    (S : ShortComplex Mod) (I : Ideal A) (m : ℕ)
    {q : LinearMap.ker ((S.idealPowerQuotientStageComplex I m).g.hom)}
    {y y' : S.ambientPrecycles I m}
    (hy : S.ambientPrecycleToStageCycles I m y = q)
    (hy' : S.ambientPrecycleToStageCycles I m y' = q) :
    y.1 - y'.1 ∈ I ^ (m + 1) • (⊤ : Submodule A S.X₂) := by
  have hEq :
      (Submodule.Quotient.mk y.1 : idealPowerModuleQuotient I S.X₂ m) =
        Submodule.Quotient.mk y'.1 := by
    -- Equality of stage cycles is equality of their quotient-module representatives in `S.X₂`.
    simpa [ambientPrecycleToStageCycles] using congrArg Subtype.val (hy.trans hy'.symm)
  simpa using (Submodule.Quotient.eq _).1 hEq

/-- Helper for Lemma 15.101.1: buffered cycle reductions of two ambient precycles representing the
same quotient-stage cycle define the same class in `ker(S.g) / (im α + I^(n+1) ker(S.g))`. -/
private theorem stage_cycles_buffered_reduction_eq_in_quotientModel
    (S : ShortComplex Mod) (I : Ideal A) (cZ cK cB n : ℕ)
    (hcycleSubtype : ∀ n : ℕ,
      Submodule.comap (LinearMap.ker S.g.hom).subtype
        (I ^ (cK + n + 1) • (⊤ : Submodule A S.X₂)) ≤
        I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom)))
    {q :
      LinearMap.ker
        ((S.idealPowerQuotientStageComplex I (cZ + cK + cB + 1 + n)).g.hom)}
    {y y' : S.ambientPrecycles I (cZ + cK + cB + 1 + n)}
    (hy :
      S.ambientPrecycleToStageCycles I (cZ + cK + cB + 1 + n) y = q)
    (hy' :
      S.ambientPrecycleToStageCycles I (cZ + cK + cB + 1 + n) y' = q)
    {z z' : LinearMap.ker S.g.hom}
    (hz : y.1 - z.1 ∈ I ^ (cK + cB + n + 2) • (⊤ : Submodule A S.X₂))
    (hz' : y'.1 - z'.1 ∈ I ^ (cK + cB + n + 2) • (⊤ : Submodule A S.X₂)) :
    (Submodule.Quotient.mk z :
        ((LinearMap.ker S.g.hom) ⧸
          (LinearMap.range S.moduleCatToCycles ⊔
            I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom))))) =
      Submodule.Quotient.mk z' := by
  have hyy' :
      y.1 - y'.1 ∈ I ^ (cZ + cK + cB + n + 2) • (⊤ : Submodule A S.X₂) := by
    -- Equality in the stage cycle object means the two ambient representatives differ by a deep
    -- quotient-denominator term upstairs.
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ambient_precycles_eq_mod_pow_of_same_stage_cycle
        (S := S) (I := I) (m := cZ + cK + cB + 1 + n) hy hy'
  have hyy'_shallow :
      y.1 - y'.1 ∈ I ^ (cK + cB + n + 2) • (⊤ : Submodule A S.X₂) := by
    -- The extra `cZ` depth can be dropped before comparing the two buffered reductions.
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (Submodule.pow_smul_top_le I S.X₂ (Nat.le_add_left (cK + cB + n + 2) cZ)) hyy'
  have hz'_from_y :
      y.1 - z'.1 ∈ I ^ (cK + cB + n + 2) • (⊤ : Submodule A S.X₂) := by
    -- Re-express the second reduction with the first ambient representative.
    have hsum : y.1 - z'.1 = (y.1 - y'.1) + (y'.1 - z'.1) := by
      abel
    simpa [hsum] using add_mem hyy'_shallow hz'
  -- Once both reductions are buffered reductions of the same ambient representative, the
  -- fixed-representative choice-independence lemma applies directly.
  exact ambient_precycle_buffered_reduction_eq_in_quotientModel
    (S := S) (I := I) (cK := cK) (n := n) hcycleSubtype
    (y := y.1) (z := z) (z' := z') hz hz'_from_y

/-- Helper for Lemma 15.101.1: the remaining source-faithful Artin-Rees work is to descend the
ambient-precycle reduction through quotient-stage cycles and homology, producing the shifted
comparison maps together with their quotient compatibility on `I^c`. -/
private theorem exists_shifted_comparison_of_artin_rees_bounds
    :
    ∃ c : ℕ, 0 < c ∧
      ∃ comparison :
        S.idealPowerHomologyShiftComparison I c,
          (∀ n : ℕ,
            S.leftHomologyQuotientComparison I (c + n) ≫ comparison.app (op n) =
              SequentialInverseSystem.transitionMap (S.leftHomologyQuotientTower I)
                (Nat.le_add_left n c)) ∧
          (∀ n : ℕ,
            ((comparison.app (op n)) :
                S.idealPowerHomologyStage I (c + n) ⟶
                  S.leftHomologyQuotientStage I n) ≫
              S.leftHomologyQuotientComparison I n =
                SequentialInverseSystem.transitionMap (S.idealPowerHomologyTower I)
                  (Nat.le_add_left n c)) ∧
          (∀ n : ℕ, S.idealPowerHomologyPowCompatibility I c comparison n) := by
  classical
  rcases exists_buffered_artin_rees_data_for_shifted_comparison (S := S) (I := I) with
    ⟨cZ, cK, cB, hcycles, hcycleSubtype, _hboundaries⟩
  let c : ℕ := cZ + cK + cB + 1
  let quotientModel (n : ℕ) :=
    ((LinearMap.ker S.g.hom) ⧸
      (LinearMap.range S.moduleCatToCycles ⊔
        I ^ (n + 1) • (⊤ : Submodule A (LinearMap.ker S.g.hom))))
  let bufferedReduction :
      ∀ n : ℕ, S.ambientPrecycles I (c + n) → LinearMap.ker S.g.hom :=
    fun n x ↦
      Classical.choose <| by
        simpa [c, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          ambient_precycle_has_buffered_cycle_reduction
            (S := S) (I := I) (cZ := cZ) (cK := cK) (cB := cB) hcycles n x
  let bufferedReduction_spec :
      ∀ n : ℕ, ∀ x : S.ambientPrecycles I (c + n),
        x.1 - (bufferedReduction n x).1 ∈
          I ^ (cK + cB + n + 2) • (⊤ : Submodule A S.X₂) :=
    fun n x ↦
      Classical.choose_spec <| by
        simpa [c, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          ambient_precycle_has_buffered_cycle_reduction
            (S := S) (I := I) (cZ := cZ) (cK := cK) (cB := cB) hcycles n x
  let ambientPrecycleToQuotientModel :
      ∀ n : ℕ, S.ambientPrecycles I (c + n) →ₗ[A] quotientModel n :=
    fun n ↦
      { toFun := fun x ↦ Submodule.Quotient.mk (bufferedReduction n x)
        map_add' := by
          intro x y
          have hxy :
              x.1 + y.1 - (bufferedReduction n (x + y)).1 ∈
                I ^ (cK + n + 1) • (⊤ : Submodule A S.X₂) := by
            have hdeep := bufferedReduction_spec n (x + y)
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              (Submodule.pow_smul_top_le I S.X₂ (Nat.le_add_left (cK + n + 1) (cB + 1))) hdeep
          have hx :
              x.1 - (bufferedReduction n x).1 ∈
                I ^ (cK + n + 1) • (⊤ : Submodule A S.X₂) := by
            have hdeep := bufferedReduction_spec n x
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              (Submodule.pow_smul_top_le I S.X₂ (Nat.le_add_left (cK + n + 1) (cB + 1))) hdeep
          have hy :
              y.1 - (bufferedReduction n y).1 ∈
                I ^ (cK + n + 1) • (⊤ : Submodule A S.X₂) := by
            have hdeep := bufferedReduction_spec n y
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              (Submodule.pow_smul_top_le I S.X₂ (Nat.le_add_left (cK + n + 1) (cB + 1))) hdeep
          have hsum :
              x.1 + y.1 - ((bufferedReduction n x).1 + (bufferedReduction n y).1) ∈
                I ^ (cK + n + 1) • (⊤ : Submodule A S.X₂) := by
            have hEq :
                x.1 + y.1 - ((bufferedReduction n x).1 + (bufferedReduction n y).1) =
                  (x.1 - (bufferedReduction n x).1) +
                    (y.1 - (bufferedReduction n y).1) := by
              abel
            simpa [hEq] using add_mem hx hy
          -- The two chosen cycle reductions of `x + y` define the same quotient-model class.
          exact ambient_precycle_buffered_reduction_eq_in_quotientModel
            (S := S) (I := I) (cK := cK) (n := n) hcycleSubtype
            (y := x.1 + y.1)
            (z := bufferedReduction n (x + y))
            (z' := bufferedReduction n x + bufferedReduction n y)
            hxy hsum
        map_smul' := by
          intro r x
          have hx :
              x.1 - (bufferedReduction n x).1 ∈
                I ^ (cK + n + 1) • (⊤ : Submodule A S.X₂) := by
            have hdeep := bufferedReduction_spec n x
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              (Submodule.pow_smul_top_le I S.X₂ (Nat.le_add_left (cK + n + 1) (cB + 1))) hdeep
          have hrx :
              r • x.1 - (bufferedReduction n (r • x)).1 ∈
                I ^ (cK + n + 1) • (⊤ : Submodule A S.X₂) := by
            have hdeep := bufferedReduction_spec n (r • x)
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              (Submodule.pow_smul_top_le I S.X₂ (Nat.le_add_left (cK + n + 1) (cB + 1))) hdeep
          have hscaled :
              r • x.1 - (r • bufferedReduction n x).1 ∈
                I ^ (cK + n + 1) • (⊤ : Submodule A S.X₂) := by
            have hEq : r • x.1 - (r • bufferedReduction n x).1 = r •
                (x.1 - (bufferedReduction n x).1) := by
              simp [smul_sub]
            simpa [hEq] using
              Submodule.smul_mem_smul (show r ∈ (⊤ : Ideal A) by simp) hx
          -- Scalar multiples preserve the chosen quotient-model class for the same ambient
          -- representative `r • x`.
          exact ambient_precycle_buffered_reduction_eq_in_quotientModel
            (S := S) (I := I) (cK := cK) (n := n) hcycleSubtype
            (y := r • x.1)
            (z := bufferedReduction n (r • x))
            (z' := r • bufferedReduction n x)
            hrx hscaled }
  have ambientPrecycleToQuotientModel_ker_le :
      ∀ n : ℕ,
        LinearMap.ker (S.ambientPrecycleToStageCycles I (c + n)) ≤
          LinearMap.ker (ambientPrecycleToQuotientModel n) := by
    intro n x hx
    rw [LinearMap.mem_ker] at hx ⊢
    change (Submodule.Quotient.mk (bufferedReduction n x) : quotientModel n) = 0
    have hxdeep :
        x.1 ∈ I ^ (c + n + 1) • (⊤ : Submodule A S.X₂) := by
      change (Submodule.Quotient.mk x.1 :
          idealPowerModuleQuotient I S.X₂ (c + n)) = 0 at hx
      exact (Submodule.Quotient.mk_eq_zero _).1 hx
    have hxshallow :
        x.1 ∈ I ^ (cK + n + 1) • (⊤ : Submodule A S.X₂) := by
      simpa [c, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Submodule.pow_smul_top_le I S.X₂ (Nat.le_add_left (cK + n + 1) (cZ + cB + 1))) hxdeep
    have hred :
        x.1 - (bufferedReduction n x).1 ∈ I ^ (cK + n + 1) • (⊤ : Submodule A S.X₂) := by
      have hdeep := bufferedReduction_spec n x
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Submodule.pow_smul_top_le I S.X₂ (Nat.le_add_left (cK + n + 1) (cB + 1))) hdeep
    have hzero :
        x.1 - (0 : LinearMap.ker S.g.hom).1 ∈ I ^ (cK + n + 1) • (⊤ : Submodule A S.X₂) := by
      simpa using hxshallow
    -- Zero is another buffered reduction of the same ambient precycle `x`, so the chosen
    -- quotient-model value vanishes.
    simpa using
      ambient_precycle_buffered_reduction_eq_in_quotientModel
        (S := S) (I := I) (cK := cK) (n := n) hcycleSubtype
        (y := x.1) (z := bufferedReduction n x) (z' := 0) hred hzero
  let stageCyclesToQuotientModel :
      ∀ n : ℕ, LinearMap.ker ((S.idealPowerQuotientStageComplex I (c + n)).g.hom) →ₗ[A]
        quotientModel n :=
    fun n ↦ by
      let f := S.ambientPrecycleToStageCycles I (c + n)
      let desc :
          (S.ambientPrecycles I (c + n) ⧸ LinearMap.ker f) →ₗ[A] quotientModel n :=
        Submodule.liftQ (LinearMap.ker f) (ambientPrecycleToQuotientModel n)
          (ambientPrecycleToQuotientModel_ker_le n)
      have hrange : LinearMap.range f = ⊤ := by
        rw [LinearMap.range_eq_top]
        exact S.ambientPrecycleToStageCycles_surjective I (c + n)
      let e :
          (S.ambientPrecycles I (c + n) ⧸ LinearMap.ker f) ≃ₗ[A]
            LinearMap.ker ((S.idealPowerQuotientStageComplex I (c + n)).g.hom) :=
        (f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange)).trans Submodule.topEquiv
      exact desc.comp e.symm.toLinearMap
  have stageCyclesToQuotientModel_apply_ambientPrecycle :
      ∀ n : ℕ, ∀ x : S.ambientPrecycles I (c + n),
        stageCyclesToQuotientModel n (S.ambientPrecycleToStageCycles I (c + n) x) =
          ambientPrecycleToQuotientModel n x := by
    intro n x
    let f := S.ambientPrecycleToStageCycles I (c + n)
    let desc :
        (S.ambientPrecycles I (c + n) ⧸ LinearMap.ker f) →ₗ[A] quotientModel n :=
      Submodule.liftQ (LinearMap.ker f) (ambientPrecycleToQuotientModel n)
        (ambientPrecycleToQuotientModel_ker_le n)
    have hrange : LinearMap.range f = ⊤ := by
      rw [LinearMap.range_eq_top]
      exact S.ambientPrecycleToStageCycles_surjective I (c + n)
    let e :
        (S.ambientPrecycles I (c + n) ⧸ LinearMap.ker f) ≃ₗ[A]
          LinearMap.ker ((S.idealPowerQuotientStageComplex I (c + n)).g.hom) :=
      (f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange)).trans Submodule.topEquiv
    change desc (e.symm (f x)) = ambientPrecycleToQuotientModel n x
    have hsymm : e.symm (f x) = Submodule.Quotient.mk x := by
      apply e.injective
      simp [e, f]
    rw [hsymm]
    simp [desc]
  have stageCyclesToQuotientModel_on_boundary :
      ∀ n : ℕ, ∀ a : S.X₁,
        let T : ShortComplex Mod := S.idealPowerQuotientStageComplex I (c + n)
        stageCyclesToQuotientModel n (T.moduleCatToCycles (Submodule.Quotient.mk a)) = 0 := by
    intro n a
    let T : ShortComplex Mod := S.idealPowerQuotientStageComplex I (c + n)
    let x : S.ambientPrecycles I (c + n) := by
      refine ⟨S.f.hom a, ?_⟩
      have hfg : S.g.hom (S.f.hom a) = 0 := by
        simpa using LinearMap.congr_fun (congrArg ModuleCat.Hom.hom S.zero) a
      simpa [hfg] using
        (show (0 : S.X₃) ∈ I ^ (c + n + 1) • (⊤ : Submodule A S.X₃) by simp)
    have hstage :
        S.ambientPrecycleToStageCycles I (c + n) x =
          T.moduleCatToCycles (Submodule.Quotient.mk a) := by
      apply Subtype.ext
      rfl
    rw [← hstage, stageCyclesToQuotientModel_apply_ambientPrecycle n x]
    change (Submodule.Quotient.mk (bufferedReduction n x) : quotientModel n) = 0
    have hred :
        x.1 - (bufferedReduction n x).1 ∈ I ^ (cK + n + 1) • (⊤ : Submodule A S.X₂) := by
      have hdeep := bufferedReduction_spec n x
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Submodule.pow_smul_top_le I S.X₂ (Nat.le_add_left (cK + n + 1) (cB + 1))) hdeep
    have hboundary :
        x.1 - (S.moduleCatToCycles a).1 ∈ I ^ (cK + n + 1) • (⊤ : Submodule A S.X₂) := by
      simp
    have hEq :
        (Submodule.Quotient.mk (bufferedReduction n x) : quotientModel n) =
          Submodule.Quotient.mk (S.moduleCatToCycles a) := by
      exact ambient_precycle_buffered_reduction_eq_in_quotientModel
        (S := S) (I := I) (cK := cK) (n := n) hcycleSubtype
        (y := x.1) (z := bufferedReduction n x) (z' := S.moduleCatToCycles a) hred hboundary
    rw [hEq, Submodule.Quotient.mk_eq_zero]
    exact le_sup_left (LinearMap.mem_range.mpr ⟨a, rfl⟩)
  let stageHomologyToQuotientModel :
      ∀ n : ℕ, S.idealPowerHomologyStage I (c + n) →ₗ[A] quotientModel n :=
    fun n ↦ by
      let T : ShortComplex Mod := S.idealPowerQuotientStageComplex I (c + n)
      change (LinearMap.ker T.g.hom ⧸ LinearMap.range T.moduleCatToCycles) →ₗ[A] quotientModel n
      refine Submodule.liftQ (LinearMap.range T.moduleCatToCycles) (stageCyclesToQuotientModel n) ?_
      intro x hx
      rcases LinearMap.mem_range.mp hx with ⟨a, rfl⟩
      simpa [T] using stageCyclesToQuotientModel_on_boundary n a
  have stageHomologyToQuotientModel_apply_ambientPrecycle :
      ∀ n : ℕ, ∀ x : S.ambientPrecycles I (c + n),
        let T : ShortComplex Mod := S.idealPowerQuotientStageComplex I (c + n)
        stageHomologyToQuotientModel n (T.leftHomologyπ.hom (S.ambientPrecycleToStageCycles I (c + n) x)) =
          Submodule.Quotient.mk (bufferedReduction n x) := by
    intro n x
    let T : ShortComplex Mod := S.idealPowerQuotientStageComplex I (c + n)
    change
      stageHomologyToQuotientModel n
          (T.leftHomologyπ.hom (S.ambientPrecycleToStageCycles I (c + n) x)) =
        Submodule.Quotient.mk (bufferedReduction n x)
    simp [stageHomologyToQuotientModel, stageCyclesToQuotientModel_apply_ambientPrecycle]
  let comparisonApp :
      ∀ n : ℕ, S.idealPowerHomologyStage I (c + n) ⟶ S.leftHomologyQuotientStage I n :=
    fun n ↦
      ModuleCat.ofHom <|
        (leftHomologyQuotientStage_iso_cycles_boundary_pow_quotient
          (S := S) (I := I) n).toLinearMap.comp (stageHomologyToQuotientModel n)
  let comparison : S.idealPowerHomologyShiftComparison I c :=
    NatTrans.ofOpSequence
      (fun n ↦ comparisonApp n)
      (fun n ↦ by
        ext x
        let T₁ : ShortComplex Mod := S.idealPowerQuotientStageComplex I (c + (n + 1))
        let T₀ : ShortComplex Mod := S.idealPowerQuotientStageComplex I (c + n)
        obtain ⟨q, rfl⟩ := (ModuleCat.epi_iff_surjective T₁.leftHomologyπ).1 inferInstance x
        obtain ⟨y, hy⟩ := S.ambientPrecycleToStageCycles_surjective I (c + (n + 1)) q
        have hy₀ :
            y.1 ∈ I ^ (c + n + 1) • (⊤ : Submodule A S.X₃) := by
          have hy₁ : y.1 ∈ S.ambientPrecycles I (c + (n + 1)) := y.2
          simpa [c, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hy₁
        let y₀ : S.ambientPrecycles I (c + n) := ⟨y.1, hy₀⟩
        have hstep :
            ((SequentialInverseSystem.stepMap (S.idealPowerHomologyTower I) (c + n)).hom)
                (T₁.leftHomologyπ.hom q) =
              T₀.leftHomologyπ.hom (S.ambientPrecycleToStageCycles I (c + n) y₀) := by
          have hq :
              ((SequentialInverseSystem.stepMap (S.idealPowerHomologyTower I) (c + n)).hom)
                  (T₁.leftHomologyπ.hom q) =
                T₀.leftHomologyπ.hom
                  (T₀.cyclesMap
                    (S.mapNatTrans (idealPowerQuotientTransitionNatTrans I (c + n))) q) := by
            simpa [idealPowerHomologyTower, idealPowerHomologyStep] using
              congrArg
                (fun f :
                  T₁.leftHomology ⟶ T₀.leftHomology ↦ f.hom (T₁.leftHomologyπ.hom q))
                (ShortComplex.homologyπ_naturality
                  (S.mapNatTrans (idealPowerQuotientTransitionNatTrans I (c + n))))
          have hcycles :
              T₀.cyclesMap
                  (S.mapNatTrans (idealPowerQuotientTransitionNatTrans I (c + n))) q =
                S.ambientPrecycleToStageCycles I (c + n) y₀ := by
            apply Subtype.ext
            simpa [idealPowerQuotientStageComplex, idealPowerQuotientFunctor, hy]
          simpa [hcycles] using hq
        rw [show
            (((comparison.app (op (n + 1))) ≫ S.leftHomologyQuotientStep I n).hom)
                (T₁.leftHomologyπ.hom q) =
              ((S.leftHomologyQuotientStep I n).hom
                (((comparison.app (op (n + 1))).hom) (T₁.leftHomologyπ.hom q))) by
              rfl]
        rw [show
            (((SequentialInverseSystem.stepMap (SequentialInverseSystem.shift
                (S.idealPowerHomologyTower I) c) n) ≫ comparison.app (op n)).hom)
                (T₁.leftHomologyπ.hom q) =
              ((comparison.app (op n)).hom
                (((SequentialInverseSystem.stepMap (S.idealPowerHomologyTower I) (c + n)).hom)
                  (T₁.leftHomologyπ.hom q))) by
              rfl]
        rw [stageHomologyToQuotientModel_apply_ambientPrecycle (n := n + 1) y]
        rw [stageHomologyToQuotientModel_apply_ambientPrecycle (n := n) y₀]
        rw [quotientModel_to_leftHomologyQuotientStage_apply_mk]
        rw [quotientModel_to_leftHomologyQuotientStage_apply_mk]
        have hEq :
            (Submodule.Quotient.mk (bufferedReduction (n + 1) y) : quotientModel n) =
              Submodule.Quotient.mk (bufferedReduction n y₀) := by
          have hleft :
              y.1 - (bufferedReduction (n + 1) y).1 ∈
                I ^ (cK + n + 1) • (⊤ : Submodule A S.X₂) := by
            have hdeep := bufferedReduction_spec (n + 1) y
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              (Submodule.pow_smul_top_le I S.X₂ (Nat.le_add_left (cK + n + 1) (cB + 2))) hdeep
          have hright :
              y₀.1 - (bufferedReduction n y₀).1 ∈
                I ^ (cK + n + 1) • (⊤ : Submodule A S.X₂) := by
            have hdeep := bufferedReduction_spec n y₀
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              (Submodule.pow_smul_top_le I S.X₂ (Nat.le_add_left (cK + n + 1) (cB + 1))) hdeep
          exact ambient_precycle_buffered_reduction_eq_in_quotientModel
            (S := S) (I := I) (cK := cK) (n := n) hcycleSubtype
            (y := y.1) (z := bufferedReduction (n + 1) y) (z' := bufferedReduction n y₀)
            hleft hright
        simpa [comparison, comparisonApp] using congrArg
          (quotientModel_to_leftHomologyQuotientStage (S := S) (I := I) n) hEq
  have hleft :
      ∀ n : ℕ,
        S.leftHomologyQuotientComparison I (c + n) ≫ comparison.app (op n) =
          SequentialInverseSystem.transitionMap (S.leftHomologyQuotientTower I)
            (Nat.le_add_left n c) := by
    intro n
    ext x
    obtain ⟨y, rfl⟩ :=
      Submodule.mkQ_surjective (I ^ (c + n + 1) • (⊤ : Submodule A S.leftHomology)) x
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective S.leftHomologyπ).1 inferInstance y
    let T : ShortComplex Mod := S.idealPowerQuotientStageComplex I (c + n)
    let φ : S ⟶ T := S.mapNatTrans (toIdealPowerQuotientNatTrans I (c + n))
    let x₀ : S.ambientPrecycles I (c + n) := by
      refine ⟨z.1, ?_⟩
      simpa using (show (0 : S.X₃) ∈ I ^ (c + n + 1) • (⊤ : Submodule A S.X₃) by simp)
    have hstage :
        (S.leftHomologyQuotientComparison I (c + n)).hom
            (Submodule.Quotient.mk (S.leftHomologyπ.hom z)) =
          T.leftHomologyπ.hom (S.ambientPrecycleToStageCycles I (c + n) x₀) := by
      have hq :
          (S.leftHomologyToIdealPowerStage I (c + n)).hom (S.leftHomologyπ.hom z) =
            T.leftHomologyπ.hom (T.cyclesMap φ z) := by
        simpa [leftHomologyToIdealPowerStage, T, φ] using
          congrArg
            (fun f : S.leftHomology ⟶ T.leftHomology ↦ f.hom (S.leftHomologyπ.hom z))
            (ShortComplex.homologyπ_naturality φ)
      have hmk :
          (S.leftHomologyQuotientComparison I (c + n)).hom
              (Submodule.Quotient.mk (S.leftHomologyπ.hom z)) =
            (S.leftHomologyToIdealPowerStage I (c + n)).hom (S.leftHomologyπ.hom z) := by
        simpa using
          congrArg
            (fun f : S.leftHomology ⟶ S.idealPowerHomologyStage I (c + n) ↦
              f.hom (S.leftHomologyπ.hom z))
            (leftHomologyQuotientComparison_comp_mkQ (S := S) (I := I) (c + n))
      have hcycles :
          T.cyclesMap φ z = S.ambientPrecycleToStageCycles I (c + n) x₀ := by
        apply Subtype.ext
        rfl
      simpa [hcycles] using hmk.trans hq
    have hred :
        (Submodule.Quotient.mk (bufferedReduction n x₀) : quotientModel n) =
          Submodule.Quotient.mk z := by
      have hx :
          x₀.1 - (bufferedReduction n x₀).1 ∈ I ^ (cK + n + 1) • (⊤ : Submodule A S.X₂) := by
        have hdeep := bufferedReduction_spec n x₀
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (Submodule.pow_smul_top_le I S.X₂ (Nat.le_add_left (cK + n + 1) (cB + 1))) hdeep
      have hz : x₀.1 - z.1 ∈ I ^ (cK + n + 1) • (⊤ : Submodule A S.X₂) := by
        simp
      exact ambient_precycle_buffered_reduction_eq_in_quotientModel
        (S := S) (I := I) (cK := cK) (n := n) hcycleSubtype
        (y := x₀.1) (z := bufferedReduction n x₀) (z' := z) hx hz
    change
      ((comparison.app (op n)).hom
          ((S.leftHomologyQuotientComparison I (c + n)).hom
            (Submodule.Quotient.mk (S.leftHomologyπ.hom z)))) =
        (((S.leftHomologyQuotientTower I).transitionMap (Nat.le_add_left n c)).hom
          (Submodule.Quotient.mk (S.leftHomologyπ.hom z)))
    rw [hstage, stageHomologyToQuotientModel_apply_ambientPrecycle (n := n) x₀]
    rw [quotientModel_to_leftHomologyQuotientStage_apply_mk]
    simpa [comparison, comparisonApp, c] using congrArg
      (quotientModel_to_leftHomologyQuotientStage (S := S) (I := I) n) hred
  have hright :
      ∀ n : ℕ,
        ((comparison.app (op n)) :
            S.idealPowerHomologyStage I (c + n) ⟶ S.leftHomologyQuotientStage I n) ≫
          S.leftHomologyQuotientComparison I n =
            SequentialInverseSystem.transitionMap (S.idealPowerHomologyTower I)
              (Nat.le_add_left n c) := by
    intro n
    ext x
    let T₁ : ShortComplex Mod := S.idealPowerQuotientStageComplex I (c + n)
    let T₀ : ShortComplex Mod := S.idealPowerQuotientStageComplex I n
    obtain ⟨q, rfl⟩ := (ModuleCat.epi_iff_surjective T₁.leftHomologyπ).1 inferInstance x
    obtain ⟨y, hy⟩ := S.ambientPrecycleToStageCycles_surjective I (c + n) q
    let y₀ : S.ambientPrecycles I n := by
      refine ⟨y.1, ?_⟩
      simpa [c, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Submodule.pow_smul_top_le I S.X₃ (Nat.le_add_left (n + 1) c)) y.2
    have hcomparison :
        ((comparison.app (op n)).hom) (T₁.leftHomologyπ.hom q) =
          Submodule.Quotient.mk (S.leftHomologyπ.hom (bufferedReduction n y)) := by
      rw [show q = S.ambientPrecycleToStageCycles I (c + n) y by simpa [hy]]
      rw [stageHomologyToQuotientModel_apply_ambientPrecycle (n := n) y]
      rw [quotientModel_to_leftHomologyQuotientStage_apply_mk]
      rfl
    have htransition :
        (((S.idealPowerHomologyTower I).transitionMap (Nat.le_add_left n c)).hom)
            (T₁.leftHomologyπ.hom q) =
          T₀.leftHomologyπ.hom (S.ambientPrecycleToStageCycles I n y₀) := by
      induction c with
      | zero =>
          simp [SequentialInverseSystem.transitionMap, y₀, T₀, T₁, c] at hy ⊢
      | succ c ih =>
          have hcomp :
              (S.idealPowerHomologyTower I).transitionMap
                  (Nat.le_add_left n (Nat.succ c)) =
                (S.idealPowerHomologyTower I).transitionMap (Nat.le_succ (n + c)) ≫
                  (S.idealPowerHomologyTower I).transitionMap (Nat.le_add_left n c) := by
            simpa [Nat.add_assoc] using
              transitionMap_comp
                (F := S.idealPowerHomologyTower I)
                (Nat.le_add_left n c) (Nat.le_succ (n + c))
          let Tm : ShortComplex Mod := S.idealPowerQuotientStageComplex I (n + c + 1)
          let ym : S.ambientPrecycles I (n + c) := by
            refine ⟨y.1, ?_⟩
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              (Submodule.pow_smul_top_le I S.X₃ (Nat.le_succ (n + c + 1))) y.2
          have hstep :
              ((S.idealPowerHomologyTower I).transitionMap (Nat.le_succ (n + c))).hom
                  (Tm.leftHomologyπ.hom
                    (S.ambientPrecycleToStageCycles I (n + c + 1) ⟨y.1, by simpa using y.2⟩)) =
                (S.idealPowerQuotientStageComplex I (n + c)).leftHomologyπ.hom
                  (S.ambientPrecycleToStageCycles I (n + c) ym) := by
            have hq' :
                ((SequentialInverseSystem.stepMap (S.idealPowerHomologyTower I) (n + c)).hom)
                    (Tm.leftHomologyπ.hom
                      (S.ambientPrecycleToStageCycles I (n + c + 1) ⟨y.1, by simpa using y.2⟩)) =
                  (S.idealPowerQuotientStageComplex I (n + c)).leftHomologyπ.hom
                    ((S.idealPowerQuotientStageComplex I (n + c)).cyclesMap
                      (S.mapNatTrans (idealPowerQuotientTransitionNatTrans I (n + c)))
                      (S.ambientPrecycleToStageCycles I (n + c + 1) ⟨y.1, by simpa using y.2⟩)) := by
              simpa [idealPowerHomologyTower, idealPowerHomologyStep] using
                congrArg
                  (fun f :
                    Tm.leftHomology ⟶ (S.idealPowerQuotientStageComplex I (n + c)).leftHomology ↦
                    f.hom
                      (Tm.leftHomologyπ.hom
                        (S.ambientPrecycleToStageCycles I (n + c + 1) ⟨y.1, by simpa using y.2⟩)))
                  (ShortComplex.homologyπ_naturality
                    (S.mapNatTrans (idealPowerQuotientTransitionNatTrans I (n + c))))
            have hcycle :
                (S.idealPowerQuotientStageComplex I (n + c)).cyclesMap
                    (S.mapNatTrans (idealPowerQuotientTransitionNatTrans I (n + c)))
                    (S.ambientPrecycleToStageCycles I (n + c + 1) ⟨y.1, by simpa using y.2⟩) =
                  S.ambientPrecycleToStageCycles I (n + c) ym := by
              apply Subtype.ext
              rfl
            simpa [SequentialInverseSystem.transitionMap, hcycle] using hq'
          change
            (((S.idealPowerHomologyTower I).transitionMap (Nat.le_succ (n + c))).hom
              ((((S.idealPowerHomologyTower I).transitionMap (Nat.le_add_left n c)).hom)
                (T₁.leftHomologyπ.hom q))) =
              T₀.leftHomologyπ.hom (S.ambientPrecycleToStageCycles I n y₀)
          rw [← Category.assoc, hcomp, ih]
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    have hred_stage :
        (S.leftHomologyToIdealPowerStage I n).hom (S.leftHomologyπ.hom (bufferedReduction n y)) =
          T₀.leftHomologyπ.hom (S.ambientPrecycleToStageCycles I n y₀) := by
      have hEq :
          (S.ambientPrecycleToStageCycles I n y₀ :
              LinearMap.ker T₀.g.hom) =
            S.ambientPrecycleToStageCycles I n
              ⟨(bufferedReduction n y).1, by
                simpa using (bufferedReduction n y).2⟩ := by
        apply Subtype.ext
        change
          (Submodule.Quotient.mk y₀.1 : idealPowerModuleQuotient I S.X₂ n) =
            Submodule.Quotient.mk (bufferedReduction n y).1
        have hmem :
            y₀.1 - (bufferedReduction n y).1 ∈ I ^ (n + 1) • (⊤ : Submodule A S.X₂) := by
          have hdeep := bufferedReduction_spec n y
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            (Submodule.pow_smul_top_le I S.X₂ (Nat.le_add_left (n + 1) (cK + cB + 1))) hdeep
        simpa using (Submodule.Quotient.eq _).2 hmem
      have hnat :=
        congrArg
          (fun f : S.leftHomology ⟶ T₀.leftHomology ↦ f.hom (S.leftHomologyπ.hom (bufferedReduction n y)))
          (ShortComplex.homologyπ_naturality
            (S.mapNatTrans (toIdealPowerQuotientNatTrans I n)))
      simpa [leftHomologyToIdealPowerStage, T₀, hEq] using hnat
    change
      (S.leftHomologyQuotientComparison I n).hom
          (((comparison.app (op n)).hom) (T₁.leftHomologyπ.hom q)) =
        (((S.idealPowerHomologyTower I).transitionMap (Nat.le_add_left n c)).hom)
          (T₁.leftHomologyπ.hom q)
    rw [hcomparison]
    rw [show
        (S.leftHomologyQuotientComparison I n).hom
            (Submodule.Quotient.mk (S.leftHomologyπ.hom (bufferedReduction n y))) =
          (S.leftHomologyToIdealPowerStage I n).hom
            (S.leftHomologyπ.hom (bufferedReduction n y)) by
          simpa using
            congrArg
              (fun f : S.leftHomology ⟶ S.idealPowerHomologyStage I n ↦
                f.hom (S.leftHomologyπ.hom (bufferedReduction n y)))
              (leftHomologyQuotientComparison_comp_mkQ (S := S) (I := I) n)]
    simpa [hred_stage] using htransition
  have hpow :
      ∀ n : ℕ, S.idealPowerHomologyPowCompatibility I c comparison n := by
    intro n
    unfold idealPowerHomologyPowCompatibility
    ext x
    -- The source proof checks the compatibility on the generators of `I^c H_{n+c+1}`.
    refine Submodule.smul_induction_on x.2 ?_ ?_
    · intro r hr y hy
      let T : ShortComplex Mod := S.idealPowerQuotientStageComplex I (c + n)
      obtain ⟨q, rfl⟩ := (ModuleCat.epi_iff_surjective T.leftHomologyπ).1 inferInstance y
      obtain ⟨a, ha⟩ := S.ambientPrecycleToStageCycles_surjective I (c + n) q
      have hcomp :
          (((comparison.app (op n)) ≫
              ModuleCat.ofHom
                ((S.leftHomologyToIdealPowerStage I (c + n)).hom.reduceModIdeal (I ^ (n + 1)))).hom)
              (r • T.leftHomologyπ.hom q) =
            (((ModuleCat.ofHom
                (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule A (S.idealPowerHomologyStage I (c + n)))))).hom)
              (r • T.leftHomologyπ.hom q)) := by
        have hred :
            a.1 - (bufferedReduction n a).1 ∈ I ^ (c + n + 1) • (⊤ : Submodule A S.X₂) := by
          have hbuf := bufferedReduction_spec n a
          have hrpow : r ∈ I ^ c := by simpa using hr
          have hscaled :
              r • (a.1 - (bufferedReduction n a).1) ∈
                I ^ (c + n + 1) • (⊤ : Submodule A S.X₂) := by
            simpa [c, pow_add, pow_succ, smul_smul, Nat.add_assoc, Nat.add_left_comm,
              Nat.add_comm, mul_assoc, mul_left_comm, mul_comm] using
              Submodule.smul_mem_smul hrpow hbuf
          exact hscaled
        have hEq :
            (Submodule.Quotient.mk (r • a.1) :
                idealPowerModuleQuotient I S.X₂ (c + n)) =
              Submodule.Quotient.mk (r • (bufferedReduction n a).1) := by
          simpa using (Submodule.Quotient.eq _).2 hred
        have hcycle :
            (S.leftHomologyToIdealPowerStage I (c + n)).hom
                (((comparison.app (op n)).hom) (r • T.leftHomologyπ.hom q)) =
              r • T.leftHomologyπ.hom q := by
          have hcmp :=
            congrArg
              (fun f :
                S.idealPowerHomologyStage I (c + n) ⟶
                  S.idealPowerHomologyStage I (c + n) ↦ f.hom (r • T.leftHomologyπ.hom q))
              (hright (n := c + n))
          simpa [comparison, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcmp
        -- The buffered reduction error is killed in stage `c + n`, hence also in its quotient
        -- modulo `I^(n+1)`.
        change
          Submodule.Quotient.mk
              ((S.leftHomologyToIdealPowerStage I (c + n)).hom
                (((comparison.app (op n)).hom) (r • T.leftHomologyπ.hom q))) =
            Submodule.Quotient.mk (r • T.leftHomologyπ.hom q)
        simpa [hcycle]
    · intro u v hu hv
      simpa using add_mem
        (I ^ c •
          (⊤ : Submodule A (S.idealPowerHomologyStage I (c + n))))
        hu hv
  exact ⟨c, Nat.succ_pos _, comparison, hleft, hright, hpow⟩

-- Proof sketch: Artin-Rees supplies a single positive constant `c` and canonical maps
-- `H_{n+c+1} ⟶ H / I^(n+1) H`. Their composites with the canonical quotient comparison maps
-- `H / I^(n+1) H ⟶ H_{n+1}` recover the transition morphisms in the quotient tower and in the
-- homology tower.
/-- Lemma 15.101.1 (1): there is a single positive constant `c` and a morphism of inverse systems
`((H_{n+1})_n).shift c ⟶ (H / I^(n+1) H)_n` whose stagewise maps
`H_{n+c+1} ⟶ H / I^(n+1) H` satisfy the two canonical composite identities with the canonical
comparison maps `H / I^(n+1) H ⟶ H_{n+1}`. -/
@[stacks 0EGU]
theorem exists_idealPowerHomologyComparison :
    ∃ c : ℕ, 0 < c ∧
      ∃ comparison :
        S.idealPowerHomologyShiftComparison I c,
        (∀ n : ℕ,
          S.leftHomologyQuotientComparison I (c + n) ≫ comparison.app (op n) =
            SequentialInverseSystem.transitionMap (S.leftHomologyQuotientTower I)
              (Nat.le_add_left n c)) ∧
          ∀ n : ℕ,
            ((comparison.app (op n)) :
                S.idealPowerHomologyStage I (c + n) ⟶
                  S.leftHomologyQuotientStage I n) ≫
              S.leftHomologyQuotientComparison I n =
              SequentialInverseSystem.transitionMap (S.idealPowerHomologyTower I)
                (Nat.le_add_left n c) := by
  -- The Artin-Rees constant is already frozen; the remaining work is the packaged stagewise
  -- descent provided by `exists_shifted_comparison_of_artin_rees_bounds`.
  rcases exists_shifted_comparison_of_artin_rees_bounds
      (S := S) (I := I) with
    ⟨c, hc, comparison, hleft, hright, hpow⟩
  exact ⟨c, hc, comparison, hleft, hright⟩

-- Proof sketch: the source-facing comparison data above produces a shift-by-`c` representative
-- `(H_{n+c+1})_n ⟶ (H / I^(n+1) H)_n`; the two composition identities show that this
-- representative has an inverse up to common refinement, hence determines an isomorphism between
-- the associated sequential pro-objects in `ModuleCat A`.
/-- Companion to Lemma 15.101.1 (1): the source-facing Artin-Rees comparison data induces an
isomorphism of the associated sequential pro-objects in `Mod_A`, expressed through the canonical
owner `SequentialProObjectMorphismRep.ofShiftNatTrans`. -/
theorem idealPowerHomologyTower_isProIsomorphic_to_leftHomologyQuotientTower :
    ∃ c : ℕ, 0 < c ∧
      ∃ comparison :
        S.idealPowerHomologyShiftComparison I c,
        (ofShiftNatTrans c comparison).IsProIsomorphism := by
  -- Extract the source-facing Artin-Rees comparison and package its two composite identities
  -- into the canonical pro-isomorphism witness.
  rcases exists_idealPowerHomologyComparison (S := S) (I := I) with
    ⟨c, hc, comparison, hleft, hright⟩
  refine ⟨c, hc, comparison, ?_⟩
  exact shifted_idealPowerHomology_comparison_isProIsomorphism
    (S := S) (I := I) c comparison hleft hright

-- Proof sketch: use the pro-object isomorphism from part `(1)` to obtain an isomorphism `η`
-- between the
-- associated sequential pro-objects in `ModuleCat A`, apply the owner theorem
-- `inducedLimitMap_isIso_of_isIso` to the canonical comparison on inverse limits, and package the
-- resulting canonical map as the corresponding object-level `IsIsomorphic` claim.
/-- Lemma 15.101.1 (2): the inverse limits of `(H_{n+1})_n` and `(H / I^(n+1) H)_n` are
isomorphic. -/
@[stacks 0EGU]
theorem limit_idealPowerHomologyTower_iso_limit_leftHomologyQuotientTower :
    IsIsomorphic (limit (S.idealPowerHomologyTower I)) (limit (S.leftHomologyQuotientTower I)) :=
  by
  rcases idealPowerHomologyTower_isProIsomorphic_to_leftHomologyQuotientTower
      (S := S) (I := I) with
    ⟨c, hc, comparison, hcomparison⟩
  let η := (ofShiftNatTrans c comparison).toProObjectHom
  have hηbij : ∀ X : Mod, Function.Bijective (η.app X) := fun X ↦
    SequentialProObjectMorphismRep.isProIsomorphism_toProObjectHom_app_bijective
      hcomparison X
  letI : ∀ X : Mod, IsIso (η.app X) := fun X ↦
    (CategoryTheory.isIso_iff_bijective (η.app X)).2 (hηbij X)
  have hη : IsIso η := NatIso.isIso_of_isIso_app η
  letI := hη
  let φ :
      limit (S.idealPowerHomologyTower I) ⟶ limit (S.leftHomologyQuotientTower I) :=
    CategoryTheory.inducedLimitMap η
  have hφ : IsIso φ := by
    simpa [φ] using CategoryTheory.inducedLimitMap_isIso_of_isIso η
  let _ := hφ
  exact ⟨asIso φ⟩

-- Proof sketch: the quotient tower `(H / I^(n+1) H)_n` is Mittag-Leffler, and a pro-isomorphic
-- tower is again Mittag-Leffler.
/-- Lemma 15.101.1 (3): the inverse system `(H_{n+1})_n` is Mittag-Leffler. -/
@[stacks 0EGU]
theorem idealPowerHomologyTower_isMittagLeffler :
    (S.idealPowerHomologyTower I).IsMittagLeffler := by
  rcases exists_image_stabilization_for_idealPowerHomologyTower (S := S) (I := I) with
    ⟨c, hc, himage⟩
  intro i
  refine ⟨i + c, Nat.le_add_right i c, ?_⟩
  intro k hk
  have hfactor :
      (S.idealPowerHomologyTower I).transitionMap ((Nat.le_add_right i c).trans hk) =
        (S.idealPowerHomologyTower I).transitionMap hk ≫
          (S.idealPowerHomologyTower I).transitionMap (Nat.le_add_right i c) := by
    simpa using transitionMap_comp
      (F := S.idealPowerHomologyTower I) (Nat.le_add_right i c) hk
  have hle₁ :
      imageSubobject
          ((S.idealPowerHomologyTower I).transitionMap ((Nat.le_add_right i c).trans hk)) ≤
        imageSubobject ((S.idealPowerHomologyTower I).transitionMap (Nat.le_add_right i c)) := by
    rw [hfactor]
    exact imageSubobject_comp_le _ _
  have hleftFactor :
      S.leftHomologyToIdealPowerStage I k ≫
          (S.idealPowerHomologyTower I).transitionMap ((Nat.le_add_right i c).trans hk) =
        S.leftHomologyToIdealPowerStage I i :=
    leftHomologyToIdealPowerStage_comp_transition
      (S := S) (I := I) ((Nat.le_add_right i c).trans hk)
  have hle₂ :
      imageSubobject ((S.idealPowerHomologyTower I).transitionMap (Nat.le_add_right i c)) ≤
        imageSubobject
          ((S.idealPowerHomologyTower I).transitionMap ((Nat.le_add_right i c).trans hk)) := by
    have hstage :
        imageSubobject ((S.idealPowerHomologyTower I).transitionMap (Nat.le_add_right i c)) =
          imageSubobject (S.leftHomologyToIdealPowerStage I i) := by
      simpa [idealPowerHomologyImageStabilizes] using himage i
    rw [hstage]
    rw [← hleftFactor]
    exact imageSubobject_comp_le _ _
  exact le_antisymm hle₁ hle₂

-- Proof sketch: use the common Artin-Rees constant from the auxiliary comparison theorem and the
-- factorization
-- `H_{n+c+1} ⟶ H / I^(n+1) H ⟶ H_{n+1}` to identify the stabilized image with the image of
-- `H ⟶ H_{n+1}`.
/-- Lemma 15.101.1 (4): after a fixed shift, the image of the transition map
`H_{n+c+1} ⟶ H_{n+1}` equals the image of the canonical map `H ⟶ H_{n+1}`. -/
@[stacks 0EGU]
theorem exists_image_stabilization_for_idealPowerHomologyTower :
    ∃ c : ℕ, 0 < c ∧
      ∀ n : ℕ, S.idealPowerHomologyImageStabilizes I c n :=
  by
  rcases exists_idealPowerHomologyComparison (S := S) (I := I) with
    ⟨c, hc, comparison, hleft, hright⟩
  refine ⟨c, hc, ?_⟩
  intro n
  have hproof :
      Nat.le_add_right n c = Nat.le_add_left n c := by
    apply Subsingleton.elim
  have hcomparison_epi :
      Function.Surjective
        (((comparison.app (op n)) :
          S.idealPowerHomologyStage I (c + n) ⟶ S.leftHomologyQuotientStage I n).hom) := by
    intro x
    obtain ⟨y, hy⟩ := idealPowerTransition_surjective (I := I) (M := S.leftHomology)
      (Nat.le_add_left n c) x
    refine ⟨(S.leftHomologyQuotientComparison I (c + n)).hom y, ?_⟩
    -- The left comparison identity computes `comparison.app (op n)` on the chosen quotient
    -- representative.
    have hxy := congrArg
      (fun f :
        S.leftHomologyQuotientStage I (c + n) ⟶ S.leftHomologyQuotientStage I n ↦ f.hom y)
      (hleft n)
    simpa [hy] using hxy
  have hmkQ_epi :
      Epi
        (ModuleCat.ofHom
          (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule A S.leftHomology))) :
            S.leftHomology ⟶ S.leftHomologyQuotientStage I n) := by
    apply (ModuleCat.epi_iff_surjective _).2
    intro x
    exact Submodule.mkQ_surjective _ x
  letI :
      Epi ((comparison.app (op n)) :
        S.idealPowerHomologyStage I (c + n) ⟶ S.leftHomologyQuotientStage I n) :=
    (ModuleCat.epi_iff_surjective _).2 hcomparison_epi
  -- The shifted comparison has epi source, so its image agrees with the image of the canonical
  -- quotient comparison.
  unfold idealPowerHomologyImageStabilizes
  calc
    imageSubobject ((S.idealPowerHomologyTower I).transitionMap (Nat.le_add_right n c)) =
        imageSubobject
          ((((comparison.app (op n)) :
              S.idealPowerHomologyStage I (c + n) ⟶
                S.leftHomologyQuotientStage I n)) ≫
            S.leftHomologyQuotientComparison I n) := by
              simpa [hproof] using congrArg imageSubobject (hright n).symm
    _ = imageSubobject (S.leftHomologyQuotientComparison I n) := by
      simpa using imageSubobject_comp_eq_of_epi
        (((comparison.app (op n)) :
          S.idealPowerHomologyStage I (c + n) ⟶ S.leftHomologyQuotientStage I n))
        (S.leftHomologyQuotientComparison I n)
    _ = imageSubobject (S.leftHomologyToIdealPowerStage I n) := by
      rw [← leftHomologyQuotientComparison_comp_mkQ (S := S) (I := I) n]
      simpa using imageSubobject_comp_eq_of_epi
        (ModuleCat.ofHom
          (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule A S.leftHomology))) :
            S.leftHomology ⟶ S.leftHomologyQuotientStage I n)
        (S.leftHomologyQuotientComparison I n)

-- Proof sketch: extract the common Artin-Rees constant `c` and the canonical maps
-- `H / I^(n+1) H ⟶ H_{n+1}` from the auxiliary comparison theorem, then read off the annihilation
-- of the kernel and cokernel from the corresponding fields of the comparison data.
/-- Lemma 15.101.1 (5): for a single positive constant `c`, the kernel and cokernel of the
canonical comparison maps `H / I^(n+1) H ⟶ H_{n+1}` are annihilated by `I^c`. -/
@[stacks 0EGU]
theorem exists_kernel_cokernel_annihilation_for_leftHomologyComparison :
    ∃ c : ℕ, 0 < c ∧
      (∀ n : ℕ, S.leftHomologyComparisonKernelAnnihilated I c n) ∧
      (∀ n : ℕ, S.leftHomologyComparisonCokernelAnnihilated I c n) :=
  by
  rcases exists_idealPowerHomologyComparison (S := S) (I := I) with
    ⟨cC, hcC, comparison, hleft, hright⟩
  rcases exists_cycle_subtype_artin_rees_shift (S := S) (I := I) with
    ⟨cK, hcycles⟩
  refine ⟨cC + cK, lt_of_lt_of_le hcC (Nat.le_add_right cC cK), ?_, ?_⟩
  · intro n
    -- Route correction: kernel annihilation is proved directly from Artin-Rees on the cycle
    -- inclusion `ker(S.g) ↪ S.X₂`, then enlarged to the common comparison shift.
    exact leftHomologyComparisonKernelAnnihilated_mono
      (S := S) (I := I) (n := n) (Nat.le_add_left cC cK)
      (leftHomologyComparison_kernel_annihilated_of_cycle_subtype_bound
        (S := S) (I := I) cK hcycles n)
  · intro n
    exact leftHomologyComparisonCokernelAnnihilated_mono
      (S := S) (I := I) (n := n) (Nat.le_add_right cC cK)
      (leftHomologyComparison_cokernel_annihilated_of_comparison
        (S := S) (I := I) cC comparison hright n)

-- Proof sketch: the shifted maps `H_{n+c+1} ⟶ H / I^(n+1) H` from the auxiliary comparison
-- theorem restrict on
-- `I^c H_{n+c+1}` to the same map as the canonical quotient
-- `I^c H_{n+c+1} ↪ H_{n+c+1} ↠ H_{n+c+1} / I^(n+1) H_{n+c+1}`.
/-- Lemma 15.101.1 (6): for a single positive constant `c`, the comparison maps
`H_{n+c+1} ⟶ H / I^(n+1) H`, assembled as a morphism of inverse systems
`((H_{n+1})_n).shift c ⟶ (H / I^(n+1) H)_n`, agree on `I^c H_{n+c+1}` with the canonical
quotient map to
`H_{n+c+1} / I^(n+1) H_{n+c+1}` after composing with the canonical map
`H / I^(n+1) H ⟶ H_{n+c+1} / I^(n+1) H_{n+c+1}`. -/
@[stacks 0EGU]
theorem exists_pow_compatibility_for_idealPowerHomologyComparison :
    ∃ c : ℕ, 0 < c ∧
      ∃ comparison :
        S.idealPowerHomologyShiftComparison I c,
        ∀ n : ℕ, S.idealPowerHomologyPowCompatibility I c comparison n :=
  by
  -- The same stagewise descent package records the `I^c`-compatibility formula explicitly.
  rcases exists_shifted_comparison_of_artin_rees_bounds
      (S := S) (I := I) with
    ⟨c, hc, comparison, hleft, hright, hpow⟩
  exact ⟨c, hc, comparison, hpow⟩

end

end Comparison

end CategoryTheory.ShortComplex

end
