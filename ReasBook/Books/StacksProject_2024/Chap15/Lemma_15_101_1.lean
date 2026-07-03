import Mathlib
import Mathlib.CategoryTheory.Functor.OfSequence
import StacksProject_2024.Chap04.Example_4_22_6
import StacksProject_2024.Chap12.Definition_12_31_2
import StacksProject_2024.Chap15.Lemma_15_87_4
import StacksProject_2024.Chap15.Lemma_15_98_6_Koll_r_Kov_cs

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

-- Proof sketch: the map on homology induced by reduction modulo `I^(n+1)` kills
-- `I^(n+1) H`, so it descends canonically to the quotient `H / I^(n+1) H`.
private theorem leftHomologyToIdealPowerStage_condition
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    I ^ (n + 1) • (⊤ : Submodule A S.leftHomology) ≤
      LinearMap.ker (S.leftHomologyToIdealPowerStage I n).hom := sorry

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
      S.leftHomologyToIdealPowerStage I n := sorry

section

variable [IsNoetherianRing A]
variable [Module.Finite A S.X₁] [Module.Finite A S.X₂] [Module.Finite A S.X₃]

-- Proof sketch: Artin-Rees supplies a single positive constant `c` and canonical maps
-- `H_{n+c+1} ⟶ H / I^(n+1) H`. Their composites with the canonical quotient comparison maps
-- `H / I^(n+1) H ⟶ H_{n+1}` recover the transition morphisms in the quotient tower and in the
-- homology tower.
/-- Lemma 15.101.1 (1): there is a single positive constant `c` and a morphism of inverse systems
`((H_{n+1})_n).shift c ⟶ (H / I^(n+1) H)_n` whose stagewise maps
`H_{n+c+1} ⟶ H / I^(n+1) H` satisfy the two canonical composite identities with the canonical
comparison maps `H / I^(n+1) H ⟶ H_{n+1}`. -/
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
                (Nat.le_add_left n c) := sorry

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
        (ofShiftNatTrans c comparison).IsProIsomorphism := sorry

-- Proof sketch: use the pro-object isomorphism from part `(1)` to obtain an isomorphism `η`
-- between the
-- associated sequential pro-objects in `ModuleCat A`, apply the owner theorem
-- `inducedLimitMap_isIso_of_isIso` to the canonical comparison on inverse limits, and package the
-- resulting canonical map as the corresponding object-level `IsIsomorphic` claim.
/-- Lemma 15.101.1 (2): the inverse limits of `(H_{n+1})_n` and `(H / I^(n+1) H)_n` are
isomorphic. -/
theorem limit_idealPowerHomologyTower_iso_limit_leftHomologyQuotientTower :
    IsIsomorphic (limit (S.idealPowerHomologyTower I)) (limit (S.leftHomologyQuotientTower I)) :=
  sorry

-- Proof sketch: the quotient tower `(H / I^(n+1) H)_n` is Mittag-Leffler, and a pro-isomorphic
-- tower is again Mittag-Leffler.
/-- Lemma 15.101.1 (3): the inverse system `(H_{n+1})_n` is Mittag-Leffler. -/
theorem idealPowerHomologyTower_isMittagLeffler :
    (S.idealPowerHomologyTower I).IsMittagLeffler := sorry

-- Proof sketch: use the common Artin-Rees constant from the auxiliary comparison theorem and the
-- factorization
-- `H_{n+c+1} ⟶ H / I^(n+1) H ⟶ H_{n+1}` to identify the stabilized image with the image of
-- `H ⟶ H_{n+1}`.
/-- Lemma 15.101.1 (4): after a fixed shift, the image of the transition map
`H_{n+c+1} ⟶ H_{n+1}` equals the image of the canonical map `H ⟶ H_{n+1}`. -/
theorem exists_image_stabilization_for_idealPowerHomologyTower :
    ∃ c : ℕ, 0 < c ∧
      ∀ n : ℕ, S.idealPowerHomologyImageStabilizes I c n := sorry

-- Proof sketch: extract the common Artin-Rees constant `c` and the canonical maps
-- `H / I^(n+1) H ⟶ H_{n+1}` from the auxiliary comparison theorem, then read off the annihilation
-- of the kernel and cokernel from the corresponding fields of the comparison data.
/-- Lemma 15.101.1 (5): for a single positive constant `c`, the kernel and cokernel of the
canonical comparison maps `H / I^(n+1) H ⟶ H_{n+1}` are annihilated by `I^c`. -/
theorem exists_kernel_cokernel_annihilation_for_leftHomologyComparison :
    ∃ c : ℕ, 0 < c ∧
      (∀ n : ℕ, S.leftHomologyComparisonKernelAnnihilated I c n) ∧
      (∀ n : ℕ, S.leftHomologyComparisonCokernelAnnihilated I c n) := sorry

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
theorem exists_pow_compatibility_for_idealPowerHomologyComparison :
    ∃ c : ℕ, 0 < c ∧
      ∃ comparison :
        S.idealPowerHomologyShiftComparison I c,
        ∀ n : ℕ, S.idealPowerHomologyPowCompatibility I c comparison n := sorry

end

end Comparison

end CategoryTheory.ShortComplex

end
