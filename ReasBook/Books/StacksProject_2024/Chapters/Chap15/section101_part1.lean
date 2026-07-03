import Mathlib
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Quotient
import Mathlib.Data.PNat.Basic
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_101_1 (from Chap15) -/
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

/-! ### Lemma_15_101_2 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)

/- Domain-style sampling for Lemma 15.101.2:
- primary domain: pseudo-coherent derived `A`-complexes, the ideal-power quotient-tensor homology
  tower, and its completion comparison;
- sampled owner declarations:
  `DerivedCategory.IsPseudoCoherent`,
  `isPseudoCoherent_iff_boundedAbove_and_homology_finite`,
  `idealPowerQuotientTensorHomologyInverseSystem`,
  `homology_idealPowerQuotient_limit_iso_tensorQuotient_homology_limit`;
- best owner abstraction:
  `source-facing`: the Mittag-Leffler property of the tower `(H^i(K_n))_n`;
  `core/canonical`: the tower owner
    `idealPowerQuotientTensorHomologyInverseSystem I K i` and the completion-limit comparison from
    Lemma `15.98.6`;
  `bridge/view`: the finite-cohomology consequence of pseudo-coherence from Lemma `15.65.17`,
    used only to specialize the canonical comparison theorem.
- primitive vs. derived:
  primitive data are the ideal `I`, the pseudo-coherent derived object `K`, and the degree `i`;
  derived API is the Mittag-Leffler assertion for the canonical tower and the resulting canonical
  comparison from the `I`-adic completion of `H^i(K)` to the inverse limit of that tower. -/

-- Proof sketch: by Lemma `15.65.17`, pseudo-coherence over the Noetherian ring `A` implies that
-- each cohomology module `H^j(K)` is finite. Represent `K` by a bounded-above complex of finite
-- free modules; then the tower `K_n = K ⊗_A^L A / I^(n+1)` is represented degreewise by quotient
-- complexes modulo `I^(n+1)`, so Lemma `15.101.1` gives the Mittag-Leffler property for both
-- `H^{i-1}(K_n)` and `H^i(K_n)`. Finally apply Lemma `15.98.6` using the degree-`i - 1`
-- hypothesis to identify the inverse limit of
-- `H^i(K) / I^(n+1) H^i(K)` with the inverse limit of `H^i(K_n)`.
theorem idealPowerQuotientTensorHomology_isMittagLeffler_of_isPseudoCoherent
    (I : Ideal A) (K : DMod) (hK : K.IsPseudoCoherent) (i : ℤ) :
    (idealPowerQuotientTensorHomologyInverseSystem I K i).IsMittagLeffler := by
  sorry

/-- Lemma 15.101.2: let `I` be an ideal of the Noetherian ring `A`, let `K ∈ D(A)` be
pseudo-coherent, and for each `n` set `K_n = K \otimes_A^{\mathbf L} A / I^(n+1)`. Then for every
`i : ℤ` the inverse system `(H^i(K_n))_n` is Mittag-Leffler, and the inverse limit of the
quotients `H^i(K) / I^(n+1) H^i(K)` is canonically isomorphic to the inverse limit of
`(H^i(K_n))_n`; equivalently, the `I`-adic completion of `H^i(K)` is canonically isomorphic to
that inverse limit. Lean starts the tower at `n = 0`, corresponding to the textbook power `I^1`.
-/
theorem idealPowerQuotientTensorHomology_isMittagLeffler_and_limit_iso_of_isPseudoCoherent
    (I : Ideal A) (K : DMod) (hK : K.IsPseudoCoherent) (i : ℤ) :
    (idealPowerQuotientTensorHomologyInverseSystem I K i).IsMittagLeffler ∧
      IsIsomorphic
        (ModuleCat.of A (AdicCompletion I ((H i).obj K)))
        (limit (idealPowerQuotientTensorHomologyInverseSystem I K i)) := by
  have hKfinite : ∀ j : ℤ, Module.Finite A ((H j).obj K) :=
    (isPseudoCoherent_iff_boundedAbove_and_homology_finite K).1 hK |>.2
  refine ⟨idealPowerQuotientTensorHomology_isMittagLeffler_of_isPseudoCoherent I K hK i, ?_⟩
  exact homology_idealPowerQuotient_limit_iso_tensorQuotient_homology_limit I K i hKfinite
    (idealPowerQuotientTensorHomology_isMittagLeffler_of_isPseudoCoherent I K hK (i - 1))

end

/-! ### Lemma_15_101_3 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape
open CochainComplex
open Opposite
open SequentialProObjectMorphismRep

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
local notation "KMod" => HomotopyCategory (ModuleCat A) (up ℤ)
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "Qh" => (DerivedCategory.Qh : KMod ⥤ DMod)
local notation "singleCpx0" => CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)
private abbrev Q : CpxA ⥤ DMod := DerivedCategory.Q

private noncomputable instance : (Q : CpxA ⥤ DMod).Monoidal := by
  change
    (((HomotopyCategory.quotient (ModuleCat A) (up ℤ)) ⋙ Qh)).Monoidal
  infer_instance
 
/- 
Domain-style sampling for Lemma 15.101.3:
- primary domain: sequential inverse systems in `D(A)` built from ideal-power quotients of a
  bounded cochain complex and compared through `SequentialProObjectMorphismRep`;
- sampled owner declarations:
  `idealPowerQuotientDerivedInverseSystem`,
  `idealPowerQuotientTensorDerivedInverseSystem`,
  `reduceModIdealA`,
  `SequentialProObjectMorphismRep.toProObjectHom`;
- best owner abstraction:
  `source-facing`: the quotient-complex tower
    `(M^• / I^(n+1) M^•)_n` in `D(A)` and the resulting pro-isomorphism statement;
  `core/canonical`: `idealPowerQuotientDerivedInverseSystem`,
    `idealPowerQuotientTensorDerivedInverseSystem`, `reduceModIdealA`,
    `DerivedCategory.Q.map`, `Functor.ofOpSequence`, and `SequentialProObjectMorphismRep`;
  `bridge/view`: the quotient-complex transition maps assembling the target tower below.

Primitive-vs-derived split:
- primitive data: the ideal `I`, the cochain complex `M`, and the quotient-complex transition maps
  induced by `AdicCompletion.transitionMap`;
- derived API: the chapter owner `idealPowerQuotientDerivedInverseSystem`, its tensor image in
  `D(A)`, the canonical quotient-complex owner `reduceModIdealA`, the inverse system below, and
  the induced pro-object isomorphism.
-/

/-- The quotient complex `M^\bullet / I^(n+1) M^\bullet`, expressed through the chapter owner
`CochainComplex.reduceModIdealA`. -/
private abbrev idealPowerQuotientComplex
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    CpxA :=
  reduceModIdealA (I ^ (n + 1)) M

private abbrev idealPowerQuotientComplexStep
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerQuotientComplex I M (n + 1) ⟶ idealPowerQuotientComplex I M n :=
  { f := fun i ↦
      show ModuleCat.of A (idealPowerModuleQuotient I (M.X i) (n + 1)) ⟶
          ModuleCat.of A (idealPowerModuleQuotient I (M.X i) n) from
        ModuleCat.ofHom (AdicCompletion.transitionMap I (M.X i) (Nat.le_succ (n + 1)))
    comm' := fun i j hij ↦ by
      sorry }

private abbrev idealPowerQuotientComplexDerivedStage
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    DMod :=
  Q.obj (idealPowerQuotientComplex I M n)

/-- The inverse-system step on the derived quotient-complex tower. -/
private abbrev idealPowerQuotientComplexDerivedStep
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerQuotientComplexDerivedStage I M (n + 1) ⟶
      idealPowerQuotientComplexDerivedStage I M n :=
  Q.map (idealPowerQuotientComplexStep I M n)

/-- The inverse system `(M^\bullet / I^(n+1) M^\bullet)_n` in `D(A)`. -/
abbrev idealPowerQuotientComplexDerivedInverseSystem
    (I : Ideal A) (M : CpxA) :
    ℕᵒᵖ ⥤ DMod :=
  Functor.ofOpSequence (idealPowerQuotientComplexDerivedStep I M)

private abbrev idealPowerQuotientTensorComplexFunctor
    (I : Ideal A) (n : ℕ) : CpxA ⥤ CpxA :=
  (tensorLeft (ModuleCat.of A (A ⧸ I ^ (n + 1)))).mapHomologicalComplex (up ℤ)

private abbrev idealPowerQuotientTensorComplex
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    CpxA :=
  (idealPowerQuotientTensorComplexFunctor I n).obj M

private abbrev idealPowerQuotientTensorStepNatTrans
    (I : Ideal A) (n : ℕ) :
    tensorLeft (ModuleCat.of A (A ⧸ I ^ (n + 2))) ⟶
      tensorLeft (ModuleCat.of A (A ⧸ I ^ (n + 1))) :=
  (tensoringLeft (ModuleCat A)).map
    (ModuleCat.ofHom
      ((Ideal.Quotient.factorₐ A
          (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))).toLinearMap))

private abbrev idealPowerQuotientTensorComplexStepNatTrans
    (I : Ideal A) (n : ℕ) :
    idealPowerQuotientTensorComplexFunctor I (n + 1) ⟶
      idealPowerQuotientTensorComplexFunctor I n :=
  NatTrans.mapHomologicalComplex (idealPowerQuotientTensorStepNatTrans I n) (up ℤ)

private abbrev idealPowerQuotientTensorComplexStep
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerQuotientTensorComplex I M (n + 1) ⟶
      idealPowerQuotientTensorComplex I M n :=
  (idealPowerQuotientTensorComplexStepNatTrans I n).app M

private abbrev idealPowerQuotientTensorComplexDerivedStage
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    DMod :=
  Q.obj (idealPowerQuotientTensorComplex I M n)

private abbrev idealPowerQuotientTensorComplexDerivedStep
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerQuotientTensorComplexDerivedStage I M (n + 1) ⟶
      idealPowerQuotientTensorComplexDerivedStage I M n :=
  Q.map (idealPowerQuotientTensorComplexStep I M n)

private abbrev idealPowerQuotientTensorComplexDerivedInverseSystem
    (I : Ideal A) (M : CpxA) :
    ℕᵒᵖ ⥤ DMod :=
  Functor.ofOpSequence (idealPowerQuotientTensorComplexDerivedStep I M)

private abbrev idealPowerQuotientTensorComplexToQuotientComplex
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerQuotientTensorComplex I M n ⟶ idealPowerQuotientComplex I M n :=
  { f := fun i ↦
      show ModuleCat.of A (TensorProduct A (A ⧸ I ^ (n + 1)) (M.X i)) ⟶
          ModuleCat.of A (idealPowerModuleQuotient I (M.X i) n) from
        ModuleCat.ofHom
          (TensorProduct.quotTensorEquivQuotSMul (M.X i) (I ^ (n + 1))).toLinearMap
    comm' := fun i j hij ↦ by
      sorry }

private theorem idealPowerQuotientTensorComplexToQuotientComplex_step_comm
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerQuotientTensorComplexStep I M n ≫
        idealPowerQuotientTensorComplexToQuotientComplex I M n =
      idealPowerQuotientTensorComplexToQuotientComplex I M (n + 1) ≫
        idealPowerQuotientComplexStep I M n := by
  sorry

private abbrev idealPowerQuotientTensorComplexToQuotientComplexNatTrans
    (I : Ideal A) (M : CpxA) :
    idealPowerQuotientTensorComplexDerivedInverseSystem I M ⟶
      idealPowerQuotientComplexDerivedInverseSystem I M :=
  NatTrans.ofOpSequence
    (fun n ↦ Q.map (idealPowerQuotientTensorComplexToQuotientComplex I M n))
    (fun n ↦ by
      simpa [idealPowerQuotientTensorComplexDerivedStep] using
        congrArg Q.map
          (idealPowerQuotientTensorComplexToQuotientComplex_step_comm I M n))

private theorem idealPowerQuotientTensorComplex_eq_tensorObj
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerQuotientTensorComplex I M n =
      HomologicalComplex.tensorObj
        ((singleCpx0).obj (ModuleCat.of A (A ⧸ I ^ (n + 1)))) M := by
  sorry

private noncomputable abbrev idealPowerQuotientTensorComplexDerivedStageIso
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerQuotientTensorComplexDerivedStage I M n ≅
      (idealPowerQuotientTensorDerivedInverseSystem I (Q.obj M)).obj (op n) :=
  (Q.mapIso (eqToIso (idealPowerQuotientTensorComplex_eq_tensorObj I M n))) ≪≫
    (Functor.Monoidal.μIso Q
      ((singleCpx0).obj (ModuleCat.of A (A ⧸ I ^ (n + 1)))) M).symm ≪≫
      (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
          (ModuleCat.of A (A ⧸ I ^ (n + 1)))) ⊗ᵢ Iso.refl _) ≪≫
        derivedCategory_tensorObj_iso_derivedTensorProduct
          (idealPowerQuotientDerivedStage I n) (Q.obj M)

private theorem idealPowerQuotientDerivedTensorToTensorComplex_step_comm
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    ((derivedTensorProduct (Q.obj M)).map (idealPowerQuotientDerivedStep I n)) ≫
        (idealPowerQuotientTensorComplexDerivedStageIso I M n).inv =
      (idealPowerQuotientTensorComplexDerivedStageIso I M (n + 1)).inv ≫
        idealPowerQuotientTensorComplexDerivedStep I M n := by
  sorry

private abbrev idealPowerQuotientDerivedTensorToTensorComplexNatTrans
    (I : Ideal A) (M : CpxA) :
    idealPowerQuotientTensorDerivedInverseSystem I (Q.obj M) ⟶
      idealPowerQuotientTensorComplexDerivedInverseSystem I M :=
  NatTrans.ofOpSequence
    (fun n ↦ (idealPowerQuotientTensorComplexDerivedStageIso I M n).inv)
    (fun n ↦ by
      simpa using idealPowerQuotientDerivedTensorToTensorComplex_step_comm I M n)

-- Proof sketch: choose generators of `I` and replace the quotient ring tower by the
-- pro-isomorphic powered Koszul tower from Lemma `15.95.1`. Since each powered Koszul complex is a
-- bounded finite free complex, the tensor tower and the quotient-complex tower are uniformly
-- bounded in cohomology. Apply Lemma `13.42.5`, reducing to cohomology, and use Lemma `15.101.1`
-- on a bounded-above finite free resolution of `M^\bullet` to identify both cohomology towers
-- with the same tower `H^i(M^\bullet) / I^(n+1) H^i(M^\bullet)`.
/-- The canonical comparison from the derived tensor tower
`((A / I^(n+1))[0] ⊗_A^{\mathbf L} Q(M^\bullet))_n` to the quotient-complex tower
`(Q(M^\bullet / I^(n+1) M^\bullet))_n`. -/
abbrev idealPowerQuotientTensorToQuotientComplexNatTrans
    (I : Ideal A) (M : CpxA) :
    idealPowerQuotientTensorDerivedInverseSystem I (Q.obj M) ⟶
      idealPowerQuotientComplexDerivedInverseSystem I M :=
  idealPowerQuotientDerivedTensorToTensorComplexNatTrans I M ≫
    idealPowerQuotientTensorComplexToQuotientComplexNatTrans I M

section

variable [IsNoetherianRing A]

/-- Lemma 15.101.3: let `A` be a Noetherian ring, let `I ⊆ A` be an ideal, and let `M^\bullet`
be a bounded complex of finite `A`-modules. Then the inverse system of maps
`M^\bullet \otimes_A^{\mathbf L} A / I^(n+1) ⟶ M^\bullet / I^(n+1) M^\bullet` defines an
isomorphism of pro-objects of `D(A)`. In this item-file convention, stage `0` corresponds to the
textbook quotient by `I`. -/
theorem idealPowerQuotientTensorToQuotientComplex_isIso
    (I : Ideal A) (M : CpxA)
    (hboundedBelow : ∃ a : ℤ, M.IsStrictlyGE a)
    (hboundedAbove : ∃ b : ℤ, M.IsStrictlyLE b)
    (hfinite : ∀ i : ℤ, Module.Finite A (M.X i)) :
    IsIso (ofNatTrans (idealPowerQuotientTensorToQuotientComplexNatTrans I M)).toProObjectHom :=
  sorry

end

end

/-! ### Lemma_15_101_4 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v w x y

/- Domain-style sampling for Lemma 15.101.4:
- primary domain: `I`-power quotient towers, adic completion, and Mittag-Leffler inverse systems
  attached to `Hom_A(M, N / I^(n + 1) N)` and quotient-level isomorphisms;
- sampled owner declarations:
  `idealPowerModuleQuotient` from `Lemma_15_101_1`,
  `CategoryTheory.SequentialInverseSystem`,
  `CategoryTheory.Functor.IsMittagLeffler`,
  `AdicCompletion.transitionMap`;
- best owner abstraction: the quotient data live in sequential inverse systems, while the
  `Type`-valued Mittag-Leffler condition is already owned canonically by
  `CategoryTheory.Functor.IsMittagLeffler`, so a local `Type`-specific redefinition would be a
  duplicate wheel;
- primitive data: the modules `M`, `N`, the ideal `I`, and the canonical reduction/transition maps
  induced by `AdicCompletion.transitionMap`;
- derived API: the Hom tower, the quotient-isomorphism tower, the comparison maps on quotients, and
  the resulting Mittag-Leffler / inverse-limit statements.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma statements about the Hom tower, the isomorphism tower, and the
  completion comparisons;
- `core/canonical`: `idealPowerModuleQuotient`, `SequentialInverseSystem`, and
  `Functor.IsMittagLeffler`;
- `bridge/view`: the explicit quotient comparison maps and the stagewise reduction maps on
  isomorphisms. -/

section

variable {A : Type u} [CommRing A]
variable (I : Ideal A)

/-- The kernel of the transition `X / I^(n + 2) X → X / I^(n + 1) X`. -/
abbrev idealPowerModuleTransitionKer (X : Type x) [AddCommGroup X] [Module A X] (n : ℕ) :
    Submodule A (idealPowerModuleQuotient I X (n + 1)) :=
  LinearMap.ker (AdicCompletion.transitionMap I X (Nat.le_succ (n + 1)))

/-- The stage `Hom_A(M, N / I^(n + 1) N)`, which canonically models `Hom_A(M_n, N_n)`. -/
abbrev homIdealPowerStage
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] (n : ℕ) : Type (max v w) :=
  M →ₗ[A] idealPowerModuleQuotient I N n

/-- The transition map on the Hom tower induced by reduction modulo one lower power of `I`. -/
abbrev homIdealPowerStep
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] (n : ℕ) :
    homIdealPowerStage I M N (n + 1) →ₗ[A] homIdealPowerStage I M N n :=
  LinearMap.compRight A (AdicCompletion.transitionMap I N (Nat.le_succ (n + 1)))

/-- The inverse system `(Hom_A(M_n, N_n))_n`, modeled as `(Hom_A(M, N / I^(n + 1) N))_n`. -/
abbrev homIdealPowerTower
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] :
    SequentialInverseSystem (ModuleCat A) :=
  @Functor.ofOpSequence (ModuleCat A) _
    (fun n ↦ ModuleCat.of A (homIdealPowerStage I M N n))
    (fun n ↦ ModuleCat.ofHom (homIdealPowerStep I M N n))

/-- The canonical map `Hom_A(M, N) → Hom_A(M, N / I^(n + 1) N)`. -/
abbrev homReductionLinearMap
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] (n : ℕ) :
    (M →ₗ[A] N) →ₗ[A] homIdealPowerStage I M N n :=
  LinearMap.compRight A (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule A N)))

-- Proof sketch: if `f` lies in `I^(n + 1) Hom_A(M, N)`, then every value of `f` lands in
-- `I^(n + 1) N`, so the composite `M → N → N / I^(n + 1) N` is zero.
/-- The canonical reduction `Hom_A(M, N) → Hom_A(M, N / I^(n + 1) N)` kills `I^(n + 1)`. -/
theorem idealPowerHomComparison_condition
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] (n : ℕ) :
    I ^ (n + 1) • (⊤ : Submodule A (M →ₗ[A] N)) ≤
      LinearMap.ker (homReductionLinearMap I M N n) := sorry

/-- The canonical comparison
`Hom_A(M, N) / I^(n + 1) Hom_A(M, N) → Hom_A(M, N / I^(n + 1) N)`. -/
abbrev homReductionComparison
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] (n : ℕ) :
    idealPowerModuleQuotient I (M →ₗ[A] N) n →ₗ[A] homIdealPowerStage I M N n :=
  Submodule.liftQ
    (I ^ (n + 1) • (⊤ : Submodule A (M →ₗ[A] N)))
    (homReductionLinearMap I M N n)
    (idealPowerHomComparison_condition I M N n)

/-- The stage of `A`-linear isomorphisms `M_n ≃ N_n`. -/
abbrev moduleIsomorphismStage
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] (n : ℕ) : Type (max v w) :=
  idealPowerModuleQuotient I M n ≃ₗ[A] idealPowerModuleQuotient I N n

-- Proof sketch: every quotient map `X / I^(n + 2) X → X / I^(n + 1) X` is induced by the
-- universal quotient map, hence is surjective.
/-- The transition map on ideal-power quotients is surjective. -/
theorem idealPowerModuleTransition_surjective
    (X : Type x) [AddCommGroup X] [Module A X] (n : ℕ) :
    Function.Surjective (AdicCompletion.transitionMap I X (Nat.le_succ (n + 1))) := sorry

-- Proof sketch: an isomorphism `e : M_(n+1) ≃ N_(n+1)` carries the kernel of the reduction map on
-- `M_(n+1)` onto the corresponding kernel on `N_(n+1)` because the reduction maps commute with `e`
-- and `e.symm`.
/-- An isomorphism of the higher quotient stages identifies the kernels of the next transition
maps. -/
theorem idealPowerModuleTransitionKer_map_eq
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N]
    (n : ℕ) (e : moduleIsomorphismStage I M N (n + 1)) :
    (idealPowerModuleTransitionKer I M n).map (e : _ →ₗ[A] _) =
      idealPowerModuleTransitionKer I N n := sorry

/-- Reduction modulo one lower power of `I` sends an isomorphism `M_(n+1) ≃ N_(n+1)` to an
isomorphism `M_n ≃ N_n`. -/
abbrev moduleIsomorphismReduction
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] (n : ℕ) :
    moduleIsomorphismStage I M N (n + 1) → moduleIsomorphismStage I M N n :=
  fun e ↦
    ((AdicCompletion.transitionMap I M (Nat.le_succ (n + 1))).quotKerEquivOfSurjective
        (idealPowerModuleTransition_surjective I M n)).symm.trans
      ((Submodule.Quotient.equiv
          (idealPowerModuleTransitionKer I M n)
          (idealPowerModuleTransitionKer I N n)
          e
          (idealPowerModuleTransitionKer_map_eq I M N n e)).trans
        ((AdicCompletion.transitionMap I N (Nat.le_succ (n + 1))).quotKerEquivOfSurjective
          (idealPowerModuleTransition_surjective I N n)))

/-- The inverse system `(Isom_A(M_n, N_n))_n` of `A`-linear isomorphisms between the quotient
modules. -/
abbrev moduleIsomorphismTower
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] :
    SequentialInverseSystem (Type (max v w)) :=
  @Functor.ofOpSequence (Type (max v w)) _
    (fun n ↦ moduleIsomorphismStage I M N n)
    (fun n ↦ moduleIsomorphismReduction I M N n)

end

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (I : Ideal A)
variable {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
variable {N : Type w} [AddCommGroup N] [Module A N] [Module.Finite A N]

local notation "HomTower" => homIdealPowerTower I M N
local notation "IsoTower" => moduleIsomorphismTower I M N
local notation "HomComparison" => fun n ↦ homReductionComparison I M N n

-- Proof sketch: choose a finite presentation of `M`, rewrite `Hom_A(M_n, N_n)` as the middle
-- homology of the induced two-term quotient complex, and apply Lemma `15.101.1 (3)` to that
-- complex.
/-- Lemma 15.101.4 (1): for finite `A`-modules `M` and `N` over a Noetherian ring, the inverse
system `(\mathrm{Hom}_A(M_n, N_n))_n`, identified with
`(\mathrm{Hom}_A(M, N / I^(n + 1) N))_n`, is Mittag-Leffler. -/
theorem homIdealPowerTower_isMittagLeffler :
    SequentialInverseSystem.IsMittagLeffler HomTower := sorry

-- Proof sketch: apply the homomorphism case to both directions `M → N` and `N → M`, then use the
-- Nakayama argument from the Stacks proof to show that an inverse pair modulo a sufficiently low
-- stage lifts to a genuine inverse pair at every higher stage.
/-- Lemma 15.101.4 (2): the inverse system of `A`-linear isomorphisms
`(\operatorname{Isom}_A(M_n, N_n))_n` is Mittag-Leffler. -/
theorem moduleIsomorphismTower_isMittagLeffler :
    Functor.IsMittagLeffler IsoTower := sorry

-- Proof sketch: use the same finite presentation of `M` and the Artin-Rees comparison from Lemma
-- `15.101.1 (5)` for the resulting two-term complex to obtain one constant `c` that annihilates
-- the kernel and cokernel at every stage.
/-- Lemma 15.101.4 (3): there is a single constant `c > 0` such that for every `n`, the kernel
and cokernel of the canonical comparison map
`Hom_A(M, N) / I^(n + 1) Hom_A(M, N) → Hom_A(M_n, N_n)` are killed by `I^c`. -/
theorem exists_homReductionComparison_annihilated_kernel_cokernel :
    ∃ c : ℕ, 0 < c ∧
      (∀ n : ℕ,
        I ^ c • (⊤ : Submodule A (LinearMap.ker (HomComparison n))) = ⊥) ∧
      ∀ n : ℕ,
        I ^ c •
            (⊤ :
              Submodule A
                (homIdealPowerStage I M N n ⧸ LinearMap.range (HomComparison n))) =
          ⊥ := sorry

-- Proof sketch: the same Artin-Rees comparison identifies the Hom tower with the quotient tower
-- of `Hom_A(M, N)` as a pro-object, so Lemma `15.101.1 (2)` yields the inverse-limit comparison
-- with the `I`-adic completion of `Hom_A(M, N)`.
/-- Lemma 15.101.4 (4): the inverse limit of the system `(\mathrm{Hom}_A(M_n, N_n))_n`,
identified with `(\mathrm{Hom}_A(M, N / I^(n + 1) N))_n`, is canonically isomorphic to the
`I`-adic completion of `Hom_A(M, N)`. -/
theorem limit_homIdealPowerTower_iso_completedHom :
    IsIsomorphic
      (limit HomTower)
      (ModuleCat.of A (AdicCompletion I (M →ₗ[A] N))) := sorry

-- Proof sketch: combine the inverse-limit description of completions with the fact that finite
-- modules satisfy `M^ = \varprojlim M_n` and `N^ = \varprojlim N_n`, then identify compatible
-- systems of maps with `A^`-linear maps between the completed modules as in Lemma `10.97.4`.
/-- Lemma 15.101.4 (5): the `I`-adic completion of `Hom_A(M, N)` is canonically isomorphic, as an
`A^`-module, to `Hom_{A^}(M^, N^)`, where completion is taken with respect to `I`. -/
theorem completedHom_iso_completedLinearMap :
    IsIsomorphic
      (ModuleCat.of (AdicCompletion I A) (AdicCompletion I (M →ₗ[A] N)))
      (ModuleCat.of (AdicCompletion I A)
        ((AdicCompletion I M) →ₗ[AdicCompletion I A] (AdicCompletion I N))) := sorry

-- Proof sketch: an element of the inverse limit of the isomorphism tower is a compatible family
-- of stagewise inverses. Apply the previous Hom-limit comparison in both directions and use the
-- Nakayama argument from the Stacks proof to show that the two limiting maps are inverse.
/-- Lemma 15.101.4 (6): the inverse limit of the system `(\operatorname{Isom}_A(M_n, N_n))_n`
is canonically identified with the type of `A^`-linear isomorphisms `M^ ≃ N^`. -/
theorem limit_moduleIsomorphismTower_iso_completedLinearEquiv :
    IsIsomorphic
      (limit IsoTower)
      (AdicCompletion I M ≃ₗ[AdicCompletion I A] AdicCompletion I N) := sorry

end

/-! ### Lemma_15_101_5 (from Chap15) -/
noncomputable section

/- Domain-style sampling for Lemma 15.101.5:
- primary domain: `I`-adic completion of finite modules, controlled by the inverse system of
  quotient-stage linear isomorphisms;
- sampled owner declarations:
  `moduleIsomorphismStage`,
  `moduleIsomorphismTower`,
  `moduleIsomorphismTower_isMittagLeffler`,
  `limit_moduleIsomorphismTower_iso_completedLinearEquiv`;
- best owner abstraction: the source-facing hypothesis is stagewise existence of quotient
  isomorphisms, but the canonical project owner for those stages is `moduleIsomorphismStage I M N`
  from Lemma `15.101.4`; the completed comparison is likewise already owned there by
  `limit_moduleIsomorphismTower_iso_completedLinearEquiv`;
- primitive data: the ideal `I` and the finite `A`-modules `M`, `N`;
- derived API: the quotient-stage isomorphism tower and the resulting completed linear
  equivalence.

Source/core/bridge triage:
- `source-facing`: the existence theorem below, matching the Stacks-project statement that
  stagewise quotient isomorphisms force an isomorphism of completions;
- `core/canonical`: `moduleIsomorphismStage`, `moduleIsomorphismTower`, and
  `limit_moduleIsomorphismTower_iso_completedLinearEquiv`;
- `bridge/view`: the indexing convention relating the source quotient `M / I^n M` for `n > 0` to
  stage `n - 1` of `moduleIsomorphismStage`. -/

universe u v w

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (I : Ideal A)
variable {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
variable {N : Type w} [AddCommGroup N] [Module A N] [Module.Finite A N]

-- Proof sketch: `moduleIsomorphismTower_isMittagLeffler` supplies the canonical Mittag-Leffler
-- owner for the quotient-isomorphism tower, and
-- `limit_moduleIsomorphismTower_iso_completedLinearEquiv` identifies its inverse limit with the
-- type of completed linear equivalences. The source-facing assumption below is written directly in
-- terms of the owner stage `moduleIsomorphismStage`, where stage `n` encodes the textbook quotient
-- by `I^(n + 1)`.
/-- Lemma 15.101.5: if for every `n : ℕ` the quotient modules
`M / I^(n + 1) M` and `N / I^(n + 1) N` are `A`-linearly isomorphic, then the `I`-adic
completions `M^` and `N^` are linearly isomorphic over the completed ring `A^`. -/
theorem nonempty_completedLinearEquiv_of_quotientLinearEquiv
    (h : ∀ n : ℕ, Nonempty (moduleIsomorphismStage I M N n)) :
    Nonempty (AdicCompletion I M ≃ₗ[AdicCompletion I A] AdicCompletion I N) := sorry

/-! ### Remark_15_101_6 (from Chap15) -/
open CategoryTheory

noncomputable section

universe u

namespace IadicFiniteModuleSystem

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- The quotient ring `A / I^n` at stage `n`. -/
abbrev stageRing (n : ℕ+) :=
  A ⧸ I ^ (n : ℕ)

end IadicFiniteModuleSystem

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- A system of finite modules over the quotients `A / I^n`, indexed by positive integers `n`. -/
abbrev IadicFiniteModuleSystem :=
  ∀ n : ℕ+, FGModuleCat.{u} (IadicFiniteModuleSystem.stageRing A I n)

namespace IadicFiniteModuleSystem

variable {A I}

/- Domain-style sampling for Remark 15.101.6:
- primary domain: i-adic systems of finite modules together with representative-level morphisms
  and the quotient category they generate;
- sampled same-kind declarations:
  `CategoryTheory.Quotient.functor`,
  `CategoryTheory.Quotient.lift`,
  `CategoryTheory.Quotient.sound`,
  `CategoryTheory.SimplicialObject.HomotopyCategory`;
- best owner abstraction:
  `source-facing`: the quotient category of i-adic finite module systems from the remark;
  `core/canonical`: `CategoryTheory.Quotient` applied to the congruence on the representative
    category generated by one-step promotion;
  `bridge/view`: the representative category with morphisms `HomRepresentative X Y` and the
    defining promotion relation `g = f.successor`.
- primitive data: the level modules, the stage ideal, the representative family `map`, and the
  one-step promotion operation on representatives.
- derived API: the representative-category composition law, the congruence on representatives, and
  the canonical quotient functor into the category of the remark.

This item is therefore centered on the canonical quotient-category owner, not on a bespoke raw-hom
quotient `Category` instance. -/

variable (A) (I) in
/-- The image of `I` inside the quotient ring `A / I^n`. -/
abbrev stageIdeal (n : ℕ+) : Ideal (stageRing A I n) :=
  Ideal.map (Ideal.Quotient.mk (I ^ (n : ℕ))) I

/-- The submodule `I^c E_n` obtained from the image of `I^c` in `A / I^n`. -/
abbrev powerSubmodule (c : ℕ) (X : IadicFiniteModuleSystem A I) (n : ℕ+) :
    Submodule (stageRing A I n) (X n) :=
  (stageIdeal A I n) ^ c • ⊤

/-- The torsion submodule `E_n[I^c]`. -/
abbrev torsionSubmodule (c : ℕ) (X : IadicFiniteModuleSystem A I) (n : ℕ+) :
    Submodule (stageRing A I n) (X n) :=
  Submodule.torsionBySet (stageRing A I n) (X n) ↑(stageIdeal A I n ^ c)

/-- The quotient `E_n / E_n[I^c]`. -/
abbrev torsionQuotient
    (c : ℕ) (X : IadicFiniteModuleSystem A I) (n : ℕ+) :=
  X n ⧸ torsionSubmodule c X n

/-- Remark 15.101.6: a representative of a morphism between finite `A/I^n`-module systems is a
cutoff `c` together with maps `I^c E_n → E'_n / E'_n[I^c]` for every `n ≥ c`. -/
structure HomRepresentative (X Y : IadicFiniteModuleSystem A I) where
  /-- The cutoff `c` from which the family of maps is defined. -/
  cutoff : ℕ
  /-- The maps `I^c E_n → E'_n / E'_n[I^c]` for all levels `n ≥ c`. -/
  map (n : ℕ+) (_ : cutoff ≤ (n : ℕ)) :
    powerSubmodule cutoff X n →ₗ[stageRing A I n]
      torsionQuotient cutoff Y n

namespace HomRepresentative

variable {X Y : IadicFiniteModuleSystem A I}

/-- A representative can be evaluated at an admissible level to recover its levelwise linear map. -/
instance :
    CoeFun (HomRepresentative X Y) (fun f ↦
      ∀ n : ℕ+, f.cutoff ≤ (n : ℕ) →
        powerSubmodule f.cutoff X n →ₗ[stageRing A I n]
          torsionQuotient f.cutoff Y n) where
  coe f := f.map

end HomRepresentative

private abbrev AdmissibleLevel (c : ℕ) :=
  {n : ℕ+ // c ≤ (n : ℕ)}

private abbrev quotientPowerMap
    (c d : ℕ) (X : IadicFiniteModuleSystem A I) (n : ℕ+) :
    powerSubmodule d X n →ₗ[stageRing A I n] torsionQuotient c X n :=
  (torsionSubmodule c X n).mkQ.comp (powerSubmodule d X n).subtype

/-- The canonical inclusion `I^d E_n ↪ I^c E_n` for `c ≤ d`. -/
private abbrev powerSubmoduleInclusion
    (X : IadicFiniteModuleSystem A I) {c d : ℕ} (h : c ≤ d) (n : ℕ+) :
    powerSubmodule d X n →ₗ[stageRing A I n] powerSubmodule c X n :=
  Submodule.inclusion <| by
    simpa [powerSubmodule] using
      (Submodule.pow_smul_top_le (stageIdeal A I n) (X n) h)

/-- The canonical quotient map induced by increasing the torsion cutoff. -/
private noncomputable abbrev torsionQuotientMap
    (X : IadicFiniteModuleSystem A I) {c d : ℕ} (h : c ≤ d) (n : ℕ+) :
    torsionQuotient c X n →ₗ[stageRing A I n] torsionQuotient d X n :=
  (torsionSubmodule c X n).mapQ
    (torsionSubmodule d X n)
    LinearMap.id
    (by
      simpa using
        (Submodule.torsionBySet_le_torsionBySet_pow c d h (stageIdeal A I n)))

/-- The promoted representative `(c + 1, \bar \varphi_n)` attached to a representative
`(c, \varphi_n)`. -/
private noncomputable def HomRepresentative.successor
    {X Y : IadicFiniteModuleSystem A I} (f : HomRepresentative X Y) :
    HomRepresentative X Y where
  cutoff := f.cutoff + 1
  map n hn :=
    (torsionQuotientMap Y (Nat.le_succ f.cutoff) n).comp
      ((f n (Nat.le_trans (Nat.le_succ f.cutoff) hn)).comp
        (powerSubmoduleInclusion X (Nat.le_succ f.cutoff) n))

private noncomputable abbrev restrictedLevelMap
    {X Y : IadicFiniteModuleSystem A I} (f : HomRepresentative X Y) (d : ℕ)
    (n : AdmissibleLevel (f.cutoff + d)) :
    powerSubmodule (f.cutoff + d) X n.1 →ₗ[stageRing A I n.1]
      torsionQuotient f.cutoff Y n.1 :=
  (f n.1 (Nat.le_trans (Nat.le_add_right f.cutoff d) n.2)).comp
    (powerSubmoduleInclusion X (Nat.le_add_right f.cutoff d) n.1)

private theorem representativeImage_mem_quotientPowerRange
    {X Y : IadicFiniteModuleSystem A I} (f : HomRepresentative X Y) (d : ℕ)
    (n : AdmissibleLevel (f.cutoff + d))
    (x : powerSubmodule (f.cutoff + d) X n.1) :
    restrictedLevelMap f d n x ∈
      (quotientPowerMap f.cutoff d Y n.1).range := by
  sorry

private noncomputable def representativeToQuotientPowerRange
    {X Y : IadicFiniteModuleSystem A I} (f : HomRepresentative X Y) (d : ℕ)
    (n : AdmissibleLevel (f.cutoff + d)) :
    powerSubmodule (f.cutoff + d) X n.1 →ₗ[stageRing A I n.1]
      (quotientPowerMap f.cutoff d Y n.1).range :=
  LinearMap.codRestrict
    (quotientPowerMap f.cutoff d Y n.1).range
    (restrictedLevelMap f d n)
    (representativeImage_mem_quotientPowerRange f d n)

private noncomputable def promotedLevelMapAux
    (c : ℕ) {Y Z : IadicFiniteModuleSystem A I} (g : HomRepresentative Y Z)
    (n : AdmissibleLevel (c + g.cutoff)) :
    powerSubmodule g.cutoff Y n.1 →ₗ[stageRing A I n.1]
      torsionQuotient (c + g.cutoff) Z n.1 :=
  let hgcut : g.cutoff ≤ c + g.cutoff := Nat.le_add_left g.cutoff c
  (torsionQuotientMap Z hgcut n.1).comp
    (g n.1 <| Nat.le_trans hgcut n.2)

private theorem quotientPowerMap_ker_le_promotedLevelMapAux_ker
    (c : ℕ) {Y Z : IadicFiniteModuleSystem A I} (g : HomRepresentative Y Z)
    (n : AdmissibleLevel (c + g.cutoff)) :
    (quotientPowerMap c g.cutoff Y n.1).ker ≤
      (promotedLevelMapAux c g n).ker := by
  sorry

private noncomputable def promotedLevelMap
    (c : ℕ) {Y Z : IadicFiniteModuleSystem A I} (g : HomRepresentative Y Z)
    (n : AdmissibleLevel (c + g.cutoff)) :
    (quotientPowerMap c g.cutoff Y n.1).range →ₗ[stageRing A I n.1]
      torsionQuotient (c + g.cutoff) Z n.1 :=
  let lifted :
      (powerSubmodule g.cutoff Y n.1 ⧸ (quotientPowerMap c g.cutoff Y n.1).ker) →ₗ[stageRing A I n.1]
        torsionQuotient (c + g.cutoff) Z n.1 :=
    (quotientPowerMap c g.cutoff Y n.1).ker.liftQ
      (promotedLevelMapAux c g n)
      (quotientPowerMap_ker_le_promotedLevelMapAux_ker c g n)
  lifted.comp (quotientPowerMap c g.cutoff Y n.1).quotKerEquivRange.symm.toLinearMap

namespace HomRepresentative

variable {W X Y Z : IadicFiniteModuleSystem A I}

/-- One representative promotes to another when the cutoff is increased by one. -/
def promotesTo (f g : HomRepresentative X Y) : Prop :=
  g = f.successor

/-- The identity representative `(0, \mathrm{id})`. -/
noncomputable def id (X : IadicFiniteModuleSystem A I) : HomRepresentative X X where
  cutoff := 0
  map n _ := quotientPowerMap 0 0 X n

/-- The obvious composition of representatives from Remark 15.101.6, with cutoff equal to the sum
of the two cutoffs. -/
noncomputable def comp
    (f : HomRepresentative X Y) (g : HomRepresentative Y Z) :
    HomRepresentative X Z where
  cutoff := f.cutoff + g.cutoff
  map n hn :=
    (promotedLevelMap f.cutoff g ⟨n, hn⟩).comp
      (representativeToQuotientPowerRange f g.cutoff ⟨n, hn⟩)

instance : Setoid (HomRepresentative X Y) :=
  Relation.EqvGen.setoid promotesTo

/-- The composite of representatives is compatible with promotion in the source variable. -/
private theorem comp_congr_left
    {f₁ f₂ : HomRepresentative X Y} (h : f₁ ≈ f₂)
    (g : HomRepresentative Y Z) :
    f₁.comp g ≈ f₂.comp g := by
  sorry

/-- The composite of representatives is compatible with promotion in the target variable. -/
private theorem comp_congr_right
    (f : HomRepresentative X Y) {g₁ g₂ : HomRepresentative Y Z}
    (h : g₁ ≈ g₂) :
    f.comp g₁ ≈ f.comp g₂ := by
  sorry

/-- The identity representative acts as a left identity up to the promotion relation. -/
private theorem id_comp_rel (f : HomRepresentative X Y) :
    (id X).comp f ≈ f := by
  sorry

/-- The identity representative acts as a right identity up to the promotion relation. -/
private theorem comp_id_rel (f : HomRepresentative X Y) :
    f.comp (id Y) ≈ f := by
  sorry

/-- Composition of representatives is associative up to the promotion relation. -/
private theorem comp_assoc_rel
    (f : HomRepresentative W X) (g : HomRepresentative X Y) (h : HomRepresentative Y Z) :
    (f.comp g).comp h ≈ f.comp (g.comp h) := by
  sorry

private theorem id_comp_eq (f : HomRepresentative X Y) :
    (id X).comp f = f := by
  sorry

private theorem comp_id_eq (f : HomRepresentative X Y) :
    f.comp (id Y) = f := by
  sorry

private theorem comp_assoc_eq
    (f : HomRepresentative W X) (g : HomRepresentative X Y) (h : HomRepresentative Y Z) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  sorry

private abbrev Representative (A : Type u) [CommRing A] (I : Ideal A) :=
  IadicFiniteModuleSystem A I

private instance representativeCategory (A : Type u) [CommRing A] (I : Ideal A) :
    Category (Representative A I) where
  Hom X Y := HomRepresentative X Y
  id := id
  comp f g := comp f g
  id_comp := by
    intro X Y f
    exact id_comp_eq f
  comp_id := by
    intro X Y f
    exact comp_id_eq f
  assoc := by
    intro W X Y Z f g h
    exact comp_assoc_eq f g h

/-- The congruence on representative morphisms generated by one-step promotion. -/
def relation (A : Type u) [CommRing A] (I : Ideal A) :
    HomRel (IadicFiniteModuleSystem A I) :=
  fun _ _ f g ↦ Relation.EqvGen promotesTo f g

instance relation_congruence (A : Type u) [CommRing A] (I : Ideal A) :
    Congruence (relation A I) where
  equivalence := by
    intro X Y
    refine
      { refl := fun f ↦ by
          simpa [relation] using (Relation.EqvGen.refl f)
        symm := fun h ↦ by
          simpa [relation] using (Relation.EqvGen.symm _ _ h)
        trans := fun h₁ h₂ ↦ by
          simpa [relation] using (Relation.EqvGen.trans _ _ _ h₁ h₂) }
  comp_left := by
    intro _ _ _ f _ _ h
    simpa [relation] using comp_congr_right f h
  comp_right := by
    intro _ _ _ _ _ g h
    simpa [relation] using comp_congr_left h g

end HomRepresentative

open HomRepresentative

/-- Remark 15.101.6: finite `A/I^n`-module systems form a category whose morphisms are
equivalence classes of representatives under promotion. Lean realizes this category as the
canonical quotient of the representative category by the congruence `HomRepresentative.relation`. -/
abbrev Category (A : Type u) [CommRing A] (I : Ideal A) :=
  CategoryTheory.Quotient (HomRepresentative.relation A I)

namespace Category

/-- The canonical quotient functor from raw representatives to the quotient category of Remark
15.101.6. -/
abbrev quotient (A : Type u) [CommRing A] (I : Ideal A) :
    IadicFiniteModuleSystem A I ⥤ IadicFiniteModuleSystem.Category A I :=
  CategoryTheory.Quotient.functor (HomRepresentative.relation A I)

/-- The image of a finite module system in the quotient category has the same underlying object. -/
theorem quotient_obj_as (X : IadicFiniteModuleSystem A I) :
    ((quotient A I).obj X).as = X :=
  rfl

end Category

end IadicFiniteModuleSystem

/-! ### Lemma_15_101_7 (from Chap15) -/
open CategoryTheory

noncomputable section

universe u

section

variable {A : Type u} [CommRing A] {I : Ideal A}

namespace IadicFiniteModuleSystem

variable {X Y : IadicFiniteModuleSystem A I}

local notation "Q" => IadicFiniteModuleSystem.Category.quotient A I

open HomRepresentative

/- Domain-style sampling for Lemma 15.101.7:
- primary domain: isomorphism criteria for morphisms in the category `IadicFiniteModuleSystem`
  from Remark `15.101.6`;
- sampled owner declarations:
  `CategoryTheory.IsIso`,
  `CategoryTheory.Quotient`,
  `IadicFiniteModuleSystem.Category.quotient`,
  `IadicFiniteModuleSystem.HomRepresentative`,
  `Submodule.torsionBySet`;
- best owner abstraction:
  `source-facing`: the isomorphism criterion for a morphism
    `f : (Q).obj X ⟶ (Q).obj Y`;
  `core/canonical`: the owner predicate `CategoryTheory.IsIso f` on morphisms in the category of
    Remark `15.101.6`;
  `bridge/view`: the representative-level predicate saying one, equivalently every,
    representative has eventually bounded kernel and cokernel;
- primitive data: the representative-level torsion conditions on kernels and cokernels;
- derived API: the morphism-level predicate
  `HasEventuallyBoundedKernelAndCokernel f` and the main `IsIso f ↔ ...` theorem below.

This item therefore should not stop at the auxiliary representative predicate: the public main
entry is the `IsIso` criterion on the actual category morphism. -/

namespace HomRepresentative

private abbrev levelKernel (f : HomRepresentative X Y)
    (n : {n : ℕ+ // f.cutoff ≤ (n : ℕ)}) :
    Submodule (stageRing A I n.1) (powerSubmodule f.cutoff X n.1) :=
  LinearMap.ker (f n.1 n.2)

private abbrev levelCokernel (f : HomRepresentative X Y)
    (n : {n : ℕ+ // f.cutoff ≤ (n : ℕ)}) : Type u :=
  torsionQuotient f.cutoff Y n.1 ⧸ LinearMap.range (f n.1 n.2)

private def hasEventuallyBoundedKernelAndCokernel (f : HomRepresentative X Y) : Prop :=
  ∃ c' N : ℕ, ∃ hN : f.cutoff ≤ N,
    ∀ n : ℕ+, ∀ hn : N ≤ (n : ℕ),
      Module.IsTorsionBySet
          (stageRing A I n)
          (levelKernel f ⟨n, Nat.le_trans hN hn⟩)
          (↑((stageIdeal A I n) ^ c') : Set (stageRing A I n)) ∧
          Module.IsTorsionBySet
              (stageRing A I n)
              (levelCokernel f ⟨n, Nat.le_trans hN hn⟩)
              (↑((stageIdeal A I n) ^ c') : Set (stageRing A I n))

private theorem hasEventuallyBoundedKernelAndCokernel_congr
    {f g : HomRepresentative X Y} (h : f ≈ g) :
    hasEventuallyBoundedKernelAndCokernel f ↔ hasEventuallyBoundedKernelAndCokernel g := by
  sorry

end HomRepresentative

private theorem relation_of_compClosure
    {f g : HomRepresentative X Y}
    (h : CategoryTheory.HomRel.CompClosure (relation A I) f g) :
    relation A I f g := by
  simpa [relation] using
    (show CategoryTheory.HomRel.CompClosure (relation A I) f g ↔ relation A I f g from
      CategoryTheory.HomRel.compClosure_iff_self (relation A I) f g).1 h

/-- Auxiliary morphism-level predicate for Lemma 15.101.7 in the category from Remark 15.101.6: a
morphism has eventually bounded kernel and cokernel if, for one (equivalently every)
representative `(c, \varphi_n)`, there exists a power `I^{c'}` annihilating both the kernel and
cokernel of the level maps `I^c E_n → E'_n / E'_n[I^c]` for all sufficiently large `n`. -/
def HasEventuallyBoundedKernelAndCokernel
    (f : (Q).obj X ⟶ (Q).obj Y) : Prop :=
  Quot.liftOn f hasEventuallyBoundedKernelAndCokernel
    (fun f g h ↦ by
      apply propext
      exact hasEventuallyBoundedKernelAndCokernel_congr (relation_of_compClosure h))

-- Proof sketch: if `f` is an isomorphism in the quotient category of Remark `15.101.6`, choose
-- an inverse representative and compose the two representatives. The identity representative has
-- zero kernel and cokernel, so the bounded-kernel/cokernel condition follows from compatibility
-- with promotion and composition. Conversely, the bounded kernel/cokernel condition yields a
-- representative that is invertible in the quotient category after increasing the cutoff, which
-- gives `IsIso f`.
/-- Lemma 15.101.7: a morphism in the category `\mathcal C` of Remark `15.101.6` is an
isomorphism if and only if it has eventually bounded kernel and cokernel. -/
theorem isIso_iff_hasEventuallyBoundedKernelAndCokernel
    (f : (Q).obj X ⟶ (Q).obj Y) :
    IsIso f ↔ HasEventuallyBoundedKernelAndCokernel f := by
  sorry

end IadicFiniteModuleSystem

end

/-! ### Lemma_15_101_8 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Abelian
open IadicFiniteModuleSystem

noncomputable section

universe u

attribute [local instance] CategoryTheory.HasExt.standard

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "Q" => IadicFiniteModuleSystem.Category.quotient A

/- Domain-style sampling for Lemma 15.101.8:
- primary domain: `Ext` towers in the quotient category of `I`-adic finite module systems from
  Remark `15.101.6`;
- sampled owner declarations:
  `IadicFiniteModuleSystem`,
  `IadicFiniteModuleSystem.Category`,
  `IadicFiniteModuleSystem.Category.quotient`,
  `IadicFiniteModuleSystem.isIso_iff_hasEventuallyBoundedKernelAndCokernel`,
  `CategoryTheory.IsIsomorphic`;
- best owner abstraction:
  `source-facing`: the two `IadicFiniteModuleSystem` objects
    `extQuotientSystem I M N i` and `extReductionSystem I M N i`;
  `core/canonical`: the quotient-category owner from Remark `15.101.6`, together with the
    object-level proposition `CategoryTheory.IsIsomorphic`;
  `bridge/view`: the stagewise reduction `M / I^n M`, which is only implementation data for the
    reduction-side system and should not remain a second public owner;
- primitive data: the two source-facing Ext systems;
- derived API: the theorem that these systems are isomorphic in the category `\mathcal C`.

This item should therefore keep the systems themselves public, but record the comparison at the
canonical object-isomorphism layer rather than as a chosen concrete isomorphism. -/

/-- The reduction `M_n = M / I^n M`, viewed as a module over `A_n = A / I^n`. This is a private
bridge for the reduction-side system, not a second public owner. -/
private abbrev stagewiseReduction (I : Ideal A) (M : ModuleCat A) (n : ℕ+) :
    ModuleCat (stageRing A I n) :=
  ModuleCat.of (stageRing A I n) (M ⧸ (I ^ (n : ℕ) • (⊤ : Submodule A M)))

/-- The inverse system whose `n`th stage is
`Ext^i_A(M, N) / I^n Ext^i_A(M, N)`, indexed by positive integers `n`. -/
abbrev extQuotientSystem (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M]
    [Module.Finite A N] (i : ℕ) : IadicFiniteModuleSystem A I :=
  fun n ↦ FGModuleCat.of (stageRing A I n)
    (Ext M N i ⧸ (I ^ (n : ℕ) • (⊤ : Submodule A (Ext M N i))))

/-- The inverse system whose `n`th stage is
`Ext^i_{A / I^n}(M / I^n M, N / I^n N)`, indexed by positive integers `n`. -/
abbrev extReductionSystem (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M]
    [Module.Finite A N] (i : ℕ) : IadicFiniteModuleSystem A I :=
  fun n ↦ FGModuleCat.of (stageRing A I n)
    (Ext (stagewiseReduction I M n) (stagewiseReduction I N n) i)

-- Proof sketch: choose a finite presentation `0 → K → A^r → M → 0`, compare the systems
-- `(K / I^n K)_n` and `(Ker(A_n^r → M_n))_n` via Lemma `15.101.1`, and then compare the induced
-- Hom systems using Lemmas `15.101.4` and `15.101.7`. Dimension shifting reduces the higher Ext
-- cases to `i = 0, 1`, where the long exact sequence and a diagram chase produce the required
-- representative with uniformly bounded kernel and cokernel.
/-- Lemma 15.101.8: for every `i ≥ 0`, the system
`(\operatorname{Ext}^i_A(M, N) / I^n \operatorname{Ext}^i_A(M, N))_{n \ge 1}` admits a
representative with eventually bounded kernel and cokernel to the system
`(\operatorname{Ext}^i_{A / I^n}(M / I^n M, N / I^n N))_{n \ge 1}`; equivalently, and here taken
as the canonical public statement, these two objects are isomorphic in the category
`\mathcal C` of Remark `15.101.6`. -/
theorem extQuotientSystem_isomorphic_extReductionSystem
    (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M] [Module.Finite A N] (i : ℕ) :
    IsIsomorphic ((Q I).obj (extQuotientSystem I M N i)) ((Q I).obj (extReductionSystem I M N i)) := by
  sorry

end

/-! ### Remark_15_101_9 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Abelian

noncomputable section

universe u

attribute [local instance] CategoryTheory.HasExt.standard

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/- Domain-style sampling for Remark 15.101.9:
- primary domain: the weak `Ext` system on the reduction-side family
  `(\operatorname{Ext}^i_{A / I^n}(M / I^n M, N / I^n N))_{n ≥ 1}` from Chapter `15`;
- sampled owner declarations:
  `IadicFiniteModuleSystem`,
  `extReductionSystem`,
  `extQuotientSystem`,
  `extQuotientSystem_isomorphic_extReductionSystem`;
- best owner abstraction:
  `source-facing`: `extReductionSystem I M N i`, the reduction-side weak `Ext` system itself;
  `core/canonical`: `IadicFiniteModuleSystem A I`, the chapter owner for weak `I`-adic systems;
  `bridge/view`: `extQuotientSystem_isomorphic_extReductionSystem`, identifying the reduction
    system with the quotient-side weak `Ext` system from Lemma `15.101.8`;
- primitive vs. derived:
  the primitive source-facing datum here is the reduction-side weak system itself, not an
  existential morphism in the quotient category;
  the comparison with the quotient-side system is derived bridge API supplied upstream by
  Lemma `15.101.8`.

Source/core/bridge triage:
- `source-facing`: `extReductionSystem`;
- `core/canonical`: `IadicFiniteModuleSystem`;
- `bridge/view`: `extQuotientSystem_isomorphic_extReductionSystem`.

This remark should therefore recall the reduction-side weak-system owner directly, and reuse the
existing comparison theorem rather than restating it as a weaker existential bounded-kernel /
bounded-cokernel package. -/

/- Remark 15.101.9: the family
`(\operatorname{Ext}^i_{A / I^n}(M / I^n M, N / I^n N))_{n ≥ 1}` is itself the source-facing weak
`I`-adic system `extReductionSystem I M N i` from Lemma `15.101.8`. -/
recall extReductionSystem

/- Companion recall: Lemma `15.101.8` identifies this reduction-side weak `Ext` system with the
canonical quotient-side weak `Ext` system
`(\operatorname{Ext}^i_A(M, N) / I^n \operatorname{Ext}^i_A(M, N))_{n ≥ 1}` in the category
`\mathcal C` of Remark `15.101.6`. -/
recall extQuotientSystem_isomorphic_extReductionSystem

end
