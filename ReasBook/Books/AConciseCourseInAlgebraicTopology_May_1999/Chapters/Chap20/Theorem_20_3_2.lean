import Mathlib.Algebra.Homology.Augment
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Theorem_20_1_2

open CategoryTheory CategoryTheory.Limits
open scoped Manifold Topology

noncomputable section

-- `Theorem_20_1_2` already owns the canonical absolute local-coefficient chain-model API via
-- `ChosenUniversalCoverChainModel` and its degreewise homology owner `C.homology`. This file
-- keeps the reduced half source-facing by packaging a chosen reduced equivariant chain model of
-- `M` as a reduced complex whose augmentation recovers one of those absolute chosen models.

/-- A chosen based reduced `π₁(M, x)`-equivariant chain model of `M`. Its reduced chain complex
augments to the chosen absolute universal-cover chain model `coverModel`, so the reduced data is
not arbitrary. -/
structure ChosenReducedUniversalCoverChainModel
    {M : Type} [TopologicalSpace M] (π : FundamentalGroupoid M ⥤ ModuleCat ℤ) (x : M) where
  coverModel : ChosenUniversalCoverChainModel π x
  reducedChains : ChainComplex (Rep ℤ (FundamentalGroup M x)) ℕ
  augmentation :
    reducedChains.X 0 ⟶ Rep.trivial ℤ (FundamentalGroup M x) ℤ
  augmentation_comm : reducedChains.d 1 0 ≫ augmentation = 0
  augmentReducedChainsIsoToCoverChains :
    ChainComplex.augment reducedChains augmentation augmentation_comm ≅ coverModel.coverChains

namespace ChosenReducedUniversalCoverChainModel

/-- The reduced local-coefficient chain complex attached to the chosen reduced equivariant chain
model `C`. -/
abbrev chainComplex
    {M : Type} [TopologicalSpace M] {π : FundamentalGroupoid M ⥤ ModuleCat ℤ} {x : M}
    (C : ChosenReducedUniversalCoverChainModel π x) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  HomologicalComplex.coinvariantsTensorObj (localSystemFiberRep π x) C.reducedChains

/-- Unfolding `C.chainComplex` recovers the reduced coinvariants complex attached to the chosen
reduced equivariant chain model `C.reducedChains`. -/
theorem chainComplex_def
    {M : Type} [TopologicalSpace M] (π : FundamentalGroupoid M ⥤ ModuleCat ℤ) (x : M)
    (C : ChosenReducedUniversalCoverChainModel π x) :
    C.chainComplex =
      HomologicalComplex.coinvariantsTensorObj (localSystemFiberRep π x) C.reducedChains :=
  rfl

/-- The degree-`i` reduced local-coefficient homology owner of `M` with coefficients in `π`,
computed from the chosen reduced chain model `C`. -/
abbrev homology
    {M : Type} [TopologicalSpace M] {π : FundamentalGroupoid M ⥤ ModuleCat ℤ} {x : M}
    (C : ChosenReducedUniversalCoverChainModel π x) (i : ℕ) :
    ModuleCat ℤ :=
  C.chainComplex.homology i

/-- Unfolding `C.homology i` recovers the homology of the reduced local-coefficient chain complex
attached to the chosen reduced equivariant chain model `C`. -/
theorem homology_def
    {M : Type} [TopologicalSpace M] (π : FundamentalGroupoid M ⥤ ModuleCat ℤ) (x : M)
    (C : ChosenReducedUniversalCoverChainModel π x) (i : ℕ) :
    C.homology i = C.chainComplex.homology i :=
  rfl

/-- A chosen reduced universal-cover chain model `C` computes a reduced local-coefficient
homology owner `Hπ` when each degree-`i` chosen reduced homology object is identified with
`Hπ i` by an explicit comparison isomorphism. -/
abbrev ComputesHomology
    {M : Type} [TopologicalSpace M] {π : FundamentalGroupoid M ⥤ ModuleCat ℤ} {x : M}
    (C : ChosenReducedUniversalCoverChainModel π x) (Hπ : ℕ → ModuleCat ℤ) :
    Type :=
  ∀ i : ℕ, C.homology i ≅ Hπ i

/-- Unfolding `C.ComputesHomology Hπ` gives the degreewise comparison isomorphisms from the chosen
reduced homology owner `C.homology i` to `Hπ i`. -/
theorem computesHomology_def
    {M : Type} [TopologicalSpace M] {π : FundamentalGroupoid M ⥤ ModuleCat ℤ} {x : M}
    (C : ChosenReducedUniversalCoverChainModel π x) (Hπ : ℕ → ModuleCat ℤ) :
    C.ComputesHomology Hπ = (∀ i : ℕ, C.homology i ≅ Hπ i) :=
  rfl

end ChosenReducedUniversalCoverChainModel

section

variable {n : ℕ}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]
variable [Fact (Module.finrank ℝ E = n)]

/-- If `C` is a chosen universal-cover chain model for `M`, then its absolute
local-coefficient homology owner `C.homology i` vanishes in every degree `i > n`. -/
theorem isZero_chosenLocalCoefficientHomology_of_lt
    (π : FundamentalGroupoid M ⥤ ModuleCat ℤ) {x : M}
    (C : ChosenUniversalCoverChainModel π x)
    {i : ℕ} (hi : n < i) :
    IsZero (C.homology i) := sorry

/-- If the chosen-model homology `C.homology i` vanishes, then every degreewise owner `Hπ`
computed from `C` also vanishes in degree `i` via the comparison isomorphism `hHπ i`. -/
theorem isZero_localCoefficientHomology_of_isZero_chosen
    (π : FundamentalGroupoid M ⥤ ModuleCat ℤ) {x : M}
    (C : ChosenUniversalCoverChainModel π x) (Hπ : ℕ → ModuleCat ℤ)
    (hHπ : C.ComputesHomology Hπ) (i : ℕ) (hzero : IsZero (C.homology i)) :
    IsZero (Hπ i) :=
  IsZero.of_iso hzero (hHπ i).symm

/-- Theorem 20.3.2 (1): any degreewise local-coefficient homology owner `Hπ` computed from a
chosen universal-cover chain model `C` vanishes in every degree `i > n`. -/
theorem isZero_localCoefficientHomology_of_lt
    (π : FundamentalGroupoid M ⥤ ModuleCat ℤ) {x : M}
    (C : ChosenUniversalCoverChainModel π x) (Hπ : ℕ → ModuleCat ℤ)
    (hHπ : C.ComputesHomology Hπ)
    {i : ℕ} (hi : n < i) :
    IsZero (Hπ i) :=
  isZero_localCoefficientHomology_of_isZero_chosen π C Hπ hHπ i
    (isZero_chosenLocalCoefficientHomology_of_lt π C hi)

/-- The chosen reduced local-coefficient homology owner attached to the chosen reduced chain model
`C` vanishes in degree `n` when `M` is connected and noncompact. -/
theorem isZero_chosenReducedLocalCoefficientHomology_of_connected_noncompact
    [ConnectedSpace M] [NoncompactSpace M] (π : FundamentalGroupoid M ⥤ ModuleCat ℤ)
    {x : M} (C : ChosenReducedUniversalCoverChainModel π x) :
    IsZero (C.homology n) := sorry

/-- If the chosen reduced chain-model homology vanishes in degree `i`, then every degreewise
reduced local-coefficient homology owner `Hπ` computed from that model also vanishes in
degree `i`. -/
theorem isZero_reducedLocalCoefficientHomology_of_isZero_chosen
    (π : FundamentalGroupoid M ⥤ ModuleCat ℤ) {x : M}
    (C : ChosenReducedUniversalCoverChainModel π x) (Hπ : ℕ → ModuleCat ℤ)
    (hHπ : C.ComputesHomology Hπ) (i : ℕ) (hzero : IsZero (C.homology i)) :
    IsZero (Hπ i) :=
  IsZero.of_iso hzero (hHπ i).symm

/-- Theorem 20.3.2 (2): any degreewise reduced local-coefficient homology owner `Hπ` computed by
a chosen reduced `π₁(M, x)`-equivariant chain model vanishes in degree `n` when `M` is
connected and noncompact. -/
theorem isZero_reducedLocalCoefficientHomology_of_connected_noncompact
    [ConnectedSpace M] [NoncompactSpace M] (π : FundamentalGroupoid M ⥤ ModuleCat ℤ)
    {x : M} (C : ChosenReducedUniversalCoverChainModel π x) (Hπ : ℕ → ModuleCat ℤ)
    (hHπ : C.ComputesHomology Hπ) :
    IsZero (Hπ n) :=
  isZero_reducedLocalCoefficientHomology_of_isZero_chosen π C Hπ hHπ n
    (isZero_chosenReducedLocalCoefficientHomology_of_connected_noncompact π C)

end
