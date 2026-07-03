import Mathlib
import StacksProject_2024.Chap13.Definition_13_27_1
import StacksProject_2024.Chap15.Definition_15_75_1
import StacksProject_2024.Chap15.«15_74_0_2»
import StacksProject_2024.Chap15.Lemma_15_59_14
import StacksProject_2024.Chap15.Lemma_15_74_4

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open Opposite

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "RHomPkg" => MonoidalClosed DMod
local notation "𝓗" => DerivedCategory.homologyFunctor (ModuleCat A)

open scoped DerivedInternalHom
open scoped DerivedExt
open scoped DerivedTensorProduct

/- Domain-style sampling for Lemma 15.75.15:
- primary domain: rigid duality for perfect objects of `D(A)`, expressed through the canonical
  tensor owner `derivedTensorProduct`, the monoidal-closed owner `MonoidalClosed DMod`, and the
  monoidal duality owner `ExactPairing`;
- sampled owner declarations:
  `CategoryTheory.derivedTensorProduct`,
  the source-facing notation `RHom[H](K, L)`,
  `CategoryTheory.MonoidalClosed.derivedTensorAdj`,
  `CategoryTheory.derivedInternalHom_comp`,
  `CategoryTheory.derivedHom_cohomology_iso_shiftedHom`,
  `CategoryTheory.ExactPairing`;
- best owner abstraction:
  `source-facing`: the derived dual `K^∨ = RHom_A(K, A[0])` and the canonical comparison maps
  appearing in parts `(2)` to `(4)`;
  `core/canonical`: `derivedTensorProduct`, `RHom[H](K, L)`, `ExactPairing`, and the chapter owner
  `derivedHom_cohomology_iso_shiftedHom` for `H^n(RHom)` versus `ShiftedHom`;
  `bridge/view`: the right-unit identifications for `A[0]`, the bidual comparison morphism, the
  tensor-to-Hom comparison natural transformation below, and the degree-zero passage from
  `ShiftedHom K L 0` to `K ⟶ L`.

Primitive data are only the chosen monoidal-closed owner `H` and the canonical tensor unit
`A[0]`. The bidual map, tensor/Hom comparison, degree-zero comparison, and exact-pairing package
are derived API and should therefore be exposed as actual morphisms and natural transformations,
not hidden behind `Nonempty` wrappers.
-/

/-- The derived dual `K^\vee = R\mathrm{Hom}_A(K, A[0])` attached to a chosen derived
internal-Hom package on `D(A)`. -/
abbrev derivedDual (H : RHomPkg) (K : DMod) : DMod :=
  RHom[H](K, ringSingle)

notation:max K:max "ᵛ⟮" H:max "⟯" => derivedDual H K

/-- The contravariant map on derived duals induced by a morphism in `D(A)`. -/
abbrev derivedDualMap
    (H : RHomPkg) {K L : DMod} (f : K ⟶ L) :
    Lᵛ⟮H⟯ ⟶ Kᵛ⟮H⟯ :=
  derivedInternalHomMap H f (𝟙 ringSingle)

/-- The canonical evaluation morphism
`K^\vee \otimes_A^{\mathbf L} K \to A[0]`. -/
private noncomputable def derivedDualEvaluationDerivedTensor
    (H : RHomPkg) (K : DMod) :
    Kᵛ⟮H⟯ ⊗[A]^L K ⟶ ringSingle :=
  (H.derivedTensorAdj K).counit.app ringSingle

private noncomputable def derivedDualTensorEvaluation
    (H : RHomPkg) (K : DMod) :
    K ⊗[A]^L Kᵛ⟮H⟯ ⟶ ringSingle :=
  (derivedTensorProduct_comm K Kᵛ⟮H⟯).hom ≫
    derivedDualEvaluationDerivedTensor H K

private noncomputable def derivedInternalHomIdUnit
    (H : RHomPkg) (K : DMod) :
    ringSingle ⟶ RHom[H](K, K) :=
  letI : MonoidalClosed DMod := H
  (H.derivedTensorAdj K).homEquiv ringSingle K (singleZeroDerivedTensorIso K).hom

private noncomputable def derivedInternalHomUnitComparison
    (H : RHomPkg) (L : DMod) :
    L ⟶ RHom[H](ringSingle, L) :=
  letI : MonoidalClosed DMod := H
  (H.derivedTensorAdj ringSingle).homEquiv L L
    ((derivedTensorProduct_comm L ringSingle ≪≫ singleZeroDerivedTensorIso L).hom)

-- Proof sketch: this is the evaluation morphism
-- `K \otimes_A^{\mathbf L} K^\vee \to A[0]` transposed across the adjunction
-- `- \otimes_A^{\mathbf L} K^\vee ⊣ R\mathrm{Hom}_A(K^\vee, -)`.
/-- The canonical bidual comparison morphism
`K \to (K^\vee)^\vee`. -/
noncomputable def derivedDualBidualComparison
    (H : RHomPkg) (K : DMod) :
    K ⟶ (Kᵛ⟮H⟯)ᵛ⟮H⟯ :=
  (H.derivedTensorAdj Kᵛ⟮H⟯).homEquiv K ringSingle
    (derivedDualTensorEvaluation H K)

-- Proof sketch: choose a bounded finite-projective representative of `K`. Lemma `15.74.2`
-- identifies `RHom_A(K, A)` with the termwise dual complex, whose terms remain finite projective,
-- so the resulting object is again represented by a bounded finite-projective complex.
/-- Lemma 15.75.15 (1): if `K` is a perfect object of `D(A)`, then its derived dual
`K^\vee = R\mathrm{Hom}_A(K, A[0])` is again perfect. -/
theorem derivedDual_isPerfect
    (H : RHomPkg) {K : DMod}
    (hK : DerivedCategory.IsPerfect K) :
    DerivedCategory.IsPerfect Kᵛ⟮H⟯ := sorry

-- Proof sketch: represent `K` by a bounded finite-projective complex. Degreewise evaluation on
-- finite projective modules identifies that complex with its double dual, and the induced map in
-- the derived category is the canonical bidual comparison defined above.
/-- Lemma 15.75.15 (2): for a perfect object `K`, the canonical bidual comparison
`K \to (K^\vee)^\vee` is an isomorphism. -/
theorem perfect_iso_derivedDual_derivedDual
    (H : RHomPkg) {K : DMod}
    (hK : DerivedCategory.IsPerfect K) :
    IsIso (derivedDualBidualComparison H K) := sorry

/-- The canonical natural transformation
`- \otimes_A^{\mathbf L} K^\vee \to R\mathrm{Hom}_A(K, -)`. -/
noncomputable def derivedDualTensorComparison
    (H : RHomPkg) (K : DMod) :
    letI := H
    derivedTensorProduct Kᵛ⟮H⟯ ⟶ ihom K where
  app L :=
    (derivedTensorProduct Kᵛ⟮H⟯).map
        (derivedInternalHomUnitComparison H L) ≫
      derivedInternalHom_comp H K ringSingle L
  naturality {L₁ L₂} f := by
    sorry

/-- The canonical comparison
`K \otimes_A^{\mathbf L} K^\vee \to R\mathrm{Hom}_A(K, K)`. -/
abbrev derivedDualTensorToEnd
    (H : RHomPkg) (K : DMod) :
    K ⊗[A]^L Kᵛ⟮H⟯ ⟶ RHom[H](K, K) :=
  (derivedDualTensorComparison H K).app K

-- Proof sketch: choose a bounded finite-projective representative of `K`, let `E^•` be its
-- termwise dual, and use the left-dual pairing from Section `15.73` to identify the totalized
-- tensor functor `- ⊗_A E^•` with the Hom complex functor `Hom^•(K^•,-)`. Passing to derived
-- categories yields the canonical natural transformation above, and it is an isomorphism for a
-- perfect source complex.
/-- Lemma 15.75.15 (3): if `K` is perfect, then the canonical natural transformation
`- \otimes_A^{\mathbf L} K^\vee \to R\mathrm{Hom}_A(K,-)` is an isomorphism. -/
theorem tensor_derivedDual_iso_derivedInternalHom
    (H : RHomPkg) {K : DMod}
    (hK : DerivedCategory.IsPerfect K) :
    IsIso (derivedDualTensorComparison H K) := sorry

/-- For a perfect object, the canonical comparison
`K \otimes_A^{\mathbf L} K^\vee \to R\mathrm{Hom}_A(K, K)` is an isomorphism. -/
theorem derivedDualTensorToEnd_isIso_of_isPerfect
    (H : RHomPkg) {K : DMod}
    (hK : DerivedCategory.IsPerfect K) :
    IsIso (derivedDualTensorToEnd H K) := sorry

/-- The canonical coevaluation morphism
`A[0] \to K \otimes_A^{\mathbf L} K^\vee`,
obtained from the identity of `K` via the tensor-to-endomorphism comparison. -/
private noncomputable def derivedDualCoevaluationDerivedTensor
    (H : RHomPkg) (K : DMod)
    [IsIso (derivedDualTensorToEnd H K)] :
    ringSingle ⟶ K ⊗[A]^L Kᵛ⟮H⟯ :=
  derivedInternalHomIdUnit H K ≫
    inv (derivedDualTensorToEnd H K)

/-- The canonical evaluation morphism
`K^\vee ⊗ K \to \mathbb{1}` in the monoidal category `D(A)`. -/
noncomputable def derivedDualEvaluation
    (H : RHomPkg) (K : DMod) :
    Kᵛ⟮H⟯ ⊗ K ⟶ 𝟙_ DMod :=
  (derivedCategory_tensorObj_iso_derivedTensorProduct Kᵛ⟮H⟯ K).hom ≫
    derivedDualEvaluationDerivedTensor H K ≫
      (singleZeroIsoTensorUnit : ringSingle ≅ 𝟙_ DMod).hom

/-- The canonical coevaluation morphism
`\mathbb{1} \to K ⊗ K^\vee` in the monoidal category `D(A)`. -/
noncomputable def derivedDualCoevaluation
    (H : RHomPkg) (K : DMod)
    [IsIso (derivedDualTensorToEnd H K)] :
    𝟙_ DMod ⟶ K ⊗ Kᵛ⟮H⟯ :=
  (singleZeroIsoTensorUnit : ringSingle ≅ 𝟙_ DMod).inv ≫
    derivedDualCoevaluationDerivedTensor H K ≫
      (derivedCategory_tensorObj_iso_derivedTensorProduct K Kᵛ⟮H⟯).inv

-- Proof sketch: after transporting across the inverse of
-- `K \otimes_A^{\mathbf L} K^\vee \to R\mathrm{Hom}_A(K, K)`, the first triangle identity becomes
-- the identity of `K^\vee`.
/-- The canonical coevaluation and evaluation maps for the derived dual satisfy the first triangle
identity. -/
theorem derivedDual_coevaluation_evaluation
    (H : RHomPkg) {K : DMod}
    [IsIso (derivedDualTensorToEnd H K)] :
    Kᵛ⟮H⟯ ◁ derivedDualCoevaluation H K ≫
        (α_ _ _ _).inv ≫
        derivedDualEvaluation H K ▷ Kᵛ⟮H⟯ =
      (ρ_ Kᵛ⟮H⟯).hom ≫
        (λ_ Kᵛ⟮H⟯).inv := sorry

-- Proof sketch: transport the identity of `K` through the same tensor-to-endomorphism
-- isomorphism.
/-- The canonical coevaluation and evaluation maps for the derived dual satisfy the second
triangle identity. -/
theorem derivedDual_evaluation_coevaluation
    (H : RHomPkg) {K : DMod}
    [IsIso (derivedDualTensorToEnd H K)] :
    derivedDualCoevaluation H K ▷ K ≫
        (α_ _ _ _).hom ≫
        K ◁ derivedDualEvaluation H K =
      (λ_ K).hom ≫ (ρ_ K).inv := sorry

/-- The derived dual together with its canonical coevaluation and evaluation maps gives a left
dual once the tensor-to-endomorphism comparison is an isomorphism. -/
@[reducible] noncomputable def derivedDualExactPairingOfIsIso
    (H : RHomPkg) (K : DMod)
    [IsIso (derivedDualTensorToEnd H K)] :
    ExactPairing Kᵛ⟮H⟯ K :=
  letI : ExactPairing K Kᵛ⟮H⟯ :=
    { coevaluation' := derivedDualCoevaluation H K
      evaluation' := derivedDualEvaluation H K
      coevaluation_evaluation' := derivedDual_coevaluation_evaluation H
      evaluation_coevaluation' := derivedDual_evaluation_coevaluation H }
  BraidedCategory.exactPairing_swap K Kᵛ⟮H⟯

/-- For a perfect object, the derived dual is the canonical left dual furnished by the evaluation
and coevaluation maps above. -/
noncomputable abbrev derivedDualExactPairing
    (H : RHomPkg) {K : DMod}
    (hK : DerivedCategory.IsPerfect K) :
    ExactPairing Kᵛ⟮H⟯ K :=
  letI : IsIso (derivedDualTensorToEnd H K) :=
    derivedDualTensorToEnd_isIso_of_isPerfect H hK
  derivedDualExactPairingOfIsIso H K

/-- The induced degree-zero comparison
`H^0(L \otimes_A^{\mathbf L} K^\vee) \to H^0(R\mathrm{Hom}_A(K, L))`. -/
noncomputable def derivedDualTensorZeroCohomologyComparison
    (H : RHomPkg) (K L : DMod) :
    (𝓗 0).obj (L ⊗[A]^L Kᵛ⟮H⟯) ⟶
      (𝓗 0).obj (RHom[H](K, L)) :=
  (𝓗 0).map ((derivedDualTensorComparison H K).app L)

-- Proof sketch: apply degree-zero cohomology to the tensor/Hom comparison from part `(3)`.
/-- If `K` is perfect, then the induced degree-zero comparison
`H^0(L \otimes_A^{\mathbf L} K^\vee) \to H^0(R\mathrm{Hom}_A(K, L))` is an isomorphism. -/
theorem derivedDualTensorZeroCohomologyComparison_isIso_of_isPerfect
    (H : RHomPkg)
    {K : DMod} (hK : DerivedCategory.IsPerfect K) (L : DMod) :
    IsIso (derivedDualTensorZeroCohomologyComparison H K L) := sorry

/-- The canonical degree-zero bridge from `Ext^0_A(K, L) = ShiftedHom K L 0` to
`Hom_{D(A)}(K, L)`. -/
private noncomputable abbrev shiftedHomZeroLinearEquiv (K L : DMod) :
    Ext^((0 : ℤ))(K, L) ≃ₗ[A] (K ⟶ L) :=
  (LinearEquiv.ofBijective
      { toFun := ShiftedHom.mk₀ (0 : ℤ) rfl
        map_add' := by
          intro f g
          simp
        map_smul' := by
          intro r f
          simpa using ShiftedHom.mk₀_smul (0 : ℤ) rfl r f }
      (by
        constructor
        · intro f g hfg
          exact (ShiftedHom.homEquiv (0 : ℤ) rfl).injective <| by
            simpa using hfg
        · intro x
          refine ⟨(ShiftedHom.homEquiv (0 : ℤ) rfl).symm x, ?_⟩
          exact (ShiftedHom.homEquiv (0 : ℤ) rfl).apply_symm_apply x)).symm

/-- The canonical degree-zero comparison
`H^0(L \otimes_A^{\mathbf L} K^\vee) \to \operatorname{Ext}^0_A(K, L)`. -/
noncomputable def derivedDualTensorExtZeroComparison
    (H : RHomPkg) (K L : DMod) :
    ((𝓗 0).obj (L ⊗[A]^L Kᵛ⟮H⟯)) →ₗ[A] Ext^((0 : ℤ))(K, L) :=
  (derivedHom_cohomology_iso_shiftedHom H K L (0 : ℤ)).toLinearMap.comp
    (derivedDualTensorZeroCohomologyComparison H K L).hom

-- Proof sketch: apply degree-zero cohomology to the tensor/Hom comparison from part `(3)`, then
-- identify the target with the chapter owner `Ext^0_A(K, L)` via the standard degree-zero
-- cohomology/internal-Hom comparison.
/-- Lemma 15.75.15 (4): if `K` is perfect, then the induced degree-zero comparison
`H^0(L \otimes_A^{\mathbf L} K^\vee) \to \operatorname{Ext}^0_A(K, L)` is bijective. -/
theorem derivedDualTensorZeroCohomology_iso_extZero
    (H : RHomPkg)
    {K : DMod} (hK : DerivedCategory.IsPerfect K) (L : DMod) :
    Function.Bijective (derivedDualTensorExtZeroComparison H K L) := by
  let f := (derivedHom_cohomology_iso_shiftedHom H K L (0 : ℤ)).toLinearMap
  have hf : Function.Bijective f := by
    simpa [f] using (derivedHom_cohomology_iso_shiftedHom H K L (0 : ℤ)).bijective
  letI : IsIso (derivedDualTensorZeroCohomologyComparison H K L) :=
    derivedDualTensorZeroCohomologyComparison_isIso_of_isPerfect H hK L
  let hg := ConcreteCategory.bijective_of_isIso
    (derivedDualTensorZeroCohomologyComparison H K L)
  refine ⟨?_, ?_⟩
  · intro x y hxy
    exact hg.1 (hf.1 hxy)
  · intro z
    obtain ⟨w, hw⟩ := hf.2 z
    obtain ⟨x, hx⟩ := hg.2 w
    refine ⟨x, ?_⟩
    simpa [derivedDualTensorExtZeroComparison, hw] using (congrArg f hx).trans hw

/-- For a perfect object `K`, the degree-zero comparison identifies
`H^0(L \otimes_A^{\mathbf L} K^\vee)` with `\operatorname{Ext}^0_A(K, L)` as an `A`-linear
equivalence. -/
noncomputable def derivedDualTensorExtZeroEquiv
    (H : RHomPkg) {K : DMod} (hK : DerivedCategory.IsPerfect K) (L : DMod) :
    ((𝓗 0).obj (L ⊗[A]^L Kᵛ⟮H⟯)) ≃ₗ[A] Ext^((0 : ℤ))(K, L) :=
  LinearEquiv.ofBijective
    (derivedDualTensorExtZeroComparison H K L)
    (derivedDualTensorZeroCohomology_iso_extZero H hK L)

/-- Companion bridge: the degree-zero comparison specialized from `Ext^0_A(K, L)` to the ordinary
morphism module `Hom_{D(A)}(K, L)`. -/
noncomputable def derivedDualTensorZeroLinearComparison
    (H : RHomPkg) (K L : DMod) :
    ((𝓗 0).obj (L ⊗[A]^L Kᵛ⟮H⟯)) →ₗ[A] (K ⟶ L) :=
  (shiftedHomZeroLinearEquiv K L).toLinearMap.comp
    (derivedDualTensorExtZeroComparison H K L)

/-- Companion bridge: for a perfect object `K`, the degree-zero comparison identifies
`H^0(L \otimes_A^{\mathbf L} K^\vee)` with `Hom_{D(A)}(K, L)` after transporting
`Ext^0_A(K, L)` across the canonical degree-zero equivalence. -/
noncomputable def derivedDualTensorZeroLinearEquiv
    (H : RHomPkg) {K : DMod} (hK : DerivedCategory.IsPerfect K) (L : DMod) :
    ((𝓗 0).obj (L ⊗[A]^L Kᵛ⟮H⟯)) ≃ₗ[A] (K ⟶ L) :=
  (derivedDualTensorExtZeroEquiv H hK L).trans (shiftedHomZeroLinearEquiv K L)

end

end CategoryTheory
