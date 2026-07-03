import Mathlib
import StacksProject_2024.Chap15.Lemma_15_59_15
import StacksProject_2024.Chap15.Lemma_15_74_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "RHomPkg" => MonoidalClosed DMod

open scoped DerivedInternalHom
open scoped DerivedTensorProduct

/-
Domain-style sampling for Lemma 15.74.3:
- primary domain: tensor/internal-Hom comparison morphisms on `D(R)`;
- sampled owner declarations:
  `CategoryTheory.MonoidalClosed.derivedTensorAdj`,
  `CategoryTheory.derivedInternalHom_comp`,
  `CategoryTheory.MonoidalClosed.compTranspose`,
  `CategoryTheory.derivedTensorProduct_associator`,
  `CategoryTheory.derivedTensorProduct_comm`;
- best owner abstraction:
  `source-facing`: the canonical tensor-right comparison morphism
  `RHom_R(L, M) ⊗^L_R K ⟶ RHom_R(RHom_R(K, L), M)`;
  `core/canonical`: the owner `H : MonoidalClosed DMod`, together with the established tensor owner
  `derivedTensorProduct`;
  `bridge/view`: the adjoint transpose of the composition-evaluation composite below;
- primitive data: the chosen monoidal-closed owner `H`, the canonical composition morphism
  `derivedInternalHom_comp`, and the tensor associativity/commutativity isomorphisms;
- derived API: the tensor-right comparison map itself and its naturality in `K`, `L`, and `M`.

The source-facing owner here is therefore a single canonical comparison morphism, not the full
type of arbitrary natural transformations between the associated trivariant functors.
-/

private noncomputable def derivedInternalHom_tensor_right_comparisonTranspose
    (H : RHomPkg) (K L M : DMod) :
    ((RHom[H](L, M) ⊗[R]^L K) ⊗[R]^L (RHom[H](K, L))) ⟶ M :=
  let _ : RHomPkg := H
  (derivedTensorProduct_associator (RHom[H](L, M)) K (RHom[H](K, L))).hom ≫
      (derivedTensorProductMap H ((derivedTensorProduct_comm K (RHom[H](K, L))).hom)).app
        (RHom[H](L, M)) ≫
    (derivedTensorProduct_associator (RHom[H](L, M)) (RHom[H](K, L)) K).inv ≫
      (derivedTensorProduct K).map (derivedInternalHom_comp H K L M) ≫
        (H.derivedTensorAdj K).counit.app M

-- Proof sketch: curry the composite
-- `((RHom_R(L, M) ⊗^L K) ⊗^L RHom_R(K, L)) ⟶ M`
-- obtained by swapping `K` and `RHom_R(K, L)`, composing
-- `RHom_R(L, M) ⊗^L RHom_R(K, L) ⟶ RHom_R(K, M)`, and then evaluating at `K`.
/-- Lemma 15.74.3: for a chosen derived internal Hom on `D(R)`, there is a canonical morphism
`R\mathrm{Hom}_R(L, M) \otimes_R^{\mathbf L} K \to
R\mathrm{Hom}_R(R\mathrm{Hom}_R(K, L), M)` in `D(R)`. -/
noncomputable def derivedInternalHom_tensor_right_comparison
    (H : RHomPkg) (K L M : DMod) :
    (RHom[H](L, M) ⊗[R]^L K) ⟶ RHom[H](RHom[H](K, L), M) :=
  let _ : RHomPkg := H
  (H.derivedTensorAdj (RHom[H](K, L))).homEquiv _ _
    (derivedInternalHom_tensor_right_comparisonTranspose H K L M)

-- Proof sketch: this is immediate from the definition as the adjoint transpose of
-- `derivedInternalHom_tensor_right_comparisonTranspose`.
/-- Applying the inverse adjunction equivalence to the tensor-right comparison recovers the
defining composition-evaluation transpose. -/
theorem derivedInternalHom_tensor_right_comparison_def
    (H : RHomPkg) (K L M : DMod) :
    ((H.derivedTensorAdj (RHom[H](K, L))).homEquiv _ _).symm
        (derivedInternalHom_tensor_right_comparison H K L M) =
      derivedInternalHom_tensor_right_comparisonTranspose H K L M := by
  sorry

-- Proof sketch: both sides are mates, under
-- `- ⊗^L_R RHom_R(K₂, L) ⊣ RHom_R(RHom_R(K₂, L), -)`, of the same morphism built from the
-- functoriality of the tensor factor `K` and the composition map `derivedInternalHom_comp`.
/-- The tensor-right comparison is natural in the tensor factor `K`. -/
theorem derivedInternalHom_tensor_right_comparison_natural_tensor
    (H : RHomPkg)
    {K₁ K₂ L M : DMod} (fK : K₁ ⟶ K₂) :
    CommSq
      ((derivedTensorProductMap H fK).app (RHom[H](L, M)))
      (derivedInternalHom_tensor_right_comparison H K₁ L M)
      (derivedInternalHom_tensor_right_comparison H K₂ L M)
      (derivedInternalHomMap H (derivedInternalHomMap H fK (𝟙 L)) (𝟙 M)) := by
  sorry

-- Proof sketch: both composites are mates of the same map out of
-- `((RHom_R(L₁, M) ⊗^L K) ⊗^L RHom_R(K, L₁))`, comparing the route that first changes `L`
-- inside `RHom_R(L, M)` with the route that first changes the argument `RHom_R(K, L)` of the
-- outer internal Hom.
/-- The tensor-right comparison is contravariantly natural in the source variable `L` of the
inner internal Hom. -/
theorem derivedInternalHom_tensor_right_comparison_natural_source
    (H : RHomPkg) (K : DMod)
    {L₁ L₂ M : DMod} (fL : L₁ ⟶ L₂) :
    CommSq
      ((derivedTensorProduct K).map (derivedInternalHomMap H fL (𝟙 M)))
      (derivedInternalHom_tensor_right_comparison H K L₂ M)
      (derivedInternalHom_tensor_right_comparison H K L₁ M)
      (derivedInternalHomMap H (derivedInternalHomMap H (𝟙 K) fL) (𝟙 M)) := by
  sorry

-- Proof sketch: both sides are mates, under
-- `- ⊗^L_R RHom_R(K, L) ⊣ RHom_R(RHom_R(K, L), -)`, of the map obtained by functoriality of
-- `RHom_R(L, -)` in the target variable `M`.
/-- The tensor-right comparison is natural in the target variable `M`. -/
theorem derivedInternalHom_tensor_right_comparison_natural_target
    (H : RHomPkg) (K L : DMod)
    {M₁ M₂ : DMod} (fM : M₁ ⟶ M₂) :
    CommSq
      ((derivedTensorProduct K).map (derivedInternalHomMap H (𝟙 L) fM))
      (derivedInternalHom_tensor_right_comparison H K L M₁)
      (derivedInternalHom_tensor_right_comparison H K L M₂)
      (derivedInternalHomMap H (𝟙 (RHom[H](K, L))) fM) := by
  sorry

end

end CategoryTheory
