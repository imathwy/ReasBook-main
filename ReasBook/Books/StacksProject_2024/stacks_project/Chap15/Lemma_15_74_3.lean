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
  -- The comparison map was defined as the adjoint mate of this transpose composite.
  simpa [derivedInternalHom_tensor_right_comparison]

/-- Helper for Lemma 15.74.3: the source-facing composition map is functorial in the target
object `M`. -/
theorem derivedInternalHom_comp_natural_target
    (H : RHomPkg) (K L : DMod)
    {M₁ M₂ : DMod} (fM : M₁ ⟶ M₂) :
    ((derivedTensorProduct (RHom[H](K, L))).map (derivedInternalHomMap H (𝟙 L) fM)) ≫
      derivedInternalHom_comp H K L M₂ =
        derivedInternalHom_comp H K L M₁ ≫ derivedInternalHomMap H (𝟙 K) fM := by
  -- TODO: unfold `derivedInternalHom_comp` once, move `fM` across the tensor/derived-tensor
  -- comparison and the braiding, and finish with the owner-level target naturality of
  -- `MonoidalClosed.comp K L -`.
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
  -- TODO: transport both sides through
  -- `- ⊗[R]^L RHom_R(K₂, L) ⊣ RHom_R(RHom_R(K₂, L), -)` and compare the resulting transposes
  -- using naturality of the associator, the braiding, `derivedTensorProductMap`, and
  -- `derivedInternalHom_comp`.
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
  -- TODO: move the square through the adjunction with right tensor factor `RHom_R(K, L₁)` and
  -- show both transposes equal the same composition/evaluation map after changing `L`.
  sorry

/-- Helper for Lemma 15.74.3: the first reassociation in the defining transpose is natural in the
target object `M`. -/
private theorem derivedInternalHom_tensor_right_comparisonTranspose_natural_target_assoc₁
    (H : RHomPkg) (K L : DMod)
    {M₁ M₂ : DMod} (fM : M₁ ⟶ M₂) :
    ((derivedTensorProduct (RHom[H](K, L))).map
        ((derivedTensorProduct K).map (derivedInternalHomMap H (𝟙 L) fM))) ≫
      (derivedTensorProduct_associator (RHom[H](L, M₂)) K (RHom[H](K, L))).hom =
        (derivedTensorProduct_associator (RHom[H](L, M₁)) K (RHom[H](K, L))).hom ≫
          (derivedTensorProduct (K ⊗[R]^L (RHom[H](K, L)))).map
            (derivedInternalHomMap H (𝟙 L) fM) := by
  -- Move the target-variable map across the first associator via naturality in the left tensor
  -- factor.
  simpa [derivedTensorProduct_associator, Functor.comp_map] using
    (derivedTensorProductTensorIso K (RHom[H](K, L))).hom.naturality
      (derivedInternalHomMap H (𝟙 L) fM)

/-- Helper for Lemma 15.74.3: the braiding step inside the defining transpose is natural in the
target object `M`. -/
private theorem derivedInternalHom_tensor_right_comparisonTranspose_natural_target_comm
    (H : RHomPkg) (K L : DMod)
    {M₁ M₂ : DMod} (fM : M₁ ⟶ M₂) :
    ((derivedTensorProduct (K ⊗[R]^L (RHom[H](K, L)))).map
        (derivedInternalHomMap H (𝟙 L) fM) ≫
      (derivedTensorProductMap H ((derivedTensorProduct_comm K (RHom[H](K, L))).hom)).app
        (RHom[H](L, M₂))) =
        (derivedTensorProductMap H ((derivedTensorProduct_comm K (RHom[H](K, L))).hom)).app
          (RHom[H](L, M₁)) ≫
          (derivedTensorProduct ((RHom[H](K, L)) ⊗[R]^L K)).map
            (derivedInternalHomMap H (𝟙 L) fM) := by
  -- The braiding-induced tensor map is a natural transformation in the outer internal-Hom slot.
  simpa using
    (derivedTensorProductMap H ((derivedTensorProduct_comm K (RHom[H](K, L))).hom)).naturality
      (derivedInternalHomMap H (𝟙 L) fM)

/-- Helper for Lemma 15.74.3: the second reassociation in the defining transpose is natural in
the target object `M`. -/
private theorem derivedInternalHom_tensor_right_comparisonTranspose_natural_target_assoc₂
    (H : RHomPkg) (K L : DMod)
    {M₁ M₂ : DMod} (fM : M₁ ⟶ M₂) :
    ((derivedTensorProduct (RHom[H](K, L) ⊗[R]^L K)).map
        (derivedInternalHomMap H (𝟙 L) fM)) ≫
      (derivedTensorProduct_associator (RHom[H](L, M₂)) (RHom[H](K, L)) K).inv =
        (derivedTensorProduct_associator (RHom[H](L, M₁)) (RHom[H](K, L)) K).inv ≫
          ((derivedTensorProduct K).map
            ((derivedTensorProduct (RHom[H](K, L))).map
              (derivedInternalHomMap H (𝟙 L) fM))) := by
  -- Move the target-variable map across the second associator using naturality of the inverse.
  simpa [derivedTensorProduct_associator, Functor.comp_map] using
    (derivedTensorProductTensorIso (RHom[H](K, L)) K).inv.naturality
      (derivedInternalHomMap H (𝟙 L) fM)

/-- Helper for Lemma 15.74.3: after transporting the public target-variable naturality square
through the fixed adjunction `- ⊗[R]^L RHom_R(K, L) ⊣ RHom_R(RHom_R(K, L), -)`, the two
transpose composites agree up to the remaining composition/evaluation naturality step. -/
private theorem derivedInternalHom_tensor_right_comparisonTranspose_natural_target
    (H : RHomPkg) (K L : DMod)
    {M₁ M₂ : DMod} (fM : M₁ ⟶ M₂) :
    ((derivedTensorProduct (RHom[H](K, L))).map
        ((derivedTensorProduct K).map (derivedInternalHomMap H (𝟙 L) fM))) ≫
      derivedInternalHom_tensor_right_comparisonTranspose H K L M₂ =
        derivedInternalHom_tensor_right_comparisonTranspose H K L M₁ ≫ fM := by
  have h_assoc₁ :=
    derivedInternalHom_tensor_right_comparisonTranspose_natural_target_assoc₁ H K L fM
  have h_comm :=
    derivedInternalHom_tensor_right_comparisonTranspose_natural_target_comm H K L fM
  have h_assoc₂ :=
    derivedInternalHom_tensor_right_comparisonTranspose_natural_target_assoc₂ H K L fM
  have h_comp := derivedInternalHom_comp_natural_target H K L fM
  have h_counit :
      (derivedTensorProduct K).map (derivedInternalHomMap H (𝟙 K) fM) ≫
          (H.derivedTensorAdj K).counit.app M₂ =
        (H.derivedTensorAdj K).counit.app M₁ ≫ fM := by
    -- The last step is exactly the counit naturality square of the fixed adjunction.
    simpa [derivedInternalHomMap] using (H.derivedTensorAdj K).counit.naturality fM
  -- TODO: after the three coherence steps above, the remaining comparison is exactly the
  -- target-variable naturality of `derivedInternalHom_comp H K L -`, followed by the counit
  -- naturality of `H.derivedTensorAdj K`.
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
  refine ⟨?_⟩
  -- Proof comment: transport the square across the fixed adjunction
  -- `- ⊗[R]^L RHom_R(K, L) ⊣ RHom_R(RHom_R(K, L), -)` and compare the explicit mates.
  simpa [derivedInternalHomMap, derivedInternalHom_tensor_right_comparison] using
    (Adjunction.homEquiv_naturality_left_square_iff
      (adj := H.derivedTensorAdj (RHom[H](K, L)))
      ((derivedTensorProduct K).map (derivedInternalHomMap H (𝟙 L) fM))
      (derivedInternalHom_tensor_right_comparisonTranspose H K L M₂)
      (derivedInternalHom_tensor_right_comparisonTranspose H K L M₁)
      fM).2
      (derivedInternalHom_tensor_right_comparisonTranspose_natural_target H K L fM)

end

end CategoryTheory
