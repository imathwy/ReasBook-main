import Mathlib
import stacks_proof.stacks_project.Chap15.Lemma_15_59_15
import stacks_proof.stacks_project.Chap15.Lemma_15_74_4

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

open scoped DerivedInternalHom DerivedTensorProduct

/- Domain-style sampling for 15.74.5:
- primary domain: tensor/internal-Hom comparison morphisms in the monoidal closed derived category
  `D(R)`;
- sampled owner declarations:
  `CategoryTheory.MonoidalClosed.derivedTensorAdj`,
  `CategoryTheory.ihom`,
  `CategoryTheory.derivedTensorProduct_associator`,
  `CategoryTheory.derivedTensorProductMap`,
  `CategoryTheory.derivedInternalHomMap`;
- best owner abstraction:
  `source-facing`: the canonical morphism
  `K ⊗^L RHom_R(M, L) ⟶ RHom_R(M, K ⊗^L L)`;
  `core/canonical`: the chosen owner `H : MonoidalClosed DMod`, the canonical internal-Hom object
  `RHom[H](M, L)`, the transported right adjunction `H.derivedTensorAdj M`, and the canonical
  associator for `⊗[R]^L`;
  `bridge/view`: the adjoint transpose of the evaluation composite below;
- primitive data vs. derived API: the primitive data are only the owner `H`, its counit map for
  `- ⊗[R]^L M ⊣ RHom[H](M,-)`, and the established tensor owner `⊗[R]^L`; the comparison map and
  its functoriality in `K`, `L`, and `M` are derived API.
-/
private noncomputable def derivedInternalHom_tensor_left_comparisonTranspose
    (H : RHomPkg)
    (K L M : DMod) :
    ((K ⊗[R]^L (RHom[H](M, L))) ⊗[R]^L M) ⟶ K ⊗[R]^L L :=
  (derivedTensorProduct_associator K (RHom[H](M, L)) M).hom ≫
    (derivedTensorProductMap H ((H.derivedTensorAdj M).counit.app L)).app K

/-- Lemma 15.74.5: in a monoidal closed structure on `D(R)`, there is a canonical morphism
`K \otimes_R^{\mathbf L} R\mathrm{Hom}_R(M, L) \to R\mathrm{Hom}_R(M, K \otimes_R^{\mathbf L} L)`
in `D(R)`. -/
@[stacks 0BYN]
noncomputable def derivedInternalHom_tensor_left_comparison
    (H : RHomPkg)
    (K L M : DMod) :
    (K ⊗[R]^L (RHom[H](M, L))) ⟶ RHom[H](M, K ⊗[R]^L L) :=
  (H.derivedTensorAdj M).homEquiv _ _
    (derivedInternalHom_tensor_left_comparisonTranspose H K L M)

-- Proof sketch: the comparison map is defined as the mate, under
-- `- ⊗[R]^L M ⊣ RHom_R(M,-)`, of the composite obtained by reassociating
-- `K ⊗[R]^L RHom_R(M,L) ⊗[R]^L M` and then applying the counit
-- `RHom_R(M,L) ⊗[R]^L M ⟶ L`.
/-- Applying the inverse adjunction equivalence to the tensor-left comparison recovers the
associativity-counit composite used to define it. -/
theorem derivedInternalHom_tensor_left_comparison_def
    (H : RHomPkg)
    (K L M : DMod) :
    ((H.derivedTensorAdj M).homEquiv _ _).symm
        (derivedInternalHom_tensor_left_comparison H K L M) =
      derivedInternalHom_tensor_left_comparisonTranspose H K L M := by
  simpa [derivedInternalHom_tensor_left_comparison]

/-- Helper for Lemma 15.74.5: the explicit transpose defining the tensor-left comparison is
natural in the tensor factor `K`. -/
private theorem derivedInternalHom_tensor_left_comparisonTranspose_natural_tensor
    (H : RHomPkg)
    {K₁ K₂ L M : DMod} (fK : K₁ ⟶ K₂) :
    ((derivedTensorProduct M).map ((derivedTensorProduct (RHom[H](M, L))).map fK)) ≫
        derivedInternalHom_tensor_left_comparisonTranspose H K₂ L M =
      derivedInternalHom_tensor_left_comparisonTranspose H K₁ L M ≫
        ((derivedTensorProduct M).map ((derivedTensorProduct L).map fK)) := by
  -- Move `fK` across the associator first, then apply naturality of tensoring by the counit map.
  have h_assoc :
      ((derivedTensorProduct M).map ((derivedTensorProduct (RHom[H](M, L))).map fK)) ≫
          (derivedTensorProduct_associator K₂ (RHom[H](M, L)) M).hom =
        (derivedTensorProduct_associator K₁ (RHom[H](M, L)) M).hom ≫
          (derivedTensorProduct ((RHom[H](M, L)) ⊗[R]^L M)).map fK := by
    simpa [derivedTensorProduct_associator, Functor.comp_map] using
      (derivedTensorProductTensorIso (RHom[H](M, L)) M).hom.naturality fK
  have h_eval :
      (derivedTensorProduct ((RHom[H](M, L)) ⊗[R]^L M)).map fK ≫
          (derivedTensorProductMap H ((H.derivedTensorAdj M).counit.app L)).app K₂ =
        (derivedTensorProductMap H ((H.derivedTensorAdj M).counit.app L)).app K₁ ≫
          ((derivedTensorProduct M).map ((derivedTensorProduct L).map fK)) := by
    simpa using
      (derivedTensorProductMap H ((H.derivedTensorAdj M).counit.app L)).naturality fK
  -- The composite transpose is therefore functorial in `K`.
  calc
    ((derivedTensorProduct M).map ((derivedTensorProduct (RHom[H](M, L))).map fK)) ≫
        derivedInternalHom_tensor_left_comparisonTranspose H K₂ L M
      =
        (((derivedTensorProduct M).map ((derivedTensorProduct (RHom[H](M, L))).map fK)) ≫
            (derivedTensorProduct_associator K₂ (RHom[H](M, L)) M).hom) ≫
          (derivedTensorProductMap H ((H.derivedTensorAdj M).counit.app L)).app K₂ := by
            simp [derivedInternalHom_tensor_left_comparisonTranspose, Category.assoc]
    _ =
        ((derivedTensorProduct_associator K₁ (RHom[H](M, L)) M).hom ≫
            (derivedTensorProduct ((RHom[H](M, L)) ⊗[R]^L M)).map fK) ≫
          (derivedTensorProductMap H ((H.derivedTensorAdj M).counit.app L)).app K₂ := by
            rw [h_assoc]
    _ =
        (derivedTensorProduct_associator K₁ (RHom[H](M, L)) M).hom ≫
          (((derivedTensorProduct ((RHom[H](M, L)) ⊗[R]^L M)).map fK) ≫
            (derivedTensorProductMap H ((H.derivedTensorAdj M).counit.app L)).app K₂) := by
              simp [Category.assoc]
    _ =
        (derivedTensorProduct_associator K₁ (RHom[H](M, L)) M).hom ≫
          ((derivedTensorProductMap H ((H.derivedTensorAdj M).counit.app L)).app K₁ ≫
            ((derivedTensorProduct M).map ((derivedTensorProduct L).map fK))) := by
              rw [h_eval]
    _ =
        derivedInternalHom_tensor_left_comparisonTranspose H K₁ L M ≫
          ((derivedTensorProduct M).map ((derivedTensorProduct L).map fK)) := by
            simp [derivedInternalHom_tensor_left_comparisonTranspose, Category.assoc]

-- Proof sketch: both sides are mates, under `- ⊗[R]^L M ⊣ RHom_R(M,-)`, of the same morphism
-- obtained by functoriality of the derived tensor product in the left variable together with the
-- canonical transpose defining `derivedInternalHom_tensor_left_comparison`.
/-- The tensor-left comparison is natural in the tensor factor `K`. -/
theorem derivedInternalHom_tensor_left_comparison_natural_tensor
    (H : RHomPkg)
    {K₁ K₂ L M : DMod} (fK : K₁ ⟶ K₂) :
    CommSq
      ((derivedTensorProduct (RHom[H](M, L))).map fK)
      (derivedInternalHom_tensor_left_comparison H K₁ L M)
      (derivedInternalHom_tensor_left_comparison H K₂ L M)
      (derivedInternalHomMap H (𝟙 M) ((derivedTensorProduct L).map fK)) := by
  refine ⟨?_⟩
  -- Compare the two morphisms after transporting them across the fixed adjunction
  -- `- ⊗[R]^L M ⊣ RHom_R(M,-)`.
  rw [Adjunction.homEquiv_naturality_right_square_iff]
  -- On the tensor side, both mates are the explicit transpose from the definition.
  simpa [derivedInternalHomMap, derivedInternalHom_tensor_left_comparison_def] using
    derivedInternalHom_tensor_left_comparisonTranspose_natural_tensor H fK

-- Proof sketch: compare the two mates of the canonical map out of
-- `((K ⊗[R]^L RHom_R(M,L₁)) ⊗[R]^L M)` obtained either by changing `L` first inside `RHom_R` or by
-- changing the target `K ⊗[R]^L L` after taking the comparison map.
/-- The tensor-left comparison is natural in the target variable `L` of the internal Hom. -/
theorem derivedInternalHom_tensor_left_comparison_natural_target
    (H : RHomPkg)
    (K M : DMod) {L₁ L₂ : DMod} (fL : L₁ ⟶ L₂) :
    CommSq
      ((derivedTensorProductMap H (derivedInternalHomMap H (𝟙 M) fL)).app K)
      (derivedInternalHom_tensor_left_comparison H K L₁ M)
      (derivedInternalHom_tensor_left_comparison H K L₂ M)
      (derivedInternalHomMap H (𝟙 M) ((derivedTensorProductMap H fL).app K)) := by
  sorry

-- Proof sketch: both composites are mates, under `- ⊗[R]^L M₁ ⊣ RHom_R(M₁,-)`, of the map
-- induced by contravariant functoriality of `RHom_R(-,L)` in its source variable.
/-- The tensor-left comparison is contravariantly natural in the source variable `M` of the
internal Hom. -/
theorem derivedInternalHom_tensor_left_comparison_natural_source
    (H : RHomPkg)
    (K L : DMod) {M₁ M₂ : DMod} (fM : M₂ ⟶ M₁) :
    CommSq
      ((derivedTensorProductMap H (derivedInternalHomMap H fM (𝟙 L))).app K)
      (derivedInternalHom_tensor_left_comparison H K L M₁)
      (derivedInternalHom_tensor_left_comparison H K L M₂)
      (derivedInternalHomMap H fM (𝟙 (K ⊗[R]^L L))) := by
  sorry

end

end CategoryTheory
