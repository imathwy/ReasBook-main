import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits ComplexShape HomotopyCategory

noncomputable section

universe v₁ u₁ v₂ u₂ v₃ u₃

set_option checkBinderAnnotations false

section

variable {𝒜 : Type u₁} {ℬ : Type u₂} {𝒞 : Type u₃}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ] [Category.{v₃} 𝒞]
  [Preadditive 𝒜] [Preadditive ℬ] [Preadditive 𝒞]
  [HasZeroObject 𝒜] [HasZeroObject ℬ] [HasZeroObject 𝒞]
  [HasBinaryBiproducts 𝒜] [HasBinaryBiproducts ℬ] [HasBinaryBiproducts 𝒞]
  [HasCountableCoproducts 𝒞]

variable (tensor : 𝒜 ⥤ ℬ ⥤ 𝒞)
variable [tensor.Additive] [∀ X : 𝒜, (tensor.obj X).Additive]
variable [∀ (X : CochainComplex 𝒜 ℤ) (Y : CochainComplex ℬ ℤ),
  CochainComplex.HasMapBifunctor X Y tensor]

/-- A bilinear bifunctor preserves zero morphisms in the first variable. -/
noncomputable instance tensor_preservesZeroMorphisms : tensor.PreservesZeroMorphisms := sorry

/-- For a fixed left tensor factor, the induced functor preserves zero morphisms. -/
noncomputable instance tensor_obj_preservesZeroMorphisms (X : 𝒜) :
    (tensor.obj X).PreservesZeroMorphisms := sorry

-- Proof sketch: this is the identity case of `HomologicalComplex.mapBifunctorMap` with the left
-- factor fixed; the resulting morphism on total complexes is the identity.
/-- The complex-level tensor-totalization functor with fixed left factor preserves identities. -/
theorem tensor_right_complex_functor_map_id
    (X : CochainComplex 𝒜 ℤ) (Y : CochainComplex ℬ ℤ) :
    HomologicalComplex.mapBifunctorMap (𝟙 X) (𝟙 Y) tensor (ComplexShape.up ℤ) =
      𝟙 (CochainComplex.mapBifunctor X Y tensor) := sorry

-- Proof sketch: functoriality of `HomologicalComplex.mapBifunctorMap` in the varying right factor
-- gives the composition law after totalization.
/-- The complex-level tensor-totalization functor with fixed left factor preserves composition. -/
theorem tensor_right_complex_functor_map_comp
    (X : CochainComplex 𝒜 ℤ) {Y₁ Y₂ Y₃ : CochainComplex ℬ ℤ}
    (φ : Y₁ ⟶ Y₂) (ψ : Y₂ ⟶ Y₃) :
    HomologicalComplex.mapBifunctorMap (𝟙 X) (φ ≫ ψ) tensor (ComplexShape.up ℤ) =
      HomologicalComplex.mapBifunctorMap (𝟙 X) φ tensor (ComplexShape.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 X) ψ tensor (ComplexShape.up ℤ) := sorry

/-- The complex-level functor `Y^\bullet ↦ \mathrm{Tot}(X^\bullet \otimes Y^\bullet)` for a fixed
left tensor factor `X^\bullet`. -/
abbrev tensor_right_complex_functor (X : CochainComplex 𝒜 ℤ) :
    CochainComplex ℬ ℤ ⥤ CochainComplex 𝒞 ℤ where
  obj Y := CochainComplex.mapBifunctor X Y tensor
  map φ := HomologicalComplex.mapBifunctorMap (𝟙 X) φ tensor (ComplexShape.up ℤ)
  map_id Y := tensor_right_complex_functor_map_id tensor X Y
  map_comp φ ψ := tensor_right_complex_functor_map_comp tensor X φ ψ

-- Proof sketch: this is the identity case of `HomologicalComplex.mapBifunctorMap` with the right
-- factor fixed; the resulting total-complex morphism is the identity.
/-- The complex-level tensor-totalization functor with fixed right factor preserves identities. -/
theorem tensor_left_complex_functor_map_id
    (Y : CochainComplex ℬ ℤ) (X : CochainComplex 𝒜 ℤ) :
    HomologicalComplex.mapBifunctorMap (𝟙 X) (𝟙 Y) tensor (ComplexShape.up ℤ) =
      𝟙 (CochainComplex.mapBifunctor X Y tensor) := sorry

-- Proof sketch: functoriality of `HomologicalComplex.mapBifunctorMap` in the varying left factor
-- gives the composition law after totalization.
/-- The complex-level tensor-totalization functor with fixed right factor preserves composition. -/
theorem tensor_left_complex_functor_map_comp
    (Y : CochainComplex ℬ ℤ) {X₁ X₂ X₃ : CochainComplex 𝒜 ℤ}
    (φ : X₁ ⟶ X₂) (ψ : X₂ ⟶ X₃) :
    HomologicalComplex.mapBifunctorMap (φ ≫ ψ) (𝟙 Y) tensor (ComplexShape.up ℤ) =
      HomologicalComplex.mapBifunctorMap φ (𝟙 Y) tensor (ComplexShape.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap ψ (𝟙 Y) tensor (ComplexShape.up ℤ) := sorry

/-- The complex-level functor `X^\bullet ↦ \mathrm{Tot}(X^\bullet \otimes Y^\bullet)` for a fixed
right tensor factor `Y^\bullet`. -/
abbrev tensor_left_complex_functor (Y : CochainComplex ℬ ℤ) :
    CochainComplex 𝒜 ℤ ⥤ CochainComplex 𝒞 ℤ where
  obj X := CochainComplex.mapBifunctor X Y tensor
  map φ := HomologicalComplex.mapBifunctorMap φ (𝟙 Y) tensor (ComplexShape.up ℤ)
  map_id X := tensor_left_complex_functor_map_id tensor Y X
  map_comp φ ψ := tensor_left_complex_functor_map_comp tensor Y φ ψ

/-- A homotopy in the varying right complex induces a homotopy after tensor-totalization with a
fixed left factor. -/
  noncomputable def tensor_right_homotopy_of_homotopy
    (X : CochainComplex 𝒜 ℤ) {L M : CochainComplex ℬ ℤ} {α β : L ⟶ M} (h : Homotopy α β) :
    Homotopy
      (HomologicalComplex.mapBifunctorMap (𝟙 X) α tensor (ComplexShape.up ℤ))
      (HomologicalComplex.mapBifunctorMap (𝟙 X) β tensor (ComplexShape.up ℤ)) :=
  HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 X) h tensor (ComplexShape.up ℤ)

/-- A homotopy in the varying left complex induces a homotopy after tensor-totalization with a
fixed right factor. -/
noncomputable def tensor_left_homotopy_of_homotopy
    (Y : CochainComplex ℬ ℤ) {L M : CochainComplex 𝒜 ℤ} {α β : L ⟶ M} (h : Homotopy α β) :
    Homotopy
      (HomologicalComplex.mapBifunctorMap α (𝟙 Y) tensor (ComplexShape.up ℤ))
      (HomologicalComplex.mapBifunctorMap β (𝟙 Y) tensor (ComplexShape.up ℤ)) :=
  HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 Y) tensor (ComplexShape.up ℤ)

/-- The functor on `K(\mathcal B)` induced by tensor-totalization with a fixed left factor
`X^\bullet`. -/
abbrev tensor_right_homotopy_functor (X : CochainComplex 𝒜 ℤ) :
    HomotopyCategory ℬ (up ℤ) ⥤ HomotopyCategory 𝒞 (up ℤ) :=
  CategoryTheory.Quotient.lift _
    (tensor_right_complex_functor tensor X ⋙ HomotopyCategory.quotient 𝒞 (up ℤ))
    (fun _ _ _ _ ⟨h⟩ ↦
      HomotopyCategory.eq_of_homotopy _ _ (tensor_right_homotopy_of_homotopy tensor X h))

/-- The functor on `K(\mathcal A)` induced by tensor-totalization with a fixed right factor
`Y^\bullet`. -/
abbrev tensor_left_homotopy_functor (Y : CochainComplex ℬ ℤ) :
    HomotopyCategory 𝒜 (up ℤ) ⥤ HomotopyCategory 𝒞 (up ℤ) :=
  CategoryTheory.Quotient.lift _
    (tensor_left_complex_functor tensor Y ⋙ HomotopyCategory.quotient 𝒞 (up ℤ))
    (fun _ _ _ _ ⟨h⟩ ↦
      HomotopyCategory.eq_of_homotopy _ _ (tensor_left_homotopy_of_homotopy tensor Y h))

/-- The homotopy-category functor induced by a fixed left tensor factor commutes with shifts. -/
noncomputable instance tensor_right_homotopy_functor_commShift (X : CochainComplex 𝒜 ℤ) :
    (tensor_right_homotopy_functor tensor X).CommShift ℤ := sorry

/-- The homotopy-category functor induced by a fixed right tensor factor commutes with shifts. -/
noncomputable instance tensor_left_homotopy_functor_commShift (Y : CochainComplex ℬ ℤ) :
    (tensor_left_homotopy_functor tensor Y).CommShift ℤ := sorry

-- Proof sketch: apply Remark 13.10.8 to the double complexes obtained from the bifunctor `tensor`.
-- The induced functors on complexes respect homotopies by
-- `HomologicalComplex.mapBifunctorMapHomotopy₂` and
-- `HomologicalComplex.mapBifunctorMapHomotopy₁`, so they descend to `K(\mathcal B)` and
-- `K(\mathcal A)`. Exactness is encoded by `Functor.IsTriangulated`. For the right-variable shift,
-- the canonical isomorphism is the signed `CochainComplex.mapBifunctorShift₂Iso`.
/-- Remark 13.10.9: fixing either factor of a bilinear functor
`\otimes : \mathcal A ⥤ \mathcal B ⥤ \mathcal C` yields an exact functor on homotopy categories,
namely `Y^\bullet ↦ \mathrm{Tot}(X^\bullet \otimes Y^\bullet)` on `K(\mathcal B)` and
`X^\bullet ↦ \mathrm{Tot}(X^\bullet \otimes Y^\bullet)` on `K(\mathcal A)`. -/
theorem tensor_left_right_homotopy_functor_isTriangulated
    (X : CochainComplex 𝒜 ℤ) (Y : CochainComplex ℬ ℤ) :
    (tensor_right_homotopy_functor tensor X).IsTriangulated ∧
      (tensor_left_homotopy_functor tensor Y).IsTriangulated := sorry

end
