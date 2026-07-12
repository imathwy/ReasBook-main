import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits ComplexShape HomotopyCategory
open HomologicalComplex

noncomputable section

universe v₁ u₁ v₂ u₂ v₃ u₃

set_option checkBinderAnnotations false

section

variable {𝒜 : Type u₁} {ℬ : Type u₂} {𝒞 : Type u₃}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ] [Category.{v₃} 𝒞]
  [Preadditive 𝒜] [Preadditive ℬ] [Preadditive 𝒞]
  [HasBinaryBiproducts 𝒜] [HasBinaryBiproducts ℬ] [HasBinaryBiproducts 𝒞]

variable (tensor : 𝒜 ⥤ ℬ ⥤ 𝒞)
variable [tensor.Additive] [∀ X : 𝒜, (tensor.obj X).Additive]
variable [∀ (X : CochainComplex 𝒜 ℤ) (Y : CochainComplex ℬ ℤ),
  CochainComplex.HasMapBifunctor X Y tensor]

/- Domain-style sampling:
- primary domain: bilinear tensor-totalization on cochain complexes and its descent to homotopy
  categories;
- sampled owner declarations:
  `CategoryTheory.Functor.map₂CochainComplex`,
  `CategoryTheory.Functor.mapHomotopyCategory`,
  `HomologicalComplex.mapBifunctorMapHomotopy₁`,
  `HomologicalComplex.mapBifunctorMapHomotopy₂`,
  `Functor.CommShift`,
  `Functor.IsTriangulated`;
- best owner abstraction: the source-facing owners in this remark are the fixed-factor
  homotopy-category tensor functors
  `((tensor.map₂CochainComplex.obj X).mapHomotopyCategory (up ℤ))` and
  `(((tensor.map₂CochainComplex).flip.obj Y).mapHomotopyCategory (up ℤ))`, while their exactness
  layer is the canonical owner `Functor.IsTriangulated` on those descended functors;
- primitive vs derived:
  primitive data are the bifunctor `tensor`, a fixed left or right cochain complex, and the
  additive structures on the fixed-factor cochain-complex functors;
  the homotopy-category functors and their `CommShift`/`IsTriangulated` structures are derived by
  the canonical `Functor.mapHomotopyCategory` owner using the bifunctor-homotopy transport lemmas
  above;
- source/core/bridge triage:
  `source-facing`: the induced exact fixed-factor tensor functors on homotopy categories in
    Remark 13.10.9;
  `core/canonical`: `tensor.map₂CochainComplex`, `Functor.mapHomotopyCategory`,
    `HomologicalComplex.mapBifunctorMapHomotopy₁`,
    `HomologicalComplex.mapBifunctorMapHomotopy₂`, `CategoryTheory.Quotient.lift`,
    `Functor.CommShift`, and `Functor.IsTriangulated`;
  `bridge/view`: no separate public bridge owner is needed here; only the additive instance layer
    below is primitive support for the canonical owner. -/

instance cochainComplexHasBinaryBiproducts
    (D : Type*) [Category D] [Preadditive D] [HasBinaryBiproducts D] :
    HasBinaryBiproducts (CochainComplex D ℤ) where
  has_binary_biproduct K L := by
    let _ : ∀ i : ℤ, HasBinaryBiproduct (K.X i) (L.X i) := fun _ ↦ inferInstance
    infer_instance

instance map₂CochainComplex_obj_additive (X : CochainComplex 𝒜 ℤ) :
    ((tensor.map₂CochainComplex).obj X).Additive where
  map_add := by
    intro L M f g
    ext j
    apply mapBifunctor.hom_ext
    intro i₁ i₂ h
    change
      ιMapBifunctor X L tensor (up ℤ) i₁ i₂ j h ≫
          (mapBifunctorMap (𝟙 X) (f + g) tensor (up ℤ)).f j =
        ιMapBifunctor X L tensor (up ℤ) i₁ i₂ j h ≫
          ((mapBifunctorMap (𝟙 X) f tensor (up ℤ)).f j +
            (mapBifunctorMap (𝟙 X) g tensor (up ℤ)).f j)
    rw [Preadditive.comp_add]
    simp [Functor.map_add, Preadditive.comp_add]

instance map₂CochainComplex_flip_obj_additive (Y : CochainComplex ℬ ℤ) :
    ((tensor.map₂CochainComplex).flip.obj Y).Additive where
  map_add := by
    intro L M f g
    ext j
    apply mapBifunctor.hom_ext
    intro i₁ i₂ h
    change
      ιMapBifunctor L Y tensor (up ℤ) i₁ i₂ j h ≫
          (mapBifunctorMap (f + g) (𝟙 Y) tensor (up ℤ)).f j =
        ιMapBifunctor L Y tensor (up ℤ) i₁ i₂ j h ≫
          ((mapBifunctorMap f (𝟙 Y) tensor (up ℤ)).f j +
            (mapBifunctorMap g (𝟙 Y) tensor (up ℤ)).f j)
    rw [Preadditive.comp_add]
    simp [Functor.map_add, Preadditive.add_comp]

variable [HasZeroObject 𝒜] [HasZeroObject ℬ] [HasZeroObject 𝒞]
variable (X : CochainComplex 𝒜 ℤ) (Y : CochainComplex ℬ ℤ)

/- Remark 13.10.9: after fixing a left cochain-complex factor, the induced tensor-totalization
functor on homotopy categories is the canonical owner
`((tensor.map₂CochainComplex.obj X).mapHomotopyCategory (up ℤ))`, with inherited
`CommShift`/`IsTriangulated` structure. -/
#check
  (inferInstance :
    ((tensor.map₂CochainComplex.obj X).mapHomotopyCategory (up ℤ)).CommShift ℤ)

#check
  (inferInstance :
    ((tensor.map₂CochainComplex.obj X).mapHomotopyCategory (up ℤ)).IsTriangulated)

/- After fixing a right cochain-complex factor, the corresponding canonical owner is
`(((tensor.map₂CochainComplex).flip.obj Y).mapHomotopyCategory (up ℤ))`, again with inherited
`CommShift`/`IsTriangulated` structure. -/
#check
  (inferInstance :
    (((tensor.map₂CochainComplex).flip.obj Y).mapHomotopyCategory (up ℤ)).CommShift ℤ)

#check
  (inferInstance :
    (((tensor.map₂CochainComplex).flip.obj Y).mapHomotopyCategory (up ℤ)).IsTriangulated)

end
