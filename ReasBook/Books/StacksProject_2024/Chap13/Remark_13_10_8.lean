import Mathlib
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex₂ HomotopyCategory

noncomputable section

universe v u

variable (𝒜 : Type u) [Category.{v} 𝒜] [Preadditive 𝒜]
  [HasZeroObject 𝒜] [HasBinaryBiproducts 𝒜] [HasCountableCoproducts 𝒜]

/- Domain-style sampling:
- primary domain: totalization of cohomological double complexes and the induced exact functors on
  homotopy categories;
- sampled owner declarations:
  `CategoryTheory.Functor.mapHomotopyCategory`,
  `HomologicalComplex₂.flipFunctor`,
  `HomologicalComplex₂.totalFunctor`,
  `Functor.CommShift`,
  `Functor.IsTriangulated`;
- best owner abstraction: the two source-facing totalization functors on homotopy categories are
  the canonical owner `F.mapHomotopyCategory (up ℤ)` applied to the additive complex-level
  functors `totalFunctor` and `flipFunctor ⋙ totalFunctor`; this remark should record only the
  inherited `Functor.CommShift` and `Functor.IsTriangulated` structures on those owners, not
  rebuild the quotient lifts by hand;
- primitive data: the complex-level functors `totalFunctor 𝒜 (up ℤ) (up ℤ) (up ℤ)` and
  `flipFunctor 𝒜 (up ℤ) (up ℤ) ⋙ totalFunctor 𝒜 (up ℤ) (up ℤ) (up ℤ)`, together with their
  additive structures;
- derived API: the canonical homotopy-category functors obtained via `Functor.mapHomotopyCategory`
  and their inherited `CommShift` and `IsTriangulated` instances.
- source/core/bridge triage:
  `source-facing`: the two totalization functors on the homotopy category of double complexes;
  `core/canonical`: `Functor.mapHomotopyCategory`, `Functor.CommShift`, and
    `Functor.IsTriangulated`;
  `bridge/view`: the two source-facing functors are the instances of
    `Functor.mapHomotopyCategory (up ℤ)` attached to `totalFunctor` and
    `flipFunctor ⋙ totalFunctor`.

This file therefore records Remark 13.10.8 by direct owner recall on
`mapHomotopyCategory`, without a parallel public totalization-functor API. -/

local instance : HasBinaryBiproducts (HomologicalComplex 𝒜 (up ℤ)) where
  has_binary_biproduct K L := by
    let _ : ∀ i : ℤ, HasBinaryBiproduct (K.X i) (L.X i) := fun _ ↦ inferInstance
    infer_instance

local instance : HasBinaryBiproducts (HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) where
  has_binary_biproduct K L := by
    delta HomologicalComplex₂
    infer_instance

local instance : (flipFunctor 𝒜 (up ℤ) (up ℤ)).Additive where
  map_add := by
    intro K L f g
    ext i j
    rfl

local instance : (totalFunctor 𝒜 (up ℤ) (up ℤ) (up ℤ)).Additive where
  map_add := by
    intro K L f g
    ext i
    apply HomologicalComplex₂.total.hom_ext
    intro i₁ i₂ h
    change K.ιTotal (up ℤ) i₁ i₂ i h ≫ (total.map (f + g) (up ℤ)).f i =
      K.ιTotal (up ℤ) i₁ i₂ i h ≫ ((total.map f (up ℤ)).f i + (total.map g (up ℤ)).f i)
    rw [Preadditive.comp_add]
    simp [Preadditive.add_comp]

/- Remark 13.10.8: viewing a double complex as
`\cdots \to A^{\bullet,-1} \to A^{\bullet,0} \to A^{\bullet,1} \to \cdots`, the induced
totalization functor on homotopy categories is the canonical owner
`(flipFunctor ⋙ totalFunctor).mapHomotopyCategory (up ℤ)`, and its exactness API is the inherited
`CommShift`/`IsTriangulated` structure on that owner. -/
#check
  (inferInstance :
    (((flipFunctor 𝒜 (up ℤ) (up ℤ)) ⋙ totalFunctor 𝒜 (up ℤ) (up ℤ) (up ℤ)).mapHomotopyCategory
      (up ℤ)).CommShift ℤ)

#check
  (inferInstance :
    (((flipFunctor 𝒜 (up ℤ) (up ℤ)) ⋙ totalFunctor 𝒜 (up ℤ) (up ℤ) (up ℤ)).mapHomotopyCategory
      (up ℤ)).IsTriangulated)

/- Viewing a double complex instead as
`\cdots \to A^{-1,\bullet} \to A^{0,\bullet} \to A^{1,\bullet} \to \cdots`, the induced
totalization functor on homotopy categories is the canonical owner
`(totalFunctor 𝒜 (up ℤ) (up ℤ) (up ℤ)).mapHomotopyCategory (up ℤ)`, again with the inherited
`CommShift`/`IsTriangulated` structure. -/
#check
  (inferInstance :
    ((totalFunctor 𝒜 (up ℤ) (up ℤ) (up ℤ)).mapHomotopyCategory (up ℤ)).CommShift ℤ)

#check
  (inferInstance :
    ((totalFunctor 𝒜 (up ℤ) (up ℤ) (up ℤ)).mapHomotopyCategory (up ℤ)).IsTriangulated)
