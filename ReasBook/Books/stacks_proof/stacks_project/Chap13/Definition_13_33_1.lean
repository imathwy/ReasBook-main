import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v u

noncomputable section

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [Preadditive D]

/- Domain-style sampling for Definition 13.33.1:
- primary domain: telescope triangles for sequential diagrams in a preadditive / triangulated
  category;
- sampled owner declarations:
  `CategoryTheory.Functor.ofSequence`,
  `CategoryTheory.Functor.ofSequence_map_homOfLE_succ`,
  `CategoryTheory.Limits.Sigma.map'`,
  `CategoryTheory.Limits.Sigma.ι_comp_map'`;
- best owner abstraction: the canonical sequential diagram `K : ℕ ⥤ D`;
- primitive-vs-derived split:
  the primitive data are the diagram `K`;
  the telescope endomorphism and the homotopy-colimit predicate are derived API built from `K`.

Source/core/bridge triage:
- `source-facing`: the telescope morphism `1 - f` and the distinguished-triangle predicate
  defining a homotopy colimit of a sequential diagram;
- `core/canonical`: the owner `K : ℕ ⥤ D`;
- `bridge/view`: `Functor.ofSequence`, used downstream to pass from a textbook family
  `K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯` to the canonical owner. -/

/-- The telescope endomorphism `1 - f` of the coproduct of a sequential diagram. -/
def sequentialTelescopeMap (K : ℕ ⥤ D) [HasCoproduct K.obj] :
    ∐ K.obj ⟶ ∐ K.obj :=
  𝟙 _ - Sigma.map' Nat.succ (fun n ↦ K.map (homOfLE (Nat.le_succ n)))

/-- On the `n`th coproduct summand, the telescope map is `1 - f_n`. -/
@[reassoc]
theorem Sigma.ι_comp_sequentialTelescopeMap (K : ℕ ⥤ D) [HasCoproduct K.obj] (n : ℕ) :
    Sigma.ι K.obj n ≫ sequentialTelescopeMap K =
      Sigma.ι K.obj n - K.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι K.obj (n + 1) := by
  simp [sequentialTelescopeMap, Preadditive.comp_sub]

attribute [simp] Sigma.ι_comp_sequentialTelescopeMap_assoc

/-- The telescope map is natural with respect to morphisms of sequential diagrams. -/
@[reassoc]
theorem sequentialTelescopeMap_naturality {K L : ℕ ⥤ D}
    [HasCoproduct K.obj] [HasCoproduct L.obj] (φ : K ⟶ L) :
    sequentialTelescopeMap K ≫ Limits.Sigma.map φ.app =
      Limits.Sigma.map φ.app ≫ sequentialTelescopeMap L := by
  apply Sigma.hom_ext
  intro n
  simp [sequentialTelescopeMap, Preadditive.comp_sub, Preadditive.sub_comp,
    φ.naturality_assoc]

end

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- Definition 13.33.1: assuming the direct sum `∐ n, K n` exists, an object `K∞` is a derived
colimit, or homotopy colimit, of a sequential system `K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯` if it occurs as the
third object of a distinguished triangle whose first morphism is the telescope map `1 - f`. -/
@[stacks 090Z]
def IsHomotopyColimitOf (K : ℕ ⥤ D) [HasCoproduct K.obj] (Khocolim : D) :
    Prop :=
  ∃ (g : ∐ K.obj ⟶ Khocolim) (h : Khocolim ⟶ (∐ K.obj)⟦(1 : ℤ)⟧),
    Triangle.mk (sequentialTelescopeMap K) g h ∈ distTriang D

end

end CategoryTheory
