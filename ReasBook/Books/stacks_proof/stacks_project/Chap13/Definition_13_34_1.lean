import Mathlib
import stacks_proof.stacks_project.Chap12.Definition_12_31_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Pretriangulated
open CategoryTheory.Limits
open Opposite

noncomputable section

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D]

/- Domain-style sampling for Definition 13.34.1:
- primary domain: sequential inverse systems in a triangulated category and their Milnor
  distinguished triangles;
- sampled owner declarations:
  `CategoryTheory.SequentialInverseSystem`,
  `CategoryTheory.SequentialInverseSystem.transitionMap`,
  `CategoryTheory.Limits.Pi.map'`,
  `CategoryTheory.IsHomotopyColimitOf`;
- best owner abstraction: the primitive owner is the chapter-level sequential inverse system
  `Ksys : SequentialInverseSystem D`, with the underlying family `n ↦ Ksys.obj (op n)` as the
  bridge view into countable products;
- primitive-vs-derived split:
  primitive data are only the inverse system `Ksys`;
  the Milnor product endomorphism and the derived-limit predicate are derived API built from that
  owner, and the shift contribution should use the canonical successor transition map
  `Ksys.transitionMap (Nat.le_succ n)` together with the canonical product reindexing morphism
  `Pi.map'`.

Source/core/bridge triage:
- `source-facing`: the existence of a product together with a Milnor triangle defining a derived
  limit of `Ksys`;
- `core/canonical`: the inverse-system owner `Ksys : SequentialInverseSystem D` together with the
  fixed-product Milnor-triangle predicate `HasMilnorTriangle`;
- `bridge/view`: the underlying family `inverseSystemFamily Ksys` and the Milnor difference map on
  its product. -/

/-- The family of objects underlying a sequential inverse system in a category. -/
abbrev inverseSystemFamily (Ksys : SequentialInverseSystem D) : ℕ → D :=
  fun n ↦ Ksys.obj (op n)

end

section

variable {D : Type u} [Category.{v} D] [Preadditive D]

/-- The Milnor difference endomorphism of `∏ K_n`, equal to `1 - shift`. -/
def derivedLimitDifferenceMap (Ksys : SequentialInverseSystem D)
    [HasProduct (inverseSystemFamily Ksys)] :
    ∏ᶜ inverseSystemFamily Ksys ⟶ ∏ᶜ inverseSystemFamily Ksys :=
  𝟙 _ - Pi.map' Nat.succ (fun n ↦ Ksys.transitionMap (Nat.le_succ n))

theorem derivedLimitDifferenceMap_comp_π (Ksys : SequentialInverseSystem D)
    [HasProduct (inverseSystemFamily Ksys)] (n : ℕ) :
    derivedLimitDifferenceMap Ksys ≫ Pi.π (inverseSystemFamily Ksys) n =
      Pi.π (inverseSystemFamily Ksys) n -
        Pi.π (inverseSystemFamily Ksys) (n + 1) ≫ Ksys.transitionMap (Nat.le_succ n) := by
  simp [derivedLimitDifferenceMap, Preadditive.sub_comp]

attribute [reassoc] derivedLimitDifferenceMap_comp_π
attribute [simp] derivedLimitDifferenceMap_comp_π derivedLimitDifferenceMap_comp_π_assoc

end

namespace SequentialInverseSystem

section

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasCountableProducts D] [HasCokernels D]

/-- The first right derived inverse limit of a sequential inverse system, presented by the
standard Milnor cokernel model. -/
abbrev firstDerivedLimit (Ksys : SequentialInverseSystem D) :=
  cokernel (derivedLimitDifferenceMap Ksys)

private abbrev productMap {Ksys Lsys : SequentialInverseSystem D} (φ : Ksys ⟶ Lsys) :
    ∏ᶜ inverseSystemFamily Ksys ⟶ ∏ᶜ inverseSystemFamily Lsys :=
  Pi.lift fun n ↦
    Pi.π (inverseSystemFamily Ksys) n ≫ φ.app (op n)

private theorem derivedLimitDifferenceMap_naturality
    {Ksys Lsys : SequentialInverseSystem D} (φ : Ksys ⟶ Lsys) :
    derivedLimitDifferenceMap Ksys ≫ productMap φ =
      productMap φ ≫ derivedLimitDifferenceMap Lsys := by
  -- Compare both Milnor endomorphisms after projection to each stage.
  apply Pi.hom_ext
  intro n
  -- Proof comment: record the projection formula for the product map at stages `n` and `n + 1`.
  have hπ :
      productMap φ ≫ Pi.π (inverseSystemFamily Lsys) n =
        Pi.π (inverseSystemFamily Ksys) n ≫ φ.app (op n) := by
    simpa [productMap] using
      (Pi.lift_π
        (fun m ↦ Pi.π (inverseSystemFamily Ksys) m ≫ φ.app (op m))
        n)
  have hπsucc :
      productMap φ ≫ Pi.π (inverseSystemFamily Lsys) (n + 1) =
        Pi.π (inverseSystemFamily Ksys) (n + 1) ≫ φ.app (op (n + 1)) := by
    simpa [productMap] using
      (Pi.lift_π
        (fun m ↦ Pi.π (inverseSystemFamily Ksys) m ≫ φ.app (op m))
        (n + 1))
  -- Proof comment: expand the target-side Milnor difference map after projecting to stage `n`.
  symm
  calc
    (productMap φ ≫ derivedLimitDifferenceMap Lsys) ≫ Pi.π (inverseSystemFamily Lsys) n =
      productMap φ ≫
        (Pi.π (inverseSystemFamily Lsys) n -
          Pi.π (inverseSystemFamily Lsys) (n + 1) ≫
            Lsys.transitionMap (Nat.le_succ n)) := by
          rw [Category.assoc, derivedLimitDifferenceMap_comp_π]
    _ =
      Pi.π (inverseSystemFamily Ksys) n ≫ φ.app (op n) -
        (Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          φ.app (op (n + 1)) ≫ Lsys.transitionMap (Nat.le_succ n)) := by
          rw [Preadditive.comp_sub]
          rw [hπ]
          simpa [Category.assoc] using
            congrArg
              (fun t ↦ t ≫ Lsys.transitionMap (Nat.le_succ n))
              hπsucc
    -- Proof comment: rewrite the shifted term using naturality of `φ` at the successor map.
    _ =
      Pi.π (inverseSystemFamily Ksys) n ≫ φ.app (op n) -
        (Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          Ksys.transitionMap (Nat.le_succ n) ≫ φ.app (op n)) := by
          congr 1
          simpa [Category.assoc] using
            congrArg
              (fun t ↦ Pi.π (inverseSystemFamily Ksys) (n + 1) ≫ t)
              (φ.naturality ((homOfLE (Nat.le_succ n)).op)).symm
    _ =
      (Pi.π (inverseSystemFamily Ksys) n -
          Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
            Ksys.transitionMap (Nat.le_succ n)) ≫
        φ.app (op n) := by
          rw [Preadditive.sub_comp]
          simp [Category.assoc]
    _ =
      derivedLimitDifferenceMap Ksys ≫ Pi.π (inverseSystemFamily Ksys) n ≫ φ.app (op n) := by
          rw [← derivedLimitDifferenceMap_comp_π_assoc]
    -- Proof comment: reassemble the source-side Milnor difference map and the product map.
    _ =
      (derivedLimitDifferenceMap Ksys ≫ productMap φ) ≫ Pi.π (inverseSystemFamily Lsys) n := by
          rw [Category.assoc, hπ, ← Category.assoc]

/-- The canonical map on `R^1 \!\varprojlim` induced by a morphism of sequential inverse systems.
-/
abbrev firstDerivedLimitMap {Ksys Lsys : SequentialInverseSystem D} (φ : Ksys ⟶ Lsys) :
    Ksys.firstDerivedLimit ⟶ Lsys.firstDerivedLimit :=
  cokernel.map
    (derivedLimitDifferenceMap Ksys)
    (derivedLimitDifferenceMap Lsys)
    (productMap φ)
    (productMap φ)
    (derivedLimitDifferenceMap_naturality φ)

end

end SequentialInverseSystem

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- Core/canonical derived-limit data: once the product `∏ K_n` is fixed, `K` is equipped with a
Milnor distinguished triangle whose middle morphism is the canonical difference map
`1 - shift`. -/
def HasMilnorTriangle (Ksys : SequentialInverseSystem D)
    [HasProduct (inverseSystemFamily Ksys)] (K : D) : Prop :=
  ∃ (ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys)
    (δ : ∏ᶜ inverseSystemFamily Ksys ⟶ K⟦(1 : ℤ)⟧),
    Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ ∈ distTriang D

namespace HasMilnorTriangle

/-- Bridge/view layer: a specified map `ι : K ⟶ ∏ K_n` extends to a Milnor distinguished triangle
for `Ksys`. -/
def WithMap (Ksys : SequentialInverseSystem D) [HasProduct (inverseSystemFamily Ksys)]
    {K : D} (ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys) : Prop :=
  ∃ δ : ∏ᶜ inverseSystemFamily Ksys ⟶ K⟦(1 : ℤ)⟧,
    Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ ∈ distTriang D

theorem WithMap.hasMilnorTriangle
    (Ksys : SequentialInverseSystem D) [HasProduct (inverseSystemFamily Ksys)]
    {K : D} {ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hι : WithMap Ksys ι) :
    HasMilnorTriangle Ksys K := by
  rcases hι with ⟨δ, hδ⟩
  exact ⟨ι, δ, hδ⟩

end HasMilnorTriangle

/-- Chap13 Definition 13 34 1: Definition 13.34.1 says that an object `K` is a derived limit, or
homotopy limit, of a sequential
inverse system `Ksys : SequentialInverseSystem D` in a triangulated category if the product `∏ K_n`
exists and
there is a distinguished triangle
`K ⟶ ∏ K_n ⟶ ∏ K_n ⟶ K⟦1⟧` whose middle morphism is the map
`(k_n) ↦ (k_n - f_{n + 1}(k_{n + 1}))`. This is the meaning of the notation
`K = R lim K_n`. -/
@[stacks 08TC]
def IsDerivedLimit (Ksys : SequentialInverseSystem D) (K : D) : Prop :=
  ∃ _ : HasProduct (inverseSystemFamily Ksys), HasMilnorTriangle Ksys K

end

end CategoryTheory
