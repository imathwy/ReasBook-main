import Mathlib
import StacksProject_2024.Chap12.Definition_12_31_2

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

omit [Preadditive D] [HasCokernels D] in
private theorem productMap_comp_π {Ksys Lsys : SequentialInverseSystem D}
    (φ : Ksys ⟶ Lsys) (n : ℕ) :
    productMap φ ≫ Pi.π (inverseSystemFamily Lsys) n =
      Pi.π (inverseSystemFamily Ksys) n ≫ φ.app (op n) := by
  rw [productMap, Pi.lift_π]

private theorem derivedLimitDifferenceMap_naturality
    {Ksys Lsys : SequentialInverseSystem D} (φ : Ksys ⟶ Lsys) :
    derivedLimitDifferenceMap Ksys ≫ productMap φ =
      productMap φ ≫ derivedLimitDifferenceMap Lsys := by
  -- Compare both Milnor endomorphisms after projection to each stage.
  sorry

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

/-- A natural isomorphism of sequential inverse systems induces an isomorphism on the first
derived inverse limit. -/
def firstDerivedLimitIsoOfNatIso
    {Ksys Lsys : SequentialInverseSystem D} (e : Ksys ≅ Lsys) :
    Ksys.firstDerivedLimit ≅ Lsys.firstDerivedLimit := by
  have hcomp :
      productMap e.hom ≫ productMap e.inv = 𝟙 (∏ᶜ inverseSystemFamily Ksys) := by
    apply Pi.hom_ext
    intro n
    change (productMap e.hom ≫ productMap e.inv) ≫ Pi.π (inverseSystemFamily Ksys) n =
      𝟙 _ ≫ Pi.π (inverseSystemFamily Ksys) n
    calc
      (productMap e.hom ≫ productMap e.inv) ≫ Pi.π (inverseSystemFamily Ksys) n =
          productMap e.hom ≫ (productMap e.inv ≫ Pi.π (inverseSystemFamily Ksys) n) := by
            rw [Category.assoc]
      _ = productMap e.hom ≫ (Pi.π (inverseSystemFamily Lsys) n ≫ e.inv.app (op n)) := by
            rw [productMap_comp_π]
      _ = (productMap e.hom ≫ Pi.π (inverseSystemFamily Lsys) n) ≫ e.inv.app (op n) := by
            rw [← Category.assoc]
      _ = (Pi.π (inverseSystemFamily Ksys) n ≫ e.hom.app (op n)) ≫ e.inv.app (op n) := by
            rw [productMap_comp_π]
      _ = Pi.π (inverseSystemFamily Ksys) n := by
            rw [Category.assoc, e.hom_inv_id_app]
            simp
      _ = 𝟙 _ ≫ Pi.π (inverseSystemFamily Ksys) n := by
            simp
  have hcomp' :
      productMap e.inv ≫ productMap e.hom = 𝟙 (∏ᶜ inverseSystemFamily Lsys) := by
    apply Pi.hom_ext
    intro n
    change (productMap e.inv ≫ productMap e.hom) ≫ Pi.π (inverseSystemFamily Lsys) n =
      𝟙 _ ≫ Pi.π (inverseSystemFamily Lsys) n
    calc
      (productMap e.inv ≫ productMap e.hom) ≫ Pi.π (inverseSystemFamily Lsys) n =
          productMap e.inv ≫ (productMap e.hom ≫ Pi.π (inverseSystemFamily Lsys) n) := by
            rw [Category.assoc]
      _ = productMap e.inv ≫ (Pi.π (inverseSystemFamily Ksys) n ≫ e.hom.app (op n)) := by
            rw [productMap_comp_π]
      _ = (productMap e.inv ≫ Pi.π (inverseSystemFamily Ksys) n) ≫ e.hom.app (op n) := by
            rw [← Category.assoc]
      _ = (Pi.π (inverseSystemFamily Lsys) n ≫ e.inv.app (op n)) ≫ e.hom.app (op n) := by
            rw [productMap_comp_π]
      _ = Pi.π (inverseSystemFamily Lsys) n := by
            rw [Category.assoc, e.inv_hom_id_app]
            simp
      _ = 𝟙 _ ≫ Pi.π (inverseSystemFamily Lsys) n := by
            simp
  refine ⟨firstDerivedLimitMap e.hom, firstDerivedLimitMap e.inv, ?_, ?_⟩
  · apply (cancel_epi (cokernel.π (derivedLimitDifferenceMap Ksys))).1
    calc
      cokernel.π (derivedLimitDifferenceMap Ksys) ≫
          firstDerivedLimitMap e.hom ≫ firstDerivedLimitMap e.inv =
        productMap e.hom ≫ productMap e.inv ≫
          cokernel.π (derivedLimitDifferenceMap Ksys) := by
            simp [firstDerivedLimitMap, Category.assoc]
      _ =
          𝟙 _ ≫ cokernel.π (derivedLimitDifferenceMap Ksys) := by
            simpa [Category.assoc] using
              congrArg (fun f ↦ f ≫ cokernel.π (derivedLimitDifferenceMap Ksys)) hcomp
      _ = cokernel.π (derivedLimitDifferenceMap Ksys) ≫ 𝟙 Ksys.firstDerivedLimit := by
            simp
  · apply (cancel_epi (cokernel.π (derivedLimitDifferenceMap Lsys))).1
    calc
      cokernel.π (derivedLimitDifferenceMap Lsys) ≫
          firstDerivedLimitMap e.inv ≫ firstDerivedLimitMap e.hom =
        productMap e.inv ≫ productMap e.hom ≫
          cokernel.π (derivedLimitDifferenceMap Lsys) := by
            simp [firstDerivedLimitMap, Category.assoc]
      _ =
          𝟙 _ ≫ cokernel.π (derivedLimitDifferenceMap Lsys) := by
            simpa [Category.assoc] using
              congrArg (fun f ↦ f ≫ cokernel.π (derivedLimitDifferenceMap Lsys)) hcomp'
      _ = cokernel.π (derivedLimitDifferenceMap Lsys) ≫ 𝟙 Lsys.firstDerivedLimit := by
            simp

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

/-- Definition 13.34.1: an object `K` is a derived limit, or homotopy limit, of a sequential
inverse system `Ksys : SequentialInverseSystem D` in a triangulated category if the product `∏ K_n`
exists and
there is a distinguished triangle
`K ⟶ ∏ K_n ⟶ ∏ K_n ⟶ K⟦1⟧` whose middle morphism is the map
`(k_n) ↦ (k_n - f_{n + 1}(k_{n + 1}))`. This is the meaning of the notation
`K = R lim K_n`. -/
def IsDerivedLimit (Ksys : SequentialInverseSystem D) (K : D) : Prop :=
  ∃ _ : HasProduct (inverseSystemFamily Ksys), HasMilnorTriangle Ksys K

/-- A morphism `c : K ⟶ K_n` is a stage comparison from a chosen derived limit of `Ksys` if some
Milnor-triangle presentation of `K = R lim_n K_n` projects to `c` at stage `n`. -/
def IsDerivedLimitStageComparison
    (Ksys : SequentialInverseSystem D) (K : D) (n : ℕ) (c : K ⟶ Ksys.obj (op n)) : Prop :=
  ∃ _ : HasProduct (inverseSystemFamily Ksys),
    ∃ ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys,
      HasMilnorTriangle.WithMap Ksys ι ∧
        c = ι ≫ Pi.π (inverseSystemFamily Ksys) n

/-- A stage comparison presents its source as a derived limit of the underlying sequential inverse
system. -/
theorem IsDerivedLimitStageComparison.isDerivedLimit
    {Ksys : SequentialInverseSystem D} {K : D} {n : ℕ} {c : K ⟶ Ksys.obj (op n)}
    (hc : IsDerivedLimitStageComparison Ksys K n c) :
    IsDerivedLimit Ksys K := by
  rcases hc with ⟨hP, _, hι, _⟩
  let _ : HasProduct (inverseSystemFamily Ksys) := hP
  exact ⟨hP, hι.hasMilnorTriangle Ksys⟩

end

end CategoryTheory
