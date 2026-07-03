import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.Chap12.Definition_12_6_2

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

universe v u

section

open Limits ComposableArrows

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/- Domain-style sampling for Definition 13.27.4:
- primary domain: finite exact composable chains with fixed endpoints and endpoint mono/epi
  conditions, indexed by the actual Yoneda degree;
- inspected owner declarations:
  `ObjectProperty.FullSubcategory`,
  `ComposableArrows`,
  `ComposableArrows.Exact`,
  `ComposableArrows.Exact.sc`,
  `Extension`;
- source/core/bridge triage:
  `source-facing`: `YonedaExtension A B n`;
  `core/canonical`: `ComposableArrows C (n + 1)` together with `ComposableArrows.Exact` and the
    inherited full-subcategory category structure;
  `bridge/view`: the degree-`1` comparison with `Extension A B` and the endpoint-identity
    predicate on ladders;
- best owner abstraction: keep `YonedaExtension A B n` as the fixed-endpoint source-facing owner,
  but realize it as the full subcategory of `ComposableArrows C (n + 1)` cut out by the fixed
  endpoint and exactness conditions, so that ladders are inherited directly from the canonical
  owner category instead of being rebuilt by a parallel local wrapper;
- primitive-vs-derived split:
  primitive data: the underlying exact composable chain with fixed endpoints and endpoint mono/epi
  conditions;
  derived API: the first and last maps, the degree-one bridge to the earlier source-facing owner
    `Extension`, the endpoint-identity predicate on ladders, and the equivalence relation built
    from those canonical ladders. -/

structure IsYonedaExtension (A B : C) (n : ℕ+) (E : ComposableArrows C (n + 1)) : Prop where
  /-- The left endpoint of the chain is the fixed object `A`. -/
  left_eq : E.left = A
  /-- The right endpoint of the chain is the fixed object `B`. -/
  right_eq : E.right = B
  /-- The first map `A ⟶ Z_(n-1)` is a monomorphism. -/
  mono_first : Mono (eqToHom left_eq.symm ≫ E.map' 0 1)
  /-- The chain is exact at every intermediate object. -/
  exact : E.Exact
  /-- The last map `Z_0 ⟶ B` is an epimorphism. -/
  epi_last : Epi (E.map' n (n + 1) ≫ eqToHom right_eq)

/-- Definition 13.27.4: a degree `n` Yoneda extension of `B` by `A`, for `n : ℕ+`, is the full
subcategory of exact composable chains `A ⟶ Z_(n-1) ⟶ ... ⟶ Z_0 ⟶ B` with monic first map and
epic last map. Equivalently, these are the chains underlying exact sequences
`0 ⟶ A ⟶ Z_(n-1) ⟶ ... ⟶ Z_0 ⟶ B ⟶ 0`. -/
abbrev YonedaExtension (A B : C) (n : ℕ+) :=
  ObjectProperty.FullSubcategory (IsYonedaExtension A B n)

namespace YonedaExtension

variable {A B : C} {n : ℕ+}

/-- The chosen identification of the left endpoint with `A`. -/
abbrev leftEq (E : YonedaExtension A B n) : E.obj.left = A :=
  E.property.left_eq

/-- The chosen identification of the right endpoint with `B`. -/
abbrev rightEq (E : YonedaExtension A B n) : E.obj.right = B :=
  E.property.right_eq

/-- Exactness of the underlying composable chain. -/
abbrev exact (E : YonedaExtension A B n) : E.obj.Exact :=
  E.property.exact

/-- The first nonzero map `A ⟶ Z_(n-1)` in a Yoneda extension. -/
abbrev firstMap (E : YonedaExtension A B n) :
    A ⟶ E.obj.obj' 1 :=
  eqToHom E.leftEq.symm ≫ E.obj.map' 0 1

/-- The last nonzero map `Z_0 ⟶ B` in a Yoneda extension. -/
abbrev lastMap (E : YonedaExtension A B n) :
    E.obj.obj' n ⟶ B :=
  E.obj.map' n (n + 1) ≫ eqToHom E.rightEq

/-- A Yoneda extension carries the canonical monomorphism instance on its first map. -/
instance (E : YonedaExtension A B n) : Mono E.firstMap :=
  E.property.mono_first

/-- A Yoneda extension carries the canonical epimorphism instance on its last map. -/
instance (E : YonedaExtension A B n) : Epi E.lastMap :=
  E.property.epi_last

private theorem firstMap_comp_lastMap (E : YonedaExtension A B 1) :
    E.firstMap ≫ E.lastMap = 0 := by
  let hComplex := E.exact.toIsComplex
  calc
    E.firstMap ≫ E.lastMap
        = eqToHom E.leftEq.symm ≫
            (E.obj.map' 0 1 ≫ E.obj.map' 1 2) ≫
              eqToHom E.rightEq := by
            simp [firstMap, lastMap, Category.assoc]
    _ = 0 := by
      rw [hComplex.zero 0 (by decide)]
      rw [zero_comp, comp_zero]

set_option linter.unnecessarySimpa false in
private theorem shortExact (E : YonedaExtension A B 1) :
    (ShortComplex.mk E.firstMap E.lastMap E.firstMap_comp_lastMap).ShortExact := by
  let e : ShortComplex.mk E.firstMap E.lastMap E.firstMap_comp_lastMap ≅
      E.exact.sc 0 (by decide) :=
    ShortComplex.isoMk
      (eqToIso E.leftEq.symm)
      (Iso.refl _)
      (eqToIso E.rightEq.symm)
      (by
        dsimp [ComposableArrows.sc, ComposableArrows.sc', firstMap]
        simpa using
          congrArg (fun k ↦ eqToHom E.leftEq.symm ≫ E.obj.map k)
            (Subsingleton.elim _ _))
      (by
        dsimp [ComposableArrows.sc, ComposableArrows.sc', lastMap]
        simp)
  refine ShortComplex.ShortExact.mk' ?_ E.property.mono_first E.property.epi_last
  exact ShortComplex.exact_of_iso e.symm (E.exact.exact 0 (by decide))

/-- The canonical bridge from a degree-`1` Yoneda extension to the earlier source-facing owner
`Extension A B`. -/
abbrev toExtension (E : YonedaExtension A B 1) : Extension A B where
  E := E.obj.obj' 1
  f := E.firstMap
  g := E.lastMap
  zero := E.firstMap_comp_lastMap
  shortExact := E.shortExact

/-- A ladder between Yoneda extensions is identity on the fixed endpoints `A` and `B`,
after transporting along the chosen endpoint identifications. -/
private def idOnEndpoints (E F : YonedaExtension A B n)
    (φ : E ⟶ F) : Prop :=
  app' φ.hom 0 = eqToHom (E.leftEq.trans F.leftEq.symm) ∧
    app' φ.hom (n + 1) = eqToHom (E.rightEq.trans F.rightEq.symm)

/-- Two Yoneda extensions of the same degree are equivalent when there exists a third Yoneda
extension mapping to both by a commutative ladder which is the identity on `A` and `B`. -/
def Equivalent (E F : YonedaExtension A B n) : Prop :=
  ∃ (G : YonedaExtension A B n)
    (φ : G ⟶ E)
    (ψ : G ⟶ F),
      idOnEndpoints G E φ ∧ idOnEndpoints G F ψ

/-- In degree `1`, endpoint-fixing isomorphic short exact sequences induce equivalent Yoneda
extensions. This reuses the Chapter `12` owner `Extension.Isomorphic` rather than keeping a
parallel short-exact equivalence notion local to Yoneda extensions. -/
theorem equivalent_of_toExtension_isomorphic {E F : YonedaExtension A B 1}
    (h : Extension.Isomorphic E.toExtension F.toExtension) :
    Equivalent E F := by
  rcases h with ⟨e, hf, hg⟩
  have w₀ : E.obj.map' 0 1 ≫ e.hom =
      eqToHom (E.leftEq.trans F.leftEq.symm) ≫ F.obj.map' 0 1 := by
    simpa [firstMap, Category.assoc] using
      congrArg (fun k ↦ eqToHom E.leftEq ≫ k) hf
  have w₁ : E.obj.map' 1 2 ≫
      eqToHom (E.rightEq.trans F.rightEq.symm) =
      e.hom ≫ F.obj.map' 1 2 := by
    apply (cancel_mono (eqToHom F.rightEq)).1
    change (E.obj.map' 1 2 ≫ eqToHom (E.rightEq.trans F.rightEq.symm)) ≫
        eqToHom F.rightEq =
      (e.hom ≫ F.obj.map' 1 2) ≫ eqToHom F.rightEq
    simpa [lastMap, Category.assoc] using hg.symm
  let i : E.obj ≅ F.obj :=
    ComposableArrows.isoMk₂
      (eqToIso (E.leftEq.trans F.leftEq.symm))
      e
      (eqToIso (E.rightEq.trans F.rightEq.symm))
      w₀
      w₁
  refine ⟨E, 𝟙 E, ObjectProperty.homMk i.hom, ?_, ?_⟩
  · change app' (𝟙 E.obj) 0 =
        eqToHom (E.leftEq.trans E.leftEq.symm) ∧
      app' (𝟙 E.obj) 2 =
        eqToHom (E.rightEq.trans E.rightEq.symm)
    constructor
    · change 𝟙 (E.obj.obj' 0) = 𝟙 E.obj.left
      simp [left]
    · change 𝟙 (E.obj.obj' 2) = 𝟙 E.obj.right
      simp [right]
  · change i.hom.app 0 = eqToHom (E.leftEq.trans F.leftEq.symm) ∧
      i.hom.app 2 = eqToHom (E.rightEq.trans F.rightEq.symm)
    constructor <;> rfl

end YonedaExtension

end

end CategoryTheory
