import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import stacks_project.Chap13.Definition_13_27_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

namespace CategoryTheory

universe w

open DerivedCategory
open Triangulated
open Abelian.Ext
open scoped DerivedExt

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

local notation "H" => homologyFunctor 𝒜
local notation "single₀" => singleFunctor 𝒜 0

/- Domain-style sampling for Lemma 13.27.3:
- primary domain: morphisms in `D(𝒜)` controlled by the canonical `t`-structure and the
  cohomology functors `H^n`;
- sampled owner declarations:
  `DerivedCategory.IsLE`,
  `DerivedCategory.IsGE`,
  `CategoryTheory.Triangulated.TStructure.zero_of_isLE_of_isGE`,
  `Abelian.Ext.homEquiv`,
  `Abelian.Ext.homEquiv₀`;
- best owner abstraction: the boundedness hypotheses belong to the canonical owners `X.IsLE a`
  and `Y.IsGE b`; the degree-`b - a` comparison is a source-facing bridge from `Ext^(b - a)(X, Y)`
  to `Hom(H^a(X), H^b(Y))`; and the single-object degree-zero clause should reuse the chapter
  owner `Abelian.Ext.homEquiv₀`, reached from the derived-side notation through
  `Abelian.Ext.homEquiv`, rather than rebuilding that identification locally;
- primitive data: objects `X Y : D(𝒜)`, bounds `a b : ℤ`, and the owner hypotheses
  `X.IsLE a`, `Y.IsGE b`;
- derived API: vanishing below `b - a`, the canonical comparison map in degree `b - a`, and the
  single-object special case.

Source/core/bridge triage:
- `source-facing`: the vanishing and comparison statements for `Ext^n(X, Y)` and their
  single-object corollaries;
- `core/canonical`: `DerivedCategory.IsLE`, `DerivedCategory.IsGE`, and
  `CategoryTheory.Triangulated.TStructure.zero_of_isLE_of_isGE`;
- `bridge/view`: the degree-`b - a` comparison map `shiftedHomToHomologyMap` and the degree-zero
  transport from derived `Ext^0` to `Abelian.Ext B A 0`, followed by `Abelian.Ext.homEquiv₀`.
-/

/-- The canonical degree-`b - a` comparison map
`Ext^(b - a)(X, Y) → Hom(H^a(X), H^b(Y))`. -/
noncomputable def shiftedHomToHomologyMap
    (X Y : DerivedCategory 𝒜) (a b : ℤ) :
    Ext^(b - a)(X, Y) → ((H a).obj X ⟶ (H b).obj Y) :=
  fun f ↦ (H 0).shiftMap f a b (sub_add_cancel b a)

/-- Lemma 13.27.3 (1), vanishing clause: if `X` has no cohomology above degree `a` and `Y` has
no cohomology below degree `b`, then `Ext^n(X, Y)` vanishes for `n < b - a`. -/
theorem shiftedHom_subsingleton_of_lt_sub
    (X Y : DerivedCategory 𝒜) (a b n : ℤ) (hX : X.IsLE a) (hY : Y.IsGE b) (hn : n < b - a) :
    Subsingleton (Ext^n(X, Y)) := by
  letI := hX
  letI := hY
  have hshift : (Y⟦n⟧).IsGE (a + 1) := by
    have hbn : (Y⟦n⟧).IsGE (b - n) := by
      simpa using
        (TStructure.t.isGE_shift Y b n (b - n) (by omega) :
          TStructure.t.IsGE (Y⟦n⟧) (b - n))
    exact TStructure.t.isGE_of_ge (Y⟦n⟧) (a + 1) (b - n) (by omega)
  refine ⟨fun f g ↦ by
    rw [TStructure.t.zero_of_isLE_of_isGE f a (a + 1) (by omega) hX hshift,
      TStructure.t.zero_of_isLE_of_isGE g a (a + 1) (by omega) hX hshift]⟩

/-- Lemma 13.27.3 (1), comparison clause: under the same hypotheses, the canonical degree
`b - a` comparison map is bijective. -/
theorem shiftedHomToHomologyMap_bijective
    (X Y : DerivedCategory 𝒜) (a b : ℤ) (hX : X.IsLE a) (hY : Y.IsGE b) :
    Function.Bijective (shiftedHomToHomologyMap X Y a b) := by
  sorry

/- Lemma 13.27.3 (1), owner form: in degree `b - a`, the canonical comparison identifies
`Ext^(b - a)(X, Y)` with `Hom(H^a(X), H^b(Y))`; this is the equivalence attached to the
preceding bijectivity theorem, so no extra wrapper declaration is needed. -/
section

variable (X Y : DerivedCategory 𝒜) (a b : ℤ) (hX : X.IsLE a) (hY : Y.IsGE b)

#check (Equiv.ofBijective (shiftedHomToHomologyMap X Y a b)
  (shiftedHomToHomologyMap_bijective X Y a b hX hY) :
    Ext^(b - a)(X, Y) ≃ ((H a).obj X ⟶ (H b).obj Y))

end

/-- Lemma 13.27.3 (2), negative-degree clause for objects of `𝒜`: for `i < 0`, the derived
extension group from `B[0]` to `A[0]` vanishes. -/
theorem single_shiftedHom_subsingleton_of_lt_zero
    (B A : 𝒜) (i : ℤ) (hi : i < 0) :
    Subsingleton (Ext^i((single₀).obj B, (single₀).obj A)) := by
  simpa using
    shiftedHom_subsingleton_of_lt_sub ((single₀).obj B) ((single₀).obj A)
      0 0 i inferInstance inferInstance (by simpa using hi)

section

local instance : HasExt.{w} 𝒜 := hasExt_of_hasDerivedCategory 𝒜

/- Lemma 13.27.3 (2), degree-zero clause for objects of `𝒜`: the degree-zero derived extension
group from `B[0]` to `A[0]` identifies canonically with `Hom(B, A)`. This is exactly the
composite of the canonical owner equivalences `Abelian.Ext.homEquiv` and
`Abelian.Ext.homEquiv₀`, so the file should expose that composite directly rather than a
parallel local alias. -/
variable (B A : 𝒜)

#check (((homEquiv : Abelian.Ext B A 0 ≃
    Ext^((0 : ℤ))((single₀).obj B, (single₀).obj A)).symm).trans homEquiv₀ :
  Ext^((0 : ℤ))((single₀).obj B, (single₀).obj A) ≃ (B ⟶ A))

end

end CategoryTheory
