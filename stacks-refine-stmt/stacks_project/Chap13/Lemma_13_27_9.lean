import Mathlib
import stacks_project.Chap13.Definition_13_11_3
import stacks_project.Chap13.Definition_13_27_1
import stacks_project.Chap13.Lemma_13_26_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open CategoryTheory.Abelian
open DerivedCategory
open scoped CategoryTheory DerivedExt

universe w v u

section

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜] [HasExt.{w} 𝒜]

/- Domain-style sampling for bounded derived decompositions:
- primary domain: objects of `D(𝒜)`, their cohomology objects in `𝒜`, and finite biproduct
  realizations of the intrinsic shifted-cohomology family over bounded integer intervals;
- sampled owner declarations:
  `CategoryTheory.derivedCategory_t_bounded_iff`,
  `DerivedCategory.isGE_iff`,
  `DerivedCategory.isLE_iff`,
  `DerivedCategory.homologyFunctor`,
  `DerivedCategory.singleFunctor`,
  `Set.Icc`,
  `CategoryTheory.Abelian.Ext`;
- best owner abstraction: the intrinsic family `i ↦ H^i(K)[-i]` is attached directly to
  `K : D(𝒜)`, while explicit bounds `a ≤ * ≤ b` belong only to the bridge that realizes a finite
  subfamily as a biproduct for bounded-amplitude objects;
- primitive data: the derived object `K : D(𝒜)` and the canonical cohomology owners `H^i`;
- derived API: the intrinsic family `shiftedCohomology 𝒜 K`, the interval restriction
  `shiftedCohomologyOn 𝒜 K a b`, the bounded-amplitude splitting theorem with hypotheses
  `K.IsGE a` and `K.IsLE b`, and the bounded-derived specialization obtained from
  `derivedCategory_t_bounded_iff`.

Source/core/bridge triage:
- `source-facing`: the bounded-derived splitting statement for `K : Dᵇ(𝒜)` and the intrinsic
  shifted-cohomology family `i ↦ H^i(K)[-i]`;
- `core/canonical`: `D(𝒜)`, `Set.Icc`, `H^i`, `singleFunctor`,
  `CategoryTheory.derivedCategory_t_bounded_iff`, `DerivedCategory.isGE_iff`,
  `DerivedCategory.isLE_iff`, `CategoryTheory.Abelian.Ext`;
- `bridge/view`: the explicit interval restriction in `D(𝒜)` with bounds `a b` and the bounded
  finite-biproduct realization hypotheses `K.IsGE a`, `K.IsLE b`.
-/

/-- The intrinsic shifted cohomology family `i ↦ H^i(K)[-i]` attached to `K : D(𝒜)`. -/
noncomputable abbrev shiftedCohomology (K : DerivedCategory 𝒜) :
    ℤ → DerivedCategory 𝒜 :=
  fun i ↦ (singleFunctor 𝒜 i).obj ((H^i).obj K)

/-- The restriction of the shifted cohomology family of `K` to the finite interval `[a, b]`. -/
noncomputable abbrev shiftedCohomologyOn (K : DerivedCategory 𝒜) (a b : ℤ) :
    Set.Icc a b → DerivedCategory 𝒜 :=
  fun i ↦ shiftedCohomology 𝒜 K i

-- Proof sketch: choose bounds `a ≤ i ≤ b` for the cohomological amplitude of `K` and induct on
-- `b - a`; use the truncation triangle for the top degree, show that its connecting morphism
-- vanishes because it lies in a higher `Ext` group from `H^b(K)` to the lower cohomologies,
-- split the triangle, and iterate.
/-- Once explicit cohomological bounds are fixed, the shifted cohomology pieces of `K` split off
as a finite biproduct over that interval. -/
theorem isomorphic_to_biproduct_shiftedCohomology_of_ext_vanishing_of_isGE_isLE
    (K : DerivedCategory 𝒜) (a b : ℤ) (hGE : K.IsGE a) (hLE : K.IsLE b)
    (hExt : ∀ (n : ℕ) (_ : 2 ≤ n) (i j : ℤ) (_ : j < i),
      Subsingleton (Ext ((H^i).obj K) ((H^j).obj K) n)) :
    Nonempty (K ≅ ⨁ shiftedCohomologyOn 𝒜 K a b) := sorry

/-- Lemma 13.27.9: if all higher extension groups in `𝒜` from higher cohomology to lower
cohomology vanish in degrees `n ≥ 2`, then any bounded derived object is isomorphic to the
biproduct of its shifted cohomology objects over some interval containing its cohomological
support. -/
theorem isomorphic_to_biproduct_shiftedCohomology_of_ext_vanishing
    (K : Dᵇ(𝒜))
    (hExt : ∀ (n : ℕ) (_ : 2 ≤ n) (i j : ℤ) (_ : j < i),
      Subsingleton (Ext ((H^i).obj K.obj) ((H^j).obj K.obj) n)) :
    ∃ a b : ℤ, Nonempty (K.obj ≅ ⨁ shiftedCohomologyOn 𝒜 K.obj a b) := by
  rcases (derivedCategory_t_bounded_iff K.obj).1 K.property with
    ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  have hGE : K.obj.IsGE a := by
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact ha i hi
  have hLE : K.obj.IsLE b := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact hb i hi
  exact ⟨a, b,
    isomorphic_to_biproduct_shiftedCohomology_of_ext_vanishing_of_isGE_isLE
      𝒜 K.obj a b hGE hLE hExt⟩

end
