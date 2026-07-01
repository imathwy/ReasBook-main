import Mathlib
import stacks_project.Chap13.Lemma_13_4_11
import stacks_project.Chap13.Lemma_13_19_10
import stacks_project.Chap15.Definition_15_69_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

/-
Domain-style sampling:
- primary domain: vanishing of morphisms in derived categories and splitting distinguished
  triangles via the canonical binary-biproduct structure;
- sampled owner declarations:
  `CategoryTheory.HasProjectiveAmplitudeIn`,
  `CochainComplex.derivedCategory_hom_eq_zero_of_bounded_projective_strictlyGE_and_homology_vanishing_ge`,
  `CategoryTheory.Pretriangulated.exists_iso_binaryBiproduct_of_distTriang`,
  `CategoryTheory.isSplitEpi_mor₂_of_distinguished_mor₃_eq_zero`;
- best owner abstractions: `HasProjectiveAmplitudeIn` is the chapter-level source-facing amplitude
  predicate, `Pretriangulated.exists_iso_binaryBiproduct_of_distTriang` is the canonical
  split-triangle owner, so the source-facing compatibility data should remain the owner theorem's
  native pair of equations rather than a parallel local wrapper;
- primitive data: the amplitude witness on `L`, the homology-vanishing hypothesis on `K`, the
  distinguished-triangle maps, and the chosen isomorphism to a biproduct;
- derived API: vanishing of `Hom(L, K)`, existence of a compatible biproduct isomorphism, and the
  corresponding uniqueness statement.

Source/core/bridge triage:
- `source-facing`: the three clauses of Lemma `15.77.1`;
- `core/canonical`: `Pretriangulated.exists_iso_binaryBiproduct_of_distTriang`;
- `bridge/view`: the conjunction
  `f ≫ e.hom = biprod.inl ∧ e.hom ≫ biprod.snd = g`, which exposes the source-facing
  compatibility equations without creating a second owner for split triangles.
-/

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

-- Proof sketch: choose a projective representative of `L` concentrated in degrees `[a, b]` from
-- `HasProjectiveAmplitudeIn`, replace `K` by a representative with zero terms in degrees `≥ a`
-- using the cohomology-vanishing hypothesis, and then apply Lemma `13.19.10` to conclude that
-- every map `L ⟶ K` in `D(R)` is zero.
/-- Lemma 15.77.1 (1): if `L` has projective-amplitude in `[a, b]` and the cohomology of `K`
vanishes in all degrees `i ≥ a`, then every morphism `L ⟶ K` in `D(R)` is zero. In particular,
this applies when `L` is perfect of tor-amplitude in `[a, b]`. -/
theorem hom_eq_zero_of_projectiveAmplitude_of_homology_vanishing_ge
    {K L : DMod} {a b : ℤ}
    (hL : HasProjectiveAmplitudeIn L a b)
    (hK : ∀ i : ℤ, a ≤ i → IsZero ((H i).obj K))
    (f : L ⟶ K) :
    f = 0 := sorry

-- Proof sketch: apply part `(1)` to the shifted target `K⟦(1 : ℤ)⟧` to deduce that the
-- connecting morphism `L ⟶ K⟦1⟧` of the distinguished triangle is zero. Lemma `13.4.11`
-- then gives a right inverse to `M ⟶ L`, and hence an isomorphism `M ≅ K ⊞ L` compatible with
-- the first and second maps of the triangle.
/-- Lemma 15.77.1 (2): if `L` has projective-amplitude in `[a, b]`, if the cohomology of `K`
vanishes in all degrees `i ≥ a + 1`, and if `K ⟶ M ⟶ L ⟶ K⟦1⟧` is a distinguished triangle in
`D(R)`, then there is an isomorphism `M ≅ K ⊞ L` compatible with the maps `K ⟶ M` and
`M ⟶ L`. -/
theorem exists_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge_succ
    {K L M : DMod} {a b : ℤ}
    (hL : HasProjectiveAmplitudeIn L a b)
    (hK : ∀ i : ℤ, a + 1 ≤ i → IsZero ((H i).obj K))
    {f : K ⟶ M} {g : M ⟶ L} {δ : L ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang DMod) :
    ∃ e : M ≅ K ⊞ L, f ≫ e.hom = biprod.inl ∧ e.hom ≫ biprod.snd = g := sorry

-- Proof sketch: part `(2)` gives existence once the stronger cohomology-vanishing hypothesis
-- forces the connecting morphism to vanish. For uniqueness, compare two compatible splittings by
-- a morphism of distinguished triangles and use part `(1)` to show the relevant cross-Hom group
-- `Hom_{D(R)}(L, K)` vanishes, so the comparison morphism is unique.
/-- Lemma 15.77.1 (3): if `L` has projective-amplitude in `[a, b]`, if the cohomology of `K`
vanishes in all degrees `i ≥ a`, and if `K ⟶ M ⟶ L ⟶ K⟦1⟧` is a distinguished triangle in
`D(R)`, then there exists a unique isomorphism `M ≅ K ⊞ L` compatible with the maps
`K ⟶ M` and `M ⟶ L`. -/
theorem existsUnique_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge
    {K L M : DMod} {a b : ℤ}
    (hL : HasProjectiveAmplitudeIn L a b)
    (hK : ∀ i : ℤ, a ≤ i → IsZero ((H i).obj K))
    {f : K ⟶ M} {g : M ⟶ L} {δ : L ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang DMod) :
    ∃! e : M ≅ K ⊞ L, f ≫ e.hom = biprod.inl ∧ e.hom ≫ biprod.snd = g := sorry

end

end CategoryTheory
