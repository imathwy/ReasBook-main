import stacks_project.Chap13.Lemma_13_27_8
import stacks_project.Chap13.Definition_13_11_3
import stacks_project.Chap13.Lemma_13_27_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open DerivedCategory
open Abelian.Ext
open scoped CategoryTheory

universe w v u

section

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜] [HasExt.{w} 𝒜]

/- Domain-style sampling for bounded derived decompositions:
- primary domain: bounded objects in `D(𝒜)`, their cohomology objects, and the Ext-vanishing
  criteria that force splitting;
- sampled owner declarations:
  `Dᵇ(𝒜)`,
  `shiftedCohomology`,
  `shiftedCohomologyOn`,
  `isomorphic_to_biproduct_shiftedCohomology_of_ext_vanishing`,
  `CategoryTheory.hasInjectiveDimensionLT_of_uniform_vanishing`,
  `CategoryTheory.HasInjectiveDimensionLT.of_ext_vanishing`;
- best owner abstraction: the source-facing input is a bounded derived object `K : Dᵇ(𝒜)`, while
  `shiftedCohomology` is the intrinsic family `i ↦ H^i(K)[-i]` on `D(𝒜)`, its finite interval
  restriction `shiftedCohomologyOn` is only the bounded-realization bridge from `Lemma_13_27_9`,
  and the degree-two vanishing hypothesis is converted pointwise into the canonical owner
  `HasInjectiveDimensionLT`;
- primitive data: the bounded derived object `K` and the degree-two vanishing hypothesis on `Ext`;
- derived API: the resulting source-facing injective-dimension bridge
  `CategoryTheory.hasInjectiveDimensionLT_of_uniform_vanishing`, together with the owner-level
  pointwise `Ext`-vanishing consequence furnished by `CategoryTheory.HasInjectiveDimensionLT`.

Source/core/bridge triage:
- `source-facing`: the textbook splitting statement for bounded derived objects under uniform
  degree-two Ext vanishing;
- `core/canonical`: `Dᵇ(𝒜)`, `shiftedCohomology`,
  `isomorphic_to_biproduct_shiftedCohomology_of_ext_vanishing`,
  `CategoryTheory.HasInjectiveDimensionLT`;
- `bridge/view`: the interval restriction `shiftedCohomologyOn` and the reduction from degree-two
  Ext vanishing on objects of `𝒜` to the general higher-degree cohomology-Ext hypothesis
  required by `13.27.9`.
-/

-- Proof sketch: apply Lemma 13.27.8 to each cohomology object `H^j(K)` to get the canonical
-- owner `HasInjectiveDimensionLT _ 2`, then feed the resulting higher `Ext`-vanishing into
-- Lemma 13.27.9 for the chosen cohomological bounds `[a, b]` of `K`.
/-- Lemma 13.27.10: if the degree-two `Ext` groups in an abelian category vanish for every pair
of objects, then any bounded derived object is isomorphic to the biproduct of its shifted
cohomology objects over some interval containing its cohomological support. -/
theorem isomorphic_to_biproduct_shiftedCohomology_of_ext2_vanishing
    (K : Dᵇ(𝒜))
    (hExt₂ : ∀ A B : 𝒜, Subsingleton (Ext B A 2)) :
    ∃ a b : ℤ, Nonempty (K.obj ≅ ⨁ shiftedCohomologyOn 𝒜 K.obj a b) := by
  refine isomorphic_to_biproduct_shiftedCohomology_of_ext_vanishing 𝒜 K ?_
  intro n hn i j hij
  letI : HasInjectiveDimensionLT ((H^j).obj K.obj) 2 :=
    hasInjectiveDimensionLT_of_uniform_vanishing 2 hExt₂ ((H^j).obj K.obj)
  exact HasInjectiveDimensionLT.subsingleton ((H^j).obj K.obj) 2 n hn ((H^i).obj K.obj)

end
