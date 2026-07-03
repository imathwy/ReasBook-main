import StacksProject_2024.Chap13.Lemma_13_27_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open DerivedCategory
open Abelian.Ext
open scoped CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] [IsDedekindDomain R]

local notation "Mod" => ModuleCat R
local notation "DbMod" => Dᵇ(Mod)

/- Domain-style sampling for Example 15.70.3:
- primary domain: injective-dimension bounds in `ModuleCat R` and bounded-derived splitting in
  `Dᵇ(ModuleCat R)`;
- sampled owner declarations:
  `injectiveDimension`,
  `injectiveDimension_le_iff`,
  `HasInjectiveDimensionLT.subsingleton`,
  `isomorphic_to_biproduct_shiftedCohomology_of_ext2_vanishing`;
- best owner abstraction: the source-facing statement is the Dedekind-domain specialization of the
  Chapter 13 bounded-derived splitting theorem. The primitive new input is the owner-level module
  bound `injectiveDimension _ ≤ 1`, while the needed `HasInjectiveDimensionLE _ 1` instance and
  resulting degree-two `Ext`-vanishing are derived through `injectiveDimension_le_iff` and
  `HasInjectiveDimensionLT.subsingleton`;
- primitive vs. derived API: primitive data are the Dedekind-domain injective-dimension bound in
  the canonical owner `injectiveDimension` and the bounded derived object `K : Dᵇ(Mod)`; the
  `HasInjectiveDimensionLE` witness and `Ext`-vanishing input for the splitting theorem are derived
  pointwise from that owner-level bound.
- source/core/bridge triage:
  `source-facing`: the Dedekind-domain specialization of the bounded-derived splitting statement;
  `core/canonical`: `injectiveDimension`, `injectiveDimension_le_iff`,
    `HasInjectiveDimensionLT.subsingleton`, and
    `isomorphic_to_biproduct_shiftedCohomology_of_ext2_vanishing`;
  `bridge/view`: the pointwise passage from the Dedekind-domain injective-dimension bound to the
  degree-two `Ext`-vanishing hypothesis required by the Chapter 13 owner theorem.
-/

/-- Every `R`-module over a Dedekind domain has injective dimension at most `1`. -/
-- Proof sketch: apply Lemma `15.70.2` to the degree-zero derived object of `M`; the hypothesis
-- needed there is that every quotient `R/I` has projective dimension at most `1`, which follows
-- from the fact that every nonzero ideal of a Dedekind domain is finite projective.
theorem injectiveDimension_le_one_of_isDedekindDomain
    (M : Mod) :
    injectiveDimension M ≤ 1 := by
  exact (injectiveDimension_le_iff M 1).2 (by
    sorry)

/-- Bridge/view: over a Dedekind domain, every degree-two `Ext` group of modules is trivial. -/
theorem subsingleton_ext_two_of_isDedekindDomain
    (M N : Mod) :
    Subsingleton (Ext N M 2) := by
  letI : HasInjectiveDimensionLE M 1 :=
    (injectiveDimension_le_iff M 1).mp (injectiveDimension_le_one_of_isDedekindDomain M)
  simpa using HasInjectiveDimensionLT.subsingleton M 2 2 le_rfl N

/-- Example 15.70.3: over a Dedekind domain, every bounded derived object of `R`-modules is
isomorphic to the finite biproduct of its shifted cohomology modules over some interval
containing its cohomological support. -/
-- Proof sketch: apply the Chapter 13 splitting theorem
-- `isomorphic_to_biproduct_shiftedCohomology_of_ext2_vanishing`; its degree-two `Ext`-vanishing
-- hypothesis is supplied by the module-level owner bound above through
-- `injectiveDimension_le_iff` and the canonical owner lemma
-- `HasInjectiveDimensionLT.subsingleton`.
theorem isomorphic_to_biproduct_shiftedCohomology_of_isDedekindDomain
    (K : DbMod) :
    ∃ a b : ℤ,
      Nonempty (K.obj ≅ ⨁ shiftedCohomologyOn Mod K.obj a b) := by
  sorry

end

end CategoryTheory
