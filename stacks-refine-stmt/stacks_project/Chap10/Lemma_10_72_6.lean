import Mathlib
import stacks_project.Chap10.Definition_10_72_1
import stacks_project.Chap10.Lemma_10_71_6
import stacks_project.Chap10.Lemma_10_72_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace CategoryTheory
namespace ShortComplex
namespace ShortExact

section

variable {R : Type u} [Ring R]
variable {S : ShortComplex (ModuleCat.{u} R)}
variable [Module.Finite R S.X₁] [Module.Finite R S.X₃]

/-- In a short exact sequence of finite modules, the middle term is finite. -/
instance finite_X₂ (hS : S.ShortExact) : Module.Finite R S.X₂ :=
  Module.Finite.of_exact
    ((moduleCat_exact_iff_function_exact S).mp hS.exact)
    hS.moduleCat_surjective_g

end

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {S : ShortComplex (ModuleCat.{u} R)}
variable [Module.Finite R S.X₁] [Module.Finite R S.X₃]

/- Domain-style sampling:
* primary domain: local commutative algebra of module depth in short exact sequences of finite
  modules, with the proof route passing through the canonical covariant long exact `Ext` sequence;
* sampled owner declarations of the same kind:
  `moduleDepth`,
  `Module.Finite.of_exact`,
  `CategoryTheory.ShortComplex.ShortExact`,
  `CategoryTheory.Abelian.Ext.covariantSequence_exact`;
* best owner abstraction: `moduleDepth` is the chapter owner surface for local depth, while
  `S : ShortComplex (ModuleCat R)` with `hS : S.ShortExact` is the canonical owner for the short
  exact sequence data;
* source/core/bridge triage: this file is `source-facing`. No upstream theorem already packages
  the depth-lemma inequalities themselves, so the refinement should keep these three inequalities
  as the public owner statements rather than introducing a parallel wrapper or a fake recall;
* primitive vs derived split: the primitive data are just the short exact sequence `S` and the
  chapter owner `moduleDepth` on its three terms. The comparisons below are derived theorems from
  Lemma `10.72.5` and the recalled long exact `Ext` owner of Lemma `10.71.6`, so no extra public
  data/package structure belongs here. In particular, finite generation of `S.X₂` is itself a
  derived owner instance `hS.finite_X₂`, while any zero-endpoint case splits needed to use
  Lemma `10.72.5`
  belong in the proof rather than in the public theorem hypotheses.
-/

-- Proof sketch: first dispose of the degenerate cases where `S.X₁ = 0` or `S.X₃ = 0`, in which
-- the short exact sequence identifies `S.X₂` with one endpoint and the inequality is immediate.
-- In the nonzero case, identify each depth with the least degree of a nonvanishing residue-field
-- `Ext` group using Lemma `10.72.5`, apply the covariant long exact `Ext` sequence from
-- Lemma `10.71.6` to the short exact sequence `S`, and compare the first nonvanishing degrees.
/-- Lemma 10.72.6 (1): in a short exact sequence of finite modules over a Noetherian local ring,
the depth of the middle module is at least the minimum of the depths of the two end modules. -/
theorem moduleDepth_middle_ge_min (hS : S.ShortExact) :
    letI : Module.Finite R S.X₂ := hS.finite_X₂
    moduleDepth R S.X₂ ≥ min (moduleDepth R S.X₁) (moduleDepth R S.X₃) := by
  sorry

-- Proof sketch: as above, handle the zero-endpoint cases internally using the isomorphisms forced
-- by short exactness. Otherwise use Lemma `10.72.5` to rewrite depths as first nonvanishing
-- residue-field `Ext` degrees, then analyze the long exact `Ext` sequence of Lemma `10.71.6` for
-- `S` to show that the first nonvanishing degree of `S.X₃` is bounded below by the minimum of the
-- corresponding degrees for `S.X₂` and `S.X₁ - 1`.
/-- Lemma 10.72.6 (2): in a short exact sequence of finite modules over a Noetherian local ring,
the depth of the quotient module is at least the minimum of the depth of the middle module and one
less than the depth of the submodule. -/
theorem moduleDepth_right_ge_min (hS : S.ShortExact) :
    letI : Module.Finite R S.X₂ := hS.finite_X₂
    moduleDepth R S.X₃ ≥ min (moduleDepth R S.X₂) (moduleDepth R S.X₁ - 1) := by
  sorry

-- Proof sketch: rewrite the three depths via Lemma `10.72.5` after the same internal zero-case
-- reductions, apply the long exact covariant `Ext` sequence from Lemma `10.71.6`, and compare the
-- first nonvanishing degrees to bound the depth of `S.X₁` below by the minimum of the depth of
-- `S.X₂` and the shifted depth of `S.X₃`.
/-- Lemma 10.72.6 (3): in a short exact sequence of finite modules over a Noetherian local ring,
the depth of the submodule is at least the minimum of the depth of the middle module and one more
than the depth of the quotient module. -/
theorem moduleDepth_left_ge_min (hS : S.ShortExact) :
    letI : Module.Finite R S.X₂ := hS.finite_X₂
    moduleDepth R S.X₁ ≥ min (moduleDepth R S.X₂) (moduleDepth R S.X₃ + 1) := by
  sorry

end

end ShortExact
end ShortComplex
end CategoryTheory
