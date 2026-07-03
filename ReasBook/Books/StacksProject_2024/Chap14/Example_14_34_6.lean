import Mathlib
import StacksProject_2024.Chap14.Example_14_33_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped IteratedEndofunctor

universe u

noncomputable section

namespace CategoryTheory

variable (R : Type u) [Ring R] (M : ModuleCat R)

/- Domain-style sampling:
- primary domain: low-degree face and degeneracy maps in the simplicial resolution attached to the
  free-forgetful adjunction on `ModuleCat R`;
- sampled owner declarations:
  `iteratedFaceMap`,
  `iteratedDegeneracyMap`,
  `SimplicialObject.δ`,
  `SimplicialObject.σ`;
- best owner abstraction: the source-facing formulas in this example should reuse the owner maps
  `d[T, ε]` and `s[T, δ]` from `Example_14_33_1`, specialized to the comonad of
  `ModuleCat.adj R`; separate public abbreviations for `d₀`, `d₁`, `s₀`, and `s₁` are only
  derived aliases and should not remain as parallel API;
- source/core/bridge triage:
  - `source-facing`: the four explicit formulas on nested sums in degree `1`;
  - `core/canonical`: the simplicial-resolution face and degeneracy owners
    `SimplicialObject.δ`/`SimplicialObject.σ`;
  - `bridge/view`: the specialization of `d[T, ε]` and `s[T, δ]` to the free-forgetful comonad on
    `ModuleCat R`;
- primitive data: the ring `R`, the module `M`, and the comonad
  `((ModuleCat.adj R).toComonad)` on `ModuleCat R`;
- derived API: the four degree-`1` maps and their explicit evaluations on nested finite sums.
-/

private abbrev freeForgetResolutionFunctor (R : Type u) [Ring R] :
    ModuleCat R ⥤ ModuleCat R :=
  (ModuleCat.adj R).toComonad.toFunctor

private abbrev freeForgetResolutionCounit (R : Type u) [Ring R] :
    freeForgetResolutionFunctor R ⟶ 𝟭 (ModuleCat R) :=
  (ModuleCat.adj R).toComonad.ε

private abbrev freeForgetResolutionComultiplication (R : Type u) [Ring R] :
    freeForgetResolutionFunctor R ⟶
      freeForgetResolutionFunctor R ⋙ freeForgetResolutionFunctor R :=
  (ModuleCat.adj R).toComonad.δ

local notation "T" => freeForgetResolutionFunctor R
local notation "ε" => freeForgetResolutionCounit R
local notation "δ" => freeForgetResolutionComultiplication R
local notation "d^⦅" n ", " j "⦆" => d[T, ε]⦅n, j⦆
local notation "s^⦅" n ", " j "⦆" => s[T, δ]⦅n, j⦆

-- Proof sketch: unfold `d^⦅0, (1 : Fin 2)⦆.app M` to the degree-`1` face map
-- `iteratedFaceMap ((ModuleCat.adj R).toComonad.toFunctor) ((ModuleCat.adj R).toComonad.ε) 0 1`,
-- which is the free-module descender that
-- applies the counit to the outer copy of `R[-]`. Evaluating on the displayed finite sum combines
-- the outer and inner coefficients into a single sum in `R[M]`.
/-- Example 14.34.6 (1): for a typical element
`ξ = ∑ i, r i • [∑ j, s i j • [m i j]]` of `R[R[M]]`, the face map `d₀` collapses the outer
brackets and sends `ξ` to `∑ i, ∑ j, (r i * s i j) • [m i j]`. -/
theorem freeForgetAdjunctionModuleResolutionD0_apply_nested_sum
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (r : ι → R) (s : ι → κ → R) (m : ι → κ → M) :
    d^⦅0, (1 : Fin 2)⦆.app M
      (∑ i, r i • ModuleCat.freeMk (∑ j, s i j • ModuleCat.freeMk (m i j))) =
        ∑ i, ∑ j, (r i * s i j) • ModuleCat.freeMk (m i j) := sorry

-- Proof sketch: unfold `d^⦅0, (0 : Fin 2)⦆.app M` to the degree-`1` face map
-- `iteratedFaceMap ((ModuleCat.adj R).toComonad.toFunctor) ((ModuleCat.adj R).toComonad.ε) 0 0`,
-- which applies the counit to the inner copy of `R[-]` before reintroducing the outer bracket.
-- The displayed formula is then the universal property of the free module applied to each basis
-- element.
/-- Example 14.34.6 (2): for the same typical element `ξ`, the face map `d₁` applies the inner
free-module counit and sends `ξ` to `∑ i, r i • [∑ j, s i j • m i j]`. -/
theorem freeForgetAdjunctionModuleResolutionD1_apply_nested_sum
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (r : ι → R) (s : ι → κ → R) (m : ι → κ → M) :
    d^⦅0, (0 : Fin 2)⦆.app M
      (∑ i, r i • ModuleCat.freeMk (∑ j, s i j • ModuleCat.freeMk (m i j))) =
        ∑ i, r i • ModuleCat.freeMk (∑ j, s i j • m i j) := sorry

-- Proof sketch: unfold `s^⦅1, (1 : Fin 2)⦆.app M` to the degree-`1` degeneracy map
-- `iteratedDegeneracyMap ((ModuleCat.adj R).toComonad.toFunctor)
--   ((ModuleCat.adj R).toComonad.δ) 1 1`,
-- which inserts the comultiplication in the outer copy of `R[-]`. On basis elements this wraps
-- one more pair of brackets around the inner linear combination, and linearity extends the formula
-- to the displayed sum.
/-- Example 14.34.6 (3): for the same typical element `ξ`, the degeneracy map `s₀` inserts one
more outer pair of brackets and sends `ξ` to `∑ i, r i • [[∑ j, s i j • [m i j]]]`. -/
theorem freeForgetAdjunctionModuleResolutionS0_apply_nested_sum
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (r : ι → R) (s : ι → κ → R) (m : ι → κ → M) :
    s^⦅1, (1 : Fin 2)⦆.app M
      (∑ i, r i • ModuleCat.freeMk (∑ j, s i j • ModuleCat.freeMk (m i j))) =
        ∑ i, r i • ModuleCat.freeMk (ModuleCat.freeMk
          (∑ j, s i j • ModuleCat.freeMk (m i j))) := sorry

-- Proof sketch: unfold `s^⦅1, (0 : Fin 2)⦆.app M` to the degree-`1` degeneracy map
-- `iteratedDegeneracyMap ((ModuleCat.adj R).toComonad.toFunctor)
--   ((ModuleCat.adj R).toComonad.δ) 1 0`,
-- which inserts the comultiplication in the inner copy of `R[-]`. On each basis vector this
-- brackets every `m i j` once more inside the inner linear combination, and linearity gives the
-- displayed formula.
/-- Example 14.34.6 (4): for the same typical element `ξ`, the degeneracy map `s₁` inserts one
more inner pair of brackets and sends `ξ` to `∑ i, r i • [∑ j, s i j • [[m i j]]]`. -/
theorem freeForgetAdjunctionModuleResolutionS1_apply_nested_sum
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (r : ι → R) (s : ι → κ → R) (m : ι → κ → M) :
    s^⦅1, (0 : Fin 2)⦆.app M
      (∑ i, r i • ModuleCat.freeMk (∑ j, s i j • ModuleCat.freeMk (m i j))) =
        ∑ i, r i • ModuleCat.freeMk
          (∑ j, s i j • ModuleCat.freeMk (ModuleCat.freeMk (m i j))) := sorry

end CategoryTheory
