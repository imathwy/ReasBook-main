import Mathlib
import StacksProject_2024.Chap14.Example_14_33_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped IteratedEndofunctor

universe u

noncomputable section

namespace CategoryTheory

variable (R : Type u) [Ring R] (M : ModuleCat.{u} R)

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

/-- Helper for Example 14.34.6: the free-forgetful adjunction unit inserts one bracket. -/
private theorem free_forget_adjunction_unit_apply {X : Type u} (x : X) :
    ((ModuleCat.adj R).unit.app X) x = ModuleCat.freeMk x := by
  -- The adjunction unit is definitionally the canonical generator map of the free module.
  rfl

/-- Helper for Example 14.34.6: the comonad counit removes one bracket on a free generator. -/
private theorem free_forget_resolution_counit_apply_freeMk
    (N : ModuleCat.{u} R) (x : N) :
    ((ε).app N) (ModuleCat.freeMk x) = x := by
  -- Identify the counit with the free descender attached to the identity function.
  have hCounit :
      (ModuleCat.adj R).counit.app N = ModuleCat.freeDesc (fun y : (N : Type u) ↦ y) := by
    simpa [ModuleCat.adj_homEquiv] using ((ModuleCat.adj R).homEquiv_symm_id N).symm
  rw [show (ε).app N = (ModuleCat.adj R).counit.app N by rfl]
  rw [hCounit]
  exact ModuleCat.freeDesc_apply (R := R) (f := fun y : (N : Type u) ↦ y) x

/-- Helper for Example 14.34.6: the comonad comultiplication adds one bracket on a free
generator. -/
private theorem free_forget_resolution_comultiplication_apply_freeMk
    (N : ModuleCat.{u} R) (x : N) :
    ((δ).app N) (ModuleCat.freeMk x) = ModuleCat.freeMk (ModuleCat.freeMk x) := by
  -- Unfold the comultiplication into the free functor applied to the adjunction unit.
  rw [show δ =
      Functor.whiskerRight (((forget (ModuleCat R)).whiskerLeft ((ModuleCat.adj R).unit)))
        (ModuleCat.free R) by
      rfl]
  rw [Functor.whiskerRight_app]
  simpa using
    (ModuleCat.free_map_apply ((ModuleCat.adj R).unit.app N) x)

/-- Helper for Example 14.34.6: the outer degree-`1` face map removes the outermost bracket on a
generator. -/
private theorem degree_one_outer_face_apply_freeMk
    (x : (T).obj M) :
    d^⦅0, (1 : Fin 2)⦆.app M (ModuleCat.freeMk x) = x := by
  -- The last face at degree `1` is the whiskered counit followed by the right unitor.
  rw [show (1 : Fin 2) = Fin.last 1 by rfl]
  rw [iteratedFaceMap, Fin.lastCases_last, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app]
  simpa using free_forget_resolution_counit_apply_freeMk (R := R) ((T).obj M) x

/-- Helper for Example 14.34.6: the inner degree-`1` face map applies the counit inside the outer
bracket. -/
private theorem degree_one_inner_face_apply_freeMk
    (x : (T).obj M) :
    d^⦅0, (0 : Fin 2)⦆.app M (ModuleCat.freeMk x) = ModuleCat.freeMk (((ε).app M) x) := by
  -- The first face at degree `1` is the free functor applied to the counit.
  rw [show (0 : Fin 2) = Fin.castSucc 0 by rfl]
  rw [iteratedFaceMap, Fin.lastCases_castSucc, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app]
  simpa using (ModuleCat.free_map_apply ((ε).app M) x)

/-- Helper for Example 14.34.6: the outer degree-`1` degeneracy adds one outer bracket to a
generator. -/
private theorem degree_one_outer_degeneracy_apply_freeMk
    (x : (T).obj M) :
    s^⦅1, (1 : Fin 2)⦆.app M (ModuleCat.freeMk x) = ModuleCat.freeMk (ModuleCat.freeMk x) := by
  -- The last degeneracy at degree `1` is the whiskered comultiplication followed by the
  -- associator.
  rw [show (1 : Fin 2) = Fin.last 1 by rfl]
  rw [iteratedDegeneracyMap, Fin.lastCases_last, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app]
  simpa using free_forget_resolution_comultiplication_apply_freeMk (R := R) ((T).obj M) x

/-- Helper for Example 14.34.6: the inner degree-`1` degeneracy applies the comultiplication
inside the outer bracket. -/
private theorem degree_one_inner_degeneracy_apply_freeMk
    (x : (T).obj M) :
    s^⦅1, (0 : Fin 2)⦆.app M (ModuleCat.freeMk x) = ModuleCat.freeMk (((δ).app M) x) := by
  -- The first degeneracy at degree `1` is the free functor applied to the comultiplication.
  rw [show (0 : Fin 2) = Fin.castSucc 0 by rfl]
  rw [iteratedDegeneracyMap, Fin.lastCases_castSucc, Functor.whiskerRight_app]
  simpa using (ModuleCat.free_map_apply ((δ).app M) x)

/-- Helper for Example 14.34.6: the counit evaluates an inner weighted sum of free generators by
linearity. -/
private theorem counit_apply_weighted_sum_freeMk
    {κ : Type u} [Fintype κ] (s : κ → R) (m : κ → M) :
    ((ε).app M) (∑ j, s j • ModuleCat.freeMk (m j)) = ∑ j, s j • m j := by
  -- Push the counit through the finite sum and then collapse each free generator.
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  calc
    ((ε).app M) (s j • ModuleCat.freeMk (m j)) = s j • ((ε).app M) (ModuleCat.freeMk (m j)) := by
      simpa using map_smul (ConcreteCategory.hom ((ε).app M)) (s j) (ModuleCat.freeMk (m j))
    _ = s j • m j := by
      simpa using congrArg (fun y ↦ s j • y)
        (free_forget_resolution_counit_apply_freeMk (R := R) M (m j))

/-- Helper for Example 14.34.6: the comultiplication evaluates an inner weighted sum of free
generators by linearity. -/
private theorem comultiplication_apply_weighted_sum_freeMk
    {κ : Type u} [Fintype κ] (s : κ → R) (m : κ → M) :
    ((δ).app M) (∑ j, s j • ModuleCat.freeMk (m j)) =
      ∑ j, s j • ModuleCat.freeMk (ModuleCat.freeMk (m j)) := by
  -- Push the comultiplication through the finite sum and then add one bracket to each generator.
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  calc
    ((δ).app M) (s j • ModuleCat.freeMk (m j)) = s j • ((δ).app M) (ModuleCat.freeMk (m j)) := by
      simpa using map_smul (ConcreteCategory.hom ((δ).app M)) (s j) (ModuleCat.freeMk (m j))
    _ = s j • ModuleCat.freeMk (ModuleCat.freeMk (m j)) := by
      simpa using congrArg (fun y ↦ s j • y)
        (free_forget_resolution_comultiplication_apply_freeMk (R := R) M (m j))

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
        ∑ i, ∑ j, (r i * s i j) • ModuleCat.freeMk (m i j) := by
  -- Push the outer face map through the outer finite sum.
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- On each outer generator, the face map removes the outer bracket and combines the scalars.
  let ξ : (T).obj M := ∑ j, s i j • ModuleCat.freeMk (m i j)
  calc
    d^⦅0, (1 : Fin 2)⦆.app M (r i • ModuleCat.freeMk ξ) =
        r i • d^⦅0, (1 : Fin 2)⦆.app M (ModuleCat.freeMk ξ) := by
          simpa using
            map_smul
              (ConcreteCategory.hom (d^⦅0, (1 : Fin 2)⦆.app M))
              (r i)
              (ModuleCat.freeMk ξ)
    _ = r i • ∑ j, s i j • ModuleCat.freeMk (m i j) := by
      simpa [ξ] using congrArg (fun y ↦ r i • y)
        (degree_one_outer_face_apply_freeMk (M := M) (x := ξ))
    _ = ∑ j, (r i * s i j) • ModuleCat.freeMk (m i j) := by
      simpa [smul_smul] using
        (Finset.smul_sum
          (r := r i)
          (s := Finset.univ)
          (f := fun j : κ ↦ s i j • ModuleCat.freeMk (R := R) (m i j)))

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
        ∑ i, r i • ModuleCat.freeMk (∑ j, s i j • m i j) := by
  -- Push the outer face map through the outer finite sum.
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- On each outer generator, the face map applies the counit to the inner linear combination.
  let ξ : (T).obj M := ∑ j, s i j • ModuleCat.freeMk (m i j)
  calc
    d^⦅0, (0 : Fin 2)⦆.app M (r i • ModuleCat.freeMk ξ) =
        r i • d^⦅0, (0 : Fin 2)⦆.app M (ModuleCat.freeMk ξ) := by
          simpa using
            map_smul
              (ConcreteCategory.hom (d^⦅0, (0 : Fin 2)⦆.app M))
              (r i)
              (ModuleCat.freeMk ξ)
    _ = r i • ModuleCat.freeMk (((ε).app M) ξ) := by
      simpa [ξ] using congrArg (fun y ↦ r i • y)
        (degree_one_inner_face_apply_freeMk (M := M) (x := ξ))
    _ = r i • ModuleCat.freeMk (∑ j, s i j • m i j) := by
      simpa [ξ] using congrArg (fun y ↦ r i • ModuleCat.freeMk y)
        (counit_apply_weighted_sum_freeMk (M := M) (s := s i) (m := m i))

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
          (∑ j, s i j • ModuleCat.freeMk (m i j))) := by
  -- Push the outer degeneracy map through the outer finite sum.
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- On each outer generator, the degeneracy inserts one new outer bracket.
  let ξ : (T).obj M := ∑ j, s i j • ModuleCat.freeMk (m i j)
  calc
    s^⦅1, (1 : Fin 2)⦆.app M (r i • ModuleCat.freeMk ξ) =
        r i • s^⦅1, (1 : Fin 2)⦆.app M (ModuleCat.freeMk ξ) := by
          simpa using
            map_smul
              (ConcreteCategory.hom (s^⦅1, (1 : Fin 2)⦆.app M))
              (r i)
              (ModuleCat.freeMk ξ)
    _ = r i • ModuleCat.freeMk (ModuleCat.freeMk (∑ j, s i j • ModuleCat.freeMk (m i j))) := by
      simpa [ξ] using congrArg (fun y ↦ r i • y)
        (degree_one_outer_degeneracy_apply_freeMk (M := M) (x := ξ))

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
          (∑ j, s i j • ModuleCat.freeMk (ModuleCat.freeMk (m i j))) := by
  -- Push the outer degeneracy map through the outer finite sum.
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- On each outer generator, the degeneracy inserts the inner comultiplication.
  let ξ : (T).obj M := ∑ j, s i j • ModuleCat.freeMk (m i j)
  calc
    s^⦅1, (0 : Fin 2)⦆.app M (r i • ModuleCat.freeMk ξ) =
        r i • s^⦅1, (0 : Fin 2)⦆.app M (ModuleCat.freeMk ξ) := by
          simpa using
            map_smul
              (ConcreteCategory.hom (s^⦅1, (0 : Fin 2)⦆.app M))
              (r i)
              (ModuleCat.freeMk ξ)
    _ = r i • ModuleCat.freeMk (((δ).app M) ξ) := by
      simpa [ξ] using congrArg (fun y ↦ r i • y)
        (degree_one_inner_degeneracy_apply_freeMk (M := M) (x := ξ))
    _ = r i • ModuleCat.freeMk (∑ j, s i j • ModuleCat.freeMk (ModuleCat.freeMk (m i j))) := by
      simpa [ξ] using congrArg (fun y ↦ r i • ModuleCat.freeMk y)
        (comultiplication_apply_weighted_sum_freeMk (M := M) (s := s i) (m := m i))

end CategoryTheory
