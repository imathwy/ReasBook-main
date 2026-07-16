import LinearRepresentations_Serre_1977.Serre.Chap04.Theorem_4_5
import Mathlib.Analysis.Complex.Tietze
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory

universe u

-- Source/core/bridge triage:
-- `source-facing`: `not_finiteDimensional_l2`;
-- `core/canonical`: `FiniteDimensional ℂ (G →₂[(normalizedHaarMeasure : Measure G)] ℂ)`;
-- `bridge/view`: the instance `instFiniteOfFiniteDimensionalL2`, which turns finite-dimensionality
--   of normalized-Haar `L²(G)` into the corresponding finiteness statement on `G`.

section

variable {G : Type u} [Group G] [TopologicalSpace G] [T2Space G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]

local notation "μG" => (normalizedHaarMeasure : Measure G)
local notation "L²G" => (G →₂[μG] ℂ)

/-- Helper for Remark 4-24: finite-dimensionality of normalized-Haar `L²(G)` forces
finite-dimensionality of `C(G, ℂ)` through the canonical `ContinuousMap.toLp` map. -/
lemma finiteDimensionalContinuousMap_of_finiteDimensionalL2 [FiniteDimensional ℂ L²G] :
    FiniteDimensional ℂ C(G, ℂ) := by
  -- The canonical map from continuous functions into `L²(G)` is injective on a compact group.
  let f : C(G, ℂ) →ₗ[ℂ] L²G :=
    (ContinuousMap.toLp (E := ℂ) (p := (2 : ENNReal)) (μ := μG) ℂ).toLinearMap
  exact
    FiniteDimensional.of_injective f
      (ContinuousMap.toLp_injective (E := ℂ) (p := (2 : ENNReal)) (μ := μG) (𝕜 := ℂ))

/-- Helper for Remark 4-24: continuous complex-valued functions on a finite subset of `G` have
finrank equal to the cardinality of that subset. -/
lemma finrank_continuousMapOnFinset_eq_card (s : Finset G) :
    Module.finrank ℂ C(↑(s : Set G), ℂ) = s.card := by
  classical
  letI : Finite ↑(s : Set G) := Set.toFinite _
  letI : Fintype ↑(s : Set G) := Fintype.ofFinite ↑(s : Set G)
  letI : DiscreteTopology ↑(s : Set G) := inferInstance
  let e : C(↑(s : Set G), ℂ) ≃ₗ[ℂ] (↑(s : Set G) → ℂ) :=
    LinearEquiv.ofBijective (ContinuousMap.coeFnLinearMap ℂ)
      ⟨DFunLike.coe_injective, fun f ↦ ⟨ContinuousMap.equivFnOfDiscrete.symm f, rfl⟩⟩
  -- On a discrete finite space, continuous functions are exactly all functions.
  calc
    Module.finrank ℂ C(↑(s : Set G), ℂ)
        = Module.finrank ℂ (↑(s : Set G) → ℂ) := by
            rw [LinearEquiv.finrank_eq e]
    _ = Fintype.card ↑(s : Set G) := Module.finrank_fintype_fun_eq_card ℂ
    _ = s.card := by
          simp only [Finset.coe_sort_coe, Fintype.card_coe]

/-- Helper for Remark 4-24: if `C(G, ℂ)` is finite-dimensional, then the compact Hausdorff group
`G` itself must be finite. -/
lemma finite_of_finiteDimensionalContinuousMap [FiniteDimensional ℂ C(G, ℂ)] : Finite G := by
  classical
  by_contra hG
  letI : Infinite G := not_finite_iff_infinite.mp hG
  obtain ⟨s, hs⟩ := Finset.exists_card_eq (α := G) (Module.finrank ℂ C(G, ℂ) + 1)
  let r : C(G, ℂ) →ₗ[ℂ] C(↑(s : Set G), ℂ) :=
    { toFun := fun f ↦ f.restrict (s : Set G)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hsurj : Function.Surjective r := by
    -- Restricting to a finite closed subset is surjective by Tietze extension.
    intro f
    obtain ⟨g, hg⟩ :=
      ContinuousMap.exists_restrict_eq (X := G) (Y := ℂ) (s := (s : Set G))
        (Set.toFinite _ |>.isClosed) f
    exact ⟨g, hg⟩
  have hcard_le : s.card ≤ Module.finrank ℂ C(G, ℂ) := by
    -- Compare the finite-subset codomain with the ambient continuous-function space.
    rw [← finrank_continuousMapOnFinset_eq_card (G := G) s]
    exact LinearMap.finrank_le_finrank_of_surjective (f := r) hsurj
  have : Module.finrank ℂ C(G, ℂ) + 1 ≤ Module.finrank ℂ C(G, ℂ) := by
    simpa [hs] using hcard_le
  exact Nat.not_succ_le_self _ this

/-- Remark 4-24: if `G` is not finite, then the normalized-Haar `L²(G)` is not finite-dimensional
over `ℂ`. -/
theorem not_finiteDimensional_l2 (hG : ¬ Finite G) :
    ¬ FiniteDimensional ℂ L²G := by
  intro hL2
  -- Route correction: pass from `L²(G)` to `C(G, ℂ)` first, where restriction to finite subsets
  -- gives the contradiction.
  letI : FiniteDimensional ℂ L²G := hL2
  letI : FiniteDimensional ℂ C(G, ℂ) :=
    finiteDimensionalContinuousMap_of_finiteDimensionalL2 (G := G)
  exact hG (finite_of_finiteDimensionalContinuousMap (G := G))

/-- If the normalized-Haar `L²(G)` is finite-dimensional over `ℂ`, then `G` is finite. -/
instance instFiniteOfFiniteDimensionalL2 [FiniteDimensional ℂ L²G] : Finite G := by
  classical
  by_contra hG
  exact not_finiteDimensional_l2 hG inferInstance

end
