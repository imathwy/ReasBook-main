import Mathlib
import StacksProject_2024.Chap15.Definition_15_50_1
import StacksProject_2024.Chap15.Lemma_15_43_9
import StacksProject_2024.Chap15.Lemma_15_45_1
import StacksProject_2024.Chap15.Lemma_15_45_10

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

noncomputable section

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R] [IsGRing R]
variable {Rh : Type u} [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]

local notation "Rhat" => AdicCompletion (maximalIdeal R) R
local notation "Rhhat" => AdicCompletion (maximalIdeal Rh) Rh

/- Domain-style sampling:
 primary domain: henselization/completion comparison for a Noetherian local `G`-ring domain, and
  algebraic elements of the maximal-ideal completion over the base domain `R`;
- sampled owner declarations in this domain:
  `IsGRing`,
  `IsHenselizationOf`,
  `maximalIdealCompletionMap`,
  `maximalIdealCompletionMap_bijective_of_flat_of_residueFieldBijective`,
  `henselizationMap_faithfullyFlat`,
  `AlgHom.range`,
  `Subalgebra.algebraicClosure`;
- best owner abstraction: the source-facing theorem should talk about the image of the chosen
  henselization inside `Rhat` under its canonical `R`-algebra map to the completion and the
  canonical subalgebra `Subalgebra.algebraicClosure R Rhat`;
- primitive data: the local domain `R`, its `G`-ring owner, the chosen henselization `Rh`, and
  the completion comparison owner data identifying `Rhat` with `Rhhat`;
- derived API: the transported bridge `Rh →ₐ[R] Rhat` and the pointwise membership
  characterization
  obtained from the main theorem by `Subalgebra.mem_algebraicClosure`.

Source/core/bridge triage:
- `source-facing`: the subalgebra equality identifying the image with
  `Subalgebra.algebraicClosure R Rhat`;
- `core/canonical`: `IsGRing`, `maximalIdealCompletionMap`,
  `maximalIdealCompletionMap_bijective_of_flat_of_residueFieldBijective`,
  `henselizationMap_faithfullyFlat`, `AlgHom.range`, and `Subalgebra.algebraicClosure`;
- `bridge/view`: the thin transported map `henselizationToCompletion` and the pointwise
  algebraicity reformulation. -/

/-- The canonical map from the chosen henselization `Rh` to the completion `Rhat`, obtained by
identifying the completion of `Rh` with `Rhat` through the canonical completion comparison. -/
noncomputable abbrev henselizationToCompletion : Rh →ₐ[R] Rhat :=
  let _ : Module.Flat R Rh := henselizationMap_faithfullyFlat.flat
  let comparison : Rhat ≃ₐ[R] Rhhat :=
    AlgEquiv.ofRingEquiv
      (f := RingEquiv.ofBijective
        (maximalIdealCompletionMap (algebraMap R Rh))
        (maximalIdealCompletionMap_bijective_of_flat_of_residueFieldBijective
          IsHenselizationOf.map_maximalIdeal
          IsHenselizationOf.residueField_bijective))
      (fun r ↦ by
        change (maximalIdealCompletionMap (algebraMap R Rh)) ((algebraMap R Rhat) r) =
          (algebraMap R Rhhat) r
        simpa [RingHom.comp_apply] using
          DFunLike.congr_fun (maximalIdealCompletionMap_comp (algebraMap R Rh)) r)
  (comparison.symm : Rhhat →ₐ[R] Rhat).comp (IsScalarTower.toAlgHom R Rh Rhhat)

-- Proof sketch: `Algebra.adicCompletion_isRegularRingMap_of_isGRing` makes the completion map
-- `R → Rhat` regular. Apply Theorem `16.13.2` to one-variable polynomial relations over `R` to
-- approximate algebraic elements of `Rhat` by roots in étale neighborhoods of `R`; the universal
-- property of the chosen henselization funnels those approximations through `Rh`. The canonical
-- bijection from `maximalIdealCompletionMap_bijective_of_flat_of_residueFieldBijective`
-- identifies the completion of `Rh` with `Rhat`, and the Stacks finiteness argument for roots
-- over the generic fiber forces the approximants to stabilize to an actual element of `Rh`. This
-- characterizes exactly the elements of `Rhat` algebraic over `R`.
/-- Example 16.13.3: let `R` be a Noetherian local domain that is a `G`-ring, let `Rh` be a chosen
henselization of `R`, and let `Rhat` be the maximal-ideal adic completion of `R`. Then the image
of the canonical map `henselizationToCompletion : Rh →ₐ[R] Rhat` is exactly the subalgebra of
`Rhat` consisting of elements algebraic over `R`, i.e. the canonical subalgebra
`Subalgebra.algebraicClosure R Rhat`. -/
theorem henselization_range_eq_algebraicClosure :
    (henselizationToCompletion : Rh →ₐ[R] Rhat).range =
      Subalgebra.algebraicClosure R Rhat := sorry

/-- An element of `Rhat` lies in the image of the canonical henselization map exactly when it is
algebraic over `R`. -/
theorem mem_range_henselizationToCompletion_iff_isAlgebraic (f : Rhat) :
    f ∈ (henselizationToCompletion : Rh →ₐ[R] Rhat).range ↔ IsAlgebraic R f := by
  rw [henselization_range_eq_algebraicClosure]
  rw [Subalgebra.mem_algebraicClosure]

end
