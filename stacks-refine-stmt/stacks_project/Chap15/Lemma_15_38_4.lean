import Mathlib
import stacks_project.Chap10.Lemma_10_160_10
import stacks_project.Chap15.Lemma_15_38_3

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v

section

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Algebra k A] [IsCompleteLocalRing A]
  [IsRegularLocalRing A]

/- Domain-style sampling for Lemma 15.38.4:
- primary domain: equal-characteristic Cohen-structure presentations of complete regular local
  algebras.
- sampled owner declarations:
  `exists_residueField_section_of_isCompleteLocalRing_of_isSeparableOver`,
  `exists_algEquiv_mvPowerSeries_of_residueField_bijective`,
  `MvPowerSeries.renameEquiv`,
  `AlgEquiv.restrictScalars`.
- best owner abstraction: the canonical owner is the finite-index power-series presentation
  `MvPowerSeries σ (ResidueField A)` with `[Finite σ]` from Lemma `10.160.10 (2)`. This file is a
  `source-facing` bridge that keeps the textbook `Fin d` surface by reindexing the canonical owner
  rather than duplicating it.
- primitive data: the complete regular local `k`-algebra `A` and the separability of
  `ResidueField A / k`.
- derived API: a `k`-algebra equivalence from a finite-variable formal power series ring over the
  residue field of `A`.

Source/core/bridge triage:
- `source-facing`: the `Fin d`-indexed Stacks Project presentation below.
- `core/canonical`: `exists_algEquiv_mvPowerSeries_of_residueField_bijective`.
- `bridge/view`: the residue-field section from Lemma `15.38.3`, followed by reindexing along
  `Fintype.equivFin`.
-/

-- Proof sketch: choose a `k`-algebra section `ResidueField A →ₐ[k] A` of the residue map via
-- Lemma `15.38.3`. This gives `A` a coefficient-field structure over `ResidueField A`, and the
-- induced residue-field map is the identity. Apply the canonical finite-index presentation from
-- Lemma `10.160.10 (2)` over `ResidueField A`, then reindex the variables along
-- `Fintype.equivFin` and restrict scalars back to `k`.
/-- Lemma 15.38.4: if `A` is a complete regular local `k`-algebra and the residue field extension
`ResidueField A / k` is separable in the Stacks Project sense, then `A` is `k`-algebra
isomorphic to a finite-variable formal power series ring over its residue field. -/
theorem exists_algEquiv_mvPowerSeries_residueField_of_isSeparableOver_of_isRegularLocalRing
    [Algebra.IsSeparableOver k (ResidueField A)] :
    ∃ d : ℕ, Nonempty (MvPowerSeries (Fin d) (ResidueField A) ≃ₐ[k] A) := by
  sorry

end
