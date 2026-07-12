import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace

universe u

-- Semantic note: Equation 25.11.3.1 is the source-facing basis-open covering statement for a
-- finite intersection. In this repository the canonical basis owner on opens is
-- `TopologicalSpace.Opens.IsBasis`, and the covering equality is stated directly in `Opens X` as a
-- supremum over the basis members contained in the intersection.

section

variable {X : Type u} [TopologicalSpace X]

namespace Opens.IsBasis

/-- Any open is the supremum of the basis opens contained in it. This is the direct `Opens`-level
covering form of the canonical mathlib basis-cover theorem `Opens.isBasis_iff_cover`. -/
theorem eq_sSup
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (U : Opens X) :
    U = sSup {V : Opens X | V ∈ B ∧ V ≤ U} := by
  ext x
  rw [Opens.coe_sSup]
  constructor
  · intro hx
    rcases Opens.isBasis_iff_nbhd.mp hB hx with ⟨V, hVB, hxV, hVU⟩
    exact Set.mem_iUnion.2 ⟨V, Set.mem_iUnion.2 ⟨⟨hVB, hVU⟩, hxV⟩⟩
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨V, hx⟩
    rcases Set.mem_iUnion.1 hx with ⟨hV, hxV⟩
    exact hV.2 hxV

/-- Any open is the supremum of the basis opens contained in it, indexed by the corresponding
subtype. This source-facing bridge avoids downstream rewrites between `sSup` on a set and `iSup`
on the subtype of basis opens contained in `U`. -/
theorem eq_iSup
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (U : Opens X) :
    U = iSup (fun V : {V : Opens X // V ∈ B ∧ V ≤ U} ↦ (V : Opens X)) := by
  ext x
  constructor
  · intro hx
    rcases Opens.isBasis_iff_nbhd.mp hB hx with ⟨V, hVB, hxV, hVU⟩
    exact Opens.mem_iSup.2 ⟨⟨V, hVB, hVU⟩, hxV⟩
  · intro hx
    rcases Opens.mem_iSup.1 hx with ⟨V, hxV⟩
    exact V.2.2 hxV

/-- 25.11.3.1: a finite intersection of opens is the supremum of the basis opens contained in it.
This is the source-facing finite-intersection specialization of `Opens.IsBasis.eq_iSup`;
specializing further to a finite intersection of basis opens recovers the source statement, and
the basis-membership hypotheses on the factors are redundant once the intersection is viewed as an
open of `X`. -/
theorem iInf_eq_iSup
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    {n : ℕ} (U : Fin (n + 2) → Opens X) :
    (⨅ k, U k) = iSup (fun V : {V : Opens X // V ∈ B ∧ V ≤ ⨅ k, U k} ↦ (V : Opens X)) := by
  simpa using Opens.IsBasis.eq_iSup hB (⨅ k, U k)

/-- The finite-intersection statement of 25.11.3.1 in set-indexed supremum form. -/
theorem iInf_eq_sSup
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    {n : ℕ} (U : Fin (n + 2) → Opens X) :
    (⨅ k, U k) = sSup {V : Opens X | V ∈ B ∧ V ≤ ⨅ k, U k} := by
  simpa using Opens.IsBasis.eq_sSup hB (⨅ k, U k)

end Opens.IsBasis

end
