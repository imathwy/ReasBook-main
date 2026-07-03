import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap13.Definition_13_19_1
import StacksProject_2024.Chap13.Lemma_13_11_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open CochainComplex

universe v u

namespace CochainComplex.ProjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K : CochainComplex C ℤ}

/- Domain-style sampling for Lemma 13.19.2:
- primary domain: bounded-above cochain complexes, projective resolutions, and eventual vanishing
  of homology;
- sampled owner declarations:
  `CochainComplex.ProjectiveResolution`,
  `CochainComplex.ProjectiveResolution.exists_isStrictlyLE`,
  `CochainComplex.isZero_of_isLE`,
  `isoOfQuasiIsoAt`,
  `exists_quasiIso_from_truncLE_of_eventually_isZero_homology`;
- best owner abstraction:
  `CochainComplex.ProjectiveResolution K` is the source-faithful owner for the projective side,
  while the bounded-above replacement in part `(2)` is already canonically owned by
  `exists_quasiIso_from_truncLE_of_eventually_isZero_homology`;
- primitive-vs-derived split:
  for part `(1)`, the primitive data are just `P : ProjectiveResolution K`; the bounded-above
  witness and degreewise projectivity are derived from the owner;
  for part `(2)`, the primitive owner data are the canonical truncation object `K.truncLE b` and
  map `K.ιTruncLE b`, while the existential bounded-above replacement is derived;
- source/core/bridge triage:
  `source-facing`: eventual vanishing of `K.homology` for a complex admitting a bounded-above
    projective resolution;
  `core/canonical`: `ProjectiveResolution K`, `K.IsLE b`, and the canonical truncation theorem
    from `Lemma 13.11.5`;
  `bridge/view`: transport of eventual homology vanishing from the bounded-above resolving complex
    via `CochainComplex.isZero_of_isLE` and `isoOfQuasiIsoAt`.
-/

-- Proof sketch: choose a bound `b` with `P.IsStrictlyLE b`, view this as an `IsLE b` instance on
-- the resolving complex, deduce its homology vanishes in degrees `> b` via
-- `CochainComplex.isZero_of_isLE`, and transport that vanishing across the quasi-isomorphism
-- `P.π`.
/-- Lemma 13.19.2 (1): if a cochain complex `K` admits a bounded-above projective resolution,
then the homology objects `H^n(K)` vanish for all sufficiently large `n`. -/
theorem eventually_isZero_homology
    (P : ProjectiveResolution K) :
    ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (K.homology n) := by
  obtain ⟨b, hP⟩ := P.exists_isStrictlyLE
  let _ : (P : CochainComplex C ℤ).IsStrictlyLE b := hP
  exact ⟨b, fun n hn ↦ by
    simpa using IsZero.of_iso
      ((P : CochainComplex C ℤ).isZero_of_isLE b n hn)
      (isoOfQuasiIsoAt P.π n).symm⟩

end CochainComplex.ProjectiveResolution

/- Lemma 13.19.2 (2): if the homology of `K` vanishes in all sufficiently positive degrees, then
the canonical upper truncation map `K.truncLE b ⟶ K` is a quasi-isomorphism for some `b`, so `K`
admits a bounded-above quasi-isomorphic model. This is already the canonical theorem
`exists_quasiIso_from_truncLE_of_eventually_isZero_homology` from `Lemma 13.11.5`. -/
recall exists_quasiIso_from_truncLE_of_eventually_isZero_homology
