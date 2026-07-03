import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap13.Definition_13_18_1
import StacksProject_2024.Chap13.Lemma_13_11_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open CochainComplex

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace CochainComplex.InjectiveResolution

variable {K : CochainComplex C ℤ}

/- Domain-style sampling:
- primary domain: bounded-below injective resolutions of cochain complexes and the induced
  eventual vanishing of low-degree homology;
- sampled owner declarations:
  `CochainComplex.InjectiveResolution`,
  `CochainComplex.InjectiveResolution.exists_isStrictlyGE`,
  `CochainComplex.isZero_of_isGE`,
  `isoOfQuasiIsoAt`,
  `exists_quasiIso_to_truncGE_of_eventually_isZero_homology`;
- best owner abstraction: `CochainComplex.InjectiveResolution` already owns the primitive bounded-
  below resolving complex, while eventual vanishing and truncation replacement are derived API;
- primitive data here: the chosen injective resolution `I` together with its bounded-below witness
  from `I.exists_isStrictlyGE`;
- derived API here: vanishing of `K.homology n` for `n ≪ 0`, and the lower-truncation
  replacement recalled below.

Source/core/bridge triage:
- `source-facing`: the source statement that a bounded-below injective resolution forces eventual
  vanishing of low-degree homology;
- `core/canonical`: `InjectiveResolution.exists_isStrictlyGE`, `ExactAt`, and quasi-isomorphism
  invariance of homology;
- `bridge/view`: the truncation existence theorem already provided by Lemma 13.11.5.
-/
-- Proof sketch: let `a` be a lower bound for the bounded-below resolving complex `I.complex.obj`.
-- Since `I.complex.obj` is strictly concentrated in degrees `≥ a`, its homology vanishes in every
-- degree `< a`. The quasi-isomorphism `I.ι` identifies the homology of `K` with that of
-- `I.complex.obj`, so `H^n(K) = 0` for all `n < a`.
/-- Lemma 13.18.2 (1): if `I` is a bounded-below injective resolution of `K`, then the homology
objects `H^n(K)` vanish for all sufficiently negative degrees. -/
theorem eventually_isZero_homology (I : InjectiveResolution K) :
    ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (K.homology n) := by
  obtain ⟨a, hI⟩ := I.exists_isStrictlyGE
  letI := hI
  exact ⟨a, fun n hn ↦ by
    simpa using IsZero.of_iso
      ((I : CochainComplex C ℤ).isZero_of_isGE a n hn)
      (isoOfQuasiIsoAt I.ι n)⟩

end CochainComplex.InjectiveResolution

/- Lemma 13.18.2 (2): this is exactly the bounded-below truncation replacement already proved as
Lemma 13.11.5 (1). -/
recall exists_quasiIso_to_truncGE_of_eventually_isZero_homology
