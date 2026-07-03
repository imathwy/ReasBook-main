import Mathlib
import StacksProject_2024.Chap15.Lemma_15_65_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open Polynomial

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

private abbrev DModR := DerivedCategory.{u + 1, u, u + 1} (ModuleCat R)
local notation "ev0" => Polynomial.evalRingHom (0 : R)

/- Domain-style sampling for Lemma 15.82.2:
- primary domain: pseudo-coherence in derived categories under restriction of scalars along the
  polynomial evaluation map;
- sampled owner declarations:
  `isMPseudoCoherent_iff_restrictScalars`,
  `isPseudoCoherent_iff_restrictScalars`,
  `Polynomial.evalRingHom`,
  `(ModuleCat.restrictScalars f).mapDerivedCategory`;
- best owner abstraction: the chapter owner theorem
  `isMPseudoCoherent_iff_restrictScalars`; the evaluation map `R[X] → R` is bridge data selecting
  the ring hom to which that owner theorem is specialized;
- primitive data: the canonical map `ev0` and the proof that `R`, viewed as an
  `R[X]`-module through that map, is pseudo-coherent;
- derived API: the specialized equivalence below between pseudo-coherence over `R` and over
  `R[X]`, expressed through the canonical derived restriction functor
  `(ModuleCat.restrictScalars ev0).mapDerivedCategory`.

Source/core/bridge triage:
- `source-facing`: the specialized equivalence below for the evaluation-at-zero map;
- `core/canonical`: `isMPseudoCoherent_iff_restrictScalars`;
- `bridge/view`: `(ModuleCat.restrictScalars ev0).mapDerivedCategory`. -/

private theorem regularModule_isPseudoCoherent_evalAtZero :
    ((ModuleCat.restrictScalars ev0).obj (ModuleCat.of R R)).IsPseudoCoherent := by
  -- Proof sketch: use the two-term finite free resolution
  -- `0 → R[X] --·X→ R[X] → R → 0` of `R` over `R[X]`.
  sorry

/-- Lemma 15.82.2: for the polynomial evaluation map `R[X] → R` sending `X` to `0`, a derived
`R`-complex is `m`-pseudo-coherent exactly when the same object viewed by restriction of scalars
as a derived `R[X]`-complex is `m`-pseudo-coherent. -/
theorem isMPseudoCoherent_iff_restrictScalars_evalAtZero
    (K : DModR) (m : ℤ) :
    K.IsMPseudoCoherent m ↔
      ((ModuleCat.restrictScalars ev0).mapDerivedCategory.obj K).IsMPseudoCoherent m := by
  have hB : ((ModuleCat.restrictScalars ev0).obj (ModuleCat.of R R)).IsPseudoCoherent :=
    regularModule_isPseudoCoherent_evalAtZero
  simpa using isMPseudoCoherent_iff_restrictScalars ev0 K m hB

end

end CategoryTheory
