import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.RingTheory.RegularLocalRing.Defs

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory IsLocalRing

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-
Source/core/bridge triage:
* primary domain: projective dimension of the residue field versus Krull dimension for Noetherian
  local rings;
* sampled owner declarations:
  `CategoryTheory.projectiveDimension`,
  `CategoryTheory.projectiveDimension_eq_bot_iff`,
  `CategoryTheory.projectiveDimension_ne_top_iff`,
  `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le`;
* core/canonical owners: `projectiveDimension (ModuleCat.of R (ResidueField R))` and
  `ringKrullDim R`;
* layer: the textbook statement below is `source-facing`, while the finite-projective-dimension
  inequality that follows is a `bridge/view` reformulation for downstream use.

Primitive data are only the ambient local Noetherian ring and the canonical invariant
`projectiveDimension` of the residue-field module. There is no additional local owner object to
package here, so the refinement should keep the source-facing comparison theorem and expose only a
thin bridge in the canonical `projectiveDimension ≠ ⊤` language.
-/

-- Proof sketch: choose a finite free resolution of `ResidueField R` of length `n`, replace it by a
-- minimal one over the local ring, apply the Buchsbaum--Eisenbud criterion to the top differential
-- to obtain a regular sequence of length `n`, and then bound that length by `ringKrullDim R` using
-- the depth-dimension inequality for Noetherian local rings.
/-- Lemma 10.110.4: if the residue field of a Noetherian local ring `R` has projective dimension
`n` over `R`, then the Krull dimension of `R` is at least `n`. -/
theorem projectiveDimension_residueField_le_ringKrullDim
    {n : ℕ} (hpd : projectiveDimension (ModuleCat.of R (ResidueField R)) = n) :
    n ≤ ringKrullDim R := sorry

-- Proof sketch: unpack `projectiveDimension ≠ ⊤` into the finite-value case for the residue field
-- and then apply the source-facing theorem above.
/-- Bridge/view: if the residue field of a Noetherian local ring has finite projective dimension,
then that projective dimension is bounded above by the Krull dimension of the ring. -/
theorem projectiveDimension_residueField_le_ringKrullDim_of_ne_top
    (hpd : projectiveDimension (ModuleCat.of R (ResidueField R)) ≠ ⊤) :
    projectiveDimension (ModuleCat.of R (ResidueField R)) ≤ ringKrullDim R := sorry

end
