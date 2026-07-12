import Mathlib
import Mathlib.Tactic.TFAE
import StacksProject_2024.Chap10.Definition_10_60_10
import StacksProject_2024.Chap10.Definition_10_109_2
import StacksProject_2024.Chap10.Definition_10_109_10
import StacksProject_2024.Chap10.Lemma_10_110_3
import StacksProject_2024.Chap10.Lemma_10_110_4
import StacksProject_2024.Chap10.Proposition_10_110_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open IsLocalRing

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/- 
Domain-style sampling:
* primary domain: homological characterizations of regular local rings for Noetherian local rings;
* sampled owner declarations:
  `projectiveDimension`,
  `projectiveDimension_ne_top_iff`,
  `IsFiniteGlobalDimensionRing`,
  `IsRegularLocalRing.iff_finrank_cotangentSpace`;
* best owner abstraction: the canonical owners are the residue-field invariant
  `projectiveDimension (ModuleCat.of R (ResidueField R))`, the ring-level owner
  `IsFiniteGlobalDimensionRing R`, and the local-regularity owner `IsRegularLocalRing R`;
* primitive data vs. derived API:
  the three owner predicates/invariants above are primitive for this proposition;
  the TFAE statement and the equalities involving `globalDimension R`, `ringKrullDim R`, and the
  cotangent-space finrank are derived API;
* source/core/bridge triage:
  the TFAE theorem is `source-facing`,
  the owner abstractions above are `core/canonical`,
  and the two equality theorems are `bridge/view` consequences.

This file should therefore stay owner-facing and avoid introducing any extra local wrapper for
"finite projective dimension of the residue field" or for regular locality.
-/

-- Proof sketch: use Proposition `10.110.1` to prove that a regular local ring has finite global
-- dimension, the definition of finite global dimension to deduce finite projective dimension for
-- the residue field, and Lemmas `10.110.3` and `10.110.4` together with the characterization of
-- regular local rings from Definition `10.60.10` to recover regularity from finite projective
-- dimension of the residue field.
/-- Helper for Proposition 10.110.5: the cotangent-space dimension dominates the Krull dimension
of a Noetherian local ring. -/
lemma ringKrullDim_le_finrank_cotangentSpace :
    ringKrullDim R ≤ Module.finrank (ResidueField R) (CotangentSpace R) := by
  -- This is the owner-level form of the discussion preceding Definition `10.60.10`.
  calc
    ringKrullDim R ≤ (maximalIdeal R).spanFinrank :=
      ringKrullDim_le_spanFinrank_maximalIdeal (R := R)
    _ = (Module.finrank (ResidueField R) (CotangentSpace R) : WithBot ℕ∞) := by
      exact_mod_cast
        IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)

/-- Helper for Proposition 10.110.5: finite global dimension gives finite projective dimension for
the residue field. -/
lemma residueField_projectiveDimension_ne_top_of_finiteGlobalDimension
    [IsFiniteGlobalDimensionRing R] :
    projectiveDimension (ModuleCat.of R (ResidueField R)) ≠ ⊤ := by
  -- Apply the canonical `projectiveDimension ≠ ⊤` criterion using the global-dimension bound.
  exact
    (CategoryTheory.projectiveDimension_ne_top_iff (ModuleCat.of R (ResidueField R))).2
      ⟨globalDimension R, inferInstance⟩

/-- Helper for Proposition 10.110.5: finite global dimension bounds the cotangent-space dimension
from above. -/
lemma finrank_cotangentSpace_le_globalDimension_of_finiteGlobalDimension
    [IsFiniteGlobalDimensionRing R] :
    (Module.finrank (ResidueField R) (CotangentSpace R) : WithBot ℕ∞) ≤ globalDimension R := by
  -- First compare the cotangent-space dimension with the residue-field projective dimension.
  have hpd_le :
      projectiveDimension (ModuleCat.of R (ResidueField R)) ≤ globalDimension R := by
    rw [CategoryTheory.projectiveDimension_le_iff]
    infer_instance
  exact le_trans
    (finrank_cotangentSpace_le_projectiveDimension_residueField (R := R))
    hpd_le

/-- Helper for Proposition 10.110.5: finite projective dimension of the residue field forces the
ambient Noetherian local ring to be regular. -/
lemma regularLocal_of_residueField_projectiveDimension_ne_top
    (hpd : projectiveDimension (ModuleCat.of R (ResidueField R)) ≠ ⊤) :
    IsRegularLocalRing R := by
  -- The source proof gives the upper bound on embedding dimension via projective dimension.
  have hcot_le :
      Module.finrank (ResidueField R) (CotangentSpace R) ≤ ringKrullDim R := by
    exact_mod_cast le_trans
      (finrank_cotangentSpace_le_projectiveDimension_residueField (R := R))
      (projectiveDimension_residueField_le_ringKrullDim_of_ne_top (R := R) hpd)
  -- Combining it with the general lower bound on the cotangent-space dimension gives regularity.
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (R := R) ?_
  simpa [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)] using hcot_le

/-- Proposition 10.110.5: for a Noetherian local ring `R`, the following are equivalent: the
residue field `ResidueField R` has finite projective dimension as an `R`-module, `R` has finite
global dimension, and `R` is a regular local ring. -/
@[stacks 00OC]
theorem residueField_finiteProjectiveDimension_finiteGlobalDimension_regularLocal_tfae :
    List.TFAE
      [ projectiveDimension (ModuleCat.of R (ResidueField R)) ≠ ⊤,
        IsFiniteGlobalDimensionRing R,
        IsRegularLocalRing R ] := by
  tfae_have 3 → 2 := by
    intro hreg
    -- Regular local rings have global dimension at most their Krull dimension.
    let _ : IsRegularLocalRing R := hreg
    have hfinrank_eq :
        Module.finrank (ResidueField R) (CotangentSpace R) = ringKrullDim R :=
      (IsRegularLocalRing.iff_finrank_cotangentSpace (R := R)).mp hreg
    have hdim :
        ringKrullDim R = Module.finrank (ResidueField R) (CotangentSpace R) :=
      hfinrank_eq.symm
    refine ⟨?_⟩
    exact
      ⟨Module.finrank (ResidueField R) (CotangentSpace R),
        hasGlobalDimensionLE_of_isRegularLocalRing (R := R) hdim⟩
  tfae_have 2 → 1 := by
    intro hfgd
    -- The residue field is one of the modules bounded by finite global dimension.
    let _ : IsFiniteGlobalDimensionRing R := hfgd
    exact residueField_projectiveDimension_ne_top_of_finiteGlobalDimension (R := R)
  tfae_have 1 → 3 := by
    intro hpd
    -- The source proof recovers regularity by sandwiching the embedding dimension.
    exact regularLocal_of_residueField_projectiveDimension_ne_top (R := R) hpd
  tfae_finish

variable [IsFiniteGlobalDimensionRing R]

-- Proof sketch: finite global dimension gives `globalDimension R` as a projective-dimension bound
-- for every module. Apply the main TFAE theorem to obtain regularity, use Proposition `10.110.1`
-- to bound the global dimension above by `ringKrullDim R`, and use the residue-field lower bound
-- from Lemma `10.110.3` together with the dimension bound from Lemma `10.110.4` to get the
-- reverse inequality.
/-- Under finite global dimension, the global dimension of a Noetherian local ring equals its Krull
dimension. -/
theorem globalDimension_eq_ringKrullDim_of_finiteGlobalDimension :
    globalDimension R = ringKrullDim R := by
  have hreg :
      IsRegularLocalRing R :=
    ((residueField_finiteProjectiveDimension_finiteGlobalDimension_regularLocal_tfae
      (R := R)).out 1 2).mp (show IsFiniteGlobalDimensionRing R from inferInstance)
  have hfinrank_eq :
      Module.finrank (ResidueField R) (CotangentSpace R) = ringKrullDim R :=
    (IsRegularLocalRing.iff_finrank_cotangentSpace (R := R)).mp hreg
  have hdim :
      ringKrullDim R = Module.finrank (ResidueField R) (CotangentSpace R) :=
    hfinrank_eq.symm
  -- The regular-local implication gives the upper bound on the global dimension.
  have hgd_le_finrank :
      globalDimension R ≤ Module.finrank (ResidueField R) (CotangentSpace R) := by
    let _ : IsRegularLocalRing R := hreg
    let _ : HasGlobalDimensionLE R (Module.finrank (ResidueField R) (CotangentSpace R)) :=
      hasGlobalDimensionLE_of_isRegularLocalRing (R := R) hdim
    exact globalDimension_le (R := R)
  have hgd_le_dim : globalDimension R ≤ ringKrullDim R := by
    simpa [hdim] using hgd_le_finrank
  -- The residue-field test module gives the reverse inequality.
  have hdim_le_gd : ringKrullDim R ≤ globalDimension R := by
    exact le_trans
      (ringKrullDim_le_finrank_cotangentSpace (R := R))
      (finrank_cotangentSpace_le_globalDimension_of_finiteGlobalDimension (R := R))
  exact le_antisymm hgd_le_dim hdim_le_gd

-- Proof sketch: by the previous theorem, `globalDimension R = ringKrullDim R`. The finite-global-
-- dimension hypothesis implies finite projective dimension for the residue field, so Lemmas
-- `10.110.3` and `10.110.4` force `ringKrullDim R` and the cotangent-space dimension to coincide.
/-- Under finite global dimension, the Krull dimension of a Noetherian local ring equals the
dimension of its cotangent space `maximalIdeal R / (maximalIdeal R)^2` over the residue field. -/
theorem ringKrullDim_eq_finrank_cotangentSpace_of_finiteGlobalDimension :
    ringKrullDim R = Module.finrank (ResidueField R) (CotangentSpace R) := by
  -- Replace the global dimension by the Krull dimension in the finite-global-dimension bound.
  have hfinrank_le_dim :
      (Module.finrank (ResidueField R) (CotangentSpace R) : WithBot ℕ∞) ≤ ringKrullDim R := by
    simpa [globalDimension_eq_ringKrullDim_of_finiteGlobalDimension (R := R)] using
      (finrank_cotangentSpace_le_globalDimension_of_finiteGlobalDimension (R := R))
  -- The ambient lower bound on cotangent-space dimension gives the opposite inequality.
  exact le_antisymm
    (ringKrullDim_le_finrank_cotangentSpace (R := R))
    hfinrank_le_dim

end
