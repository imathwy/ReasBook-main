import Mathlib
import StacksProject_2024.Chap10.Lemma_10_155_1
import StacksProject_2024.Chap10.Lemma_10_155_2
import StacksProject_2024.Chap15.Definition_15_50_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsGRing R]
variable {Rh : Type u} [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable {Rsh : Type u} [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/- Domain-style sampling:
* primary domain: local commutative algebra of `G`-rings under henselization and strict
  henselization;
* sampled owner declarations of the same kind:
  `IsGRing`,
  `IsHenselizationOf`,
  `IsStrictHenselizationOf`,
  `isGRing_iff_forall_localizationAtMaximal_isGRing`,
  `isGRing_iff_forall_primePair_formalFiber_isGeometricallyRegular`;
* best owner abstraction: `IsGRing` is the `core/canonical` owner, while
  `IsHenselizationOf` / `IsStrictHenselizationOf` provide only the ambient chosen algebra
  objects; this file should therefore contribute canonical instances for those owners rather than
  parallel named wrapper theorems;
* primitive data: the local `G`-ring `R` together with a chosen henselization or strict
  henselization;
* derived API: the transferred `IsGRing` instances on those canonical algebra objects.

Source/core/bridge triage:
* `source-facing`: the two transferred `G`-ring assertions from Lemma 15.50.8;
* `core/canonical`: `IsGRing`;
* `bridge/view`: the henselization owners and the local-maximal-ideal criterion from
  Lemma `15.50.7`.
-/
-- Proof sketch: by Lemma `15.50.7`, it suffices to check that each localization of `Rh` at a
-- maximal ideal is a `G`-ring. For a prime of `Rh` over `p ⊂ R`, Lemma `15.45.13` identifies the
-- residue-field extension as separable algebraic over `κ(p)`, Lemma `15.45.3` identifies the
-- completion of `Rh` with the completion of `R`, and Algebra Lemma `10.166.6` transfers
-- geometric regularity of the formal fiber from `κ(p)` to the residue field upstairs.
/-- Lemma 15.50.8 (1): if `R` is a Noetherian local `G`-ring, then any henselization `Rh` of `R`
is a `G`-ring. -/
instance : IsGRing Rh := sorry

-- Proof sketch: again use Lemma `15.50.7` to reduce to the local criterion. For a prime of a
-- strict henselization over `p ⊂ R`, Lemma `15.45.13` gives a separable algebraic residue-field
-- extension over `κ(p)`. Lemma `15.45.3` and Proposition `15.49.2` show that the completion map
-- from `R^∧` to `(R^sh)^∧` is regular, and Lemma `15.41.4` then propagates regularity to the
-- formal fibers over `κ(p)`. Algebra Lemma `10.166.6` upgrades this to geometric regularity over
-- the residue field of the prime of `R^sh`.
/-- Lemma 15.50.8 (2): if `R` is a Noetherian local `G`-ring, then any strict henselization `Rsh`
of `R` is a `G`-ring. -/
instance : IsGRing Rsh := sorry

end
