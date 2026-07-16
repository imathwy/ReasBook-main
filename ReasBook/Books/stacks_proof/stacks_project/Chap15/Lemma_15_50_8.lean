import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_166_6
import stacks_proof.stacks_project.Chap10.Lemma_10_155_1
import stacks_proof.stacks_project.Chap10.Lemma_10_155_2
import stacks_proof.stacks_project.Chap15.Definition_15_50_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsGRing R]
variable {Rh : Type u} [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable {Rsh : Type u} [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/-- Helper for Lemma 15.50.8: a local ring is its own localization at the complement of the
maximal ideal. -/
lemma self_isLocalization_primeCompl_maximalIdeal
    (A : Type u) [CommRing A] [IsLocalRing A] :
    IsLocalization (maximalIdeal A).primeCompl A := by
  -- Every element away from the maximal ideal is already a unit, so the identity map satisfies
  -- the universal localization property.
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    exact IsLocalRing.notMem_maximalIdeal.mp y.2
  · intro z
    exact ⟨⟨z, 1⟩, by simp⟩
  · intro x y hxy
    exact ⟨1, by simpa using hxy⟩

/-- Helper for Lemma 15.50.8: localizing a local ring at its maximal ideal does not change the
ring. -/
noncomputable abbrev localizationAtMaximalIdeal_algEquiv_self
    (A : Type u) [CommRing A] [IsLocalRing A] :
    Localization.AtPrime (maximalIdeal A) ≃ₐ[A] A :=
  let _ : IsLocalization (maximalIdeal A).primeCompl A :=
    self_isLocalization_primeCompl_maximalIdeal A
  Localization.algEquiv (maximalIdeal A).primeCompl A

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
-- Route correction: the clean bridge through the generic `P`-ring henselization theorem would be
-- source-faithful here, but in this repo snapshot its dependency chain currently fails in
-- `Lemma_15_12_3`. The remaining work is therefore to execute the textbook branch-by-branch proof
-- directly in this file using `Lemma_15_45_3`, `Lemma_15_45_13`, and the local formal-fiber
-- criterion from `Lemma_15_50_7`.
-- TODO: prove the henselization case by checking local formal fibers over primes `q ⊂ Rh`,
-- identifying `(Rh)^∧` with `R^∧`, extracting the `q`-branch from the finite product
-- decomposition over `κ(p)`, and then applying separable base change to `κ(q)`.
instance : IsGRing Rh := sorry

-- Proof sketch: again use Lemma `15.50.7` to reduce to the local criterion. For a prime of a
-- strict henselization over `p ⊂ R`, Lemma `15.45.13` gives a separable algebraic residue-field
-- extension over `κ(p)`. Lemma `15.45.3` and Proposition `15.49.2` show that the completion map
-- from `R^∧` to `(R^sh)^∧` is regular, and Lemma `15.41.4` then propagates regularity to the
-- formal fibers over `κ(p)`. Algebra Lemma `10.166.6` upgrades this to geometric regularity over
-- the residue field of the prime of `R^sh`.
/-- Lemma 15.50.8 (2): if `R` is a Noetherian local `G`-ring, then any strict henselization `Rsh`
of `R` is a `G`-ring. -/
-- TODO: prove the strict henselization case by showing the completion map
-- `R^∧ → (R^sh)^∧` is regular, base-changing that regularity to the `κ(p)`-fiber, extracting the
-- chosen branch from the finite product decomposition over primes above `p`, and then upgrading
-- to `κ(r)` by separable base change.
instance : IsGRing Rsh := sorry

end
