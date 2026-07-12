import Mathlib
import StacksProject_2024.Chap10.Definition_10_162_1
import StacksProject_2024.Chap10.Lemma_10_162_14
import StacksProject_2024.Chap15.Lemma_15_51_4
import StacksProject_2024.Chap15.Lemma_15_51_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing

section

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-
Domain-style sampling:
- primary domain: Noetherian local Nagata rings and geometric reducedness of formal fibers;
- sampled owner declarations:
  `NagataRing`,
  `LocalFormalFibersHaveProperty`,
  `IsAnalyticallyUnramified`,
  `Algebra.IsGeometricallyReducedProperty`;
- best owner abstraction: the source-facing local formal-fiber hypothesis should use the Chapter 15
  owner `LocalFormalFibersHaveProperty`, specialized to the canonical bridge
  `Algebra.IsGeometricallyReducedProperty`, while `NagataRing` remains the source-facing owner on
  the ring side;
- primitive data vs. derived API: the primitive data are the Noetherian local ring `A` and the
  formal-fiber property owner. The expanded quantifier over `q : PrimeSpectrum A` and the explicit
  fiber expression are derived API and should not remain the main public surface.

Source/core/bridge triage:
- `source-facing`: the equivalence between the Nagata condition and geometrically reduced formal
  fibers for a Noetherian local ring;
- `core/canonical`: `NagataRing`, `LocalFormalFibersHaveProperty`, `IsAnalyticallyUnramified`, and
  `Algebra.IsGeometricallyReducedProperty`;
- `bridge/view`: Lemma `10.162.14` supplies the analytic-unramified bridge, while
  `LocalFormalFibersHaveProperty` packages the fiberwise condition.
-/

-- Proof sketch: apply Lemma `10.162.14` to identify the Nagata condition for a Noetherian local
-- ring with analytic unramifiedness of finite local domain extensions. For the forward direction,
-- geometrically reduced formal fibers imply the relevant completions are reduced after passing to
-- fraction fields, hence those local extensions are analytically unramified. For the reverse
-- direction, use the Nagata criterion to show that every finite residue-field extension of every
-- prime formal fiber remains reduced.
/-- Helper for Lemma 15.52.4: on a local base, the `P`-ring criterion reduces to transporting the
closed formal-fiber hypothesis to the localization at the maximal ideal. -/
theorem isPRing_of_localFormalFibersHaveProperty_closed_point
    (P : FieldAlgebraProperty)
    [P.HasPropertyC] [P.HasPropertyD]
    (htransport :
      LocalFormalFibersHaveProperty P A →
        LocalFormalFibersHaveProperty P (Localization.AtPrime (maximalIdeal A)))
    (hformal : LocalFormalFibersHaveProperty P A) :
    IsPRing P A := by
  -- Proof comment: for a local ring, Lemma `15.51.4` only asks for the unique maximal
  -- localization, so it is enough to transport the closed formal-fiber hypothesis once.
  rw [isPRing_iff_localFormalFibersHaveProperty_atMaximal]
  intro m
  have hm : m.asIdeal = maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal m.isMaximal
  cases m
  cases hm
  simpa using htransport hformal

/-- Helper for Lemma 15.52.4: a `P`-ring has formal fibers with property `P` along the maximal
ideal completion map. -/
theorem localFormalFibersHaveProperty_of_pRing
    (P : FieldAlgebraProperty)
    [P.HasPropertyB] [P.HasPropertyD]
    (hP : IsPRing P A) :
    LocalFormalFibersHaveProperty P A := by
  -- TODO: apply Lemma `15.51.6` specialized to the maximal ideal completion map once the
  -- prerequisite completion-fiber API is available in the dependency-closed import chain for this
  -- item.
  sorry

/-- Helper for Lemma 15.52.4: geometrically reduced formal fibers persist after localizing a
local ring at its maximal ideal. -/
lemma geometricallyReduced_formalFibers_closed_point_localization
    (hred : LocalFormalFibersHaveProperty Algebra.IsGeometricallyReducedProperty A) :
    LocalFormalFibersHaveProperty Algebra.IsGeometricallyReducedProperty
      (Localization.AtPrime (maximalIdeal A)) := by
  -- TODO: compare the closed-point localization with `A` via the canonical algebra equivalence,
  -- then transport both the residue field and the formal-fiber ring across the induced completion
  -- comparison.
  sorry

/-- Helper for Lemma 15.52.4: a geometrically reduced `P`-ring forces finite local domain
extensions to be analytically unramified. -/
lemma finite_local_domain_isAnalyticallyUnramified_of_geometricallyReduced_pRing
    {S : Type v} [CommRing S] [Algebra A S] [Module.Finite A S] [IsDomain S]
    [IsLocalRing S] [IsLocalHom (algebraMap A S)]
    (hP : IsPRing Algebra.IsGeometricallyReducedProperty A) :
    IsAnalyticallyUnramified S := by
  -- TODO: first pass `hP` to `S` using essential finite type permanence, then apply
  -- `completion_fibers_have_property_of_pRing` at the zero prime of the domain `S` and use the
  -- injective map from the completion into its generic fiber to deduce that the completion itself
  -- is reduced.
  sorry

/-- Helper for Lemma 15.52.4: a Nagata local ring is a geometrically reduced `P`-ring. -/
lemma geometricallyReduced_pRing_of_nagataRing
    (hNagata : NagataRing A) :
    IsPRing Algebra.IsGeometricallyReducedProperty A := by
  -- TODO: follow the source proof by testing geometric reducedness on finite purely inseparable
  -- residue-field extensions of each prime formal fiber, model those extensions by finite local
  -- domain algebras over `A / q`, and compare with the reduced completions given by the Nagata
  -- criterion.
  sorry

/-- Helper for Lemma 15.52.4: geometrically reduced formal fibers imply the Nagata condition for
the local ring. -/
theorem nagataRing_of_geometricallyReduced_formalFibers
    (hred : LocalFormalFibersHaveProperty Algebra.IsGeometricallyReducedProperty A) :
    NagataRing A := by
  -- Proof comment: first turn the local formal-fiber hypothesis into the closed-point `P`-ring
  -- condition.
  have hP : IsPRing Algebra.IsGeometricallyReducedProperty A := by
    exact
      isPRing_of_localFormalFibersHaveProperty_closed_point
        (A := A)
        (P := Algebra.IsGeometricallyReducedProperty)
        geometricallyReduced_formalFibers_closed_point_localization
        hred
  -- Proof comment: the local TFAE for Nagata rings reduces the conclusion to the analytic
  -- unramifiedness of finite local domain extensions.
  exact
    (nagataRing_tfae_analyticallyUnramified_finite_domain_extensions A).out 2 0
      (fun S ↦
        finite_local_domain_isAnalyticallyUnramified_of_geometricallyReduced_pRing
          (A := A)
          (S := S)
          hP)

/-- Lemma 15.52.4: for a Noetherian local ring `A`, being Nagata is equivalent to having
geometrically reduced formal fibers. -/
@[stacks 0BJ0]
theorem nagataRing_iff_geometricallyReduced_formalFibers :
    NagataRing A ↔
      LocalFormalFibersHaveProperty Algebra.IsGeometricallyReducedProperty A := by
  constructor
  · intro hNagata
    -- Proof comment: the reverse direction is the source-faithful `Nagata ⇒ P` upgrade followed
    -- by the standard completion-fiber theorem for `P`-rings.
    exact
      localFormalFibersHaveProperty_of_pRing
        (A := A)
        (P := Algebra.IsGeometricallyReducedProperty)
        (geometricallyReduced_pRing_of_nagataRing (A := A) hNagata)
  · intro hred
    -- Proof comment: the forward direction is packaged in the local Nagata reduction above.
    exact nagataRing_of_geometricallyReduced_formalFibers (A := A) hred

end
