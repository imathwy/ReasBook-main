import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LocalizedModule.Away
import stacks_project.Chap15.Situation_15_128_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open scoped ClosedPointFiber

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-
Domain triage:
- primary domain: fibrewise linear algebra on the quotient fibre `M(x) = M / xM` at a closed point;
- owner declarations sampled for this file:
  `closedPointFiber`,
  `LocalizedModule.Away`,
  `LocalizedModule.map`,
  `closedPointFiberVisibleQuotient`,
  `closedPointFiberVisibleClass`;
- source-facing layer: the localized splitting-after-inverting predicate from the source statement,
  expressed against the chapter owner `V(x)` for the visible quotient of the fibre;
- core/canonical layer: the owner localization map `LocalizedModule.map` and the visible quotient
  owner declarations imported from `Situation_15_128_1`;
- bridge/view: the free localized source `LocalizedModule.Away f (Fin r → R)` is canonically a
  finite free `Localization.Away f`-module, but the source predicate is best phrased as a left
  inverse to the localized owner map rather than through a tensor-product presentation;
- primitive data: the closed point `x`, the chosen sections `s`, and the localization parameter
  `f`;
- derived API: the visible classes supplied by the chapter owner file and the localized splitting
  predicate below.
-/

local notation "Ω" => closedPoints (PrimeSpectrum R)

/-- The `R`-linear map sending the standard basis of `R^r` to the chosen sections. -/
private noncomputable abbrev selectedSectionsMap {r : ℕ} (s : Fin r → M) : (Fin r → R) →ₗ[R] M :=
  (Pi.basisFun R (Fin r)).constr R s

/-- The textbook condition that the sections `s₁, …, s_r` become the inclusion of a direct summand
after inverting some element away from the closed point `x`. -/
def selectedSectionsSplitAfterInverting {r : ℕ} (x : Ω) (s : Fin r → M) : Prop :=
  ∃ f : R, f ∉ x.1.asIdeal ∧
    ∃ ρ : LocalizedModule.Away f M →ₗ[Localization.Away f] LocalizedModule.Away f (Fin r → R),
      Function.LeftInverse ρ (LocalizedModule.map (Submonoid.powers f) (selectedSectionsMap s))

section

variable [Module.FinitePresentation R M]

-- Proof sketch: identify `B(x)` with the orthogonal of the image of `Hom_R(M, R)` in the dual of
-- the fibre `M(x)`. If the localized section map splits, pull the dual basis back to obtain
-- functionals whose classes separate the images of the chosen sections, giving linear independence
-- in `V(x)`. Conversely, lift independent classes in `V(x)` to fibrewise linear forms, use finite
-- presentation together with the localization statement from Algebra, Lemma 10.10.2, and recover a
-- retraction after inverting an element outside `x`.
/-- Lemma 15.128.2: for a closed point `x`, the canonical quotient `V(x)` of the fibre by the
subspace `B(x)` detects when finitely many sections split off a free summand after inverting an
element away from `x`; equivalently, the corresponding classes in `V(x)` are linearly independent
over `κ(x)`. -/
theorem selectedSections_splitAfterInverting_iff_linearIndependent_visibleClasses
    (x : Ω) {r : ℕ} (s : Fin r → M) :
    selectedSectionsSplitAfterInverting x s ↔
      LinearIndependent (κ(x)) (closedPointFiberVisibleClass x ∘ s) :=
  sorry

end

end
