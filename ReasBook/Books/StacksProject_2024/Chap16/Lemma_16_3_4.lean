import Mathlib
import StacksProject_2024.Chap10.Lemma_10_137_9
import StacksProject_2024.Chap16.Lemma_16_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/- Domain-style sampling for smooth retractions with standard smooth targets:
* primary domain: smooth commutative algebra, syntomic factorization, and standard smooth
  presentations;
* sampled owner declarations:
  `Smooth R A`,
  `exists_smooth_retraction_relativeGlobalCompleteIntersection_of_syntomic`,
  `Algebra.IsStandardSmooth`;
* best owner abstraction:
  the ambient owners are `Smooth R A` for the input algebra, the Chapter 16 retraction theorem
  `exists_smooth_retraction_relativeGlobalCompleteIntersection_of_syntomic` for the retract data,
  and `Algebra.IsStandardSmooth R B` for the strengthened target conclusion;
* primitive vs. derived:
  the primitive public output is only the smooth `A`-algebra retract together with the standard
  smooth owner on the target. The syntomic upgrade and the relative-global-complete-intersection
  witness are bridge data from upstream owners and should not be repackaged here as a parallel
  local wrapper.

Source/core/bridge triage:
* `source-facing`: the existence of a smooth `A`-algebra retract `B` that is standard smooth over
  `R`;
* `core/canonical`: `Smooth`, `RingHom.Syntomic`, `Algebra.IsStandardSmooth`, and the Chapter 16
  retraction owner theorem;
* `bridge/view`: the intermediate relative-global-complete-intersection presentation obtained from
  syntomicity, together with the bridge theorem `smooth_syntomic` converting the input smoothness
  hypothesis into the syntomic hypothesis needed for that retraction theorem.
-/

-- Proof sketch: first apply the bridge theorem `smooth_syntomic` to view the smooth map `R → A`
-- as syntomic. Then invoke the Chapter 16 retraction theorem
-- `exists_smooth_retraction_relativeGlobalCompleteIntersection_of_syntomic` to obtain a smooth
-- `A`-algebra retraction `A → B → A` with `B` a relative global complete intersection over `R`.
-- Finally apply the Stacks Jacobian argument to that retract presentation to promote the target to
-- the canonical owner `IsStandardSmooth R B`, while preserving the same retract shape over `A`.
/-- Lemma 16.3.4: if `R → A` is smooth, then there exists a smooth `R`-algebra map `A → B` with
an `A`-algebra retraction such that `B` is standard smooth over `R`. The presentation-theoretic
Jacobian data are carried canonically by the owner `IsStandardSmooth R B`, so they are not
repackaged here as separate public output. -/
theorem exists_smooth_retraction_standardSmooth_of_smooth [Smooth R A] :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B) (_ : Algebra A B)
      (_ : IsScalarTower R A B) (_ : Smooth A B) (r : B →ₐ[A] A),
      IsStandardSmooth R B := sorry

end

end Algebra
