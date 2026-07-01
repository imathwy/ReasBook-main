import Mathlib
import stacks_project.Chap10.Lemma_10_136_12
import stacks_project.Chap15.Lemma_15_30_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open RingTheory Sequence

namespace Algebra

variable {R : Type u} [CommRing R]
variable {n c : ℕ}

/- Domain-style sampling:
- primary domain: explicit polynomial presentations of relative global complete intersections and
  their Koszul complexes in commutative algebra;
- sampled owner declarations:
  `Algebra.Presentation.IsRelativeGlobalCompleteIntersection`,
  `Algebra.Presentation.naive`,
  `RingTheory.Sequence.IsKoszulRegularSequence`,
  `RingTheory.Sequence.IsRegular.isKoszulRegularOn`;
- best owner abstraction: for the explicit quotient by the displayed relations `f`, the source-
  facing hypothesis should be the naive presentation-level predicate
  `Algebra.Presentation.IsRelativeGlobalCompleteIntersection`; the conclusion already uses the
  chapter owner `IsKoszulRegularSequence`;
- primitive vs. derived: the primitive data are the relations `f`; the intrinsic existential class
  `Algebra.IsRelativeGlobalCompleteIntersection R _` is derived bridge data that forgets which
  presentation witnesses the complete-intersection condition, so it is too coarse for this item.

Source/core/bridge triage:
- `source-facing`: the theorem about the specific relations `f₁, …, f_c` in the displayed
  polynomial quotient;
- `core/canonical`: the naive presentation of that quotient together with its presentation-level
  relative-global-complete-intersection predicate, and the owner predicate
  `RingTheory.Sequence.IsKoszulRegularSequence`;
- `bridge/view`: Lemma `10.136.12` for localized regularity of the displayed relations and Lemma
  `15.30.2` upgrading regular sequences to Koszul-regularity.
-/
variable (f : Fin c → MvPolynomial (Fin n) R)

local notation "PresentedIdeal" => Ideal.span (Set.range f)
local notation "PresentedAlgebra" => MvPolynomial (Fin n) R ⧸ PresentedIdeal
local notation "PresentedPresentation" =>
  (Algebra.Presentation.naive : Algebra.Presentation R PresentedAlgebra (Fin n) (Fin c))

-- Proof sketch: by Lemma `10.136.12`, every localization of the displayed presentation at a prime
-- of `PresentedAlgebra` makes the localized relations regular. Lemma `15.30.2` upgrades each such
-- localized regular sequence to localized Koszul-regularity, and the local vanishing of positive
-- Koszul homology descends back to the global Koszul complex on `f`.
/-- Lemma 15.33.4: if the quotient `R[x₁, …, xₙ] / (f₁, …, f_c)` is a relative global complete
intersection over `R`, then the defining equations `f₁, …, f_c` form a Koszul-regular sequence in
`R[x₁, …, xₙ]`. -/
theorem relativeGCI_relations_isKoszulRegularSequence
    (hP : Algebra.Presentation.IsRelativeGlobalCompleteIntersection PresentedPresentation) :
    IsKoszulRegularSequence f := by
  sorry

end Algebra
