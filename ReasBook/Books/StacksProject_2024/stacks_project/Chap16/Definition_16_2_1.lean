import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_137_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

open PrimeSpectrum

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]

/-
Domain-style sampling for Definition 16.2.1:
- primary domain: commutative algebra on `PrimeSpectrum`, relating smooth loci and radical ideals;
- sampled owner declarations:
  `Algebra.SmoothAtPrime`,
  `Algebra.smoothLocus`,
  `Algebra.isOpen_smoothLocus`,
  `PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical`;
- best owner abstraction: the source-facing ideal `Algebra.singularIdeal`, defined from the closed
  nonsmooth locus and exposed on the textbook surface as `H[A⁄R]`;
- primitive data: the closed set `nonsmoothLocus R A = {q | ¬ SmoothAtPrime R A q}`;
- derived API: the comparison with `smoothLocus`, radicality, its zero-locus description, and
  uniqueness among radical ideals with the same zero locus.

Source/core/bridge triage:
- source-facing: the singular ideal `H_{A/R}` and its source-level characterization by the
  nonsmooth locus;
- core/canonical: `SmoothAtPrime`, `smoothLocus`, `vanishingIdeal`, and `zeroLocus`;
- bridge/view: the finitely presented comparison with mathlib's canonical `smoothLocus`.
-/

/-- The nonsmooth locus of `Spec(A) → Spec(R)`, i.e. the primes where the Stacks-project notion
`SmoothAtPrime` fails. -/
def nonsmoothLocus : Set (PrimeSpectrum A) := { q | ¬ SmoothAtPrime R A q }

/-- The source-facing smooth locus `{q | SmoothAtPrime R A q}` is open because smoothness near a
prime is witnessed on a basic open neighborhood. -/
theorem isOpen_setOf_smoothAtPrime : IsOpen { q : PrimeSpectrum A | SmoothAtPrime R A q } := by
  refine isOpen_iff_forall_mem_open.mpr fun q hq ↦ ?_
  rcases hq with ⟨g, hgq, hg⟩
  refine ⟨↑(basicOpen g), ?_, (basicOpen g).2, ?_⟩
  · intro x hx
    exact ⟨g, by simpa [mem_basicOpen] using hx, hg⟩
  · simpa [mem_basicOpen] using hgq

/-- The nonsmooth locus is closed. -/
theorem isClosed_nonsmoothLocus : IsClosed (nonsmoothLocus R A) := by
  change IsClosed ({ q : PrimeSpectrum A | SmoothAtPrime R A q }ᶜ)
  exact (isOpen_setOf_smoothAtPrime R A).isClosed_compl

/-- For finitely presented algebras, the source-facing nonsmooth locus is the complement of
`smoothLocus`. -/
theorem nonsmoothLocus_eq_compl_smoothLocus [FinitePresentation R A] :
    nonsmoothLocus R A = (smoothLocus R A)ᶜ := by
  ext q
  simp [nonsmoothLocus, smoothLocus, smoothAtPrime_iff_isSmoothAt]

/-- Definition 16.2.1: the singular ideal `H_{A/R}` is the radical ideal cutting out the
nonsmooth locus of `Spec(A) → Spec(R)`. Since the source-facing condition `SmoothAtPrime` is
defined by existence of a smooth basic-open neighborhood, the nonsmooth locus is closed, so this
is the vanishing ideal of that closed set. We write it as `H[A⁄R]`. -/
def singularIdeal : Ideal A :=
  vanishingIdeal (nonsmoothLocus R A)

end Algebra

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The singular ideal of the target of an `R`-algebra map, viewed relative to the induced
`A`-algebra structure on the codomain. This packages the canonical owner `H[B⁄A]` without
requiring theorem surfaces to install `f.toAlgebra` explicitly. -/
abbrev singularIdeal (f : A →ₐ[R] B) : Ideal B :=
  let _ : Algebra A B := f.toAlgebra
  Algebra.singularIdeal A B

end AlgHom

namespace SingularIdealNotation

@[inherit_doc Algebra.singularIdeal]
scoped notation:max "H[" A "⁄" R "]" => Algebra.singularIdeal R A

end SingularIdealNotation

open scoped SingularIdealNotation

namespace Algebra

open PrimeSpectrum

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]

-- Proof sketch: the singular ideal is defined as a vanishing ideal, and vanishing ideals on
-- `PrimeSpectrum` are radical by `PrimeSpectrum.isRadical_vanishingIdeal`.
/-- The singular ideal is a radical ideal. -/
theorem singularIdeal_isRadical :
    (H[A⁄R]).IsRadical := by
  simpa [singularIdeal] using isRadical_vanishingIdeal (nonsmoothLocus R A)

-- Proof sketch: the nonsmooth locus is closed, so
-- `PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure` simplifies to that closed set itself.
/-- The zero locus of the singular ideal is the nonsmooth locus of `Spec(A) → Spec(R)`. -/
theorem zeroLocus_singularIdeal :
    zeroLocus (H[A⁄R]) = nonsmoothLocus R A := by
  simpa [singularIdeal] using
    (zeroLocus_vanishingIdeal_eq_closure (nonsmoothLocus R A)).trans
      (isClosed_nonsmoothLocus R A).closure_eq

/-- For finitely presented algebras, the zero locus of the singular ideal is the complement of
mathlib's `smoothLocus`. -/
theorem zeroLocus_singularIdeal_eq_compl_smoothLocus [FinitePresentation R A] :
    zeroLocus (H[A⁄R]) = (smoothLocus R A)ᶜ := by
  rw [zeroLocus_singularIdeal, nonsmoothLocus_eq_compl_smoothLocus]

-- Proof sketch: the previous theorem gives the same zero locus as `I`, and
-- `PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical` identifies `I` with the vanishing ideal of
-- its zero locus.
/-- Any radical ideal with zero locus equal to the nonsmooth locus is the singular ideal. -/
theorem singularIdeal_unique {I : Ideal A} (hI : I.IsRadical)
    (hV : zeroLocus I = nonsmoothLocus R A) :
    I = H[A⁄R] := by
  calc
    I = I.radical := by rw [hI.radical]
    _ = vanishingIdeal (zeroLocus I) := (vanishingIdeal_zeroLocus_eq_radical I).symm
    _ = vanishingIdeal (nonsmoothLocus R A) := by rw [hV]
    _ = H[A⁄R] := rfl

end Algebra
