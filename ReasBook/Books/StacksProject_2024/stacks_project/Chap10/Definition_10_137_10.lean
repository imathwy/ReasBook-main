import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- Definition 10.137.10: the source-facing Stacks condition that `R → S` is smooth at the prime
`q`, meaning that some basic open neighborhood `S_g` with `g ∉ q` is smooth over `R`. -/
def SmoothAtPrime (q : PrimeSpectrum S) : Prop :=
  ∃ g : S, g ∉ q.asIdeal ∧ Smooth R (Localization.Away g)

-- Proof sketch: if `S_g` is smooth over `R` for some `g ∉ q`, then localizing further at the
-- prime corresponding to `q` gives `S_q`, so `S_q` is formally smooth over `R`. Conversely, for a
-- finitely presented `R`-algebra, mathlib's theorem `Algebra.IsSmoothAt.exists_notMem_smooth`
-- produces such a neighborhood from the formal smoothness of `S_q`.
/-- For finitely presented algebras, the source-facing condition `SmoothAtPrime R S q` is
equivalent to the canonical owner predicate `IsSmoothAt R q.asIdeal`. -/
theorem smoothAtPrime_iff_isSmoothAt [FinitePresentation R S] (q : PrimeSpectrum S) :
    SmoothAtPrime R S q ↔ IsSmoothAt R q.asIdeal := sorry

end Algebra

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The source-facing smoothness predicate for an `R`-algebra map at a prime of the target,
packaged through the induced `A`-algebra structure on the codomain. -/
abbrev SmoothAtPrime (f : A →ₐ[R] B) (q : PrimeSpectrum B) : Prop :=
  let _ : Algebra A B := f.toAlgebra
  Algebra.SmoothAtPrime A B q

end AlgHom

namespace RingHom

variable {A : Type v} {B : Type w}
variable [CommRing A] [CommRing B]

/-- The canonical `A`-algebra map induced by a ring hom `A → B`, used to pass from ring-map data
to the source-facing owner `AlgHom.SmoothAtPrime` without repeating anonymous `AlgHom` records. -/
abbrev toSelfAlgHom (f : A →+* B) :=
  let _ : Algebra A B := f.toAlgebra
  Algebra.ofId A B

/-- The source-facing smoothness predicate for a ring map at a prime of the target, routed through
the canonical `AlgHom.SmoothAtPrime` owner attached to the induced `A`-algebra structure. -/
abbrev SmoothAtPrime (f : A →+* B) (q : PrimeSpectrum B) : Prop :=
  let _ : Algebra A B := f.toAlgebra
  AlgHom.SmoothAtPrime f.toSelfAlgHom q

end RingHom
