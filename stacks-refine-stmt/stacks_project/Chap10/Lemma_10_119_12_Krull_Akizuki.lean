import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {L : Type v}
variable [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable [Field L] [Algebra (FractionRing R) L] [FiniteDimensional (FractionRing R) L]
variable [Algebra R L] [IsScalarTower R (FractionRing R) L]

/-
Domain triage:
* primary domain: intermediate `R`-subalgebras of a finite extension of `FractionRing R` over a
  one-dimensional Noetherian domain;
* sampled owner declarations in this domain:
  - `Ring.KrullDimLE 1 R`, the core dimension-at-most-one owner already used in nearby files;
  - `IsNoetherianRing.of_finite`, the canonical owner for deriving Noetherianity from
    module-finiteness when that stronger input is available;
  - `Subalgebra.isNoetherianRing_of_fg`, the owner-side API showing that Noetherianity of a
    subalgebra is derived data of the subalgebra object rather than separate packaged structure;
  - `FiniteDimensional.finiteDimensional_subalgebra`, the ambient finite-dimensional owner for
    subalgebras inside a finite-dimensional algebra.
* source/core/bridge split:
  - `source-facing`: the textbook Krull-Akizuki statement with explicit hypothesis
    `ringKrullDim R = 1`;
  - `core/canonical`: the intermediate owner `A : Subalgebra R L` together with the ambient owner
    hypothesis `[Ring.KrullDimLE 1 R]`;
  - `bridge/view`: the conversion from the explicit equality `ringKrullDim R = 1` to the
    canonical typeclass owner.
* primitive vs. derived:
  - primitive data are the ambient field-extension tower and the chosen intermediate subalgebra
    `A`;
  - `IsNoetherianRing A` is derived API and should live as owner-side output on `A`, not as a
    separate wrapper notion.
-/

namespace Subalgebra

-- Proof sketch: let `I` be a nonzero ideal of an intermediate `R`-subalgebra `A ⊆ L`. Since
-- `L` is algebraic over the fraction field of `R`, Lemma `10.30.8` gives a nonzero element
-- `x ∈ I ∩ R`. Realize `A` as an `R`-submodule of a finite-dimensional `FractionRing R`-vector
-- space and apply Lemma `10.119.11` to deduce that `A / xA`, hence also `I / xA`, has finite
-- length over `R`. A finite-length quotient yields finite generation of `I`, so every ideal of
-- `A` is finitely generated and `A` is Noetherian.
/-- Under the canonical dimension-at-most-one owner hypothesis, every intermediate `R`-subalgebra
of a finite extension of `FractionRing R` is Noetherian. -/
instance isNoetherianRing_of_krullDimLEOne_of_finiteDimensional [Ring.KrullDimLE 1 R]
    (A : Subalgebra R L) :
    IsNoetherianRing A := by
  sorry

/-- Lemma 10.119.12 (Krull-Akizuki): if `R` is a Noetherian domain of Krull dimension `1` and
`L` is a finite extension of the fraction field of `R`, then every intermediate `R`-subalgebra
of `L` is a Noetherian ring. This source-facing form is a bridge to the canonical owner-side
instance above. -/
theorem isNoetherianRing_of_ringKrullDim_eq_one
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {L : Type v} [Field L] [Algebra (FractionRing R) L] [FiniteDimensional (FractionRing R) L]
    [Algebra R L] [IsScalarTower R (FractionRing R) L]
    (A : Subalgebra R L) (hdim : ringKrullDim R = 1) :
    IsNoetherianRing A := by
  letI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by simp [hdim])
  exact isNoetherianRing_of_krullDimLEOne_of_finiteDimensional A

end Subalgebra

end
