import Mathlib
import Mathlib.Tactic.Recall

universe u

variable (R : Type u) [CommRing R]

/- Definition 10.120.12 is a `source-facing` item presented through the canonical mathlib owner:
there is no separate PID class in mathlib, and the textbook notion that `R` is a principal ideal
domain is expressed by the combined proposition `IsDomain R ∧ IsPrincipalIdealRing R`, usually
used via the typeclass context `[IsDomain R] [IsPrincipalIdealRing R]`. -/
#check (IsDomain R ∧ IsPrincipalIdealRing R)

section

variable [IsDomain R] [IsPrincipalIdealRing R]

/- Companion recall: the principal-ideal part of the PID hypothesis is owned by the canonical
mathlib class `IsPrincipalIdealRing R`. -/
recall IsPrincipalIdealRing

end
