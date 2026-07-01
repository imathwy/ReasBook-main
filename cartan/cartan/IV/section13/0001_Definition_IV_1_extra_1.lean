import Mathlib.RingTheory.MvPowerSeries.Basic

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool unavailable in this session; this item was matched directly against
-- `Mathlib.RingTheory.MvPowerSeries.Basic`, in particular the owner `MvPowerSeries` and its
-- inherited `AddCommGroup`, `Module`, and `Algebra` instances.

universe u

namespace MvPowerSeries

/-- `K⟦X,Y⟧` is notation for the ring of two-variable formal power series over `K`. -/
scoped notation:9000 K "⟦X,Y⟧" => MvPowerSeries (Fin 2) K

end MvPowerSeries

open scoped MvPowerSeries

section

variable (K : Type u)

/- Definition IV.1-extra-1: the textbook algebra `K[[X, Y]]` is the canonical mathlib type
`K⟦X,Y⟧`, implemented by `MvPowerSeries (Fin 2) K`, of two-variable formal power series with
coefficients in `K`. -/
#check K⟦X,Y⟧

end

section

variable (K : Type u) [AddCommGroup K]

/- The additive group structure on `K[[X, Y]]` is inherited pointwise from the coefficients. -/
#check (inferInstance : AddCommGroup K⟦X,Y⟧)

end

section

variable (K : Type u) [Semiring K]

/- The `K`-module structure on `K[[X, Y]]` is the canonical pointwise scalar action. -/
#check (inferInstance : Module K K⟦X,Y⟧)

end

section

variable (K : Type u) [CommSemiring K]

/- The `K`-algebra structure on `K[[X, Y]]` is already provided by
`Mathlib.RingTheory.MvPowerSeries.Basic`. -/
#check (inferInstance : Algebra K K⟦X,Y⟧)

end
