import DifferentialForms_Cartan_1970.cartan.IV.section13.«0001_Definition_IV_1_extra_1»
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool unavailable in this session; this item is matched directly against
-- `MvPowerSeries.order`, `MvPowerSeries.order_eq_nat`, and `MvPowerSeries.order_mul`.

universe u

open scoped MvPowerSeries

section
variable {K : Type u} [Semiring K]

/- Definition IV.1-extra-2: for a two-variable formal power series, the textbook order is the
canonical mathlib notion `MvPowerSeries.order`. Its defining clause as the least total degree with
nonzero homogeneous component is expressed by `MvPowerSeries.order_eq_nat`. -/
#check MvPowerSeries.order
#check MvPowerSeries.order_eq_nat

end

section

variable {K : Type u} [Semiring K] [NoZeroDivisors K]

/- Definition IV.1-extra-2 (1): multiplicativity of order for two-variable formal power series is
the canonical theorem `MvPowerSeries.order_mul` under the upstream no-zero-divisors hypothesis on
the coefficient semiring. -/
#check (MvPowerSeries.order_mul : ∀ f g : K⟦X,Y⟧, (f * g).order = f.order + g.order)

end

section

variable {K : Type u} [Ring K] [NoZeroDivisors K] [Nontrivial K]

/- Definition IV.1-extra-2 (2): the textbook field case that `K[[X, Y]]` is an integral domain is
a specialization of the canonical `NoZeroDivisors.to_isDomain` bridge, applied to the upstream
`NoZeroDivisors` instance on `MvPowerSeries`. -/
#check (NoZeroDivisors.to_isDomain K⟦X,Y⟧ : IsDomain K⟦X,Y⟧)

end
