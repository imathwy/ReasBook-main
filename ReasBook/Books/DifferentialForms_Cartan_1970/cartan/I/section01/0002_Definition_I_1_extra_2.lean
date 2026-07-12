import Mathlib

open scoped PowerSeries

universe u

section

variable (K : Type u)

/- Definition I.1-extra-2: the algebra of formal series in one variable over `K` is the
canonical type `K⟦X⟧` of formal power series. Its standard addition, scalar multiplication,
multiplication, zero, and unit are the existing algebraic structure on this type. -/
#check K⟦X⟧

section

variable [CommSemiring K]

/- The inherited `K`-algebra structure on formal power series over `K`. -/
#check (inferInstance : Algebra K K⟦X⟧)

/- The canonical algebra map identifying polynomials with a subalgebra of `K⟦X⟧`. -/
#check (Polynomial.coeToPowerSeries.algHom K : Polynomial K →ₐ[K] K⟦X⟧)

end

end
