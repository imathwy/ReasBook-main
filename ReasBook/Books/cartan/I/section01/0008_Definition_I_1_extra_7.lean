import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped PowerSeries
open PowerSeries

universe u

/- Definition I.1-extra-7: substitution of a formal series `T` with vanishing constant term into a
formal series `S` is the canonical power-series substitution operation `PowerSeries.subst`; the
side condition `b₀ = 0` is recorded by `PowerSeries.HasSubst`, and for fixed `T` the induced map
on formal series is expressed by `PowerSeries.substAlgHom`. -/
recall PowerSeries.subst

/- The source-side hypothesis `T.constantCoeff = 0` yields the canonical algebra homomorphism
`PowerSeries.substAlgHom (HasSubst.of_constantCoeff_zero' hT)`. -/
recall PowerSeries.substAlgHom

/-- The algebra homomorphism attached to a series with vanishing constant coefficient acts by the
usual substitution operation. -/
-- Proof sketch: use `HasSubst.of_constantCoeff_zero' hT` and specialize `coe_substAlgHom`.
theorem coe_substAlgHom_of_constantCoeff_zero
    {R : Type u} [CommRing R] {T : R⟦X⟧} (hT : T.constantCoeff = 0) :
    ⇑(substAlgHom (HasSubst.of_constantCoeff_zero' hT) : R⟦X⟧ →ₐ[R] R⟦X⟧) =
      (subst T : R⟦X⟧ → R⟦X⟧) := by
  let h : HasSubst T := HasSubst.of_constantCoeff_zero' hT
  simpa [h] using
    (coe_substAlgHom h : ⇑(substAlgHom h : R⟦X⟧ →ₐ[R] R⟦X⟧) = (subst T : R⟦X⟧ → R⟦X⟧))
