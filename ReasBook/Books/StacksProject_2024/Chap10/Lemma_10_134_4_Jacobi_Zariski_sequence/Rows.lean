import Mathlib
import stacks_project.Chap10.Lemma_10_75_2

-- Theorem-local support for Lemma 10.134.4.

open Algebra
open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

universe u

section

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): the canonical inclusion
`range(P.cotangentComplex) ↪ P.CotangentSpace` lands in the kernel of `P.toKaehler`. This isolates
the first source exact row as a standalone rewrite fact for the low-degree `Tor` arguments. -/
theorem toKaehler_comp_cotangent_range_subtype_eq_zero
    (P : Algebra.Extension A B) :
    P.toKaehler.comp ((LinearMap.range P.cotangentComplex).subtype) = 0 := by
  -- Every element of the range is a differential, and exactness kills differentials in `Ω[B⁄A]`.
  ext x
  rcases x with ⟨x, hx⟩
  rcases hx with ⟨y, rfl⟩
  exact DFunLike.congr_fun
    (Function.Exact.linearMap_comp_eq_zero P.exact_cotangentComplex_toKaehler) y

/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): the first source row
`0 → range(d) → P.CotangentSpace → Ω[B⁄A] → 0` packaged as a short complex. -/
abbrev cotangent_range_shortComplex (P : Algebra.Extension A B) : ShortComplex (ModuleCat B) :=
  ShortComplex.moduleCatMk
    ((LinearMap.range P.cotangentComplex).subtype)
    P.toKaehler
    (toKaehler_comp_cotangent_range_subtype_eq_zero (A := A) (B := B) P)

/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): the cotangent-space presentation is
short exact. This is the first short exact row in the source proof. -/
theorem cotangent_range_shortExact
    (P : Algebra.Extension A B) :
    (cotangent_range_shortComplex (A := A) (B := B) P).ShortExact := by
  -- The range inclusion and the quotient map recover the exact cotangent row.
  have hExact :
      Function.Exact ((LinearMap.range P.cotangentComplex).subtype) P.toKaehler := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
    exact LinearMap.exact_iff.mp P.exact_cotangentComplex_toKaehler
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact hExact
  · exact (ModuleCat.mono_iff_injective _).2 (Submodule.injective_subtype _)
  · exact (ModuleCat.epi_iff_surjective _).2 P.toKaehler_surjective

/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): replacing the cotangent differential by
its image identifies the `H¹`-row with the second source short exact sequence. -/
theorem h1Cotangent_exact_rangeRestrict
    (P : Algebra.Extension A B) :
    Function.Exact P.h1Cotangentι P.cotangentComplex.rangeRestrict := by
  -- Exactness identifies `H¹(L_{B/A})` with the kernel of the range-restricted differential.
  rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict]
  exact LinearMap.exact_iff.mp P.exact_hCotangentι_cotangentComplex

/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): the second source row is a complex, i.e.
the map `P.H1Cotangent → P.Cotangent → range(d)` has zero composite. -/
theorem h1Cotangent_comp_rangeRestrict_eq_zero
    (P : Algebra.Extension A B) :
    P.cotangentComplex.rangeRestrict.comp P.h1Cotangentι = 0 := by
  -- This is the vanishing composite extracted once from the exact `H¹` row.
  exact Function.Exact.linearMap_comp_eq_zero
    (h1Cotangent_exact_rangeRestrict (A := A) (B := B) P)

end
