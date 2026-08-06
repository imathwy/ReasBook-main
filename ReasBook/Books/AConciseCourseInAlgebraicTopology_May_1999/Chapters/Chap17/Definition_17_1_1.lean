import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.RingTheory.Flat.CategoryTheory

noncomputable section

universe u

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

variable (R : Type u) [CommRing R]

/-- Definition 17.1.1. In the module-theoretic setting used throughout Chapter 17, `Tor` is the
first derived tensor bifunctor on `ModuleCat R`. This is the source-facing bridge to the canonical
mathlib owner `CategoryTheory.Tor (ModuleCat R) 1`; the contrasting exactness facts remain the
existing theorems `rTensor_exact` and `Module.Flat.rTensor_exact`. -/
abbrev ModuleCat.torFunctor : ModuleCat R ⥤ ModuleCat R ⥤ ModuleCat R :=
  CategoryTheory.Tor (ModuleCat R) 1

/-- `ModuleCat.torFunctor R` is the degree-one Tor bifunctor on `R`-modules. -/
theorem ModuleCat.torFunctor_def : ModuleCat.torFunctor R = CategoryTheory.Tor (ModuleCat R) 1 :=
  rfl

/-- The module-theoretic `Tor` object `Tor(M, N)` over `R`. -/
abbrev ModuleCat.tor (M N : ModuleCat R) : ModuleCat R :=
  ((ModuleCat.torFunctor R).obj M).obj N

/-- `ModuleCat.tor R M N` is the same degree-one Tor module as the raw bifunctor application. -/
theorem ModuleCat.tor_def (M N : ModuleCat R) :
    ModuleCat.tor R M N = ((CategoryTheory.Tor (ModuleCat R) 1).obj M).obj N :=
  rfl

/-- If the second module is projective, then `Tor(M, N)` vanishes. -/
theorem ModuleCat.isZero_tor_of_projective_right
    (M N : ModuleCat R) [Projective N] :
    IsZero (ModuleCat.tor R M N) := by
  simpa [ModuleCat.tor_def, ModuleCat.torFunctor_def] using
    (CategoryTheory.isZero_Tor_succ_of_projective (ModuleCat R) M N 0)
