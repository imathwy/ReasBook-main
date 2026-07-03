import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import StacksProject_2024.Chap10.Lemma_10_51_7_Artin_Tate

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open AlgHom
open scoped BigOperators

variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra R B] [Algebra R C]

/-
Domain-style sampling:
- primary domain: finite-type and finite-module arguments for fibre products in commutative
  algebra;
- sampled owner declarations: `AlgHom.equalizer`, `AlgHom.mem_equalizer`,
  `AlgHom.Finite.of_surjective`, and the Artin-Tate consequence
  `Subalgebra.finiteType_of_finite`.
- primitive data: the two comparison maps into `B`, the finite-type hypotheses on `A` and `C`,
  the surjectivity of `f`, and the finiteness of `g`;
- derived API: the finite-type conclusion for the fibre product comes from the Artin-Tate bridge
  once `A × C` is finite over the equalizer.

Source/core/bridge triage:
- `source-facing`: the fibre product is the canonical owner `AlgHom.equalizer` of the two maps
  `A × C →ₐ[R] B`;
- `bridge/view`: the internal module-finite bridge showing that `A × C` is finite as a module
  over that equalizer;
- `core/canonical`: once that bridge is available, the finite-type conclusion is the canonical
  Artin-Tate consequence `Subalgebra.finiteType_of_finite`.
-/
-- Proof sketch: realize `A ×_B C` as the equalizer subalgebra of the two maps
-- `A × C →ₐ[R] B`. Internally, the module-finite bridge identifies `A × C` as finite over that
-- equalizer, and the finite-type conclusion is then the canonical Artin-Tate consequence
-- `Subalgebra.finiteType_of_finite`.
/-- Bridge lemma for Lemma 15.5.1: under the surjective/finite hypotheses, the ambient product
`A × C` is finite as a module over the equalizer subalgebra defining the fibre product. -/
theorem moduleFinite_prod_over_equalizer_of_surjective_of_finite
    (f : A →ₐ[R] B) (g : C →ₐ[R] B) (hf : Function.Surjective f) (hg : g.Finite) :
    Module.Finite (equalizer (f.comp (fst R A C)) (g.comp (snd R A C))) (A × C) := by
  sorry

variable [IsNoetherianRing R] [Algebra.FiniteType R A] [Algebra.FiniteType R C]

/-- Lemma 15.5.1: if `R` is Noetherian, `A` and `C` are of finite type over `R`,
`f : A →ₐ[R] B` is surjective, and `g : C →ₐ[R] B` is finite, then the fibre product
`A ×_B C`, realized as the equalizer subalgebra of `A × C`, is of finite type over `R`. -/
theorem finiteType_fiberProduct_of_surjective_of_finite
    (f : A →ₐ[R] B) (g : C →ₐ[R] B) (hf : Function.Surjective f) (hg : g.Finite) :
    Algebra.FiniteType R (equalizer (f.comp (fst R A C)) (g.comp (snd R A C))) := by
  let left : A × C →ₐ[R] B := f.comp (fst R A C)
  let right : A × C →ₐ[R] B := g.comp (snd R A C)
  let T : Subalgebra R (A × C) := equalizer left right
  change Algebra.FiniteType R T
  let _ : Module.Finite T (A × C) := by
    simpa [T, left, right] using moduleFinite_prod_over_equalizer_of_surjective_of_finite f g hf hg
  exact Subalgebra.finiteType_of_finite T

end
