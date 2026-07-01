import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import stacks_project.Chap15.Definition_15_59_1
import stacks_project.Chap15.Lemma_15_59_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

set_option checkBinderAnnotations false

universe u

namespace CochainComplex

section

variable {R : Type u} [CommRing R]
variable {K L : CochainComplex (ModuleCat R) ℤ}

/- Domain sampling pass:
* primary domain: factorization up to homotopy of morphisms of cochain complexes of `R`-modules
  through quasi-isomorphisms with K-flat source, on the canonical tensor surface of
  `ModuleCat R`;
* sampled owner declarations:
  - `CochainComplex.IsKFlat` from `Definition_15_59_1`, the chapter owner for the K-flatness
    clause on the intermediate complex in the canonical module-tensor context;
  - `CochainComplex.tensorHom_right_quasiIso_of_isKFlat` from `Lemma_15_59_2`, the nearby owner
    showing that tensoring with a K-flat complex preserves quasi-isomorphisms;
  - `CochainComplex.isKFlat_obj₂_of_distinguished_triangle` and
    `CochainComplex.isKFlat_obj₃_of_distinguished_triangle` from `Lemma_15_59_5`, the chapter
    owners for the two-out-of-three propagation of K-flatness in distinguished triangles;
  - `exists_termwiseEpi_kFlatResolution` from `Lemma_15_59_10`, the chapter owner supplying the
    K-flat replacement input used in the standard construction;
  - `Homotopy` and `QuasiIso`, the canonical comparison owners for the factorization data.

Source/core/bridge triage:
* `source-facing`: the Stacks lemma is stated for an arbitrary ring, but the current Chapter 15
  owner `CochainComplex.IsKFlat` is available here only on the canonical tensor surface of
  `ModuleCat R`, so this file records the faithful commutative-ring specialization instead of
  quantifying over an arbitrary monoidal structure on `ModuleCat R`;
* `core/canonical`: `N.IsKFlat`, `QuasiIso c`, and `Homotopy a (b ≫ c)`;
* `bridge/view`: the commutative-ring specialization of the source factorization statement to the
  canonical module-tensor owner used in this chapter.

Primitive data are only the intermediate complex `N` and the maps `b`, `c`. The K-flatness,
quasi-isomorphism, and homotopy clauses are derived API over existing owner abstractions, so this
file exposes them directly instead of introducing a factorization wrapper structure.
-/

-- Proof sketch: complete `a` to a distinguished triangle and replace its cone by a K-flat
-- quasi-isomorphic model. The resulting comparison triangle
-- `K^• ⟶ N^• ⟶ M^• ⟶ K^•[1]` gives `N^•` K-flat by the two-out-of-three K-flatness theorem, and
-- the triangle comparison yields a map `c : N^• ⟶ L^•` whose composite with `b` is homotopic to
-- `a`.
/-- Commutative-ring specialization of Lemma 15.59.16 (1): if
`a : K^• ⟶ L^•` is a morphism of cochain complexes of `R`-modules and `K^•` is K-flat, then `a`
factors up to homotopy through a quasi-isomorphism `c : N^• ⟶ L^•` with `N^•` K-flat. -/
theorem exists_kFlat_factorization_up_to_homotopy
    (a : K ⟶ L) (hK : K.IsKFlat) :
    ∃ (N : CochainComplex (ModuleCat R) ℤ) (b : K ⟶ N) (c : N ⟶ L),
      Nonempty (Homotopy a (b ≫ c)) ∧ N.IsKFlat ∧ QuasiIso c := sorry

/- The source also records a termwise-flat refinement. In the current Chapter 15 owner hierarchy,
`CochainComplex.IsTermwiseFlat` is likewise available on the commutative-ring tensor surface, so
the strengthened factorization theorem stays in the same canonical module-tensor context as the
preceding specialization. The source K-flatness hypothesis on `K` is retained here: termwise
flatness refines the choice of `N`, but the two-out-of-three K-flatness argument for `N` still
runs through `K.IsKFlat`. -/

-- Proof sketch: choose the comparison triangle in split degreewise form so that
-- `N^n ≅ M^n ⊕ K^n`; K-flatness of `K^•` and of the chosen cone replacement gives `N.IsKFlat`
-- by the same two-out-of-three argument as above, while flatness of the terms of `K^•` and of
-- the cone replacement propagates termwise to `N^•`.
/-- Commutative-ring bridge for the termwise-flat refinement of Lemma 15.59.16: if
`a : K^• ⟶ L^•` is a morphism of cochain
complexes of `R`-modules, `K^•` is K-flat, and each term of `K^•` is flat, then one may moreover
choose the intermediate complex `N^•` with flat terms. -/
theorem exists_termwiseFlat_kFlat_factorization_up_to_homotopy
    (a : K ⟶ L) (hK : K.IsKFlat) (hFlat : K.IsTermwiseFlat) :
    ∃ (N : CochainComplex (ModuleCat R) ℤ) (b : K ⟶ N) (c : N ⟶ L),
      Nonempty (Homotopy a (b ≫ c)) ∧ N.IsKFlat ∧ N.IsTermwiseFlat ∧ QuasiIso c := sorry

end

end CochainComplex
