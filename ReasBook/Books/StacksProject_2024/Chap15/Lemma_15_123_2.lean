import Mathlib
import StacksProject_2024.Chap15.Lemma_15_123_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

section

variable {R : Type u} [CommRing R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

namespace CochainComplex

/- Domain-style sampling for Lemma 15.123.2:
- primary domain: determinant maps of admissible morphisms between bounded finite-projective
  two-term cochain complexes, and invariance of those maps under chain homotopy;
- sampled owner declarations of the same kind:
  `_root_.Homotopy`,
  `_root_.Homotopy.dNext_eq`,
  `determinantMap`,
  `determinantIso`;
- best owner abstraction:
  `core/canonical`: the homotopy datum should be owned by `_root_.Homotopy a b`, and the
    determinant comparison should be stated using the chapter owner `determinantMap`;
  `source-facing`: the Stacks statement that chain-homotopic admissible perturbations induce the
    same determinant map;
  `bridge/view`: in these degrees a homotopy is equivalently determined by its degree-`0`
    component `K.X 0 ⟶ L.X (-1)`, while `determinantMap` is the contravariant view of
    `determinantIso`.
- primitive data: the two morphisms `a`, `b`, their admissibility witnesses, and a chain homotopy
  `_root_.Homotopy a b`;
- derived API: the degree `-1/0` perturbation formulas and the expanded inverse linear map
  `(determinantIso _ _).symm.toLinearMap`, so those should not remain primitive public input or
  output data here.
-/

-- Proof sketch: locally on `Spec R`, the homotopy perturbation is given by conjugating the short
-- exact kernel rows by automorphisms of the middle terms. Lemma `15.119.6` then identifies the
-- determinant contributions of `a` and `b`.
/-- Lemma 15.123.2: if `a^•, b^• : K^• → L^•` are chain-homotopic, both satisfy the
determinant-complex hypotheses, and the degree maps are surjective, then the attached determinant
maps `det(L^•) → det(K^•)` agree. For two-term complexes concentrated in degrees `-1` and `0`,
this homotopy is equivalently determined by its single component `K^0 → L^{-1}`. -/
theorem determinantMap_eq_of_chainHomotopic_surjective_perturbation
    {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    (a b : K ⟶ L) (ha : IsAdmissible a) (hb : IsAdmissible b)
    (H : _root_.Homotopy a b) :
    determinantMap b hb = determinantMap a ha := sorry

end CochainComplex

end
