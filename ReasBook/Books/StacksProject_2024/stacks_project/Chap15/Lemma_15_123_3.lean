import Mathlib
import StacksProject_2024.stacks_project.Chap15.Lemma_15_123_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

section

variable {R : Type u} [CommRing R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

namespace CochainComplex

/- Domain-style sampling for Lemma 15.123.3:
- primary domain: determinant-line comparison maps attached to admissible morphisms of bounded
  finite-projective two-term cochain complexes;
- sampled owner declarations:
  `determinantIso`,
  `determinantMap`,
  `determinantTensorIsoOfShortExact`,
  `determinant_tensor_iso_tower_commutes`;
- best owner abstraction:
  `core/canonical`: the determinant comparison maps are built from the short-exact-sequence owner
    `determinantTensorIsoOfShortExact` and its naturality/tower compatibilities;
  `source-facing`: multiplicativity of the canonical determinant isomorphism `det(a^•)` for
    composable admissible morphisms of two-term complexes;
  `bridge/view`: the contravariant map `determinantMap`, identified as the inverse linear map of
    `determinantIso`.
- primitive data: the composable morphisms `a`, `b` and admissibility of `a` and `b`;
- derived API: admissibility of `a ≫ b` via `IsAdmissible.comp`, together with the explicit
  degreewise formulas for `(a ≫ b).f (-1)` and `(a ≫ b).f 0`, so none of this should remain
  separate public input data.
-/

section

variable {K L M : Cpx}
variable [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
variable [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
variable [M.IsStrictlyGE (-1)] [M.IsStrictlyLE 0]
variable [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
variable [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
variable [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
variable [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
variable [Module.Finite R (M.X (-1))] [Module.Projective R (M.X (-1))]
variable [Module.Finite R (M.X 0)] [Module.Projective R (M.X 0)]

-- Proof sketch: apply Lemmas `15.119.2`, `15.119.3`, and `15.119.4` to the short exact kernel rows
-- in degrees `-1` and `0` for `a`, `b`, and `a ≫ b`. The determinant tensor compatibilities
-- identify the determinant isomorphism of the composite with the composite of the determinant
-- isomorphisms.
/-- Lemma 15.123.3: for composable admissible morphisms of two-term bounded finite-projective
complexes, the canonical determinant isomorphism of the composite is the composite of the
canonical determinant isomorphisms `det(K^•) → det(L^•) → det(M^•)`. -/
theorem determinantIso_comp
    (a : K ⟶ L) (ha : IsAdmissible a) (b : L ⟶ M) (hb : IsAdmissible b)
    : det((a ≫ b)^•; IsAdmissible.comp ha hb) =
        (det(a^•; ha)).trans ((det(b^•; hb) : det(L^•) ≃ₗ[R] det(M^•))) :=
  sorry

/-- Bridge/view: applying `symm` to `determinantIso_comp` recovers multiplicativity of the
contravariant determinant map `det(M^•) → det(K^•)`. -/
theorem determinantMap_comp
    (a : K ⟶ L) (ha : IsAdmissible a) (b : L ⟶ M) (hb : IsAdmissible b)
    : determinantMap (a ≫ b) (IsAdmissible.comp ha hb) =
      LinearMap.comp (determinantMap a ha)
        ((determinantMap b hb) : det(M^•) →ₗ[R] det(L^•)) :=
  congrArg (fun e ↦ e.symm.toLinearMap) (determinantIso_comp a ha b hb)

end

end CochainComplex

end
