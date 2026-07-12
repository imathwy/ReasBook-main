import Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Tactic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MonoidalCategory
open ComplexShape HomologicalComplex

universe u v

section

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
variable [MonoidalPreadditive C]
variable {K L : CochainComplex C ℤ} [HomologicalComplex.HasTensor K L]

/- Domain-style sampling for 20.25.3.1:
- primary domain: the summandwise differential on the tensor totalization of two cochain
  complexes;
- sampled owner declarations:
  `HomologicalComplex.tensorObj`,
  `HomologicalComplex.mapBifunctor.d_eq`,
  `HomologicalComplex.mapBifunctor.d₁_eq'`,
  `HomologicalComplex.mapBifunctor.d₂_eq'`,
  `ComplexShape.ε_up_ℤ`;
- best owner abstraction:
  `core/canonical`: `HomologicalComplex.mapBifunctor` for the total differential on tensor
  products of complexes;
  `source-facing`: the degree-`(p,q)` Leibniz rule on a tensor summand;
  `bridge/view`: the tensor-specialized theorem below;
- primitive data vs. derived API: the primitive data are the canonical total differential and its
  horizontal and vertical summand maps together with the canonical summand inclusions
  `ιTensorObj`; the displayed formula is derived by specializing those owners to
  `curriedTensor C` and `up ℤ`.
- source/core/bridge triage:
  this file is `bridge/view`; it should reuse the owner formulas directly rather than introduce a
  parallel tensor-differential API.
-/

-- Proof sketch: combine `HomologicalComplex.mapBifunctor.d_eq` with the summand formulas
-- `HomologicalComplex.mapBifunctor.d₁_eq'` and `HomologicalComplex.mapBifunctor.d₂_eq'`,
-- specialized to `curriedTensor C`; for cochain complexes indexed by `ℤ`, the vertical sign is
-- `ComplexShape.ε_up_ℤ p = p.negOnePow`.
/-- 20.25.3.1: on the degree-`(p,q)` summand of the tensor product cochain complex, the
differential is the sum of the horizontal differential and `(-1)^p` times the vertical
differential. This is the categorical form of
`d(α ⊗ β) = d(α) ⊗ β + (-1)^deg(α) α ⊗ d(β)`. -/
@[stacks 07MA, reassoc]
theorem tensorObj_d_on_summand_eq (p q : ℤ) :
    ιTensorObj K L p q (p + q) rfl ≫ (tensorObj K L).d (p + q) (p + q + 1) =
      (K.d p (p + 1) ⊗ₘ 𝟙 (L.X q)) ≫
          ιTensorObj K L (p + 1) q (p + q + 1) (by abel_nf) +
        p.negOnePow •
          ((𝟙 (K.X p) ⊗ₘ L.d q (q + 1)) ≫
            ιTensorObj K L p (q + 1) (p + q + 1) (by abel_nf)) := by
  have hp : (up ℤ).Rel p (p + 1) := by simp
  have hq : (up ℤ).Rel q (q + 1) := by simp
  have hpq : (p + 1) + q = p + q + 1 := by abel_nf
  have hqp : p + (q + 1) = p + q + 1 := by abel_nf
  change
    ιMapBifunctor K L (curriedTensor C) (up ℤ) p q (p + q) rfl ≫
        (mapBifunctor K L (curriedTensor C) (up ℤ)).d (p + q) (p + q + 1) =
      (K.d p (p + 1) ⊗ₘ 𝟙 (L.X q)) ≫
          ιMapBifunctor K L (curriedTensor C) (up ℤ) (p + 1) q (p + q + 1)
            (by simpa using hpq) +
        p.negOnePow •
          ((𝟙 (K.X p) ⊗ₘ L.d q (q + 1)) ≫
            ιMapBifunctor K L (curriedTensor C) (up ℤ) p (q + 1) (p + q + 1)
              (by simpa using hqp))
  rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq' K L (curriedTensor C) (up ℤ) hp q (p + q + 1),
    mapBifunctor.d₂_eq' K L (curriedTensor C) (up ℤ) p hq (p + q + 1)]
  rw [ιMapBifunctorOrZero_eq K L (curriedTensor C) (up ℤ) (p + 1) q (p + q + 1) hpq,
    ιMapBifunctorOrZero_eq K L (curriedTensor C) (up ℤ) p (q + 1) (p + q + 1) hqp]
  simp only [curriedTensor_obj_obj, ε₁_def, curriedTensor_map_app, ε₂_def,
    ComplexShape.ε_up_ℤ, curriedTensor_obj_map, tensorHom_id, id_tensorHom]
  let A :=
    K.d p (p + 1) ▷ L.X q ≫
      ιMapBifunctor K L (curriedTensor C) (up ℤ) (p + 1) q (p + q + 1) hpq
  let B :=
    p.negOnePow •
      (K.X p ◁ L.d q (q + 1) ≫
        ιMapBifunctor K L (curriedTensor C) (up ℤ) p (q + 1) (p + q + 1) hqp)
  change ((1 : ℤ) • A) + B = A + B
  have hA : (1 : ℤ) • A = A := by simp
  exact congrArg (fun t ↦ t + B) hA

end
