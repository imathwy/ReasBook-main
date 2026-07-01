import stacks_project.Chap14.Lemma_14_18_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial

universe v u

noncomputable section

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]

/- Domain-style sampling for Lemma 14.18.8:
- primary domain: simplicial objects in an abelian category, subobjects cut out by face-map
  kernels, and the simplicial identities relating adjacent face maps;
- sampled owner API:
  `NormalizedMooreComplex.objX`,
  `SimplicialObject.lowerFaceKernelSubobject`,
  `SimplicialObject.lowerFaceKernelSubobject_add_one`,
  `SimplicialObject.opFunctor`,
  `SimplicialObject.δ_comp_δ`,
  `Limits.pullback_factors_iff`;
- best owner abstraction: the core/canonical kernel-intersection owner in this domain is
  `NormalizedMooreComplex.objX`; the source-facing lower-face convention is already exposed
  upstream as the bridge/view owner `SimplicialObject.lowerFaceKernelSubobject`, defined from
  `NormalizedMooreComplex.objX` via `SimplicialObject.opFunctor`;
- source/core/bridge triage:
  `source-facing`: the stability of the lower-face kernel intersection under the last face map;
  `core/canonical`: `NormalizedMooreComplex.objX`;
  `bridge/view`: the owner `SimplicialObject.lowerFaceKernelSubobject` from
  [Lemma_14_18_6](/volume/math/AI4M/users/zcwang/stacks_project/stacks_project/Items/Chap14/Lemma_14_18_6.lean),
  which packages the lower-face convention as the reversed-simplex view of the normalized Moore
  subobject. -/

-- Proof sketch: for `m = 0` the target lower-face kernel intersection is `⊤`. For `m + 1`, the
-- degree-`m + 1` lower-face kernel intersection is the finite infimum of the kernel subobjects of
-- `U.δ (Fin.castSucc k)`. To show the last face factors through that infimum, it suffices to show
-- it factors through each kernel. For a fixed `k`, the simplicial identity rewrites
-- `U.δ (Fin.last (m + 2)) ≫ U.δ (Fin.castSucc k)` as
-- `U.δ (Fin.castSucc (Fin.castSucc k)) ≫ U.δ (Fin.last (m + 1))`, and the source arrow already
-- factors through the kernel of `U.δ (Fin.castSucc (Fin.castSucc k))`.
namespace SimplicialObject

/-- Lemma 14.18.8: the last face map sends the intersection of the kernels of the lower faces in
degree `m + 1` into the corresponding intersection in degree `m`. -/
theorem lowerFaceKernelSubobject_succ_le_pullback_last_face
    (U : SimplicialObject A) (m : ℕ) :
    U.lowerFaceKernelSubobject (m + 1) ≤
      (Subobject.pullback (U.δ (Fin.last (m + 1)))).obj
        (U.lowerFaceKernelSubobject m) := by
  cases m with
  | zero =>
      apply Subobject.le_of_factors
      rw [pullback_factors_iff]
      simpa using
        (Subobject.top_factors ((U.lowerFaceKernelSubobject 1).arrow ≫ U.δ (Fin.last 1)))
  | succ m =>
      apply Subobject.le_of_factors
      rw [pullback_factors_iff]
      rw [lowerFaceKernelSubobject_add_one U m]
      refine (Subobject.finset_inf_factors _).2 ?_
      intro k hk
      apply kernelSubobject_factors
      have hklt : Fin.castSucc (Fin.castSucc k) < Fin.last (m + 2) := by
        simp
      have hfac :
          (kernelSubobject (U.δ (Fin.castSucc (Fin.castSucc k)))).Factors
            (U.lowerFaceKernelSubobject (m + 2)).arrow := by
        rw [lowerFaceKernelSubobject_add_one U (m + 1)]
        exact
          Subobject.finset_inf_arrow_factors Finset.univ
            (fun l : Fin (m + 2) ↦ kernelSubobject (U.δ (Fin.castSucc l)))
            (Fin.castSucc k) (by simp)
      rw [Category.assoc, U.δ_comp_δ' hklt]
      simp only [Fin.pred_last]
      rw [← Subobject.factorThru_arrow _ _ hfac, Category.assoc,
        kernelSubobject_arrow_comp_assoc, zero_comp, comp_zero]

end SimplicialObject

end CategoryTheory
