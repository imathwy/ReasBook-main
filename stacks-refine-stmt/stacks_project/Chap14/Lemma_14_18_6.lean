import Mathlib
import Mathlib.AlgebraicTopology.SimplicialObject.Op

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicTopology
open Abelian.DoldKan
open scoped Simplicial

universe v u

noncomputable section

namespace CategoryTheory

open _root_.SimplicialObject

variable {A : Type u} [Category.{v} A] [Abelian A]

/- Domain-style sampling for Lemma 14.18.6:
- primary domain: split simplicial objects and the Dold-Kan equivalence in abelian categories
- sampled owner API:
  `DoldKan.Γ₀'`,
  `SimplicialObject.Split.forget`,
  `Abelian.DoldKan.equivalence`,
  `NormalizedMooreComplex.objX`,
  `SimplicialObject.opFunctor`
- best owner abstraction: the canonical split functor `Abelian.DoldKan.N ⋙ DoldKan.Γ₀'`
- primitive data: that split functor together with the canonical normalized-Moore owner
  `NormalizedMooreComplex.objX`
- derived API: the forgetful comparison with `𝟭 (SimplicialObject A)` and the identification of
  its nondegenerate terms with `NormalizedMooreComplex.objX`; the lower-face convention
  `d₀, …, d_{n-1}` is a bridge/view obtained by applying `NormalizedMooreComplex.objX` to
  `SimplicialObject.opFunctor.obj U`
- source/core/bridge triage: the textbook lemma is `source-facing`, but its canonical owner is the
  split functor `Abelian.DoldKan.N ⋙ DoldKan.Γ₀'`; the forgetful isomorphism, the degreewise
  identification, and the lower-face kernel-intersection description are the relevant
  `bridge/view` consequences, so no extra existential wrapper should remain public.
-/

/- Lemma 14.18.6: the canonical functorial splitting of simplicial objects in an abelian category
is the Dold-Kan composite `Abelian.DoldKan.N ⋙ DoldKan.Γ₀'`. -/
#check (N ⋙ DoldKan.Γ₀' : SimplicialObject A ⥤ SimplicialObject.Split A)

namespace SimplicialObject

/-- The intersection of the kernels of the lower face maps in degree `n`. This is the normalized
Moore subobject of the simplicial object obtained from `U` by reversing the simplex indexing. -/
abbrev lowerFaceKernelSubobject (U : SimplicialObject A) (n : ℕ) :
    Subobject (U.obj (op ⦋n⦌)) :=
  NormalizedMooreComplex.objX (opFunctor.obj U) n

@[simp] theorem lowerFaceKernelSubobject_zero (U : SimplicialObject A) :
    U.lowerFaceKernelSubobject 0 = ⊤ :=
  rfl

@[simp] theorem lowerFaceKernelSubobject_add_one (U : SimplicialObject A) (n : ℕ) :
    U.lowerFaceKernelSubobject (n + 1) =
      Finset.univ.inf (fun k : Fin (n + 1) ↦ kernelSubobject (U.δ (Fin.castSucc k))) := by
  change NormalizedMooreComplex.objX (opFunctor.obj U) (n + 1) = _
  rw [NormalizedMooreComplex.objX_add_one]
  let g : Fin (n + 1) → Subobject (U.obj (op ⦋n + 1⦌)) :=
    fun k ↦ kernelSubobject (U.δ (Fin.castSucc k))
  let e : Fin (n + 1) ≃ Fin (n + 1) :=
    { toFun := Fin.rev
      invFun := Fin.rev
      left_inv := Fin.rev_rev
      right_inv := Fin.rev_rev }
  calc
    Finset.univ.inf
      (fun k : Fin (n + 1) ↦
        kernelSubobject ((opFunctor.obj U).δ k.succ))
      = Finset.univ.inf (fun k : Fin (n + 1) ↦ kernelSubobject (U.δ k.rev.castSucc)) := by
          refine congrArg
            (fun f : Fin (n + 1) → Subobject (U.obj (op ⦋n + 1⦌)) ↦ Finset.univ.inf f) ?_
          funext k
          rw [opFunctor_obj_δ, Fin.rev_succ]
          congr 1
          change
            𝟙 (U.obj (op ⦋n + 1⦌)) ≫ U.δ k.rev.castSucc ≫ 𝟙 (U.obj (op ⦋n⦌)) =
              U.δ k.rev.castSucc
          simp
    _ = (Finset.image (fun k : Fin (n + 1) ↦ k.rev) Finset.univ).inf g := by
          symm
          exact Finset.inf_image Finset.univ (fun k : Fin (n + 1) ↦ k.rev) g
    _ = Finset.univ.inf g := by
          simpa [g, e] using
            congrArg (fun s : Finset (Fin (n + 1)) ↦ s.inf g) (Finset.image_univ_equiv e)
    _ = Finset.univ.inf (fun k : Fin (n + 1) ↦ kernelSubobject (U.δ (Fin.castSucc k))) := by
          rfl

end SimplicialObject

/- Forgetting the canonical normalized-Moore splitting recovers the original simplicial object.
This is the Dold-Kan unit isomorphism rewritten through the split owner `Γ₀'`. -/
#check
  ((Functor.associator N DoldKan.Γ₀' (SimplicialObject.Split.forget A)).symm ≪≫
    (equivalence).unitIso.symm :
      (N ⋙ DoldKan.Γ₀') ⋙ SimplicialObject.Split.forget A ≅ 𝟭 (SimplicialObject A))

/- The nondegenerate degree-`n` term of the canonical normalized-Moore splitting is, by
definition, the normalized Moore subobject `NormalizedMooreComplex.objX U n`. -/
#check
  (fun (U : SimplicialObject A) (n : ℕ) ↦
    (rfl :
      ((N ⋙ DoldKan.Γ₀').obj U).s.N n = (NormalizedMooreComplex.objX U n : A)))

end CategoryTheory
