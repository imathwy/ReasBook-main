import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap14.Lemma_14_18_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Abelian.DoldKan
open scoped Simplicial

noncomputable section

namespace CategoryTheory

/- Domain-style sampling for Lemma 14.18.5:
- primary domain: split simplicial objects in simplicial abelian groups
- sampled owner API:
  `Abelian.DoldKan.N ⋙ DoldKan.Γ₀'`,
  `Abelian.DoldKan.equivalence.unitIso`,
  `SimplicialObject.Splitting`,
  `SimplicialObject.Split`,
  `NormalizedMooreComplex.objX`,
  `NormalizedMooreComplex.objX_zero`,
  `NormalizedMooreComplex.objX_add_one`
- best owner abstraction: the normalized Moore subobject
  `NormalizedMooreComplex.objX U n` together with the canonical functor
  `Abelian.DoldKan.N ⋙ DoldKan.Γ₀'`
- primitive data: `NormalizedMooreComplex.objX U n` and the canonical split owner
  `Abelian.DoldKan.N ⋙ DoldKan.Γ₀'`
- derived API: the successor-degree kernel-intersection formula, the forgetful comparison
  with the Dold-Kan unit isomorphism, and the degreewise identification coming from the
  definition of `Γ₀'`
- source/core/bridge triage: this file is `bridge/view`; Lemma 14.18.5 is the
  `AddCommGrpCat` specialization of the generic owner declarations in Lemma 14.18.6, so the
  correct refinement is direct specialized reuse of those declarations rather than a parallel
  specialized API.
-/

/- Companion check: simplicial abelian groups inherit the canonical normalized-Moore split
functor from the generic abelian-category owner in Lemma 14.18.6. -/
#check (N ⋙ DoldKan.Γ₀' :
  SimplicialObject AddCommGrpCat ⥤ SimplicialObject.Split AddCommGrpCat)

/- Companion recall: forgetting the canonical normalized-Moore split functor gives back the
underlying simplicial abelian group. -/
#check
  (((Functor.associator N DoldKan.Γ₀' (SimplicialObject.Split.forget AddCommGrpCat)).symm ≪≫
      (equivalence).unitIso.symm) :
    (N ⋙ DoldKan.Γ₀' : SimplicialObject AddCommGrpCat ⥤ SimplicialObject.Split AddCommGrpCat) ⋙
        SimplicialObject.Split.forget AddCommGrpCat ≅
      𝟭 (SimplicialObject AddCommGrpCat))

/- Companion recall: the degree-`n` nondegenerate term of the canonical split object is the
normalized Moore subobject. -/
#check
  (fun (U : SimplicialObject AddCommGrpCat) (n : ℕ) ↦
    (rfl :
      ((N ⋙ DoldKan.Γ₀').obj U).s.N n = (NormalizedMooreComplex.objX U n : AddCommGrpCat)))

/- Companion recall: for a simplicial abelian group, the normalized Moore subobject is the generic
abelian-category owner specialized to `AddCommGrpCat`. -/
recall NormalizedMooreComplex.objX

#check
  (NormalizedMooreComplex.objX :
    ∀ U : SimplicialObject AddCommGrpCat, ∀ n : ℕ, Subobject (U.obj (op ⦋n⦌)))

/- Companion recall: in degree `0`, the normalized Moore subobject is all of `U₀`. -/
recall NormalizedMooreComplex.objX_zero

#check
  (NormalizedMooreComplex.objX_zero :
    ∀ U : SimplicialObject AddCommGrpCat, NormalizedMooreComplex.objX U 0 = ⊤)

/- Companion recall: in positive degree, the normalized Moore subobject is the intersection of the
kernels of the face maps `d₁, \dotsc, d_{n+1}`. -/
recall NormalizedMooreComplex.objX_add_one

#check
  (NormalizedMooreComplex.objX_add_one :
    ∀ U : SimplicialObject AddCommGrpCat, ∀ n : ℕ,
      NormalizedMooreComplex.objX U (n + 1) =
        Finset.univ.inf (fun k : Fin (n + 1) ↦ kernelSubobject (U.δ k.succ)))

/- Lemma 14.18.5: simplicial abelian groups admit the functorial normalized-Moore splitting.
In the generic abelian-category owner file, this content is already exposed directly by the
canonical split functor `N ⋙ DoldKan.Γ₀'`, the Dold-Kan unit isomorphism rewritten through
`Γ₀' ⋙ SimplicialObject.Split.forget`, and the definitional identification of the nondegenerate
degree-`n` term with `NormalizedMooreComplex.objX U n`. -/

end CategoryTheory
