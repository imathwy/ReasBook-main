import StacksProject_2024.Chap20.Lemma_20_12_3
import StacksProject_2024.Chap06.Definition_6_7_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

variable {X : TopCat.{u}}

variable [IrreducibleSpace X]

local notation "JX" => Opens.grothendieckTopology X

/- Domain-style sampling for Lemma 20.20.2:
- primary domain: constant abelian sheaves on a topological space, their locally constant sections,
  flasqueness, and higher sheaf cohomology;
- sampled owner declarations:
  `constantSheaf`,
  `TopCat.Sheaf.IsFlasque`,
  `Sheaf.H'`,
  `constantSheafToLocallyConstantSheaf`;
- best owner abstraction: the sheaf itself should remain the canonical owner
  `((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A)`, with flasqueness and
  higher cohomology expressed by the owner predicates `TopCat.Sheaf.IsFlasque` and `H'`;
- primitive data: only the irreducible space `X` and the coefficient group `A`;
- derived API: flasqueness of the constant sheaf and vanishing of its positive cohomology.

Source/core/bridge triage:
- `source-facing`: the vanishing of higher cohomology for the constant abelian sheaf on an
  irreducible space;
- `core/canonical`: `constantSheaf`, `TopCat.Sheaf.IsFlasque`, and `Sheaf.H'`;
- `bridge/view`: `constantSheafToLocallyConstantSheaf`, which identifies the constant sheaf with
  the sheaf of locally constant functions from Definition `6.7.4`.

This file should therefore use the canonical `constantSheaf` owner vocabulary directly rather than
keeping public theorem names branded by a parallel "constant abelian sheaf" wrapper phrasing.
-/

-- Proof sketch: by Definition `6.7.4`, sections of the constant sheaf over an open `U` are the
-- locally constant maps `U → A`. Every nonempty open subset of an irreducible space is again
-- irreducible, hence connected, so such a section is determined by any one of its values and is
-- therefore constant. Restriction maps are then surjective, which is exactly flasqueness.
/-- Helper for Lemma 20.20.2: every nonempty open subspace of an irreducible space is itself
irreducible. -/
private theorem irreducibleSpaceOfOpenNeBot (U : Opens X) (hU : U ≠ ⊥) :
    IrreducibleSpace U := by
  -- Restrict the ambient irreducible set `Set.univ` to the open subset `U`.
  refine Subtype.irreducibleSpace ?_
  refine ⟨U.ne_bot_iff_nonempty.mp hU, ?_⟩
  simpa [Set.inter_univ] using
    (IrreducibleSpace.isIrreducible_univ X).isPreirreducible.open_subset U.2 (by simp)

/-- Helper for Lemma 20.20.2: a commuting square of equivalences transports surjectivity. -/
private theorem surjective_of_equiv_transport
    {α β α' β' : Type*} (eα : α ≃ α') (eβ : β ≃ β')
    (f : α → β) (g : α' → β')
    (hcomm : ∀ a, eβ (f a) = g (eα a))
    (hg : Function.Surjective g) :
    Function.Surjective f := by
  intro b
  obtain ⟨a', ha'⟩ := hg (eβ b)
  refine ⟨eα.symm a', ?_⟩
  apply eβ.injective
  simpa [ha'] using hcomm (eα.symm a')

/-- Helper for Lemma 20.20.2: restriction maps of the locally constant sheaf are surjective on
an irreducible space. -/
private theorem locallyConstantSheafRestriction_surjective_of_irreducible
    (A : AddCommGrpCat.{u}) {U V : Opens X} (i : U ⟶ V) :
    Function.Surjective ((locallyConstantSheaf X A).1.map i.op) := by
  intro s
  by_cases hU : U = ⊥
  · subst hU
    refine ⟨⟨fun x ↦ 0, IsLocallyConstant.const 0⟩, ?_⟩
    apply Subtype.ext
    funext x
    exact False.elim x.2
  · have hU_irred : IrreducibleSpace U := irreducibleSpaceOfOpenNeBot (X := X) U hU
    obtain ⟨x0, hx0⟩ := U.ne_bot_iff_nonempty.mp hU
    let a : A := s.1 ⟨x0, hx0⟩
    refine ⟨⟨fun _ ↦ a, IsLocallyConstant.const a⟩, ?_⟩
    apply Subtype.ext
    funext x
    change a = s.1 x
    have ha : s.1 x = s.1 ⟨x0, hx0⟩ :=
      s.2.apply_eq_of_preconnectedSpace x ⟨x0, hx0⟩
    simpa [a] using ha.symm

/-- Helper for Lemma 20.20.2: restriction maps of the constant sheaf are surjective on an
irreducible space. -/
private theorem constantSheafRestriction_surjective_of_irreducible
    [HasWeakSheafify JX AddCommGrpCat.{u}]
    (A : AddCommGrpCat.{u}) {U V : Opens X} (i : U ⟶ V) :
    Function.Surjective (((constantSheaf JX AddCommGrpCat.{u}).obj A).1.map i.op) := by
  let E := constantCommuteCompose JX (forget AddCommGrpCat.{u})
  let eForgetU :
      (((CategoryTheory.sheafForget JX).obj
          ((constantSheaf JX AddCommGrpCat.{u}).obj A)).1.obj (Opposite.op U)) ≅
        (((constantSheaf JX (Type u)).obj A).1.obj (Opposite.op U)) :=
    ((sheafToPresheaf JX (Type u)).mapIso (E.app A)).app (Opposite.op U)
  let eForgetV :
      (((CategoryTheory.sheafForget JX).obj
          ((constantSheaf JX AddCommGrpCat.{u}).obj A)).1.obj (Opposite.op V)) ≅
        (((constantSheaf JX (Type u)).obj A).1.obj (Opposite.op V)) :=
    ((sheafToPresheaf JX (Type u)).mapIso (E.app A)).app (Opposite.op V)
  let eForgetU' :
      (((constantSheaf JX AddCommGrpCat.{u}).obj A).1.obj (Opposite.op U)) ≃
        (((constantSheaf JX (Type u)).obj A).1.obj (Opposite.op U)) := by
    simpa [CategoryTheory.sheafForget, TopCat.Sheaf.forget] using eForgetU.toEquiv
  let eForgetV' :
      (((constantSheaf JX AddCommGrpCat.{u}).obj A).1.obj (Opposite.op V)) ≃
        (((constantSheaf JX (Type u)).obj A).1.obj (Opposite.op V)) := by
    simpa [CategoryTheory.sheafForget, TopCat.Sheaf.forget] using eForgetV.toEquiv
  let eTypeU :
      (((constantSheaf JX (Type u)).obj A).1.obj (Opposite.op U)) ≃
        ((locallyConstantSheaf X A).1.obj (Opposite.op U)) := by
    letI := constantSheafToLocallyConstantSheaf_app_isIso X A U
    exact (asIso ((constantSheafToLocallyConstantSheaf X A).hom.app (Opposite.op U))).toEquiv
  let eTypeV :
      (((constantSheaf JX (Type u)).obj A).1.obj (Opposite.op V)) ≃
        ((locallyConstantSheaf X A).1.obj (Opposite.op V)) := by
    letI := constantSheafToLocallyConstantSheaf_app_isIso X A V
    exact (asIso ((constantSheafToLocallyConstantSheaf X A).hom.app (Opposite.op V))).toEquiv
  let eU :
      (((constantSheaf JX AddCommGrpCat.{u}).obj A).1.obj (Opposite.op U)) ≃
        ((locallyConstantSheaf X A).1.obj (Opposite.op U)) :=
    eForgetU'.trans eTypeU
  let eV :
      (((constantSheaf JX AddCommGrpCat.{u}).obj A).1.obj (Opposite.op V)) ≃
        ((locallyConstantSheaf X A).1.obj (Opposite.op V)) :=
    eForgetV'.trans eTypeV
  have hForget :
      ∀ t : ((constantSheaf JX AddCommGrpCat.{u}).obj A).1.obj (Opposite.op V),
        eForgetU' ((((constantSheaf JX AddCommGrpCat.{u}).obj A).1.map i.op) t) =
          (((constantSheaf JX (Type u)).obj A).1.map i.op) (eForgetV' t) := by
    intro t
    simpa [eForgetU, eForgetV, eForgetU', eForgetV', CategoryTheory.sheafForget,
      TopCat.Sheaf.forget] using
      congrFun (((sheafToPresheaf JX (Type u)).mapIso (E.app A)).hom.naturality i.op) t
  have hType :
      ∀ t : ((constantSheaf JX (Type u)).obj A).1.obj (Opposite.op V),
        eTypeU ((((constantSheaf JX (Type u)).obj A).1.map i.op) t) =
          ((locallyConstantSheaf X A).1.map i.op) (eTypeV t) := by
    intro t
    change
      ((constantSheafToLocallyConstantSheaf X A).hom.app (Opposite.op U))
          ((((constantSheaf JX (Type u)).obj A).1.map i.op) t) =
        ((locallyConstantSheaf X A).1.map i.op)
          (((constantSheafToLocallyConstantSheaf X A).hom.app (Opposite.op V)) t)
    exact congrFun ((constantSheafToLocallyConstantSheaf X A).hom.naturality i.op) t
  have hcomm :
      ∀ t : ((constantSheaf JX AddCommGrpCat.{u}).obj A).1.obj (Opposite.op V),
        eU ((((constantSheaf JX AddCommGrpCat.{u}).obj A).1.map i.op) t) =
          ((locallyConstantSheaf X A).1.map i.op) (eV t) := by
    intro t
    change
      eTypeU (eForgetU' ((((constantSheaf JX AddCommGrpCat.{u}).obj A).1.map i.op) t)) =
        ((locallyConstantSheaf X A).1.map i.op) (eTypeV (eForgetV' t))
    rw [hForget t]
    exact hType (eForgetV' t)
  exact surjective_of_equiv_transport eV eU
    (((constantSheaf JX AddCommGrpCat.{u}).obj A).1.map i.op)
    ((locallyConstantSheaf X A).1.map i.op)
    hcomm
    (locallyConstantSheafRestriction_surjective_of_irreducible (X := X) A i)

/-- Helper for Lemma 20.20.2: the constant `AddCommGrpCat` sheaf on an irreducible space is
flasque. -/
private theorem constantSheaf_isFlasque_of_irreducible
    [HasWeakSheafify JX AddCommGrpCat.{u}]
    (A : AddCommGrpCat.{u}) :
    TopCat.Sheaf.IsFlasque ((constantSheaf JX AddCommGrpCat.{u}).obj A) := by
  refine ⟨fun {U V} i ↦ ?_⟩
  -- Flasqueness is exactly surjectivity of each restriction map in `AddCommGrpCat`.
  rw [AddCommGrpCat.epi_iff_surjective]
  exact constantSheafRestriction_surjective_of_irreducible
    (X := X) (U := V.unop) (V := U.unop) A i.unop

-- Proof sketch: the previous theorem makes the constant abelian sheaf with value `A` flasque on
-- an irreducible space. Flasque sheaves are acyclic for global sections by Lemma `20.12.3`, so
-- the positive-degree global cohomology objects of `((constantSheaf JX AddCommGrpCat.{u}).obj A)`
-- vanish.
/-- Lemma 20.20.2: if `X` is irreducible, then the higher cohomology of the constant abelian
sheaf with value `A` vanishes in every positive degree. -/
@[stacks 02UW]
theorem isZero_higherCohomology_constantSheaf_of_irreducible
    [HasSheafify JX AddCommGrpCat.{u}]
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]
    (A : AddCommGrpCat.{u}) {p : ℕ} (hp : 0 < p) :
    IsZero (((constantSheaf JX AddCommGrpCat.{u}).obj A).H' p (⊤ : Opens X)) := by
  simpa using higherCohomology_isZero_of_isFlasque
    ((constantSheaf JX AddCommGrpCat.{u}).obj A)
    (constantSheaf_isFlasque_of_irreducible A)
    (⊤ : Opens X) p hp

end Sheaf
end CategoryTheory
