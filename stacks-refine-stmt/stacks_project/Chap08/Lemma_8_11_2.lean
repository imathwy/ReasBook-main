import Mathlib
import stacks_project.Chap04.Lemma_4_35_9
import stacks_project.Chap08.Lemma_8_2_3
import stacks_project.Chap08.Definition_8_5_5
import stacks_project.Chap08.Definition_8_11_1
import stacks_project.Chap08.Lemma_8_5_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open BasedFunctor
open Functor
open Functor IsStronglyCartesian
open StackInGroupoidsOver.Hom

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮₁ 𝒮₂ : StackInGroupoidsOver J}

/- Domain-style sampling for Lemma 8.11.2:
- primary domain: stacks in groupoids over a site, gerbes, and equivalences in `Cat/C`;
- inspected owner-level declarations:
  `IsGerbe`,
  `StackInGroupoidsOver`,
  `FibredInGroupoidsMor.IsEquivalenceOverBase`,
  `isStackInGroupoids_iff_of_equivalence_over_base`,
  `BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase`;
- best owner abstraction: the source-facing gerbe predicate `IsGerbe J p`, transported along the
  owner morphism `F : 𝒮₁ ⟶ 𝒮₂` in `StackInGroupoidsOver J` rather than a parallel raw
  based-functor API;
- primitive data: the gerbe fields `locally_inhabited` and `locally_isomorphic` together with the
  over-base equivalence datum on the owner morphism;
- derived API: transport of those owner fields along the induced fibre equivalences and the
  `iff` statement below.

Source/core/bridge triage:
- `source-facing`: `IsGerbe J p`;
- `core/canonical`: `StackInGroupoidsOver J`, `StackInGroupoidsOver.Hom.IsEquivalenceOverBase`,
  `IsStackInGroupoids`,
  `FibredInGroupoidsMor.IsEquivalenceOverBase`, fibre functors, chosen pullback functors, and
  `FibredCategoryMor.pullbackComparison`;
- `bridge/view`: the equivalence-invariant restatement
  `IsGerbe J 𝒮₁.p ↔ IsGerbe J 𝒮₂.p`. -/

theorem isGerbe_of_equivalence_over_base
    (F : 𝒮₁ ⟶ 𝒮₂)
    (hF : F.IsEquivalenceOverBase)
    (h₁ : IsGerbe J 𝒮₁.p) :
    IsGerbe J 𝒮₂.p := by
  let hstack : IsStackInGroupoids J 𝒮₂.p :=
    (isStackInGroupoids_iff_of_equivalence_over_base J 𝒮₁.p 𝒮₂.p F.toBasedFunctor hF).1
      h₁.toIsStackInGroupoids
  refine
    { toIsStackInGroupoids := hstack
      locally_inhabited := ?_
      locally_isomorphic := ?_ }
  · intro U
    obtain ⟨S, hS⟩ := h₁.locally_inhabited U
    refine ⟨S, fun I ↦ ?_⟩
    obtain ⟨x⟩ := hS I
    exact ⟨(F.fiberFunctor I.Y).obj x⟩
  · intro U x y
    let F' := F.toFibredCategoryMor
    let fiberU := F.fiberFunctor U
    letI : fiberU.IsEquivalence :=
      fiberFunctor_isEquivalence_of_isEquivalenceOverBase F.toBasedFunctor hF U
    let eU := fiberU.asEquivalence
    let x₁ : 𝒮₁.p.Fiber U := eU.inverse.obj x
    let y₁ : 𝒮₁.p.Fiber U := eU.inverse.obj y
    let εx : fiberU.obj x₁ ≅ x := eU.counitIso.app x
    let εy : fiberU.obj y₁ ≅ y := eU.counitIso.app y
    obtain ⟨S, hS⟩ := h₁.locally_isomorphic x₁ y₁
    refine ⟨S, fun I ↦ ?_⟩
    let fiberI := F.fiberFunctor I.Y
    letI : fiberI.IsEquivalence :=
      fiberFunctor_isEquivalence_of_isEquivalenceOverBase F.toBasedFunctor hF I.Y
    let hc₂ := canonicalPullbackChoice 𝒮₂.p
    obtain ⟨α⟩ := hS I
    exact
      ⟨(hc₂.pullbackFunctor I.f).mapIso εx.symm ≪≫
        FibredCategoryMor.pullbackComparison F' I.f x₁ ≪≫
        fiberI.mapIso α ≪≫
        (FibredCategoryMor.pullbackComparison F' I.f y₁).symm ≪≫
        (hc₂.pullbackFunctor I.f).mapIso εy⟩

-- Proof sketch: transport the stack-in-groupoids structure across the equivalence by Lemma
-- `8.5.4`. For local nonemptiness, apply the functor on each fiber to local objects of `𝒮₁`.
-- For local isomorphism, apply a quasi-inverse on fibers, use the gerbe condition in `𝒮₁`, and
-- then transfer the resulting fiberwise isomorphisms back along the equivalence using Lemma
-- `4.35.9`.
/-- Lemma 8.11.2: if `𝒮₁` and `𝒮₂` are equivalent as categories over `C`, then `𝒮₁` is a gerbe
over `(C, J)` if and only if `𝒮₂` is a gerbe over `(C, J)`. -/
theorem isGerbe_iff_of_equivalence_over_base
    (F : 𝒮₁ ⟶ 𝒮₂)
    (hF : F.IsEquivalenceOverBase) :
    IsGerbe J 𝒮₁.p ↔ IsGerbe J 𝒮₂.p := by
  constructor
  · exact isGerbe_of_equivalence_over_base F hF
  · intro h₂
    let e : EquivalenceOverBase F.toBasedFunctor := Classical.choice hF.nonempty
    let G : 𝒮₂ ⟶ 𝒮₁ := ofBasedFunctor e.inverse
    have hG : G.IsEquivalenceOverBase := e.inverse_isEquivalenceOverBase
    simpa [G] using isGerbe_of_equivalence_over_base G hG h₂

end

end CategoryTheory
