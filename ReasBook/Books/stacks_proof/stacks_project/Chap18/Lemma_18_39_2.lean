import Mathlib
import stacks_proof.stacks_project.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable (p : GrothendieckTopology.Point J)
variable (ℱ : SheafOfModules (ringSheaf J 𝒪))

/-- The stalk functor on `\mathcal O`-modules at the point `p`, obtained by forgetting to sheaves
of abelian groups and then applying the point fiber functor. -/
abbrev point_stalk_functor :
    SheafOfModules (ringSheaf J 𝒪) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙ p.sheafFiber

/-- Tensoring on the right by `ℱ` and then taking the stalk at `p`. This is the categorical form
of tensoring with the stalk `ℱ_p`. -/
abbrev point_tensor_stalk_functor :
    SheafOfModules (ringSheaf J 𝒪) ⥤ AddCommGrpCat.{u} :=
  CategoryTheory.MonoidalCategory.tensorRight ℱ ⋙ point_stalk_functor 𝒪 p

/-- Flatness of `ℱ` at the point `p`, expressed as exactness of the tensor-then-stalk functor.
This packages the textbook statement that the stalk `ℱ_p` is flat over the stalk ring
`\mathcal O_p` in the available site-theoretic API. -/
def IsFlatAtPoint : Prop :=
  exactFunctor
    (SheafOfModules (ringSheaf J 𝒪))
    AddCommGrpCat.{u}
    (point_tensor_stalk_functor 𝒪 p ℱ)

omit [MonoidalCategory (ringedSiteModuleCategory J 𝒪)] in
/-- Helper for Lemma 18.39.2: the underlying additive stalk functor at `p` is exact. -/
private theorem pointStalkFunctor_exact :
    exactFunctor
      (SheafOfModules (ringSheaf J 𝒪))
      AddCommGrpCat.{u}
      (point_stalk_functor 𝒪 p) := by
  -- Proof comment: the additive stalk is the composite of the exact forgetful functor to
  -- sheaves of abelian groups and the exact point fiber functor.
  have hlim : PreservesFiniteLimits (point_stalk_functor 𝒪 p) := by
    have : PreservesFiniteLimits
        (SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙ p.sheafFiber) := by
      have hToSheaf :
          exactFunctor
            (SheafOfModules (ringSheaf J 𝒪))
            (Sheaf J AddCommGrpCat.{u})
            (SheafOfModules.toSheaf (ringSheaf J 𝒪)) :=
        (ExactFunctor.of (SheafOfModules.toSheaf (ringSheaf J 𝒪))).property
      have hFiber :
          exactFunctor
            (Sheaf J AddCommGrpCat.{u})
            AddCommGrpCat.{u}
            p.sheafFiber :=
        (ExactFunctor.of p.sheafFiber).property
      let _ : PreservesFiniteLimits (SheafOfModules.toSheaf (ringSheaf J 𝒪)) :=
        ((exactFunctor_iff (SheafOfModules.toSheaf (ringSheaf J 𝒪))).1 hToSheaf).1
      let _ : PreservesFiniteLimits p.sheafFiber :=
        ((exactFunctor_iff p.sheafFiber).1 hFiber).1
      infer_instance
    simpa [point_stalk_functor] using this
  have hcolim : PreservesFiniteColimits (point_stalk_functor 𝒪 p) := by
    have : PreservesFiniteColimits
        (SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙ p.sheafFiber) := by
      have hToSheaf :
          exactFunctor
            (SheafOfModules (ringSheaf J 𝒪))
            (Sheaf J AddCommGrpCat.{u})
            (SheafOfModules.toSheaf (ringSheaf J 𝒪)) :=
        (ExactFunctor.of (SheafOfModules.toSheaf (ringSheaf J 𝒪))).property
      have hFiber :
          exactFunctor
            (Sheaf J AddCommGrpCat.{u})
            AddCommGrpCat.{u}
            p.sheafFiber :=
        (ExactFunctor.of p.sheafFiber).property
      let _ : PreservesFiniteColimits (SheafOfModules.toSheaf (ringSheaf J 𝒪)) :=
        ((exactFunctor_iff (SheafOfModules.toSheaf (ringSheaf J 𝒪))).1 hToSheaf).2
      let _ : PreservesFiniteColimits p.sheafFiber :=
        ((exactFunctor_iff p.sheafFiber).1 hFiber).2
      infer_instance
    simpa [point_stalk_functor] using this
  exact (exactFunctor_iff (point_stalk_functor 𝒪 p)).2 ⟨hlim, hcolim⟩

-- Proof sketch: flatness of `ℱ` means tensoring with `ℱ` is exact on `\mathcal O`-modules. The
-- point fiber functor `p.sheafFiber` is exact on sheaves of abelian groups, so the composite
-- tensor-then-stalk functor is exact. This is the canonical categorical rendering of the
-- textbook claim that `ℱ_p` is a flat `\mathcal O_p`-module.
/-- Lemma 18.39.2: if `ℱ` is a flat `\mathcal O`-module on a ringed site and `p` is a point of
the site, then `ℱ` is flat at `p`, i.e. the stalkwise tensor functor at `p` is exact. This is
the canonical site-theoretic formulation of the statement that the stalk `ℱ_p` is a flat
`\mathcal O_p`-module. -/
@[stacks 05VB]
theorem isFlatAtPoint_of_isFlat [IsFlat 𝒪 ℱ] :
    IsFlatAtPoint 𝒪 p ℱ := by
  -- Proof comment: flatness gives exactness of tensoring by `ℱ`, and the previous helper gives
  -- exactness of taking the additive stalk at `p`; the target is their composite.
  have hTensor :
      exactFunctor
        (SheafOfModules (ringSheaf J 𝒪))
        (SheafOfModules (ringSheaf J 𝒪))
        (CategoryTheory.MonoidalCategory.tensorRight ℱ) :=
    IsFlat.exact_tensor (𝒪 := 𝒪) (ℱ := ℱ)
  have hStalk :
      exactFunctor
        (SheafOfModules (ringSheaf J 𝒪))
        AddCommGrpCat.{u}
        (point_stalk_functor 𝒪 p) :=
    pointStalkFunctor_exact (𝒪 := 𝒪) (p := p)
  rw [exactFunctor_iff] at hTensor hStalk
  let _ : PreservesFiniteLimits (CategoryTheory.MonoidalCategory.tensorRight ℱ) := hTensor.1
  let _ : PreservesFiniteColimits (CategoryTheory.MonoidalCategory.tensorRight ℱ) := hTensor.2
  let _ : PreservesFiniteLimits (point_stalk_functor 𝒪 p) := hStalk.1
  let _ : PreservesFiniteColimits (point_stalk_functor 𝒪 p) := hStalk.2
  have hComposite :
      exactFunctor
        (SheafOfModules (ringSheaf J 𝒪))
        AddCommGrpCat.{u}
        (point_tensor_stalk_functor 𝒪 p ℱ) := by
    -- Proof comment: once the two factors preserve finite limits and finite colimits, their
    -- composite does as well.
    exact (exactFunctor_iff (point_tensor_stalk_functor 𝒪 p ℱ)).2 ⟨inferInstance, inferInstance⟩
  simpa [IsFlatAtPoint] using hComposite
