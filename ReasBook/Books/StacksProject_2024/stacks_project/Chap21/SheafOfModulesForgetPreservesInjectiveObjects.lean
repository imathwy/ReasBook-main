import StacksProject_2024.stacks_project.Chap12.Lemma_12_29_1

noncomputable section

universe u

namespace CategoryTheory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J RingCat.{u}}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restricting scalars along the identity ring-sheaf map is naturally isomorphic to the identity
on presheaf modules. -/
private def restrictScalarsIdIso
    (F : PresheafOfModules.{u} 𝒪.obj) :
    (PresheafOfModules.restrictScalars.{u} (𝟙 𝒪.obj)).obj F ≅ F :=
  PresheafOfModules.isoMk
    (fun U ↦ by
      simpa using
        (ModuleCat.restrictScalarsId'App
          (((𝟙 𝒪.obj : 𝒪.obj ⟶ 𝒪.obj).app U).hom)
          rfl
          (F.obj U)))
    (fun {U V} i ↦ by
      ext x
      rfl)

/-- Shared Chapter 21 support instance: the forgetful functor from sheaves of `𝒪`-modules to
presheaves of `𝒪`-modules preserves injective objects. -/
instance sheafOfModulesForgetPreservesInjectiveObjects :
    (SheafOfModules.forget.{u} 𝒪).PreservesInjectiveObjects where
  injective_obj {F} hF := by
    letI : HasSheafify J AddCommGrpCat.{u} := inferInstance
    let G : SheafOfModules.{u} 𝒪 ⥤ PresheafOfModules.{u} 𝒪.obj :=
      SheafOfModules.forget.{u} 𝒪 ⋙ PresheafOfModules.restrictScalars.{u} (𝟙 𝒪.obj)
    let hExact :
        exactFunctor _ _ (PresheafOfModules.sheafification (𝟙 𝒪.obj)) :=
      (exactFunctor_iff (PresheafOfModules.sheafification (𝟙 𝒪.obj))).2
        ⟨inferInstance, inferInstance⟩
    letI : G.PreservesInjectiveObjects :=
      preservesInjectiveObjects_of_exact_leftAdjoint
        (PresheafOfModules.sheafificationAdjunction (𝟙 𝒪.obj)) hExact
    exact Injective.of_iso
      (restrictScalarsIdIso ((SheafOfModules.forget.{u} 𝒪).obj F))
      (G.injective_obj_of_injective hF)

end CategoryTheory
