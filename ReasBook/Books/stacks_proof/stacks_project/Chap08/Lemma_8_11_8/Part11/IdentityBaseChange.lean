import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.Part11.IdentityBaseChangePointCore

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

theorem automorphismUnderlyingSheaf_identity_baseChange_eq_conj_pullbackId_part11
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} (x : 𝒮.p.Fiber U) :
    ((J.pseudofunctorOver (Type (max u v))).mapId
        (LocallyDiscrete.mk (op U))).inv.toNatTrans.app
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x) ≫
    (automorphismUnderlyingSheafBaseChangeIso
      (𝒮 := 𝒮) hAbelian (𝟙 U) x).hom =
      (automorphismUnderlyingSheafConj
      (𝒮 := 𝒮) hAbelian
      ((canonicalPullbackChoice 𝒮.p).pullbackIdComponentIso U x).hom).hom := by
  apply Sheaf.hom_ext
  ext T α
  exact automorphismUnderlyingSheaf_identity_baseChange_point_core
    (𝒮 := 𝒮) hAbelian x T α

end CategoryTheory
