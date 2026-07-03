import Mathlib

open CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {DModX DModX' DModZ DModZ' : Type u}
variable [Category DModX] [Category DModX'] [Category DModZ] [Category DModZ']

-- Proof sketch: the source object lies in the supported full subcategory by `hsource`.
-- The adjunction `supportedProperty.ι ⊣ supportedRightAdjoint` therefore identifies morphisms
-- from this supported source to `pullbackDerived.obj K` with morphisms from the same source to
-- `supportedRightAdjoint.obj (pullbackDerived.obj K)`. Transport the resulting unique factor
-- across `supportedRightAdjointAmbientIso`, and then across the base-change isomorphism
-- `baseChangeIso`, to obtain the desired unique morphism on the closed subsets.
/-- Remark 20.34.12: suppose `i_* : D(\mathcal O_X|_Z) ⥤ D(\mathcal O_X)` is left adjoint to
`R\mathcal H_Z`, suppose `D_{Z'}(\mathcal O_{X'})` is realized as a full subcategory of
`D(\mathcal O_{X'})` whose right adjoint is identified with
`i'_* \circ R\mathcal H_{Z'}`, and suppose the usual base-change isomorphism
`Lf^* \circ i_* \cong i'_* \circ L(f|_{Z'})^*` has been fixed. Then for every `K`, once
`Lf^*(i_*R\mathcal H_Z(K))` is known to lie in `D_{Z'}(\mathcal O_{X'})`, there is a unique
morphism `L(f|_{Z'})^*R\mathcal H_Z(K) ⟶ R\mathcal H_{Z'}(Lf^*K)` whose pushforward along `i'_*`
is the factorization of `Lf^*(i_*R\mathcal H_Z(K)) ⟶ Lf^*K` through the universal map
`i'_*R\mathcal H_{Z'}(Lf^*K) ⟶ Lf^*K`. -/
theorem existsUnique_closedSubsetPullback_sectionsWithSupportDerived_map
    (iPushforwardDerived : DModZ ⥤ DModX)
    (i'PushforwardDerived : DModZ' ⥤ DModX')
    (sectionsWithSupportDerived : DModX ⥤ DModZ)
    (sectionsWithSupportDerived' : DModX' ⥤ DModZ')
    (pullbackDerived : DModX ⥤ DModX')
    (restrictedPullbackDerived : DModZ ⥤ DModZ')
    (supportedProperty : ObjectProperty DModX')
    (supportedRightAdjoint : DModX' ⥤ supportedProperty.FullSubcategory)
    (baseChangeIso :
      iPushforwardDerived ⋙ pullbackDerived ≅
        restrictedPullbackDerived ⋙ i'PushforwardDerived)
    (adjZ : iPushforwardDerived ⊣ sectionsWithSupportDerived)
    (adjSupported : supportedProperty.ι ⊣ supportedRightAdjoint)
    (supportedRightAdjointAmbientIso :
      supportedRightAdjoint ⋙ supportedProperty.ι ≅
        sectionsWithSupportDerived' ⋙ i'PushforwardDerived)
    {K : DModX}
    (hsource :
      supportedProperty
        (pullbackDerived.obj
          (iPushforwardDerived.obj (sectionsWithSupportDerived.obj K)))) :
    ∃! τ :
        restrictedPullbackDerived.obj (sectionsWithSupportDerived.obj K) ⟶
          sectionsWithSupportDerived'.obj (pullbackDerived.obj K),
      baseChangeIso.hom.app (sectionsWithSupportDerived.obj K) ≫
          i'PushforwardDerived.map τ ≫
          supportedRightAdjointAmbientIso.inv.app (pullbackDerived.obj K) ≫
          adjSupported.counit.app (pullbackDerived.obj K) =
        pullbackDerived.map (adjZ.counit.app K) := sorry

end

end AlgebraicGeometry.RingedSpace
