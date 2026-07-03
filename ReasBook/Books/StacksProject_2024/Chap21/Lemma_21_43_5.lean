import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.ObjectProperty

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory.ModulesOnCategory

section

variable {D : Type v} [Category D]
variable (QC : ObjectProperty D)
variable {DU : Type u} [Category DU]

/-- Lemma 21.43.5: for a fixed localized site over `U`, if `K` is quasi-coherent and the counit
identifies `K|_U` with `Lf^*(R\Gamma(U, K))`, then morphisms `K|_U ⟶ M|_U` are canonically
equivalent to morphisms `R\Gamma(U, K) ⟶ R\Gamma(U, M)` via the adjunction `Lf ⊣ R\Gamma(U,-)`. -/
noncomputable abbrev quasiCoherent_homEquiv_sections
    (RGammaU : D ⥤ DU)
    (Lf : DU ⥤ D)
    (adj : Lf ⊣ RGammaU)
    (K : QC.FullSubcategory)
    (M : D)
    [IsIso (adj.counit.app K.obj)] :
    (K.obj ⟶ M) ≃ (RGammaU.obj K.obj ⟶ RGammaU.obj M) :=
  (Iso.homCongr (asIso (adj.counit.app K.obj)).symm (Iso.refl M)).trans
    (adj.homEquiv (RGammaU.obj K.obj) M)

-- Proof sketch: use the counit isomorphism to replace `K` by `Lf.obj (RΓ(U,K))`, then apply the
-- adjunction Hom-set equivalence for `Lf ⊣ RΓ(U,-)`.
/-- The Hom-set equivalence of `quasiCoherent_homEquiv_sections` is the composite of the counit
comparison isomorphism with `Adjunction.homEquiv`. -/
theorem quasiCoherent_homEquiv_sections_def
    (RGammaU : D ⥤ DU)
    (Lf : DU ⥤ D)
    (adj : Lf ⊣ RGammaU)
    (K : QC.FullSubcategory)
    (M : D)
    [IsIso (adj.counit.app K.obj)] :
    quasiCoherent_homEquiv_sections QC RGammaU Lf adj K M =
      (Iso.homCongr (asIso (adj.counit.app K.obj)).symm (Iso.refl M)).trans
        (adj.homEquiv (RGammaU.obj K.obj) M) := sorry

end

end CategoryTheory.ModulesOnCategory
