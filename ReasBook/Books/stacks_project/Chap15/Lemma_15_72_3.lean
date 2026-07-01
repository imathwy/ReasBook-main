import Mathlib.Algebra.Homology.Monoidal
import stacks_project.Chap15.Lemma_15_72_1

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open MonoidalClosed
open scoped ModuleComplexInternalHom

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]

local notation "CpxR" => CochainComplex (ModuleCat R) ℤ
local notation:70 A " ⊗ " B => tensorObj A B

/- Domain-style sampling for 15.72.3:
- primary domain: the source-facing composition morphism on the Chapter 15 internal-Hom complexes
  `⟪-, -⟫` of cochain complexes of `R`-modules;
- sampled owner declarations:
  `module_complex_internal_hom`,
  `module_complex_internal_hom_piIso`,
  `module_complex_internal_hom_piProj`,
  `HomologicalComplex.mapBifunctorDesc`,
  `MonoidalClosed.comp`;
- best owner abstraction: the public owner remains the chapter internal-Hom complex `⟪-, -⟫`;
  the ambient module-level closed-monoidal composition `MonoidalClosed.comp` supplies only the
  degreewise composition maps used to build the chain map;
- primitive data vs. derived API: the primitive owner data are the complexes `⟪K, L⟫` and their
  canonical degree decompositions `module_complex_internal_hom_piIso`; the projection maps
  `module_complex_internal_hom_piProj` and the composition morphism
  `⟪L, M⟫ ⊗ ⟪K, L⟫ ⟶ ⟪K, M⟫` are derived bridge API;
- source/core/bridge triage:
  `source-facing`: `module_complex_internal_hom_comp`;
  `core/canonical`: `module_complex_internal_hom`, `module_complex_internal_hom_piIso`,
    `HomologicalComplex.tensorObj`, `HomologicalComplex.mapBifunctorDesc`, and the degreewise
    module-level `MonoidalClosed.comp`;
  `bridge/view`: the product projections `module_complex_internal_hom_piProj` together with the
    index-transport map on the target degree.
-/

/-- Reindexing the target degree in the internal-Hom composition map. -/
private theorem module_complex_internal_hom_comp_indexEq
    {t r n p : ℤ} (h : t + r = n) :
    t + (r + p) = n + p := by
  omega

section

open MonoidalCategory

/-- The summandwise composition map contributing to the degree-`n` component of
`⟪L, M⟫ ⊗ ⟪K, L⟫ ⟶ ⟪K, M⟫`. -/
noncomputable def module_complex_internal_hom_comp_component
    (K L M : CpxR) (t r n p : ℤ) (h : t + r = n) :
    ((⟪L, M⟫).X t ⊗ (⟪K, L⟫).X r) ⟶
      (ihom (K.X p)).obj (M.X (n + p)) :=
  ((module_complex_internal_hom_piProj L M t (r + p)) ⊗ₘ
      (module_complex_internal_hom_piProj K L r p)) ≫
    (β_ ((ihom (L.X (r + p))).obj (M.X (t + (r + p))))
      ((ihom (K.X p)).obj (L.X (r + p)))).hom ≫
    MonoidalClosed.comp (K.X p) (L.X (r + p)) (M.X (t + (r + p))) ≫
    (ihom (K.X p)).map
      (eqToHom (congrArg (fun z : ℤ ↦ M.X z)
        (module_complex_internal_hom_comp_indexEq h)))

end

/-- The degree-`n` component of the composition morphism on the chapter internal-Hom complexes. -/
private noncomputable def module_complex_internal_hom_comp_f
    (K L M : CpxR) [HasTensor (⟪L, M⟫) (⟪K, L⟫)] (n : ℤ) :
    (⟪L, M⟫ ⊗ ⟪K, L⟫).X n ⟶ (⟪K, M⟫).X n :=
  let desc :
      (⟪L, M⟫ ⊗ ⟪K, L⟫).X n ⟶
        ∏ᶜ fun p : ℤ ↦ (ihom (K.X p)).obj (M.X (n + p)) :=
    mapBifunctorDesc fun t r h ↦
      Pi.lift fun p ↦
        module_complex_internal_hom_comp_component K L M t r n p h
  desc ≫ (module_complex_internal_hom_piIso K M n).hom

-- Proof sketch: project both sides to a tensor summand in degree `i` and then to a factor of the
-- target product decomposition. The source differential is the tensor differential on
-- `⟪L, M⟫ ⊗ ⟪K, L⟫`, while the target differential is the internal-Hom differential on `⟪K, M⟫`;
-- the component identities reduce to the sign conventions in the Hom-complex differential.
/-- Lemma 15.72.3: the chapter internal-Hom complexes admit the canonical composition morphism
`⟪L, M⟫ ⊗ ⟪K, L⟫ ⟶ ⟪K, M⟫`. -/
noncomputable def module_complex_internal_hom_comp
    (K L M : CpxR) [HasTensor (⟪L, M⟫) (⟪K, L⟫)] :
    (⟪L, M⟫ ⊗ ⟪K, L⟫) ⟶ ⟪K, M⟫ :=
  { f := module_complex_internal_hom_comp_f K L M
    comm' := by
      sorry }

end
