import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap18.Lemma_18_14_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/- Domain-style sampling for Lemma 17.3.1:
- primary domain: exactness in the abelian category of `\mathcal O_X`-modules and detection of
  exactness by stalks of `\mathcal O_X`-modules;
- inspected owner declarations:
  `Mod`,
  `RingedSpace.stalkModuleCat`,
  `RingedSpace.moduleStalkHom`,
  `SheafOfModules.toSheaf`,
  `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact`,
  `Functor.reflects_exact_of_faithful`;
- best owner abstraction: the source-facing owner notation `Mod(𝒪X)` on top of the canonical
  owner `RingedSpace.Modules X`, together with the induced stalk-module short complex
  `stalkShortComplex S x`; the underlying additive sheaf stalk functor is only an internal bridge
  to the generic sheaf exactness criterion;
- primitive-vs-derived split:
  the primitive data are the ringed space `X`, the source-facing owner `Mod(𝒪X)`, a short
  complex `S : ShortComplex (Mod(𝒪X))`, and its canonical stalk-module realization
  `stalkShortComplex S x`;
  the underlying abelian-sheaf forgetful composite and the stalkwise exactness criterion for
  abelian sheaves are derived bridge API and should stay internal.

Source/core/bridge triage:
- `source-facing`: the two Stacks assertions that `Mod(\mathcal O_X)` is abelian and that
  exactness is stalkwise;
- `core/canonical`: `RingedSpace.Modules X`, `Mod(𝒪X)`, `RingedSpace.stalkModuleCat`,
  `RingedSpace.moduleStalkHom`, and `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact`;
- `bridge/view`: the private comparison between the module-valued stalk complex and the underlying
  abelian-sheaf stalk complex obtained through `SheafOfModules.toSheaf`. -/

local notation "𝒪X" => RingedSpace.ringCatSheaf X
local notation "ModX" => RingedSpace.Modules X

/-- Helper for Lemma 17.3.1: forgetting a sheaf of abelian groups to its underlying presheaf
preserves zero morphisms. -/
private instance sheafForget_preservesZeroMorphisms :
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X).PreservesZeroMorphisms := by
  exact ⟨fun _ _ ↦ rfl⟩

/-- Helper for Lemma 17.3.1: the underlying additive short complex on the canonical point stalks
induced by a short complex of `\mathcal O_X`-modules. -/
private noncomputable abbrev stalkComposite (x : X) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x

/-- Helper for Lemma 17.3.1: the additive stalk functor on sheaves of abelian groups preserves
zero morphisms. -/
private instance stalkComposite_preservesZeroMorphisms (x : X) :
    (stalkComposite x).PreservesZeroMorphisms := by
  let G : TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
    stalkComposite x
  letI : (TopCat.Sheaf.forget AddCommGrpCat.{u} X).PreservesZeroMorphisms :=
    sheafForget_preservesZeroMorphisms (X := X)
  letI : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).PreservesZeroMorphisms := by
    infer_instance
  simpa [stalkComposite] using (inferInstance : G.PreservesZeroMorphisms)

/-- Helper for Lemma 17.3.1: forgetting an `\mathcal O_X`-module sheaf to its underlying additive
sheaf preserves zero morphisms. -/
private theorem toAbelianSheaf_preservesZeroMorphisms :
    (SheafOfModules.toSheaf 𝒪X).PreservesZeroMorphisms := by
  exact ⟨fun _ _ ↦ rfl⟩

/-- Helper for Lemma 17.3.1: the underlying additive short complex on the canonical point stalks
induced by a short complex of `\mathcal O_X`-modules. -/
noncomputable abbrev stalkShortComplex (S : ShortComplex ModX) (x : X) :
    ShortComplex AddCommGrpCat.{u} :=
  @ShortComplex.map
    (TopCat.Sheaf AddCommGrpCat.{u} X)
    AddCommGrpCat.{u}
    _ _ _ _
    (@ShortComplex.map
      ModX
      (TopCat.Sheaf AddCommGrpCat.{u} X)
      _ _ _ _
      S
      (SheafOfModules.toSheaf 𝒪X)
      toAbelianSheaf_preservesZeroMorphisms)
    (stalkComposite x)
    (stalkComposite_preservesZeroMorphisms x)

/- Lemma 17.3.1 (1): for a ringed space `(X, 𝒪_X)`, the category `Mod(𝒪_X)` of sheaves of
`𝒪_X`-modules is abelian. This is the canonical owner instance on `Mod(𝒪X)`. -/
#check (SheafOfModules.instAbelian 𝒪X : Abelian ModX)

-- Proof sketch: first forget the `\mathcal O_X`-module structure to a short complex of sheaves of
-- abelian groups, then apply the generic stalkwise exactness criterion for sheaves.
/-- Lemma 17.3.1 (2): a short complex of `𝒪_X`-modules is exact in the middle if and only if all
its stalk-module complexes are exact in the middle. -/
theorem ringedSpaceModule_exact_iff_stalkwise_exact (S : ShortComplex ModX) :
    S.Exact ↔ ∀ x : X, (stalkShortComplex S x).Exact := by
  let F : ModX ⥤ TopCat.Sheaf AddCommGrpCat.{u} X := SheafOfModules.toSheaf 𝒪X
  letI : F.PreservesZeroMorphisms := by
    simpa [F] using toAbelianSheaf_preservesZeroMorphisms (X := X)
  letI : F.Faithful := by
    change (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).Faithful
    infer_instance
  letI : Limits.PreservesFiniteLimits F := by
    change Limits.PreservesFiniteLimits (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X))
    infer_instance
  letI : Limits.PreservesFiniteColimits F := by
    change Limits.PreservesFiniteColimits (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X))
    infer_instance
  constructor
  · intro hS x
    -- Proof comment: exactness survives forgetting to abelian sheaves, and then the standard
    -- stalk criterion applies pointwise.
    have hFx :
        ((S.map F).map
          (stalkComposite x)).Exact :=
      (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map F)).mp
        ((S.exact_map_iff_of_faithful F).mpr hS) x
    simpa [stalkShortComplex, stalkComposite, F] using hFx
  · intro hS
    have hF : (S.map F).Exact := by
      -- Proof comment: if every stalk complex is exact, then the underlying short complex of
      -- abelian sheaves is exact by the generic sheaf criterion.
      refine (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map F)).mpr ?_
      intro x
      simpa [stalkShortComplex, stalkComposite, F] using hS x
    exact (S.exact_map_iff_of_faithful F).mp hF
end AlgebraicGeometry.RingedSpace
