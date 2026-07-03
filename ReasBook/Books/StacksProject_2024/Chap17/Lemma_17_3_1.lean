import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.Definition_17_4_1
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
  `RingedSpace.stalkModuleCat`,
  `RingedSpace.moduleStalkHom`,
  `SheafOfModules.toSheaf`,
  `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact`,
  `Functor.reflects_exact_of_faithful`;
- best owner abstraction: the ambient owner category `RingedSpace.Modules X` together with the
  induced stalk-module short complex `stalkShortComplex S x`; the underlying additive sheaf stalk
  functor is only an internal bridge to the generic sheaf exactness criterion;
- primitive-vs-derived split:
  the primitive data are the ringed space `X`, a short complex
  `S : ShortComplex (RingedSpace.Modules X)`, and its canonical stalk-module realization
  `stalkShortComplex S x`;
  the underlying abelian-sheaf forgetful composite and the stalkwise exactness criterion for
  abelian sheaves are derived bridge API and should stay internal.

Source/core/bridge triage:
- `source-facing`: the two Stacks assertions that `Mod(\mathcal O_X)` is abelian and that
  exactness is stalkwise;
- `core/canonical`: `RingedSpace.Modules X`, `RingedSpace.stalkModuleCat`,
  `RingedSpace.moduleStalkHom`, and `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact`;
- `bridge/view`: the private comparison between the module-valued stalk complex and the underlying
  abelian-sheaf stalk complex obtained through `SheafOfModules.toSheaf`. -/

local notation "𝒪X" => RingedSpace.ringCatSheaf X
local notation "ModX" => RingedSpace.Modules X
local notation "toAbelianSheaf" => (SheafOfModules.toSheaf 𝒪X)

private noncomputable abbrev stalkAddCommGrpFunctor (x : X) :
    ModX ⥤ AddCommGrpCat.{u} :=
  toAbelianSheaf ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x

local instance toAbelianSheaf_preservesZeroMorphisms :
    (SheafOfModules.toSheaf 𝒪X).PreservesZeroMorphisms :=
  { map_zero _ _ := by rfl }

local instance stalkwiseAddCommGrpFunctor_preservesZeroMorphisms (x : X) :
    (stalkAddCommGrpFunctor x).PreservesZeroMorphisms := by
  let F : ModX ⥤ TopCat.Sheaf AddCommGrpCat.{u} X := toAbelianSheaf
  let G : TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
    TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  letI : F.PreservesZeroMorphisms := toAbelianSheaf_preservesZeroMorphisms
  letI : G.PreservesZeroMorphisms := by infer_instance
  simpa [stalkAddCommGrpFunctor, F, G] using
    (inferInstance : (F ⋙ G).PreservesZeroMorphisms)

/-- The short complex on stalk modules induced by a short complex of `\mathcal O_X`-modules. -/
noncomputable abbrev stalkShortComplex (S : ShortComplex ModX) (x : X) :
    ShortComplex (ModuleCat (X.presheaf.stalk x)) :=
  ShortComplex.mk
    (RingedSpace.moduleStalkHom x S.f)
    (RingedSpace.moduleStalkHom x S.g)
    (by sorry)

-- Proof sketch: `SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))` is exact, so exactness of a
-- short complex of `\mathcal O_X`-modules is equivalent to exactness of the underlying short
-- complex of abelian sheaves.
/-- Exactness of a short complex of `\mathcal O_X`-modules agrees with exactness of its underlying
short complex of abelian sheaves. -/
private theorem exact_iff_toAbelianSheaf_exact (S : ShortComplex ModX) :
    S.Exact ↔ (S.map toAbelianSheaf).Exact := sorry

/-- The stalk-module short complex is exact if and only if its underlying additive stalk complex
is exact. This is the internal bridge from the intrinsic stalk-module layer to the generic sheaf
criterion on abelian sheaves. -/
private theorem stalkShortComplex_exact_iff_stalkAddCommGrp_exact
    (S : ShortComplex ModX) (x : X) :
    (stalkShortComplex S x).Exact ↔ (S.map (stalkAddCommGrpFunctor x)).Exact := by
  sorry

/- Lemma 17.3.1 (1): for a ringed space `(X, 𝒪_X)`, the category `Mod(𝒪_X)` of sheaves of
`𝒪_X`-modules is abelian. This is the canonical owner instance on `RingedSpace.Modules X`. -/
#synth Abelian ModX

-- Proof sketch: first forget the `\mathcal O_X`-module structure to a short complex of sheaves of
-- abelian groups, then apply the generic stalkwise exactness criterion for sheaves.
/-- Lemma 17.3.1 (2): a short complex of `𝒪_X`-modules is exact in the middle if and only if all
its stalk-module complexes are exact in the middle. -/
theorem ringedSpaceModule_exact_iff_stalkwise_exact (S : ShortComplex ModX) :
    S.Exact ↔ ∀ x : X, (stalkShortComplex S x).Exact := by
  let F : ModX ⥤ TopCat.Sheaf AddCommGrpCat.{u} X := toAbelianSheaf
  letI : F.PreservesZeroMorphisms := toAbelianSheaf_preservesZeroMorphisms
  rw [exact_iff_toAbelianSheaf_exact]
  constructor
  · intro h x
    have hx : (S.map (stalkAddCommGrpFunctor x)).Exact := by
      simpa [stalkAddCommGrpFunctor] using
        (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map F)).mp h x
    exact (stalkShortComplex_exact_iff_stalkAddCommGrp_exact S x).mpr hx
  · intro h
    refine (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map F)).mpr ?_
    intro x
    have hx : (S.map (stalkAddCommGrpFunctor x)).Exact :=
      (stalkShortComplex_exact_iff_stalkAddCommGrp_exact S x).mp (h x)
    simpa [stalkAddCommGrpFunctor] using hx

end AlgebraicGeometry.RingedSpace

namespace CategoryTheory.ShortComplex.ShortExact

open AlgebraicGeometry

variable {X : RingedSpace.{u}}
variable {S : ShortComplex (RingedSpace.Modules X)}

/-- A short exact sequence of `\mathcal O_X`-modules induces a short exact sequence on each stalk
module. -/
theorem stalkShortComplex (hS : S.ShortExact) (x : X) :
    (RingedSpace.stalkShortComplex S x).ShortExact := by
  let toAbelianSheaf : RingedSpace.Modules X ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
    SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)
  letI : toAbelianSheaf.PreservesZeroMorphisms := by
    change (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).PreservesZeroMorphisms
    exact { map_zero _ _ := by rfl }
  let hExact :
      ∀ T : ShortComplex (RingedSpace.Modules X), T.Exact → (T.map toAbelianSheaf).Exact :=
    fun T hT ↦ (AlgebraicGeometry.RingedSpace.exact_iff_toAbelianSheaf_exact T).mp hT
  letI : toAbelianSheaf.PreservesMonomorphisms :=
    CategoryTheory.Functor.preservesMonomorphisms_of_map_exact toAbelianSheaf hExact
  letI : toAbelianSheaf.PreservesEpimorphisms :=
    CategoryTheory.Functor.preservesEpimorphisms_of_map_exact toAbelianSheaf hExact
  refine ModuleCat.shortComplex_shortExact (RingedSpace.stalkShortComplex S x)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      ((RingedSpace.ringedSpaceModule_exact_iff_stalkwise_exact S).mp hS.exact x))
    ?_ ?_
  · have hmono :
        Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (toAbelianSheaf.map S.f).hom) := by
      letI : Mono S.f := hS.mono_f
      exact (TopCat.Presheaf.mono_iff_stalk_mono (toAbelianSheaf.map S.f)).1
        (Functor.map_mono toAbelianSheaf S.f) x
    simpa [RingedSpace.moduleStalkMap] using (AddCommGrpCat.mono_iff_injective _).1 hmono
  · have hsurj :
        Function.Surjective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (toAbelianSheaf.map S.g).hom) := by
      letI : Epi S.g := hS.epi_g
      have hloc :
          TopCat.Presheaf.IsLocallySurjective (toAbelianSheaf.map S.g).hom :=
        (TopCat.Sheaf.isLocallySurjective_iff_epi (toAbelianSheaf.map S.g)).2 <|
          Functor.map_epi toAbelianSheaf S.g
      exact (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
        (toAbelianSheaf.map S.g).hom).1 hloc x
    simpa [RingedSpace.moduleStalkMap, toAbelianSheaf] using hsurj

end CategoryTheory.ShortComplex.ShortExact
