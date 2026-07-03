import Mathlib
import StacksProject_2024.Chap17.Definition_17_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Mayer-Vietoris in sheaf cohomology on ringed spaces:
- primary domain: sheaf cohomology of `\mathcal O_X`-modules on a ringed space, specialized from
  the site-theoretic Mayer-Vietoris owner API;
- sampled owner declarations:
  `RingedSpace.Modules`,
  `SheafOfModules.toSheaf`,
  `Opens.mayerVietorisSquare`,
  `GrothendieckTopology.MayerVietorisSquare.sequence`;
- best owner abstraction: the core Mayer-Vietoris owner is the site-theoretic
  `GrothendieckTopology.MayerVietorisSquare`, while the ringed-space specialization should keep the
  module datum as `ℱ : (RingedSpace.Modules X)` and derive the underlying additive sheaf via
  `SheafOfModules.toSheaf`;
- primitive-vs-derived split:
  primitive data are the ringed space `X`, opens `U,V`, the covering equation `hUV`, the module
  `ℱ : (RingedSpace.Modules X)`, and the degree data;
  the additive sheaf, the Mayer-Vietoris square of opens, and the cohomology maps are derived API
  and should not be reintroduced as parallel owner declarations.

Source/core/bridge triage:
- `source-facing`: the Mayer-Vietoris six-term segment for a cover `X = U ∪ V`;
- `core/canonical`: `Opens.mayerVietorisSquare U V` and its site-theoretic cohomology sequence;
- `bridge/view`: the identification of the union object `U ⊔ V` with `⊤` via `hUV`, and passage
  from an `\mathcal O_X`-module to its underlying additive sheaf. -/

variable {X : RingedSpace.{u}}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

private noncomputable abbrev moduleToAddSheaf :
    (RingedSpace.Modules X) ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))

private abbrev mvSquare (U V : Opens X) :=
  Opens.mayerVietorisSquare U V

/-- The morphism on degree-`n` cohomology induced by a morphism of `\mathcal O_X`-modules,
evaluated on an open subset `U`. -/
private abbrev ringedSpaceModuleCohomologyMap
    {ℱ 𝒢 : (RingedSpace.Modules X)} (φ : ℱ ⟶ 𝒢) (n : ℕ) (U : Opens X) :
    (moduleToAddSheaf.obj ℱ).H' n U ⟶ (moduleToAddSheaf.obj 𝒢).H' n U :=
  ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map
      (moduleToAddSheaf.map φ)).app (op U)

private noncomputable abbrev ringedSpaceModuleMayerVietorisUnionSequence
    (U V : Opens X) (ℱ : (RingedSpace.Modules X)) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGrpCat.{u} 5 :=
  (mvSquare U V).sequence (moduleToAddSheaf.obj ℱ) n₀ n₁ h

/-- The canonical Mayer-Vietoris six-term cohomology segment attached to a cover `X = U ∪ V`. -/
noncomputable def ringedSpaceModuleMayerVietorisSequence
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (ℱ : (RingedSpace.Modules X))
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGrpCat.{u} 5 :=
  let F := moduleToAddSheaf.obj ℱ
  let S := mvSquare U V
  ComposableArrows.mk₅
    ((F.cohomologyPresheaf n₀).map (eqToHom hUV).op ≫ S.toBiprod F n₀)
    (S.fromBiprod F n₀)
    (S.δ F n₀ n₁ h ≫ (F.cohomologyPresheaf n₁).map (eqToHom hUV.symm).op)
    ((F.cohomologyPresheaf n₁).map (eqToHom hUV).op ≫ S.toBiprod F n₁)
    (S.fromBiprod F n₁)

private noncomputable def ringedSpaceModuleMayerVietorisSequenceIso
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (ℱ : (RingedSpace.Modules X))
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ringedSpaceModuleMayerVietorisSequence U V hUV ℱ n₀ n₁ h ≅
      ringedSpaceModuleMayerVietorisUnionSequence U V ℱ n₀ n₁ h :=
  let F := moduleToAddSheaf.obj ℱ
  let e₀ := (F.cohomologyPresheaf n₀).mapIso (eqToIso hUV).op
  let e₃ := (F.cohomologyPresheaf n₁).mapIso (eqToIso hUV).op
  ComposableArrows.isoMk₅ e₀ (Iso.refl _) (Iso.refl _) e₃ (Iso.refl _) (Iso.refl _)
    (by sorry)
    (by sorry)
    (by sorry)
    (by sorry)
    (by sorry)

-- Proof sketch: specialize the canonical site-theoretic Mayer-Vietoris exact sequence to the
-- underlying abelian sheaf of the `\mathcal O_X`-module `ℱ`, with the Mayer-Vietoris square of
-- the opens `U` and `V`; the hypothesis `hUV` identifies the union open `U ⊔ V` with `X`.
/-- Lemma 20.8.2 (Mayer-Vietoris): if a ringed space `X` is covered by two opens `U` and `V`,
then for every `\mathcal O_X`-module `\mathcal F` and every `n₀ + 1 = n₁`, the canonical
Mayer-Vietoris segment
`H^{n₀}(X, \mathcal F) ⟶ H^{n₀}(U, \mathcal F) ⊞ H^{n₀}(V, \mathcal F) ⟶
H^{n₀}(U ∩ V, \mathcal F) ⟶ H^{n₁}(X, \mathcal F) ⟶
H^{n₁}(U, \mathcal F) ⊞ H^{n₁}(V, \mathcal F) ⟶ H^{n₁}(U ∩ V, \mathcal F)`
is exact. -/
theorem ringedSpaceModule_mayerVietoris_sequence_exact
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (ℱ : (RingedSpace.Modules X))
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (ringedSpaceModuleMayerVietorisSequence U V hUV ℱ n₀ n₁ h).Exact := by
  refine exact_of_iso (ringedSpaceModuleMayerVietorisSequenceIso U V hUV ℱ n₀ n₁ h) ?_
  simpa [ringedSpaceModuleMayerVietorisUnionSequence, mvSquare] using
    (mvSquare U V).sequence_exact (moduleToAddSheaf.obj ℱ) n₀ n₁ h

private theorem ringedSpaceModuleCohomologyMap_toBiprod_natural
    (U V : Opens X) {ℱ 𝒢 : (RingedSpace.Modules X)} (φ : ℱ ⟶ 𝒢) (n : ℕ) :
    (mvSquare U V).toBiprod (moduleToAddSheaf.obj ℱ) n ≫
        biprod.map (ringedSpaceModuleCohomologyMap φ n U)
          (ringedSpaceModuleCohomologyMap φ n V) =
      ringedSpaceModuleCohomologyMap φ n (U ⊔ V) ≫
        (mvSquare U V).toBiprod (moduleToAddSheaf.obj 𝒢) n := sorry

private theorem ringedSpaceModuleCohomologyMap_fromBiprod_natural
    (U V : Opens X) {ℱ 𝒢 : (RingedSpace.Modules X)} (φ : ℱ ⟶ 𝒢) (n : ℕ) :
    (mvSquare U V).fromBiprod (moduleToAddSheaf.obj ℱ) n ≫
        ringedSpaceModuleCohomologyMap φ n (U ⊓ V) =
      biprod.map (ringedSpaceModuleCohomologyMap φ n U)
          (ringedSpaceModuleCohomologyMap φ n V) ≫
        (mvSquare U V).fromBiprod (moduleToAddSheaf.obj 𝒢) n := sorry

private theorem ringedSpaceModuleCohomologyMap_δ_natural
    (U V : Opens X) {ℱ 𝒢 : (RingedSpace.Modules X)} (φ : ℱ ⟶ 𝒢)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (mvSquare U V).δ (moduleToAddSheaf.obj ℱ) n₀ n₁ h ≫
        ringedSpaceModuleCohomologyMap φ n₁ (U ⊔ V) =
      ringedSpaceModuleCohomologyMap φ n₀ (U ⊓ V) ≫
        (mvSquare U V).δ (moduleToAddSheaf.obj 𝒢) n₀ n₁ h := sorry

private noncomputable def ringedSpaceModuleMayerVietorisUnionSequenceMap
    (U V : Opens X) {ℱ 𝒢 : (RingedSpace.Modules X)} (φ : ℱ ⟶ 𝒢)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ringedSpaceModuleMayerVietorisUnionSequence U V ℱ n₀ n₁ h ⟶
      ringedSpaceModuleMayerVietorisUnionSequence U V 𝒢 n₀ n₁ h :=
  ComposableArrows.homMk₅
    (ringedSpaceModuleCohomologyMap φ n₀ (U ⊔ V))
    (biprod.map (ringedSpaceModuleCohomologyMap φ n₀ U)
      (ringedSpaceModuleCohomologyMap φ n₀ V))
    (ringedSpaceModuleCohomologyMap φ n₀ (U ⊓ V))
    (ringedSpaceModuleCohomologyMap φ n₁ (U ⊔ V))
    (biprod.map (ringedSpaceModuleCohomologyMap φ n₁ U)
      (ringedSpaceModuleCohomologyMap φ n₁ V))
    (ringedSpaceModuleCohomologyMap φ n₁ (U ⊓ V))
    (ringedSpaceModuleCohomologyMap_toBiprod_natural U V φ n₀)
    (ringedSpaceModuleCohomologyMap_fromBiprod_natural U V φ n₀)
    (ringedSpaceModuleCohomologyMap_δ_natural U V φ n₀ n₁ h)
    (ringedSpaceModuleCohomologyMap_toBiprod_natural U V φ n₁)
    (ringedSpaceModuleCohomologyMap_fromBiprod_natural U V φ n₁)

/-- The morphism of Mayer-Vietoris sequences induced by a morphism of `\mathcal O_X`-modules. -/
noncomputable def ringedSpaceModuleMayerVietorisSequenceMap
    (U V : Opens X) (hUV : U ⊔ V = ⊤) {ℱ 𝒢 : (RingedSpace.Modules X)} (φ : ℱ ⟶ 𝒢)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ringedSpaceModuleMayerVietorisSequence U V hUV ℱ n₀ n₁ h ⟶
      ringedSpaceModuleMayerVietorisSequence U V hUV 𝒢 n₀ n₁ h :=
  (ringedSpaceModuleMayerVietorisSequenceIso U V hUV ℱ n₀ n₁ h).hom ≫
    ringedSpaceModuleMayerVietorisUnionSequenceMap U V φ n₀ n₁ h ≫
      (ringedSpaceModuleMayerVietorisSequenceIso U V hUV 𝒢 n₀ n₁ h).inv

end AlgebraicGeometry
