import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Topology.Sheaves.MayerVietoris
import StacksProject_2024.Chap20.«20_11_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace
open Opposite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Mayer-Vietoris in sheaf cohomology on ringed spaces:
- primary domain: sheaf cohomology of `𝒪_X`-modules on a ringed space, specialized from
  the site-theoretic Mayer-Vietoris owner API;
- sampled owner declarations:
  `RingedSpace.Modules`,
  `moduleUnderlyingSheaf`,
  `Opens.mayerVietorisSquare`,
  `GrothendieckTopology.MayerVietorisSquare.sequence`;
- best owner abstraction: the core Mayer-Vietoris owner is the site-theoretic
  `GrothendieckTopology.MayerVietorisSquare`, while the ringed-space specialization should keep the
  module datum as `ℱ : (RingedSpace.Modules X)` and derive the underlying additive sheaf via
  `moduleUnderlyingSheaf X`;
- primitive-vs-derived split:
  primitive data are the ringed space `X`, opens `U,V`, the covering equation `hUV`, the module
  `ℱ : (RingedSpace.Modules X)`, and the degree data;
  the additive sheaf, the Mayer-Vietoris square of opens, and the cohomology maps are derived API
  and should not be reintroduced as parallel owner declarations.

Source/core/bridge triage:
- `source-facing`: the Mayer-Vietoris six-term segment for a cover `X = U ∪ V`;
- `core/canonical`: `Opens.mayerVietorisSquare U V` and its site-theoretic cohomology sequence;
- `bridge/view`: the identification of the union object `U ⊔ V` with `⊤` via `hUV`, and passage
  from an `𝒪_X`-module to its underlying additive sheaf. -/

variable {X : RingedSpace.{u}}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

local notation "ModX" => RingedSpace.Modules X
local notation "AbSheaf" => moduleUnderlyingSheaf X

/-- The owner-facing Mayer-Vietoris six-term cohomology segment attached to a cover `X = U ∪ V`,
obtained from the canonical Chapter 20 forgetful bridge `moduleUnderlyingSheaf X`. -/
noncomputable def ringedSpaceModuleMayerVietorisSequence
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (ℱ : ModX) (n : ℕ) :
    ComposableArrows AddCommGrpCat.{u} 5 :=
  let F := (AbSheaf).obj ℱ
  let S := Opens.mayerVietorisSquare U V
  let e₀ := (F.cohomologyPresheaf n).mapIso (eqToIso hUV).op
  let e₁ := (F.cohomologyPresheaf (n + 1)).mapIso (eqToIso hUV).op
  ComposableArrows.mk₅
    (e₀.hom ≫ S.toBiprod F n)
    (S.fromBiprod F n)
    (S.δ F n (n + 1) rfl ≫ e₁.inv)
    (e₁.hom ≫ S.toBiprod F (n + 1))
    (S.fromBiprod F (n + 1))

private theorem ringedSpaceModuleMayerVietorisSequence_exact₀
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (ℱ : ModX) (n : ℕ) :
    let F := (AbSheaf).obj ℱ
    let S := Opens.mayerVietorisSquare U V
    let e := (F.cohomologyPresheaf n).mapIso (eqToIso hUV).op
    (ShortComplex.mk
      (e.hom ≫ S.toBiprod F n)
      (S.fromBiprod F n)
      (by
        simpa [Category.assoc] using (S.sequence_exact F n (n + 1) rfl).toIsComplex.zero 0)).Exact := by
  dsimp
  let F := (AbSheaf).obj ℱ
  let S := Opens.mayerVietorisSquare U V
  let e := (F.cohomologyPresheaf n).mapIso (eqToIso hUV).op
  let hExact := S.sequence_exact F n (n + 1) rfl
  let i :
      ShortComplex.mk
          (S.toBiprod F n)
          (S.fromBiprod F n)
          (by simpa using hExact.toIsComplex.zero 0) ≅
        ShortComplex.mk
          (e.hom ≫ S.toBiprod F n)
          (S.fromBiprod F n)
          (by simpa [Category.assoc] using hExact.toIsComplex.zero 0) :=
    ShortComplex.isoMk e.symm (Iso.refl _) (Iso.refl _)
      (by
        calc
          e.inv ≫ e.hom ≫ S.toBiprod F n = (e.inv ≫ e.hom) ≫ S.toBiprod F n := by
            simp
          _ = 𝟙 _ ≫ S.toBiprod F n := by simp
          _ = S.toBiprod F n := by simp)
      (by simp)
  exact ShortComplex.exact_of_iso i (hExact.exact 0)

private theorem ringedSpaceModuleMayerVietorisSequence_exact₁
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (ℱ : ModX) (n : ℕ) :
    let F := (AbSheaf).obj ℱ
    let S := Opens.mayerVietorisSquare U V
    let e := (F.cohomologyPresheaf (n + 1)).mapIso (eqToIso hUV).op
    (ShortComplex.mk
      (S.fromBiprod F n)
      (S.δ F n (n + 1) rfl ≫ e.inv)
      (by
        simpa [Category.assoc, S.fromBiprod_δ F n (n + 1) rfl])).Exact := by
  dsimp
  let F := (AbSheaf).obj ℱ
  let S := Opens.mayerVietorisSquare U V
  let e := (F.cohomologyPresheaf (n + 1)).mapIso (eqToIso hUV).op
  let hExact := S.sequence_exact F n (n + 1) rfl
  let i :
      ShortComplex.mk
          (S.fromBiprod F n)
          (S.δ F n (n + 1) rfl)
          (by simpa using hExact.toIsComplex.zero 1) ≅
        ShortComplex.mk
          (S.fromBiprod F n)
          (S.δ F n (n + 1) rfl ≫ e.inv)
          (by
            calc
              S.fromBiprod F n ≫ (S.δ F n (n + 1) rfl ≫ e.inv) =
                  (S.fromBiprod F n ≫ S.δ F n (n + 1) rfl) ≫ e.inv := by
                simp
              _ = 0 ≫ e.inv := by simpa [S.fromBiprod_δ F n (n + 1) rfl]
              _ = 0 := by simp) :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e.symm
      (by simp)
      (by simp)
  exact ShortComplex.exact_of_iso i (hExact.exact 1)

private theorem ringedSpaceModuleMayerVietorisSequence_exact₂_zero
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (ℱ : ModX) (n : ℕ) :
    let F := (AbSheaf).obj ℱ
    let S := Opens.mayerVietorisSquare U V
    let e := (F.cohomologyPresheaf (n + 1)).mapIso (eqToIso hUV).op
    (S.δ F n (n + 1) rfl ≫ e.inv) ≫ (e.hom ≫ S.toBiprod F (n + 1)) = 0 := by
  dsimp
  let F := (AbSheaf).obj ℱ
  let S := Opens.mayerVietorisSquare U V
  let e := (F.cohomologyPresheaf (n + 1)).mapIso (eqToIso hUV).op
  have hcancel :
      e.inv ≫ e.hom ≫ S.toBiprod F (n + 1) = S.toBiprod F (n + 1) :=
    e.inv_hom_id_assoc (S.toBiprod F (n + 1))
  calc
    (S.δ F n (n + 1) rfl ≫ e.inv) ≫ (e.hom ≫ S.toBiprod F (n + 1)) =
        S.δ F n (n + 1) rfl ≫ S.toBiprod F (n + 1) := by
      change
        S.δ F n (n + 1) rfl ≫ (e.inv ≫ e.hom ≫ S.toBiprod F (n + 1)) =
          S.δ F n (n + 1) rfl ≫ S.toBiprod F (n + 1)
      exact congrArg (fun k ↦ S.δ F n (n + 1) rfl ≫ k) hcancel
    _ = 0 := by
      simpa using (S.sequence_exact F n (n + 1) rfl).toIsComplex.zero 2

private theorem ringedSpaceModuleMayerVietorisSequence_exact₂
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (ℱ : ModX) (n : ℕ) :
    let F := (AbSheaf).obj ℱ
    let S := Opens.mayerVietorisSquare U V
    let e := (F.cohomologyPresheaf (n + 1)).mapIso (eqToIso hUV).op
    (ShortComplex.mk
      (S.δ F n (n + 1) rfl ≫ e.inv)
      (e.hom ≫ S.toBiprod F (n + 1))
      (by simpa using ringedSpaceModuleMayerVietorisSequence_exact₂_zero U V hUV ℱ n)).Exact := by
  dsimp
  let F := (AbSheaf).obj ℱ
  let S := Opens.mayerVietorisSquare U V
  let e := (F.cohomologyPresheaf (n + 1)).mapIso (eqToIso hUV).op
  let hExact := S.sequence_exact F n (n + 1) rfl
  let i :
      ShortComplex.mk
          (S.δ F n (n + 1) rfl)
          (S.toBiprod F (n + 1))
          (by simpa using hExact.toIsComplex.zero 2) ≅
        ShortComplex.mk
          (S.δ F n (n + 1) rfl ≫ e.inv)
          (e.hom ≫ S.toBiprod F (n + 1))
          (by simpa using ringedSpaceModuleMayerVietorisSequence_exact₂_zero U V hUV ℱ n) :=
    ShortComplex.isoMk (Iso.refl _) e.symm (Iso.refl _)
      (by simp)
      (by
        calc
          e.inv ≫ e.hom ≫ S.toBiprod F (n + 1) = (e.inv ≫ e.hom) ≫ S.toBiprod F (n + 1) := by
            simp
          _ = 𝟙 _ ≫ S.toBiprod F (n + 1) := by simp
          _ = S.toBiprod F (n + 1) := by simp)
  exact ShortComplex.exact_of_iso i (hExact.exact 2)

private theorem ringedSpaceModuleMayerVietorisSequence_exact₃
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (ℱ : ModX) (n : ℕ) :
    let F := (AbSheaf).obj ℱ
    let S := Opens.mayerVietorisSquare U V
    let e := (F.cohomologyPresheaf (n + 1)).mapIso (eqToIso hUV).op
    (ShortComplex.mk
      (e.hom ≫ S.toBiprod F (n + 1))
      (S.fromBiprod F (n + 1))
      (by
        simpa [Category.assoc] using (S.sequence_exact F n (n + 1) rfl).toIsComplex.zero 3)).Exact := by
  dsimp
  let F := (AbSheaf).obj ℱ
  let S := Opens.mayerVietorisSquare U V
  let e := (F.cohomologyPresheaf (n + 1)).mapIso (eqToIso hUV).op
  let hExact := S.sequence_exact F n (n + 1) rfl
  let i :
      ShortComplex.mk
          (S.toBiprod F (n + 1))
          (S.fromBiprod F (n + 1))
          (by simpa using hExact.toIsComplex.zero 3) ≅
        ShortComplex.mk
          (e.hom ≫ S.toBiprod F (n + 1))
          (S.fromBiprod F (n + 1))
          (by simpa [Category.assoc] using hExact.toIsComplex.zero 3) :=
    ShortComplex.isoMk e.symm (Iso.refl _) (Iso.refl _)
      (by
        calc
          e.inv ≫ e.hom ≫ S.toBiprod F (n + 1) = (e.inv ≫ e.hom) ≫ S.toBiprod F (n + 1) := by
            simp
          _ = 𝟙 _ ≫ S.toBiprod F (n + 1) := by simp
          _ = S.toBiprod F (n + 1) := by simp)
      (by simp)
  exact ShortComplex.exact_of_iso i (hExact.exact 3)

-- Proof sketch: specialize the canonical site-theoretic Mayer-Vietoris exact sequence to the
-- underlying abelian sheaf of the `𝒪_X`-module `ℱ`, with the Mayer-Vietoris square of
-- the opens `U` and `V`; the hypothesis `hUV` identifies the union open `U ⊔ V` with `X`.
/-- Lemma 20.8.2 (Mayer-Vietoris): if a ringed space `X` is covered by two opens `U` and `V`,
then for every `𝒪_X`-module `ℱ` and every degree `n`, the canonical
Mayer-Vietoris segment
`H^n(X, ℱ) ⟶ H^n(U, ℱ) ⊞ H^n(V, ℱ) ⟶
H^n(U ∩ V, ℱ) ⟶ H^{n + 1}(X, ℱ) ⟶
H^{n + 1}(U, ℱ) ⊞ H^{n + 1}(V, ℱ) ⟶ H^{n + 1}(U ∩ V, ℱ)`
is exact. -/
@[stacks 01EB]
theorem ringedSpaceModule_mayerVietoris_sequence_exact
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (ℱ : ModX)
    (n : ℕ) :
    (ringedSpaceModuleMayerVietorisSequence U V hUV ℱ n).Exact := by
  refine exact_of_δ₀
    (ringedSpaceModuleMayerVietorisSequence_exact₀ U V hUV ℱ n).exact_toComposableArrows ?_
  refine exact_of_δ₀
    (ringedSpaceModuleMayerVietorisSequence_exact₁ U V hUV ℱ n).exact_toComposableArrows ?_
  exact exact_of_δ₀
    (ringedSpaceModuleMayerVietorisSequence_exact₂ U V hUV ℱ n).exact_toComposableArrows
    (ringedSpaceModuleMayerVietorisSequence_exact₃ U V hUV ℱ n).exact_toComposableArrows

end AlgebraicGeometry
