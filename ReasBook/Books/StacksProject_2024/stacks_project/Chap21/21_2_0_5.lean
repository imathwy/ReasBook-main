import Mathlib.Tactic.Recall
import StacksProject_2024.Chap21.Lemma_21_12_4

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext

noncomputable section

universe u

/- Domain-style sampling for 21.2.0.5:
- primary domain: module cohomology on a ringed site over a fixed object `U`, computed on the
  localized ringed site `(C/U, 𝒪_U)` and compared with cohomology of the
  underlying abelian sheaf;
- sampled owner API:
  `SheafOfModules.toSheaf`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.unit`,
  `underlyingAbelianSheaf_cohomologyOver_eq_moduleCohomology`;
- best owner abstraction:
  `underlyingAbelianSheaf_cohomologyOver_eq_moduleCohomology`;
- primitive data: a site `(C, J)`, a ring-valued sheaf `𝒪`, an object `U : C`, an
  `𝒪`-module `ℱ`, and a degree `i : ℕ`;
- derived API: the identification of `H^i(U, ℱ_{ab})` with the module cohomology of the
  localized module on `(C/U, 𝒪_U)`.

Source/core/bridge triage:
- `source-facing`: the Chapter 21 module-side meaning of `H^i(U, \mathcal F)`;
- `core/canonical`: `underlyingAbelianSheaf_cohomologyOver_eq_moduleCohomology`;
- `bridge/view`: the source-facing specialization below, which keeps the Stacks surface while
  reusing the canonical Chapter 21 bridge theorem.

The previous file duplicated `21.2.0.1` by recalling the abelian-sheaf injective-resolution owner
from Chapter 20 and therefore dropped the localized module-cohomology content. This item is the
ringed-site/module analogue, so the main entry should reuse the Chapter 21 module-cohomology
comparison theorem directly. -/

/- 21.2.0.5 is the canonical Chapter 21 comparison identifying cohomology over an object `U` of
the underlying abelian sheaf of an `𝒪`-module with the corresponding module cohomology on the
localized ringed site `(C/U, 𝒪_U)`. -/
recall underlyingAbelianSheaf_cohomologyOver_eq_moduleCohomology

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [HasSheafify J AddCommGrpCat]
variable {𝒪 : Sheaf J RingCat.{u}} (U : C)
variable [HasExt (Sheaf J AddCommGrpCat)]
variable [HasSheafify (J.over U) AddCommGrpCat]
variable [HasExt (Sheaf (J.over U) AddCommGrpCat)]
variable [HasExt (SheafOfModules (𝒪.over U))]
variable (ℱ : SheafOfModules 𝒪) (i : ℕ)

local notation "𝒪_U" => 𝒪.over U

/- Source-facing specialization: for an `𝒪`-module `ℱ`, the degree-`i` cohomology over `U`
agrees with the degree-`i` module cohomology of the localized module on `(C/U, 𝒪_U)`. -/
#check (underlyingAbelianSheaf_cohomologyOver_eq_moduleCohomology U ℱ i :
  IsIsomorphic
    (((SheafOfModules.toSheaf 𝒪).obj ℱ).H' i U)
    (AddCommGrpCat.of (Ext (SheafOfModules.unit 𝒪_U) (ℱ.over U) i)))

end
