import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap18.Definition_18_28_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_88_1
import StacksProject_2024.stacks_project.Chap21.Lemma_21_12_4

open CategoryTheory Opposite
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Limits

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : ℕ → Type u} [∀ n, CommRing (A n)]
variable {ρ : ∀ n, A (n + 1) →+* A n}

/- Domain-style sampling for Remark 15.88.2:
- primary domain: modules over a sheaf of rings on the chaotic site of `ℕ`, together with their
  derived global sections;
- sampled owner declarations:
  `sequentialRingSystem`,
  `sequentialRingSystemRingSheaf`,
  `SeqRingMod`,
  `ringedModuleDerivedInverseLimitFunctor`,
  `ringSheaf`,
  `CategoryTheory.Sheaf.ΓNatIsoLim`,
  `underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology`;
- best owner abstraction: the Chapter 15 owners `SeqRingMod` and
  `ringedModuleDerivedInverseLimitFunctor`, together with the canonical commutative-ring-sheaf
  owner `ringSheaf` and the canonical global-sections owner `CategoryTheory.Sheaf.ΓNatIsoLim`;
- primitive data: the sequential inverse system of commutative rings `A₀ ← A₁ ← A₂ ← ⋯`,
  encoded by `sequentialRingSystem A ρ`;
- derived API: the chaotic-site module category `SeqRingMod A ρ`, the underived global-sections
  functor on that module category, its Chapter 15 derived inverse-limit owner
  `ringedModuleDerivedInverseLimitFunctor A ρ`, and the general cohomology-versus-`Ext`
  comparison theorem specialized to this setting.

Source/core/bridge triage:
- `source-facing`: the identification of sheaves of modules on the chaotic site of `ℕ` with
  `Mod(ℕ, (A_n))`, together with the interpretation of `R lim` as `RΓ(\mathbf N, -)`;
- `core/canonical`: `sequentialRingSystem`, `SeqRingMod`,
  `ringedModuleDerivedInverseLimitFunctor`, `ringSheaf`,
  `CategoryTheory.Sheaf.ΓNatIsoLim`, and
  `underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology`;
- `bridge/view`: the explicit module-valued global-sections functor on the chaotic site, compared
  with the Chapter 15 inverse-limit owner.

This file is therefore a bridge/view specialization: it should recall the existing owners rather
than introduce a parallel local ring-sheaf wrapper or a duplicate specialization theorem. -/

local notation "NatSite" => (⊥ : GrothendieckTopology ℕ)

/- The chaotic-site global-sections owner `Γ(\mathbf N, -)` identifies the global sections ring of
the structure sheaf `sequentialRingSystemRingSheaf A ρ` with the inverse limit ring
`A∞ = \varprojlim_n A_n`. -/
#check ((Sheaf.ΓNatIsoLim NatSite RingCat.{u}).app (sequentialRingSystemRingSheaf A ρ) :
  (Sheaf.Γ NatSite RingCat.{u}).obj (sequentialRingSystemRingSheaf A ρ) ≅
    limit (sequentialRingSystem A ρ ⋙ forget₂ CommRingCat RingCat))

/- Remark 15.88.2, owner form: together with the global-sections comparison above, the Chapter 15
owner `ringedModuleDerivedInverseLimitFunctor A ρ` is exactly the source-facing
`R\Gamma(\mathbf N,-)` functor on `\mathrm{Mod}(\mathbf N,(A_n))`. The defining total-right-
derived construction itself is already owned upstream by `Lemma_15_88_1`, so this bridge/view file
recalls that owner rather than restating its construction behind a parallel local theorem. -/
#check (ringedModuleDerivedInverseLimitFunctor A ρ :
  DerivedCategory (SeqRingMod A ρ) ⥤
    DerivedCategory (ModuleCat.{0}
      (((limit (sequentialRingSystem A ρ) : CommRingCat.{u}) : Type u))))

/- Remark 15.88.2 uses the canonical Chapter 21 comparison theorem directly; no new specialization
owner is introduced in this bridge/view file. -/
recall underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology

end
