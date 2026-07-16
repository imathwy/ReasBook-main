import Mathlib
import StacksProject_2024.stacks_project.Chap19.Lemma_19_11_6
import StacksProject_2024.stacks_project.Chap24.Lemma_24_11_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.IsGrothendieckAbelian
open scoped SheafOfModules.RingedSite.GradedModuleSheaf

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/- Semantic search note: `lean_leansearch` was unavailable in this environment (HTTP 521), so the
owner choice was checked against the local Chapter 24 Grothendieck-abelian instance
`gradedModuleSheaf_isGrothendieckAbelian` and the Chapter 19 injective criterion
`injective_iff_generator_subobject_extension`. -/

/-- The canonical index set of separator-subobject tests for injectivity in `Mod(\mathcal A)`. -/
abbrev injectiveTestIndex (𝒜 : GradedAlgebraSheaf 𝒪) :=
  Subobject (separator (Mod(𝒜)))

/-- The source of the canonical separator-subobject test morphism indexed by `t`. -/
abbrev injectiveTestSource (𝒜 : GradedAlgebraSheaf 𝒪) (t : injectiveTestIndex 𝒜) :
    Mod(𝒜) :=
  ((show Subobject (separator (Mod(𝒜))) from t) : Mod(𝒜))

/-- The target of each canonical separator-subobject test morphism is the chosen separator. -/
abbrev injectiveTestTarget (𝒜 : GradedAlgebraSheaf 𝒪) (_t : injectiveTestIndex 𝒜) :
    Mod(𝒜) :=
  separator (Mod(𝒜))

/-- The canonical separator-subobject test morphism indexed by `t`. -/
abbrev injectiveTestι (𝒜 : GradedAlgebraSheaf 𝒪) (t : injectiveTestIndex 𝒜) :
    injectiveTestSource 𝒜 t ⟶ injectiveTestTarget 𝒜 t :=
  (show Subobject (separator (Mod(𝒜))) from t).arrow

/-- Each canonical separator-subobject test morphism is a monomorphism. -/
instance injectiveTestι_mono (𝒜 : GradedAlgebraSheaf 𝒪) (t : injectiveTestIndex 𝒜) :
    Mono (injectiveTestι 𝒜 t) :=
  Subobject.arrow_mono (show Subobject (separator (Mod(𝒜))) from t)

/-- Helper for Lemma 24.25.1: a graded `\mathcal A`-module is injective exactly when every map
from a canonical separator subobject extends across its inclusion into the separator. -/
theorem injective_iff_forall_lifts_injectiveTestι
    (𝒜 : GradedAlgebraSheaf 𝒪) (ℐ : Mod(𝒜)) :
    Injective ℐ ↔
      ∀ t : injectiveTestIndex 𝒜, ∀ f : injectiveTestSource 𝒜 t ⟶ ℐ,
        ∃ g : injectiveTestTarget 𝒜 t ⟶ ℐ, injectiveTestι 𝒜 t ≫ g = f := sorry

/-- Lemma 24.25.1: let `(\mathcal C, \mathcal O)` be a ringed site and let `\mathcal A` be a sheaf
of graded algebras on it. Then there exists a set `T` and, for each `t : T`, an injective map
`\mathcal N_t \to \mathcal N'_t` of graded `\mathcal A`-modules such that a graded
`\mathcal A`-module `\mathcal I` is injective if and only if every morphism
`\mathcal N_t \to \mathcal I` extends across `\mathcal N_t \to \mathcal N'_t`. -/
theorem exists_injectiveTestFamily
    (𝒜 : GradedAlgebraSheaf 𝒪) :
    ∃ (T : Type _) (𝒩 𝒩' : T → Mod(𝒜))
      (ι : ∀ t, 𝒩 t ⟶ 𝒩' t),
      (∀ t, Mono (ι t)) ∧
        ∀ ℐ : Mod(𝒜),
          Injective ℐ ↔ ∀ t (f : 𝒩 t ⟶ ℐ), ∃ g : 𝒩' t ⟶ ℐ, ι t ≫ g = f := sorry

end

end SheafOfModules.RingedSite
