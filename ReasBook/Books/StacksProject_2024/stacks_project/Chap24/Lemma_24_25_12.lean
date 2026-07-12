import StacksProject_2024.Chap24.Definition_24_13_1

open CategoryTheory Limits

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

local notation "DGAO" => @DifferentialGradedAlgebra C _ J _ 𝒪 _
local notation "DGModA" => @DifferentialGradedModule.moduleCategory C _ J _ 𝒪 _

open scoped SheafOfModules.RingedSite.DifferentialGradedModule

namespace DifferentialGradedModule

/-
The source-facing extension clause already has the canonical square owner `CommSq`. It records
the existence of the new bottom arrow `Mr' r ⟶ F.obj M`, so it should remain an explicit
square-filler statement rather than being repackaged as a lifting-property owner.
-/
/-- A functorial enlargement of dg-modules that kills the chosen acyclic mono family by the source
extension property. The data is bundled so downstream files can reuse the chosen endofunctor and
comparison map directly, with mono, quasi-isomorphism, and square-filler conditions as companion
API. -/
structure AcyclicKillingFunctor
    (𝒜 : DGAO) {R : Type _} (Mr Mr' : R → DGModA 𝒜) (ιr : ∀ r : R, Mr r ⟶ Mr' r) where
  /-- The underlying endofunctor on differential graded `\mathcal A`-modules. -/
  toFunctor : DGModA 𝒜 ⥤ DGModA 𝒜
  /-- The comparison map from a dg-module to its acyclic-killing enlargement. -/
  ι : 𝟭 (DGModA 𝒜) ⟶ toFunctor
  /-- The comparison natural transformation is monomorphic. -/
  mono_ι : Mono ι
  /-- Each comparison component is a quasi-isomorphism on the underlying cochain complexes. -/
  quasiIso_app (M : DGModA 𝒜) : QuasiIso (ι.app M).toCochainMap
  /-- Every square with left edge in the chosen acyclic mono family extends across `ι.app M`. -/
  has_filler {r : R} {M : DGModA 𝒜} (w : Mr r ⟶ M) :
      ∃ l : Mr' r ⟶ toFunctor.obj M, CommSq (ιr r) w l (ι.app M)

namespace AcyclicKillingFunctor

variable {𝒜 : DGAO} {R : Type _} {Mr Mr' : R → DGModA 𝒜} {ιr : ∀ r : R, Mr r ⟶ Mr' r}

/-- The comparison natural transformation of an acyclic-killing functor is mono. -/
instance instMono (J : AcyclicKillingFunctor 𝒜 Mr Mr' ιr) : Mono J.ι :=
  J.mono_ι

/-- Each component of an acyclic-killing comparison map is mono. -/
theorem mono_app (J : AcyclicKillingFunctor 𝒜 Mr Mr' ιr) (M : DGModA 𝒜) :
    Mono (J.ι.app M) :=
  (NatTrans.mono_iff_mono_app J.ι).1 J.mono_ι M

/-- The source extension property of an acyclic-killing functor, stated for one square. -/
theorem exists_filler (J : AcyclicKillingFunctor 𝒜 Mr Mr' ιr)
    {r : R} {M : DGModA 𝒜} (w : Mr r ⟶ M) :
    ∃ l : Mr' r ⟶ J.toFunctor.obj M, CommSq (ιr r) w l (J.ι.app M) :=
  J.has_filler w

end AcyclicKillingFunctor

/-- Lemma 24.25.12: for a ringed site `(\mathcal C, \mathcal O)` and a sheaf of differential
graded algebras `(\mathcal A, d)` on it, any family of injective maps
`\mathcal M_r \to \mathcal M'_r` between acyclic differential graded `\mathcal A`-modules admits
a functorial enlargement `j : \mathrm{id} \to M` in `\mathrm{Mod}(\mathcal A, d)` whose
components are injective quasi-isomorphisms and through which every square
`\mathcal M_r \to \mathcal N \leftarrow \mathcal M'_r` with left side one of the chosen maps
admits a filler. -/
@[stacks 0FSZ]
theorem exists_acyclic_killing_functor
    (𝒜 : DGAO) {R : Type _} (Mr Mr' : R → DGModA 𝒜) (ιr : ∀ r : R, Mr r ⟶ Mr' r)
    (hιr : ∀ r : R, Mono (ιr r))
    (hMr : ∀ r : R, HomologicalComplex.Acyclic (Mr r).toComplex)
    (hMr' : ∀ r : R, HomologicalComplex.Acyclic (Mr' r).toComplex) :
    Nonempty (AcyclicKillingFunctor 𝒜 Mr Mr' ιr) := sorry

end DifferentialGradedModule

end

end SheafOfModules.RingedSite
