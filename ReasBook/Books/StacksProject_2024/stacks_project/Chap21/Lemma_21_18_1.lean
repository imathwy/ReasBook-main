import StacksProject_2024.Chap21.«21_18_0_1»
import StacksProject_2024.Chap21.Definition_21_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open CochainComplex
open SheafOfModules.RingedSite.CochainComplex

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

/-
Domain-style sampling for Lemma 21.18.1:
- primary domain: inverse image of K-flat cochain complexes of module sheaves on a ringed site;
- inspected owner declarations:
  `ringedSiteModuleCategory`,
  `pullbackFunctor`,
  `SheafOfModules.RingedSite.IsFlat`,
  `CochainComplex.IsKFlat`;
- best owner abstraction: the Chapter 21 inverse-image bridge `pullbackFunctor F φ` for module
  sheaves along the site-presented morphism of ringed topoi determined by `φ`;
- primitive data: the complex `K`, the site-presented morphism encoded by `φ`, and the
  termwise-flatness/K-flatness hypotheses on `K`;
- derived API: the pulled-back complex, viewed degreewise by the bridge owner `pullbackComplex`,
  and its termwise flatness.

Source/core/bridge triage:
- `source-facing`: pullback preserves K-flatness with flat terms for a site-presented morphism of
  ringed topoi;
- `core/canonical`: `ringedSiteModuleCategory`, `pullbackFunctor`,
  `CochainComplex.IsTermwiseFlat`, and `CochainComplex.IsKFlat`;
- `bridge/view`: `pullbackComplex`, the degreewise `mapHomologicalComplex` view of
  `pullbackFunctor F φ`.

The public theorem surface below intentionally omits
`[HasWeakSheafify _ AddCommGrpCat.{u}]` and `[_ .WEqualsLocallyBijective AddCommGrpCat.{u}]` on
both sites, as well as any right-adjoint witness for the site functor or module pushforward: once
the Chapter 21 bridge `ringedSiteUnderlyingStructureMap F φ`, `K.IsKFlat`, and
`K.IsTermwiseFlat` are fixed, those assumptions are proof infrastructure rather than source-facing
mathematical data.
-/
variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable {𝒪 : Sheaf JC CommRingCat.{max u v}} {𝒪' : Sheaf JD CommRingCat.{max u v}}
variable (φ : 𝒪 ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u v} JC JD).obj 𝒪')
variable [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).IsRightAdjoint]

local notation "ModC" => ringedSiteModuleCategory JC 𝒪
local notation "ModD" => ringedSiteModuleCategory JD 𝒪'

/-- The pullback of a cochain complex of `𝒪`-modules along the site-presented morphism determined
by `φ`, obtained by applying the Chapter 21 inverse-image functor `pullbackFunctor F φ`
degreewise. -/
def pullbackComplex (K : CochainComplex ModC ℤ) : CochainComplex ModD ℤ :=
  ((pullbackFunctor F φ).mapHomologicalComplex (up ℤ)).obj K

/-- In degree `n`, `pullbackComplex F φ K` is obtained by applying `pullbackFunctor F φ` to the
term `K.X n`. -/
@[simp] theorem pullbackComplex_obj_X (K : CochainComplex ModC ℤ) (n : ℤ) :
    (pullbackComplex F φ K).X n = (pullbackFunctor F φ).obj (K.X n) :=
  rfl

variable [MonoidalCategory (ringedSiteModuleCategory JC 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory JC 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory JD 𝒪')]
variable [MonoidalPreadditive (ringedSiteModuleCategory JD 𝒪')]

-- Proof sketch: apply Lemma `18.39.1` in each degree to keep flatness termwise. For K-flatness,
-- the source route replaces `K` by a bounded-above flat resolution tower, pulls that tower back
-- degreewise, preserves K-flatness through the colimit step, and then applies the short exact
-- sequence criterion to the pulled-back comparison sequence.
/-- Companion API for Lemma 21.18.1: pullback preserves termwise flatness for cochain complexes
of `𝒪`-modules along the site-presented morphism determined by `φ`. -/
theorem pullback_isTermwiseFlat_of_isTermwiseFlat
    (K : CochainComplex ModC ℤ)
    (hFlat : IsTermwiseFlat K) :
    IsTermwiseFlat (pullbackComplex F φ K) := by
  sorry

instance instPullbackComplexIsTermwiseFlat (K : CochainComplex ModC ℤ) [hFlat : IsTermwiseFlat K] :
    IsTermwiseFlat (pullbackComplex F φ K) :=
  pullback_isTermwiseFlat_of_isTermwiseFlat F φ K hFlat

/-- Companion API for Lemma 21.18.1: if `K` is K-flat and termwise flat, then its pullback along
the site-presented morphism determined by `φ` is again K-flat. -/
theorem pullback_isKFlat_of_isKFlat_and_termwiseFlat
    (K : CochainComplex ModC ℤ)
    (hKFlat : K.IsKFlat)
    (hFlat : IsTermwiseFlat K) :
    (pullbackComplex F φ K).IsKFlat := by
  sorry

/-- Lemma 21.18.1: for a site-presented morphism of ringed topoi, pulling back a K-flat cochain
complex of `𝒪`-modules with flat terms yields a K-flat cochain complex of `𝒪'`-modules with flat
terms. -/
@[stacks 0G7E]
theorem pullback_isKFlat_and_termwiseFlat_of_isKFlat_and_termwiseFlat
    (K : CochainComplex ModC ℤ)
    (hKFlat : K.IsKFlat)
    (hFlat : IsTermwiseFlat K) :
    (pullbackComplex F φ K).IsKFlat ∧
      IsTermwiseFlat (pullbackComplex F φ K) := by
  exact ⟨
    pullback_isKFlat_of_isKFlat_and_termwiseFlat F φ K hKFlat hFlat,
    pullback_isTermwiseFlat_of_isTermwiseFlat F φ K hFlat
  ⟩

end

end SheafOfModules.RingedSite
