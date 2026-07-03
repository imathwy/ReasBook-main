import Mathlib
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Lemma_15_69_2
import StacksProject_2024.Chap15.Lemma_15_75_2
import StacksProject_2024.Chap15.Lemma_15_75_15
import StacksProject_2024.Chap15.Lemma_15_78_4

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedExt
open scoped DerivedInternalHom

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A]
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "RHomPkg" => MonoidalClosed DMod
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)
local notation "𝓗" => DerivedCategory.homologyFunctor (ModuleCat A)

variable (H : RHomPkg)

/- Domain-style sampling for Remark 15.75.16:
- primary domain: tor-amplitude in `D(A)` together with the chapter's derived-duality owner;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `HasTorAmplitudeIn`,
  `HasProjectiveAmplitudeIn`,
  `CategoryTheory.derivedDual`,
  `CategoryTheory.derivedDual_isPerfect`,
  `CategoryTheory.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`,
  `projectiveAmplitudeIn_ext_vanishing_tfae`;
- best owner abstraction:
  `source-facing`: the tor-amplitude interval of the derived dual of a perfect complex;
  `core/canonical`: `K.IsPerfect`, `HasTorAmplitudeIn`, `HasProjectiveAmplitudeIn`, and
    `derivedDual`;
  `bridge/view`: derive projective amplitude from perfectness plus tor-amplitude via Lemma
    `15.78.4`, convert it to unrestricted Ext-vanishing via Lemma `15.69.2`, and transport that
    vanishing across the canonical tensor/Hom comparison for the derived dual.

Primitive data are the perfect object `K` and its tor-amplitude interval `[a, b]`.
Pseudo-coherence is derived API here, obtained from the chapter owner `K.IsPerfect` by
Lemma `15.75.2`, so it should not replace perfectness in the public theorem header. The derived dual itself is
already owned upstream by `derivedDual`, so this file should reuse that owner directly, with the
chapter notation `Kᵛ⟮H⟯` as the source-facing theorem surface, rather than introducing a parallel
local dual API.
-/

-- Proof sketch: perfectness plus tor-amplitude in `[a, b]` gives projective amplitude in
-- `[a, b]` by Lemma `15.78.4`, hence Ext-vanishing outside `[-b, -a]` by Lemma `15.69.2`.
-- The tensor/Hom comparison from Lemma `15.75.15` identifies
-- `M[0] ⊗^L K^\vee` with `RHom_A(K, M[0])`, and `15.74.0.2` rewrites the latter cohomology as
-- Ext. This transports the Ext-vanishing to the required tor-amplitude bounds for `K^\vee`.
/-- Remark 15.75.16: if `K` is perfect and has tor-amplitude in `[a, b]`, then its derived dual
`K^\vee = R\mathrm{Hom}_A(K, A)` has tor-amplitude in `[-b, -a]`. -/
theorem derivedDual_hasTorAmplitudeIn_neg_swap
    (H : RHomPkg) {K : DMod} {a b : ℤ}
    (hK : K.IsPerfect) (hamp : HasTorAmplitudeIn K a b) :
    HasTorAmplitudeIn Kᵛ⟮H⟯ (-b) (-a) := by
  have hKpc : K.IsPseudoCoherent :=
    (isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension K).1 hK |>.1
  have hPerfectTor : K.IsPerfect ∧ HasTorAmplitudeIn K a b := ⟨hK, hamp⟩
  have hprojAmp : HasProjectiveAmplitudeIn K a b :=
    ((projectiveAmplitudeIn_perfect_finitelyPresented_ext_tfae_of_isPseudoCoherent
      K a b hKpc).out 1 0).mp hPerfectTor
  have hExt :
      ∀ (M : ModuleCat A) (i : ℤ), i ∉ Set.Icc (-b) (-a) →
        ∀ e : Ext^i(K, (single₀).obj M), e = 0 :=
    ((projectiveAmplitudeIn_ext_vanishing_tfae K a b).out 0 1).mp hprojAmp
  intro M i hi
  let Kdual : DMod := Kᵛ⟮H⟯
  have hExtSub : Subsingleton (Ext^i(K, (single₀).obj M)) :=
    (subsingleton_iff_forall_eq 0).2 fun e ↦ hExt M i hi e
  letI : Subsingleton (Ext^i(K, (single₀).obj M)) := hExtSub
  have hRHomZero : IsZero ((𝓗 i).obj (RHom[H](K, (single₀).obj M))) := by
    let e := derivedHom_cohomology_iso_shiftedHom H K ((single₀).obj M) i
    letI : Subsingleton (((𝓗 i).obj (RHom[H](K, (single₀).obj M))) : Type u) :=
      e.injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  letI : IsIso (derivedDualTensorComparison H K) :=
    tensor_derivedDual_iso_derivedInternalHom H hK
  have hTensorZero :
      IsZero ((𝓗 i).obj ((derivedTensorProduct Kdual).obj ((single₀).obj M))) :=
    IsZero.of_iso hRHomZero <|
      (𝓗 i).mapIso (asIso ((derivedDualTensorComparison H K).app ((single₀).obj M)))
  exact IsZero.of_iso hTensorZero <|
    (𝓗 i).mapIso (derivedTensorProduct_comm Kdual ((single₀).obj M))

end

end CategoryTheory
