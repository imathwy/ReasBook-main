import Mathlib
import StacksProject_2024.Chap13.Definition_13_27_1
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Definition_15_69_1
import StacksProject_2024.Chap15.«15_74_0_2»
import StacksProject_2024.Chap15.RingSingle
import StacksProject_2024.Chap15.Lemma_15_75_12

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

/-- Helper for Remark 15.75.16: the derived dual `K^\vee = R\mathrm{Hom}_A(K, A[0])`. -/
abbrev derivedDual (H : RHomPkg) (K : DMod) : DMod :=
  RHom[H](K, ringSingle)

notation:max K:max "ᵛ⟮" H:max "⟯" => derivedDual H K

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
/-- Helper for Remark 15.75.16: a perfect object with tor-amplitude in `[a, b]` has projective
amplitude in the same interval. -/
lemma projective_amplitude_of_perfect_tor
    {K : DMod} {a b : ℤ}
    (hK : K.IsPerfect) (hamp : HasTorAmplitudeIn K a b) :
    HasProjectiveAmplitudeIn K a b := by
  sorry

/-- Helper for Remark 15.75.16: projective amplitude in `[a, b]` forces vanishing of
`Ext^i_A(K, M[0])` outside `[-b, -a]`. -/
lemma projective_amplitude_ext_vanishes
    {K : DMod} {a b : ℤ}
    (hK : HasProjectiveAmplitudeIn K a b)
    (M : ModuleCat A) (i : ℤ) (hi : i ∉ Set.Icc (-b) (-a))
    (e : Ext^i(K, (single₀).obj M)) :
    e = 0 := by
  sorry

/-- Helper for Remark 15.75.16: perfectness plus tor-amplitude on `K` forces vanishing of
`Ext^i_A(K, M[0])` outside the negated interval `[-b, -a]`. -/
lemma ext_vanishing_outside_negated_interval_of_perfect_tor
    {K : DMod} {a b : ℤ}
    (hK : K.IsPerfect) (hamp : HasTorAmplitudeIn K a b) :
    ∀ (M : ModuleCat A) (i : ℤ), i ∉ Set.Icc (-b) (-a) →
      ∀ e : Ext^i(K, (single₀).obj M), e = 0 := by
  sorry

/-- Helper for Remark 15.75.16: vanishing of all `Ext^i_A(K, M[0])` classes makes the degree-`i`
cohomology of `RHom_A(K, M[0])` a zero module. -/
lemma rhom_homology_isZero_of_ext_vanishing
    (H : RHomPkg) {K : DMod} (M : ModuleCat A) (i : ℤ)
    (hExt : ∀ e : Ext^i(K, (single₀).obj M), e = 0) :
    IsZero ((𝓗 i).obj (RHom[H](K, (single₀).obj M))) := by
  let e := derivedHom_cohomology_iso_shiftedHom (R := A) H K ((single₀).obj M) i
  let _ : Subsingleton (Ext^i(K, (single₀).obj M)) := by
    refine ⟨fun x y ↦ ?_⟩
    have hx : x = 0 := hExt x
    have hy : y = 0 := hExt y
    simpa [hx, hy]
  let _ : Subsingleton (((𝓗 i).obj (RHom[H](K, (single₀).obj M))) : Type _) :=
    e.injective.subsingleton
  -- A module with subsingleton underlying type is a zero object in `ModuleCat`.
  rw [ModuleCat.isZero_iff_subsingleton]
  infer_instance

/-- Helper for Remark 15.75.16: the tensor/Hom comparison for a perfect complex transports
vanishing of `H^i(RHom_A(K, M[0]))` to vanishing of the degree-`i` homology of
`K^\vee \otimes_A^{\mathbf L} M[0]`. -/
lemma derivedDual_tensor_homology_isZero_of_rhom_homology_isZero
    (H : RHomPkg) {K : DMod} (M : ModuleCat A) (i : ℤ)
    (hK : K.IsPerfect)
    (hRHomZero : IsZero ((𝓗 i).obj (RHom[H](K, (single₀).obj M)))) :
    IsZero ((𝓗 i).obj ((derivedTensorProduct ((single₀).obj M)).obj Kᵛ⟮H⟯)) := by
  sorry

/-- Remark 15.75.16: if `K` is perfect and has tor-amplitude in `[a, b]`, then its derived dual
`K^\vee = R\mathrm{Hom}_A(K, A)` has tor-amplitude in `[-b, -a]`. -/
theorem derivedDual_hasTorAmplitudeIn_neg_swap
    (H : RHomPkg) {K : DMod} {a b : ℤ}
    (hK : K.IsPerfect) (hamp : HasTorAmplitudeIn K a b) :
    HasTorAmplitudeIn Kᵛ⟮H⟯ (-b) (-a) := by
  intro M i hi
  have hExt :
      ∀ e : Ext^i(K, (single₀).obj M), e = 0 := by
    exact ext_vanishing_outside_negated_interval_of_perfect_tor hK hamp M i hi
  have hRHomZero :
      IsZero ((𝓗 i).obj (RHom[H](K, (single₀).obj M))) := by
    exact rhom_homology_isZero_of_ext_vanishing H M i hExt
  exact
    derivedDual_tensor_homology_isZero_of_rhom_homology_isZero
      H M i hK hRHomZero

end

end CategoryTheory
