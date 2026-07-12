import StacksProject_2024.Chap13.Definition_13_27_1
import StacksProject_2024.Chap20.Global_sections_module_owners_core
import StacksProject_2024.Chap20.Lemma_20_32_2
import StacksProject_2024.Chap20.Lemma_20_31_8
import StacksProject_2024.Chap20.Lemma_20_32_3
import StacksProject_2024.Chap20.Lemma_20_32_6
import StacksProject_2024.Chap20.Lemma_20_42_1
import StacksProject_2024.Chap20.Open_subspace_module_core

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalClosed
open CategoryTheory.Preadditive
open TopologicalSpace
open scoped AlgebraicGeometry.RingedSpaceCohomology CartesianClosed DerivedExt RingedSpace.Hom
  RingedSpaceDerivedPushforward

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

open scoped RingedSpaceOpenHypercohomology

variable {X Y : RingedSpace.{u}}
local notation "DModX" => ModuleDerived X

variable (f : X ⟶ Y) (𝓑 : Set (Opens Y.carrier))

/- Domain-style sampling for Lemma 20.45.2:
- primary domain: derived pushforward, preimage hypercohomology on basis opens, and the resulting
  degree-zero internal-Hom/Ext comparison on a ringed space;
- sampled owner declarations:
  `ModuleDerived`,
  `moduleOpenHypercohomology`,
  `RingedSpace.cohomologySheaf`,
  `moduleDerivedPushforward`,
  `preimageObjectwiseCohomologyPresheaf_sheafification_isomorphic_pushforwardCohomologySheaf`,
  `open_zeroHypercohomology_internalHom_isomorphic_restrictedDerivedHom`;
- best owner abstraction: the Chapter 20 owners `ModuleDerived`, `moduleOpenHypercohomology`,
  `RingedSpace.cohomologySheaf`, `moduleDerivedPushforward`, the source-facing preimage
  sheafification bridge of Lemma `20.32.6`, and the degree-zero internal-Hom/derived-Hom bridge
  of Lemma `20.42.1`; the present file should keep the source-facing basiswise vanishing
  hypotheses and their consequences, with clause `(5)` stated on the canonical degree-zero
  preimage internal-Hom presheaf and interpreted objectwise by Lemma `20.42.1`;
- primitive data: a morphism `f : X ⟶ Y`, a basis `𝓑` of opens of `Y`, and an object of
  `D(𝒪_X)` or a pair of derived objects whose restrictions define local Ext groups;
- derived API: negative cohomology-sheaf vanishing, extension from basis opens to all opens, and
  sheafness of the canonical degree-zero preimage internal-Hom presheaf
  `preimageObjectwiseCohomologyPresheaf f (K ⟹ L) 0`, together with its source-facing
  objectwise interpretation
  `V ↦ Hom(K|_{f⁻¹(V)}, L|_{f⁻¹(V)})`.

Source/core/bridge triage:
- `source-facing`: the basiswise negative vanishing hypotheses and the all-open/sheaf consequences
  of Stacks Project Lemma 20.45.2;
- `core/canonical`: `ModuleDerived`, `moduleOpenHypercohomology`,
  `RingedSpace.cohomologySheaf`, `moduleDerivedPushforward`,
  `preimageObjectwiseCohomologyPresheaf_sheafification_isomorphic_pushforwardCohomologySheaf`,
  `moduleRestrictionToOpenDerived`, the canonical `Ext^i(-, -)` owner in the derived category,
  and the internal-Hom comparison theorem
  `open_zeroHypercohomology_internalHom_isomorphic_restrictedDerivedHom`;
- `bridge/view`: the objectwise comparison between the canonical internal-Hom presheaf
  `(Opens.map f.hom.base).op ⋙ 𝓗'[0](X, K ⟹ L)` and the source-facing local derived-Hom groups
  `Hom(K|_{f⁻¹(V)}, L|_{f⁻¹(V)})`.
-/

section CohomologyPart

section

-- Proof sketch: apply Lemma `20.32.6` with `i < 0`. The basiswise vanishing hypothesis says that
-- the presheaf whose sheafification is `H^i(Rf_* K)` is zero on a topological basis, so its
-- sheafification, hence the cohomology sheaf itself, is zero.
/-- Lemma 20.45.2 (1): if `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` is a morphism of ringed
spaces, `𝓑` is a basis for the topology on `Y`, and `K ∈ D(𝒪_X)` has
`H^i(f^{-1}(V), K) = 0` for every `V ∈ 𝓑` and every `i < 0`, then the negative cohomology
sheaves of `Rf_* K` vanish. -/
@[stacks 0D66]
theorem pushforward_negative_cohomologySheaf_isZero_of_basiswise_negative_preimage_hypercohomology
    (K : DModX)
    (h𝓑 : Opens.IsBasis 𝓑)
    (hK :
      ∀ ⦃V : Opens Y.carrier⦄, V ∈ 𝓑 → (i : ℤ) → i < 0 →
        IsZero (H^i(preimageOpen f V, K)))
    (i : ℤ) (hi : i < 0) :
    IsZero (𝓗[i](Y, (R(f)_*).obj K)) := by
  sorry

-- Proof sketch: first use the previous clause to show `H^i(Rf_* K) = 0` for `i < 0`. Then apply
-- Lemma `20.32.6` again to identify `H^i(f^{-1}(V), K)` with sections of the zero sheaf
-- `H^i(Rf_* K)` on an arbitrary open `V ⊆ Y`.
/-- Lemma 20.45.2 (2): under the same basiswise negative-vanishing hypothesis on `K`, one has
`H^i(f^{-1}(V), K) = 0` for every open subset `V ⊆ Y` and every `i < 0`. -/
@[stacks 0D66]
theorem preimage_negative_hypercohomology_isZero_on_all_opens
    (K : DModX)
    (h𝓑 : Opens.IsBasis 𝓑)
    (hK :
      ∀ ⦃V : Opens Y.carrier⦄, V ∈ 𝓑 → (i : ℤ) → i < 0 →
        IsZero (H^i(preimageOpen f V, K)))
    (V : Opens Y.carrier) (i : ℤ) (hi : i < 0) :
    IsZero (H^i(preimageOpen f V, K)) := sorry

section ZeroPresheaf

-- Proof sketch: the previous clause kills the negative cohomology sheaves of `Rf_* K`. Hence
-- `Rf_* K` is concentrated in degrees `≥ 0`, so Lemma `20.32.6` identifies `H^0(Rf_* K)` with the
-- sheafification of the presheaf `V ↦ H^0(f^{-1}(V), K)`, while concentration in nonnegative
-- degrees implies this presheaf already satisfies the sheaf condition.
/-- Lemma 20.45.2 (3): under the same hypotheses, the rule
`V ↦ H^0(f^{-1}(V), K)` is a sheaf on `Y`. In Lean this is the source-facing preimage presheaf
`preimageObjectwiseCohomologyPresheaf f K 0`. -/
@[stacks 0D66]
theorem preimage_zero_hypercohomology_presheaf_isSheaf
    (K : DModX)
    (h𝓑 : Opens.IsBasis 𝓑)
    (hK :
      ∀ ⦃V : Opens Y.carrier⦄, V ∈ 𝓑 → (i : ℤ) → i < 0 →
        IsZero (H^i(preimageOpen f V, K)))
    :
    Presheaf.IsSheaf (Opens.grothendieckTopology Y.carrier)
      (preimageObjectwiseCohomologyPresheaf f K 0) := sorry

end ZeroPresheaf

end

end CohomologyPart

section ExtPart

section

-- Proof sketch: apply the cohomology part of the lemma to the derived internal-Hom object
-- `RHom(K, L)`. This is exactly the Chapter 20 degree-zero internal-Hom/Ext
-- bridge on the restricted open subspace.
/-- Lemma 20.45.2 (4): if `K, L ∈ D(𝒪_X)` satisfy
`Ext^i(K|_{f⁻¹(V)}, L|_{f⁻¹(V)}) = 0` for every `V ∈ 𝓑` and every `i < 0`,
then the same vanishing holds for every open subset `V ⊆ Y`. -/
@[stacks 0D66]
theorem preimage_negative_ext_isZero_on_all_opens
    (K L : DModX)
    (h𝓑 : Opens.IsBasis 𝓑)
    (hKL :
      ∀ ⦃V : Opens Y.carrier⦄, V ∈ 𝓑 → (i : ℤ) → i < 0 →
        IsZero (AddCommGrpCat.of (Ext^i(K↾[preimageOpen f V], L↾[preimageOpen f V]))))
    (V : Opens Y.carrier) (i : ℤ) (hi : i < 0) :
    IsZero (AddCommGrpCat.of (Ext^i(K↾[preimageOpen f V], L↾[preimageOpen f V]))) := sorry

section ZeroDerivedHomPresheaf

variable [MonoidalCategory (ModuleDerived X)] [MonoidalClosed (ModuleDerived X)]

/-- On an open subset `V ⊆ Y`, the canonical degree-zero preimage internal-Hom presheaf
`preimageObjectwiseCohomologyPresheaf f (K ⟹ L) 0` is canonically isomorphic, after the standard
universe lift, to the source-facing local derived morphism group
`Hom(K|_{f⁻¹(V)}, L|_{f⁻¹(V)})`. -/
theorem preimageObjectwiseCohomologyPresheaf_internalHom_obj_isomorphic_restrictedDerivedHom
    (K L : DModX) (V : Opens Y.carrier) :
    IsIsomorphic
      ((AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        ((preimageObjectwiseCohomologyPresheaf f (K ⟹ L) 0).obj (Opposite.op V)))
      (AddCommGrpCat.of (K↾[preimageOpen f V] ⟶ L↾[preimageOpen f V])) := by
  rcases
      preimageObjectwiseCohomologyPresheaf_isomorphic_pushforwardObjectwiseCohomologyPresheaf
        f (K ⟹ L) 0 with
    ⟨e₁⟩
  rcases
      pushforwardObjectwiseCohomologyPresheaf_obj_isomorphic_preimageHypercohomology
        f (K ⟹ L) 0 V with
    ⟨e₂⟩
  rcases
    open_zeroHypercohomology_internalHom_isomorphic_restrictedDerivedHom
      (preimageOpen f V) K L
    with ⟨e₃⟩
  exact
    ⟨(AddCommGrpCat.uliftFunctor.mapIso (e₁.app (Opposite.op V))) ≪≫
      (AddCommGrpCat.uliftFunctor.mapIso e₂) ≪≫
      e₃⟩

-- Proof sketch: apply the zero-degree sheaf statement from the cohomology part to the object
-- `RHom(K, L)`. On each open `V`, Lemma `20.42.1` identifies the resulting degree-zero
-- hypercohomology group with the local derived-Hom group.
/-- Lemma 20.45.2 (5): under the same basiswise negative Ext-vanishing hypothesis, the rule
`V ↦ Hom(K|_{f⁻¹(V)}, L|_{f⁻¹(V)})` is a sheaf on `Y`. In Lean this source-facing rule is
expressed by the canonical degree-zero preimage internal-Hom presheaf
`preimageObjectwiseCohomologyPresheaf f (K ⟹ L) 0`, and the companion theorem
`preimageObjectwiseCohomologyPresheaf_internalHom_obj_isomorphic_restrictedDerivedHom`
identifies its sections with the local derived-Hom groups. -/
@[stacks 0D66]
theorem preimage_zero_derivedHom_presheaf_isSheaf
    (K L : DModX)
    (h𝓑 : Opens.IsBasis 𝓑)
    (hKL :
      ∀ ⦃V : Opens Y.carrier⦄, V ∈ 𝓑 → (i : ℤ) → i < 0 →
        IsZero (AddCommGrpCat.of (Ext^i(K↾[preimageOpen f V], L↾[preimageOpen f V]))))
    :
    Presheaf.IsSheaf (Opens.grothendieckTopology Y.carrier)
      (preimageObjectwiseCohomologyPresheaf f (K ⟹ L) 0) := sorry

end ZeroDerivedHomPresheaf

end

end ExtPart

end AlgebraicGeometry.RingedSpace
