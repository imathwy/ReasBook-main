import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_134_1
import stacks_proof.stacks_project.Chap10.Lemma_10_39_3
import stacks_proof.stacks_project.Chap10.Lemma_10_134_11
import stacks_proof.stacks_project.Chap10.Lemma_10_143_3
import stacks_proof.stacks_project.Chap10.Lemma_10_150_4
import stacks_proof.stacks_project.Chap10.Lemma_10_150_7
import stacks_proof.stacks_project.Chap10.Lemma_10_154_3
import stacks_proof.stacks_project.Chap15.Lemma_15_33_5
import stacks_proof.stacks_project.Chap15.Lemma_15_33_7

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open scoped TensorProduct

universe u v

noncomputable section

section

variable {A : Type u} {B : Type u} {Ah : Type u} {Bh : Type u}
variable [CommRing A] [CommRing B] [CommRing Ah] [CommRing Bh]
variable [Algebra A B] [Algebra A Ah] [Algebra B Bh] [Algebra A Bh] [Algebra Ah Bh]
variable [IsScalarTower A B Bh] [IsScalarTower A Ah Bh]

/-
Domain-style sampling for Lemma 15.33.8:
* primary domain: cotangent-homology and Kähler-differential comparison maps for a compatible
  square of commutative rings under ind-étale hypotheses;
* sampled owner declarations:
  - `RingHom.IsFilteredColimitOfEtale`, the chapter owner for ind-étale ring maps;
  - `tensor_presentation_cotangent_h1_to_h1_cotangent`, the source-facing `H^{-1}` map from a
    tensorized naive cotangent complex to cotangent homology;
  - `H1Cotangent.map`, the owner change-of-base map on `H^{-1}`;
  - `KaehlerDifferential.mapBaseChange` and `KaehlerDifferential.map`, the owner maps on degree
    `0`.
* best owner abstraction: the primitive data here are the two cohomology comparison maps induced
  by the source-facing comparison
  `NL_{B/A} ⊗[B] Bh ⟶ NL_{Bh/Ah}`. The current chapter already has canonical owners for these
  induced maps on `H^{-1}` and `H^0`, but not for a general non-flat tensorized morphism in
  `D(Bh)`, so this file should expose those cohomology-level maps directly instead of inventing a
  parallel derived-category owner.

Source/core/bridge triage:
* `source-facing`: the comparison
  `NL_{B/A} ⊗[B] Bh ⟶ NL_{Bh/Ah}` through its induced maps on `H^{-1}` and `H^0`;
* `core/canonical`: `RingHom.IsFilteredColimitOfEtale`,
  `tensor_presentation_cotangent_h1_to_h1_cotangent`, `H1Cotangent.map`,
  `KaehlerDifferential.mapBaseChange`, and `KaehlerDifferential.map`;
* `bridge/view`: the named cohomology comparison composites below.
-/

attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Algebra.H1Cotangent

/-- The degree `-1` comparison
`H₁(NL(P/A) ⊗[B] Bh) → H₁(L_{Bh/Ah})`
attached to a compatible square `A → Ah`, `A → B`, `B → Bh`, `Ah → Bh`, written through the
chapter owners for the presentation-level Jacobi-Zariski map and the change-of-base map. -/
noncomputable abbrev presentationBaseChangeComparison
    (A Ah B Bh : Type u)
    [CommRing A] [CommRing B] [CommRing Ah] [CommRing Bh]
    [Algebra A B] [Algebra A Ah] [Algebra B Bh] [Algebra A Bh] [Algebra Ah Bh]
    [IsScalarTower A B Bh] [IsScalarTower A Ah Bh] {ι : Type v}
    (P : Generators A B ι) :
    LinearMap.ker (LinearMap.baseChange Bh P.toExtension.cotangentComplex) →ₗ[Bh]
      H1Cotangent Ah Bh :=
  (map A Ah Bh Bh).comp (tensor_presentation_cotangent_h1_to_h1_cotangent Bh P)

end Algebra.H1Cotangent

namespace KaehlerDifferential

/-- The degree `0` comparison
`Bh ⊗[B] Ω[B⁄A] → Ω[Bh⁄Ah]`
attached to a compatible square `A → Ah`, `A → B`, `B → Bh`, `Ah → Bh`. -/
noncomputable abbrev baseChangeComparison
    (A Ah B Bh : Type u)
    [CommRing A] [CommRing B] [CommRing Ah] [CommRing Bh]
    [Algebra A B] [Algebra A Ah] [Algebra B Bh] [Algebra A Bh] [Algebra Ah Bh]
    [IsScalarTower A B Bh] [IsScalarTower A Ah Bh] :
    Bh ⊗[B] Ω[B⁄A] →ₗ[Bh] Ω[Bh⁄Ah] :=
  (map A Ah Bh Bh).comp (mapBaseChange A B Bh)

end KaehlerDifferential

/-- Helper for Lemma 15.33.8: tensoring a linear equivalence along a scalar extension keeps the
underlying linear map bijective. -/
theorem baseChange_bijective_of_bijective
    {R : Type u} {S : Type u} {M : Type u} {N : Type u}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Bijective f) :
    Function.Bijective (LinearMap.baseChange S f) := by
  let e : M ≃ₗ[R] N := LinearEquiv.ofBijective f hf
  let g : N →ₗ[R] M := e.symm.toLinearMap
  have hleft : g ∘ₗ f = LinearMap.id := by
    -- The chosen inverse from the linear equivalence is a left inverse to `f`.
    ext x
    change e.symm (e x) = x
    exact e.symm_apply_apply x
  have hright : f ∘ₗ g = LinearMap.id := by
    -- The same inverse is also a right inverse to `f`.
    ext y
    change e (e.symm y) = y
    exact e.apply_symm_apply y
  have hbase_left :
      (LinearMap.baseChange S g) ∘ₗ (LinearMap.baseChange S f) = LinearMap.id := by
    -- Base change preserves the left-inverse identity.
    have hleft' :
        LinearMap.baseChange S (g ∘ₗ f) =
          LinearMap.baseChange S (LinearMap.id : M →ₗ[R] M) := by
      exact congrArg (LinearMap.baseChange S) hleft
    calc
      (LinearMap.baseChange S g) ∘ₗ (LinearMap.baseChange S f)
          = LinearMap.baseChange S (g ∘ₗ f) := by
              rw [← LinearMap.baseChange_comp]
      _ = LinearMap.baseChange S (LinearMap.id : M →ₗ[R] M) := hleft'
      _ = LinearMap.id := by
            simpa using (LinearMap.baseChange_id (R := R) (A := S) (M := M))
  have hbase_right :
      (LinearMap.baseChange S f) ∘ₗ (LinearMap.baseChange S g) = LinearMap.id := by
    -- Base change preserves the right-inverse identity.
    have hright' :
        LinearMap.baseChange S (f ∘ₗ g) =
          LinearMap.baseChange S (LinearMap.id : N →ₗ[R] N) := by
      exact congrArg (LinearMap.baseChange S) hright
    calc
      (LinearMap.baseChange S f) ∘ₗ (LinearMap.baseChange S g)
          = LinearMap.baseChange S (f ∘ₗ g) := by
              rw [← LinearMap.baseChange_comp]
      _ = LinearMap.baseChange S (LinearMap.id : N →ₗ[R] N) := hright'
      _ = LinearMap.id := by
            simpa using (LinearMap.baseChange_id (R := R) (A := S) (M := N))
  refine ⟨?_, ?_⟩
  · -- A left inverse after base change makes the tensorized map injective.
    exact Function.LeftInverse.injective (f := LinearMap.baseChange S f) <| by
      intro x
      exact LinearMap.congr_fun hbase_left x
  · -- A right inverse after base change makes the tensorized map surjective.
    exact Function.RightInverse.surjective (f := LinearMap.baseChange S f) <| by
      intro x
      exact LinearMap.congr_fun hbase_right x

/-- Helper for Lemma 15.33.8: a filtered colimit of étale ring maps is also a filtered colimit of
local complete intersection ring maps. -/
theorem isFilteredColimitOfLocalCompleteIntersection_of_isFilteredColimitOfEtale
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hS : (algebraMap R S).IsFilteredColimitOfEtale) :
    (algebraMap R S).IsFilteredColimitOfLocalCompleteIntersection := by
  -- Route correction: keep the hidden filtered-colimit presentation fixed and only replace each
  -- étale stage by its local-complete-intersection consequence.
  dsimp [RingHom.IsFilteredColimitOfEtale, RingHom.IsFilteredColimitOfLocalCompleteIntersection]
    at hS ⊢
  rcases hS with ⟨J, _, hJ, D, t, s, hs, hstage⟩
  refine ⟨J, inferInstance, hJ, D, t, s, hs, ?_⟩
  intro j
  refine ⟨?_, (hstage j).2⟩
  let _ : Algebra (ULift.{u} R) (D.obj j) := (t.app j).hom.toAlgebra
  have hEtaleAlg : Algebra.Etale (ULift.{u} R) (D.obj j) := by
    exact (RingHom.etale_algebraMap (R := ULift.{u} R) (S := D.obj j)).mp <| by
      simpa [CommRingCat.etale] using (hstage j).1
  letI : Algebra.Etale (ULift.{u} R) (D.obj j) := hEtaleAlg
  have hStageSyntomic :
      (algebraMap (ULift.{u} R) (D.obj j)).Syntomic :=
    Algebra.etale_syntomic
  have hStageLci :
      RingHom.IsLocalCompleteIntersection (algebraMap (ULift.{u} R) (D.obj j)) :=
    (RingHom.Syntomic.iff_flat_and_isLocalCompleteIntersection
      (algebraMap (ULift.{u} R) (D.obj j))).mp hStageSyntomic |>.2
  -- Read the stage property back through the `RingHom.toMorphismProperty` wrapper.
  simpa [RingHom.toMorphismProperty, RingHom.algebraMap_toAlgebra] using hStageLci

/-- Helper for Lemma 15.33.8: for an étale algebra `R → S`, the self-presentation differential of
the naive cotangent complex is bijective. -/
theorem etale_self_presentation_cotangentComplex_bijective
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.Etale R S] :
    Function.Bijective ((Generators.self R S).toExtension.cotangentComplex) := by
  let P : Algebra.Extension R S := (Generators.self R S).toExtension
  refine ⟨?_, ?_⟩
  · -- Vanishing of `H^{-1}` for étale algebras identifies the kernel with zero.
    exact (Algebra.Extension.subsingleton_h1Cotangent P).mp inferInstance
  · intro x
    -- Vanishing of Kähler differentials makes every cotangent-space element a boundary.
    have hx : x ∈ LinearMap.ker P.toKaehler := by
      change P.toKaehler x = 0
      exact Subsingleton.elim _ _
    have hexact := (LinearMap.exact_iff).mp P.exact_cotangentComplex_toKaehler
    rw [hexact] at hx
    exact hx

/-- Helper for Lemma 15.33.8: for a formally étale algebra `R → S`, the self-presentation
differential of the naive cotangent complex is bijective. -/
theorem formallyEtale_self_presentation_cotangentComplex_bijective
    {R : Type u} {S : Type u}
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallyEtale R S] :
    Function.Bijective ((Generators.self R S).toExtension.cotangentComplex) := by
  let P : Algebra.Extension R S := (Generators.self R S).toExtension
  letI : Subsingleton P.H1Cotangent := by
    -- Formal smoothness kills `H^{-1}(L_{S/R})`, and the self-presentation identifies with it.
    change Subsingleton (H1Cotangent R S)
    infer_instance
  letI : Subsingleton Ω[S⁄R] := by
    -- Formal unramifiedness kills the Kähler differentials of a formally étale map.
    infer_instance
  refine ⟨?_, ?_⟩
  · -- Vanishing of `H^{-1}` for étale algebras identifies the kernel with zero.
    exact (Algebra.Extension.subsingleton_h1Cotangent P).mp inferInstance
  · intro x
    -- Vanishing of Kähler differentials makes every cotangent-space element a boundary.
    have hx : x ∈ LinearMap.ker P.toKaehler := by
      change P.toKaehler x = 0
      exact Subsingleton.elim _ _
    have hexact := (LinearMap.exact_iff).mp P.exact_cotangentComplex_toKaehler
    rw [hexact] at hx
    exact hx

/-- Helper for Lemma 15.33.8: after any scalar extension `S → T`, the tensorized differential in
the self-presentation of an étale algebra `R → S` stays bijective. -/
theorem etale_self_baseChange_cotangentComplex_bijective
    {R : Type u} {S : Type u} {T : Type u}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.Etale R S] :
    Function.Bijective
      (LinearMap.baseChange T (Generators.self R S).toExtension.cotangentComplex) := by
  -- The étale self-presentation differential is already an isomorphism before tensoring.
  exact baseChange_bijective_of_bijective
    (S := T) (Generators.self R S).toExtension.cotangentComplex
    (etale_self_presentation_cotangentComplex_bijective (R := R) (S := S))

/-- Helper for Lemma 15.33.8: after any scalar extension `S → T`, the tensorized differential in
the self-presentation of a formally étale algebra `R → S` stays bijective. -/
theorem formallyEtale_self_baseChange_cotangentComplex_bijective
    {R : Type u} {S : Type u} {T : Type u}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallyEtale R S] :
    Function.Bijective
      (LinearMap.baseChange T (Generators.self R S).toExtension.cotangentComplex) := by
  -- The étale self-presentation differential is already an isomorphism before tensoring.
  exact baseChange_bijective_of_bijective
    (S := T) (Generators.self R S).toExtension.cotangentComplex
    (formallyEtale_self_presentation_cotangentComplex_bijective (R := R) (S := S))

/-- Helper for Lemma 15.33.8: the left Jacobi-Zariski term attached to an étale source map
vanishes already at the level of cycles after any scalar extension. -/
theorem etale_self_baseChange_cotangentComplex_ker_subsingleton
    {R : Type u} {S : Type u} {T : Type u}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.Etale R S] :
    Subsingleton
      (LinearMap.ker (LinearMap.baseChange T (Generators.self R S).toExtension.cotangentComplex)) :=
  let h :=
    etale_self_baseChange_cotangentComplex_bijective
      (R := R) (S := S) (T := T)
  ⟨fun x y ↦ by
    -- Injectivity of the tensorized differential forces any two cycles to coincide.
    apply Subtype.ext
    exact h.1 <| by simpa [x.2, y.2]⟩

/-- Helper for Lemma 15.33.8: the left Jacobi-Zariski term attached to a formally étale source map
vanishes already at the level of cycles after any scalar extension. -/
theorem formallyEtale_self_baseChange_cotangentComplex_ker_subsingleton
    {R : Type u} {S : Type u} {T : Type u}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallyEtale R S] :
    Subsingleton
      (LinearMap.ker (LinearMap.baseChange T (Generators.self R S).toExtension.cotangentComplex)) :=
  let h :=
    formallyEtale_self_baseChange_cotangentComplex_bijective
      (R := R) (S := S) (T := T)
  ⟨fun x y ↦ by
    -- Injectivity of the tensorized differential forces any two cycles to coincide.
    apply Subtype.ext
    exact h.1 <| by simpa [x.2, y.2]⟩

/-- Helper for Lemma 15.33.8: in an exact pair `L ⟶ M ⟶ N`, a subsingleton source forces the
second map to be injective. -/
theorem h1_map_injective_of_exact_of_subsingleton_source
    {K : Type u} {L : Type u} {M : Type u} {N : Type u}
    [CommRing K] [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module K L] [Module K M] [Module K N]
    (α : L →ₗ[K] M) (β : M →ₗ[K] N)
    (hExact : Function.Exact α β) (hL : Subsingleton L) :
    Function.Injective β := by
  let _ : Subsingleton L := hL
  intro x y hxy
  -- Exactness identifies `x - y` with the image of the vanishing left term.
  have hker : x - y ∈ LinearMap.ker β := by
    rw [LinearMap.mem_ker]
    simp [map_sub, hxy]
  rw [hExact.linearMap_ker_eq] at hker
  rcases hker with ⟨z, hz⟩
  have hz0 : z = 0 := Subsingleton.elim _ _
  have hsub : x - y = 0 := by
    simpa [hz0] using hz.symm
  exact sub_eq_zero.mp hsub

/-- Helper for Lemma 15.33.8: once the source-facing left Jacobi-Zariski row is exact, an étale
source map makes the owner change-of-source map on `H^{-1}` injective because the left term
already vanishes after base change. -/
theorem etale_source_change_h1_injective_of_left_exact
    {R : Type u} {S : Type u} {T : Type u}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.Etale R S]
    (hExact :
      Function.Exact
        (tensor_presentation_cotangent_h1_to_h1_cotangent T (Generators.self R S))
        (H1Cotangent.map R S T T)) :
    Function.Injective (H1Cotangent.map R S T T) := by
  -- The new algebraic helper closes the row as soon as the exactness owner is available.
  exact h1_map_injective_of_exact_of_subsingleton_source
    (tensor_presentation_cotangent_h1_to_h1_cotangent T (Generators.self R S))
    (H1Cotangent.map R S T T) hExact
    (etale_self_baseChange_cotangentComplex_ker_subsingleton
      (R := R) (S := S) (T := T))

/-- Helper for Lemma 15.33.8: once the source-facing left Jacobi-Zariski row is exact, a formally
étale source map makes the owner change-of-source map on `H^{-1}` injective because the left term
already vanishes after base change. -/
theorem formallyEtale_source_change_h1_injective_of_left_exact
    {R : Type u} {S : Type u} {T : Type u}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallyEtale R S]
    (hExact :
      Function.Exact
        (tensor_presentation_cotangent_h1_to_h1_cotangent T (Generators.self R S))
        (H1Cotangent.map R S T T)) :
    Function.Injective (H1Cotangent.map R S T T) := by
  -- The same exactness-to-injectivity argument now uses only formal étaleness of the source.
  exact h1_map_injective_of_exact_of_subsingleton_source
    (tensor_presentation_cotangent_h1_to_h1_cotangent T (Generators.self R S))
    (H1Cotangent.map R S T T) hExact
    (formallyEtale_self_baseChange_cotangentComplex_ker_subsingleton
      (R := R) (S := S) (T := T))

/-- Helper for Lemma 15.33.8: when `S → T` is a filtered colimit of local complete intersection
maps, the left Jacobi-Zariski row for the self-presentation of `S` over `R` is exact on the raw
owner maps `H₁(NL_{S/R} ⊗[S] T) → H¹(L_{T/R}) → H¹(L_{T/S})`. -/
theorem jacobi_zariski_h1_exact_of_filteredColimitOfLocalCompleteIntersection_target
    {R : Type u} {S : Type u} {T : Type u}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (hT : (algebraMap S T).IsFilteredColimitOfLocalCompleteIntersection) :
    Function.Exact
      (tensor_presentation_cotangent_h1_to_h1_cotangent T (Generators.self R S))
      (H1Cotangent.map R S T T) := by
  have hInjExact :
      Function.Injective
          (tensor_presentation_cotangent_h1_to_h1_cotangent T (Generators.self R S)) ∧
        (presentationJacobiZariskiLeftSequence T (Generators.self R S)).Exact :=
    presentation_jacobi_zariski_exact_sequence_with_zero_left_of_isFilteredColimitOfLocalCompleteIntersection
      (P := Generators.self R S) hT
  let α :
      LinearMap.ker
          (LinearMap.baseChange T (Generators.self R S).toExtension.cotangentComplex) →ₗ[T]
        ULift.{u, u} (H1Cotangent R T) :=
    (ULift.moduleEquiv :
      ULift.{u, u} (H1Cotangent R T) ≃ₗ[T] H1Cotangent R T).symm.toLinearMap ∘ₗ
      tensor_presentation_cotangent_h1_to_h1_cotangent T (Generators.self R S)
  let β :
      ULift.{u, u} (H1Cotangent R T) →ₗ[T]
        ULift.{u, u} (H1Cotangent S T) :=
    (ULift.moduleEquiv :
      ULift.{u, u} (H1Cotangent S T) ≃ₗ[T] H1Cotangent S T).symm.toLinearMap ∘ₗ
      H1Cotangent.map R S T T ∘ₗ
      (ULift.moduleEquiv : ULift.{u, u} (H1Cotangent R T) ≃ₗ[T] H1Cotangent R T).toLinearMap
  have hExactPackaged : Function.Exact α β := by
    -- Read the packaged `ShortComplex` exactness as exactness of its underlying functions.
    simpa [presentationJacobiZariskiLeftSequence, α, β] using
      (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (presentationJacobiZariskiLeftSequence T (Generators.self R S))).1 hInjExact.2
  have h₁₂ :
      α ∘ₗ
          (LinearEquiv.refl T
            (LinearMap.ker
              (LinearMap.baseChange T (Generators.self R S).toExtension.cotangentComplex))).symm.toLinearMap =
        (ULift.moduleEquiv :
          ULift.{u, u} (H1Cotangent R T) ≃ₗ[T] H1Cotangent R T).symm.toLinearMap ∘ₗ
          tensor_presentation_cotangent_h1_to_h1_cotangent T (Generators.self R S) := by
    -- The left term is unchanged; only the middle term carries the `ULift` packaging.
    ext x
    rfl
  have h₂₃ :
      β ∘ₗ
          (ULift.moduleEquiv :
            ULift.{u, u} (H1Cotangent R T) ≃ₗ[T] H1Cotangent R T).symm.toLinearMap =
        (ULift.moduleEquiv :
          ULift.{u, u} (H1Cotangent S T) ≃ₗ[T] H1Cotangent S T).symm.toLinearMap ∘ₗ
          H1Cotangent.map R S T T := by
    -- Likewise on the right, the only change is the outer `ULift` identification.
    ext x
    rfl
  -- Transport exactness from the packaged `ULift` row back to the raw owner maps.
  exact (Function.Exact.iff_of_ladder_linearEquiv h₁₂ h₂₃).1 hExactPackaged

/-- Helper for Lemma 15.33.8: if `S → T` is a filtered colimit of étale algebras, then the
target-change map from the tensorized naive cotangent complex of `R → S` to `H^{-1}(L_{T/R})`
is bijective. -/
theorem filteredColimitOfEtale_tensor_presentation_h1_bijective
    {R : Type u} {S : Type u} {T : Type u}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (hT : (algebraMap S T).IsFilteredColimitOfEtale) :
    Function.Bijective
      (tensor_presentation_cotangent_h1_to_h1_cotangent T (Generators.self R S)) := by
  -- The source proof first gets injectivity and left exactness from the ind-lci Jacobi-Zariski
  -- row for `S → T`, then upgrades exactness to surjectivity because `S → T` is formally étale.
  letI : Algebra.FormallyEtale S T := (RingHom.formallyEtale_algebraMap).mp
    (RingHom.formallyEtale_of_isFilteredColimitOfEtale hT)
  have hLci :
      (algebraMap S T).IsFilteredColimitOfLocalCompleteIntersection :=
    isFilteredColimitOfLocalCompleteIntersection_of_isFilteredColimitOfEtale hT
  have hInj :
      Function.Injective
        (tensor_presentation_cotangent_h1_to_h1_cotangent T (Generators.self R S)) :=
    presentation_jacobi_zariski_exact_sequence_with_zero_left_of_isFilteredColimitOfLocalCompleteIntersection
      (P := Generators.self R S) hLci |>.1
  have hExact :
      Function.Exact
        (tensor_presentation_cotangent_h1_to_h1_cotangent T (Generators.self R S))
        (H1Cotangent.map R S T T) :=
    jacobi_zariski_h1_exact_of_filteredColimitOfLocalCompleteIntersection_target
      (R := R) (S := S) (T := T) hLci
  refine ⟨hInj, ?_⟩
  intro y
  -- Formal étaleness kills the right-hand term, so exactness makes the left map surjective.
  have hy0 : H1Cotangent.map R S T T y = 0 := by
    exact Subsingleton.elim _ _
  exact (hExact y).1 hy0

/-- Helper for Lemma 15.33.8: if the source map `R → S` is formally étale, then the
Jacobi-Zariski map on `H^{-1}` is surjective for every compatible `S`-algebra `T`. -/
theorem source_change_h1_surjective_of_formallyEtale
    {R : Type u} {S : Type u} {T : Type u}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallyEtale R S] :
    Function.Surjective (H1Cotangent.map R S T T) := by
  intro y
  -- The Kähler source term vanishes for formally étale maps, so exactness produces a preimage.
  have hy0 : H1Cotangent.δ R S T y = 0 := by
    exact Subsingleton.elim _ _
  exact (H1Cotangent.exact_map_δ R S T y).1 hy0

/-- Helper for Lemma 15.33.8: an étale source map already makes the owner change-of-source map on
`H^{-1}` surjective for every compatible target algebra. -/
theorem etale_source_change_h1_surjective
    {R : Type u} {S : Type u} {T : Type u}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.Etale R S] :
    Function.Surjective (H1Cotangent.map R S T T) := by
  -- Étale maps are formally étale, so the surjectivity statement is exactly the owner theorem
  -- already proved for formally étale source maps.
  letI : Algebra.FormallyEtale R S := inferInstance
  exact source_change_h1_surjective_of_formallyEtale (R := R) (S := S) (T := T)

section IndEtaleFlat

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Under
open CommRingCat

/-- Helper for Lemma 15.33.8: an `ind` presentation of a ring map lifts canonically to the
under-category over the fixed source ring. -/
private abbrev ind_underFunctor {R : CommRingCat.{u}} {J : Type u} [SmallCategory J]
    (D : J ⥤ CommRingCat.{u}) (t : (Functor.const J).obj R ⟶ D) :
    J ⥤ Under R :=
  { obj := fun j ↦ Under.mk (t.app j)
    map := fun {i j} g ↦ Under.homMk (D.map g) (by
      -- The `Under` morphism condition is exactly the naturality square of `t`.
      simpa using (t.naturality g).symm) }

/-- Helper for Lemma 15.33.8: the target cocone of an `ind` presentation lifts to the matching
under-category cocone. -/
private abbrev ind_underCocone {R S : CommRingCat.{u}} {J : Type u} [SmallCategory J]
    (D : J ⥤ CommRingCat.{u}) (t : (Functor.const J).obj R ⟶ D)
    (s : D ⟶ (Functor.const J).obj S) (f : R ⟶ S)
    (hcompat : ∀ j : J, t.app j ≫ s.app j = f) :
    Cocone (ind_underFunctor (R := R) D t) :=
  { pt := Under.mk f
    ι :=
      { app := fun j ↦ Under.homMk (s.app j) (hcompat j)
        naturality := by
          intro i j g
          -- Equality in `Under` reduces to equality of the right components.
          refine CategoryTheory.CommaMorphism.ext rfl ?_
          simpa using s.naturality g } }

/-- Helper for Lemma 15.33.8: a colimit cocone in rings remains colimiting after lifting the same
`ind` presentation to the under-category. -/
private noncomputable def ind_underCocone_isColimit_of_isColimit
    {R S : CommRingCat.{u}} {J : Type u} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{u}) (t : (Functor.const J).obj R ⟶ D)
    (s : D ⟶ (Functor.const J).obj S) (f : R ⟶ S)
    (hcompat : ∀ j : J, t.app j ≫ s.app j = f)
    (hs : IsColimit (Cocone.mk S s)) :
    IsColimit (ind_underCocone D t s f hcompat) := by
  classical
  refine IsColimit.mk ?_ ?_ ?_
  · intro c
    let j₀ : J := Classical.choice (CategoryTheory.IsFiltered.nonempty (C := J))
    refine Under.homMk (hs.desc ((Under.forget R).mapCocone c)) ?_
    -- One stage equation reduces the `Under` condition to the ordinary colimit desc map.
    change f ≫ hs.desc ((Under.forget R).mapCocone c) = c.pt.hom
    rw [← hcompat j₀]
    have hfac₀ :
        s.app j₀ ≫ hs.desc ((Under.forget R).mapCocone c) = (c.ι.app j₀).right := by
      simpa using hs.fac ((Under.forget R).mapCocone c) j₀
    have hdesc :
        (t.app j₀ ≫ s.app j₀) ≫ hs.desc ((Under.forget R).mapCocone c) =
          t.app j₀ ≫ (c.ι.app j₀).right := by
      calc
        (t.app j₀ ≫ s.app j₀) ≫ hs.desc ((Under.forget R).mapCocone c) =
            t.app j₀ ≫ (s.app j₀ ≫ hs.desc ((Under.forget R).mapCocone c)) := by
              simp [Category.assoc]
        _ = t.app j₀ ≫ (c.ι.app j₀).right := by
              exact congrArg (fun z ↦ t.app j₀ ≫ z) hfac₀
    exact hdesc.trans <| by
      simpa using (c.ι.app j₀).w.symm
  · intro c j
    -- Forgetting to rings exposes the usual colimit `fac` equation on the chosen stage.
    refine CategoryTheory.CommaMorphism.ext rfl ?_
    simpa using hs.fac ((Under.forget R).mapCocone c) j
  · intro c m hm
    -- Uniqueness is checked after forgetting to rings, where `hs` already controls the desc map.
    refine CategoryTheory.CommaMorphism.ext rfl ?_
    apply hs.hom_ext
    intro j
    have hmj :
        s.app j ≫ m.right = (c.ι.app j).right := by
      simpa [ind_underCocone] using congrArg CategoryTheory.CommaMorphism.right (hm j)
    have hfac :
        s.app j ≫ hs.desc ((Under.forget R).mapCocone c) = (c.ι.app j).right := by
      simpa using hs.fac ((Under.forget R).mapCocone c) j
    exact hmj.trans hfac.symm

/-- Helper for Lemma 15.33.8: forgetting a commutative ring under `R` to its underlying
`R`-module. -/
private abbrev under_forget_to_module (R : CommRingCat.{u}) : Under R ⥤ ModuleCat R where
  obj S := ModuleCat.of R S
  map f := ModuleCat.ofHom (CommRingCat.toAlgHom f).toLinearMap

/-- Helper for Lemma 15.33.8: an object under `CommRingCat.of R` carries the canonical
`R`-module structure induced by its structure map. -/
private instance under_module (R : Type u) [CommRing R] (S : Under (CommRingCat.of R)) :
    Module R S := by
  let _ : Algebra R S.right := S.hom.hom.toAlgebra
  infer_instance

/-- Helper for Lemma 15.33.8: a filtered colimit in `Under (CommRingCat.of R)` is flat once every
stage is flat over the fixed base ring `R`. -/
private theorem under_colimit_flat_of_stagewise_flat {R : Type u} [CommRing R]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of R)) (c : Cocone F) (hc : IsColimit c)
    [∀ j, Module.Flat R (F.obj j)] :
    Module.Flat R c.pt.right := by
  let cM := (under_forget_to_module (CommRingCat.of R)).mapCocone c
  letI : ∀ j, Module.Flat R ((F ⋙ under_forget_to_module (CommRingCat.of R)).obj j) :=
    fun j ↦ by
      simpa [under_forget_to_module] using (inferInstance : Module.Flat R (F.obj j))
  have hcM : IsColimit cM := by
    -- Forget to additive groups, preserve the filtered colimit there, then reflect it back.
    apply isColimitOfReflects (forget₂ (ModuleCat R) AddCommGrpCat)
    simpa [under_forget_to_module] using
      (isColimitOfPreserves
        (CategoryTheory.Under.forget (CommRingCat.of R) ⋙
          forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) hc)
  -- Apply the filtered-colimit flatness theorem to the transported module diagram.
  simpa using
    flat_of_isColimit_filtered_system
      (F := F ⋙ under_forget_to_module (CommRingCat.of R)) cM hcM

/-- Helper for Lemma 15.33.8: a filtered colimit of étale algebras is flat over the base ring. -/
private theorem flat_of_isFilteredColimitOfEtale
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hS : (algebraMap R S).IsFilteredColimitOfEtale) :
    Module.Flat R S := by
  let _ : Algebra R (ULift S) := ULift.algebra
  let _ : Algebra (ULift.{u} R) (ULift S) := ULift.algebra' R (ULift S)
  -- Route correction: keep the source-proof on the same hidden filtered presentation and pass
  -- stagewise étale flatness through the under-category colimit once.
  dsimp [RingHom.IsFilteredColimitOfEtale] at hS
  rcases hS with ⟨J, _, _, D, t, s, hs, hstage⟩
  let F := ind_underFunctor (R := CommRingCat.of (ULift.{u} R)) D t
  let cUnder :=
    ind_underCocone D t s
      (CommRingCat.ofHom (algebraMap (ULift.{u} R) (ULift S)))
      (fun j ↦ (hstage j).2)
  have hsUnder : IsColimit cUnder := by
    -- The filtered colimit presentation lifts from rings to rings under the fixed base.
    exact ind_underCocone_isColimit_of_isColimit
      (D := D) (t := t) (s := s)
      (f := CommRingCat.ofHom (algebraMap (ULift.{u} R) (ULift S)))
      (hcompat := fun j ↦ (hstage j).2) hs
  letI : ∀ j, Module.Flat (ULift.{u} R) (F.obj j) :=
    fun j ↦ by
      let _ : Algebra (ULift.{u} R) (D.obj j) := (t.app j).hom.toAlgebra
      have hEtale : (t.app j).hom.Etale := by
        -- Each stage map in the chosen presentation is étale by construction.
        simpa [CommRingCat.etale] using (hstage j).1
      have hflatStageHom : (algebraMap (ULift.{u} R) (D.obj j)).Flat := by
        have hflat : (t.app j).hom.Flat :=
          (RingHom.Etale.iff_flat_and_formallyUnramified (f := (t.app j).hom)).mp hEtale |>.1
        simpa [RingHom.algebraMap_toAlgebra] using hflat
      have hflatStage : Module.Flat (ULift.{u} R) (D.obj j) :=
        RingHom.flat_algebraMap_iff.mp hflatStageHom
      simpa [F, ind_underFunctor] using hflatStage
  have hflatUpUnder : Module.Flat (ULift.{u} R) cUnder.pt.right := by
    -- Stagewise étale flatness now feeds into the filtered-colimit flatness theorem.
    exact under_colimit_flat_of_stagewise_flat (R := ULift.{u} R) F cUnder hsUnder
  let _ : Algebra (ULift.{u} R) cUnder.pt.right := cUnder.pt.hom.hom.toAlgebra
  have hflatUpUnderHom : (algebraMap (ULift.{u} R) cUnder.pt.right).Flat :=
    (RingHom.flat_algebraMap_iff (R := ULift.{u} R) (S := cUnder.pt.right)).mpr hflatUpUnder
  have hflatUp : (algebraMap (ULift.{u} R) (ULift S)).Flat := by
    -- Unfold the cocone point once to identify its algebra map with the canonical `ULift` map.
    simpa [cUnder, ind_underCocone] using hflatUpUnderHom
  have hsource :
      ((ULift.ringEquiv.symm : R ≃+* ULift.{u} R).toRingHom).Flat :=
    RingHom.Flat.of_bijective (ULift.ringEquiv.symm : R ≃+* ULift.{u} R).bijective
  have htarget :
      ((ULift.ringEquiv : ULift S ≃+* S).toRingHom).Flat :=
    RingHom.Flat.of_bijective (ULift.ringEquiv : ULift S ≃+* S).bijective
  have hcomp :
      (((ULift.ringEquiv : ULift S ≃+* S).toRingHom).comp
        ((algebraMap (ULift.{u} R) (ULift S)).comp
          ((ULift.ringEquiv.symm : R ≃+* ULift.{u} R).toRingHom))).Flat := by
    -- Flatness is stable under composition with the two `ULift` equivalences.
    exact RingHom.Flat.comp (RingHom.Flat.comp hsource hflatUp) htarget
  have hEq :
      ((ULift.ringEquiv : ULift S ≃+* S).toRingHom).comp
        ((algebraMap (ULift.{u} R) (ULift S)).comp
          ((ULift.ringEquiv.symm : R ≃+* ULift.{u} R).toRingHom)) =
        algebraMap R S := by
    -- The transported composite is definitionally the original structure map.
    ext x
    rfl
  have hflatRS : (algebraMap R S).Flat := by
    rw [← hEq]
    exact hcomp
  exact RingHom.flat_algebraMap_iff.mp hflatRS

/-- Helper for Lemma 15.33.8: if the source map `R → R'` is flat, then for any compatible
`R'`-algebra `T` the canonical source-change map on `H^{-1}` is bijective. -/
private theorem h1Cotangent_map_bijective_of_flat_source
    {R : Type u} {R' : Type u} {T : Type u}
    [CommRing R] [CommRing R'] [CommRing T]
    [Algebra R R'] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T]
    [Module.Flat R R'] :
    Function.Bijective (H1Cotangent.map R R' T T) := by
  let e :
      H1Cotangent R T ≃ₗ[R'] H1Cotangent R' T :=
    (Algebra.TensorProduct.lidOfCompatibleSMul R R' (H1Cotangent R T)).toLinearEquiv.symm.trans
      ((Algebra.tensorH1CotangentOfFlat R T R').trans
        (H1Cotangent.mapEquiv R' (R' ⊗[R] T) T
          (Algebra.TensorProduct.lidOfCompatibleSMul R R' T)))
  have h : ∀ x, e x = H1Cotangent.map R R' T T x := by
    intro x
    rw [show (Algebra.TensorProduct.lidOfCompatibleSMul R R' (H1Cotangent R T)).toLinearEquiv.symm x =
        1 ⊗ₜ[R] x by rfl]
    rw [Algebra.tensorH1CotangentOfFlat_tmul, one_smul]
    let eT : R' ⊗[R] T ≃ₐ[R'] T := Algebra.TensorProduct.lidOfCompatibleSMul R R' T
    letI : Algebra T (R' ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
    letI := eT.toRingHom.toAlgebra
    letI : IsScalarTower R' (R' ⊗[R] T) T :=
      .of_algebraMap_eq' (((eT : R' ⊗[R] T →ₐ[R'] T)).comp_algebraMap).symm
    letI : IsScalarTower T (R' ⊗[R] T) T := .of_algebraMap_eq fun t ↦ by
      change t = eT (1 ⊗ₜ[R] t)
      simpa using (Algebra.TensorProduct.lidOfCompatibleSMul_tmul R R' T (1 : R') t).symm
    simp only [H1Cotangent.mapEquiv, LinearEquiv.coe_mk, H1Cotangent.map]
    let f₁ := ((Generators.self R T).defaultHom (Generators.self R' (R' ⊗[R] T))).toExtensionHom
    let f₂ := ((Generators.self R' (R' ⊗[R] T)).defaultHom (Generators.self R' T)).toExtensionHom
    let f := ((Generators.self R T).defaultHom (Generators.self R' T)).toExtensionHom
    have hcomp := (Extension.H1Cotangent.map_comp_apply f₁ f₂ x).symm
    have hEq : Extension.H1Cotangent.map (f₂.comp f₁) = Extension.H1Cotangent.map f :=
      Extension.H1Cotangent.map_eq _ _
    exact hcomp.trans (by simpa using congrArg (fun g ↦ g x) hEq)
  have hmap : (e : H1Cotangent R T → H1Cotangent R' T) = H1Cotangent.map R R' T T := funext h
  simpa [hmap] using e.bijective

end IndEtaleFlat

/-- Helper for Lemma 15.33.8: if `R → R'` is a filtered colimit of étale algebras, then for any
compatible `R'`-algebra `T` the canonical source-change map on `H^{-1}` is bijective. -/
theorem filteredColimitOfEtale_source_change_h1_bijective
    {R : Type u} {R' : Type u} {T : Type u}
    [CommRing R] [CommRing R'] [CommRing T]
    [Algebra R R'] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T]
    (hR' : (algebraMap R R').IsFilteredColimitOfEtale) :
    Function.Bijective (H1Cotangent.map R R' T T) := by
  -- Route correction: the source proof makes the ind-étale source acyclic; here we realize the
  -- same closure route through the earlier flat-base-change owner theorem after deriving flatness
  -- from the hidden filtered étale presentation.
  letI : Module.Flat R R' := flat_of_isFilteredColimitOfEtale (R := R) (S := R') hR'
  exact h1Cotangent_map_bijective_of_flat_source (R := R) (R' := R') (T := T)

/-- Helper for Lemma 15.33.8: if `R → R'` is a filtered colimit of étale algebras, then for any
compatible `R'`-algebra `T` the canonical source-change map `Ω[T⁄R] → Ω[T⁄R']` is bijective. -/
theorem filteredColimitOfEtale_source_change_kaehler_bijective
    {R : Type u} {R' : Type u} {T : Type u}
    [CommRing R] [CommRing R'] [CommRing T]
    [Algebra R R'] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T]
    (hR' : (algebraMap R R').IsFilteredColimitOfEtale) :
    Function.Bijective (KaehlerDifferential.map R R' T T) := by
  letI : Algebra.FormallyEtale R R' := (RingHom.formallyEtale_algebraMap).mp
    (RingHom.formallyEtale_of_isFilteredColimitOfEtale hR')
  refine ⟨?_, KaehlerDifferential.map_surjective R R' T⟩
  intro x y hxy
  -- The Jacobi-Zariski tail makes the kernel exactly the image of the vanishing source term.
  have hzero : KaehlerDifferential.map R R' T T (x - y) = 0 := by
    simp [map_sub, hxy]
  obtain ⟨z, hz⟩ := (KaehlerDifferential.exact_mapBaseChange_map R R' T (x - y)).mp hzero
  have hz0 : z = 0 := Subsingleton.elim _ _
  have hsub : x - y = 0 := by
    simpa [hz0] using hz.symm
  exact sub_eq_zero.mp hsub

-- Proof sketch: `A → Ah` and `B → Bh` being filtered colimits of étale algebras makes
-- `NL_{Ah/A}` and `NL_{Bh/B}` acyclic. Apply the Jacobi-Zariski sequence to `A → Ah → Bh` to
-- identify `NL_{Bh/A}` and `NL_{Bh/Ah}` on cohomology, then apply Lemma `15.33.7` to
-- `A → B → Bh`, using that étale maps are local complete intersections, to identify
-- `NL_{B/A} ⊗[B] Bh` and `NL_{Bh/A}` on cohomology. Composing these identifications gives the
-- stated bijectivity in degrees `1` and `0`. 
/-- Lemma 15.33.8, degree `-1`: if `A → Ah` and `B → Bh` are filtered colimits of étale
algebras compatible with `A → B`, then the canonical comparison
`NL_{B/A} ⊗[B] Bh → NL_{Bh/Ah}` induces a bijection on `H^{-1}`. -/
@[stacks 0D08]
theorem naiveCotangentFilteredColimitOfEtaleComparison_h1_bijective
    (hAh : (algebraMap A Ah).IsFilteredColimitOfEtale)
    (hBh : (algebraMap B Bh).IsFilteredColimitOfEtale) :
    Function.Bijective
      (H1Cotangent.presentationBaseChangeComparison A Ah B Bh (Generators.self A B)) := by
  have hSource :
      Function.Bijective (H1Cotangent.map A Ah Bh Bh) :=
    filteredColimitOfEtale_source_change_h1_bijective
      (R := A) (R' := Ah) (T := Bh) hAh
  -- First compare `H₁(NL_{B/A} ⊗[B] Bh)` with `H¹(L_{Bh/A})` via the target ind-étale map
  -- `B → Bh`.
  have hTarget :
      Function.Bijective
        (tensor_presentation_cotangent_h1_to_h1_cotangent Bh (Generators.self A B)) :=
    filteredColimitOfEtale_tensor_presentation_h1_bijective
      (R := A) (S := B) (T := Bh) hBh
  -- Then change the source ring from `A` to `Ah` and compose the two textbook isomorphisms.
  simpa [H1Cotangent.presentationBaseChangeComparison] using hSource.comp hTarget

/-- Lemma 15.33.8, degree `0`: if `A → Ah` and `B → Bh` are filtered colimits of étale
algebras compatible with `A → B`, then the canonical comparison
`NL_{B/A} ⊗[B] Bh → NL_{Bh/Ah}` induces a bijection on `H^0 = Ω`. -/
@[stacks 0D08]
theorem naiveCotangentFilteredColimitOfEtaleComparison_kaehler_bijective
    (hAh : (algebraMap A Ah).IsFilteredColimitOfEtale)
    (hBh : (algebraMap B Bh).IsFilteredColimitOfEtale) :
    Function.Bijective (KaehlerDifferential.baseChangeComparison A Ah B Bh) := by
  letI : Algebra.FormallyEtale B Bh := (RingHom.formallyEtale_algebraMap).mp
    (RingHom.formallyEtale_of_isFilteredColimitOfEtale hBh)
  -- First compare `Bh ⊗[B] Ω[B⁄A]` with `Ω[Bh⁄A]` using formal étaleness of `B → Bh`.
  have hbase :
      Function.Bijective (KaehlerDifferential.mapBaseChange A B Bh) := by
    simpa using formallyEtale_kaehlerDifferential_mapBaseChange_bijective
      (R := A) (S := B) (S' := Bh)
  -- Then change the source ring from `A` to `Ah`; the source term vanishes because `A → Ah` is
  -- ind-étale, hence formally étale.
  have hsource :
      Function.Bijective (KaehlerDifferential.map A Ah Bh Bh) :=
    filteredColimitOfEtale_source_change_kaehler_bijective
      (R := A) (R' := Ah) (T := Bh) hAh
  -- Compose the two textbook comparison isomorphisms.
  simpa [KaehlerDifferential.baseChangeComparison] using hsource.comp hbase

/-- Lemma 15.33.8: if `A → Ah` and `B → Bh` are filtered colimits of étale algebras compatible
with `A → B`, then the canonical comparison
`NL_{B/A} ⊗[B] Bh → NL_{Bh/Ah}` induces bijections on the two cohomology groups of the naive
cotangent complex. In particular, this applies to henselizations and strict henselizations. -/
@[stacks 0D08]
theorem naiveCotangent_cohomology_comparison_bijective_of_filteredColimitOfEtale
    (hAh : (algebraMap A Ah).IsFilteredColimitOfEtale)
    (hBh : (algebraMap B Bh).IsFilteredColimitOfEtale) :
    Function.Bijective
      (H1Cotangent.presentationBaseChangeComparison A Ah B Bh (Generators.self A B)) ∧
      Function.Bijective (KaehlerDifferential.baseChangeComparison A Ah B Bh) := by
  exact ⟨
    naiveCotangentFilteredColimitOfEtaleComparison_h1_bijective hAh hBh,
    naiveCotangentFilteredColimitOfEtaleComparison_kaehler_bijective hAh hBh
  ⟩

end
