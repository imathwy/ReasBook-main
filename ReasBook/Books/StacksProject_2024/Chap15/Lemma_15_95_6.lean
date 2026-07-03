import Mathlib
import StacksProject_2024.Chap15.Lemma_15_95_3
import StacksProject_2024.Chap15.Lemma_15_95_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open AdicCompletion
open scoped TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)
local notation "single₀" => (ModuleCat.single0Functor : ModuleCat A ⥤ DMod)
local notation "Away" => LocalizedModule.Away

/- Domain-style sampling for Lemma 15.95.6:
- primary domain: derived `I`-adic completion of degree-zero objects in `D(A)`, together with the
  module-theoretic tensor and localization realizations that feed the source text;
- sampled owner declarations:
  `ModuleCat.single0Functor`,
  `singleFunctorIso_of_isGE_of_isLE`,
  `derivedCompletionOfModule_cohomology_shortExact`,
  `DerivedCategory.homology_derivedCompletionOf_iso_adicCompletion`,
  `AdicCompletion`,
  `tor_eventually_zero_map_quotient_pow`,
  `LocalizedModule.equivTensorProduct`;
- best owner abstraction: the main public statements should identify the canonical derived
  completion object `((single₀).obj X)^∧[I, I.fg_of_isNoetherianRing]` itself with the canonical
  degree-zero owner `(single₀).obj (AdicCompletion I X)` in `D(A)`, formalized propositionally as
  `IsIsomorphic` because this file does not yet expose a canonical comparison morphism; the
  degree-zero comparison and off-zero vanishing remain companion API used to build that
  identification through `singleFunctorIso_of_isGE_of_isLE`; the Milnor short exact sequence of
  Lemma `15.95.3` is the core owner input, while the tensor-product/localization descriptions
  remain bridge/view input to the proof;
- primitive vs. derived:
  primitive data are the ideal `I`, the finite module `M`, and the auxiliary flat or localized
  module appearing in the two source statements;
  derived API is the source-facing identification of the actual derived-completion object with the
  degree-zero object on `AdicCompletion I X`, together with degree-zero comparison and off-zero
  vanishing as supporting companions.

Source/core/bridge triage:
- `source-facing`: the two derived-category completion isomorphisms below for `M ⊗[A] N` and
  `Away f M`;
- `core/canonical`: `ModuleCat.single0Functor`, `DerivedCategory.derivedCompletionOf`, the
  Milnor short exact sequence owner `derivedCompletionOfModule_cohomology_shortExact`,
  `singleFunctorIso_of_isGE_of_isLE`, and the module-side completion owner `AdicCompletion`;
- `bridge/view`: the tensor-product model and the localization/tensor comparison
  `LocalizedModule.equivTensorProduct`. -/

-- Proof sketch: apply Lemma `15.95.3` to `X := M ⊗[A] N`. Since `N` is flat, the Tor towers
-- `Tor_i^A(X, A / I^(n+1))` identify with `Tor_i^A(M, A / I^(n+1)) ⊗[A] N`, so Lemma `15.27.3`
-- makes them pro-zero for `i > 0`. The `i = 0` term is the usual quotient tower
-- `(M ⊗[A] N) / I^(n+1)(M ⊗[A] N)`.
/-- Degree-zero companion for Lemma `15.95.6 (1)`: if `M` is finite and `N` is flat, then the
zero-th cohomology of the derived completion of `(M ⊗[A] N)[0]` is isomorphic to the ordinary
`I`-adic completion of `M ⊗[A] N`. This is the degree-zero input used to build the full
derived-object identification in `tensor_finite_flat_derivedCompletion_usual_adicCompletion`. -/
theorem tensor_finite_flat_homology_zero_derivedCompletion_isomorphic_adicCompletion
    (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (N : Type u) [AddCommGroup N] [Module A N] [Module.Flat A N] :
    IsIsomorphic
      ((H 0).obj
        (((single₀).obj (ModuleCat.of A (M ⊗[A] N)))^∧[I, I.fg_of_isNoetherianRing]))
      (ModuleCat.of A (AdicCompletion I (M ⊗[A] N))) := by
  sorry

-- Proof sketch: for `X = M ⊗[A] N`, flatness of `N` identifies the tower
-- `Tor_i^A(X, A / I^(n + 1))` with `Tor_i^A(M, A / I^(n + 1)) ⊗[A] N`. Lemma `15.27.3` makes the
-- positive-degree Tor towers pro-zero, so Lemma `15.95.3` yields that the derived `I`-adic
-- completion of `X[0]` has no nonzero cohomology outside degree `0`. This off-zero vanishing,
-- together with
-- `tensor_finite_flat_homology_zero_derivedCompletion_isomorphic_adicCompletion`, supplies the
-- proposition-level
-- derived-category isomorphism in `tensor_finite_flat_derivedCompletion_usual_adicCompletion`.
/-- Off-zero vanishing companion for Lemma `15.95.6 (1)`: if `M` is finite and `N` is flat, then
the derived completion of `(M ⊗[A] N)[0]` has zero cohomology in every degree `n ≠ 0`. Together
with `tensor_finite_flat_homology_zero_derivedCompletion_isomorphic_adicCompletion`, this yields
the full derived-object identification with the degree-zero object on the ordinary completion. -/
theorem tensor_finite_flat_homology_derivedCompletion_isZero_of_ne_zero
    (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (N : Type u) [AddCommGroup N] [Module A N] [Module.Flat A N] (n : ℤ) (hn : n ≠ 0) :
      IsZero ((H n).obj
        (((single₀).obj (ModuleCat.of A (M ⊗[A] N)))^∧[I, I.fg_of_isNoetherianRing])) := by
  sorry

-- Proof sketch: combine the degree-zero comparison
-- `tensor_finite_flat_homology_zero_derivedCompletion_isomorphic_adicCompletion` with the off-zero
-- vanishing in `tensor_finite_flat_homology_derivedCompletion_isZero_of_ne_zero` to obtain the
-- canonical bounds `IsGE 0` and `IsLE 0`, then identify the resulting single-degree object with
-- the ordinary completion.
/-- Lemma 15.95.6 (1): if `I` is an ideal in a Noetherian ring `A`, `M` is a finite `A`-module,
and `N` is a flat `A`-module, then the derived `I`-adic completion of `M ⊗[A] N`, viewed as a
degree-zero object of `D(A)`, is isomorphic to the degree-zero object on the ordinary `I`-adic
completion of `M ⊗[A] N`. -/
theorem tensor_finite_flat_derivedCompletion_usual_adicCompletion
    (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (N : Type u) [AddCommGroup N] [Module A N] [Module.Flat A N] :
    IsIsomorphic
      (((single₀).obj (ModuleCat.of A (M ⊗[A] N)))^∧[I, I.fg_of_isNoetherianRing])
      ((single₀).obj (ModuleCat.of A (AdicCompletion I (M ⊗[A] N)))) := by
  sorry

-- Proof sketch: specialize the tensor statement to `N = Localization.Away f`, then transport the
-- conclusion across the canonical localization/tensor equivalence
-- `LocalizedModule.equivTensorProduct`.
/-- Degree-zero companion for Lemma `15.95.6 (2)`: for a finite module `M`, the zero-th
cohomology of the derived completion of `M_f[0]` is isomorphic to the ordinary `I`-adic
completion of the localization `M_f`. This is obtained by transporting part `(1)` along
`LocalizedModule.equivTensorProduct`. -/
theorem localizationAway_finite_homology_zero_derivedCompletion_isomorphic_adicCompletion
    (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (f : A) :
    IsIsomorphic
      ((H 0).obj
        (((single₀).obj (ModuleCat.of A (Away f M)))^∧[I, I.fg_of_isNoetherianRing]))
      (ModuleCat.of A (AdicCompletion I (Away f M))) := by
  sorry

-- Proof sketch: specialize the previous tensor-product statement to `N = Localization.Away f`,
-- use the standard identification of `M_f` with `M ⊗[A] A_f`, and transport the resulting
-- degree-zero cohomology description along that localization equivalence, and reuse the same
-- Tor-vanishing argument to conclude that all other cohomology groups vanish.
/-- Off-zero vanishing companion for Lemma `15.95.6 (2)`: for a finite module `M`, the derived
completion of `M_f[0]` has zero cohomology in every degree `n ≠ 0`. -/
theorem localizationAway_finite_homology_derivedCompletion_isZero_of_ne_zero
    (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (f : A)
    (n : ℤ) (hn : n ≠ 0) :
      IsZero ((H n).obj
        (((single₀).obj (ModuleCat.of A (Away f M)))^∧[I, I.fg_of_isNoetherianRing])) := by
  sorry

-- Proof sketch: combine
-- `localizationAway_finite_homology_zero_derivedCompletion_isomorphic_adicCompletion` with
-- `localizationAway_finite_homology_derivedCompletion_isZero_of_ne_zero` to obtain the canonical
-- `t`-structure bounds and conclude by `singleFunctorIso_of_isGE_of_isLE`.
/-- Lemma 15.95.6 (2): if `I` is an ideal in a Noetherian ring `A`, `M` is a finite `A`-module,
and `f ∈ A`, then the derived `I`-adic completion of the localization `M_f`, viewed as a
degree-zero object of `D(A)`, is isomorphic to the degree-zero object on the ordinary `I`-adic
completion of `M_f`. -/
theorem localizationAway_finite_derivedCompletion_usual_adicCompletion
    (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (f : A) :
    IsIsomorphic
      (((single₀).obj (ModuleCat.of A (Away f M)))^∧[I, I.fg_of_isNoetherianRing])
      ((single₀).obj (ModuleCat.of A (AdicCompletion I (Away f M)))) := by
  sorry

end
