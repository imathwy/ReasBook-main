import Mathlib
import StacksProject_2024.Chap10.Definition_10_137_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

namespace Algebra

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

/- Domain-style sampling for the local smoothness criterion:
- primary domain: commutative algebra of smooth ring maps, localized cotangent homology, and
  localized Kähler differentials at a prime;
- sampled owner declarations:
  `Algebra.SmoothAtPrime`,
  `Algebra.smoothAtPrime_iff_isSmoothAt`,
  `Algebra.smoothLocus_eq_compl_support_inter`,
  `Module.free_of_flat_of_isLocalRing`,
  `module_finite_projective_iff_finitePresentation_and_flat`;
- best owner abstraction: the source-facing owner at this stage is `Algebra.SmoothAtPrime`,
  with `Algebra.IsSmoothAt` used only as the canonical local bridge;
- primitive data: the prime `q`, the local ring `S_q`, the localized cotangent homology, and the
  localized module of Kähler differentials;
- derived API: the finite-free/projective/flat reformulations of the same localized criterion.

Source/core/bridge triage:
- `source-facing`: the textbook `List.TFAE` statement with first clause `SmoothAtPrime R S q`;
- `core/canonical`: `Algebra.IsSmoothAt`, the localized cotangent-homology support criterion, and
  the local-ring projective/free criterion;
- `bridge/view`: `smoothAtPrime_iff_isSmoothAt`, used internally to pass from the source-facing
  predicate to the canonical local owner.

This file remains `source-facing`: it keeps the textbook `List.TFAE` packaging while exposing the
canonical local criterion only through a private bridge theorem.
-/

variable [FinitePresentation R S]

section

variable (q : PrimeSpectrum S)

local notation "S₍q₎" => Localization.AtPrime q.asIdeal
local notation "H¹₍q₎" => LocalizedModule.AtPrime q.asIdeal (H1Cotangent R S)
local notation "Ω₍q₎" => LocalizedModule.AtPrime q.asIdeal Ω[S⁄R]

private theorem isSmoothAt_iff_subsingleton_localizedH1Cotangent_and_localizedKaehler_free
    :
    IsSmoothAt R q.asIdeal ↔
      Subsingleton H¹₍q₎ ∧
        Module.Free S₍q₎ Ω₍q₎ := by
  -- Evaluate the smooth locus criterion at the fixed prime `q`.
  have hq :
      q ∈ Algebra.smoothLocus R S ↔
        q ∈ (Module.support S (H1Cotangent R S))ᶜ ∩ Module.freeLocus S Ω[S⁄R] := by
    simpa using
      congrArg (fun U : Set (PrimeSpectrum S) => q ∈ U)
        (Algebra.smoothLocus_eq_compl_support_inter (R := R) (A := S))
  -- Translate support and free-locus membership to the localized `H¹` and `Ω` conditions.
  simpa only [Algebra.smoothLocus, Set.mem_inter_iff, Set.mem_compl_iff,
      Module.notMem_support_iff, Module.mem_freeLocus] using hq

-- Proof sketch: use `Algebra.smoothLocus_eq_compl_support_inter` to identify `IsSmoothAt R q.asIdeal`
-- with vanishing of the localized cotangent homology and freeness of the localized Kähler
-- differentials. Since `R → S` is finitely presented, `Ω[S⁄R]` is finitely presented over `S`, so
-- after localizing at `q` the local module criterion for finite projective modules identifies the
-- finite-free, projective, and flat clauses over the local ring `S_q`.
/-- Chap10 Lemma 10 137 11: for a finitely presented ring map `R → S` and a prime `q` of `S`, the
following are equivalent: `R → S` is smooth at `q` in the source-facing sense `SmoothAtPrime R S q`;
the localized first cotangent homology `H¹(L_{S/R})_q` vanishes and the localized module of Kähler
differentials `Ω[S⁄R]_q` is finite free over `S_q`; `H¹(L_{S/R})_q` vanishes and `Ω[S⁄R]_q` is
projective over `S_q`; and `H¹(L_{S/R})_q` vanishes and `Ω[S⁄R]_q` is flat over `S_q`. -/
@[stacks 07BU]
theorem smoothAtPrime_tfae_subsingleton_localizedH1Cotangent_and_localizedKaehler_finiteFree_projective_flat
    :
    List.TFAE
      [ SmoothAtPrime R S q
      , Subsingleton H¹₍q₎ ∧
          Module.Finite S₍q₎ Ω₍q₎ ∧
          Module.Free S₍q₎ Ω₍q₎
      , Subsingleton H¹₍q₎ ∧
          Module.Projective S₍q₎ Ω₍q₎
      , Subsingleton H¹₍q₎ ∧
          Module.Flat S₍q₎ Ω₍q₎
      ] := by
  -- The localized Kähler differentials stay finite for finitely presented algebras.
  have hFiniteOmega : Module.Finite S₍q₎ Ω₍q₎ := inferInstance
  -- Compare the source-facing smoothness clause with the canonical local criterion first.
  tfae_have 1 ↔ 2 := by
    rw [Algebra.smoothAtPrime_iff_isSmoothAt (R := R) (S := S) q]
    constructor
    · intro hSmooth
      have hBridge :=
        (isSmoothAt_iff_subsingleton_localizedH1Cotangent_and_localizedKaehler_free
          (R := R) (S := S) (q := q)).mp hSmooth
      exact ⟨hBridge.1, hFiniteOmega, hBridge.2⟩
    · rintro ⟨hH1, _, hFree⟩
      exact
        (isSmoothAt_iff_subsingleton_localizedH1Cotangent_and_localizedKaehler_free
          (R := R) (S := S) (q := q)).mpr ⟨hH1, hFree⟩
  tfae_have 2 → 3 := by
    rintro ⟨hH1, _, hFree⟩
    -- Free modules are projective.
    letI : Module.Free S₍q₎ Ω₍q₎ := hFree
    exact ⟨hH1, Module.Projective.of_free (R := S₍q₎) (P := Ω₍q₎)⟩
  tfae_have 3 → 4 := by
    rintro ⟨hH1, hProjective⟩
    -- Projective modules are flat.
    letI : Module.Projective S₍q₎ Ω₍q₎ := hProjective
    exact ⟨hH1, Module.Flat.of_projective (R := S₍q₎) (M := Ω₍q₎)⟩
  tfae_have 4 → 2 := by
    rintro ⟨hH1, hFlat⟩
    -- Over the local ring `S_q`, a finite flat module is free.
    letI : Module.Finite S₍q₎ Ω₍q₎ := hFiniteOmega
    letI : Module.Flat S₍q₎ Ω₍q₎ := hFlat
    exact ⟨hH1, hFiniteOmega, Module.free_of_flat_of_isLocalRing (R := S₍q₎) (P := Ω₍q₎)⟩
  tfae_finish

end

end Algebra
