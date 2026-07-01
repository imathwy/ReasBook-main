import Mathlib
import stacks_project.Chap16.Lemma_16_9_2
import stacks_project.Chap16.Situation_16_9_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Algebra

open IsLocalization
open scoped Algebra

section

variable {R : Type u} {A : Type v} {Λ : Type w}
variable [CommRing R] [CommRing A] [CommRing Λ]
variable [Algebra R A] [Algebra R Λ] [Algebra A Λ] [IsScalarTower R A Λ]

section Prime

variable (q : Ideal Λ) [q.IsPrime]

/- Domain-style sampling:
- primary domain: localized commutative algebra and finite-presentation resolution data;
- sampled owner declarations:
  `ResolvableAtPrime`,
  `resolvableAtPrime_iff`,
  `Localization.AtPrime`,
  `Localization (Algebra.algebraMapSubmonoid A p.primeCompl)`;
- best owner abstraction: the localized source condition in Lemma `16.9.3` is the existing owner
  `ResolvableAtPrime`, specialized to `R_𝔭 → A_𝔭 → Λ_𝔮 ⊃ 𝔮Λ_𝔮`;
- primitive vs. derived: the primitive data are the localized rings and the prime ideal
  `𝔮Λ_𝔮`; the former `HasLocalResolutionAtPrime` wrapper was only a derived repackaging and is
  deleted in favor of the owner predicate itself.

Source/core/bridge triage:
- `source-facing`: the localized resolution hypothesis in the Stacks statement;
- `core/canonical`: `ResolvableAtPrime` on the localized rings;
- `bridge/view`: the local notation identifying the localized base ring, algebra, and target
  prime ideal.
-/

local notation "Rₚ" => Localization.AtPrime (q.under R)
local notation "Sₚ" => Algebra.algebraMapSubmonoid A (Ideal.primeCompl (q.under R))
local notation "Aₚ" => Localization Sₚ
local notation "Λ_𝔮" => Localization.AtPrime q
local notation "𝔮Λ_𝔮" => Ideal.map (algebraMap Λ Λ_𝔮) q

private theorem localizedTargetSubmonoid_le (q : Ideal Λ) [q.IsPrime] :
    Algebra.algebraMapSubmonoid Λ (Ideal.primeCompl (q.under R)) ≤ q.primeCompl := by
  rintro _ ⟨r, hr, rfl⟩
  simpa [Ideal.primeCompl, Ideal.mem_comap] using hr

private theorem localizedSubmonoid_le (q : Ideal Λ) [q.IsPrime] :
    Algebra.algebraMapSubmonoid A (Ideal.primeCompl (q.under R)) ≤
      Submonoid.comap (algebraMap A Λ) q.primeCompl := by
  intro a ha
  exact localizedTargetSubmonoid_le q <|
    (Algebra.algebraMapSubmonoid_le_comap (Ideal.primeCompl (q.under R))
      (IsScalarTower.toAlgHom R A Λ)) ha

noncomputable instance : Algebra Aₚ Λ_𝔮 := by
  have hSubmonoid : Sₚ ≤ Submonoid.comap (algebraMap A Λ) q.primeCompl := localizedSubmonoid_le q
  exact
    RingHom.toAlgebra <| IsLocalization.map Λ_𝔮 (algebraMap A Λ) hSubmonoid

instance : IsScalarTower Rₚ Aₚ Λ_𝔮 := by
  refine IsScalarTower.of_algebraMap_eq ?_
  intro x
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq (Ideal.primeCompl (q.under R)) x
  have hSubmonoid : Sₚ ≤ Submonoid.comap (algebraMap A Λ) q.primeCompl := localizedSubmonoid_le q
  have hsA : algebraMap R A ↑s ∈ Sₚ := by
    exact ⟨↑s, s.2, rfl⟩
  have hsΛ : algebraMap R Λ ↑s ∈ q.primeCompl := by
    change ↑s ∉ q.under R
    exact s.2
  change algebraMap Rₚ Λ_𝔮 (IsLocalization.mk' Rₚ r s) =
    algebraMap Aₚ Λ_𝔮 (algebraMap Rₚ Aₚ (IsLocalization.mk' Rₚ r s))
  have hAp :
      algebraMap Rₚ Aₚ (IsLocalization.mk' Rₚ r s) =
        IsLocalization.mk' Aₚ (algebraMap R A r) ⟨algebraMap R A ↑s, hsA⟩ :=
    by simpa using IsLocalization.algebraMap_mk' A Rₚ Aₚ r s
  have hRq :
      algebraMap Rₚ Λ_𝔮 (IsLocalization.mk' Rₚ r s) =
        IsLocalization.mk' Λ_𝔮 (algebraMap R Λ r) ⟨algebraMap R Λ ↑s, hsΛ⟩ := by
    refine (Localization.localRingHom_mk' (q.under R) q (algebraMap R Λ) rfl r s).trans ?_
    congr 1
  rw [hAp, hRq]
  have hMap :
      algebraMap Aₚ Λ_𝔮 (IsLocalization.mk' Aₚ (algebraMap R A r) ⟨algebraMap R A ↑s, hsA⟩) =
        IsLocalization.mk' Λ_𝔮 (algebraMap R Λ r) ⟨algebraMap R Λ ↑s, hsΛ⟩ := by
    change
      IsLocalization.map Λ_𝔮 (algebraMap A Λ) hSubmonoid
          (IsLocalization.mk' Aₚ (algebraMap R A r) ⟨algebraMap R A ↑s, hsA⟩) =
        _
    simpa [IsScalarTower.algebraMap_eq R A Λ] using
      IsLocalization.map_mk' hSubmonoid
        (algebraMap R A r) ⟨algebraMap R A ↑s, hsA⟩
  simp [hMap]

end Prime

-- Proof sketch: start from the local resolution at `Λ_𝔮`, replace it by a standard smooth
-- factorization over `R_𝔭` using Lemmas `16.2.8`, `16.3.4`, and `16.3.6`, then clear
-- denominators in the resulting standard smooth presentation and homogenize the defining
-- equations. The resulting finitely presented global algebra still maps to `Λ`, and the chosen
-- Jacobian determinant stays away from `𝔮`, so the image of `H_{C/R}` is not contained in `𝔮`.
/-- Lemma 16.9.3: if `𝔮` is a minimal prime over `𝔥_A` and the localized map
`R_𝔭 → A_𝔭 → Λ_𝔮 ⊃ 𝔮 Λ_𝔮`, with `𝔭 = R ∩ 𝔮`, admits a resolution and `R` is Noetherian while `A`
is finitely presented over `R`, then `A → Λ` factors through a finitely presented `R`-algebra `C`
whose singular ideal image in `Λ` is not contained in `𝔮`. -/
theorem exists_factorization_with_singularIdeal_not_le_of_localResolutionAtMinimalPrime
    [IsNoetherianRing R] [FinitePresentation R A] (q : Ideal Λ)
    (hq : q ∈ (h(A⁄R, Λ)).minimalPrimes)
    (hresolve :
      let _ : q.IsPrime := Ideal.minimalPrimes_isPrime hq
      let Rₚ := Localization.AtPrime (q.under R)
      let Sₚ := Algebra.algebraMapSubmonoid A (Ideal.primeCompl (q.under R))
      let Aₚ := Localization Sₚ
      let Λ_𝔮 := Localization.AtPrime q
      let 𝔮Λ_𝔮 := Ideal.map (algebraMap Λ Λ_𝔮) q
      ResolvableAtPrime Rₚ Aₚ Λ_𝔮 𝔮Λ_𝔮) :
    ∃ (C : Type (max u v w)) (_ : CommRing C) (_ : Algebra R C) (_ : FinitePresentation R C)
      (f : A →ₐ[R] C) (g : C →ₐ[R] Λ),
      g.comp f = IsScalarTower.toAlgHom R A Λ ∧
        ¬ g.singularIdealIn R ≤ q := by
  letI : q.IsPrime := Ideal.minimalPrimes_isPrime hq
  sorry

end

end Algebra
