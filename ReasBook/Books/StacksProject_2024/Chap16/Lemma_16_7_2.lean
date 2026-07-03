import Mathlib
import StacksProject_2024.Chap16.Definition_16_2_1
import StacksProject_2024.Chap16.Definition_16_2_3
import StacksProject_2024.Chap16.Lemma_16_7_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace Algebra

open scoped SingularIdealNotation

section

variable {R : Type u} {A : Type v} {D : Type w} {Λ : Type x}
variable [CommRing R] [CommRing A] [CommRing D] [CommRing Λ]
variable [Algebra R A] [Algebra R D] [Algebra R Λ]

variable (π : R)

local notation "I4" => Ideal.span ({π ^ 4} : Set R)

local notation "R4" => R ⧸ I4
local notation "A4" => A ⧸ Ideal.map (algebraMap R A) I4
local notation "D4" => D ⧸ Ideal.map (algebraMap R D) I4
local notation "AnnR[" x "]" => Ideal.torsionOf R R x
local notation "AnnΛ[" x "]" => Ideal.torsionOf Λ Λ x

/- Domain-style sampling for Lemma 16.7.2:
- primary domain: commutative algebra of finitely presented `R`-algebras, strict-standard
  elements, reduction modulo `π⁴`, and singular-ideal control in a common factorization;
- sampled owner declarations:
  `Ideal.torsionOf`,
  `Algebra.IsStrictlyStandard`,
  `Algebra.singularIdeal`,
  `AlgHom.singularIdeal`,
  `piPowFourQuotientMap`;
- best owner abstraction: this item remains a source-facing existence theorem, with the
  annihilator hypotheses expressed through the canonical owner `Ideal.torsionOf`, the mod-`π⁴`
  compatibility carried by the bridge `piPowFourQuotientMap π`, and the singular-ideal conditions
  stated through the chapter owners `H[−⁄−]` and the induced-target bridge
  `AlgHom.singularIdeal`;
- primitive data: the maps `fA : A →ₐ[R] Λ` and `fD : D →ₐ[R] Λ`, the annihilator equalities for
  `π` in `R` and `Λ`, the strict-standardness witness for the image of `π` in `A`, and the
  compatible reduction map `A / π⁴A → D / π⁴D`;
- derived API: the finitely presented intermediate algebra `B`, the factorization maps
  `A →ₐ[R] B`, `D →ₐ[R] B`, `B →ₐ[R] Λ`, and the two singular-ideal containments they induce.

Source/core/bridge triage:
- `source-facing`: the common factorization theorem below;
- `core/canonical`: `Ideal.torsionOf`, `IsStrictlyStandard`, `H[−⁄−]`, and finite presentation;
- `bridge/view`: `piPowFourQuotientMap π`, `AlgHom.singularIdeal`, and the compatibility equation
  defining `hφ`.
-/

-- Proof sketch: apply Lemma `16.7.1` to the composite `D → A ⊗[R] D → Λ`, using Lemma `16.2.7`
-- to transport strict standardness of `π` from `A` to `A ⊗[R] D` over `D`. The mod-`π⁴`
-- comparison through `piPowFourQuotientMap` produces the required section after base change.
-- This yields a finitely presented factorization through `B` with `H_{D/R}B ⊆ H_{B/D}`; the
-- inclusion `H_{D/R}B ⊆ H_{B/R}` then follows from the stability of smoothness under
-- composition.
/-- Lemma 16.7.2: let `R` be Noetherian, let `Λ` be an `R`-algebra, let `π ∈ R`, and let
`A → Λ` and `D → Λ` be `R`-algebra maps with `A` and `D` of finite presentation. Assume
`Ann_R(π) = Ann_R(π²)` and `Ann_Λ(π) = Ann_Λ(π²)`, assume the image of `π` is strictly standard
in `A` over `R`, and assume there is an `R`-algebra map `A / π⁴A → D / π⁴D` compatible with the
maps to `Λ / π⁴Λ`. Then there is a finitely presented `R`-algebra `B`, together with compatible
maps `A → B`, `D → B`, and `B → Λ`, such that the image of `H_{D/R}` in `B` is contained in both
`H_{B/D}` and `H_{B/R}`. -/
theorem exists_common_finitePresentation_factorization_with_singularIdeal_control
    [IsNoetherianRing R] [FinitePresentation R A] [FinitePresentation R D]
    (fA : A →ₐ[R] Λ) (fD : D →ₐ[R] Λ)
    (hAnnR : AnnR[π] = AnnR[π ^ 2])
    (hAnnΛ : AnnΛ[algebraMap R Λ π] = AnnΛ[algebraMap R Λ (π ^ 2)])
    (hπ : IsStrictlyStandard R (algebraMap R A π))
    (hφ : ∃ φ : A4 →ₐ[R4] D4,
      (piPowFourQuotientMap π fD).comp φ = piPowFourQuotientMap π fA) :
    ∃ (B : Type (max u v w x)) (_ : CommRing B) (_ : Algebra R B) (_ : FinitePresentation R B)
      (fAB : A →ₐ[R] B) (fDB : D →ₐ[R] B) (g : B →ₐ[R] Λ),
      g.comp fAB = fA ∧
        g.comp fDB = fD ∧
        Ideal.map fDB.toRingHom (H[D⁄R]) ≤ fDB.singularIdeal ∧
        Ideal.map fDB.toRingHom (H[D⁄R]) ≤ H[B⁄R] := sorry

end

end Algebra
