import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_40_4
import stacks_proof.stacks_project.Chap10.Lemma_10_40_5
import stacks_proof.stacks_project.Chap10.Lemma_10_137_13
import stacks_proof.stacks_project.Chap16.Lemma_16_2_7
import stacks_proof.stacks_project.Chap16.Lemma_16_7_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace Algebra

open scoped SingularIdealNotation
open scoped TensorProduct

section

variable {R : Type u} {A : Type v} {D : Type w} {Λ : Type x}
variable [CommRing R] [CommRing A] [CommRing D] [CommRing Λ]
variable [Algebra R A] [Algebra R D] [Algebra R Λ]

variable (π : R)

local notation "I4" => Ideal.span ({π ^ 4} : Set R)

local notation "R4" => R ⧸ I4
local notation "A4" => A ⧸ Ideal.map (algebraMap R A) I4
local notation "D4" => D ⧸ Ideal.map (algebraMap R D) I4
local notation "Λ4" => Λ ⧸ Ideal.map (algebraMap R Λ) I4
local notation "AnnR[" x "]" => Ideal.torsionOf R R x
local notation "AnnD[" x "]" => Ideal.torsionOf D D x
local notation "AnnΛ[" x "]" => Ideal.torsionOf Λ Λ x
local notation "πD" => algebraMap R D π

/-- Helper for Lemma 16.7.2: the quotient `Ann_D(π²) / Ann_D(π)` that appears in the
source-faithful reduction to Lemma `16.7.1` over the base ring `D`. -/
private abbrev quotient_annihilator_module_D : Type w :=
  AnnD[πD ^ 2] ⧸ Submodule.comap (AnnD[πD ^ 2]).subtype AnnD[πD]

/-- Helper for Lemma 16.7.2: the annihilator ideal of the quotient
`Ann_D(π²) / Ann_D(π)`. -/
private abbrev quotient_annihilator_ideal_D : Ideal D :=
  Module.annihilator D (quotient_annihilator_module_D (R := R) (D := D) (π := π))

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
  stated through the chapter owners `H[−⁄−]` and `AlgHom.singularIdeal`;
- primitive data: the maps `fA : A →ₐ[R] Λ` and `fD : D →ₐ[R] Λ`, the annihilator equalities for
  `π` in `R` and `Λ`, the strict-standardness witness for the image of `π` in `A`, and the
  compatible reduction map `A / π⁴A → D / π⁴D`;
- derived API: the finitely presented intermediate algebra `B`, the factorization maps
  `A →ₐ[R] B`, `D →ₐ[R] B`, `B →ₐ[R] Λ`, and the two singular-ideal containments they induce.

Source/core/bridge triage:
- `source-facing`: the common factorization theorem below;
- `core/canonical`: `Ideal.torsionOf`, `IsStrictlyStandard`, `H[−⁄−]`,
  `AlgHom.singularIdeal`, and finite presentation;
- `bridge/view`: `piPowFourQuotientMap π` and the compatibility equation defining `hφ`.
-/

-- Proof sketch: apply Lemma `16.7.1` to the composite `D → A ⊗[R] D → Λ`, using Lemma `16.2.7`
-- to transport strict standardness of `π` from `A` to `A ⊗[R] D` over `D`. The mod-`π⁴`
-- comparison through `piPowFourQuotientMap` produces the required section after base change.
-- This yields a finitely presented factorization through `B` with `H_{D/R}B ⊆ H_{B/D}`; the
-- inclusion `H_{D/R}B ⊆ H_{B/R}` then follows from the stability of smoothness under
-- composition.
/-- Helper for Lemma 16.7.2: in the tensor product `D ⊗[R] A`, the left image of `π` from the
base-changed ring `D` agrees with the pure tensor `1 ⊗ π`. -/
private theorem includeLeft_pi_eq_baseChange :
    ((Algebra.TensorProduct.includeLeft : D →ₐ[D] (TensorProduct R D A)) πD) =
      (1 : D) ⊗ₜ[R] algebraMap R A π := by
  calc
    ((Algebra.TensorProduct.includeLeft : D →ₐ[D] (TensorProduct R D A)) πD) =
        πD ⊗ₜ[R] (1 : A) := by
          rw [Algebra.TensorProduct.includeLeft_apply]
    _ = π • ((1 : D) ⊗ₜ[R] (1 : A)) := by
          simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul']
    _ = (1 : D) ⊗ₜ[R] algebraMap R A π := by
          simp [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul]

/-- Helper for Lemma 16.7.2: strict standardness of `π` survives the base change from `R` to `D`
inside the tensor-product algebra `D ⊗[R] A`. -/
lemma strict_standard_tensor_baseChange
    (hπ : IsStrictlyStandard R (algebraMap R A π)) :
    IsStrictlyStandard D
      ((Algebra.TensorProduct.includeLeft : D →ₐ[D] (TensorProduct R D A)) πD) := by
  -- Base change the chosen strict-standard presentation from `A` to `D ⊗[R] A`.
  rcases hπ with ⟨n, m, P, hP⟩
  have hP_base :
      (P.baseChange D).IsStrictlyStandardElement ((1 : D) ⊗ₜ[R] algebraMap R A π) :=
    hP.baseChange
  have hP_tensor :
      (P.baseChange D).IsStrictlyStandardElement
        ((Algebra.TensorProduct.includeLeft : D →ₐ[D] (TensorProduct R D A)) πD) := by
    -- Rewrite the target element using the tensor identity `π ⊗ 1 = 1 ⊗ π`.
    rw [includeLeft_pi_eq_baseChange (R := R) (A := A) (D := D) (π := π)]
    exact hP_base
  exact ⟨n, m, P.baseChange D, hP_tensor⟩

/-- Helper for Lemma 16.7.2: after passing to `T = D ⊗[R] A`, Lemma `16.7.1` should produce the
common finitely presented factorization together with the quotient-annihilator control over `D`.
-/
theorem exists_tensor_factorization_with_quotient_annihilator_control
    [IsNoetherianRing R] [FinitePresentation R A] [FinitePresentation R D]
    (fA : A →ₐ[R] Λ) (fD : D →ₐ[R] Λ)
    (hAnnΛ : AnnΛ[algebraMap R Λ π] = AnnΛ[algebraMap R Λ (π ^ 2)])
    (hπ : IsStrictlyStandard R (algebraMap R A π))
    (hφ : ∃ φ : A4 →ₐ[R4] D4,
      (piPowFourQuotientMap π fD).comp φ = piPowFourQuotientMap π fA) :
    ∃ (B : Type _) (_ : CommRing B) (_ : Algebra R B) (_ : FinitePresentation R B)
      (fAB : A →ₐ[R] B) (fDB : D →ₐ[R] B) (g : B →ₐ[R] Λ),
      g.comp fAB = fA ∧
        g.comp fDB = fD ∧
        Ideal.map fDB.toRingHom (quotient_annihilator_ideal_D (R := R) (D := D) (π := π)) ≤
          AlgHom.singularIdeal fDB := by
  letI : Algebra D Λ := fD.toAlgebra
  let T := TensorProduct R D A
  letI : CommRing T := inferInstance
  letI : Algebra R T := inferInstance
  letI : Algebra D T := inferInstance
  let fT : T →ₐ[D] Λ :=
    Algebra.TensorProduct.lift (Algebra.ofId D Λ) fA (fun x y ↦ Commute.all _ _)
  have hπT :
      IsStrictlyStandard D
        ((Algebra.TensorProduct.includeLeft : D →ₐ[D] T) πD) :=
    strict_standard_tensor_baseChange (R := R) (A := A) (D := D) (π := π) hπ
  have hAnnΛD :
      AnnΛ[algebraMap D Λ πD] = AnnΛ[algebraMap D Λ (πD ^ 2)] := by
    -- Reassociate the scalar tower `R → D → Λ`; both elements of `Λ` are the images of `π` and
    -- `π²` from the original base ring `R`.
    calc
      AnnΛ[algebraMap D Λ πD] = AnnΛ[algebraMap R Λ π] := by
        congr 1
        change fD (algebraMap R D π) = algebraMap R Λ π
        rw [fD.commutes]
      _ = AnnΛ[algebraMap R Λ (π ^ 2)] := hAnnΛ
      _ = AnnΛ[algebraMap D Λ (πD ^ 2)] := by
        congr 1
        have hcomm_pi : fD (algebraMap R D π) = algebraMap R Λ π := fD.commutes π
        calc
          algebraMap R Λ (π ^ 2) = (algebraMap R Λ π) ^ 2 := by
            rw [map_pow]
          _ = (fD (algebraMap R D π)) ^ 2 := by
            rw [hcomm_pi]
          _ = fD ((algebraMap R D π) ^ 2) := by
            rw [map_pow]
  rcases hφ with ⟨φ, hφcompat⟩
  letI : Algebra D4 Λ4 := (piPowFourQuotientMap π fD).toAlgebra
  let qD : D →ₐ[D] D4 := Ideal.Quotient.mkₐ D (Ideal.map (algebraMap R D) I4)
  let qA : A →ₐ[R] A4 := Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R A) I4)
  let φR : A4 →ₐ[R] D4 := φ.restrictScalars R
  let sA : A →ₐ[R] D4 := φR.comp qA
  let σ : T →ₐ[D] D4 :=
    Algebra.TensorProduct.lift qD sA (fun x y ↦ Commute.all (qD x) (sA y))
  have hqD_piPowFour : qD (algebraMap R D (π ^ 4)) = 0 := by
    rw [show qD (algebraMap R D (π ^ 4)) =
        Ideal.Quotient.mk (Ideal.map (algebraMap R D) I4) (algebraMap R D (π ^ 4)) by rfl]
    refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))
  have hσ_ker :
      ∀ x ∈ Ideal.map (algebraMap D T) (Ideal.map (algebraMap R D) I4), σ x = 0 := by
    -- The descended tensor map kills the `D`-ideal generated by `π⁴`.
    intro x hx
    have hle :
        Ideal.map (algebraMap D T) (Ideal.map (algebraMap R D) I4) ≤ RingHom.ker σ := by
      rw [Ideal.map_map, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem,
        RingHom.mem_ker]
      have hpiPowFour_mem : algebraMap R D (π ^ 4) ∈ Ideal.map (algebraMap R D) I4 := by
        exact Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))
      simpa [qD] using
        (Ideal.Quotient.eq_zero_iff_mem.mpr hpiPowFour_mem :
          Ideal.Quotient.mk (Ideal.map (algebraMap R D) I4) (algebraMap R D (π ^ 4)) = 0)
    exact RingHom.mem_ker.mp (hle hx)
  -- Route correction: the `D`-linear tensor map `σ : D ⊗[R] A → D / π⁴D` is now fixed, and the
  -- quotient-killing lemma `hσ_ker` reduces the remaining work to a single compatibility step.
  -- TODO: descend `σ` to a `D4`-algebra section on
  -- `T ⧸ Ideal.map (algebraMap D T) (Ideal.span ({πD ^ 4} : Set D))`, prove the compatibility
  -- with `piPowFourQuotientMap πD fT` by tensor-product extensionality using `hφcompat`, and then
  -- run Lemma `16.7.1` over the base ring `D`.
  sorry

/-- Helper for Lemma 16.7.2: the quotient-annihilator control produced over `D` upgrades to the
two singular-ideal containments claimed in the statement. -/
theorem singularIdeal_containments_of_quotient_annihilator_control
    {B : Type _} [CommRing B] [Algebra R B] [FinitePresentation R B]
    (fDB : D →ₐ[R] B)
    (hAnnR : AnnR[π] = AnnR[π ^ 2])
    (hquot :
      Ideal.map fDB.toRingHom (quotient_annihilator_ideal_D (R := R) (D := D) (π := π)) ≤
        AlgHom.singularIdeal fDB) :
    Ideal.map fDB.toRingHom (H[D⁄R]) ≤ AlgHom.singularIdeal fDB ∧
      Ideal.map fDB.toRingHom (H[D⁄R]) ≤ H[B⁄R] := by
  -- The source proof argues primewise: smooth primes of `D/R` do not contain `aD`, so `hquot`
  -- forces smoothness of `B/D` above them. Composing smooth maps then gives the absolute
  -- containment inside `H[B⁄R]`.
  -- TODO: formalize the zero-locus comparison `zeroLocus aD ⊆ zeroLocus H[D⁄R]` using flatness of
  -- localizations at smooth primes together with the annihilator base-change lemmas from Lemma
  -- `10.40.4`, and then finish the absolute containment with `RingHom.Smooth.comp`.
  sorry

/-- Lemma 16.7.2: let `R` be Noetherian, let `Λ` be an `R`-algebra, let `π ∈ R`, and let
`A → Λ` and `D → Λ` be `R`-algebra maps with `A` and `D` of finite presentation. Assume
`Ann_R(π) = Ann_R(π²)` and `Ann_Λ(π) = Ann_Λ(π²)`, assume the image of `π` is strictly standard
in `A` over `R`, and assume there is an `R`-algebra map `A / π⁴A → D / π⁴D` compatible with the
maps to `Λ / π⁴Λ`. Then there is a finitely presented `R`-algebra `B`, together with compatible
maps `A → B`, `D → B`, and `B → Λ`, such that the image of `H_{D/R}` in `B` is contained in both
`H_{B/D}` and `H_{B/R}`. -/
@[stacks 07CT]
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
        Ideal.map fDB.toRingHom (H[D⁄R]) ≤ AlgHom.singularIdeal fDB ∧
        Ideal.map fDB.toRingHom (H[D⁄R]) ≤ H[B⁄R] := by
  -- Apply the tensor-product reduction first, then convert the quotient-annihilator control into
  -- the two desired singular-ideal containments.
  obtain ⟨B, hB, hAlgB, hfpB, fAB, fDB, g, hgA, hgD, hquot⟩ :=
    exists_tensor_factorization_with_quotient_annihilator_control
      (R := R) (A := A) (D := D) (Λ := Λ) (π := π) fA fD hAnnΛ hπ hφ
  letI : CommRing B := hB
  letI : Algebra R B := hAlgB
  letI : FinitePresentation R B := hfpB
  have hsingular :
      Ideal.map fDB.toRingHom (H[D⁄R]) ≤ AlgHom.singularIdeal fDB ∧
        Ideal.map fDB.toRingHom (H[D⁄R]) ≤ H[B⁄R] :=
    singularIdeal_containments_of_quotient_annihilator_control
      (R := R) (D := D) (π := π) fDB hAnnR hquot
  exact ⟨B, hB, hAlgB, hfpB, fAB, fDB, g, hgA, hgD, hsingular.1, hsingular.2⟩

end

end Algebra
