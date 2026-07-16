import LinearRepresentations_Serre_1977.Serre.Chap16.Proposition_16_16_4_1.Index
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.CanonicalPacketFrontier
import LinearRepresentations_Serre_1977.Serre.Chap16.Proposition_16_16_4_1.Frontier_PacketReindex
import LinearRepresentations_Serre_1977.Serre.Chap16.Proposition_16_16_4_1.Frontier_CharZeroSupportedFamily
import LinearRepresentations_Serre_1977.Serre.Chap16.Proposition_16_16_4_1.Frontier_AsAlgebraHomTransport
import LinearRepresentations_Serre_1977.Serre.Chap16.Proposition_16_16_4_1.Frontier_FiberInternalCoordinate
import LinearRepresentations_Serre_1977.Serre.Chap16.Proposition_16_16_4_1.Frontier_FourierOrthogonality
import LinearRepresentations_Serre_1977.Serre.Chap16.Proposition_16_16_4_1.Frontier_IntegralFourier
import LinearRepresentations_Serre_1977.Serre.Chap16.Proposition_16_16_4_1.Frontier_SerreFourierConsequences


-- Route correction: stable theorem-local helper owners now live behind the local index import, so
-- this file carries only the remaining unstable frontier and the public proposition statements.
-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped MonoidAlgebra
open Representation
open CategoryTheory

universe u v w x y

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type w} [Group G]
variable {E : Type x} [AddCommGroup E] [Module A E] [Module K E] [IsScalarTower A K E]

local notation "k" => IsLocalRing.ResidueField A

namespace StableLattice

section DefectZero

variable [Finite G] [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
variable {ρ : Representation K G E} [FiniteDimensional K E]
variable (L : StableLattice A ρ)

/-- Helper for Proposition 16-16.4-1: in this defect-zero section we realize the finite group as
a `Fintype` whenever Serre's coefficient formulas sum over `G`. -/
local instance instFintypeGDefectZero : Fintype G := Fintype.ofFinite G

/-
**Hypotheses vs. Serre (GTM 42, §16.4, Proposition 46).**
Serre states Prop. 46 under two standing assumptions of his `p`-modular system: "`K` has
characteristic zero" (Part III preamble) and, for §16.4, "`K` is *sufficiently large*". The latter
means `K` is a **splitting field for `G`** — every simple `K[G]`-module is absolutely irreducible —
which is what lets Serre invoke the global Wedderburn decomposition `K[G] ≅ ∏ᵢ End_K(Eᵢ)`
(props. 10–11) to read off `u_φ ↦ φ` on the `E`-block and `↦ 0` on all others.

The theorems below carry the precise hypotheses actually *consumed* by the proof:
`[CharZero K]` (faithful to Serre) together with the **per-representation** absolute-irreducibility
hypothesis `[(scalarExtension ρ to AlgebraicClosure K).IsIrreducible]` — i.e. only the module
`E = ρ` in hand need be absolutely irreducible. This is strictly *weaker* than (hence the statement
is more general than) Serre's global "sufficiently large" assumption: the formalized proof
base-changes `E` to the algebraic closure and applies single-block Fourier inversion
(`fourier_inversion_irreducible_general`, = prop. 11 on one block) there, never using the other
simple blocks.

NB: one must NOT encode "`K` sufficiently large" as `[IsAlgClosed K]` here — over the discretely
valued base it is *vacuous* (a discretely valued field is never algebraically closed, so
`[IsDiscreteValuationRing A] + [IsFractionRing A K] + [IsAlgClosed K] ⟹ False`).
-/



-- Proof sketch: the defect-zero divisibility hypothesis makes the integral Fourier idempotent for
-- `ρ` lie in `A[G]`; the resulting averaging operator gives the projective splitting criterion for
-- the induced `A[G]`-module structure on the lattice.
/-- Proposition 16-16.4-1 (1): under the defect-zero divisibility hypothesis, a `G`-stable lattice
in a simple `K[G]`-module is projective as an `A[G]`-module. -/
theorem projective_of_defect_zero
    [CharZero K]
    [(@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).IsIrreducible]
    (hdefect : ρ.HasDefectZero p) :
    Module.Projective A[G] L.toRepresentation.asModule := by
  -- Reuse the isolated irreducibility-to-nontriviality bridge before passing to the lattice.
  letI : Nontrivial E :=
    StableLattice.carrier_nontrivial_of_defect_zero (K := K) (G := G) (E := E)
      (p := p) (ρ := ρ) hdefect
  letI : Nontrivial L.toSubmodule := L.toSubmodule_nontrivial
  have hsurj :
      Function.Surjective L.toRepresentation.asAlgebraHom := by
    intro φ
    exact L.exists_groupAlgebra_preimage_of_endomorphism hdefect φ
  have hkernel_split :
      ∃ I : TwoSidedIdeal A[G],
        IsCompl (TwoSidedIdeal.ker L.toRepresentation.asAlgebraHom) I := by
    exact (L.serre_fourier_id_consequences hdefect).2
  -- Route correction: follow Serre's actual part `(b) ⇒ (a)` implication. Once
  -- `A[G] → End_A(P)` is onto with split kernel, projectivity descends formally from the
  -- endomorphism ring.
  exact L.projective_of_action_hom_surjective_and_ker_isCompl hsurj hkernel_split

-- Proof sketch: the defect-zero Fourier idempotent attached to each `A`-linear endomorphism of the
-- lattice produces an element of `A[G]` mapping to that endomorphism, giving surjectivity of the
-- canonical action map.
/-- Proposition 16-16.4-1 (2): assuming `K` is algebraically closed, the defect-zero divisibility
hypothesis makes the canonical homomorphism `A[G] → End_A(P)` of a stable lattice `P`
surjective. -/
theorem action_hom_surjective_of_defect_zero
    [CharZero K]
    [(@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).IsIrreducible]
    (hdefect : ρ.HasDefectZero p) :
    Function.Surjective L.toRepresentation.asAlgebraHom := by
  -- The source-faithful Fourier step has been isolated as the preimage lemma above.
  intro φ
  exact L.exists_groupAlgebra_preimage_of_endomorphism hdefect φ

/-- Helper for Proposition 16-16.4-1: once the source-faithful Fourier lift exists over `A[G]`,
reducing that lift coefficientwise along `A[G] → k[G]` makes the reduced action map hit every
`k`-linear endomorphism of the reduction. -/
theorem reduction_action_hom_surjective_of_defect_zero
    [CharZero K]
    [(@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).IsIrreducible]
    (hdefect : ρ.HasDefectZero p) :
    Function.Surjective L.reductionRepresentation.asAlgebraHom := by
  letI : Module A[G] L.toSubmodule := by
    change Module A[G] L.toRepresentation.asModule
    infer_instance
  letI : IsScalarTower A A[G] L.toSubmodule := by
    change IsScalarTower A A[G] L.toRepresentation.asModule
    infer_instance
  letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
  letI : IsScalarTower A k L.reduction :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ rfl
  letI : Module k[G] L.reduction := by
    change Module k[G] L.reductionRepresentation.asModule
    infer_instance
  letI : IsScalarTower k k[G] L.reduction := by
    change IsScalarTower k k[G] L.reductionRepresentation.asModule
    infer_instance
  letI : Module A (Module.End k L.reduction) :=
    Module.compHom (Module.End k L.reduction) (algebraMap A k)
  letI : IsScalarTower A k (Module.End k L.reduction) :=
    IsScalarTower.of_algebraMap_smul fun a u ↦ rfl
  let hf : IsBaseChange k
      (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction) :=
    L.reduction_mkQ_isBaseChange
  intro ψ
  -- First lift the reduced endomorphism to the lattice, then realize that lift by Serre's
  -- integral Fourier element upstairs.
  obtain ⟨φ, hφlift⟩ := L.reduction_endomorphism_lift_exists ψ
  obtain ⟨u, hu⟩ := L.exists_groupAlgebra_preimage_of_endomorphism hdefect φ
  refine ⟨MonoidAlgebra.mapRingHom G (algebraMap A k) u, ?_⟩
  -- The reduced action of the coefficientwise image of `u` is exactly the base-changed action of
  -- `u` on the lattice, because the quotient map intertwines arbitrary `A[G]`-actions.
  have htransport :
      L.reductionRepresentation.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A k) u) =
        hf.endHom (L.toRepresentation.asAlgebraHom u) := by
    let q : L.toSubmodule →ₗ[A] L.reduction := Submodule.mkQ L.maximalIdealSubmodule
    apply hf.algHom_ext
    intro x
    change
      (MonoidAlgebra.mapRingHom G (algebraMap A k) u) • q x =
        hf.endHom (L.toRepresentation.asAlgebraHom u) (q x)
    calc
      (MonoidAlgebra.mapRingHom G (algebraMap A k) u) • q x = q (u • x) := by
        symm
        exact L.reduction_mkQ_map_monoidAlgebra u x
      _ = hf.endHom (L.toRepresentation.asAlgebraHom u) (q x) := by
        symm
        simpa [q] using hf.endHom_comp_apply (L.toRepresentation.asAlgebraHom u) x
  calc
    L.reductionRepresentation.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A k) u) =
      hf.endHom (L.toRepresentation.asAlgebraHom u) := htransport
    _ = hf.endHom φ := by rw [hu]
    _ = ψ := by
      have hφ : hf.endHom φ = ψ := by
        exact hφlift
      exact hφ

-- Proof sketch: once the canonical action map is split by the defect-zero averaging construction,
-- its kernel is the kernel of an idempotent endomorphism of `A[G]`, hence a complementary
-- two-sided ideal.
/-- Proposition 16-16.4-1 (3): assuming `K` is algebraically closed, the kernel of the canonical
homomorphism `A[G] → End_A(P)` is a direct factor as a two-sided ideal of `A[G]`. -/
theorem action_hom_ker_isCompl_of_defect_zero
    [CharZero K]
    [(@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).IsIrreducible]
    (hdefect : ρ.HasDefectZero p) :
    ∃ I : TwoSidedIdeal A[G],
      IsCompl (TwoSidedIdeal.ker L.toRepresentation.asAlgebraHom) I := by
  -- The same specialized Fourier packet already contains the direct-factor statement for the
  -- kernel ideal.
  exact (L.serre_fourier_id_consequences hdefect).2

section Reduction

/-- Helper for Proposition 16-16.4-1: once the reduced action map hits every `k`-linear
endomorphism, the reduction has no nontrivial proper `k[G]`-submodules. -/
lemma reduction_irreducible_of_surjective_reduction_action_hom
    [Nontrivial L.reduction]
    (hsurj : Function.Surjective L.reductionRepresentation.asAlgebraHom) :
    L.reductionRepresentation.IsIrreducible := by
  -- Work directly with subrepresentations so the Burnside argument stays on the canonical
  -- invariant-subspace owner attached to `L.reductionRepresentation`.
  refine
    { toNontrivial := ?_
      eq_bot_or_eq_top := ?_ }
  · refine ⟨⊥, ⊤, ?_⟩
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : L.reduction)
    have hxmem : x ∈ (⊥ : Subrepresentation L.reductionRepresentation).toSubmodule := by
      simpa [h] using
        (show x ∈ (⊤ : Subrepresentation L.reductionRepresentation).toSubmodule from trivial)
    exact hx (by simpa using hxmem)
  · intro N
    by_cases hNbot : N = ⊥
    · exact Or.inl hNbot
    · by_cases hNtop : N = ⊤
      · exact Or.inr hNtop
      · -- Pick a nonzero vector in `N` and a target vector outside `N`; surjectivity then
        -- produces a `G`-equivariant endomorphism sending the first to the second, contradicting
        -- the defining `G`-stability of `N`.
        have hNbot_sub : N.toSubmodule ≠ ⊥ := by
          intro h
          exact hNbot (Subrepresentation.toSubmodule_injective h)
        obtain ⟨x, hxN, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hNbot_sub
        have hNtop_sub : N.toSubmodule ≠ ⊤ := by
          intro h
          exact hNtop (Subrepresentation.toSubmodule_injective h)
        have hnot_all : ¬ ∀ y : L.reduction, y ∈ N.toSubmodule := by
          simpa [Submodule.eq_top_iff'] using hNtop_sub
        push_neg at hnot_all
        obtain ⟨y, hyN⟩ := hnot_all
        let b := Module.Free.chooseBasis k L.reduction
        have hxrepr : b.repr x ≠ 0 := by
          intro hxrepr0
          apply hx0
          exact b.repr.injective (by simpa using hxrepr0)
        have hsupport : (b.repr x).support.Nonempty :=
          Finsupp.support_nonempty_iff.mpr hxrepr
        obtain ⟨i, hi⟩ := hsupport
        let f : L.reduction →ₗ[k] k := (b.repr x i)⁻¹ • b.coord i
        have hfx : f x = 1 := by
          have hcoeff : b.repr x i ≠ 0 := Finsupp.mem_support_iff.mp hi
          change (b.repr x i)⁻¹ * b.repr x i = 1
          exact inv_mul_cancel₀ hcoeff
        let T : Module.End k L.reduction := f.smulRight y
        obtain ⟨u, hu⟩ := hsurj T
        letI : Module k[G] L.reductionRepresentation.asModule := by
          change Module k[G] L.reductionRepresentation.asModule
          infer_instance
        have hTx_mem : T x ∈ N := by
          rw [← hu]
          simpa using (Subrepresentation.asSubmodule N).smul_mem u hxN
        have hTx : T x = y := by
          calc
            T x = f x • y := by
              simp [T]
            _ = y := by
              simp [hfx]
        exact False.elim (hyN (hTx ▸ hTx_mem))

-- Proof sketch: the same integral Fourier idempotent identifies the reduction modulo `𝔪_A` with a
-- defect-zero irreducible representation, so the induced representation on `P / 𝔪_A P` has no
-- nontrivial proper subrepresentations.
/-- Proposition 16-16.4-1 (4): under the defect-zero divisibility hypothesis, the reduction
`P / 𝔪_A P` of a stable lattice `P` is simple as a representation of `G` over `A / 𝔪_A`. -/
theorem reduction_irreducible_of_defect_zero
    [CharZero K]
    [(@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).IsIrreducible]
    (hdefect : ρ.HasDefectZero p) :
    L.reductionRepresentation.IsIrreducible := by
  letI : ρ.IsIrreducible := hdefect.isIrreducible
  -- Route correction: the Burnside/simple-module part is now isolated in the previous helper, so
  -- the only remaining source-faithful gap is descending the integral Fourier lift to the reduced
  -- action map.
  -- First make the ambient carrier nontrivial using the same defect-zero simplicity input.
  letI : Nontrivial E :=
    StableLattice.carrier_nontrivial_of_defect_zero (K := K) (G := G) (E := E)
      (p := p) (ρ := ρ) hdefect
  letI : Nontrivial L.reduction :=
    StableLattice.reduction_nontrivial_monoid (A := A) (K := K) L
  have hsurj :
      Function.Surjective L.reductionRepresentation.asAlgebraHom := by
    -- The reduction lift was isolated above, so this is now exactly the descended Fourier lift.
    exact L.reduction_action_hom_surjective_of_defect_zero hdefect
  exact L.reduction_irreducible_of_surjective_reduction_action_hom hsurj

-- Proof sketch: after part (1), the same averaging argument descends through the quotient
-- `P → P / 𝔪_A P`, so the reduced module inherits projectivity over `(A / 𝔪_A)[G]`.
/-- Proposition 16-16.4-1 (5): under the defect-zero divisibility hypothesis, the reduction
`P / 𝔪_A P` of a stable lattice `P` is projective as an `(A / 𝔪_A)[G]`-module. -/
theorem reduction_projective_of_defect_zero
    [CharZero K]
    [(@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).IsIrreducible]
    (hdefect : ρ.HasDefectZero p) :
    Module.Projective k[G]
      L.reductionRepresentation.asModule := by
  -- Descend the lattice projectivity statement through the residue-field reduction comparison.
  have hprojA : Module.Projective A[G] L.toRepresentation.asModule :=
    L.projective_of_defect_zero hdefect
  letI : Module A[G] L.toSubmodule := by
    change Module A[G] L.toRepresentation.asModule
    infer_instance
  letI : IsScalarTower A A[G] L.toSubmodule := by
    change IsScalarTower A A[G] L.toRepresentation.asModule
    infer_instance
  letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
  letI : IsScalarTower A k L.reduction :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ rfl
  letI : Module k[G] L.reduction := by
    change Module k[G] L.reductionRepresentation.asModule
    infer_instance
  letI : IsScalarTower k k[G] L.reduction := by
    change IsScalarTower k k[G] L.reductionRepresentation.asModule
    infer_instance
  have hprojA' : Module.Projective A[G] L.toSubmodule := by
    simpa using hprojA
  have hprojk : Module.Projective k[G] L.reduction :=
    (L.projective_iff_reduction_projective).mp hprojA'
  simpa using hprojk

end Reduction

end DefectZero

end StableLattice

end
