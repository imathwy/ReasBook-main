import stacks_project.Chap15.Definition_15_8_3
import stacks_project.Chap10.Definition_10_78_1
import stacks_project.Chap15.Lemma_15_96_2
import stacks_project.Chap15.Lemma_15_96_8
import stacks_project.Chap15.Lemma_15_97_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ComplexShape
open BerthelotOgusEtaReduction.Nat
open scoped nonZeroDivisors

universe u

section

variable {A : Type u} [CommRing A]
local notation "CpxA" => NatModuleCochainComplex A

/-
Domain-style sampling:
- primary domain: Berthelot-Ogus `η_f` for bounded-above `ℕ`-indexed cochain complexes, together
  with the degree-`i` determinantal ideal `I_i(M^•, f)`;
- sampled owner declarations:
  `_root_.etaDeterminantalIdeal`,
  `CochainComplex.IsStrictlyLE`,
  `etaFDegreeSubmodule`,
  `etaPairMap`,
  `Module.Free`,
  `Module.FiniteLocallyFreeOfRank`;
- best owner abstraction:
  `source-facing`: the two theorems of this file about `(η_f M)^i`, the unreduced map
    `(1, d^i)`, and the degree-`i` ideal `I_i(M^•, f)` on `M : NatModuleCochainComplex A`;
  `core/canonical`: the chapter owner `etaDeterminantalIdeal` on `ℤ`-indexed complexes together
    with the `ℤ`-indexed bounded-above predicate on `M.extend embeddingUpNat`;
  `bridge/view`: extension by zero along `embeddingUpNat`, used only internally to recall the
    `ℤ`-indexed determinantal-ideal owner and bounded-above predicate.
- primitive data vs derived API: the primitive public data are the degreewise finite-free terms of
  `M` and the nat-level ideal `M.etaDeterminantalIdeal f i`; the extension-by-zero presentation is
  derived bridge data and should not remain in theorem interfaces. -/

private noncomputable instance extend_embeddingUpNat_term_moduleFree
    (M : CpxA) (i : ℕ) [Module.Free A (M.X i)] :
    Module.Free A ((M.extend embeddingUpNat).X (i : ℤ)) := by
  let e : (((M.extend embeddingUpNat).X (i : ℤ)) : ModuleCat A) ≃ₗ[A] M.X i :=
    (M.extendXIso embeddingUpNat rfl).toLinearEquiv
  exact Module.Free.of_equiv e.symm

private noncomputable instance extend_embeddingUpNat_term_moduleFinite
    (M : CpxA) (i : ℕ) [Module.Finite A (M.X i)] :
    Module.Finite A ((M.extend embeddingUpNat).X (i : ℤ)) := by
  let e : (((M.extend embeddingUpNat).X (i : ℤ)) : ModuleCat A) ≃ₗ[A] M.X i :=
    (M.extendXIso embeddingUpNat rfl).toLinearEquiv
  exact Module.Finite.equiv e.symm

private noncomputable instance extend_embeddingUpNat_succ_term_moduleFree
    (M : CpxA) (i : ℕ) [Module.Free A (M.X (i + 1))] :
    Module.Free A ((M.extend embeddingUpNat).X ((i : ℤ) + 1)) := by
  let e : (((M.extend embeddingUpNat).X ((i : ℤ) + 1)) : ModuleCat A) ≃ₗ[A] M.X (i + 1) := by
    simpa using (M.extendXIso embeddingUpNat (by simp : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1)).toLinearEquiv
  exact Module.Free.of_equiv e.symm

private noncomputable instance extend_embeddingUpNat_succ_term_moduleFinite
    (M : CpxA) (i : ℕ) [Module.Finite A (M.X (i + 1))] :
    Module.Finite A ((M.extend embeddingUpNat).X ((i : ℤ) + 1)) := by
  let e : (((M.extend embeddingUpNat).X ((i : ℤ) + 1)) : ModuleCat A) ≃ₗ[A] M.X (i + 1) := by
    simpa using (M.extendXIso embeddingUpNat (by simp : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1)).toLinearEquiv
  exact Module.Finite.equiv e.symm

namespace NatModuleCochainComplex

/-- A bounded-below complex is bounded above if its extension by zero vanishes above some
nonnegative degree. This keeps the `ℤ`-indexed support bridge internal to the owner. -/
abbrev IsBoundedAbove (M : CpxA) : Prop :=
  ∃ b : ℕ, CochainComplex.IsStrictlyLE (M.extend embeddingUpNat) (b : ℤ)

/-- The degree-`i` Berthelot-Ogus determinantal ideal `I_i(M^•, f)` for a bounded-below complex,
viewed through the canonical extension-by-zero bridge. -/
abbrev etaDeterminantalIdeal
    (M : CpxA) (f : A) (i : ℕ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))] :
    Ideal A :=
  _root_.etaDeterminantalIdeal f (M.extend embeddingUpNat) (i : ℤ)

end NatModuleCochainComplex

variable (f : A) (M : CpxA) (i : ℕ)
variable [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
variable [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))]
variable (hf : f ∈ nonZeroDivisors A)
variable (hI : (M.etaDeterminantalIdeal f i).IsPrincipal)

-- Proof sketch: after localizing at each prime, choose a generator of the principal ideal
-- `I_i(M^\bullet, f)` and apply Lemma `15.8.10` to the quotient by the torsion of the cokernel of
-- `(f, d^i)`. The textbook argument identifies `(η_f M)^i` with the kernel of `(d^i, -1)` inside
-- the split exact three-term complex built from `f^i M^i`, `f^(i + 1) M^i`, and
-- `f^(i + 1) M^(i + 1)`, which yields the claimed local freeness and rank.
/-- Lemma 15.97.5: if `f` is a nonzerodivisor in `A`, the terms `M^i` and `M^{i + 1}` are finite
free, and `I_i(M^\bullet, f)` is principal, then the degree-`i` term `(η_f M)^i` is finite locally
free of rank `rk(M^i)`. -/
theorem etaFDegree_finiteLocallyFreeOfRank_of_determinantalIdeal_isPrincipal
    :
    Module.FiniteLocallyFreeOfRank A ((η[f] M).X i) (Module.finrank A (M.X i)) := sorry

-- Proof sketch: with the same local normal form as in the rank statement, the image of
-- `(1, d^i)` identifies with the kernel of `(d^i, -1)` in a short exact sequence whose cokernel
-- is the torsion-free quotient controlled by Lemma `15.8.10`. The quotient is projective, so the
-- short exact sequence splits and `(1, d^i)` becomes the inclusion of a direct summand.
/-- Under the principal-ideal hypothesis on `I_i(M^\bullet, f)`, the canonical map
`(1, d^i) : (η_f M)^i → f^i M^i × f^(i + 1) M^(i + 1)` is a split monomorphism, i.e. the
inclusion of a direct summand. -/
theorem etaFDegreePairMap_isSplitMono_of_determinantalIdeal_isPrincipal
    :
    IsSplitMono (ModuleCat.ofHom (etaPairMap f M i)) := sorry

end
