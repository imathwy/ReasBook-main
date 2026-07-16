import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_51_3
import stacks_proof.stacks_project.Chap10.«10_69_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DirectSum Pointwise
open RingTheory.Sequence
open LinearMap

universe u v w x

section

variable {A : Type u} [CommRing A]
variable {L : Type v} [AddCommGroup L] [Module A L]
variable {M : Type w} [AddCommGroup M] [Module A M]
variable {N : Type x} [AddCommGroup N] [Module A N]

namespace Ideal

/- Domain-style sampling:
- primary domain: Artin-Rees control of the `I`-adic filtration and its induced cokernel graded
  module;
- sampled declarations: `LinearMap.IsArtinReesBound`, `Ideal.exists_artin_rees_constant_of_exact`,
  `RingTheory.Sequence.idealAssociatedGradedPiece`, and
  `RingTheory.Sequence.idealAssociatedGradedModule`;
- core/canonical owner: `idealAssociatedGradedPiece I (N ⧸ range g) n` degreewise, with
  `idealAssociatedGradedModule I (N ⧸ range g)` as the derived direct-sum owner;
- source-facing layer: the degree-preserving comparison of the associated graded pieces of
  `coker g` and `coker g'`;
- bridge/view layer: the denominator inside `idealAssociatedGradedStage I N n` used to present the
  quotient pieces of `N ⧸ range g`, and the induced `DirectSum.lmap` on the owner direct sums.

Primitive data are the ideal `I`, the maps `g`, `g'`, and the quotient modules `N ⧸ range g`,
`N ⧸ range g'`. The denominator inside `idealAssociatedGradedStage I N n` is derived API for the
internal quotient model of each owner graded piece, so it should stay internal rather than become
the main public declaration.
-/

private abbrev cokernelAssociatedGradedDenominator (I : Ideal A) (g : M →ₗ[A] N) (n : ℕ) :
    Submodule A (idealAssociatedGradedStage I N n) :=
  Submodule.comap
    (idealAssociatedGradedStage I N n).subtype
    (idealAssociatedGradedStage I N (n + 1) ⊔
      range g ⊓ idealAssociatedGradedStage I N n)

-- Proof sketch: the quotient map `N → N / range g` sends `I^n N` into `I^n (N / range g)`.
private theorem cokernelAssociatedGradedStageMap_mem
    (I : Ideal A) (g : M →ₗ[A] N) (n : ℕ) (x : idealAssociatedGradedStage I N n) :
    (range g).mkQ x.1 ∈ idealAssociatedGradedStage I (N ⧸ range g) n := sorry

private noncomputable def cokernelAssociatedGradedStageMap
    (I : Ideal A) (g : M →ₗ[A] N) (n : ℕ) :
    idealAssociatedGradedStage I N n →ₗ[A]
      idealAssociatedGradedStage I (N ⧸ range g) n :=
  LinearMap.codRestrict
    (idealAssociatedGradedStage I (N ⧸ range g) n)
    ((range g).mkQ.comp (idealAssociatedGradedStage I N n).subtype)
    (fun x ↦ cokernelAssociatedGradedStageMap_mem I g n x)

private noncomputable def cokernelAssociatedGradedPieceMap
    (I : Ideal A) (g : M →ₗ[A] N) (n : ℕ) :
    idealAssociatedGradedStage I N n →ₗ[A]
      idealAssociatedGradedPiece I (N ⧸ range g) n :=
  ((idealAssociatedGradedStage I (N ⧸ range g) (n + 1)).submoduleOf
      (idealAssociatedGradedStage I (N ⧸ range g) n)).mkQ.comp
    (cokernelAssociatedGradedStageMap I g n)

-- Proof sketch: the kernel is exactly the pullback of `I^(n+1)(N / range g)` along
-- `I^n N → I^n(N / range g)`, which expands to the denominator used in the ambient quotient model.
private theorem cokernelAssociatedGradedPieceMap_ker
    (I : Ideal A) (g : M →ₗ[A] N) (n : ℕ) :
    LinearMap.ker (cokernelAssociatedGradedPieceMap I g n) =
      cokernelAssociatedGradedDenominator I g n := sorry

-- Proof sketch: every class in the degree-`n` piece of `N / range g` has a representative in
-- `I^n(N / range g)` lifted from `I^n N`.
private theorem cokernelAssociatedGradedPieceMap_surjective
    (I : Ideal A) (g : M →ₗ[A] N) (n : ℕ) :
    Function.Surjective (cokernelAssociatedGradedPieceMap I g n) := sorry

private noncomputable def cokernelAssociatedGradedInternalPieceEquiv
    (I : Ideal A) (g : M →ₗ[A] N) (n : ℕ) :
    (idealAssociatedGradedStage I N n ⧸ cokernelAssociatedGradedDenominator I g n) ≃ₗ[A]
      idealAssociatedGradedPiece I (N ⧸ range g) n :=
  (Submodule.quotEquivOfEq _ _ (cokernelAssociatedGradedPieceMap_ker I g n).symm).trans
    ((cokernelAssociatedGradedPieceMap I g n).quotKerEquivOfSurjective
      (cokernelAssociatedGradedPieceMap_surjective I g n))

-- Proof sketch: first use Lemma 15.4.1 to transfer the Artin-Rees bound `c` from `g` to `g'`.
-- Then compare `LinearMap.range g ∩ I^n N` and `LinearMap.range g' ∩ I^n N` exactly as in the
-- textbook proof: for `n ≤ c`, the congruence modulo `I^(c + 1)` is enough, and for `n > c` the
-- Artin-Rees bound writes elements of the intersection as images of elements in `I^(n - c) M`,
-- so the perturbation term lands in `I^(n + 1) N`. Symmetry gives equality of the two ambient
-- denominators, and hence equality of the induced submodules inside `I^n N`.
private theorem cokernelAssociatedGradedDenominator_eq_of_congr_mod_pow_and_artin_rees
    (I : Ideal A) {c : ℕ} {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N))
    (n : ℕ) :
    cokernelAssociatedGradedDenominator I g n =
      cokernelAssociatedGradedDenominator I g' n := sorry

/-- Lemma 15.4.2, degree `n`: under the hypotheses of Lemma 15.4.1, the degree-`n` associated
graded pieces of `N ⧸ range g` and `N ⧸ range g'` are canonically linearly equivalent. This is the
source-facing graded comparison; the direct-sum equivalence of the full associated graded modules
is derived from these piece maps. -/
@[stacks 07VF]
noncomputable def cokernelIdealAssociatedGradedPieceEquiv_of_congr_mod_pow_and_artin_rees
    (I : Ideal A) {c : ℕ} {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N))
    (n : ℕ) :
    idealAssociatedGradedPiece I (N ⧸ range g) n ≃ₗ[A]
      idealAssociatedGradedPiece I (N ⧸ range g') n :=
  (cokernelAssociatedGradedInternalPieceEquiv I g n).symm.trans <|
    (Submodule.quotEquivOfEq _ _
      (cokernelAssociatedGradedDenominator_eq_of_congr_mod_pow_and_artin_rees
        I hf hg hexact hff' hgg' n)).trans <|
      cokernelAssociatedGradedInternalPieceEquiv I g' n

private noncomputable def cokernelIdealAssociatedGradedModuleMap_of_congr_mod_pow_and_artin_rees
    (I : Ideal A) {c : ℕ} {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N)) :
    idealAssociatedGradedModule I (N ⧸ range g) →ₗ[A]
      idealAssociatedGradedModule I (N ⧸ range g') :=
  DirectSum.lmap fun n ↦
    (cokernelIdealAssociatedGradedPieceEquiv_of_congr_mod_pow_and_artin_rees
      I hf hg hexact hff' hgg' n).toLinearMap

private noncomputable def cokernelIdealAssociatedGradedModuleInvMap_of_congr_mod_pow_and_artin_rees
    (I : Ideal A) {c : ℕ} {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N)) :
    idealAssociatedGradedModule I (N ⧸ range g') →ₗ[A]
      idealAssociatedGradedModule I (N ⧸ range g) :=
  DirectSum.lmap fun n ↦
    (cokernelIdealAssociatedGradedPieceEquiv_of_congr_mod_pow_and_artin_rees
      I hf hg hexact hff' hgg' n).symm.toLinearMap

private theorem cokernelIdealAssociatedGradedModule_left_inv_of_congr_mod_pow_and_artin_rees
    (I : Ideal A) {c : ℕ} {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N)) :
    (cokernelIdealAssociatedGradedModuleInvMap_of_congr_mod_pow_and_artin_rees
        I hf hg hexact hff' hgg').comp
      (cokernelIdealAssociatedGradedModuleMap_of_congr_mod_pow_and_artin_rees
        I hf hg hexact hff' hgg') =
      LinearMap.id := by
  sorry

private theorem cokernelIdealAssociatedGradedModule_right_inv_of_congr_mod_pow_and_artin_rees
    (I : Ideal A) {c : ℕ} {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N)) :
    (cokernelIdealAssociatedGradedModuleMap_of_congr_mod_pow_and_artin_rees
        I hf hg hexact hff' hgg').comp
      (cokernelIdealAssociatedGradedModuleInvMap_of_congr_mod_pow_and_artin_rees
        I hf hg hexact hff' hgg') =
      LinearMap.id := by
  sorry

-- Proof sketch: assemble the degreewise equivalences into a direct-sum linear equivalence between
-- the full associated graded modules.
/-- Lemma 15.4.2: under the hypotheses of Lemma 15.4.1, the associated graded modules
`Gr_I(N ⧸ range g)` and `Gr_I(N ⧸ range g')` are canonically linearly equivalent, and this
equivalence is induced degreewise by
`cokernelIdealAssociatedGradedPieceEquiv_of_congr_mod_pow_and_artin_rees`. The comparison of the
degree-`n` quotient models inside `I^n N` remains internal and is used only to build the
owner-level direct-sum equivalence. -/
@[stacks 07VF]
noncomputable def cokernelIdealAssociatedGradedModuleEquiv_of_congr_mod_pow_and_artin_rees
    (I : Ideal A) {c : ℕ} {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N)) :
    idealAssociatedGradedModule I (N ⧸ range g) ≃ₗ[A]
      idealAssociatedGradedModule I (N ⧸ range g') :=
  LinearEquiv.ofLinear
    (cokernelIdealAssociatedGradedModuleMap_of_congr_mod_pow_and_artin_rees
      I hf hg hexact hff' hgg')
    (cokernelIdealAssociatedGradedModuleInvMap_of_congr_mod_pow_and_artin_rees
      I hf hg hexact hff' hgg')
    (cokernelIdealAssociatedGradedModule_right_inv_of_congr_mod_pow_and_artin_rees
      I hf hg hexact hff' hgg')
    (cokernelIdealAssociatedGradedModule_left_inv_of_congr_mod_pow_and_artin_rees
      I hf hg hexact hff' hgg')

/-- Companion: the associated-graded module equivalence of Lemma 15.4.2 preserves degrees and is
obtained by applying the degree-`n` piece equivalence on the `n`-th direct-sum summand. -/
theorem cokernelIdealAssociatedGradedModuleEquiv_of_congr_mod_pow_and_artin_rees_lof
    (I : Ideal A) {c : ℕ} {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N))
    (n : ℕ) (x : idealAssociatedGradedPiece I (N ⧸ range g) n) :
    cokernelIdealAssociatedGradedModuleEquiv_of_congr_mod_pow_and_artin_rees
        I hf hg hexact hff' hgg'
        (DirectSum.lof A ℕ (idealAssociatedGradedPiece I (N ⧸ range g)) n x) =
      DirectSum.lof A ℕ (idealAssociatedGradedPiece I (N ⧸ range g')) n
        (cokernelIdealAssociatedGradedPieceEquiv_of_congr_mod_pow_and_artin_rees
          I hf hg hexact hff' hgg' n x) := by
  simpa
    [cokernelIdealAssociatedGradedModuleEquiv_of_congr_mod_pow_and_artin_rees,
      cokernelIdealAssociatedGradedModuleMap_of_congr_mod_pow_and_artin_rees]
    using
      (DirectSum.lmap_lof A ℕ
        (fun n ↦
          (cokernelIdealAssociatedGradedPieceEquiv_of_congr_mod_pow_and_artin_rees
            I hf hg hexact hff' hgg' n).toLinearMap)
        n x)

end Ideal

end
