import StacksProject_2024.Chap10.Definition_10_17_1
import StacksProject_2024.Chap10.Definition_10_54_1
import StacksProject_2024.Chap10.Lemma_10_150_4
import StacksProject_2024.Chap15.«15_18_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum
open scoped PrimeSpectrum
open scoped TensorProduct

universe u v w x y z

noncomputable section

section DirectLimitDescent

variable {R : Type u} {S : Type v} {M : Type w} {Λ : Type x}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module.FinitePresentation S M]
variable [Preorder Λ] [IsDirectedOrder Λ] [Nonempty Λ]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/- Domain-style sampling:
- primary domain: directed colimits of commutative `R`-algebras and flat-over-base loci on closed
  subsets;
- sampled owner declarations:
  `PrimeSpectrum.zeroLocus`,
  `StacksProject_2024.Chap10.Definition_10_17_1`'s notation owner `V(-)`,
  `Ring.DirectLimit.algebraMap`,
  `Ring.DirectLimit.algebraMap_eq_of`,
  `Ring.DirectLimit.instAlgebra`,
  `Module.flatOverBaseLocus`;
- best owner abstraction: the direct-limit `R`-algebra owner `Ring.DirectLimit.algebraMap`;
- layer triage:
  - `source-facing`: Lemma 15.19.4;
  - `core/canonical`: `Module.flatOverBaseLocus` and `Ring.DirectLimit.algebraMap`;
  - `bridge/view`: passing to the underlying ring-hom system of an `AlgHom`-valued directed
    system when forming `Ring.DirectLimit`.

Primitive data are the stage rings, their `R`-algebra structures, the directed system, and the
stage ideal family. The direct-limit `R`-algebra structure is derived API and should therefore be
reused from the chapter-10 owner rather than rebuilt from a separate compatibility witness on raw
ring homomorphisms.
-/

section

variable (J : Ideal S)
variable (A : Λ → Type y) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable (φ : ∀ i j, i ≤ j → A i →ₐ[R] A j)
variable [DirectedSystem A fun i j h ↦ (φ i j h : A i →+* A j)]
variable (I : ∀ i, Ideal (A i))

local notation "ρ" => fun i j h ↦ (φ i j h : A i →+* A j)
local notation "A∞" => Ring.DirectLimit A ρ
local notation "ι∞" => Ring.DirectLimit.of A ρ
local notation "I∞" => ⨆ i, Ideal.map (ι∞ i) (I i)
local notation "S∞" => S ⊗[R] A∞
local notation "M∞" => S∞ ⊗[S] M
local notation "K∞" =>
  (Ideal.map (algebraMap A∞ S∞) I∞ + Ideal.map (algebraMap S S∞) J : Ideal S∞)
local notation "S[" i "]" => S ⊗[R] A i
local notation "M[" i "]" => S[i] ⊗[S] M
local notation "K[" i "]" =>
  (Ideal.map (algebraMap (A i) S[i]) (I i) + Ideal.map (algebraMap S S[i]) J : Ideal S[i])

-- Proof sketch: write `S` as a localization of a finitely presented `R`-algebra, descend the
-- finitely many basic opens covering the closed subset defined by `I∞` and `J` from the direct
-- limit to one stage, and then apply the finite-presentation flatness descent lemma stagewise to
-- conclude flatness on that entire closed subset.
/-- Lemma 15.19.4: if `R → S` is essentially of finite presentation, `M` is a finitely presented
`S`-module, and the source condition `(15.19.1.1)` holds after base change to the
direct limit of a directed system of `R`-algebras for the colimit ideal `I∞`, then the same
condition already holds after base change to some stage ring `A i` for the corresponding stage
ideal `I i`. -/
theorem exists_stage_zeroLocus_add_subset_flatOverBaseLocus_of_direct_limit_base_change
    (hS : RingHom.EssFinitePresentation (algebraMap R S))
    (hI : ∀ ⦃i j⦄, (hij : i ≤ j) → Ideal.map (φ i j hij) (I i) ≤ I j)
    (hflat_inf : V((K∞ : Set S∞)) ⊆ Module.flatOverBaseLocus A∞ S∞ M∞) :
    ∃ i : Λ,
      V((K[i] : Set S[i])) ⊆ Module.flatOverBaseLocus (A i) S[i] M[i] := sorry

end

end DirectLimitDescent
