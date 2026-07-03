import stacks_project.Chap10.Lemma_10_150_4
import stacks_project.Chap15.«15_18_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum
open scoped TensorProduct

universe u v w x y

noncomputable section

section DirectLimitDescent

variable {R : Type u} {S : Type v} {M : Type w} {Λ : Type x}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M]
variable [Algebra.FinitePresentation R S] [Module.FinitePresentation S M]
variable [Preorder Λ] [IsDirectedOrder Λ] [Nonempty Λ]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/- Domain-style sampling:
- primary domain: directed colimits of commutative `R`-algebras and flat-over-base loci after
  base change;
- sampled owner declarations:
  `Ring.DirectLimit.algebraMap`,
  `Ring.DirectLimit.algebraMap_eq_of`,
  `Ring.DirectLimit.instAlgebra`,
  `Module.flatOverBaseLocus`;
- best owner abstraction: the canonical direct-limit `R`-algebra owner
  `Ring.DirectLimit.algebraMap`;
- layer triage:
  - `source-facing`: Lemma 15.18.3;
  - `core/canonical`: `Module.flatOverBaseLocus` and `Ring.DirectLimit.algebraMap`;
  - `bridge/view`: passing from the `AlgHom`-valued directed system to its underlying ring-hom
    system when forming `Ring.DirectLimit`.

Primitive data are the stage rings, their `R`-algebra structures, the directed system, and the
stage ideals. Their extensions to `S ⊗[R] A i` and to the direct-limit base change are derived
API, as is the direct-limit `R`-algebra structure; all of these should come directly from the
canonical owner built from the directed system of `R`-algebra morphisms.
-/

section

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
local notation "S[" i "]" => S ⊗[R] A i
local notation "M[" i "]" => S[i] ⊗[S] M

-- Proof sketch: apply openness of the flat locus for finitely presented modules after base
-- change, cover the closed set cut out by the colimit ideal by finitely many basic opens on which
-- the base-changed module is flat, then descend the finitely many elements and their flatness data
-- to some sufficiently large stage using finite presentation and the directed-colimit hypotheses.
/-- Lemma 15.18.3: if the canonical closed-subset inclusion `(15.18.0.1)` holds for the base
change of `(R → S, M)` to the direct limit of a directed system of `R`-algebras and for the
colimit ideal of a compatible family of stage ideals, then the same inclusion already holds after
base change to some stage. -/
theorem exists_stage_zeroLocus_subset_flatOverBaseLocus_of_direct_limit_base_change
    (hI : ∀ ⦃i j⦄, (hij : i ≤ j) → Ideal.map (ρ i j hij) (I i) ≤ I j)
    (hflat_inf :
      zeroLocus (Ideal.map (algebraMap A∞ S∞) I∞ : Set S∞) ⊆
        Module.flatOverBaseLocus A∞ S∞ M∞) :
    ∃ i : Λ,
      zeroLocus (Ideal.map (algebraMap (A i) S[i]) (I i) : Set S[i]) ⊆
        Module.flatOverBaseLocus (A i) S[i] M[i] := sorry

end

end DirectLimitDescent
