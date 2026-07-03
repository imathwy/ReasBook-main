

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_18_1 (from Chap15) -/
open PrimeSpectrum
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} {S : Type v} {M : Type w} {R' : Type x}
variable [CommRing R] [CommRing S] [CommRing R'] [Algebra R S] [Algebra R R']
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable {I : Ideal R} {I' : Ideal R'}

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation "S'" => S ⊗[R] R'
local notation "M'" => S' ⊗[S] M

namespace Ideal

/- Domain triage:
- primary domain: flatness loci of modules on closed subsets of `Spec` under tensor-product base
  change in commutative algebra;
- sampled owner declarations: `Module.flatOverBaseLocus`,
  `Ideal.zeroLocus_subset_flatOverBaseLocus_iff`, `Module.Flat.baseChange`,
  `LocalizedModule.equivTensorProduct`;
- core/canonical owner: `Module.flatOverBaseLocus`;
- layer choice here: `source-facing`; the Stacks lemma is the base-change stability of the
  canonical closed-subset inclusion, while the primewise localization formulation is derived API.

Primitive data vs derived API:
- primitive data: the original closed-subset inclusion into `Module.flatOverBaseLocus` and the
  ideal containment `IR' ≤ I'`;
- derived API: the primewise statement for localizations above primes in the closed subset;
- the local base-change step itself is most canonically expressed by the tensor-product/base-change
  owners `LocalizedModule.equivTensorProduct`, `isLocalizedModule_iff_isBaseChange`, and
  `Module.Flat.baseChange`, rather than by a separate ad hoc localization wrapper.
-/

private theorem le_comap_asIdeal_of_mem_zeroLocus_map_le
    {K : Ideal S} {K' : Ideal S'} {q' : PrimeSpectrum S'}
    (hq' : q' ∈ zeroLocus (K' : Set S'))
    (hK' : Ideal.map (algebraMap S S') K ≤ K') :
    K ≤ Ideal.comap (algebraMap S S') q'.asIdeal := by
  have hq'le : K' ≤ q'.asIdeal := (mem_zeroLocus q' (K' : Set S')).1 hq'
  exact Ideal.map_le_iff_le_comap.mp <| le_trans hK' hq'le

-- Proof sketch: let `q'` be a prime of `S'` containing the extension of `I'`, and let `q` be its
-- image in `Spec S`. The hypothesis gives flatness of `M_q` over `R`. Localizing the tensor-product
-- square at `q'` identifies the localized base-changed module with the textbook local base change
-- of `M_q` via the canonical localization/tensor-product equivalences, and then
-- `Module.Flat.baseChange` gives the required flatness over `R'`.
/-- Base-change stability of a flatness-locus inclusion along any closed subset whose defining
ideal contains the extension of the original one. This is the owner-level closed-subset form used
by later Stacks specializations with additional algebra-side summand ideals. -/
theorem zeroLocus_subset_flatOverBaseLocus_of_baseChange_of_map_le
    {K : Ideal S} {K' : Ideal S'}
    (hflat : zeroLocus (K : Set S) ⊆ Module.flatOverBaseLocus R S M)
    (hK' : Ideal.map (algebraMap S S') K ≤ K') :
    zeroLocus (K' : Set S') ⊆ Module.flatOverBaseLocus R' S' M' := by
  have hsource :
      ∀ q : PrimeSpectrum S,
        q ∈ zeroLocus (K : Set S) →
          Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) :=
    (zeroLocus_subset_flatOverBaseLocus_iff K).mp hflat
  refine (zeroLocus_subset_flatOverBaseLocus_iff K').mpr ?_
  intro q' hq'
  let q : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S S') q'
  have hq : q ∈ zeroLocus (K : Set S) :=
    (mem_zeroLocus q (K : Set S)).2 <| by
      change K ≤ Ideal.comap (algebraMap S S') q'.asIdeal
      exact le_comap_asIdeal_of_mem_zeroLocus_map_le hq' hK'
  have hflatq : Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) :=
    hsource q hq
  -- Localize the tensor-product square at `q'`, identify the result with the corresponding base
  -- change of `M_q` via the canonical localization/tensor-product equivalences, and apply
  -- `Module.Flat.baseChange`.
  sorry

/-- Lemma 15.18.1: if `15.18.0.1` holds for `(R → S, I, M)`, then after a base change `R → R'`
and for any ideal `I'` containing `IR'`, the corresponding closed-subset inclusion into the
flat-over-base locus holds for `(R' → S', I', M')`. -/
theorem zeroLocus_subset_flatOverBaseLocus_of_baseChange
    (hflat : zeroLocus (I.map (algebraMap R S) : Set S) ⊆ Module.flatOverBaseLocus R S M)
    (hI' : I.map (algebraMap R R') ≤ I') :
    zeroLocus (I'.map (algebraMap R' S') : Set S') ⊆ Module.flatOverBaseLocus R' S' M' := by
  let iR' : R' →+* S' := (Algebra.TensorProduct.includeRight : R' →ₐ[R] S').toRingHom
  have hmap_eq :
      Ideal.map (algebraMap S S') (Ideal.map (algebraMap R S) I) =
        Ideal.map iR' (Ideal.map (algebraMap R R') I) := by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    simpa [iR'] using
      (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap :
        (algebraMap S S').comp (algebraMap R S) =
          ((Algebra.TensorProduct.includeRight : R' →ₐ[R] S').toRingHom).comp
            (algebraMap R R'))
  have hK' :
      Ideal.map (algebraMap S S') (Ideal.map (algebraMap R S) I) ≤
        Ideal.map (algebraMap R' S') I' := by
    rw [hmap_eq]
    simpa [iR'] using Ideal.map_mono hI'
  exact zeroLocus_subset_flatOverBaseLocus_of_baseChange_of_map_le hflat hK'

end Ideal

end

/-! ### Lemma_15_18_2 (from Chap15) -/
open PrimeSpectrum
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} {S : Type v} {M : Type w} {R' : Type x}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable {I : Ideal R} {I' : Ideal R'}

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation "S'" => S ⊗[R] R'
local notation "M'" => S' ⊗[S] M

/- Domain-style sampling for Lemma 15.18.2:
- primary domain: flatness loci of modules on closed subsets of `Spec` under tensor-product base
  change and descent in commutative algebra;
- sampled owner declarations:
  `Module.flatOverBaseLocus`,
  `Ideal.zeroLocus_subset_flatOverBaseLocus_of_baseChange`,
  `zeroLocus_subset_flatOverBaseLocus_of_surjOn_zeroLocus_descends`;
- best owner abstraction: the canonical owner is `Module.flatOverBaseLocus`, while the chapter
  owner-level descent bridge is
  `zeroLocus_subset_flatOverBaseLocus_of_surjOn_zeroLocus_descends`;
- primitive data: the ideal comparison `IR' ≤ I'`, surjectivity of `V(I') → V(I)`, the local
  flatness locus condition on `Spec R'`, and the tensor-base-changed flatness-locus inclusion on
  `Spec (S ⊗[R] R')`;
- derived API: this file's source-facing specialization theorem, obtained by instantiating the
  later descent bridge with `R' := R`, `S' := S`, `R'' := R'`, and
  `M'' := (S ⊗[R] R') ⊗[S] M`.

Source/core/bridge triage:
- `source-facing`: the Stacks tensor-base-change descent statement for `(R → S, R → R', I, I')`;
- `core/canonical`: `Module.flatOverBaseLocus`;
- `bridge/view`: the later chapter theorem
  `zeroLocus_subset_flatOverBaseLocus_of_surjOn_zeroLocus_descends`, which this file specializes
  to the tensor-product base-change interface. -/

/-- Lemma 15.18.2: if the canonical closed-subset inclusion
`V(I'(S ⊗[R] R')) ⊆ Module.flatOverBaseLocus R' (S ⊗[R] R') ((S ⊗[R] R') ⊗[S] M)` holds after the
tensor-product base change `R → R'`, then the corresponding inclusion
`V(IS) ⊆ Module.flatOverBaseLocus R S M` already holds over `R`, provided `IR' ≤ I'`, the induced
map `V(I') → V(I)` is surjective, and `I'` has flat-over-`R` zero locus on `Spec R'`. -/
theorem zeroLocus_subset_flatOverBaseLocus_of_tensorBaseChange_descends
    (hI' : Ideal.map (algebraMap R R') I ≤ I')
    (hsurj : Set.SurjOn (PrimeSpectrum.comap (algebraMap R R'))
      (zeroLocus (I' : Set R')) (zeroLocus (I : Set R)))
    (hlocFlat : zeroLocus (I' : Set R') ⊆ Module.flatOverBaseLocus R R' R')
    (hbase :
      zeroLocus (Ideal.map (algebraMap R' S') I' : Set S') ⊆
        Module.flatOverBaseLocus R' S' M') :
    zeroLocus (Ideal.map (algebraMap R S) I : Set S) ⊆ Module.flatOverBaseLocus R S M :=
  zeroLocus_subset_flatOverBaseLocus_of_surjOn_zeroLocus_descends hI' hsurj hlocFlat hbase

end

/-! ### Lemma_15_18_3 (from Chap15) -/
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
