import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_19_2 (from Chap15) -/
open PrimeSpectrum
open scoped TensorProduct

universe u v w x y

section

variable {R : Type u} {S : Type v} {M : Type w} {R' : Type x} {R'' : Type y}
variable [CommRing R] [CommRing S] [CommRing R'] [CommRing R'']
variable [Algebra R S] [Algebra R R'] [Algebra R R''] [Algebra R' R'']
variable [IsScalarTower R R' R'']
variable [AddCommGroup M] [Module S M]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation "S1" => S ⊗[R] R'
local notation "S2" => S ⊗[R] R''
local notation "M1" => S1 ⊗[S] M
local notation "M2" => S2 ⊗[S] M

/-
Domain triage:
- primary domain: flatness loci under tensor-product base change in commutative algebra;
- sampled owner declarations: `Module.flatOverBaseLocus`,
  `Ideal.zeroLocus_subset_flatOverBaseLocus_iff`,
  `Ideal.zeroLocus_subset_flatOverBaseLocus_of_baseChange_of_map_le`,
  `Algebra.TensorProduct.map`;
- best owner abstraction: the flatness-locus owner `Module.flatOverBaseLocus`;
- bridge/view layer needed here: the explicit tensor-base-change map
  `Algebra.TensorProduct.map (AlgHom.id S S) (algebraMap R' R'')`, because the chapter keeps the
  target ring as `S ⊗[R] R''` rather than the associatively equivalent iterated tensor product from
  `15.18.1`;
- layer choice here: `source-facing`; the lemma keeps the Stacks sum ideal `I'S + J` visible, but
  states it directly as inclusion of the closed subset into the flatness locus rather than
  repeating its primewise expansion.
-/

/-- Tensor-base-change stability of a flatness-locus inclusion for the chapter’s preferred target
ring `S ⊗[R] R''`, expressed using the canonical map induced by `R' → R''` on the right tensor
factor. -/
theorem zeroLocus_subset_flatOverBaseLocus_of_tensorBaseChange_of_map_le
    {K1 : Ideal S1} {K2 : Ideal S2}
    (hflat : zeroLocus (K1 : Set S1) ⊆ Module.flatOverBaseLocus R' S1 M1)
    (hK2 :
      Ideal.map
          (Algebra.TensorProduct.map (AlgHom.id S S)
            (IsScalarTower.toAlgHom R R' R'')).toRingHom K1 ≤
        K2) :
    zeroLocus (K2 : Set S2) ⊆ Module.flatOverBaseLocus R'' S2 M2 := sorry

-- Proof sketch: apply the tensor-base-change bridge theorem to the source-facing sum ideal
-- `I'S1 + JS1`. The ideal-containment input is checked entrywise on the two summands, using `hI''`
-- on the `I'`-part and functoriality of `Ideal.map` on the `J`-part.
/-- Lemma 15.19.2: for the base change of Situation `15.19.1`, if condition `(15.19.1.1)` holds
over `R'` for an ideal `I'`, then it also holds after any further `R`-algebra base change
`R' → R''` for every ideal `I''` containing `I'R''`. -/
theorem localizedModule_flat_over_base_at_primes_of_zeroLocus_add_of_baseChange
    (J : Ideal S) (I' : Ideal R') (I'' : Ideal R'')
    (hI'' : Ideal.map (algebraMap R' R'') I' ≤ I'')
    (hflat : zeroLocus
      ((Ideal.map (algebraMap R' S1) I' + Ideal.map (algebraMap S S1) J : Ideal S1) : Set S1) ⊆
        Module.flatOverBaseLocus R' S1 M1) :
    zeroLocus
        ((Ideal.map (algebraMap R'' S2) I'' + Ideal.map (algebraMap S S2) J : Ideal S2) :
          Set S2) ⊆
      Module.flatOverBaseLocus R'' S2 M2 := by
  let K1 : Ideal S1 := Ideal.map (algebraMap R' S1) I' + Ideal.map (algebraMap S S1) J
  let K2 : Ideal S2 := Ideal.map (algebraMap R'' S2) I'' + Ideal.map (algebraMap S S2) J
  have hflat' : zeroLocus (K1 : Set S1) ⊆ Module.flatOverBaseLocus R' S1 M1 := by
    simpa [K1] using hflat
  have hmap :
      Ideal.map
          (Algebra.TensorProduct.map (AlgHom.id S S)
            (IsScalarTower.toAlgHom R R' R'')).toRingHom K1 ≤
        K2 := by
    let φ : S1 →ₐ[S] S2 := Algebra.TensorProduct.map (AlgHom.id S S)
      (IsScalarTower.toAlgHom R R' R'')
    change Ideal.map φ.toRingHom K1 ≤ K2
    dsimp [K1, K2, φ]
    rw [Ideal.map_sup]
    refine sup_le ?_ ?_
    · have hmap_eq :
          Ideal.map
              ((Algebra.TensorProduct.map (AlgHom.id S S)
                (IsScalarTower.toAlgHom R R' R'')) : S1 →+* S2)
              (Ideal.map (algebraMap R' S1) I') =
            Ideal.map (algebraMap R'' S2) (Ideal.map (algebraMap R' R'') I') := by
        rw [Ideal.map_map, Ideal.map_map]
        rfl
      rw [hmap_eq]
      exact le_trans (Ideal.map_mono hI'') le_sup_left
    · have hmap_eq :
          Ideal.map
              ((Algebra.TensorProduct.map (AlgHom.id S S)
                (IsScalarTower.toAlgHom R R' R'')) : S1 →+* S2)
              (Ideal.map (algebraMap S S1) J) =
            Ideal.map (algebraMap S S2) J := by
        rw [Ideal.map_map]
        congr 1
        ext x
        simp
      rw [hmap_eq]
      exact le_sup_right
  have hresult : zeroLocus (K2 : Set S2) ⊆ Module.flatOverBaseLocus R'' S2 M2 :=
    zeroLocus_subset_flatOverBaseLocus_of_tensorBaseChange_of_map_le hflat' hmap
  simpa [K2] using hresult

end

/-! ### Lemma_15_19_3 (from Chap15) -/
open PrimeSpectrum
open scoped TensorProduct

universe u v w x

section

variable {R' : Type u} {S' : Type v} {M' : Type w} {R'' : Type x}
variable [CommRing R'] [CommRing S'] [CommRing R'']
variable [Algebra R' S'] [Algebra R' R'']
variable [AddCommGroup M'] [Module S' M'] [Module R' M'] [IsScalarTower R' S' M']
variable {I' : Ideal R'} {I'' : Ideal R''} {J' : Ideal S'}

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation "S''" => S' ⊗[R'] R''
local notation "M''" => S'' ⊗[S'] M'

/- Domain triage:
- primary domain: flatness loci of modules over a base ring on closed subsets of `Spec`;
- sampled owner declarations: `Module.flatOverBaseLocus`,
  `Ideal.zeroLocus_subset_flatOverBaseLocus_iff`,
  `Ideal.zeroLocus_subset_flatOverBaseLocus_of_baseChange`;
- core/canonical owner: `Module.flatOverBaseLocus`;
- `Lemma 15.19.3` is a `bridge/view` descent statement for that owner, so the flatness hypothesis
  on `V(I'')` should use the same closed-subset inclusion rather than a duplicate primewise
  formulation.

Primitive data vs derived API:
- primitive data: the ring maps `R' → S'` and `R' → R''`, the ideals `I'`, `I''`, `J'`,
  surjectivity of `V(I'') → V(I')`, and the base-changed flatness-locus statement;
- derived API: the primewise flatness of the localizations of `R''` over `V(I'')`, already
  canonically expressed by `zeroLocus (I'' : Set R'') ⊆ Module.flatOverBaseLocus R' R'' R''`. -/

-- Proof sketch: given a prime `q'` of `S'` containing `I'S' + J'`, let `p'` be its image in
-- `Spec R'`. Use surjectivity of `V(I'') → V(I')` to choose `p'' ∈ V(I'')` above `p'`, then pick
-- a prime `q''` of `S' ⊗[R'] R''` above both `q'` and `p''`. The hypothesis for `(R'', I'')`
-- gives flatness of the localized base-changed module at `q''` over `R''`. Since `R''_{p''}` is
-- flat over `R'`, Lemma `10.100.1` descends this flatness to `M'_{q'}` over `R'`.
/-- Lemma 15.19.3: if the canonical closed-subset inclusion
`V(I''(S' ⊗[R'] R'') + J'(S' ⊗[R'] R'')) ⊆ Module.flatOverBaseLocus R'' (S' ⊗[R'] R'')
((S' ⊗[R'] R'') ⊗[S'] M')` holds after base change from `R'` to `R''`, then the corresponding
inclusion for `V(I'S' + J')` already holds over `R'`, provided `I'R'' ≤ I''`, the induced map
`V(I'') → V(I')` is surjective, and `I''` has flat-over-`R'` zero locus on `Spec R''`. -/
theorem zeroLocus_add_subset_flatOverBaseLocus_of_surjOn_zeroLocus_descends
    (hI'' : Ideal.map (algebraMap R' R'') I' ≤ I'')
    (hsurj : Set.SurjOn (PrimeSpectrum.comap (algebraMap R' R''))
      (zeroLocus (I'' : Set R'')) (zeroLocus (I' : Set R')))
    (hlocFlat : zeroLocus (I'' : Set R'') ⊆ Module.flatOverBaseLocus R' R'' R'')
    (hbase : zeroLocus
      ((Ideal.map (algebraMap R'' S'') I'' + Ideal.map (algebraMap S' S'') J' : Ideal S'') :
        Set S'') ⊆
        Module.flatOverBaseLocus R'' S'' M'') :
    zeroLocus ((Ideal.map (algebraMap R' S') I' + J' : Ideal S') : Set S') ⊆
      Module.flatOverBaseLocus R' S' M' := sorry

/-- The `J' = 0` specialization of Lemma 15.19.3, phrased directly as the canonical closed-subset
inclusion `V(I'S') ⊆ Module.flatOverBaseLocus R' S' M'`. -/
theorem zeroLocus_subset_flatOverBaseLocus_of_surjOn_zeroLocus_descends
    (hI'' : Ideal.map (algebraMap R' R'') I' ≤ I'')
    (hsurj : Set.SurjOn (PrimeSpectrum.comap (algebraMap R' R''))
      (zeroLocus (I'' : Set R'')) (zeroLocus (I' : Set R')))
    (hlocFlat : zeroLocus (I'' : Set R'') ⊆ Module.flatOverBaseLocus R' R'' R'')
    (hbase :
      zeroLocus (Ideal.map (algebraMap R'' S'') I'' : Set S'') ⊆
        Module.flatOverBaseLocus R'' S'' M'') :
    zeroLocus (Ideal.map (algebraMap R' S') I' : Set S') ⊆
      Module.flatOverBaseLocus R' S' M' := by
  have hbase' :
      zeroLocus
          ((Ideal.map (algebraMap R'' S'') I'' + Ideal.map (algebraMap S' S'') (⊥ : Ideal S') :
              Ideal S'') : Set S'') ⊆
        Module.flatOverBaseLocus R'' S'' M'' := by
    simpa [Ideal.map_bot, Ideal.add_eq_sup, sup_bot_eq] using hbase
  intro q hq
  exact zeroLocus_add_subset_flatOverBaseLocus_of_surjOn_zeroLocus_descends
    hI'' hsurj hlocFlat hbase' <| by
      simpa [Ideal.add_eq_sup, sup_bot_eq] using hq

end

/-! ### Lemma_15_19_4 (from Chap15) -/
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

/-! ### Lemma_15_19_5 (from Chap15) -/
open Ideal PrimeSpectrum
open scoped PrimeSpectrum

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable (I : Ideal R) (J : Ideal S)

local notation "K" => (I.map (algebraMap R S) + J : Ideal S)

/-
Domain triage:
- primary domain: flatness loci of finite modules over a Noetherian base, detected primewise on a
  closed subset of `Spec S` by the local criterion for flatness;
- sampled owner declarations:
  `StacksProject_2024.Chap10.Definition_10_17_1`'s closed-subset notation owner `V(-)`,
  `Module.flatOverBaseLocus`,
  `Ideal.zeroLocus_subset_flatOverBaseLocus_iff`,
  `flat_localizedModule_atPrime_of_flat_quotients_by_ideal_powers`,
  `localizedQuotientEquiv`,
  `Submodule.Quotient.module'`;
- best owner abstraction: the conclusion belongs on the chapter owner
  `Module.flatOverBaseLocus R S M`;
- primitive data: the ideals `I`, `J`, and the source-facing primewise flatness hypothesis on the
  quotient modules `M_q / I^n M_q`; the source wording `(M / I^n M)_q` is a bridge view, related
  to this owner-level local criterion input by `localizedQuotientEquiv`;
- derived API: the quotient `R ⧸ I^n`-module structure on
  `LocalizedModule.AtPrime q.asIdeal M ⧸ (I ^ n) • ⊤`, obtained canonically from
  `Submodule.Quotient.module'`, and the resulting closed-subset inclusion into
  `Module.flatOverBaseLocus`.

Source/core/bridge triage:
- `source-facing`: the hypothesis that for every `q ∈ V(I.map (algebraMap R S) + J)` and every
  `n ≥ 1`, the local quotient `M_q / I^n M_q` is flat over `R / I^n`;
- `core/canonical`: `Module.flatOverBaseLocus`, `Ideal.zeroLocus_subset_flatOverBaseLocus_iff`,
  and the local criterion
  `flat_localizedModule_atPrime_of_flat_quotients_by_ideal_powers`;
- `bridge/view`: the source presentation `(M / I^n M)_q`, which this file demotes in favor of the
  canonically equivalent quotient of the localized module `M_q / I^n M_q`.

The source hypothesis remains primewise because the ambient target ring for the quotient modules is
the localization of `S` at `q`, not a fixed global target ring, so the chapter owner
`Module.flatOverBaseLocus` does not apply to those hypotheses without adding an unnecessary
quotient-localization bridge layer.
-/

-- Proof sketch: fix `q ∈ V(J + IS)` and apply the local criterion for flatness from Lemma
-- `10.99.11` to the local homomorphism `R → S_q` and the finite `S_q`-module `M_q`. The
-- hypothesis supplies flatness of each quotient `M_q / I^n M_q` over `R / I^n`, so the criterion
-- yields flatness of `M_q` over `R`.
/-- Lemma 15.19.5: if `R` and `S` are Noetherian, `M` is finite over `S`, and for every `n ≥ 1`
and every prime `q ∈ V(J + IS)` the quotient `M_q / I^n M_q` is flat over `R / I^n`,
then for every `q ∈ V(J + IS)` the localization `M_q` is flat over `R`. -/
theorem localizedModule_flat_over_base_at_primes_of_zeroLocus_add_of_flat_quotient_powers
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Finite S M]
    (hquot : ∀ (q : PrimeSpectrum S) (_ : q ∈ V((K : Set S))) (n : ℕ) (_ : 1 ≤ n),
      Module.Flat (R ⧸ I ^ n)
        (LocalizedModule.AtPrime q.asIdeal M ⧸
          ((I ^ n) • (⊤ : Submodule R (LocalizedModule.AtPrime q.asIdeal M))))) :
    V((K : Set S)) ⊆
      Module.flatOverBaseLocus R S M := sorry

end
