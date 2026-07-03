import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Regular.Basic
import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.Ideal.Pure

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_30_1 (from Chap15) -/
noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open MonoidalCategory

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]

/- Domain triage:
* primary domain: Koszul complexes and regular sequences for finite families in commutative
  algebra;
* sampled owner API: `koszulComplexOn`, `HomologicalComplex.tensorObj`, `ρ_`,
  `HomologicalComplex.homologyMapIso`;
* layer split: `koszulComplexOn` is the `Fin`-family owner for the complex itself, and this file
  is the source-facing owner layer for the regularity predicates on finite families;
* primitive data vs derived API: the only new source-facing primitive here is the degree-one
  vanishing predicate `IsH1RegularOn`; `IsKoszulRegularSequence` and `IsH1RegularSequence` are the
  regular-module specializations derived from the module-valued owners.
-/

section ModuleRegularity

variable (M : Type u) [AddCommGroup M] [Module R M]

/-- Definition 15.30.1 (1): a finite family `f` is `M`-Koszul-regular if every positive homology
object of the Koszul complex on `f`, after tensoring with `M`, vanishes. -/
noncomputable abbrev IsKoszulRegularOn {r : ℕ} (f : Fin r → R) : Prop :=
  ∀ i : ℕ, 1 ≤ i →
    IsZero ((HomologicalComplex.tensorObj (koszulComplexOn f) ((ChainComplex.single₀ (ModuleCat R)).obj
      (ModuleCat.of R M))).homology i)

/-- Definition 15.30.1 (2): a finite family `f` is `M`-`H_1`-regular if the first homology object
of the Koszul complex on `f`, after tensoring with `M`, vanishes. -/
noncomputable def IsH1RegularOn {r : ℕ} (f : Fin r → R) : Prop :=
  IsZero ((HomologicalComplex.tensorObj (koszulComplexOn f) ((ChainComplex.single₀ (ModuleCat R)).obj
    (ModuleCat.of R M))).homology 1)

end ModuleRegularity

/-- Definition 15.30.1 (3): a finite family `f` is Koszul-regular if it is Koszul-regular on the
regular module `R`. -/
noncomputable abbrev IsKoszulRegularSequence {r : ℕ} (f : Fin r → R) : Prop :=
  IsKoszulRegularOn R f

/-- The ring-theoretic predicate `IsKoszulRegularSequence f` is equivalently the vanishing of all
positive homology objects of `koszulComplexOn f`. -/
theorem isKoszulRegularSequence_iff {r : ℕ} (f : Fin r → R) :
    IsKoszulRegularSequence f ↔
      ∀ i : ℕ, 1 ≤ i → IsZero ((koszulComplexOn f).homology i) := by
  let e :
      HomologicalComplex.tensorObj (koszulComplexOn f)
          ((ChainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R R)) ≅
        koszulComplexOn f :=
    ρ_ (koszulComplexOn f)
  constructor
  · intro h i hi
    exact (Iso.isZero_iff (HomologicalComplex.homologyMapIso e i)).mp (h i hi)
  · intro h i hi
    exact (Iso.isZero_iff (HomologicalComplex.homologyMapIso e i)).mpr (h i hi)

/-- Definition 15.30.1 (4): a finite family `f` is `H_1`-regular if it is `H_1`-regular on the
regular module `R`. -/
noncomputable abbrev IsH1RegularSequence {r : ℕ} (f : Fin r → R) : Prop :=
  IsH1RegularOn R f

/-- The ring-theoretic predicate `IsH1RegularSequence f` is equivalently the vanishing of the first
homology object of `koszulComplexOn f`. -/
theorem isH1RegularSequence_iff {r : ℕ} (f : Fin r → R) :
    IsH1RegularSequence f ↔ IsZero ((koszulComplexOn f).homology 1) := by
  let e :
      HomologicalComplex.tensorObj (koszulComplexOn f)
          ((ChainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R R)) ≅
        koszulComplexOn f :=
    ρ_ (koszulComplexOn f)
  simpa [IsH1RegularSequence, IsH1RegularOn] using
    (Iso.isZero_iff (HomologicalComplex.homologyMapIso e 1))

end RingTheory.Sequence

/-! ### Lemma_15_30_2 (from Chap15) -/
universe u

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

/- Domain-style sampling:
- primary domain: regular and weakly regular sequences versus Koszul-regularity in commutative
  algebra;
- sampled owner declarations: `RingTheory.Sequence.IsWeaklyRegular`,
  `RingTheory.Sequence.IsRegular`, `RingTheory.Sequence.IsKoszulRegularOn`,
  `RingTheory.Sequence.IsKoszulRegularSequence`;
- best owner abstraction: `IsKoszulRegularOn` is the Chapter 15 owner for module-valued
  Koszul-regularity, with the source-facing list `rs` entering only through the canonical finite
  family `rs.get : Fin rs.length → R`, while the bridge itself should live owner-style under
  `IsWeaklyRegular` and `IsRegular`;
- primitive data: the source list `rs : List R` and the regular-sequence owner hypothesis on that
  list;
- derived API: the bridge from list-level weak/regular sequence hypotheses to the owner predicate
  `IsKoszulRegularOn M rs.get`;
- layer triage: the Stacks lemma here is `source-facing` on the list side and `bridge/view` on the
  conclusion side, so the local list-valued Koszul-complex wrapper should be deleted in favor of
  the owner predicate from `Definition 15.30.1`.
-/

-- Proof sketch: interpret the source list as the canonical finite family `rs.get`. Then induct on
-- the list using `isWeaklyRegular_cons_iff`. Lemma `15.28.8` identifies the Koszul complex of a
-- nonempty family with the homotopy cofiber of multiplication by its last entry, and the
-- resulting long exact homology sequence compares positive homology with the Koszul complex of the
-- tail on the successive quotient module.
namespace IsWeaklyRegular

/-- Lemma 15.30.2, weakly regular owner form: if a list `rs` is weakly regular on `M`, then the
canonical finite family `rs.get` is Koszul-regular on `M`. -/
theorem isKoszulRegularOn {rs : List R} (hreg : IsWeaklyRegular M rs) :
    IsKoszulRegularOn M rs.get := sorry

end IsWeaklyRegular

-- Proof sketch: every regular sequence is weakly regular, so the previous theorem applies to the
-- underlying weakly regular sequence.
namespace IsRegular

/-- Every regular sequence on `M` is Koszul-regular on `M`, expressed through the canonical finite
family owner `IsKoszulRegularOn`. -/
theorem isKoszulRegularOn {rs : List R} (hreg : IsRegular M rs) :
    IsKoszulRegularOn M rs.get :=
  hreg.toIsWeaklyRegular.isKoszulRegularOn

end IsRegular

end RingTheory.Sequence

/-! ### Lemma_15_30_3 (from Chap15) -/
universe u

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

-- Proof sketch: unfold `IsKoszulRegularOn`; specializing the defining vanishing statement to
-- degree `1` gives exactly `IsH1RegularOn`.
/-- Lemma 15.30.3 (1): an `M`-Koszul-regular finite family is `M`-`H_1`-regular. -/
theorem isH1RegularOn_of_isKoszulRegularOn {r : ℕ} {f : Fin r → R}
    (hKoszul : IsKoszulRegularOn M f) : IsH1RegularOn M f := by
  simpa [IsKoszulRegularOn, IsH1RegularOn] using hKoszul 1 le_rfl

-- Proof sketch: unfold `IsKoszulRegularSequence`; specializing the defining vanishing statement to
-- degree `1` gives exactly `IsH1RegularSequence`.
/-- Lemma 15.30.3 (2): a Koszul-regular finite family is `H_1`-regular. -/
theorem isH1RegularSequence_of_isKoszulRegularSequence {r : ℕ} {f : Fin r → R}
    (hKoszul : IsKoszulRegularSequence f) : IsH1RegularSequence f := by
  simpa [IsKoszulRegularSequence, IsH1RegularSequence] using hKoszul 1 le_rfl

end RingTheory.Sequence

/-! ### Lemma_15_30_4 (from Chap15) -/
universe u

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

/- Domain-style sampling for Lemma 15.30.4:
* primary domain: module-valued `H_1`- and Koszul-regularity of finite families via Koszul
  homology;
* sampled owner declarations: `IsH1RegularOn`, `IsKoszulRegularOn`,
  `koszulComplex_iso_homotopyCofiber_truncate_last`, and
  `koszulComplexOn_snoc_mul_exists_homotopyEquiv_homotopyCofiber`;
* source-facing layer: the two `Fin.snoc` closure statements below;
* core/canonical layer: the Koszul-complex owner `K^•(-)` together with the canonical
  homotopy-cofiber comparison from Lemma `15.28.11`;
* bridge/view layer: the long exact homology argument transporting the homotopy-cofiber model to
  vanishing statements for `IsH1RegularOn` and `IsKoszulRegularOn`;
* primitive vs derived API: the primitive public content here is exactly the `Fin.snoc` owner
  surface, while any list-based reformulation is derived transport across `List.ofFn` and should
  not survive as a parallel theorem.
-/

section

variable {r : ℕ} {fs : Fin r → R} {f g : R}

namespace IsH1RegularOn

-- Proof sketch: use the exact sequence from Lemma `15.28.11` after tensoring with `M` and take
-- homology in degree `1`; the first and third terms vanish by the two hypotheses, so the middle
-- term vanishes as well.
/-- Lemma 15.30.4, owner form: if `Fin.snoc fs f` and `Fin.snoc fs g` are `M`-`H_1`-regular, then
`Fin.snoc fs (f * g)` is also `M`-`H_1`-regular. -/
theorem snoc_mul (hf : IsH1RegularOn M (Fin.snoc fs f)) (hg : IsH1RegularOn M (Fin.snoc fs g)) :
    IsH1RegularOn M (Fin.snoc fs (f * g)) := sorry

end IsH1RegularOn

namespace IsKoszulRegularOn

-- Proof sketch: apply the long exact homology sequence coming from Lemma `15.28.11` in every
-- positive degree. The outer terms vanish because `Fin.snoc fs f` and `Fin.snoc fs g` are
-- `M`-Koszul-regular, so the middle term vanishes as well.
/-- Lemma 15.30.4, owner form: if `Fin.snoc fs f` and `Fin.snoc fs g` are `M`-Koszul-regular, then
`Fin.snoc fs (f * g)` is also `M`-Koszul-regular. -/
theorem snoc_mul
    (hf : IsKoszulRegularOn M (Fin.snoc fs f)) (hg : IsKoszulRegularOn M (Fin.snoc fs g)) :
    IsKoszulRegularOn M (Fin.snoc fs (f * g)) := sorry

end IsKoszulRegularOn

end

end RingTheory.Sequence

/-! ### Lemma_15_30_5 (from Chap15) -/
noncomputable section

universe u

open scoped TensorProduct

namespace RingTheory.Sequence

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

variable {M N : Type u} [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/- Domain triage:
* primary domain: module-valued regularity predicates defined by Koszul homology and their
  behavior under flat base change;
* sampled owner API: `IsH1RegularOn`, `IsKoszulRegularOn`, `IsBaseChange`, `TensorProduct.isBaseChange`,
  and the earlier chapter base-change pattern `IsQuasiRegular.of_flat_of_isBaseChange`;
* owner abstraction: the source-facing owners are `IsH1RegularOn` and `IsKoszulRegularOn`, while
  `IsBaseChange S f` is the core/canonical owner for the chosen base-change realization;
* primitive data vs derived API: the primitive content here is the owner-level transport across an
  arbitrary `IsBaseChange S f`; the tensor-product statements are derived bridge/view
  specializations obtained from `TensorProduct.isBaseChange`.
-/

namespace IsH1RegularOn

-- Proof sketch: identify the Koszul complex on the image family `algebraMap R S ∘ f` with the
-- base change of the Koszul complex on `f` along the owner map `M →ₗ[R] N`. Since `S` is flat over
-- `R`, tensoring with `S` preserves the vanishing of first homology, so `H₁`-regularity descends
-- across any canonical base-change realization.
/-- Lemma 15.30.5 (1), owner form: `H_1`-regularity is preserved by flat base change along an
owner-level base-change map. The textbook tensor-product statement is the specialization
`IsH1RegularOn.of_flat`. -/
theorem of_flat_of_isBaseChange {f : M →ₗ[R] N} (hf : IsBaseChange S f) {r : ℕ}
    {s : Fin r → R} (hreg : IsH1RegularOn M s) :
    IsH1RegularOn N (fun i ↦ algebraMap R S (s i)) := sorry

/-- Lemma 15.30.5 (1): if `s` is an `M`-`H_1`-regular sequence over `R`, then its image in `S` is
an `S ⊗[R] M`-`H_1`-regular sequence after flat base change. -/
theorem of_flat {r : ℕ} {s : Fin r → R} (hreg : IsH1RegularOn M s) :
    IsH1RegularOn (S ⊗[R] M) (fun i ↦ algebraMap R S (s i)) := by
  simpa using hreg.of_flat_of_isBaseChange (TensorProduct.isBaseChange R M S)

end IsH1RegularOn

namespace IsKoszulRegularOn

-- Proof sketch: identify `(K^•(s) ⊗ M)` after applying the owner base-change map
-- `M →ₗ[R] N` with the tensor Koszul complex over `S` on the image family `algebraMap R S ∘ s`.
-- Flatness makes homology commute with this base change, so vanishing of all positive homology
-- groups is preserved across any canonical base-change realization.
/-- Lemma 15.30.5 (2), owner form: Koszul-regularity is preserved by flat base change along an
owner-level base-change map. The textbook tensor-product statement is the specialization
`IsKoszulRegularOn.of_flat`. -/
theorem of_flat_of_isBaseChange {f : M →ₗ[R] N} (hf : IsBaseChange S f) {r : ℕ}
    {s : Fin r → R} (hreg : IsKoszulRegularOn M s) :
    IsKoszulRegularOn N (fun i ↦ algebraMap R S (s i)) := sorry

/-- Lemma 15.30.5 (2): if `s` is an `M`-Koszul-regular sequence over `R`, then its image in `S`
is an `S ⊗[R] M`-Koszul-regular sequence after flat base change. -/
theorem of_flat {r : ℕ} {s : Fin r → R} (hreg : IsKoszulRegularOn M s) :
    IsKoszulRegularOn (S ⊗[R] M) (fun i ↦ algebraMap R S (s i)) := by
  simpa using hreg.of_flat_of_isBaseChange (TensorProduct.isBaseChange R M S)

end IsKoszulRegularOn

end RingTheory.Sequence

/-! ### Lemma_15_30_6 (from Chap15) -/
universe u

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

-- Proof sketch: identify quasi-regularity with the graded coefficient criterion for
-- `quasiRegularSequenceAssociatedGradedMap M (List.ofFn f)`. The `H₁`-regularity hypothesis
-- forces the degree-one Koszul relations to be generated by the trivial ones, and the argument in
-- the Stacks proof uses Lemmas `15.30.4`, `15.30.5`, and `15.28.4` to induct on the total degree
-- of a homogeneous relation and conclude that every coefficient lies in the ideal generated by
-- `f`, yielding bijectivity of the associated-graded map.
/-- Lemma 15.30.6: if a finite family `f` is `M`-`H_1`-regular, then the associated finite
sequence `List.ofFn f` is `M`-quasi-regular. -/
theorem isQuasiRegular_of_isH1RegularOn {r : ℕ} {f : Fin r → R} (hH1 : IsH1RegularOn M f) :
    IsQuasiRegular M (List.ofFn f) := sorry

end RingTheory.Sequence

/-! ### Lemma_15_30_7 (from Chap15) -/
universe u

open RingTheory

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]

-- Proof sketch: combine the four implications already isolated in the surrounding development:
-- regular implies Koszul-regular, Koszul-regular implies `H_1`-regular, `H_1`-regular implies
-- quasi-regular, and over a Noetherian local ring a quasi-regular sequence in the maximal ideal
-- is regular on every nonzero finite module.
/-- Lemma 15.30.7: for a finite family `f` of elements of the maximal ideal of a Noetherian local
ring, on a nonzero finite `R`-module `M`, the following are equivalent: `List.ofFn f` is
`M`-regular, `f` is `M`-Koszul-regular, `f` is `M`-`H_1`-regular, and `List.ofFn f` is
`M`-quasi-regular. -/
theorem regular_koszul_h1_quasi_tfae_of_mem_maximalIdeal {r : ℕ} (f : Fin r → R)
    (hf : ∀ i, f i ∈ IsLocalRing.maximalIdeal R) :
    List.TFAE
      [IsRegular M (List.ofFn f), IsKoszulRegularOn M f, IsH1RegularOn M f,
        IsQuasiRegular M (List.ofFn f)] := sorry

-- Proof sketch: specialize `regular_koszul_h1_quasi_tfae_of_mem_maximalIdeal` to the regular
-- module `M = R`; the ring-specific Koszul and `H_1` predicates are exactly the corresponding
-- module predicates for `M = R`, and `IsQuasiRegularSequence` is by definition quasi-regularity
-- on the regular module.
/-- For the regular module `R`, regularity, Koszul-regularity, `H_1`-regularity, and
quasi-regularity of a finite sequence in the maximal ideal are equivalent. -/
theorem regularSequence_koszul_h1_quasi_tfae_of_mem_maximalIdeal [Nontrivial R] {r : ℕ}
    (f : Fin r → R) (hf : ∀ i, f i ∈ IsLocalRing.maximalIdeal R) :
    List.TFAE
      [IsRegular R (List.ofFn f), IsKoszulRegularSequence f, IsH1RegularSequence f,
        IsQuasiRegularSequence (List.ofFn f)] := by
  have hTFAE :
      List.TFAE
        [IsRegular R (List.ofFn f), IsKoszulRegularOn R f, IsH1RegularOn R f,
          IsQuasiRegular R (List.ofFn f)] :=
    regular_koszul_h1_quasi_tfae_of_mem_maximalIdeal f hf
  simpa [IsKoszulRegularSequence, IsH1RegularSequence, IsQuasiRegularSequence] using hTFAE

end RingTheory.Sequence

/-! ### Lemma_15_30_8 (from Chap15) -/
universe u

namespace RingTheory.Sequence

variable {A : Type u} [CommRing A]

/- Domain triage:
* primary domain: `H₁`-regular finite sequences and the ideal-theoretic criterion
  `I ⊓ J = I * J` in commutative algebra;
* sampled owner API:
  `RingTheory.Sequence.IsH1RegularSequence`,
  `RingTheory.Sequence.IsH1RegularOn.isQuasiRegular`,
  `Ideal.ofList`,
  `injective_lTensor_quotient_iff_inf_eq_mul`;
* `source-facing`: the public equality for `Ideal.span (Set.range g)`;
* `core/canonical`: the finite-sequence owner data are organized around `List.ofFn g`, so the
  canonical ideal generated by the family is `Ideal.ofList (List.ofFn g)`;
* `bridge/view`: rewrite that owner ideal to the source-facing `Ideal.span (Set.range g)` only at
  the public theorem boundary.
-/

-- Proof sketch: work first with the owner ideal `Ideal.ofList (List.ofFn g)`, since the chapter's
-- finite-sequence regularity API is organized around `List.ofFn`. The `H₁`-regularity hypothesis
-- gives injectivity of the associated canonical tensor map for that owner ideal.
/-- The canonical tensor map attached to the owner ideal `Ideal.ofList (List.ofFn g)` is injective
when the image family of `g` in `A ⧸ I` is `H_1`-regular. -/
private theorem injective_lTensor_ofList_of_isH1RegularSequence_quotient {m : ℕ} (I : Ideal A)
    (g : Fin m → A) (hreg : IsH1RegularSequence (fun i ↦ Ideal.Quotient.mk I (g i))) :
    Function.Injective ((Ideal.ofList (List.ofFn g)).subtype.lTensor (A ⧸ I)) := sorry

-- Proof sketch: first use the owner-level injectivity statement for `Ideal.ofList (List.ofFn g)`,
-- then rewrite that ideal as the source-facing `Ideal.span (Set.range g)` and conclude via the
-- mathlib owner theorem `injective_lTensor_quotient_iff_inf_eq_mul`.
/-- Lemma 15.30.8: if the image of a finite family `g` in `A ⧸ I` is `H_1`-regular, then the
intersection of `I` with the ideal generated by `g` is the product `I * (g_1, \ldots, g_m)`. -/
theorem ideal_inf_span_eq_mul_of_isH1RegularSequence_quotient {m : ℕ} (I : Ideal A)
    (g : Fin m → A) (hreg : IsH1RegularSequence (fun i ↦ Ideal.Quotient.mk I (g i))) :
    I ⊓ Ideal.span (Set.range g) = I * Ideal.span (Set.range g) := by
  have hspan : Ideal.ofList (List.ofFn g) = Ideal.span (Set.range g) := by
    ext x
    simp [Ideal.ofList, List.mem_ofFn', Set.range]
  rw [← hspan]
  rw [← injective_lTensor_quotient_iff_inf_eq_mul]
  exact injective_lTensor_ofList_of_isH1RegularSequence_quotient I g hreg

end RingTheory.Sequence

/-! ### Lemma_15_30_9 (from Chap15) -/
universe u

namespace Ideal

open RingTheory.Sequence

variable {A : Type u} [CommRing A]

/- Domain triage:
* primary domain: commutative algebra of ideals in quotient rings and finite `H₁`-regular
  sequences;
* sampled owner declarations in this domain:
  - `Ideal.map_span`,
  - `Ideal.map_eq_iff_sup_ker_eq_of_surjective`,
  - `Ideal.mk_ker`,
  - `RingTheory.Sequence.ideal_inf_span_eq_mul_of_isH1RegularSequence_quotient`;
* layer split:
  - `source-facing`: the quotient-generation hypothesis for one fixed pair `I ≤ J`, expressed by
    a finite family in the quotient ring `A ⧸ I`;
  - `core/canonical`: the ideal owner surface, using the quotient ideal correspondence through
    `Ideal.map_eq_iff_sup_ker_eq_of_surjective` together with the finite-sequence bridge from
    Lemma `15.30.8`;
  - `bridge/view`: choose lifts of the quotient family privately, rewrite the quotient-span
    hypothesis as equality of mapped ideals, then transport it back through the canonical quotient
    ideal correspondence to recover `J = I ⊔ Ideal.span (Set.range g)`.
* primitive data vs derived API: the primitive source data are the ideals `I ≤ J` and the finite
  `H₁`-regular family in the quotient; the chosen lifts in `A` and the equality
  `J = I ⊔ Ideal.span (Set.range g)` are derived from the canonical quotient ideal correspondence
  and should not be stored as separate public data.
-/

/-- Lemma 15.30.9: if the quotient ideal `J / I` is generated in `A ⧸ I` by an `H_1`-regular
finite sequence, then `I ∩ J^2 = IJ`. -/
theorem inf_sq_eq_mul_of_quotient_generated_by_h1RegularSequence
    (I J : Ideal A) (hIJ : I ≤ J)
    (hgen :
      ∃ (m : ℕ) (f : Fin m → A ⧸ I),
        J.map (Ideal.Quotient.mk I) = Ideal.span (Set.range f) ∧ IsH1RegularSequence f) :
    I ⊓ J ^ 2 = I * J := by
  classical
  obtain ⟨m, f, hmap, hreg⟩ := hgen
  let π : A →+* A ⧸ I := Ideal.Quotient.mk I
  choose g hg using fun i ↦ Ideal.Quotient.mk_surjective (f i)
  let K : Ideal A := Ideal.span (Set.range g)
  have hg' : (fun i ↦ π (g i)) = f := funext hg
  have hJ : J = I ⊔ K := by
    have hrange : Set.range f = π '' Set.range g := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨g i, ⟨i, rfl⟩, hg i⟩
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, (hg i).symm⟩
    have hmap' : J.map π = K.map π := by
      rw [hmap]
      simpa [K, Ideal.map_span] using congrArg Ideal.span hrange
    rw [Ideal.map_eq_iff_sup_ker_eq_of_surjective π Ideal.Quotient.mk_surjective] at hmap'
    simpa [π, K, Ideal.mk_ker, sup_eq_left.mpr hIJ, sup_comm] using hmap'
  have hIK :
      I ⊓ K = I * K := by
    have hreg' : IsH1RegularSequence (fun i ↦ π (g i)) := by
      simpa [π, hg'] using hreg
    simpa [π, K] using ideal_inf_span_eq_mul_of_isH1RegularSequence_quotient I g hreg'
  have hKJ : K ≤ J := by
    rw [hJ]
    exact le_sup_right
  have hIK_le_hIJ :
      I * K ≤ I * J :=
    Ideal.mul_mono_right hKJ
  have hJ_sq :
      J ^ 2 = I * J ⊔ K ^ 2 := by
    calc
      J ^ 2 = J * J := by rw [pow_two]
      _ = (I ⊔ K) * J := by rw [hJ]
      _ = I * J ⊔ K * J := by rw [Ideal.sup_mul]
      _ = I * J ⊔ K * (I ⊔ K) := by rw [hJ]
      _ = I * J ⊔ (K * I ⊔ K ^ 2) := by rw [Ideal.mul_sup, pow_two]
      _ = I * J ⊔ (I * K ⊔ K ^ 2) := by rw [Ideal.mul_comm K I]
      _ = I * J ⊔ K ^ 2 := by
        rw [← sup_assoc, sup_eq_left.mpr hIK_le_hIJ]
  have hIinfKsq :
      I ⊓ K ^ 2 ≤ I * J := by
    calc
      I ⊓ K ^ 2 ≤ I ⊓ K := by
        refine inf_le_inf_left _ ?_
        simpa [pow_two] using (show K * K ≤ K from Ideal.mul_le_right)
      _ = I * K := hIK
      _ ≤ I * J := hIK_le_hIJ
  have hmul_le_I : I * J ≤ I := Ideal.mul_le_right
  apply le_antisymm
  · calc
      I ⊓ J ^ 2 = I ⊓ (I * J ⊔ K ^ 2) := by rw [hJ_sq]
      _ = I * J ⊔ (I ⊓ K ^ 2) := by
        rw [sup_comm, ← inf_sup_assoc_of_le (K ^ 2) hmul_le_I, sup_comm]
      _ = I * J := sup_eq_left.mpr hIinfKsq
      _ ≤ I * J := le_rfl
  · refine le_inf Ideal.mul_le_right ?_
    have hmul : I * J ≤ J * J := Ideal.mul_mono_left hIJ
    simpa [pow_two] using hmul

end Ideal

/-! ### Lemma_15_30_10 (from Chap15) -/
universe u

namespace RingTheory.Sequence

variable {A : Type u} [CommRing A]

/- Domain triage:
* primary domain: quasi-regular and `H₁`-regular finite sequences in commutative algebra;
* sampled owner API:
  `RingTheory.Sequence.IsQuasiRegularSequence`,
  `RingTheory.Sequence.IsH1RegularSequence`,
  `RingTheory.Sequence.IsH1RegularOn.isQuasiRegular`,
  `RingTheory.Sequence.isH1RegularSequence_append_of_quotient`;
* core/canonical owners: `IsQuasiRegularSequence` on the list side and
  `IsH1RegularSequence` on the finite-family side;
* primitive data vs derived API: the primitive source data are the finite families `f` and `g`;
  the ambient ideal is canonically `Ideal.span (Set.range f)`, so an extra ideal parameter and an
  equality witness are derived presentation data and should not remain in the public interface;
* layer: `bridge/view`, since the source-facing append statement is expressed through the canonical
  owner predicates rather than a separate wrapper around a named ideal.
-/

-- Proof sketch: the quotient-side `H₁`-regularity hypothesis is already stated for the canonical
-- ideal generated by `f`, namely `Ideal.span (Set.range f)`, so no separate ideal parameter is
-- needed. The owner-level conclusion for quasi-regularity naturally lives on the concatenated list
-- `List.ofFn f ++ List.ofFn g` rather than on the coordinate presentation `List.ofFn (Fin.append f g)`.
/-- Lemma 15.30.10: if the finite sequence `f` is quasi-regular in `A`, and the images of `g` in
the quotient ring `A ⧸ Ideal.span (Set.range f)` form an `H_1`-regular sequence, then the
concatenated finite sequence `f_1, \ldots, f_n, g_1, \ldots, g_m` is quasi-regular in `A`. -/
theorem isQuasiRegularSequence_append_of_quotient_h1Regular {n m : ℕ} (f : Fin n → A)
    (g : Fin m → A)
    (hf : IsQuasiRegularSequence (List.ofFn f))
    (hg : IsH1RegularSequence (fun j ↦ Ideal.Quotient.mk (Ideal.span (Set.range f)) (g j))) :
    IsQuasiRegularSequence (List.ofFn f ++ List.ofFn g) := sorry

end RingTheory.Sequence

/-! ### Lemma_15_30_11 (from Chap15) -/
noncomputable section

universe u

namespace Ideal

theorem ofList_ofFn_eq_span_range {A : Type u} [CommRing A] {n : ℕ} (f : Fin n → A) :
    Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f) := by
  ext x
  simp [Ideal.ofList, List.mem_ofFn', Set.range]

end Ideal

namespace RingTheory.Sequence

variable {A : Type u} [CommRing A]

/- 
Domain triage:
* primary domain: `H₁`-regular finite sequences in commutative algebra and their behavior under
  passage to a quotient by the ideal generated by an initial block;
* sampled owner API:
  `RingTheory.Sequence.IsH1RegularSequence`,
  `RingTheory.Sequence.isH1RegularSequence_iff`,
  `RingTheory.Sequence.IsH1RegularOn.isQuasiRegular`,
  `RingTheory.Sequence.IsQuasiRegular.tail_quotient`,
  `Ideal.ofList`,
  `Ideal.ofList_ofFn_eq_span_range`;
* core/canonical owner abstraction: the finite-family predicate `IsH1RegularSequence`, with the
  canonical quotient-by-prefix owner API organized around `Ideal.ofList (List.ofFn f)`;
* primitive data: the prefix `f` and the tail `g`;
  derived API: the quotient-side `H₁`-regularity statement for the image family of `g` in the
  quotient by the prefix ideal generated by `f`;
* layer: `bridge/view`, since this item keeps the source-facing append statement while reusing the
  chapter's canonical quotient-by-prefix owner abstraction.
-/

-- Owner-level bridge: first state the append criterion for the canonical prefix ideal
-- `Ideal.ofList (List.ofFn f)` used by the quotient-by-prefix regular-sequence API.
private theorem isH1RegularSequence_append_of_quotient_ofList {n m : ℕ} (f : Fin n → A)
    (g : Fin m → A) (hf : IsH1RegularSequence f)
    (hg : IsH1RegularSequence (fun j ↦ Ideal.Quotient.mk (Ideal.ofList (List.ofFn f)) (g j))) :
    IsH1RegularSequence (Fin.append f g) := sorry

-- Proof sketch: prove the owner-level append statement for the canonical prefix ideal
-- `Ideal.ofList (List.ofFn f)`, then rewrite that quotient to the source-facing quotient
-- `A ⧸ Ideal.span (Set.range f)` via `Ideal.ofList_ofFn_eq_span_range`.
/-- Lemma 15.30.11: if `f` is an `H_1`-regular sequence in `A`, and the images of `g` form an
`H_1`-regular sequence in the quotient ring `A ⧸ Ideal.span (Set.range f)`, then the concatenated
sequence `Fin.append f g` is `H_1`-regular in `A`. -/
theorem isH1RegularSequence_append_of_quotient {n m : ℕ} (f : Fin n → A) (g : Fin m → A)
    (hf : IsH1RegularSequence f)
    (hg : IsH1RegularSequence (fun j ↦ Ideal.Quotient.mk (Ideal.span (Set.range f)) (g j))) :
    IsH1RegularSequence (Fin.append f g) := by
  rw [← Ideal.ofList_ofFn_eq_span_range f] at hg
  exact isH1RegularSequence_append_of_quotient_ofList f g hf hg

end RingTheory.Sequence

/-! ### Lemma_15_30_12 (from Chap15) -/
universe u

namespace RingTheory.Sequence

variable {A : Type u} [CommRing A]

/-
Domain triage:
* primary domain: `H₁`-regular and quasi-regular finite sequences in commutative algebra;
* sampled owner API:
  `Ideal.ofList`,
  `Ideal.ofList_ofFn_eq_span_range`,
  `RingTheory.Sequence.IsH1RegularSequence`,
  `RingTheory.Sequence.IsH1RegularOn.isQuasiRegular`,
  `RingTheory.Sequence.IsQuasiRegular.tail_quotient`;
* core/canonical owner abstraction: the canonical quotient-by-prefix and tail construction already
  organized by `IsQuasiRegular.tail_quotient`, with the prefix ideal canonically expressed as
  `Ideal.ofList (List.ofFn f)`;
* primitive data: the prefix `f` and the tail `g`;
  derived API: the source-facing quotient ring `A ⧸ Ideal.span (Set.range f)` and the quotient-side
  `H₁`-regularity statement for the image family of `g`;
* layer: `bridge/view`, since the public theorem keeps the source-facing quotient by
  `(f₁, \ldots, fₙ)` while the owner-level regular-sequence API is already organized around
  `Ideal.ofList (List.ofFn f)`.
-/

-- Proof sketch: first prove the quotient-side statement for the canonical prefix ideal
-- `Ideal.ofList (List.ofFn f)`, which is the owner-level quotient-by-prefix input for finite
-- sequences. Then rewrite that owner-level quotient to the source-facing ideal
-- `Ideal.span (Set.range f)`.
/-- Lemma 15.30.12: if the concatenated family `f_1, \ldots, f_n, g_1, \ldots, g_m` is
`H_1`-regular in `A`, then the images of `g_1, \ldots, g_m` in `A / (f_1, \ldots, f_n)` form an
`H_1`-regular sequence. -/
theorem isH1RegularSequence_quotient_of_append {n m : ℕ} (f : Fin n → A) (g : Fin m → A)
    (hfg : IsH1RegularSequence (Fin.append f g)) :
    IsH1RegularSequence (fun i ↦ Ideal.Quotient.mk (Ideal.span (Set.range f)) (g i)) := by
  suffices hcanon :
      IsH1RegularSequence (fun i ↦ Ideal.Quotient.mk (Ideal.ofList (List.ofFn f)) (g i)) by
    rw [← Ideal.ofList_ofFn_eq_span_range f]
    exact hcanon
  sorry

end RingTheory.Sequence

/-! ### Lemma_15_30_13 (from Chap15) -/
universe u

namespace RingTheory.Sequence

variable {A : Type u} [CommRing A]

/- Domain triage:
* primary domain: Koszul-regular finite sequences in commutative algebra and their behavior under
  passage to the quotient by the ideal generated by an initial block;
* sampled owner declarations: `RingTheory.Sequence.IsKoszulRegularSequence`,
  `RingTheory.Sequence.isKoszulRegularSequence_quotient_of_append`,
  `RingTheory.Sequence.isH1RegularSequence_append_of_quotient`,
  `RingTheory.Sequence.isKoszulRegularSequence_of_span_eq`;
* best owner abstraction: the finite-family predicate `IsKoszulRegularSequence`, with the quotient
  ring canonically taken by the prefix ideal `Ideal.span (Set.range f)`;
* primitive data vs derived API: the primitive source data are only the families `f` and `g`
  together with the regularity hypotheses; an extra ideal parameter `I` and equality witness
  `Ideal.span (Set.range f) = I` are derived presentation data and should not remain in the public
  statement;
* layer: `bridge/view`, since the source-facing append theorem is expressed directly through the
  owner predicate rather than through an auxiliary named-ideal wrapper.
-/

-- Proof sketch: identify the Koszul complex on `Fin.append f g` with the total complex of the
-- tensor product of the Koszul complexes on `f` and `g`. The hypothesis on `f` makes the first
-- factor a finite free resolution of `A ⧸ Ideal.span (Set.range f)`, so tensoring with the second
-- factor identifies this total complex with the Koszul complex of the image family of `g` in that
-- quotient ring. The quotient-side Koszul-regularity assumption then gives the required vanishing
-- of all positive homology.
/-- Lemma 15.30.13: if `f` is a Koszul-regular sequence in `A`, and the images of `g` form a
Koszul-regular sequence in the quotient ring `A ⧸ Ideal.span (Set.range f)`, then the concatenated
sequence `Fin.append f g` is Koszul-regular in `A`. -/
theorem isKoszulRegularSequence_append_of_quotient {n m : ℕ} (f : Fin n → A) (g : Fin m → A)
    (hf : IsKoszulRegularSequence f)
    (hg : IsKoszulRegularSequence (fun j ↦ Ideal.Quotient.mk (Ideal.span (Set.range f)) (g j))) :
    IsKoszulRegularSequence (Fin.append f g) := sorry

end RingTheory.Sequence

/-! ### Lemma_15_30_14 (from Chap15) -/
universe u

namespace RingTheory.Sequence

variable {A : Type u} [CommRing A]

/-
Domain triage:
* primary domain: Koszul-regular finite sequences in commutative algebra and their behavior under
  quotienting by the ideal generated by an initial block;
* sampled owner declarations:
  `RingTheory.Sequence.IsKoszulRegularSequence`,
  `RingTheory.Sequence.isKoszulRegularSequence_append_of_quotient`,
  `Ideal.ofList_ofFn_eq_span_range`,
  `RingTheory.Sequence.IsQuasiRegular.tail_quotient`;
* best owner abstraction: the finite-family owner predicate `IsKoszulRegularSequence`, with the
  canonical quotient-by-prefix ideal expressed chapter-wide as `Ideal.ofList (List.ofFn f)`;
* primitive data vs derived API: the primitive source data are the families `f`, `g`, and the two
  Koszul-regularity hypotheses; the source-facing quotient by `Ideal.span (Set.range f)` is a
  derived view obtained from the owner-level quotient by `Ideal.ofList (List.ofFn f)`.
-/

-- Proof sketch: use Lemma 15.28.12 to identify the Koszul complex on `Fin.append f g` with the
-- total complex of the tensor product of the Koszul complexes on `f` and `g`. Since `f` is
-- Koszul-regular, the complex on `f` resolves `A ⧸ Ideal.span (Set.range f)`, so tensoring with the
-- complex on `g` identifies the homology with that of the Koszul complex on the image family of
-- `g` in the quotient ring. The assumed Koszul-regularity of `Fin.append f g` then forces all
-- positive homology of that quotient Koszul complex to vanish.
private theorem isKoszulRegularSequence_quotient_of_append_ofList {n m : ℕ} (f : Fin n → A)
    (g : Fin m → A) (hf : IsKoszulRegularSequence f)
    (hfg : IsKoszulRegularSequence (Fin.append f g)) :
    IsKoszulRegularSequence (fun i ↦ Ideal.Quotient.mk (Ideal.ofList (List.ofFn f)) (g i)) := by
  sorry

/-- Lemma 15.30.14: if both `f_1, \ldots, f_n` and the concatenated family
`f_1, \ldots, f_n, g_1, \ldots, g_m` are Koszul-regular sequences in `A`, then the images of
`g_1, \ldots, g_m` in `A / (f_1, \ldots, f_n)` form a Koszul-regular sequence. -/
theorem isKoszulRegularSequence_quotient_of_append {n m : ℕ} (f : Fin n → A) (g : Fin m → A)
    (hf : IsKoszulRegularSequence f) (hfg : IsKoszulRegularSequence (Fin.append f g)) :
    IsKoszulRegularSequence (fun i ↦ Ideal.Quotient.mk (Ideal.span (Set.range f)) (g i)) := by
  rw [← Ideal.ofList_ofFn_eq_span_range f]
  exact isKoszulRegularSequence_quotient_of_append_ofList f g hf hfg

end RingTheory.Sequence

/-! ### Lemma_15_30_15 (from Chap15) -/
universe u

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]

/- Domain triage:
* primary domain: finite regularity conditions in commutative algebra that depend only on the ideal
  generated by a finite family;
* sampled owner declarations: `IsQuasiRegularSequence`, `IsH1RegularSequence`,
  `IsKoszulRegularSequence`, and the canonical bridge `Ideal.ofList_ofFn_eq_span_range`;
* best owner abstraction: the regularity predicates above are the owner-level notions, while
  `Ideal.ofList (List.ofFn f)` is the canonical list-side ideal attached to a finite family;
* primitive data vs derived API: the primitive source data are just the two families `f`, `g`, and
  the equality of the ideals they generate; rewriting between the list-side owner ideal and the
  source-facing span ideal is derived bridge data, so it should be reused from the chapter owner
  theorem rather than reproved locally.
-/

section

variable {r : ℕ} (f g : Fin r → R)

private theorem isQuasiRegularSequence_of_ofList_eq
    (hI : Ideal.ofList (List.ofFn f) = Ideal.ofList (List.ofFn g))
    (hg : IsQuasiRegularSequence (List.ofFn g)) :
    IsQuasiRegularSequence (List.ofFn f) := sorry

-- Proof sketch: let `I = Ideal.span (Set.range f) = Ideal.span (Set.range g)`. Since `g` is
-- quasi-regular, the conormal module `I / I^2` is free of rank `r`, and the images of both `f`
-- and `g` give bases. The resulting change-of-generators matrix is invertible modulo `I`, so the
-- associated graded criterion for quasi-regularity transfers from `g` to `f`.
/-- Lemma 15.30.15 (1): if two length-`r` generating families of a ring generate the same ideal
and one of them is quasi-regular, then the other is quasi-regular. -/
theorem isQuasiRegularSequence_of_span_eq
    (hspan : Ideal.span (Set.range f) = Ideal.span (Set.range g))
    (hg : IsQuasiRegularSequence (List.ofFn g)) :
    IsQuasiRegularSequence (List.ofFn f) := by
  have hI : Ideal.ofList (List.ofFn f) = Ideal.ofList (List.ofFn g) := by
    rw [Ideal.ofList_ofFn_eq_span_range, Ideal.ofList_ofFn_eq_span_range, hspan]
  exact isQuasiRegularSequence_of_ofList_eq f g hI hg

-- Proof sketch: first apply Lemma `15.30.6` to the `H₁`-regular sequence `g` to obtain
-- quasi-regularity. Then part `(1)` shows that `f` is quasi-regular as well, so the
-- change-of-generators matrix is invertible modulo the common ideal. The induced comparison map of
-- Koszul complexes is therefore a quasi-isomorphism, and vanishing of `H₁` transfers from `g` to
-- `f`.
/-- Lemma 15.30.15 (2): if two length-`r` generating families of a ring generate the same ideal
and one of them is `H_1`-regular, then the other is `H_1`-regular. -/
theorem isH1RegularSequence_of_span_eq
    (hspan : Ideal.span (Set.range f) = Ideal.span (Set.range g))
    (hg : IsH1RegularSequence g) :
    IsH1RegularSequence f := sorry

-- Proof sketch: the same quasi-isomorphism of Koszul complexes used in part `(2)` compares the
-- positive homology of the Koszul complexes on `f` and `g`. Hence if `g` is Koszul-regular and
-- the two families generate the same ideal, then all positive Koszul homology groups for `f`
-- vanish as well.
/-- Lemma 15.30.15 (3): if two length-`r` generating families of a ring generate the same ideal
and one of them is Koszul-regular, then the other is Koszul-regular. -/
theorem isKoszulRegularSequence_of_span_eq
    (hspan : Ideal.span (Set.range f) = Ideal.span (Set.range g))
    (hg : IsKoszulRegularSequence g) :
    IsKoszulRegularSequence f := sorry

end

end RingTheory.Sequence

/-! ### Lemma_15_30_16 (from Chap15) -/
universe u

open MvPolynomial
open scoped BigOperators

section

variable {R : Type u} [CommRing R]
variable {n : ℕ}

/- Domain triage:
- primary domain: regular elements in multivariable polynomial rings, with the coefficient
  hypothesis organized by the Chapter 10 localization-family owner;
- sampled owner declarations:
  `awayLocalizationFamilyMap`,
  `away_localization_family_map_injective_iff_smul_family_map_injective`,
  `koszulLinearForm`,
  `regular_permutations_subsequences_polynomial_tfae`,
  `IsRegular`;
- best owner abstraction: the canonical injectivity hypothesis is the Chapter 10 owner
  `awayLocalizationFamilyMap R a`; the textbook tuple-multiplication map is only a bridge/view via
  the equivalence theorem from `Lemma_10_24_4`, while the Chapter 15 tuple owner
  `koszulLinearForm` stays auxiliary because this item is about the source-facing polynomial linear
  form itself rather than the Koszul complex owner;
- primitive data: a finite coefficient family `a : Fin n → R`;
- derived API: the regularity of the linear form `∑ i, C (a i) * X i`.

Layering:
- `source-facing`: the regularity of the linear form `∑ i, C (a i) * X i`;
- `core/canonical`: the owner map `awayLocalizationFamilyMap R a`;
- `bridge/view`: `away_localization_family_map_injective_iff_smul_family_map_injective`.
-/

/-- Lemma 15.30.16: if the canonical map from `R` to the family of away localizations at the
coefficients `a_i` is injective, equivalently if the map `R → R^n`, `x ↦ (x a_i)_i`, is
injective, then the linear form `∑ i, a_i t_i` is a nonzerodivisor in the polynomial ring
`R[t_0, ..., t_{n-1}]`. -/
theorem isRegular_linearForm_of_injective_awayLocalizationFamilyMap (a : Fin n → R)
    (h : Function.Injective (awayLocalizationFamilyMap R a)) :
    IsRegular (∑ i, C (a i) * X i) := by
  sorry

end

/-! ### Lemma_15_30_17 (from Chap15) -/
universe u

open MvPolynomial
open RingTheory
open RingTheory.Sequence

noncomputable section

/-- The upper-triangular index set `\{(i, j) \mid i \le j\}` used for the universal change of
generators matrix. -/
abbrev UpperTriangularIndex (n : ℕ) :=
  { ij : Fin n × Fin n // ij.1 ≤ ij.2 }

/-- The universal smooth `R`-algebra obtained by adjoining upper-triangular coefficients and
inverting the diagonal variables. -/
abbrev UpperTriangularBaseChangeRing (R : Type u) [CommRing R] (n : ℕ) :=
  Localization.Away
    (∏ i : Fin n, (X ⟨(i, i), le_rfl⟩ : MvPolynomial (UpperTriangularIndex n) R))

/- Domain triage:
* primary domain: finite regular sequences in commutative algebra together with change of
  generators by an upper-triangular matrix;
* sampled owner declarations: `RingTheory.Sequence.IsKoszulRegularSequence`,
  `RingTheory.Sequence.isKoszulRegularSequence_of_span_eq`,
  `RingTheory.Sequence.IsKoszulRegularOn.of_flat`, and `Matrix.mulVec`;
* best owner abstraction: the source-facing objects here are the universal base-change ring and
  the transformed family, while the coefficient bookkeeping is canonically a universal
  upper-triangular matrix acting by `Matrix.mulVec`;
* primitive data vs derived API: the primitive data are the universal coefficient ring and the
  upper-triangular matrix; the entrywise summation formula is derived API for evaluating the
  transformed family.
-/

section

variable {R : Type u} [CommRing R]
variable {n : ℕ}

private noncomputable def upperTriangularMatrix :
    Matrix (Fin n) (Fin n) (UpperTriangularBaseChangeRing R n) :=
  Matrix.of fun i j ↦
    if hij : i ≤ j then
      algebraMap (MvPolynomial (UpperTriangularIndex n) R) (UpperTriangularBaseChangeRing R n)
        (X ⟨(i, j), hij⟩)
    else 0

/-- The universal upper-triangular linear combinations `g_i = \sum_{i \le j} t_{ij} f_j` of a
finite family `f`. -/
noncomputable def upperTriangularLinearCombination (f : Fin n → R) :
    Fin n → UpperTriangularBaseChangeRing R n :=
  Matrix.mulVec upperTriangularMatrix
    (fun j ↦ algebraMap R (UpperTriangularBaseChangeRing R n) (f j))

-- Proof sketch: this is just the defining expansion of `upperTriangularLinearCombination`; the
-- summand for `j < i` is zero and the summand for `i ≤ j` is the variable `tᵢⱼ` times `f j`.
/-- Evaluating `upperTriangularLinearCombination f` at `i` gives the prescribed universal
upper-triangular row combination of the entries of `f`. -/
theorem upperTriangularLinearCombination_apply (f : Fin n → R) (i : Fin n) :
    upperTriangularLinearCombination f i =
      ∑ j, if hij : i ≤ j then
        algebraMap (MvPolynomial (UpperTriangularIndex n) R) (UpperTriangularBaseChangeRing R n)
            (X ⟨(i, j), hij⟩) *
          algebraMap R (UpperTriangularBaseChangeRing R n) (f j)
      else 0 := by
  simp [upperTriangularLinearCombination, upperTriangularMatrix, Matrix.mulVec, dotProduct]

-- Proof sketch: first `g₁` is a nonzerodivisor by applying Lemma `15.30.16` to the first row of
-- universal coefficients. Then use flat base change from Lemma `15.30.5`, invariance under
-- changing generators from Lemma `15.30.15`, and the quotient step from Lemma `15.30.14`; an
-- induction on `n` gives regularity of the transformed family.
/-- Lemma 15.30.17: if `f` is a Koszul-regular sequence in `R` whose span is a proper ideal, then
the universal upper-triangular linear combinations of `f` form a regular sequence after adjoining
upper-triangular coefficients and inverting the diagonal ones. -/
theorem isRegular_upperTriangularLinearCombination_of_isKoszulRegularSequence (f : Fin n → R)
    (hKoszul : IsKoszulRegularSequence f) (hproper : Ideal.span (Set.range f) ≠ (⊤ : Ideal R)) :
    IsRegular (UpperTriangularBaseChangeRing R n) (List.ofFn (upperTriangularLinearCombination f)) :=
  sorry

-- Proof sketch: the coefficient matrix relating `f` and `upperTriangularLinearCombination f` is
-- upper triangular with diagonal entries inverted in `UpperTriangularBaseChangeRing R n`, hence it
-- is invertible. Therefore each family lies in the ideal generated by the other.
/-- The universal upper-triangular linear combinations generate the extension of the ideal
generated by the original family. -/
theorem ideal_map_span_eq_span_upperTriangularLinearCombination (f : Fin n → R) :
    Ideal.map (algebraMap R (UpperTriangularBaseChangeRing R n)) (Ideal.span (Set.range f)) =
      Ideal.span (Set.range (upperTriangularLinearCombination f)) := sorry

end
