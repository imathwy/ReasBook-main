import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_16_2_1 (from Chap16) -/
universe u v

namespace Algebra

open PrimeSpectrum

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]

/-
Domain-style sampling for Definition 16.2.1:
- primary domain: commutative algebra on `PrimeSpectrum`, relating smooth loci and radical ideals;
- sampled owner declarations:
  `Algebra.SmoothAtPrime`,
  `Algebra.smoothLocus`,
  `Algebra.isOpen_smoothLocus`,
  `PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical`;
- best owner abstraction: the source-facing ideal `Algebra.singularIdeal`, defined from the closed
  nonsmooth locus and exposed on the textbook surface as `H[A⁄R]`;
- primitive data: the closed set `nonsmoothLocus R A = {q | ¬ SmoothAtPrime R A q}`;
- derived API: the comparison with `smoothLocus`, radicality, its zero-locus description, and
  uniqueness among radical ideals with the same zero locus.

Source/core/bridge triage:
- source-facing: the singular ideal `H_{A/R}` and its source-level characterization by the
  nonsmooth locus;
- core/canonical: `SmoothAtPrime`, `smoothLocus`, `vanishingIdeal`, and `zeroLocus`;
- bridge/view: the finitely presented comparison with mathlib's canonical `smoothLocus`.
-/

/-- The nonsmooth locus of `Spec(A) → Spec(R)`, i.e. the primes where the Stacks-project notion
`SmoothAtPrime` fails. -/
def nonsmoothLocus : Set (PrimeSpectrum A) := { q | ¬ SmoothAtPrime R A q }

/-- The source-facing smooth locus `{q | SmoothAtPrime R A q}` is open because smoothness near a
prime is witnessed on a basic open neighborhood. -/
theorem isOpen_setOf_smoothAtPrime : IsOpen { q : PrimeSpectrum A | SmoothAtPrime R A q } := by
  refine isOpen_iff_forall_mem_open.mpr fun q hq ↦ ?_
  rcases hq with ⟨g, hgq, hg⟩
  refine ⟨↑(basicOpen g), ?_, (basicOpen g).2, ?_⟩
  · intro x hx
    exact ⟨g, by simpa [mem_basicOpen] using hx, hg⟩
  · simpa [mem_basicOpen] using hgq

/-- The nonsmooth locus is closed. -/
theorem isClosed_nonsmoothLocus : IsClosed (nonsmoothLocus R A) := by
  change IsClosed ({ q : PrimeSpectrum A | SmoothAtPrime R A q }ᶜ)
  exact (isOpen_setOf_smoothAtPrime R A).isClosed_compl

/-- For finitely presented algebras, the source-facing nonsmooth locus is the complement of
`smoothLocus`. -/
theorem nonsmoothLocus_eq_compl_smoothLocus [FinitePresentation R A] :
    nonsmoothLocus R A = (smoothLocus R A)ᶜ := by
  ext q
  simp [nonsmoothLocus, smoothLocus, smoothAtPrime_iff_isSmoothAt]

/-- Definition 16.2.1: the singular ideal `H_{A/R}` is the radical ideal cutting out the
nonsmooth locus of `Spec(A) → Spec(R)`. Since the source-facing condition `SmoothAtPrime` is
defined by existence of a smooth basic-open neighborhood, the nonsmooth locus is closed, so this
is the vanishing ideal of that closed set. We write it as `H[A⁄R]`. -/
def singularIdeal : Ideal A :=
  vanishingIdeal (nonsmoothLocus R A)

end Algebra

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The singular ideal of the target of an `R`-algebra map, viewed relative to the induced
`A`-algebra structure on the codomain. This packages the canonical owner `H[B⁄A]` without
requiring theorem surfaces to install `f.toAlgebra` explicitly. -/
abbrev singularIdeal (f : A →ₐ[R] B) : Ideal B := by
  let _ : Algebra A B := f.toAlgebra
  exact Algebra.singularIdeal A B

end AlgHom

namespace SingularIdealNotation

@[inherit_doc Algebra.singularIdeal]
scoped notation:max "H[" A "⁄" R "]" => Algebra.singularIdeal R A

end SingularIdealNotation

open scoped SingularIdealNotation

namespace Algebra

open PrimeSpectrum

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]

-- Proof sketch: the singular ideal is defined as a vanishing ideal, and vanishing ideals on
-- `PrimeSpectrum` are radical by `PrimeSpectrum.isRadical_vanishingIdeal`.
/-- The singular ideal is a radical ideal. -/
theorem singularIdeal_isRadical :
    (H[A⁄R]).IsRadical := by
  simpa [singularIdeal] using isRadical_vanishingIdeal (nonsmoothLocus R A)

-- Proof sketch: the nonsmooth locus is closed, so
-- `PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure` simplifies to that closed set itself.
/-- The zero locus of the singular ideal is the nonsmooth locus of `Spec(A) → Spec(R)`. -/
theorem zeroLocus_singularIdeal :
    zeroLocus (H[A⁄R]) = nonsmoothLocus R A := by
  simpa [singularIdeal] using
    (zeroLocus_vanishingIdeal_eq_closure (nonsmoothLocus R A)).trans
      (isClosed_nonsmoothLocus R A).closure_eq

/-- For finitely presented algebras, the zero locus of the singular ideal is the complement of
mathlib's `smoothLocus`. -/
theorem zeroLocus_singularIdeal_eq_compl_smoothLocus [FinitePresentation R A] :
    zeroLocus (H[A⁄R]) = (smoothLocus R A)ᶜ := by
  rw [zeroLocus_singularIdeal, nonsmoothLocus_eq_compl_smoothLocus]

-- Proof sketch: the previous theorem gives the same zero locus as `I`, and
-- `PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical` identifies `I` with the vanishing ideal of
-- its zero locus.
/-- Any radical ideal with zero locus equal to the nonsmooth locus is the singular ideal. -/
theorem singularIdeal_unique {I : Ideal A} (hI : I.IsRadical)
    (hV : zeroLocus I = nonsmoothLocus R A) :
    I = H[A⁄R] := by
  calc
    I = I.radical := by rw [hI.radical]
    _ = vanishingIdeal (zeroLocus I) := (vanishingIdeal_zeroLocus_eq_radical I).symm
    _ = vanishingIdeal (nonsmoothLocus R A) := by rw [hV]
    _ = H[A⁄R] := rfl

end Algebra

/-! ### Lemma_16_2_2 (from Chap16) -/
universe u v

namespace Algebra

variable {R : Type u} [CommRing R]
variable {A : Type v} [CommRing A] [Algebra R A] [FinitePresentation R A]

/- Domain-style sampling for Lemma 16.2.2:
* primary domain: local smoothness of finitely presented commutative algebras at primes and
  source-facing Jacobian-standard neighbourhoods;
* sampled owner declarations:
  `SmoothAtPrime`,
  `smoothAtPrime_iff_isSmoothAt`,
  `Algebra.IsSmoothAt.exists_notMem_isStandardSmooth`,
  `standardSmoothAway_eventually_elementaryStandard_pow`;
* best owner abstraction:
  `SmoothAtPrime` is the source-facing owner at a prime of `Spec A`, while `IsSmoothAt` and
  `IsStandardSmooth` are the canonical core owners for the proof route on a basic open
  localization;
* primitive vs. derived:
  the primitive public data are only the prime `q` and the source-facing smoothness hypothesis.
  The standard-smooth basic open and the eventual elementary-standard powers are derived bridge
  data and should be reused directly from the existing owner theorems rather than repackaged
  locally.

Source/core/bridge triage:
* `source-facing`: existence of an element outside `q` that is elementary standard or strictly
  standard;
* `core/canonical`: `IsSmoothAt` and `IsStandardSmooth` on localizations `A[1/a]`;
* `bridge/view`: `smoothAtPrime_iff_isSmoothAt`,
  `standardSmoothAway_eventually_elementaryStandard_pow`, and
  `isElementaryStandard_implies_isStrictlyStandard`.
-/

-- Proof sketch: use `IsSmoothAt.exists_notMem_isStandardSmooth` to pass to a basic open
-- neighbourhood on which `A` becomes standard smooth, then apply the Chapter 16 bridge from
-- standard smoothness of a localization to eventual elementary standardness of a power of the
-- defining element.
/-- Lemma 16.2.2: if the finitely presented `R`-algebra `A` is smooth at the prime `q`, then some
element of `A` avoiding `q` is elementary standard over `R`. Equivalently, every smooth point of
`Spec A` admits a basic open neighbourhood cut out by an elementary standard element. -/
theorem smoothAtPrime_exists_not_mem_isElementaryStandard
    (q : PrimeSpectrum A) (hq : SmoothAtPrime R A q) :
    ∃ a : A, a ∉ q.asIdeal ∧ IsElementaryStandard R a := by
  let _ : IsSmoothAt R q.asIdeal := (smoothAtPrime_iff_isSmoothAt R A q).mp hq
  obtain ⟨a, haq, hstd⟩ :=
    IsSmoothAt.exists_notMem_isStandardSmooth R q.asIdeal
  obtain ⟨e0, he0⟩ :=
    standardSmoothAway_eventually_elementaryStandard_pow a hstd
  let e : ℕ := e0 + 1
  refine ⟨a ^ e, ?_, he0 e (Nat.le_add_right e0 1)⟩
  have hprime : q.asIdeal.IsPrime := inferInstance
  exact mt (hprime.mem_of_pow_mem e) haq

-- Proof sketch: apply Lemma 16.3.7 (b), i.e. the implication `(6) ⇒ (5)`, to the elementary
-- standard element produced above.
/-- Companion corollary: a smooth point also admits a basic open neighbourhood cut out by a
strictly standard element. -/
theorem smoothAtPrime_exists_not_mem_isStrictlyStandard
    (q : PrimeSpectrum A) (hq : SmoothAtPrime R A q) :
    ∃ a : A, a ∉ q.asIdeal ∧ IsStrictlyStandard R a := by
  rcases smoothAtPrime_exists_not_mem_isElementaryStandard q hq with
    ⟨a, haq, ha⟩
  exact ⟨a, haq, isElementaryStandard_implies_isStrictlyStandard a ha⟩

end Algebra

/-! ### Definition_16_2_3 (from Chap16) -/
open scoped BigOperators
open MvPolynomial

universe u v

/- Domain-style sampling for `Definition_16_2_3`:
- primary domain: finite presentations of commutative algebras, Jacobian matrices/minors, and the
  Chapter 16 source-facing predicates of elementary and strict standardness;
- sampled owner API:
  `Algebra.Presentation`,
  `Algebra.Presentation.tailRelationCondition`,
  `Algebra.Presentation.jacobianMatrix`,
  `Algebra.Presentation.jacobianColumnMinor`,
  `Algebra.IsStandardSmooth`;
- best owner abstraction: the source-facing owners in this file should live on
  `Algebra.Presentation`, with `jacobianMatrix` as primitive presentation-level Jacobian data and
  the determinant/minor expressions derived from it; the global predicates on `a : A` remain
  source-facing existential wrappers over a finite presentation and should not be collapsed into
  the later standard-smooth owner;
- primitive vs. derived:
  the primitive data are a finite presentation `P`, the first-`c` relation ideal, and the
  Jacobian matrix of the first `c` relations against all variables, together with the
  representative-independent tail condition expressed by some lift of `a` to `P.Ring`;
  `leadingJacobianDet` and the column minors are derived from that matrix, while the deleted
  exact-unfolding `_iff` wrappers were only redundant derived API.

Source/core/bridge triage:
- `source-facing`: `IsElementaryStandardElement`, `IsStrictlyStandardElement`,
  `IsElementaryStandard`, and `IsStrictlyStandard`;
- `core/canonical`: the ambient presentation owner `Algebra.Presentation` and its Jacobian matrix;
- `bridge/view`: the determinant/minor expressions and the existential passage from a specific
  presentation witness to the global predicates on `a`.
-/

namespace Algebra.Presentation

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable {n m c : ℕ}

/-- The index of the relation `f_{c + j}` among the `m` relations of a finite presentation. -/
def tailRelationIndex (hc : c ≤ m) : Fin (m - c) → Fin m :=
  Fin.cast (Nat.add_sub_of_le hc) ∘ Fin.natAdd c

/-- The ideal generated by the first `c` relations of a finite presentation. -/
noncomputable def leadingRelationIdeal
    (P : Algebra.Presentation R A (Fin n) (Fin m))
    (hc : c ≤ m) : Ideal P.Ring :=
  Ideal.span (Set.range fun i : Fin c ↦ P.relation (Fin.castLE hc i))

/-- The tail ideal-membership condition from Definition 16.2.3, stated intrinsically in the
presentation ring by requiring some lift of `a` to satisfy the displayed congruences. -/
def tailRelationCondition
    (P : Algebra.Presentation R A (Fin n) (Fin m))
    (a : A) (hcₘ : c ≤ m) : Prop :=
  ∃ a₀ : P.Ring,
    algebraMap P.Ring A a₀ = a ∧
      ∀ j : Fin (m - c),
        a₀ * P.relation (tailRelationIndex hcₘ j) ∈
          P.leadingRelationIdeal hcₘ + P.ker ^ 2

/-- The intrinsic tail condition is equivalent to checking the same congruences on the arbitrary
chosen section `P.σ a`; the difference between any two lifts lies in `P.ker`, so multiplying by a
tail relation changes the condition only by an element of `P.ker ^ 2`. -/
theorem tailRelationCondition_iff_sigma
    (P : Algebra.Presentation R A (Fin n) (Fin m))
    (a : A) (hcₘ : c ≤ m) :
    P.tailRelationCondition a hcₘ ↔
      ∀ j : Fin (m - c),
        P.σ a * P.relation (tailRelationIndex hcₘ j) ∈
          P.leadingRelationIdeal hcₘ + P.ker ^ 2 := by
  constructor
  · rintro ⟨a₀, ha₀, htail⟩ j
    let r : P.Ring := P.relation (tailRelationIndex hcₘ j)
    have ha₀' : aeval P.val a₀ = a := by
      simpa [P.algebraMap_apply] using ha₀
    have hk : P.σ a - a₀ ∈ P.ker := by
      rw [P.ker_eq_ker_aeval_val, RingHom.mem_ker, map_sub, P.aeval_val_σ, ha₀', sub_eq_zero]
    have hr : r ∈ P.ker := by
      dsimp [r]
      exact P.relation_mem_ker _
    have hsq : (P.σ a - a₀) * r ∈ P.ker ^ 2 := by
      simpa [pow_two] using Ideal.mul_mem_mul hk hr
    have hdecomp : P.σ a * r = a₀ * r + (P.σ a - a₀) * r := by
      ring
    rw [hdecomp]
    exact Ideal.add_mem _ (htail j) (Ideal.mem_sup_right hsq)
  · intro h
    exact ⟨P.σ a, by simp [P.algebraMap_apply], h⟩

/-- The `c × n` Jacobian matrix built from the first `c` relations of a finite presentation. -/
noncomputable def jacobianMatrix
    (P : Algebra.Presentation R A (Fin n) (Fin m))
    (hcₘ : c ≤ m) : Matrix (Fin c) (Fin n) P.Ring :=
  fun j i ↦ pderiv i (P.relation (Fin.castLE hcₘ j))

/-- The `c × c` leading Jacobian determinant built from the first `c` relations and first `c`
variables of a finite presentation. -/
noncomputable def leadingJacobianDet
    (P : Algebra.Presentation R A (Fin n) (Fin m))
    (hcₙ : c ≤ n) (hcₘ : c ≤ m) : P.Ring :=
  Matrix.det ((P.jacobianMatrix hcₘ).submatrix (fun i ↦ i) (Fin.castLE hcₙ))

/-- The Jacobian minor indexed by a `c`-element subset of the variables. -/
noncomputable def jacobianColumnMinor
    (P : Algebra.Presentation R A (Fin n) (Fin m))
    (hcₘ : c ≤ m) (I : Set.powersetCard (Fin n) c) : P.Ring :=
  Matrix.det ((P.jacobianMatrix hcₘ).submatrix (fun i ↦ i) (I.1.orderEmbOfFin I.2))

/-- The presentation-specific witness that `a` is elementary standard for the chosen finite
presentation. The second displayed condition is phrased intrinsically via
`P.tailRelationCondition a hcₘ`, equivalently by
`P.tailRelationCondition_iff_sigma a hcₘ`. -/
def IsElementaryStandardElement
    (P : Algebra.Presentation R A (Fin n) (Fin m)) (a : A) : Prop :=
  ∃ (c : ℕ) (hcₙ : c ≤ n) (hcₘ : c ≤ m) (a' : A),
    a = a' * algebraMap P.Ring A (P.leadingJacobianDet hcₙ hcₘ) ∧
      P.tailRelationCondition a hcₘ

/-- The presentation-specific witness that `a` is strictly standard for the chosen finite
presentation. The strict Jacobian expansion is indexed by the `c`-element subsets of the
variables, and the shared tail condition is the intrinsic predicate
`P.tailRelationCondition a hcₘ`. -/
def IsStrictlyStandardElement
    (P : Algebra.Presentation R A (Fin n) (Fin m)) (a : A) : Prop :=
  ∃ (c : ℕ) (hcₘ : c ≤ m) (aI : Set.powersetCard (Fin n) c → A),
    a = ∑ I : Set.powersetCard (Fin n) c,
        aI I * algebraMap P.Ring A (P.jacobianColumnMinor hcₘ I) ∧
      P.tailRelationCondition a hcₘ

end Algebra.Presentation

namespace Algebra

section

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable (R)

/-- Definition 16.2.3 (1): an element `a : A` is elementary standard over `R` if some finite
presentation `A = R[x₁, ..., xₙ] / (f₁, ..., fₘ)` and some `0 ≤ c ≤ min (n, m)` witness the
leading Jacobian determinant identity and the tail ideal-membership condition from the text. -/
def IsElementaryStandard (a : A) : Prop :=
  ∃ (n m : ℕ) (P : Algebra.Presentation R A (Fin n) (Fin m)),
    P.IsElementaryStandardElement a

/-- Definition 16.2.3 (2): an element `a : A` is strictly standard over `R` if some finite
presentation `A = R[x₁, ..., xₙ] / (f₁, ..., fₘ)` and some `0 ≤ c ≤ min (n, m)` write `a` as an
`A`-linear combination of the `c × c` Jacobian minors and satisfy the same tail ideal-membership
condition. -/
def IsStrictlyStandard (a : A) : Prop :=
  ∃ (n m : ℕ) (P : Algebra.Presentation R A (Fin n) (Fin m)),
    P.IsStrictlyStandardElement a

end

end Algebra

/-! ### Lemma_16_2_4 (from Chap16) -/
open Matrix

universe u v

/- Domain-style sampling for `Lemma_16_2_4`:
- primary domain: Jacobian matrices of finite presentations and the determinantal `minorIdeal`
  criterion for a matrix to admit a left inverse up to scalar;
- sampled owner API:
  `Algebra.Presentation.jacobianMatrix`,
  `Matrix.minorIdeal`,
  `exists_mul_eq_smul_one_of_mem_minorIdeal`,
  `pow_mem_minorIdeal_of_exists_mul_eq_smul_one`;
- best owner abstraction: the core owner is the Chapter 10 matrix-level `minorIdeal` API; the
  Chapter 16 statement is the `bridge/view` specialization to the transposed Jacobian matrix
  `((P.jacobianMatrix hcₘ)ᵀ)` attached to the source-facing owner
  `Algebra.Presentation.jacobianMatrix`;
- primitive data: a finite presentation `P`, the truncation bound `hcₘ : c ≤ m`, the matrix
  `((P.jacobianMatrix hcₘ)ᵀ)`, and a scalar `a : P.Ring`;
- derived API: the existence of a matrix `B` with `B * (P.jacobianMatrix hcₘ)ᵀ = a • 1` and the
  converse power-membership statement both come directly from the matrix owner theorems.

Source/core/bridge triage:
- `source-facing`: the chapter's Jacobian specialization of the determinantal criterion for the
  chosen finite presentation;
- `core/canonical`: `exists_mul_eq_smul_one_of_mem_minorIdeal` and
  `pow_mem_minorIdeal_of_exists_mul_eq_smul_one`;
- `bridge/view`: the specialization `A := (P.jacobianMatrix hcₘ)ᵀ`.
-/

namespace Algebra.Presentation

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable {n m c : ℕ}

/-- Lemma 16.2.4 (1): if `a` lies in the ideal generated by the `c × c` minors of the Jacobian
matrix of the first `c` relations of `P`, then the transposed Jacobian matrix admits a left inverse
up to the scalar `a`. -/
theorem exists_mul_transpose_jacobianMatrix_eq_smul_one
    (P : Algebra.Presentation R A (Fin n) (Fin m)) (hcₘ : c ≤ m) {a : P.Ring}
    (ha : a ∈ I_(c)((P.jacobianMatrix hcₘ)ᵀ)) :
    ∃ B : Matrix (Fin c) (Fin n) P.Ring, B * (P.jacobianMatrix hcₘ)ᵀ = a • 1 := by
  simpa using exists_mul_eq_smul_one_of_mem_minorIdeal ((P.jacobianMatrix hcₘ)ᵀ) ha

/-- Lemma 16.2.4 (2): conversely, a left inverse up to the scalar `a` for the transposed Jacobian
matrix forces `a ^ c` to lie in the ideal generated by its `c × c` minors. -/
theorem pow_mem_minorIdeal_transpose_jacobianMatrix
    (P : Algebra.Presentation R A (Fin n) (Fin m)) (hcₘ : c ≤ m) {a : P.Ring}
    (hB : ∃ B : Matrix (Fin c) (Fin n) P.Ring, B * (P.jacobianMatrix hcₘ)ᵀ = a • 1) :
    a ^ c ∈ I_(c)((P.jacobianMatrix hcₘ)ᵀ) := by
  simpa using pow_mem_minorIdeal_of_exists_mul_eq_smul_one ((P.jacobianMatrix hcₘ)ᵀ) hB

end

end Algebra.Presentation

/-! ### Lemma_16_2_5_Elkik (from Chap16) -/
universe u v

namespace Algebra

open PrimeSpectrum
open scoped SingularIdealNotation

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable [FinitePresentation R A]

/- Domain-style sampling for Lemma 16.2.5 (Elkik):
- primary domain: singular ideals and Jacobian-standard elements in finitely presented
  commutative algebras;
- sampled owner declarations:
  `Algebra.singularIdeal`,
  `Algebra.singularIdeal_unique`,
  `Algebra.smoothAtPrime_exists_not_mem_isStrictlyStandard`,
  `Algebra.smoothAtPrime_exists_not_mem_isElementaryStandard`;
- best owner abstraction: the public owner remains the singular ideal `H[A⁄R]`; the radical
  ideals generated by strictly standard and elementary standard elements are derived
  source-facing descriptions of that owner, not new owners themselves;
- primitive vs. derived:
  the primitive comparison for Elkik's lemma is the equality of zero loci with
  `nonsmoothLocus R A`; the radical ideal equalities are the derived owner-level consequences
  obtained canonically from `singularIdeal_unique`.

Source/core/bridge triage:
- `source-facing`: the two Elkik descriptions of `H_{A/R}` below;
- `core/canonical`: `H[A⁄R]`, `nonsmoothLocus R A`, `zeroLocus`, and `singularIdeal_unique`;
- `bridge/view`: the internal zero-locus comparisons for the loci cut out by strictly standard
  and elementary standard elements.
-/

private theorem zeroLocus_strictlyStandard_eq_nonsmoothLocus :
    zeroLocus ({ a | IsStrictlyStandard R a } : Set A) = nonsmoothLocus R A := by
  sorry

private theorem zeroLocus_elementaryStandard_eq_nonsmoothLocus :
    zeroLocus ({ a | IsElementaryStandard R a } : Set A) = nonsmoothLocus R A := by
  sorry

-- Proof sketch: let `H_s` be the radical of the ideal generated by strictly standard elements and
-- `H_e` the radical of the ideal generated by elementary standard elements. A strictly standard
-- element becomes smooth after localizing, so `H_s ≤ H[A⁄R]`; elementary standard elements are
-- strictly standard, so `H_e ≤ H_s`; and the Jacobian criterion at smooth primes yields
-- `H[A⁄R] ≤ H_e`. Since `H[A⁄R]` is radical, all three ideals agree.
/-- Lemma 16.2.5 (Elkik): for a finitely presented `R`-algebra `A`, the singular ideal `H_{A/R}`
is the radical of the ideal generated by strictly standard elements of `A` over `R`. -/
theorem singularIdeal_eq_radical_span_strictlyStandard :
    H[A⁄R] = (Ideal.span { a | IsStrictlyStandard R a }).radical := by
  symm
  let I : Ideal A := (Ideal.span { a | IsStrictlyStandard R a }).radical
  change I = H[A⁄R]
  have hI : I.IsRadical := by
    simpa [I] using (Ideal.span { a | IsStrictlyStandard R a }).radical_isRadical
  exact singularIdeal_unique R A hI <| by
    simpa [I, zeroLocus_radical, zeroLocus_span] using
      zeroLocus_strictlyStandard_eq_nonsmoothLocus

-- Proof sketch: the same comparison of ideals shows that the radical of the ideal generated by
-- elementary standard elements equals the radical generated by strictly standard elements, hence
-- equals `H[A⁄R]`.
/-- The singular ideal is also the radical of the ideal generated by elementary standard elements
of `A` over `R`. -/
theorem singularIdeal_eq_radical_span_elementaryStandard :
    H[A⁄R] = (Ideal.span { a | IsElementaryStandard R a }).radical := by
  symm
  let I : Ideal A := (Ideal.span { a | IsElementaryStandard R a }).radical
  change I = H[A⁄R]
  have hI : I.IsRadical := by
    simpa [I] using (Ideal.span { a | IsElementaryStandard R a }).radical_isRadical
  exact singularIdeal_unique R A hI <| by
    simpa [I, zeroLocus_radical, zeroLocus_span] using
      zeroLocus_elementaryStandard_eq_nonsmoothLocus

end

end Algebra

/-! ### Example_16_2_6 (from Chap16) -/
open MvPolynomial PrimeSpectrum

universe u

noncomputable section

namespace Algebra

/-
Domain-style sampling for Example 16.2.6:
- primary domain: commutative algebra and affine smooth loci for finitely presented quotient maps;
- sampled owner declarations:
  `Algebra.smoothLocus`,
  `Algebra.basicOpen_subset_smoothLocus_iff_smooth`,
  `Algebra.isOpen_smoothLocus`,
  `Algebra.singularIdeal`;
- best owner abstraction: `Algebra.smoothLocus` for the quotient map `R → A`;
- primitive data: the public owner declarations
  `smoothCounterexamplePolynomialRing k`,
  `smoothCounterexampleRelationIdeal k`,
  `smoothCounterexampleR k`,
  `smoothCounterexampleA k`,
  `smoothCounterexampleX k`,
  `smoothCounterexampleYInR k i`,
  `smoothCounterexampleY k i`;
- derived API: the identification of `smoothLocus R A` with `⋃ i, D(yᵢ)` and the resulting
  non-compactness.
- minimal coefficient assumptions from the sampled owners: `CommRing k` for the quotient
  presentation and smooth-locus description, with `Nontrivial k` needed only for the
  non-compactness statement.

Source/core/bridge triage:
- source-facing: the two public theorems describing the smooth locus and its non-compactness;
- core/canonical: `Algebra.smoothLocus`, `PrimeSpectrum.basicOpen`, and
  `Algebra.FinitePresentation.quotient`;
- bridge/view: the internal `Option ℕ+` presentation, with `none` representing `x` and `some i`
  representing `yᵢ`. This keeps the source indexing `y₁, y₂, …` explicit rather than silently
  reindexing by all of `ℕ`, while the public theorem surface is expressed through the source-facing
  owners listed above.
-/

/-- The ambient polynomial ring `k[x, yᵢ \mid i : ℕ+]` for Example 16.2.6, modeled by letting
`none` index `x` and `some i` index `yᵢ`. -/
def smoothCounterexamplePolynomialRing (k : Type u) [CommRing k] : Type u :=
  MvPolynomial (Option ℕ+) k

instance (k : Type u) [CommRing k] : CommRing (smoothCounterexamplePolynomialRing k) := by
  delta smoothCounterexamplePolynomialRing
  infer_instance

/-- The polynomial variable `x` in the ambient ring of Example 16.2.6. -/
private def smoothCounterexampleXPolynomial (k : Type u) [CommRing k] :
    smoothCounterexamplePolynomialRing k :=
  X (none : Option ℕ+)

/-- The polynomial variable `yᵢ` in the ambient ring of Example 16.2.6. -/
private def smoothCounterexampleYPolynomial (k : Type u) [CommRing k] (i : ℕ+) :
    smoothCounterexamplePolynomialRing k :=
  X (some i)

/-- The defining ideal `(x yᵢ \mid i \ge 1)` of the source ring `R` in Example 16.2.6. -/
def smoothCounterexampleRelationIdeal (k : Type u) [CommRing k] :
    Ideal (smoothCounterexamplePolynomialRing k) :=
  Ideal.span (Set.range fun i : ℕ+ ↦
    smoothCounterexampleXPolynomial k * smoothCounterexampleYPolynomial k i)

/-- The source ring
`R = k[x, y₁, y₂, y₃, ...] / (x yᵢ \mid i \ge 1)` from Example 16.2.6. -/
def smoothCounterexampleR (k : Type u) [CommRing k] : Type u :=
  smoothCounterexamplePolynomialRing k ⧸ smoothCounterexampleRelationIdeal k

instance (k : Type u) [CommRing k] : CommRing (smoothCounterexampleR k) := by
  delta smoothCounterexampleR
  infer_instance

/-- The class of `x` in the source ring `R` of Example 16.2.6. -/
def smoothCounterexampleX (k : Type u) [CommRing k] : smoothCounterexampleR k :=
  Ideal.Quotient.mk (smoothCounterexampleRelationIdeal k) (smoothCounterexampleXPolynomial k)

/-- The class of `yᵢ` in the source ring `R` of Example 16.2.6. -/
def smoothCounterexampleYInR (k : Type u) [CommRing k] (i : ℕ+) :
    smoothCounterexampleR k :=
  Ideal.Quotient.mk (smoothCounterexampleRelationIdeal k) (smoothCounterexampleYPolynomial k i)

/-- The principal ideal `(x)` in the source ring `R` of Example 16.2.6. -/
def smoothCounterexampleXIdeal (k : Type u) [CommRing k] :
    Ideal (smoothCounterexampleR k) :=
  principalIdeal (smoothCounterexampleX k)

/-- The target ring `A = R / (x)` from Example 16.2.6. -/
def smoothCounterexampleA (k : Type u) [CommRing k] : Type u :=
  smoothCounterexampleR k ⧸ smoothCounterexampleXIdeal k

instance (k : Type u) [CommRing k] : CommRing (smoothCounterexampleA k) := by
  delta smoothCounterexampleA
  infer_instance

instance (k : Type u) [CommRing k] :
    Algebra (smoothCounterexampleR k) (smoothCounterexampleA k) := by
  exact Ideal.Quotient.algebra _

/-- The class of `yᵢ` in the target ring `A` of Example 16.2.6. -/
def smoothCounterexampleY (k : Type u) [CommRing k] (i : ℕ+) :
    smoothCounterexampleA k :=
  Ideal.Quotient.mk (smoothCounterexampleXIdeal k) (smoothCounterexampleYInR k i)

open scoped PrimeSpectrum

/-- The quotient map `R → A = R / (x)` in Example 16.2.6 is finitely presented. -/
instance smoothCounterexampleFinitePresentation (k : Type u) [CommRing k] :
    FinitePresentation (smoothCounterexampleR k) (smoothCounterexampleA k) := by
  let _ : Module (smoothCounterexampleR k) (smoothCounterexampleR k) :=
    @Semiring.toModule (smoothCounterexampleR k) inferInstance
  have hfg : (smoothCounterexampleXIdeal k).FG := by
    simpa [smoothCounterexampleXIdeal, principalIdeal] using
      (Submodule.fg_span_singleton (smoothCounterexampleX k))
  simpa [smoothCounterexampleA] using
    (FinitePresentation.quotient hfg :
      FinitePresentation (smoothCounterexampleR k)
        ((smoothCounterexampleR k) ⧸ smoothCounterexampleXIdeal k))

-- Proof sketch: away from `y_i`, the relation `x y_i = 0` forces `x = 0`, so on `D(y_i)` the
-- quotient `A` agrees with the corresponding localization of `R` and is smooth there. Conversely,
-- if all `y_i` vanish at a prime of `A`, the fiber still carries infinitely many singular
-- directions coming from the countable family of relations `x y_i`, so the map is not smooth at
-- that prime.
/-- Example 16.2.6: for
`R = k[x, y₁, y₂, y₃, ...] / (x y_i \mid i \ge 1)` and `A = R / (x)`, the smooth locus of the
ring map `R → A` is exactly `⋃_i D(y_i)`. -/
theorem smoothCounterexample_smoothLocus_eq_iUnion_basicOpen
    (k : Type u) [CommRing k] :
    smoothLocus (smoothCounterexampleR k) (smoothCounterexampleA k) =
      ⋃ i : ℕ+, D(smoothCounterexampleY k i) := sorry

-- Proof sketch: if the displayed union were compact, then in the spectral space `Spec(A)` it
-- would be a finite union of basic opens. But any finite subunion `⋃_{i ∈ s} D(y_i)` misses a
-- prime containing all `y_i` with `i ∉ s`, so no finite subcover exists.
/-- The smooth locus in the counterexample is not quasi-compact, equivalently not compact as a
subset of `Spec(A)`. -/
theorem smoothCounterexample_smoothLocus_not_isCompact
    (k : Type u) [CommRing k] [Nontrivial k] :
    ¬ IsCompact (smoothLocus (smoothCounterexampleR k) (smoothCounterexampleA k)) := sorry

end Algebra

/-! ### Lemma_16_2_7 (from Chap16) -/
open scoped TensorProduct

universe u v w

section

variable {R : Type u} {A : Type v} {R' : Type w}
variable [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']

/-
Domain-style sampling for `Lemma 16.2.7`:
- primary domain: base change for finite-presentation Jacobian witnesses of elementary and strict
  standardness;
- sampled owner API:
  `Algebra.Presentation.baseChange`,
  `Algebra.Presentation.IsElementaryStandardElement`,
  `Algebra.Presentation.IsStrictlyStandardElement`,
  `Algebra.IsStandardSmooth.baseChange`;
- best owner abstraction: the primitive base-change statements live at the presentation level,
  while `Algebra.IsElementaryStandard` and `Algebra.IsStrictlyStandard` are the derived
  existential owner predicates;
- primitive data: a finite presentation `P` and a presentation-level witness
  `P.IsElementaryStandardElement a` or `P.IsStrictlyStandardElement a`;
- derived API: the algebra-level base-change theorems obtained by existentially choosing `P`.

Source/core/bridge triage:
- `source-facing`: the Stacks statements that elementary or strictly standard elements remain so
  after base change;
- `core/canonical`: `Algebra.Presentation.baseChange` together with the owner predicates
  `P.IsElementaryStandardElement a` and `P.IsStrictlyStandardElement a`;
- `bridge/view`: the tensor element `1 ⊗ₜ[R] a` in the base-changed algebra `R' ⊗[R] A`.
-/

namespace Algebra.Presentation

variable {n m : ℕ}

-- Proof sketch: unfold the presentation-level witness from Definition `16.2.3`, apply the
-- canonical base-changed presentation `P.baseChange R'`, and transport the same size `c`, the
-- Jacobian determinant or minor expression, and the tail ideal-membership condition along the ring
-- map `MvPolynomial.map (algebraMap R R')`.
/-- Presentation-level base change of the elementary standard condition. -/
theorem isElementaryStandardElement_baseChange
    (P : Algebra.Presentation R A (Fin n) (Fin m)) {a : A}
    (ha : P.IsElementaryStandardElement a) :
    (baseChange R' P).IsElementaryStandardElement ((1 : R') ⊗ₜ[R] a) :=
  sorry

-- Proof sketch: base change the witnessing presentation `P` and transport the Jacobian-minor
-- expansion termwise through the canonical tensor-product algebra map.
/-- Presentation-level base change of the strictly standard condition. -/
theorem isStrictlyStandardElement_baseChange
    (P : Algebra.Presentation R A (Fin n) (Fin m)) {a : A}
    (ha : P.IsStrictlyStandardElement a) :
    (baseChange R' P).IsStrictlyStandardElement ((1 : R') ⊗ₜ[R] a) := sorry

end Algebra.Presentation

namespace Algebra

-- Proof sketch: choose a witnessing finite presentation from `IsElementaryStandard R a`, apply the
-- presentation-level base-change theorem, and package the resulting witness back into the
-- canonical existential owner predicate.
/-- Lemma 16.2.7: an elementary standard element remains elementary standard after base change. -/
theorem isElementaryStandard_baseChange
    (a : A) (ha : IsElementaryStandard R a) :
    IsElementaryStandard R' ((1 : R') ⊗ₜ[R] a) := by
  rcases ha with ⟨n, m, P, hP⟩
  exact ⟨n, m, Presentation.baseChange R' P,
    Presentation.isElementaryStandardElement_baseChange P hP⟩

-- Proof sketch: the algebra-level strict statement is the derived existential package of the
-- presentation-level base-change theorem for strict standardness.
/-- Lemma 16.2.7: a strictly standard element remains strictly standard after base change. -/
theorem isStrictlyStandard_baseChange
    (a : A) (ha : IsStrictlyStandard R a) :
    IsStrictlyStandard R' ((1 : R') ⊗ₜ[R] a) := by
  rcases ha with ⟨n, m, P, hP⟩
  exact ⟨n, m, Presentation.baseChange R' P,
    Presentation.isStrictlyStandardElement_baseChange P hP⟩

end Algebra

end

/-! ### Lemma_16_2_8 (from Chap16) -/
universe u v w

namespace Algebra

open scoped SingularIdealNotation

section

variable {R : Type u} {A : Type v} {Λ : Type w}
variable [CommRing R] [CommRing A] [CommRing Λ]
variable [Algebra R A] [Algebra R Λ]
variable [FinitePresentation R A]

/- Domain-style sampling for Lemma 16.2.8:
- primary domain: commutative algebra of smooth `R`-algebras and the singular ideal criterion for
  factoring an `R`-algebra map through a smooth algebra;
- sampled owner declarations:
  `Algebra.singularIdeal`,
  `Algebra.singularIdeal_eq_radical_span_elementaryStandard`,
  `Ideal.map`,
  `Smooth`,
  `FinitePresentation`;
- best owner abstraction: this item is a source-facing existence theorem whose public surface
  should stay the direct smooth factorization of `φ : A →ₐ[R] Λ`, expressed using the chapter
  owner `H[A⁄R]` and the canonical smoothness owner `Smooth R B`;
- primitive data: the finitely presented `R`-algebra `A`, the target `R`-algebra `Λ`, the map
  `φ`, and the unit-ideal hypothesis on the image of `H[A⁄R]`;
- derived API: the smooth intermediate algebra `B` and factorization maps `A →ₐ[R] B →ₐ[R] Λ`.

Source/core/bridge triage:
- source-facing: the existence of a smooth factorization under the singular-ideal hypothesis;
- core/canonical: `H[A⁄R]`, `Ideal.map`, `Smooth`, and `FinitePresentation`;
- bridge/view: the explicit factorization maps `f` and `g`.

There is no upstream exact-interface owner theorem to recall here, so the refinement keeps the
source-facing theorem itself and trims only redundant surface detail.
-/

-- Proof sketch: by Elkik's description of `H[A⁄R]` as the radical of the ideal generated by
-- elementary standard elements, the hypothesis yields finitely many elementary standard elements
-- of `A` whose images under `φ` generate the unit ideal in `Λ`. Each such element gives a
-- standard smooth localization of `A`, and the corresponding localized maps to `Λ` glue through
-- a finite product of smooth `R`-algebras, yielding the required smooth factorization of `φ`.
/-- Lemma 16.2.8: if `A` is finitely presented over `R` and the image of the singular ideal
`H_{A/R}` under an `R`-algebra map `φ : A → Λ` is the unit ideal, then `φ` factors through a
smooth `R`-algebra. -/
theorem exists_smooth_factorization_of_singularIdeal_map_eq_top
    (φ : A →ₐ[R] Λ) (hHtop : Ideal.map φ (H[A⁄R]) = ⊤) :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B) (_ : Smooth R B)
      (f : A →ₐ[R] B) (g : B →ₐ[R] Λ), g.comp f = φ := by
  sorry

end

end Algebra
