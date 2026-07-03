import Mathlib
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Topology.Sheaves.Presheaf

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_20_23_1 (from Chap20) -/
open CategoryTheory Opposite TopCat TopologicalSpace
open CategoryTheory.Limits

universe u v

variable {X : TopCat.{u}} {ι : Type v}
variable (𝒰 : ι → Opens X) (ℱ : X.Presheaf AddCommGrpCat.{max u v})

local instance : HasFiniteProducts (Opens X) := opensHasFiniteProducts X

/- Domain-style sampling for Definition 20.23.1:
- primary domain: Čech cochain complexes of abelian presheaves on the lattice of opens of a
  topological space;
- sampled owner API:
  `AlternatingCofaceMapComplex.objD`,
  `FormalCoproduct.cochainComplexFunctor`,
  `cechComplexFunctor`;
- best owner abstraction: `cechComplexFunctor 𝒰`.

Source/core/bridge triage:
- `source-facing`: the alternating Čech complex attached to the cover `𝒰` and presheaf `ℱ`;
- `core/canonical`: `(cechComplexFunctor 𝒰).obj ℱ`;
- `bridge/view`: the tuplewise Čech-term and differential formulas developed later as coordinate API.

Primitive data versus derived API:
- primitive data: only the indexed family `𝒰` and the abelian presheaf `ℱ`;
- derived API: the cochain terms, differentials, and full complex structure, all already supplied
  by `cechComplexFunctor`.

This numbered definition is therefore recall-only: it should not keep a parallel local alias for
the canonical owner. -/

/- Core recall: the alternating Čech complex of `ℱ` for the cover `𝒰` is the canonical
specialization `(cechComplexFunctor 𝒰).obj ℱ`. -/
recall cechComplexFunctor

/- Specialized check for Definition 20.23.1. -/
#check ((cechComplexFunctor 𝒰).obj ℱ : CochainComplex AddCommGrpCat.{max u v} ℕ)

/-! ### Definition_20_23_2 (from Chap20) -/
open CategoryTheory Opposite TopologicalSpace
open scoped BigOperators

noncomputable section

universe u v

variable {X : TopCat.{u}} {ι : Type v}

/- Domain-style sampling for Definition 20.23.2:
- primary domain: ordered Čech cochain complexes for abelian presheaves on a family of opens;
- sampled owner API:
  `CategoryTheory.cechComplexFunctor`,
  `Limits.FormalCoproduct.cochainComplexFunctor`,
  `AlgebraicTopology.AlternatingCofaceMapComplex.objD`,
  `CochainComplex.of`;
- best owner abstraction for this item: the explicit-order ordered Čech complex
  `orderedCechComplexOfOrder o 𝒰 F`, with the ambient-order specialization
  `orderedCechComplex 𝒰 F` as the source-facing surface.

Source/core/bridge triage:
- `source-facing`: the ordered Čech complex attached to a linearly ordered index set;
- `core/canonical`: the explicit-order owner `orderedCechComplexOfOrder o 𝒰 F`;
- `bridge/view`: specialization along the ambient instance `[LinearOrder ι]`.

Primitive data versus derived API:
- primitive data: a total order `o` on the index type, the family `𝒰`, and the presheaf `F`;
- derived API: ordered Čech terms, restrictions, differentials, and the full complex. -/

/-- A degree-`p` ordered Čech index for the explicit linear order `o` on the index set. -/
abbrev OrderedCechIndex (o : LinearOrder ι) (p : ℕ) :=
  letI := o
  {σ : Fin (p + 1) → ι // StrictMono σ}

/-- The order-embedding view of an ordered Čech index. -/
def orderedCechIndexOrderEmbedding (o : LinearOrder ι) {p : ℕ} (σ : OrderedCechIndex o p) :
    Fin (p + 1) ↪o ι :=
  letI := o
  OrderEmbedding.ofStrictMono σ.1 σ.2

/-- Omitting one entry from an ordered Čech index again yields an ordered Čech index. -/
abbrev orderedCechIndexSuccAbove (o : LinearOrder ι) {p : ℕ}
    (σ : OrderedCechIndex o (p + 1)) (j : Fin (p + 2)) : OrderedCechIndex o p :=
  letI := o
  ⟨σ.1 ∘ j.succAboveEmb, σ.2.comp (Fin.strictMono_succAbove j)⟩

/-- The degree-`p` term of the ordered Čech complex for the explicit order `o`. -/
abbrev orderedCechTermOfOrder (o : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) : AddCommGrpCat.{max u v} :=
  AddCommGrpCat.of
    (∀ σ : OrderedCechIndex o p, F.obj (op (cechIntersection 𝒰 σ.1)))

/-- The restriction map obtained by omitting one index from an ordered Čech tuple. -/
abbrev orderedCechRestrictionOfOrder (o : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) {p : ℕ}
    (σ : OrderedCechIndex o (p + 1)) (j : Fin (p + 2)) :
    F.obj (op (cechIntersection 𝒰 (orderedCechIndexSuccAbove o σ j).1)) ⟶
      F.obj (op (cechIntersection 𝒰 σ.1)) :=
  F.map (homOfLE (cechIntersection_le_succAbove 𝒰 σ.1 j)).op

/-- The underlying function of the degree-`p` ordered Čech differential for the order `o`. -/
def orderedCechDifferentialToFunOfOrder (o : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechTermOfOrder o 𝒰 F p → orderedCechTermOfOrder o 𝒰 F (p + 1) :=
  fun s σ ↦
    ∑ j : Fin (p + 2),
      (-1 : ℤ) ^ (j : ℕ) •
        orderedCechRestrictionOfOrder o 𝒰 F σ j (s (orderedCechIndexSuccAbove o σ j))

-- Proof sketch: each summand in the ordered alternating sum is additive in the cochain, and
-- finite sums preserve additivity.
/-- The ordered Čech differential is additive on cochains. -/
theorem orderedCechDifferentialToFunOfOrder_map_add (o : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s t : orderedCechTermOfOrder o 𝒰 F p) :
    orderedCechDifferentialToFunOfOrder o 𝒰 F p (s + t) =
      orderedCechDifferentialToFunOfOrder o 𝒰 F p s +
        orderedCechDifferentialToFunOfOrder o 𝒰 F p t := sorry

/-- The degree-`p` differential in the ordered Čech complex for the order `o`. -/
abbrev orderedCechDifferentialOfOrder (o : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechTermOfOrder o 𝒰 F p ⟶ orderedCechTermOfOrder o 𝒰 F (p + 1) :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (orderedCechDifferentialToFunOfOrder o 𝒰 F p)
      (orderedCechDifferentialToFunOfOrder_map_add o 𝒰 F p))

-- Proof sketch: the ordered differential satisfies the same alternating-face cancellation as the
-- ordinary Čech differential, now restricted to strictly increasing tuples.
/-- Two successive ordered Čech differentials compose to zero. -/
theorem orderedCechDifferentialOfOrder_comp (o : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechDifferentialOfOrder o 𝒰 F p ≫ orderedCechDifferentialOfOrder o 𝒰 F (p + 1) = 0 :=
  sorry

/-- The ordered Čech complex attached to the explicit order `o` on the index set. -/
def orderedCechComplexOfOrder (o : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) : CochainComplex AddCommGrpCat.{max u v} ℕ :=
  CochainComplex.of (orderedCechTermOfOrder o 𝒰 F) (orderedCechDifferentialOfOrder o 𝒰 F)
    (orderedCechDifferentialOfOrder_comp o 𝒰 F)

section

variable [LinearOrder ι]

/-- A degree-`p` ordered Čech index for the ambient linear order on `ι`. -/
abbrev StrictCechTuple (p : ℕ) :=
  OrderedCechIndex inferInstance p

/-- Omitting one entry from a strictly increasing Čech tuple again yields a strictly increasing
tuple. -/
abbrev strictCechTupleSuccAbove {p : ℕ} (σ : StrictCechTuple (p + 1))
    (j : Fin (p + 2)) : StrictCechTuple p :=
  orderedCechIndexSuccAbove inferInstance σ j

/-- The degree-`p` term of the ordered Čech complex for the ambient linear order. -/
abbrev orderedCechTerm (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    AddCommGrpCat.{max u v} :=
  orderedCechTermOfOrder inferInstance 𝒰 F p

/-- The restriction map in the ordered Čech complex for the ambient linear order. -/
abbrev orderedCechRestriction (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) {p : ℕ}
    (σ : StrictCechTuple (p + 1)) (j : Fin (p + 2)) :
    F.obj (op (cechIntersection 𝒰 (strictCechTupleSuccAbove σ j).1)) ⟶
      F.obj (op (cechIntersection 𝒰 σ.1)) :=
  orderedCechRestrictionOfOrder inferInstance 𝒰 F σ j

/-- The underlying function of the ordered Čech differential for the ambient linear order. -/
abbrev orderedCechDifferentialToFun (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechTerm 𝒰 F p → orderedCechTerm 𝒰 F (p + 1) :=
  orderedCechDifferentialToFunOfOrder inferInstance 𝒰 F p

/-- The degree-`p` ordered Čech differential for the ambient linear order. -/
abbrev orderedCechDifferential (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechTerm 𝒰 F p ⟶ orderedCechTerm 𝒰 F (p + 1) :=
  orderedCechDifferentialOfOrder inferInstance 𝒰 F p

/-- Two successive ordered Čech differentials compose to zero. -/
theorem orderedCechDifferential_comp_orderedCechDifferential (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechDifferential 𝒰 F p ≫ orderedCechDifferential 𝒰 F (p + 1) = 0 :=
  orderedCechDifferentialOfOrder_comp inferInstance 𝒰 F p

/-- The ordered Čech complex attached to the ambient linear order on the index set. -/
abbrev orderedCechComplex (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) :
    CochainComplex AddCommGrpCat.{max u v} ℕ :=
  orderedCechComplexOfOrder inferInstance 𝒰 F

/-- The degree-`p` object of the ordered Čech complex is the ordered Čech term in degree `p`. -/
theorem orderedCechComplex_X (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (orderedCechComplex 𝒰 F).X p = orderedCechTerm 𝒰 F p :=
  rfl

end

end

/-! ### Lemma_20_23_3 (from Chap20) -/
open CategoryTheory TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe u v

/- Domain-style sampling for Lemma 20.23.3:
- primary domain: ordered and alternating Čech cochain complexes for a linearly ordered cover.
- sampled owner declarations:
  `orderedCechComplex`,
  `alternatingCechComplex`,
  `orderedCechComparison`,
  `alternatingCechProjection`.
- best owner abstraction: the complex morphism `orderedCechComparison : orderedCechComplex 𝒰 F ⟶
  alternatingCechComplex 𝒰 F` from `Lemma_20_23_4`; the isomorphism statement here is derived API,
  not a second owner.
- primitive data: the cover `𝒰` and presheaf `F`.
- derived API: the projection `alternatingCechProjection`, its isomorphism
  `alternatingCechProjection_isIso`, and the left-inverse identity
  `orderedCechComparison_comp_alternatingCechProjection`.

Source/core/bridge triage:
- `source-facing`: Lemma 20.23.3, asserting that the ordered-to-alternating comparison is an
  isomorphism.
- `core/canonical`: `orderedCechComparison` and `alternatingCechProjection` from
  `Lemma_20_23_4`.
- `bridge/view`: this file only derives the `IsIso` statement from that owner-level comparison and
  its canonical inverse. -/

variable {X : TopCat.{u}} {ι : Type v} [LinearOrder ι]

local instance : HasFiniteProducts (Opens X) := opensHasFiniteProducts X

-- Proof sketch: `Lemma 20.23.4` constructs the projection from alternating to ordered Čech
-- cochains and proves it is an isomorphism; the comparison `c` is its inverse because their
-- composite is the identity on the ordered complex.
/-- Lemma 20.23.3: for a linearly ordered index set, the canonical comparison from the ordered
Čech complex of a cover to the alternating Čech complex is an isomorphism of cochain complexes. -/
theorem orderedCechComparison_isIso (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    IsIso (orderedCechComparison 𝒰 F) := by
  exact CategoryTheory.isIso_of_comp_hom_eq_id (alternatingCechProjection 𝒰 F)
    (orderedCechComparison_comp_alternatingCechProjection 𝒰 F)

/-! ### Lemma_20_23_4 (from Chap20) -/
open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Limits
open scoped BigOperators

noncomputable section

universe u v

variable {X : TopCat.{u}} {ι : Type v} [LinearOrder ι]

local instance : HasFiniteProducts (Opens X) := opensHasFiniteProducts X

/- Domain-style sampling for Lemma 20.23.4:
- primary domain: comparison morphisms between the ordinary, ordered, and alternating Čech
  cochain complexes attached to a linearly ordered cover;
- sampled owner declarations:
  `cechComplexFunctor`,
  `orderedCechComplexOfOrder`,
  `orderedCechComplex`,
  `CochainComplex.of`;
- best owner abstraction: the ordinary Čech complex stays at the canonical owner
  `cechComplexFunctor 𝒰`, the ordered complex stays at the chapter owner `orderedCechComplex 𝒰 F`,
  and the alternating-to-ordered projection should live only as the bridge composite through the
  ordinary-owner inclusion/projection rather than as a second parallel componentwise owner.

Source/core/bridge triage:
- `source-facing`: the alternating Čech complex and the comparison/projection morphisms of
  Lemma 20.23.4;
- `core/canonical`: `cechComplexFunctor 𝒰` and `orderedCechComplexOfOrder o 𝒰 F` from earlier in
  the chapter;
- `bridge/view`: `alternatingCechInclusion`, `cechProjectionToOrderedCech`, and the derived
  composite `alternatingCechProjection`.

Primitive data versus derived API:
- primitive data: the alternating predicate on ordinary Čech cochains and the induced restricted
  differential;
- derived API: the inclusion into the ordinary Čech complex, the projection to the ordered Čech
  complex, and the ordered-to-alternating comparison morphism. -/

/-- Permuting the indices of a Čech tuple does not change the corresponding intersection of opens. -/
theorem cechIntersection_comp_perm (𝒰 : ι → Opens X) {p : ℕ}
    (σ : Fin (p + 1) → ι) (τ : Equiv.Perm (Fin (p + 1))) :
    cechIntersection 𝒰 (σ ∘ τ) = cechIntersection 𝒰 σ := sorry

/-- A sorted injective tuple of indices is strictly increasing. -/
theorem strictMono_comp_tuple_sort_of_injective {p : ℕ} {σ : Fin (p + 1) → ι}
    (hσ : Function.Injective σ) :
    StrictMono (σ ∘ Tuple.sort σ) := sorry

/-- Sorting an injective tuple produces the corresponding strictly increasing Čech tuple. -/
def sortedStrictCechTupleOfInjective {p : ℕ} (σ : Fin (p + 1) → ι)
    (hσ : Function.Injective σ) : StrictCechTuple p :=
  ⟨σ ∘ Tuple.sort σ, strictMono_comp_tuple_sort_of_injective hσ⟩

/-- The predicate that a degree-`p` Čech cochain is alternating: it vanishes on repeated indices
and transforms by the sign of a permutation. -/
def IsAlternatingCechCochain (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) (s : cechTerm 𝒰 F p) : Prop :=
  (∀ σ : Fin (p + 1) → ι, ¬ Function.Injective σ → s σ = 0) ∧
    ∀ (σ : Fin (p + 1) → ι) (τ : Equiv.Perm (Fin (p + 1))),
      F.map (eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm).op (s (σ ∘ τ)) =
        (Equiv.Perm.sign τ) • s σ

-- Proof sketch: the zero cochain vanishes on all repeated tuples and is fixed by every signed
-- permutation relation.
/-- The zero Čech cochain is alternating. -/
theorem isAlternatingCechCochain_zero (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    IsAlternatingCechCochain 𝒰 F p 0 := sorry

-- Proof sketch: the alternating conditions are linear, so the sum of two alternating cochains is
-- again alternating.
/-- Alternating Čech cochains are closed under addition. -/
theorem IsAlternatingCechCochain.add (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) {s t : cechTerm 𝒰 F p}
    (hs : IsAlternatingCechCochain 𝒰 F p s)
    (ht : IsAlternatingCechCochain 𝒰 F p t) :
    IsAlternatingCechCochain 𝒰 F p (s + t) := sorry

-- Proof sketch: negation preserves both vanishing on repeated indices and the signed permutation
-- relation.
/-- Alternating Čech cochains are closed under negation. -/
theorem IsAlternatingCechCochain.neg (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) {s : cechTerm 𝒰 F p}
    (hs : IsAlternatingCechCochain 𝒰 F p s) :
    IsAlternatingCechCochain 𝒰 F p (-s) := sorry

/-- The additive subgroup of degree-`p` alternating Čech cochains. -/
def alternatingCechTermSubgroup (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    AddSubgroup (cechTerm 𝒰 F p) where
  carrier := {s | IsAlternatingCechCochain 𝒰 F p s}
  zero_mem' := isAlternatingCechCochain_zero 𝒰 F p
  add_mem' hs ht := IsAlternatingCechCochain.add 𝒰 F p hs ht
  neg_mem' hs := IsAlternatingCechCochain.neg 𝒰 F p hs

/-- The degree-`p` term of the alternating Čech complex. -/
abbrev alternatingCechTerm (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    AddCommGrpCat.{max u v} :=
  AddCommGrpCat.of (alternatingCechTermSubgroup 𝒰 F p)

-- Proof sketch: the usual Čech differential preserves vanishing on repeated indices and the sign
-- rule for permuting indices, so it restricts to the alternating subgroup.
/-- The ordinary Čech differential preserves alternating cochains. -/
theorem cechDifferential_preserves_alternating (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) {s : cechTerm 𝒰 F p}
    (hs : IsAlternatingCechCochain 𝒰 F p s) :
    IsAlternatingCechCochain 𝒰 F (p + 1) (cechDifferentialToFun 𝒰 F p s) := sorry

/-- The underlying function of the differential on the alternating Čech complex. -/
def alternatingCechDifferentialToFun (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    alternatingCechTerm 𝒰 F p → alternatingCechTerm 𝒰 F (p + 1) :=
  fun s ↦
    ⟨cechDifferentialToFun 𝒰 F p s.1,
      cechDifferential_preserves_alternating 𝒰 F p s.2⟩

-- Proof sketch: the restricted differential is induced from the additive ordinary Čech
-- differential, hence remains additive on the alternating subgroup.
/-- The alternating Čech differential is additive. -/
theorem alternatingCechDifferentialToFun_map_add (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s t : alternatingCechTerm 𝒰 F p) :
    alternatingCechDifferentialToFun 𝒰 F p (s + t) =
      alternatingCechDifferentialToFun 𝒰 F p s +
        alternatingCechDifferentialToFun 𝒰 F p t := sorry

/-- The degree-`p` differential in the alternating Čech complex. -/
abbrev alternatingCechDifferential (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    alternatingCechTerm 𝒰 F p ⟶ alternatingCechTerm 𝒰 F (p + 1) :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (alternatingCechDifferentialToFun 𝒰 F p)
      (alternatingCechDifferentialToFun_map_add 𝒰 F p))

-- Proof sketch: the restricted differential squares to zero because it is obtained by restricting
-- the ordinary Čech differential, which already satisfies `d ∘ d = 0`.
/-- Consecutive differentials in the alternating Čech complex compose to zero. -/
theorem alternatingCechDifferential_comp_alternatingCechDifferential (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    alternatingCechDifferential 𝒰 F p ≫ alternatingCechDifferential 𝒰 F (p + 1) = 0 := sorry

/-- The alternating Čech complex as the alternating cochain subcomplex of the ordinary Čech
complex. -/
def alternatingCechComplex (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) :
    CochainComplex AddCommGrpCat.{max u v} ℕ :=
  CochainComplex.of (alternatingCechTerm 𝒰 F) (alternatingCechDifferential 𝒰 F)
    (alternatingCechDifferential_comp_alternatingCechDifferential 𝒰 F)

/-- The degreewise inclusion of alternating Čech cochains into ordinary Čech cochains. -/
abbrev alternatingCechInclusionComponent (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (alternatingCechComplex 𝒰 F).X p ⟶ ((cechComplexFunctor 𝒰).obj F).X p :=
  AddCommGrpCat.ofHom (alternatingCechTermSubgroup 𝒰 F p).subtype ≫
    eqToHom (cechComplexFunctor_obj_X 𝒰 F p).symm

-- Proof sketch: the inclusion is compatible with differentials because the alternating complex was
-- defined by restricting the ordinary Čech differential.
/-- The inclusion of alternating Čech cochains is a morphism of complexes. -/
theorem alternatingCechInclusionComponent_comm (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    alternatingCechInclusionComponent 𝒰 F p ≫ ((cechComplexFunctor 𝒰).obj F).d p (p + 1) =
      (alternatingCechComplex 𝒰 F).d p (p + 1) ≫
        alternatingCechInclusionComponent 𝒰 F (p + 1) := sorry

-- Proof sketch: in a cochain complex indexed by `ℕ`, the only nontrivial shape relation is
-- `j = i + 1`, so the previously recorded consecutive-degree compatibility suffices.
/-- The inclusion of alternating Čech cochains satisfies the full cochain-map compatibility
relation. -/
theorem alternatingCechInclusion_comm (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    ∀ i j : ℕ, (ComplexShape.up ℕ).Rel i j →
      alternatingCechInclusionComponent 𝒰 F i ≫ ((cechComplexFunctor 𝒰).obj F).d i j =
        (alternatingCechComplex 𝒰 F).d i j ≫ alternatingCechInclusionComponent 𝒰 F j := sorry

/-- The canonical inclusion of the alternating Čech complex into the ordinary Čech complex. -/
def alternatingCechInclusion (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    alternatingCechComplex 𝒰 F ⟶ (cechComplexFunctor 𝒰).obj F :=
  { f := alternatingCechInclusionComponent 𝒰 F
    comm' := alternatingCechInclusion_comm 𝒰 F }

-- Proof sketch: componentwise projection to the strictly increasing indices is linear because it is
-- just evaluation of an ordinary Čech cochain on the chosen ordered tuples.
/-- The projection from ordinary Čech cochains to ordered Čech cochains is additive. -/
theorem cechProjectionToOrderedCechComponent_map_add (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s t : cechTerm 𝒰 F p) :
    (fun σ : StrictCechTuple p ↦ (s + t) σ.1) =
      (fun σ : StrictCechTuple p ↦ s σ.1) +
        fun σ : StrictCechTuple p ↦ t σ.1 := sorry

/-- The degreewise projection from the ordinary Čech complex to the ordered Čech complex. -/
abbrev cechProjectionToOrderedCechComponent (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    ((cechComplexFunctor 𝒰).obj F).X p ⟶ (orderedCechComplex 𝒰 F).X p :=
  eqToHom (cechComplexFunctor_obj_X 𝒰 F p) ≫
    AddCommGrpCat.ofHom
      (AddMonoidHom.mk'
        (fun s σ ↦ s σ.1)
        (cechProjectionToOrderedCechComponent_map_add 𝒰 F p))

-- Proof sketch: both differentials use the same alternating restriction formula, and restricting
-- to strictly increasing tuples before or after applying the differential gives the same result.
/-- The projection to ordered Čech cochains commutes with the differentials. -/
theorem cechProjectionToOrderedCechComponent_comm (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    cechProjectionToOrderedCechComponent 𝒰 F p ≫ (orderedCechComplex 𝒰 F).d p (p + 1) =
      ((cechComplexFunctor 𝒰).obj F).d p (p + 1) ≫
        cechProjectionToOrderedCechComponent 𝒰 F (p + 1) := sorry

/-- The extension of an ordered Čech cochain to an alternating Čech cochain obtained by sorting an
injective tuple and inserting the corresponding sign, and by sending tuples with repetitions to
zero. -/
def orderedCechComparisonToFun (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechTerm 𝒰 F p → cechTerm 𝒰 F p :=
  fun s σ ↦
    if hσ : Function.Injective σ then
      let τ := Tuple.sort σ
      let σ' : StrictCechTuple p := sortedStrictCechTupleOfInjective σ hσ
      (Equiv.Perm.sign τ) •
        F.map (eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm).op (s σ')
    else
      0

-- Proof sketch: by construction the comparison map kills tuples with repeated indices and its
-- value on an injective tuple changes by the sign of the reordering permutation.
/-- The ordered-to-alternating comparison formula lands in alternating Čech cochains. -/
theorem orderedCechComparisonToFun_mem_alternating (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) (s : orderedCechTerm 𝒰 F p) :
    IsAlternatingCechCochain 𝒰 F p (orderedCechComparisonToFun 𝒰 F p s) := sorry

-- Proof sketch: the extension formula for `c` is linear in the ordered cochain.
/-- The ordered-to-alternating comparison map is additive on cochains. -/
theorem orderedCechComparisonToFun_map_add (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s t : orderedCechTerm 𝒰 F p) :
    orderedCechComparisonToFun 𝒰 F p (s + t) =
      orderedCechComparisonToFun 𝒰 F p s + orderedCechComparisonToFun 𝒰 F p t := sorry

/-- The ordered comparison formula packaged as an alternating Čech cochain. -/
def orderedCechComparisonAlternatingCochain (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechTerm 𝒰 F p → alternatingCechTerm 𝒰 F p :=
  fun s ↦
    ⟨orderedCechComparisonToFun 𝒰 F p s,
      orderedCechComparisonToFun_mem_alternating 𝒰 F p s⟩

-- Proof sketch: the packaged alternating cochain is defined from the linear extension formula for
-- `c`, so additivity is inherited from `orderedCechComparisonToFun`.
/-- The packaged ordered-to-alternating comparison is additive. -/
theorem orderedCechComparisonComponent_map_add (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s t : (orderedCechComplex 𝒰 F).X p) :
    orderedCechComparisonAlternatingCochain 𝒰 F p (s + t) =
      orderedCechComparisonAlternatingCochain 𝒰 F p s +
        orderedCechComparisonAlternatingCochain 𝒰 F p t := sorry

/-- The degreewise comparison map from ordered Čech cochains to alternating Čech cochains. -/
abbrev orderedCechComparisonComponent (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (orderedCechComplex 𝒰 F).X p ⟶ (alternatingCechComplex 𝒰 F).X p :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk'
      (orderedCechComparisonAlternatingCochain 𝒰 F p)
      (orderedCechComparisonComponent_map_add 𝒰 F p))

-- Proof sketch: both sides are computed by the same signed extension rule followed by the ordinary
-- Čech differential, so the component formulas agree degreewise.
/-- The ordered-to-alternating comparison is a morphism of complexes. -/
theorem orderedCechComparisonComponent_comm (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechComparisonComponent 𝒰 F p ≫ (alternatingCechComplex 𝒰 F).d p (p + 1) =
      (orderedCechComplex 𝒰 F).d p (p + 1) ≫
        orderedCechComparisonComponent 𝒰 F (p + 1) := sorry

-- Proof sketch: for `ℕ`-indexed cochain complexes, the full compatibility relation reduces to the
-- consecutive-degree formula already recorded in `orderedCechComparisonComponent_comm`.
/-- The comparison `c` satisfies the full cochain-map compatibility relation. -/
theorem orderedCechComparison_comm (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    ∀ i j : ℕ, (ComplexShape.up ℕ).Rel i j →
      orderedCechComparisonComponent 𝒰 F i ≫ (alternatingCechComplex 𝒰 F).d i j =
        (orderedCechComplex 𝒰 F).d i j ≫ orderedCechComparisonComponent 𝒰 F j := sorry

/-- The canonical comparison morphism `c : \check C_{ord}^\bullet → \check C_{alt}^\bullet`. -/
def orderedCechComparison (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    orderedCechComplex 𝒰 F ⟶ alternatingCechComplex 𝒰 F :=
  { f := orderedCechComparisonComponent 𝒰 F
    comm' := orderedCechComparison_comm 𝒰 F }

-- Proof sketch: the ordered differential is the same alternating-sum restriction formula as the
-- ordinary Čech differential, so projection to ordered tuples commutes with `d`.
/-- The projection from the ordinary Čech complex to the ordered Čech complex satisfies the full
cochain-map compatibility relation. -/
theorem cechProjectionToOrderedCech_comm (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    ∀ i j : ℕ, (ComplexShape.up ℕ).Rel i j →
      cechProjectionToOrderedCechComponent 𝒰 F i ≫ (orderedCechComplex 𝒰 F).d i j =
        ((cechComplexFunctor 𝒰).obj F).d i j ≫ cechProjectionToOrderedCechComponent 𝒰 F j :=
      sorry

/-- Lemma 20.23.4 (1): the projection to the strictly increasing multi-indices defines the map
`\pi : \check{\mathcal C}^\bullet(\mathcal U,\mathcal F) \to
\check{\mathcal C}_{ord}^\bullet(\mathcal U,\mathcal F)` as a morphism of complexes. -/
def cechProjectionToOrderedCech (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    (cechComplexFunctor 𝒰).obj F ⟶ orderedCechComplex 𝒰 F :=
  { f := cechProjectionToOrderedCechComponent 𝒰 F
    comm' := cechProjectionToOrderedCech_comm 𝒰 F }

/-- The projection `π : \check C_{alt}^\bullet → \check C_{ord}^\bullet` obtained by first
including alternating Čech cochains into the ordinary Čech complex and then restricting to the
strictly increasing tuples. -/
abbrev alternatingCechProjection (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    alternatingCechComplex 𝒰 F ⟶ orderedCechComplex 𝒰 F :=
  alternatingCechInclusion 𝒰 F ≫ cechProjectionToOrderedCech 𝒰 F

-- Proof sketch: the ordered complex and the alternating subcomplex are identified by the explicit
-- comparison maps `c` and `π`, which undo each other on strictly increasing tuples.
/-- Lemma 20.23.4 (2): the restriction of `π` to alternating Čech cochains is an isomorphism of
complexes onto the ordered Čech complex. -/
theorem alternatingCechProjection_isIso (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    IsIso (alternatingCechProjection 𝒰 F) := sorry

-- Proof sketch: applying `c` first extends an ordered cochain by the signed permutation rule, and
-- restricting back with `π` recovers the original ordered coordinates.
/-- Lemma 20.23.4 (3): the induced map `π : \check{\mathcal C}_{alt}^\bullet(\mathcal U,\mathcal
F) \to \check{\mathcal C}_{ord}^\bullet(\mathcal U,\mathcal F)` is a left inverse to the
comparison morphism `c`. -/
theorem orderedCechComparison_comp_alternatingCechProjection (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    orderedCechComparison 𝒰 F ≫ alternatingCechProjection 𝒰 F = 𝟙 _ := sorry

/-! ### Remark_20_23_5 (from Chap20) -/
open CategoryTheory Opposite TopologicalSpace
open Set.powersetCard
open scoped BigOperators

noncomputable section

universe u v

variable {X : TopCat.{u}} {ι : Type v}

/- Domain-style sampling for Remark 20.23.5:
- primary domain: explicit-order ordered Čech complexes and their invariance under changing the
  total order on the index set.
- sampled owner declarations:
  `OrderedCechIndex`,
  `orderedCechIndexOrderEmbedding`,
  `orderedCechTermOfOrder`,
  `orderedCechComplexOfOrder`.
- best owner abstraction: the explicit-order owner `orderedCechComplexOfOrder o 𝒰 F` from
  `Definition_20_23_2`; this file should stay at the bridge/view layer and construct the canonical
  change-of-order isomorphism between two such owners.

Source/core/bridge triage:
- `source-facing`: Remark 20.23.5, asserting canonical independence of the chosen total ordering.
- `core/canonical`: `orderedCechComplexOfOrder o 𝒰 F` and its explicit-order term/index API from
  `Definition_20_23_2`.
- `bridge/view`: the reindexing permutation, signed component isomorphisms, and the induced complex
  isomorphism between two order choices.

Primitive data versus derived API:
- primitive data: two linear orders `o₁`, `o₂`, the cover `𝒰`, and the presheaf `F`.
- derived API: the underlying finite subset of an ordered index, the reindexing permutation, the
  degreewise signed reindexing isomorphisms, and the resulting complex isomorphism. -/

/-- The finite subset of indices underlying an ordered Čech multi-index. -/
noncomputable def orderedCechIndexSubset (o : LinearOrder ι) {p : ℕ}
    (σ : OrderedCechIndex o p) : Set.powersetCard ι (p + 1) :=
  letI := o
  ofFinEmbEquiv (orderedCechIndexOrderEmbedding o σ)

/-- The enumeration of a finite index set by `Fin` with respect to an explicit linear order. -/
noncomputable def orderedCechIndexEnumeration (o : LinearOrder ι) {p : ℕ}
    (s : Set.powersetCard ι (p + 1)) : Fin (p + 1) ≃ s.val :=
  letI := o
  (orderIsoOfFin s).toEquiv

/-- Reordering the same finite Čech index set by a second total ordering. -/
noncomputable def orderedCechIndexReindex (o₁ o₂ : LinearOrder ι) {p : ℕ}
    (σ : OrderedCechIndex o₂ p) : OrderedCechIndex o₁ p :=
  let s := orderedCechIndexSubset o₂ σ
  letI := o₁
  let e := ofFinEmbEquiv.symm s
  ⟨e, e.strictMono⟩

/-- The permutation sending the `o₁`-ordering of a finite index set to its `o₂`-ordering. -/
noncomputable def orderedCechIndexPermutation (o₁ o₂ : LinearOrder ι) {p : ℕ}
    (σ : OrderedCechIndex o₂ p) : Equiv.Perm (Fin (p + 1)) :=
  let s := orderedCechIndexSubset o₂ σ
  let e₁ := orderedCechIndexEnumeration o₁ s
  let e₂ := orderedCechIndexEnumeration o₂ s
  e₂.trans e₁.symm

-- Proof sketch: both ordered embeddings enumerate the same finite subset of `ι`; `cechIntersection`
-- is the infimum of the corresponding family of opens, so it depends only on that subset and not
-- on which total ordering is used to list its elements.
/-- Reordering a finite Čech index set by a different total order does not change the underlying
intersection of covering opens. -/
theorem cechIntersection_orderedCechIndexReindex (o₁ o₂ : LinearOrder ι)
    (𝒰 : ι → Opens X) {p : ℕ} (σ : OrderedCechIndex o₂ p) :
    cechIntersection 𝒰 (orderedCechIndexReindex o₁ o₂ σ) = cechIntersection 𝒰 σ := sorry

-- Proof sketch: apply `F.obj` to the equality of intersections from
-- `cechIntersection_orderedCechIndexReindex`; the two section groups are the same object after this
-- rewrite.
/-- Reordering an ordered Čech multi-index identifies the two corresponding section groups. -/
theorem orderedCechComponent_eq (o₁ o₂ : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) {p : ℕ} (σ : OrderedCechIndex o₂ p) :
    F.obj (op (cechIntersection 𝒰 (orderedCechIndexReindex o₁ o₂ σ))) =
      F.obj (op (cechIntersection 𝒰 σ)) := sorry

/-- The canonical identification of section groups obtained by reordering the same finite index
set. -/
noncomputable def orderedCechComponentIso (o₁ o₂ : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) {p : ℕ} (σ : OrderedCechIndex o₂ p) :
    F.obj (op (cechIntersection 𝒰 (orderedCechIndexReindex o₁ o₂ σ))) ≅
      F.obj (op (cechIntersection 𝒰 σ)) :=
  eqToIso (orderedCechComponent_eq o₁ o₂ 𝒰 F σ)

/-- The coordinatewise signed reindexing map from the ordered Čech term for `o₁` to the ordered
Čech term for `o₂`. -/
noncomputable def orderedCechTermChangeOrderToFun (o₁ o₂ : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechTermOfOrder o₁ 𝒰 F p → orderedCechTermOfOrder o₂ 𝒰 F p :=
  fun s σ ↦
    (↑(Equiv.Perm.sign (orderedCechIndexPermutation o₁ o₂ σ)) : ℤ) •
      (orderedCechComponentIso o₁ o₂ 𝒰 F σ).hom (s (orderedCechIndexReindex o₁ o₂ σ))

/-- The inverse coordinatewise signed reindexing map from the ordered Čech term for `o₂` to the
ordered Čech term for `o₁`. -/
noncomputable def orderedCechTermChangeOrderInvFun (o₁ o₂ : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechTermOfOrder o₂ 𝒰 F p → orderedCechTermOfOrder o₁ 𝒰 F p :=
  fun s σ ↦
    (↑(Equiv.Perm.sign (orderedCechIndexPermutation o₂ o₁ σ)) : ℤ) •
      (orderedCechComponentIso o₂ o₁ 𝒰 F σ).hom (s (orderedCechIndexReindex o₂ o₁ σ))

-- Proof sketch: evaluation at any ordered multi-index is additive, the identification morphism of
-- section groups is additive, and multiplication by the sign of a permutation is additive.
/-- The signed reindexing map between ordered Čech terms is additive. -/
theorem orderedCechTermChangeOrderToFun_map_add (o₁ o₂ : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s t : orderedCechTermOfOrder o₁ 𝒰 F p) :
    orderedCechTermChangeOrderToFun o₁ o₂ 𝒰 F p (s + t) =
      orderedCechTermChangeOrderToFun o₁ o₂ 𝒰 F p s +
        orderedCechTermChangeOrderToFun o₁ o₂ 𝒰 F p t := sorry

-- Proof sketch: apply the forward map and then the reverse map at a fixed ordered multi-index.
-- The two reindexings return to the original finite subset, the two identification isomorphisms
-- compose to the identity, and the two permutation signs multiply to `1`.
/-- Changing from `o₁` to `o₂` and back recovers the original ordered Čech term. -/
theorem orderedCechTermChangeOrder_left_inv (o₁ o₂ : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : orderedCechTermOfOrder o₁ 𝒰 F p) :
    orderedCechTermChangeOrderInvFun o₁ o₂ 𝒰 F p
        (orderedCechTermChangeOrderToFun o₁ o₂ 𝒰 F p s) = s := sorry

-- Proof sketch: the same argument as in `orderedCechTermChangeOrder_left_inv`, with the two orders
-- interchanged, shows that the reverse map is also a left inverse of the forward map.
/-- Changing from `o₂` to `o₁` and back recovers the original ordered Čech term. -/
theorem orderedCechTermChangeOrder_right_inv (o₁ o₂ : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : orderedCechTermOfOrder o₂ 𝒰 F p) :
    orderedCechTermChangeOrderToFun o₁ o₂ 𝒰 F p
        (orderedCechTermChangeOrderInvFun o₁ o₂ 𝒰 F p s) = s := sorry

/-- The signed reindexing equivalence between ordered Čech terms for two total orders. -/
noncomputable def orderedCechTermChangeOrderEquiv (o₁ o₂ : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechTermOfOrder o₁ 𝒰 F p ≃+ orderedCechTermOfOrder o₂ 𝒰 F p where
  toFun := orderedCechTermChangeOrderToFun o₁ o₂ 𝒰 F p
  invFun := orderedCechTermChangeOrderInvFun o₁ o₂ 𝒰 F p
  map_add' := orderedCechTermChangeOrderToFun_map_add o₁ o₂ 𝒰 F p
  left_inv := orderedCechTermChangeOrder_left_inv o₁ o₂ 𝒰 F p
  right_inv := orderedCechTermChangeOrder_right_inv o₁ o₂ 𝒰 F p

/-- The degreewise signed reindexing isomorphism between ordered Čech terms for two total orders. -/
noncomputable def orderedCechTermChangeOrderIso (o₁ o₂ : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechTermOfOrder o₁ 𝒰 F p ≅ orderedCechTermOfOrder o₂ 𝒰 F p :=
  (orderedCechTermChangeOrderEquiv o₁ o₂ 𝒰 F p).toAddCommGrpIso

-- Proof sketch: compare the two ordered Čech differentials componentwise. After reindexing a
-- fixed finite subset, omitting the `j`th entry before or after changing orders differs exactly by
-- the sign of the permutation that records how the two total orderings enumerate the same subset,
-- so the signed reindexing intertwines the alternating sums.
/-- The degreewise signed reindexing is compatible with the ordered Čech differentials. -/
theorem orderedCechTermChangeOrder_comm (o₁ o₂ : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    ∀ i j, (ComplexShape.up ℕ).Rel i j →
      (orderedCechTermChangeOrderIso o₁ o₂ 𝒰 F i).hom ≫
          (orderedCechComplexOfOrder o₂ 𝒰 F).d i j =
        (orderedCechComplexOfOrder o₁ 𝒰 F).d i j ≫
          (orderedCechTermChangeOrderIso o₁ o₂ 𝒰 F j).hom := sorry

/-- Remark 20.23.5: two total orderings on the index set define canonically isomorphic ordered
Čech complexes, so the ordered Čech complex is independent of the chosen total ordering up to a
canonical isomorphism of complexes. -/
noncomputable def orderedCechComplexChangeOrderIso (o₁ o₂ : LinearOrder ι)
    (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) :
    orderedCechComplexOfOrder o₁ 𝒰 F ≅ orderedCechComplexOfOrder o₂ 𝒰 F :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ orderedCechTermChangeOrderIso o₁ o₂ 𝒰 F p)
    (orderedCechTermChangeOrder_comm o₁ o₂ 𝒰 F)

-- Proof sketch: by construction `orderedCechComplexChangeOrderIso` is obtained from the
-- degreewise signed reindexing equivalences, so its degree-`p` component is exactly the map
-- described by the explicit permutation formula in the textbook.
/-- The degree-`p` component of the order-change isomorphism is the signed reindexing map given by
the permutation that compares the two orderings on the same finite subset of indices. -/
theorem orderedCechComplexChangeOrderIso_hom_apply (o₁ o₂ : LinearOrder ι)
    (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : orderedCechTermOfOrder o₁ 𝒰 F p) (σ : OrderedCechIndex o₂ p) :
    ((orderedCechComplexChangeOrderIso o₁ o₂ 𝒰 F).hom.f p s) σ =
      (↑(Equiv.Perm.sign (orderedCechIndexPermutation o₁ o₂ σ)) : ℤ) •
        (orderedCechComponentIso o₁ o₂ 𝒰 F σ).hom
          (s (orderedCechIndexReindex o₁ o₂ σ)) := sorry

/-! ### Lemma_20_23_6 (from Chap20) -/
open CategoryTheory HomologicalComplex TopologicalSpace

noncomputable section

universe u v

variable {X : TopCat.{u}} {ι : Type v} [LinearOrder ι]

local instance : HasFiniteProducts (Opens X) := opensHasFiniteProducts X

/-- The morphism from the ordinary Čech complex to the alternating Čech complex obtained by first
projecting to ordered cochains and then extending by the signed comparison map. -/
abbrev cechProjectionToAlternating (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    (cechComplexFunctor 𝒰).obj F ⟶ alternatingCechComplex 𝒰 F :=
  cechProjectionToOrderedCech 𝒰 F ≫ orderedCechComparison 𝒰 F

-- Proof sketch: use the explicit first homotopy from 20.23.6.1 to pass from the identity of the
-- ordinary Čech complex to the semi-alternating projector, identify the semi-alternating complex
-- with the semi-ordered complex, and then apply the second explicit homotopy 20.23.6.2 to deform
-- further to the ordered projector. Transporting along the comparison map from ordered to
-- alternating cochains yields the displayed composite with the alternating inclusion.
/-- Lemma 20.23.6 (1): the composite of the projection from ordinary to ordered Čech cochains with
the comparison to alternating cochains, followed by the inclusion of the alternating Čech complex
into the ordinary Čech complex, is homotopic to the identity on the ordinary Čech complex. -/
theorem cechProjectionToAlternating_comp_alternatingCechInclusion_homotopic_id
    (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) :
    Nonempty
      (Homotopy
        (cechProjectionToAlternating 𝒰 F ≫ alternatingCechInclusion 𝒰 F)
        (𝟙 ((cechComplexFunctor 𝒰).obj F))) := sorry

-- Proof sketch: use `cechProjectionToAlternating` as the candidate homotopy inverse to the
-- inclusion. The previous theorem provides a homotopy from the composite on the ordinary Čech
-- complex to the identity, while Lemma 20.23.4 identifies the alternating complex with the ordered
-- complex and gives the identity on the alternating side after projecting back to ordered
-- cochains.
/-- Lemma 20.23.6 (2): the inclusion
`\check{\mathcal C}_{alt}^\bullet(\mathcal U,\mathcal F) \to
\check{\mathcal C}^\bullet(\mathcal U,\mathcal F)` is a homotopy equivalence of cochain
complexes. -/
theorem alternatingCechInclusion_isHomotopyEquivalence
    (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) :
    (homotopyEquivalences AddCommGrpCat.{max u v} (ComplexShape.up ℕ))
      (alternatingCechInclusion 𝒰 F) := sorry

/-! ### Lemma_20_23_7 (from Chap20) -/
open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Limits
open scoped BigOperators ZeroObject

noncomputable section

universe u v

variable {X : TopCat.{u}} {ι : Type v}

local instance : HasFiniteProducts (Opens X) := opensHasFiniteProducts X

/- Domain-style sampling for Lemma 20.23.7:
- primary domain: augmentations and extended complexes built from the alternating and ordered Čech
  complexes of a cover;
- sampled owner declarations:
  `cechAugmentationToFun`,
  `alternatingCechComplex`,
  `orderedCechComplex`,
  `orderedCechComparison`;
- best owner abstraction: the ordinary Čech augmentation remains at the canonical owner from
  `Lemma_20_9_3`, while the alternating and ordered Čech complexes are reused directly from
  `Lemma_20_23_4` and `Definition_20_23_2`; this file adds only the augmentation and
  `fromSingle₀` bridge layer.

Source/core/bridge triage:
- `source-facing`: the extended alternating and extended ordered Čech complexes of Lemma 20.23.7;
- `core/canonical`: `cechAugmentationToFun`, `alternatingCechComplex`, and `orderedCechComplex`;
- `bridge/view`: the degree-zero augmentation maps into those complexes and the resulting
  `fromSingle₀` complexes.

Primitive data versus derived API:
- primitive data: the open `U`, the family `𝒰`, the presheaf `F`, and the cover equality
  `hcover : U = iSup 𝒰`;
- derived API: the alternating and ordered augmentation maps and the extended complexes built from
  them. -/

-- Proof sketch: in degree `0` every tuple is automatically injective and every permutation of
-- `Fin 1` is trivial, so the degree-zero restriction cochain is alternating.
/-- The ordinary degree-zero Čech augmentation defines an alternating cochain. -/
theorem cechAugmentationToFun_isAlternating_zero
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) (s : F.obj (op U)) :
    IsAlternatingCechCochain 𝒰 F 0 (cechAugmentationToFun U 𝒰 F hcover s) := sorry

/-- The canonical augmentation from `F(U)` to degree `0` of the alternating Čech complex. -/
def alternatingCechAugmentationToFun
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) :
    F.obj (op U) → (alternatingCechComplex 𝒰 F).X 0 :=
  fun s ↦
    ⟨cechAugmentationToFun U 𝒰 F hcover s,
      cechAugmentationToFun_isAlternating_zero U 𝒰 F hcover s⟩

-- Proof sketch: the underlying degree-zero Čech augmentation is additive, and the alternating
-- version just repackages it in the alternating subgroup.
/-- The alternating Čech augmentation is additive. -/
theorem alternatingCechAugmentationToFun_map_add
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) (s t : F.obj (op U)) :
    alternatingCechAugmentationToFun U 𝒰 F hcover (s + t) =
      alternatingCechAugmentationToFun U 𝒰 F hcover s +
        alternatingCechAugmentationToFun U 𝒰 F hcover t := sorry

/-- The canonical map from `F(U)` to degree `0` of the alternating Čech complex. -/
abbrev alternatingCechAugmentationMap
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) :
    F.obj (op U) ⟶ (alternatingCechComplex 𝒰 F).X 0 :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (alternatingCechAugmentationToFun U 𝒰 F hcover)
      (alternatingCechAugmentationToFun_map_add U 𝒰 F hcover))

-- Proof sketch: evaluate the alternating differential on the degree-zero restriction family and
-- observe that the two faces of every double intersection coincide with opposite signs.
/-- The alternating Čech augmentation is a degree-zero cocycle. -/
theorem alternatingCechAugmentationMap_comp_d_zero_one
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) :
    alternatingCechAugmentationMap U 𝒰 F hcover ≫
        (alternatingCechComplex 𝒰 F).d 0 1 =
      0 := sorry

/-- The augmentation from `F(U)` to the alternating Čech complex viewed as a map from a single-term
complex in degree `0`. -/
abbrev alternatingExtendedCechComplexAugmentation
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) :
    (CochainComplex.single₀ AddCommGrpCat.{max u v}).obj (F.obj (op U)) ⟶
      alternatingCechComplex 𝒰 F :=
  (CochainComplex.fromSingle₀Equiv (alternatingCechComplex 𝒰 F) (F.obj (op U))).symm
    ⟨alternatingCechAugmentationMap U 𝒰 F hcover,
      alternatingCechAugmentationMap_comp_d_zero_one U 𝒰 F hcover⟩

/-- The extended alternating Čech complex obtained by placing `F(U)` in degree `-1`. -/
def alternatingExtendedCechComplex
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) :
    CochainComplex AddCommGrpCat.{max u v} ℕ :=
  CochainComplex.fromSingle₀AsComplex (alternatingCechComplex 𝒰 F) (F.obj (op U))
    (alternatingExtendedCechComplexAugmentation U 𝒰 F hcover)

-- Proof sketch: compare the extended alternating Čech complex with the ordinary extended Čech
-- complex and transport the explicit contracting homotopy from the ordinary case.
/-- Lemma 20.23.7 (1): if an open cover of `U` contains `U` itself, then the extended alternating
Čech complex obtained by adjoining `F(U)` in degree `-1` is homotopy equivalent to the zero
complex. -/
theorem alternatingExtendedCechComplex_homotopyEquivalent_zero_of_exists_eq
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) (htrivial : ∃ i : ι, 𝒰 i = U) :
    Nonempty
      (HomotopyEquiv (alternatingExtendedCechComplex U 𝒰 F hcover)
        ((CochainComplex.single₀ AddCommGrpCat.{max u v}).obj
          (⊥_ AddCommGrpCat.{max u v}))) := sorry

section Ordered

variable [LinearOrder ι]

/-- The canonical augmentation from `F(U)` to degree `0` of the ordered Čech complex. -/
def orderedCechAugmentationToFun
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) :
    F.obj (op U) → (orderedCechComplex 𝒰 F).X 0 :=
  fun s σ ↦
    F.map (homOfLE (cechIntersection_le_of_iSup_eq U 𝒰 hcover σ.1)).op s

-- Proof sketch: each ordered degree-zero component is a restriction morphism from `F(U)`, hence
-- the augmentation is additive componentwise.
/-- The ordered Čech augmentation is additive. -/
theorem orderedCechAugmentationToFun_map_add
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) (s t : F.obj (op U)) :
    orderedCechAugmentationToFun U 𝒰 F hcover (s + t) =
      orderedCechAugmentationToFun U 𝒰 F hcover s +
        orderedCechAugmentationToFun U 𝒰 F hcover t := sorry

/-- The canonical map from `F(U)` to degree `0` of the ordered Čech complex. -/
abbrev orderedCechAugmentationMap
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) :
    F.obj (op U) ⟶ (orderedCechComplex 𝒰 F).X 0 :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (orderedCechAugmentationToFun U 𝒰 F hcover)
      (orderedCechAugmentationToFun_map_add U 𝒰 F hcover))

-- Proof sketch: the ordered degree-one differential is the alternating sum of the two
-- restrictions to double intersections, and those two terms are equal with opposite signs.
/-- The ordered Čech augmentation is a degree-zero cocycle. -/
theorem orderedCechAugmentationMap_comp_d_zero_one
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) :
    orderedCechAugmentationMap U 𝒰 F hcover ≫ (orderedCechComplex 𝒰 F).d 0 1 = 0 := sorry

/-- The augmentation from `F(U)` to the ordered Čech complex viewed as a map from a single-term
complex in degree `0`. -/
abbrev orderedExtendedCechComplexAugmentation
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) :
    (CochainComplex.single₀ AddCommGrpCat.{max u v}).obj (F.obj (op U)) ⟶
      orderedCechComplex 𝒰 F :=
  (CochainComplex.fromSingle₀Equiv (orderedCechComplex 𝒰 F) (F.obj (op U))).symm
    ⟨orderedCechAugmentationMap U 𝒰 F hcover,
      orderedCechAugmentationMap_comp_d_zero_one U 𝒰 F hcover⟩

/-- The extended ordered Čech complex obtained by placing `F(U)` in degree `-1`. -/
def orderedExtendedCechComplex
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) :
    CochainComplex AddCommGrpCat.{max u v} ℕ :=
  CochainComplex.fromSingle₀AsComplex (orderedCechComplex 𝒰 F) (F.obj (op U))
    (orderedExtendedCechComplexAugmentation U 𝒰 F hcover)

-- Proof sketch: insert the distinguished index with `U_i = U` into every ordered multi-index to
-- obtain the standard contracting homotopy described in the textbook.
/-- Lemma 20.23.7 (2): for any total ordering on the index set, if an open cover of `U` contains
`U` itself, then the extended ordered Čech complex obtained by adjoining `F(U)` in degree `-1` is
homotopy equivalent to the zero complex. -/
theorem orderedExtendedCechComplex_homotopyEquivalent_zero_of_exists_eq
    (U : Opens X) (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (hcover : U = iSup 𝒰) (htrivial : ∃ i : ι, 𝒰 i = U) :
    Nonempty
      (HomotopyEquiv (orderedExtendedCechComplex U 𝒰 F hcover)
        ((CochainComplex.single₀ AddCommGrpCat.{max u v}).obj
          (⊥_ AddCommGrpCat.{max u v}))) := sorry

end Ordered

end
