import Mathlib
import stacks_project.Chap20.Definition_20_23_2

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
