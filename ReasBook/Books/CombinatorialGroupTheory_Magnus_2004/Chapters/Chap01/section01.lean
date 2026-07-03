import Mathlib
import Mathlib.GroupTheory.FreeGroup.GeneratorEquiv

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_1_1 (from Items/Chap01) -/
variable {F : Type u} [Group F] {X : Set F}

-- Layer triage:
-- `source-facing`: the textbook subset-style universal property for a basis of a free group.
-- `core/canonical`: `FreeGroupBasis X F` is the owner abstraction for a free group with chosen
-- basis indexed by `X`.
-- `bridge/view`: the inclusion `Subtype.val : X → F` identifies the source subset with that owner
-- basis data.
--
-- Domain sampling:
-- 1. `FreeGroupBasis.ofUniqueLift` is the canonical owner constructor from a unique-extension
--    universal property.
-- 2. `FreeGroupBasis.isFreeGroup` is the canonical owner theorem that a chosen basis makes the
--    ambient group free.
-- 3. `FreeGroupBasis.lift` and `FreeGroupBasis.ext_hom` are the owner APIs behind the reverse
--    bridge from a chosen basis to the textbook subset property.
--
-- Primitive vs. derived:
-- the primitive source data are only the subset `X` and its unique-extension universal property.
-- The chosen owner-side basis and the ambient `IsFreeGroup F` instance are derived from that
-- source-facing predicate.

/-- Definition 1-1-1: A subset `X` of a group `F` is a basis of a free group structure on `F`
when every function from `X` to any group extends uniquely to a homomorphism from `F`. -/
def IsFreeGroupBasis (X : Set F) : Prop :=
  ∀ {H : Type u} [Group H] (φ : X → H), ∃! φStar : F →* H, ∀ x : X, φStar x.1 = φ x

/-- A subset satisfying the textbook universal property makes the ambient group free. -/
-- Proof sketch: Apply `IsFreeGroup.ofUniqueLift` to the inclusion `Subtype.val : X → F`, and use
-- the canonical owner bridge `FreeGroupBasis.ofUniqueLift`; then use
-- `FreeGroupBasis.isFreeGroup`.
theorem IsFreeGroupBasis.isFreeGroup (hX : IsFreeGroupBasis X) : IsFreeGroup F :=
  (FreeGroupBasis.ofUniqueLift X Subtype.val hX).isFreeGroup

namespace FreeGroupBasis

/-- Reindex a free group basis by its image subset in the ambient group. -/
protected noncomputable def reindexRange {ι : Type v} (b : FreeGroupBasis ι F) :
    FreeGroupBasis (Set.range b) F :=
  b.reindex (Equiv.ofInjective b b.injective)

@[simp] theorem reindexRange_apply {ι : Type v} (b : FreeGroupBasis ι F) (x : Set.range b) :
    b.reindexRange x = x.1 := by
  simpa [FreeGroupBasis.reindexRange] using Equiv.apply_ofInjective_symm b.injective x

/-- A `FreeGroupBasis` indexed by the subtype `X` gives the source-style basis property when its
underlying map is the inclusion of `X` into `F`. -/
-- Proof sketch: Use the equivalence `b.lift` to obtain the extending homomorphism, then use the
-- hypothesis `hb` to identify the basis elements with the corresponding elements of the subset `X`
-- and conclude uniqueness from the inverse direction of `b.lift`.
theorem isFreeGroupBasis (b : FreeGroupBasis X F) (hb : ∀ x : X, b x = x.1) :
    IsFreeGroupBasis X :=
  fun {H} _ φ ↦ by
    refine ⟨b.lift φ, ?_, ?_⟩
    · intro x
      have hbx : (b.lift φ) (b x) = φ x := congr_fun (b.lift.symm_apply_apply φ) x
      simpa [hb x] using hbx
    · intro ψ hψ
      apply b.ext_hom
      intro x
      have hbx : (b.lift φ) (b x) = φ x := congr_fun (b.lift.symm_apply_apply φ) x
      calc
        ψ (b x) = ψ x.1 := by rw [hb x]
        _ = φ x := hψ x
        _ = (b.lift φ) (b x) := hbx.symm

/-- Any chosen free basis yields the source-style basis predicate on its image subset. -/
theorem isFreeGroupBasis_range {ι : Type v} (b : FreeGroupBasis ι F) :
    IsFreeGroupBasis (Set.range b) :=
  FreeGroupBasis.isFreeGroupBasis b.reindexRange b.reindexRange_apply

end FreeGroupBasis

/-! ### Proposition_1_1_2 (from Items/Chap01) -/
-- Layer triage:
-- `source-facing`: the subset-style basis hypotheses `IsFreeGroupBasis X₁` and
--   `IsFreeGroupBasis X₂`.
-- `core/canonical`: `FreeGroupBasis ι F` is the owner abstraction for a group with a chosen free
--   basis.
-- `bridge/view`: `FreeGroupBasis.ofUniqueLift X Subtype.val` turns the textbook subset universal
--   property into the owner basis data.
--
-- Domain sampling:
-- 1. `FreeGroupBasis.ofUniqueLift` is the canonical bridge from the source universal property to a
--    chosen basis.
-- 2. `FreeGroupBasis.map` transports a chosen basis across a group isomorphism.
-- 3. `FreeGroupBasis.reindex` transports a chosen basis across an equivalence of indexing types.
-- 4. `FreeGroupBasis.cardinal_eq` is the chapter owner theorem that any two bases of the same
--    free group have the same cardinality.
--
-- Primitive vs. derived:
-- the primitive source data are only the two subset-style basis hypotheses. The chosen owner-side
-- bases arise canonically from `FreeGroupBasis.ofUniqueLift`, and the group isomorphism in the
-- reverse direction is derived by reindexing one chosen basis along an equivalence of the index
-- types.

namespace FreeGroupBasis

/-- Two groups carrying chosen free bases are isomorphic if and only if those bases have the same
cardinality. -/
theorem nonempty_mulEquiv_iff_cardinal_eq {F₁ : Type u} {F₂ : Type u} [Group F₁] [Group F₂]
    {ι₁ : Type u} {ι₂ : Type u} (b₁ : FreeGroupBasis ι₁ F₁) (b₂ : FreeGroupBasis ι₂ F₂) :
    Nonempty (F₁ ≃* F₂) ↔ #ι₁ = #ι₂ := by
  constructor
  · rintro ⟨e⟩
    simpa using (b₁.map e).cardinal_eq b₂
  · intro hι
    obtain ⟨eι⟩ : Nonempty (ι₁ ≃ ι₂) := Cardinal.eq.mp hι
    exact ⟨(b₁.reindex eι).repr.trans b₂.repr.symm⟩

end FreeGroupBasis

/-- Proposition 1-1-2: If `X₁` and `X₂` are bases of the free groups `F₁` and `F₂`, then `F₁` and
`F₂` are isomorphic if and only if `X₁` and `X₂` have the same cardinality. -/
-- Proof sketch: bridge the two source-facing hypotheses to the owner abstraction
-- `FreeGroupBasis.ofUniqueLift Xᵢ Subtype.val hXᵢ`, then apply the owner theorem
-- `FreeGroupBasis.nonempty_mulEquiv_iff_cardinal_eq`.
theorem free_group_mulEquiv_iff_basis_cardinal_eq {F₁ : Type u} {F₂ : Type u} [Group F₁]
    [Group F₂] {X₁ : Set F₁} {X₂ : Set F₂} (hX₁ : IsFreeGroupBasis X₁)
    (hX₂ : IsFreeGroupBasis X₂) :
    Nonempty (F₁ ≃* F₂) ↔ #X₁ = #X₂ := by
  let b₁ : FreeGroupBasis X₁ F₁ := FreeGroupBasis.ofUniqueLift X₁ Subtype.val hX₁
  let b₂ : FreeGroupBasis X₂ F₂ := FreeGroupBasis.ofUniqueLift X₂ Subtype.val hX₂
  simpa using FreeGroupBasis.nonempty_mulEquiv_iff_cardinal_eq b₁ b₂

/-! ### Corollary_1_1_3 (from Items/Chap01) -/
/-- Corollary 1-1-3: Any two bases of the same free group have the same cardinality. This common
cardinality is the rank of the free group. -/
-- Proof sketch: A basis identifies `F` with a free group on its indexing type. Composing the
-- isomorphism coming from `b₁` with the one coming from `b₂` gives an isomorphism
-- `FreeGroup ι ≃* FreeGroup κ`, hence an equivalence `ι ≃ κ` by `Equiv.ofFreeGroupEquiv`; then
-- apply `Equiv.lift_cardinal_eq`.
theorem FreeGroupBasis.cardinal_eq {F : Type u} [Group F] {ι : Type v} {κ : Type w}
    (b₁ : FreeGroupBasis ι F) (b₂ : FreeGroupBasis κ F) :
    Cardinal.lift.{w} #ι = Cardinal.lift.{v} #κ := by
  simpa using
    (Equiv.ofFreeGroupEquiv (MulEquiv.trans b₁.repr.symm b₂.repr)).lift_cardinal_eq

/-! ### Proposition_1_1_4 (from Items/Chap01) -/
universe u

open QuotientGroup

variable {G : Type u} [Group G]
variable (S : Set G)

-- Layer triage:
-- `source-facing`: a group `G`, a subset `S ⊆ G`, the hypothesis that `S` generates `G`, and the
-- resulting quotient description of `G`.
-- `core/canonical`: the homomorphism `FreeGroup.lift (Subtype.val : S → G)`, its kernel, and the
-- first-isomorphism owner theorem `QuotientGroup.quotientKerEquivOfSurjective`.
-- `bridge/view`: the generating hypothesis is converted into surjectivity of the canonical lift by
-- `FreeGroup.closure_eq_range`, and the textbook quotient description is then exactly the kernel
-- quotient supplied by the owner theorem.
--
-- Domain sampling:
-- 1. `FreeGroup.lift` is the canonical map out of the free group determined by the generator
--    function `Subtype.val : S → G`.
-- 2. `FreeGroup.closure_eq_range` identifies the subgroup generated by `S` with the range of that
--    canonical lift.
-- 3. `MonoidHom.range_eq_top` is the owner-level bridge from a top-range statement to
--    surjectivity.
-- 4. `QuotientGroup.quotientKerEquivOfSurjective` is the canonical first-isomorphism equivalence.
--
-- Primitive vs. derived:
-- the primitive source data are only `S` and the hypothesis `Subgroup.closure S = ⊤`;
-- surjectivity of the canonical lift and the quotient equivalence are derived API.

/-- If `S` generates `G`, then the canonical lift `FreeGroup S →* G` is surjective. -/
private theorem lift_subtype_surjective
    (hS : Subgroup.closure S = (⊤ : Subgroup G)) :
    Function.Surjective (FreeGroup.lift (Subtype.val : S → G)) := by
  rwa [← MonoidHom.range_eq_top, ← FreeGroup.closure_eq_range]

/-- Proposition 1-1-4: if a group `G` is generated by a subset `S`, then `G` is canonically
isomorphic to the quotient of the free group on `S` by the kernel of the canonical lift. -/
-- Proof sketch: `FreeGroup.closure_eq_range` identifies the range of the canonical lift
-- `FreeGroup.lift ((↑) : S → G)` with the subgroup generated by `S`, so `hS` implies that this
-- lift is surjective. Apply `QuotientGroup.quotientKerEquivOfSurjective`.
noncomputable def quotient_freeGroup_of_generating_set
    (hS : Subgroup.closure S = (⊤ : Subgroup G)) :
    (FreeGroup S ⧸ (FreeGroup.lift (Subtype.val : S → G)).ker) ≃* G :=
  quotientKerEquivOfSurjective (FreeGroup.lift (Subtype.val : S → G))
    (lift_subtype_surjective S hS)

/-- The canonical isomorphism from the quotient of the free group sends the class of a word to
its evaluation in `G` under the canonical lift. -/
-- Proof sketch: unfold `quotient_freeGroup_of_generating_set` to the quotient-kernel equivalence
-- attached to `FreeGroup.lift ((↑) : S → G)`, then reduce to the standard quotient-kernel
-- evaluation formula on representatives.
@[simp] theorem quotient_freeGroup_of_generating_set_apply_mk
    (hS : Subgroup.closure S = (⊤ : Subgroup G)) (x : FreeGroup S) :
    quotient_freeGroup_of_generating_set S hS (mk x) =
      FreeGroup.lift (Subtype.val : S → G) x :=
  rfl

/-! ### Definition_1_1_5 (from Items/Chap01) -/
universe u

open CategoryTheory
open CategoryTheory.Projective

/-!
Primary domain: projective objects in the category of groups.

Layer triage:
- `source-facing`: projective groups, expressed by lifting homomorphisms along surjective group
  homomorphisms.
- `core/canonical`: `CategoryTheory.Projective` on `GrpCat`.
- `bridge/view`: the concrete group-hom lifting statement obtained from the owner abstraction using
  `GrpCat.epi_iff_surjective`.

Domain sampling:
1. `CategoryTheory.Projective` is mathlib's owner predicate for projective objects.
2. `Projective.factorThru` and `Projective.factorThru_comp` are the canonical factorization API for
   maps out of a projective object through an epimorphism.
3. `GrpCat.epi_iff_surjective` is the category-specific bridge identifying epimorphisms in
   `GrpCat` with surjective group homomorphisms.
4. `Projective.factors` is the primitive existence statement; the theorem below is the derived
   source-facing reformulation in ordinary group-hom language.

Primitive vs. derived:
the primitive owner-side data are only the projective factorization property in `GrpCat`; the
explicit lifting statement for surjective homomorphisms is derived from that owner abstraction and
should remain a bridge theorem rather than a parallel owner definition.
-/

/- Definition 1-1-5: a projective group is a projective object of `GrpCat`, equivalently a group
whose homomorphisms lift along surjective homomorphisms. -/
#check (Projective : GrpCat → Prop)

/-- A group is projective exactly when every homomorphism out of it lifts along surjective
group homomorphisms. -/
-- Proof sketch: use `GrpCat.epi_iff_surjective` to rewrite surjective homomorphisms as
-- epimorphisms in `GrpCat`, and then apply the defining factorization property of
-- `Projective`.
theorem group_projective_iff_lifts_along_surjective
    {P : Type u} [Group P] :
    Projective (GrpCat.of P) ↔
      ∀ ⦃G H : Type u⦄ [Group G] [Group H]
        (γ : G →* H) (_ : Function.Surjective γ) (π : P →* H),
        ∃ φ : P →* G, γ.comp φ = π := by
  constructor
  · intro hP G H _ _ γ hγ π
    letI : Projective (GrpCat.of P) := hP
    let γ' : GrpCat.of G ⟶ GrpCat.of H := GrpCat.ofHom γ
    let π' : GrpCat.of P ⟶ GrpCat.of H := GrpCat.ofHom π
    haveI : Epi γ' := (GrpCat.epi_iff_surjective γ').2 hγ
    refine ⟨(factorThru π' γ').hom, ?_⟩
    ext x
    change γ ((factorThru π' γ').hom x) = π x
    exact DFunLike.congr_fun (congrArg GrpCat.Hom.hom (factorThru_comp π' γ')) x
  · intro hLift
    refine ⟨fun {G H} π γ ↦ ?_⟩
    intro _hγepi
    have hγ : Function.Surjective γ.hom := (GrpCat.epi_iff_surjective γ).1 inferInstance
    obtain ⟨φ, hφ⟩ := hLift γ.hom hγ π.hom
    refine ⟨GrpCat.ofHom φ, ?_⟩
    ext x
    simpa using DFunLike.congr_fun hφ x

/-! ### Definition_1_1_6 (from Items/Chap01) -/
universe u

variable {G : Type u} [Group G]

open CategoryTheory

namespace MonoidHom

/-- A retraction is equivalently a surjective homomorphism onto `S` whose induced endomorphism of
`G` is idempotent. -/
-- Proof sketch: one direction uses the restriction-identity equation to get surjectivity and then
-- rewrites the square of `S.subtype.comp ρ`; the converse uses surjectivity onto `S` to test the
-- restriction identity on arbitrary elements of `S`.
theorem leftInverse_subtype_iff_surjective_and_idempotent {S : Subgroup G} (ρ : G →* S) :
    Function.LeftInverse ρ S.subtype ↔
      Function.Surjective ρ ∧
        (S.subtype.comp ρ).comp (S.subtype.comp ρ) = S.subtype.comp ρ := sorry

end MonoidHom

namespace Subgroup

/-- Definition 1-1-6: a subgroup is a retract of `G` exactly when its inclusion is split. -/
theorem subtype_isSplitMono_iff_exists_leftInverse (S : Subgroup G) :
    IsSplitMono (GrpCat.ofHom S.subtype) ↔ ∃ ρ : G →* S, Function.LeftInverse ρ S.subtype := by
  constructor
  · intro hS
    let _ : IsSplitMono (GrpCat.ofHom S.subtype) := hS
    refine ⟨(retraction (GrpCat.ofHom S.subtype)).hom, ?_⟩
    intro x
    exact
      DFunLike.congr_fun
        (congrArg GrpCat.Hom.hom (IsSplitMono.id (GrpCat.ofHom S.subtype))) x
  · rintro ⟨ρ, hρ⟩
    refine IsSplitMono.mk' ⟨GrpCat.ofHom ρ, ?_⟩
    ext x
    exact congrArg Subtype.val (hρ x)

/-- The whole group is a retract of itself. -/
theorem top_subtype_isSplitMono :
    IsSplitMono (GrpCat.ofHom ((⊤ : Subgroup G).subtype)) := by
  rw [subtype_isSplitMono_iff_exists_leftInverse]
  exact ⟨((Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).symm.toMonoidHom),
    (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).left_inv⟩

end Subgroup

/-! ### Proposition_1_1_7 (from Items/Chap01) -/
universe u

open CategoryTheory
open CategoryTheory.Projective

/-!
Primary domain: projective objects and retract subgroups in `GrpCat`.

Layer triage:
- `source-facing`: a projective group and the textbook assertion that it is isomorphic to a retract
  subgroup of a free group.
- `core/canonical`: `CategoryTheory.Projective`, `CategoryTheory.Retract`, `IsFreeGroup`, and the
  split-mono owner API in `GrpCat`.
- `bridge/view`: the subgroup inclusion `R.subtype`, together with
  `Subgroup.subtype_isSplitMono_iff_exists_leftInverse`, identifies “retract subgroup” with the
  categorical split-inclusion condition.

Domain sampling:
1. `CategoryTheory.Projective` is the owner abstraction for projective objects.
2. `Adjunction.map_projective` applied to `GrpCat.adj` is the owner-side route from projective
   types to projective free groups.
3. `CategoryTheory.Retract.projective` is the canonical theorem that retracts of projective objects
   are projective.
4. `Subgroup.subtype_isSplitMono_iff_exists_leftInverse` in `Definition_1_1_6` is the chapter's
   owner-level criterion for retract subgroups.

Primitive vs. derived:
the source-facing primitive data are the free ambient group, the subgroup, the isomorphism with
`P`, and the split inclusion of that subgroup. Projectivity of free groups and projectivity of the
retract subgroup are derived from the owner abstractions above and should not be reproved as
parallel local APIs.
-/

/-- Proposition 1-1-7: A group is projective exactly when it is isomorphic to a retract subgroup
of some free group. -/
-- Proof sketch: if `P` is projective, lift the identity of `P` along the canonical surjection
-- `FreeGroup P → P`; the image of the lift is then a retract subgroup of `FreeGroup P`
-- canonically isomorphic to `P`. Conversely, a retract subgroup of a free group is free, and
-- freeness transports across `MulEquiv`.
theorem projective_group_iff_isomorphic_to_retract_of_free_group {P : Type u} [Group P] :
    Projective (GrpCat.of P) ↔
      ∃ F : GrpCat.{u}, IsFreeGroup F ∧
        ∃ R : Subgroup F, ∃ _ : P ≃* R, IsSplitMono (GrpCat.ofHom R.subtype) := by
  constructor
  · intro hP
    let π : FreeGroup P →* P := FreeGroup.lift id
    have hπ : Function.Surjective π := fun p ↦ ⟨FreeGroup.of p, by simp [π]⟩
    obtain ⟨σ, hσ⟩ :=
      group_projective_iff_lifts_along_surjective.1 hP π hπ (MonoidHom.id P)
    let R : Subgroup (FreeGroup P) := σ.range
    let ρ : FreeGroup P →* R := (σ.comp π).codRestrict R fun x ↦ ⟨π x, rfl⟩
    have hρ : Function.LeftInverse ρ R.subtype := by
      rintro ⟨x, hx⟩
      rcases hx with ⟨p, rfl⟩
      apply Subtype.ext
      simpa using congrArg σ (DFunLike.congr_fun hσ p)
    have hσ' : Function.LeftInverse π σ := fun x ↦ DFunLike.congr_fun hσ x
    have hR : IsSplitMono (GrpCat.ofHom R.subtype) :=
      (Subgroup.subtype_isSplitMono_iff_exists_leftInverse R).2 ⟨ρ, hρ⟩
    exact ⟨GrpCat.of (FreeGroup P), inferInstance, R, MonoidHom.ofLeftInverse hσ', hR⟩
  · rintro ⟨F, hF, R, e, hR⟩
    letI : IsFreeGroup F := hF
    let X : GrpCat := GrpCat.of (FreeGroup (IsFreeGroup.Generators F))
    have eFree : X ≃* F := IsFreeGroup.mulEquiv F
    letI : Projective X :=
      Adjunction.map_projective GrpCat.adj (IsFreeGroup.Generators F) inferInstance
    letI : Projective F := Projective.of_iso eFree.toGrpIso inferInstance
    let i : GrpCat.of ↥R ⟶ F := GrpCat.ofHom R.subtype
    have hi : IsSplitMono i := by
      simpa [i] using hR
    letI : IsSplitMono i := hi
    have hR_retract : Retract (GrpCat.of ↥R) F :=
      { i := i
        r := retraction i
        retract := IsSplitMono.id i }
    have hR_projective : Projective (GrpCat.of ↥R) := hR_retract.projective
    exact Projective.of_iso e.symm.toGrpIso hR_projective

/-! ### Corollary_1_1_8 (from Items/Chap01) -/
universe u

open CategoryTheory

/-- Corollary 1-1-8: A group is projective exactly when it is free. -/
-- Proof sketch: use Proposition `1-1-7`, which identifies projective groups with retract
-- subgroups of free groups. A retract subgroup of a free group is free by Nielsen–Schreier, and a
-- free group is trivially a retract of itself via the top subgroup inclusion.
theorem projective_group_iff_free_group {G : Type u} [Group G] :
    Projective (GrpCat.of G) ↔ IsFreeGroup G := by
  rw [projective_group_iff_isomorphic_to_retract_of_free_group]
  constructor
  · rintro ⟨F, hF, R, e, _hR⟩
    let _ : IsFreeGroup F := hF
    let _ : IsFreeGroup R := subgroupIsFreeOfIsFree R
    exact IsFreeGroup.ofMulEquiv e.symm
  · intro hG
    exact ⟨GrpCat.of G, hG, ⊤, Subgroup.topEquiv.symm, Subgroup.top_subtype_isSplitMono⟩

/-! ### Proposition_1_1_9 (from Items/Chap01) -/
universe u

open scoped Cardinal

-- Layer triage:
-- `source-facing`: the image in `FreeGroup X` of the canonical generators `FreeGroup.of x`.
-- `core/canonical`: the owner basis `FreeGroupBasis.ofFreeGroup X`.
-- `bridge/view`: `FreeGroupBasis.reindexRange`, which reindexes that owner basis by its image
-- subset in the ambient group.
--
-- Domain sampling:
-- 1. `FreeGroupBasis.ofFreeGroup X` is the canonical owner basis on `FreeGroup X`.
-- 2. `FreeGroupBasis.reindexRange` is the chapter owner bridge from a basis to its image subset.
-- 3. `FreeGroupBasis.reindexRange_apply` is the companion pointwise lemma for that bridge.
--
-- Primitive vs. derived:
-- the only primitive data here are the canonical basis `FreeGroupBasis.ofFreeGroup X` and its
-- generator map `FreeGroup.of`. The basis indexed by the generator-image subset is derived
-- canonically by `reindexRange`, so this file does not introduce a parallel owner declaration.

variable (X : Type u)

/- Proposition 1-1-9: the canonical free group on `X` has the basis on the textbook
generator-image subset `Set.range (FreeGroup.of : X → FreeGroup X)`, obtained by reindexing the
standard basis `FreeGroupBasis.ofFreeGroup X` along its range. -/
#check
  (show FreeGroupBasis (Set.range (FreeGroup.of : X → FreeGroup X)) (FreeGroup X) from
    (FreeGroupBasis.ofFreeGroup X).reindexRange)

/-- The generator image subset in the free group on `X` has the same cardinality as `X`. -/
-- Proof sketch: apply `Cardinal.mk_range_eq` to the injective map `FreeGroup.of : X → FreeGroup X`.
theorem free_group_generator_image_cardinal_eq :
    #(Set.range (FreeGroup.of : X → FreeGroup X)) = #X := by
  simpa using Cardinal.mk_range_eq (FreeGroup.of : X → FreeGroup X) FreeGroup.of_injective

/-! ### Corollary_1_1_10 (from Items/Chap01) -/
universe u

/-- Corollary 1-1-10: For any set `X`, the canonical generators of `FreeGroup X` form a basis of
the free group on `X`. -/
theorem free_group_on_has_basis (X : Type u) :
    IsFreeGroupBasis (Set.range (FreeGroup.of : X → FreeGroup X)) :=
  (FreeGroupBasis.ofFreeGroup X).isFreeGroupBasis_range

/-! ### Proposition_1_1_11 (from Items/Chap01) -/
universe u

section

variable {G : Type u} [Group G]
variable {F : Type u} [Group F] {S : Set G} {X : Set F}

-- Layer triage:
-- `source-facing`: a subset `S ⊆ G`, a basis subset `X ⊆ F`, and a homomorphism `φ : G →* F`
-- that restricts to a bijection `S ≃ X`.
-- `core/canonical`: `FreeGroupBasis X F` and
-- `FreeGroupBasis {x : Subgroup.closure S | (x : G) ∈ S} (Subgroup.closure S)` are the owner
-- basis objects, while `IsFreeGroupBasis` is the chapter's subset-style bridge.
-- `bridge/view`: Proposition `1-1-11` transports the owner basis on `X` across the subtype
-- equivalence induced by `hφS`, then reads the result back on the generated subgroup via the
-- inclusion `{x : Subgroup.closure S | (x : G) ∈ S} → Subgroup.closure S`.
--
-- Domain sampling:
-- 1. `FreeGroupBasis.ofUniqueLift` from Definition `1-1-1` is the owner bridge from the textbook
--    subset universal property to a chosen basis object.
-- 2. `FreeGroupBasis.reindex` is the canonical owner transport along the subtype equivalence
--    induced by the bijection `S ≃ X`.
-- 3. `FreeGroupBasis.map` is the owner transport along the induced isomorphism between
--    `Subgroup.closure S` and `F`.
-- 4. `FreeGroupBasis.isFreeGroupBasis` turns the resulting owner basis back into the
--    subset-style conclusion stated below.
--
-- Primitive vs. derived:
-- the primitive source data are `φ`, the basis witness `hX`, and the bijection witness `hφS`.
-- The subgroup `Subgroup.closure S` and the subtype basis
-- `{x : Subgroup.closure S | (x : G) ∈ S}` are derived owner-side objects.

/-- Proposition 1-1-11: if a homomorphism sends `S` bijectively onto a free basis `X`, then the
subgroup of `G` generated by `S` is free with basis given by the corresponding subset of
`Subgroup.closure S`. -/
-- Proof sketch: convert `hX` to the owner basis `FreeGroupBasis X F` using
-- `FreeGroupBasis.ofUniqueLift`, reindex that basis along the subtype equivalence induced by
-- `hφS`, then transport it across the induced isomorphism from `Subgroup.closure S` to `F`. The
-- chapter bridge `FreeGroupBasis.isFreeGroupBasis` converts the resulting owner basis back to the
-- subset-style statement on `Subgroup.closure S`.
theorem closure_preimage_isFreeGroupBasis_of_bijOn
    (φ : G →* F) (hX : IsFreeGroupBasis X) (hφS : Set.BijOn φ S X) :
    IsFreeGroupBasis {x : Subgroup.closure S | (x : G) ∈ S} := sorry

/-- The subgroup generated by `S` is free whenever `S` maps bijectively onto a free basis of the
target group. -/
-- Proof sketch: apply `IsFreeGroupBasis.isFreeGroup` to
-- `closure_preimage_isFreeGroupBasis_of_bijOn`.
theorem closure_isFreeGroup_of_bijOn
    (φ : G →* F) (hX : IsFreeGroupBasis X) (hφS : Set.BijOn φ S X) :
    IsFreeGroup (Subgroup.closure S) :=
  IsFreeGroupBasis.isFreeGroup (closure_preimage_isFreeGroupBasis_of_bijOn φ hX hφS)

end

/-! ### Proposition_1_1_12 (from Items/Chap01) -/
universe u

open FreeGroup

section

variable {G : Type u} [Group G]

/-- Proposition 1-1-12, owner form: the subset of `Subgroup.closure X` cut out by `X` is a free
basis exactly when the canonical homomorphism from the free group on `X` into `G` is injective. -/
-- Layer triage:
-- `source-facing`: the reduced-word criterion stated below.
-- `core/canonical`: the induced homomorphism `FreeGroup.lift ((↑) : X → G)` and the owner basis
-- object on its range.
-- `bridge/view`: `FreeGroup.closure_eq_range` identifies that range with `Subgroup.closure X`,
-- while the subtype `{x : Subgroup.closure X | (x : G) ∈ X}` records the original generating set
-- inside the closure.
--
-- Domain sampling:
-- 1. `FreeGroup.closure_eq_range` is the canonical owner identification of the subgroup generated
--    by a subset with the range of the induced free-group homomorphism.
-- 2. `MonoidHom.ofInjective` is the canonical owner equivalence from an injective homomorphism to
--    its range.
-- 3. `FreeGroupBasis.ofFreeGroup` is the owner basis of a free group.
-- 4. `FreeGroupBasis.isFreeGroupBasis_range` is the chapter bridge from an owner basis to the
--    subset-style basis predicate.
--
-- Primitive vs. derived:
-- the primitive source data are only the subset `X` and the induced homomorphism
-- `FreeGroup.lift ((↑) : X → G)`. The basis on `Subgroup.closure X` and the reduced-word
-- criterion are derived API.
theorem closure_preimage_isFreeGroupBasis_iff_injective_lift
    (X : Set G) :
    IsFreeGroupBasis {x : Subgroup.closure X | (x : G) ∈ X} ↔
      Function.Injective (FreeGroup.lift (Subtype.val : X → G)) := by
  let φ : FreeGroup X →* G := FreeGroup.lift (Subtype.val : X → G)
  have hφ_range : φ.range = Subgroup.closure X := by
    simpa [φ] using (FreeGroup.closure_eq_range X).symm
  constructor
  · intro hBasis
    let basis :
        FreeGroupBasis {x : Subgroup.closure X | (x : G) ∈ X} (Subgroup.closure X) :=
      FreeGroupBasis.ofUniqueLift {x : Subgroup.closure X | (x : G) ∈ X} Subtype.val hBasis
    let e : {x : Subgroup.closure X | (x : G) ∈ X} ≃ X :=
      { toFun := fun x ↦ ⟨x.1.1, x.2⟩
        invFun := fun x ↦ ⟨⟨x.1, Subgroup.subset_closure x.2⟩, x.2⟩
        left_inv := fun x ↦ by
          cases x
          rfl
        right_inv := fun x ↦ rfl }
    let ψ : Subgroup.closure X →* FreeGroup X :=
      basis.lift (FreeGroup.of ∘ e)
    have hcomp :
        ψ.comp (φ.codRestrict (Subgroup.closure X) fun x ↦ hφ_range ▸ ⟨x, rfl⟩) =
          MonoidHom.id (FreeGroup X) := by
      apply FreeGroup.ext_hom
      intro x
      have hψ :=
        congr_fun (basis.lift.symm_apply_apply (FreeGroup.of ∘ e))
          ⟨⟨x.1, Subgroup.subset_closure x.property⟩, x.property⟩
      simpa [ψ, e]
    intro x y hxy
    have hxy' :
        φ.codRestrict (Subgroup.closure X) (fun z ↦ hφ_range ▸ ⟨z, rfl⟩) x =
          φ.codRestrict (Subgroup.closure X) (fun z ↦ hφ_range ▸ ⟨z, rfl⟩) y :=
      Subtype.ext hxy
    have hx :
        ψ (φ.codRestrict (Subgroup.closure X) (fun z ↦ hφ_range ▸ ⟨z, rfl⟩) x) = x := by
      simpa [MonoidHom.comp_apply] using
        congrArg (fun f : FreeGroup X →* FreeGroup X ↦ f x) hcomp
    have hy :
        ψ (φ.codRestrict (Subgroup.closure X) (fun z ↦ hφ_range ▸ ⟨z, rfl⟩) y) = y := by
      simpa [MonoidHom.comp_apply] using
        congrArg (fun f : FreeGroup X →* FreeGroup X ↦ f y) hcomp
    calc
      x = ψ (φ.codRestrict (Subgroup.closure X) (fun z ↦ hφ_range ▸ ⟨z, rfl⟩) x) := hx.symm
      _ = ψ (φ.codRestrict (Subgroup.closure X) (fun z ↦ hφ_range ▸ ⟨z, rfl⟩) y) := by
        simpa using congrArg ψ hxy'
      _ = y := hy
  · intro hφ
    let basis : FreeGroupBasis X (Subgroup.closure X) :=
      (FreeGroupBasis.ofFreeGroup X).map
        ((MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hφ_range))
    have hrange :
        Set.range basis = {x : Subgroup.closure X | (x : G) ∈ X} := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        simp [basis, MonoidHom.ofInjective_apply]
      · intro hy
        refine ⟨⟨y.1, hy⟩, ?_⟩
        ext
        simp [basis, MonoidHom.ofInjective_apply]
    rw [← hrange]
    exact (FreeGroupBasis.isFreeGroupBasis_range basis : IsFreeGroupBasis (Set.range basis))

/-- Proposition 1-1-12: A subset `X` is a basis for the subgroup it generates if and only if every
nonempty reduced word in `X^{±1}` has nontrivial product.

In this reduced-word bridge formulation, the textbook disjointness hypothesis `X ∩ X⁻¹ = ∅` is
redundant: it is already forced by the nontrivial-product condition. -/
-- Proof sketch: combine the owner criterion
-- `closure_preimage_isFreeGroupBasis_iff_injective_lift` with the free-group normal form theorem.
-- Injectivity rules out a nonempty reduced word evaluating to `1`, and conversely any kernel
-- element has a canonical reduced representative given by `toWord`.
theorem closure_preimage_isFreeGroupBasis_iff_no_trivial_reduced_word
    (X : Set G) :
    IsFreeGroupBasis {x : Subgroup.closure X | (x : G) ∈ X} ↔
      ∀ w : List (X × Bool), w ≠ [] →
        IsReduced w →
        lift Subtype.val (mk w) ≠ 1 := by
  classical
  rw [closure_preimage_isFreeGroupBasis_iff_injective_lift]
  constructor
  · intro hφ w hw hred htriv
    have hmk : (mk w : FreeGroup X) = 1 := hφ (by simpa using htriv)
    have hword : (mk w : FreeGroup X).toWord = [] := by
      simp [hmk]
    exact hw <| by simpa [toWord_mk, hred.reduce_eq] using hword
  · intro hφ x y hxy
    by_cases hword : (x * y⁻¹).toWord = []
    · exact (mul_inv_eq_one.mp <| (toWord_eq_nil_iff.mp hword))
    · have htriv : lift Subtype.val (x * y⁻¹) = 1 := by
        rw [MonoidHom.map_mul, MonoidHom.map_inv, hxy, mul_inv_cancel]
      have :=
        hφ (x * y⁻¹).toWord hword isReduced_toWord
          (by simpa [mk_toWord] using htriv)
      exact False.elim this

end
