import Mathlib
import Mathlib.GroupTheory.SemidirectProduct

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_1_10_1 (from Items/Chap01) -/
noncomputable section

universe u

open FreeMonoid

variable {n : ℕ}
variable {F : Type u} [Group F]

/-
Layer triage:
- `source-facing`: the Magnus representation attached to a chosen finite free basis.
- `core/canonical`: `FreeGroupBasis.lift` on the free-group side and `AddMonoid.End` for the
  left-regular noncommutative target action.
- `bridge/view`: the classical noncommutative formal power series algebra is realized faithfully by
  its left action on word-indexed integer series; the generator `X i` acts by prefix shift.

Domain sampling:
1. `FreeGroupBasis.lift` is the owner abstraction for defining group homomorphisms out of a free
   group with chosen basis.
2. `AddMonoid.End` is mathlib's canonical owner for a noncommutative ring of additive
   endomorphisms.
3. `FreeMonoid (Fin n)` is the canonical owner for noncommutative words on `n` generators.
4. `AddMonoid.End.applyFaithfulSMul` is the owner action showing endomorphisms are determined by
   their action on the underlying series module.

Primitive vs. derived:
the primitive target data are the word-indexed integer series on the list model of
`FreeMonoid (Fin n)` and the prefix-shift operators giving the noncommuting variables. The Magnus
homomorphism is the derived free-group map obtained from `FreeGroupBasis.lift`, so there is no
separate wrapper around the chosen basis or around generator images. -/

private abbrev foxMagnusModule (n : ℕ) := FreeMonoid (Fin n) → ℤ

/-- The left-regular Magnus target on `n` generators, realizing the noncommutative formal power
series algebra by its action on integer-valued series indexed by words in `FreeMonoid (Fin n)`. -/
abbrev foxMagnusTarget (n : ℕ) := AddMonoid.End (foxMagnusModule n)

private def foxMagnusVar (i : Fin n) : foxMagnusTarget n where
  toFun f w :=
    match w.toList with
    | [] => 0
    | j :: l => if j = i then f (ofList l) else 0
  map_zero' := by
    funext w
    cases h : w.toList with
    | nil => simp
    | cons j l =>
        by_cases hji : j = i
        · simp [hji]
        · simp [hji]
  map_add' f g := by
    funext w
    cases h : w.toList with
    | nil => simp [h]
    | cons j l =>
        by_cases hji : j = i
        · simp [h, hji, Pi.add_apply]
        · simp [h, hji, Pi.add_apply]

@[simp] private theorem foxMagnusVar_apply_one (i : Fin n) (f : foxMagnusModule n) :
    foxMagnusVar i f 1 = 0 := by
  rfl

@[simp] private theorem foxMagnusVar_apply_mul_self
    (i : Fin n) (f : foxMagnusModule n) (w : FreeMonoid (Fin n)) :
    foxMagnusVar i f (of i * w) = f w := by
  change
    (match (of i * w).toList with
      | [] => 0
      | j :: l => if j = i then f (ofList l) else 0) = f w
  simp

@[simp] private theorem foxMagnusVar_apply_mul_ne
    (i j : Fin n) (f : foxMagnusModule n) (w : FreeMonoid (Fin n)) (h : j ≠ i) :
    foxMagnusVar i f (of j * w) = 0 := by
  change
    (match (of j * w).toList with
      | [] => 0
      | k :: l => if k = i then f (ofList l) else 0) = 0
  simp [h]

private def oneAddFoxMagnusVarInvAux (i : Fin n) (f : foxMagnusModule n) :
    List (Fin n) → ℤ
  | [] => f 1
  | j :: l => f (ofList (j :: l)) - if j = i then oneAddFoxMagnusVarInvAux i f l else 0

private theorem oneAddFoxMagnusVarInvAux_zero (i : Fin n) :
    oneAddFoxMagnusVarInvAux i (0 : foxMagnusModule n) = 0 := by
  funext l
  induction l with
  | nil => simp [oneAddFoxMagnusVarInvAux]
  | cons j l ih =>
      by_cases h : j = i
      · simp [oneAddFoxMagnusVarInvAux, h, ih]
      · simp [oneAddFoxMagnusVarInvAux, h]

private theorem oneAddFoxMagnusVarInvAux_add (i : Fin n) (f g : foxMagnusModule n) :
    oneAddFoxMagnusVarInvAux i (f + g) =
      oneAddFoxMagnusVarInvAux i f + oneAddFoxMagnusVarInvAux i g := by
  funext l
  induction l with
  | nil => simp [oneAddFoxMagnusVarInvAux]
  | cons j l ih =>
      by_cases h : j = i
      · simp [oneAddFoxMagnusVarInvAux, h, ih, sub_eq_add_neg]
        abel
      · simp [oneAddFoxMagnusVarInvAux, h]

private def oneAddFoxMagnusVarInv (i : Fin n) : foxMagnusTarget n where
  toFun f w := oneAddFoxMagnusVarInvAux i f w.toList
  map_zero' := by
    funext w
    simpa using congr_fun (oneAddFoxMagnusVarInvAux_zero i) w.toList
  map_add' f g := by
    funext w
    simpa using congr_fun (oneAddFoxMagnusVarInvAux_add i f g) w.toList

@[simp] private theorem oneAddFoxMagnusVarInv_apply_ofList
    (i : Fin n) (f : foxMagnusModule n) (l : List (Fin n)) :
    oneAddFoxMagnusVarInv i f (ofList l) = oneAddFoxMagnusVarInvAux i f l := by
  rfl

private theorem one_add_foxMagnusVar_apply_inv_ofList (i : Fin n) (f : foxMagnusModule n) :
    ∀ l : List (Fin n),
      (1 + foxMagnusVar i) (oneAddFoxMagnusVarInv i f) (ofList l) = f (ofList l)
  | [] => by
      change oneAddFoxMagnusVarInvAux i f [] + foxMagnusVar i (oneAddFoxMagnusVarInv i f) 1 = f 1
      simp [oneAddFoxMagnusVarInvAux]
  | j :: l => by
      by_cases h : j = i
      · subst j
        change
          oneAddFoxMagnusVarInvAux i f (i :: l) +
              foxMagnusVar i (oneAddFoxMagnusVarInv i f) (of i * ofList l) =
            f (of i * ofList l)
        rw [foxMagnusVar_apply_mul_self]
        simp [oneAddFoxMagnusVarInvAux, sub_eq_add_neg]
      · change
          oneAddFoxMagnusVarInvAux i f (j :: l) +
              foxMagnusVar i (oneAddFoxMagnusVarInv i f) (of j * ofList l) =
            f (of j * ofList l)
        rw [foxMagnusVar_apply_mul_ne _ _ _ _ h]
        simp [oneAddFoxMagnusVarInvAux, h]

private theorem oneAddFoxMagnusVarInv_apply_one_add_ofList (i : Fin n) (f : foxMagnusModule n) :
    ∀ l : List (Fin n),
      oneAddFoxMagnusVarInv i ((1 + foxMagnusVar i) f) (ofList l) = f (ofList l)
  | [] => by
      change ((1 + foxMagnusVar i) f) 1 = f 1
      change f 1 + foxMagnusVar i f 1 = f 1
      simp
  | j :: l => by
      by_cases h : j = i
      · subst j
        change oneAddFoxMagnusVarInvAux i ((1 + foxMagnusVar i) f) (i :: l) = f (of i * ofList l)
        rw [oneAddFoxMagnusVarInvAux, if_pos rfl]
        rw [show oneAddFoxMagnusVarInvAux i ((1 + foxMagnusVar i) f) l = f (ofList l) by
          simpa using oneAddFoxMagnusVarInv_apply_one_add_ofList i f l]
        change
          f (of i * ofList l) + foxMagnusVar i f (of i * ofList l) - f (ofList l) =
            f (of i * ofList l)
        simp [sub_eq_add_neg]
      · change oneAddFoxMagnusVarInvAux i ((1 + foxMagnusVar i) f) (j :: l) = f (of j * ofList l)
        rw [oneAddFoxMagnusVarInvAux, if_neg h, ofList_cons]
        simp
        change f (of j * ofList l) + foxMagnusVar i f (of j * ofList l) = f (of j * ofList l)
        simp [h]

/-- The source-facing Magnus generator image `1 + X i` in the left-regular Magnus target. -/
def foxMagnusGeneratorUnit (i : Fin n) : Units (foxMagnusTarget n) where
  val := 1 + foxMagnusVar i
  inv := oneAddFoxMagnusVarInv i
  val_inv := by
    apply AddMonoidHom.ext
    intro f
    funext w
    change (1 + foxMagnusVar i) (oneAddFoxMagnusVarInv i f) w = f w
    rw [← ofList_toList w]
    simpa using one_add_foxMagnusVar_apply_inv_ofList i f w.toList
  inv_val := by
    apply AddMonoidHom.ext
    intro f
    funext w
    change oneAddFoxMagnusVarInv i ((1 + foxMagnusVar i) f) w = f w
    rw [← ofList_toList w]
    simpa using oneAddFoxMagnusVarInv_apply_one_add_ofList i f w.toList

/-- The Magnus homomorphism sending each basis element of a rank-`n` free group to the unit
`1 + X i`, realized here by the left-prefix action of the noncommutative variable `X i` on
word-indexed integer series. -/
def foxMagnusHom (basis : FreeGroupBasis (Fin n) F) : F →* Units (foxMagnusTarget n) :=
  basis.lift foxMagnusGeneratorUnit

/-- The Magnus homomorphism sends the chosen basis element `basis i` to the unit `1 + X i`. -/
@[simp] theorem foxMagnusHom_apply_basis (basis : FreeGroupBasis (Fin n) F) (i : Fin n) :
    foxMagnusHom basis (basis i) = foxMagnusGeneratorUnit i := by
  simp [foxMagnusHom]

-- Proof sketch: transport along `basis.repr : F ≃* FreeGroup (Fin n)` to the standard free group,
-- then apply the classical squarefree-highest-word argument for the noncommutative Magnus action on
-- formal series. The noncommutative target used above is the left-regular realization of that
-- completed Magnus algebra, so the usual argument applies unchanged.
/-- Proposition 1-10-1: if `F` is free on the basis `basis : FreeGroupBasis (Fin n) F`, then the
Magnus map sending `basis i` to `1 + X i` in the noncommutative formal power series Magnus target
is injective, hence identifies `F` with a subgroup of its unit group. -/
theorem foxMagnusHom_injective (basis : FreeGroupBasis (Fin n) F) :
    Function.Injective (foxMagnusHom basis) := sorry

/-! ### Proposition_1_10_2 (from Items/Chap01) -/
universe u

section

open QuotientGroup

variable {F : Type u} [Group F] [IsFreeGroup F]

/-- Proposition 1-10-2: the intersection of the terms of the descending central series of a free
group is trivial. In mathlib's indexing this is the infimum of `lowerCentralSeries F m`, since
`lowerCentralSeries F 0 = F` and `lowerCentralSeries F (m + 1) = ⁅lowerCentralSeries F m, ⊤⁆`.

The textbook finite-rank hypothesis and the choice of a basis are redundant for this statement, so
the theorem is stated directly under the owner assumption `[IsFreeGroup F]`. -/
-- Layer triage:
-- `source-facing`: the textbook descending central series `F₁ = F`, `F_{m + 1} = [F_m, F]` and
-- the assertion that its intersection is trivial.
-- `core/canonical`: mathlib's owner sequence `lowerCentralSeries F`.
-- `bridge/view`: Proposition `1-4-10` gives the owner separation theorem saying that every
-- nontrivial element of a free group survives in some lower-central-series quotient.
-- Domain sampling:
-- 1. `lowerCentralSeries F` is the canonical descending central series in mathlib.
-- 2. `exists_lowerCentralSeries_quotient_separating_nonconjugate` is the chapter's owner
--    separation theorem for lower-central quotients of a free group.
-- 3. `QuotientGroup.eq_one_iff` is the canonical membership test for the quotient map
--    `mk' (lowerCentralSeries F m)`.
-- 4. `Subgroup.eq_bot_iff_forall` and `Subgroup.mem_iInf` are the owner lattice lemmas for
--    converting subgroup infima into pointwise membership statements.
-- Primitive vs. derived:
-- the primitive datum is the free-group owner instance `[IsFreeGroup F]`; the subgroup
-- intersection `⨅ m, lowerCentralSeries F m` is the canonical derived owner encoding the textbook
-- intersection `⋂_m F_m`.
-- Proof sketch: let `g` lie in every `lowerCentralSeries F m`. If `g ≠ 1`, then `g` is not
-- conjugate to `1`, so Proposition `1-4-10` gives an index `m` such that the image of `g` in
-- `F ⧸ lowerCentralSeries F m` is not conjugate to `1`. But membership of `g` in
-- `lowerCentralSeries F m` forces that image to be `1`, contradiction.
theorem iInf_lowerCentralSeries_eq_bot_of_isFreeGroup :
    (⨅ m : ℕ, lowerCentralSeries F m) = (⊥ : Subgroup F) := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  by_contra hg1
  obtain ⟨m, hm⟩ :=
    exists_lowerCentralSeries_quotient_separating_nonconjugate g 1 <|
      by simpa [isConj_one_left] using hg1
  have hgq : (mk' (lowerCentralSeries F m) g : F ⧸ lowerCentralSeries F m) = 1 :=
    (QuotientGroup.eq_one_iff g).mpr <| Subgroup.mem_iInf.mp hg m
  exact hm <| by
    simpa using isConj_one_left.mpr hgq

end

/-! ### Proposition_1_10_3 (from Items/Chap01) -/
universe u

noncomputable section

section

variable {G : Type u} [Group G]

/-- The augmentation ideal of the integral group ring of `G`. -/
private abbrev groupRingAugmentationIdeal (G : Type u) [Group G] :
    Ideal (MonoidAlgebra ℤ G) :=
  RingHom.ker (Bialgebra.counitAlgHom ℤ (MonoidAlgebra ℤ G))

/-- The augmentation ideal of the noncommutative free algebra on `m` generators. -/
private abbrev freeAlgebraAugmentationIdeal (m : ℕ) : Ideal (FreeAlgebra ℤ (Fin m)) :=
  RingHom.ker (FreeAlgebra.algebraMapInv : FreeAlgebra ℤ (Fin m) →ₐ[ℤ] ℤ)

/-- The truncated Magnus algebra on `m` generators modulo the `n`th augmentation-ideal power. -/
private abbrev truncatedFoxMagnusAlgebra (m n : ℕ) :=
  FreeAlgebra ℤ (Fin m) ⧸ freeAlgebraAugmentationIdeal m ^ n

private def dimensionSubgroupToUnits (G : Type u) [Group G] (n : ℕ) :
    G →* Units ((MonoidAlgebra ℤ G) ⧸ groupRingAugmentationIdeal G ^ n) :=
  ((Ideal.Quotient.mk (groupRingAugmentationIdeal G ^ n)).toMonoidHom.comp
    (MonoidAlgebra.of ℤ G)).toHomUnits

/-- The section-10 dimension subgroup `D_n(G)`, defined by the `n`-th power of the augmentation
ideal of the integral group ring of `G`, equivalently the kernel of the canonical quotient
representation into the units of `ℤ[G] / I^n`. -/
def dimensionSubgroup (G : Type u) [Group G] (n : ℕ) : Subgroup G :=
  (dimensionSubgroupToUnits G n).ker

/-- Membership in `D_n(G)` is the usual augmentation-ideal condition
`MonoidAlgebra.of ℤ G g - 1 ∈ I^n`. -/
@[simp] theorem mem_dimensionSubgroup_iff {n : ℕ} {g : G} :
    g ∈ dimensionSubgroup G n ↔
      MonoidAlgebra.of ℤ G g - 1 ∈ groupRingAugmentationIdeal G ^ n := by
  rw [dimensionSubgroup, MonoidHom.mem_ker, ← Units.val_inj]
  simp [dimensionSubgroupToUnits, Ideal.Quotient.mk_eq_one_iff_sub_mem]

/-- The section-10 Magnus/Fox filtration `L_n(G)`, realized as the intersection of the kernels of
all representations of `G` into the unit groups of the truncated noncommutative Magnus algebras
`ℤ⟨X₁, …, X_m⟩ / I^n`, where `I` is the augmentation ideal. -/
def foxMagnusSeries (G : Type u) [Group G] (n : ℕ) : Subgroup G :=
  ⨅ m : ℕ, ⨅ ρ : G →* Units (truncatedFoxMagnusAlgebra m n), ρ.ker

-- Layer triage:
-- `source-facing`: the textbook filtrations `G_n`, `L_n(G)`, and `D_n(G)`.
-- `core/canonical`: mathlib's owner lower central series `lowerCentralSeries G`, the augmentation
-- ideals of `MonoidAlgebra ℤ G` and `FreeAlgebra ℤ (Fin m)`, together with quotient rings by
-- powers of those ideals and their unit groups.
-- `bridge/view`: the textbook lower central term `G_n` starts with `G_1 = G`, whereas mathlib
-- uses `lowerCentralSeries G 0 = G`; the theorem below therefore uses the Lean index `n` to encode
-- the textbook index `n + 1`.
-- Domain sampling:
-- 1. `lowerCentralSeries G` is the canonical descending central series in mathlib.
-- 2. `foxMagnusHom` from Proposition `1-10-1` is the chapter's earlier Magnus owner on a chosen
--    free basis, so this file should only add the source-facing all-representations filtration and
--    not a second basis-packaged Magnus map.
-- 3. `foxTriangularRepresentation` from Definition `1-10-7` is the project owner for the Fox
--    representation viewpoint, confirming that the representation targets here are derived from the
--    augmentation owners rather than primitive public data.
-- 4. `Bialgebra.counitAlgHom` and `FreeAlgebra.algebraMapInv`, together with `RingHom.ker`, are
--    the canonical augmentation owners on the integral group ring and the noncommutative free
--    algebra.
-- Primitive vs. derived:
-- the primitive section-10 data are the augmentation filtrations on the integral group ring and on
-- the noncommutative free algebra; the truncated Magnus targets and the quotient-to-units map
-- defining `dimensionSubgroup G n` are derived quotient owners, and the subgroup
-- `foxMagnusSeries G n` is the derived intersection of the resulting representation kernels on `G`.

/- Proposition 1-10-3: after reindexing the lower central series to match the textbook convention
`G_1 = G`, every group satisfies
`G_{n + 1} ⊆ L_{n + 1}(G) ⊆ D_{n + 1}(G)`. In Lean this is
`lowerCentralSeries G n ≤ foxMagnusSeries G (n + 1)` and
`foxMagnusSeries G (n + 1) ≤ dimensionSubgroup G (n + 1)`.

The atomic inclusions are exposed first as the reusable public API, and the original chained
statement is then recovered as a bundled companion theorem. -/
-- Proof sketch: the first inclusion comes from the standard fact that, after quotienting the
-- target noncommutative Magnus algebra by the `(n + 1)`st augmentation power, every such reduced
-- representation factors through an `n`-step nilpotent quotient, so it kills the `(n + 1)`st
-- textbook lower-central term. For the second inclusion, apply the Magnus/Fox formula `(*)` to
-- compare the augmentation filtration on those truncated Magnus representations with powers of the
-- augmentation ideal in the integral group ring.
/-- Proposition 1-10-3, first inclusion: the `(n + 1)`st textbook lower-central term lies in the
Magnus/Fox filtration term `L_{n + 1}(G)`. -/
theorem lowerCentralSeries_le_foxMagnusSeries (n : ℕ) :
    lowerCentralSeries G n ≤ foxMagnusSeries G (n + 1) := sorry

/-- Proposition 1-10-3, second inclusion: the Magnus/Fox filtration term `L_{n + 1}(G)` lies in
the section-10 dimension subgroup `D_{n + 1}(G)`. -/
theorem foxMagnusSeries_le_dimensionSubgroup (n : ℕ) :
    foxMagnusSeries G (n + 1) ≤ dimensionSubgroup G (n + 1) := sorry

/-- Proposition 1-10-3 in its original chained form. -/
theorem lowerCentralSeries_le_foxMagnusSeries_le_dimensionSubgroup (n : ℕ) :
    lowerCentralSeries G n ≤ foxMagnusSeries G (n + 1) ∧
      foxMagnusSeries G (n + 1) ≤ dimensionSubgroup G (n + 1) :=
  ⟨lowerCentralSeries_le_foxMagnusSeries n, foxMagnusSeries_le_dimensionSubgroup n⟩

end

/-! ### Definition_1_10_4 (from Items/Chap01) -/
/-- The integral group ring of the free group on `X`. -/
abbrev FreeGroupRing (X : Type u) := MonoidAlgebra ℤ (FreeGroup X)

variable {X : Type u}

section

local notation "R" => FreeGroupRing X
local notation "ε" => Bialgebra.counitAlgHom ℤ R

/-- Definition 1-10-4: a Fox derivation of the integral group ring of the free group on `X` is a
`ℤ`-linear endomorphism satisfying the Fox product rule
`D (u * v) = ε(v) • D u + u * D v` for all `u` and `v`, where `ε` is the augmentation morphism of
the group ring. This rule already forces `D 1 = 0`; see `IsFoxDerivation.map_one_eq_zero`. -/
def IsFoxDerivation (D : Module.End ℤ (FreeGroupRing X)) : Prop :=
  ∀ u v : R, D (u * v) = ε v • D u + u * D v

namespace IsFoxDerivation

/-- A Fox derivation annihilates the multiplicative unit. -/
theorem map_one_eq_zero {D : Module.End ℤ (FreeGroupRing X)} (hD : IsFoxDerivation D) :
    D 1 = 0 :=
  by
    have h : D 1 + D 1 = D 1 + 0 := by
      simpa [add_comm] using (hD 1 1).symm
    exact add_left_cancel h

end IsFoxDerivation

end

/-! ### Definition_1_10_5 (from Items/Chap01) -/
noncomputable section

universe u

variable {X : Type u}

/- Definition 1-10-5 lies in Fox calculus for free groups.

Layer triage:
- `source-facing`: the coordinate Fox derivative with respect to a generator `x`.
- `core/canonical`: the chapter owner map `foxTriangularRepresentation X` and its coordinate
  `foxUniversalDifferential`.
- `bridge/view`: the explicit signed-letter formula `foxLetterDerivative` and the word-sum formula
  `foxDerivative_mk_eq_sum`.

Domain sampling:
1. `FreeGroup.lift` is mathlib's owner constructor for multiplicative maps out of a free group.
2. `FreeGroup.lift_mk` is the canonical word-level formula for such owner maps on displayed words.
3. `foxTriangularRepresentation` is the chapter owner Fox-calculus representation built from that
   constructor, and `foxUniversalDifferential` is its canonical differential coordinate.

Primitive vs. derived:
the primitive chapter owner data is `foxUniversalDifferential`; the source-facing coordinate is
its ordinary evaluation at `x`, while the explicit signed-letter and displayed-word formulas on
`SignedLetter X` and `List (SignedLetter X)` are derived API. This file should therefore avoid
owning a second public Fox-derivative owner parallel to that canonical differential.
-/

section

local notation "R" => FreeGroupRing X
local instance : DecidableEq X := Classical.decEq X

/-- The Fox derivative of a single signed letter with respect to the generator `x`. -/
def foxLetterDerivative (x : X) : SignedLetter X → R :=
  fun
  | (y, true) => if y = x then 1 else 0
  | (y, false) => if y = x then -MonoidAlgebra.of ℤ (FreeGroup X) ((FreeGroup.of y)⁻¹) else 0

/-- Definition 1-10-5: the Fox derivative of `w` with respect to the generator `x`, defined as the
`x`-coordinate of the universal Fox differential from Proposition `1-10-6`. -/
abbrev foxDerivative (x : X) (w : FreeGroup X) : R :=
  foxUniversalDifferential w x

/- Definition 1-10-5 is the coordinate Fox derivative `∂w / ∂x`. -/
#check foxDerivative

-- Proof sketch: induct on the list `word`; the empty word contributes `0`, and the inductive step
-- pulls out the first-letter term and multiplies the inductive sum for the suffix by the prefix
-- monomial represented by that first letter.
/-- The universal Fox differential of a displayed word is the sum of the derivatives of its
letters weighted by their preceding prefixes. -/
theorem foxUniversalDifferential_mk_eq_sum
    (word : List (SignedLetter X)) (x : X) :
    foxUniversalDifferential (FreeGroup.mk word) x =
      ∑ j : Fin word.length,
        MonoidAlgebra.of ℤ (FreeGroup X) (FreeGroup.mk (word.take j.val)) *
          foxLetterDerivative x (word.get j) := sorry

/-- The Fox derivative of a displayed word is the corresponding coordinate form of
`foxUniversalDifferential_mk_eq_sum`. -/
theorem foxDerivative_mk_eq_sum (word : List (SignedLetter X)) (x : X) :
    foxDerivative x (FreeGroup.mk word) =
      ∑ j : Fin word.length,
        MonoidAlgebra.of ℤ (FreeGroup X) (FreeGroup.mk (word.take j.val)) *
          foxLetterDerivative x (word.get j) := by
  simpa [foxDerivative] using foxUniversalDifferential_mk_eq_sum word x

end

/-! ### Proposition_1_10_6 (from Items/Chap01) -/
noncomputable section

universe u

/- Proposition 1-10-6 lies in Fox calculus for free groups.

Layer triage:
- `source-facing`: the faithful Fox triangular representation of `FreeGroup X`.
- `core/canonical`: `MonoidAlgebra.comapDistribMulActionSelf`, the induced `Finsupp` action on the
  Fox module, `FreeGroup.lift`, and `SemidirectProduct.rightHom`.
- `bridge/view`: the universal differential as the left coordinate of the triangular map, together
  with the pair formula `(d w, w)`.

Domain sampling:
1. `MonoidAlgebra.comapDistribMulActionSelf` is the mathlib owner for left multiplication of
   `FreeGroup X` on its integral group ring.
2. `X →₀ FreeGroupRing X` inherits the coefficientwise owner action from that ring action, so the
   previous hand-written `smul` helper was duplicate surface.
3. `FreeGroup.lift` is the owner abstraction for defining the representation from its generator
   values.
4. `SemidirectProduct.rightHom` is the owner projection detecting faithfulness.

Primitive vs. derived:
the primitive public data are the Fox module, the semidirect-product target, and the triangular
representation; the universal differential and the pair description are derived coordinate API.
-/

instance (X : Type u) : DistribMulAction (FreeGroup X) (FreeGroupRing X) :=
  MonoidAlgebra.comapDistribMulActionSelf

/-- The free left `ℤ[FreeGroup X]`-module on the formal symbols `dx`, modeled as finitely
supported coefficient families. -/
abbrev foxDifferentialModule (X : Type u) := X →₀ FreeGroupRing X

instance foxDifferentialModuleMulDistribMulAction (X : Type u) :
    MulDistribMulAction (FreeGroup X) (Multiplicative (foxDifferentialModule X)) where
  smul g d := Additive.toMul (g • d.toAdd)
  one_smul d := by
    cases d with
    | ofAdd a =>
        change Multiplicative.ofAdd ((1 : FreeGroup X) • a) = Multiplicative.ofAdd a
        exact congrArg Multiplicative.ofAdd (by simp : (1 : FreeGroup X) • a = a)
  mul_smul g h d := by
    cases d with
    | ofAdd a =>
        change Multiplicative.ofAdd ((g * h) • a) = Multiplicative.ofAdd (g • (h • a))
        exact congrArg Multiplicative.ofAdd (by simp [mul_smul] : (g * h) • a = g • (h • a))
  smul_mul g d e := by
    cases d with
    | ofAdd a =>
        cases e with
        | ofAdd b =>
            change Multiplicative.ofAdd (g • (a + b)) = Multiplicative.ofAdd (g • a + g • b)
            exact congrArg Multiplicative.ofAdd
              (by simp [smul_add] : g • (a + b) = g • a + g • b)
  smul_one g := by
    change Multiplicative.ofAdd (g • (0 : foxDifferentialModule X)) = Multiplicative.ofAdd 0
    exact congrArg Multiplicative.ofAdd (by simp : g • (0 : foxDifferentialModule X) = 0)

/-- The canonical semidirect-product target for the Fox triangular representation, corresponding to
upper triangular matrices whose upper-right entry lies in the Fox differential module. -/
abbrev foxTriangularRepresentationTarget (X : Type u) :=
  Multiplicative (foxDifferentialModule X) ⋊[
    MulDistribMulAction.toMulAut (FreeGroup X) (Multiplicative (foxDifferentialModule X))]
    FreeGroup X

/-- The canonical Fox triangular representation of `FreeGroup X`, written in semidirect-product
form rather than as a literal upper triangular matrix group. -/
def foxTriangularRepresentation (X : Type u) :
    FreeGroup X →* foxTriangularRepresentationTarget X :=
  FreeGroup.lift fun x ↦
    (⟨Additive.toMul (Finsupp.single x (1 : FreeGroupRing X)), FreeGroup.of x⟩ :
      foxTriangularRepresentationTarget X)

/-- The universal Fox differential `d : FreeGroup X → foxDifferentialModule X`, extracted as the
upper-right coordinate of the triangular representation. -/
def foxUniversalDifferential {X : Type u} (w : FreeGroup X) : foxDifferentialModule X :=
  (foxTriangularRepresentation X w).left.toAdd

private theorem foxTriangularRepresentation_right {X : Type u} (w : FreeGroup X) :
    SemidirectProduct.rightHom (foxTriangularRepresentation X w) = w := by
  change ((SemidirectProduct.rightHom.comp (foxTriangularRepresentation X)) w) = w
  have hcomp : SemidirectProduct.rightHom.comp (foxTriangularRepresentation X) = MonoidHom.id _ := by
    ext x
    simp [foxTriangularRepresentation]
  simp [hcomp]

/-- The semidirect-product form of the Fox representation is the pair `(d w, w)`. -/
theorem foxTriangularRepresentation_eq_pair {X : Type u} (w : FreeGroup X) :
    foxTriangularRepresentation X w =
      (⟨Additive.toMul (foxUniversalDifferential w), w⟩ :
        foxTriangularRepresentationTarget X) := by
  ext
  · rfl
  · exact foxTriangularRepresentation_right w

/-- Proposition 1-10-6: the Fox differential determines a well-defined faithful triangular
representation of `FreeGroup X`; in Lean this is packaged as `foxTriangularRepresentation`. -/
theorem foxTriangularRepresentation_injective (X : Type u) :
    Function.Injective (foxTriangularRepresentation X) := by
  intro u v h
  have h' := congrArg SemidirectProduct.rightHom h
  rw [foxTriangularRepresentation_right, foxTriangularRepresentation_right] at h'
  exact h'

/-! ### Definition_1_10_7 (from Items/Chap01) -/
universe u

noncomputable section

variable {X : Type u}

/- Definition 1-10-7 lies in Fox calculus for free groups.

Layer triage:
- `source-facing`: the Fox differential `dw` and the second Magnus representation of `FreeGroup X`.
- `core/canonical`: `foxDifferentialModule X`, `foxUniversalDifferential`,
  `foxTriangularRepresentationTarget X`, and `foxTriangularRepresentation`.
- `bridge/view`: the coordinate word formula from Definition `1-10-5`, expressing
  `foxUniversalDifferential (FreeGroup.mk word) x` as the signed-letter sum over the displayed
  word.

Domain sampling:
1. `foxDifferentialModule` is the owner module for Fox differentials.
2. `foxUniversalDifferential` is its canonical differential coordinate.
3. `foxTriangularRepresentation` is the canonical triangular owner map.
4. `foxTriangularRepresentation_eq_pair` and `foxTriangularRepresentation_injective` provide the
   textbook coordinate description and faithfulness.

Primitive vs. derived:
the primitive owner data is the semidirect-product representation `foxTriangularRepresentation`;
the coordinate descriptions of `dw` are derived API. -/

-- Proof sketch: `foxTriangularRepresentation 1 = 1`, so its left coordinate is the additive
-- identity of the Fox differential module.
/-- The universal Fox differential of the identity element is zero. -/
theorem foxUniversalDifferential_one :
    foxUniversalDifferential (1 : FreeGroup X) = 0 := by
  simp [foxUniversalDifferential]

-- Proof sketch: compare the left coordinates in the multiplicativity of
-- `foxTriangularRepresentation X`; semidirect-product multiplication gives the additive product
-- rule.
/-- The universal Fox differential satisfies the Fox product rule `d(uv) = du + u · dv`. -/
theorem foxUniversalDifferential_mul (u v : FreeGroup X) :
    foxUniversalDifferential (u * v) =
      foxUniversalDifferential u + u • foxUniversalDifferential v := by
  apply Additive.toMul.injective
  change (foxTriangularRepresentation X (u * v)).left =
    Additive.toMul (foxUniversalDifferential u + u • foxUniversalDifferential v)
  rw [map_mul, foxTriangularRepresentation_eq_pair u, foxTriangularRepresentation_eq_pair v]
  rfl

/- Definition 1-10-7: the second Magnus representation is the canonical Fox triangular
representation of the free group. -/
#check foxTriangularRepresentation

/- In source coordinates, the canonical triangular representation sends `w` to `(dw, w)`. -/
#check (foxTriangularRepresentation_eq_pair :
  ∀ w : FreeGroup X,
    foxTriangularRepresentation X w =
      (⟨Additive.toMul (foxUniversalDifferential w), w⟩ :
        foxTriangularRepresentationTarget X))

/- The second Magnus representation is faithful. -/
#check foxTriangularRepresentation_injective
