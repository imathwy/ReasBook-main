import Mathlib.Topology.Homotopy.HomotopyGroup

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Function
open scoped Topology Topology.Homotopy

variable {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]

-- Semantic recall: `lean_leansearch` surfaced `FundamentalGroup.map`; mathlib exposes `π_ q Y y`
-- canonically, so we model `e_*` by the quotient map induced by postcomposition on generalized
-- loops.

/-- Postcompose a generalized loop with a continuous map. -/
def genLoopMap (e : C(Y, Z)) {q : ℕ} {y : Y} :
    Ω^ (Fin q) Y y → Ω^ (Fin q) Z (e y)
  | γ =>
      ⟨e.comp γ.1, fun t ht ↦ by
        simpa using congrArg e (γ.2 t ht)⟩

/-- The map on `π_ q` induced by a continuous map `e : C(Y, Z)` at the basepoint `y : Y`. -/
def homotopyGroupMap (e : C(Y, Z)) (q : ℕ) (y : Y) :
    π_ q Y y → π_ q Z (e y) :=
  Quotient.map (genLoopMap e) fun γ δ h ↦ by
    change (genLoopMap e γ).1.HomotopicRel (genLoopMap e δ).1 (Cube.boundary (Fin q))
    simpa [genLoopMap, GenLoop.Homotopic] using
      ContinuousMap.HomotopicRel.comp_continuousMap h e

namespace ContinuousMap

/-- The induced map on `π_ q` attached to `e`, i.e. the source notation `e_*`. -/
abbrev eStar (e : C(Y, Z)) (q : ℕ) (y : Y) :
    π_ q Y y → π_ q Z (e y) :=
  homotopyGroupMap e q y

end ContinuousMap

/-- The induced map on `π_ q` sends the class of a generalized loop to the class of its
postcomposition with `e`. -/
@[simp] theorem homotopyGroupMap_mk (e : C(Y, Z)) (q : ℕ) (y : Y) (γ : Ω^ (Fin q) Y y) :
    e.eStar q y ⟦γ⟧ = (⟦genLoopMap e γ⟧ : π_ q Z (e y)) := rfl

/-- Helper for Definition 9.6.1: postcomposition sends the constant generalized loop to the
constant generalized loop. -/
@[simp] theorem genLoopMap_const (e : C(Y, Z)) {q : ℕ} {y : Y} :
    genLoopMap e (GenLoop.const : Ω^ (Fin q) Y y) =
      (GenLoop.const : Ω^ (Fin q) Z (e y)) := by
  -- Compare the two generalized loops pointwise, where both sides are constant.
  ext t
  rfl

/-- Helper for Definition 9.6.1: postcomposition commutes with the standard concatenation
representative `GenLoop.transAt`. -/
@[simp] theorem genLoopMap_transAt (e : C(Y, Z)) {n : ℕ} {y : Y} (i : Fin (n + 1))
    (γ δ : Ω^ (Fin (n + 1)) Y y) :
    genLoopMap e (GenLoop.transAt i γ δ) =
      GenLoop.transAt i (genLoopMap e γ) (genLoopMap e δ) := by
  -- Unfold the representative formulas and compare them pointwise.
  ext t
  dsimp [genLoopMap, GenLoop.transAt, GenLoop.copy]
  split_ifs <;> rfl

/-- Helper for Definition 9.6.1: the induced map on `π_(n + 1)` preserves the unit element. -/
@[simp] theorem homotopyGroupMap_one (e : C(Y, Z)) (n : ℕ) (y : Y) :
    e.eStar (n + 1) y 1 = (1 : π_ (n + 1) Z (e y)) := by
  -- Rewrite both units as classes of constant representatives.
  rw [HomotopyGroup.one_def, homotopyGroupMap_mk, HomotopyGroup.one_def]
  -- Postcomposition preserves the constant representative.
  rw [genLoopMap_const]

/-- Helper for Definition 9.6.1: the induced map on `π_(n + 1)` preserves multiplication. -/
theorem homotopyGroupMap_mul (e : C(Y, Z)) (n : ℕ) (y : Y)
    (p q : π_ (n + 1) Y y) :
    e.eStar (n + 1) y (p * q) = e.eStar (n + 1) y p * e.eStar (n + 1) y q := by
  -- Reduce the quotient statement to representatives of the two homotopy classes.
  refine Quotient.inductionOn₂ p q ?_
  intro γ δ
  have hsource :
      ((· * ·) : π_ (n + 1) Y y → π_ (n + 1) Y y → π_ (n + 1) Y y) ⟦γ⟧ ⟦δ⟧ =
        ⟦GenLoop.transAt (0 : Fin (n + 1)) δ γ⟧ := by
    rw [HomotopyGroup.mul_spec (i := (0 : Fin (n + 1))) (p := γ) (q := δ)]
  have htarget :
      ((· * ·) : π_ (n + 1) Z (e y) → π_ (n + 1) Z (e y) → π_ (n + 1) Z (e y))
          ⟦genLoopMap e γ⟧ ⟦genLoopMap e δ⟧ =
        ⟦GenLoop.transAt (0 : Fin (n + 1)) (genLoopMap e δ) (genLoopMap e γ)⟧ := by
    rw [HomotopyGroup.mul_spec (i := (0 : Fin (n + 1))) (p := genLoopMap e γ)
      (q := genLoopMap e δ)]
  have hleft :
      e.eStar (n + 1) y
          (((· * ·) : π_ (n + 1) Y y → π_ (n + 1) Y y → π_ (n + 1) Y y) ⟦γ⟧ ⟦δ⟧) =
        e.eStar (n + 1) y (⟦GenLoop.transAt (0 : Fin (n + 1)) δ γ⟧) := by
    simpa using congrArg (e.eStar (n + 1) y) hsource
  have hfinal :
      e.eStar (n + 1) y
          (((· * ·) : π_ (n + 1) Y y → π_ (n + 1) Y y → π_ (n + 1) Y y) ⟦γ⟧ ⟦δ⟧) =
        ((· * ·) : π_ (n + 1) Z (e y) → π_ (n + 1) Z (e y) → π_ (n + 1) Z (e y))
          (e.eStar (n + 1) y ⟦γ⟧) (e.eStar (n + 1) y ⟦δ⟧) := by
    have hMappedRepresentative :
        e.eStar (n + 1) y
            (((· * ·) : π_ (n + 1) Y y → π_ (n + 1) Y y → π_ (n + 1) Y y) ⟦γ⟧ ⟦δ⟧) =
          (⟦genLoopMap e (GenLoop.transAt (0 : Fin (n + 1)) δ γ)⟧ : π_ (n + 1) Z (e y)) := by
      exact hleft.trans (by rw [homotopyGroupMap_mk])
    have hMappedTransAt :
        e.eStar (n + 1) y
            (((· * ·) : π_ (n + 1) Y y → π_ (n + 1) Y y → π_ (n + 1) Y y) ⟦γ⟧ ⟦δ⟧) =
          (⟦GenLoop.transAt (0 : Fin (n + 1)) (genLoopMap e δ) (genLoopMap e γ)⟧ :
            π_ (n + 1) Z (e y)) := by
      exact hMappedRepresentative.trans (by rw [genLoopMap_transAt])
    have hMappedProduct :
        e.eStar (n + 1) y
            (((· * ·) : π_ (n + 1) Y y → π_ (n + 1) Y y → π_ (n + 1) Y y) ⟦γ⟧ ⟦δ⟧) =
          ((· * ·) : π_ (n + 1) Z (e y) → π_ (n + 1) Z (e y) → π_ (n + 1) Z (e y))
            ⟦genLoopMap e γ⟧ ⟦genLoopMap e δ⟧ := by
      exact hMappedTransAt.trans (by simpa using htarget.symm)
    exact hMappedProduct.trans (by simp [homotopyGroupMap_mk])
  -- Rewrite both products using the standard concatenation representative in coordinate `0`.
  simpa using hfinal

namespace ContinuousMap

/-- The induced map on positive-degree homotopy groups attached to `e`, bundled as a
multiplicative homomorphism. -/
def eStarMulHom (e : C(Y, Z)) (n : ℕ) (y : Y) :
    π_ (n + 1) Y y →* π_ (n + 1) Z (e y) where
  toFun := e.eStar (n + 1) y
  map_one' := by
    -- Delegate the unit computation to the canonical companion theorem for `e_*`.
    exact homotopyGroupMap_one e n y
  map_mul' := by
    -- Delegate multiplicativity to the representative-level compatibility theorem.
    exact homotopyGroupMap_mul e n y

/-- A target-basepoint equality rewrites the positive-degree induced map of `e` at a chosen
basepoint. -/
def eStarMulHomOverEq (e : C(Y, Z)) (n : ℕ) {y : Y} {z : Z} (h : e y = z) :
    π_ (n + 1) Y y →* π_ (n + 1) Z z :=
  match h with
  | rfl => e.eStarMulHom n y

@[simp] theorem eStarMulHomOverEq_rfl (e : C(Y, Z)) (n : ℕ) (y : Y) :
    e.eStarMulHomOverEq n (rfl : e y = e y) = e.eStarMulHom n y := rfl

end ContinuousMap

/-- The induced map on homotopy groups of the identity map is the identity. -/
@[simp] theorem homotopyGroupMap_id (q : ℕ) (y : Y) :
    (ContinuousMap.id Y).eStar q y = id := by
  funext x
  refine Quotient.inductionOn x ?_
  intro γ
  rfl

/-- Definition 9.6.1: a continuous map `e : C(Y, Z)` is an `n`-equivalence if for every
basepoint `y : Y`, the induced map `e_* : π_ q Y y → π_ q Z (e y)` is injective for `q < n` and
surjective for `q ≤ n`. -/
@[mk_iff isNEquivalence_iff]
class IsNEquivalence (n : ℕ) (e : C(Y, Z)) : Prop where
  /-- The induced maps on `π_ q` are injective in every degree `q < n`. -/
  injectiveBelow (y : Y) {q : ℕ} (hq : q < n) : Injective (e.eStar q y)
  /-- The induced maps on `π_ q` are surjective in every degree `q ≤ n`. -/
  surjectiveUpTo (y : Y) {q : ℕ} (hq : q ≤ n) : Surjective (e.eStar q y)

/-- The identity map is an `n`-equivalence. -/
instance isNEquivalence_id (n : ℕ) : IsNEquivalence n (ContinuousMap.id Y) where
  injectiveBelow y {q} hq := by
    simpa [homotopyGroupMap_id] using (injective_id : Injective (id : π_ q Y y → π_ q Y y))
  surjectiveUpTo y {q} hq := by
    simpa [homotopyGroupMap_id] using (surjective_id : Surjective (id : π_ q Y y → π_ q Y y))

/-- An `n`-equivalence induces injective maps on `π_ q` in every degree `q < n`. -/
theorem IsNEquivalence.injective {n : ℕ} {e : C(Y, Z)} (h : IsNEquivalence n e) (y : Y)
    {q : ℕ} (hq : q < n) :
    Injective (e.eStar q y) :=
  h.injectiveBelow y hq

/-- An `n`-equivalence induces surjective maps on `π_ q` in every degree `q ≤ n`. -/
theorem IsNEquivalence.surjective {n : ℕ} {e : C(Y, Z)} (h : IsNEquivalence n e) (y : Y)
    {q : ℕ} (hq : q ≤ n) :
    Surjective (e.eStar q y) :=
  h.surjectiveUpTo y hq

/-- An `n`-equivalence induces surjective maps on `π_ q` in every degree `q < n`. -/
theorem IsNEquivalence.surjective_of_lt {n : ℕ} {e : C(Y, Z)} (h : IsNEquivalence n e) (y : Y)
    {q : ℕ} (hq : q < n) :
    Surjective (e.eStar q y) :=
  h.surjective y (Nat.le_of_lt hq)

/-- An `n`-equivalence induces bijective maps on `π_ q` in every degree `q < n`. -/
theorem IsNEquivalence.bijective {n : ℕ} {e : C(Y, Z)} (h : IsNEquivalence n e) (y : Y)
    {q : ℕ} (hq : q < n) :
    Bijective (e.eStar q y) :=
  ⟨h.injective y hq, h.surjective_of_lt y hq⟩

/-- The two-degree homotopy-group condition used in Lemma 9.6.6: at every basepoint, `e_*` is
injective on `π_ n` and surjective on `π_ (n + 1)`. -/
class HasPiInjectiveSurjectiveSucc (n : ℕ) (e : C(Y, Z)) : Prop where
  /-- The induced map on `π_ n` is injective at every basepoint. -/
  injective (y : Y) : Function.Injective (e.eStar n y)
  /-- The induced map on `π_ (n + 1)` is surjective at every basepoint. -/
  surjectiveSucc (y : Y) : Function.Surjective (e.eStar (n + 1) y)

/-- An `(n + 1)`-equivalence satisfies the two-degree condition used in Lemma 9.6.6. -/
instance hasPiInjectiveSurjectiveSucc_of_isNEquivalence (n : ℕ) (e : C(Y, Z))
    [h : IsNEquivalence (n + 1) e] : HasPiInjectiveSurjectiveSucc n e where
  injective y := h.injectiveBelow y (Nat.lt_succ_self n)
  surjectiveSucc y := h.surjectiveUpTo y (le_rfl)
