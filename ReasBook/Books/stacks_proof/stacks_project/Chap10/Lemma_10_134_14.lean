import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex

universe u v

noncomputable section

/- Domain-style sampling:
* primary domain: two-term complexes encoded by short complexes with vanishing second
  differential, and transported from chain complexes through `K.sc 0`;
* sampled owner declarations:
  - `HomologicalComplex.shortComplexFunctor` and `HomologicalComplex.sc`,
    which package the degree-`0` two-term view of a chain complex;
  - `ShortComplex.HomotopyEquiv`, the canonical owner for homotopy equivalences of those
    two-term objects;
  - `Homotopy.toShortComplex`, which transports chain homotopies to the associated short
    complexes;
  - `HomologicalComplex.XIsoOfEq`, the owner-level transport used to identify the degree-`0`
    short-complex terms with `A.X 1` and `A.X 0`;
  - `HomologicalComplex.sc`, used only as the bridge from the chain-complex presentation back to
    the short-complex owner.
* best owner abstraction: the stable block morphism and isomorphism belong at the
  `ShortComplex.HomotopyEquiv` level, under the intrinsic two-term hypothesis `g = 0`; the
  chain-complex statement is then only the thin transport along `A.sc 0` and `B.sc 0`.
* layer triage:
  - `source-facing`: the stable block morphism for short complexes with zero second differential;
  - `core/canonical`: `ShortComplex.HomotopyEquiv`;
  - `bridge/view`: the chain-complex morphism `A.X 1 ⊞ B.X 0 ⟶ B.X 1 ⊞ A.X 0` obtained from
    `(A.sc 0)` and `(B.sc 0)`.
-/

section

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Helper for Lemma 10.134.14: in degree `0`, the extra `h₀` term produced by
`Homotopy.toShortComplex` factors through degree `2`, so it vanishes as soon as the target is
zero there. -/
private lemma chain_homotopy_toSc0_h₀_eq_zero
    {A B : ChainComplex C ℕ} {f g : A ⟶ B} (ho : Homotopy f g) (hB₂ : IsZero (B.X 2)) :
    (ho.toShortComplex 0).h₀ = 0 := by
  -- At `i = 0`, the defining branch of `toShortComplex` uses the degree-`2` component.
  have hzero : ho.hom 1 2 = 0 := hB₂.eq_of_tgt _ _
  have hcomp : ho.hom 1 2 ≫ B.d 2 1 = 0 := by
    rw [hzero, zero_comp]
  have hprev0 : (ComplexShape.down ℕ).prev 0 = 1 := by
    simp [ChainComplex.prev]
  have hprev1 : (ComplexShape.down ℕ).prev ((ComplexShape.down ℕ).prev 0) = 2 := by
    rw [hprev0]
    simp [ChainComplex.prev]
  have hprev_one : (ComplexShape.down ℕ).prev 1 = 2 := by
    simp [ChainComplex.prev]
  dsimp [Homotopy.toShortComplex]
  rw [if_pos (by simp)]
  have hzero' :
      ho.hom ((ComplexShape.down ℕ).prev 0)
        ((ComplexShape.down ℕ).prev ((ComplexShape.down ℕ).prev 0)) = 0 := by
    rw [hprev0]
    rw [hprev_one]
    exact hzero
  rw [hzero', zero_comp]
  rfl

namespace ShortComplex

variable [HasBinaryBiproducts C]
variable {S T : ShortComplex C}

/-- The stable block morphism attached to a homotopy equivalence of two-term short complexes. -/
noncomputable def stableBiprodHom (e : S.HomotopyEquiv T) :
    S.X₁ ⊞ T.X₂ ⟶ T.X₁ ⊞ S.X₂ :=
  biprod.lift
    (biprod.desc e.hom.τ₁ e.homotopyInvHomId.h₁)
    (biprod.desc S.f e.inv.τ₂)

private noncomputable def stableBiprodInv (e : S.HomotopyEquiv T) :
    T.X₁ ⊞ S.X₂ ⟶ S.X₁ ⊞ T.X₂ :=
  biprod.lift
    (biprod.desc e.inv.τ₁ (-e.homotopyHomInvId.h₁))
    (biprod.desc (-T.f) e.hom.τ₂)

/-- Helper for Lemma 10.134.14: normalize the forward block morphism as a biproduct matrix so
the source proof can be read entrywise. -/
lemma stableBiprodHom_eq_ofComponents (e : S.HomotopyEquiv T) :
    stableBiprodHom e =
      Biprod.ofComponents e.hom.τ₁ S.f e.homotopyInvHomId.h₁ e.inv.τ₂ := by
  -- We freeze the four matrix entries of `stableBiprodHom` once so later calculations can use
  -- the source proof's block notation instead of repeated `biprod.lift`/`biprod.desc` expansion.
  rw [← Biprod.ofComponents_eq (stableBiprodHom e)]
  simp [stableBiprodHom]

/-- Helper for Lemma 10.134.14: normalize the backward block morphism as a biproduct matrix so
the source proof can be compared directly with the Lean block map. -/
lemma stableBiprodInv_eq_ofComponents (e : S.HomotopyEquiv T) :
    stableBiprodInv e =
      Biprod.ofComponents e.inv.τ₁ (-T.f) (-e.homotopyHomInvId.h₁) e.hom.τ₂ := by
  -- As above, we expose the four entries explicitly before attempting the matrix computation.
  rw [← Biprod.ofComponents_eq (stableBiprodInv e)]
  simp [stableBiprodInv]

/-- Helper for Lemma 10.134.14: the forward-then-backward block product is the lower unipotent
automorphism predicted by the source proof once the extra diagonal `h₀` term disappears. -/
lemma stableBiprodHom_comp_stableBiprodInv_eq_unipotentLower
    (e : S.HomotopyEquiv T) (hT : T.g = 0) (h0S : e.homotopyHomInvId.h₀ = 0) :
    stableBiprodHom e ≫ stableBiprodInv e =
      (Biprod.unipotentLower
        (e.homotopyInvHomId.h₁ ≫ e.inv.τ₁ - e.inv.τ₂ ≫ e.homotopyHomInvId.h₁)).hom := by
  -- We translate the composite into a four-entry block matrix before simplifying each entry.
  rw [stableBiprodHom_eq_ofComponents, stableBiprodInv_eq_ofComponents, Biprod.ofComponents_comp]
  -- The off-diagonal zero and diagonal identities come from the morphism and homotopy equations.
  ext <;> simp [Biprod.unipotentLower, e.hom.comm₁₂]
  · -- The `(1,1)` entry is the identity after cancelling the homotopy correction.
    rw [show e.hom.τ₁ ≫ e.inv.τ₁ =
        S.f ≫ e.homotopyHomInvId.h₁ + e.homotopyHomInvId.h₀ + 𝟙 S.X₁ by
          simpa using e.homotopyHomInvId.comm₁, h0S]
    abel
  · abel
  · -- The `(2,2)` entry is the identity because `T.g = 0` kills the extra term in `comm₂`.
    rw [show e.inv.τ₂ ≫ e.hom.τ₂ =
        T.g ≫ e.homotopyInvHomId.h₂ + e.homotopyInvHomId.h₁ ≫ T.f + 𝟙 T.X₂ by
          simpa using e.homotopyInvHomId.comm₂, hT, zero_comp]
    abel

/-- Helper for Lemma 10.134.14: the backward-then-forward block product is the symmetric lower
unipotent automorphism from the source proof after the degree-`2` diagonal term vanishes. -/
lemma stableBiprodInv_comp_stableBiprodHom_eq_unipotentLower
    (e : S.HomotopyEquiv T) (hS : S.g = 0) (h0T : e.homotopyInvHomId.h₀ = 0) :
    stableBiprodInv e ≫ stableBiprodHom e =
      (Biprod.unipotentLower
        (e.hom.τ₂ ≫ e.homotopyInvHomId.h₁ - e.homotopyHomInvId.h₁ ≫ e.hom.τ₁)).hom := by
  -- This is the same entrywise block computation with `S` and `T` interchanged.
  rw [stableBiprodInv_eq_ofComponents, stableBiprodHom_eq_ofComponents, Biprod.ofComponents_comp]
  ext <;> simp [Biprod.unipotentLower, e.inv.comm₁₂]
  · -- The `(1,1)` entry is the identity after the target-side homotopy correction cancels.
    rw [show e.inv.τ₁ ≫ e.hom.τ₁ =
        T.f ≫ e.homotopyInvHomId.h₁ + e.homotopyInvHomId.h₀ + 𝟙 T.X₁ by
          simpa using e.homotopyInvHomId.comm₁, h0T]
    abel
  · abel
  · -- The `(2,2)` entry is the identity because `S.g = 0` removes the extra `comm₂` term.
    rw [show e.hom.τ₂ ≫ e.inv.τ₂ =
        S.g ≫ e.homotopyHomInvId.h₂ + e.homotopyHomInvId.h₁ ≫ S.f + 𝟙 S.X₂ by
          simpa using e.homotopyHomInvId.comm₂, hS, zero_comp]
    abel

/-- Helper for Lemma 10.134.14: after correcting the naive backward block map by the inverse
unipotent factors coming from the two block products, the forward block morphism becomes an
isomorphism. -/
theorem stableBiprodHom_isIso_of_h₀_eq_zero
    (e : S.HomotopyEquiv T) (hS : S.g = 0) (hT : T.g = 0)
    (h0S : e.homotopyHomInvId.h₀ = 0) (h0T : e.homotopyInvHomId.h₀ = 0) :
    IsIso (stableBiprodHom e) := by
  -- The source proof shows that the naive inverse works up to lower-unipotent corrections.
  let U : S.X₁ ⊞ T.X₂ ≅ S.X₁ ⊞ T.X₂ :=
    Biprod.unipotentLower
      (e.homotopyInvHomId.h₁ ≫ e.inv.τ₁ - e.inv.τ₂ ≫ e.homotopyHomInvId.h₁)
  let V : T.X₁ ⊞ S.X₂ ≅ T.X₁ ⊞ S.X₂ :=
    Biprod.unipotentLower
      (e.hom.τ₂ ≫ e.homotopyInvHomId.h₁ - e.homotopyHomInvId.h₁ ≫ e.hom.τ₁)
  let rightInv : T.X₁ ⊞ S.X₂ ⟶ S.X₁ ⊞ T.X₂ := stableBiprodInv e ≫ U.inv
  let leftInv : T.X₁ ⊞ S.X₂ ⟶ S.X₁ ⊞ T.X₂ := V.inv ≫ stableBiprodInv e
  have hright : stableBiprodHom e ≫ rightInv = 𝟙 _ := by
    -- The right correction removes the unipotent defect on `stableBiprodHom ≫ stableBiprodInv`.
    calc
      stableBiprodHom e ≫ rightInv = (stableBiprodHom e ≫ stableBiprodInv e) ≫ U.inv := by
        simp [rightInv, Category.assoc]
      _ = 𝟙 _ := by
        rw [stableBiprodHom_comp_stableBiprodInv_eq_unipotentLower e hT h0S, Iso.hom_inv_id]
  have hleft : leftInv ≫ stableBiprodHom e = 𝟙 _ := by
    -- The left correction removes the symmetric defect on the other composite.
    calc
      leftInv ≫ stableBiprodHom e = V.inv ≫ (stableBiprodInv e ≫ stableBiprodHom e) := by
        simp [leftInv, Category.assoc]
      _ = 𝟙 _ := by
        rw [stableBiprodInv_comp_stableBiprodHom_eq_unipotentLower e hS h0T, Iso.inv_hom_id]
  have hsame : leftInv = rightInv := by
    -- Any left inverse and right inverse of the same map must coincide.
    calc
      leftInv = leftInv ≫ 𝟙 _ := by simp
      _ = leftInv ≫ (stableBiprodHom e ≫ rightInv) := by rw [hright]
      _ = (leftInv ≫ stableBiprodHom e) ≫ rightInv := by simp [Category.assoc]
      _ = rightInv := by rw [hleft, Category.id_comp]
  -- Packaging the common inverse yields the desired `IsIso` witness.
  exact ⟨⟨leftInv, by simpa [hsame] using hright, hleft⟩⟩

end ShortComplex

variable {A B : ChainComplex C ℕ}

/-- The degree-`0` short-complex homotopy equivalence induced by a chain-complex homotopy
equivalence. This is the thin bridge from the chain-complex owner `HomotopyEquiv` to the
short-complex owner `ShortComplex.HomotopyEquiv`. -/
private noncomputable def HomotopyEquiv.toSc0 (e : HomotopyEquiv A B) :
    ShortComplex.HomotopyEquiv (A.sc 0) (B.sc 0) where
  hom := (shortComplexFunctor C (ComplexShape.down ℕ) 0).map e.hom
  inv := (shortComplexFunctor C (ComplexShape.down ℕ) 0).map e.inv
  homotopyHomInvId := e.homotopyHomInvId.toShortComplex 0
  homotopyInvHomId := e.homotopyInvHomId.toShortComplex 0

/-- The associated degree-`0` short complexes of a chain complex have zero second differential. -/
private lemma sc0_g_eq_zero (A : ChainComplex C ℕ) : (A.sc 0).g = 0 := by
  change A.d 0 ((ComplexShape.down ℕ).next 0) = 0
  simp

section

variable [HasBinaryBiproducts C]

private noncomputable def sourceBiprodIso (A B : ChainComplex C ℕ) :
    (A.sc 0).X₁ ⊞ (B.sc 0).X₂ ≅ A.X 1 ⊞ B.X 0 :=
  biprod.mapIso
    (A.XIsoOfEq <| by simp)
    (B.XIsoOfEq <| by simp)

private noncomputable def targetBiprodIso (A B : ChainComplex C ℕ) :
    (B.sc 0).X₁ ⊞ (A.sc 0).X₂ ≅ B.X 1 ⊞ A.X 0 :=
  biprod.mapIso
    (B.XIsoOfEq <| by simp)
    (A.XIsoOfEq <| by simp)

/-- The source-facing block morphism `A.X 1 ⊞ B.X 0 ⟶ B.X 1 ⊞ A.X 0` induced by a homotopy
equivalence of chain complexes. It is the bridge/view obtained by transporting
`ShortComplex.stableBiprodHom (e.toSc0)` along the degree-`1` / degree-`0` identifications for
`A.sc 0` and `B.sc 0`. -/
noncomputable def term_complex_biprod_hom (e : HomotopyEquiv A B) :
    A.X 1 ⊞ B.X 0 ⟶ B.X 1 ⊞ A.X 0 :=
  (sourceBiprodIso A B).inv ≫ ShortComplex.stableBiprodHom (e.toSc0) ≫ (targetBiprodIso A B).hom

/-- Lemma 10.134.14: if chain complexes in a preadditive category with binary biproducts are
homotopy equivalent, then the canonical block morphism
`A.X 1 ⊞ B.X 0 ⟶ B.X 1 ⊞ A.X 0` induced by a homotopy equivalence is invertible. This is the
transport of the owner-level stable isomorphism for the associated two-term short complexes
`A.sc 0` and `B.sc 0`. -/
@[stacks 00S3]
theorem term_complex_biprod_hom_isIso
    (hA : ∀ n : ℕ, n ≠ 0 → n ≠ 1 → IsZero (A.X n))
    (hB : ∀ n : ℕ, n ≠ 0 → n ≠ 1 → IsZero (B.X n))
    (e : HomotopyEquiv A B) :
    IsIso (term_complex_biprod_hom e) := by
  -- Route correction: we keep the source block-matrix argument, but execute it on `A.sc 0` and
  -- `B.sc 0`, where the concentration hypotheses kill the extra `toShortComplex` diagonal terms.
  have hA₂ : IsZero (A.X 2) := hA 2 (by norm_num) (by norm_num)
  have hB₂ : IsZero (B.X 2) := hB 2 (by norm_num) (by norm_num)
  have h0A : (e.homotopyHomInvId.toShortComplex 0).h₀ = 0 :=
    chain_homotopy_toSc0_h₀_eq_zero e.homotopyHomInvId hA₂
  have h0B : (e.homotopyInvHomId.toShortComplex 0).h₀ = 0 :=
    chain_homotopy_toSc0_h₀_eq_zero e.homotopyInvHomId hB₂
  -- The owner-level short-complex block map is invertible, so its transport is too.
  letI : IsIso (ShortComplex.stableBiprodHom (e.toSc0)) :=
    ShortComplex.stableBiprodHom_isIso_of_h₀_eq_zero (e.toSc0)
      (sc0_g_eq_zero A) (sc0_g_eq_zero B) h0A h0B
  change IsIso
    ((((sourceBiprodIso A B).symm ≪≫ asIso (ShortComplex.stableBiprodHom (e.toSc0)) ≪≫
        targetBiprodIso A B).hom))
  infer_instance


end

end
