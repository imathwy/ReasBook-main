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

namespace ShortComplex

variable [HasBinaryBiproducts C]
variable {S T : ShortComplex C}

/-- The stable block morphism attached to a homotopy equivalence of two-term short complexes. -/
noncomputable def stableBiprodHom (e : S.HomotopyEquiv T) :
    S.X₁ ⊞ T.X₂ ⟶ T.X₁ ⊞ S.X₂ :=
  biprod.lift
    (biprod.desc e.hom.τ₁ (-e.homotopyInvHomId.h₁))
    (biprod.desc S.f e.inv.τ₂)

private noncomputable def stableBiprodInv (e : S.HomotopyEquiv T) :
    T.X₁ ⊞ S.X₂ ⟶ S.X₁ ⊞ T.X₂ :=
  biprod.lift
    (biprod.desc e.inv.τ₁ e.homotopyHomInvId.h₁)
    (biprod.desc (-T.f) e.hom.τ₂)

-- Proof sketch: expand the biproduct components of the two block maps and use the homotopy
-- identities for `e`. Since `S.g = 0` and `T.g = 0`, the two-term condition removes the residual
-- rightmost terms, leaving the standard block-matrix computation.
/-- The two stable block morphisms compose to the identity on `S.X₁ ⊞ T.X₂`. -/
private lemma stableBiprodHom_inv_id
    (hS : S.g = 0) (hT : T.g = 0) (e : S.HomotopyEquiv T) :
    stableBiprodHom e ≫ stableBiprodInv e = 𝟙 (S.X₁ ⊞ T.X₂) := sorry

-- Proof sketch: this is the same computation with `S` and `T` exchanged.
/-- The two stable block morphisms compose to the identity on `T.X₁ ⊞ S.X₂`. -/
private lemma stableBiprodInv_hom_id
    (hS : S.g = 0) (hT : T.g = 0) (e : S.HomotopyEquiv T) :
    stableBiprodInv e ≫ stableBiprodHom e = 𝟙 (T.X₁ ⊞ S.X₂) := sorry

/-- The stable block isomorphism attached to a homotopy equivalence of two-term short
complexes. -/
noncomputable def stableBiprodIso
    (hS : S.g = 0) (hT : T.g = 0) (e : S.HomotopyEquiv T) :
    S.X₁ ⊞ T.X₂ ≅ T.X₁ ⊞ S.X₂ where
  hom := stableBiprodHom e
  inv := stableBiprodInv e
  hom_inv_id := stableBiprodHom_inv_id hS hT e
  inv_hom_id := stableBiprodInv_hom_id hS hT e

/-- The stable block morphism for a homotopy equivalence of two-term short complexes is an
isomorphism. -/
theorem stableBiprodHom_isIso
    (hS : S.g = 0) (hT : T.g = 0) (e : S.HomotopyEquiv T) :
    IsIso (stableBiprodHom e) := by
  change IsIso ((stableBiprodIso hS hT e).hom)
  infer_instance

noncomputable instance
    (hS : S.g = 0) (hT : T.g = 0) (e : S.HomotopyEquiv T) :
    IsIso (stableBiprodHom e) :=
  stableBiprodHom_isIso hS hT e

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
theorem term_complex_biprod_hom_isIso
    (e : HomotopyEquiv A B) :
    IsIso (term_complex_biprod_hom e) := by
  letI : IsIso (ShortComplex.stableBiprodHom (e.toSc0)) :=
    ShortComplex.stableBiprodHom_isIso (sc0_g_eq_zero A) (sc0_g_eq_zero B) (e.toSc0)
  change IsIso
    ((((sourceBiprodIso A B).symm ≪≫ asIso (ShortComplex.stableBiprodHom (e.toSc0)) ≪≫
        targetBiprodIso A B).hom))
  infer_instance

noncomputable instance
    (e : HomotopyEquiv A B) :
    IsIso (term_complex_biprod_hom e) :=
  term_complex_biprod_hom_isIso e

end

end
