import Mathlib
import StacksProject_2024.Chap14.Definition_14_26_1
import StacksProject_2024.Chap14.Definition_14_26_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open SimplexCategory Simplicial Opposite

universe w u v

noncomputable section

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]
variable {T : Type w}

/- Domain-style sampling for Lemma 14.26.10:
- primary domain: closure of simplicial homotopy and simplicial homotopy equivalence under
  categorical products of simplicial objects;
- inspected same-kind declarations:
  `CategoryTheory.SimplicialObject.Homotopy`,
  `CategoryTheory.SimplicialObject.Homotopic`,
  `CategoryTheory.SimplicialObject.HomotopyEquiv`,
  `CategoryTheory.Limits.Pi.map`;
- best owner abstractions: the primitive directed data live in `Homotopy`, the zigzag relation
  lives in `Homotopic`, the equivalence data live in `HomotopyEquiv`, and the product maps are the
  canonical `Pi.map`s;
- primitive-vs-derived split:
  primitive input data are a family `H : ∀ t, Homotopy (a t) (b t)` or a family
  `e : ∀ t, HomotopyEquiv (X t) (Y t)`;
  derived API consists of the owner construction `Homotopy.piMap`, the induced zigzag theorem
  `Homotopic.piMap`, and the induced product homotopy equivalence `HomotopyEquiv.piObj` for finite
  index families.

Source/core/bridge triage:
- `source-facing`: the three product-closure assertions stated in Lemma 14.26.10;
- `core/canonical`: the owner-level APIs `Homotopy.piMap`, `Homotopic.piMap`, and
  `HomotopyEquiv.piObj` for finite index families;
- `bridge/view`: none introduced here, since the owner-level constructions already match the source
  mathematics directly.
-/

namespace Homotopy

variable {X Y : T → SimplicialObject C}
variable [HasProductsOfShape T C]
variable {a b : ∀ t, X t ⟶ Y t}

/-- Lemma 14.26.10 (2): a family of simplicial homotopies `a t ⟶ b t` induces a simplicial
homotopy from the product map `∏ a t` to the product map `∏ b t`. -/
def piMap (H : ∀ t, Homotopy (a t) (b t)) :
    Homotopy (Limits.Pi.map a) (Limits.Pi.map b) where
  h {n} i :=
    (piObjIso X (op ⦋n⦌)).hom ≫
      Limits.Pi.map (fun t ↦ (H t).h i) ≫
      (piObjIso Y (op ⦋n + 1⦌)).inv
  h_zero_comp_δ_zero n := by
    apply (cancel_mono (piObjIso Y (op ⦋n⦌)).hom).1
    refine Pi.hom_ext _ _ fun t ↦ ?_
    simpa only [Category.assoc, piObjIso_hom_comp_π, δ_naturality, piObjIso_inv_comp_π_assoc,
      Pi.map_π_assoc, Homotopy.h_zero_comp_δ_zero, piObjIso_hom_comp_π_assoc] using
      congr_app (Pi.map_π b t).symm (op ⦋n⦌)
  h_last_comp_δ_last n := by
    apply (cancel_mono (piObjIso Y (op ⦋n⦌)).hom).1
    refine Pi.hom_ext _ _ fun t ↦ ?_
    simpa only [Category.assoc, piObjIso_hom_comp_π, δ_naturality, piObjIso_inv_comp_π_assoc,
      Pi.map_π_assoc, Homotopy.h_last_comp_δ_last, piObjIso_hom_comp_π_assoc] using
      congr_app (Pi.map_π a t).symm (op ⦋n⦌)
  h_succ_comp_δ_castSucc_of_lt {n} i j hij := by
    apply (cancel_mono (piObjIso Y (op ⦋n + 1⦌)).hom).1
    refine Pi.hom_ext _ _ fun t ↦ ?_
    simp [Category.assoc, (H t).h_succ_comp_δ_castSucc_of_lt i j hij]
  h_succ_comp_δ_castSucc_succ {n} j := by
    apply (cancel_mono (piObjIso Y (op ⦋n + 1⦌)).hom).1
    refine Pi.hom_ext _ _ fun t ↦ ?_
    simp [Category.assoc, (H t).h_succ_comp_δ_castSucc_succ j]
  h_castSucc_comp_δ_succ_of_lt {n} i j hji := by
    apply (cancel_mono (piObjIso Y (op ⦋n + 1⦌)).hom).1
    refine Pi.hom_ext _ _ fun t ↦ ?_
    simp [Category.assoc, (H t).h_castSucc_comp_δ_succ_of_lt i j hji]
  h_comp_σ_castSucc_of_le {n} i j hij := by
    apply (cancel_mono (piObjIso Y (op ⦋n + 2⦌)).hom).1
    refine Pi.hom_ext _ _ fun t ↦ ?_
    simp [Category.assoc, (H t).h_comp_σ_castSucc_of_le i j hij]
  h_comp_σ_succ_of_lt {n} i j hji := by
    apply (cancel_mono (piObjIso Y (op ⦋n + 2⦌)).hom).1
    refine Pi.hom_ext _ _ fun t ↦ ?_
    simp [Category.assoc, (H t).h_comp_σ_succ_of_lt i j hji]

end Homotopy

namespace Homotopic

variable [Finite T]
variable {X Y : T → SimplicialObject C}
variable [HasProductsOfShape T C]
variable {a b : ∀ t, X t ⟶ Y t}

-- Proof sketch: expand each component zigzag `Homotopic (a t) (b t)` into finitely many directed
-- homotopies, promote each single-coordinate change to a product zigzag via the owner-level
-- construction `Homotopy.piMap`, and concatenate the finitely many coordinatewise zigzags.
/-- Lemma 14.26.10 (3): if each pair of component maps `a t`, `b t` are homotopic in the zigzag
sense, then the induced product maps are homotopic. -/
theorem piMap
    (hab : ∀ t, Homotopic (a t) (b t)) :
    Homotopic (Limits.Pi.map a) (Limits.Pi.map b) := by
  classical
  letI : Fintype T := Fintype.ofFinite T
  let c : Finset T → ∀ t, X t ⟶ Y t := fun s t ↦ if t ∈ s then b t else a t
  have hs : ∀ s : Finset T, Homotopic (Limits.Pi.map a) (Limits.Pi.map (c s)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa [c] using Homotopic.refl (Limits.Pi.map a)
    | @insert t s ht ih =>
        have hcs : Function.update (c s) t (a t) = c s := by
          funext x
          by_cases hx : x = t
          · subst hx
            simp [c, ht]
          · simp [c, Function.update, hx]
        have hct : Function.update (c s) t (b t) = c (insert t s) := by
          funext x
          by_cases hx : x = t
          · subst hx
            simp [c]
          · simp [c, Function.update, hx, Finset.mem_insert]
        have hst :
            Homotopic (Limits.Pi.map (c s)) (Limits.Pi.map (c (insert t s))) := by
          simpa [hcs, hct] using
            (hab t).map
              (fun u : X t ⟶ Y t ↦ Limits.Pi.map (Function.update (c s) t u))
              (fun {u v} huv ↦
                Homotopic.of_homotopy <|
                  Homotopy.piMap fun x ↦ by
                    by_cases hx : x = t
                    · subst hx
                      simpa using huv
                    · simpa [Function.update, hx] using Homotopy.refl ((c s) x))
        exact ih.trans hst
  simpa [c] using hs Finset.univ

end Homotopic

namespace HomotopyEquiv

variable {X Y : T → SimplicialObject C}
variable [HasProductsOfShape T C]

/-- Lemma 14.26.10 (1): if each `X t` is homotopy equivalent to `Y t` and the index type is
finite, then the categorical products of the families of simplicial objects are homotopy
equivalent. -/
def piObj [Finite T] (e : ∀ t, HomotopyEquiv (X t) (Y t)) :
    HomotopyEquiv (∏ᶜ X) (∏ᶜ Y) where
  hom := Limits.Pi.map fun t ↦ (e t).hom
  inv := Limits.Pi.map fun t ↦ (e t).inv
  homotopyHomInvId := by
    let a : ∀ t, X t ⟶ X t := fun t ↦ (e t).hom ≫ (e t).inv
    let b : ∀ t, X t ⟶ X t := fun t ↦ 𝟙 (X t)
    simpa [a, b, Limits.Pi.map_comp_map, Limits.Pi.map_id] using
      Homotopic.piMap (fun t ↦ (e t).homotopyHomInvId)
  homotopyInvHomId := by
    let a : ∀ t, Y t ⟶ Y t := fun t ↦ (e t).inv ≫ (e t).hom
    let b : ∀ t, Y t ⟶ Y t := fun t ↦ 𝟙 (Y t)
    simpa [a, b, Limits.Pi.map_comp_map, Limits.Pi.map_id] using
      Homotopic.piMap (fun t ↦ (e t).homotopyInvHomId)

end HomotopyEquiv

end CategoryTheory.SimplicialObject
