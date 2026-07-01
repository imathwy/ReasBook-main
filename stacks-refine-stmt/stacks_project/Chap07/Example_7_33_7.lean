import Mathlib
import stacks_project.Chap07.GSetForgetfulPoint
import stacks_project.Chap07.Lemma_7_32_7
import stacks_project.Chap07.Lemma_7_32_9
import stacks_project.Chap07.Proposition_7_9_1

open CategoryTheory Limits Opposite
open GrothendieckTopology.Point

universe u

namespace CategoryTheory

noncomputable section

open scoped MorphismOfTopoiIn

variable (G : Type u) [Group G]

/- Domain-style sampling for Example 7.33.7:
- sampled owner declarations:
  `Point.skyscraperSheafFunctor`,
  `Point.toToposPoint_pointPushforwardIso`,
  `sheafSectionsOnLeftRegularFunctor`,
  `gSetForgetfulPointMapMulAction`;
- core/canonical owners:
  the direct-image/skyscraper owner of the point `gSetForgetfulPoint G`,
  together with the left-regular-sections functor from Proposition 7.9.1;
- source-facing declarations in this file:
  the fiber comparison `p⁻¹(p_* S) ≃ Map(G, S)` and the resulting action-level description of
  `p_* S`;
- primitive data:
  the point `gSetForgetfulPoint G`, its left regular object, and the chapter's canonical
  right-translation action on `G → S`;
- derived API:
  the objectwise `Map(G, S)` equivalence and the section/counit comparison theorems.
-/

private noncomputable abbrev gSetForgetfulPoint_pushforwardObj
    (S : Type u) :
    Sheaf (Action.jointlySurjectiveTopology G) (Type u) :=
  ((gSetForgetfulPoint G).toToposPoint).typePushforward.obj S

/-- The value of `p_* S` on the left regular `G`-set is canonically the set `Map(G, S)`. -/
private noncomputable abbrev pushforwardLeftRegularObjEquiv
    (S : Type u) :
    ((gSetForgetfulPoint_pushforwardObj G S).1.obj (op (Action.leftRegular G))) ≃
      (G → S) :=
  let Φ := gSetForgetfulPoint G
  let e' :
      ((gSetForgetfulPoint_pushforwardObj G S).1.obj (op (Action.leftRegular G))) ≃
        (Φ.skyscraperPresheaf S).obj (op (Action.leftRegular G)) :=
    (((evaluation (Action (Type u) G)ᵒᵖ (Type u)).obj (op (Action.leftRegular G))).mapIso
      ((sheafToPresheaf _ _).mapIso
        ((GrothendieckTopology.Point.toToposPoint_pointPushforwardIso Φ).app S))).toEquiv
  e'.trans
    (Types.productIso (fun _ : Φ.fiber.obj (Action.leftRegular G) ↦ S)).toEquiv

/-- The canonical map `Map(G, S) → p^{-1}(p_* S)` obtained from the generator `1 ∈ G` of the left
regular `G`-set. -/
noncomputable def gSetForgetfulPoint_pushforwardFiberMap
    (S : Type u) (ψ : G → S) :
    ((gSetForgetfulPoint G).toToposPoint).typeInverseImage.obj
      (((gSetForgetfulPoint G).toToposPoint).typePushforward.obj S) :=
    let Φ := gSetForgetfulPoint G
    let F := gSetForgetfulPoint_pushforwardObj G S
    let x :
        Φ.sheafFiber.obj F :=
      Φ.toPresheafFiber (Action.leftRegular G)
        ((1 : G) : Φ.fiber.obj (Action.leftRegular G))
        F.1
        ((pushforwardLeftRegularObjEquiv G S).symm ψ)
    ((GrothendieckTopology.Point.toToposPoint_pointInverseImageIso Φ).app F).inv x

-- Proof sketch: the sheaf condition on the surjective site identifies the stalk of the
-- skyscraper sheaf `p_* S` with its value on the left regular `G`-set, and the chosen generator
-- `1 ∈ G` yields the inverse direction explicitly.
/-- Example 7.33.7: the canonical map `Map(G, S) → p^{-1}(p_* S)` is bijective. -/
theorem gSetForgetfulPoint_pushforwardFiberMap_bijective
    (S : Type u) :
    Function.Bijective (gSetForgetfulPoint_pushforwardFiberMap G S) :=
  sorry

/-- The canonical identification `p^{-1}(p_* S) = Map(G, S)` from Example 7.33.7. -/
noncomputable def gSetForgetfulPoint_pushforwardFiberEquiv
    (S : Type u) :
    ((gSetForgetfulPoint G).toToposPoint).typeInverseImage.obj
      (((gSetForgetfulPoint G).toToposPoint).typePushforward.obj S) ≃
      (G → S) :=
  (Equiv.ofBijective
    (gSetForgetfulPoint_pushforwardFiberMap G S)
    (gSetForgetfulPoint_pushforwardFiberMap_bijective G S)).symm

@[simp] theorem gSetForgetfulPoint_pushforwardFiberEquiv_symm_apply
    (S : Type u) (ψ : G → S) :
    (gSetForgetfulPoint_pushforwardFiberEquiv G S).symm ψ =
      gSetForgetfulPoint_pushforwardFiberMap G S ψ :=
  rfl

/-- Under the canonical equivalence `p^{-1}(p_* S) ≃ Map(G, S)` from Example 7.33.7, the section
`S → p^{-1}(p_* S)` of Lemma 7.32.9 is the constant-function map. -/
theorem gSetForgetfulPoint_pushforwardFiber_section_eq_const
    (S : Type u) :
    (fun s ↦
      gSetForgetfulPoint_pushforwardFiberEquiv G S
        (MorphismOfTopoiIn.pointPushforwardFiberSection
          ((gSetForgetfulPoint G).toToposPoint) S s)) =
      fun s _ ↦ s :=
  sorry

/-- Under the canonical equivalence `p^{-1}(p_* S) ≃ Map(G, S)` from Example 7.33.7, the counit
map `p^{-1}(p_* S) → S` of Lemma 7.32.9 is evaluation at `1 ∈ G`. -/
theorem gSetForgetfulPoint_pushforwardFiber_counit_eq_eval_one
    (S : Type u) :
    (fun ψ ↦
      (((gSetForgetfulPoint G).toToposPoint).typeAdjunction.counit.app S)
        ((gSetForgetfulPoint_pushforwardFiberEquiv G S).symm ψ)) =
      fun ψ ↦ ψ 1 :=
  sorry

-- Proof sketch: under the canonical identification of `p_* S` on the left regular `G`-set with
-- `Map(G, S)`, pullback along right multiplication by `g` becomes precomposition by the map
-- `x ↦ x * g`.
private theorem pushforwardRightTranslation_comm
    (S : Type u) (g : G) :
    ((sheafSectionsOnLeftRegularFunctor G).obj
        (gSetForgetfulPoint_pushforwardObj G S)).ρ g ≫
      (pushforwardLeftRegularObjEquiv G S).toIso.hom =
        (pushforwardLeftRegularObjEquiv G S).toIso.hom ≫
          (Action.ofMulAction G (G → S)).ρ g :=
  sorry

/-- After identifying sheaves on `\mathcal T_G` with `G`-sets via evaluation on the left regular
object, the pushforward `p_* S` is the right-translation `G`-set `Map(G, S)`. -/
noncomputable def gSetForgetfulPoint_pushforwardRightTranslationIso
    (S : Type u) :
    (sheafSectionsOnLeftRegularFunctor G).obj
        (((gSetForgetfulPoint G).toToposPoint).typePushforward.obj S) ≅
      Action.ofMulAction G (G → S) :=
  Action.mkIso
    (pushforwardLeftRegularObjEquiv G S).toIso
    (pushforwardRightTranslation_comm G S)

end

end CategoryTheory
