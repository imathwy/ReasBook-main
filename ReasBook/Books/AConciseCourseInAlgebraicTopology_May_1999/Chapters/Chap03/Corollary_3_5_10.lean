import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_3_11
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_4_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_5_9
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Lemma_3_4_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Theorem_3_5_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v u₁ u₂

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory
open scoped QuotientGroup

namespace CategoryTheory.Functor.IsCovering

variable {E B : Type u} [Groupoid.{v} E] [Groupoid.{v} B]
variable {p : E ⥤ B}

noncomputable section

/-- The induced map on the fiber over `p.obj e` coming from a covering automorphism is bijective. -/
-- Proof sketch: the inverse automorphism of `α` induces the inverse fiber map, and the two
-- composites are identities because `α.hom ≫ α.inv = 𝟙 _` and `α.inv ≫ α.hom = 𝟙 _`.
private theorem coveringAutFiberMap_bijective (e : E)
    (α : CoveringAut p) :
    Function.Bijective
      (mapOfCoveringsToFiberFun (p.obj e) α.hom) := by
  let f := mapOfCoveringsToFiberFun (p.obj e) α.hom
  let g := mapOfCoveringsToFiberFun (p.obj e) α.inv
  have hleft : Function.LeftInverse g f := by
    intro x
    have hcomp : g ∘ f = id := by
      -- Restricting `α.hom ≫ α.inv = 𝟙` to the fiber gives a left inverse.
      calc
        g ∘ f = mapOfCoveringsToFiberFun (p.obj e) (α.hom ≫ α.inv) := by
          symm
          exact mapOfCoveringsToFiberFun_comp (p.obj e) α.hom α.inv
        _ = mapOfCoveringsToFiberFun (p.obj e) (𝟙 (Over.mk p.toCatHom)) := by
          rw [α.hom_inv_id]
        _ = id := mapOfCoveringsToFiberFun_id (p.obj e)
    simpa [f, g, Function.comp] using congrFun hcomp x
  have hright : Function.RightInverse g f := by
    intro x
    have hcomp : f ∘ g = id := by
      -- Restricting `α.inv ≫ α.hom = 𝟙` to the fiber gives a right inverse.
      calc
        f ∘ g = mapOfCoveringsToFiberFun (p.obj e) (α.inv ≫ α.hom) := by
          symm
          exact mapOfCoveringsToFiberFun_comp (p.obj e) α.inv α.hom
        _ = mapOfCoveringsToFiberFun (p.obj e) (𝟙 (Over.mk p.toCatHom)) := by
          rw [α.inv_hom_id]
        _ = id := mapOfCoveringsToFiberFun_id (p.obj e)
    simpa [f, g, Function.comp] using congrFun hcomp x
  exact ⟨hleft.injective, hright.surjective⟩

/-- The permutation of the fiber over `p.obj e` induced by a covering automorphism. -/
private noncomputable def coveringAutFiberPerm (e : E)
    (α : CoveringAut p) : Equiv.Perm (p.Fiber (p.obj e)) :=
  Equiv.ofBijective
    (mapOfCoveringsToFiberFun (p.obj e) α.hom)
    (coveringAutFiberMap_bijective e α)

/-- The permutation induced on the fiber by a covering automorphism is equivariant for the
fiber-translation `π(B, p.obj e)`-action. -/
-- Proof sketch: `mapOfCoveringsToFiberFun_comm` gives the required commutation relation with the
-- canonical fiber-translation action, and `mem_gSetAut_iff` expresses this equivariance as
-- membership in `gSetAut`.
private theorem coveringAutFiberPerm_mem_gSetAut (hp : Functor.IsCovering p) (e : E)
    (α : CoveringAut p) :
    letI := fiberTranslationMulAction hp (p.obj e)
    coveringAutFiberPerm e α ∈ gSetAut (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) := by
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  rw [mem_gSetAut_iff]
  intro γ x
  -- The pointwise equivariance relation is exactly Theorem 3.5.8 on the fiber map.
  simpa [coveringAutFiberPerm] using
    mapOfCoveringsToFiberFun_comm hp hp (p.obj e) α.hom γ x

/-- The permutation induced by the identity covering automorphism is the identity on the fiber. -/
-- Proof sketch: unfold `coveringAutFiberPerm` and use that the identity morphism of
-- `Over.mk p.toCatHom` restricts to the identity map on every fiber.
private theorem coveringAutFiberPerm_one (e : E) :
    coveringAutFiberPerm e (1 : CoveringAut p) = 1 := by
  ext x
  -- The identity over-morphism restricts to the identity on the fiber.
  change mapOfCoveringsToFiberFun (p.obj e) (𝟙 (Over.mk p.toCatHom)) x = x
  simp [mapOfCoveringsToFiberFun_id]

/-- The permutation induced on the fiber is multiplicative in the covering automorphism. -/
-- Proof sketch: restriction to the fiber respects composition of maps of coverings, so the
-- permutation attached to `α * β` is the composite of the permutations attached to `α` and `β`.
private theorem coveringAutFiberPerm_mul (e : E)
    (α β : CoveringAut p) :
    coveringAutFiberPerm e (α * β) = coveringAutFiberPerm e α * coveringAutFiberPerm e β := by
  ext x
  -- Restriction to the fiber respects composition of covering automorphisms.
  change mapOfCoveringsToFiberFun (p.obj e) ((α * β).hom) x =
    mapOfCoveringsToFiberFun (p.obj e) α.hom (mapOfCoveringsToFiberFun (p.obj e) β.hom x)
  rw [show (α * β).hom = β.hom ≫ α.hom by rfl]
  simpa [Function.comp] using
    congrFun (mapOfCoveringsToFiberFun_comp (p.obj e) β.hom α.hom) x

/-- Automorphisms of the fiber over `p.obj e` as the canonical `π(B, p.obj e)`-set. -/
noncomputable abbrev FiberAut (hp : Functor.IsCovering p) (e : E) :=
  letI := fiberTranslationMulAction hp (p.obj e)
  Aut_ (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e))

/-- The canonical homomorphism from covering automorphisms to automorphisms of the fiber as a
`π(B, p.obj e)`-set. -/
noncomputable def coveringAutToFiberAutHom (hp : Functor.IsCovering p) (e : E) :
    CoveringAut p →* FiberAut hp e :=
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  ((autMulEquivGSetAut (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e))).symm.toMonoidHom).comp
    { toFun := fun α ↦
        ⟨coveringAutFiberPerm e α, coveringAutFiberPerm_mem_gSetAut hp e α⟩
      map_one' := Subtype.ext (coveringAutFiberPerm_one e)
      map_mul' := fun α β ↦ Subtype.ext (coveringAutFiberPerm_mul e α β) }

/-- The canonical homomorphism acts on the fiber by restricting the underlying covering
automorphism. -/
@[simp] theorem coveringAutToFiberAutHom_hom_apply (hp : Functor.IsCovering p) (e : E)
    (α : CoveringAut p) (x : p.Fiber (p.obj e)) :
    (coveringAutToFiberAutHom hp e α).hom.hom x =
      mapOfCoveringsToFiberFun (p.obj e) α.hom x := by
  rfl

/-- The canonical homomorphism from covering automorphisms to `G`-set automorphisms of the fiber
is bijective when the total groupoid is connected. -/
-- Proof sketch: Theorem 3.5.8 identifies all endomorphisms of the covering with equivariant
-- endomorphisms of the fiber. Restricting to invertible endomorphisms on both sides gives
-- bijectivity on the corresponding automorphism groups.
private theorem coveringAutToFiberAutHom_bijective [IsConnected E]
    (hp : Functor.IsCovering p) (e : E) :
    Function.Bijective (coveringAutToFiberAutHom hp e) := by
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  constructor
  · intro α β hαβ
    apply Iso.ext
    apply (mapOfCoveringsToFiber_bijective hp hp (p.obj e)).1
    apply MulActionHom.ext
    intro x
    have hx :
        (coveringAutToFiberAutHom hp e α).hom.hom x =
          (coveringAutToFiberAutHom hp e β).hom.hom x := by
      simpa using
        congrArg
          (fun φ : FiberAut hp e ↦ φ.hom.hom x)
          hαβ
    -- Equality of fiber automorphisms gives equality of the restricted covering maps.
    simpa [coveringAutToFiberAutHom, coveringAutFiberPerm, mapOfCoveringsToFiber] using hx
  · intro φ
    -- Route correction: lift the inverse fiber automorphism through Theorem 3.5.8 instead of
    -- rebuilding the Weyl-group argument directly.
    have hφ_hom_smul :
        ∀ (γ : p.obj e ⟶ p.obj e) (x : p.Fiber (p.obj e)),
          φ.hom.hom (γ • x) = γ • (show p.Fiber (p.obj e) from φ.hom.hom x) := by
      intro γ x
      -- The forward automorphism of the fiber is equivariant by definition.
      simpa [Action.ofMulAction_apply] using congrFun (φ.hom.comm γ) x
    let φhom : p.Fiber (p.obj e) →[(p.obj e ⟶ p.obj e)] p.Fiber (p.obj e) :=
      { toFun := φ.hom.hom
        map_smul' := hφ_hom_smul }
    have hφ_inv_smul :
        ∀ (γ : p.obj e ⟶ p.obj e) (x : p.Fiber (p.obj e)),
          φ.inv.hom (γ • x) = γ • (show p.Fiber (p.obj e) from φ.inv.hom x) := by
      intro γ x
      -- The inverse automorphism is equivariant for the same fiber action.
      simpa [Action.ofMulAction_apply] using congrFun (φ.inv.comm γ) x
    let φinv : p.Fiber (p.obj e) →[(p.obj e ⟶ p.obj e)] p.Fiber (p.obj e) :=
      { toFun := φ.inv.hom
        map_smul' := hφ_inv_smul }
    obtain ⟨h, hh⟩ := (mapOfCoveringsToFiber_bijective hp hp (p.obj e)).2 φhom
    obtain ⟨i, hi⟩ := (mapOfCoveringsToFiber_bijective hp hp (p.obj e)).2 φinv
    have hh_apply (x : p.Fiber (p.obj e)) :
        mapOfCoveringsToFiberFun (p.obj e) h x = φ.hom.hom x := by
      -- The lifted morphism `h` restricts to the given equivariant automorphism `φ.hom`.
      simpa [mapOfCoveringsToFiber] using
        congrArg
          (fun ψ : p.Fiber (p.obj e) →[(p.obj e ⟶ p.obj e)] p.Fiber (p.obj e) ↦ ψ x)
          hh
    have hi_apply (x : p.Fiber (p.obj e)) :
        mapOfCoveringsToFiberFun (p.obj e) i x = φ.inv.hom x := by
      -- Likewise, `i` restricts to the inverse equivariant automorphism `φ.inv.hom`.
      simpa [mapOfCoveringsToFiber] using
        congrArg
          (fun ψ : p.Fiber (p.obj e) →[(p.obj e ⟶ p.obj e)] p.Fiber (p.obj e) ↦ ψ x)
          hi
    have hhi : h ≫ i = 𝟙 (Over.mk p.toCatHom) := by
      apply (mapOfCoveringsToFiber_bijective hp hp (p.obj e)).1
      apply MulActionHom.ext
      intro x
      -- The lifted maps compose to the identity because `φ.hom` and `φ.inv.hom` are inverse.
      have hcompose :
          mapOfCoveringsToFiberFun (p.obj e) (h ≫ i) x =
            φ.inv.hom (φ.hom.hom x) := by
        calc
          mapOfCoveringsToFiberFun (p.obj e) (h ≫ i) x =
              mapOfCoveringsToFiberFun (p.obj e) i (mapOfCoveringsToFiberFun (p.obj e) h x) := by
                simpa [Function.comp] using
                  congrFun (mapOfCoveringsToFiberFun_comp (p.obj e) h i) x
          _ = φ.inv.hom (φ.hom.hom x) := by
                rw [hh_apply x, hi_apply (φ.hom.hom x)]
      have hidentity : φ.inv.hom (φ.hom.hom x) = x := by
        simpa [Function.comp] using congrFun (Action.hom_inv_hom φ) x
      exact hcompose.trans hidentity
    have hih : i ≫ h = 𝟙 (Over.mk p.toCatHom) := by
      apply (mapOfCoveringsToFiber_bijective hp hp (p.obj e)).1
      apply MulActionHom.ext
      intro x
      -- The opposite composite is also the identity because `φ.inv.hom` and `φ.hom` are inverse.
      have hcompose :
          mapOfCoveringsToFiberFun (p.obj e) (i ≫ h) x =
            φ.hom.hom (φ.inv.hom x) := by
        calc
          mapOfCoveringsToFiberFun (p.obj e) (i ≫ h) x =
              mapOfCoveringsToFiberFun (p.obj e) h (mapOfCoveringsToFiberFun (p.obj e) i x) := by
                simpa [Function.comp] using
                  congrFun (mapOfCoveringsToFiberFun_comp (p.obj e) i h) x
          _ = φ.hom.hom (φ.inv.hom x) := by
                rw [hi_apply x, hh_apply (φ.inv.hom x)]
      have hidentity : φ.hom.hom (φ.inv.hom x) = x := by
        simpa [Function.comp] using congrFun (Action.inv_hom_hom φ) x
      exact hcompose.trans hidentity
    have hIso : IsIso h := IsIso.mk ⟨i, hhi, hih⟩
    refine ⟨asIso h, ?_⟩
    ext x
    -- The reconstructed covering automorphism acts on the fiber as the original automorphism `φ`.
    simpa [coveringAutToFiberAutHom, coveringAutFiberPerm, mapOfCoveringsToFiber,
      CategoryTheory.asIso_hom, φhom] using hh_apply x

/-- Corollary 3.5.10 (1): for a connected covering functor `p : E ⥤ B`, the automorphism group
of the covering is canonically isomorphic to the automorphism group of the fiber over `p.obj e`
as a `π(B, p.obj e)`-set. -/
noncomputable def coveringAutMulEquivFiberAut [IsConnected E]
    (hp : Functor.IsCovering p) (e : E) :
    CoveringAut p ≃* FiberAut hp e :=
  MulEquiv.ofBijective
    (coveringAutToFiberAutHom hp e)
    (coveringAutToFiberAutHom_bijective hp e)

/-- Evaluating the first clause agrees with the canonical homomorphism
`coveringAutToFiberAutHom`. -/
-- Proof sketch: unfold `coveringAutMulEquivFiberAut`; `MulEquiv.ofBijective` keeps the same
-- underlying function.
theorem coveringAutMulEquivFiberAut_apply [IsConnected E]
    (hp : Functor.IsCovering p) (e : E) (α : CoveringAut p) :
    coveringAutMulEquivFiberAut hp e α = coveringAutToFiberAutHom hp e α := rfl

/-- The first clause is realized by the canonical homomorphism
`coveringAutToFiberAutHom`. -/
@[simp] theorem coveringAutMulEquivFiberAut_toMonoidHom [IsConnected E]
    (hp : Functor.IsCovering p) (e : E) :
    (coveringAutMulEquivFiberAut hp e).toMonoidHom = coveringAutToFiberAutHom hp e := rfl

/-- The automorphism group of the fiber-translation action is canonically identified with the Weyl
group of the image subgroup `p(π(E, e)) ≤ π(B, p.obj e)`. -/
noncomputable def fiberAutMulEquivWeylGroupMapVertexGroupRange [IsConnected E]
    (hp : Functor.IsCovering p) (e : E) :
    FiberAut hp e ≃*
      Subgroup.weylGroup ((Functor.mapVertexGroup p e).range) :=
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  letI : MulAction.IsPretransitive (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction_isPretransitive hp (p.obj e)
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  let eW :
      Subgroup.weylGroup (MulAction.stabilizer (p.obj e ⟶ p.obj e) x₀) ≃*
        Aut_ (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    weylGroup_stabilizer_mulEquiv_aut x₀
  (eW.symm).trans
    (MulEquiv.cast (fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e))

/-- Corollary 3.5.10 (2): for a connected covering functor, the automorphism group of the
covering is canonically isomorphic to the Weyl group of the image subgroup
`p(π(E, e)) ≤ π(B, p.obj e)`. -/
noncomputable def coveringAutMulEquivWeylGroupMapVertexGroupRange
    [IsConnected E] (hp : Functor.IsCovering p) (e : E) :
    CoveringAut p ≃* Subgroup.weylGroup ((Functor.mapVertexGroup p e).range) :=
  (coveringAutMulEquivFiberAut hp e).trans
    (fiberAutMulEquivWeylGroupMapVertexGroupRange hp e)

/-- Evaluating the second clause identifies a covering automorphism with its induced Weyl-group
class through the fiber `π(B, p.obj e)`-set. -/
-- Proof sketch: unfold `coveringAutMulEquivWeylGroupMapVertexGroupRange`; the value is the
-- composite of the fiber-action equivalence and the bundled fiber-action Weyl-group bridge.
theorem coveringAutMulEquivWeylGroupMapVertexGroupRange_apply
    [IsConnected E] (hp : Functor.IsCovering p) (e : E)
    (α : CoveringAut p) :
    coveringAutMulEquivWeylGroupMapVertexGroupRange hp e α =
      fiberAutMulEquivWeylGroupMapVertexGroupRange hp e
        (coveringAutMulEquivFiberAut hp e α) := rfl

/-- Corollary 3.5.10 (3): for a connected regular covering functor, the automorphism group of the
covering is canonically isomorphic to the quotient `π(B, p.obj e) / p(π(E, e))`. -/
noncomputable def regularCoveringAutMulEquivQuotientMapVertexGroupRange
    [IsConnected E] (e : E) [hp : Functor.IsRegularCovering p e] :
    CoveringAut p ≃* ((p.obj e ⟶ p.obj e) ⧸ (Functor.mapVertexGroup p e).range) :=
  (coveringAutMulEquivWeylGroupMapVertexGroupRange
    hp.isCovering e).trans
    (Subgroup.weylGroupMulEquivQuotientOfNormal ((Functor.mapVertexGroup p e).range))

/-- Evaluating the third clause factors through the Weyl-group description and then the quotient
by the normal image subgroup. -/
-- Proof sketch: unfold
-- `regularCoveringAutMulEquivQuotientMapVertexGroupRange`; its value is the application of
-- `weylGroupMulEquivQuotientOfNormal` to the Weyl-group class from the second clause.
theorem regularCoveringAutMulEquivQuotientMapVertexGroupRange_apply
    [IsConnected E] (e : E) [hp : Functor.IsRegularCovering p e]
    (α : CoveringAut p) :
    regularCoveringAutMulEquivQuotientMapVertexGroupRange e α =
      Subgroup.weylGroupMulEquivQuotientOfNormal ((Functor.mapVertexGroup p e).range)
        (coveringAutMulEquivWeylGroupMapVertexGroupRange
          hp.isCovering e α) := rfl

/-- Corollary 3.5.10 (4): for a connected universal covering functor, the automorphism group of
the covering is canonically isomorphic to `π(B, p.obj e)`. -/
noncomputable def universalCoveringAutMulEquivVertexGroup
    [IsConnected E] (e : E) [hp : Functor.IsUniversalCovering p e] :
    CoveringAut p ≃* (p.obj e ⟶ p.obj e) :=
  (regularCoveringAutMulEquivQuotientMapVertexGroupRange e).trans
    ((QuotientGroup.quotientMulEquivOfEq
      (hp.mapVertexGroup_range_eq_bot)).trans
      QuotientGroup.quotientBot)

/-- Evaluating the fourth clause specializes the quotient description along the equality
`p(π(E, e)) = ⊥`. -/
-- Proof sketch: unfold `universalCoveringAutMulEquivVertexGroup`; its value is the regular-case
-- quotient class, followed by the quotient identifications for the trivial subgroup.
theorem universalCoveringAutMulEquivVertexGroup_apply
    [IsConnected E] (e : E) [hp : Functor.IsUniversalCovering p e]
    (α : CoveringAut p) :
    universalCoveringAutMulEquivVertexGroup e α =
      QuotientGroup.quotientBot
        ((QuotientGroup.quotientMulEquivOfEq
          (hp.mapVertexGroup_range_eq_bot))
          (regularCoveringAutMulEquivQuotientMapVertexGroupRange e
            α)) := rfl

end

end CategoryTheory.Functor.IsCovering
