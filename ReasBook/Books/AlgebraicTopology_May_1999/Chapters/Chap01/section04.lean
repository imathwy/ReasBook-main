import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_4_1 (from Chap01) -/
universe u v

open Path.Homotopic.Quotient

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {x₀ x₁ : X}

/- Definition 1.4.1: a continuous map `p : X → Y` induces a map on loop classes, hence on
`π₁(X, x) = Path.Homotopic.Quotient x x`, by sending the class `[f]` to the class `[p ∘ f]`. -/
recall map (γ : Path.Homotopic.Quotient x₀ x₁) (f : C(X, Y)) :
    Path.Homotopic.Quotient (f x₀) (f x₁)

/-! ### Lemma_1_4_2 (from Chap01) -/
universe u v w

noncomputable section

open scoped ContinuousMap

variable {X : Type u} [TopologicalSpace X]
variable {Y : Type v} [TopologicalSpace Y]
variable {Z : Type w} [TopologicalSpace Z]

/-- Lemma 1.4.2 (1): the map on fundamental groups induced by the identity map is the identity
homomorphism. -/
-- Proof sketch: every loop class is represented by a loop `p : Path x x`, and both sides send the
-- class of `p` to itself by definition.
theorem fundamental_group_map_id (x : X) :
    FundamentalGroup.map (.id X) x = MonoidHom.id (FundamentalGroup X x) := by
  ext γ
  refine Quotient.inductionOn γ ?_
  intro p
  rfl

/-- Lemma 1.4.2 (2): the map on fundamental groups induced by a composite `q ∘ p` is the
composite of the induced homomorphisms `q_*` and `p_*`. -/
-- Proof sketch: on a representative loop `r : Path x x`, both sides are definitionally the class
-- of the composite path map `(q ∘ p) ∘ r`.
theorem fundamental_group_map_comp (p : C(X, Y)) (q : C(Y, Z)) (x : X) :
    FundamentalGroup.map (q.comp p) x =
      (FundamentalGroup.map q (p x)).comp (FundamentalGroup.map p x) := by
  ext γ
  refine Quotient.inductionOn γ ?_
  intro r
  rfl

/-! ### Definition_1_4_3 (from Chap01) -/
universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/- Definition 1.4.3: for a homotopy `H : p.Homotopy q` and a basepoint `x : X`, the basepoint
track is the path `H.evalAt x : Path (p x) (q x)` obtained by following the point `x` through the
homotopy, namely `t ↦ H (t, x)`. -/
recall ContinuousMap.Homotopy.evalAt {p q : C(X, Y)} (H : p.Homotopy q) (x : X) :
    Path (p x) (q x)

/- Evaluating a homotopy track at time `t` gives the value of the homotopy at `(t, x)`. -/
recall ContinuousMap.Homotopy.evalAt_apply {p q : C(X, Y)} (H : p.Homotopy q) (x : X)
    (t : ↑unitInterval) :
    (H.evalAt x) t = H (t, x)

/-! ### Proposition_1_4_4 (from Chap01) -/
universe u v

noncomputable section

open CategoryTheory FundamentalGroupoidFunctor
open scoped ContinuousMap
open scoped FundamentalGroup

variable {X : Type u} [TopologicalSpace X]
variable {Y : Type v} [TopologicalSpace Y]

/-- Proposition 1.4.4: if `H : p.Homotopy q`, then the induced maps on fundamental groups commute
with basepoint change along the track `H.evalAt x`, so `γ[H.evalAt x] ∘ p_* = q_*`. -/
-- Proof sketch: use the natural isomorphism on fundamental groupoids induced by a homotopy,
-- evaluate its naturality square at the object `x`, and read the resulting equality on
-- endomorphism groups as conjugation by the path `H.evalAt x`.
theorem fundamental_group_map_homotopy_commutes (p q : C(X, Y)) (H : p.Homotopy q) (x : X) :
    ((γ[H.evalAt x]).toMonoidHom.comp (FundamentalGroup.map p x)) =
      FundamentalGroup.map q x := by
  let e : FundamentalGroupoid.mk (p x) ≅ FundamentalGroupoid.mk (q x) :=
    (Groupoid.isoEquivHom _ _).symm ⟦H.evalAt x⟧
  ext α
  change e.conj ((FundamentalGroupoid.map p).map α) = (FundamentalGroupoid.map q).map α
  have hnat :
      (FundamentalGroupoid.map p).map α ≫ e.hom =
        e.hom ≫ (FundamentalGroupoid.map q).map α := by
    simpa [e, FundamentalGroupoidFunctor.homotopicMapsNatIso] using
      NatTrans.naturality (homotopicMapsNatIso H) α
  have hconj :
      (FundamentalGroupoid.map q).map α =
        e.inv ≫ ((FundamentalGroupoid.map p).map α ≫ e.hom) :=
    (e.eq_inv_comp).2 hnat.symm
  simpa [Iso.conj_apply, Category.assoc] using hconj.symm
