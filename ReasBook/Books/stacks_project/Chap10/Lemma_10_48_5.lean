import Mathlib
import stacks_project.Chap10.Definition_10_48_3
import stacks_project.Chap10.Lemma_10_21_4
import stacks_project.Chap10.Lemma_10_43_4
import stacks_project.Chap10.Lemma_10_127_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open CategoryTheory Limits
open Algebra.TensorProduct
open AlgebraicGeometry CommRingCat

universe u

namespace Algebra

section

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]

/-- Helper for Lemma 10.48.5: a connected prime spectrum is nonempty, so the ring is nontrivial. -/
private theorem nontrivial_of_connected_primeSpectrum {R : Type u} [CommRing R]
    (hR : ConnectedSpace (PrimeSpectrum R)) : Nontrivial R := by
  -- Connected spaces are nonempty, and `Spec R` is nonempty exactly for nontrivial rings.
  letI : ConnectedSpace (PrimeSpectrum R) := hR
  exact PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance

/-- Geometric connectedness descends along injective algebra morphisms. -/
-- Proof sketch: after any field extension of `k`, tensoring with that field preserves injectivity.
-- Then triviality of idempotents descends along the induced tensor-product map.
private theorem geometricallyConnected_of_injective {B : Type u} [CommRing B] [Algebra k B]
    (f : B →ₐ[k] A) (hf : Function.Injective f) :
    geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k A))) →
      geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k B))) := by
  intro hA
  rw [geometricallyConnected_iff_connectedSpace_primeSpectrum_baseChange] at hA ⊢
  intro K _ _
  -- After base change to `K`, the tensor-product map stays injective.
  let g : B ⊗[k] K →ₐ[k] A ⊗[k] K :=
    Algebra.TensorProduct.map f (AlgHom.id k K)
  have hg : Function.Injective g := by
    simpa [g] using TensorProduct.map_injective_of_flat_flat
      f.toLinearMap (AlgHom.id k K).toLinearMap hf (AlgHom.id k K).injective
  have hAK : ConnectedSpace (PrimeSpectrum (A ⊗[k] K)) := hA K
  letI : Nontrivial (A ⊗[k] K) := nontrivial_of_connected_primeSpectrum hAK
  letI : Nontrivial (B ⊗[k] K) := RingHom.domain_nontrivial g.toRingHom
  -- Use the idempotent criterion on both tensor products and pull triviality back along `g`.
  refine (primeSpectrum_connectedSpace_iff_idempotents_trivial (R := B ⊗[k] K)).2 ?_
  intro e he
  have htrivA :
      ∀ a : A ⊗[k] K, IsIdempotentElem a → a = 0 ∨ a = 1 :=
    (primeSpectrum_connectedSpace_iff_idempotents_trivial (R := A ⊗[k] K)).1 hAK
  rcases htrivA (g e) (he.map g) with hzero | hone
  · left
    exact hg <| by simpa [g] using hzero
  · right
    exact hg <| by simpa [g] using hone

/-- Lemma 10.48.5 (1): every `k`-subalgebra of a geometrically connected `k`-algebra is
geometrically connected over `k`. -/
-- Proof sketch: apply `geometricallyConnected_of_injective` to the inclusion of the subalgebra.
theorem geometricallyConnected_subalgebra (S : Subalgebra k A) :
    geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k A))) →
      geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k S))) :=
  geometricallyConnected_of_injective S.val Subtype.val_injective

/-- Lemma 10.48.5 (2): if all finitely generated `k`-subalgebras of `A` are geometrically
connected over `k`, then `A` is geometrically connected over `k`. -/
-- Route correction: first use the bottom subalgebra to force `A` itself to be nontrivial. Then
-- descend a hypothetical nontrivial idempotent to a finite tensor stage via Lemma `10.43.4`, and
-- map that finite stage into the ambient base-changed algebra `T.left ⊗[k] K`.
theorem geometricallyConnected_of_forall_fg
    (h : ∀ S : Subalgebra k A, S.FG →
      geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k S)))) :
    geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k A))) := by
  rw [geometricallyConnected_iff_connectedSpace_primeSpectrum_baseChange]
  intro K _ _
  by_contra hK
  have hbot :
      geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k (⊥ : Subalgebra k A)))) :=
    h ⊥ Subalgebra.fg_bot
  rw [geometricallyConnected_iff_connectedSpace_primeSpectrum_baseChange] at hbot
  have hbotk : ConnectedSpace (PrimeSpectrum ((⊥ : Subalgebra k A) ⊗[k] k)) := hbot k
  letI : Nontrivial ((⊥ : Subalgebra k A) ⊗[k] k) := nontrivial_of_connected_primeSpectrum hbotk
  let ebot : ((⊥ : Subalgebra k A) ⊗[k] k) ≃ (⊥ : Subalgebra k A) :=
    (Algebra.TensorProduct.rid k (⊥ : Subalgebra k A) (⊥ : Subalgebra k A)).toEquiv
  letI : Nontrivial (⊥ : Subalgebra k A) := ebot.injective.nontrivial
  have hbot_inj : Function.Injective ((⊥ : Subalgebra k A).val) := Subtype.val_injective
  letI : Nontrivial A := hbot_inj.nontrivial
  letI : Nontrivial (A ⊗[k] K) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left
      (R := k) (A := A) (B := K) (algebraMap k K).injective
  -- Failure of connectedness produces a nontrivial idempotent after base change.
  have hnot_trivial_idempotents :
      ¬ ∀ e : A ⊗[k] K, IsIdempotentElem e → e = 0 ∨ e = 1 := by
    intro htriv
    exact hK ((primeSpectrum_connectedSpace_iff_idempotents_trivial (R := A ⊗[k] K)).2 htriv)
  classical
  push Not at hnot_trivial_idempotents
  rcases hnot_trivial_idempotents with ⟨e, he, he0, he1⟩
  have hwitness : Nonempty (NontrivialIdempotentWitness (A ⊗[k] K)) := by
    exact ⟨{ elem := e, isIdempotent := he, ne_zero := he0, ne_one := he1 }⟩
  obtain ⟨T, ⟨w⟩⟩ :=
    exists_fg_subalgebras_tensorProduct_has_nontrivial_idempotent
      (k := k) (R := A) (S := K) hwitness
  let j : T.right →ₐ[k] K := T.right.val
  let g : T.left ⊗[k] T.right →ₐ[k] T.left ⊗[k] K :=
    Algebra.TensorProduct.map (AlgHom.id k T.left) j
  have hg : Function.Injective g := by
    -- Tensoring with the ambient field `K` preserves injectivity of the right-hand inclusion.
    simpa [g, j] using TensorProduct.map_injective_of_flat_flat
      (AlgHom.id k T.left).toLinearMap j.toLinearMap
      Function.injective_id Subtype.val_injective
  have hTK : ConnectedSpace (PrimeSpectrum (T.left ⊗[k] K)) := by
    -- The left-hand finite stage is geometrically connected by hypothesis, so its `K`-base change
    -- is connected.
    have hT : geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k T.left))) :=
      h T.left T.left_fg
    rw [geometricallyConnected_iff_connectedSpace_primeSpectrum_baseChange] at hT
    exact hT K
  letI : Nontrivial (T.left ⊗[k] K) := nontrivial_of_connected_primeSpectrum hTK
  -- The mapped idempotent must be trivial in the connected `K`-base change, contradicting
  -- injectivity of `g`.
  have htrivK :
      ∀ x : T.left ⊗[k] K, IsIdempotentElem x → x = 0 ∨ x = 1 :=
    (primeSpectrum_connectedSpace_iff_idempotents_trivial (R := T.left ⊗[k] K)).1 hTK
  rcases htrivK (g w.elem) (w.isIdempotent.map g) with hzero | hone
  · exact w.ne_zero (hg <| by simpa [g] using hzero)
  · exact w.ne_one (hg <| by simpa [g] using hone)

end

section

variable {k I : Type u} [Field k] [Preorder I] [IsDirectedOrder I]

/-- Lemma 10.48.5 (3): a directed colimit of geometrically connected `k`-algebras is
geometrically connected over `k`. -/
-- Proof sketch: in the nonempty case, every finitely generated subalgebra of the colimit factors
-- through one stage by the same finite-presentation/coyoneda argument as in Lemma `10.43.2`, and
-- then part `(1)` descends geometric connectedness from that stage. In the empty case the colimit
-- is the initial `k`-algebra `k`.
theorem geometricallyConnected_colimit_of_directedSystem
    (F : I ⥤ CommAlgCat k)
    (hF : ∀ i,
      geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k (F.obj i))))) :
    geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k (colimit F : CommAlgCat k)))) := by
  by_cases hI : Nonempty I
  · letI : Nonempty I := hI
    letI : IsFiltered I := inferInstance
    -- Reduce to finitely generated subalgebras of the colimit.
    apply geometricallyConnected_of_forall_fg
    intro T hT
    let E := commAlgCatEquivUnder (CommRingCat.of k)
    let G : I ⥤ Under (CommRingCat.of k) := F ⋙ E.functor
    let c : Cocone G := E.functor.mapCocone (colimit.cocone F)
    have hc : IsColimit c := isColimitOfPreserves E.functor (colimit.isColimit F)
    have hfp : (algebraMap k T).FinitePresentation := by
      -- A finitely generated algebra over a field is finitely presented.
      simpa [RingHom.finitePresentation_algebraMap] using
        (Algebra.FinitePresentation.of_finiteType).mp ((Subalgebra.fg_iff_finiteType T).mp hT)
    have hpres :
        PreservesFilteredColimits
          (CategoryTheory.coyoneda.obj (.op (CommRingCat.mkUnder (CommRingCat.of k) T))) := by
      -- This is exactly the owner theorem from the finite-presentation criterion.
      simpa using
        CommRingCat.preservesFilteredColimits_coyoneda
          (CommRingCat.of k) (CommRingCat.mkUnder (CommRingCat.of k) T) hfp
    let g : CommRingCat.mkUnder (CommRingCat.of k) T ⟶ c.pt := T.val.toUnder
    obtain ⟨i, g', hg⟩ :=
      factorsThroughStage_of_preservesFilteredColimits_coyoneda
        (algebraMap k T) hpres G c hc g
    let g'' :
        CommRingCat.mkUnder (CommRingCat.of k) T ⟶
          CommRingCat.mkUnder (CommRingCat.of k) (F.obj i) := by
      simpa [G, E] using g'
    let ιi : CommRingCat.mkUnder (CommRingCat.of k) (F.obj i) ⟶ c.pt := by
      simpa [G, E] using c.ι.app i
    have hg' : g = g'' ≫ ιi := by
      dsimp [g'', ιi]
      simpa [g, G, E] using hg
    have hφcomm :
        ∀ x : k,
          ((CommRingCat.Hom.hom g''.right).comp (algebraMap k T)) x =
            (algebraMap k (F.obj i)) x := by
      intro x
      have hw := CommRingCat.hom_ext_iff.mp (Under.w g'')
      change ((CommRingCat.Hom.hom g''.right).comp (algebraMap k T)) x =
        (algebraMap k (F.obj i)) x
      simpa [CommRingCat.mkUnder_hom, CommRingCat.hom_comp] using DFunLike.congr_fun hw x
    let φ : T →ₐ[k] F.obj i :=
      { __ := g''.right.hom
        commutes' := hφcomm }
    have hfac (x : T) : ιi.right (φ x) = T.val x := by
      have hw := CommRingCat.hom_ext_iff.mp (congrArg (fun f ↦ f.right) hg')
      simpa [g, φ, CommRingCat.hom_comp] using (DFunLike.congr_fun hw x).symm
    have hφ : Function.Injective φ := by
      intro x y hxy
      exact Subtype.ext <| by
        change T.val x = T.val y
        rw [← hfac x, ← hfac y, hxy]
    -- Part `(1)` now descends geometric connectedness from the chosen stage.
    exact geometricallyConnected_of_injective φ hφ (hF i)
  · letI : IsEmpty I := not_nonempty_iff.mp hI
    have hcolim : IsInitial (colimit F : CommAlgCat.{u} k) :=
      (isColimitEquivIsInitialOfIsEmpty (CommAlgCat.{u} k) (colimit.cocone F))
        (colimit.isColimit F)
    have hself : IsInitial (CommAlgCat.of k k) := CommAlgCat.isInitialSelf
    let e : (colimit F : CommAlgCat.{u} k) ≅ CommAlgCat.of k k :=
      hcolim.coconePointUniqueUpToIso hself
    let e' : (colimit F : CommAlgCat.{u} k) ≃ₐ[k] CommAlgCat.of k k :=
      CommAlgCat.algEquivOfIso e
    -- The initial `k`-algebra is `k` itself, which is geometrically connected.
    have hk :
        geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k (CommAlgCat.of k k)))) := by
      rw [geometricallyConnected_iff_connectedSpace_primeSpectrum_baseChange]
      intro K _ _
      let e : k ⊗[k] K ≃ₐ[k] K := Algebra.TensorProduct.lid k K
      letI : IsDomain (k ⊗[k] K) := MulEquiv.isDomain _ e.toMulEquiv
      infer_instance
    exact geometricallyConnected_of_injective e'.toAlgHom e'.injective hk

end

end Algebra
