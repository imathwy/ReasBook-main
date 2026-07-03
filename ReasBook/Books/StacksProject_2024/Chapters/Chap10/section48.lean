import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_48_1 (from Chap10) -/
open scoped TensorProduct
open Algebra.TensorProduct
open AlgebraicGeometry CommRingCat
open Topology

namespace Algebra

universe u

section

variable {k R S : Type u}
variable [Field k] [IsSepClosed k] [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]

-- Proof sketch: first reinterpret connectedness of `Spec R` and `Spec S` as geometric
-- connectedness over the separably closed field `k` using Lemma `10.48.4`; then apply the
-- connected-components bijection induced by tensoring with a geometrically connected algebra from
-- Lemma `10.48.6`, and conclude that `Spec (R ⊗[k] S)` has a single connected component.
/-- Lemma 10.48.1 (Tag 037R): over a separably algebraically closed field `k`, if `Spec R` and
`Spec S` are connected, then `Spec (R ⊗[k] S)` is connected. This is stated in the canonical
prime-spectrum form. -/
@[stacks 037R]
theorem Lemma_10_48_1
    (hR : ConnectedSpace (PrimeSpectrum R))
    (hS : ConnectedSpace (PrimeSpectrum S)) :
    ConnectedSpace (PrimeSpectrum (R ⊗[k] S)) := by
  letI : ConnectedSpace (PrimeSpectrum R) := hR
  have hgeomS :
      geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k S))) :=
    geometricallyConnected_iff_connectedSpace_primeSpectrum_of_isSepClosed.2 hS
  let e :
      ConnectedComponents (PrimeSpectrum (R ⊗[k] S)) →
        ConnectedComponents (PrimeSpectrum R) :=
    (PrimeSpectrum.continuous_comap (includeLeft : R →ₐ[k] R ⊗[k] S)).connectedComponentsMap
  have hbij : Function.Bijective e := (Lemma_10_48_6 hgeomS).2
  letI : Subsingleton (ConnectedComponents (PrimeSpectrum (R ⊗[k] S))) :=
    hbij.injective.subsingleton
  have hnonempty : Nonempty (PrimeSpectrum (R ⊗[k] S)) := by
    exact ConnectedComponents.nonempty_iff_nonempty.mp hbij.surjective.nonempty
  letI : Nonempty (PrimeSpectrum (R ⊗[k] S)) := hnonempty
  rw [connectedSpace_iff_connectedComponent]
  refine ⟨Classical.choice hnonempty, Set.eq_univ_of_forall fun y ↦ ?_⟩
  exact ConnectedComponents.coe_eq_coe'.mp <| Subsingleton.elim _ _

end

end Algebra

/-! ### Lemma_10_48_2 (from Chap10) -/
open scoped TensorProduct
open AlgebraicGeometry CommRingCat

namespace Algebra

universe u

section

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]

-- Proof sketch: the forward implication is immediate. For the converse, pass to
-- `SeparableClosure k`, use the idempotent criterion for connectedness together with the
-- finite-subalgebra detection of idempotents after tensor product, and then compare an arbitrary
-- base change with a common overfield containing both it and `SeparableClosure k`.
/-- Source-facing companion to Lemma 10.48.2: it suffices to test connectedness of
`Spec (R ⊗[k] K)` on finite separable field extensions `K / k`. -/
theorem connectedSpace_primeSpectrum_baseChange_iff_finiteSeparable_baseChange :
    (∀ (K : Type u) [Field K] [Algebra k K], ConnectedSpace (PrimeSpectrum (R ⊗[k] K))) ↔
      ∀ (K : Type u) [Field K] [Algebra k K]
        [FiniteDimensional k K] [Algebra.IsSeparable k K],
        ConnectedSpace (PrimeSpectrum (R ⊗[k] K)) := sorry

/-- Lemma 10.48.2 (Tag 037S): a `k`-algebra is geometrically connected iff it remains connected
after every finite separable base change. -/
@[stacks 037S]
theorem Lemma_10_48_2 :
    geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k R))) ↔
      ∀ (K : Type u) [Field K] [Algebra k K]
        [FiniteDimensional k K] [Algebra.IsSeparable k K],
        ConnectedSpace (PrimeSpectrum (R ⊗[k] K)) := by
  rw [geometricallyConnected_iff_connectedSpace_primeSpectrum_baseChange]
  exact connectedSpace_primeSpectrum_baseChange_iff_finiteSeparable_baseChange

end

end Algebra

/-! ### Definition_10_48_3 (from Chap10) -/
open scoped TensorProduct
open CategoryTheory Limits
open AlgebraicGeometry CommRingCat

namespace Algebra

universe u

section

variable {k S : Type u} [Field k] [CommRing S] [Algebra k S]

/- Definition 10.48.3 (Tag 037T): the canonical scheme-theoretic notion of a geometrically
connected `k`-algebra `S` is that the affine morphism `Spec S ⟶ Spec k` is geometrically
connected, namely
`geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k S)))`.
-/
#check (geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k S))))

private theorem connectedSpace_of_iso {X Y : Scheme} (e : X ≅ Y) [ConnectedSpace X] :
    ConnectedSpace Y := by
  let e' := Scheme.homeoOfIso e
  exact e'.surjective.connectedSpace e'.continuous

local instance :
    ObjectProperty.IsClosedUnderIsomorphisms
      (ConnectedSpace · : CategoryTheory.ObjectProperty Scheme) := by
  exact ⟨fun {X Y} e h ↦ by
    letI : ConnectedSpace ↥X := h
    exact connectedSpace_of_iso e⟩

/-- Prime-spectrum form of the base-change criterion from Definition 10.48.3. -/
@[stacks 037T]
theorem geometricallyConnected_iff_connectedSpace_primeSpectrum_baseChange :
    geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k S))) ↔
      ∀ (K : Type u) [Field K] [Algebra k K], ConnectedSpace (PrimeSpectrum (S ⊗[k] K)) := by
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  constructor
  · intro h K _ _
    letI :
        ConnectedSpace
          ↥(pullback (Spec.map (ofHom (algebraMap k S))) (Spec.map (ofHom (algebraMap k K)))) :=
      h K
    simpa using connectedSpace_of_iso (pullbackSpecIso k S K)
  · intro h K _ _
    letI : ConnectedSpace (Spec (of (S ⊗[k] K))) := by
      simpa using h K
    simpa using connectedSpace_of_iso (pullbackSpecIso k S K).symm

end

section

variable {k : Type u} [Field k]

/-- A field is geometrically connected over itself. -/
instance : geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k k))) := by
  rw [geometricallyConnected_iff_connectedSpace_primeSpectrum_baseChange]
  intro K _ _
  let e : k ⊗[k] K ≃ₐ[k] K := Algebra.TensorProduct.lid k K
  letI : IsDomain (k ⊗[k] K) := MulEquiv.isDomain _ e.toMulEquiv
  infer_instance

end

end Algebra

/-! ### Lemma_10_48_4 (from Chap10) -/
open scoped TensorProduct
open Algebra.TensorProduct
open AlgebraicGeometry CommRingCat

namespace Algebra

universe u

section

variable {k R : Type u} [Field k] [IsSepClosed k] [CommRing R] [Algebra k R]

-- Proof sketch: use the remark after Definition 10.48.3 together with
-- Lemma `10.48.2`; over a separably closed field every finite separable extension is already
-- `k`, so every relevant base change is canonically isomorphic to `R`.
/-- Lemma 10.48.4: if `k` is separably algebraically closed, then a `k`-algebra `R` is
geometrically connected over `k` if and only if `Spec R` is connected. -/
theorem geometricallyConnected_iff_connectedSpace_primeSpectrum_of_isSepClosed :
    geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k R))) ↔
      ConnectedSpace (PrimeSpectrum R) := by
  rw [Lemma_10_48_2]
  have baseChange_iff (K : Type u) [Field K] [Algebra k K]
      [FiniteDimensional k K] [Algebra.IsSeparable k K] :
      ConnectedSpace (PrimeSpectrum (R ⊗[k] K)) ↔ ConnectedSpace (PrimeSpectrum R) := by
    let eK : K ≃ₐ[k] k :=
      (AlgEquiv.ofBijective (Algebra.ofId k K)
        ⟨(algebraMap k K).injective, IsSepClosed.algebraMap_surjective k K⟩).symm
    let e : R ⊗[k] K ≃ₐ[R] R :=
      (TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) eK).trans (TensorProduct.rid k R R)
    let eSpec : PrimeSpectrum (R ⊗[k] K) ≃ₜ PrimeSpectrum R :=
      PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv
    constructor
    · intro hRK
      letI : ConnectedSpace (PrimeSpectrum (R ⊗[k] K)) := hRK
      have hsurj : Function.Surjective eSpec := eSpec.surjective
      exact hsurj.connectedSpace eSpec.continuous
    · intro hR
      letI : ConnectedSpace (PrimeSpectrum R) := hR
      have hsurj : Function.Surjective eSpec.symm := eSpec.symm.surjective
      exact hsurj.connectedSpace eSpec.symm.continuous
  constructor
  · intro h
    simpa using (baseChange_iff k).1 (h k)
  · intro h K _ _ _ _
    exact (baseChange_iff K).2 h

end

end Algebra

/-! ### Lemma_10_48_5 (from Chap10) -/
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

/-! ### Lemma_10_48_6 (from Chap10) -/
open scoped TensorProduct
open Algebra.TensorProduct
open AlgebraicGeometry CommRingCat
open TopologicalSpace

universe u

namespace Algebra

local notation "Idempotents" R => {e : R // IsIdempotentElem e}

section

variable {k R S : Type u}
variable [Field k] [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]

/-- Helper for Lemma 10.48.6: a connected prime spectrum is nonempty, so the ring is nontrivial. -/
private theorem nontrivial_of_connected_primeSpectrum {A : Type u} [CommRing A]
    (hA : ConnectedSpace (PrimeSpectrum A)) : Nontrivial A := by
  -- Connected spaces are nonempty, and `Spec(A)` is nonempty exactly when `A` is nontrivial.
  letI : ConnectedSpace (PrimeSpectrum A) := hA
  exact PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance

/-- Helper for Lemma 10.48.6: connectedness transports across a homeomorphism. -/
private theorem connectedSpace_of_homeomorph {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) [ConnectedSpace X] : ConnectedSpace Y :=
  e.surjective.connectedSpace e.continuous

/-- Helper for Lemma 10.48.6: every fiber of `Spec(R ⊗[k] S) → Spec(R)` is connected when `S` is
geometrically connected over `k`. -/
private theorem tensorProduct_fiber_connected_of_geometricallyConnected
    (hgeom : geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k S))))
    (p : PrimeSpectrum R) :
    IsConnected
      ((PrimeSpectrum.comap (algebraMap R (R ⊗[k] S))) ⁻¹' ({p} : Set (PrimeSpectrum R))) := by
  -- Rewrite geometric connectedness into connectedness after residue-field base change.
  rw [geometricallyConnected_iff_connectedSpace_primeSpectrum_baseChange] at hgeom
  have hbase' : ConnectedSpace (PrimeSpectrum (S ⊗[k] p.asIdeal.ResidueField)) :=
    hgeom p.asIdeal.ResidueField
  have hbase : ConnectedSpace (PrimeSpectrum (p.asIdeal.ResidueField ⊗[k] S)) := by
    -- Commute the two tensor factors to match the standard fiber comparison.
    let e :
        PrimeSpectrum (S ⊗[k] p.asIdeal.ResidueField) ≃ₜ
          PrimeSpectrum (p.asIdeal.ResidueField ⊗[k] S) :=
      PrimeSpectrum.homeomorphOfRingEquiv
        (Algebra.TensorProduct.comm k S p.asIdeal.ResidueField).toRingEquiv
    letI : ConnectedSpace (PrimeSpectrum (S ⊗[k] p.asIdeal.ResidueField)) := hbase'
    exact connectedSpace_of_homeomorph e
  have hfiber :
      ConnectedSpace (PrimeSpectrum (p.asIdeal.Fiber (R ⊗[k] S))) := by
    -- The standard base-change comparison identifies the fiber ring with `κ(p) ⊗[k] S`.
    let e :
        PrimeSpectrum (p.asIdeal.Fiber (R ⊗[k] S)) ≃ₜ
          PrimeSpectrum (p.asIdeal.ResidueField ⊗[k] S) :=
      PrimeSpectrum.homeomorphOfRingEquiv
        ((Algebra.TensorProduct.cancelBaseChange
          k R R p.asIdeal.ResidueField S).toRingEquiv)
    letI : ConnectedSpace (PrimeSpectrum (p.asIdeal.ResidueField ⊗[k] S)) := hbase
    exact connectedSpace_of_homeomorph e.symm
  -- Transport connectedness back across the canonical homeomorphism describing the fiber.
  have hpreimage :
      ConnectedSpace
        (((PrimeSpectrum.comap (algebraMap R (R ⊗[k] S))) ⁻¹'
          ({p} : Set (PrimeSpectrum R)))) := by
    let e :=
      (PrimeSpectrum.preimageHomeomorphFiber R (R ⊗[k] S) p).symm
    letI : ConnectedSpace (PrimeSpectrum (p.asIdeal.Fiber (R ⊗[k] S))) := hfiber
    exact connectedSpace_of_homeomorph e
  simpa [isConnected_iff_connectedSpace] using
    hpreimage

/-- Helper for Lemma 10.48.6: the projection `Spec(R ⊗[k] S) → Spec(R)` induces a bijection on
connected components. -/
private theorem connectedComponentsMap_bijective_tensorProduct_includeLeft
    (hgeom : geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k S)))) :
    Function.Bijective
      ((PrimeSpectrum.continuous_comap (algebraMap R (R ⊗[k] S))).connectedComponentsMap :
        ConnectedComponents (PrimeSpectrum (R ⊗[k] S)) →
          ConnectedComponents (PrimeSpectrum R)) := by
  -- The tensor-product projection is open over a field, so the connected-fiber criterion applies.
  refine connectedComponents_bijective_of_isOpenMap_of_connectedFibers
    (PrimeSpectrum.continuous_comap (algebraMap R (R ⊗[k] S)))
    (PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field :
      IsOpenMap (PrimeSpectrum.comap (algebraMap R (R ⊗[k] S))))
    ?_
  intro p
  simpa using tensorProduct_fiber_connected_of_geometricallyConnected
    (k := k) (R := R) (S := S) hgeom p

/-- Helper for Lemma 10.48.6: under an open map with connected fibers, a clopen subset is exactly
the full preimage of its image, and that image is again clopen. -/
private theorem isClopen_image_of_isClopen_of_connectedFibers
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hopen : IsOpenMap f) (hfibers : ∀ y : Y, IsConnected (f ⁻¹' ({y} : Set Y)))
    {U : Set X} (hU : IsClopen U) :
    IsClopen (f '' U) ∧ f ⁻¹' (f '' U) = U := by
  have hpre : f ⁻¹' (f '' U) = U := by
    -- A fiber meeting a clopen set lies entirely inside that clopen set.
    ext x
    constructor
    · rintro ⟨u, huU, hxu⟩
      have huFiber : u ∈ f ⁻¹' ({f x} : Set Y) := by
        simpa [Set.mem_singleton_iff] using hxu
      have hxFiber : x ∈ f ⁻¹' ({f x} : Set Y) := by
        simp
      have huComp : u ∈ connectedComponent x :=
        (hfibers (f x)).subset_connectedComponent hxFiber huFiber
      have hxComp : x ∈ connectedComponent u := by
        simpa [connectedComponent_eq huComp] using mem_connectedComponent (x := x)
      exact hU.connectedComponent_subset huU hxComp
    · intro hx
      exact ⟨x, hx, rfl⟩
  have himage_compl : (f '' U)ᶜ = f '' Uᶜ := by
    -- Every point of `Y` has a connected nonempty fiber, so it lands in exactly one image.
    ext y
    constructor
    · intro hy
      obtain ⟨x, hxFiber⟩ := (hfibers y).nonempty
      have hxy : f x = y := by
        simpa using hxFiber
      by_cases hx : x ∈ U
      · exact False.elim (hy ⟨x, hx, hxy⟩)
      · exact ⟨x, hx, hxy⟩
    · rintro ⟨x, hxUc, rfl⟩ hy
      have hxPre : x ∈ f ⁻¹' (f '' U) := hy
      exact hxUc (by simpa [hpre] using hxPre)
  have hclosed : IsClosed (f '' U) := by
    -- The complement is the open image of the complementary clopen subset.
    refine (isOpen_compl_iff).mp ?_
    rw [himage_compl]
    exact hopen _ hU.1.isOpen_compl
  constructor
  · exact ⟨hclosed, hopen _ hU.2⟩
  · exact hpre

/-- Lemma 10.48.6 (Tag 037W): if `k` is a field, `S` is geometrically connected over `k`, and `R`
is any `k`-algebra, then the canonical map `R → R ⊗[k] S` induces bijections both on idempotents
and on connected components of prime spectra. -/
@[stacks 037W]
theorem Lemma_10_48_6
    (hgeom : geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k S)))) :
    Function.Bijective
      (fun e : Idempotents R ↦
        (⟨includeLeft e.1, e.2.map (includeLeft : R →ₐ[k] R ⊗[k] S)⟩ :
          Idempotents (R ⊗[k] S))) ∧
      Function.Bijective
        ((PrimeSpectrum.continuous_comap (includeLeft : R →ₐ[k] R ⊗[k] S)).connectedComponentsMap :
          ConnectedComponents (PrimeSpectrum (R ⊗[k] S)) →
            ConnectedComponents (PrimeSpectrum R)) :=
  by
    -- The source proof is governed by the tensor-product projection on spectra: first control its
    -- fibers and connected components, then read idempotents through clopen subsets.
    let f : PrimeSpectrum (R ⊗[k] S) → PrimeSpectrum R :=
      PrimeSpectrum.comap (algebraMap R (R ⊗[k] S))
    have hfibers : ∀ p : PrimeSpectrum R, IsConnected (f ⁻¹' ({p} : Set (PrimeSpectrum R))) := by
      intro p
      simpa [f] using tensorProduct_fiber_connected_of_geometricallyConnected
        (k := k) (R := R) (S := S) hgeom p
    have hcomp :
        Function.Bijective
          ((PrimeSpectrum.continuous_comap (algebraMap R (R ⊗[k] S))).connectedComponentsMap :
            ConnectedComponents (PrimeSpectrum (R ⊗[k] S)) →
              ConnectedComponents (PrimeSpectrum R)) :=
      connectedComponentsMap_bijective_tensorProduct_includeLeft
        (k := k) (R := R) (S := S) hgeom
    have hSbase : ConnectedSpace (PrimeSpectrum (S ⊗[k] k)) := by
      -- Evaluate geometric connectedness at the ground field to force nontriviality of `S`.
      rw [geometricallyConnected_iff_connectedSpace_primeSpectrum_baseChange] at hgeom
      exact hgeom k
    let eS := Algebra.TensorProduct.rid k S S
    letI : Nontrivial (S ⊗[k] k) := nontrivial_of_connected_primeSpectrum hSbase
    letI : Nontrivial S := eS.injective.nontrivial
    have hleft_injective :
        Function.Injective (includeLeft : R →ₐ[k] R ⊗[k] S) :=
      Algebra.TensorProduct.includeLeft_injective (algebraMap k S).injective
    constructor
    · constructor
      · -- Injectivity on idempotents follows from injectivity of `includeLeft`.
        intro e₁ e₂ h
        apply Subtype.ext
        exact hleft_injective (congrArg Subtype.val h)
      · intro e
        let U : Clopens (PrimeSpectrum (R ⊗[k] S)) :=
          PrimeSpectrum.isIdempotentElemEquivClopens e
        have himage :
            IsClopen (f '' (U : Set (PrimeSpectrum (R ⊗[k] S)))) ∧
              f ⁻¹' (f '' (U : Set (PrimeSpectrum (R ⊗[k] S)))) =
                (U : Set (PrimeSpectrum (R ⊗[k] S))) :=
          isClopen_image_of_isClopen_of_connectedFibers
            (X := PrimeSpectrum (R ⊗[k] S)) (Y := PrimeSpectrum R) (f := f)
            (PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field :
              IsOpenMap (PrimeSpectrum.comap (algebraMap R (R ⊗[k] S))))
            hfibers U.2
        let V : Clopens (PrimeSpectrum R) :=
          ⟨f '' (U : Set (PrimeSpectrum (R ⊗[k] S))), himage.1⟩
        let r : Idempotents R := PrimeSpectrum.isIdempotentElemEquivClopens.symm V
        have hVbasic : (V : Set (PrimeSpectrum R)) = PrimeSpectrum.basicOpen r.1 := by
          -- The chosen idempotent `r` is exactly the clopen subset `V`.
          calc
            (V : Set (PrimeSpectrum R)) =
                (PrimeSpectrum.isIdempotentElemEquivClopens r : Set (PrimeSpectrum R)) := by
                  simp [r]
            _ = PrimeSpectrum.basicOpen r.1 :=
                  PrimeSpectrum.coe_isIdempotentElemEquivClopens_apply r
        refine ⟨r, ?_⟩
        -- Compare the associated clopen subsets and use injectivity of the idempotent/clopen
        -- equivalence.
        apply PrimeSpectrum.isIdempotentElemEquivClopens.injective
        ext q
        change q ∈ PrimeSpectrum.basicOpen ((includeLeft : R →ₐ[k] R ⊗[k] S) r.1) ↔ q ∈ U
        calc
          q ∈ PrimeSpectrum.basicOpen ((includeLeft : R →ₐ[k] R ⊗[k] S) r.1)
              ↔ q ∈ f ⁻¹' (PrimeSpectrum.basicOpen r.1 : Set (PrimeSpectrum R)) := by
                  rfl
          _ ↔ q ∈ f ⁻¹' ((V : Set (PrimeSpectrum R))) := by
                rw [hVbasic]
          _ ↔ q ∈ f ⁻¹' (f '' (U : Set (PrimeSpectrum (R ⊗[k] S)))) := by
                rfl
          _ ↔ q ∈ U := by
                simpa [himage.2]
    · change Function.Bijective
          ((PrimeSpectrum.continuous_comap (algebraMap R (R ⊗[k] S))).connectedComponentsMap :
            ConnectedComponents (PrimeSpectrum (R ⊗[k] S)) →
              ConnectedComponents (PrimeSpectrum R))
      exact hcomp

end

end Algebra
