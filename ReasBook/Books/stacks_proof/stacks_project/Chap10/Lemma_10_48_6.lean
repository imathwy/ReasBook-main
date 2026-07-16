import Mathlib
import stacks_proof.stacks_project.Chap05.Lemma_5_7_6
import stacks_proof.stacks_project.Chap10.Definition_10_48_3

-- Declarations for this item will be appended below by the statement pipeline.

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
