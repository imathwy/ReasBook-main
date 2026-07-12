import Mathlib
import StacksProject_2024.Chap13.Lemma_13_4_11
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Lemma_15_65_2
import StacksProject_2024.Chap15.Lemma_15_65_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ObjectProperty.IsStableUnderRetracts
open CategoryTheory.Pretriangulated
open DerivedCategory.TStructure
open scoped ZeroObject

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/-- Helper for Lemma 15.65.8: the zero cochain complex over `ModuleCat R`. -/
private abbrev zeroCpx : Cpx := 0

/-- Helper for Lemma 15.65.8: the zero cochain complex is termwise finite free. -/
private instance zero_isTermwiseFiniteFree :
    (zeroCpx (R := R)).IsTermwiseFiniteFree where
  out i := by
    let E0 : Cpx := zeroCpx (R := R)
    change Module.Free R ↥(E0.X i) ∧ Module.Finite R ↥(E0.X i)
    -- Proof comment: each degree of the chosen zero complex is a zero module, hence free by
    -- subsingleton and finite by transport from the one-point module.
    let hzero : IsZero (E0.X i) := by
      simpa [zeroCpx] using
        (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i).map_isZero
          (isZero_zero Cpx : IsZero (0 : Cpx))
    letI : Subsingleton ↥(E0.X i) :=
      ModuleCat.subsingleton_of_isZero hzero
    refine
      ⟨Module.Free.of_subsingleton (R := R) (N := ↥(E0.X i)), ?_⟩
    let e : ModuleCat.of R PUnit ≅ E0.X i :=
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit)).isoZero ≪≫ hzero.isoZero.symm
    exact Module.Finite.equiv e.toLinearEquiv

/-- Helper for Lemma 15.65.8: if all derived homology objects of `K` vanish in degrees `≥ m`,
then `K` is `m`-pseudo-coherent. -/
private theorem isMPseudoCoherent_of_derived_homology_isZero_ge
    {K : DMod} {m : ℤ}
    (hK : ∀ i : ℤ, m ≤ i → IsZero ((H i).obj K)) :
    K.IsMPseudoCoherent m := by
  let E0 : Cpx := zeroCpx (R := R)
  let α : DerivedCategory.Q.obj E0 ⟶ K := 0
  refine ⟨E0, ?_, inferInstance, α, ?_, ?_⟩
  · -- Proof comment: the zero complex is bounded on both sides by any chosen cutoff.
    exact ⟨m, m, inferInstance, inferInstance⟩
  · intro i hi
    -- Proof comment: both source and target homology vanish in degree `i`, so the zero map is an
    -- isomorphism there.
    let hsrc : IsZero ((H i).obj (DerivedCategory.Q.obj E0)) := by
      simpa [zeroCpx] using
        (H i).map_isZero
          ((DerivedCategory.Q).map_isZero (isZero_zero Cpx : IsZero (0 : Cpx)))
    let htgt : IsZero ((H i).obj K) := hK i (le_of_lt hi)
    exact hsrc.isIso htgt ((H i).map α)
  · -- Proof comment: the same zero-object argument makes the degree-`m` map an epimorphism.
    let hsrc : IsZero ((H m).obj (DerivedCategory.Q.obj E0)) := by
      simpa [zeroCpx] using
        (H m).map_isZero
          ((DerivedCategory.Q).map_isZero (isZero_zero Cpx : IsZero (0 : Cpx)))
    let htgt : IsZero ((H m).obj K) := hK m le_rfl
    letI : IsIso ((H m).map α) := hsrc.isIso htgt ((H m).map α)
    infer_instance

/-- Helper for Lemma 15.65.8: `m`-pseudo-coherence weakens as the index increases. -/
private theorem isMPseudoCoherent_of_le
    {K : DMod} {m n : ℤ} (hmn : m ≤ n)
    (hK : K.IsMPseudoCoherent m) :
    K.IsMPseudoCoherent n := by
  rcases hK with ⟨E, hbounds, hfree, α, hαgt, hαm⟩
  -- Proof comment: the same approximation works in every weaker degree because the degree-`n`
  -- map is either the original epimorphism (`n = m`) or already an isomorphism (`m < n`).
  refine ⟨E, hbounds, hfree, α, ?_, ?_⟩
  · intro i hi
    exact hαgt i (lt_of_le_of_lt hmn hi)
  · rcases eq_or_lt_of_le hmn with rfl | hmn'
    · simpa using hαm
    · letI : IsIso ((H n).map α) := hαgt n hmn'
      infer_instance

/-- Helper for Lemma 15.65.8: an `m`-pseudo-coherent object of `D(R)` is bounded above. -/
private theorem isLE_of_isMPseudoCoherent
    {K : DMod} {m : ℤ} (hK : K.IsMPseudoCoherent m) :
    ∃ b : ℤ, K.IsLE b := by
  rcases hK with ⟨E, ⟨a, b, hEa, hEb⟩, hEfree, α, hαgt, hαm⟩
  letI : E.IsStrictlyGE a := hEa
  letI : E.IsStrictlyLE b := hEb
  -- Proof comment: above the witness bound `b`, the source complex has zero cohomology, and
  -- above `m` the comparison map is an isomorphism, so `K` also has zero cohomology there.
  refine ⟨max m b, ?_⟩
  rw [DerivedCategory.isLE_iff]
  intro j hj
  have hbj : b < j := by
    omega
  have hmj : m < j := by
    omega
  have hsource : IsZero ((H j).obj (DerivedCategory.Q.obj E)) := by
    have hQ : (DerivedCategory.Q.obj E).IsLE b := by
      rw [DerivedCategory.isLE_Q_obj_iff]
      infer_instance
    let _ : (DerivedCategory.Q.obj E).IsLE b := hQ
    exact DerivedCategory.isZero_of_isLE _ b j hbj
  let eH : ((H j).obj (DerivedCategory.Q.obj E)) ≅ ((H j).obj K) := by
    let _ : IsIso ((H j).map α) := hαgt j hmj
    exact asIso ((H j).map α)
  exact eH.isZero_iff.1 hsource

/-- Helper for Lemma 15.65.8: a bounded-above object with no homology in degrees `≥ m` is
`m`-pseudo-coherent. -/
private theorem isMPseudoCoherent_of_isLE_pred
    {K : DMod} {m : ℤ} (hK : K.IsLE (m - 1)) :
    K.IsMPseudoCoherent m := by
  -- Proof comment: the `IsLE (m - 1)` bound is exactly the vanishing of homology in degrees
  -- `≥ m`, so the zero-complex witness applies directly.
  refine isMPseudoCoherent_of_derived_homology_isZero_ge ?_
  rw [DerivedCategory.isLE_iff] at hK
  intro i hi
  exact hK i (by omega)

/-- Helper for Lemma 15.65.8: an `IsLE` bound weakens when the cutoff increases. -/
private theorem isLE_of_le
    {K : DMod} {a b : ℤ} (hK : K.IsLE a) (hab : a ≤ b) :
    K.IsLE b := by
  -- Proof comment: vanishing above the smaller cutoff `a` already implies vanishing above the
  -- larger cutoff `b`.
  rw [DerivedCategory.isLE_iff] at hK ⊢
  intro i hi
  exact hK i (lt_of_le_of_lt hab hi)

/-- Helper for Lemma 15.65.8: the bounded-above condition descends to the right summand of a
binary biproduct. -/
private theorem isLE_of_biprod_right
    {K L : DMod} {b : ℤ} (hKL : (K ⊞ L).IsLE b) :
    L.IsLE b := by
  rw [DerivedCategory.isLE_iff] at hKL ⊢
  intro i hi
  let r : Retract ((H i).obj L) ((H i).obj (K ⊞ L)) :=
    ⟨(H i).map (Limits.biprod.inr : L ⟶ K ⊞ L),
      (H i).map (Limits.biprod.snd : K ⊞ L ⟶ L), by
        calc
          (H i).map (Limits.biprod.inr : L ⟶ K ⊞ L) ≫
              (H i).map (Limits.biprod.snd : K ⊞ L ⟶ L) =
              (H i).map ((Limits.biprod.inr : L ⟶ K ⊞ L) ≫ (Limits.biprod.snd : K ⊞ L ⟶ L)) := by
            simpa using (Functor.map_comp (H i)
              (Limits.biprod.inr : L ⟶ K ⊞ L) (Limits.biprod.snd : K ⊞ L ⟶ L)).symm
          _ = 𝟙 ((H i).obj L) := by
            simpa using congrArg ((H i).map) (Limits.biprod.inr_snd :
              (Limits.biprod.inr : L ⟶ K ⊞ L) ≫ (Limits.biprod.snd : K ⊞ L ⟶ L) = 𝟙 L)⟩
  -- Proof comment: a retract of a zero homology object is again zero.
  exact IsZero.of_mono r.i (hKL i hi)

/-- Helper for Lemma 15.65.8: shifting a bounded-above object by `n : ℕ` lowers the cutoff by
`n`. -/
private theorem iterated_shift_isLE_of_isLE
    {L : DMod} {b : ℤ} (n : ℕ) (hL : L.IsLE b) :
    (L⟦(n : ℤ)⟧).IsLE (b - n) := by
  rw [DerivedCategory.isLE_iff] at hL ⊢
  intro i hi
  let e := homology_shift_iso (R := R) L i (n : ℤ)
  -- Proof comment: degree-`i` homology after shifting is degree-`i + n` homology before shifting.
  exact e.isZero_iff.2 (hL (i + n) (by omega))

/-- Helper for Lemma 15.65.8: the source `L`-summand triangle from the Stacks proof is the
inverse rotation of the standard split triangle on `L` and `L⟦1⟧`. -/
private abbrev successor_pair_right_triangle (L : DMod) : Triangle DMod :=
  (binaryBiproductTriangle L (L⟦(1 : ℤ)⟧)).invRotate

/-- Helper for Lemma 15.65.8: the first vertex of the inverse-rotated `L`-triangle is canonically
isomorphic to `L`. -/
private def successor_pair_right_triangle_obj₁_iso
    (L : DMod) :
    (successor_pair_right_triangle (R := R) L).obj₁ ≅ L := by
  -- Proof comment: inverse rotation shifts the third vertex back by `-1`, and the third vertex
  -- of the split triangle is `L⟦1⟧`, so the standard shift-cancellation isomorphism applies.
  simpa [successor_pair_right_triangle, Triangle.invRotate_obj₁] using
    (shiftFunctorCompIsoId DMod (1 : ℤ) (-1 : ℤ) (by simp)).app L

/-- Helper for Lemma 15.65.8: the second vertex of the inverse-rotated `L`-triangle is `L`. -/
private theorem successor_pair_right_triangle_obj₂
    (L : DMod) :
    (successor_pair_right_triangle (R := R) L).obj₂ = L := by
  -- Proof comment: inverse rotation keeps the original first vertex as the new second vertex.
  simpa [successor_pair_right_triangle, Triangle.invRotate_obj₂] using
    (binaryBiproductTriangle_obj₁ L (L⟦(1 : ℤ)⟧))

/-- Helper for Lemma 15.65.8: the third vertex of the inverse-rotated `L`-triangle is the
successor pair `L ⊞ L⟦1⟧`. -/
private theorem successor_pair_right_triangle_obj₃
    (L : DMod) :
    (successor_pair_right_triangle (R := R) L).obj₃ = (L ⊞ L⟦(1 : ℤ)⟧) := by
  -- Proof comment: inverse rotation moves the middle term of the split triangle into the third
  -- position.
  simpa [successor_pair_right_triangle, Triangle.invRotate_obj₃] using
    (binaryBiproductTriangle_obj₂ L (L⟦(1 : ℤ)⟧))

/-- Helper for Lemma 15.65.8: the inverse-rotated `L`-triangle is distinguished. -/
private theorem successor_pair_right_triangle_distinguished
    (L : DMod) :
    successor_pair_right_triangle (R := R) L ∈ distTriang DMod := by
  -- Proof comment: this is the inverse rotation of the canonical split distinguished triangle.
  simpa [successor_pair_right_triangle] using
    (inv_rot_of_distTriang
      (binaryBiproductTriangle L (L⟦(1 : ℤ)⟧))
      (binaryBiproductTriangle_distinguished L (L⟦(1 : ℤ)⟧)))

/-- Helper for Lemma 15.65.8: if the left summand is zero, then the projection
`X ⊞ Y ⟶ Y` is an isomorphism. -/
private theorem biprod_snd_isIso_of_isZero_left
    {X Y : DMod} [HasBinaryBiproduct X Y] (hX : IsZero X) :
    IsIso (Limits.biprod.snd : X ⊞ Y ⟶ Y) := by
  have hfst_zero : (Limits.biprod.fst : X ⊞ Y ⟶ X) = 0 := by
    exact hX.eq_of_tgt _ _
  -- Proof comment: `biprod.inr` is a two-sided inverse once the left projection vanishes.
  refine ⟨⟨Limits.biprod.inr, ?_, ?_⟩⟩
  · apply Limits.biprod.hom_ext
    · simpa [Category.assoc, hfst_zero]
    · simp [Category.assoc]
  · simp

/-- Helper for Lemma 15.65.8: a binary biproduct is canonically isomorphic to the product over
the walking pair. -/
private def biprodIsoPairProduct (X Y : DMod) : X ⊞ Y ≅ ∏ᶜ pairFunction X Y := by
  let fan : Fan (pairFunction X Y) :=
    Fan.mk (X ⊞ Y) (fun j ↦ WalkingPair.casesOn j biprod.fst biprod.snd)
  let hfan : IsLimit fan := by
    refine mkFanLimit _ (fun s ↦ biprod.lift (s.proj WalkingPair.left) (s.proj WalkingPair.right))
      ?_ ?_
    · intro s j
      cases j <;> simp [fan]
    · intro s m hm
      apply BinaryFan.IsLimit.hom_ext (BinaryBiproduct.isLimit X Y)
      · simpa [fan] using hm WalkingPair.left
      · simpa [fan] using hm WalkingPair.right
  exact (limit.isoLimitCone ⟨fan, hfan⟩).symm

/-- Helper for Lemma 15.65.8: the source-faithful successor-pair product triangle combining the
contractible triangle on `K` with the split right triangle on `L`. -/
private abbrev successor_pair_contractible_product_triangle (K L : DMod) : Triangle DMod :=
  productTriangle (pairFunction (contractibleTriangle K) (successor_pair_right_triangle (R := R) L))

/-- Helper for Lemma 15.65.8: the product of the contractible `K`-triangle and the successor-pair
`L`-triangle is distinguished. -/
private theorem successor_pair_contractible_product_triangle_distinguished
    (K L : DMod) :
    successor_pair_contractible_product_triangle (R := R) K L ∈ distTriang DMod := by
  -- Proof comment: `productTriangle_distinguished` is the canonical owner for direct sums of
  -- distinguished triangles indexed by the walking pair.
  refine productTriangle_distinguished
    (pairFunction (contractibleTriangle K) (successor_pair_right_triangle (R := R) L)) ?_
  intro j
  cases j with
  | left =>
      simpa [contractibleTriangle] using contractible_distinguished K
  | right =>
      exact successor_pair_right_triangle_distinguished (R := R) L

/-- Helper for Lemma 15.65.8: the first vertex of the source-faithful product triangle is the
binary biproduct `K ⊞ L`. -/
private def successor_pair_contractible_product_triangle_obj₁_iso
    (K L : DMod) :
    K ⊞ L ≅ (successor_pair_contractible_product_triangle (R := R) K L).obj₁ := by
  -- Proof comment: the two factors in degree `1` are `K` and the first vertex of the
  -- successor-pair triangle, which is canonically `L`.
  exact biprodIsoPairProduct (R := R) K L ≪≫
    Pi.mapIso (fun j ↦ by
      cases j with
      | left =>
          exact Iso.refl K
      | right =>
          exact (successor_pair_right_triangle_obj₁_iso (R := R) L).symm)

/-- Helper for Lemma 15.65.8: the second vertex of the source-faithful product triangle is the
same binary biproduct `K ⊞ L`. -/
private def successor_pair_contractible_product_triangle_obj₂_iso
    (K L : DMod) :
    K ⊞ L ≅ (successor_pair_contractible_product_triangle (R := R) K L).obj₂ := by
  -- Proof comment: the contractible triangle contributes a second copy of `K`, while the
  -- successor-pair triangle contributes a second copy of `L`.
  exact biprodIsoPairProduct (R := R) K L ≪≫
    Pi.mapIso (fun j ↦ by
      cases j with
      | left =>
          exact Iso.refl K
      | right =>
          exact (eqToIso (successor_pair_right_triangle_obj₂ (R := R) L)).symm)

/-- Helper for Lemma 15.65.8: the third vertex of the source-faithful product triangle is the
binary biproduct `0 ⊞ (L ⊞ L⟦1⟧)`. -/
private def successor_pair_contractible_product_triangle_obj₃_iso
    (K L : DMod) :
    (0 : DMod) ⊞ (L ⊞ L⟦(1 : ℤ)⟧) ≅
      (successor_pair_contractible_product_triangle (R := R) K L).obj₃ := by
  -- Proof comment: the contractible triangle contributes the zero third vertex and the
  -- successor-pair triangle contributes `L ⊞ L⟦1⟧`.
  exact biprodIsoPairProduct (R := R) (0 : DMod) (L ⊞ L⟦(1 : ℤ)⟧) ≪≫
    Pi.mapIso (fun j ↦ by
      cases j with
      | left =>
          exact Iso.refl (0 : DMod)
      | right =>
          exact (eqToIso (successor_pair_right_triangle_obj₃ (R := R) L)).symm)

/-- Helper for Lemma 15.65.8: the split successor triangle upgrades
`(K ⊞ L).IsMPseudoCoherent m` to `(L ⊞ L⟦1⟧).IsMPseudoCoherent m`. -/
private theorem isMPseudoCoherent_successor_pair_explicit_triangle
    (K L : DMod) (m : ℤ)
    (hKL : (K ⊞ L).IsMPseudoCoherent m) :
    (L ⊞ L⟦(1 : ℤ)⟧).IsMPseudoCoherent m := by
  let T : Triangle DMod := successor_pair_contractible_product_triangle (R := R) K L
  have hT : T ∈ distTriang DMod :=
    successor_pair_contractible_product_triangle_distinguished (R := R) K L
  have h₁ : T.obj₁.IsMPseudoCoherent (m + 1) := by
    let e₁ := successor_pair_contractible_product_triangle_obj₁_iso (R := R) K L
    -- Proof comment: the first vertex is just `K ⊞ L`, viewed at the weaker index `m + 1`.
    exact isMPseudoCoherent_of_iso e₁ (m + 1)
      (isMPseudoCoherent_of_le (show m ≤ m + 1 by omega) hKL)
  have h₂ : T.obj₂.IsMPseudoCoherent m := by
    let e₂ := successor_pair_contractible_product_triangle_obj₂_iso (R := R) K L
    -- Proof comment: the second vertex is the same biproduct `K ⊞ L`.
    exact isMPseudoCoherent_of_iso e₂ m hKL
  have h₃ : T.obj₃.IsMPseudoCoherent m := by
    -- Proof comment: Lemma `15.65.2(1)` applies to the distinguished source-faithful product
    -- triangle once the first two vertices are identified with `K ⊞ L`.
    exact isMPseudoCoherent_obj₃_of_distinguishedTriangle T hT h₁ h₂
  let e₃ := successor_pair_contractible_product_triangle_obj₃_iso (R := R) K L
  have hZeroBiprod : ((0 : DMod) ⊞ (L ⊞ L⟦(1 : ℤ)⟧)).IsMPseudoCoherent m := by
    -- Proof comment: rewrite the third product vertex as `0 ⊞ (L ⊞ L⟦1⟧)`.
    exact isMPseudoCoherent_of_iso e₃.symm m h₃
  have hZero : IsZero (0 : DMod) := isZero_zero DMod
  let _ : IsIso (Limits.biprod.snd : (0 : DMod) ⊞ (L ⊞ L⟦(1 : ℤ)⟧) ⟶ (L ⊞ L⟦(1 : ℤ)⟧)) :=
    biprod_snd_isIso_of_isZero_left (R := R) hZero
  -- Proof comment: the left summand of the third vertex is zero, so the projection collapses it.
  exact isMPseudoCoherent_of_iso (asIso (Limits.biprod.snd :
    (0 : DMod) ⊞ (L ⊞ L⟦(1 : ℤ)⟧) ⟶ (L ⊞ L⟦(1 : ℤ)⟧))) m hZeroBiprod

/-- Helper for Lemma 15.65.8: one backward step along the standard split triangle recovers the
predecessor shift from a successor pair and the current shift. -/
private theorem isMPseudoCoherent_predecessor_of_pair
    (L : DMod) (k : ℕ) (m : ℤ)
    (hpair : (L⟦((k : ℤ) - 1)⟧ ⊞ L⟦(k : ℤ)⟧).IsMPseudoCoherent m)
    (hcurr : (L⟦(k : ℤ)⟧).IsMPseudoCoherent m) :
    (L⟦((k : ℤ) - 1)⟧).IsMPseudoCoherent m := by
  let T : Triangle DMod := binaryBiproductTriangle (L⟦(k : ℤ)⟧) (L⟦((k : ℤ) - 1)⟧)
  have hT : T ∈ distTriang DMod := binaryBiproductTriangle_distinguished _ _
  have h₁ : T.obj₁.IsMPseudoCoherent (m + 1) := by
    -- Proof comment: the first vertex is the already-known current shift, viewed at the weaker
    -- index `m + 1`.
    simpa [T, binaryBiproductTriangle] using
      isMPseudoCoherent_of_le (show m ≤ m + 1 by omega) hcurr
  have h₂ : T.obj₂.IsMPseudoCoherent m := by
    -- Proof comment: swap the biproduct summands so the source pair matches the canonical split
    -- triangle orientation.
    simpa [T, binaryBiproductTriangle] using
      isMPseudoCoherent_of_iso
        (Limits.biprod.braiding (L⟦((k : ℤ) - 1)⟧) (L⟦(k : ℤ)⟧)) m hpair
  -- Proof comment: Lemma `15.65.2(1)` now descends one step in the reverse induction.
  simpa [T, binaryBiproductTriangle] using
    isMPseudoCoherent_obj₃_of_distinguishedTriangle T hT h₁ h₂

/-- Helper for Lemma 15.65.8: the target of a retract is isomorphic to a biproduct whose right
summand is the retract source. -/
private theorem retract_target_iso_biprod_right
    {X Y : DMod} (r : Retract X Y) :
    ∃ C : DMod, Nonempty (Y ≅ C ⊞ X) := by
  obtain ⟨C, i, h, hT⟩ := distinguished_cocone_triangle₁ r.r
  letI : IsSplitEpi r.r := IsSplitEpi.mk' { section_ := r.i, id := r.retract }
  have hzero : h = 0 := by
    exact Triangle.mor₃_eq_zero_of_epi₂ _ hT (inferInstance : Epi r.r)
  -- Proof comment: the split-triangle theorem identifies the retract map with the standard
  -- projection from a binary biproduct.
  obtain ⟨e, _, _⟩ := exists_iso_binaryBiproduct_of_distTriang (Triangle.mk i r.r h) hT hzero
  exact ⟨C, ⟨e⟩⟩

/-- Helper for Lemma 15.65.8: pseudo-coherence is invariant under isomorphism in `D(R)`. -/
private theorem isPseudoCoherent_of_iso
    {K L : DMod} (e : K ≅ L) (hK : K.IsPseudoCoherent) :
    L.IsPseudoCoherent := by
  rcases hK with ⟨E, hEbounded, hEfree, α, hα⟩
  -- Proof comment: keep the same bounded-above finite-free model and compose its comparison map
  -- with the target isomorphism.
  refine ⟨E, hEbounded, hEfree, α ≫ e.hom, ?_⟩
  simpa using (show IsIso (α ≫ e.hom) by infer_instance)

/-- Helper for Lemma 15.65.8: a derived complex is pseudo-coherent exactly when it is
`m`-pseudo-coherent for every integer `m`. -/
private theorem isPseudoCoherent_iff_forall_isMPseudoCoherent_local
    (K : DMod) :
    K.IsPseudoCoherent ↔ ∀ m : ℤ, K.IsMPseudoCoherent m := by
  -- TODO(Lemma 15.65.8): re-express the cochain-level TFAE through a universe-stable
  -- representative API. The direct `Q.objPreimage` route no longer elaborates robustly here.
  sorry

/-- Helper for Lemma 15.65.8: if `K ⊞ L` is `m`-pseudo-coherent, then the right summand `L` is
`m`-pseudo-coherent. -/
private theorem isMPseudoCoherent_right_of_biprod_aux
    (K L : DMod) (m : ℤ)
    (hKL : (K ⊞ L).IsMPseudoCoherent m) :
    L.IsMPseudoCoherent m := by
  obtain ⟨b, hBiprodLE⟩ := isLE_of_isMPseudoCoherent hKL
  have hLLE : L.IsLE b := isLE_of_biprod_right hBiprodLE
  let N : ℕ := Int.toNat (b - m) + 1
  have hShiftLE_raw : (L⟦(N : ℤ)⟧).IsLE (b - N) :=
    iterated_shift_isLE_of_isLE N hLLE
  have hBound : b - N ≤ m - 1 := by
    -- Proof comment: this choice of `N` pushes the upper bound strictly below `m`.
    by_cases hbm : m ≤ b
    · rw [show (N : ℤ) = b - m + 1 by
          dsimp [N]
          rw [Int.toNat_of_nonneg (sub_nonneg.mpr hbm)]]
      omega
    · have hlt : b < m := lt_of_not_ge hbm
      have hNone : (N : ℤ) = 1 := by
        dsimp [N]
        rw [Int.toNat_of_nonpos (by omega)]
        norm_num
      omega
  have hShiftLE : (L⟦(N : ℤ)⟧).IsLE (m - 1) :=
    isLE_of_le hShiftLE_raw hBound
  have hBase : (L⟦(N : ℤ)⟧).IsMPseudoCoherent m :=
    isMPseudoCoherent_of_isLE_pred hShiftLE
  have hPair :
      ∀ n : ℕ, (L⟦(n : ℤ)⟧ ⊞ L⟦((n : ℤ) + 1)⟧).IsMPseudoCoherent m := by
    intro n
    induction n with
    | zero =>
        -- Proof comment: this is exactly the first split-successor step from the source proof.
        let eZero :
            (L ⊞ L⟦(1 : ℤ)⟧) ≅ (L⟦(0 : ℤ)⟧ ⊞ L⟦(1 : ℤ)⟧) :=
          Limits.biprod.mapIso ((shiftFunctorZero DMod ℤ).app L).symm (Iso.refl _)
        simpa using isMPseudoCoherent_of_iso eZero m
          (isMPseudoCoherent_successor_pair_explicit_triangle K L m hKL)
    | succ n ih =>
        have hsucc :
            (L⟦((n : ℤ) + 1)⟧ ⊞ L⟦((n : ℤ) + 1)⟧⟦(1 : ℤ)⟧).IsMPseudoCoherent m :=
          isMPseudoCoherent_successor_pair_explicit_triangle
            (L⟦(n : ℤ)⟧) (L⟦((n : ℤ) + 1)⟧) m ih
        let eShift :
            (L⟦((n : ℤ) + 1)⟧ ⊞ L⟦((n : ℤ) + 1)⟧⟦(1 : ℤ)⟧) ≅
              (L⟦((n : ℤ) + 1)⟧ ⊞ L⟦((n : ℤ) + 2)⟧) :=
          Limits.biprod.mapIso (Iso.refl _) (((shiftFunctorAdd DMod ((n : ℤ) + 1) 1).app L).symm)
        -- Proof comment: rewrite the nested shift on the second summand into the next single
        -- shift so the pair family keeps the source indexing.
        simpa [Nat.cast_add, add_assoc] using isMPseudoCoherent_of_iso eShift m hsucc
  have hDesc :
      ∀ j : ℕ, j ≤ N → (L⟦((N - j : ℕ) : ℤ)⟧).IsMPseudoCoherent m := by
    intro j hj
    induction j with
    | zero =>
        simpa [N] using hBase
    | succ j ih =>
        have hj' : j ≤ N := Nat.le_of_succ_le hj
        have hCurr : (L⟦((N - j : ℕ) : ℤ)⟧).IsMPseudoCoherent m := ih hj'
        have hstep : N - (j + 1) + 1 = N - j := by omega
        have hidx₁ : (((N - (j + 1) : ℕ) : ℤ)) = (((N - j : ℕ) : ℤ) - 1) := by
          omega
        have hidx₂ : (((N - (j + 1) : ℕ) : ℤ) + 1) = (((N - j : ℕ) : ℤ)) := by
          omega
        have hPairStep :
            (L⟦(((N - j : ℕ) : ℤ) - 1)⟧ ⊞ L⟦((N - j : ℕ) : ℤ)⟧).IsMPseudoCoherent m := by
          simpa [hidx₁, hidx₂] using
            hPair (N - (j + 1))
        -- Proof comment: descend from `L[N - j]` to `L[N - j - 1]` using the corresponding
        -- successor pair and the fixed split triangle.
        simpa [hidx₁] using
          isMPseudoCoherent_predecessor_of_pair L (N - j) m hPairStep hCurr
  have hFinal :
      (L⟦(0 : ℤ)⟧).IsMPseudoCoherent m := by
    simpa using hDesc N le_rfl
  let eZero : (L⟦(0 : ℤ)⟧) ≅ L := (shiftFunctorZero DMod ℤ).app L
  exact isMPseudoCoherent_of_iso eZero m hFinal

/- Domain-style sampling for Lemma 15.65.8:
- primary domain: pseudo-coherence as an object property on `D(R)`, together with the generic
  retract/direct-summand API for additive categories;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`,
  `ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_left`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_right`;
- best owner abstraction: the `core/canonical` layer is the object property
  `fun K : DMod ↦ K.IsMPseudoCoherent m` and its pseudo-coherent analogue; the source-facing
  biproduct statements are thin `bridge/view` specializations of the generic direct-summand API;
- primitive vs. derived:
  primitive data are the owner predicates `K.IsMPseudoCoherent m` and `K.IsPseudoCoherent`;
  derived API is retract stability and the left/right biproduct consequences.
-/

/-- `m`-pseudo-coherent objects of `D(R)` are stable under retracts/direct summands. -/
-- Proof sketch: if `K` is a retract of `L`, then `L ≅ K ⊞ K'` for some complement `K'`. Apply
-- the biproduct argument from the Stacks proof, using the distinguished triangle attached to the
-- projection `K ⊞ K' ⟶ K` together with Lemmas `15.65.2` and `15.65.7`.
instance isMPseudoCoherent_isStableUnderRetracts (m : ℤ) :
    ObjectProperty.IsStableUnderRetracts (fun K : DMod ↦ K.IsMPseudoCoherent m) where
  of_retract {X} {Y} h hK := by
    -- Proof comment: reduce the retract to a direct-summand statement using the standard split
    -- triangle on the retraction map.
    obtain ⟨C, ⟨e⟩⟩ := retract_target_iso_biprod_right h
    have hBiprod : (C ⊞ X).IsMPseudoCoherent m := by
      exact isMPseudoCoherent_of_iso e m hK
    exact isMPseudoCoherent_right_of_biprod_aux C X m hBiprod

/-- Pseudo-coherent objects of `D(R)` are stable under retracts/direct summands. -/
-- Proof sketch: combine Lemma `15.65.5`, which characterizes pseudo-coherence by
-- `m`-pseudo-coherence for every `m`, with the retract-stability instance above applied degreewise.
instance isPseudoCoherent_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts (fun K : DMod ↦ K.IsPseudoCoherent) where
  of_retract h hK := by
    -- Proof comment: apply the fixed-degree retract stability result for every `m`, then package
    -- the resulting family back into pseudo-coherence via the local `∀ m` characterization.
    rw [isPseudoCoherent_iff_forall_isMPseudoCoherent_local] at hK ⊢
    intro m
    exact prop_of_retract (fun K : DMod ↦ K.IsMPseudoCoherent m) h (hK m)

/-- Lemma 15.65.8 (1): if `K ⊞ L` is `m`-pseudo-coherent in `D(R)`, then `K` is
`m`-pseudo-coherent. -/
theorem isMPseudoCoherent_left_of_biprod
    (K L : DMod) (m : ℤ)
    (hKL : (K ⊞ L).IsMPseudoCoherent m) :
    K.IsMPseudoCoherent m :=
  of_biprod_left (fun X : DMod ↦ X.IsMPseudoCoherent m) hKL

/-- Lemma 15.65.8 (2): if `K ⊞ L` is `m`-pseudo-coherent in `D(R)`, then `L` is
`m`-pseudo-coherent. -/
theorem isMPseudoCoherent_right_of_biprod
    (K L : DMod) (m : ℤ)
    (hKL : (K ⊞ L).IsMPseudoCoherent m) :
    L.IsMPseudoCoherent m :=
  of_biprod_right (fun X : DMod ↦ X.IsMPseudoCoherent m) hKL

/-- Lemma 15.65.8 (3): if `K ⊞ L` is pseudo-coherent in `D(R)`, then `K` is pseudo-coherent. -/
theorem isPseudoCoherent_left_of_biprod
    (K L : DMod)
    (hKL : (K ⊞ L).IsPseudoCoherent) :
    K.IsPseudoCoherent :=
  of_biprod_left (fun X : DMod ↦ X.IsPseudoCoherent) hKL

/-- Lemma 15.65.8 (4): if `K ⊞ L` is pseudo-coherent in `D(R)`, then `L` is pseudo-coherent. -/
theorem isPseudoCoherent_right_of_biprod
    (K L : DMod)
    (hKL : (K ⊞ L).IsPseudoCoherent) :
    L.IsPseudoCoherent :=
  of_biprod_right (fun X : DMod ↦ X.IsPseudoCoherent) hKL

end

end CategoryTheory
