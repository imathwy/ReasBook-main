import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_43_1 (from Chap10) -/
open AlgebraicGeometry CategoryTheory Limits CommRingCat
open scoped TensorProduct

/- Definition 10.43.1 (Tag 030S): the canonical notion of a geometrically reduced `k`-algebra is
`Algebra.IsGeometricallyReduced`. -/
recall Algebra.IsGeometricallyReduced

namespace Algebra

universe u v

local instance :
    ObjectProperty.IsClosedUnderIsomorphisms (IsReduced : ObjectProperty Scheme) :=
  ⟨fun {X Y} e h ↦ by
    letI : IsReduced X := h
    exact isReduced_of_isOpenImmersion e.inv⟩

section

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]

/-- Definition 10.43.1 (Tag 030S): the Stacks Project condition that every field extension
`K / k` yields a reduced base change `K ⊗[k] S` is equivalent to the canonical mathlib class
`Algebra.IsGeometricallyReduced k S`. -/
@[stacks 030S]
theorem isGeometricallyReduced_iff_forall_isReduced_tensorProduct
    :
    IsGeometricallyReduced k S ↔
      ∀ (K : Type u) [Field K] [Algebra k K], IsReduced (K ⊗[k] S) := by
  rw [isGeometricallyReduced_iff]
  constructor
  · intro h K _ _
    letI : IsGeometricallyReduced k S := ⟨h⟩
    exact isReduced_tensorProduct_of_geometricallyReduced
  · intro h
    exact h (AlgebraicClosure k)

end

section

variable {k S : Type u} [Field k] [CommRing S] [Algebra k S]

/-- Companion bridge for Definition 10.43.1: on affine schemes over a field, the scheme-theoretic
notion of geometric reducedness agrees with `Algebra.IsGeometricallyReduced`. -/
theorem geometricallyReduced_iff_isGeometricallyReduced
    :
    GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap k S))) ↔
      IsGeometricallyReduced k S := by
  let f : Spec (of S) ⟶ Spec (of k) := Spec.map (CommRingCat.ofHom (algebraMap k S))
  change GeometricallyReduced f ↔ IsGeometricallyReduced k S
  rw [geometricallyReduced_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  constructor
  · intro h
    rw [isGeometricallyReduced_iff_forall_isReduced_tensorProduct]
    intro K _ _
    let e := pullbackSpecIso k S K
    let e' : K ⊗[k] S ≃ₐ[k] S ⊗[k] K := Algebra.TensorProduct.comm k K S
    letI : IsReduced (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := h K
    have hTensor : IsReduced (S ⊗[k] K) := by
      have hSpec : IsReduced (Spec (of (S ⊗[k] K))) := isReduced_of_isOpenImmersion e.inv
      exact (affine_isReduced_iff (of (S ⊗[k] K))).mp hSpec
    exact isReduced_of_injective e'.toRingHom e'.injective
  · intro h K _ _
    let e := pullbackSpecIso k S K
    let e' : K ⊗[k] S ≃ₐ[k] S ⊗[k] K := Algebra.TensorProduct.comm k K S
    have hReduced : IsReduced (S ⊗[k] K) := by
      let _ : IsReduced (K ⊗[k] S) :=
        (isGeometricallyReduced_iff_forall_isReduced_tensorProduct.mp h) K
      exact isReduced_of_injective e'.symm.toRingHom e'.symm.injective
    letI : IsReduced (Spec (of (S ⊗[k] K))) :=
      (affine_isReduced_iff (of (S ⊗[k] K))).mpr hReduced
    exact isReduced_of_isOpenImmersion e.hom

end

section

variable {k : Type u} [Field k]

/-- A field is geometrically reduced over itself. -/
instance : IsGeometricallyReduced k k := by
  rw [isGeometricallyReduced_iff]
  let e : AlgebraicClosure k ⊗[k] k ≃ₐ[k] AlgebraicClosure k :=
    Algebra.TensorProduct.rid k k (AlgebraicClosure k)
  exact isReduced_of_injective e.toRingHom e.injective

end

end Algebra

/-! ### Lemma_10_43_2 (from Chap10) -/
universe u v

open CategoryTheory Limits
open Algebra
open Algebra.TensorProduct
open scoped TensorProduct

/- Domain-style sampling for geometric reducedness:
- primary domain: commutative algebra of geometrically reduced algebras over a field;
- sampled owner-style declarations:
  `Algebra.IsGeometricallyReduced`,
  `Algebra.IsGeometricallyReduced.of_injective`,
  `Algebra.IsGeometricallyReduced.of_forall_fg`,
  `Algebra.isGeometricallyReduced_iff_forall_isReduced_tensorProduct`;
- best owner abstraction: `Algebra.IsGeometricallyReduced`;
- primitive data: the source-facing inputs in this file are a subalgebra inclusion, a directed
  diagram in `CommAlgCat k`, and a localization map;
- derived API: the finite-presentation/coyoneda factorization from Lemma `10.127.3`, used only to
  descend finitely generated subalgebras of a directed colimit to one stage.
-/

section

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]

/-- Lemma 10.43.2 (1): every `k`-subalgebra of a `k`-algebra geometrically reduced over `k` is
geometrically reduced over `k`. -/
-- Proof sketch: apply `Algebra.IsGeometricallyReduced.of_injective` to the inclusion
-- `T →ₐ[k] S`.
theorem isGeometricallyReduced_subalgebra
    (T : Subalgebra k S) (hS : IsGeometricallyReduced k S) : IsGeometricallyReduced k T := by
  letI := hS
  simpa using IsGeometricallyReduced.of_injective T.val Subtype.val_injective

instance (T : Subalgebra k S) [IsGeometricallyReduced k S] : IsGeometricallyReduced k T :=
  isGeometricallyReduced_subalgebra T inferInstance

/- Lemma 10.43.2 (2): if every finitely generated `k`-subalgebra of `S` is geometrically reduced
over `k`, then `S` is geometrically reduced over `k`. This is exactly the canonical theorem
`Algebra.IsGeometricallyReduced.of_forall_fg`. -/
recall Algebra.IsGeometricallyReduced.of_forall_fg

end

section

variable {k I : Type u} [Field k] [Preorder I] [IsDirectedOrder I]

/-- Lemma 10.43.2 (3): a directed colimit of `k`-algebras geometrically reduced over `k` is
geometrically reduced over `k`. -/
-- Proof sketch: every finitely generated `k`-subalgebra of the colimit is generated by finitely
-- many elements, each coming from some stage. Directedness moves those generators to a common
-- stage, so `Algebra.IsGeometricallyReduced.of_forall_fg` reduces the claim to one stage.
theorem isGeometricallyReduced_colimit_of_directedSystem
    (F : I ⥤ CommAlgCat.{u} k) (hF : ∀ i, IsGeometricallyReduced k (F.obj i)) :
    IsGeometricallyReduced k (colimit F : CommAlgCat.{u} k) := by
  by_cases hI : Nonempty I
  · letI := hI
    letI : IsFiltered I := inferInstance
    apply IsGeometricallyReduced.of_forall_fg
    intro T hT
    let E := commAlgCatEquivUnder (CommRingCat.of k)
    let G : I ⥤ Under (CommRingCat.of k) :=
      F ⋙ E.functor
    let c : Cocone G :=
      E.functor.mapCocone (colimit.cocone F)
    have hc : IsColimit c :=
      isColimitOfPreserves E.functor (colimit.isColimit F)
    have hfp : (algebraMap k T).FinitePresentation := by
      simpa [RingHom.finitePresentation_algebraMap] using
        (Algebra.FinitePresentation.of_finiteType).mp ((Subalgebra.fg_iff_finiteType T).mp hT)
    have hpres :
        PreservesFilteredColimits
          (coyoneda.obj (.op (CommRingCat.mkUnder (CommRingCat.of k) T))) := by
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
    let φ : T →ₐ[k] F.obj i :=
      { __ := g''.right.hom
        commutes' := by
          intro x
          have hw := CommRingCat.hom_ext_iff.mp (Under.w g'')
          change ((CommRingCat.Hom.hom g''.right).comp (algebraMap k T)) x =
            (algebraMap k (F.obj i)) x
          simpa [CommRingCat.mkUnder_hom, CommRingCat.hom_comp] using DFunLike.congr_fun hw x }
    have hfac (x : T) : ιi.right (φ x) = T.val x := by
      have hw := CommRingCat.hom_ext_iff.mp (congrArg (fun f ↦ f.right) hg')
      simpa [g, φ, CommRingCat.hom_comp] using (DFunLike.congr_fun hw x).symm
    have hφ : Function.Injective φ := by
      intro x y hxy
      exact Subtype.ext <| by
        change T.val x = T.val y
        rw [← hfac x, ← hfac y, hxy]
    letI : IsGeometricallyReduced k (F.obj i) := hF i
    exact show IsGeometricallyReduced k T from
      IsGeometricallyReduced.of_injective φ hφ
  · letI : IsEmpty I := not_nonempty_iff.mp hI
    have hcolim : IsInitial (colimit F : CommAlgCat.{u} k) :=
      (isColimitEquivIsInitialOfIsEmpty (CommAlgCat.{u} k) (colimit.cocone F))
        (colimit.isColimit F)
    have hself : IsInitial (CommAlgCat.of k k) := CommAlgCat.isInitialSelf
    let e : (colimit F : CommAlgCat.{u} k) ≅ CommAlgCat.of k k :=
      hcolim.coconePointUniqueUpToIso hself
    let e' : (colimit F : CommAlgCat.{u} k) ≃ₐ[k] CommAlgCat.of k k := CommAlgCat.algEquivOfIso e
    letI : IsGeometricallyReduced k (CommAlgCat.of k k) := inferInstance
    exact show IsGeometricallyReduced k (colimit F : CommAlgCat.{u} k) from
      IsGeometricallyReduced.of_injective e'.toAlgHom e'.injective

end

section

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]

/-- Lemma 10.43.2 (4): every localization of a geometrically reduced `k`-algebra is
geometrically reduced over `k`. The owner abstraction is an arbitrary `S`-localization, with the
concrete ring `Localization M` recovered as a specialization. -/
-- Proof sketch: use the owner criterion
-- `Algebra.isGeometricallyReduced_iff_forall_isReduced_tensorProduct`. For any field extension
-- `K / k`, the tensor product `Sₘ ⊗[k] K` is canonically a localization of `S ⊗[k] K`, hence is
-- reduced because reducedness is preserved by localization.
theorem isGeometricallyReduced_localization
    (M : Submonoid S) {Sₘ : Type v} [CommRing Sₘ] [Algebra S Sₘ] [Algebra k Sₘ]
    [IsScalarTower k S Sₘ] [IsLocalization M Sₘ] (hS : IsGeometricallyReduced k S) :
    IsGeometricallyReduced k Sₘ := by
  letI := hS
  rw [isGeometricallyReduced_iff_forall_isReduced_tensorProduct]
  intro K _ _
  have hKS : IsReduced (K ⊗[k] S) :=
    (isGeometricallyReduced_iff_forall_isReduced_tensorProduct.mp hS) K
  let _ : IsReduced (K ⊗[k] S) := hKS
  let _ : IsReduced (S ⊗[k] K) := by
    let e : S ⊗[k] K ≃ₐ[k] K ⊗[k] S := Algebra.TensorProduct.comm k S K
    exact isReduced_of_injective e.toRingHom e.injective
  let φ : S ⊗[k] K →ₐ[S] Sₘ ⊗[k] K :=
    map (Algebra.ofId S Sₘ) (.id _ _)
  letI : Algebra (S ⊗[k] K) (Sₘ ⊗[k] K) := φ.toAlgebra
  letI : IsScalarTower S (S ⊗[k] K) (Sₘ ⊗[k] K) :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have hReduced : IsReduced (Sₘ ⊗[k] K) := by
    let _ :
        IsLocalization (Algebra.algebraMapSubmonoid (S ⊗[k] K) M) (Sₘ ⊗[k] K) := by
      refine IsLocalization.tensorProduct_tensorProduct k K M Sₘ ?_
      ext
      simp [RingHom.algebraMap_toAlgebra, φ]
    exact isReduced_localizationPreserves (Algebra.algebraMapSubmonoid (S ⊗[k] K) M)
      (Sₘ ⊗[k] K) inferInstance
  let e : K ⊗[k] Sₘ ≃ₐ[k] Sₘ ⊗[k] K := Algebra.TensorProduct.comm k K Sₘ
  exact isReduced_of_injective e.toRingHom e.injective

instance {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    (M : Submonoid S) [IsGeometricallyReduced k S] :
    IsGeometricallyReduced k (Localization M) :=
  isGeometricallyReduced_localization M inferInstance

end

/-! ### Lemma_10_43_3 (from Chap10) -/
universe u v

open scoped TensorProduct
open Algebra
open Algebra.TensorProduct

section

variable {k : Type u} {R : Type v} [Field k] [CommRing R] [Algebra k R]

/- Lemma 10.43.3 (1): if `R` is geometrically reduced over `k`, then every localization of `R`
at a multiplicative subset is geometrically reduced over `k`. This is exactly
`isGeometricallyReduced_localization`. -/
recall isGeometricallyReduced_localization

-- Proof sketch: identify `K ⊗[k] R[X]` with
-- `(K ⊗[k] R)[X]` for an arbitrary field extension `K / k`. The tensor product `K ⊗[k] R` is
-- reduced by Lemma `10.43.5`, and polynomial rings over reduced commutative rings are reduced.
/-- Lemma 10.43.3 (2) (Tag 04KN): if `R` is geometrically reduced over `k`, then `R[X]` is
geometrically reduced over `k`. -/
@[stacks 04KN]
theorem isGeometricallyReduced_polynomial [IsGeometricallyReduced k R] :
    IsGeometricallyReduced k (Polynomial R) := by
  rw [isGeometricallyReduced_iff_forall_isReduced_tensorProduct]
  intro K _ _
  letI : IsReduced (K ⊗[k] R) := inferInstance
  letI : IsReduced (Polynomial (K ⊗[k] R)) := by
    let e := MvPolynomial.pUnitAlgEquiv.{max u v, 0} (K ⊗[k] R)
    letI : IsReduced (MvPolynomial PUnit (K ⊗[k] R)) := inferInstance
    exact isReduced_of_injective e.symm e.symm.injective
  let e : K ⊗[k] Polynomial R ≃ₐ[k] Polynomial (K ⊗[k] R) :=
    (congr (AlgEquiv.refl : K ≃ₐ[k] K) (polyEquivTensor k R)).trans <|
      (Algebra.TensorProduct.assoc k k k K R (Polynomial k)).symm.trans <|
        (polyEquivTensor k (K ⊗[k] R)).symm
  exact isReduced_of_injective e e.injective

instance [IsGeometricallyReduced k R] : IsGeometricallyReduced k (Polynomial R) :=
  isGeometricallyReduced_polynomial

end

/-! ### Lemma_10_43_4 (from Chap10) -/
open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

section

variable {k : Type u} {R : Type v} {S : Type w}
variable [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

/-- A pair of finitely generated `k`-subalgebras of `R` and `S`. -/
structure FGSubalgebraPair where
  left : Subalgebra k R
  right : Subalgebra k S
  left_fg : left.FG
  right_fg : right.FG

/-- A witness that a ring contains two nonzero elements whose product is zero. -/
structure NonzeroZeroDivisorWitness (A : Type*) [Mul A] [Zero A] where
  left : A
  right : A
  left_ne_zero : left ≠ 0
  right_ne_zero : right ≠ 0
  mul_eq_zero : left * right = 0

/-- A witness that a ring contains an idempotent different from `0` and `1`. -/
structure NontrivialIdempotentWitness (A : Type*) [Mul A] [One A] [Zero A] where
  elem : A
  isIdempotent : IsIdempotentElem elem
  ne_zero : elem ≠ 0
  ne_one : elem ≠ 1

/-
Domain triage:
- `source-facing`: the three public statements detect nonreducedness, zerodivisors, and nontrivial
  idempotents in `R ⊗[k] S` on finitely generated `k`-subalgebras on both sides.
- `core/canonical`: one-sided finite descent in tensor products is already owned by
  `exists_fg_and_mem_baseChange`, and reducedness over a field is detected from finitely generated
  subalgebras by `IsReduced.tensorProduct_of_flat_of_forall_fg`.
- `bridge/view`: for parts `(2)` and `(3)`, the finite-family bookkeeping is derived by iterating
  `exists_fg_and_mem_baseChange` and commuting tensor factors, rather than by introducing a
  parallel local helper abstraction.

Primitive data are only the two `k`-algebras and the witness tensor elements. No extra wrapper
carrying finite-stage data is mathematically primary here.
-/

/-- Helper for Lemma 10.43.4: the comparison map from a finitely generated tensor stage into
`R ⊗[k] S` is injective. -/
lemma tensorProduct_map_injective_of_fgSubalgebraPair
    (T : @FGSubalgebraPair k R S _ _ _ _ _) :
    Function.Injective (Algebra.TensorProduct.map T.left.val T.right.val) := by
  -- Over a field, tensoring the two inclusion maps preserves injectivity.
  simpa using TensorProduct.map_injective_of_flat_flat
    T.left.val.toLinearMap T.right.val.toLinearMap
    Subtype.val_injective Subtype.val_injective

/-- Helper for Lemma 10.43.4: every element of `R ⊗[k] S` already comes from the tensor product of
finitely generated `k`-subalgebras on both sides. -/
lemma exists_fg_subalgebras_tensorProduct_lift (x : R ⊗[k] S) :
    ∃ T : @FGSubalgebraPair k R S _ _ _ _ _,
      ∃ x' : T.left ⊗[k] T.right,
        Algebra.TensorProduct.map T.left.val T.right.val x' = x := by
  -- First descend the tensor to finitely many coefficients on the `S`-side.
  obtain ⟨B, hBfg, hxB⟩ := exists_fg_and_mem_baseChange (R := k) (A := R) (B := S) x
  obtain ⟨u, hu⟩ := hxB
  -- Then commute the tensor and descend the remaining coefficients on the `R`-side.
  obtain ⟨A, hAfg, huA⟩ := exists_fg_and_mem_baseChange
    (R := k) (A := B) (B := R) (Algebra.TensorProduct.comm k R B u)
  obtain ⟨v, hv⟩ := huA
  have hu' : Algebra.TensorProduct.map (AlgHom.id k R) B.val u = x := hu
  have hv' : Algebra.TensorProduct.map (AlgHom.id k B) A.val v =
      Algebra.TensorProduct.comm k R B u := hv
  refine ⟨{
    left := A
    right := B
    left_fg := hAfg
    right_fg := hBfg
  }, Algebra.TensorProduct.comm k B A v, ?_⟩
  change Algebra.TensorProduct.map A.val B.val (Algebra.TensorProduct.comm k B A v) = x
  -- Compare after commuting: both one-sided lifts now line up with the same tensor.
  apply (Algebra.TensorProduct.comm k R S).injective
  calc
    Algebra.TensorProduct.comm k R S
        (Algebra.TensorProduct.map A.val B.val (Algebra.TensorProduct.comm k B A v))
      = Algebra.TensorProduct.map B.val A.val
          (Algebra.TensorProduct.comm k A B (Algebra.TensorProduct.comm k B A v)) := by
          simpa using
            (Algebra.TensorProduct.comm_comp_map_apply
              (f := A.val)
              (g := B.val)
              (Algebra.TensorProduct.comm k B A v))
    _ = Algebra.TensorProduct.map B.val A.val v := by
          have hcomm : Algebra.TensorProduct.comm k A B
              (Algebra.TensorProduct.comm k B A v) = v := by
            change Algebra.TensorProduct.comm k A B
                ((Algebra.TensorProduct.comm k A B).symm v) = v
            exact AlgEquiv.apply_symm_apply (Algebra.TensorProduct.comm k A B) v
          rw [hcomm]
    _ = Algebra.TensorProduct.comm k R S x := by
          calc
            Algebra.TensorProduct.map B.val A.val v
              = ((Algebra.TensorProduct.map B.val (AlgHom.id k R)).comp
                  (Algebra.TensorProduct.map (AlgHom.id k B) A.val)) v := by
                  simpa using congrArg (fun f => f v)
                    (Algebra.TensorProduct.map_comp
                      (f₂ := B.val)
                      (f₁ := AlgHom.id k B)
                      (g₂ := AlgHom.id k R)
                      (g₁ := A.val))
            _ = Algebra.TensorProduct.map B.val (AlgHom.id k R)
                  (Algebra.TensorProduct.map (AlgHom.id k B) A.val v) := rfl
            _ = Algebra.TensorProduct.map B.val (AlgHom.id k R)
                  (Algebra.TensorProduct.comm k R B u) := by rw [hv']
            _ = Algebra.TensorProduct.comm k R S
                  (Algebra.TensorProduct.map (AlgHom.id k R) B.val u) := by
                  symm
                  simpa using
                    (Algebra.TensorProduct.comm_comp_map_apply
                      (f := AlgHom.id k R) (g := B.val) u)
            _ = Algebra.TensorProduct.comm k R S x := by rw [hu']

/-- Helper for Lemma 10.43.4: two tensor elements can be realized inside one common finitely
generated tensor stage. -/
lemma exists_fg_subalgebras_tensorProduct_lift_pair (x y : R ⊗[k] S) :
    ∃ T : @FGSubalgebraPair k R S _ _ _ _ _,
      ∃ x' y' : T.left ⊗[k] T.right,
        Algebra.TensorProduct.map T.left.val T.right.val x' = x ∧
          Algebra.TensorProduct.map T.left.val T.right.val y' = y := by
  -- Lift each tensor separately, then enlarge by the sup of the two finitely generated stages.
  obtain ⟨Tx, x', hx⟩ := exists_fg_subalgebras_tensorProduct_lift (k := k) (R := R) (S := S) x
  obtain ⟨Ty, y', hy⟩ := exists_fg_subalgebras_tensorProduct_lift (k := k) (R := R) (S := S) y
  let T : FGSubalgebraPair := {
    left := Tx.left ⊔ Ty.left
    right := Tx.right ⊔ Ty.right
    left_fg := Subalgebra.FG.sup Tx.left_fg Ty.left_fg
    right_fg := Subalgebra.FG.sup Tx.right_fg Ty.right_fg
  }
  let x'' : T.left ⊗[k] T.right := Algebra.TensorProduct.map
    (Subalgebra.inclusion (show Tx.left ≤ T.left from le_sup_left))
    (Subalgebra.inclusion (show Tx.right ≤ T.right from le_sup_left)) x'
  let y'' : T.left ⊗[k] T.right := Algebra.TensorProduct.map
    (Subalgebra.inclusion (show Ty.left ≤ T.left from le_sup_right))
    (Subalgebra.inclusion (show Ty.right ≤ T.right from le_sup_right)) y'
  refine ⟨T, x'', y'', ?_, ?_⟩
  · -- The enlarged left/right stages still map `x''` to the original tensor `x`.
    calc
      Algebra.TensorProduct.map T.left.val T.right.val x''
        = Algebra.TensorProduct.map Tx.left.val Tx.right.val x' := by
            simpa [T, x''] using congrArg (fun f => f x')
              (Algebra.TensorProduct.map_comp
                (f₂ := T.left.val)
                (f₁ := Subalgebra.inclusion (show Tx.left ≤ T.left from le_sup_left))
                (g₂ := T.right.val)
                (g₁ := Subalgebra.inclusion (show Tx.right ≤ T.right from le_sup_left))).symm
      _ = x := hx
  · -- The same sup-enlargement carries `y''` to `y`.
    calc
      Algebra.TensorProduct.map T.left.val T.right.val y''
        = Algebra.TensorProduct.map Ty.left.val Ty.right.val y' := by
            simpa [T, y''] using congrArg (fun f => f y')
              (Algebra.TensorProduct.map_comp
                (f₂ := T.left.val)
                (f₁ := Subalgebra.inclusion (show Ty.left ≤ T.left from le_sup_right))
                (g₂ := T.right.val)
                (g₁ := Subalgebra.inclusion (show Ty.right ≤ T.right from le_sup_right))).symm
      _ = y := hy

-- Proof sketch: use the contrapositive of
-- `IsReduced.tensorProduct_of_flat_of_forall_fg` twice, first in the `S`-variable and then in the
-- `R`-variable. Over a field, all modules are flat, so the nonreduced nilpotent element already
-- lives in the tensor product of finitely generated subalgebras on both sides.
/-- Lemma 10.43.4 (1): if `R ⊗[k] S` is not reduced, then there exist finitely generated
`k`-subalgebras `R' ⊆ R` and `S' ⊆ S` such that `R' ⊗[k] S'` is not reduced. -/
theorem exists_fg_subalgebras_not_isReduced_tensorProduct
    (h : ¬ IsReduced (R ⊗[k] S)) :
    ∃ T : @FGSubalgebraPair k R S _ _ _ _ _,
      ¬ IsReduced (T.left ⊗[k] T.right) := by
  -- Choose a nonzero nilpotent witness for nonreducedness in the ambient tensor product.
  obtain ⟨z, hz_ne_zero, hz_nilpotent⟩ := exists_isNilpotent_of_not_isReduced h
  -- Lift that witness to a finitely generated tensor stage on both sides.
  obtain ⟨T, z', hz_map⟩ := exists_fg_subalgebras_tensorProduct_lift (k := k) (R := R) (S := S) z
  have h_inj := tensorProduct_map_injective_of_fgSubalgebraPair (k := k) (R := R) (S := S) T
  have hz'_nilpotent : IsNilpotent z' := by
    rw [← IsNilpotent.map_iff h_inj, hz_map]
    exact hz_nilpotent
  have hz'_ne_zero : z' ≠ 0 := by
    intro hz'_eq_zero
    apply hz_ne_zero
    simpa [hz'_eq_zero] using hz_map.symm
  refine ⟨T, ?_⟩
  -- The descended nilpotent stays nonzero, so the smaller tensor product is not reduced.
  intro hReduced
  exact hz'_ne_zero (hReduced.eq_zero z' hz'_nilpotent)

-- Proof sketch: apply `exists_fg_and_mem_baseChange` to `z`, then after commuting tensor factors
-- apply it again to the resulting coefficients needed for `w`, obtaining a common finitely
-- generated stage on both sides. The equalities `z ≠ 0`, `w ≠ 0`, and `z * w = 0` then descend
-- along the induced map from the smaller tensor product.
/-- Lemma 10.43.4 (2): if `R ⊗[k] S` contains a nonzero zerodivisor, then it already appears in
the tensor product of finitely generated `k`-subalgebras on both sides. -/
theorem exists_fg_subalgebras_tensorProduct_has_nonzero_zerodivisor
    (h : Nonempty (NonzeroZeroDivisorWitness (R ⊗[k] S))) :
    ∃ T : @FGSubalgebraPair k R S _ _ _ _ _,
      Nonempty (NonzeroZeroDivisorWitness (T.left ⊗[k] T.right)) := by
  -- Start from a zerodivisor witness and descend both elements to one common finite stage.
  obtain ⟨w⟩ := h
  obtain ⟨T, z', w', hz_map, hw_map⟩ := exists_fg_subalgebras_tensorProduct_lift_pair
    (k := k) (R := R) (S := S) w.left w.right
  have h_inj := tensorProduct_map_injective_of_fgSubalgebraPair (k := k) (R := R) (S := S) T
  have hz'_ne_zero : z' ≠ 0 := by
    intro hz'_eq_zero
    apply w.left_ne_zero
    simpa [hz'_eq_zero] using hz_map.symm
  have hw'_ne_zero : w' ≠ 0 := by
    intro hw'_eq_zero
    apply w.right_ne_zero
    simpa [hw'_eq_zero] using hw_map.symm
  have hmul_eq_zero : z' * w' = 0 := by
    apply h_inj
    simpa [map_mul, hz_map, hw_map] using w.mul_eq_zero
  refine ⟨T, ?_⟩
  -- Injectivity transports the zerodivisor equations and nonvanishing to the smaller stage.
  exact ⟨{
    left := z'
    right := w'
    left_ne_zero := hz'_ne_zero
    right_ne_zero := hw'_ne_zero
    mul_eq_zero := hmul_eq_zero
  }⟩

-- Proof sketch: iterate `exists_fg_and_mem_baseChange` to place the idempotent `e` in a common
-- finitely generated tensor stage, then transport the equations `e * e = e`, `e ≠ 0`, and
-- `e ≠ 1` along the comparison map.
/-- Lemma 10.43.4 (3): if `R ⊗[k] S` contains a nontrivial idempotent, then it already appears in
finitely generated `k`-subalgebras on both sides. -/
theorem exists_fg_subalgebras_tensorProduct_has_nontrivial_idempotent
    (h : Nonempty (NontrivialIdempotentWitness (R ⊗[k] S))) :
    ∃ T : @FGSubalgebraPair k R S _ _ _ _ _,
      Nonempty (NontrivialIdempotentWitness (T.left ⊗[k] T.right)) := by
  -- Lift the idempotent itself to a finitely generated tensor stage.
  obtain ⟨w⟩ := h
  obtain ⟨T, e', he_map⟩ := exists_fg_subalgebras_tensorProduct_lift
    (k := k) (R := R) (S := S) w.elem
  have h_inj := tensorProduct_map_injective_of_fgSubalgebraPair (k := k) (R := R) (S := S) T
  have he'_idempotent : IsIdempotentElem e' := by
    apply h_inj
    simpa [map_mul, he_map] using w.isIdempotent.eq
  have he'_ne_zero : e' ≠ 0 := by
    intro he'_eq_zero
    apply w.ne_zero
    simpa [he'_eq_zero] using he_map.symm
  have he'_ne_one : e' ≠ 1 := by
    intro he'_eq_one
    apply w.ne_one
    simpa [he'_eq_one] using he_map.symm
  refine ⟨T, ?_⟩
  -- Injectivity also transports the inequalities against `0` and `1`.
  exact ⟨{
    elem := e'
    isIdempotent := he'_idempotent
    ne_zero := he'_ne_zero
    ne_one := he'_ne_one
  }⟩

end

/-! ### Lemma_10_43_5 (from Chap10) -/
open scoped TensorProduct
open Algebra

universe u v w

/-!
Domain triage:
- `source-facing`: the statement says that tensoring a reduced `k`-algebra with a geometrically
  reduced `k`-algebra over the same field stays reduced.
- `core/canonical`: the owner abstraction on the right factor is `Algebra.IsGeometricallyReduced`.
- `bridge/view`: Lemma `10.43.4` gives the finite descent skeleton, so the remaining work is the
  finite-stage reducedness statement.
-/

section

variable {k : Type u} {R : Type v} {S : Type w}
variable [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

/-- Helper for Lemma 10.43.5: a minimal prime carries its canonical primality instance. -/
local instance minimalPrime_isPrime (p : minimalPrimes R) : p.1.IsPrime :=
  Ideal.minimalPrimes_isPrime p.2

/-- Helper for Lemma 10.43.5: a reduced `k`-algebra has reduced `k`-subalgebras. -/
lemma isReduced_subalgebra_of_isReduced [IsReduced R] (T : Subalgebra k R) :
    IsReduced T := by
  -- Reducedness descends along the injective inclusion into the ambient reduced algebra.
  exact isReduced_of_injective T.val Subtype.val_injective

/-- Helper for Lemma 10.43.5: the left side of a finitely generated tensor stage is Noetherian. -/
lemma isNoetherianRing_left_of_fgSubalgebraPair
    (T : @FGSubalgebraPair k R S _ _ _ _ _) :
    IsNoetherianRing T.left := by
  -- Finite generation over the field `k` upgrades the left stage to a finite type algebra.
  let _ : Algebra.FiniteType k T.left := (Subalgebra.fg_iff_finiteType T.left).mp T.left_fg
  -- Finite type algebras over a Noetherian ring are Noetherian, and fields are Noetherian.
  exact Algebra.FiniteType.isNoetherianRing k T.left

/-- Helper for Lemma 10.43.5: it is enough to prove reducedness on every finitely generated tensor
stage produced by Lemma `10.43.4`. -/
lemma isReduced_tensorProduct_of_forall_fgSubalgebraPair
    [IsReduced R] [IsGeometricallyReduced k S]
    (hfg : ∀ T : @FGSubalgebraPair k R S _ _ _ _ _, IsReduced (T.left ⊗[k] T.right)) :
    IsReduced (R ⊗[k] S) := by
  -- Any nonreduced witness in the ambient tensor product descends to a finite stage.
  by_contra hnot
  obtain ⟨T, hTnot⟩ := exists_fg_subalgebras_not_isReduced_tensorProduct
    (k := k) (R := R) (S := S) hnot
  -- The assumed finite-stage reducedness contradicts that descended witness.
  exact hTnot (hfg T)

/-- Helper for Lemma 10.43.5: tensoring an injective algebra map on the right over a field stays
injective. -/
lemma tensorProduct_map_injective_of_injective_rightAlgHom
    {A : Type*} {B : Type*} {C : Type*}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C]
    (f : B →ₐ[k] C) (hf : Function.Injective f) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id k A) f) := by
  -- Over a field, both tensor factors are flat, so the tensor-product map preserves injectivity.
  simpa using
    TensorProduct.map_injective_of_flat_flat
      (LinearMap.id : A →ₗ[k] A)
      f.toLinearMap
      (fun _ _ h ↦ h)
      hf

/-- Helper for Lemma 10.43.5: if a field extension is essentially of finite type over `k`, then
tensoring a geometrically reduced `k`-algebra with it is reduced. -/
lemma essFiniteTypeField_tensor_right_reduced
    {K : Type*} [Field K] [Algebra k K] [Algebra.EssFiniteType k K]
    [IsGeometricallyReduced k S] :
    IsReduced (S ⊗[k] K) := by
  -- Route correction: the remaining gap is not a local tensor rewrite but the owner-level bridge
  -- that geometrically reduced base change stays reduced over essentially finite type field
  -- extensions. Reusing later `10.43.6`/`10.44.4` directly would create an import cycle through
  -- `Definition_10_43_1`, so the missing theorem must be moved to an earlier support owner.
  -- TODO: prove the dependency-closed support theorem
  -- `isReduced_tensorProduct_of_essFiniteTypeField :
  --    [Field K] [Algebra k K] [Algebra.EssFiniteType k K] [IsGeometricallyReduced k S] →
  --    IsReduced (S ⊗[k] K)`
  -- by combining the purely inseparable lift from `Lemma 10.42.4` with the separably generated
  -- field case, and then replace this local placeholder by a direct application of that theorem.
  sorry

/-- Helper for Lemma 10.43.5: tensoring the geometrically reduced right stage with any
minimal-prime field factor of a finite-type left stage stays reduced. -/
lemma minimalPrime_localization_tensor_right_reduced
    [IsReduced R] [Algebra.FiniteType k R] [IsGeometricallyReduced k S]
    (p : minimalPrimes R) :
    IsReduced (S ⊗[k] Localization.AtPrime p.1) := by
  let _ : Field (Localization.AtPrime p.1) :=
    (isField_localizationAtPrime_of_minimalPrime (R := R) p).toField
  let _ : Algebra.EssFiniteType R (Localization.AtPrime p.1) :=
    Algebra.EssFiniteType.of_isLocalization
      (R := R)
      (S := Localization.AtPrime p.1)
      p.1.primeCompl
  let _ : Algebra.EssFiniteType k (Localization.AtPrime p.1) :=
    Algebra.EssFiniteType.comp k R (Localization.AtPrime p.1)
  -- The minimal-prime localization is a finitely generated field extension of `k`, so this is
  -- exactly the field case isolated above.
  exact essFiniteTypeField_tensor_right_reduced (k := k) (S := S)

/-- Helper for Lemma 10.43.5: after commuting the tensor factors, tensoring the minimal-prime
product embedding of the left stage gives an injective comparison map into the product of field
factors. -/
abbrev fgStageFieldFactor
    (T : @FGSubalgebraPair k R S _ _ _ _ _)
    (p : minimalPrimes T.left) : Type _ :=
  T.right ⊗[k] Localization.AtPrime p.1

/-- Helper for Lemma 10.43.5: the product of all minimal-prime field tensor factors attached to a
finitely generated stage. -/
abbrev fgStageTensorTarget
    (T : @FGSubalgebraPair k R S _ _ _ _ _) : Type _ :=
  ∀ p : minimalPrimes T.left, fgStageFieldFactor (k := k) (R := R) (S := S) T p

/-- Helper for Lemma 10.43.5: after commuting the tensor factors, tensoring the minimal-prime
product embedding of the left stage gives an injective comparison map into the product of field
factors. -/
noncomputable abbrev fgStageTensorCompare
    (T : @FGSubalgebraPair k R S _ _ _ _ _)
    [Fintype (minimalPrimes T.left)] [DecidableEq (minimalPrimes T.left)] :
    T.left ⊗[k] T.right →ₐ[k] fgStageTensorTarget (k := k) (R := R) (S := S) T :=
  (((Algebra.TensorProduct.piRight k k T.right
      (fun p : minimalPrimes T.left ↦ Localization.AtPrime p.1)).toAlgHom).comp
      (Algebra.TensorProduct.map (AlgHom.id k T.right)
        (IsScalarTower.toAlgHom
          k
          T.left
          (∀ p : minimalPrimes T.left, Localization.AtPrime p.1)))).comp
    (Algebra.TensorProduct.comm k T.left T.right).toAlgHom

/-- Helper for Lemma 10.43.5: after commuting the tensor factors, tensoring the minimal-prime
product embedding of the left stage gives an injective comparison map into the product of field
factors. -/
lemma fg_stage_tensor_to_minimalPrime_fields_injective
    (T : @FGSubalgebraPair k R S _ _ _ _ _)
    [IsReduced T.left]
    [Fintype (minimalPrimes T.left)] [DecidableEq (minimalPrimes T.left)] :
    Function.Injective (fgStageTensorCompare (k := k) (R := R) (S := S) T) := by
  have hleft :
      Function.Injective
        (IsScalarTower.toAlgHom
          k
          T.left
          (∀ p : minimalPrimes T.left, Localization.AtPrime p.1)) :=
    (algebraMap_embedding_into_product_of_fields (R := T.left)).1
  have htensor :
      Function.Injective
        (Algebra.TensorProduct.map (AlgHom.id k T.right)
          (IsScalarTower.toAlgHom
            k
            T.left
            (∀ p : minimalPrimes T.left, Localization.AtPrime p.1))) := by
    -- Tensoring the injective product-of-fields embedding with the identity preserves injectivity.
    exact
      tensorProduct_map_injective_of_injective_rightAlgHom
        (k := k)
        (A := T.right)
        (B := T.left)
        (C := ∀ p : minimalPrimes T.left, Localization.AtPrime p.1)
        (IsScalarTower.toAlgHom
          k
          T.left
          (∀ p : minimalPrimes T.left, Localization.AtPrime p.1))
        hleft
  -- Compose the tensor comparison with the finite-product tensor equivalence.
  exact
    (Algebra.TensorProduct.piRight k k T.right
      (fun p : minimalPrimes T.left ↦ Localization.AtPrime p.1)).injective.comp
      (htensor.comp (Algebra.TensorProduct.comm k T.left T.right).injective)

/-- Helper for Lemma 10.43.5: a finitely generated tensor stage is reduced once the source proof's
product-of-fields reduction is implemented. -/
lemma fgSubalgebraPair_isReduced_tensorProduct
    [IsReduced R] [IsGeometricallyReduced k S]
    (T : @FGSubalgebraPair k R S _ _ _ _ _) :
    IsReduced (T.left ⊗[k] T.right) := by
  let _ : IsReduced T.left :=
    isReduced_subalgebra_of_isReduced (k := k) (R := R) T.left
  let _ : IsGeometricallyReduced k T.right :=
    IsGeometricallyReduced.of_injective T.right.val Subtype.val_injective
  let _ : Algebra.FiniteType k T.left :=
    (Subalgebra.fg_iff_finiteType T.left).mp T.left_fg
  let _ : IsNoetherianRing T.left :=
    isNoetherianRing_left_of_fgSubalgebraPair (k := k) (R := R) (S := S) T
  let _ : Fintype (minimalPrimes T.left) :=
    (minimalPrimes.finite_of_isNoetherianRing (R := T.left)).fintype
  let compare :
      T.left ⊗[k] T.right →ₐ[k] fgStageTensorTarget (k := k) (R := R) (S := S) T :=
    fgStageTensorCompare (k := k) (R := R) (S := S) T
  have hcompare : Function.Injective compare :=
    fg_stage_tensor_to_minimalPrime_fields_injective (k := k) (R := R) (S := S) T
  let _ : ∀ p : minimalPrimes T.left, IsReduced (fgStageFieldFactor (k := k) (R := R) (S := S) T p) :=
    fun p ↦
      minimalPrime_localization_tensor_right_reduced
        (k := k) (R := T.left) (S := T.right) p
  let _ : Pow (fgStageTensorTarget (k := k) (R := R) (S := S) T) ℕ :=
    ⟨fun x n p ↦ x p ^ n⟩
  let _ : IsReduced (fgStageTensorTarget (k := k) (R := R) (S := S) T) :=
    { eq_zero := fun x hx ↦
        let ⟨n, hn⟩ := hx
        funext fun p ↦ IsReduced.eq_zero (x p) ⟨n, congrFun hn p⟩ }
  -- The source proof now closes the finite stage by embedding it into a product of reduced field
  -- factors and reflecting reducedness across that injective comparison map.
  exact isReduced_of_injective compare.toMonoidWithZeroHom hcompare

-- Proof sketch: descend nonreducedness to a finitely generated tensor stage using Lemma `10.43.4`,
-- then prove that finite stage reduced by the source proof's embedding into a finite product of
-- fields and the field-factor case of geometric reducedness.
/-- Lemma 10.43.5 (Tag 034N): if `S` is geometrically reduced over the field `k` and `R` is a
reduced `k`-algebra, then `R ⊗[k] S` is reduced. -/
@[stacks 034N, instance]
theorem isReduced_tensorProduct_of_geometricallyReduced
    [IsReduced R] [IsGeometricallyReduced k S] :
    IsReduced (R ⊗[k] S) := by
  -- First reduce the global claim to the finite tensor stages produced by Lemma `10.43.4`.
  refine isReduced_tensorProduct_of_forall_fgSubalgebraPair
    (k := k) (R := R) (S := S) ?_
  intro T
  -- Then discharge the finite stage by the source proof's product-of-fields argument.
  exact fgSubalgebraPair_isReduced_tensorProduct (k := k) (R := R) (S := S) T

end

/-! ### Lemma_10_43_6 (from Chap10) -/
open scoped TensorProduct
open Algebra

universe u v w

/-
Domain triage:
- `source-facing`: the main lemma is reducedness of `K ⊗[k] S` for a reduced `k`-algebra `S` and a
  Stacks-separable field extension `K / k`.
- `core/canonical`: the owner abstraction for the field-extension side is
  `Algebra.IsGeometricallyReduced k K`.
- `bridge/view`: the geometric-reducedness consequence is derived from the source-facing tensor
  product lemma by commuting `AlgebraicClosure k ⊗[k] K`.

Primitive data are the reduced algebra `S` and the separable extension `K / k`; geometric
reducedness of `K` is derived API, not primitive data.
-/

section

variable {k : Type u} {K : Type v} {S : Type w}
variable [Field k] [Field K] [CommRing S] [Algebra k K] [Algebra k S]

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Helper for Lemma 10.43.6: after base change to a field `κ / k`, the fraction-field stage of
the transcendence-basis argument is still a domain. -/
lemma isDomain_tensor_fractionRing_of_mvPolynomial
    {ι : Type*} {κ : Type*} [Field κ] [Algebra k κ] :
    IsDomain (FractionRing (MvPolynomial ι k) ⊗[k] κ) := by
  sorry

/-- Helper for Lemma 10.43.6: after identifying the transcendence-basis stage with a rational
function field, tensoring with any left field still yields a domain. -/
lemma isDomain_tensor_adjoin_of_isTranscendenceBasis
    {κ : Type*} [Field κ] [Algebra k κ]
    {L : Type*} [Field L] [Algebra k L]
    {ι : Type*} (x : ι → L) (hx : IsTranscendenceBasis k x) :
    IsDomain (κ ⊗[k] IntermediateField.adjoin k (Set.range x)) := by
  let P : Type _ := MvPolynomial ι k
  let eAdjoin :
      κ ⊗[k] IntermediateField.adjoin k (Set.range x) ≃+* (κ ⊗[k] FractionRing P) :=
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : κ ≃ₐ[k] κ) hx.1.aevalEquivField.symm).toRingEquiv
  let ePoly :
      P ⊗[k] κ ≃+* MvPolynomial ι κ :=
    (Algebra.TensorProduct.comm k P κ).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv (σ := ι) k κ).toRingEquiv
  have hPolyDomain : IsDomain (P ⊗[k] κ) := by
    -- After commuting the factors, the polynomial base change is exactly `MvPolynomial ι κ`.
    exact ePoly.isDomain_iff.mpr inferInstance
  have hFracDomain : IsDomain (FractionRing P ⊗[k] κ) := by
    -- This is the fraction-field domain step isolated from the localization transport.
    simpa [P] using
      isDomain_tensor_fractionRing_of_mvPolynomial (k := k) (ι := ι) (κ := κ)
  let eTensor :
      (κ ⊗[k] FractionRing P) ≃+* (FractionRing P ⊗[k] κ) :=
    (Algebra.TensorProduct.comm k κ (FractionRing P)).toRingEquiv
  -- Transport the fraction-field domain result back to the transcendence-basis stage.
  exact (eAdjoin.trans eTensor).isDomain_iff.mpr hFracDomain

/-- Helper for Lemma 10.43.6: a separable polynomial cuts out a reduced adjoin-root quotient. -/
lemma isReduced_adjoinRoot_of_separable
    {F : Type*} [Field F] (P : Polynomial F) (hP : P.Separable) :
    IsReduced (AdjoinRoot P) := by
  -- Route correction: package the squarefree-to-radical quotient step as a standalone field lemma
  -- instead of reproving it inside the final one-generator tensor argument.
  change IsReduced (Polynomial F ⧸ Ideal.span ({P} : Set (Polynomial F)))
  rw [← Ideal.isRadical_iff_quotient_reduced, ← isRadical_iff_span_singleton]
  exact hP.squarefree.isRadical

/-- Helper for Lemma 10.43.6: tensoring the injective map from a domain to its fraction field with
the identity on a finite-dimensional right field factor remains injective. -/
lemma tensorProduct_map_injective_to_fractionRing_of_finiteDimensional_right
    {E : Type*} [Field E]
    {A : Type*} [CommRing A] [IsDomain A] [Algebra E A]
    {L : Type*} [Field L] [Algebra E L] [FiniteDimensional E L] :
    Function.Injective
      (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom E A (FractionRing A))
        (AlgHom.id E L)) := by
  -- Over the base field `E`, both target modules are flat, so tensoring preserves injectivity.
  simpa using TensorProduct.map_injective_of_flat_flat
    (IsScalarTower.toAlgHom E A (FractionRing A)).toLinearMap
    (LinearMap.id : L →ₗ[E] L)
    (IsFractionRing.injective A (FractionRing A))
    (fun _ _ h ↦ h)

/-- Helper for Lemma 10.43.6: an algebraic simple generator identifies the whole field with the
corresponding `AdjoinRoot` model. -/
noncomputable def simple_generator_adjoinRoot_algEquiv
    {E : Type*} [Field E]
    {L : Type*} [Field L] [Algebra E L]
    {y : L} (hy_int : IsIntegral E y)
    (hgen : IntermediateField.adjoin E ({y} : Set L) = ⊤) :
    AdjoinRoot (minpoly E y) ≃ₐ[E] L :=
  let eTop : IntermediateField.adjoin E ({y} : Set L) ≃ₐ[E] L :=
    (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
  (IntermediateField.adjoinRootEquivAdjoin E hy_int).trans eTop

/-- Helper for Lemma 10.43.6: a field generated by one integral element is finite-dimensional over
the base field. -/
lemma finiteDimensional_of_singleton_adjoin_eq_top
    {E : Type*} [Field E]
    {L : Type*} [Field L] [Algebra E L]
    {y : L} (hy_int : IsIntegral E y)
    (hgen : IntermediateField.adjoin E ({y} : Set L) = ⊤) :
    FiniteDimensional E L := by
  -- First control the one-generator intermediate field by integrality of `y`.
  letI : FiniteDimensional E (IntermediateField.adjoin E ({y} : Set L)) :=
    IntermediateField.adjoin.finiteDimensional hy_int
  let eTop : IntermediateField.adjoin E ({y} : Set L) ≃ₐ[E] L :=
    (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
  -- Then transport finite dimensionality across the identification with the top field.
  exact FiniteDimensional.of_injective
    eTop.symm.toLinearMap eTop.symm.injective

/-- Helper for Lemma 10.43.6: under the polynomial-tensor equivalence, the right tensor inclusion
of a polynomial is exactly coefficientwise base change. -/
lemma polyEquivTensor_symm_includeRight
    {E : Type*} [Field E]
    {A : Type*} [CommRing A] [Algebra E A]
    (p : Polynomial E) :
    (polyEquivTensor' E A).symm
      ((Algebra.TensorProduct.includeRight : Polynomial E →ₐ[E] A ⊗[E] Polynomial E) p) =
        Polynomial.map (algebraMap E A) p := by
  -- Rewrite the tensor-side polynomial relation as the mapped polynomial over `A`.
  rw [Algebra.TensorProduct.includeRight_apply]
  simpa using
    (polyEquivTensor_symm_apply_tmul_eq_smul (R := E) (A := A) (a := (1 : A)) (p := p))

/-- Helper for Lemma 10.43.6: after transporting along `polyEquivTensor`, the tensor-side ideal of
the relation `p` becomes the principal ideal of the mapped polynomial. -/
lemma tensor_adjoinRoot_ideal_map_eq_span
    {E : Type*} [Field E]
    {A : Type*} [CommRing A] [Algebra E A]
    (p : Polynomial E) :
    Ideal.span ({Polynomial.map (algebraMap E A) p} : Set (Polynomial A)) =
      Ideal.map ((polyEquivTensor' E A).symm : A ⊗[E] Polynomial E →ₐ[A] Polynomial A).toRingHom
        (Ideal.map
          (Algebra.TensorProduct.includeRight : Polynomial E →ₐ[E] A ⊗[E] Polynomial E)
          (Ideal.span ({p} : Set (Polynomial E)))) := by
  -- The quotient relation is still generated by one polynomial after passing through the tensor.
  rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
  congr 1
  exact congrArg Set.singleton (polyEquivTensor_symm_includeRight (E := E) (A := A) p).symm

/-- Helper for Lemma 10.43.6: base changing `AdjoinRoot p` along an `E`-algebra `A` produces the
adjoin-root algebra of the coefficientwise image of `p`. -/
noncomputable abbrev tensor_adjoinRoot_algEquiv
    {E : Type*} [Field E]
    {A : Type*} [CommRing A] [Algebra E A]
    (p : Polynomial E) :
    A ⊗[E] AdjoinRoot p ≃ₐ[A] AdjoinRoot (Polynomial.map (algebraMap E A) p) :=
  let eQuot :
      A ⊗[E] AdjoinRoot p ≃ₐ[A]
        (A ⊗[E] Polynomial E) ⧸
          Ideal.map
            (Algebra.TensorProduct.includeRight : Polynomial E →ₐ[E] A ⊗[E] Polynomial E)
            (Ideal.span ({p} : Set (Polynomial E))) :=
    Algebra.TensorProduct.tensorQuotientEquiv (R := E) A (Polynomial E) A
      (Ideal.span ({p} : Set (Polynomial E)))
  let ePoly :
      ((A ⊗[E] Polynomial E) ⧸
          Ideal.map
            (Algebra.TensorProduct.includeRight : Polynomial E →ₐ[E] A ⊗[E] Polynomial E)
            (Ideal.span ({p} : Set (Polynomial E)))) ≃ₐ[A]
        Polynomial A ⧸ Ideal.span ({Polynomial.map (algebraMap E A) p} : Set (Polynomial A)) :=
    Ideal.quotientEquivAlg
      (I := Ideal.map
        (Algebra.TensorProduct.includeRight : Polynomial E →ₐ[E] A ⊗[E] Polynomial E)
        (Ideal.span ({p} : Set (Polynomial E))))
      (J := Ideal.span ({Polynomial.map (algebraMap E A) p} : Set (Polynomial A)))
      ((polyEquivTensor' E A).symm)
      (tensor_adjoinRoot_ideal_map_eq_span (E := E) (A := A) p)
  eQuot.trans ePoly

/-- Helper for Lemma 10.43.6: after passing to the fraction field on the left, a separable
one-relation extension stays reduced. -/
lemma isReduced_fractionRing_tensor_adjoinRoot_of_separable
    {E : Type*} [Field E]
    {A0 : Type*} [CommRing A0] [IsDomain A0] [Algebra E A0]
    (p : Polynomial E) (hp : p.Separable) :
    IsReduced (FractionRing A0 ⊗[E] AdjoinRoot p) := by
  sorry

/-- Helper for Lemma 10.43.6: if `L / E` is generated by one separable element and `A0` is a
domain, then `A0 ⊗[E] L` is reduced. -/
lemma isReduced_tensor_simple_separable_extension_of_domain
    {E : Type*} [Field E]
    {A0 : Type*} [CommRing A0] [IsDomain A0] [Algebra E A0]
    {L : Type*} [Field L] [Algebra E L]
    {y : L} (hgen : IntermediateField.adjoin E ({y} : Set L) = ⊤)
    (hy_sep : IsSeparable E y) :
    IsReduced (A0 ⊗[E] L) := by
  let hy_int : IsIntegral E y := hy_sep.isIntegral
  letI : FiniteDimensional E L :=
    finiteDimensional_of_singleton_adjoin_eq_top (E := E) hy_int hgen
  let eSimple : AdjoinRoot (minpoly E y) ≃ₐ[E] L :=
    simple_generator_adjoinRoot_algEquiv (E := E) hy_int hgen
  have hReducedFracSimple :
      IsReduced (FractionRing A0 ⊗[E] AdjoinRoot (minpoly E y)) := by
    -- The fraction-field stage is the `F[T]/(P)` paragraph from the source proof.
    exact
      isReduced_fractionRing_tensor_adjoinRoot_of_separable
        (E := E) (A0 := A0) (p := minpoly E y) hy_sep
  letI : IsReduced (FractionRing A0 ⊗[E] AdjoinRoot (minpoly E y)) := hReducedFracSimple
  let eFrac :
      FractionRing A0 ⊗[E] AdjoinRoot (minpoly E y) ≃ₐ[FractionRing A0]
        FractionRing A0 ⊗[E] L :=
    Algebra.TensorProduct.congr
      (AlgEquiv.refl : FractionRing A0 ≃ₐ[FractionRing A0] FractionRing A0) eSimple
  have hReducedFrac :
      IsReduced (FractionRing A0 ⊗[E] L) := by
    -- Replace the simple extension by its `AdjoinRoot` model over the fraction field.
    exact isReduced_of_injective eFrac.symm.toRingHom eFrac.symm.injective
  let φ :
      A0 ⊗[E] L →+* FractionRing A0 ⊗[E] L :=
    Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom E A0 (FractionRing A0))
      (AlgHom.id E L)
  have hφ : Function.Injective φ := by
    -- Finite dimensionality of the right factor lets reducedness descend along tensoring.
    exact
      tensorProduct_map_injective_to_fractionRing_of_finiteDimensional_right
        (E := E) (A := A0) (L := L)
  letI : IsReduced (FractionRing A0 ⊗[E] L) := hReducedFrac
  -- Descend reducedness from the fraction-field tensor back to the original domain tensor.
  exact isReduced_of_injective φ hφ

/-- Helper for Lemma 10.43.6: once the field extension `K / k` is geometrically reduced, the
commutativity constraint on tensor products turns `Lemma_10_43_5` into reducedness of
`K ⊗[k] S`. -/
lemma isReduced_tensorProduct_of_geometricallyReduced_field
    [IsReduced S] [IsGeometricallyReduced k K] :
    IsReduced (K ⊗[k] S) := by
  let e : S ⊗[k] K ≃ₐ[k] K ⊗[k] S := Algebra.TensorProduct.comm k S K
  have hSK : IsReduced (S ⊗[k] K) := by
    -- Apply the geometric-reducedness tensor theorem with the reduced algebra on the left.
    exact isReduced_tensorProduct_of_geometricallyReduced (k := k) (R := S) (S := K)
  -- Transport reducedness across the tensor-product commutativity equivalence.
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective

/-- Helper for Lemma 10.43.6: an essentially finite type separably generated field extension is
geometrically reduced over the base field. -/
lemma isGeometricallyReduced_of_essFiniteType_isSeparablyGenerated
    {L : Type*} [Field L] [Algebra k L]
    [Algebra.EssFiniteType k L] [IsSeparablyGenerated k L] :
    IsGeometricallyReduced k L := by
  sorry

/-- Helper for Lemma 10.43.6: every finitely generated intermediate field of a Stacks-separable
extension is geometrically reduced over the base field. -/
lemma fg_intermediateField_isGeometricallyReduced_of_isSeparableOver
    (L : IntermediateField k K) (hL : L.FG) [IsSeparableOver k K] :
    IsGeometricallyReduced k L := by
  letI : Algebra.EssFiniteType k L := (IntermediateField.essFiniteType_iff).2 hL
  have hSepOver : IsSeparableOver k L :=
    (inferInstance : IsSeparableOver k K).of_intermediateField L
  have hTopSepGen : IsSeparablyGenerated k (⊤ : IntermediateField k L) := by
    exact hSepOver.isSeparablyGenerated_of_fg ⊤ (IntermediateField.fg_top k L)
  have hSepGen : IsSeparablyGenerated k L := by
    simpa using hTopSepGen.of_algEquiv IntermediateField.topEquiv
  letI : IsSeparablyGenerated k L := hSepGen
  -- The remaining finite-stage input is exactly the planned source-faithful theorem above.
  exact isGeometricallyReduced_of_essFiniteType_isSeparablyGenerated (k := k) (L := L)

/-- Lemma 10.43.6 (Tag 030U): if `S` is a reduced `k`-algebra and `K / k` is separable in the
sense of Definition 10.42.1(2), then the base change `K ⊗[k] S` is reduced. By
`Lemma_10_44_3`, this also applies to separably generated extensions. -/
@[stacks 030U]
theorem Lemma_10_43_6
    [IsReduced S]
    [IsSeparableOver k K] :
    IsReduced (K ⊗[k] S) := by
  -- Route correction: the tensor-commutation step is now separated from the actual blocker,
  -- namely the source-faithful proof that a Stacks-separable field extension is geometrically
  -- reduced.
  have hgeom : IsGeometricallyReduced k K := by
    -- First reduce geometric reducedness to finitely generated `k`-subalgebras of `K`.
    refine IsGeometricallyReduced.of_forall_fg ?_
    intro B hB
    rcases Subalgebra.fg_def.mp hB with ⟨t, htfin, htB⟩
    let L : IntermediateField k K := IntermediateField.adjoin k t
    have hL : L.FG := IntermediateField.fg_adjoin_of_finite htfin
    have hB_le : B ≤ L.toSubalgebra := by
      rw [← htB]
      exact IntermediateField.algebra_adjoin_le_adjoin k t
    let φ : B →ₐ[k] L :=
      { toFun := fun x ↦ ⟨x.1, hB_le x.2⟩
        map_zero' := rfl
        map_one' := rfl
        map_add' := fun _ _ ↦ rfl
        map_mul' := fun _ _ ↦ rfl
        commutes' := fun _ ↦ rfl }
    have hφ : Function.Injective φ := by
      intro x y hxy
      have hvals : ((φ x : L) : K) = ((φ y : L) : K) := by
        exact congrArg (fun z : L ↦ (z : K)) hxy
      exact Subtype.ext hvals
    letI : IsGeometricallyReduced k L :=
      fg_intermediateField_isGeometricallyReduced_of_isSeparableOver
        (k := k) (K := K) L hL
    -- Then descend geometric reducedness from the finite generated intermediate field to `B`.
    exact IsGeometricallyReduced.of_injective φ hφ
  -- Once geometric reducedness is available, Lemma `10.43.5` gives the target reducedness.
  exact @isReduced_tensorProduct_of_geometricallyReduced_field
    k K S _ _ _ _ _ inferInstance hgeom

end

section

variable {k : Type u} {K : Type v}
variable [Field k] [Field K] [Algebra k K]

/-- A field extension that is separable in the sense of Definition `10.42.1 (2)` is geometrically
reduced over the base field. -/
theorem isGeometricallyReduced_of_isSeparableOver
    [IsSeparableOver k K] :
    IsGeometricallyReduced k K := by
  refine ⟨?_⟩
  let e : AlgebraicClosure k ⊗[k] K ≃ₐ[k] K ⊗[k] AlgebraicClosure k :=
    Algebra.TensorProduct.comm k (AlgebraicClosure k) K
  letI : IsReduced (K ⊗[k] AlgebraicClosure k) := Lemma_10_43_6
  exact isReduced_of_injective e.toRingHom e.injective

@[instance low] instance [IsSeparableOver k K] : IsGeometricallyReduced k K :=
  isGeometricallyReduced_of_isSeparableOver

end

/-! ### Lemma_10_43_7 (from Chap10) -/
universe u v

open Algebra
open scoped TensorProduct

section

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]

local instance (p : minimalPrimes S) : p.1.IsPrime :=
  Ideal.minimalPrimes_isPrime p.2

/-- Helper for Lemma 10.43.7 (Tag 07K2): if the left tensor factor is a field extension, then the
canonical map from tensoring with a product to the product of tensor factors is injective. -/
lemma piRightHom_injective_of_field_left
    {K : Type*} [Field K] [Algebra k K]
    {ι : Type*} (M : ι → Type*)
    [∀ i, CommRing (M i)] [∀ i, Algebra k (M i)] :
    Function.Injective (Algebra.TensorProduct.piRightHom k K K M) := by
  classical
  let ιK := Module.Free.ChooseBasisIndex k K
  let b : Module.Basis ιK k K := Module.Free.chooseBasis k K
  let g := TensorProduct.piRightHom k K K M
  have hg : Function.Injective g := by
    intro x y hxy
    -- Compare coefficients against a `k`-basis of `K` and reduce injectivity to each component.
    let z : K ⊗[k] (∀ i, M i) := x - y
    have hzero : g z = 0 := by
      rw [show z = x - y by rfl, map_sub, hxy, sub_self]
    let c : ιK →₀ ∀ i, M i := TensorProduct.equivFinsuppOfBasisLeft b z
    have hc : c = 0 := by
      apply Finsupp.ext
      intro i
      ext j
      let cj : ιK →₀ M j := c.mapRange (fun f ↦ f j) (by simp)
      -- Evaluating the tensor-to-product map at `j` produces the basis expansion in the `j`-th
      -- factor, so zero image forces all coefficients in that factor to vanish.
      have hrepr : z = (TensorProduct.equivFinsuppOfBasisLeft b).symm c := by
        simpa [c] using ((TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply z).symm
      have hj_repr :
          g z j = cj.sum (fun i' m ↦ b i' ⊗ₜ[k] m) := by
        rw [hrepr]
        rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, map_finsuppSum]
        rw [Finsupp.sum_mapRange_index]
        · rw [Finsupp.sum, Finsupp.sum]
          simp [g]
        · intro a
          simp
      have hj_zero : cj.sum (fun i' m ↦ b i' ⊗ₜ[k] m) = 0 := by
        simpa [hj_repr] using congrArg (fun f ↦ f j) hzero
      have hcj : cj = 0 :=
        TensorProduct.sum_tmul_basis_left_eq_zero (ℬ := b) cj hj_zero
      simpa [cj] using congrArg (fun d : ιK →₀ M j ↦ d i) hcj
    have hz : z = 0 := by
      apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
      simpa [c] using hc
    exact sub_eq_zero.mp (by simpa [z] using hz)
  simpa [g] using hg

/-- Helper for Lemma 10.43.7 (Tag 07K2): the algebraic-closure base change of the product of the
minimal-prime localizations is reduced because it embeds into the product of the reduced tensor
factors. -/
lemma isReduced_algebraicClosure_tensor_minimalPrimeLocalizations
    (hlocal :
      ∀ p : minimalPrimes S,
        IsGeometricallyReduced k (Localization.AtPrime p.1)) :
    IsReduced (AlgebraicClosure k ⊗[k] (∀ p : minimalPrimes S, Localization.AtPrime p.1)) := by
  let f := Algebra.TensorProduct.piRightHom k (AlgebraicClosure k) (AlgebraicClosure k)
    (fun p : minimalPrimes S ↦ Localization.AtPrime p.1)
  have hf : Function.Injective f := by
    -- The source proof uses that a field is a free module over the base field.
    simpa using
      piRightHom_injective_of_field_left (k := k) (K := AlgebraicClosure k)
        (fun p : minimalPrimes S ↦ Localization.AtPrime p.1)
  have hfactor :
      ∀ p : minimalPrimes S, IsReduced (AlgebraicClosure k ⊗[k] Localization.AtPrime p.1) :=
    fun p ↦ by
      let _ : IsGeometricallyReduced k (Localization.AtPrime p.1) := hlocal p
      infer_instance
  let _ : ∀ p : minimalPrimes S, IsReduced (AlgebraicClosure k ⊗[k] Localization.AtPrime p.1) :=
    hfactor
  -- Descend reducedness from the product of reduced tensor factors along the injective map `f`.
  exact isReduced_of_injective f hf

-- Source-facing theorem with owner abstraction `Algebra.IsGeometricallyReduced`.
-- Proof sketch: first use `Algebra.isReduced_of_isGeometricallyReduced` on each minimal-prime
-- localization; the explicit reducedness hypothesis `hS : IsReduced S` is needed to apply the
-- canonical embedding into the product of these localizations from Lemma `10.25.2`. After
-- tensoring that embedding with `AlgebraicClosure k`, flatness preserves injectivity, while each
-- tensor factor is reduced by the geometric reducedness hypothesis on the corresponding
-- localization. Therefore `AlgebraicClosure k ⊗[k] S` is reduced.
/-- Lemma 10.43.7 (Tag 07K2): if a `k`-algebra is reduced and the localizations at all of its
minimal prime ideals are geometrically reduced over `k`, then the algebra is geometrically reduced
over `k`. -/
@[stacks 07K2]
theorem isGeometricallyReduced_of_forall_minimalPrime_localization
    (hS : IsReduced S)
    (hlocal :
      ∀ p : minimalPrimes S,
        IsGeometricallyReduced k (Localization.AtPrime p.1)) :
    IsGeometricallyReduced k S := by
  let _ : IsReduced S := hS
  let T := ∀ p : minimalPrimes S, Localization.AtPrime p.1
  let f : S →ₐ[k] T := IsScalarTower.toAlgHom k S T
  have hembed : Function.Injective f := by
    -- Lemma `10.25.2` gives the canonical embedding into the product of minimal-prime
    -- localizations once `S` is known to be reduced.
    simpa [f] using (algebraMap_embedding_into_product_of_fields (R := S)).1
  let _ : IsGeometricallyReduced k T := by
    -- The source proof first shows that the algebraic-closure base change of the product ring is
    -- reduced by embedding it into the product of the geometrically reduced local factors.
    exact ⟨isReduced_algebraicClosure_tensor_minimalPrimeLocalizations
      (k := k) (S := S) hlocal⟩
  -- Finally descend geometric reducedness along the injective canonical algebra map `S → T`.
  exact IsGeometricallyReduced.of_injective f hembed

end
