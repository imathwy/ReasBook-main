import StacksProject_2024.Chap15.Definition_15_3_1
import StacksProject_2024.Chap15.Lemma_15_3_2
import StacksProject_2024.Chap15.Lemma_15_3_3
import StacksProject_2024.Chap15.Lemma_15_129_4
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open CategoryTheory.ShortComplex

section

variable {R : Type u} [CommRing R]
variable {P : Type v} [AddCommGroup P] [Module R P] [Module.Projective R P]
variable [IsNoetherianRing (R ⧸ Ring.jacobson R)]

omit [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: a split retraction identifies the ambient module with the product
of the source and the kernel of the retraction. -/
private theorem split_linearEquiv_prod_ker
    {F : Type*} [AddCommMonoid F] [Module R F]
    (i : P →ₗ[R] F) (s : F →ₗ[R] P) (hs : s.comp i = LinearMap.id) :
    Nonempty (F ≃ₗ[R] (P × LinearMap.ker s)) := by
  letI : AddCommGroup F := Module.addCommMonoidToAddCommGroup R
  let g : P × LinearMap.ker s →ₗ[R] F := LinearMap.coprod i (LinearMap.ker s).subtype
  have hs_apply : ∀ p : P, s (i p) = p := by
    intro p
    have h := congrArg (fun t : P →ₗ[R] P => t p) hs
    simpa [LinearMap.comp_apply] using h
  have hg : Function.Bijective g := by
    constructor
    · intro x y hxy
      rcases x with ⟨px, kx⟩
      rcases y with ⟨py, ky⟩
      have hfst : px = py := by
        have h := congrArg s hxy
        simpa [g, hs_apply, LinearMap.mem_ker.mp kx.property, LinearMap.mem_ker.mp ky.property]
          using h
      subst hfst
      have hsnd : (kx : F) = ky := add_left_cancel hxy
      exact Prod.ext rfl (Subtype.ext hsnd)
    · intro x
      refine ⟨(s x, ⟨x - i (s x), ?_⟩), ?_⟩
      · rw [LinearMap.mem_ker]
        simp [LinearMap.map_sub, hs_apply]
      · simp [g, sub_eq_add_neg, add_left_comm]
  exact ⟨(LinearEquiv.ofBijective g hg).symm⟩

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: a non-finitely generated free module has an infinite chosen basis
index type. -/
private theorem chooseBasisIndex_infinite_of_not_finite
    {F : Type*} [AddCommMonoid F] [Module R F] [Module.Free R F]
    (hF : ¬ Module.Finite R F) :
    Infinite (Module.Free.ChooseBasisIndex R F) := by
  classical
  by_contra hι
  let b : Module.Basis (Module.Free.ChooseBasisIndex R F) R F := Module.Free.chooseBasis R F
  letI : Finite (Module.Free.ChooseBasisIndex R F) := Finite.of_not_infinite hι
  exact hF (Module.Finite.of_basis b)

/-- Helper for Lemma 15.129.5: an infinite type is equivalent to its product with `ℕ`. -/
private theorem nat_prod_equiv_self_of_infinite
    {ι : Type*} [Infinite ι] :
    Nonempty ((ℕ × ι) ≃ ι) := by
  have hcard : Cardinal.mk (ℕ × ι) = Cardinal.mk ι := by
    rw [Cardinal.mk_prod, Cardinal.mk_nat]
    convert (Cardinal.mk_mul_aleph0_eq (α := ι)) using 1
    · simp [mul_comm]
  exact ⟨Classical.choice (Cardinal.eq.mp hcard)⟩

/-- Helper for Lemma 15.129.5: `Option ℕ` is equivalent to `ℕ` by isolating `none` as `0`. -/
private theorem option_nat_equiv_nat :
    Nonempty (Option ℕ ≃ ℕ) := by
  refine ⟨
    { toFun := fun o =>
        match o with
        | none => 0
        | some n => n + 1
      invFun := fun n =>
        match n with
        | 0 => none
        | m + 1 => some m
      left_inv := ?_
      right_inv := ?_ }⟩
  · intro o
    cases o <;> rfl
  · intro n
    cases n <;> rfl

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: finitely supported functions on `Option α` split off the
distinguished `none` coordinate. -/
private theorem finsupp_option_linearEquiv
    {α : Type*} {M : Type*} [AddCommMonoid M] [Module R M] :
    Nonempty ((Option α →₀ M) ≃ₗ[R] (M × (α →₀ M))) := by
  let hsome : Function.Injective (@Option.some α) := fun _ _ h => Option.some.inj h
  let toMap : (Option α →₀ M) →ₗ[R] M × (α →₀ M) :=
    LinearMap.prod
      (Finsupp.lapply none)
      (Finsupp.lcomapDomain (R := R) (M := M) Option.some hsome)
  let invMap : M × (α →₀ M) →ₗ[R] Option α →₀ M :=
    LinearMap.coprod
      (Finsupp.lsingle none)
      (Finsupp.lmapDomain M R Option.some)
  refine ⟨LinearEquiv.ofLinear toMap invMap ?_ ?_⟩
  · ext x <;> simp [toMap, invMap]
  · ext o
    cases o with
    | none =>
        simp [toMap, invMap]
    | some a =>
        simp [toMap, invMap]

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: finitely supported sequences split into their head term and tail. -/
private theorem finsupp_nat_head_linearEquiv
    {M : Type*} [AddCommMonoid M] [Module R M] :
    Nonempty ((ℕ →₀ M) ≃ₗ[R] (M × (ℕ →₀ M))) := by
  obtain ⟨eOption⟩ := option_nat_equiv_nat
  obtain ⟨eSplit⟩ := finsupp_option_linearEquiv (R := R) (α := ℕ) (M := M)
  exact ⟨(Finsupp.mapDomain.linearEquiv M R eOption.symm).trans eSplit⟩

omit [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: finitely supported functions into a product split pointwise. -/
private theorem finsupp_codomain_prod_linearEquiv
    {Q : Type*} [AddCommMonoid Q] [Module R Q] {α : Type*} :
    Nonempty ((α →₀ (P × Q)) ≃ₗ[R] ((α →₀ P) × (α →₀ Q))) := by
  let toMap : (α →₀ (P × Q)) →ₗ[R] ((α →₀ P) × (α →₀ Q)) :=
    LinearMap.prod
      (Finsupp.mapRange.linearMap (LinearMap.fst R P Q))
      (Finsupp.mapRange.linearMap (LinearMap.snd R P Q))
  let invMap : ((α →₀ P) × (α →₀ Q)) →ₗ[R] (α →₀ (P × Q)) :=
    LinearMap.coprod
      (Finsupp.mapRange.linearMap (LinearMap.inl R P Q))
      (Finsupp.mapRange.linearMap (LinearMap.inr R P Q))
  refine ⟨LinearEquiv.ofLinear toMap invMap ?_ ?_⟩
  · ext x <;> simp [toMap, invMap]
  · ext a <;> simp [toMap, invMap]

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: a countable copower of an infinitely generated free module is
linearly equivalent to the original module. -/
private theorem free_countable_copower_linearEquiv_self
    {ι : Type*} [Infinite ι] :
    Nonempty ((ℕ →₀ (ι →₀ R)) ≃ₗ[R] (ι →₀ R)) := by
  obtain ⟨eNat⟩ := nat_prod_equiv_self_of_infinite (ι := ι)
  exact ⟨(Finsupp.curryLinearEquiv R).symm.trans (Finsupp.domLCongr eNat)⟩

omit [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: countably many copies of `P × Q` absorb one extra copy of `P`. -/
private theorem finsupp_pair_swindle
    {Q : Type*} [AddCommMonoid Q] [Module R Q] :
    Nonempty ((ℕ →₀ (P × Q)) ≃ₗ[R] (P × (ℕ →₀ (P × Q)))) := by
  obtain ⟨eSplit⟩ := finsupp_codomain_prod_linearEquiv (R := R) (P := P) (Q := Q) (α := ℕ)
  obtain ⟨eHead⟩ := finsupp_nat_head_linearEquiv (R := R) (M := P)
  exact
    ⟨eSplit.trans
      ((LinearEquiv.prodCongr eHead (LinearEquiv.refl R (ℕ →₀ Q))).trans
        ((LinearEquiv.prodAssoc R P (ℕ →₀ P) (ℕ →₀ Q)).trans
          (LinearEquiv.prodCongr (LinearEquiv.refl R P) eSplit.symm)))⟩

omit [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: a non-finitely generated free module absorbs a split summand. -/
private theorem nonfinitely_generated_free_absorption_of_split
    {F : Type*} [AddCommMonoid F] [Module R F] [Module.Free R F]
    {Q : Type*} [AddCommMonoid Q] [Module R Q]
    (hF : ¬ Module.Finite R F) (i : P →ₗ[R] F) (s : F →ₗ[R] P)
    (hs : s.comp i = LinearMap.id) :
    Nonempty ((P × F) ≃ₗ[R] F) := by
  letI : AddCommGroup F := Module.addCommMonoidToAddCommGroup R
  let ι := Module.Free.ChooseBasisIndex R F
  let b : Module.Basis ι R F := Module.Free.chooseBasis R F
  letI : Infinite ι := chooseBasisIndex_infinite_of_not_finite (R := R) (F := F) hF
  obtain ⟨eSplit⟩ := split_linearEquiv_prod_ker (R := R) (P := P) (F := F) i s hs
  obtain ⟨eCountBase⟩ := free_countable_copower_linearEquiv_self (R := R) (ι := ι)
  let eBasis : F ≃ₗ[R] (ι →₀ R) := b.repr
  let eCountLift : (ℕ →₀ F) ≃ₗ[R] (ℕ →₀ (ι →₀ R)) :=
    Finsupp.mapRange.linearEquiv (R := R) eBasis
  let eCount : (ℕ →₀ F) ≃ₗ[R] F := eCountLift.trans eCountBase |>.trans eBasis.symm
  obtain ⟨eSwindle⟩ :=
    finsupp_pair_swindle (R := R) (P := P) (Q := LinearMap.ker s)
  let eSplitLift : (ℕ →₀ F) ≃ₗ[R] (ℕ →₀ (P × LinearMap.ker s)) :=
    Finsupp.mapRange.linearEquiv (R := R) eSplit
  let eStart : (P × F) ≃ₗ[R] (P × (ℕ →₀ F)) := (LinearEquiv.refl R P).prodCongr eCount.symm
  let eMiddle : (P × (ℕ →₀ F)) ≃ₗ[R] (P × (ℕ →₀ (P × LinearMap.ker s))) :=
    (LinearEquiv.refl R P).prodCongr eSplitLift
  exact ⟨eStart.trans (eMiddle.trans (eSwindle.symm.trans (eSplitLift.symm.trans eCount)))⟩

namespace Module.Projective

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: every projective module becomes free after adding a suitable free
factor on the right. -/
private theorem exists_free_prod_free :
    ∃ (F : Type (max u v)) (_ : AddCommGroup F) (_ : Module R F) (_ : Module.Free R F),
      Module.Free R (P × F) := by
  classical
  by_cases hR : Subsingleton R
  · letI : Subsingleton R := hR
    letI : Subsingleton P := Module.subsingleton R P
    exact ⟨PUnit, inferInstance, inferInstance, inferInstance, inferInstance⟩
  · obtain ⟨M, _, _, _, i, r, hr⟩ := iff_split.mp (inferInstance : Module.Projective R P)
    letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
    let G := ℕ →₀ R
    have hG_not_finite : ¬ Module.Finite R G := by
      intro hG
      rcases Module.finite_finsupp_self_iff.1 hG with hsub | hfin
      · exact hR hsub
      · letI : Finite ℕ := hfin
        exact (inferInstance : Infinite ℕ).false
    have hMG_not_finite : ¬ Module.Finite R (M × G) := by
      intro hMG
      letI : Module.Finite R (M × G) := hMG
      have hG_finite : Module.Finite R G :=
        Module.Finite.of_surjective (LinearMap.snd R M G) LinearMap.snd_surjective
      exact hG_not_finite hG_finite
    let i' : P →ₗ[R] M × G := LinearMap.inl R M G ∘ₗ i
    let r' : M × G →ₗ[R] P := r ∘ₗ LinearMap.fst R M G
    have hr' : r'.comp i' = LinearMap.id := by
      ext p
      simpa [i', r'] using LinearMap.congr_fun hr p
    obtain ⟨e⟩ := nonfinitely_generated_free_absorption_of_split
      (R := R) (P := P) (F := M × G) (Q := G) hMG_not_finite i' r' hr'
    exact ⟨M × G, inferInstance, inferInstance, inferInstance, Module.Free.of_equiv e.symm⟩

end Module.Projective

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: finitely supported functions on a fixed finite set form a
complemented submodule. -/
private lemma finsupp_supported_is_complemented {ι : Type*} (t : Set ι) :
    IsComplemented (Finsupp.supported R R t : Submodule R (ι →₀ R)) := by
  have hcodisjoint : Codisjoint t tᶜ := by
    rw [codisjoint_iff]
    exact Set.union_compl_self t
  refine ⟨Finsupp.supported R R tᶜ, ?_⟩
  constructor
  · exact Finsupp.disjoint_supported_supported (M := R) (R := R) disjoint_compl_right
  · exact Finsupp.codisjoint_supported_supported (M := R) (R := R) hcodisjoint

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: a finite submodule of a free module lies in a finite free
complemented submodule cut out by finitely many basis coordinates. -/
private lemma finite_submodule_le_complemented_finite_free
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
    (N : Submodule R M) (hN : Module.Finite R N) :
    ∃ L : Complementeds (Submodule R M),
      N ≤ (L : Submodule R M) ∧
        Module.Free R (L : Submodule R M) ∧ Module.Finite R (L : Submodule R M) := by
  classical
  letI : Module.Finite R N := hN
  let b : Module.Basis (Module.Free.ChooseBasisIndex R M) R M := Module.Free.chooseBasis R M
  let Ncoord : Submodule R ((Module.Free.ChooseBasisIndex R M) →₀ R) :=
    N.map b.repr.toLinearMap
  letI : Module.Finite R Ncoord := by
    infer_instance
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := Ncoord)
  let t : Finset (Module.Free.ChooseBasisIndex R M) :=
    Finset.univ.biUnion fun i ↦ ((s i : Ncoord) : (Module.Free.ChooseBasisIndex R M) →₀ R).support
  let Kcoord : Submodule R ((Module.Free.ChooseBasisIndex R M) →₀ R) :=
    Finsupp.supported R R (↑t : Set (Module.Free.ChooseBasisIndex R M))
  have hsKcoord : ∀ i,
      (((s i : Ncoord) : (Module.Free.ChooseBasisIndex R M) →₀ R)) ∈ Kcoord := by
    intro i
    change ↑(((s i : Ncoord) : (Module.Free.ChooseBasisIndex R M) →₀ R).support) ⊆
      (↑t : Set (Module.Free.ChooseBasisIndex R M))
    intro x hx
    change x ∈ t
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩
  have htop : (⊤ : Submodule R Ncoord) ≤ Kcoord.comap Ncoord.subtype := by
    rw [← hs]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    simpa using hsKcoord i
  have htop' : Kcoord.comap Ncoord.subtype = ⊤ := top_le_iff.mp htop
  have hNcoord_le : Ncoord ≤ Kcoord := (Submodule.comap_subtype_eq_top).mp htop'
  have hKcoord_complemented : IsComplemented Kcoord :=
    finsupp_supported_is_complemented (R := R)
      (t := (↑t : Set (Module.Free.ChooseBasisIndex R M)))
  have hKcoord_free : Module.Free R Kcoord := by
    exact
      Module.Free.of_equiv
        (Finsupp.supportedEquivFinsupp
          (R := R) (M := R) (↑t : Set (Module.Free.ChooseBasisIndex R M))).symm
  have hKcoord_finite : Module.Finite R Kcoord := by
    exact
      Module.Finite.equiv
        (Finsupp.supportedEquivFinsupp
          (R := R) (M := R) (↑t : Set (Module.Free.ChooseBasisIndex R M))).symm
  let eSub : Submodule R M ≃o Submodule R ((Module.Free.ChooseBasisIndex R M) →₀ R) :=
    Submodule.orderIsoMapComap b.repr
  let L : Submodule R M := Kcoord.comap b.repr.toLinearMap
  have hN_le_L : N ≤ L := by
    simpa [L, Ncoord] using (Submodule.map_le_iff_le_comap.mp hNcoord_le)
  have hL_map : L.map b.repr.toLinearMap = Kcoord := by
    exact
      Submodule.map_comap_eq_of_surjective
        (f := b.repr.toLinearMap) b.repr.surjective Kcoord
  have hL_complemented : IsComplemented L := by
    rcases hKcoord_complemented with ⟨Kcoordc, hcompl⟩
    let Lc : Submodule R M := Kcoordc.comap b.repr.toLinearMap
    have hLc_map : Lc.map b.repr.toLinearMap = Kcoordc := by
      exact
        Submodule.map_comap_eq_of_surjective
          (f := b.repr.toLinearMap) b.repr.surjective Kcoordc
    refine ⟨Lc, ?_⟩
    have himage : IsCompl (eSub L) (eSub Lc) := by
      simpa [eSub, L, Lc, Submodule.orderIsoMapComap_apply', hL_map, hLc_map] using hcompl
    exact (eSub.isCompl_iff).2 himage
  let eL : Kcoord ≃ₗ[R] L := (LinearEquiv.ofSubmodules b.repr L Kcoord hL_map).symm
  have hL_free : Module.Free R L := by
    letI : Module.Free R Kcoord := hKcoord_free
    exact Module.Free.of_equiv eL
  have hL_finite : Module.Finite R L := by
    letI : Module.Finite R Kcoord := hKcoord_finite
    exact Module.Finite.equiv eL
  exact ⟨⟨L, hL_complemented⟩, hN_le_L, hL_free, hL_finite⟩

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: complementedness survives when restricting along a larger subtype. -/
private lemma is_complemented_comap_subtype_of_le
    {M : Type*} [AddCommGroup M] [Module R M] {K L : Submodule R M}
    (hK : IsComplemented K) (hKL : K ≤ L) :
    IsComplemented (K.comap L.subtype) := by
  rcases hK with ⟨Kc, hcompl⟩
  refine ⟨Kc.comap L.subtype, ?_⟩
  exact Submodule.isCompl_comap_subtype_of_isCompl_of_le hcompl hKL

omit [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: the natural submodule `Submodule.prod Fsub ⊤` is canonically
linearly equivalent to `Fsub × P`. -/
private theorem prod_top_equiv_prod_nonempty
    {F₀ : Type*} [AddCommGroup F₀] [Module R F₀]
    (Fsub : Submodule R F₀) :
    Nonempty (↥(Submodule.prod Fsub (⊤ : Submodule R P)) ≃ₗ[R] (Fsub × P)) := by
  let toFun : ↥(Submodule.prod Fsub (⊤ : Submodule R P)) → (Fsub × P) :=
    fun x ↦ (⟨x.1.1, x.2.1⟩, x.1.2)
  have hmem : ∀ x : Fsub × P,
      (((x.1 : F₀), x.2) : F₀ × P) ∈ Submodule.prod Fsub (⊤ : Submodule R P) := by
    intro x
    exact ⟨x.1.2, trivial⟩
  let invFun : (Fsub × P) → ↥(Submodule.prod Fsub (⊤ : Submodule R P)) :=
    fun x ↦ ⟨((x.1 : F₀), x.2), hmem x⟩
  have hleft : Function.LeftInverse invFun toFun := by
    intro x
    apply Subtype.ext
    rfl
  have hright : Function.RightInverse invFun toFun := by
    intro x
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl
  exact
    ⟨{ toFun := toFun
       invFun := invFun
       left_inv := hleft
       right_inv := hright
       map_add' := by
         intro x y
         rfl
       map_smul' := by
         intro a x
         rfl }⟩

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: every element of a projective module lies in a finite free direct
summand of `F × P` for some finite free `F`. -/
private theorem exists_finiteFree_directSummand_prod_contains_zero_s (s : P) :
    ∃ (F : Type (max u v)) (_ : AddCommGroup F) (_ : Module R F) (_ : Module.Free R F)
      (_ : Module.Finite R F),
      ∃ K : Complementeds (Submodule R (F × P)),
        Module.Free R (K : Submodule R (F × P)) ∧
          Module.Finite R (K : Submodule R (F × P)) ∧ ((0 : F), s) ∈ (K : Submodule R (F × P)) := by
  classical
  obtain ⟨F₀, _, _, hF₀_free, hprod_free⟩ :=
    Module.Projective.exists_free_prod_free (R := R) (P := P)
  have hAmbient_free : Module.Free R (F₀ × P) := by
    letI : Module.Free R (P × F₀) := hprod_free
    exact Module.Free.of_equiv (LinearEquiv.prodComm R P F₀)
  letI : Module.Free R (F₀ × P) := hAmbient_free
  let x : F₀ × P := ((0 : F₀), s)
  have hx_span_finite : Module.Finite R (R ∙ x) := by
    infer_instance
  obtain ⟨K₀, hx_span_le_K₀, hK₀_free, hK₀_finite⟩ :=
    finite_submodule_le_complemented_finite_free
      (R := R) (M := F₀ × P) (N := R ∙ x) hx_span_finite
  have hx_mem_span : x ∈ R ∙ x := by
    simp [x]
  have hx_mem_K₀ : x ∈ (K₀ : Submodule R (F₀ × P)) := hx_span_le_K₀ hx_mem_span
  letI : Module.Finite R (K₀ : Submodule R (F₀ × P)) := hK₀_finite
  let Fimage : Submodule R F₀ :=
    Submodule.map (LinearMap.fst R F₀ P) (K₀ : Submodule R (F₀ × P))
  have hFimage_finite : Module.Finite R Fimage := by
    infer_instance
  obtain ⟨FsubCompl, hFimage_le_Fsub, hFsub_free, hFsub_finite⟩ :=
    finite_submodule_le_complemented_finite_free
      (R := R) (M := F₀) (N := Fimage) hFimage_finite
  let Fsub : Submodule R F₀ := FsubCompl
  let A : Submodule R (F₀ × P) := Submodule.prod Fsub (⊤ : Submodule R P)
  have hK₀_le_A : (K₀ : Submodule R (F₀ × P)) ≤ A := by
    rw [Submodule.le_prod_iff]
    constructor
    · simpa [Fimage, Fsub] using hFimage_le_Fsub
    · exact le_top
  let Kinside : Submodule R A := (K₀ : Submodule R (F₀ × P)).comap A.subtype
  have hKinside_complemented : IsComplemented Kinside :=
    is_complemented_comap_subtype_of_le (R := R) K₀.2 hK₀_le_A
  have hKinside_free : Module.Free R Kinside := by
    let eInside : (K₀ : Submodule R (F₀ × P)) ≃ₗ[R] Kinside :=
      (Submodule.submoduleOfEquivOfLe hK₀_le_A).symm
    letI : Module.Free R (K₀ : Submodule R (F₀ × P)) := hK₀_free
    exact Module.Free.of_equiv eInside
  have hKinside_finite : Module.Finite R Kinside := by
    let eInside : (K₀ : Submodule R (F₀ × P)) ≃ₗ[R] Kinside :=
      (Submodule.submoduleOfEquivOfLe hK₀_le_A).symm
    letI : Module.Finite R (K₀ : Submodule R (F₀ × P)) := hK₀_finite
    exact Module.Finite.equiv eInside
  have hx_mem_A : x ∈ A := hK₀_le_A hx_mem_K₀
  let xA : A := ⟨x, hx_mem_A⟩
  have hxA_mem_Kinside : xA ∈ Kinside := hx_mem_K₀
  let eProdToFun : A → (Fsub × P) := fun x ↦ (⟨x.1.1, x.2.1⟩, x.1.2)
  let eProdInvFun : (Fsub × P) → A := fun x ↦ ⟨((x.1 : F₀), x.2), ⟨x.1.2, trivial⟩⟩
  have hProdLeft : Function.LeftInverse eProdInvFun eProdToFun := by
    intro x
    apply Subtype.ext
    rfl
  have hProdRight : Function.RightInverse eProdInvFun eProdToFun := by
    intro x
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl
  let eProd : A ≃ₗ[R] (Fsub × P) :=
    { toFun := eProdToFun
      invFun := eProdInvFun
      left_inv := hProdLeft
      right_inv := hProdRight
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro a x
        rfl }
  let eProdSub : Submodule R A ≃o Submodule R (Fsub × P) := Submodule.orderIsoMapComap eProd
  let KfinalSub : Submodule R (Fsub × P) := eProdSub Kinside
  have hKfinal_complemented : IsComplemented KfinalSub := by
    rcases hKinside_complemented with ⟨C, hcompl⟩
    refine ⟨eProdSub C, ?_⟩
    simpa [KfinalSub, eProdSub] using eProdSub.isCompl hcompl
  have hKfinal_map : Kinside.map eProd.toLinearMap = KfinalSub := by
    simp [KfinalSub, eProdSub]
  have hKfinal_free : Module.Free R KfinalSub := by
    let eKfinal : Kinside ≃ₗ[R] KfinalSub := LinearEquiv.ofSubmodules eProd Kinside KfinalSub hKfinal_map
    letI : Module.Free R Kinside := hKinside_free
    exact Module.Free.of_equiv eKfinal
  have hKfinal_finite : Module.Finite R KfinalSub := by
    let eKfinal : Kinside ≃ₗ[R] KfinalSub := LinearEquiv.ofSubmodules eProd Kinside KfinalSub hKfinal_map
    letI : Module.Finite R Kinside := hKinside_finite
    exact Module.Finite.equiv eKfinal
  have hxA_image : eProd xA = ((0 : Fsub), s) := by
    rfl
  have hxA_mem_Kfinal : eProd xA ∈ KfinalSub := by
    exact ⟨xA, hxA_mem_Kinside, rfl⟩
  have htarget_mem : ((0 : Fsub), s) ∈ KfinalSub := by
    simpa [hxA_image] using hxA_mem_Kfinal
  refine ⟨Fsub, inferInstance, inferInstance, hFsub_free, hFsub_finite, ?_⟩
  exact ⟨⟨KfinalSub, hKfinal_complemented⟩, hKfinal_free, hKfinal_finite, htarget_mem⟩

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: if the localized module of a submodule is finite, then the
localized copy of that submodule inside the localized ambient module is finite as well. -/
lemma localized_submodule_finite_of_localized_module_finite
    {M : Type v} [AddCommGroup M] [Module R M]
    (K : Submodule R M) (m : MaximalSpectrum R)
    [hKloc :
      Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal K)] :
    Module.Finite (Localization.AtPrime m.asIdeal)
      ((Submodule.localized (p := m.asIdeal.primeCompl) K :
          Submodule (Localization.AtPrime m.asIdeal)
            (LocalizedModule.AtPrime m.asIdeal M))) := by
  let locMap :
      LocalizedModule.AtPrime m.asIdeal K →ₗ[Localization.AtPrime m.asIdeal]
        LocalizedModule.AtPrime m.asIdeal M :=
    LocalizedModule.map m.asIdeal.primeCompl K.subtype
  have hrange0 :
      (((LinearMap.restrictScalars R locMap).range :
          Submodule R (LocalizedModule.AtPrime m.asIdeal M))) =
        (Submodule.localized₀ m.asIdeal.primeCompl
          (LocalizedModule.mkLinearMap m.asIdeal.primeCompl M) K :
            Submodule R (LocalizedModule.AtPrime m.asIdeal M)) := by
    -- The localized image of the inclusion is exactly the canonical localized-copy owner.
    simpa [locMap, Submodule.range_subtype] using
      (LinearMap.range_localizedMap_eq_localized₀_range
        (p := m.asIdeal.primeCompl)
        (f := LocalizedModule.mkLinearMap m.asIdeal.primeCompl K)
        (f' := LocalizedModule.mkLinearMap m.asIdeal.primeCompl M)
        (g := K.subtype))
  have hrange :
      locMap.range =
        (Submodule.localized (p := m.asIdeal.primeCompl) K :
          Submodule (Localization.AtPrime m.asIdeal)
            (LocalizedModule.AtPrime m.asIdeal M)) := by
    -- Rewrite the range equality through the `localized₀` carrier description of
    -- `Submodule.localized`.
    ext x
    change x ∈ (((LinearMap.restrictScalars R locMap).range :
      Submodule R (LocalizedModule.AtPrime m.asIdeal M)) : Set
        (LocalizedModule.AtPrime m.asIdeal M)) ↔
      x ∈ (Submodule.localized₀ m.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap m.asIdeal.primeCompl M) K :
          Submodule R (LocalizedModule.AtPrime m.asIdeal M))
    simp [hrange0]
  letI :
      Module.Finite (Localization.AtPrime m.asIdeal)
        (LinearMap.range locMap) := by
    infer_instance
  rw [← hrange]
  infer_instance

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: non-finite localizations persist after adjoining any left module
factor. -/
lemma localizations_not_finite_prod_left
    {F : Type*} [AddCommGroup F] [Module R F]
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    (hQ : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal Q)) :
    ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal)
        (LocalizedModule.AtPrime m.asIdeal (F × Q)) := by
  intro m hprod
  let sndLoc :
      LocalizedModule.AtPrime m.asIdeal (F × Q) →ₗ[Localization.AtPrime m.asIdeal]
        LocalizedModule.AtPrime m.asIdeal Q :=
    LocalizedModule.map m.asIdeal.primeCompl (LinearMap.snd R F Q)
  have hsndLoc_surj : Function.Surjective sndLoc := by
    -- Localization preserves the surjectivity of the second projection, so any finite generating
    -- set upstairs would descend to one for `Q`.
    simpa [sndLoc] using
      LocalizedModule.map_surjective m.asIdeal.primeCompl
        (LinearMap.snd R F Q)
        (LinearMap.snd_surjective : Function.Surjective (LinearMap.snd R F Q))
  have hQfinite :
      Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal Q) :=
    Module.Finite.of_surjective sndLoc hsndLoc_surj
  exact hQ m hQfinite

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: if `K` is a finite complemented summand in `R × Q`, then the
localizations of its complement are still not finite. -/
lemma complement_localizations_not_finite_of_finite_summand
    {Q : Type v} [AddCommGroup Q] [Module R Q]
    (hQ : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal Q))
    (K K' : Submodule R (R × Q)) (hKK' : IsCompl K K')
    [Module.Finite R K] :
    ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal K') := by
  intro m hK'loc
  have hAmbient :
      ¬ Module.Finite (Localization.AtPrime m.asIdeal)
        (LocalizedModule.AtPrime m.asIdeal (R × Q)) :=
    localizations_not_finite_prod_left (R := R) hQ m
  let eQuot : ((R × Q) ⧸ K') ≃ₗ[R] K :=
    Submodule.quotientEquivOfIsCompl K' K hKK'.symm
  have hfiniteQuot : Module.Finite R ((R × Q) ⧸ K') := by
    exact Module.Finite.equiv eQuot.symm
  have hlocalizedK' :
      Module.Finite (Localization.AtPrime m.asIdeal)
        ((Submodule.localized (p := m.asIdeal.primeCompl) K' :
            Submodule (Localization.AtPrime m.asIdeal)
              (LocalizedModule.AtPrime m.asIdeal (R × Q)))) := by
    letI :
        Module.Finite (Localization.AtPrime m.asIdeal)
          (LocalizedModule.AtPrime m.asIdeal K') := hK'loc
    exact localized_submodule_finite_of_localized_module_finite (R := R) K' m
  exact localized_common_kernel_not_finite_at_lieover
    (R := R) (P := R × Q) m hfiniteQuot hAmbient hlocalizedK'

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: a zero-rank free factor on the left does not change the ambient
product module. -/
theorem prod_fin_zero_left_linearEquiv_nonempty
    {Q : Type*} [AddCommGroup Q] [Module R Q] :
    Nonempty (((Fin 0 → R) × Q) ≃ₗ[R] Q) := by
  rcases prod_fin_zero_linearEquiv_nonempty (R := R) (M := Q) with ⟨e⟩
  -- First commute the zero-rank block to the right, then cancel it using the chapter API.
  exact ⟨(LinearEquiv.prodComm R (Fin 0 → R) Q).trans e.symm⟩

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: a successor finite free coordinate module splits as the previous
block together with one rank-one free factor. -/
theorem fin_succ_arrow_linearEquiv_nonempty
    (n : ℕ) :
    Nonempty ((Fin (n + 1) → R) ≃ₗ[R] ((Fin n → R) × R)) := by
  rcases fin_append_linearEquiv_nonempty (R := R) n 1 with ⟨eAppend⟩
  let eOne : (Fin 1 → R) ≃ₗ[R] R := LinearEquiv.funUnique (Fin 1) R R
  -- Rewrite the `Fin (n + 1)` block as `Fin n ⊕ Fin 1`, then identify the one-coordinate tail
  -- with the free rank-one module `R`.
  exact ⟨eAppend.symm.trans (LinearEquiv.prodCongr (LinearEquiv.refl R (Fin n → R)) eOne)⟩

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: complemented submodules remain complemented after transport across
an ambient linear equivalence. -/
lemma isComplemented_map_of_linearEquiv
    {A : Type*} [AddCommGroup A] [Module R A]
    {B : Type*} [AddCommGroup B] [Module R B]
    (e : A ≃ₗ[R] B) (K : Submodule R A) (hK : IsComplemented K) :
    IsComplemented (K.map e.toLinearMap) := by
  let eSub : Submodule R A ≃o Submodule R B := Submodule.orderIsoMapComap e
  rcases hK with ⟨C, hcompl⟩
  -- Transport the chosen complement through the submodule order isomorphism induced by `e`.
  refine ⟨eSub C, ?_⟩
  simpa [eSub] using eSub.isCompl hcompl

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: finite generation of a submodule is preserved by transport across an
ambient linear equivalence. -/
lemma module_finite_map_of_linearEquiv
    {A : Type*} [AddCommGroup A] [Module R A]
    {B : Type*} [AddCommGroup B] [Module R B]
    (e : A ≃ₗ[R] B) (K : Submodule R A) (hKfinite : Module.Finite R K) :
    Module.Finite R (K.map e.toLinearMap) := by
  let eK : K ≃ₗ[R] K.map e.toLinearMap :=
    LinearEquiv.ofSubmodules e K (K.map e.toLinearMap) rfl
  letI : Module.Finite R K := hKfinite
  -- Restrict the ambient equivalence to the transported image of `K`.
  exact Module.Finite.equiv eK

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: stable freeness of a submodule is preserved by transport across an
ambient linear equivalence. -/
lemma stablyFree_map_of_linearEquiv
    {A : Type v} [AddCommGroup A] [Module R A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (e : A ≃ₗ[R] B) (K : Submodule R A)
    (hKfinite : Module.Finite R K) (hKstablyFree : Module.StablyFree R K) :
    Module.StablyFree R (K.map e.toLinearMap) := by
  let eK : K ≃ₗ[R] K.map e.toLinearMap :=
    LinearEquiv.ofSubmodules e K (K.map e.toLinearMap) rfl
  letI : Module.Finite R K := hKfinite
  letI : Module.StablyFree R K := hKstablyFree
  have hKStabilization :
      ∃ m n : ℕ, Nonempty ((K × (Fin m → R)) ≃ₗ[R] (Fin n → R)) :=
    CategoryTheory.ShortComplex.finite_stablyFree_exists_fin_stabilization (R := R) (M := K)
  have hMapStabilization :
      ∃ m n : ℕ, Nonempty (((K.map e.toLinearMap) × (Fin m → R)) ≃ₗ[R] (Fin n → R)) :=
    CategoryTheory.ShortComplex.fin_stabilization_of_equiv (R := R) (M := K.map e.toLinearMap)
      (N := K) eK.symm hKStabilization
  exact CategoryTheory.ShortComplex.stablyFree_of_fin_stabilization
    (R := R) (M := K.map e.toLinearMap) hMapStabilization

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: for a chosen complement of `K ≤ R × Q`, the complement projection is
generated by the image of `(1, 0)` together with the image of the right factor. -/
lemma rank_one_complement_projection_span_top
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    (K Kc : Submodule R (R × Q)) (hKKc : IsCompl K Kc) :
    let π : (R × Q) →ₗ[R] Kc := Kc.linearProjOfIsCompl K hKKc.symm
    R ∙ π (1, 0) + LinearMap.range (π.comp (LinearMap.inr R R Q)) = ⊤ := by
  dsimp
  let π : (R × Q) →ₗ[R] Kc := Kc.linearProjOfIsCompl K hKKc.symm
  ext x
  constructor
  · intro hx
    simp
  · intro hx
    have hπx : π x.1 = x := by
      -- On elements already in the chosen complement, the projection is the identity.
      exact LinearMap.congr_fun (Kc.linearProjOfIsCompl_comp_subtype hKKc.symm) x
    have hx_decomp :
        x = x.1.1 • π (1, 0) + (π.comp (LinearMap.inr R R Q)) x.1.2 := by
      -- Split the ambient pair into its left scalar part and right-factor part, then project.
      calc
        x = π x.1 := hπx.symm
        _ = x.1.1 • π (1, 0) + π (0, x.1.2) := by
          rw [← map_smul, ← map_add]
          congr 1
          ext <;> simp
        _ = x.1.1 • π (1, 0) + (π.comp (LinearMap.inr R R Q)) x.1.2 := by
          rfl
    refine Submodule.mem_sup.2 ?_
    refine ⟨x.1.1 • π (1, 0), ?_, (π.comp (LinearMap.inr R R Q)) x.1.2, ?_, hx_decomp.symm⟩
    · exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    · exact ⟨x.1.2, rfl⟩

/-- Helper for Lemma 15.129.5: after applying Lemma `15.129.4` to the chosen complement of
`K ≤ R × Q`, the free cyclic summand can be written as `R ∙ π (1, p)` for a concrete `p : Q`. -/
lemma exists_rank_one_cyclic_complement_data
    {Q : Type*} [AddCommGroup Q] [Module R Q] [Module.Projective R Q]
    (hnotFiniteAtMax : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal Q))
    (K Kc : Submodule R (R × Q)) (hKKc : IsCompl K Kc)
    [Module.Finite R K] :
    let π : (R × Q) →ₗ[R] Kc := Kc.linearProjOfIsCompl K hKKc.symm
    ∃ p : Q, ∃ K'' : Submodule R Kc,
      IsCompl (R ∙ π (1, p)) K'' ∧
      Module.Free R (R ∙ π (1, p)) ∧
      Module.Finite R (R ∙ π (1, p)) := by
  dsimp
  let π : (R × Q) →ₗ[R] Kc := Kc.linearProjOfIsCompl K hKKc.symm
  letI : Module.Projective R Kc :=
    Module.Projective.of_split Kc.subtype π (by
      -- The chosen complement projection is a section of the subtype inclusion.
      simpa [π] using Kc.linearProjOfIsCompl_comp_subtype hKKc.symm)
  have hKc_notFinite :
      ∀ m : MaximalSpectrum R,
        ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal Kc) :=
    complement_localizations_not_finite_of_finite_summand (R := R) hnotFiniteAtMax K Kc hKKc
  have hspan :
      R ∙ π (1, 0) + LinearMap.range (π.comp (LinearMap.inr R R Q)) = ⊤ :=
    rank_one_complement_projection_span_top (R := R) K Kc hKKc
  obtain ⟨m, hmCompl, hmFree⟩ :=
    exists_perturbation_with_cyclicSpan_free_directSummand
      (R := R) (P := Kc)
      (M := LinearMap.range (π.comp (LinearMap.inr R R Q)))
      (s := π (1, 0)) hKc_notFinite hspan
  rcases m with ⟨m, hm⟩
  rcases hm with ⟨p, rfl⟩
  have hvec :
      π (1, 0) + (π.comp (LinearMap.inr R R Q)) p = π (1, p) := by
    -- The perturbation term lies in the projected right factor, so the corrected generator is
    -- exactly the projection of `(1, p)`.
    change π (1, 0) + π (0, p) = π (1, p)
    rw [← LinearMap.map_add]
    congr 1
    ext <;> simp
  have hspan_eq : (R ∙ (π (1, 0) + (π.comp (LinearMap.inr R R Q)) p) : Submodule R Kc) = R ∙ π (1, p) := by
    rw [hvec]
  have hmCompl' : IsComplemented (R ∙ π (1, p)) := by
    exact hspan_eq ▸ hmCompl
  have hmFree' : Module.Free R (R ∙ π (1, p)) := by
    exact hspan_eq ▸ hmFree
  have hmFinite' : Module.Finite R (R ∙ π (1, p)) := by
    infer_instance
  rcases hmCompl' with ⟨K'', hK''⟩
  exact ⟨p, K'', hK'', hmFree', hmFinite'⟩

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: the kernel of the projection onto a complement is the original
summand. -/
lemma ker_linearProjOfIsCompl_eq_left
    {X : Type*} [AddCommGroup X] [Module R X]
    (L K'' : Submodule R X) (hLK'' : IsCompl L K'') :
    LinearMap.ker (K''.linearProjOfIsCompl L hLK''.symm) = L := by
  -- This is the canonical kernel computation for the complement projection.
  exact Submodule.linearProjOfIsCompl_ker (p := K'') (q := L) hLK''.symm

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: the residual projection to the chosen complement of the cyclic
rank-one summand is surjective and splits because the target is projective. -/
lemma exists_split_residual_projection_of_rank_one_complement
    {Q : Type*} [AddCommGroup Q] [Module R Q] [Module.Projective R Q]
    (K Kc : Submodule R (R × Q)) (hKKc : IsCompl K Kc)
    (p : Q) (K'' : Submodule R Kc)
    (hLK'' : IsCompl (R ∙ (Kc.linearProjOfIsCompl K hKKc.symm) (1, p)) K'') :
    let π : (R × Q) →ₗ[R] Kc := Kc.linearProjOfIsCompl K hKKc.symm
    let L : Submodule R Kc := R ∙ π (1, p)
    let ρ : Kc →ₗ[R] K'' := K''.linearProjOfIsCompl L hLK''.symm
    let π' : Q →ₗ[R] K'' := ρ.comp (π.comp (LinearMap.inr R R Q))
    ∃ σ : K'' →ₗ[R] Q, π'.comp σ = LinearMap.id ∧ Function.Surjective π' := by
  dsimp
  let π : (R × Q) →ₗ[R] Kc := Kc.linearProjOfIsCompl K hKKc.symm
  let L : Submodule R Kc := R ∙ π (1, p)
  let ρ : Kc →ₗ[R] K'' := K''.linearProjOfIsCompl L hLK''.symm
  let π' : Q →ₗ[R] K'' := ρ.comp (π.comp (LinearMap.inr R R Q))
  have hπ_subtype : ∀ y : K'', π (Kc.subtype y) = (y : Kc) := by
    intro y
    -- The complement projection is the identity on the chosen complement `Kc`.
    exact LinearMap.congr_fun (Kc.linearProjOfIsCompl_comp_subtype hKKc.symm) (y : Kc)
  have hρ_left : ∀ y : K'', ρ (y : Kc) = y := by
    intro y
    -- The residual projection is the identity on the residual complement `K''`.
    exact Submodule.linearProjOfIsCompl_apply_left (p := K'') (q := L) hLK''.symm y
  have hρ_generator : ρ (π (1, p)) = 0 := by
    -- The distinguished generator lies in `L`, so the complementary projection kills it.
    have hmem : π (1, p) ∈ L := by
      exact Submodule.subset_span (by simp)
    exact Submodule.linearProjOfIsCompl_apply_right' (p := K'') (q := L) hLK''.symm (π (1, p)) hmem
  have hπ'surj : Function.Surjective π' := by
    intro y
    let a : R := (Kc.subtype y).1
    let x : Q := (Kc.subtype y).2
    refine ⟨x - a • p, ?_⟩
    -- The correction term `a • p` removes the `L`-component and leaves exactly `y`.
    change ρ (π (0, x - a • p)) = y
    have hpair :
        (0, x - a • p) = (Kc.subtype y : R × Q) - a • ((1 : R), p) := by
      ext <;> simp [a, x]
    rw [hpair, map_sub, map_smul, map_sub, map_smul]
    rw [hπ_subtype, hρ_left, hρ_generator]
    simp
  letI : Module.Projective R Kc :=
    Module.Projective.of_split Kc.subtype π (by
      -- The chosen complement projection splits the inclusion `Kc → R × Q`.
      simpa [π] using Kc.linearProjOfIsCompl_comp_subtype hKKc.symm)
  letI : Module.Projective R K'' :=
    Module.Projective.of_split K''.subtype ρ (by
      -- The residual projection splits the inclusion `K'' → Kc`.
      simpa [ρ] using K''.linearProjOfIsCompl_comp_subtype hLK''.symm)
  obtain ⟨σ, hσ⟩ :=
    Module.projective_lifting_property π' (LinearMap.id : K'' →ₗ[R] K'') hπ'surj
  exact ⟨σ, hσ, hπ'surj⟩

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: membership in the kernel of the residual projection is equivalent to
having complement projection in the cyclic rank-one summand. -/
lemma mem_ker_residual_projection_iff
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    (K Kc : Submodule R (R × Q)) (hKKc : IsCompl K Kc)
    (p : Q) (K'' : Submodule R Kc)
    (hLK'' : IsCompl (R ∙ (Kc.linearProjOfIsCompl K hKKc.symm) (1, p)) K'')
    (x : Q) :
    let π : (R × Q) →ₗ[R] Kc := Kc.linearProjOfIsCompl K hKKc.symm
    let L : Submodule R Kc := R ∙ π (1, p)
    let ρ : Kc →ₗ[R] K'' := K''.linearProjOfIsCompl L hLK''.symm
    let π' : Q →ₗ[R] K'' := ρ.comp (π.comp (LinearMap.inr R R Q))
    x ∈ LinearMap.ker π' ↔ π (0, x) ∈ L := by
  dsimp
  let π : (R × Q) →ₗ[R] Kc := Kc.linearProjOfIsCompl K hKKc.symm
  let L : Submodule R Kc := R ∙ π (1, p)
  let ρ : Kc →ₗ[R] K'' := K''.linearProjOfIsCompl L hLK''.symm
  let π' : Q →ₗ[R] K'' := ρ.comp (π.comp (LinearMap.inr R R Q))
  -- Rewrite the residual-kernel condition through the kernel of the complement projection `ρ`.
  change ρ (π (0, x)) = 0 ↔ π (0, x) ∈ L
  rw [← LinearMap.mem_ker, ker_linearProjOfIsCompl_eq_left (R := R) L K'' hLK'']

/-- Helper for Lemma 15.129.5: the source rank-one paragraph removes the left copy of `R` from a
finite stably free summand inside `R × Q`. -/
theorem exists_finiteStablyFree_directSummand_submodule_containing_of_rank_one_prod
    {Q : Type*} [AddCommGroup Q] [Module R Q] [Module.Projective R Q]
    (q : Q)
    (hnotFiniteAtMax : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal Q))
    (K : Complementeds (Submodule R (R × Q)))
    (hKfinite : Module.Finite R (K : Submodule R (R × Q)))
    (hKstablyFree : Module.StablyFree R (K : Submodule R (R × Q)))
    (hqK : ((0 : R), q) ∈ (K : Submodule R (R × Q))) :
    ∃ M : Submodule R Q, q ∈ M ∧ IsComplemented M ∧ Module.Finite R M ∧ Module.StablyFree R M := by
  -- Route correction: the complement span identity and the concrete perturbation witness `p : Q`
  -- are now isolated, so we can follow the source paragraph literally: split the residual map
  -- `Q → K''`, take its kernel, and compare `R × ker(π')` with `K × (R ∙ π (1, p))`.
  rcases K.2 with ⟨Kc, hKKc⟩
  let π : (R × Q) →ₗ[R] Kc := Kc.linearProjOfIsCompl (K : Submodule R (R × Q)) hKKc.symm
  letI : Module.Finite R (K : Submodule R (R × Q)) := hKfinite
  obtain ⟨p, K'', hLK'', hLfree, hLfinite⟩ :=
    exists_rank_one_cyclic_complement_data (R := R) hnotFiniteAtMax (K : Submodule R (R × Q)) Kc hKKc
  let L : Submodule R Kc := R ∙ π (1, p)
  have hLK''L : IsCompl L K'' := by
    simpa [L, π] using hLK''
  let ρ : Kc →ₗ[R] K'' := K''.linearProjOfIsCompl L hLK''L.symm
  let π' : Q →ₗ[R] K'' := ρ.comp (π.comp (LinearMap.inr R R Q))
  obtain ⟨σ, hσ, _hπ'surj⟩ :=
    exists_split_residual_projection_of_rank_one_complement
      (R := R) (Q := Q) (K : Submodule R (R × Q)) Kc hKKc p K'' (by
        simpa [L, π] using hLK''L)
  let M : Submodule R Q := LinearMap.ker π'
  have hqM : q ∈ M := by
    -- The distinguished element already lies in `K`, so the complement projection sends it to `0`.
    change q ∈ LinearMap.ker π'
    refine (mem_ker_residual_projection_iff (R := R) (K : Submodule R (R × Q)) Kc hKKc p K''
      (by simpa [L, π] using hLK''L) q).2 ?_
    have hπq : π ((0 : R), q) = 0 := by
      exact Submodule.linearProjOfIsCompl_apply_right' (p := Kc) (q := (K : Submodule R (R × Q)))
        hKKc.symm ((0 : R), q) hqK
    rw [hπq]
    exact zero_mem L
  have hσ_apply : ∀ y : K'', π' (σ y) = y := by
    intro y
    exact LinearMap.congr_fun hσ y
  let projKerRaw : Q →ₗ[R] Q := LinearMap.id - σ.comp π'
  have hprojKer_mem : ∀ x : Q, projKerRaw x ∈ M := by
    intro x
    -- The retraction `id - σ ∘ π'` lands in `ker π'`.
    change π' (projKerRaw x) = 0
    simp [projKerRaw, hσ_apply]
  let projKer : Q →ₗ[R] M := LinearMap.codRestrict M projKerRaw hprojKer_mem
  have hprojKer_id : ∀ x : M, projKer x = x := by
    intro x
    apply Subtype.ext
    -- On the kernel, the correction term vanishes.
    change projKerRaw x = x
    simp [projKerRaw, LinearMap.mem_ker.mp x.2]
  have hMcompl : IsComplemented M := by
    refine ⟨LinearMap.ker projKer, LinearMap.isCompl_of_proj hprojKer_id⟩
  let generatorMap : R →ₗ[R] R × Q :=
    (LinearMap.id : R →ₗ[R] R).prod ((LinearMap.id : R →ₗ[R] R).smulRight p)
  let kernelInclusion : M →ₗ[R] R × Q :=
    (LinearMap.inr R R Q).comp M.subtype
  let ambientOfKer : (R × M) →ₗ[R] R × Q :=
    LinearMap.coprod generatorMap kernelInclusion
  let kComponent : (R × M) →ₗ[R] (K : Submodule R (R × Q)) :=
    ((K : Submodule R (R × Q)).linearProjOfIsCompl Kc hKKc).comp ambientOfKer
  let lRaw : (R × M) →ₗ[R] Kc := π.comp ambientOfKer
  have hlRaw_mem : ∀ z : R × M, lRaw z ∈ L := by
    intro z
    have hz_mem : π ((0 : R), (z.2 : Q)) ∈ L := by
      exact (mem_ker_residual_projection_iff (R := R) (K : Submodule R (R × Q)) Kc hKKc p K''
        (by simpa [L, π] using hLK''L) (z.2 : Q)).1 z.2.2
    -- The ambient point `(a, x + a • p)` differs from `(0, x)` by the chosen generator.
    change π (ambientOfKer z) ∈ L
    have hdecomp :
        ambientOfKer z = z.1 • ((1 : R), p) + (0, (z.2 : Q)) := by
      ext <;> simp [ambientOfKer, generatorMap, kernelInclusion, add_comm]
    rw [hdecomp, map_add]
    refine Submodule.add_mem L ?_ hz_mem
    have hgen : π (1, p) ∈ L := Submodule.subset_span (by simp)
    have hsmul : z.1 • π (1, p) ∈ L := Submodule.smul_mem L z.1 hgen
    have hscaled : π (z.1 • ((1 : R), p)) = z.1 • π (1, p) := by
      rw [map_smul]
    rw [hscaled]
    exact hsmul
  let lComponent : (R × M) →ₗ[R] L := LinearMap.codRestrict L lRaw hlRaw_mem
  let KL : Type _ := ↥(K : Submodule R (R × Q)) × ↥L
  letI : AddCommGroup KL := inferInstance
  letI : Module R KL := inferInstance
  let forward : (R × M) →ₗ[R] KL :=
    LinearMap.prod kComponent lComponent
  let ambientSum : KL →ₗ[R] (R × Q) :=
    LinearMap.coprod (K : Submodule R (R × Q)).subtype (Kc.subtype.comp L.subtype)
  let fstAmbient : KL →ₗ[R] R :=
    (LinearMap.fst R R Q).comp ambientSum
  let sndAmbient : KL →ₗ[R] Q :=
    (LinearMap.snd R R Q).comp ambientSum
  let rawSecond : KL →ₗ[R] Q :=
    sndAmbient - fstAmbient.smulRight p
  have hrawSecond_mem : ∀ w : KL, rawSecond w ∈ M := by
    intro w
    change rawSecond w ∈ LinearMap.ker π'
    refine (mem_ker_residual_projection_iff (R := R) (K : Submodule R (R × Q)) Kc hKKc p K''
      (by simpa [L, π] using hLK''L) (rawSecond w)).2 ?_
    have hpair :
        ((0 : R), rawSecond w) = ambientSum w - (fstAmbient w) • ((1 : R), p) := by
      ext <;> simp [rawSecond, fstAmbient, sndAmbient]
    rw [hpair, map_sub, map_smul]
    have hπAmbient : π (ambientSum w) = w.2 := by
      -- Recombine the `K ⊕ Kc` decomposition and read off the `Kc`-component.
      change π ((w.1 : R × Q) + Kc.subtype (w.2 : Kc)) = w.2
      rw [map_add]
      have hKzero :
          π (w.1 : R × Q) = 0 := by
        exact Submodule.linearProjOfIsCompl_apply_right' (p := Kc) (q := (K : Submodule R (R × Q)))
          hKKc.symm (w.1 : R × Q) w.1.2
      have hKid :
          π (Kc.subtype (w.2 : Kc)) = (w.2 : Kc) := by
        exact LinearMap.congr_fun (Kc.linearProjOfIsCompl_comp_subtype hKKc.symm) (w.2 : Kc)
      simpa [hKzero, hKid]
    rw [hπAmbient]
    refine Submodule.sub_mem L w.2.2 ?_
    have hgen : π (1, p) ∈ L := Submodule.subset_span (by simp)
    have hsmul : fstAmbient w • π (1, p) ∈ L := Submodule.smul_mem L (fstAmbient w) hgen
    exact hsmul
  let secondComponent : KL →ₗ[R] M :=
    LinearMap.codRestrict M rawSecond hrawSecond_mem
  let inverse : KL →ₗ[R] (R × M) :=
    LinearMap.prod fstAmbient secondComponent
  have hambientSum_forward : ∀ z : R × M, ambientSum (forward z) = ambientOfKer z := by
    intro z
    -- Compare both sides via the complementary projections onto `K` and `Kc`.
    let projK : (R × Q) →ₗ[R] (K : Submodule R (R × Q)) :=
      (K : Submodule R (R × Q)).linearProjOfIsCompl Kc hKKc
    have hprojK :
        projK (ambientSum (forward z)) = projK (ambientOfKer z) := by
      change ((K : Submodule R (R × Q)).linearProjOfIsCompl Kc hKKc)
          ((kComponent z : R × Q) + Kc.subtype (lComponent z : Kc)) =
        ((K : Submodule R (R × Q)).linearProjOfIsCompl Kc hKKc) (ambientOfKer z)
      rw [map_add]
      have hleft :
          ((K : Submodule R (R × Q)).linearProjOfIsCompl Kc hKKc) (kComponent z : R × Q) =
            kComponent z := by
        exact Submodule.linearProjOfIsCompl_apply_left
          (p := (K : Submodule R (R × Q))) (q := Kc) hKKc (kComponent z)
      have hright :
          ((K : Submodule R (R × Q)).linearProjOfIsCompl Kc hKKc) (Kc.subtype (lComponent z : Kc)) = 0 := by
        exact Submodule.linearProjOfIsCompl_apply_right' (p := (K : Submodule R (R × Q))) (q := Kc)
          hKKc (Kc.subtype (lComponent z : Kc)) (lComponent z : Kc).2
      calc
        ((K : Submodule R (R × Q)).linearProjOfIsCompl Kc hKKc) (kComponent z : R × Q) +
            ((K : Submodule R (R × Q)).linearProjOfIsCompl Kc hKKc) (Kc.subtype (lComponent z : Kc))
            = kComponent z + 0 := by rw [hleft, hright]
        _ = ((K : Submodule R (R × Q)).linearProjOfIsCompl Kc hKKc) (ambientOfKer z) := by
          simp [kComponent]
    have hprojKc :
        π (ambientSum (forward z)) = π (ambientOfKer z) := by
      change π ((kComponent z : R × Q) + Kc.subtype (lComponent z : Kc)) = π (ambientOfKer z)
      rw [map_add]
      have hleft :
          π (kComponent z : R × Q) = 0 := by
        exact Submodule.linearProjOfIsCompl_apply_right' (p := Kc) (q := (K : Submodule R (R × Q)))
          hKKc.symm (kComponent z : R × Q) (kComponent z).2
      have hright :
          π (Kc.subtype (lComponent z : Kc)) = π (ambientOfKer z) := by
        have hid :
            π ((π (ambientOfKer z)) : Kc) = π (ambientOfKer z) := by
          exact LinearMap.congr_fun
            (Kc.linearProjOfIsCompl_comp_subtype hKKc.symm) (π (ambientOfKer z))
        simpa [lRaw, lComponent] using hid
      calc
        π (kComponent z : R × Q) + π (Kc.subtype (lComponent z : Kc))
            = 0 + π (ambientOfKer z) := by rw [hleft, hright]
        _ = π (ambientOfKer z) := by simp
    have hmemK : ambientSum (forward z) - ambientOfKer z ∈ (K : Submodule R (R × Q)) := by
      have hker :
          LinearMap.ker π = (K : Submodule R (R × Q)) := by
        exact ker_linearProjOfIsCompl_eq_left (R := R) (L := (K : Submodule R (R × Q))) (K'' := Kc)
          hKKc
      have hmem : ambientSum (forward z) - ambientOfKer z ∈ LinearMap.ker π := by
        rw [LinearMap.mem_ker, map_sub, hprojKc]
        simp
      simpa [hker] using hmem
    have hmemKc : ambientSum (forward z) - ambientOfKer z ∈ Kc := by
      have hker :
          LinearMap.ker projK = Kc := by
        exact ker_linearProjOfIsCompl_eq_left (R := R) (L := Kc)
          (K'' := (K : Submodule R (R × Q))) hKKc.symm
      have hmem : ambientSum (forward z) - ambientOfKer z ∈ LinearMap.ker projK := by
        rw [LinearMap.mem_ker, map_sub, hprojK]
        simp
      simpa [hker] using hmem
    have hzero : ambientSum (forward z) - ambientOfKer z = 0 := by
      have hmem : ambientSum (forward z) - ambientOfKer z ∈ ((K : Submodule R (R × Q)) ⊓ Kc) :=
        ⟨hmemK, hmemKc⟩
      have : ambientSum (forward z) - ambientOfKer z ∈ (⊥ : Submodule R (R × Q)) := by
        simpa [hKKc.inf_eq_bot] using hmem
      simpa using this
    exact sub_eq_zero.mp hzero
  have hambientOfKer_inverse :
      ∀ w : KL, ambientOfKer (inverse w) = ambientSum w := by
    rintro ⟨k, l⟩
    -- The inverse keeps the ambient point and subtracts off the rank-one correction in `Q`.
    ext
    · simp [ambientOfKer, inverse, ambientSum, generatorMap, kernelInclusion, fstAmbient]
    · change
        ((k : R × Q).1 + ((l : Kc) : R × Q).1) • p +
            (((k : R × Q).2 + ((l : Kc) : R × Q).2) -
              (((k : R × Q).1 + ((l : Kc) : R × Q).1) • p)) =
          (k : R × Q).2 + ((l : Kc) : R × Q).2
      simp [sub_eq_add_neg, add_assoc, add_left_comm]
  have hK_ambientSum :
      ∀ w : KL,
        ((K : Submodule R (R × Q)).linearProjOfIsCompl Kc hKKc) (ambientSum w) = w.1 := by
    intro w
    -- The `K`-projection kills the `L`-part and is the identity on the `K`-part.
    change ((K : Submodule R (R × Q)).linearProjOfIsCompl Kc hKKc)
        ((w.1 : R × Q) + Kc.subtype (w.2 : Kc)) = w.1
    rw [map_add]
    have hKleft :
        ((K : Submodule R (R × Q)).linearProjOfIsCompl Kc hKKc) (w.1 : R × Q) = w.1 := by
      exact Submodule.linearProjOfIsCompl_apply_left
        (p := (K : Submodule R (R × Q))) (q := Kc) hKKc w.1
    have hKright :
        ((K : Submodule R (R × Q)).linearProjOfIsCompl Kc hKKc) (Kc.subtype (w.2 : Kc)) = 0 := by
      exact Submodule.linearProjOfIsCompl_apply_right' (p := (K : Submodule R (R × Q))) (q := Kc)
        hKKc (Kc.subtype (w.2 : Kc)) (w.2 : Kc).2
    simp [hKleft]
  have hπ_ambientSum :
      ∀ w : KL, π (ambientSum w) = w.2 := by
    intro w
    -- The `Kc`-projection kills the `K`-part and is the identity on the `L`-part.
    change π ((w.1 : R × Q) + Kc.subtype (w.2 : Kc)) = w.2
    rw [map_add]
    have hπleft :
        π (w.1 : R × Q) = 0 := by
      exact Submodule.linearProjOfIsCompl_apply_right' (p := Kc) (q := (K : Submodule R (R × Q)))
        hKKc.symm (w.1 : R × Q) w.1.2
    have hπright :
        π (Kc.subtype (w.2 : Kc)) = (w.2 : Kc) := by
      exact LinearMap.congr_fun (Kc.linearProjOfIsCompl_comp_subtype hKKc.symm) (w.2 : Kc)
    simpa [hπleft, hπright]
  have hinverse_forward : ∀ z : R × M, inverse (forward z) = z := by
    intro z
    apply Prod.ext
    · have hfst := congrArg Prod.fst (hambientSum_forward z)
      simpa [ambientOfKer, ambientSum, forward, generatorMap, kernelInclusion, fstAmbient] using hfst
    · apply Subtype.ext
      have hfst := congrArg Prod.fst (hambientSum_forward z)
      have hsnd := congrArg Prod.snd (hambientSum_forward z)
      have hfst' : fstAmbient (forward z) = z.1 := by
        simpa [ambientOfKer, ambientSum, forward, generatorMap, kernelInclusion, fstAmbient] using hfst
      have hsnd' : sndAmbient (forward z) = z.1 • p + (z.2 : Q) := by
        simpa [ambientOfKer, ambientSum, forward, generatorMap, kernelInclusion, sndAmbient] using hsnd
      change sndAmbient (forward z) - fstAmbient (forward z) • p = (z.2 : Q)
      rw [hfst', hsnd']
      simp [sub_eq_add_neg, add_assoc, add_comm]
  have hforward_inverse :
      ∀ w : KL, forward (inverse w) = w := by
    intro w
    apply Prod.ext
    · calc
        kComponent (inverse w)
            = ((K : Submodule R (R × Q)).linearProjOfIsCompl Kc hKKc) (ambientOfKer (inverse w)) := by
                rfl
        _ = ((K : Submodule R (R × Q)).linearProjOfIsCompl Kc hKKc) (ambientSum w) := by
              simpa using congrArg ((K : Submodule R (R × Q)).linearProjOfIsCompl Kc hKKc)
                (hambientOfKer_inverse w)
        _ = w.1 := hK_ambientSum w
    · apply Subtype.ext
      calc
        π (ambientOfKer (inverse w)) = π (ambientSum w) := by
          simpa using congrArg π (hambientOfKer_inverse w)
        _ = w.2 := hπ_ambientSum w
  have hforward_injective : Function.Injective forward := by
    intro z₁ z₂ hz
    rw [← hinverse_forward z₁, ← hinverse_forward z₂, hz]
  have hforward_surjective : Function.Surjective forward := by
    intro w
    exact ⟨inverse w, hforward_inverse w⟩
  let e : (R × M) ≃ₗ[R] KL :=
    LinearEquiv.ofBijective forward ⟨hforward_injective, hforward_surjective⟩
  letI : Module.Finite R (K : Submodule R (R × Q)) := hKfinite
  letI : Module.StablyFree R (K : Submodule R (R × Q)) := hKstablyFree
  letI : Module.Free R L := by
    simpa [L, π] using hLfree
  letI : Module.Finite R L := by
    simpa [L, π] using hLfinite
  letI : Module.Finite R KL := inferInstance
  have hKLstablyFree : Module.StablyFree R KL := by
    have hA :
        ∃ m n : ℕ, Nonempty ((↥(K : Submodule R (R × Q)) × (Fin m → R)) ≃ₗ[R] (Fin n → R)) :=
      CategoryTheory.ShortComplex.finite_stablyFree_exists_fin_stabilization
        (R := R) (M := ↥(K : Submodule R (R × Q)))
    have hB :
        ∃ m n : ℕ, Nonempty ((↥L × (Fin m → R)) ≃ₗ[R] (Fin n → R)) :=
      CategoryTheory.ShortComplex.finite_stablyFree_exists_fin_stabilization (R := R) (M := ↥L)
    have hProd :
        ∃ m n : ℕ, Nonempty ((KL × (Fin m → R)) ≃ₗ[R] (Fin n → R)) :=
      CategoryTheory.ShortComplex.fin_stabilization_prod
        (R := R) (M := ↥(K : Submodule R (R × Q))) (N := ↥L) hA hB
    exact CategoryTheory.ShortComplex.stablyFree_of_fin_stabilization (R := R) (M := KL) hProd
  letI : Module.StablyFree R KL := hKLstablyFree
  letI : Module.Finite R (R × M) := Module.Finite.equiv e.symm
  have hMfinite : Module.Finite R M := by
    exact Module.Finite.of_surjective
      (LinearMap.snd R R M)
      (LinearMap.snd_surjective : Function.Surjective (LinearMap.snd R R M))
  have hMstablyFree : Module.StablyFree R M := by
    have hR :
        ∃ m n : ℕ, Nonempty ((R × (Fin m → R)) ≃ₗ[R] (Fin n → R)) :=
      CategoryTheory.ShortComplex.finite_stablyFree_exists_fin_stabilization (R := R) (M := R)
    have hKL :
        ∃ m n : ℕ, Nonempty ((KL × (Fin m → R)) ≃ₗ[R] (Fin n → R)) :=
      CategoryTheory.ShortComplex.finite_stablyFree_exists_fin_stabilization (R := R) (M := KL)
    have hProd :
        ∃ m n : ℕ, Nonempty (((R × M) × (Fin m → R)) ≃ₗ[R] (Fin n → R)) :=
      CategoryTheory.ShortComplex.fin_stabilization_of_equiv
        (R := R) (M := R × M) (N := KL) e hKL
    have hM :
        ∃ m n : ℕ, Nonempty ((M × (Fin m → R)) ≃ₗ[R] (Fin n → R)) :=
      CategoryTheory.ShortComplex.fin_stabilization_right_of_prod
        (R := R) (M := R) (N := M) hR hProd
    exact CategoryTheory.ShortComplex.stablyFree_of_fin_stabilization (R := R) (M := M) hM
  exact ⟨M, hqM, hMcompl, hMfinite, hMstablyFree⟩

/-- Helper for Lemma 15.129.5: after identifying the left free factor with `Fin n → R`, the
source argument proceeds by induction on `n`. -/
theorem exists_finiteStablyFree_directSummand_submodule_containing_of_fin_prod
    (n : ℕ)
    {Q : Type*} [AddCommGroup Q] [Module R Q] [Module.Projective R Q]
    (q : Q)
    (hnotFiniteAtMax : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal Q))
    (K : Complementeds (Submodule R ((Fin n → R) × Q)))
    (hKfinite : Module.Finite R (K : Submodule R ((Fin n → R) × Q)))
    (hKstablyFree : Module.StablyFree R (K : Submodule R ((Fin n → R) × Q)))
    (hqK : ((0 : Fin n → R), q) ∈ (K : Submodule R ((Fin n → R) × Q))) :
    ∃ M : Submodule R Q, q ∈ M ∧ IsComplemented M ∧ Module.Finite R M ∧ Module.StablyFree R M := by
  induction n generalizing Q with
  | zero =>
      let eZero : ((Fin 0 → R) × Q) ≃ₗ[R] Q :=
        { toFun := fun x ↦ x.2
          invFun := fun q ↦ (0, q)
          left_inv := by
            intro x
            rcases x with ⟨f, q⟩
            apply Prod.ext
            · funext i
              exact Fin.elim0 i
            · rfl
          right_inv := by
            intro q
            rfl
          map_add' := by
            intro x y
            rfl
          map_smul' := by
            intro a x
            rfl }
      let M : Submodule R Q := (K : Submodule R ((Fin 0 → R) × Q)).map eZero.toLinearMap
      have hqM : q ∈ M := by
        -- In rank zero, the ambient product is already linearly equivalent to `Q`.
        exact ⟨((0 : Fin 0 → R), q), hqK, rfl⟩
      have hMcompl : IsComplemented M :=
        isComplemented_map_of_linearEquiv (R := R) eZero (K : Submodule R ((Fin 0 → R) × Q)) K.2
      have hMfinite : Module.Finite R M :=
        module_finite_map_of_linearEquiv (R := R) eZero (K : Submodule R ((Fin 0 → R) × Q)) hKfinite
      have hMstablyFree : Module.StablyFree R M :=
        by
          simpa [M] using
            stablyFree_map_of_linearEquiv (R := R) eZero (K : Submodule R ((Fin 0 → R) × Q))
              hKfinite hKstablyFree
      exact ⟨M, hqM, hMcompl, hMfinite, hMstablyFree⟩
  | succ n ih =>
      let eSuccBase : (Fin (n + 1) → R) ≃ₗ[R] ((Fin n → R) × R) :=
        { toFun := fun f ↦ ((fun i ↦ f i.succ), f 0)
          invFun := fun x i ↦ Fin.cases x.2 (fun j ↦ x.1 j) i
          left_inv := by
            intro f
            funext i
            refine Fin.cases ?_ ?_ i
            · rfl
            · intro j
              rfl
          right_inv := by
            intro x
            apply Prod.ext
            · funext i
              rfl
            · rfl
          map_add' := by
            intro f g
            rfl
          map_smul' := by
            intro a f
            rfl }
      let eReassoc₁ :
          (((Fin n → R) × R) × Q) ≃ₗ[R] ((Fin n → R) × (R × Q)) :=
        LinearEquiv.prodAssoc R (Fin n → R) R Q
      let eReassoc₂ :
          ((Fin n → R) × (R × Q)) ≃ₗ[R] ((Fin n → R) × (Q × R)) :=
        LinearEquiv.prodCongr
          (LinearEquiv.refl R (Fin n → R))
          (LinearEquiv.prodComm R R Q)
      let eReassoc₃ :
          ((Fin n → R) × (Q × R)) ≃ₗ[R] (((Fin n → R) × Q) × R) :=
        (LinearEquiv.prodAssoc R (Fin n → R) Q R).symm
      let eReassoc₄ :
          (((Fin n → R) × Q) × R) ≃ₗ[R] (R × ((Fin n → R) × Q)) :=
        LinearEquiv.prodComm R ((Fin n → R) × Q) R
      let eSucc :
          ((Fin (n + 1) → R) × Q) ≃ₗ[R] (R × ((Fin n → R) × Q)) :=
        (LinearEquiv.prodCongr eSuccBase (LinearEquiv.refl R Q)).trans
          (eReassoc₁.trans (eReassoc₂.trans (eReassoc₃.trans eReassoc₄)))
      let KRankOne : Submodule R (R × ((Fin n → R) × Q)) :=
        (K : Submodule R ((Fin (n + 1) → R) × Q)).map eSucc.toLinearMap
      have hqKRankOne : ((0 : R), ((0 : Fin n → R), q)) ∈ KRankOne := by
        -- The transported distinguished element still has zero in the left free coordinate.
        exact ⟨((0 : Fin (n + 1) → R), q), hqK, rfl⟩
      have hKRankOneCompl : IsComplemented KRankOne :=
        isComplemented_map_of_linearEquiv (R := R) eSucc
          (K : Submodule R ((Fin (n + 1) → R) × Q)) K.2
      have hKRankOneFinite : Module.Finite R KRankOne :=
        module_finite_map_of_linearEquiv (R := R) eSucc
          (K : Submodule R ((Fin (n + 1) → R) × Q)) hKfinite
      have hKRankOneStablyFree : Module.StablyFree R KRankOne :=
        by
          simpa [KRankOne] using
            stablyFree_map_of_linearEquiv (R := R) eSucc
              (K : Submodule R ((Fin (n + 1) → R) × Q)) hKfinite hKstablyFree
      have hnotFiniteAtMaxProd :
          ∀ m : MaximalSpectrum R,
            ¬ Module.Finite (Localization.AtPrime m.asIdeal)
              (LocalizedModule.AtPrime m.asIdeal ((Fin n → R) × Q)) :=
        localizations_not_finite_prod_left (R := R) hnotFiniteAtMax
      -- First eliminate the final rank-one free factor.
      obtain ⟨MRankOne, hqMRankOne, hMRankOneCompl, hMRankOneFinite, hMRankOneStablyFree⟩ :=
        exists_finiteStablyFree_directSummand_submodule_containing_of_rank_one_prod
          (R := R) (Q := (Fin n → R) × Q) ((0 : Fin n → R), q) hnotFiniteAtMaxProd
          ⟨KRankOne, hKRankOneCompl⟩ hKRankOneFinite hKRankOneStablyFree hqKRankOne
      -- Then apply the induction hypothesis to the remaining `Fin n` block.
      exact ih (Q := Q) q hnotFiniteAtMax
        ⟨MRankOne, hMRankOneCompl⟩ hMRankOneFinite hMRankOneStablyFree hqMRankOne

/-- Helper for Lemma 15.129.5: eliminate a finite free factor from a finite stably free summand in
`F × Q`, following the source induction on the rank of `F`. -/
theorem exists_finiteStablyFree_directSummand_submodule_containing_of_prod_summand
    {Q : Type*} [AddCommGroup Q] [Module R Q] [Module.Projective R Q]
    (q : Q)
    (hnotFiniteAtMax : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal Q))
    {F : Type*} [AddCommGroup F] [Module R F] [Module.Free R F] [Module.Finite R F]
    (K : Complementeds (Submodule R (F × Q)))
    (hKfinite : Module.Finite R (K : Submodule R (F × Q)))
    (hKstablyFree : Module.StablyFree R (K : Submodule R (F × Q)))
    (hqK : ((0 : F), q) ∈ (K : Submodule R (F × Q))) :
    ∃ M : Submodule R Q, q ∈ M ∧ IsComplemented M ∧ Module.Finite R M ∧ Module.StablyFree R M := by
  obtain ⟨n, ⟨eF⟩⟩ := finite_free_linearEquiv_fin (R := R) (F := F)
  let eProd : (F × Q) ≃ₗ[R] ((Fin n → R) × Q) :=
    LinearEquiv.prodCongr eF (LinearEquiv.refl R Q)
  let KFin : Submodule R ((Fin n → R) × Q) := (K : Submodule R (F × Q)).map eProd.toLinearMap
  have hqKFin : ((0 : Fin n → R), q) ∈ KFin := by
    -- Transport the distinguished element into the `Fin n` coordinate model of `F`.
    exact ⟨((0 : F), q), hqK, by simp [eProd]⟩
  have hKFinCompl : IsComplemented KFin :=
    isComplemented_map_of_linearEquiv (R := R) eProd (K : Submodule R (F × Q)) K.2
  have hKFinFinite : Module.Finite R KFin :=
    module_finite_map_of_linearEquiv (R := R) eProd (K : Submodule R (F × Q)) hKfinite
  have hKFinStablyFree : Module.StablyFree R KFin :=
    by
      simpa [KFin] using
        stablyFree_map_of_linearEquiv (R := R) eProd (K : Submodule R (F × Q))
          hKfinite hKstablyFree
  -- Once `F` is in coordinates, the source proof becomes the induction on the number of free
  -- coordinates established in the dedicated `Fin`-model helper above.
  exact exists_finiteStablyFree_directSummand_submodule_containing_of_fin_prod
    (R := R) n q hnotFiniteAtMax ⟨KFin, hKFinCompl⟩ hKFinFinite hKFinStablyFree hqKFin

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: the product of two finite stably free modules is again finite
stably free. -/
lemma finite_stablyFree_prod
    {A : Type*} [AddCommGroup A] [Module R A]
    {B : Type*} [AddCommGroup B] [Module R B]
    [Module.Finite R A] [Module.StablyFree R A]
    [Module.Finite R B] [Module.StablyFree R B] :
    Module.Finite R (A × B) ∧ Module.StablyFree R (A × B) := by
  constructor
  · -- Finite generation is preserved by the finite product module.
    infer_instance
  · -- Combine finite-rank stabilization witnesses for the two factors.
    have hA :
        ∃ m n : ℕ, Nonempty ((A × (Fin m → R)) ≃ₗ[R] (Fin n → R)) :=
      CategoryTheory.ShortComplex.finite_stablyFree_exists_fin_stabilization (R := R) (M := A)
    have hB :
        ∃ m n : ℕ, Nonempty ((B × (Fin m → R)) ≃ₗ[R] (Fin n → R)) :=
      CategoryTheory.ShortComplex.finite_stablyFree_exists_fin_stabilization (R := R) (M := B)
    have hProd :
        ∃ m n : ℕ, Nonempty (((A × B) × (Fin m → R)) ≃ₗ[R] (Fin n → R)) :=
      CategoryTheory.ShortComplex.fin_stabilization_prod (R := R) (M := A) (N := B) hA hB
    exact CategoryTheory.ShortComplex.stablyFree_of_fin_stabilization
      (R := R) (M := A × B) hProd

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Lemma 15.129.5: if `R × M` is linearly equivalent to a finite stably free module,
then `M` itself is finite stably free. -/
lemma finite_stablyFree_of_prod_left_free
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    (e : (R × M) ≃ₗ[R] N)
    [Module.Finite R N] [Module.StablyFree R N] :
    Module.Finite R M ∧ Module.StablyFree R M := by
  letI : Module.Finite R (R × M) := Module.Finite.equiv e.symm
  constructor
  · -- Project away the free left factor to recover finite generation of `M`.
    exact Module.Finite.of_surjective
      (LinearMap.snd R R M)
      (LinearMap.snd_surjective : Function.Surjective (LinearMap.snd R R M))
  · -- Transport the finite stabilization of `N` back to `R × M`, then cancel the free `R` factor.
    have hR :
        ∃ m n : ℕ, Nonempty ((R × (Fin m → R)) ≃ₗ[R] (Fin n → R)) :=
      CategoryTheory.ShortComplex.finite_stablyFree_exists_fin_stabilization (R := R) (M := R)
    have hN :
        ∃ m n : ℕ, Nonempty ((N × (Fin m → R)) ≃ₗ[R] (Fin n → R)) :=
      CategoryTheory.ShortComplex.finite_stablyFree_exists_fin_stabilization (R := R) (M := N)
    have hProd :
        ∃ m n : ℕ, Nonempty (((R × M) × (Fin m → R)) ≃ₗ[R] (Fin n → R)) :=
      CategoryTheory.ShortComplex.fin_stabilization_of_equiv
        (R := R) (M := R × M) (N := N) e hN
    have hM :
        ∃ m n : ℕ, Nonempty ((M × (Fin m → R)) ≃ₗ[R] (Fin n → R)) :=
      CategoryTheory.ShortComplex.fin_stabilization_right_of_prod
        (R := R) (M := R) (N := M) hR hProd
    exact CategoryTheory.ShortComplex.stablyFree_of_fin_stabilization (R := R) (M := M) hM

/- Domain triage:
- primary domain: projective modules, complemented direct summands, and finite stably free
  submodules;
- sampled owner declarations: `MaximalSpectrum R`, `IsComplemented`, `Module.Finite`,
  `Module.StablyFree`, and `exists_perturbation_with_cyclicSpan_free_directSummand`;
- `source-facing`: the numbered item says a chosen element `s : P` lies in a finite stably free
  direct summand of `P`;
- `core/canonical`: the ambient owner is the concrete submodule `M : Submodule R P` together with
  the standard predicates `IsComplemented M`, `Module.Finite R M`, and `Module.StablyFree R M`,
  while maximal-local conditions are canonically indexed by `MaximalSpectrum R`;
- `bridge/view`: the theorem below is already the source-facing existence statement, so there is no
  additional owner-level bridge to a stronger free-summand property in this file.

Primitive data are only the ambient projective module `P`, the chosen element `s`, and the
submodule `M ≤ P` containing `s`. Complementedness, finiteness, and stable freeness are canonical
properties of that fixed submodule, so the public source-facing statement should expose `M`
directly instead of packaging it first as an element of `Complementeds (Submodule R P)`. -/

-- Proof sketch: first apply Lemma `15.129.3` to place `(0, s)` inside a finite free direct summand
-- of `F ⊕ P`. Induct on the finite free rank of `F`, reducing to a complemented finite stably free
-- submodule of `R ⊕ P` containing `(0, s)`. Then use Lemma `15.129.4` on the complement to split
-- off a free rank-one summand and identify the kernel of the resulting projection `P → K''` as a
-- complemented submodule of `P` containing `s`; this kernel is finite stably free because
-- `R ⊕ ker(π')` is isomorphic to the sum of the original finite stably free summand and a free
-- rank-one summand.
/-- Lemma 15.129.5: if `R ⧸ Ring.jacobson R` is Noetherian and `P` is a projective `R`-module
whose localizations at maximal ideals are not finitely generated, then every element `s : P` is
contained in a finite stably free direct summand of `P`, expressed directly by a submodule
`M ≤ P` together with `IsComplemented M`, `Module.Finite R M`, and `Module.StablyFree R M`. -/
@[stacks 0GVJ]
theorem exists_finiteStablyFree_directSummand_submodule_containing
    (s : P)
    (hnotFiniteAtMax : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal P)) :
    ∃ M : Submodule R P, s ∈ M ∧ IsComplemented M ∧ Module.Finite R M ∧ Module.StablyFree R M :=
  by
  -- Route correction: the upstream Lemma `15.129.3` witness is available again, so the top theorem
  -- reduces immediately to the local source-faithful elimination of the finite free factor.
  obtain ⟨F, _instAddCommGroupF, _instModuleF, _instFreeF, _instFiniteF, K, hKfree, hKfinite, hsK⟩ :=
    exists_finiteFree_directSummand_prod_contains_zero_s (R := R) (P := P) s
  letI : Module.Free R (K : Submodule R (F × P)) := hKfree
  have hKstablyFree : Module.StablyFree R (K : Submodule R (F × P)) := inferInstance
  -- Feed the finite free witness into the auxiliary theorem that removes the left free factor.
  simpa using
    exists_finiteStablyFree_directSummand_submodule_containing_of_prod_summand
      (R := R) (Q := P) s hnotFiniteAtMax K hKfinite hKstablyFree hsK

end
