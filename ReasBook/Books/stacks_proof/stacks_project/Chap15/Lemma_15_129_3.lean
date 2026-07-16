import stacks_proof.stacks_project.Chap15.Lemma_15_129_2
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [Ring R]
variable {P : Type v} [AddCommGroup P] [Module R P] [Module.Projective R P]

/- Domain sampling:
- primary domain: projective modules, free ambient modules, and complemented submodules;
- sampled owner declarations: `Module.Projective.exists_free_prod_free`,
  `Module.Free.chooseBasis`, `Finsupp.supported`, and `Complementeds (Submodule R M)`;
- source-facing layer: existence of a finite free direct summand of `F ⊕ P` containing `(0, s)`;
- core/canonical layer: the owner `Complementeds (Submodule R (F × P))` for the summand itself,
  with the finite-support submodule `Finsupp.supported R R S` as the canonical free finite model
  on basis coordinates;
- bridge/view: Lemma `15.129.2` provides the free ambient module `F₀ × P`, and a chosen basis of
  that free module identifies finite-support coordinate submodules with finite free complemented
  submodules in the ambient module.

Primitive data are the ambient finite free module `F` and the complemented submodule `K ≤ F × P`.
The properties `Module.Free R K` and `Module.Finite R K` are standard derived API on that owner
and should remain theorem-level output, not primitive wrapper fields. -/

-- Proof sketch: invoke `Module.Projective.exists_free_prod_free` to place `P` in a free ambient
-- module `F₀ × P`. In coordinates with respect to a chosen basis of that free module, the element
-- `(0, s)` has finite support, so it lies in the canonical finite-support submodule
-- `Finsupp.supported R R S`. Transport that finite free complemented submodule back to the ambient
-- module, then shrink the first factor of `F₀` to a finite free summand containing all first
-- coordinates occurring in this transported submodule so that the witness lives in some `F × P`.
/-- Helper for Lemma 15.129.3: the coordinate submodule of finitely supported functions with
support contained in `t` is complemented by the coordinate submodule supported on `tᶜ`. -/
lemma finsupp_supported_is_complemented {ι : Type*} (t : Set ι) :
    IsComplemented (Finsupp.supported R R t : Submodule R (ι →₀ R)) := by
  -- The canonical complement is obtained by requiring support in the set-theoretic complement.
  have hcodisjoint : Codisjoint t tᶜ := by
    rw [codisjoint_iff]
    exact Set.union_compl_self t
  refine ⟨Finsupp.supported R R tᶜ, ?_⟩
  constructor
  · exact Finsupp.disjoint_supported_supported (M := R) (R := R) disjoint_compl_right
  · exact Finsupp.codisjoint_supported_supported (M := R) (R := R) hcodisjoint

/-- Helper for Lemma 15.129.3: a finite submodule of a free module is contained in a finite free
complemented submodule, obtained by keeping only finitely many basis coordinates. -/
lemma finite_submodule_le_complemented_finite_free
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
  -- Finite generation of the coordinate image lets us take the union of all generator supports.
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
    finsupp_supported_is_complemented (R := R) (t := (↑t : Set (Module.Free.ChooseBasisIndex R M)))
  have hKcoord_free : Module.Free R Kcoord := by
    -- The coordinate owner is equivalent to a finitely indexed free `Finsupp` module.
    exact
      Module.Free.of_equiv
        (Finsupp.supportedEquivFinsupp
          (R := R) (M := R) (↑t : Set (Module.Free.ChooseBasisIndex R M))).symm
  have hKcoord_finite : Module.Finite R Kcoord := by
    -- The finite index set `↑t` makes the corresponding `Finsupp` module finite.
    exact
      Module.Finite.equiv
        (Finsupp.supportedEquivFinsupp
          (R := R) (M := R) (↑t : Set (Module.Free.ChooseBasisIndex R M))).symm
  let eSub : Submodule R M ≃o Submodule R ((Module.Free.ChooseBasisIndex R M) →₀ R) :=
    Submodule.orderIsoMapComap b.repr
  let L : Submodule R M := Kcoord.comap b.repr.toLinearMap
  have hN_le_L : N ≤ L := by
    -- Pull the coordinate containment back along the basis representation.
    simpa [L, Ncoord] using (Submodule.map_le_iff_le_comap.mp hNcoord_le)
  have hL_map : L.map b.repr.toLinearMap = Kcoord := by
    -- The basis coordinates recover the chosen finite-support owner on the nose.
    exact
      Submodule.map_comap_eq_of_surjective
        (f := b.repr.toLinearMap) b.repr.surjective Kcoord
  have hL_complemented : IsComplemented L := by
    -- Complementedness is preserved by the order isomorphism on submodules.
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

/-- Helper for Lemma 15.129.3: if a complemented submodule `K` lies in a larger submodule `L`,
then the copy of `K` inside `L` is again complemented. -/
lemma is_complemented_comap_subtype_of_le
    {M : Type*} [AddCommGroup M] [Module R M] {K L : Submodule R M}
    (hK : IsComplemented K) (hKL : K ≤ L) :
    IsComplemented (K.comap L.subtype) := by
  -- Restrict both complementary summands along the subtype map of the larger owner.
  rcases hK with ⟨Kc, hcompl⟩
  refine ⟨Kc.comap L.subtype, ?_⟩
  exact Submodule.isCompl_comap_subtype_of_isCompl_of_le hcompl hKL

/-- Helper for Lemma 15.129.3: the forward map from `Submodule.prod Fsub ⊤` to `Fsub × P`
forgets the ambient proof and records the first coordinate as an element of `Fsub`. -/
def prod_top_equiv_prod_toFun {F₀ : Type*} [AddCommGroup F₀] [Module R F₀]
    (Fsub : Submodule R F₀) :
    ↥(Submodule.prod Fsub (⊤ : Submodule R P)) → (Fsub × P)
  | x => (⟨x.1.1, x.2.1⟩, x.1.2)

/-- Helper for Lemma 15.129.3: the obvious pair built from an element of `Fsub × P` lies in the
ambient owner `Submodule.prod Fsub ⊤`. -/
lemma prod_top_equiv_prod_inv_mem {F₀ : Type*} [AddCommGroup F₀] [Module R F₀]
    (Fsub : Submodule R F₀) (x : Fsub × P) :
    (((x.1 : F₀), x.2) : F₀ × P) ∈ Submodule.prod Fsub (⊤ : Submodule R P) := by
  exact ⟨x.1.2, trivial⟩

/-- Helper for Lemma 15.129.3: the inverse map from `Fsub × P` into `Submodule.prod Fsub ⊤`. -/
def prod_top_equiv_prod_invFun {F₀ : Type*} [AddCommGroup F₀] [Module R F₀]
    (Fsub : Submodule R F₀) :
    (Fsub × P) → ↥(Submodule.prod Fsub (⊤ : Submodule R P))
  | x => ⟨((x.1 : F₀), x.2), prod_top_equiv_prod_inv_mem (R := R) (P := P) Fsub x⟩

/-- Helper for Lemma 15.129.3: the two coordinate maps are inverse on `Submodule.prod Fsub ⊤`. -/
lemma prod_top_equiv_prod_left_inv {F₀ : Type*} [AddCommGroup F₀] [Module R F₀]
    (Fsub : Submodule R F₀) :
    Function.LeftInverse
      (prod_top_equiv_prod_invFun (R := R) (P := P) Fsub)
      (prod_top_equiv_prod_toFun (R := R) (P := P) Fsub) := by
  intro x
  apply Subtype.ext
  rfl

/-- Helper for Lemma 15.129.3: the two coordinate maps are inverse on `Fsub × P`. -/
lemma prod_top_equiv_prod_right_inv {F₀ : Type*} [AddCommGroup F₀] [Module R F₀]
    (Fsub : Submodule R F₀) :
    Function.RightInverse
      (prod_top_equiv_prod_invFun (R := R) (P := P) Fsub)
      (prod_top_equiv_prod_toFun (R := R) (P := P) Fsub) := by
  intro x
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · rfl

/-- Helper for Lemma 15.129.3: the forward coordinate map respects addition. -/
lemma prod_top_equiv_prod_toFun_map_add {F₀ : Type*} [AddCommGroup F₀] [Module R F₀]
    (Fsub : Submodule R F₀) (x y : ↥(Submodule.prod Fsub (⊤ : Submodule R P))) :
    prod_top_equiv_prod_toFun (R := R) (P := P) Fsub (x + y) =
      prod_top_equiv_prod_toFun (R := R) (P := P) Fsub x +
        prod_top_equiv_prod_toFun (R := R) (P := P) Fsub y := by
  rfl

/-- Helper for Lemma 15.129.3: the forward coordinate map respects scalar multiplication. -/
lemma prod_top_equiv_prod_toFun_map_smul {F₀ : Type*} [AddCommGroup F₀] [Module R F₀]
    (Fsub : Submodule R F₀) (a : R) (x : ↥(Submodule.prod Fsub (⊤ : Submodule R P))) :
    prod_top_equiv_prod_toFun (R := R) (P := P) Fsub (a • x) =
      a • prod_top_equiv_prod_toFun (R := R) (P := P) Fsub x := by
  rfl

/-- Helper for Lemma 15.129.3: the owner `Submodule.prod Fsub ⊤` is canonically the same module as
`Fsub × P`; this is the final transport from the natural ambient submodule to the source-facing
product module. -/
noncomputable def prod_top_equiv_prod {F₀ : Type*} [AddCommGroup F₀] [Module R F₀]
    (Fsub : Submodule R F₀) :
    ↥(Submodule.prod Fsub (⊤ : Submodule R P)) ≃ₗ[R] (Fsub × P) :=
  { toFun := prod_top_equiv_prod_toFun (R := R) (P := P) Fsub
    invFun := prod_top_equiv_prod_invFun (R := R) (P := P) Fsub
    left_inv := prod_top_equiv_prod_left_inv (R := R) (P := P) Fsub
    right_inv := prod_top_equiv_prod_right_inv (R := R) (P := P) Fsub
    map_add' := prod_top_equiv_prod_toFun_map_add (R := R) (P := P) Fsub
    map_smul' := prod_top_equiv_prod_toFun_map_smul (R := R) (P := P) Fsub }

/-- Lemma 15.129.3: for a projective `R`-module `P` and an element `s : P`, there exist a finite
free `R`-module `F` and a finite free direct summand `K` of `F ⊕ P`, modeled in Lean as a
complemented submodule `K ≤ F × P` together with the standard properties `Module.Free R K` and
`Module.Finite R K`, such that `(0, s) ∈ K`. -/
@[stacks 0GVH]
theorem exists_finiteFree_directSummand_prod_contains_zero_s (s : P) :
    ∃ (F : Type (max u v)) (_ : AddCommGroup F) (_ : Module R F) (_ : Module.Free R F)
      (_ : Module.Finite R F),
      ∃ K : Complementeds (Submodule R (F × P)),
        Module.Free R (K : Submodule R (F × P)) ∧
          Module.Finite R (K : Submodule R (F × P)) ∧ ((0 : F), s) ∈ (K : Submodule R (F × P)) :=
    by
  classical
  obtain ⟨F₀, _, _, hF₀_free, hprod_free⟩ :=
    Module.Projective.exists_free_prod_free (R := R) (P := P)
  -- First move to a genuinely free ambient module of the shape `F₀ × P`.
  have hAmbient_free : Module.Free R (F₀ × P) := by
    letI : Module.Free R (P × F₀) := hprod_free
    exact Module.Free.of_equiv (LinearEquiv.prodComm R P F₀)
  letI : Module.Free R (F₀ × P) := hAmbient_free
  let x : F₀ × P := ((0 : F₀), s)
  have hx_span_finite : Module.Finite R (R ∙ x) := by
    infer_instance
  -- Cut out a finite free complemented submodule around the chosen element.
  obtain ⟨K₀, hx_span_le_K₀, hK₀_free, hK₀_finite⟩ :=
    finite_submodule_le_complemented_finite_free
      (R := R) (M := F₀ × P) (N := R ∙ x) hx_span_finite
  have hx_mem_span : x ∈ R ∙ x := by
    simp [x]
  have hx_mem_K₀ : x ∈ (K₀ : Submodule R (F₀ × P)) :=
    hx_span_le_K₀ hx_mem_span
  letI : Module.Finite R (K₀ : Submodule R (F₀ × P)) := hK₀_finite
  let Fimage : Submodule R F₀ :=
    Submodule.map (LinearMap.fst R F₀ P) (K₀ : Submodule R (F₀ × P))
  have hFimage_finite : Module.Finite R Fimage := by
    infer_instance
  -- Shrink the first factor to a finite free complemented owner containing all first coordinates.
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
    -- Inside the smaller ambient owner, the submodule is still equivalent to the original `K₀`.
    let eInside : (K₀ : Submodule R (F₀ × P)) ≃ₗ[R] Kinside :=
      (Submodule.submoduleOfEquivOfLe hK₀_le_A).symm
    letI : Module.Free R (K₀ : Submodule R (F₀ × P)) := hK₀_free
    exact Module.Free.of_equiv eInside
  have hKinside_finite : Module.Finite R Kinside := by
    let eInside : (K₀ : Submodule R (F₀ × P)) ≃ₗ[R] Kinside :=
      (Submodule.submoduleOfEquivOfLe hK₀_le_A).symm
    letI : Module.Finite R (K₀ : Submodule R (F₀ × P)) := hK₀_finite
    exact Module.Finite.equiv eInside
  have hx_mem_A : x ∈ A :=
    hK₀_le_A hx_mem_K₀
  let xA : A := ⟨x, hx_mem_A⟩
  have hxA_mem_Kinside : xA ∈ Kinside :=
    hx_mem_K₀
  let eProd : A ≃ₗ[R] (Fsub × P) := prod_top_equiv_prod (R := R) (P := P) Fsub
  let eProdSub : Submodule R A ≃o Submodule R (Fsub × P) := Submodule.orderIsoMapComap eProd
  let KfinalSub : Submodule R (Fsub × P) := eProdSub Kinside
  have hKfinal_complemented : IsComplemented KfinalSub := by
    -- Complementedness transports across the linear equivalence to the literal `Fsub × P` owner.
    rcases hKinside_complemented with ⟨C, hcompl⟩
    refine ⟨eProdSub C, ?_⟩
    simpa [KfinalSub, eProdSub] using eProdSub.isCompl hcompl
  have hKfinal_map : Kinside.map eProd.toLinearMap = KfinalSub := by
    simpa [KfinalSub, eProdSub, Submodule.orderIsoMapComap_apply']
  have hKfinal_free : Module.Free R KfinalSub := by
    let eKfinal : Kinside ≃ₗ[R] KfinalSub := LinearEquiv.ofSubmodules eProd Kinside KfinalSub hKfinal_map
    letI : Module.Free R Kinside := hKinside_free
    exact Module.Free.of_equiv eKfinal
  have hKfinal_finite : Module.Finite R KfinalSub := by
    let eKfinal : Kinside ≃ₗ[R] KfinalSub := LinearEquiv.ofSubmodules eProd Kinside KfinalSub hKfinal_map
    letI : Module.Finite R Kinside := hKinside_finite
    exact Module.Finite.equiv eKfinal
  have hxA_image : eProd xA = ((0 : Fsub), s) := by
    ext <;> rfl
  have hxA_mem_Kfinal : eProd xA ∈ KfinalSub := by
    exact ⟨xA, hxA_mem_Kinside, rfl⟩
  have htarget_mem : ((0 : Fsub), s) ∈ KfinalSub := by
    simpa [hxA_image] using hxA_mem_Kfinal
  refine ⟨Fsub, inferInstance, inferInstance, hFsub_free, hFsub_finite, ?_⟩
  refine ⟨⟨KfinalSub, hKfinal_complemented⟩, hKfinal_free, hKfinal_finite, htarget_mem⟩

end
