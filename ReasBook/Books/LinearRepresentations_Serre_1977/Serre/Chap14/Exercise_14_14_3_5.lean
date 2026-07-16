import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap14.Proposition_14_14_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped MonoidAlgebra

universe u v w x

section

namespace LinearMap

-- Source/core/bridge triage:
-- * source-facing: `LinearMap.IsEssentialExtension` and `LinearMap.IsInjectiveEnvelope` on module
--   maps.
-- * core/canonical owners: the chapter's projective-side owners `LinearMap.IsEssential` and
--   `LinearMap.IsProjectiveEnvelope` from `Proposition_14_14_3_1`, together with mathlib's
--   `Module.Injective`, `Module.Projective`, and the categorical owner `ModuleCat` for simple and
--   indecomposable modules.
-- * bridge/view: `f.hom` is the canonical passage from a `ModuleCat` morphism to the linear map
--   carrying the injective-envelope structure.
-- There is no upstream mathlib/project owner for essential extensions of module monomorphisms, so
-- the injective-side owner stays local to this file instead of being repackaged through a wrapper.

section EssentialExtension

variable {R : Type u} [Semiring R]
variable {M : Type v} {Q : Type w} [AddCommMonoid M] [Module R M]
variable [AddCommMonoid Q] [Module R Q]

/-- An essential extension is a linear map whose image meets every nonzero submodule of the target
nontrivially. -/
class IsEssentialExtension (f : M →ₗ[R] Q) : Prop where
  /-- Any submodule of the target disjoint from the image of `f` is zero. -/
  eq_bot_of_inf_range_eq_bot (N : Submodule R Q) (hN : N ⊓ f.range = ⊥) : N = ⊥

end EssentialExtension

section InjectiveEnvelope

variable {R : Type u} [Ring R]
variable {M : Type v} {Q : Type w} [AddCommGroup M] [Module R M]
variable [AddCommGroup Q] [Module R Q]

/-- An injective envelope is an injective essential embedding into an injective module. -/
class IsInjectiveEnvelope (f : M →ₗ[R] Q) : Prop extends Module.Injective R Q,
    f.IsEssentialExtension where
  /-- The envelope map is injective. -/
  injective : Function.Injective f

end InjectiveEnvelope

end LinearMap

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

/-- Helper for Exercise 14-14.3-5: a `k`-linear functional on `k[G]` determines a `k[G]`-linear
endomorphism by recovering each coefficient from the translate whose coefficient at `1` is read
by the functional. -/
private noncomputable def reconstruct_from_coeff_one
    (L : k[G] →ₗ[k] k) : k[G] →ₗ[k[G]] k[G] := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  refine
    { toFun := fun r => Finsupp.equivFunOnFinite.symm fun t => L ((MonoidAlgebra.of k G t⁻¹) * r)
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    apply Finsupp.equivFunOnFinite.injective
    funext t
    -- Read the coefficient at `t` after translating by `t⁻¹`.
    simp [mul_add, map_add]
  · intro a r
    let h : k[G] := Finsupp.equivFunOnFinite.symm fun t => L ((MonoidAlgebra.of k G t⁻¹) * r)
    apply Finsupp.equivFunOnFinite.injective
    funext t
    simp [Finsupp.equivFunOnFinite_apply]
    let P : k[G] → Prop := fun b =>
      L (MonoidAlgebra.single t⁻¹ 1 * (b * r)) = (b * h) t
    have hPa : P a := by
      refine MonoidAlgebra.induction_on a ?_ ?_ ?_
      · intro m
        -- For a basis vector, both sides read the same translated coefficient.
        change
          L (MonoidAlgebra.single t⁻¹ 1 * ((MonoidAlgebra.of k G m) * r)) =
            (((MonoidAlgebra.of k G m) * h : k[G]) t)
        rw [MonoidAlgebra.of_apply]
        rw [← mul_assoc, MonoidAlgebra.single_mul_single, one_mul]
        simp [MonoidAlgebra.single_mul_apply, h]
      · intro b c hb hc
        -- The reconstruction is additive in the ambient group-algebra coefficient.
        simp [P, add_mul, left_distrib, hb, hc]
      · intro b s hs
        -- Scalar multiples commute with the coefficient-reading reconstruction.
        simp [P, hs, smul_eq_mul]
    exact hPa

@[simp]
private theorem reconstruct_from_coeff_one_apply
    (L : k[G] →ₗ[k] k) (r : k[G]) (t : G) :
    reconstruct_from_coeff_one (k := k) (G := G) L r t =
      L ((MonoidAlgebra.of k G t⁻¹) * r) :=
  rfl

/-- Helper for Exercise 14-14.3-5: a `k`-linear functional on a `k[G]`-module determines a
`k[G]`-linear map to the regular module by reading coefficients after translating the input. -/
private noncomputable def reconstruct_from_coeff_one_module
    {M : Type w} [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (L : M →ₗ[k] k) : M →ₗ[k[G]] k[G] := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  refine
    { toFun := fun m => Finsupp.equivFunOnFinite.symm fun t => L ((MonoidAlgebra.of k G t⁻¹) • m)
      map_add' := by
        intro x y
        apply Finsupp.equivFunOnFinite.injective
        funext t
        simp [smul_add, map_add]
      map_smul' := ?_ }
  intro a m
  let h : k[G] := Finsupp.equivFunOnFinite.symm fun t => L ((MonoidAlgebra.of k G t⁻¹) • m)
  apply Finsupp.equivFunOnFinite.injective
  funext t
  let P : k[G] → Prop := fun b => L ((MonoidAlgebra.of k G t⁻¹) • (b • m)) = (b * h) t
  have hPa : P a := by
    refine MonoidAlgebra.induction_on a ?_ ?_ ?_
    · intro g
      have hsmul :
          MonoidAlgebra.single t⁻¹ (1 : k) • MonoidAlgebra.single g (1 : k) • m =
            (MonoidAlgebra.single (t⁻¹ * g) (1 : k) : k[G]) • m := by
        simpa using
          (smul_assoc (MonoidAlgebra.single t⁻¹ (1 : k)) (MonoidAlgebra.single g (1 : k)) m).symm
      -- Rewrite the translated basis action into the single translated coefficient that `h` reads.
      calc
        L ((MonoidAlgebra.of k G t⁻¹) • ((MonoidAlgebra.of k G g) • m)) =
            L (MonoidAlgebra.single t⁻¹ (1 : k) • MonoidAlgebra.single g (1 : k) • m) := by
              simp [MonoidAlgebra.of_apply]
        _ = L ((MonoidAlgebra.single (t⁻¹ * g) (1 : k) : k[G]) • m) := by
              exact congrArg L hsmul
        _ = (((MonoidAlgebra.of k G g) * h : k[G]) t) := by
              simp [h, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_apply]
    · intro b c hb hc
      -- Additivity in the group-algebra coefficient matches additivity of convolution.
      calc
        L ((MonoidAlgebra.of k G t⁻¹) • ((b + c) • m)) =
            L ((MonoidAlgebra.of k G t⁻¹) • (b • m)) +
              L ((MonoidAlgebra.of k G t⁻¹) • (c • m)) := by
                simp [add_smul, map_add]
        _ = (b * h) t + (c * h) t := by rw [hb, hc]
        _ = ((b + c) * h) t := by simp [add_mul]
    · intro r b hb
      -- Scalar multiples commute with the translated coefficient reconstruction.
      calc
        L ((MonoidAlgebra.of k G t⁻¹) • ((r • b) • m)) =
            r * L ((MonoidAlgebra.of k G t⁻¹) • (b • m)) := by
              have hs :
                  (MonoidAlgebra.of k G t⁻¹) • ((r • b) • m) =
                    r • ((MonoidAlgebra.of k G t⁻¹) • (b • m)) := by
                calc
                  (MonoidAlgebra.of k G t⁻¹) • ((r • b) • m) =
                      (((MonoidAlgebra.of k G t⁻¹) * (r • b)) : k[G]) • m := by
                        simpa using
                          (smul_assoc (MonoidAlgebra.of k G t⁻¹) (r • b) m).symm
                  _ = (r • (((MonoidAlgebra.of k G t⁻¹) * b : k[G]))) • m := by
                        rw [mul_smul_comm]
                  _ = r • ((((MonoidAlgebra.of k G t⁻¹) * b : k[G])) • m) := by
                        simpa using
                          (smul_assoc r (((MonoidAlgebra.of k G t⁻¹) * b : k[G])) m)
                  _ = r • ((MonoidAlgebra.of k G t⁻¹) • (b • m)) := by
                        simpa [smul_eq_mul] using
                          congrArg (fun x : M => r • x) (smul_assoc (MonoidAlgebra.of k G t⁻¹) b m)
              calc
                L ((MonoidAlgebra.of k G t⁻¹) • ((r • b) • m)) =
                    L (r • ((MonoidAlgebra.of k G t⁻¹) • (b • m))) := by
                      exact congrArg L hs
                _ = r * L ((MonoidAlgebra.of k G t⁻¹) • (b • m)) := by simp
        _ = r * (b * h) t := by rw [hb]
        _ = ((r • b) * h) t := by simp
  exact hPa

@[simp]
private theorem reconstruct_from_coeff_one_module_apply
    {M : Type w} [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (L : M →ₗ[k] k) (m : M) (t : G) :
    reconstruct_from_coeff_one_module (k := k) (G := G) (M := M) L m t =
      L ((MonoidAlgebra.of k G t⁻¹) • m) :=
  rfl

-- Proof sketch: identify `k[G]` as a Frobenius algebra, so the regular left module is
-- isomorphic to its `k`-linear dual and therefore injective as a module over itself.
/-- Exercise 14-14.3-5: the regular `k[G]`-module is injective. -/
theorem groupAlgebra_self_injective :
    Module.Injective k[G] k[G] := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  -- Route correction: instead of packaging the dual regular module as a separate object, extend
  -- the coefficient-at-`1` functional over the base field and then reconstruct the full
  -- group-algebra-valued map from its translated coefficients.
  apply Module.Baer.injective
  intro I g
  let fI : I →ₗ[k] k[G] :=
    { toFun := I.subtype
      map_add' := I.subtype.map_add
      map_smul' := by
        intro a x
        simpa using I.subtype.map_smulₛₗ a x }
  let coeff_one : I →ₗ[k] k :=
    { toFun := fun x => g x 1
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro a x
        simpa using congrArg (fun z : k[G] => z 1) (g.map_smulₛₗ a x) }
  have : IsSemisimpleModule k k[G] := by infer_instance
  obtain ⟨coeff_one_ext, hcoeff_one_ext⟩ :=
    IsSemisimpleModule.extension_property fI I.subtype_injective coeff_one
  let g' : k[G] →ₗ[k[G]] k[G] :=
    reconstruct_from_coeff_one (k := k) (G := G) coeff_one_ext
  refine ⟨g', ?_⟩
  intro x hx
  ext t
  let xt : I := ⟨(MonoidAlgebra.of k G t⁻¹) * x, by
    simpa using I.mul_mem_left (MonoidAlgebra.of k G t⁻¹) hx⟩
  have hxt := LinearMap.congr_fun hcoeff_one_ext xt
  -- Evaluating the extended coefficient-at-`1` functional on the translated element recovers the
  -- original coefficient at `t`.
  have hgxt :
      g xt 1 = g ⟨x, hx⟩ t := by
    simpa [xt, MonoidAlgebra.of_apply] using
      congrArg (fun z : k[G] => z 1) (g.map_smulₛₗ (MonoidAlgebra.of k G t⁻¹) ⟨x, hx⟩)
  simpa [reconstruct_from_coeff_one_apply, coeff_one, fI, xt] using hxt.trans hgxt

variable {M : Type w} [AddCommGroup M] [Module k[G] M]

namespace Exercise_14_14_3_5

/-- Helper for Exercise 14-14.3-5: the finitely supported part of a free `k[G]`-module on a finite
index set is injective, because it is linearly equivalent to a finite free module and finite
projective `k[G]`-modules are already known to be injective. -/
private theorem supported_groupAlgebra_module_injective
    {ι : Type w} (s : Finset ι) :
    Module.Injective k[G] (Finsupp.supported k[G] k[G] (s : Set ι)) := by
  classical
  let e :
      Finsupp.supported k[G] k[G] (s : Set ι) ≃ₗ[k[G]] (↥(s : Set ι) →₀ k[G]) :=
    Finsupp.supportedEquivFinsupp (M := k[G]) (R := k[G]) (s := (s : Set ι))
  let e' : (↥(s : Set ι) →₀ k[G]) ≃ₗ[k[G]] (↥(s : Set ι) → k[G]) :=
    Finsupp.linearEquivFunOnFinite k[G] k[G] ↥(s : Set ι)
  let n : ℕ := Fintype.card ↥(s : Set ι)
  let e'' : (↥(s : Set ι) → k[G]) ≃ₗ[k[G]] (Fin n → k[G]) :=
    (LinearEquiv.funCongrLeft k[G] k[G] (Fintype.equivFin ↥(s : Set ι))).symm
  have hpi_injective : Module.Injective k[G] (Fin n → k[G]) := by
    let Z : Fin n → ModuleCat k[G] := fun _ => ModuleCat.of k[G] k[G]
    have hprodObj : CategoryTheory.Injective (∏ᶜ Z) := by
      have hobj : ∀ i, CategoryTheory.Injective (Z i) := fun _ =>
        (Module.injective_iff_injective_object k[G] k[G]).mp groupAlgebra_self_injective
      infer_instance
    let iso : (∏ᶜ Z) ≅ ModuleCat.of k[G] (Fin n → k[G]) := ModuleCat.piIsoPi Z
    exact
      (Module.injective_iff_injective_object k[G] (Fin n → k[G])).mpr
        (CategoryTheory.Injective.of_iso iso hprodObj)
  have hsubtype_injective : Module.Injective k[G] (↥(s : Set ι) → k[G]) := by
    let hpi_ulift :
        Module.Injective k[G] (ULift.{max u w, u} (Fin n → k[G])) :=
      Module.ulift_injective_of_injective k[G] hpi_injective
    let eU : (↥(s : Set ι) → k[G]) ≃ₗ[k[G]] ULift.{max u w, u} (Fin n → k[G]) :=
      e''.trans ULift.moduleEquiv.symm
    letI : Module.Injective k[G] (ULift.{max u w, u} (Fin n → k[G])) := hpi_ulift
    refine ⟨?_⟩
    intro X Y _ _ _ _ i hi g
    obtain ⟨h, hh⟩ := Module.Injective.out (Q := ULift.{max u w, u} (Fin n → k[G])) (f := i) hi
      (eU.toLinearMap.comp g)
    refine ⟨eU.symm.toLinearMap.comp h, ?_⟩
    intro x
    simpa using congrArg eU.symm (hh x)
  have hfinsupp_injective : Module.Injective k[G] (↥(s : Set ι) →₀ k[G]) := by
    letI : Module.Injective k[G] (↥(s : Set ι) → k[G]) := hsubtype_injective
    refine ⟨?_⟩
    intro X Y _ _ _ _ i hi g
    obtain ⟨h, hh⟩ := Module.Injective.out (Q := ↥(s : Set ι) → k[G]) (f := i) hi
      (e'.toLinearMap.comp g)
    refine ⟨e'.symm.toLinearMap.comp h, ?_⟩
    intro x
    simpa using congrArg e'.symm (hh x)
  letI : Module.Injective k[G] (↥(s : Set ι) →₀ k[G]) := hfinsupp_injective
  refine ⟨?_⟩
  intro X Y _ _ _ _ i hi g
  -- Transport the extension problem across the linear equivalence with the finite free module.
  obtain ⟨h, hh⟩ := Module.Injective.out (Q := ↥(s : Set ι) →₀ k[G]) (f := i) hi
    (e.toLinearMap.comp g)
  refine ⟨e.symm.toLinearMap.comp h, ?_⟩
  intro x
  simpa using congrArg e.symm (hh x)

/-- Helper for Exercise 14-14.3-5: every free `k[G]`-module is injective. The key point is that a
map out of an ideal has image supported on finitely many basis coordinates once one restricts to a
finite `k`-basis of the ideal, so Baer's criterion reduces to the finite free case. -/
private theorem finsupp_groupAlgebra_injective
    {ι : Type w} :
    Module.Injective k[G] (ι →₀ k[G]) := by
  classical
  apply Module.Baer.injective
  intro I g
  let _ : Module.Finite k k[G] := MonoidAlgebra.moduleFinite
  let _ : Module.Finite k I := Module.Finite.of_injective (I.subtype.restrictScalars k)
    I.subtype_injective
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' k I
  let h : (Fin n → k) →ₗ[k] (ι →₀ k[G]) := (g.restrictScalars k).comp f
  let s : Finset ι := Finset.univ.biUnion fun j => (h (Pi.basisFun k (Fin n) j)).support
  let supportedK : Submodule k (ι →₀ k[G]) := Finsupp.supported k[G] k (s : Set ι)
  let supportedR : Submodule k[G] (ι →₀ k[G]) := Finsupp.supported k[G] k[G] (s : Set ι)
  have h_basis_mem : ∀ j, h (Pi.basisFun k (Fin n) j) ∈ supportedK := by
    intro j
    -- Each basis image is supported inside the explicit finite union of supports.
    rw [Finsupp.mem_supported]
    intro i hi
    exact Finset.mem_coe.2 <| Finset.mem_biUnion.2 ⟨j, by simp, hi⟩
  have h_rangeK : LinearMap.range h ≤ supportedK := by
    intro z hz
    rcases hz with ⟨y, rfl⟩
    have hy :
        h y = ∑ j, y j • h (Pi.basisFun k (Fin n) j) := by
      simpa using (congrArg h ((Pi.basisFun k (Fin n)).sum_repr y)).symm
    -- Rewrite through the standard basis and use support stability under finite sums.
    rw [hy]
    refine Submodule.sum_mem _ ?_
    intro j _
    exact Submodule.smul_mem _ _ (h_basis_mem j)
  have hg_range : LinearMap.range g ≤ supportedR := by
    intro z hz
    rcases hz with ⟨x, rfl⟩
    rcases hf x with ⟨y, rfl⟩
    have hzK : h y ∈ supportedK := h_rangeK ⟨y, rfl⟩
    rw [Finsupp.mem_supported] at hzK ⊢
    exact hzK
  let gSupported : I →ₗ[k[G]] supportedR :=
    LinearMap.codRestrict supportedR g fun x => hg_range ⟨x, rfl⟩
  have hsupported_injective : Module.Injective k[G] supportedR :=
    supported_groupAlgebra_module_injective (k := k) (G := G) s
  have hsupported_baer : Module.Baer k[G] supportedR :=
    Module.Baer.iff_injective.mpr hsupported_injective
  -- Extend inside the finite supported submodule, then include back into the full free module.
  obtain ⟨gExt, hgExt⟩ := hsupported_baer I gSupported
  refine ⟨supportedR.subtype.comp gExt, ?_⟩
  intro x hx
  simpa [gSupported] using congrArg supportedR.subtype (hgExt x hx)

/-- Helper for Exercise 14-14.3-5: a projective `k[G]`-module is injective because it is a direct
summand of a free module, and free `k[G]`-modules are injective by the Frobenius argument above. -/
private theorem projective_groupAlgebra_module_injective
    {M : Type w} [AddCommGroup M] [Module k[G] M]
    (hM : Module.Projective k[G] M) :
    Module.Injective k[G] M := by
  let π : (M →₀ k[G]) →ₗ[k[G]] M := Finsupp.linearCombination k[G] id
  have hπ_surjective : Function.Surjective π := by
    intro m
    refine ⟨Finsupp.single m 1, ?_⟩
    simpa [π] using
      (Finsupp.linearCombination_single (R := k[G]) (v := id) (c := (1 : k[G])) (a := m))
  obtain ⟨i, hi⟩ := (Module.Projective.iff_split_of_projective π hπ_surjective).1 hM
  have hfree_injective : Module.Injective k[G] (M →₀ k[G]) :=
    finsupp_groupAlgebra_injective (k := k) (G := G)
  let UM := ULift.{max u w, w} M
  let iU : UM →ₗ[k[G]] (M →₀ k[G]) := i.comp ULift.moduleEquiv.toLinearMap
  let sU : (M →₀ k[G]) →ₗ[k[G]] UM := ULift.moduleEquiv.symm.toLinearMap.comp π
  have hsUiU : sU.comp iU = LinearMap.id := by
    ext x
    simpa [sU, iU] using LinearMap.congr_fun hi x.down
  letI : Module.Injective k[G] (M →₀ k[G]) := hfree_injective
  have hUM_injective : Module.Injective k[G] UM := by
    refine ⟨?_⟩
    intro X Y _ _ _ _ a ha φ
    -- Extend into the free ambient module and project back along the lifted splitting.
    obtain ⟨l, hl⟩ := Module.Injective.out (Q := M →₀ k[G]) (f := a) ha (iU.comp φ)
    refine ⟨sU.comp l, ?_⟩
    intro x
    change sU (l (a x)) = φ x
    rw [hl]
    change (sU.comp iU) (φ x) = φ x
    simpa [hsUiU]
  exact Module.injective_of_ulift_injective k[G] hUM_injective

/-- Helper for Exercise 14-14.3-5: the source of a projective envelope is injective once the
forward implication `projective -> injective` has been established. -/
private theorem projective_envelope_source_injective
    {P M : Type w} [AddCommGroup P] [Module k[G] P]
    [AddCommGroup M] [Module k[G] M] {f : P →ₗ[k[G]] M}
    (hf : f.IsProjectiveEnvelope) :
    Module.Injective k[G] P := by
  -- The source is projective by definition of projective envelope, so the established forward
  -- implication upgrades it to injective.
  exact projective_groupAlgebra_module_injective (k := k) (G := G) hf.toProjective

/-- Helper for Exercise 14-14.3-5: a nontrivial `k[G]`-module forces `k[G]` to be small in that
module universe, so `ULift` can transport injectivity to the free-module universe needed below. -/
private theorem small_groupAlgebra_of_nontrivial_module
    (M : Type w) [AddCommGroup M] [Module k[G] M] [Nontrivial M] :
    Small.{w} k[G] := by
  classical
  let _ : Module k M := Module.compHom M (algebraMap k k[G])
  let m : M := Classical.choose (exists_ne (0 : M))
  have hm : m ≠ 0 := Classical.choose_spec (exists_ne (0 : M))
  have _ : Small.{w} k := small_of_injective (smul_left_injective k hm)
  let e : k[G] ≃ (G → k) := Finsupp.equivFunOnFinite
  exact small_map e

/-- Helper for Exercise 14-14.3-5: every `k[G]`-module embeds into a free `k[G]`-module by
recording the basis coordinates of all translated vectors inside copies of the regular module. -/
private theorem groupAlgebra_module_exists_free_embedding
    {M : Type w} [AddCommGroup M] [Module k[G] M] :
    ∃ (ι : Type w) (e : M →ₗ[k[G]] (ι →₀ k[G])), Function.Injective e := by
  classical
  letI : Module k M := Module.compHom M (algebraMap k k[G])
  letI : IsScalarTower k k[G] M := IsScalarTower.of_compHom k k[G] M
  letI : Fintype G := Fintype.ofFinite G
  let ι := Module.Free.ChooseBasisIndex k M
  let b : Module.Basis ι k M := Module.Free.chooseBasis k M
  let coordMap : ι → M →ₗ[k[G]] k[G] := fun i =>
    reconstruct_from_coeff_one_module (k := k) (G := G) (M := M)
      ((Finsupp.lapply i).comp b.repr.toLinearMap)
  let e : M →ₗ[k[G]] (ι →₀ k[G]) :=
    { toFun := fun m =>
        let s : Finset ι :=
          Finset.univ.biUnion fun t : G => (b.repr ((MonoidAlgebra.of k G t⁻¹) • m)).support
        Finsupp.onFinset s (fun i => coordMap i m) fun i hi => by
          obtain ⟨t, ht⟩ := Finsupp.support_nonempty_iff.mpr hi
          refine Finset.mem_biUnion.2 ?_
          refine ⟨t, by simp, ?_⟩
          exact Finsupp.mem_support_iff.mpr <| by
            simpa [coordMap, reconstruct_from_coeff_one_module_apply, LinearMap.comp_apply] using ht
      map_add' := by
        intro x y
        ext i
        -- Each coordinate is the translated coefficient map attached to the chosen `k`-basis.
        simp [coordMap]
      map_smul' := by
        intro a m
        ext i
        -- The reconstructed coordinate maps are already `k[G]`-linear, so the embedding is too.
        simp [coordMap] }
  refine ⟨ι, e, ?_⟩
  intro x y hxy
  have hrepr : b.repr x = b.repr y := by
    ext i
    have hi : e x i 1 = e y i 1 := congrArg (fun f : ι →₀ k[G] => f i 1) hxy
    have h1x : (MonoidAlgebra.single (1 : G) (1 : k) : k[G]) • x = x := by
      simpa [MonoidAlgebra.one_def] using (one_smul k[G] x)
    have h1y : (MonoidAlgebra.single (1 : G) (1 : k) : k[G]) • y = y := by
      simpa [MonoidAlgebra.one_def] using (one_smul k[G] y)
    -- Evaluating the `i`-th regular-module coordinate at `1` recovers the original basis
    -- coefficient.
    simpa [e, coordMap, reconstruct_from_coeff_one_module_apply, LinearMap.comp_apply,
      MonoidAlgebra.of_apply, MonoidAlgebra.one_def, inv_one, h1x, h1y] using hi
  exact b.repr.injective hrepr

/-- Helper for Exercise 14-14.3-5: an injective `k[G]`-module is projective because the canonical
free embedding splits against its injectivity. -/
private theorem injective_groupAlgebra_module_projective
    {M : Type w} [AddCommGroup M] [Module k[G] M]
    (hM : Module.Injective k[G] M) :
    Module.Projective k[G] M := by
  by_cases hSub : Subsingleton M
  · letI : Subsingleton M := hSub
    infer_instance
  · letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hSub
    letI : Small.{w} k[G] := small_groupAlgebra_of_nontrivial_module (k := k) (G := G) M
    obtain ⟨ι, e, he⟩ :=
      groupAlgebra_module_exists_free_embedding (k := k) (G := G) (M := M)
    let UM : Type (max u w) := ULift.{max u w, w} M
    let eUM : UM ≃ₗ[k[G]] M := ULift.moduleEquiv
    let eU : UM →ₗ[k[G]] (ι →₀ k[G]) := e.comp eUM.toLinearMap
    have heU : Function.Injective eU := he.comp eUM.injective
    have hUM_injective : Module.Injective k[G] UM :=
      Module.ulift_injective_of_injective.{u, w, max u w} k[G] hM
    letI : Module.Injective k[G] UM := hUM_injective
    obtain ⟨s, hs⟩ := Module.Injective.out (Q := UM) (f := eU) heU
      (LinearMap.id : UM →ₗ[k[G]] UM)
    have hs_split : s.comp eU = LinearMap.id := by
      ext m
      simpa [LinearMap.comp_apply] using hs m
    letI : Module.Projective k[G] (ι →₀ k[G]) := inferInstance
    have hUM_projective : Module.Projective k[G] UM :=
      Module.Projective.of_split eU s hs_split
    -- Split the lifted free embedding and transport projectivity back down through `ULift`.
    exact Module.Projective.of_equiv' (eUM : UM ≃ₗ[k[G]] M)

end Exercise_14_14_3_5

-- Proof sketch: use the self-injectivity of `k[G]` together with the finite-dimensional Frobenius
-- property of the group algebra: projectives are direct summands of free modules, hence injective,
-- and injectives become projective by the dual argument.
/-- Over the group algebra of a finite group, a module is projective if and only if it is
injective. -/
theorem groupAlgebra_module_projective_iff_injective :
    Module.Projective k[G] M ↔ Module.Injective k[G] M := by
  constructor
  · intro hM
    -- The forward implication is the free-module retract argument proved in the local helper API.
    exact Exercise_14_14_3_5.projective_groupAlgebra_module_injective
      (k := k) (G := G) hM
  · intro hM
    -- Route correction: instead of forcing a projective-envelope isomorphism, embed `M` into a
    -- free module built from translated basis coefficients and split that monomorphism by
    -- injectivity.
    exact Exercise_14_14_3_5.injective_groupAlgebra_module_projective
      (k := k) (G := G) hM

namespace Exercise_14_14_3_5

/-- Helper for Exercise 14-14.3-5: the source of a projective envelope of a simple `k[G]`-module
is cyclic, hence finitely generated. -/
private theorem moduleFinite_of_projectiveEnvelope_simple
    {P S : Type w} [AddCommGroup P] [Module k[G] P]
    [AddCommGroup S] [Module k[G] S] [IsSimpleModule k[G] S]
    {f : P →ₗ[k[G]] S} (hf : f.IsProjectiveEnvelope) :
    Module.Finite k[G] P := by
  letI : Nontrivial S := IsSimpleModule.nontrivial (R := k[G]) (M := S)
  obtain ⟨s, hs⟩ := exists_ne (0 : S)
  obtain ⟨x, hx⟩ := hf.surjective s
  let N : Submodule k[G] P := Submodule.span k[G] {x}
  have hmap_ne_bot : N.map f ≠ ⊥ := by
    intro hbot
    have hxmem : f x ∈ N.map f := by
      exact ⟨x, Submodule.mem_span_singleton_self x, rfl⟩
    have hfx : f x = 0 := by
      rw [hbot] at hxmem
      simpa using hxmem
    exact hs <| by simpa [hx] using hfx
  have hmap_top : N.map f = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top (N.map f)).resolve_left hmap_ne_bot
  have hN_top : N = ⊤ := hf.toIsEssential.eq_top_of_map_eq_top N hmap_top
  -- Once the cyclic span is all of `P`, the singleton generator gives the required finite source.
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton k[G] P x) := by
    simpa [LinearMap.toSpanSingleton_apply] using
      (Submodule.span_singleton_eq_top_iff (R := k[G]) (x := x)).1 (by simpa [N] using hN_top)
  exact Module.Finite.of_surjective (LinearMap.toSpanSingleton k[G] P x) hsurj

/-- Helper for Exercise 14-14.3-5: a finite projective `k[G]`-module is injective because it
splits off a finite free module, and finite products of the injective regular module are
injective. -/
private theorem finite_projective_groupAlgebra_module_injective
    {P : Type w} [AddCommGroup P] [Module k[G] P]
    [Module.Projective k[G] P] [Module.Finite k[G] P] :
    Module.Injective k[G] P := by
  obtain ⟨n, f, g, _, _, hfg⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective (R := k[G]) (M := P)
  -- First package the finite free ambient module as a finite product of copies of `k[G]`.
  have hF_injective : Module.Injective k[G] (Fin n → k[G]) := by
    let Z : Fin n → ModuleCat k[G] := fun _ => ModuleCat.of k[G] k[G]
    have hprodObj : CategoryTheory.Injective (∏ᶜ Z) := by
      have hobj : ∀ i, CategoryTheory.Injective (Z i) := fun _ =>
        (Module.injective_iff_injective_object k[G] k[G]).mp groupAlgebra_self_injective
      infer_instance
    let e : (∏ᶜ Z) ≅ ModuleCat.of k[G] (Fin n → k[G]) := ModuleCat.piIsoPi Z
    exact
      (Module.injective_iff_injective_object k[G] (Fin n → k[G])).mpr
        (CategoryTheory.Injective.of_iso e hprodObj)
  -- Lift both modules to a common universe so that the retract argument can be carried out
  -- directly with `Module.Injective.out`.
  let UP := ULift.{max u w, w} P
  let UF := ULift.{max u w, u} (Fin n → k[G])
  let gU : UP →ₗ[k[G]] UF :=
    ULift.moduleEquiv.symm.toLinearMap.comp (g.comp ULift.moduleEquiv.toLinearMap)
  let fU : UF →ₗ[k[G]] UP :=
    ULift.moduleEquiv.symm.toLinearMap.comp (f.comp ULift.moduleEquiv.toLinearMap)
  have hfUgU_down : ∀ x : UP, (fU (gU x)).down = x.down := by
    intro x
    change f (g x.down) = x.down
    exact LinearMap.congr_fun hfg x.down
  have hfUgU : fU.comp gU = LinearMap.id := by
    -- The lifted retraction still splits because the original one does.
    ext x
    exact hfUgU_down x
  have hUF_injective : Module.Injective k[G] UF :=
    Module.ulift_injective_of_injective k[G] hF_injective
  have hUP_injective : Module.Injective k[G] UP := by
    letI : Module.Injective k[G] UF := hUF_injective
    refine ⟨?_⟩
    intro X Y _ _ _ _ i hi φ
    obtain ⟨l, hl⟩ := Module.Injective.out (Q := UF) (f := i) hi (gU.comp φ)
    refine ⟨fU.comp l, ?_⟩
    intro x
    -- Extend into the finite free ambient module and project back along the retraction.
    change fU (l (i x)) = φ x
    rw [hl]
    change (fU.comp gU) (φ x) = φ x
    simpa [hfUgU]
  exact Module.injective_of_ulift_injective k[G] hUP_injective

/-- Helper for Exercise 14-14.3-5: every nonzero projective `k[G]`-module admits a simple
quotient, obtained by projecting a nonzero basis coordinate to a nonzero submodule of the regular
module and then quotienting by a coatom. -/
private theorem exists_simple_quotient_of_nonzero_projective_groupAlgebra_module
    {P : Type w} [AddCommGroup P] [Module k[G] P] [Module.Projective k[G] P]
    [Nontrivial P] :
    ∃ (S : Type u) (_ : AddCommGroup S) (_ : Module k[G] S)
      (_ : IsSimpleModule k[G] S) (q : P →ₗ[k[G]] S), Function.Surjective q := by
  classical
  obtain ⟨F, _, _, _, i, s, hs⟩ := (Module.Projective.iff_split (R := k[G]) (P := P)).mp inferInstance
  let b := Module.Free.chooseBasis k[G] F
  obtain ⟨x, hx⟩ := exists_ne (0 : P)
  have hix_ne : i x ≠ 0 := by
    intro hix
    have hsi : s (i x) = 0 := by
      simpa using congrArg s hix
    have hsx : s (i x) = x := by
      simpa using LinearMap.congr_fun hs x
    exact hx (hsx.symm.trans hsi)
  have hrepr_ne : b.repr (i x) ≠ 0 := by
    intro hrepr
    exact hix_ne ((LinearEquiv.map_eq_zero_iff b.repr).1 hrepr)
  obtain ⟨t, ht⟩ := (Finsupp.ne_iff.1 hrepr_ne)
  let π : F →ₗ[k[G]] k[G] := (Finsupp.lapply t).comp b.repr.toLinearMap
  have hπi_ne : π (i x) ≠ 0 := by
    simpa [π] using ht
  let N : Submodule k[G] k[G] := LinearMap.range (π.comp i)
  have hN_ne_bot : N ≠ ⊥ := by
    intro hN
    have hxmem : (π.comp i) x ∈ N := LinearMap.mem_range_self _ _
    rw [hN] at hxmem
    exact hπi_ne (by simpa using hxmem)
  letI : Module.Finite k k[G] := MonoidAlgebra.moduleFinite
  letI : IsArtinianRing k[G] := IsArtinianRing.of_finite k k[G]
  have hN_artinian : IsArtinian k[G] N := by infer_instance
  letI : IsCoatomic (Submodule k[G] N) :=
    LinearMap.isCoatomic_submodule_of_isArtinianRing_and_isArtinian (R := k[G]) (P := N)
  have hbot_ne_top : (⊥ : Submodule k[G] N) ≠ ⊤ := by
    letI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN_ne_bot
    exact bot_ne_top
  obtain ⟨K, hKcoatom, _⟩ :=
    (eq_top_or_exists_le_coatom (⊥ : Submodule k[G] N)).resolve_left hbot_ne_top
  let S := N ⧸ K
  let q : P →ₗ[k[G]] S := K.mkQ.comp (LinearMap.rangeRestrict (π.comp i))
  have hq_surjective : Function.Surjective q := by
    intro y
    rcases (Submodule.mkQ_surjective K) y with ⟨n, rfl⟩
    rcases n with ⟨n, hn⟩
    rcases hn with ⟨p, rfl⟩
    exact ⟨p, rfl⟩
  refine ⟨S, inferInstance, inferInstance, ?_, q, hq_surjective⟩
  exact (isSimpleModule_iff_isCoatom (R := k[G]) (m := K)).2 hKcoatom

/-- Helper for Exercise 14-14.3-5: an indecomposable projective `k[G]`-module is finite because it
identifies with the projective envelope of one of its simple quotients, and that envelope is
already finite. -/
private theorem moduleFinite_of_projective_indecomposable
    {P : ModuleCat (k[G])} [Module.Projective k[G] P]
    (hP : Indecomposable P) :
    Module.Finite k[G] P := by
  classical
  have hP_nontrivial : Nontrivial P := by
    refine not_subsingleton_iff_nontrivial.mp ?_
    intro hSub
    exact hP.1 ((ModuleCat.isZero_iff_subsingleton).2 hSub)
  letI : Nontrivial P := hP_nontrivial
  obtain ⟨S, _, _, hSsimple, q, hq_surj⟩ :=
    exists_simple_quotient_of_nonzero_projective_groupAlgebra_module
      (k := k) (G := G) (P := P)
  let S' : ModuleCat (k[G]) := ModuleCat.of k[G] S
  have hSsimple' : Simple S' := by
    letI : IsSimpleModule k[G] S := hSsimple
    infer_instance
  obtain ⟨Q, f, hf⟩ := exists_isProjectiveEnvelope (k := k) (G := G) (M := S')
  letI : Module.Projective k[G] Q := hf.toProjective
  have hQ_finite : Module.Finite k[G] Q :=
    moduleFinite_of_projectiveEnvelope_simple (k := k) (G := G) hf
  obtain ⟨u, hu⟩ := Module.projective_lifting_property f.hom q hf.surjective
  have hu_range_top : LinearMap.range u = ⊤ := by
    have hmap : (LinearMap.range u).map f.hom = ⊤ := by
      rw [← LinearMap.range_comp u f.hom]
      simpa [hu, LinearMap.range_eq_top] using LinearMap.range_eq_top.2 hq_surj
    exact hf.toIsEssential.eq_top_of_map_eq_top _ hmap
  have hu_surjective : Function.Surjective u := (LinearMap.range_eq_top.1 hu_range_top)
  obtain ⟨v, huv⟩ := (Module.Projective.iff_split_of_projective u hu_surjective).1 inferInstance
  have huv_left : Function.LeftInverse u v := by
    intro x
    exact LinearMap.congr_fun huv x
  let T : P →ₗ[k[G]] P := v.comp u
  have hT_idempotent : IsIdempotentElem T := by
    -- The splitting `u ∘ v = id` turns `v ∘ u` into an idempotent projector on `P`.
    ext x
    simp [T, huv_left (u x)]
  have hcompl : IsCompl (LinearMap.range T) (LinearMap.ker T) :=
    LinearMap.IsIdempotentElem.isCompl hT_idempotent
  have hTrange_ne_bot : LinearMap.range T ≠ ⊥ := by
    letI : Nontrivial S := IsSimpleModule.nontrivial (R := k[G]) (M := S)
    have hQ_nontrivial : Nontrivial Q := by
      refine not_subsingleton_iff_nontrivial.mp ?_
      intro hQsub
      letI : Subsingleton Q := hQsub
      have hSsub : Subsingleton S := hf.surjective.subsingleton
      exact not_nontrivial S inferInstance
    letI : Nontrivial Q := hQ_nontrivial
    obtain ⟨q₀, hq₀⟩ := exists_ne (0 : Q)
    intro hbot
    have hvq_mem : T (v q₀) ∈ LinearMap.range T := LinearMap.mem_range_self _ _
    have hvq_zero : T (v q₀) = 0 := by
      rw [hbot] at hvq_mem
      simpa using hvq_mem
    have hvq_eq : v q₀ = 0 := by
      simpa [T, huv_left q₀] using hvq_zero
    have : v q₀ = v 0 := by simpa using hvq_eq
    exact hq₀ (huv_left.injective this)
  let eProd : P ≃ₗ[k[G]] LinearMap.range T × LinearMap.ker T :=
    (LinearMap.range T).prodEquivOfIsCompl (LinearMap.ker T) hcompl |>.symm
  have hDecomp :
      P ≅ ModuleCat.of k[G] (LinearMap.range T) ⊞ ModuleCat.of k[G] (LinearMap.ker T) := by
    exact eProd.toModuleIso ≪≫
      (ModuleCat.biprodIsoProd
        (ModuleCat.of k[G] (LinearMap.range T))
        (ModuleCat.of k[G] (LinearMap.ker T))).symm
  rcases hP.2
      (ModuleCat.of k[G] (LinearMap.range T))
      (ModuleCat.of k[G] (LinearMap.ker T)) hDecomp with hRange_zero | hKer_zero
  · have hRange_subsingleton : Subsingleton (LinearMap.range T) :=
      (ModuleCat.isZero_iff_subsingleton).1 hRange_zero
    have hRange_nontrivial : Nontrivial (LinearMap.range T) :=
      Submodule.nontrivial_iff_ne_bot.mpr hTrange_ne_bot
    exact False.elim (not_nontrivial _ hRange_nontrivial)
  · have hKer_subsingleton : Subsingleton (LinearMap.ker T) :=
      (ModuleCat.isZero_iff_subsingleton).1 hKer_zero
    have hker_eq_bot : LinearMap.ker T = ⊥ :=
      Submodule.subsingleton_iff_eq_bot.mp hKer_subsingleton
    have hv_injective : Function.Injective v := huv_left.injective
    have hker_eq : LinearMap.ker T = LinearMap.ker u := by
      ext x
      constructor
      · intro hx
        have hTx : T x = 0 := by simpa using hx
        have huvx : v (u x) = 0 := by simpa [T] using hTx
        have : v (u x) = v 0 := by simpa using huvx
        simpa using hv_injective this
      · intro hx
        have hux : u x = 0 := by simpa using hx
        simpa [T, hux]
    have hu_injective : Function.Injective u := by
      rw [← LinearMap.ker_eq_bot, ← hker_eq, hker_eq_bot]
    let e : P ≃ₗ[k[G]] Q := LinearEquiv.ofBijective u ⟨hu_injective, hu_surjective⟩
    exact (Module.Finite.equiv_iff e).2 hQ_finite

/-- Helper for Exercise 14-14.3-5: a finite indecomposable injective `k[G]`-module is the
injective envelope of one of its simple submodules. -/
private theorem exists_simple_injectiveEnvelope_of_finite_injective_indecomposable
    {P : ModuleCat (k[G])} [Module.Injective k[G] P] [Module.Finite k[G] P]
    (hP : Indecomposable P) :
    ∃ (S : ModuleCat (k[G])) (f : S ⟶ P),
      Simple S ∧ f.hom.IsInjectiveEnvelope := by
  let _ : Module.Finite k k[G] := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing k[G] := IsArtinianRing.of_finite k k[G]
  let _ : IsArtinian k[G] P := by infer_instance
  let _ : IsNoetherian k[G] P := by infer_instance
  have hP_nontrivial : Nontrivial P := by
    refine not_subsingleton_iff_nontrivial.mp ?_
    intro hSub
    exact hP.1 ((ModuleCat.isZero_iff_subsingleton).2 hSub)
  letI : Nontrivial P := hP_nontrivial
  let A : Set (Submodule k[G] P) := {N | N ≠ ⊥}
  have hA_nonempty : A.Nonempty := ⟨⊤, top_ne_bot⟩
  obtain ⟨T, hT_mem, hT_min⟩ :=
    IsArtinian.set_has_minimal (R := k[G]) (M := P) A hA_nonempty
  have hT_ne_bot : T ≠ ⊥ := hT_mem
  have hT_simple : IsSimpleModule k[G] T := by
    rw [isSimpleModule_iff_isAtom]
    refine ⟨hT_ne_bot, ?_⟩
    intro U hUT
    by_contra hU_ne_bot
    exact hT_min U hU_ne_bot hUT
  let S : ModuleCat (k[G]) := ModuleCat.of k[G] T
  let i : S ⟶ P := ModuleCat.ofHom T.subtype
  have hi_injective : Function.Injective i.hom := T.subtype_injective
  refine ⟨S, i, ?_, ?_⟩
  · letI : IsSimpleModule k[G] T := hT_simple
    infer_instance
  · letI : IsSimpleModule k[G] T := hT_simple
    letI : Nontrivial T := IsSimpleModule.nontrivial (R := k[G]) (M := T)
    refine
      { toInjective := inferInstance
        toIsEssentialExtension := ?_
        injective := hi_injective }
    refine ⟨fun N hN => ?_⟩
    let q : P →ₗ[k[G]] P ⧸ N := N.mkQ
    have hqi_injective : Function.Injective (q.comp i.hom) := by
      intro x y hxy
      have hxy_zero : (q.comp i.hom) (x - y) = 0 := by
        simp [map_sub, hxy]
      have hxy_mem : i.hom (x - y) ∈ N ⊓ i.hom.range := by
        refine ⟨?_, LinearMap.mem_range_self _ _⟩
        exact (Submodule.Quotient.mk_eq_zero N).1 hxy_zero
      have hxy_bot : i.hom (x - y) = 0 := by
        have : i.hom (x - y) ∈ (⊥ : Submodule k[G] P) := by
          simpa [hN] using hxy_mem
        simpa using this
      exact sub_eq_zero.mp (hi_injective hxy_bot)
    have h_injective : Module.Injective k[G] P := inferInstance
    obtain ⟨h, hh⟩ := Module.Injective.out (Q := P) (f := q.comp i.hom) hqi_injective i.hom
    let u : P →ₗ[k[G]] P := h.comp q
    have hu_fix : ∀ x : T, u (i.hom x) = i.hom x := by
      intro x
      exact hh x
    have hN_le_ker_u : N ≤ LinearMap.ker u := by
      intro x hx
      change h (q x) = 0
      rw [show q x = 0 by exact (Submodule.Quotient.mk_eq_zero N).2 hx, map_zero]
    obtain ⟨m, hm⟩ :=
      Filter.eventually_atTop.mp
        (LinearMap.eventually_isCompl_ker_pow_range_pow (R := k[G]) (M := P) u)
    let n : ℕ := m + 1
    have hcompl : IsCompl (LinearMap.ker (u ^ n)) (LinearMap.range (u ^ n)) := by
      exact hm n (Nat.le_succ m)
    obtain ⟨t, ht⟩ := exists_ne (0 : T)
    have hrange_ne_bot : LinearMap.range (u ^ n) ≠ ⊥ := by
      intro hrange
      have hpow_fix : (u ^ n) (i.hom t) = i.hom t := by
        induction n with
        | zero =>
            simp
        | succ n ih =>
            calc
              (u ^ (n + 1)) (i.hom t) = (u ^ n) (u (i.hom t)) := by
                simp [pow_succ, Module.End.mul_apply]
              _ = (u ^ n) (i.hom t) := by
                exact congrArg (fun y => (u ^ n) y) (hu_fix t)
              _ = i.hom t := ih
      have hit_mem : i.hom t ∈ LinearMap.range (u ^ n) := ⟨i.hom t, hpow_fix⟩
      have hit_zero : i.hom t = 0 := by
        rw [hrange] at hit_mem
        simpa using hit_mem
      exact ht (hi_injective hit_zero)
    let eProd : P ≃ₗ[k[G]] LinearMap.ker (u ^ n) × LinearMap.range (u ^ n) :=
      (LinearMap.ker (u ^ n)).prodEquivOfIsCompl (LinearMap.range (u ^ n)) hcompl |>.symm
    have hDecomp :
        P ≅ ModuleCat.of k[G] (LinearMap.ker (u ^ n)) ⊞
          ModuleCat.of k[G] (LinearMap.range (u ^ n)) := by
      exact eProd.toModuleIso ≪≫
        (ModuleCat.biprodIsoProd
          (ModuleCat.of k[G] (LinearMap.ker (u ^ n)))
          (ModuleCat.of k[G] (LinearMap.range (u ^ n)))).symm
    rcases hP.2
        (ModuleCat.of k[G] (LinearMap.ker (u ^ n)))
        (ModuleCat.of k[G] (LinearMap.range (u ^ n))) hDecomp with hker_zero | hrange_zero
    · have hker_subsingleton : Subsingleton (LinearMap.ker (u ^ n)) :=
        (ModuleCat.isZero_iff_subsingleton).1 hker_zero
      have hker_eq_bot : LinearMap.ker (u ^ n) = ⊥ :=
        Submodule.subsingleton_iff_eq_bot.mp hker_subsingleton
      have hN_le_ker_pow : N ≤ LinearMap.ker (u ^ n) := by
        change N ≤ LinearMap.ker (u ^ (m + 1))
        intro x hx
        have hux : u x = 0 := hN_le_ker_u hx
        simp [pow_succ, Module.End.mul_apply, hux]
      exact le_bot_iff.mp (by simpa [hker_eq_bot] using hN_le_ker_pow)
    · have hrange_nontrivial : Nontrivial (LinearMap.range (u ^ n)) :=
        Submodule.nontrivial_iff_ne_bot.mpr hrange_ne_bot
      have hrange_subsingleton : Subsingleton (LinearMap.range (u ^ n)) :=
        (ModuleCat.isZero_iff_subsingleton).1 hrange_zero
      exfalso
      exact not_nontrivial _ hrange_nontrivial

/-- Helper for Exercise 14-14.3-5: once projective and injective modules are identified, the
finite projective indecomposable case of the final statement follows from the injective-side
envelope argument. -/
private theorem exists_simple_injectiveEnvelope_of_finite_projective_indecomposable
    {P : ModuleCat (k[G])} [Module.Projective k[G] P] [Module.Finite k[G] P]
    (hP : Indecomposable P) :
    ∃ (S : ModuleCat (k[G])) (f : S ⟶ P),
      Simple S ∧ f.hom.IsInjectiveEnvelope := by
  -- Convert the finite indecomposable projective into the injective case handled above by
  -- splitting it off a finite free injective ambient module.
  have hPinj : Module.Injective k[G] P :=
    finite_projective_groupAlgebra_module_injective (k := k) (G := G) (P := P)
  letI : Module.Injective k[G] P := hPinj
  exact exists_simple_injectiveEnvelope_of_finite_injective_indecomposable
    (k := k) (G := G) hP

end Exercise_14_14_3_5

-- Proof sketch: combine Corollary `14-14.3-2 (3)` with the previous equivalence. A projective
-- indecomposable module is the projective envelope of a simple module, and after identifying
-- projective with injective over `k[G]`, the same object becomes the injective envelope of that
-- simple module.
/-- Every projective indecomposable `k[G]`-module is an injective envelope of a simple
`k[G]`-module. -/
theorem indecomposable_projective_groupAlgebra_module_exists_simple_injectiveEnvelope
    {P : ModuleCat (k[G])} [Module.Projective k[G] P] (hP : Indecomposable P) :
    ∃ (S : ModuleCat (k[G])) (f : S ⟶ P),
      Simple S ∧ f.hom.IsInjectiveEnvelope := by
  -- Route correction: instead of forcing the full projective/injective equivalence first, prove
  -- finiteness of the indecomposable projective by comparison with a projective envelope of a
  -- simple quotient, then invoke the finite projective injective-envelope result.
  letI : Module.Finite k[G] P :=
    Exercise_14_14_3_5.moduleFinite_of_projective_indecomposable (k := k) (G := G) hP
  exact
    Exercise_14_14_3_5.exists_simple_injectiveEnvelope_of_finite_projective_indecomposable
      (k := k) (G := G) hP

end
