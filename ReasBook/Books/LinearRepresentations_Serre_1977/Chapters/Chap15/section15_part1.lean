import Mathlib
import Mathlib.Algebra.Module.Lattice
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_15_1_1 (from Chap15) -/
noncomputable section

universe u w x

open CategoryTheory
open scoped Representation
open scoped MonoidAlgebra

namespace Representation

section CartanHom

variable (k : Type u) [Field k] (G : Type u) [Group G] [Finite G]

local notation:max "P₀[" A "](" G ")" =>
  finiteProjectiveGroupAlgebraGrothendieckGroup A G

/- Domain-style sampling for this item:
* core/canonical owners already fixed upstream in Chapter `14`: `P₀[k](G)` for finite projective
  `k[G]`-modules and `R₀[k](G)` for finite-dimensional `k`-representations.
* source-facing declaration in this file: LinearRepresentations_Serre_1977's Cartan homomorphism `c : P_k(G) → R_k(G)`.
* bridge/view layer: `cartanHom` is the additive map induced by forgetting projectivity, while
  `cartanCokernel` and `cartanMatrix` are derived companions of that owner.

Primitive data vs derived API:
* primitive data: the canonical owner map `FiniteProjectiveGroupAlgebraModule.toFiniteRep` and the
  Grothendieck relations on `P₀[k](G)` and `R₀[k](G)`.
* derived API: the descended homomorphism `cartanHom`, its evaluation on projective classes, the
  quotient `cartanCokernel`, and the thin basis-dependent matrix view `cartanMatrix`.
-/

private abbrev cartanLift :
    FreeAbelianGroup (FiniteProjectiveGroupAlgebraModule k G) →+
      R₀[k](G) :=
  FreeAbelianGroup.lift fun P ↦ [P.toFiniteRep]₀

/-- Helper for Definition 15-15.1-1: the inclusion of finite projective `k[G]`-modules into the
ambient category of finitely generated `k[G]`-modules. -/
private abbrev finiteProjective_toFGModuleCat :
    FiniteProjectiveGroupAlgebraModule k G ⥤ FGModuleCat k[G] :=
  ObjectProperty.ι (fun M : FGModuleCat k[G] ↦ Module.Projective k[G] M)

/-- Helper for Definition 15-15.1-1: forgetting projectivity and finite generation yields the
ambient `ModuleCat k[G]` owner. -/
private abbrev finiteProjective_toModuleCat :
    FiniteProjectiveGroupAlgebraModule k G ⥤ ModuleCat k[G] :=
  finiteProjective_toFGModuleCat (k := k) (G := G) ⋙ (ModuleCat.isFG k[G]).ι

/-- Helper for Definition 15-15.1-1: forgetting projectivity all the way to `Rep k G`. -/
private abbrev finiteProjective_toRep :
    FiniteProjectiveGroupAlgebraModule k G ⥤ Rep k G :=
  finiteProjective_toModuleCat (k := k) (G := G) ⋙ Rep.ofModuleMonoidAlgebra

/-- Helper for Definition 15-15.1-1: the underlying `Rep k G` morphism attached to a morphism of
finite projective `k[G]`-modules. -/
private abbrev projective_toFiniteRep_repMap
    {P Q : FiniteProjectiveGroupAlgebraModule k G} (f : P ⟶ Q) :
    ((forget₂ (FDRep k G) (Rep k G)).obj P.toFiniteRep ⟶
      (forget₂ (FDRep k G) (Rep k G)).obj Q.toFiniteRep) :=
  Rep.ofModuleMonoidAlgebra.map f.hom.hom

/-- Helper for Definition 15-15.1-1: the corresponding morphism in `FDRep k G` obtained by
forgetting projectivity. -/
private abbrev projective_toFiniteRep_map
    {P Q : FiniteProjectiveGroupAlgebraModule k G} (f : P ⟶ Q) :
    P.toFiniteRep ⟶ Q.toFiniteRep :=
  (FDRep.forget₂HomLinearEquiv P.toFiniteRep Q.toFiniteRep)
    (projective_toFiniteRep_repMap (k := k) (G := G) f)

/-- Helper for Definition 15-15.1-1: forgetting the `FDRep` morphism recovers the canonical
`Rep`-level map. -/
private theorem projective_toFiniteRep_map_forget
    {P Q : FiniteProjectiveGroupAlgebraModule k G} (f : P ⟶ Q) :
    (forget₂ (FDRep k G) (Rep k G)).map
        (projective_toFiniteRep_map (k := k) (G := G) f) =
      projective_toFiniteRep_repMap (k := k) (G := G) f := by
  -- Unpack the `FDRep.forget₂HomLinearEquiv` bridge once so later exactness arguments can work in
  -- the simpler `Rep` owner.
  change (FDRep.forget₂HomLinearEquiv P.toFiniteRep Q.toFiniteRep).symm
      ((FDRep.forget₂HomLinearEquiv P.toFiniteRep Q.toFiniteRep)
        (projective_toFiniteRep_repMap (k := k) (G := G) f)) =
    projective_toFiniteRep_repMap (k := k) (G := G) f
  exact (FDRep.forget₂HomLinearEquiv P.toFiniteRep Q.toFiniteRep).left_inv _

omit [Finite G] in
/-- Helper for Definition 15-15.1-1: the underlying `ModuleCat k[G]` short complex still satisfies
the relation `g ∘ f = 0`. -/
private theorem finiteProjective_underlying_moduleCat_zero
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) :
    S.f.hom.hom ≫ S.g.hom.hom = 0 := by
  let F : FiniteProjectiveGroupAlgebraModule k G ⥤ ModuleCat k[G] :=
    finiteProjective_toModuleCat (k := k) (G := G)
  -- The underlying `ModuleCat` short complex is definitionally the image of `S` under the
  -- inclusion functor.
  simpa [F, finiteProjective_toModuleCat, finiteProjective_toFGModuleCat] using (S.map F).zero

/-- Helper for Definition 15-15.1-1: the transported short complex in `FDRep k G` still has zero
composite. -/
private theorem projective_toFiniteRep_shortComplex_zero
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) :
    projective_toFiniteRep_map (k := k) (G := G) S.f ≫
        projective_toFiniteRep_map (k := k) (G := G) S.g = 0 := by
  -- Forget to `Rep`, where the two structure maps are the functorial images of the underlying
  -- `k[G]`-linear maps.
  apply (forget₂ (FDRep k G) (Rep k G)).map_injective
  rw [Functor.map_comp]
  rw [projective_toFiniteRep_map_forget (k := k) (G := G) S.f]
  rw [projective_toFiniteRep_map_forget (k := k) (G := G) S.g]
  have hRep :
      projective_toFiniteRep_repMap (k := k) (G := G) S.f ≫
        projective_toFiniteRep_repMap (k := k) (G := G) S.g = 0 := by
    -- Map the already-known zero relation in `ModuleCat k[G]` through
    -- `Rep.ofModuleMonoidAlgebra`.
    have hModule :=
      congrArg (fun m ↦ Rep.ofModuleMonoidAlgebra.map m)
        (finiteProjective_underlying_moduleCat_zero (k := k) (G := G) S)
    simpa [projective_toFiniteRep_repMap] using hModule
  exact hRep

/-- Helper for Definition 15-15.1-1: forgetting projectivity produces a short complex of
finite-dimensional representations. -/
private abbrev projective_toFiniteRep_shortComplex
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) :
    ShortComplex (FDRep k G) :=
  ShortComplex.mk
    (projective_toFiniteRep_map (k := k) (G := G) S.f)
    (projective_toFiniteRep_map (k := k) (G := G) S.g)
    (projective_toFiniteRep_shortComplex_zero (k := k) (G := G) S)

/-- Helper for Definition 15-15.1-1: after forgetting `FDRep`, the transported short complex is
definitionally the same `Rep`-valued short complex obtained by forgetting projectivity directly.
-/
private theorem projective_toFiniteRep_shortComplex_map_forget
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) :
    ((projective_toFiniteRep_shortComplex (k := k) (G := G) S).map
      (forget₂ (FDRep k G) (Rep k G))) =
        S.map (finiteProjective_toRep (k := k) (G := G)) := by
  -- Both sides are built from the same `Rep`-level morphisms, so the short complexes coincide
  -- definitionally.
  rfl

/-- Helper for Definition 15-15.1-1: the same definitional identification remains true after one
more forgetful step to `ModuleCat k`. -/
private theorem projective_toFiniteRep_shortComplex_map_forget_moduleCat
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) :
    (((projective_toFiniteRep_shortComplex (k := k) (G := G) S).map
      (forget₂ (FDRep k G) (Rep k G))).map
        (forget₂ (Rep k G) (ModuleCat k))) =
      (S.map (finiteProjective_toRep (k := k) (G := G))).map
        (forget₂ (Rep k G) (ModuleCat k)) := by
  -- Forgetting once more to `k`-vector spaces preserves the same definitional short-complex
  -- identification.
  simpa using congrArg
    (fun T : ShortComplex (Rep k G) ↦ T.map (forget₂ (Rep k G) (ModuleCat k)))
    (projective_toFiniteRep_shortComplex_map_forget (k := k) (G := G) S)

omit [Finite G] in
/-- Helper for Definition 15-15.1-1: the cyclic map generated by `x` in a `k[G]`-module sends
`1` to `x`. -/
private theorem regular_module_generated_map_apply_one
    {M : Type w} [AddCommGroup M] [Module k[G] M] (x : M) :
    (((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight x) 1 : M) = x := by
  -- Evaluating the cyclic map at the regular-module generator recovers the chosen vector.
  simp

omit [Finite G] in
/-- Helper for Definition 15-15.1-1: if `x` lies in the kernel of `g`, then the cyclic map
`r ↦ r • x` already lands in that kernel. -/
private theorem regular_module_generated_map_comp_zero
    {M : Type w} [AddCommGroup M] [Module k[G] M]
    {N : Type w} [AddCommGroup N] [Module k[G] N]
    (g : M →ₗ[k[G]] N) (x : M) (hx : g x = 0) :
    g.comp ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight x) = 0 := by
  -- Extensionality reduces the whole claim to the single kernel hypothesis `g x = 0`.
  ext
  simp [hx]

/-- Helper for Definition 15-15.1-1: the regular `k[G]`-module viewed inside the finite-projective
owner category. -/
private abbrev finiteProjective_regular_owner :
    FiniteProjectiveGroupAlgebraModule k G :=
  ⟨FGModuleCat.of k[G] k[G], inferInstance⟩

/-- Helper for Definition 15-15.1-1: a nontrivial finite `k[G]`-module admits a nonzero map to
the regular module `k[G]`. -/
private theorem exists_nonzero_map_to_regular_of_nontrivial
    {M : Type w} [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    [Module.Finite k M] [Nontrivial M] :
    ∃ φ : M →ₗ[k[G]] k[G], φ ≠ 0 := by
  classical
  let b := Module.Free.chooseBasis k M
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have hrepr_ne : b.repr m ≠ 0 := by
    -- A nonzero vector has a nonzero coordinate in any basis.
    intro hrepr
    exact hm ((LinearEquiv.map_eq_zero_iff b.repr).1 hrepr)
  obtain ⟨t, ht⟩ := Finsupp.ne_iff.1 hrepr_ne
  let L : M →ₗ[k] k := (Finsupp.lapply t).comp b.repr.toLinearMap
  letI : Fintype G := Fintype.ofFinite G
  let φFun : M → k[G] :=
    fun m' => Finsupp.equivFunOnFinite.symm fun s => L ((MonoidAlgebra.of k G s⁻¹) • m')
  have hφFun_add : ∀ x y, φFun (x + y) = φFun x + φFun y := by
    intro x y
    apply Finsupp.equivFunOnFinite.injective
    funext s
    simp [φFun, smul_add, map_add]
  have hφFun_smul : ∀ (a : k[G]) m', φFun (a • m') = a * φFun m' := by
    intro a m'
    let h : k[G] := Finsupp.equivFunOnFinite.symm fun s => L ((MonoidAlgebra.of k G s⁻¹) • m')
    apply Finsupp.equivFunOnFinite.injective
    funext s
    let P : k[G] → Prop := fun c => L ((MonoidAlgebra.of k G s⁻¹) • (c • m')) = (c * h) s
    have hPa : P a := by
      -- Expand the group-algebra scalar one basis vector at a time.
      refine MonoidAlgebra.induction_on a ?_ ?_ ?_
      · intro g
        have hsmul :
            MonoidAlgebra.single s⁻¹ (1 : k) • MonoidAlgebra.single g (1 : k) • m' =
              (MonoidAlgebra.single (s⁻¹ * g) (1 : k) : k[G]) • m' := by
          simpa using
            (smul_assoc (MonoidAlgebra.single s⁻¹ (1 : k)) (MonoidAlgebra.single g (1 : k)) m').symm
        calc
          L ((MonoidAlgebra.of k G s⁻¹) • ((MonoidAlgebra.of k G g) • m')) =
              L (MonoidAlgebra.single s⁻¹ (1 : k) • MonoidAlgebra.single g (1 : k) • m') := by
                simp [MonoidAlgebra.of_apply]
          _ = L ((MonoidAlgebra.single (s⁻¹ * g) (1 : k) : k[G]) • m') := by
                exact congrArg L hsmul
          _ = (((MonoidAlgebra.of k G g) * h : k[G]) s) := by
                simp [h, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_apply]
      · intro c d hc hd
        calc
          L ((MonoidAlgebra.of k G s⁻¹) • ((c + d) • m')) =
              L ((MonoidAlgebra.of k G s⁻¹) • (c • m')) +
                L ((MonoidAlgebra.of k G s⁻¹) • (d • m')) := by
                  simp [add_smul, map_add]
          _ = (c * h) s + (d * h) s := by rw [hc, hd]
          _ = ((c + d) * h) s := by simp [add_mul]
      · intro r c hc
        calc
          L ((MonoidAlgebra.of k G s⁻¹) • ((r • c) • m')) =
              r * L ((MonoidAlgebra.of k G s⁻¹) • (c • m')) := by
                have hs :
                    (MonoidAlgebra.of k G s⁻¹) • ((r • c) • m') =
                      r • ((MonoidAlgebra.of k G s⁻¹) • (c • m')) := by
                  calc
                    (MonoidAlgebra.of k G s⁻¹) • ((r • c) • m') =
                        (((MonoidAlgebra.of k G s⁻¹) * (r • c)) : k[G]) • m' := by
                          simpa using
                            (smul_assoc (MonoidAlgebra.of k G s⁻¹) (r • c) m').symm
                    _ = (r • (((MonoidAlgebra.of k G s⁻¹) * c : k[G]))) • m' := by
                          rw [mul_smul_comm]
                    _ = r • ((((MonoidAlgebra.of k G s⁻¹) * c : k[G])) • m') := by
                          simpa using
                            (smul_assoc r (((MonoidAlgebra.of k G s⁻¹) * c : k[G])) m')
                    _ = r • ((MonoidAlgebra.of k G s⁻¹) • (c • m')) := by
                          simpa [smul_eq_mul] using
                            congrArg (fun x : M => r • x)
                              (smul_assoc (MonoidAlgebra.of k G s⁻¹) c m')
                calc
                  L ((MonoidAlgebra.of k G s⁻¹) • ((r • c) • m')) =
                      L (r • ((MonoidAlgebra.of k G s⁻¹) • (c • m'))) := by
                        exact congrArg L hs
                  _ = r * L ((MonoidAlgebra.of k G s⁻¹) • (c • m')) := by
                        simp
          _ = r * (c * h) s := by rw [hc]
          _ = ((r • c) * h) s := by simp
    simpa [φFun, h] using hPa
  let φ : M →ₗ[k[G]] k[G] :=
    { toFun := φFun
      map_add' := hφFun_add
      map_smul' := hφFun_smul }
  have hφ_apply : ∀ m' s, φ m' s = L ((MonoidAlgebra.of k G s⁻¹) • m') := by
    intro m' s
    rfl
  refine ⟨φ, ?_⟩
  intro hφ
  have hφm : φ m = 0 := by simp [hφ]
  have hLm' : L ((MonoidAlgebra.of k G (1 : G)⁻¹) • m) = 0 := by
    -- Reading the coefficient at `1` of `φ m` recovers the chosen coordinate functional.
    simpa [hφ_apply] using congrArg (fun z : k[G] => z 1) hφm
  have hof_one : (MonoidAlgebra.of k G ((1 : G)⁻¹) : k[G]) = 1 := by
    ext g
    simp [MonoidAlgebra.of_apply, MonoidAlgebra.one_def]
  have hsingle_one_smul : (MonoidAlgebra.single 1 (1 : k) : k[G]) • m = m := by
    simpa [MonoidAlgebra.one_def] using (one_smul k[G] m)
  have hLm : L m = 0 := by
    have hLm'' : L ((MonoidAlgebra.single 1 (1 : k) : k[G]) • m) = 0 := by
      simpa [hof_one, MonoidAlgebra.one_def] using hLm'
    simpa [hsingle_one_smul] using hLm''
  exact ht (by simpa [L] using hLm)

/-- Helper for Definition 15-15.1-1: an epimorphism in the finite-projective owner category is
already surjective on the forgotten underlying `k[G]`-linear map. -/
private theorem finiteProjective_underlying_surjective_of_epi
    {E X : FiniteProjectiveGroupAlgebraModule k G} (e : E ⟶ X) [Epi e] :
    Function.Surjective e.hom.hom.hom := by
  let eLin : E.V →ₗ[k[G]] X.V := e.hom.hom.hom
  by_contra hnsurj
  let Q : Type u := X.V ⧸ LinearMap.range eLin
  let q : X.V →ₗ[k[G]] Q := (LinearMap.range eLin).mkQ
  have hQ_nontrivial : Nontrivial Q := by
    -- If the quotient vanished, then `range(e)` would already be all of `X`.
    apply not_subsingleton_iff_nontrivial.mp
    intro hQ_sub
    apply hnsurj
    exact LinearMap.range_eq_top.mp ((Submodule.Quotient.subsingleton_iff).mp hQ_sub)
  letI : Nontrivial Q := hQ_nontrivial
  letI : Module k Q := Module.compHom Q (algebraMap k k[G])
  letI : IsScalarTower k k[G] Q := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module.Finite k Q := by
    let _ : Module.Finite k k[G] := MonoidAlgebra.moduleFinite
    exact Module.Finite.trans k[G] Q
  obtain ⟨η, hη_nonzero⟩ :=
    exists_nonzero_map_to_regular_of_nontrivial (k := k) (G := G) (M := Q)
  let gLin : X.V →ₗ[k[G]] k[G] := η.comp q
  have hq_comp : q.comp eLin = 0 := by
    -- The quotient map kills the image of `e`.
    ext x
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
  have hgLin_comp : gLin.comp eLin = 0 := by
    -- Therefore the induced probe to the regular module annihilates `e`.
    ext x s
    have hηx : η (q (eLin x)) = 0 := by
      rw [show q (eLin x) = 0 by exact LinearMap.congr_fun hq_comp x, LinearMap.map_zero]
    simpa [gLin, LinearMap.comp_apply] using congrArg (fun z : k[G] => z s) hηx
  have hgLin_nonzero : gLin ≠ 0 := by
    -- Surjectivity of the quotient map pushes a zero composite back to `η = 0`.
    intro hgLin_zero
    have hη_zero : η = (0 : Q →ₗ[k[G]] k[G]) := by
      apply LinearMap.ext
      intro y
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range eLin) y
      exact LinearMap.congr_fun hgLin_zero x
    exact hη_nonzero hη_zero
  let g : X ⟶ finiteProjective_regular_owner (k := k) (G := G) :=
    ObjectProperty.homMk (FGModuleCat.ofHom gLin)
  have hg_nonzero : g ≠ 0 := by
    -- Equality to zero in the owner category is equality to zero on underlying linear maps.
    intro hg_zero
    have hg_hom_zero : g.hom = 0 := by
      simpa using
        congrArg (fun f : X ⟶ finiteProjective_regular_owner (k := k) (G := G) => f.hom) hg_zero
    rw [show g = ObjectProperty.homMk (FGModuleCat.ofHom gLin) by rfl] at hg_hom_zero
    have hg_lin_zero : gLin = 0 := by
      ext x s
      have h0 :=
        congrArg
          (fun f : X.obj ⟶ (finiteProjective_regular_owner (k := k) (G := G)).obj =>
            (f.hom.hom x) s)
          hg_hom_zero
      simpa [FGModuleCat.ofHom] using h0
    exact hgLin_nonzero hg_lin_zero
  have hge : e ≫ g = 0 := by
    -- Package the annihilating composite as an equality back in the owner category.
    apply ObjectProperty.hom_ext
    apply FGModuleCat.hom_ext
    ext x s
    simpa [g, FGModuleCat.ofHom, LinearMap.comp_apply] using
      congrArg (fun z : k[G] => z s) (LinearMap.congr_fun hgLin_comp x)
  have : g = 0 := (cancel_epi e).1 (by simpa using hge)
  exact hg_nonzero this

/-- Helper for Definition 15-15.1-1: the regular owner is projective in the finite-projective
category because owner epimorphisms are already surjective on underlying `k[G]`-modules. -/
private theorem regular_owner_projective :
    Projective (finiteProjective_regular_owner (k := k) (G := G)) := by
  refine ⟨?_⟩
  intro E X f e hepi
  letI : Epi e := hepi
  let eLin : E.V →ₗ[k[G]] X.V := e.hom.hom.hom
  let fLin : k[G] →ₗ[k[G]] X.V := f.hom.hom.hom
  have hsurj : Function.Surjective eLin := by
    -- Lift along the underlying surjective linear map.
    simpa [eLin] using finiteProjective_underlying_surjective_of_epi (k := k) (G := G) e
  obtain ⟨l, hl⟩ := Module.projective_lifting_property eLin fLin hsurj
  refine ⟨ObjectProperty.homMk (FGModuleCat.ofHom l), ?_⟩
  -- Repackage the linear lift as a morphism in the owner category.
  apply ObjectProperty.hom_ext
  apply FGModuleCat.hom_ext
  simpa [eLin, fLin] using hl

/-- Helper for Definition 15-15.1-1: a kernel element of the forgotten right map comes from the
forgotten left map by lifting the regular cyclic map through the source exactness witness. -/
private theorem finiteProjective_regular_owner_lift_of_kernel_element
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) (hS : S.ShortExact)
    (x₂ : S.X₂.V) (hx₂ : S.g.hom.hom x₂ = 0) :
    ∃ x₁ : S.X₁.V, S.f.hom.hom x₁ = x₂ := by
  haveI : Projective (finiteProjective_regular_owner (k := k) (G := G)) :=
    regular_owner_projective (k := k) (G := G)
  haveI : S.HasHomology := hS.exact.hasHomology
  let hLeft := S.leftHomologyData
  let ψ₂ : finiteProjective_regular_owner (k := k) (G := G) ⟶ S.X₂ :=
    ObjectProperty.homMk (FGModuleCat.ofHom ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight x₂))
  have hψ₂_zero_lin :
      S.g.hom.hom.hom.comp ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight x₂) = 0 := by
    -- The cyclic map generated by a cycle stays in the cycles object.
    exact regular_module_generated_map_comp_zero (k := k) (G := G) S.g.hom.hom.hom x₂ hx₂
  have hψ₂_zero : ψ₂ ≫ S.g = 0 := by
    -- Repackage the vanishing composite inside the owner category.
    apply ObjectProperty.hom_ext
    apply FGModuleCat.hom_ext
    simpa [ψ₂, FGModuleCat.ofHom] using hψ₂_zero_lin
  let ψK : finiteProjective_regular_owner (k := k) (G := G) ⟶ hLeft.K :=
    hLeft.liftK ψ₂ hψ₂_zero
  haveI : Epi hLeft.f' := hS.exact.epi_f' hLeft
  let ψ₁ : finiteProjective_regular_owner (k := k) (G := G) ⟶ S.X₁ :=
    Projective.factorThru ψK hLeft.f'
  have hψ₁_factor : ψ₁ ≫ hLeft.f' = ψK := by
    simpa [ψ₁] using (Projective.factorThru_comp ψK hLeft.f')
  have hψ₁f : ψ₁ ≫ S.f = ψ₂ := by
    -- Compare both lifts after factoring through the cycles object.
    calc
      ψ₁ ≫ S.f = ψ₁ ≫ hLeft.f' ≫ hLeft.i := by
        simp [hLeft.f'_i]
      _ = ψK ≫ hLeft.i := by
        simpa [Category.assoc] using congrArg (fun φ => φ ≫ hLeft.i) hψ₁_factor
      _ = ψ₂ := by
        simpa [ψK] using hLeft.liftK_i ψ₂ hψ₂_zero
  refine ⟨ψ₁.hom.hom.hom 1, ?_⟩
  -- Evaluate the lifted equality at `1` to recover the original cycle.
  have hEval := ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.hom) hψ₁f) 1
  have hEval' :
      S.f.hom.hom.hom (ψ₁.hom.hom.hom 1) =
        ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight x₂) 1 := by
    have hψ₂_eval :
        (ConcreteCategory.hom
            (FGModuleCat.ofHom ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight x₂)).hom) 1 =
          ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight x₂) 1 := rfl
    exact hEval.trans hψ₂_eval
  simpa [regular_module_generated_map_apply_one (k := k) (G := G) (x := x₂)] using hEval'

/-- Helper for Definition 15-15.1-1: owner-category exactness is already exactness of the
underlying `k[G]`-linear maps. -/
private theorem finiteProjective_underlying_function_exact
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) (hS : S.ShortExact) :
    Function.Exact S.f.hom.hom S.g.hom.hom := by
  intro x₂
  constructor
  · intro hx₂
    -- Lift the cyclic probe of a cycle through the left-homology factorization.
    exact
      finiteProjective_regular_owner_lift_of_kernel_element
        (k := k) (G := G) S hS x₂ hx₂
  · intro hx₂
    -- The reverse inclusion is just the already-known identity `g ∘ f = 0`.
    rcases hx₂ with ⟨x₁, hx₁⟩
    have hzero : S.g.hom.hom (S.f.hom.hom x₁) = 0 := by
      simpa using
        ConcreteCategory.congr_hom
          (finiteProjective_underlying_moduleCat_zero (k := k) (G := G) S) x₁
    simpa [hx₁] using hzero

/-- Helper for Definition 15-15.1-1: mono and epi in the finite-projective owner category remain
injective and surjective on forgotten `k[G]`-linear maps. -/
private theorem finiteProjective_underlying_injective_surjective_bridge
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) (hS : S.ShortExact) :
    Function.Injective S.f.hom.hom ∧ Function.Surjective S.g.hom.hom := by
  constructor
  · intro x y hxy
    let ψ : finiteProjective_regular_owner (k := k) (G := G) ⟶ S.X₁ :=
      ObjectProperty.homMk
        (FGModuleCat.ofHom ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight (x - y)))
    have hψ_zero_lin :
        S.f.hom.hom.hom.comp ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight (x - y)) = 0 := by
      -- The kernel element `x - y` produces a cyclic map killed by `f`.
      ext
      simp [hxy]
    have hψ_zero : ψ ≫ S.f = 0 := by
      -- Repackage the vanished composite back in the owner category.
      apply ObjectProperty.hom_ext
      apply FGModuleCat.hom_ext
      simpa [ψ, FGModuleCat.ofHom] using hψ_zero_lin
    letI : Mono S.f := hS.mono_f
    have hψ_eq_zero : ψ = 0 := by
      exact (cancel_mono S.f).1 (by simpa using hψ_zero)
    have hEval := ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.hom) hψ_eq_zero) 1
    have hEval' :
        (ConcreteCategory.hom
            (FGModuleCat.ofHom ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight (x - y))).hom) 1 =
          0 := by
      -- Read the equality `ψ = 0` at the generator `1`.
      simpa [ψ] using hEval
    have hEval'' :
        ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight (x - y)) 1 = 0 := by
      have hψ_eval :
          (ConcreteCategory.hom
              (FGModuleCat.ofHom
                ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight (x - y))).hom) 1 =
            ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight (x - y)) 1 := rfl
      exact hψ_eval.symm.trans hEval'
    have hdiff : x - y = 0 := by
      simpa [regular_module_generated_map_apply_one (k := k) (G := G) (x := x - y)] using hEval''
    exact sub_eq_zero.mp hdiff
  · letI : Epi S.g := hS.epi_g
    -- The surjective half is exactly the generic owner-to-underlying epi bridge.
    simpa using finiteProjective_underlying_surjective_of_epi (k := k) (G := G) S.g

/-- Helper for Definition 15-15.1-1: a short exact sequence of finite projective `k[G]`-modules
is already short exact after forgetting to the ambient `ModuleCat k[G]`. -/
private theorem finiteProjective_shortExact_underlying_moduleCat
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) (hS : S.ShortExact) :
    (ShortComplex.mk S.f.hom.hom S.g.hom.hom
      (finiteProjective_underlying_moduleCat_zero (k := k) (G := G) S)).ShortExact := by
  obtain ⟨hf, hg⟩ :=
    finiteProjective_underlying_injective_surjective_bridge (k := k) (G := G) S hS
  -- This packages the source-faithful regular-module exactness argument into ambient short
  -- exactness in `ModuleCat k[G]`.
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact finiteProjective_underlying_function_exact (k := k) (G := G) S hS
  · rw [ModuleCat.mono_iff_injective]
    exact hf
  · rw [ModuleCat.epi_iff_surjective]
    exact hg

/-- Helper for Definition 15-15.1-1: forgetting projectivity should preserve short exactness for
the transported `FDRep` sequence. -/
private theorem projective_toFiniteRep_shortExact
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) (hS : S.ShortExact) :
    (projective_toFiniteRep_shortComplex (k := k) (G := G) S).ShortExact := by
  -- Route correction: instead of asking the projective inclusion functor to preserve homology, we
  -- first rebuild short exactness in `ModuleCat k[G]`, then map that ambient short exact sequence
  -- to `Rep k G`, and finally reflect it back through the faithful forgetful functor from `FDRep`.
  let Smod : ShortComplex (ModuleCat k[G]) :=
    ShortComplex.mk S.f.hom.hom S.g.hom.hom
      (finiteProjective_underlying_moduleCat_zero (k := k) (G := G) S)
  have hMod : Smod.ShortExact :=
    finiteProjective_shortExact_underlying_moduleCat (k := k) (G := G) S hS
  have hRep' : (S.map (finiteProjective_toRep (k := k) (G := G))).ShortExact := by
    -- The ambient `k[G]`-module short exact sequence maps to the corresponding `Rep k G`
    -- sequence via the standard equivalence `ModuleCat k[G] ⥤ Rep k G`.
    simpa [Smod, finiteProjective_toRep, finiteProjective_toModuleCat,
      finiteProjective_toFGModuleCat] using
      hMod.map_of_exact (Rep.ofModuleMonoidAlgebra : ModuleCat k[G] ⥤ Rep k G)
  have hRep :
      ((projective_toFiniteRep_shortComplex (k := k) (G := G) S).map
        (forget₂ (FDRep k G) (Rep k G))).ShortExact := by
    -- The `Rep`-image of the `FDRep` short complex is definitionally the mapped ambient
    -- representation sequence.
    simpa [projective_toFiniteRep_shortComplex_map_forget (k := k) (G := G) S] using hRep'
  -- Reflect short exactness from `Rep k G` back to `FDRep k G`.
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact
      ((projective_toFiniteRep_shortComplex (k := k) (G := G) S).exact_map_iff_of_faithful
        (forget₂ (FDRep k G) (Rep k G))).1 hRep.exact
  · exact (forget₂ (FDRep k G) (Rep k G)).mono_of_mono_map hRep.mono_f
  · exact (forget₂ (FDRep k G) (Rep k G)).epi_of_epi_map hRep.epi_g

/-- Helper for Definition 15-15.1-1: after forgetting projectivity, a short exact sequence of
finite projective `k[G]`-modules yields the usual Grothendieck relation in `R_k(G)`. -/
private theorem projective_toFiniteRep_class_middle_eq_left_add_right
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) (hS : S.ShortExact) :
    [S.X₂.toFiniteRep]₀ = [S.X₁.toFiniteRep]₀ + [S.X₃.toFiniteRep]₀ := by
  -- Proposition `14-14.1-1` applies once the transported `FDRep` short complex is known to be
  -- short exact.
  simpa [projective_toFiniteRep_shortComplex] using
    finiteRepGrothendieckClass_middle_eq_left_add_right (L := k) (G := G)
      (projective_toFiniteRep_shortComplex (k := k) (G := G) S)
      (projective_toFiniteRep_shortExact (k := k) (G := G) S hS)

/-- Helper for Definition 15-15.1-1: the Cartan lift evaluates a defining short-exact-sequence
generator as the expected formal difference in `R₀[k](G)`. -/
private theorem cartanLift_shortExact_generator_eq
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) (_hS : S.ShortExact) :
    cartanLift k G
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) =
        [S.X₂.toFiniteRep]₀ - [S.X₁.toFiniteRep]₀ - [S.X₃.toFiniteRep]₀ := by
  -- The free lift is defined generatorwise, so evaluating it on a short-exact-sequence
  -- generator is immediate.
  rfl

-- Proof sketch: each generator of `finiteProjectiveGroupAlgebraGrothendieckRelations k G` comes
-- from a short exact sequence of finite projective `k[G]`-modules; forgetting projectivity gives a
-- short exact sequence of finite-dimensional representations, and Proposition `14-14.1-1` kills
-- the corresponding relation in `R_k(G)`.
private theorem finiteProjectiveGroupAlgebraGrothendieckRelations_le_cartanLift_ker :
    finiteProjectiveGroupAlgebraGrothendieckRelations k G ≤ (cartanLift k G).ker := by
  -- It suffices to check the defining short-exact-sequence generators of the projective
  -- Grothendieck relations.
  rw [finiteProjectiveGroupAlgebraGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  -- Evaluate the free lift on the generator and rewrite it using the transported Grothendieck
  -- relation in `R₀[k](G)`.
  change cartanLift k G
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  rw [cartanLift_shortExact_generator_eq (k := k) (G := G) S hS]
  rw [sub_eq_iff_eq_add]
  rw [sub_eq_iff_eq_add]
  rw [add_comm]
  exact projective_toFiniteRep_class_middle_eq_left_add_right (k := k) (G := G) S hS

/-- Definition 15-15.1-1: the Cartan homomorphism `c : P_k(G) → R_k(G)` sends the class of a
finite projective `k[G]`-module to the same class in the representation Grothendieck group. -/
def cartanHom :
    P₀[k](G) →+ R₀[k](G) :=
  QuotientAddGroup.lift
    (finiteProjectiveGroupAlgebraGrothendieckRelations k G)
    (cartanLift k G)
    (finiteProjectiveGroupAlgebraGrothendieckRelations_le_cartanLift_ker k G)

/-- The cokernel of the Cartan homomorphism `c : P_k(G) → R_k(G)`, realized as the quotient of
`R_k(G)` by the range of `c`. -/
abbrev cartanCokernel :=
  R₀[k](G) ⧸ (cartanHom k G).range

-- Proof sketch: the quotient lift defining `cartanHom k G` sends the generator `[P]` of
-- `P_k(G)` to the same generator in `R_k(G)`, so evaluating on the class of a projective module
-- is immediate from the definition of `QuotientAddGroup.lift`.
/-- The Cartan homomorphism sends the class of a finite projective `k[G]`-module to its class in
`R_k(G)`. -/
@[simp] theorem cartanHom_projectiveClass_eq (P : FiniteProjectiveGroupAlgebraModule k G) :
    cartanHom k G [P]ₚ₀ = [P.toFiniteRep]₀ := rfl

/-- The Cartan matrix of `G` with respect to chosen `ℤ`-bases of `P_k(G)` and `R_k(G)` is the
matrix of the Cartan homomorphism. In LinearRepresentations_Serre_1977's setting, one takes the bases coming from projective
envelopes of simples and from simple modules. This is a thin abbreviation for the canonical
matrix of the owner map `cartanHom`. -/
abbrev cartanMatrix {ι : Type w} {κ : Type x}
    [Fintype ι] [Fintype κ]
    (bP : Module.Basis ι ℤ (P₀[k](G)))
    (bR : Module.Basis κ ℤ (R₀[k](G))) :
    Matrix κ ι ℤ :=
  let _ := Classical.decEq ι
  let _ := Classical.decEq κ
  LinearMap.toMatrix bP bR (cartanHom k G).toIntLinearMap

end CartanHom

end Representation
