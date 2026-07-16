import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_4_4
import LinearRepresentations_Serre_1977.Serre.Chap14.Lemma_14_14_4_2
import LinearRepresentations_Serre_1977.Serre.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.RealizableOver
import Mathlib.RingTheory.TensorProduct.Finite

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra TensorProduct
open scoped Representation

universe u w

namespace Representation

section TensorProductHom

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {K : Type u} [Field K] [Algebra A K]
variable {G : Type u} [Group G] [Finite G]

local notation:max "P₀[" A "](" G ")" =>
  finiteProjectiveGroupAlgebraGrothendieckGroup A G

/-
Domain-style sampling:
* Primary domain: scalar extension of finite projective `A[G]`-modules and the induced maps on
  Serre's Grothendieck groups.
* Core/canonical owner abstraction already present upstream: the Chapter `14` owner
  `FiniteProjectiveGroupAlgebraModule A G`, together with its canonical bridges `toRep`,
  `finiteProjectiveGroupAlgebraGrothendieckGroup`, and `finiteRepGrothendieckGroup`.
* Related owner declarations inspected in this domain:
  `FiniteProjectiveGroupAlgebraModule.toRep`,
  `FiniteProjectiveGroupAlgebraModule.toFiniteRep`,
  `projectiveGrothendieckReductionEquiv`, and
  `FDRep.scalarExtension`.
* Primitive data here: the owner-level scalar extension
  `FiniteProjectiveGroupAlgebraModule.scalarExtension`.
* Derived API here: the induced additive lift on the free abelian group and the quotient maps on
  `P₀[A](G)` and `P₀[k](G)`.
This item is therefore a bridge/view construction built on the Chapter `14` finite-projective
owner, not a second owner for Grothendieck classes.
-/

namespace FiniteProjectiveGroupAlgebraModule

/-- Extending scalars from `A` to `K` turns a finite projective `A[G]`-module into a
finite-dimensional `K`-representation of `G`. -/
abbrev scalarExtension (K : Type u) [Field K] [Algebra A K]
    (P : FiniteProjectiveGroupAlgebraModule A G) : FDRep K G :=
  let ρ : Representation A G P.V := Representation.ofModule' P.V
  let _ : Module.Finite A P.V := by infer_instance
  let _ : Module.Finite K (K ⊗[A] P.V) := by infer_instance
  FDRep.of (Representation.scalarExtension ρ)

end FiniteProjectiveGroupAlgebraModule

variable (K)

/-- The additive map on the free abelian group of finite projective `A[G]`-modules induced by
extension of scalars from `A` to `K`. -/
private abbrev projectiveGrothendieckBaseChangeLift :
    FreeAbelianGroup (FiniteProjectiveGroupAlgebraModule A G) →+ R₀[K](G) :=
  FreeAbelianGroup.lift fun P ↦ [P.scalarExtension K]₀

/-- Helper for Definition 15-15.3-1: the base-change lift sends a defining short-exact-sequence
generator to the expected formal difference of scalar-extension classes in `R₀[K](G)`. -/
private theorem projectiveGrothendieckBaseChangeLift_shortExact_generator_eq
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule A G))
    (_hSplit : Nonempty (S.X₂.V ≃ₗ[A[G]] S.X₁.V × S.X₃.V)) :
    projectiveGrothendieckBaseChangeLift K
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) =
        [S.X₂.scalarExtension K]₀ - [S.X₁.scalarExtension K]₀ - [S.X₃.scalarExtension K]₀ := by
  -- This is just the defining evaluation of the free lift on a short-exact-sequence generator.
  rfl

omit [Finite G] in
/-- Helper for Definition 15-15.3-1: the defining short-exact-sequence generator of `P_A(G)`
already yields the corresponding relation inside the projective Grothendieck group. -/
private theorem projectiveGrothendieckClass_middle_eq_left_add_right
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule A G))
    (hSplit : Nonempty (S.X₂.V ≃ₗ[A[G]] S.X₁.V × S.X₃.V)) :
    [S.X₂]ₚ₀ = [S.X₁]ₚ₀ + [S.X₃]ₚ₀ :=
  finiteProjectiveGroupAlgebraGrothendieckClass_middle_eq_left_add_right S hSplit

omit [Finite G] in
/-- Helper for Definition 15-15.3-1: every short-exact-sequence relation in `P_A(G)` becomes the
corresponding Grothendieck relation in `R_K(G)` after scalar extension. -/
-- Proof sketch: identify the scalar-extended `K[G]`-action with `Representation.scalarExtension`
-- and evaluate the action of `MonoidAlgebra.of`.
private theorem monoidAlgebra_of_smul_tmul
    {P : Type w} [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    (g : G) (a : K) (x : P) :
    MonoidAlgebra.of K G g • (a ⊗ₜ[A] x : K ⊗[A] P) =
      a ⊗ₜ[A] (MonoidAlgebra.of A G g • x) := by
  -- Rewrite the scalar-extended `K[G]`-action through `Representation.single_smul`.
  let ρ : Representation A G P := Representation.ofModule' P
  let ρK : Representation K G (K ⊗[A] P) := Representation.scalarExtension ρ
  have hsingle :=
    Representation.single_smul (ρ := ρK) (t := (1 : K)) (g := g)
      (v := TensorProduct.mk A K P a x)
  simpa [ρ, ρK, Representation.scalarExtension, Representation.ofModule',
    MonoidAlgebra.of_apply] using hsingle

omit [Finite G] in
/-- Helper for Definition 15-15.3-1: every pure tensor in the scalar-extended product is a
scalar multiple of one whose left tensor factor is `1`. -/
private theorem scalarExtension_prod_tmul_eq_smul_unit_tmul
    {P Q : Type w} [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [AddCommGroup Q] [Module A Q] [Module A[G] Q] [IsScalarTower A A[G] Q]
    (c : K) (p : P) (q : Q) :
    (c ⊗ₜ[A] (p, q) : K ⊗[A] (P × Q)) = c • ((1 : K) ⊗ₜ[A] (p, q)) := by
  -- Normalize a pure tensor so the equivariance check can focus on the case `1 ⊗ (p, q)`.
  calc
    (c ⊗ₜ[A] (p, q) : K ⊗[A] (P × Q))
        = ((c • (1 : K)) ⊗ₜ[A] (p, q) : K ⊗[A] (P × Q)) := by simp
    _ = c • ((1 : K) ⊗ₜ[A] (p, q)) := by
          rw [TensorProduct.smul_tmul']

omit [Finite G] in
/-- Helper for Definition 15-15.3-1: `TensorProduct.prodRight` sends a pure tensor in the
scalar-extended product model to the corresponding pair of pure tensors. -/
private theorem scalarExtension_prodRight_tmul_eq_smul
    {P Q : Type w} [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [AddCommGroup Q] [Module A Q] [Module A[G] Q] [IsScalarTower A A[G] Q]
    (c : K) (p : P) (q : Q) :
    TensorProduct.prodRight A K K P Q (c ⊗ₜ[A] (p, q)) =
      c • (((1 : K) ⊗ₜ[A] p), ((1 : K) ⊗ₜ[A] q)) := by
  -- First normalize the source tensor, then evaluate `TensorProduct.prodRight` on `1 ⊗ (p, q)`.
  calc
    TensorProduct.prodRight A K K P Q (c ⊗ₜ[A] (p, q))
        = TensorProduct.prodRight A K K P Q (((c • (1 : K)) ⊗ₜ[A] (p, q) : K ⊗[A] (P × Q))) := by
            simp
    _ = TensorProduct.prodRight A K K P Q (c • ((1 : K) ⊗ₜ[A] (p, q) : K ⊗[A] (P × Q))) := by
          rw [TensorProduct.smul_tmul']
    _ = c • TensorProduct.prodRight A K K P Q ((1 : K) ⊗ₜ[A] (p, q) : K ⊗[A] (P × Q)) := by
          rw [map_smul]
    _ = c • (((1 : K) ⊗ₜ[A] p), ((1 : K) ⊗ₜ[A] q)) := by
          simp [TensorProduct.prodRight_tmul]

omit [Finite G] in
/-- Helper for Definition 15-15.3-1: `TensorProduct.prodRight` commutes with the action of
`MonoidAlgebra.of K G g` on scalar-extended pure tensors. -/
-- Proof sketch: reduce to pure tensors of the form `1 ⊗ (p, q)`, use
-- `monoidAlgebra_of_smul_tmul` on each factor, and transport through `TensorProduct.prodRight`.
private theorem scalarExtension_prodRight_map_monoidAlgebra_of
    {P Q : Type w} [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [AddCommGroup Q] [Module A Q] [Module A[G] Q] [IsScalarTower A A[G] Q]
    (g : G) (c : K) (p : P) (q : Q) :
    TensorProduct.prodRight A K K P Q
        (MonoidAlgebra.of K G g • (c ⊗ₜ[A] (p, q) : K ⊗[A] (P × Q))) =
      MonoidAlgebra.of K G g •
        TensorProduct.prodRight A K K P Q (c ⊗ₜ[A] (p, q) : K ⊗[A] (P × Q)) := by
  have hp :
      MonoidAlgebra.of K G g • (((1 : K) ⊗ₜ[A] p) : K ⊗[A] P) =
        (((1 : K) ⊗ₜ[A] (MonoidAlgebra.of A G g • p)) : K ⊗[A] P) := by
    simpa using monoidAlgebra_of_smul_tmul (A := A) (K := K) (G := G) (P := P) g 1 p
  have hq :
      MonoidAlgebra.of K G g • (((1 : K) ⊗ₜ[A] q) : K ⊗[A] Q) =
        (((1 : K) ⊗ₜ[A] (MonoidAlgebra.of A G g • q)) : K ⊗[A] Q) := by
    simpa using monoidAlgebra_of_smul_tmul (A := A) (K := K) (G := G) (P := Q) g 1 q
  have hpair :
      MonoidAlgebra.of K G g •
          ((((1 : K) ⊗ₜ[A] p) : K ⊗[A] P), (((1 : K) ⊗ₜ[A] q) : K ⊗[A] Q)) =
        ((((1 : K) ⊗ₜ[A] (MonoidAlgebra.of A G g • p)) : K ⊗[A] P),
          (((1 : K) ⊗ₜ[A] (MonoidAlgebra.of A G g • q)) : K ⊗[A] Q)) := by
    ext <;> assumption
  -- Route correction: prove equivariance first on normalized pure tensors `c • (1 ⊗ (p, q))`,
  -- then transport the normalization through `TensorProduct.prodRight`.
  calc
    TensorProduct.prodRight A K K P Q
        (MonoidAlgebra.of K G g • (c ⊗ₜ[A] (p, q) : K ⊗[A] (P × Q))) =
      TensorProduct.prodRight A K K P Q
        (c • (MonoidAlgebra.of K G g • ((1 : K) ⊗ₜ[A] (p, q) : K ⊗[A] (P × Q)))) := by
          rw [scalarExtension_prod_tmul_eq_smul_unit_tmul
            (A := A) (K := K) (G := G) (P := P) (Q := Q) c p q]
          rw [smul_comm]
    _ = c • TensorProduct.prodRight A K K P Q
        (MonoidAlgebra.of K G g • ((1 : K) ⊗ₜ[A] (p, q) : K ⊗[A] (P × Q))) := by
          rw [map_smul]
    _ = c • TensorProduct.prodRight A K K P Q
        (((1 : K) ⊗ₜ[A] (MonoidAlgebra.of A G g • (p, q)) : K ⊗[A] (P × Q))) := by
          refine congrArg (fun t ↦ c • TensorProduct.prodRight A K K P Q t) ?_
          simpa using
            monoidAlgebra_of_smul_tmul (A := A) (K := K) (G := G) (P := P × Q) g 1 (p, q)
    _ = c •
        ((((1 : K) ⊗ₜ[A] (MonoidAlgebra.of A G g • p)) : K ⊗[A] P),
          (((1 : K) ⊗ₜ[A] (MonoidAlgebra.of A G g • q)) : K ⊗[A] Q)) := by
          simp [TensorProduct.prodRight_tmul]
    _ = c •
        (MonoidAlgebra.of K G g •
          ((((1 : K) ⊗ₜ[A] p) : K ⊗[A] P), (((1 : K) ⊗ₜ[A] q) : K ⊗[A] Q))) := by
          rw [hpair]
    _ = MonoidAlgebra.of K G g •
        (c • ((((1 : K) ⊗ₜ[A] p) : K ⊗[A] P), (((1 : K) ⊗ₜ[A] q) : K ⊗[A] Q))) := by
          rw [smul_comm]
    _ = MonoidAlgebra.of K G g •
        TensorProduct.prodRight A K K P Q (c ⊗ₜ[A] (p, q) : K ⊗[A] (P × Q)) := by
          rw [scalarExtension_prodRight_tmul_eq_smul
            (A := A) (K := K) (G := G) (P := P) (Q := Q) c p q]

omit [Finite G] in
/-- Helper for Definition 15-15.3-1: scalar extension commutes with binary products of
`A[G]`-modules. -/
-- Proof sketch: upgrade `TensorProduct.prodRight` to a `K[G]`-linear equivalence by checking
-- equivariance on `MonoidAlgebra` generators and then extending by induction.
private theorem scalarExtension_prod_nonempty_linearEquiv
    {P Q : Type w} [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [AddCommGroup Q] [Module A Q] [Module A[G] Q] [IsScalarTower A A[G] Q] :
    Nonempty (((K ⊗[A] (P × Q)) ≃ₗ[K[G]] (K ⊗[A] P) × (K ⊗[A] Q))) := by
  let e₀ : (K ⊗[A] (P × Q)) ≃ₗ[K] (K ⊗[A] P) × (K ⊗[A] Q) :=
    TensorProduct.prodRight A K K P Q
  refine ⟨
    { toFun := e₀
      invFun := e₀.symm
      left_inv := e₀.left_inv
      right_inv := e₀.right_inv
      map_add' := e₀.map_add
      map_smul' := ?_ }⟩
  intro a x
  -- Extend the `MonoidAlgebra.of` computation from pure tensors to all scalars in `K[G]`.
  refine MonoidAlgebra.induction_on
    (p := fun b : K[G] => e₀ (b • x) = b • e₀ x) a ?_ ?_ ?_
  · intro g
    induction x using TensorProduct.induction_on with
    | zero =>
        simp [e₀]
    | tmul c y =>
        rcases y with ⟨p, q⟩
        simpa [e₀] using
          scalarExtension_prodRight_map_monoidAlgebra_of
            (A := A) (K := K) (G := G) (P := P) (Q := Q) g c p q
    | add y z hy hz =>
        simpa [MonoidAlgebra.of_apply, map_add, smul_add, e₀] using
          calc
            e₀ (MonoidAlgebra.of K G g • (y + z))
                = e₀ (MonoidAlgebra.of K G g • y) + e₀ (MonoidAlgebra.of K G g • z) := by
                    simp [map_add, smul_add, e₀]
            _ = MonoidAlgebra.of K G g • e₀ y + MonoidAlgebra.of K G g • e₀ z := by
                  rw [hy, hz]
            _ = MonoidAlgebra.of K G g • e₀ (y + z) := by
                  simp [smul_add, e₀]
  · intro b c hb hc
    simp [add_smul, map_add, hb, hc]
  · intro c b hb
    calc
      e₀ ((c • b) • x) = e₀ (c • (b • x)) := by rw [smul_assoc]
      _ = c • e₀ (b • x) := by
            exact e₀.toLinearMap.map_smul c (b • x)
      _ = c • (b • e₀ x) := by rw [hb]
      _ = (c • b) • e₀ x := by rw [smul_assoc]

/-- Helper for Definition 15-15.3-1: a split exact sequence of modules identifies the middle term
with the product of the two outer terms. -/
private noncomputable def linearEquivProdOfRightSplitExact_15_3
    {R : Type u} [Ring R]
    {X₁ : Type w} [AddCommGroup X₁] [Module R X₁]
    {X₂ : Type w} [AddCommGroup X₂] [Module R X₂]
    {X₃ : Type w} [AddCommGroup X₃] [Module R X₃]
    (f : X₁ →ₗ[R] X₂) (g : X₂ →ₗ[R] X₃)
    (hf : Function.Injective f) (hexact : Function.Exact f g)
    (s : X₃ →ₗ[R] X₂) (hs : g.comp s = LinearMap.id) :
    (X₁ × X₃) ≃ₗ[R] X₂ := by
  -- Convert the split exact sequence to the canonical biproduct splitting in `ModuleCat`.
  let hexact' : LinearMap.range f = LinearMap.ker g := by
    simpa [LinearMap.exact_iff, eq_comm] using hexact
  exact
    ((ShortComplex.Splitting.ofExactOfSection _
      (ShortComplex.Exact.moduleCat_of_range_eq_ker (ModuleCat.ofHom f)
        (ModuleCat.ofHom g) hexact')
      (ModuleCat.ofHom s) (ModuleCat.hom_ext hs)
      (by simpa only [ModuleCat.mono_iff_injective] using hf)).isoBinaryBiproduct ≪≫
      ModuleCat.biprodIsoProd _ _).symm.toLinearEquiv

/-- Helper for Definition 15-15.3-1: a short exact sequence of modules with projective right term
splits, so the middle term is linearly equivalent to the product of the two outer terms. -/
private theorem moduleCat_shortExact_middle_nonempty_linearEquiv_prod_15_3
    {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat R)) [Module.Projective R S.X₃] (hS : S.ShortExact) :
    Nonempty ((↑S.X₁ × ↑S.X₃) ≃ₗ[R] ↑S.X₂) := by
  have hsurj : Function.Surjective S.g.hom := hS.moduleCat_surjective_g
  have hinj : Function.Injective S.f.hom := hS.moduleCat_injective_f
  have hexact : Function.Exact S.f.hom S.g.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact
  -- Choose a section of `g` and apply the standard split-exact decomposition lemma.
  obtain ⟨s, hs⟩ :=
    Module.projective_lifting_property S.g.hom (LinearMap.id : S.X₃ →ₗ[R] S.X₃) hsurj
  refine ⟨?_⟩
  simpa using linearEquivProdOfRightSplitExact_15_3 S.f.hom S.g.hom hinj hexact s hs

omit [Finite G] in
/-- Helper for Definition 15-15.3-1: forgetting a short complex of finite projective
`A[G]`-modules to `ModuleCat A[G]` preserves the relation `g ∘ f = 0`. -/
private theorem finiteProjective_underlying_moduleCat_zero_15_3
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule A G)) :
    S.f.hom.hom ≫ S.g.hom.hom = 0 := by
  let F : FiniteProjectiveGroupAlgebraModule A G ⥤ ModuleCat A[G] :=
    (ObjectProperty.ι (fun M : FGModuleCat A[G] ↦ Module.Projective A[G] M)) ⋙
      (ModuleCat.isFG A[G]).ι
  -- The mapped short complex in `ModuleCat A[G]` has the same two structure maps.
  simpa using (S.map F).zero

omit [Finite G] in
/-- Helper for Definition 15-15.3-1: an `A[G]`-linear equivalence induces a `K[G]`-linear
equivalence after scalar extension along `A → K`. -/
-- Proof sketch: base change the underlying `A[G]`-linear equivalence and verify that the resulting
-- `K`-linear map intertwines the scalar-extended `K[G]`-actions.
private theorem scalarExtension_nonempty_linearEquiv_of_nonempty_linearEquiv
    {P Q : Type w} [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [AddCommGroup Q] [Module A Q] [Module A[G] Q] [IsScalarTower A A[G] Q]
    (hPQ : Nonempty (P ≃ₗ[A[G]] Q)) :
    Nonempty ((K ⊗[A] P) ≃ₗ[K[G]] (K ⊗[A] Q)) := by
  rcases hPQ with ⟨e⟩
  let e₀ : (K ⊗[A] P) ≃ₗ[K] (K ⊗[A] Q) :=
    LinearEquiv.baseChange A K P Q (LinearEquiv.restrictScalars A e)
  refine ⟨
    { toFun := e₀
      invFun := e₀.symm
      left_inv := e₀.left_inv
      right_inv := e₀.right_inv
      map_add' := e₀.map_add
      map_smul' := ?_ }⟩
  intro a x
  -- Extend the `MonoidAlgebra.of` computation from pure tensors to all scalars in `K[G]`.
  refine MonoidAlgebra.induction_on
    (p := fun b : K[G] => e₀ (b • x) = b • e₀ x) a ?_ ?_ ?_
  · intro g
    induction x using TensorProduct.induction_on with
    | zero =>
        simp [e₀]
    | tmul c p =>
        have hq :
            MonoidAlgebra.of K G g • (c ⊗ₜ[A] e p : K ⊗[A] Q) =
              (c ⊗ₜ[A] (MonoidAlgebra.of A G g • e p) : K ⊗[A] Q) := by
          simpa using
            monoidAlgebra_of_smul_tmul (A := A) (K := K) (G := G) (P := Q) g c (e p)
        calc
          e₀ (MonoidAlgebra.of K G g • (c ⊗ₜ[A] p : K ⊗[A] P))
              = e₀ (c ⊗ₜ[A] (MonoidAlgebra.of A G g • p) : K ⊗[A] P) := by
                  rw [monoidAlgebra_of_smul_tmul (A := A) (K := K) (G := G) (P := P)]
          _ = (c ⊗ₜ[A] e (MonoidAlgebra.of A G g • p) : K ⊗[A] Q) := by
                simp [e₀, LinearEquiv.baseChange_tmul]
          _ = (c ⊗ₜ[A] (MonoidAlgebra.of A G g • e p) : K ⊗[A] Q) := by
                rw [e.map_smul]
          _ = MonoidAlgebra.of K G g • e₀ (c ⊗ₜ[A] p : K ⊗[A] P) := by
                rw [← hq]
                simp [e₀, LinearEquiv.baseChange_tmul]
    | add y z hy hz =>
        simpa [MonoidAlgebra.of_apply, map_add, smul_add, e₀] using
          calc
            e₀ (MonoidAlgebra.of K G g • (y + z))
                = e₀ (MonoidAlgebra.of K G g • y) + e₀ (MonoidAlgebra.of K G g • z) := by
                    simp [map_add, smul_add, e₀]
            _ = MonoidAlgebra.of K G g • e₀ y + MonoidAlgebra.of K G g • e₀ z := by
                  rw [hy, hz]
            _ = MonoidAlgebra.of K G g • e₀ (y + z) := by
                  simp [smul_add, e₀]
  · intro b c hb hc
    simp [add_smul, map_add, hb, hc]
  · intro c b hb
    calc
      e₀ ((c • b) • x) = e₀ (c • (b • x)) := by rw [smul_assoc]
      _ = c • e₀ (b • x) := by
            exact e₀.toLinearMap.map_smul c (b • x)
      _ = c • (b • e₀ x) := by rw [hb]
      _ = (c • b) • e₀ x := by rw [smul_assoc]

/-- Helper for Definition 15-15.3-1: after splitting a short exact sequence of projective
`A[G]`-modules, scalar extension identifies the middle term with the product of the scalar-extended
outer terms. -/
-- Proof sketch: forget the short exact sequence to `ModuleCat A[G]`, split it because the right
-- term stays projective, then base change the resulting `A[G]`-linear equivalence.
private theorem projective_scalarExtension_middle_nonempty_linearEquiv_prod
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule A G))
    (hSplit : Nonempty (S.X₂.V ≃ₗ[A[G]] S.X₁.V × S.X₃.V)) :
    Nonempty ((((K ⊗[A] S.X₁.V) × (K ⊗[A] S.X₃.V)) ≃ₗ[K[G]] (K ⊗[A] S.X₂.V))) := by
  -- The relation generator carries the upstairs splitting directly; scalar-extend it.  (No appeal
  -- to the false "categorical SES ⇒ underlying module SES" bridge over the local ring `A`.)
  obtain ⟨e⟩ := hSplit
  obtain ⟨ebase⟩ :=
    scalarExtension_nonempty_linearEquiv_of_nonempty_linearEquiv
      (A := A) (K := K) (G := G) (P := S.X₁.V × S.X₃.V) (Q := S.X₂.V) ⟨e.symm⟩
  obtain ⟨eprod⟩ :=
    scalarExtension_prod_nonempty_linearEquiv
      (A := A) (K := K) (G := G) (P := S.X₁.V) (Q := S.X₃.V)
  -- Compose the base-changed splitting with the product/base-change comparison.
  exact ⟨eprod.symm.trans ebase⟩

/-- Helper for Definition 15-15.3-1: the canonical finite-dimensional representation on the
product of two scalar-extended outer terms. -/
private abbrev scalarExtension_prod_fdRep
    (P Q : FiniteProjectiveGroupAlgebraModule A G) : FDRep K G :=
  FDRep.of (Representation.prod (P.scalarExtension K).ρ (Q.scalarExtension K).ρ)

/-- Helper for Definition 15-15.3-1: the `K[G]`-module underlying a finite-dimensional
representation. -/
private noncomputable abbrev fdRepAsModule (τ : FDRep K G) : ModuleCat K[G] :=
  Rep.toModuleMonoidAlgebra.obj ((forget₂ (FDRep K G) (Rep K G)).obj τ)

omit [Finite G] in
/-- Helper for Definition 15-15.3-1: for a module viewed through `Representation.ofModule'`,
the induced group-algebra action is the original `K[G]`-scalar multiplication. -/
private theorem ofModule'_asAlgebraHom_apply
    (M : Type w) [AddCommGroup M] [Module K M] [Module K[G] M] [IsScalarTower K K[G] M]
    (r : K[G]) (m : M) :
    ((Representation.ofModule' (k := K) (G := G) M).asAlgebraHom r) m = r • m := by
  -- Expand the group-algebra element linearly and check the claim on monomials.
  refine MonoidAlgebra.induction_on (p := fun r : K[G] =>
    ((Representation.ofModule' (k := K) (G := G) M).asAlgebraHom r) m = r • m) r ?_ ?_ ?_
  · intro g
    simp [Representation.ofModule', MonoidAlgebra.of]
  · intro a b ha hb
    simp [ha, hb, add_smul]
  · intro a b hb
    simp [hb]

omit [Finite G] in
/-- Helper for Definition 15-15.3-1: the owner module of `Representation.ofModule' M` is
canonically the original `K[G]`-module `M`. -/
private theorem nonempty_ofModule'_asModuleLinearEquiv
    (M : Type w) [AddCommGroup M] [Module K M] [Module K[G] M] [IsScalarTower K K[G] M] :
    Nonempty ((Representation.ofModule' (k := K) (G := G) M).asModule ≃ₗ[K[G]] M) := by
  let toFun : (Representation.ofModule' (k := K) (G := G) M).asModule → M :=
    fun x ↦ (Representation.ofModule' (k := K) (G := G) M).asModuleEquiv x
  let invFun : M → (Representation.ofModule' (k := K) (G := G) M).asModule :=
    fun x ↦ (Representation.ofModule' (k := K) (G := G) M).asModuleEquiv.symm x
  have hleft : Function.LeftInverse invFun toFun := by
    intro x
    simp [toFun, invFun]
  have hright : Function.RightInverse invFun toFun := by
    intro x
    simp [toFun, invFun]
  have hadd : ∀ x y, toFun (x + y) = toFun x + toFun y := by
    intro x y
    rfl
  have hsmul : ∀ (r : K[G]) x, toFun (r • x) = r • toFun x := by
    intro r x
    -- Rewrite the transported action through `asModuleEquiv`, then identify it with the
    -- original `K[G]`-action on `M`.
    calc
      (Representation.ofModule' (k := K) (G := G) M).asModuleEquiv (r • x)
          = ((Representation.ofModule' (k := K) (G := G) M).asAlgebraHom r)
              ((Representation.ofModule' (k := K) (G := G) M).asModuleEquiv x) := by
                exact
                  (Representation.asModuleEquiv_map_smul
                    (ρ := Representation.ofModule' (k := K) (G := G) M) r x)
      _ = r • (Representation.ofModule' (k := K) (G := G) M).asModuleEquiv x := by
            simp [ofModule'_asAlgebraHom_apply]
  exact ⟨
    { toFun := toFun
      invFun := invFun
      left_inv := hleft
      right_inv := hright
      map_add' := hadd
      map_smul' := hsmul }⟩

omit [Finite G] in
/-- Helper for Definition 15-15.3-1: applying the identity ring homomorphism does not change the
`K[G]`-scalar action. -/
private theorem ringHom_id_smul_eq
    {M : Type w} [AddCommGroup M] [Module K[G] M]
    (r : K[G]) (x : M) :
    ((RingHom.id K[G]) r) • x = r • x := by
  simp

omit [Finite G] in
/-- Helper for Definition 15-15.3-1: the module underlying
`Rep.ofModuleMonoidAlgebra.obj (ModuleCat.of K[G] M)` is canonically linearly equivalent to `M`.
-/
private theorem nonempty_ofModuleMonoidAlgebra_asModuleLinearEquiv
    (M : Type w) [AddCommGroup M] [Module K M] [Module K[G] M] [IsScalarTower K K[G] M] :
    Nonempty ((Rep.ofModuleMonoidAlgebra.obj (ModuleCat.of K[G] M)).ρ.asModule ≃ₗ[K[G]] M) := by
  change Nonempty ((Representation.ofModule (ModuleCat.of K[G] M)).asModule ≃ₗ[K[G]] M)
  let Mmod : ModuleCat K[G] := ModuleCat.of K[G] M
  let toFun : (Representation.ofModule Mmod).asModule → M := fun x ↦
    (RestrictScalars.addEquiv K K[G] M) ((Representation.ofModule Mmod).asModuleEquiv x)
  let invFun : M → (Representation.ofModule Mmod).asModule := fun x ↦
    (Representation.ofModule Mmod).asModuleEquiv.symm ((RestrictScalars.addEquiv K K[G] M).symm x)
  refine ⟨
    { toFun := toFun
      invFun := invFun
      left_inv := by
        intro x
        simp [toFun, invFun, Mmod]
      right_inv := by
        intro x
        simp [toFun, invFun, Mmod]
      map_add' := by
        intro x y
        simp [toFun, Mmod]
      map_smul' := by
        intro r x
        exact Representation.smul_ofModule_asModule (M := Mmod) r x }⟩

/-- Helper for Definition 15-15.3-1: every finite-dimensional representation is canonically
isomorphic to the `FDRep.of` owner rebuilt from its bundled representation. -/
private noncomputable def fdRepIsoOfRho (τ : FDRep K G) : τ ≅ FDRep.of τ.ρ :=
  Action.mkIso (Iso.refl _) fun g ↦ by
    -- Rebundling does not change the carrier or the action.
    ext x
    rfl

omit [Finite G] in
/-- Helper for Definition 15-15.3-1: a `K[G]`-linear equivalence of the owner modules of two
finite-dimensional representations upgrades to an isomorphism in `FDRep K G`. -/
-- Proof sketch: convert the `K[G]`-linear equivalence into an intertwining map between the bundled
-- representations and then rebundle it as an `FDRep` isomorphism.
private theorem fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv
    {σ τ : FDRep K G} (hστ : Nonempty (fdRepAsModule K σ ≃ₗ[K[G]] fdRepAsModule K τ)) :
    Nonempty (σ ≅ τ) := by
  rcases hστ with ⟨e⟩
  let eRep : ((forget₂ (FDRep K G) (Rep K G)).obj σ) ≅
      ((forget₂ (FDRep K G) (Rep K G)).obj τ) :=
    Rep.unitIso ((forget₂ (FDRep K G) (Rep K G)).obj σ) ≪≫
      Rep.ofModuleMonoidAlgebra.mapIso e.toModuleIso ≪≫
      (Rep.unitIso ((forget₂ (FDRep K G) (Rep K G)).obj τ)).symm
  -- Transport the recovered `Rep` isomorphism back across the faithful `FDRep → Rep` functor.
  refine ⟨⟨(FDRep.forget₂HomLinearEquiv σ τ) eRep.hom,
    (FDRep.forget₂HomLinearEquiv τ σ) eRep.inv, ?_, ?_⟩⟩
  · apply (forget₂ (FDRep K G) (Rep K G)).map_injective
    change eRep.hom ≫ eRep.inv = 𝟙 _
    exact eRep.hom_inv_id
  · apply (forget₂ (FDRep K G) (Rep K G)).map_injective
    change eRep.inv ≫ eRep.hom = 𝟙 _
    exact eRep.inv_hom_id

/-- Helper for Definition 15-15.3-1: the class of the canonical product owner on the two
scalar-extended outer terms is the sum of the two scalar-extension classes. -/
-- Proof sketch: build the standard split short exact sequence
-- `0 → P_K → P_K × Q_K → Q_K → 0` in `FDRep K G` and apply the Chapter `14` Grothendieck
-- relation.
private theorem scalarExtension_prod_fdRep_class_eq_add
    (P Q : FiniteProjectiveGroupAlgebraModule A G) :
    [scalarExtension_prod_fdRep K P Q]₀ =
      [P.scalarExtension K]₀ + [Q.scalarExtension K]₀ := by
  let X₂ : FDRep K G := scalarExtension_prod_fdRep K P Q
  let fRep :
      ((forget₂ (FDRep K G) (Rep K G)).obj (P.scalarExtension K) ⟶
        (forget₂ (FDRep K G) (Rep K G)).obj X₂) :=
    Rep.ofHom ⟨LinearMap.inl K (P.scalarExtension K).V (Q.scalarExtension K).V, by
      -- The left inclusion intertwines the coordinatewise product action.
      intro g
      ext x
      change
        LinearMap.inl K (P.scalarExtension K).V (Q.scalarExtension K).V
            ((P.scalarExtension K).ρ g x) =
          (((P.scalarExtension K).ρ g).prodMap ((Q.scalarExtension K).ρ g))
            (LinearMap.inl K (P.scalarExtension K).V (Q.scalarExtension K).V x)
      simp [LinearMap.prodMap]⟩
  let gRep :
      ((forget₂ (FDRep K G) (Rep K G)).obj X₂ ⟶
        (forget₂ (FDRep K G) (Rep K G)).obj (Q.scalarExtension K)) :=
    Rep.ofHom ⟨LinearMap.snd K (P.scalarExtension K).V (Q.scalarExtension K).V, by
      -- The right projection is equivariant for the same coordinatewise action.
      intro g
      ext x
      rfl⟩
  let f : P.scalarExtension K ⟶ X₂ :=
    (FDRep.forget₂HomLinearEquiv (P.scalarExtension K) X₂) fRep
  let g : X₂ ⟶ Q.scalarExtension K :=
    (FDRep.forget₂HomLinearEquiv X₂ (Q.scalarExtension K)) gRep
  let S : ShortComplex (FDRep K G) := ShortComplex.mk f g (by
    -- The composite already vanishes on the underlying representation maps.
    apply (forget₂ (FDRep K G) (Rep K G)).map_injective
    ext x
    rfl)
  let SRep : ShortComplex (Rep K G) := ShortComplex.mk fRep gRep (by
    ext x
    rfl)
  have hRepMap : ((SRep.map (forget₂ (Rep K G) (ModuleCat K))).ShortExact) := by
    let SMod : ShortComplex (ModuleCat K) :=
      CategoryTheory.ShortComplex.moduleCatMk
        (LinearMap.inl K (P.scalarExtension K).V (Q.scalarExtension K).V)
        (LinearMap.snd K (P.scalarExtension K).V (Q.scalarExtension K).V)
        (by
          ext x
          rfl)
    have hSMod : SMod.ShortExact := by
      refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
      · exact CategoryTheory.ShortComplex.Exact.moduleCat_of_range_eq_ker
          (ModuleCat.ofHom
            (LinearMap.inl K (P.scalarExtension K).V (Q.scalarExtension K).V))
          (ModuleCat.ofHom
            (LinearMap.snd K (P.scalarExtension K).V (Q.scalarExtension K).V))
          (by
            ext x
            constructor
            · rintro ⟨y, rfl⟩
              simp
            · intro hx
              refine ⟨x.1, ?_⟩
              ext
              · rfl
              · simpa using hx.symm)
      · exact (ModuleCat.mono_iff_injective _).mpr fun x y h => by
          exact congrArg Prod.fst h
      · exact (ModuleCat.epi_iff_surjective _).mpr fun z => ⟨(0, z), rfl⟩
    -- Forgetting from `Rep` to `ModuleCat` preserves and reflects short exactness.
    simpa [SRep, SMod, fRep, gRep] using hSMod
  have hRepShort : SRep.ShortExact := by
    -- Reflect the concrete module short exactness back to `Rep`.
    exact
      (CategoryTheory.ShortExact.shortExact_map_iff
        (S := SRep) (F := forget₂ (Rep K G) (ModuleCat K))).1 hRepMap
  have hS : (S.map (forget₂ (FDRep K G) (Rep K G))).ShortExact := by
    -- The explicit `Rep` short complex is definitionally the image of the `FDRep` short complex.
    simpa [S, SRep, f, g, fRep, gRep, X₂] using hRepShort
  have hSFD : S.ShortExact := by
    -- Forgetting from `FDRep` to `Rep` preserves and reflects short exactness.
    exact
      (CategoryTheory.ShortExact.shortExact_map_iff
        (S := S) (F := forget₂ (FDRep K G) (Rep K G))).1 hS
  -- Proposition `14-14.1-1` turns this split short exact sequence into the desired class relation.
  simpa [S, X₂] using
    finiteRepGrothendieckClass_middle_eq_left_add_right (L := K) (G := G) S hSFD

/-- Helper for Definition 15-15.3-1: the owner module of a scalar-extended finite projective
object is the raw tensor-product `K[G]`-module. -/
private theorem fdRepAsModule_scalarExtension_linearEquiv
    (P : FiniteProjectiveGroupAlgebraModule A G) :
    Nonempty (fdRepAsModule K (P.scalarExtension K) ≃ₗ[K[G]]
      ModuleCat.of K[G] (K ⊗[A] P.V)) := by
  -- Unfold the scalar-extension owner once; the underlying `K[G]`-module is definitionally the
  -- ambient tensor-product module.
  refine ⟨?_⟩
  simpa [fdRepAsModule, FiniteProjectiveGroupAlgebraModule.scalarExtension] using
    (LinearEquiv.refl K[G] (fdRepAsModule K (P.scalarExtension K)))

/-- Helper for Definition 15-15.3-1: the scalar action on the owner module of the
scalar-extended product is the raw product scalar action. -/
private theorem scalarExtension_prod_owner_id_map_smul
    (P Q : FiniteProjectiveGroupAlgebraModule A G) (r : K[G])
    (x : fdRepAsModule K (scalarExtension_prod_fdRep K P Q)) :
    ((r • x : fdRepAsModule K (scalarExtension_prod_fdRep K P Q)) :
        ModuleCat.of K[G] ((K ⊗[A] P.V) × (K ⊗[A] Q.V))) =
      ((((RingHom.id K[G]) r) •
          (x : ModuleCat.of K[G] ((K ⊗[A] P.V) × (K ⊗[A] Q.V))) :
        ModuleCat.of K[G] ((K ⊗[A] P.V) × (K ⊗[A] Q.V)))) := by
  -- Unfold the owner bundle and the product representation so both actions are visibly the same.
  simp [fdRepAsModule, scalarExtension_prod_fdRep,
    FiniteProjectiveGroupAlgebraModule.scalarExtension, Representation.prod]

/-- Helper for Definition 15-15.3-1: the owner module of the scalar-extended product owner is the
raw product of the two scalar-extended tensor-product modules. -/
private theorem fdRepAsModule_scalarExtension_prod_linearEquiv
    (P Q : FiniteProjectiveGroupAlgebraModule A G) :
    Nonempty (fdRepAsModule K (scalarExtension_prod_fdRep K P Q) ≃ₗ[K[G]]
      ModuleCat.of K[G] ((K ⊗[A] P.V) × (K ⊗[A] Q.V))) := by
  let ρ : Representation K G ((K ⊗[A] P.V) × (K ⊗[A] Q.V)) :=
    Representation.prod (P.scalarExtension K).ρ (Q.scalarExtension K).ρ
  -- Source route: `scalarExtension_prod_fdRep` is the product of the two scalar-extended
  -- representations, whose owner module is the raw product module.  The remaining work is the
  -- standard product-action identification between `Representation.prod` and the product
  -- `K[G]`-module.
  -- Route correction: identify the source owner with `ρ.asModule`, then use the canonical
  -- `asModuleEquiv` rather than rebuilding the same identity carrier map by hand.
  change Nonempty (ρ.asModule ≃ₗ[K[G]]
    ModuleCat.of K[G] ((K ⊗[A] P.V) × (K ⊗[A] Q.V)))
  refine ⟨
    { toFun := fun x ↦ ρ.asModuleEquiv x
      invFun := fun x ↦ ρ.asModuleEquiv.symm x
      left_inv := by
        intro x
        exact ρ.asModuleEquiv.left_inv x
      right_inv := by
        intro x
        exact ρ.asModuleEquiv.right_inv x
      map_add' := by
        intro x y
        exact ρ.asModuleEquiv.map_add x y
      map_smul' := by
        intro r x
        -- `asModuleEquiv` converts the owner action into `ρ.asAlgebraHom`, which for the product
        -- representation is the raw coordinatewise `K[G]`-action.
        calc
          ρ.asModuleEquiv (r • x) = ρ.asAlgebraHom r (ρ.asModuleEquiv x) := by
            exact Representation.asModuleEquiv_map_smul (ρ := ρ) r x
          _ = r • ρ.asModuleEquiv x := by
            rcases ρ.asModuleEquiv x with ⟨x₁, x₂⟩
            refine MonoidAlgebra.induction_on
              (p := fun s : K[G] => ρ.asAlgebraHom s (x₁, x₂) = s • (x₁, x₂)) r ?_ ?_ ?_
            · intro g
              have hP :
                  ((Representation.ofModule' (k := A) (G := G) P.V).scalarExtension g) x₁ =
                    MonoidAlgebra.of K G g • x₁ := by
                exact
                  (Representation.asModuleEquiv_symm_map_rho
                    (ρ := (Representation.ofModule' (k := A) (G := G) P.V).scalarExtension) g x₁)
              have hQ :
                  ((Representation.ofModule' (k := A) (G := G) Q.V).scalarExtension g) x₂ =
                    MonoidAlgebra.of K G g • x₂ := by
                exact
                  (Representation.asModuleEquiv_symm_map_rho
                    (ρ := (Representation.ofModule' (k := A) (G := G) Q.V).scalarExtension) g x₂)
              ext
              · simpa [ρ, Representation.prod, Representation.asAlgebraHom_of] using hP
              · simpa [ρ, Representation.prod, Representation.asAlgebraHom_of] using hQ
            · intro a b ha hb
              simp [map_add, add_smul, ha, hb]
            · intro c a ha
              simp [ha, smul_smul] }⟩

/-- Helper for Definition 15-15.3-1: the scalar-extension splitting equivalence upgrades directly
to a `K[G]`-linear equivalence of the owner modules of the corresponding `FDRep` objects. -/
-- Proof sketch: transport the scalar-extension splitting through the canonical equivalences
-- between `FDRep` owners and their underlying `K[G]`-modules.
private theorem scalarExtension_middle_asModule_nonempty_linearEquiv_prod
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule A G))
    (hSplit : Nonempty (S.X₂.V ≃ₗ[A[G]] S.X₁.V × S.X₃.V)) :
    Nonempty (fdRepAsModule K (S.X₂.scalarExtension K) ≃ₗ[K[G]]
      fdRepAsModule K (scalarExtension_prod_fdRep K S.X₁ S.X₃)) := by
  obtain ⟨e⟩ :=
    projective_scalarExtension_middle_nonempty_linearEquiv_prod
      (A := A) (K := K) (G := G) S hSplit
  obtain ⟨eMiddle⟩ :=
    fdRepAsModule_scalarExtension_linearEquiv (A := A) (K := K) (G := G) S.X₂
  obtain ⟨eProd⟩ :=
    fdRepAsModule_scalarExtension_prod_linearEquiv (A := A) (K := K) (G := G) S.X₁ S.X₃
  -- Route correction: once the owner modules are identified explicitly, the desired comparison is
  -- just the raw split equivalence sandwiched between those two adapters.
  exact ⟨eMiddle.trans (e.symm.trans eProd.symm)⟩

/-- Helper for Definition 15-15.3-1: the scalar-extension splitting equivalence upgrades directly
to an isomorphism of the corresponding scalar-extended `FDRep` owners. -/
-- Proof sketch: combine the underlying `K[G]`-linear equivalence with
-- `fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv`.
private theorem scalarExtension_middle_nonempty_iso_prod
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule A G))
    (hSplit : Nonempty (S.X₂.V ≃ₗ[A[G]] S.X₁.V × S.X₃.V)) :
    Nonempty (S.X₂.scalarExtension K ≅ scalarExtension_prod_fdRep K S.X₁ S.X₃) := by
  obtain ⟨e⟩ :=
    scalarExtension_middle_asModule_nonempty_linearEquiv_prod (A := A) (K := K) (G := G) S hSplit
  exact fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv (K := K) (G := G) ⟨e⟩

/-- Helper for Definition 15-15.3-1: every short-exact-sequence relation in `P_A(G)` becomes the
corresponding Grothendieck relation in `R_K(G)` after scalar extension. -/
-- Proof sketch: replace the scalar-extended middle term by the product owner via the preceding
-- isomorphism and then apply additivity for the product class.
private theorem projective_scalarExtension_class_middle_eq_left_add_right
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule A G))
    (hSplit : Nonempty (S.X₂.V ≃ₗ[A[G]] S.X₁.V × S.X₃.V)) :
    [S.X₂.scalarExtension K]₀ = [S.X₁.scalarExtension K]₀ + [S.X₃.scalarExtension K]₀ := by
  obtain ⟨e⟩ := scalarExtension_middle_nonempty_iso_prod (A := A) (K := K) (G := G) S hSplit
  -- Replace the middle term by the split product owner, then use additivity for the product.
  calc
    [S.X₂.scalarExtension K]₀ = [scalarExtension_prod_fdRep K S.X₁ S.X₃]₀ := by
      exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := K) (G := G) ⟨e⟩
    _ = [S.X₁.scalarExtension K]₀ + [S.X₃.scalarExtension K]₀ :=
      scalarExtension_prod_fdRep_class_eq_add (A := A) (K := K) (G := G) S.X₁ S.X₃

/-- Helper for Definition 15-15.3-1: once the scalar-extension class relation is available, each
defining short-exact-sequence generator of `P_A(G)` lies in the kernel of the base-change lift. -/
-- Proof sketch: evaluate the free lift on the defining generator and rewrite the resulting class
-- relation using `projective_scalarExtension_class_middle_eq_left_add_right`.
private theorem projective_baseChange_generator_mem_ker
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule A G))
    (hSplit : Nonempty (S.X₂.V ≃ₗ[A[G]] S.X₁.V × S.X₃.V)) :
    FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃ ∈
      (projectiveGrothendieckBaseChangeLift K).ker := by
  -- Evaluate the free lift on the defining generator and rewrite by scalar-extension additivity.
  change
    projectiveGrothendieckBaseChangeLift K
        (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  rw [projectiveGrothendieckBaseChangeLift_shortExact_generator_eq (K := K) S hSplit]
  rw [sub_eq_zero]
  rw [sub_eq_iff_eq_add]
  rw [add_comm]
  exact projective_scalarExtension_class_middle_eq_left_add_right (A := A) (K := K) (G := G) S hSplit

-- Proof sketch: generators of
-- `finiteProjectiveGroupAlgebraGrothendieckRelations A G` come from short exact sequences, and
-- `projective_baseChange_generator_mem_ker` sends each such generator into the kernel.
private theorem finiteProjectiveGroupAlgebraGrothendieckRelations_le_baseChangeLift_ker :
    finiteProjectiveGroupAlgebraGrothendieckRelations A G ≤
      (projectiveGrothendieckBaseChangeLift K).ker := by
  -- Each defining generator comes from a short exact sequence, and scalar extension kills it.
  rw [finiteProjectiveGroupAlgebraGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  exact projective_baseChange_generator_mem_ker (A := A) (K := K) (G := G) S hS

/-- Scalar extension along `A → K` induces a homomorphism `P_A(G) → R_K(G)` on projective
Grothendieck groups. -/
def projectiveGrothendieckBaseChangeHom :
    finiteProjectiveGroupAlgebraGrothendieckGroup A G →+ R₀[K](G) :=
  QuotientAddGroup.lift
    (finiteProjectiveGroupAlgebraGrothendieckRelations A G)
    (projectiveGrothendieckBaseChangeLift K)
    (finiteProjectiveGroupAlgebraGrothendieckRelations_le_baseChangeLift_ker K)

-- Proof sketch: `projectiveGrothendieckBaseChangeHom` is the quotient lift of
-- `projectiveGrothendieckBaseChangeLift`, which sends a finite projective `A[G]`-module to the
-- Grothendieck class of its scalar extension to `K`.
/-- On a generator class, tensor product with `K` gives the Grothendieck class of the scalar
extension of the corresponding finite projective `A[G]`-module. -/
@[simp] theorem projectiveGrothendieckBaseChangeHom_projectiveClass_eq
    (P : FiniteProjectiveGroupAlgebraModule A G) :
    projectiveGrothendieckBaseChangeHom K [P]ₚ₀ = [P.scalarExtension K]₀ := rfl

end TensorProductHom

section ScalarExtensionHom

variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A
variable (A K)

/-- Definition 15-15.3-1: using the canonical identification `P_A(G) ≃ P_k(G)`, Serre's
homomorphism `e : P_k(G) → R_K(G)` is the scalar-extension map on `P_A(G)` transported along the
inverse reduction isomorphism. -/
def projectiveGrothendieckScalarExtensionHom
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    finiteProjectiveGroupAlgebraGrothendieckGroup k G →+ R₀[K](G) :=
  (projectiveGrothendieckBaseChangeHom K).comp
    projectiveGrothendieckReductionEquiv.symm.toAddMonoidHom

-- Proof sketch: unfold `projectiveGrothendieckScalarExtensionHom`; it is the composite of
-- `projectiveGrothendieckBaseChangeHom` with `projectiveGrothendieckReductionEquiv.symm`, so
-- evaluation is immediate.
/-- Evaluating Serre's scalar-extension homomorphism amounts to transporting a class in `P_k(G)`
back to `P_A(G)` by the inverse reduction isomorphism and then extending scalars to `K`. -/
theorem projectiveGrothendieckScalarExtensionHom_apply
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (x : finiteProjectiveGroupAlgebraGrothendieckGroup k G) :
    projectiveGrothendieckScalarExtensionHom A K x =
      projectiveGrothendieckBaseChangeHom K
        (projectiveGrothendieckReductionEquiv.symm x) := rfl

end ScalarExtensionHom

end Representation
