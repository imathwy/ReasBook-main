import Mathlib
import stacks_project.Chap15.Lemma_15_119_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped TensorProduct
open scoped DeterminantLine

universe u v

variable {R : Type u} [CommRing R]

/-
Domain-style sampling for determinant-line comparison maps in a submodule tower:
- primary domain: determinant lines of finite projective modules and the canonical comparison maps
  attached to short exact sequences;
- sampled owner declarations:
  * `CategoryTheory.ShortComplex.ShortExact.determinantTensorIso`,
  * `determinantTensorIsoOfShortExact_naturality`,
  * `determinantTensorIsoOfShortExact`,
  * `Submodule.quotientQuotientEquivQuotient`;
- best owner abstraction:
  `core/canonical`: `determinantTensorIsoOfShortExact_naturality` is the chapter-level owner for
    commutative squares of determinant comparison maps attached to isomorphic presented short exact
    rows;
  `source-facing`: the main theorem should specialize that owner square to a tower `K ≤ L ≤ M`
    and the quotients `L / K`, `M / L`, `M / K`;
  `bridge/view`: the quotient row `L / K → M / K → M / L` is expressed through the canonical
    submodule `L.map K.mkQ ⊆ M / K` and the standard quotient identifications.
- primitive data: the submodules `K ≤ L ≤ M` together with the finite projective hypotheses on
  `K`, `L / K`, and `M / L`;
- derived API: finiteness/projectivity of `L`, `M`, and `M / K`, and the resulting determinant
  comparison square.
-/

section SubmoduleTower

variable {M : Type v} [AddCommGroup M] [Module R M]

private theorem projective_of_submodule_quotient (N : Submodule R M)
    [Module.Projective R N] [Module.Projective R (M ⧸ N)] :
    Module.Projective R M := by
  let s : (M ⧸ N) →ₗ[R] M :=
    Classical.choose
      (Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective)
  have hs : N.mkQ.comp s = LinearMap.id :=
    Classical.choose_spec
      (Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective)
  obtain ⟨e, -, -⟩ :=
    ((Function.Exact.split_tfae (LinearMap.exact_subtype_mkQ N) Subtype.val_injective
      N.mkQ_surjective).out 0 2 rfl rfl).mp ⟨s, hs⟩
  exact Module.Projective.of_equiv e.symm

private theorem exact_inclusion_mkQ (K L : Submodule R M) (hKL : K ≤ L) :
    Function.Exact (Submodule.inclusion hKL) (K.submoduleOf L).mkQ := by
  have hExact : Function.Exact (K.submoduleOf L).subtype (K.submoduleOf L).mkQ :=
    LinearMap.exact_subtype_mkQ (K.submoduleOf L)
  simpa [Submodule.inclusion] using
    (Function.Surjective.comp_exact_iff_exact
      (Submodule.submoduleOfEquivOfLe hKL).symm.surjective).2 hExact

namespace SubmoduleTower

private theorem finite_submoduleOf (K L : Submodule R M) (hKL : K ≤ L)
    [Module.Finite R ↥K] :
    Module.Finite R (K.submoduleOf L) :=
  Module.Finite.equiv (Submodule.submoduleOfEquivOfLe hKL).symm

private theorem projective_submoduleOf (K L : Submodule R M) (hKL : K ≤ L)
    [Module.Projective R ↥K] :
    Module.Projective R (K.submoduleOf L) :=
  Module.Projective.of_equiv (Submodule.submoduleOfEquivOfLe hKL).symm

private theorem finite_L (K L : Submodule R M) (hKL : K ≤ L)
    [Module.Finite R ↥K] [Module.Finite R (L ⧸ K.submoduleOf L)] :
    Module.Finite R ↥L := by
  letI := finite_submoduleOf K L hKL
  exact Module.Finite.of_submodule_quotient (K.submoduleOf L)

private theorem projective_L (K L : Submodule R M) (hKL : K ≤ L)
    [Module.Projective R ↥K] [Module.Projective R (L ⧸ K.submoduleOf L)] :
    Module.Projective R ↥L := by
  letI := projective_submoduleOf K L hKL
  exact projective_of_submodule_quotient (K.submoduleOf L)

private theorem finite_M (L : Submodule R M)
    [Module.Finite R ↥L] [Module.Finite R (M ⧸ L)] :
    Module.Finite R M := by
  exact Module.Finite.of_submodule_quotient L

private theorem projective_M (L : Submodule R M)
    [Module.Projective R ↥L] [Module.Projective R (M ⧸ L)] :
    Module.Projective R M := by
  exact projective_of_submodule_quotient L

-- Bridge/view: the quotient of `L` by the induced submodule from `K` is canonically equivalent
-- to the image of `L` in `M ⧸ K`.
private noncomputable def quotientSubmoduleOfEquivImage (K L : Submodule R M) :
    (L ⧸ K.submoduleOf L) ≃ₗ[R] L.map K.mkQ :=
  let f : L →ₗ[R] M ⧸ K := K.mkQ.comp L.subtype
  let hk : f.ker = K.submoduleOf L := by
    ext x
    simp [f, Submodule.submoduleOf]
  let hr : f.range = L.map K.mkQ := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  (Submodule.quotEquivOfEq _ _ hk.symm).trans
    (f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hr))

private theorem projective_quotientSubmodule (K L : Submodule R M)
    [Module.Projective R (L ⧸ K.submoduleOf L)] :
    Module.Projective R (L.map K.mkQ) :=
  Module.Projective.of_equiv (quotientSubmoduleOfEquivImage K L)

private theorem finite_quotientSubmodule (K L : Submodule R M)
    [Module.Finite R (L ⧸ K.submoduleOf L)] :
    Module.Finite R ↥(L.map K.mkQ) :=
  Module.Finite.equiv (quotientSubmoduleOfEquivImage K L)

private theorem projective_quotientQuotient (K L : Submodule R M) (hKL : K ≤ L)
    [Module.Projective R (M ⧸ L)] :
    Module.Projective R ((M ⧸ K) ⧸ L.map K.mkQ) :=
  Module.Projective.of_equiv (Submodule.quotientQuotientEquivQuotient K L hKL).symm

private theorem finite_quotientQuotient (K L : Submodule R M) (hKL : K ≤ L)
    [Module.Finite R (M ⧸ L)] :
    Module.Finite R ((M ⧸ K) ⧸ L.map K.mkQ) :=
  Module.Finite.equiv (Submodule.quotientQuotientEquivQuotient K L hKL).symm

private theorem finite_quotientKM (K : Submodule R M)
    [Module.Finite R M] :
    Module.Finite R (M ⧸ K) := by
  exact Module.Finite.quotient R K

private theorem projective_quotientKM (K L : Submodule R M)
    [Module.Projective R ↥(L.map K.mkQ)]
    [Module.Projective R ((M ⧸ K) ⧸ L.map K.mkQ)] :
    Module.Projective R (M ⧸ K) := by
  exact projective_of_submodule_quotient (L.map K.mkQ)

end SubmoduleTower

variable (K L : Submodule R M) (hKL : K ≤ L)
variable [Module.Finite R K] [Module.Projective R K]
variable [Module.Finite R (L ⧸ K.submoduleOf L)] [Module.Projective R (L ⧸ K.submoduleOf L)]
variable [Module.Finite R (M ⧸ L)] [Module.Projective R (M ⧸ L)]

local notation3:max "det(" M ")" => Module.det R M

open SubmoduleTower

namespace SubmoduleTower

/-- The determinant comparison map for
`0 → K → L → L / K → 0`. -/
noncomputable def submoduleDeterminantIso :
    (det(↥K) ⊗[R] det(L ⧸ K.submoduleOf L)) ≃ₗ[R] det(↥L) :=
  let _ : Module.Finite R ↥L := finite_L K L hKL
  let _ : Module.Projective R ↥L := projective_L K L hKL
  determinantTensorIsoOfShortExact
    (Submodule.inclusion hKL)
    (K.submoduleOf L).mkQ
    (Submodule.inclusion_injective hKL)
    (K.submoduleOf L).mkQ_surjective
    (exact_inclusion_mkQ K L hKL)

/-- The determinant comparison map for
`0 → L → M → M / L → 0`. -/
noncomputable def ambientDeterminantIso :
    (det(↥L) ⊗[R] det(M ⧸ L)) ≃ₗ[R] det(M) :=
  let _ : Module.Finite R ↥L := finite_L K L hKL
  let _ : Module.Projective R ↥L := projective_L K L hKL
  let _ : Module.Finite R M := finite_M L
  let _ : Module.Projective R M := projective_M L
  determinantTensorIsoOfShortExact
    L.subtype
    L.mkQ
    Subtype.val_injective
    L.mkQ_surjective
    (LinearMap.exact_subtype_mkQ L)

/-- The determinant comparison map for
`0 → K → M → M / K → 0`. -/
noncomputable def totalDeterminantIso :
    (det(↥K) ⊗[R] det(M ⧸ K)) ≃ₗ[R] det(M) :=
  let _ : Module.Finite R ↥L := finite_L K L hKL
  let _ : Module.Projective R ↥L := projective_L K L hKL
  let _ : Module.Finite R M := finite_M L
  let _ : Module.Projective R M := projective_M L
  let _ : Module.Finite R (M ⧸ K) := finite_quotientKM K
  let _ : Module.Finite R ↥(L.map K.mkQ) := finite_quotientSubmodule K L
  let _ : Module.Projective R ↥(L.map K.mkQ) := projective_quotientSubmodule K L
  let _ : Module.Finite R ((M ⧸ K) ⧸ L.map K.mkQ) := finite_quotientQuotient K L hKL
  let _ : Module.Projective R ((M ⧸ K) ⧸ L.map K.mkQ) := projective_quotientQuotient K L hKL
  let _ : Module.Projective R (M ⧸ K) := projective_quotientKM K L
  determinantTensorIsoOfShortExact
    K.subtype
    K.mkQ
    Subtype.val_injective
    K.mkQ_surjective
    (LinearMap.exact_subtype_mkQ K)

/-- Bridge/view: the determinant comparison map for
`0 → L / K → M / K → M / L → 0`, obtained from the canonical exact row
`0 → L.map K.mkQ → M / K → (M / K) / L.map K.mkQ → 0`
through the standard quotient identifications. -/
noncomputable def quotientDeterminantIso :
    (det(L ⧸ K.submoduleOf L) ⊗[R] det(M ⧸ L)) ≃ₗ[R] det(M ⧸ K) :=
  let _ : Module.Finite R ↥L := finite_L K L hKL
  let _ : Module.Finite R M := finite_M L
  let _ : Module.Finite R (M ⧸ K) := finite_quotientKM K
  let _ : Module.Finite R ↥(L.map K.mkQ) := finite_quotientSubmodule K L
  let _ : Module.Projective R ↥(L.map K.mkQ) := projective_quotientSubmodule K L
  let _ : Module.Finite R ((M ⧸ K) ⧸ L.map K.mkQ) := finite_quotientQuotient K L hKL
  let _ : Module.Projective R ((M ⧸ K) ⧸ L.map K.mkQ) := projective_quotientQuotient K L hKL
  let _ : Module.Projective R (M ⧸ K) := projective_quotientKM K L
  (TensorProduct.congr
      (determinantLineMap (quotientSubmoduleOfEquivImage K L))
      (determinantLineMap (Submodule.quotientQuotientEquivQuotient K L hKL).symm)).trans
    (determinantTensorIsoOfShortExact
      (L.map K.mkQ).subtype
      (L.map K.mkQ).mkQ
      Subtype.val_injective
      (L.map K.mkQ).mkQ_surjective
      (LinearMap.exact_subtype_mkQ (L.map K.mkQ)))

-- Proof sketch: derive the finite projective structures on `L`, `M`, and `M / K` from the three
-- source-facing hypotheses using split exactness for the quotient rows. Then compare the two ways
-- of passing from `det K ⊗ det(L / K) ⊗ det(M / L)` to `det M` by rewriting the left quotient row
-- through the canonical identifications `L / K ≃ L.map K.mkQ` and
-- `(M / K) / (L / K) ≃ M / L`, and finally applying the determinant-map naturality of
-- Lemma `15.119.3`.
/-- Lemma 15.119.4: for submodules `K ≤ L` of an `R`-module `M`, if `K`, `L / K`, and `M / L` are
finite projective, then the determinant comparison maps from Lemma `15.119.2` for the short exact
sequences
`0 → K → L → L / K → 0`, `0 → L → M → M / L → 0`, `0 → K → M → M / K → 0`, and
`0 → L / K → M / K → M / L → 0`
form a commutative square. The left vertical map is the source-facing quotient-row bridge
`quotientDeterminantIso K L hKL`, built from the canonical identifications
`L / K ≃ L.map K.mkQ` and `(M / K) / (L / K) ≃ M / L`. -/
theorem determinant_tensor_iso_tower_commutes :
    CommSq
      (ModuleCat.ofHom <|
        (TensorProduct.congr
          (submoduleDeterminantIso K L hKL)
          (LinearEquiv.refl R (det(M ⧸ L)))).toLinearMap)
      (ModuleCat.ofHom <|
        ((TensorProduct.assoc R
            (det(↥K))
            (det(L ⧸ K.submoduleOf L))
            (det(M ⧸ L))).trans
          (TensorProduct.congr
            (LinearEquiv.refl R (det(↥K)))
            (quotientDeterminantIso K L hKL))).toLinearMap)
      (ModuleCat.ofHom <|
        (ambientDeterminantIso K L hKL).toLinearMap)
      (ModuleCat.ofHom <| (totalDeterminantIso K L hKL).toLinearMap) := by
  sorry

/-- The determinant square from `determinant_tensor_iso_tower_commutes`, evaluated on a pure
tensor. -/
theorem determinant_tensor_iso_tower_commutes_apply
    (xK : det(↥K)) (xQ : det(L ⧸ K.submoduleOf L)) (xC : det(M ⧸ L)) :
    ambientDeterminantIso K L hKL
      ((TensorProduct.congr
          (submoduleDeterminantIso K L hKL)
          (LinearEquiv.refl R (det(M ⧸ L)))).toLinearMap
        (xK ⊗ₜ[R] xQ ⊗ₜ[R] xC)) =
      totalDeterminantIso K L hKL
        (((TensorProduct.assoc R
            (det(↥K))
            (det(L ⧸ K.submoduleOf L))
            (det(M ⧸ L))).trans
          (TensorProduct.congr
            (LinearEquiv.refl R (det(↥K)))
            (quotientDeterminantIso K L hKL))).toLinearMap
          (xK ⊗ₜ[R] xQ ⊗ₜ[R] xC)) := by
  sorry

end SubmoduleTower
end SubmoduleTower
