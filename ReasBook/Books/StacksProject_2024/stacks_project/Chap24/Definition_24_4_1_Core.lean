import StacksProject_2024.stacks_project.Chap24.Definition_24_3_1

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- Definition 24.4.1 (1): a graded `\mathcal A`-module on the ringed site
`(\mathcal C, \mathcal O)` is a `\mathbf Z`-graded family `\mathcal M^n` of `\mathcal O`-module
sheaves with sectionwise `\mathcal O`-bilinear multiplication maps
`\mathcal M^n \times \mathcal A^m \to \mathcal M^{n + m}` satisfying associativity and the
identity-section axiom. -/
@[stacks 0FQZ]
structure GradedModuleSheaf (𝒜 : GradedAlgebraSheaf 𝒪) where
  /-- The degreewise family of `\mathcal O`-module sheaves. -/
  obj : ℤ → SheafOfModules.{max u v, v, u, max u v} (ringSheaf J 𝒪)
  /-- The degreewise right action on local sections. -/
  smul (n m : ℤ) (U : Cᵒᵖ) :
      (obj n).val.obj U →ₗ[𝒪.obj.obj U]
        (𝒜 m).val.obj U →ₗ[𝒪.obj.obj U] (obj (n + m)).val.obj U
  /-- The action maps commute with restriction. -/
  map_smul {n m : ℤ} {U V : Cᵒᵖ} (f : U ⟶ V)
      (x : (obj n).val.obj U) (a : (𝒜 m).val.obj U) :
      (((obj (n + m)).val.map f).hom) (smul n m U x a) =
        smul n m V (((obj n).val.map f).hom x) (((𝒜 m).val.map f).hom a)
  /-- The action is associative with the graded multiplication on `\mathcal A`. -/
  smul_assoc (n m l : ℤ) (U : Cᵒᵖ)
      (x : (obj n).val.obj U) (a : (𝒜 m).val.obj U) (b : (𝒜 l).val.obj U) :
      HEq (smul (n + m) l U (smul n m U x a) b)
        (smul n (m + l) U x (𝒜.mul U m l a b))
  /-- The identity section of `\mathcal A^0` acts trivially. -/
  smul_one (n : ℤ) (U : Cᵒᵖ) (x : (obj n).val.obj U) :
      HEq (smul n 0 U x (𝒜.one U)) x

namespace GradedModuleSheaf

/- Source-facing notation: the Stacks Project writes the category of graded `\mathcal A`-modules
as `\mathrm{Mod}(\mathcal A)`. This scoped notation exposes the canonical owner
`GradedModuleSheaf 𝒜`. -/
scoped[SheafOfModules.RingedSite.GradedModuleSheaf] notation:max "Mod(" 𝒜:arg ")" =>
  _root_.SheafOfModules.RingedSite.GradedModuleSheaf 𝒜

end GradedModuleSheaf

open scoped SheafOfModules.RingedSite.GradedModuleSheaf

/-- A graded module sheaf can be evaluated at each integer degree. -/
instance instCoeFun (𝒜 : GradedAlgebraSheaf 𝒪) :
    CoeFun (Mod(𝒜))
      (fun _ ↦ ℤ → SheafOfModules.{max u v, v, u, max u v} (ringSheaf J 𝒪)) where
  coe ℳ := ℳ.obj

namespace GradedModuleSheaf

/-- The degree-`n` local sections of a graded module sheaf over an object of the site. -/
abbrev sections {𝒜 : GradedAlgebraSheaf 𝒪} (ℳ : Mod(𝒜)) (U : Cᵒᵖ) (n : ℤ) :
    Type (max u v) :=
  (ℳ n).val.obj U

/-- Definition 24.4.1 (2): a homomorphism of graded `\mathcal A`-modules is a degreewise family
of `\mathcal O`-module sheaf morphisms compatible with the graded action maps. -/
@[stacks 0FQZ, ext] structure Hom {𝒜 : GradedAlgebraSheaf 𝒪}
    (ℳ 𝒩 : Mod(𝒜)) where
  /-- The degreewise maps `f^n : \mathcal M^n \to \mathcal N^n`. -/
  hom (n : ℤ) : ℳ n ⟶ 𝒩 n
  /-- Compatibility with the graded action maps on local sections. -/
  comm (n m : ℤ) (U : Cᵒᵖ) (x : ℳ.sections U n) (a : 𝒜.sections U m) :
      ((hom (n + m)).val.app U).hom (ℳ.smul n m U x a) =
        𝒩.smul n m U (((hom n).val.app U).hom x) a

/-- A graded `\mathcal A`-module homomorphism can be evaluated degreewise. -/
instance instCoeFunHom {𝒜 : GradedAlgebraSheaf 𝒪}
    (ℳ 𝒩 : Mod(𝒜)) : CoeFun (Hom ℳ 𝒩) (fun _ ↦ ∀ n : ℤ, ℳ n ⟶ 𝒩 n) where
  coe f := f.hom

end GradedModuleSheaf

end

end SheafOfModules.RingedSite
