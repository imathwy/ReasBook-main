import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

noncomputable section

/-!
# Lemma 21.48.4 (Stacks tag 08JJ) — perfect objects and their duals on a ringed site

Source statement.  Let `(C, O)` be a ringed site and let `K` be a perfect object of
`D(O)`.  Then `K^∨ = RHom_O(K, O)` is a perfect object too and `(K^∨)^∨ ≅ K`.  There are
functorial isomorphisms
`M ⊗^L_O K^∨ = RHom_O(K, M)` and `H⁰(C, M ⊗^L_O K^∨) = Hom_{D(O)}(K, M)` for `M` in `D(O)`.

## Owner abstraction (domain-style sampling)

- Primary domain: dualizable (rigid) objects of a symmetric monoidal closed category and the
  standard evaluation/coevaluation calculus relating duals, internal hom and the tensor
  product.
- Sampled owner declarations: `CategoryTheory.HasRightDual`, the right dual `Xᘁ`,
  `CategoryTheory.ExactPairing`, `CategoryTheory.MonoidalClosed`, `CategoryTheory.ihom`,
  `CategoryTheory.leftDual_rightDual`, `CategoryTheory.tensorRightHomEquiv`,
  `SheafOfModules.unit`, `DerivedCategory.singleFunctor`.
- Best owner abstraction: a *perfect* object of `D(O)` is a *dualizable* object of the
  symmetric monoidal closed derived category, i.e. an object `K` with `[HasRightDual K]`; the
  dual `K^∨` is the right dual `Kᘁ = RHom_O(K, O) = ihom K (𝟙_)`, the derived tensor `⊗^L` is
  the monoidal product `⊗`, `RHom_O(K, -)` is the internal hom `ihom K`, the structure sheaf in
  degree `0` is the monoidal unit `𝟙_`, and `H⁰(C, N) = Hom_{D(O)}(O[0], N)`.
- Source/core/bridge triage:
  - `source-facing`: the lemma vocabulary `K^∨`, `(K^∨)^∨ ≅ K`, `M ⊗^L K^∨ ≅ RHom(K, M)`,
    `H⁰(C, M ⊗^L K^∨) = Hom_{D(O)}(K, M)` collected in the bundle `DualPerfect`;
  - `core/canonical`: the symmetric monoidal closed derived category `D(O)` together with the
    dualizability datum `[HasRightDual K]`;
  - `bridge/view`: the four iso/equiv fields of `DualPerfect` and the unit identification
    `eO : 𝟙_ D ≅ O[0]` translating global sections into `Hom`-from-the-unit.

## Faithfulness note

Mathlib (rev `52cc3b45`) carries no monoidal — hence no derived tensor `⊗^L` or `RHom` —
structure on `D(O) := DerivedCategory (SheafOfModules R)` (it only has the *underived*
monoidal structure on `PresheafOfModules` of a commutative ring sheaf).  We therefore take the
symmetric monoidal closed structure on `D(O)` as instance hypotheses and the unit
identification `eO : 𝟙_ D ≅ O[0]` (both canonical in the genuine derived tensor structure) as
context data.  Under this abstraction the four assertions of the lemma are the standard facts
about dualizable objects, which is exactly the mathematical content of the Stacks proof
(`K` perfect `⟺` `K` represented locally by a strictly perfect complex `⟺` `K` dualizable).
Only the Prop-level naturality clauses and the final proof are `sorry`; every `def`/`abbrev`
and every data field below is a genuine term.
-/

-- The `O`-module universe is forced to coincide with the ring-sheaf universe `u`
-- by `SheafOfModules.unit R : SheafOfModules.{u} R`.
universe u uC vC

namespace Stacks.Tag08JJ

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})
  -- instances making `SheafOfModules R` abelian and `unit R` available:
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

-- A chosen derived category of the abelian category of `O`-modules.
attribute [local instance] HasDerivedCategory.standard

/-- The derived category `D(O)` of `O`-modules, with `O := unit R` the structure sheaf. -/
abbrev DerivedModules : Type _ := DerivedCategory (SheafOfModules.{u} R)

/-- The structure sheaf `O`, as the rank-`1` free module `unit R`. -/
abbrev structureSheaf : SheafOfModules.{u} R := SheafOfModules.unit R

/-- `O[0]`: the structure sheaf placed in cohomological degree `0`, an object of `D(O)`. -/
abbrev structureSheafZero : DerivedModules R :=
  (DerivedCategory.singleFunctor (SheafOfModules.{u} R) 0).obj (structureSheaf R)

/--
**Stacks 21.48.4 / tag 08JJ.**  The conclusions of the lemma packaged as the data of a
dualizable object of the symmetric monoidal closed derived category `D := D(O)`.

We take a *perfect* object as a *dualizable* one (`[HasRightDual K]`), identify the monoidal
unit `𝟙_ D` with `O[0]` via the iso `eO`, and read off the four assertions:

* `dual_perfect` — (1) `K^∨ = Kᘁ` is again perfect, i.e. dualizable.
* `doubleDual` — (2) `(K^∨)^∨ ≅ K`.
* `evalIso` (+ `evalIso_natural`) — (3) the functorial iso `M ⊗^L K^∨ ≅ RHom(K, M)`,
  i.e. `(M ⊗ Kᘁ) ≅ (ihom K).obj M`.
* `globalSectionsEquiv` (+ `globalSectionsEquiv_natural`) — (4) the functorial bijection
  `H⁰(C, M ⊗^L K^∨) ≅ Hom_{D(O)}(K, M)`, with `H⁰(C, N) = Hom(O[0], N) = (O[0] ⟶ N)`.

All iso/equiv fields are returned as data; only the naturality fields are `Prop`-valued. -/
structure DualPerfect
    [MonoidalCategory (DerivedModules R)] [SymmetricCategory (DerivedModules R)]
    [MonoidalClosed (DerivedModules R)]
    (K : DerivedModules R) [HasRightDual K]
    (eO : 𝟙_ (DerivedModules R) ≅ structureSheafZero R) where
  /-- (1) `K^∨ = Kᘁ` is again perfect (dualizable). -/
  dual_perfect : HasRightDual (Kᘁ)
  /-- (2) `(K^∨)^∨ ≅ K`. -/
  doubleDual : haveI := dual_perfect; (Kᘁ)ᘁ ≅ K
  /-- (3) `M ⊗^L K^∨ ≅ RHom(K, M)` for every `M`. -/
  evalIso (M : DerivedModules R) : (M ⊗ Kᘁ) ≅ ((ihom K).obj M)
  /-- (3, naturality) the family `evalIso` is functorial in `M`. -/
  evalIso_natural :
    ∀ {M N : DerivedModules R} (f : M ⟶ N),
      (evalIso M).hom ≫ (ihom K).map f = (f ▷ Kᘁ) ≫ (evalIso N).hom
  /-- (4) `H⁰(C, M ⊗^L K^∨) ≅ Hom_{D(O)}(K, M)`, with `H⁰(C, N) = Hom(O[0], N)`. -/
  globalSectionsEquiv (M : DerivedModules R) :
    (structureSheafZero R ⟶ M ⊗ Kᘁ) ≃ (K ⟶ M)
  /-- (4, naturality) the family `globalSectionsEquiv` is functorial in `M`. -/
  globalSectionsEquiv_natural :
    ∀ {M N : DerivedModules R} (g : M ⟶ N) (x : structureSheafZero R ⟶ M ⊗ Kᘁ),
      globalSectionsEquiv N (x ≫ (g ▷ Kᘁ)) = globalSectionsEquiv M x ≫ g

variable [MonoidalCategory (DerivedModules R)] [SymmetricCategory (DerivedModules R)]
  [MonoidalClosed (DerivedModules R)]

/--
Lemma 21.48.4 (tag 08JJ).  For a perfect (= dualizable) object `K` of `D(O)` and any
identification `eO : 𝟙_ D ≅ O[0]` of the monoidal unit with the structure sheaf in degree `0`,
the dual `K^∨ = Kᘁ` is perfect, `(K^∨)^∨ ≅ K`, and there are functorial isomorphisms
`M ⊗^L K^∨ ≅ RHom(K, M)` and `H⁰(C, M ⊗^L K^∨) ≅ Hom_{D(O)}(K, M)`.

The statement is fully real-typed (no data `sorry`); only the proof — which constructs the
four (iso/equiv) data together with their naturality — is `sorry`. -/
theorem perfect_dual
    (K : DerivedModules R) [HasRightDual K]
    (eO : 𝟙_ (DerivedModules R) ≅ structureSheafZero R) :
    Nonempty (DualPerfect R K eO) := by
  sorry

end Stacks.Tag08JJ

end
