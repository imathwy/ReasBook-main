import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.LinearAlgebra.Dimension.Finite

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_65_1 (from Chap15) -/
noncomputable section

open CategoryTheory
open ComplexShape

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
private abbrev Q : Cpx ⥤ DMod := DerivedCategory.Q

/- Domain-style sampling for Definition 15.65.1:
- primary domain: pseudo-coherence for derived `R`-complexes and `R`-modules;
  `CochainComplex.IsMPseudoCoherent`,
  `CochainComplex.IsPseudoCoherent`,
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsPseudoCoherentRelativeTo`;
- best owner abstraction: this file owns the absolute derived predicates
  `DerivedCategory.IsMPseudoCoherent` and `DerivedCategory.IsPseudoCoherent`, together with the
  high-frequency cochain-complex and module bridge abbreviations built from these owners; the
  relative notions remain downstream bridge/view layers;
- primitive vs. derived:
  primitive data are the bounded finite-free representative and the cohomology comparison map in
  `D(R)`;
  derived API is the cochain-complex specialization via `DerivedCategory.Q` and the module
  specialization `M ↦ M[0]`, exposed through `CochainComplex.IsMPseudoCoherent`,
  `CochainComplex.IsPseudoCoherent`, `ModuleCat.IsMPseudoCoherent`, and
  `ModuleCat.IsPseudoCoherent`;
- source/core/bridge triage:
  `source-facing`: the four numbered predicates of Definition `15.65.1`;
  `core/canonical`: the owner predicates on `DerivedCategory` together with
    `CochainComplex.IsTermwiseFiniteFree` and its induced termwise `Module.Free` /
    `Module.Finite` instances;
  `bridge/view`: the cochain-complex and module specializations, together with the relative
    extensions from `15.82.4` and `15.82.10`.
-/

namespace CochainComplex

/-- A cochain complex of `R`-modules is termwise finite free when every degree is a finite free
`R`-module. -/
class IsTermwiseFiniteFree (E : Cpx) : Prop where
  out : ∀ i : ℤ, Module.Free R (E.X i) ∧ Module.Finite R (E.X i)

instance (E : Cpx) [hE : IsTermwiseFiniteFree E] (i : ℤ) : Module.Free R (E.X i) :=
  (hE.out i).1

instance (E : Cpx) [hE : IsTermwiseFiniteFree E] (i : ℤ) : Module.Finite R (E.X i) :=
  (hE.out i).2

end CochainComplex

namespace DerivedCategory

/-- Definition 15.65.1 (1): an object `K^•` of `D(R)` is `m`-pseudo-coherent if it admits a map
from a bounded cochain complex of finite free `R`-modules inducing isomorphisms on cohomology in
degrees `> m` and an epimorphism in degree `m`. -/
def IsMPseudoCoherent (K : DMod) (m : ℤ) : Prop :=
  ∃ E : Cpx,
    (∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b) ∧
      E.IsTermwiseFiniteFree ∧
      ∃ α : Q.obj E ⟶ K,
        (∀ i : ℤ, m < i → IsIso ((H i).map α)) ∧
          Epi ((H m).map α)

/-- Definition 15.65.1 (2): an object `K^•` of `D(R)` is pseudo-coherent if it is represented in
the derived category by a bounded-above cochain complex of finite free `R`-modules. -/
def IsPseudoCoherent (K : DMod) : Prop :=
  ∃ E : Cpx,
    (∃ b : ℤ, E.IsStrictlyLE b) ∧
      E.IsTermwiseFiniteFree ∧
      ∃ α : Q.obj E ⟶ K, IsIso α

end DerivedCategory

namespace CochainComplex

/-- A cochain complex is `m`-pseudo-coherent when its image in `D(R)` is `m`-pseudo-coherent in
the canonical sense of Definition `15.65.1`. -/
abbrev IsMPseudoCoherent (K : Cpx) (m : ℤ) : Prop :=
  DerivedCategory.IsMPseudoCoherent ((Q).obj K) m

/-- A cochain complex is pseudo-coherent when its image in `D(R)` is pseudo-coherent in the
canonical sense of Definition `15.65.1`. -/
abbrev IsPseudoCoherent (K : Cpx) : Prop :=
  DerivedCategory.IsPseudoCoherent ((Q).obj K)

end CochainComplex

namespace ModuleCat

/-- The degree-zero embedding `\operatorname{Mod}(R) ⥤ D(R)`. -/
abbrev single0Functor : ModuleCat R ⥤ DMod :=
  DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/-- Definition 15.65.1 (3): an `R`-module `M` is `m`-pseudo-coherent when the derived object
`M[0]` is `m`-pseudo-coherent. -/
abbrev IsMPseudoCoherent (M : ModuleCat R) (m : ℤ) : Prop :=
  DerivedCategory.IsMPseudoCoherent (single0Functor.obj M) m

/-- Definition 15.65.1 (4): an `R`-module `M` is pseudo-coherent when the derived object `M[0]`
is pseudo-coherent. -/
abbrev IsPseudoCoherent (M : ModuleCat R) : Prop :=
  DerivedCategory.IsPseudoCoherent (single0Functor.obj M)

end ModuleCat

end

end CategoryTheory

/-! ### Lemma_15_65_2 (from Chap15) -/
noncomputable section

open CategoryTheory ObjectProperty Pretriangulated

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/- Domain-style sampling for Lemma 15.65.2:
- primary domain: `m`-pseudo-coherent objects of `D(R)` and their behavior in distinguished
  triangles;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherent`,
  `ObjectProperty.IsTriangulatedClosed₂`,
  `Triangle.rotate`,
  `Triangle.invRotate`,
  `rot_of_distTriang`,
  `inv_rot_of_distTriang`;
- best owner abstraction: the source-facing owner is the canonical predicate
  `DerivedCategory.IsMPseudoCoherent` on objects of `D(R)`; for a fixed `m`, the exact
  two-out-of-three owner already present in mathlib is the object property
  `(fun K : DMod ↦ K.IsMPseudoCoherent m)`;
- primitive vs. derived:
  primitive data are the owner predicate `IsMPseudoCoherent`, the shift behavior of that owner,
  and the distinguished triangle;
  derived API is clause `(1)` together with the fixed-`m` canonical
  `ObjectProperty.IsTriangulatedClosed₂` instance below; the source-facing clauses `(2)` and `(3)`
  are then recovered from that owner property and the canonical triangle rotations;
- source/core/bridge triage:
  `source-facing`: the three numbered closure statements of Lemma `15.65.2`;
  `core/canonical`: `DerivedCategory.IsMPseudoCoherent` and the fixed-`m`
    object property `(fun K : DMod ↦ K.IsMPseudoCoherent m)` on `D(R)`;
  `bridge/view`: the shift equivalence below and the use of `Triangle.rotate` / `Triangle.invRotate`
    to move between clause `(1)` and the source-facing clauses `(2)` and `(3)`.
-/

-- Proof sketch: shift a bounded finite-free approximation of `K` termwise; the cohomology
-- comparison conditions in degrees `> m` and `= m` translate by the standard homology shift
-- isomorphisms.
/-- Shifting an object of `D(R)` by `n` translates the `m`-pseudo-coherence bound by the same
amount. -/
theorem isMPseudoCoherent_shift_iff (K : DMod) (n m : ℤ) :
    (K⟦n⟧).IsMPseudoCoherent (m - n) ↔ K.IsMPseudoCoherent m := sorry

instance isMPseudoCoherent_isClosedUnderIsomorphisms (m : ℤ) :
    IsClosedUnderIsomorphisms (fun K : DMod ↦ K.IsMPseudoCoherent m) where
  of_iso e hK := by
    rcases hK with ⟨E, hbounds, hfree, α, hαgt, hαm⟩
    refine ⟨E, hbounds, hfree, α ≫ e.hom, ?_, ?_⟩
    · intro i hi
      simpa using hαgt i hi
    · simpa [Functor.map_comp] using
        (show Epi ((H m).map α ≫ (H m).map e.hom) by infer_instance)

-- Proof sketch: compare finite-free approximations of `T.obj₁` and `T.obj₂` by a morphism of
-- complexes and use the cone triangle together with the long exact cohomology sequence to produce
-- the required approximation of `T.obj₃`.
/-- Lemma 15.65.2 (1): in a distinguished triangle in `D(R)`, if the first term is
`(m + 1)`-pseudo-coherent and the second term is `m`-pseudo-coherent, then the third term is
`m`-pseudo-coherent. -/
theorem isMPseudoCoherent_obj₃_of_distinguishedTriangle
    {m : ℤ} (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : T.obj₁.IsMPseudoCoherent (m + 1)) (h₂ : T.obj₂.IsMPseudoCoherent m) :
    T.obj₃.IsMPseudoCoherent m := sorry

/-- For fixed `m`, `m`-pseudo-coherent objects of `D(R)` satisfy the canonical
`ObjectProperty.IsTriangulatedClosed₂` two-out-of-three axiom. -/
instance isMPseudoCoherent_isTriangulatedClosed₂ (m : ℤ) :
    IsTriangulatedClosed₂ (fun K : DMod ↦ K.IsMPseudoCoherent m) :=
  .mk' fun T hT h₁ h₃ ↦ by
    have h₃' : (T.obj₃⟦-1⟧).IsMPseudoCoherent (m + 1) := by
      simpa using (isMPseudoCoherent_shift_iff T.obj₃ (-1) m).2 h₃
    exact isMPseudoCoherent_obj₃_of_distinguishedTriangle T.invRotate
      (inv_rot_of_distTriang T hT) h₃' h₁

-- Proof sketch: rotate the distinguished triangle once and reduce to part `(1)`.
/-- Lemma 15.65.2 (2): in a distinguished triangle in `D(R)`, if the first and third terms are
`m`-pseudo-coherent, then the second term is `m`-pseudo-coherent. -/
theorem isMPseudoCoherent_obj₂_of_distinguishedTriangle
    {m : ℤ} (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : T.obj₁.IsMPseudoCoherent m) (h₃ : T.obj₃.IsMPseudoCoherent m) :
    T.obj₂.IsMPseudoCoherent m := by
  let P : ObjectProperty DMod := fun K ↦ K.IsMPseudoCoherent m
  exact P.ext_of_isTriangulatedClosed₂ T hT h₁ h₃

-- Proof sketch: rotate the distinguished triangle once so that `T.obj₁⟦1⟧` becomes the third
-- vertex, apply part `(1)`, and shift back.
/-- Lemma 15.65.2 (3): in a distinguished triangle in `D(R)`, if the second term is
`(m + 1)`-pseudo-coherent and the third term is `m`-pseudo-coherent, then the first term is
`(m + 1)`-pseudo-coherent. -/
theorem isMPseudoCoherent_obj₁_of_distinguishedTriangle
    {m : ℤ} (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₂ : T.obj₂.IsMPseudoCoherent (m + 1)) (h₃ : T.obj₃.IsMPseudoCoherent m) :
    T.obj₁.IsMPseudoCoherent (m + 1) := by
  have hshift : (T.obj₁⟦(1 : ℤ)⟧).IsMPseudoCoherent m :=
    isMPseudoCoherent_obj₃_of_distinguishedTriangle T.rotate
      (rot_of_distTriang T hT) h₂ h₃
  have hshift' : (T.obj₁⟦(1 : ℤ)⟧).IsMPseudoCoherent ((m + 1) - 1) := by
    simpa using hshift
  exact (isMPseudoCoherent_shift_iff T.obj₁ 1 (m + 1)).1 hshift'

end

end CategoryTheory

/-! ### Lemma_15_65_3 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CochainComplex

variable {R : Type u} [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

-- Proof sketch: choose a bounded-above finite-projective approximation `E^• ⟶ K^•` from the
-- definition of `m`-pseudo-coherence. Under the stated vanishing hypotheses, replace `E^•` by a
-- bounded finite-projective complex, peel off the top nonzero term inductively, and identify the
-- surviving top cohomology as a quotient of a finite module in degree `m` and as a cokernel of a
-- map between finite projectives in degree `m + 1`.
/-- Lemma 15.65.3: if an `R`-module cochain complex `K^•` is `m`-pseudo-coherent, then vanishing
of `H^i(K^•)` for `i > m` implies that `H^m(K^•)` is a finite `R`-module, and vanishing of
`H^i(K^•)` for `i > m + 1` implies that `H^{m + 1}(K^•)` is finitely presented. -/
theorem homology_finite_and_finitePresentation_of_isMPseudoCoherent
    {K : Cpx} {m : ℤ} (hK : K.IsMPseudoCoherent m) :
    ((∀ i : ℤ, m < i → IsZero (K.homology i)) → Module.Finite R (K.homology m)) ∧
      ((∀ i : ℤ, m + 1 < i → IsZero (K.homology i)) →
        Module.FinitePresentation R (K.homology (m + 1))) := sorry

-- Proof sketch: apply the first component of
-- `homology_finite_and_finitePresentation_of_isMPseudoCoherent` to the given vanishing range.
/-- The top surviving cohomology of an `m`-pseudo-coherent complex is finite when all higher
cohomology vanishes. -/
theorem homology_finite_of_isMPseudoCoherent
    {K : Cpx} {m : ℤ} (hK : K.IsMPseudoCoherent m)
    (hvanish : ∀ i : ℤ, m < i → IsZero (K.homology i)) :
    Module.Finite R (K.homology m) := sorry

-- Proof sketch: apply the second component of
-- `homology_finite_and_finitePresentation_of_isMPseudoCoherent` to the stronger vanishing range
-- above degree `m + 1`.
/-- The next cohomology of an `m`-pseudo-coherent complex is finitely presented when all
cohomology above degree `m + 1` vanishes. -/
theorem homology_finitePresentation_of_isMPseudoCoherent
    {K : Cpx} {m : ℤ} (hK : K.IsMPseudoCoherent m)
    (hvanish : ∀ i : ℤ, m + 1 < i → IsZero (K.homology i)) :
    Module.FinitePresentation R (K.homology (m + 1)) := sorry

end CochainComplex

/-! ### Lemma_15_65_4 (from Chap15) -/
open CategoryTheory

universe u v w

namespace Module

/- Domain-style sampling for Lemma 15.65.4:
- primary domain: pseudo-coherence of modules concentrated in degree `0`, finite generation,
  finite presentation, and recursive finite free resolutions by syzygies;
- sampled owner declarations:
  `Module.Finite`,
  `Module.FinitePresentation`,
  `Module.Finite.iff_exists_surjective_free`,
  `ChainComplex.IsFiniteFreeResolution`;
- best owner abstraction: the source-facing recursive owner
  `Module.HasLengthFiniteFreeResolution`;
- primitive vs. derived:
  primitive data are finite generation in length `0` and, in the successor step, a surjective map
  from some finite free `R`-module onto `M`;
  derived API is the successor unpacking theorem and the pseudo-coherence characterizations below.

The local cover wrapper added no mathematical content beyond the canonical finite-generation owner
and the raw finite-free-surjection data needed for the recursive step, so it should be deleted
rather than preserved as a parallel public API.
-/

/-- `M` has a length-`n` finite free resolution if one can recursively resolve the kernel of a
surjection from a finite free module onto `M` for `n` steps. For `n = 0`, this is just finite
generation of `M`. -/
def HasLengthFiniteFreeResolution
    (R : Type u) [Ring R] (M : Type w) [AddCommGroup M] [Module R M] : ℕ → Prop
  | 0 => Module.Finite R M
  | n + 1 =>
      ∃ (F : Type w) (_ : AddCommGroup F) (_ : Module R F),
        Module.Free R F ∧ Module.Finite R F ∧
        ∃ f : F →ₗ[R] M, Function.Surjective f ∧
        HasLengthFiniteFreeResolution R (LinearMap.ker f) n

variable (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]

-- Proof sketch: unfold the recursive definition of `HasLengthFiniteFreeResolution` at `n + 1`.
/-- A successor-length finite free resolution is obtained by first taking a finite free cover and
then resolving its kernel for one fewer step. -/
theorem hasLengthFiniteFreeResolution_succ_iff (n : ℕ) :
    HasLengthFiniteFreeResolution R M (n + 1) ↔
      ∃ (F : Type v) (_ : AddCommGroup F) (_ : Module R F),
        Module.Free R F ∧ Module.Finite R F ∧
        ∃ f : F →ₗ[R] M, Function.Surjective f ∧
        HasLengthFiniteFreeResolution R (LinearMap.ker f) n := by
  rfl

end Module

section

variable {R : Type u} [Ring R]

-- Proof sketch: use Lemma `15.65.3` with `m = 0` and the vanishing of the higher cohomology of
-- `M[0]` for the forward implication; for the reverse implication, a surjection from a finite free
-- module onto `M` gives the required bounded finite free approximation concentrated in degree `0`.
/-- Lemma 15.65.4 (1): an `R`-module is `0`-pseudo-coherent exactly when it is finite. -/
theorem moduleCat_isZeroPseudoCoherent_iff_finite
    (M : ModuleCat R) :
    M.IsMPseudoCoherent 0 ↔ Module.Finite R M := sorry

-- Proof sketch: if `M` is `(-1)`-pseudo-coherent, combine part `(1)` with Lemma `15.65.2` for the
-- kernel of a finite free cover to prove finite presentation; conversely, a finite presentation is
-- a length-one finite free resolution and hence a `(-1)`-pseudo-coherent approximation.
/-- Lemma 15.65.4 (2): an `R`-module is `(-1)`-pseudo-coherent exactly when it is finitely
presented. -/
theorem moduleCat_isMinusOnePseudoCoherent_iff_finitePresentation
    (M : ModuleCat R) :
    M.IsMPseudoCoherent (-1) ↔ Module.FinitePresentation R M := sorry

-- Proof sketch: argue by induction on `d`. The cases `d = 0` and `d = 1` are parts `(1)` and
-- `(2)`. For the inductive step, peel off a finite free cover of `M`, apply Lemma `15.65.2` to the
-- kernel, and translate the recursive kernel condition using `Module.HasLengthFiniteFreeResolution`.
/-- Lemma 15.65.4 (3): for `d : ℕ`, an `R`-module is `(-d)`-pseudo-coherent exactly when it admits
a length-`d` finite free resolution. -/
theorem moduleCat_isNegPseudoCoherent_iff_hasFiniteFreeResolutionLength
    (M : ModuleCat R) (d : ℕ) :
    M.IsMPseudoCoherent (-(d : ℤ)) ↔ Module.HasLengthFiniteFreeResolution R M d := sorry

-- Proof sketch: an infinite finite free resolution gives `(-d)`-pseudo-coherence for every `d` by
-- truncation. Conversely, recursively choose the finite free covers supplied by part `(3)` for all
-- lengths to assemble an exact infinite resolution by finite free modules.
/-- Lemma 15.65.4 (4): an `R`-module is pseudo-coherent exactly when it admits an infinite
resolution by finite free `R`-modules. -/
theorem moduleCat_isPseudoCoherent_iff_exists_infiniteFiniteFreeResolution
    (M : ModuleCat R) :
    M.IsPseudoCoherent ↔
      ∃ (F : ChainComplex (ModuleCat R) ℕ)
        (π : F ⟶ (ChainComplex.single₀ (ModuleCat R)).obj M),
        ChainComplex.IsFiniteFreeResolution π := sorry

end

/-! ### Lemma_15_65_5 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "FiniteProjectiveClass" => (fun P : ModuleCat R ↦ Module.Finite R P ∧ Projective P)
local notation "FiniteFreeClass" => (fun P : ModuleCat R ↦ Module.Free R P ∧ Module.Finite R P)

/- Domain-style sampling for Lemma 15.65.5:
- primary domain: pseudo-coherence of cochain complexes via bounded-above finite-free and finite-
  projective models;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`,
  `CochainComplex.IsTermwiseFiniteFree`,
  `CochainComplex.MinusWithTermsIn`;
- best owner abstraction: the pseudo-coherence owners stay `K.IsMPseudoCoherent` and
  `K.IsPseudoCoherent`, while bounded-above model data should be carried by the existing owner
  `CochainComplex.MinusWithTermsIn` specialized to the finite-projective or finite-free term
  class, rather than by a parallel local wrapper that repeats boundedness and termwise membership;
- primitive vs. derived:
  primitive data are a bounded-above owner complex in `MinusWithTermsIn ...` and a quasi-
  isomorphism to the target complex;
  derived API is the TFAE and the bounded-above finite-free existence statement below;
- source/core/bridge triage:
  `source-facing`: the TFAE and the finite-free existence theorem;
  `core/canonical`: `K.IsMPseudoCoherent`, `K.IsPseudoCoherent`, and `MinusWithTermsIn`;
  `bridge/view`: the existential model clauses relating a cochain complex to a chosen owner
    complex in `MinusWithTermsIn`.
-/

-- Proof sketch: `(1) → (3)` is immediate because finite free modules are finite projective. For
-- `(3) → (1)`, replace each finite projective term by a finite free module using a direct-summand
-- argument to obtain a bounded-above finite-free complex that is still quasi-isomorphic to `K`.
-- Then `(1) → (2)` comes from stupid truncations of a bounded-above finite-free model, while
-- `(2) → (3)` is built by the descending-induction argument of the Stacks proof, using Lemmas
-- `15.65.2` and `15.65.3` to keep control of pseudo-coherence and finiteness at each step.
/-- Lemma 15.65.5: for a cochain complex `K^•` of `R`-modules, the following are equivalent:
`K^•` is pseudo-coherent, `K^•` is `m`-pseudo-coherent for every `m : ℤ`, and `K^•` is
quasi-isomorphic to a bounded-above cochain complex of finite projective `R`-modules. -/
theorem cochainComplex_pseudoCoherent_tfae
    (K : Cpx) :
    [K.IsPseudoCoherent,
      ∀ m : ℤ, K.IsMPseudoCoherent m,
      ∃ P : CochainComplex.MinusWithTermsIn FiniteProjectiveClass,
        ∃ α : (P : Cpx) ⟶ K, QuasiIso α].TFAE := sorry

-- Proof sketch: start from a bounded-above finite-free model of `K` given by pseudo-coherence and
-- descend from degree `b + 1`, extending the partial finite-free approximation one step at a time.
-- The cone of the partial map stays `(n - 1)`-pseudo-coherent by Lemma `15.65.2`, Lemma `15.65.3`
-- makes the relevant cohomology finite, and adjoining finitely many free generators yields the
-- next stage while keeping the complex zero above degree `b`.
/-- A pseudo-coherent cochain complex with vanishing cohomology above `b` admits a
quasi-isomorphic bounded-above termwise finite-free model concentrated in degrees `≤ b`. -/
theorem exists_boundedAbove_termwiseFiniteFree_quasiIso
    {K : Cpx} {b : ℤ}
    (hK : K.IsPseudoCoherent)
    (hvanish : ∀ i : ℤ, b < i → IsZero (K.homology i)) :
    ∃ F : CochainComplex.MinusWithTermsIn FiniteFreeClass,
      (F : Cpx).IsStrictlyLE b ∧
        ∃ α : (F : Cpx) ⟶ K, QuasiIso α := sorry

end
end

/-! ### Lemma_15_65_6 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for Lemma 15.65.6:
- primary domain: pseudo-coherent object properties in the derived category `D(R)` and their
  closure under distinguished triangles;
- sampled owner declarations:
  `DerivedCategory.IsPseudoCoherent`,
  `DerivedCategory.IsMPseudoCoherent`,
  `isMPseudoCoherent_obj₃_of_distinguishedTriangle`,
  `ObjectProperty.IsTriangulated`;
- best owner abstraction: the reusable owner statement is that the object property
  `fun K : DMod ↦ K.IsPseudoCoherent` is triangulated; the three numbered textbook statements are
  its source-facing `obj₁`/`obj₂`/`obj₃` consequences;
- primitive vs. derived:
  primitive data are the absolute notions `DerivedCategory.IsMPseudoCoherent` and
  `DerivedCategory.IsPseudoCoherent` from Definition `15.65.1`;
  the distinguished-triangle closure of `m`-pseudo-coherence from Lemma `15.65.2` is derived API,
  and this file upgrades it to pseudo-coherence;
- source/core/bridge triage:
  `source-facing`: the three numbered two-out-of-three statements below;
  `core/canonical`: `ObjectProperty.IsTriangulated (fun K : DMod ↦ K.IsPseudoCoherent)`;
  `bridge/view`: deriving the three source-facing consequences from that owner theorem.
- layer: this file keeps the source-facing statements but factors them through the canonical
  triangulated-object-property owner. -/

-- Proof sketch: choose any representative cochain complex of `K` in the derived category. Lemma
-- `15.65.5` characterizes pseudo-coherence of that representative by `m`-pseudo-coherence for all
-- integers `m`, and transport across the chosen isomorphism shows that this depends only on the
-- derived object `K`.
/-- Companion bridge for Lemma 15.65.6: a derived `R`-complex is pseudo-coherent exactly when it
is `m`-pseudo-coherent for every integer `m`. -/
theorem isPseudoCoherent_iff_forall_isMPseudoCoherent (K : DMod) :
    K.IsPseudoCoherent ↔ ∀ m : ℤ, K.IsMPseudoCoherent m := by
  sorry

instance isPseudoCoherent_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (fun K : DMod ↦ K.IsPseudoCoherent) where
  of_iso e hK := by
    rw [isPseudoCoherent_iff_forall_isMPseudoCoherent] at hK ⊢
    intro m
    let P : ObjectProperty DMod := fun K ↦ K.IsMPseudoCoherent m
    exact P.prop_of_iso e (hK m)

-- Proof sketch: combine Lemma `15.65.5`, which upgrades pseudo-coherence to
-- `m`-pseudo-coherence in every degree, with Lemma `15.65.2`, which gives the corresponding
-- two-out-of-three property for distinguished triangles degreewise in `m`. The resulting object
-- property is closed under isomorphisms by the previous instance, and the zero/shift axioms are
-- handled directly from the definition.
/-- Canonical owner form of Lemma 15.65.6: pseudo-coherent objects of `D(R)` form a triangulated
object property. -/
instance isPseudoCoherent_isTriangulated :
    ObjectProperty.IsTriangulated (fun K : DMod ↦ K.IsPseudoCoherent) := by
  sorry

-- Proof sketch: this is the `obj₁`-`obj₂` to `obj₃` closure consequence of the triangulated
-- object property instance on pseudo-coherent objects.
/-- Lemma 15.65.6 (1): in a distinguished triangle in `D(R)`, if the first and second terms are
pseudo-coherent, then the third term is pseudo-coherent. -/
theorem isPseudoCoherent_obj₃_of_distinguishedTriangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : T.obj₁.IsPseudoCoherent) (h₂ : T.obj₂.IsPseudoCoherent) :
    T.obj₃.IsPseudoCoherent := by
  let P : ObjectProperty DMod := fun K ↦ K.IsPseudoCoherent
  exact P.ext_of_isTriangulatedClosed₃ T hT h₁ h₂

-- Proof sketch: this is the `obj₁`-`obj₃` to `obj₂` closure consequence of the triangulated
-- object property instance on pseudo-coherent objects.
/-- Lemma 15.65.6 (2): in a distinguished triangle in `D(R)`, if the first and third terms are
pseudo-coherent, then the second term is pseudo-coherent. -/
theorem isPseudoCoherent_obj₂_of_distinguishedTriangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : T.obj₁.IsPseudoCoherent) (h₃ : T.obj₃.IsPseudoCoherent) :
    T.obj₂.IsPseudoCoherent := by
  let P : ObjectProperty DMod := fun K ↦ K.IsPseudoCoherent
  exact P.ext_of_isTriangulatedClosed₂ T hT h₁ h₃

-- Proof sketch: this is the `obj₂`-`obj₃` to `obj₁` closure consequence of the triangulated
-- object property instance on pseudo-coherent objects.
/-- Lemma 15.65.6 (3): in a distinguished triangle in `D(R)`, if the second and third terms are
pseudo-coherent, then the first term is pseudo-coherent. -/
theorem isPseudoCoherent_obj₁_of_distinguishedTriangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₂ : T.obj₂.IsPseudoCoherent) (h₃ : T.obj₃.IsPseudoCoherent) :
    T.obj₁.IsPseudoCoherent := by
  let P : ObjectProperty DMod := fun K ↦ K.IsPseudoCoherent
  exact P.ext_of_isTriangulatedClosed₁ T hT h₂ h₃

end

end CategoryTheory

/-! ### Lemma_15_65_7 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits

universe u

namespace CochainComplex

section

variable {R : Type u} [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

/- Domain-style sampling for Lemma 15.65.7:
- primary domain: recognition of `m`-pseudo-coherence for cochain complexes from cohomology
  vanishing and finiteness conditions on the top surviving cohomology objects;
- sampled owner declarations:
  `CochainComplex.IsMPseudoCoherent`,
  `homology_finite_of_isMPseudoCoherent`,
  `homology_finitePresentation_of_isMPseudoCoherent`,
  `DerivedCategory.IsLE`;
- best owner abstraction: the pseudo-coherence owner stays `K.IsMPseudoCoherent m`; the explicit
  cohomology-vanishing hypotheses below are source-facing bridge data rather than a second owner,
  and the canonical derived `t`-structure bound `((DerivedCategory.Q : Cpx ⥤ _).obj K).IsLE _`
  remains a downstream view;
- primitive vs. derived:
  primitive data are the cochain complex `K`, the homology vanishing ranges, and the finiteness
  / finite-presentation hypotheses on the surviving cohomology modules;
  derived API is the resulting `m`-pseudo-coherence conclusion, whose converse finiteness
  consequences already belong to Lemma `15.65.3`;
- source/core/bridge triage:
  `source-facing`: the three recognition statements below in textbook homology language;
  `core/canonical`: the owner predicate `K.IsMPseudoCoherent m`;
  `bridge/view`: the cohomology-vanishing input and the derived `IsLE` reformulation of that
    input, which should not replace the source-facing statements here.
-/

-- Proof sketch: apply part `(3)` below with `H^(m + 1)(K)` and `H^m(K)` both zero, using that the
-- zero `R`-module is finitely presented and finite.
/-- Lemma 15.65.7 (1): if a cochain complex `K^•` of `R`-modules has vanishing cohomology
in every degree `i ≥ m`, then `K^•` is `m`-pseudo-coherent. -/
theorem isMPseudoCoherent_of_homology_isZero_ge
    {K : Cpx} {m : ℤ}
    (hvanish : ∀ i : ℤ, m ≤ i → IsZero (K.homology i)) :
    K.IsMPseudoCoherent m := sorry

-- Proof sketch: use the finite generation of `H^m(K)` to choose a finite free cover onto the top
-- surviving cohomology, realize it as a map `E[-m] ⟶ K`, and note that all higher cohomology
-- vanishes, so this map gives the required `m`-pseudo-coherent approximation.
/-- Lemma 15.65.7 (2): if a cochain complex `K^•` of `R`-modules has vanishing cohomology
in every degree `i > m` and `H^m(K^•)` is finite, then `K^•` is `m`-pseudo-coherent. -/
theorem isMPseudoCoherent_of_homology_isZero_gt_and_finite
    {K : Cpx} {m : ℤ}
    (hvanish : ∀ i : ℤ, m < i → IsZero (K.homology i))
    (hm : Module.Finite R (K.homology m)) :
    K.IsMPseudoCoherent m := sorry

-- Proof sketch: replace `τ≥m+1 K` by the shift of `H^(m + 1)(K)` using the higher vanishing,
-- apply Lemma `15.65.4` to that shifted module complex, and use the truncation triangle together
-- with Lemma `15.65.2` to reduce to the previous case for `τ≤m K`.
/-- Lemma 15.65.7 (3): if a cochain complex `K^•` of `R`-modules has vanishing cohomology
in every degree `i > m + 1`, `H^(m + 1)(K^•)` is finitely presented, and `H^m(K^•)` is finite,
then `K^•` is `m`-pseudo-coherent. -/
theorem isMPseudoCoherent_of_homology_isZero_gt_add_one_and_finite
    {K : Cpx} {m : ℤ}
    (hvanish : ∀ i : ℤ, m + 1 < i → IsZero (K.homology i))
    (hm_succ : Module.FinitePresentation R (K.homology (m + 1)))
    (hm : Module.Finite R (K.homology m)) :
    K.IsMPseudoCoherent m := sorry

end

end CochainComplex

/-! ### Lemma_15_65_8 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ObjectProperty.IsStableUnderRetracts

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)

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
  of_retract h hK := by
    sorry

/-- Pseudo-coherent objects of `D(R)` are stable under retracts/direct summands. -/
-- Proof sketch: combine Lemma `15.65.5`, which characterizes pseudo-coherence by
-- `m`-pseudo-coherence for every `m`, with the retract-stability instance above applied degreewise.
instance isPseudoCoherent_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts (fun K : DMod ↦ K.IsPseudoCoherent) where
  of_retract h hK := by
    sorry

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

/-! ### Lemma_15_65_9 (from Chap15) -/
noncomputable section

open CategoryTheory
open ComplexShape

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CochainComplex

section

variable {R : Type u} [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

/- Domain-style sampling for Lemma 15.65.9:
- primary domain: pseudo-coherence of bounded-above cochain complexes of `R`-modules, with the
  source-facing hypotheses stated termwise on the underlying modules;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`,
  `CochainComplex.IsMPseudoCoherent`,
  `ModuleCat.IsMPseudoCoherent`,
  `CochainComplex.minus`;
- best owner abstraction: the chapter owners remain the existing predicates
  `CochainComplex.IsMPseudoCoherent` and `CochainComplex.IsPseudoCoherent`; this file is the
  source-facing bridge from termwise module pseudo-coherence plus the canonical bounded-above
  owner `CochainComplex.minus (ModuleCat R) K` to those owner predicates, and should not
  introduce any extra bounded-above wrapper or parallel pseudo-coherence API;
- primitive vs. derived:
  primitive data are the cochain complex `K`, the bounded-above hypothesis
  `CochainComplex.minus (ModuleCat R) K`,
  and the degreewise module hypotheses on `K.X i`;
  derived API is the resulting owner-level pseudo-coherence of `K`;
- source/core/bridge triage:
  `source-facing`: the two theorems below about bounded-above cochain complexes with termwise
    pseudo-coherent terms;
  `core/canonical`: `DerivedCategory.IsMPseudoCoherent`, `DerivedCategory.IsPseudoCoherent`,
    `CochainComplex.IsMPseudoCoherent`, `CochainComplex.IsPseudoCoherent`, and
    `CochainComplex.minus`;
  `bridge/view`: passage from the termwise module hypotheses on `K.X i` to the cochain-complex
    owner predicates. -/

-- Proof sketch: truncate the bounded-above complex far enough above degree `m` to reduce to a
-- bounded complex, then induct on the number of nonzero terms using stupid truncation triangles.
-- Apply Lemma `15.65.2` at each step, observing that the shifted single-term complex `K.X i[-i]`
-- is `m`-pseudo-coherent exactly when `K.X i` is `(m - i)`-pseudo-coherent.
/-- Lemma 15.65.9: a bounded-above cochain complex of `R`-modules whose term in degree `i` is
`(m - i)`-pseudo-coherent is `m`-pseudo-coherent. -/
theorem isMPseudoCoherent_of_boundedAbove_of_termwise
    (K : Cpx) (m : ℤ)
    (hbounded : CochainComplex.minus (ModuleCat R) K)
    (hterm : ∀ i : ℤ, (K.X i).IsMPseudoCoherent (m - i)) :
    K.IsMPseudoCoherent m := sorry

-- Proof sketch: for each fixed `m`, use the first theorem and the hypothesis that every term of
-- `K` is pseudo-coherent, hence `(m - i)`-pseudo-coherent for every `i`, and then invoke Lemma
-- `15.65.5` to pass from `m`-pseudo-coherence for all `m` to pseudo-coherence.
/-- A bounded-above cochain complex of pseudo-coherent `R`-modules is pseudo-coherent. -/
theorem isPseudoCoherent_of_boundedAbove_of_termwise
    (K : Cpx)
    (hbounded : CochainComplex.minus (ModuleCat R) K)
    (hterm : ∀ i : ℤ, (K.X i).IsPseudoCoherent) :
    K.IsPseudoCoherent := sorry

end

end CochainComplex

/-! ### Lemma_15_65_10 (from Chap15) -/
noncomputable section

open CategoryTheory
open DerivedCategory.TStructure

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "DModMinus" => boundedAboveDerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/- Domain-style sampling for Lemma 15.65.10:
- primary domain: pseudo-coherence of bounded-above derived `R`-complexes from degreewise
  pseudo-coherence of their cohomology modules;
- sampled owner declarations:
  `boundedAboveDerivedCategory`,
  `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`,
  `DerivedCategory.homologyFunctor`;
- best owner abstraction: bounded-above complexes should be carried by the chapter owner
  `boundedAboveDerivedCategory (ModuleCat R)` rather than by a separate membership proof in
  `t.minus`;
- primitive vs. derived:
  primitive data are the bounded-above derived object `K : DModMinus` and the degreewise
  cohomology hypotheses;
  derived API is the resulting owner conclusions `K.obj.IsMPseudoCoherent m` and
  `K.obj.IsPseudoCoherent`;
- source/core/bridge triage:
  `source-facing`: the bounded-above cohomology criteria below;
  `core/canonical`: `DModMinus`, `K.IsMPseudoCoherent`, `K.IsPseudoCoherent`, and
    `DerivedCategory.homologyFunctor`;
  `bridge/view`: reading the cohomology hypotheses via `K.obj` in the ambient unbounded derived
    category.
-/

-- Proof sketch: choose a bounded-above representative for `K` and induct on the largest degree
-- with nonvanishing cohomology. If this degree is `< m`, apply Lemma `15.65.7`; otherwise use the
-- truncation triangle with top cohomology `H^n(K)[-n]`, note that the hypothesis makes this shift
-- `m`-pseudo-coherent, and reduce to the lower truncation via Lemma `15.65.2`.
/-- Lemma 15.65.10: if `K` is a bounded-above derived `R`-complex and every cohomology module
`H^i(K)` is `(m - i)`-pseudo-coherent, then `K` is `m`-pseudo-coherent. -/
theorem boundedAbove_isMPseudoCoherent_of_homology
    (K : DModMinus) (m : ℤ)
    (hH : ∀ i : ℤ, ((H i).obj K.obj).IsMPseudoCoherent (m - i)) :
    K.obj.IsMPseudoCoherent m := sorry

-- Proof sketch: apply the previous theorem for each integer `m`, using that a pseudo-coherent
-- module is `(m - i)`-pseudo-coherent for every `i`, and conclude with the characterization of
-- pseudo-coherence from Lemma `15.65.5`.
/-- If every cohomology module of a bounded-above derived `R`-complex is pseudo-coherent, then the
complex itself is pseudo-coherent. -/
theorem boundedAbove_isPseudoCoherent_of_homology
    (K : DModMinus)
    (hH : ∀ i : ℤ, ((H i).obj K.obj).IsPseudoCoherent) :
    K.obj.IsPseudoCoherent := sorry

end

end CategoryTheory

/-! ### Lemma_15_65_11 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [Ring A] [Ring B] (f : A →+* B)

local notation "DModB" => DerivedCategory (ModuleCat B)

/- Domain-style sampling for Lemma 15.65.11:
- primary domain: pseudo-coherence in derived categories under restriction of scalars along
  a ring hom `f : A →+* B`;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`,
  `ModuleCat.IsPseudoCoherent`,
  `ModuleCat.restrictScalars`,
  `restrictScalars_exact`,
  `CategoryTheory.Functor.mapDerivedCategory`;
- best owner abstraction: the source-facing content is the pair of comparison theorems below,
  while the restriction construction itself is owned canonically by the exact derived functor
  `(ModuleCat.restrictScalars f).mapDerivedCategory`; this file should reuse that owner directly
  rather than keep an `Algebra`-specific wrapper;
- primitive vs. derived:
  primitive data are the ring map `f`, the derived `B`-complex `K`, and the pseudo-coherence
  hypothesis on the restricted module object `((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))`;
  derived API is the equivalence between the absolute pseudo-coherence owners on `K` and on its
  image under the canonical restriction functor;
- source/core/bridge triage:
  `source-facing`: `isMPseudoCoherent_iff_restrictScalars`,
    `isPseudoCoherent_iff_restrictScalars`;
  `core/canonical`: `DerivedCategory.IsMPseudoCoherent`,
    `DerivedCategory.IsPseudoCoherent`, `ModuleCat.IsPseudoCoherent`,
    `ModuleCat.restrictScalars`, `restrictScalars_exact`, and
    `Functor.mapDerivedCategory`;
  `bridge/view`: restriction of scalars along `f` via
    `(ModuleCat.restrictScalars f).mapDerivedCategory`.
-/

local instance restrictScalars_preservesFiniteLimits :
    Limits.PreservesFiniteLimits (ModuleCat.restrictScalars.{u} f) :=
  ((exactFunctor_iff (ModuleCat.restrictScalars.{u} f)).1 (restrictScalars_exact f)).1

-- Proof sketch: for `→`, view a bounded finite-free `B`-model for `K` termwise as a bounded-above
-- complex of pseudo-coherent `A`-modules using the hypothesis that `B` is pseudo-coherent over
-- `A` after restriction of scalars along `f`, then apply Lemma `15.65.9` and the
-- distinguished-triangle criterion of Lemma
-- `15.65.2`. For `←`, start from an `A`-linear approximation of the restricted complex, tensor it with `B`,
-- and descend on the top nonvanishing cohomology degree exactly as in the Stacks Project proof.
/-- Lemma 15.65.11: if `f : A →+* B` is a ring map and `B` is pseudo-coherent as an `A`-module,
then a
derived `B`-complex is `m`-pseudo-coherent exactly when its restriction of scalars to `A` is
`m`-pseudo-coherent. -/
theorem isMPseudoCoherent_iff_restrictScalars
    (K : DModB) (m : ℤ)
    (hB : ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)).IsPseudoCoherent) :
    K.IsMPseudoCoherent m ↔
      ((ModuleCat.restrictScalars f).mapDerivedCategory.obj K).IsMPseudoCoherent m := sorry

-- Proof sketch: apply `isMPseudoCoherent_iff_restrictScalars` for every `m : ℤ` and use the
-- characterization of pseudo-coherence as `m`-pseudo-coherence for all `m` from Lemma `15.65.5`
-- on both the `B`-linear complex and its restriction to `A`.
/-- Under the same hypothesis on `B`, pseudo-coherence of a derived `B`-complex is equivalent to
pseudo-coherence after restriction of scalars to `A`. -/
theorem isPseudoCoherent_iff_restrictScalars
    (K : DModB)
    (hB : ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)).IsPseudoCoherent) :
    K.IsPseudoCoherent ↔
      ((ModuleCat.restrictScalars f).mapDerivedCategory.obj K).IsPseudoCoherent := sorry

end

end CategoryTheory

/-! ### Lemma_15_65_12 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.65.12:
- primary domain: derived scalar extension on module derived categories and preservation of
  pseudo-coherence;
- sampled owner declarations:
  `derivedTensorWithAlgebra`,
  `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`,
  `CochainComplex.IsTermwiseFiniteFree`;
- best owner abstraction: the core/canonical owner is the derived scalar-extension functor
  `derivedTensorWithAlgebra (algebraMap A B) : D(A) ⥤ D(B)`, with pseudo-coherence carried by the existing
  `DerivedCategory` predicates rather than any local wrapper;
- primitive vs. derived:
  primitive data are the ring map `A → B` and the pseudo-coherence witness on `K`;
  the preservation statements below are derived API over that owner;
- source/core/bridge triage:
  `source-facing`: scalar extension preserves `m`-pseudo-coherence and pseudo-coherence;
  `core/canonical`: `derivedTensorWithAlgebra` and the `DerivedCategory` pseudo-coherence owners;
  `bridge/view`: the notation `K ⊗[A]^L[B]` for the owner applied to an object.
- layer: this file is source-facing over canonical owners, so the theorem surface should use the
  existing owner notation instead of repeating raw functor application terms. -/

-- Proof sketch: choose a bounded finite-free approximation of `K` as in the definition of
-- `m`-pseudo-coherence, apply derived scalar extension to the comparison map, and use that
-- tensoring a finite free complex with `B` stays finite free over `B`, while the cone stays
-- acyclic in degrees `≥ m`.
/-- Lemma 15.65.12: derived extension of scalars along `A → B` preserves `m`-pseudo-coherent
objects of `D(A)`. -/
theorem derivedTensorWithAlgebra_isMPseudoCoherent
    (K : DModA) (m : ℤ) (hK : K.IsMPseudoCoherent m) :
    (K ⊗[A]^L[B]).IsMPseudoCoherent m := sorry

-- Proof sketch: rewrite pseudo-coherence as `m`-pseudo-coherence for all `m` using the canonical
-- owner theorem `isPseudoCoherent_iff_forall_isMPseudoCoherent`, then apply part `(1)` degreewise.
/-- Derived extension of scalars along `A → B` preserves pseudo-coherent objects of `D(A)`. -/
theorem derivedTensorWithAlgebra_isPseudoCoherent
    (K : DModA) (hK : K.IsPseudoCoherent) :
    (K ⊗[A]^L[B]).IsPseudoCoherent := by
  rw [isPseudoCoherent_iff_forall_isMPseudoCoherent] at hK ⊢
  intro m
  simpa using derivedTensorWithAlgebra_isMPseudoCoherent K m (hK m)

end

end CategoryTheory

/-! ### Lemma_15_65_13 (from Chap15) -/
noncomputable section

universe u

open CategoryTheory
open scoped DerivedTensorWithAlgebra

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "Ext" => ModuleCat.extendScalars (algebraMap A B)

/- Domain-style sampling for Lemma 15.65.13:
- primary domain: pseudo-coherent modules under flat scalar extension, viewed through their
  degree-zero images in the derived category;
- sampled owner declarations:
  `ModuleCat.single0Functor`,
  `DerivedCategory.IsMPseudoCoherent`,
  `derivedTensorWithAlgebra_isMPseudoCoherent`,
  `derivedTensorWithAlgebra_isPseudoCoherent`;
- best owner abstraction: the core/canonical owner is derived scalar extension
  `derivedTensorWithAlgebra A B : D(A) ⥤ D(B)`, while the module-level theorems below are flat
  `bridge/view` consequences obtained only after identifying `M[0] ⊗[A]^L B` with ordinary scalar
  extension of `M` in degree `0`;
- primitive vs. derived:
  primitive data are the ring map `A → B`, the flatness hypothesis, and the module `M` viewed as
  `(ModuleCat.single0Functor : ModuleCat A ⥤ DerivedCategory (ModuleCat A)).obj M : D(A)`;
  the ordinary module pseudo-coherence conclusions are derived API obtained from the owner
  theorems in Lemma `15.65.12` plus the flat degree-zero comparison;
- layer: `bridge/view`. The public statement should therefore be a flat bridge from the derived
  owner theorem, not an arbitrary ordinary base-change theorem. -/

-- Proof sketch: `M.IsMPseudoCoherent m` is definitionally `m`-pseudo-coherence of the degree-zero
-- owner object `(ModuleCat.single0Functor.obj M)`. Apply
-- `derivedTensorWithAlgebra_isMPseudoCoherent`, then use flatness of `A → B` to identify the
-- derived base change of that degree-zero object with the degree-zero object of `Ext.obj M`.
/-- Lemma 15.65.13: for a flat ring map `A → B`, if an `A`-module `M` is `m`-pseudo-coherent,
then its scalar extension `M \otimes_A B` is `m`-pseudo-coherent as a `B`-module. -/
theorem isMPseudoCoherent_extendScalars
    (hflat : (algebraMap A B).Flat) (M : ModuleCat A) (m : ℤ)
    (hM : M.IsMPseudoCoherent m) :
    ((Ext).obj M).IsMPseudoCoherent m := sorry

-- Proof sketch: apply the previous theorem for every `m : ℤ`, or equivalently specialize
-- `derivedTensorWithAlgebra_isPseudoCoherent` and use the same flat degree-zero identification.
/-- For a flat ring map `A → B`, ordinary scalar extension preserves pseudo-coherent modules. -/
theorem isPseudoCoherent_extendScalars
    (hflat : (algebraMap A B).Flat) (M : ModuleCat A)
    (hM : M.IsPseudoCoherent) :
    ((Ext).obj M).IsPseudoCoherent := sorry

end

end CategoryTheory

/-! ### Lemma_15_65_14 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
variable {ι : Type*} [Finite ι]

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for Lemma 15.65.14:
- primary domain: descent of pseudo-coherence in `D(R)` from a finite principal-open cover;
- sampled owner-level declarations:
  `Module.FinitePresentationRelativeTo.iff_localizationAway_unitIdeal`,
  `quotient_torsionBy_fintypeLinearCombination_surjective_of_presentation_minorIdeal_eq_span_singleton`,
  and the underlying finite-family owner `Fintype.linearCombination`;
- best owner abstraction: this item stays `source-facing`, but its covering data should be an
  arbitrary finite family `f : ι → R`, not the coordinate model `Fin r → R`;
- primitive data: the family `f`, the unit-ideal hypothesis `Ideal.span (Set.range f) = ⊤`, and
  the localized pseudo-coherence hypotheses;
- derived API: the descent conclusions for `m`-pseudo-coherence and pseudo-coherence. -/

-- Proof sketch: use the finite principal-open cover `D(f i)` of `Spec R` coming from
-- `Ideal.span (Set.range f) = ⊤`. Descend the bounded finite-projective approximation from each
-- localization and glue the finite top cohomology modules by the standard local criterion for
-- finite generation, then induct on the highest nonvanishing cohomological degree as in the
-- Stacks proof.
/-- Lemma 15.65.14 (1): if the finite family `f : ι → R` generates the unit ideal and each
localization of `K` away from `f i` is `m`-pseudo-coherent, then `K` is `m`-pseudo-coherent. -/
theorem isMPseudoCoherent_of_localizationAway_unitIdeal
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤) (K : DMod) (m : ℤ)
    (hloc : ∀ i, (K ⊗[R]^L[Localization.Away (f i)]).IsMPseudoCoherent m) :
    K.IsMPseudoCoherent m := sorry

/-- Combining Lemma `15.65.14 (1)` with scalar-extension preservation, `m`-pseudo-coherence is
local for finite principal-open covers of `Spec R`. -/
theorem isMPseudoCoherent_iff_localizationAway_unitIdeal
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤) (K : DMod) (m : ℤ) :
    (∀ i, (K ⊗[R]^L[Localization.Away (f i)]).IsMPseudoCoherent m) ↔
      K.IsMPseudoCoherent m := by
  constructor
  · exact isMPseudoCoherent_of_localizationAway_unitIdeal f hunit K m
  · intro hK i
    exact derivedTensorWithAlgebra_isMPseudoCoherent K m hK

-- Proof sketch: pseudo-coherence means `m`-pseudo-coherence for every `m`. Apply part `(1)` to
-- each integer `m`, using the localized pseudo-coherence hypotheses, and then invoke the standard
-- characterization of pseudo-coherence by uniform `m`-pseudo-coherence.
/-- Lemma 15.65.14 (2): if the finite family `f : ι → R` generates the unit ideal and each
localization of `K` away from `f i` is pseudo-coherent, then `K` is pseudo-coherent. -/
theorem isPseudoCoherent_of_localizationAway_unitIdeal
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤) (K : DMod)
    (hloc : ∀ i, (K ⊗[R]^L[Localization.Away (f i)]).IsPseudoCoherent) :
    K.IsPseudoCoherent := sorry

/-- Combining Lemma `15.65.14 (2)` with scalar-extension preservation, pseudo-coherence is local
for finite principal-open covers of `Spec R`. -/
theorem isPseudoCoherent_iff_localizationAway_unitIdeal
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤) (K : DMod) :
    (∀ i, (K ⊗[R]^L[Localization.Away (f i)]).IsPseudoCoherent) ↔
      K.IsPseudoCoherent := by
  constructor
  · exact isPseudoCoherent_of_localizationAway_unitIdeal f hunit K
  · intro hK i
    exact derivedTensorWithAlgebra_isPseudoCoherent K hK

end

end CategoryTheory

/-! ### Lemma_15_65_15 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R R' : Type u} [CommRing R] [CommRing R']

local notation "DModR" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for Lemma 15.65.15:
- primary domain: faithful-flat descent of pseudo-coherence in derived categories of modules;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`,
  `derivedTensorWithAlgebra`,
  `isPseudoCoherent_iff_forall_isMPseudoCoherent`;
- best owner abstraction: this file is `source-facing`, so the public descent statements should be
  organized around the actual ring map `f : R →+* R'`; the `core/canonical` owners remain the
  Chapter 15 predicates `K.IsMPseudoCoherent` and `K.IsPseudoCoherent` on `D(R)`, together with
  the derived scalar-extension owner `derivedTensorWithAlgebra f`, while the chapter base-change
  notation `K ⊗[R]^L[R']` remains the bridge view after passing from `f` to `f.toAlgebra`;
- primitive vs. derived:
  primitive data are the ring map `f`, the derived object `K`, the faithfully flatness of `f`,
  and the pseudo-coherence of the derived base change along `f`;
  the descent statements below are derived API over those owners, so there should be no parallel
  wrapper notion for faithful-flat descent itself;
- source/core/bridge triage:
  `source-facing`: descent of `m`-pseudo-coherence and pseudo-coherence;
  `core/canonical`: `DerivedCategory.IsMPseudoCoherent`,
    `DerivedCategory.IsPseudoCoherent`, and `derivedTensorWithAlgebra`;
  `bridge/view`: the chapter notation `K ⊗[R]^L[R']` for derived scalar extension along the
    explicit ring map `f`.

This file therefore keeps the source-facing descent theorems, but its public surface should stay
entirely on the existing owner predicates and the canonical scalar-extension owner notation, with
the ring map kept explicit rather than hidden in an ambient algebra instance.
-/

-- Proof sketch: use faithful flatness to reflect the vanishing range of cohomology from the
-- base-changed derived complex back to `K`, descend finiteness of the top surviving cohomology by
-- faithful-flat descent for modules, and then run the downward induction on the largest nonzero
-- cohomological degree as in the Stacks proof, applying Lemmas `15.65.7`, `15.65.3`, and
-- `15.65.2` to the cone construction.
/-- Lemma 15.65.15 (1): if the faithfully flat derived base change of a derived `R`-complex `K`
along a faithfully flat ring map `f : R →+* R'` is `m`-pseudo-coherent, then `K` is
`m`-pseudo-coherent. -/
theorem isMPseudoCoherent_of_faithfullyFlat_baseChange
    (f : R →+* R') (K : DModR) (m : ℤ)
    (hff : f.FaithfullyFlat)
    (hK : ((derivedTensorWithAlgebra f).obj K).IsMPseudoCoherent m) :
    K.IsMPseudoCoherent m := sorry

-- Proof sketch: apply part `(1)` for every integer `m` and then use the canonical owner theorem
-- `isPseudoCoherent_iff_forall_isMPseudoCoherent`.
/-- Lemma 15.65.15 (2): if the faithfully flat derived base change of a derived `R`-complex `K`
along a faithfully flat ring map `f : R →+* R'` is pseudo-coherent, then `K` is
pseudo-coherent. -/
theorem isPseudoCoherent_of_faithfullyFlat_baseChange
    (f : R →+* R') (K : DModR)
    (hff : f.FaithfullyFlat)
    (hK : ((derivedTensorWithAlgebra f).obj K).IsPseudoCoherent) :
    K.IsPseudoCoherent := by
  rw [isPseudoCoherent_iff_forall_isMPseudoCoherent] at hK ⊢
  intro m
  exact isMPseudoCoherent_of_faithfullyFlat_baseChange f K m hff (hK m)

end

end CategoryTheory

/-! ### Lemma_15_65_16 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/- Domain-style sampling for Lemma 15.65.16:
- primary domain: pseudo-coherence in `D(R)` and its behavior under the Chapter 15 derived tensor
  product owner;
- sampled owner declarations:
  `CategoryTheory.derivedTensorProduct`,
  `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`,
  `DerivedCategory.homologyFunctor`;
- best owner abstraction: this file is `source-facing`, but its statements should stay directly on
  the canonical owners `K.IsMPseudoCoherent`, `K.IsPseudoCoherent`, the tensor notation
  `K ⊗[R]^L L`, and the homology functor owner `H`;
- primitive vs. derived:
  primitive data are the objects `K`, `L`, the bounds `n m a b`, and the homology-vanishing
  assumptions;
  derived API is the preservation of `m`-pseudo-coherence and pseudo-coherence under the canonical
  tensor owner.
-/

-- Proof sketch: choose bounded-above finite-projective models for `K` and `L` with the stated
-- cohomological control, compute the derived tensor product by the total tensor complex of these
-- models, and use the Tor spectral sequence to obtain isomorphisms above
-- `max (m + a) (n + b)` together with surjectivity in that degree.
/-- Lemma 15.65.16 (1): if `K` is `n`-pseudo-coherent with vanishing cohomology in degrees
strictly above `a`, and `L` is `m`-pseudo-coherent with vanishing cohomology in degrees strictly
above `b`, then `K ⊗[R]^L L` is `max (m + a) (n + b)`-pseudo-coherent. -/
theorem derivedTensorProduct_isMPseudoCoherent_of_isMPseudoCoherent_of_vanishingAbove
    (K L : DMod) (n m a b : ℤ)
    (hK : K.IsMPseudoCoherent n)
    (hKvanish : ∀ i : ℤ, a < i → IsZero ((H i).obj K))
    (hL : L.IsMPseudoCoherent m)
    (hLvanish : ∀ j : ℤ, b < j → IsZero ((H j).obj L)) :
    (K ⊗[R]^L L).IsMPseudoCoherent (max (m + a) (n + b)) := sorry

-- Proof sketch: by Lemma `15.65.5`, pseudo-coherent objects admit bounded-above termwise finite
-- projective models, so they satisfy the hypotheses of part `(1)` for suitable cohomological
-- bounds; applying part `(1)` then yields pseudo-coherence of the derived tensor product.
/-- Lemma 15.65.16 (2): if `K` and `L` are pseudo-coherent, then
`K ⊗[R]^L L` is pseudo-coherent. -/
theorem derivedTensorProduct_isPseudoCoherent_of_isPseudoCoherent
    (K L : DMod)
    (hK : K.IsPseudoCoherent)
    (hL : L.IsPseudoCoherent) :
    (K ⊗[R]^L L).IsPseudoCoherent := sorry

end

end CategoryTheory

/-! ### Lemma_15_65_17 (from Chap15) -/
noncomputable section

open CategoryTheory
open DerivedCategory.TStructure

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R] [IsNoetherianRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "BoundedAbove" => (t.minus : ObjectProperty DMod)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/- Domain-style sampling for Lemma 15.65.17:
- primary domain: pseudo-coherence in the derived category of modules over a Noetherian ring and
  its degree-zero module specialization;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`,
  `boundedAboveDerivedCategory`,
  `ModuleCat.IsPseudoCoherent`;
- best owner abstraction: the source-facing statements in parts `(1)` and `(2)` stay on the
  chapter owners `K.IsMPseudoCoherent` and `K.IsPseudoCoherent`, while the module theorem in part
  `(3)` should use the ordinary unbundled module bridge surface rather than a parallel bundled
  `ModuleCat`-only theorem;
- primitive vs. derived:
  primitive data are the derived owner predicates and the bounded-above owner subcategory from
  Lemma `15.65.10`;
  derived API is the bounded-above finite-homology characterization below, together with the
  degree-zero module bridge in part `(3)`;
- source/core/bridge triage:
  `source-facing`: the three numbered criteria of Lemma `15.65.17`;
  `core/canonical`: `K.IsMPseudoCoherent`, `K.IsPseudoCoherent`, and
    `boundedAboveDerivedCategory (ModuleCat R)`;
  `bridge/view`: the ordinary module surface `(ModuleCat.of R M).IsPseudoCoherent`.
-/

-- Proof sketch: for the forward implication, use the bounded-above finite-free approximation in
-- the definition of `m`-pseudo-coherence to see that `K` lies in `D^-(R)` and that the cohomology
-- groups in degrees `i ≥ m` are finite. For the reverse implication, combine the bounded-above
-- hypothesis with the finiteness of `H^i(K)` for `i ≥ m`, use that finite modules are
-- pseudo-coherent over a Noetherian ring, and apply Lemma `15.65.10`.
/-- Lemma 15.65.17 (1): a derived `R`-complex is `m`-pseudo-coherent exactly when it lies in
`D^-(R)` and its cohomology modules `H^i` are finite for all `i ≥ m`. -/
theorem isMPseudoCoherent_iff_boundedAbove_and_homology_finite_ge
    (K : DMod) (m : ℤ) :
    K.IsMPseudoCoherent m ↔
      BoundedAbove K ∧
        ∀ i : ℤ, m ≤ i → Module.Finite R ((H i).obj K) := sorry

-- Proof sketch: apply part `(1)` for every integer `m`. If `K` is pseudo-coherent, then it is
-- `m`-pseudo-coherent for all `m`; conversely, bounded-above together with finiteness of every
-- cohomology module makes each cohomology module pseudo-coherent over a Noetherian ring, so
-- Lemma `15.65.10` yields `m`-pseudo-coherence for every `m`, hence pseudo-coherence.
/-- Lemma 15.65.17 (2): a derived `R`-complex is pseudo-coherent exactly when it lies in `D^-(R)`
and all of its cohomology modules are finite. -/
theorem isPseudoCoherent_iff_boundedAbove_and_homology_finite
    (K : DMod) :
    K.IsPseudoCoherent ↔
      BoundedAbove K ∧
        ∀ i : ℤ, Module.Finite R ((H i).obj K) := sorry

end

section

variable {R : Type u} [Ring R] [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

-- Proof sketch: over a Noetherian ring, every finite module is pseudo-coherent and every
-- pseudo-coherent module is finite. Translate the module into the derived category concentrated in
-- degree `0` and combine these two implications with the module-level definition of
-- pseudo-coherence.
/-- Lemma 15.65.17 (3): an `R`-module is pseudo-coherent exactly when it is finite. -/
theorem _root_.Module.isPseudoCoherent_iff_finite :
    (ModuleCat.of R M).IsPseudoCoherent ↔ Module.Finite R M := sorry

end

end CategoryTheory

/-! ### Lemma_15_65_18 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} [Ring R] [Module.Coherent R R]
variable {M : Type u} [AddCommGroup M] [Module R M]

-- Domain sampling:
-- * primary domain: pseudo-coherence for bounded-above derived complexes of `R`-modules over a
--   coherent ring;
-- * sampled owner API: `DerivedCategory.IsMPseudoCoherent`, `DerivedCategory.IsPseudoCoherent`,
--   `DerivedCategory.homologyFunctor`, `boundedAbove_isMPseudoCoherent_of_homology`,
--   `isPseudoCoherent_iff_forall_isMPseudoCoherent`,
--   `moduleCat_isMinusOnePseudoCoherent_iff_finitePresentation`, and
--   `module_coherent_iff_finitePresentation`;
-- * layer triage: the source-facing statements below reformulate the canonical derived-category
--   owners in terms of cohomology coherence / finite presentation, so the bounded-above complex is
--   primitive data while the cohomology predicates are derived companion views.
local notation "DModMinus" => boundedAboveDerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

-- Degree-zero bridge: over a coherent ring, pseudo-coherent modules are exactly coherent modules.
-- The forward implication factors through finite presentation via Lemma `15.65.4` and
-- Lemma `10.90.4`; the reverse implication is the reusable module-level input for the bounded-above
-- homology criterion below.
/-- Over a coherent ring, an `R`-module is pseudo-coherent exactly when it is coherent. -/
theorem _root_.Module.isPseudoCoherent_iff_coherent :
    (ModuleCat.of R M).IsPseudoCoherent ↔ Module.Coherent R M := sorry

-- Proof sketch: the second and third conditions differ only by Lemma `10.90.4`, which identifies
-- coherent and finitely presented modules over a coherent ring. For the implication to
-- `m`-pseudo-coherence, first use that coherent modules over a coherent ring are pseudo-coherent,
-- upgrade this to all `m` with `isPseudoCoherent_iff_forall_isMPseudoCoherent`, and then apply
-- `boundedAbove_isMPseudoCoherent_of_homology`; the finiteness of `H^m(K)` is the degree-`m`
-- clause recorded separately in the source statement.
/-- Lemma 15.65.18: for a bounded-above derived `R`-complex over a coherent ring, the following
are equivalent: `K` is `m`-pseudo-coherent; `H^m(K)` is finite and all higher cohomology modules
are coherent; and `H^m(K)` is finite and all higher cohomology modules are finitely presented. -/
theorem boundedAbove_isMPseudoCoherent_tfae_of_coherentRing
    (K : DModMinus) (m : ℤ) :
    ([ K.obj.IsMPseudoCoherent m
      , Module.Finite R ((H m).obj K.obj) ∧
          ∀ i : ℤ, m < i → Module.Coherent R ((H i).obj K.obj)
      , Module.Finite R ((H m).obj K.obj) ∧
          ∀ i : ℤ, m < i → Module.FinitePresentation R ((H i).obj K.obj)
      ] : List Prop).TFAE := sorry

-- Proof sketch: apply the previous equivalence for every `m`. If `K` is pseudo-coherent, then it
-- is `m`-pseudo-coherent for all `m`, so each cohomology module is coherent. Conversely, if every
-- cohomology module is coherent, then for each `m` the second clause of the previous theorem
-- holds, so `K` is `m`-pseudo-coherent for every `m`; now use the canonical owner theorem
-- `isPseudoCoherent_iff_forall_isMPseudoCoherent` to recover `K.obj.IsPseudoCoherent`.
/-- A bounded-above derived complex over a coherent ring is pseudo-coherent exactly when all of
its cohomology modules are coherent. -/
theorem boundedAbove_isPseudoCoherent_iff_homology_coherent
    (K : DModMinus) :
    K.obj.IsPseudoCoherent ↔
      ∀ i : ℤ, Module.Coherent R ((H i).obj K.obj) := sorry

end
