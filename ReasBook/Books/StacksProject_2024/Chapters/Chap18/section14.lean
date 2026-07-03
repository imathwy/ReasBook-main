import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_18_14_1 (from Chap18) -/
import Mathlib.CategoryTheory.Limits.ExactFunctor

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J RingCat.{u})

/- Domain-style sampling for Lemma 18.14.1:
- primary domain: sheaves of modules on a Grothendieck site, together with exact functors between
  abelian categories and the generic kernel/cokernel comparison isomorphisms attached to a
  functor that preserves finite (co)limits;
- sampled owner declarations:
  `SheafOfModules.toSheaf`,
  `exactFunctor`,
  `PreservesKernel.iso`,
  `PreservesCokernel.iso`;
- best owner abstraction: the canonical owner category `SheafOfModules 𝒪` together with the
  bridge/view functor `SheafOfModules.toSheaf 𝒪` to sheaves of abelian groups;
- primitive-vs-derived split:
  the primitive data are only the ambient site, the ring-valued sheaf `𝒪`, and the canonical
  forgetful functor `SheafOfModules.toSheaf 𝒪`;
  abelianness of `SheafOfModules 𝒪` and the kernel/cokernel comparison isomorphisms already live
  upstream, while the source-facing content here is the exactness of `SheafOfModules.toSheaf 𝒪`
  and the resulting exactness comparison for short complexes.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma asserting that `Mod(𝒪)` is abelian and that the forgetful
  functor to abelian sheaves is exact, plus the exactness comparison for short complexes;
- `core/canonical`: the owner category `SheafOfModules 𝒪`, the canonical bridge functor
  `SheafOfModules.toSheaf 𝒪`, and the generic declarations `exactFunctor`,
  `PreservesKernel.iso`, and `PreservesCokernel.iso`;
- `bridge/view`: the theorem `moduleSheaf_exact_iff_underlyingAbelian_exact`, which compares
  exactness in `Mod(𝒪)` with exactness after applying the canonical forgetful functor.

The two comparison isomorphisms are already owned upstream by `PreservesKernel.iso` and
`PreservesCokernel.iso`, so this file should not keep parallel public abbreviations for them.
-/

/- Lemma 18.14.1 (1): the category `Mod(𝒪)` of sheaves of `𝒪`-modules is abelian. This is the
canonical mathlib instance on `SheafOfModules 𝒪`. -/
#synth Abelian (SheafOfModules 𝒪)

section Exactness

variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Forgetting the module structure on sheaves preserves finite colimits. -/
private noncomputable instance moduleSheafToSheaf_preservesFiniteColimits :
    PreservesFiniteColimits (SheafOfModules.toSheaf 𝒪) := sorry

-- Proof sketch: `SheafOfModules 𝒪` is abelian by the owner API, and
-- `SheafOfModules.toSheaf 𝒪` already preserves finite limits. Together with the finite-colimit
-- preservation above, this is exactly the bundled notion of an exact functor.
/-- Lemma 18.14.1: for a ringed topos `(Sh(𝒞), 𝒪)`, the category `Mod(𝒪)` of sheaves of
`𝒪`-modules is abelian, and the forgetful functor to abelian sheaves is exact. -/
theorem moduleSheaf_toSheaf_exact :
    exactFunctor (SheafOfModules 𝒪) (Sheaf J AddCommGrpCat.{u})
      (SheafOfModules.toSheaf 𝒪) := sorry

-- Proof sketch: use the exactness of `SheafOfModules.toSheaf 𝒪`; exact functors preserve exact
-- short complexes, and for this forgetful functor the kernel-cokernel comparison identifies the
-- exactness condition with the one in abelian sheaves.
/-- Exactness of a short complex of `𝒪`-module sheaves agrees with exactness of the underlying
short complex of abelian sheaves. -/
theorem moduleSheaf_exact_iff_underlyingAbelian_exact
    (S : ShortComplex (SheafOfModules 𝒪)) :
    S.Exact ↔ (S.map (SheafOfModules.toSheaf 𝒪)).Exact := sorry

/- Companion recall: the kernel comparison for `SheafOfModules.toSheaf 𝒪` is the canonical
generic isomorphism `PreservesKernel.iso`. -/
#check PreservesKernel.iso (SheafOfModules.toSheaf 𝒪)

/- Companion recall: the cokernel comparison for `SheafOfModules.toSheaf 𝒪` is the canonical
generic isomorphism `PreservesCokernel.iso`. -/
#check PreservesCokernel.iso (SheafOfModules.toSheaf 𝒪)

end Exactness

/-! ### Lemma_18_14_2 (from Chap18) -/
open CategoryTheory Limits

noncomputable section

universe u v

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J RingCat.{max u v})

/- Domain-style sampling for Lemma 18.14.2:
- primary domain: categorical completeness, cocompleteness, and Grothendieck-axiom structure for
  sheaves of modules on a ringed site;
- inspected owner declarations:
  `Mod`,
  `SheafOfModules`,
  `SheafOfModules.toSheaf`,
  the canonical `HasLimitsOfSize` / `HasColimitsOfSize` instances on `SheafOfModules 𝒪`,
  `CategoryTheory.Sheaf.ab5ofSize`;
- best owner abstraction: the source-facing owner notation `Mod(𝒪)` on top of the canonical owner
  `SheafOfModules 𝒪`, together with the canonical bridge functor `SheafOfModules.toSheaf 𝒪` to
  sheaves of abelian groups;
- primitive-vs-derived split:
  the primitive data are only the sheaf of rings `𝒪` and the canonical forgetful bridge
  `SheafOfModules.toSheaf 𝒪`;
  all limit, colimit, and `AB5` assertions are derived owner-level API, so the public surface
  should use `Mod(𝒪)` plus anonymous owner instances rather than parallel named wrappers.

Source/core/bridge triage:
- `source-facing`: the Stacks assertions that `Mod(𝒪)` has limits and colimits and that filtered
  colimits are exact;
- `core/canonical`: the owner `SheafOfModules 𝒪`, the bridge functor `SheafOfModules.toSheaf 𝒪`,
  and the Grothendieck-axiom owner `AB5`;
- `bridge/view`: the two preservation instances for `SheafOfModules.toSheaf 𝒪`, which connect the
  owner `Mod(𝒪)` to the already-canonical sheaf category `Sheaf J AddCommGrpCat`.
-/

/- Lemma 18.14.2 (1): the category `Mod(𝒪)` of sheaves of `𝒪`-modules has all small limits. -/
#synth HasLimits (Mod(𝒪))

private theorem toSheaf_preservesLimits :
    PreservesLimits (SheafOfModules.toSheaf 𝒪) := by
  sorry

noncomputable instance :
    PreservesLimits (SheafOfModules.toSheaf 𝒪) :=
  toSheaf_preservesLimits 𝒪

/- Lemma 18.14.2 (2): the forgetful functor from `Mod(𝒪)` to the category of sheaves of abelian
groups on `(C, J)` commutes with all small limits. -/
#synth PreservesLimits (SheafOfModules.toSheaf 𝒪)

section Colimits

variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/- Lemma 18.14.2 (3): the category `Mod(𝒪)` of sheaves of `𝒪`-modules has all small colimits. -/
#synth HasColimits (Mod(𝒪))

private theorem toSheaf_preservesColimits :
    PreservesColimits (SheafOfModules.toSheaf 𝒪) := by
  sorry

noncomputable instance :
    PreservesColimits (SheafOfModules.toSheaf 𝒪) :=
  toSheaf_preservesColimits 𝒪

/- Lemma 18.14.2 (4): the forgetful functor from `Mod(𝒪)` to the category of sheaves of abelian
groups on `(C, J)` commutes with all small colimits. -/
#synth PreservesColimits (SheafOfModules.toSheaf 𝒪)

section ExactFilteredColimits

variable [HasSheafify J AddCommGrpCat.{max u v}]

noncomputable instance : AB5 (Mod(𝒪)) where
  ofShape K _ _ := by
    let _ : HasExactColimitsOfShape K (Sheaf J AddCommGrpCat.{max u v}) := by
      infer_instance
    exact HasExactColimitsOfShape.domain_of_functor K (SheafOfModules.toSheaf 𝒪)

/- Lemma 18.14.2 (5): filtered colimits are exact in `Mod(𝒪)`. In canonical mathlib form, this
says that `Mod(𝒪)` satisfies `AB5`. -/
#synth AB5 (Mod(𝒪))

end ExactFilteredColimits

end Colimits

end

/-! ### Lemma_18_14_3 (from Chap18) -/
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u₁ u₂ v₁ v₂ u

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {F : C ⥤ D} [Functor.IsContinuous F J K]
variable {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
variable (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
variable [(SheafOfModules.pushforward φ).IsRightAdjoint]

/-
Domain-style sampling for Lemma 18.14.3:
- primary domain: pullback/pushforward of sheaves of modules along a morphism of ringed sites or
  ringed topoi, together with the generic exact-functor owners `leftExactFunctor` and
  `rightExactFunctor`;
- sampled owner declarations:
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `leftExactFunctor`,
  `rightExactFunctor`;
- best owner abstraction: the adjunction
  `SheafOfModules.pullbackPushforwardAdjunction φ`,
  together with the owner-level exactness predicates and the adjoint-preserves-(co)limits
  instances;
- primitive data: only the ring-sheaf morphism `φ`, with the right-adjoint structure on
  `SheafOfModules.pushforward φ`;
- derived API: preservation of limits/colimits and the bundled left/right exactness predicates for
  `SheafOfModules.pushforward φ` and `SheafOfModules.pullback φ`.

Source/core/bridge triage:
- `source-facing`: the four clauses asserting that `f_*` preserves limits and is left exact, and
  that `f^*` preserves colimits and is right exact;
- `core/canonical`: `SheafOfModules.pullbackPushforwardAdjunction φ` together with the generic
  owners `leftExactFunctor` and `rightExactFunctor`;
- `bridge/view`: the direct `#check` / `#synth` queries below, with no parallel local theorem API.
-/

/- Lemma 18.14.3 (1): the direct-image functor `f_*` on sheaves of modules is left exact. -/
#check
  (show leftExactFunctor (SheafOfModules R) (SheafOfModules S) (SheafOfModules.pushforward φ) from
    by
      simpa [leftExactFunctor_iff] using
        (inferInstance : PreservesFiniteLimits (SheafOfModules.pushforward φ)))

/- Lemma 18.14.3 (2): in fact, the direct-image functor `f_*` on sheaves of modules commutes with
all limits. -/
#synth PreservesLimits (SheafOfModules.pushforward φ)

/- Lemma 18.14.3 (3): the inverse-image functor `f^*` on sheaves of modules is right exact. -/
#check
  (show rightExactFunctor (SheafOfModules S) (SheafOfModules R) (SheafOfModules.pullback φ) from
    by
      simpa [rightExactFunctor_iff] using
        (inferInstance : PreservesFiniteColimits (SheafOfModules.pullback φ)))

/- Lemma 18.14.3 (4): in fact, the inverse-image functor `f^*` on sheaves of modules commutes
with all colimits. -/
#synth PreservesColimits (SheafOfModules.pullback φ)

/-! ### Lemma_18_14_4 (from Chap18) -/
open CategoryTheory
open CategoryTheory.ObjectProperty

universe v u w

namespace CategoryTheory
namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- Domain-style sampling:
- primary domain: conservative families of site points and exactness detection on abelian sheaves;
- sampled owner declarations:
  `ObjectProperty.IsConservativeFamilyOfPoints`,
  `JointlyReflectIsomorphisms.exact_iff`,
  `GrothendieckTopology.hasEnoughPoints_iff_exists_conservativePointFamily`,
  `ExactFunctor.of p.sheafFiber`;
- source/core/bridge triage:
  `source-facing`: the two stalkwise exactness criteria below;
  `core/canonical`: `ObjectProperty.IsConservativeFamilyOfPoints` and
    `JointlyReflectIsomorphisms.exact_iff`;
  `bridge/view`: this file specializes the owner exactness-detection theorem to stalk functors on
    sheaves of abelian groups and reuses the chapter-level enough-points bridge.
- primitive data: the short complex `S`, the indexed family of points `p`, and the conservativity
  hypothesis `hp`;
- derived API: the two iff-criteria below. -/

section

variable [LocallySmall C]

omit [LocallySmall C] in
private theorem stalkJointlyReflectsIsomorphisms {I : Type w}
    (p : I → Point.{max u v w} J)
    (hp : (ofObj p).IsConservativeFamilyOfPoints) :
    JointlyReflectIsomorphisms
      (fun i : I ↦
        ((p i).sheafFiber :
          Sheaf J AddCommGrpCat.{max u v w} ⥤ AddCommGrpCat.{max u v w})) := by
  refine ⟨?_⟩
  intro X Y f _
  let h := hp.jointlyReflectIsomorphisms AddCommGrpCat.{max u v w}
  let _ : ∀ Φ : (ofObj p).FullSubcategory, IsIso (Φ.obj.sheafFiber.map f) := fun Φ ↦ by
    rcases (ofObj_iff p Φ.obj).1 Φ.property with ⟨i, hi⟩
    have hΦ : Φ = ⟨p i, ofObj_apply p i⟩ := by
      cases Φ
      simp only [FullSubcategory.mk.injEq] at hi ⊢
      cases hi
      rfl
    cases hΦ
    infer_instance
  exact h.isIso f

end

-- Proof sketch: apply the exactness-detection theorem for a jointly conservative family of exact
-- fiber functors, using `hp.jointlyReflectIsomorphisms AddCommGrpCat` for the sheaf fibers
-- attached to the chosen family of points.
/-- Lemma 18.14.4 (1): if `p_i`, `i ∈ I`, is a conservative family of points on a site, then a
short complex of abelian sheaves is exact if and only if it is exact on the stalks at the points
`p_i`. -/
theorem abelianSheaf_exact_iff_stalkwise_exact_of_conservativeFamily
    {I : Type w} (p : I → Point.{max u v w} J)
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    [HasSheafify J AddCommGrpCat.{max u v w}]
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v w})) :
    S.Exact ↔
      ∀ i : I, (S.map (p i).sheafFiber).Exact := by
  simpa using (stalkJointlyReflectsIsomorphisms p hp).exact_iff S

-- Proof sketch: choose a small conservative family of points from `J.HasEnoughPoints`, apply the
-- first clause to that family, and use that exactness on all stalks obviously implies exactness on
-- the selected conservative subfamily.
/-- Lemma 18.14.4 (2): if a site has enough points, then a short complex of abelian sheaves is
exact if and only if it is exact on all stalks. -/
theorem abelianSheaf_exact_iff_stalkwise_exact_of_hasEnoughPoints
    [HasEnoughPoints.{max u v w} J]
    [HasSheafify J AddCommGrpCat.{max u v w}]
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v w})) :
    S.Exact ↔
      ∀ p : Point.{max u v w} J,
        (S.map p.sheafFiber).Exact := by
  let hJ : HasEnoughPoints.{max u v w} J := inferInstance
  obtain ⟨I, p, hp⟩ := hasEnoughPoints_iff_exists_conservativePointFamily.mp hJ
  constructor
  · intro hS p'
    exact hS.map p'.sheafFiber
  · intro hS
    exact ((stalkJointlyReflectsIsomorphisms p hp).exact_iff S).2 fun i ↦ hS (p i)

end GrothendieckTopology
end CategoryTheory
