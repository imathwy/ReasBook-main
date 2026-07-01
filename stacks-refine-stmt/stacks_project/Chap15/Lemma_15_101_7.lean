import stacks_project.Chap15.Remark_15_101_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u

section

variable {A : Type u} [CommRing A] {I : Ideal A}

namespace IadicFiniteModuleSystem

variable {X Y : IadicFiniteModuleSystem A I}

local notation "Q" => IadicFiniteModuleSystem.Category.quotient A I

open HomRepresentative

/- Domain-style sampling for Lemma 15.101.7:
- primary domain: isomorphism criteria for morphisms in the category `IadicFiniteModuleSystem`
  from Remark `15.101.6`;
- sampled owner declarations:
  `CategoryTheory.IsIso`,
  `CategoryTheory.Quotient`,
  `IadicFiniteModuleSystem.Category.quotient`,
  `IadicFiniteModuleSystem.HomRepresentative`,
  `Submodule.torsionBySet`;
- best owner abstraction:
  `source-facing`: the isomorphism criterion for a morphism
    `f : (Q).obj X ⟶ (Q).obj Y`;
  `core/canonical`: the owner predicate `CategoryTheory.IsIso f` on morphisms in the category of
    Remark `15.101.6`;
  `bridge/view`: the representative-level predicate saying one, equivalently every,
    representative has eventually bounded kernel and cokernel;
- primitive data: the representative-level torsion conditions on kernels and cokernels;
- derived API: the morphism-level predicate
  `HasEventuallyBoundedKernelAndCokernel f` and the main `IsIso f ↔ ...` theorem below.

This item therefore should not stop at the auxiliary representative predicate: the public main
entry is the `IsIso` criterion on the actual category morphism. -/

namespace HomRepresentative

private abbrev levelKernel (f : HomRepresentative X Y)
    (n : {n : ℕ+ // f.cutoff ≤ (n : ℕ)}) :
    Submodule (stageRing A I n.1) (powerSubmodule f.cutoff X n.1) :=
  LinearMap.ker (f n.1 n.2)

private abbrev levelCokernel (f : HomRepresentative X Y)
    (n : {n : ℕ+ // f.cutoff ≤ (n : ℕ)}) : Type u :=
  torsionQuotient f.cutoff Y n.1 ⧸ LinearMap.range (f n.1 n.2)

private def hasEventuallyBoundedKernelAndCokernel (f : HomRepresentative X Y) : Prop :=
  ∃ c' N : ℕ, ∃ hN : f.cutoff ≤ N,
    ∀ n : ℕ+, ∀ hn : N ≤ (n : ℕ),
      Module.IsTorsionBySet
          (stageRing A I n)
          (levelKernel f ⟨n, Nat.le_trans hN hn⟩)
          (↑((stageIdeal A I n) ^ c') : Set (stageRing A I n)) ∧
          Module.IsTorsionBySet
              (stageRing A I n)
              (levelCokernel f ⟨n, Nat.le_trans hN hn⟩)
              (↑((stageIdeal A I n) ^ c') : Set (stageRing A I n))

private theorem hasEventuallyBoundedKernelAndCokernel_congr
    {f g : HomRepresentative X Y} (h : f ≈ g) :
    hasEventuallyBoundedKernelAndCokernel f ↔ hasEventuallyBoundedKernelAndCokernel g := by
  sorry

end HomRepresentative

private theorem relation_of_compClosure
    {f g : HomRepresentative X Y}
    (h : CategoryTheory.HomRel.CompClosure (relation A I) f g) :
    relation A I f g := by
  simpa [relation] using
    (show CategoryTheory.HomRel.CompClosure (relation A I) f g ↔ relation A I f g from
      CategoryTheory.HomRel.compClosure_iff_self (relation A I) f g).1 h

/-- Auxiliary morphism-level predicate for Lemma 15.101.7 in the category from Remark 15.101.6: a
morphism has eventually bounded kernel and cokernel if, for one (equivalently every)
representative `(c, \varphi_n)`, there exists a power `I^{c'}` annihilating both the kernel and
cokernel of the level maps `I^c E_n → E'_n / E'_n[I^c]` for all sufficiently large `n`. -/
def HasEventuallyBoundedKernelAndCokernel
    (f : (Q).obj X ⟶ (Q).obj Y) : Prop :=
  Quot.liftOn f hasEventuallyBoundedKernelAndCokernel
    (fun f g h ↦ by
      apply propext
      exact hasEventuallyBoundedKernelAndCokernel_congr (relation_of_compClosure h))

-- Proof sketch: if `f` is an isomorphism in the quotient category of Remark `15.101.6`, choose
-- an inverse representative and compose the two representatives. The identity representative has
-- zero kernel and cokernel, so the bounded-kernel/cokernel condition follows from compatibility
-- with promotion and composition. Conversely, the bounded kernel/cokernel condition yields a
-- representative that is invertible in the quotient category after increasing the cutoff, which
-- gives `IsIso f`.
/-- Lemma 15.101.7: a morphism in the category `\mathcal C` of Remark `15.101.6` is an
isomorphism if and only if it has eventually bounded kernel and cokernel. -/
theorem isIso_iff_hasEventuallyBoundedKernelAndCokernel
    (f : (Q).obj X ⟶ (Q).obj Y) :
    IsIso f ↔ HasEventuallyBoundedKernelAndCokernel f := by
  sorry

end IadicFiniteModuleSystem

end
