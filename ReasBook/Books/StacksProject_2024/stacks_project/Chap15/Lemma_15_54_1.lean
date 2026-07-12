import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Module.Baer

universe u

/- Domain-style sampling for Lemma 15.54.1:
- primary domain: injective objects in `AddCommGrpCat` and divisibility of abelian groups;
- sampled core/canonical declarations:
  `Injective`,
  `AddCommGrpCat.injective_as_module_iff`,
  `AddCommGrpCat.injective_of_divisible`,
  `DivisibleBy`;
- best owner abstraction: the categorical owner `Injective (AddCommGrpCat.of J)`, with
  `DivisibleBy J ℤ` used only as a local bridge where mathlib already owns the converse instance;
- primitive data: the abelian group `J`;
- derived API: the surjectivity of `n • ·` for `n ≠ 0`, and the local `DivisibleBy J ℤ` witness
  constructed from those surjectivity hypotheses in the reverse implication;
- source/core/bridge triage:
  `source-facing`: the textbook equivalence between injectivity and divisibility;
  `core/canonical`: `Injective` and `DivisibleBy`;
  `bridge/view`: `AddCommGrpCat.injective_as_module_iff` and the local divisibility witness built
  from surjective scalar multiplication.

The public surface should therefore stay theorem-level; no separate public chosen divisibility
witness is needed. -/

/-- If a `ℤ`-module is injective, then multiplication by any nonzero integer is surjective. -/
private theorem surjective_zsmul_of_injective
    (J : Type u) [AddCommGroup J] (hJ : Module.Injective ℤ J) (n : ℤ) (hn : n ≠ 0) :
    Function.Surjective (n • · : J → J) := by
  intro x
  let e : ℤ ≃ₗ[ℤ] Ideal.span ({n} : Set ℤ) := by
    let f : ℤ →ₗ[ℤ] Ideal.span ({n} : Set ℤ) :=
      LinearMap.codRestrict (Ideal.span ({n} : Set ℤ)) (LinearMap.toSpanSingleton ℤ ℤ n)
        (fun m ↦ by
          change m * n ∈ Ideal.span ({n} : Set ℤ)
          exact Ideal.mem_span_singleton.mpr ⟨m, by ring⟩)
    refine LinearEquiv.ofBijective f ?_
    constructor
    · intro a b hab
      have hmul : a * n = b * n := by
        simpa [f, LinearMap.toSpanSingleton_apply] using congrArg Subtype.val hab
      exact Int.eq_of_mul_eq_mul_right hn hmul
    · intro y
      obtain ⟨m, hm⟩ := Ideal.mem_span_singleton.mp y.2
      refine ⟨m, Subtype.ext ?_⟩
      change m * n = y.1
      simpa [mul_comm] using hm.symm
  let I : Ideal ℤ := Ideal.span ({n} : Set ℤ)
  let g : I →ₗ[ℤ] J := LinearMap.toSpanSingleton ℤ J x ∘ₗ e.symm.toLinearMap
  have he1 : e 1 = ⟨n, Ideal.mem_span_singleton_self n⟩ := by
    ext
    simp [e]
  have hgen : e.symm ⟨n, Ideal.mem_span_singleton_self n⟩ = 1 := by
    rw [← he1]
    exact e.left_inv 1
  have hg : g ⟨n, Ideal.mem_span_singleton_self n⟩ = x := by
    change e.symm ⟨n, Ideal.mem_span_singleton_self n⟩ • x = x
    rw [hgen, one_smul]
  have hBaer : Module.Baer ℤ J := Module.Baer.of_injective hJ
  obtain ⟨h, hh⟩ := (iff_surjective.mp hBaer I) g
  refine ⟨h 1, ?_⟩
  have hx : h n = x := by
    have := congrArg (fun k : I →ₗ[ℤ] J ↦ k ⟨n, Ideal.mem_span_singleton_self n⟩) hh
    simpa [LinearMap.lcomp_apply, g] using this.trans hg
  have hmap : h n = n • h 1 := by
    simpa using map_zsmul h n (1 : ℤ)
  exact hmap.symm.trans hx

/-- Lemma 15.54.1: an abelian group is an injective object of the category of abelian groups if and
only if it is divisible, i.e. each multiplication-by-`n` map is surjective for `n ≠ 0`. We use
the canonical owner `DivisibleBy J ℤ` only as a local bridge in the converse implication. -/
-- Proof sketch: the forward direction passes from categorical injectivity in `AddCommGrpCat` to
-- injectivity as a `ℤ`-module and then applies Baer's criterion on the principal ideal `(n)`.
-- The reverse direction packages the surjectivity hypothesis as `DivisibleBy J ℤ` and then uses
-- mathlib's injectivity theorem for divisible abelian groups.
theorem addCommGrpCat_injective_iff_divisible (J : Type u) [AddCommGroup J] :
    Injective (AddCommGrpCat.of J) ↔
      ∀ n : ℤ, n ≠ 0 → Function.Surjective (n • · : J → J) := by
  constructor
  · intro h n hn
    let _ : Injective (ModuleCat.of ℤ J) := (AddCommGrpCat.injective_as_module_iff J).mpr h
    let hJ : Module.Injective ℤ J := Module.injective_module_of_injective_object ℤ J
    exact surjective_zsmul_of_injective J hJ n hn
  · intro h
    let _ : DivisibleBy J ℤ := divisibleByOfSMulRightSurj J ℤ (fun {n} hn ↦ h n hn)
    infer_instance
