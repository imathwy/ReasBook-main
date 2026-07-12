import StacksProject_2024.Chap10.Lemma_10_99_17.QuotientModule

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u

section

variable {A : Type u} [CommRing A]
variable {M : Type u} [AddCommGroup M] [Module A M]
variable {r : ℕ} (f : Fin r → A)

local notation "I" => Ideal.span (Set.range f)
local notation "Ā" => A ⧸ I
local notation "M̄" => M ⧸ (I • (⊤ : Submodule A M))
set_option quotPrecheck false in
local notation "TorQ[" n "]" =>
  (((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).obj (ModuleCat.of A Ā))

/-- Helper for Lemma 10.99.17: if a module is annihilated by the initial generators of `g`, then
the kernel of multiplication by the last generator is annihilated by the whole family. This is the
kernel row input in the corrected generator-descent step. -/
lemma span_range_le_annihilator_ker_last_lsmul
    {s : ℕ} (g : Fin (s + 1) → A)
    {K : Type u} [AddCommGroup K] [Module A K]
    (hK : Ideal.span (Set.range (Fin.init g)) ≤ Module.annihilator A K) :
    Ideal.span (Set.range g) ≤ Module.annihilator A
      (LinearMap.ker (LinearMap.lsmul A K (g (Fin.last s)))) := by
  refine Ideal.span_le.mpr ?_
  intro x hx
  rcases hx with ⟨i, rfl⟩
  refine Fin.lastCases ?_ ?_ i
  · -- The last generator kills the kernel by definition of `ker (lsmul a)`.
    change
      (Module.toAddMonoidEnd A
        (LinearMap.ker (LinearMap.lsmul A K (g (Fin.last s))))) (g (Fin.last s)) = 0
    apply AddMonoidHom.ext
    rintro ⟨y, hy⟩
    apply Subtype.ext
    simpa [LinearMap.mem_ker, LinearMap.lsmul_apply] using hy
  · intro j
    have hjInit :
        Fin.init g j ∈ Module.annihilator A K := by
      exact hK (Ideal.subset_span ⟨j, rfl⟩)
    have hj :
        Module.toAddMonoidEnd A K (g j.castSucc) = 0 := by
      simpa [Module.annihilator, RingHom.mem_ker] using hjInit
    -- The older generators already kill all of `K`, so they also kill the kernel subtype.
    change
      (Module.toAddMonoidEnd A
        (LinearMap.ker (LinearMap.lsmul A K (g (Fin.last s))))) (g j.castSucc) = 0
    apply AddMonoidHom.ext
    intro y
    apply Subtype.ext
    have hval := congrArg (fun φ : AddMonoid.End K => φ y.1) hj
    simpa using hval

/-- Helper for Lemma 10.99.17: if a module is annihilated by the initial generators of `g`, then
the quotient by multiplication with the last generator is annihilated by the whole family. This is
the quotient row input in the corrected generator-descent step. -/
lemma span_range_le_annihilator_quotient_last_lsmul
    {s : ℕ} (g : Fin (s + 1) → A)
    {K : Type u} [AddCommGroup K] [Module A K]
    (hK : Ideal.span (Set.range (Fin.init g)) ≤ Module.annihilator A K) :
    Ideal.span (Set.range g) ≤ Module.annihilator A
      (K ⧸ LinearMap.range (LinearMap.lsmul A K (g (Fin.last s)))) := by
  let μ : K →ₗ[A] K := LinearMap.lsmul A K (g (Fin.last s))
  refine Ideal.span_le.mpr ?_
  intro x hx
  rcases hx with ⟨i, rfl⟩
  refine Fin.lastCases ?_ ?_ i
  · -- The last generator acts trivially on the quotient because its image is exactly the
    -- defining submodule of the quotient.
    change
      (Module.toAddMonoidEnd A
        (K ⧸ LinearMap.range (LinearMap.lsmul A K (g (Fin.last s))))) (g (Fin.last s)) = 0
    apply AddMonoidHom.ext
    intro q
    rcases Submodule.mkQ_surjective (LinearMap.range μ) q with ⟨y, rfl⟩
    change Submodule.mkQ (LinearMap.range μ) ((g (Fin.last s)) • y) = 0
    apply (Submodule.Quotient.mk_eq_zero (LinearMap.range μ)).2
    exact ⟨y, by simp [μ, LinearMap.lsmul_apply]⟩
  · intro j
    have hjInit :
        Fin.init g j ∈ Module.annihilator A K := by
      exact hK (Ideal.subset_span ⟨j, rfl⟩)
    have hj :
        Module.toAddMonoidEnd A K (g j.castSucc) = 0 := by
      simpa [Module.annihilator, RingHom.mem_ker] using hjInit
    -- The older generators already kill all representatives, hence also their quotient classes.
    change
      (Module.toAddMonoidEnd A
        (K ⧸ LinearMap.range (LinearMap.lsmul A K (g (Fin.last s))))) (g j.castSucc) = 0
    apply AddMonoidHom.ext
    intro q
    rcases Submodule.mkQ_surjective (LinearMap.range μ) q with ⟨y, rfl⟩
    change Submodule.mkQ (LinearMap.range μ) (g j.castSucc • y) = 0
    have hval := congrArg (fun φ : AddMonoid.End K => φ y) hj
    have hzero : g j.castSucc • y = 0 := by
      simpa using hval
    simpa [hzero]

end
