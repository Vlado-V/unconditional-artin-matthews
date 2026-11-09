module

public import ArtinMatthews.VaryingKummerAnalyticRayUnramifiedEuler
public import ArtinMatthews.VaryingKummerAnalyticRayUnramifiedClassXi


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine entire continuation of residue-one nonprincipal ray series over
arbitrary number fields, retaining the actual deleted conductor Euler factors. -/

namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section
open NumberField Set Module Filter Topology
open scoped BigOperators NumberField nonZeroDivisors Classical
namespace EvenRayCharacter
variable {K : Type*} [Field K] [NumberField K] {N : ℕ} [NeZero N]
variable (ψ : EvenRayCharacter K N)

def unramifiedContinued (hψ : ψ.residue = 1) (s : ℂ) : ℂ :=
  mixedIdealClassContinued K (ψ.classCharacter hψ) s *
    badEulerCorrection (ψ.classUnitCharacter hψ) N s

theorem unramifiedContinued_entire (hψ : ψ.residue = 1) :
    Differentiable ℂ (ψ.unramifiedContinued hψ) :=
  (mixedIdealClassContinued_entire K _).mul (badEulerCorrection_entire _ N)

/-- Nonprincipality is the actual existence of a nontrivial value on a
nonzero coprime integral ideal. Values at omitted primes are not used. -/
theorem unramifiedContinued_eq_dirichlet (hψ : ψ.residue = 1) (hnp : ψ.IsNonprincipal)
    {s : ℂ} (hs : 1 < s.re) :
    ψ.unramifiedContinued hψ s = ψ.dirichlet s := by
  rw [unramifiedContinued, mixedIdealClassContinued_eq K _
    (ψ.classCharacter_ne_one_of_nonprincipal hψ hnp) hs]
  exact (ψ.dirichlet_of_residue_one hψ hs).symm

theorem unramifiedContinued_ne_zero (hψ : ψ.residue = 1) (hnp : ψ.IsNonprincipal) :
    ψ.unramifiedContinued hψ ≠ 0 := by
  intro H
  have HE := ψ.unramifiedContinued_eq_dirichlet hψ hnp (s := 2) (by norm_num)
  rw [H, Pi.zero_apply] at HE
  exact ψ.dirichlet_ne_zero (by norm_num : 1 < (2 : ℂ).re) HE.symm

theorem unramifiedContinued_finite_nonnegative_order
    (hψ : ψ.residue = 1) (hnp : ψ.IsNonprincipal) (β : ℂ) :
    ∃ m : ℕ, meromorphicOrderAt (ψ.unramifiedContinued hψ) β = (m : WithTop ℤ) := by
  have ha : ∀ z, AnalyticAt ℂ (ψ.unramifiedContinued hψ) z :=
    fun z => (ψ.unramifiedContinued_entire hψ).analyticAt z
  have hfin : analyticOrderAt (ψ.unramifiedContinued hψ) β ≠ ⊤ := by
    intro H
    exact ψ.unramifiedContinued_ne_zero hψ hnp
      ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero β ha).mp H)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
  refine ⟨m, ?_⟩
  rw [(ha β).meromorphicOrderAt_eq, ← hm, ENat.map_natCast]
  rfl

end EvenRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
