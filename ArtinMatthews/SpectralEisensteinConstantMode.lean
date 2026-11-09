module

public import ArtinMatthews.SpectralEisensteinTailWeakSystem
public import ArtinMatthews.SpectralCuspRayWeakEuler
public import ArtinMatthews.SpectralCuspComplexEulerSolutions
public import ArtinMatthews.SpectralCuspComplexEulerEnergy
public import ArtinMatthews.SpectralCuspConstantTermEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine constant term of the actual continued full ambient
Eisenstein remainder has only the decaying Euler mode. The first and
second weak equations and weighted L2 are derived from the actual graph. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0CuspEisensteinContinuedRemainder_constant_mode
    (N : ℕ) [NeZero N] (r a : SL(2,ℤ)) (s : ℂ)
    (hs : s ∈ gamma0EisensteinContinuationDomain)
    (Y : ℝ) (hY : 0<Y) (hhigh : 2*(gamma0CuspTrueWidth N r:ℝ) ≤ Y) :
    ∃ B : ℂ, gamma0GlobalCuspConstantTerm N r (gamma0CuspEisensteinContinuedRemainder N a s)
      =ᵐ[volume.restrict (Ioi Y)] fun y => B*(y:ℂ)^(1-s) := by
  let c := gamma0GlobalCuspConstantTerm N r (gamma0CuspEisensteinContinuedRemainder N a s)
  let g := gamma0GlobalCuspConstantTermDerivative N r (gamma0CuspEisensteinContinuedEnergy N a s hs)
  have hsub : Ioi Y ⊆ Ioi (0:ℝ) := fun _ hy => hY.trans hy
  obtain ⟨C,G,_,_,hcC,_,hC,hG⟩ := cuspRayWeakEuler_exists_classical hY.le (s*(1-s)) c g
    ((gamma0GlobalCuspConstantTerm_locallyIntegrable N r
      (gamma0CuspEisensteinContinuedRemainder N a s)).mono_set hsub)
    ((gamma0GlobalCuspConstantTermDerivative_locallyIntegrable N r
      (gamma0CuspEisensteinContinuedEnergy N a s hs)).mono_set hsub)
    (gamma0CuspEisensteinContinuedRemainder_constant_first_weak N r a s hs hY)
    (gamma0CuspEisensteinContinuedRemainder_constant_derivative_weak N r a s hs Y hY hhigh)
  have hpq : s≠1-s := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re,Complex.one_re] at hre
    linarith [hs.1]
  obtain ⟨A,B,hAB⟩ := cuspComplexEuler_solution_classification C G hY.le (s*(1-s)) s (1-s)
    (by ring) rfl hpq hC hG
  have hcAB : c =ᵐ[volume.restrict (Ioi Y)] fun y => A*(y:ℂ)^s+B*(y:ℂ)^(1-s) := by
    filter_upwards [hcC,ae_restrict_mem measurableSet_Ioi] with y hy hyY
    exact hy.trans (hAB y hyY)
  have ht : IntegrableOn (fun y : ℝ => ‖A*(y:ℂ)^s+B*(y:ℂ)^(1-s)‖^2/y^2) (Ioi Y) := by
    apply (gamma0GlobalCuspConstantTerm_integrable_energy N r
      (gamma0CuspEisensteinContinuedRemainder N a s) Y hY).congr
    filter_upwards [hcAB] with y hy
    change ‖c y‖^2/y^2=_
    rw [hy]
  have hA := cuspComplexEuler_tail_forces_plus_zero A B s (1-s) hY hs.1.le
    (by simp only [Complex.sub_re,Complex.one_re];linarith [hs.1]) ht
  refine ⟨B,?_⟩
  simpa only [hA,zero_mul,zero_add] using hcAB

end ArtinMatthews
