module

public import ArtinMatthews.SpectralCuspWeakRegularityRepresentative
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine local weak-to-classical regularity step for the cusp Euler
system. Both continuous representatives are constructed from the given
locally integrable functions and their compact-test weak equations. -/
namespace ArtinMatthews
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
open SpectralCuspWeakRegularity

/-- Actual locally integrable weak Euler solutions admit classical
representatives on the positive half-line. -/
theorem cuspWeakEuler_exists_classical (c g : ℝ → ℂ)
    (hc : LocallyIntegrableOn c (Ioi (0 : ℝ)) volume)
    (hg : LocallyIntegrableOn g (Ioi (0 : ℝ)) volume)
    (hfirst : PositiveWeakDerivative c g)
    (hsecond : ∀ (ρ : ℝ → ℝ), ContDiff ℝ ∞ ρ → HasCompactSupport ρ →
      tsupport ρ ⊆ Ioi (0 : ℝ) →
      (∫ y in Ioi (0 : ℝ), deriv ρ y • g y) =
        -(∫ y in Ioi (0 : ℝ), (ρ y / y ^ 2) • c y)) :
    ∃ C G : ℝ → ℂ,
      ContinuousOn C (Ioi (0 : ℝ)) ∧ ContinuousOn G (Ioi (0 : ℝ)) ∧
      c =ᵐ[volume.restrict (Ioi (0 : ℝ))] C ∧
      g =ᵐ[volume.restrict (Ioi (0 : ℝ))] G ∧
      (∀ y > 0, HasDerivAt C (G y) y) ∧
      (∀ y > 0, HasDerivAt G (C y / (y : ℂ) ^ 2) y) := by
  let m : ℝ → ℝ := fun y => (y ^ 2)⁻¹
  have hm : ContinuousOn m (Ioi (0 : ℝ)) :=
    (continuousOn_id.pow 2).inv₀ (fun y hy => pow_ne_zero 2 (ne_of_gt hy))
  have hmc : LocallyIntegrableOn (fun y => m y • c y) (Ioi (0 : ℝ)) volume :=
    hc.continuousOn_smul isOpen_Ioi.isLocallyClosed hm
  have hsecond' : PositiveWeakDerivative g (fun y => m y • c y) := by
    intro ρ hρ hρc hρs
    simpa only [m, div_eq_mul_inv, mul_smul] using hsecond ρ hρ hρc hρs
  obtain ⟨C, hC, hcC⟩ := positive_weak_continuous_representative hc hg hfirst
  obtain ⟨G, hG, hgG⟩ := positive_weak_continuous_representative hg hmc hsecond'
  have hmcC : (fun y => m y • c y) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun y => m y • C y := by
    filter_upwards [hcC] with y hy
    rw [hy]
  refine ⟨C, G, hC, hG, hcC, hgG,
    positiveWeakDerivative_hasDerivAt hc hg hfirst hC hG hcC hgG, ?_⟩
  intro y hy
  have H := positiveWeakDerivative_hasDerivAt hg hmc hsecond' hG (hm.smul hC) hgG hmcC y hy
  change HasDerivAt G ((y ^ 2)⁻¹ • C y) y at H
  simpa only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow,
    div_eq_mul_inv, mul_comm] using H

end
end ArtinMatthews
