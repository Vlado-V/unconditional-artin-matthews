module

public import ArtinMatthews.SpectralCuspConstantTermGlobal
public import ArtinMatthews.SpectralCuspConstantTermEnergy
public import ArtinMatthews.SpectralCuspConstantTermWeakDerivative
public import ArtinMatthews.SpectralCuspEulerRepresentative
public import ArtinMatthews.SpectralCuspWeakRegularity
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Euler uniqueness for the actual completed constant term. The only
remaining equation in this interface is the explicitly displayed second
compact-test equation; the first derivative and both energy bounds are
proved for the actual operators. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem gamma0GlobalCuspConstantTerm_zero_of_second_weak_equation
    (N : ℕ) [NeZero N] (r : SL(2, ℤ)) (u : gamma0EnergySpace N)
    (hsecond : ∀ (ρ : ℝ → ℝ), ContDiff ℝ ∞ ρ → HasCompactSupport ρ →
      tsupport ρ ⊆ Ioi (0 : ℝ) →
      (∫ y in Ioi (0 : ℝ), deriv (deriv ρ) y •
        gamma0GlobalCuspConstantTerm N r (gamma0EnergyInclusion N u) y) =
      (∫ y in Ioi (0 : ℝ), (ρ y / y ^ 2) •
        gamma0GlobalCuspConstantTerm N r (gamma0EnergyInclusion N u) y)) :
    gamma0GlobalCuspConstantTerm N r (gamma0EnergyInclusion N u)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
  let c := gamma0GlobalCuspConstantTerm N r (gamma0EnergyInclusion N u)
  let g := gamma0GlobalCuspConstantTermDerivative N r u
  have hfirst := gamma0GlobalCuspConstantTerm_weak_derivative N r u
  have hsecond' : ∀ (ρ : ℝ → ℝ), ContDiff ℝ ∞ ρ → HasCompactSupport ρ →
      tsupport ρ ⊆ Ioi (0 : ℝ) →
      (∫ y in Ioi (0 : ℝ), deriv ρ y • g y) =
        -(∫ y in Ioi (0 : ℝ), (ρ y / y ^ 2) • c y) := by
    intro ρ hρ hρc hρs
    have hd : ContDiff ℝ ∞ (deriv ρ) := (contDiff_infty_iff_deriv.mp hρ).2
    have h := hfirst (deriv ρ) hd hρc.deriv (tsupport_deriv_subset.trans hρs)
    rw [hsecond ρ hρ hρc hρs] at h
    simpa only [neg_neg] using congrArg Neg.neg h.symm
  obtain ⟨C, G, _, _, hc, _, hC, hG⟩ := cuspWeakEuler_exists_classical c g
    (gamma0GlobalCuspConstantTerm_locallyIntegrable N r (gamma0EnergyInclusion N u))
    (gamma0GlobalCuspConstantTermDerivative_locallyIntegrable N r u) hfirst hsecond'
  exact (cuspEuler_vanishes_of_ae_quadratic_bound c C G hc.symm hC hG
    (gamma0GlobalCuspConstantTerm_integrable_energy N r (gamma0EnergyInclusion N u) 1 zero_lt_one)
    (fun Y hY hY1 => gamma0GlobalCuspConstantTerm_near_zero_energy N r
      (gamma0EnergyInclusion N u) Y hY hY1)).2

end ArtinMatthews
