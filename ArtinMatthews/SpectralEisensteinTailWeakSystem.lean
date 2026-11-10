module

public import ArtinMatthews.SpectralCuspRayRepresentative
public import ArtinMatthews.SpectralCuspConstantTermGlobal
public import ArtinMatthews.SpectralEisensteinContinuation
public import ArtinMatthews.SpectralCuspConstantTermWeakDerivative
public import ArtinMatthews.SpectralCuspRayLocal
public import ArtinMatthews.SpectralEisensteinTailEquation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The actual full ambient energy vector supplies both weak derivatives
of the continued Eisenstein constant mode on every high cusp tail. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff
namespace ArtinMatthews
open SpectralCuspRayRegularity

def gamma0CuspEisensteinContinuedEnergy (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ)
    (hs : s ∈ gamma0EisensteinContinuationDomain) : gamma0EnergySpace N :=
  gamma0AmbientWeakResolvent N (s*(1-s)) hs.2 (-gamma0CuspEisensteinCompactForcingMass N a s)

theorem gamma0CuspEisensteinContinuedEnergy_mass (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : s ∈ gamma0EisensteinContinuationDomain) :
    gamma0EnergyInclusion N (gamma0CuspEisensteinContinuedEnergy N a s hs)=
      gamma0CuspEisensteinContinuedRemainder N a s := by
  rw [gamma0CuspEisensteinContinuedRemainder,gamma0AmbientResolventFamily_eq N (s*(1-s)) hs.2]
  rfl

theorem gamma0CuspEisensteinContinuedRemainder_constant_first_weak
    (N : ℕ) [NeZero N] (r a : SL(2,ℤ)) (s : ℂ)
    (hs : s ∈ gamma0EisensteinContinuationDomain) {Y : ℝ} (hY : 0<Y) :
    RayWeakDerivative (Y:=Y)
      (gamma0GlobalCuspConstantTerm N r (gamma0CuspEisensteinContinuedRemainder N a s))
      (gamma0GlobalCuspConstantTermDerivative N r (gamma0CuspEisensteinContinuedEnergy N a s hs)) := by
  intro ρ hρ hρc hρs
  have hρpos : tsupport ρ ⊆ Ioi (0:ℝ) := fun _ hy => hY.trans (hρs hy)
  have he := gamma0GlobalCuspConstantTerm_weak_derivative N r
    (gamma0CuspEisensteinContinuedEnergy N a s hs) ρ hρ hρc hρpos
  rw [gamma0CuspEisensteinContinuedEnergy_mass,
    spectralTest_setIntegral_eq_integral (deriv ρ) (Ioi (0:ℝ)) (tsupport_deriv_subset.trans hρpos),
    spectralTest_setIntegral_eq_integral ρ (Ioi (0:ℝ)) hρpos] at he
  rw [ray_test_setIntegral_eq _ (tsupport_deriv_subset.trans hρs),ray_test_setIntegral_eq _ hρs]
  exact he

theorem gamma0CuspEisensteinContinuedRemainder_global_constant_second_weak
    (N : ℕ) [NeZero N] (r a : SL(2,ℤ)) (s : ℂ)
    (hs : s ∈ gamma0EisensteinContinuationDomain)
    (Y : ℝ) (hY : 0<Y) (hhigh : 2*(gamma0CuspTrueWidth N r:ℝ) ≤ Y)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρs : tsupport ρ ⊆ Ioi Y) :
    (∫ y in Ioi Y, deriv (deriv ρ) y • gamma0GlobalCuspConstantTerm N r
      (gamma0CuspEisensteinContinuedRemainder N a s) y)=
      -(s*(1-s))*(∫ y in Ioi Y, (ρ y/y^2) • gamma0GlobalCuspConstantTerm N r
        (gamma0CuspEisensteinContinuedRemainder N a s) y) := by
  have he := (spectralCuspVerticalL2_ae_iff (Nat.cast_pos.mpr (NeZero.pos N)) hY).mp
    (gamma0GlobalCuspConstantTerm_ae N r (gamma0CuspEisensteinContinuedRemainder N a s) Y hY)
  have hleft : (∫ y in Ioi Y, deriv (deriv ρ) y • gamma0GlobalCuspConstantTerm N r
      (gamma0CuspEisensteinContinuedRemainder N a s) y)=
      ∫ y in Ioi Y, deriv (deriv ρ) y • gamma0CuspConstantTerm N r Y hY
        (gamma0CuspEisensteinContinuedRemainder N a s) y := by
    apply integral_congr_ae
    filter_upwards [he] with y hy
    rw [hy]
  have hright : (∫ y in Ioi Y, (ρ y/y^2) • gamma0GlobalCuspConstantTerm N r
      (gamma0CuspEisensteinContinuedRemainder N a s) y)=
      ∫ y in Ioi Y, (ρ y/y^2) • gamma0CuspConstantTerm N r Y hY
        (gamma0CuspEisensteinContinuedRemainder N a s) y := by
    apply integral_congr_ae
    filter_upwards [he] with y hy
    rw [hy]
  rw [hleft,hright]
  exact gamma0CuspEisensteinContinuedRemainder_constant_second_weak N r a s hs Y hY hhigh ρ hρ hρc hρs

theorem gamma0CuspEisensteinContinuedRemainder_constant_derivative_weak
    (N : ℕ) [NeZero N] (r a : SL(2,ℤ)) (s : ℂ)
    (hs : s ∈ gamma0EisensteinContinuationDomain)
    (Y : ℝ) (hY : 0<Y) (hhigh : 2*(gamma0CuspTrueWidth N r:ℝ) ≤ Y) :
    RayWeakDerivative (Y:=Y)
      (gamma0GlobalCuspConstantTermDerivative N r (gamma0CuspEisensteinContinuedEnergy N a s hs))
      (fun y => -(s*(1-s))*gamma0GlobalCuspConstantTerm N r
        (gamma0CuspEisensteinContinuedRemainder N a s) y/(y:ℂ)^2) := by
  intro ρ hρ hρc hρs
  have hd := gamma0CuspEisensteinContinuedRemainder_constant_first_weak N r a s hs hY
    (deriv ρ) (contDiff_infty_iff_deriv.mp hρ).2 hρc.deriv (tsupport_deriv_subset.trans hρs)
  have he := gamma0CuspEisensteinContinuedRemainder_global_constant_second_weak N r a s hs
    Y hY hhigh ρ hρ hρc hρs
  have hi (y : ℝ) : ρ y • (-(s*(1-s))*gamma0GlobalCuspConstantTerm N r
        (gamma0CuspEisensteinContinuedRemainder N a s) y/(y:ℂ)^2)=
      -(s*(1-s))*((ρ y/y^2) • gamma0GlobalCuspConstantTerm N r
        (gamma0CuspEisensteinContinuedRemainder N a s) y) := by
    simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_pow]
    ring
  simp_rw [hi]
  rw [integral_const_mul]
  linear_combination hd-he

end ArtinMatthews
