module

public import ArtinMatthews.SpectralEisensteinGreenMultiplier
public import ArtinMatthews.SpectralGamma0CuspEigenfunctions
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Bounded continuous tests on the genuine nonnegative energy axis.
The continuous symbol uses lambda=1/4+t² and the discrete symbols use
actual native energies, including complementary and residual energies. -/
noncomputable section
open Set MeasureTheory
open scoped BoundedContinuousFunction
namespace ArtinMatthews

abbrev SpectralEnergyTest := Ici (0:ℝ) →ᵇ ℂ

def spectralContinuousEnergyParameter : C(ℝ,Ici (0:ℝ)) where
  toFun t := ⟨spectralStoneEnergyFromFrequency t,by
    change (0:ℝ)≤1/4+t^2
    positivity⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous (fun t : ℝ => 1/4+t^2)
    fun_prop

def spectralContinuousTestSymbol (h : SpectralEnergyTest) : ℝ →ᵇ ℂ :=
  h.compContinuous spectralContinuousEnergyParameter

theorem spectralContinuousTestSymbol_apply (h : SpectralEnergyTest) (t : ℝ) :
    spectralContinuousTestSymbol h t=h (spectralContinuousEnergyParameter t) := rfl

theorem spectralContinuousTestSymbol_norm (h : SpectralEnergyTest) : ‖spectralContinuousTestSymbol h‖≤‖h‖ :=
  h.norm_compContinuous_le spectralContinuousEnergyParameter

def gamma0CuspidalTestSymbol (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (i : Gamma0AllHeightSpectralIndex N) : ℂ :=
  h ⟨gamma0AllHeightGradientSpectralValue N i,gamma0AllHeightGradientSpectralValue_nonneg N i⟩

theorem gamma0CuspidalTestSymbol_bound (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (i : Gamma0AllHeightSpectralIndex N) : ‖gamma0CuspidalTestSymbol N h i‖≤‖h‖ := h.norm_coe_le_norm _

def spectralGreenEnergyTest : SpectralEnergyTest :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun l : Ici (0:ℝ) => gamma0EnergyGreenWeight l)
    (by
      apply Continuous.inv₀
      · exact (Complex.continuous_ofReal.comp continuous_subtype_val).add continuous_const
      · intro l
        have hl : (0:ℝ)≤l := l.property
        have hp : (0:ℝ)<(l:ℝ)+1 := by linarith
        exact_mod_cast hp.ne')
    1 (fun l => by
      have hl : (0:ℝ)≤l := l.property
      rw [gamma0EnergyGreenWeight_eq_real,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr (by linarith))]
      simpa only [one_div,inv_one] using one_div_le_one_div_of_le zero_lt_one (show (1:ℝ)≤(l:ℝ)+1 by linarith))

theorem spectralGreenEnergyTest_apply (l : Ici (0:ℝ)) :
    spectralGreenEnergyTest l=gamma0EnergyGreenWeight l := rfl

theorem spectralContinuousTestSymbol_green (t : ℝ) :
    spectralContinuousTestSymbol spectralGreenEnergyTest t=gamma0EisensteinGreenWeight t := rfl

theorem gamma0CuspidalTestSymbol_green (N : ℕ) [NeZero N] (i : Gamma0AllHeightSpectralIndex N) :
    gamma0CuspidalTestSymbol N spectralGreenEnergyTest i=i.1 := by
  change gamma0EnergyGreenWeight (gamma0AllHeightGradientSpectralValue N i)=i.1
  rw [gamma0EnergyGreenWeight_eq_real,gamma0AllHeightGradientSpectralValue,sub_add_cancel,inv_inv,
    gamma0AllHeightSpectralValue_real]

end ArtinMatthews
