module

public import ArtinMatthews.SourceAnnularFourierTest
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import ArtinMatthews.SourceComplexZetaFunctionalEquation
public import ArtinMatthews.SourceComplexZetaIntegrability
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

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory Set
open scoped SchwartzMap FourierTransform
noncomputable section

/-- At s=1/6 the complex-place multiplicative density is ‖z‖^(-5/3).
The actual constructed test survives the Fourier transform at this weight. -/
theorem sourceAnnularSchwartzTest_fourier_mellin_nonzero :
    (∫ z : ℂ, (𝓕 sourceAnnularSchwartzTest : 𝓢(ℂ, ℂ)) z *
      ((‖z‖ ^ (-(5 / 3 : ℝ)) : ℝ) : ℂ)) ≠ 0 := by
  apply source_complex_zeta_fourier_nonzero sourceAnnularSchwartzTest
    (5 / 3) (by norm_num) (by norm_num)
  convert sourceAnnularSchwartzTest_weighted_nonzero using 1
  norm_num

theorem sourceAnnularSchwartzTest_fourier_mellin_integrable :
    Integrable (fun z : ℂ => (𝓕 sourceAnnularSchwartzTest : 𝓢(ℂ, ℂ)) z *
      ((‖z‖ ^ (-(5 / 3 : ℝ)) : ℝ) : ℂ)) :=
  source_complex_schwartz_fourier_weighted_integrable sourceAnnularSchwartzTest
    (5 / 3) (by norm_num) (by norm_num)

end
end ArtinMatthews.VaryingKummerAnalytic
