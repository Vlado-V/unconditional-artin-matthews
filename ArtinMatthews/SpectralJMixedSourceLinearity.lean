module

public import ArtinMatthews.SpectralBareSpectrumLimit
public import ArtinMatthews.SpectralJClippedEnergyTest
public import ArtinMatthews.SpectralJRealTestParts
public import ArtinMatthews.SpectralABLOppositeComplexTrace
public import ArtinMatthews.SpectralJClippedLinearity
public import ArtinMatthews.SpectralJSourceAbsolute
public import ArtinMatthews.SpectralNativeHermitian
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

/-! Complex linearity of the actual clipped mixed-cusp native source. -/

namespace ArtinMatthews
open Set Complex
open scoped ContDiff MatrixGroups
noncomputable section

theorem gamma0MixedJ_clipped_source_parts
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    let hRe := spectralJClippedEnergyTest (spectralJRealTest f)
      (spectralJRealTest_contDiff f hf) (spectralJRealTest_hasCompactSupport f hc)
      ((spectralJRealTest_tsupport f).trans hp)
    let hIm := spectralJClippedEnergyTest (spectralJImagTest f)
      (spectralJImagTest_contDiff f hf) (spectralJImagTest_hasCompactSupport f hc)
      ((spectralJImagTest_tsupport f).trans hp)
    gamma0BareSourceSpectralSide (r*s) (spectralJClippedEnergyTest f hf hc hp)
      (gamma0CuspOneOver s) 1 Y hY n m hn hm =
    gamma0BareSourceSpectralSide (r*s) hRe (gamma0CuspOneOver s) 1 Y hY n m hn hm +
      I * gamma0BareSourceSpectralSide (r*s) hIm (gamma0CuspOneOver s) 1 Y hY n m hn hm := by
  let fRe := spectralJRealTest f
  let fIm := spectralJImagTest f
  have hfRe := spectralJRealTest_contDiff f hf
  have hfIm := spectralJImagTest_contDiff f hf
  have hcRe := spectralJRealTest_hasCompactSupport f hc
  have hcIm := spectralJImagTest_hasCompactSupport f hc
  have hpRe := (spectralJRealTest_tsupport f).trans hp
  have hpIm := (spectralJImagTest_tsupport f).trans hp
  let h := spectralJClippedEnergyTest f hf hc hp
  let hRe := spectralJClippedEnergyTest fRe hfRe hcRe hpRe
  let hIm := spectralJClippedEnergyTest fIm hfIm hcIm hpIm
  have hparts (l : Ici (0 : ℝ)) : h l = hRe l + I * hIm l :=
    spectralJClippedWeight_parts f hf.continuous hc hp (l : ℝ)
  obtain ⟨hCRe, hIRe⟩ := gamma0JSource_absolute fRe hfRe hcRe hpRe r s hcop Y hY m n hm hn
  obtain ⟨hCIm, hIIm⟩ := gamma0JSource_absolute fIm hfIm hcIm hpIm r s hcop Y hY m n hm hn
  obtain ⟨hCRe', hIRe'⟩ := gamma0BareSource_absolute_swap (r*s) hRe 1 (gamma0CuspOneOver s)
    Y hY m n hm hn hCRe hIRe
  obtain ⟨hCIm', hIIm'⟩ := gamma0BareSource_absolute_swap (r*s) hIm 1 (gamma0CuspOneOver s)
    Y hY m n hm hn hCIm hIIm
  exact gamma0BareSourceSpectralSide_add_mul (r*s) h hRe hIm I hparts
    (gamma0CuspOneOver s) 1 Y hY n m hn hm hCRe' hCIm' hIRe' hIIm'

end
end ArtinMatthews
