module

public import ArtinMatthews.SpectralBareSpectrumLimit
public import ArtinMatthews.SpectralBareEisensteinLimit
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

/-! Exact orientation reversal on the original bare spectral carrier. -/
namespace ArtinMatthews
open Set MeasureTheory
open scoped MatrixGroups BigOperators
noncomputable section

theorem gamma0BareCuspidalTerm_star_swap (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (a b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (i : Gamma0AllHeightSpectralIndex N) :
    gamma0BareCuspidalTerm N (star h) a b Y hY m n hm hn i =
      star (gamma0BareCuspidalTerm N h b a Y hY n m hn hm i) := by
  change star (gamma0CuspidalTestSymbol N h i) *
    (gamma0BareCuspidalAmplitude N i a Y hY m hm *
      star (gamma0BareCuspidalAmplitude N i b Y hY n hn)) =
    star (gamma0CuspidalTestSymbol N h i *
      (gamma0BareCuspidalAmplitude N i b Y hY n hn *
        star (gamma0BareCuspidalAmplitude N i a Y hY m hm)))
  simp only [star_mul, star_star] <;> ring

theorem gamma0BareContinuousRhoIntegrand_star_swap (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (a b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (t : ℝ) :
    gamma0BareContinuousRhoIntegrand N (star h) a b Y hY m n hm hn t =
      star (gamma0BareContinuousRhoIntegrand N h b a Y hY n m hn hm t) := by
  have hK : (∑ j : Gamma0EisensteinCuspClasses N,
      gamma0BareEisensteinSourceCoefficient N j a Y hY m hm t *
        star (gamma0BareEisensteinSourceCoefficient N j b Y hY n hn t)) =
      star (∑ j : Gamma0EisensteinCuspClasses N,
        gamma0BareEisensteinSourceCoefficient N j b Y hY n hn t *
          star (gamma0BareEisensteinSourceCoefficient N j a Y hY m hm t)) := by
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [star_mul, star_star] <;> ring
  unfold gamma0BareContinuousRhoIntegrand
  change (star (spectralContinuousTestSymbol h t) / ((2 * Real.pi : ℝ) : ℂ)) * _ =
    star ((spectralContinuousTestSymbol h t / ((2 * Real.pi : ℝ) : ℂ)) * _)
  have hscalar : star (spectralContinuousTestSymbol h t / ((2 * Real.pi : ℝ) : ℂ)) =
      star (spectralContinuousTestSymbol h t) / ((2 * Real.pi : ℝ) : ℂ) := by
    change (starRingEnd ℂ) _ = (starRingEnd ℂ) _ / _
    rw [map_div₀, Complex.conj_ofReal]
  rw [hK, star_mul, hscalar]
  ring

theorem gamma0BareResidualRhoTerm_star_swap (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (a b : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (l : Ici (0 : ℝ)) (j : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N l))) :
    gamma0BareResidualRhoTerm N (star h) a b m n hm hn l j =
      star (gamma0BareResidualRhoTerm N h b a n m hn hm l j) := by
  unfold gamma0BareResidualRhoTerm
  change star (h l) * _ = star (h l * _)
  simp only [star_mul, star_star] <;> ring

theorem gamma0BareSourceSpectralSide_star_swap (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (a b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    gamma0BareSourceSpectralSide N (star h) a b Y hY m n hm hn =
      star (gamma0BareSourceSpectralSide N h b a Y hY n m hn hm) := by
  have hC : (∑' i, gamma0BareCuspidalTerm N (star h) a b Y hY m n hm hn i) =
      star (∑' i, gamma0BareCuspidalTerm N h b a Y hY n m hn hm i) := by
    rw [tsum_star]
    exact tsum_congr (gamma0BareCuspidalTerm_star_swap N h a b Y hY m n hm hn)
  have hI : (∫ t in Ioi (0 : ℝ), gamma0BareContinuousRhoIntegrand N (star h) a b Y hY m n hm hn t) =
      star (∫ t in Ioi (0 : ℝ), gamma0BareContinuousRhoIntegrand N h b a Y hY n m hn hm t) := by
    calc
      _ = ∫ t in Ioi (0 : ℝ), star (gamma0BareContinuousRhoIntegrand N h b a Y hY n m hn hm t) :=
        setIntegral_congr_fun measurableSet_Ioi
          (fun t _ => gamma0BareContinuousRhoIntegrand_star_swap N h a b Y hY m n hm hn t)
      _ = _ := by simpa only [Complex.star_def] using
        (integral_conj (f := gamma0BareContinuousRhoIntegrand N h b a Y hY n m hn hm))
  have hR : gamma0BareResidualRhoSum N (star h) a b m n hm hn =
      star (gamma0BareResidualRhoSum N h b a n m hn hm) := by
    unfold gamma0BareResidualRhoSum
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact gamma0BareResidualRhoTerm_star_swap N h a b m n hm hn l j
  unfold gamma0BareSourceSpectralSide
  rw [hC, hI, hR, star_add, star_add]

theorem gamma0BareSourceSpectralSide_real_swap (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (hreal : ∀ l, star (h l) = h l)
    (a b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    gamma0BareSourceSpectralSide N h a b Y hY m n hm hn =
      star (gamma0BareSourceSpectralSide N h b a Y hY n m hn hm) := by
  have hh : star h = h := BoundedContinuousFunction.ext hreal
  simpa only [hh] using gamma0BareSourceSpectralSide_star_swap N h a b Y hY m n hm hn

theorem gamma0BareCuspidalTerm_norm_swap (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (a b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (i : Gamma0AllHeightSpectralIndex N) :
    ‖gamma0BareCuspidalTerm N h a b Y hY m n hm hn i‖ =
      ‖gamma0BareCuspidalTerm N h b a Y hY n m hn hm i‖ := by
  unfold gamma0BareCuspidalTerm
  simp only [norm_mul, norm_star]
  ring

theorem gamma0BareContinuousRhoIntegrand_norm_swap (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (a b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (t : ℝ) :
    ‖gamma0BareContinuousRhoIntegrand N h a b Y hY m n hm hn t‖ =
      ‖gamma0BareContinuousRhoIntegrand N h b a Y hY n m hn hm t‖ := by
  have htest : ‖gamma0BareContinuousRhoIntegrand N (star h) a b Y hY m n hm hn t‖ =
      ‖gamma0BareContinuousRhoIntegrand N h a b Y hY m n hm hn t‖ := by
    unfold gamma0BareContinuousRhoIntegrand
    change ‖(star (spectralContinuousTestSymbol h t) / ((2 * Real.pi : ℝ) : ℂ)) * _‖ =
      ‖(spectralContinuousTestSymbol h t / ((2 * Real.pi : ℝ) : ℂ)) * _‖
    simp only [norm_mul, norm_div, norm_star]
  rw [← htest, gamma0BareContinuousRhoIntegrand_star_swap, norm_star]

theorem gamma0BareResidualRhoTerm_norm_swap (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (a b : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (l : Ici (0 : ℝ)) (j : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N l))) :
    ‖gamma0BareResidualRhoTerm N h a b m n hm hn l j‖ =
      ‖gamma0BareResidualRhoTerm N h b a n m hn hm l j‖ := by
  unfold gamma0BareResidualRhoTerm
  simp only [norm_mul, norm_star]
  ring

theorem gamma0BareSource_absolute_swap (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (a b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hC : Summable (fun i => ‖gamma0BareCuspidalTerm N h a b Y hY m n hm hn i‖))
    (hI : IntegrableOn (gamma0BareContinuousRhoIntegrand N h a b Y hY m n hm hn) (Ioi (0 : ℝ))) :
    Summable (fun i => ‖gamma0BareCuspidalTerm N h b a Y hY n m hn hm i‖) ∧
      IntegrableOn (gamma0BareContinuousRhoIntegrand N h b a Y hY n m hn hm) (Ioi (0 : ℝ)) := by
  constructor
  · exact hC.congr (fun i => gamma0BareCuspidalTerm_norm_swap N h a b Y hY m n hm hn i)
  · apply hI.norm.mono'
      (gamma0BareContinuousRhoIntegrand_aestronglyMeasurable N h b a Y hY n m hn hm)
    exact ae_of_all _ (fun t =>
      (gamma0BareContinuousRhoIntegrand_norm_swap N h b a Y hY n m hn hm t).le)

end
end ArtinMatthews
