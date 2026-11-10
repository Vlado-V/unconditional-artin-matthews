module

public import ArtinMatthews.SpectralHeatSpectralPairing
public import ArtinMatthews.SpectralTrueWidthPhysicalSummability
public import ArtinMatthews.SpectralNativeHeatAction
public import ArtinMatthews.SpectralNativeHeatMoment
public import ArtinMatthews.SpectralTwoDecayingPoincare
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

namespace ArtinMatthews
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace
noncomputable section

theorem gamma0HeatSource_inequivalent_physical
    (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (hneq : ¬ gamma0EisensteinCuspsEquivalent N r s)
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (R : ℝ) (hR : 0 < R) (G : ℝ → ℂ)
    (hreg : SpectralKLHeatRegularity G)
    (hzero : ∀ x : ℝ, x ≤ 0 → G x = 0) (hreal : ∀ x, star (G x) = G x)
    (W : ℂ → ℂ) (h : SpectralEnergyTest) (hr : ∀ l, star (h l) = h l)
    (he : ∀ l : Ici (0 : ℝ), W ((-Complex.I) *
      Complex.sqrt (1 / 4 - ((l : ℝ) : ℂ))) = h l)
    (ht : ∀ t : ℝ, W (t : ℂ) = spectralContinuousTestSymbol h t)
    (htransform : ∀ ν : ℂ, |ν.re| ≤ 1 / 2 →
      spectralKLCompactOrderTransform G ν =
        W ((-Complex.I) * ν) * Complex.exp (ν ^ 2 / (R : ℂ) ^ 2)) :
    gamma0HeatSourceSpectralSide N h r s Y hY m n hm hn R =
      (1 / 4 : ℂ) * ∑' c : Ioi (0 : ℕ),
        gamma0TrueWidthPhysicalFibre N r s c m n G (spectralKLHeatProfile R) := by
  let P := gamma0HeatHeightProfile N r m hm R hR
  obtain ⟨Q, hQ, _, hphysical, _, hact⟩ :=
    gamma0HeatPoincareTest_window_action N s n hn R hR G hreg hzero hreal W h hr he ht htransform
  have hF := spectralKLHeatRegularity_five_eighths _
    (spectralKLHeatProfile_properties R hR) (spectralKLHeatProfile_nonpositive_zero R)
  have hMoment : Integrable (fun x : ℝ =>
      x ^ (-(5 / 8 : ℝ)) * ‖gamma0PrimitivePhysicalTest N r m P.value x‖)
      spectralKLPhysicalMeasure := by
    simpa only [P, gamma0HeatHeightProfile_physical] using hF.1
  obtain ⟨M, hM, hpower⟩ := (spectralKLHeatRegularity_five_eighths G hreg hzero).2
  have hQpower : ∀ x : ℝ, 0 < x →
      ‖gamma0PrimitivePhysicalTest N s n Q.value x‖ ≤ M * x ^ (5 / 8 : ℝ) := by
    simpa only [hphysical] using hpower
  have hgeom := gamma0TwoDecayingPoincare_inequivalent_physical N r s hneq
    m n hm hn P Q (by rw [hQ]; norm_num)
    (B := (5 / 8 : ℝ)) (by norm_num) (by norm_num) hM hMoment hQpower
  rw [← gamma0HeatPoincareTest_source_pairing_eq N h r s Y hY m n hm hn R hR,
    hact, inner_smul_right]
  change (1 / 4 : ℂ) * inner ℂ (gamma0PrimitiveDecayingPoincare N r m P)
    (gamma0PrimitiveDecayingPoincare N s n Q) = _
  rw [hgeom, hphysical]
  dsimp only [P]
  rw [gamma0HeatHeightProfile_physical]

theorem gamma0HeatSource_sameCusp_physical
    (N : ℕ) [NeZero N] (r : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (R : ℝ) (hR : 0 < R) (G : ℝ → ℂ)
    (hreg : SpectralKLHeatRegularity G)
    (hzero : ∀ x : ℝ, x ≤ 0 → G x = 0) (hreal : ∀ x, star (G x) = G x)
    (W : ℂ → ℂ) (h : SpectralEnergyTest) (hr : ∀ l, star (h l) = h l)
    (he : ∀ l : Ici (0 : ℝ), W ((-Complex.I) *
      Complex.sqrt (1 / 4 - ((l : ℝ) : ℂ))) = h l)
    (ht : ∀ t : ℝ, W (t : ℂ) = spectralContinuousTestSymbol h t)
    (htransform : ∀ ν : ℂ, |ν.re| ≤ 1 / 2 →
      spectralKLCompactOrderTransform G ν =
        W ((-Complex.I) * ν) * Complex.exp (ν ^ 2 / (R : ℂ) ^ 2)) :
    gamma0HeatSourceSpectralSide N h r r Y hY m n hm hn R =
      (1 / 4 : ℂ) * ((if m = n then (gamma0CuspTrueWidth N r : ℂ) *
        (cuspFourierHeightPairing
          (fun y => Real.sqrt (y / (gamma0CuspTrueWidth N r : ℝ)) *
            (spectralKLHeatProfile R
              ((|cuspFourierFrequency 1 m| / (gamma0CuspTrueWidth N r : ℝ)) * y)).re)
          (fun y => Real.sqrt (y / (gamma0CuspTrueWidth N r : ℝ)) *
            (G ((|cuspFourierFrequency 1 n| / (gamma0CuspTrueWidth N r : ℝ)) * y)).re) : ℂ)
        else 0) +
        ∑' c : Ioi (0 : ℕ),
          gamma0TrueWidthPhysicalFibre N r r c m n G (spectralKLHeatProfile R)) := by
  let P := gamma0HeatHeightProfile N r m hm R hR
  obtain ⟨Q, hQ, hvalue, hphysical, _, hact⟩ :=
    gamma0HeatPoincareTest_window_action N r n hn R hR G hreg hzero hreal W h hr he ht htransform
  have hF := spectralKLHeatRegularity_five_eighths _
    (spectralKLHeatProfile_properties R hR) (spectralKLHeatProfile_nonpositive_zero R)
  have hMoment : Integrable (fun x : ℝ =>
      x ^ (-(5 / 8 : ℝ)) * ‖gamma0PrimitivePhysicalTest N r m P.value x‖)
      spectralKLPhysicalMeasure := by
    simpa only [P, gamma0HeatHeightProfile_physical] using hF.1
  obtain ⟨M, hM, hpower⟩ := (spectralKLHeatRegularity_five_eighths G hreg hzero).2
  have hQpower : ∀ x : ℝ, 0 < x →
      ‖gamma0PrimitivePhysicalTest N r n Q.value x‖ ≤ M * x ^ (5 / 8 : ℝ) := by
    simpa only [hphysical] using hpower
  have hgeom := gamma0TwoDecayingPoincare_sameCusp_physical N r
    m n hm hn P Q (by rw [hQ]; norm_num)
    (B := (5 / 8 : ℝ)) (by norm_num) (by norm_num) hM hMoment hQpower
  rw [← gamma0HeatPoincareTest_source_pairing_eq N h r r Y hY m n hm hn R hR,
    hact, inner_smul_right]
  change (1 / 4 : ℂ) * inner ℂ (gamma0PrimitiveDecayingPoincare N r m P)
    (gamma0PrimitiveDecayingPoincare N r n Q) = _
  rw [hgeom, hphysical]
  dsimp only [P]
  rw [gamma0HeatHeightProfile_physical, funext hvalue,
    funext (gamma0HeatHeightProfile_value N r m hm R hR)]

end
end ArtinMatthews
