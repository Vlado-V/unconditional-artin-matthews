module

public import ArtinMatthews.SpectralCuspEisensteinWidthFormula
public import ArtinMatthews.SpectralCuspExceptionalMoment
public import ArtinMatthews.SpectralCompactExceptionalForcing
public import ArtinMatthews.SpectralGamma0LocalFourierBessel
public import ArtinMatthews.SpectralMixedCuspExceptionalWeil
public import ArtinMatthews.SpectralNativeBesselAmplitudeHeights
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

/-! A nonzero native mixed-cusp mode forces the Selberg exponent by the
actual compact singleton bound. The height can vary with the cutoff. -/
noncomputable section
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0MixedCusp_spectralValue_ge_three_sixteenths_of_amplitude
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    (i : Gamma0AllHeightSpectralIndex (r*s)) (n : ℤ) (hn : n ≠ 0)
    (hAmp : gamma0CuspBesselAmplitude (r*s) i (gamma0CuspOneOver s) 1 one_pos
      ((gamma0CuspFrequencyStep (r*s) (gamma0CuspOneOver s) : ℤ)*n)
      (gamma0CuspFrequencyStep_mul_ne_zero (r*s) (gamma0CuspOneOver s) hn) ≠ 0) :
    3/16 ≤ gamma0AllHeightGradientSpectralValue (r*s) i := by
  let eig := gamma0AllHeightGradientSpectralValue (r*s) i
  by_cases heig : eig ≤ 1/4
  · let κ := Real.sqrt (1/4-eig)
    let w : ℝ := gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s)
    let c := Real.exp (-Real.exp 1)/16
    let m := (gamma0CuspFrequencyStep (r*s) (gamma0CuspOneOver s) : ℤ)*n
    have hm : m ≠ 0 := gamma0CuspFrequencyStep_mul_ne_zero (r*s) (gamma0CuspOneOver s) hn
    let amp := gamma0CuspBesselAmplitude (r*s) i (gamma0CuspOneOver s) 1 one_pos m hm
    let W := c^2*‖(Real.sqrt w : ℂ)*amp‖^2
    let q := |cuspFourierFrequency 1 n|
    have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos (r*s) (gamma0CuspOneOver s))
    have hq : 0 < q := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 one_pos n hn)
    have hc : 0 < c := div_pos (Real.exp_pos _) (by norm_num)
    have hNorm : 0 < ‖(Real.sqrt w : ℂ)*amp‖ := norm_pos_iff.mpr
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hw).ne') hAmp)
    have hW : 0 < W := mul_pos (sq_pos_of_pos hc) (sq_pos_of_pos hNorm)
    have hκ : κ ≤ 1/4 := spectral_compact_exceptional_growth_forces_quarter hW hq (by
      intro ε hε _
      obtain ⟨D,hD,hWeil⟩ := gamma0MixedCusp_exceptional_singleton_weil hε
      let C := 8*D*(n.natAbs.divisors.card : ℝ)*Real.sqrt (Nat.gcd (r*s) n.natAbs : ℝ)/((r*s : ℕ) : ℝ)
      have hC : 0 ≤ C := by dsimp only [C]; positivity
      refine ⟨C,hC,?_⟩
      intro A hA hA₁
      let Y := (A/(q/w))/2
      have hCut : 0 < A/(q/w) := div_pos hA (div_pos hq hw)
      have hY : 0 < Y := half_pos hCut
      have hYA : Y < A/(q/w) := half_lt_self hCut
      classical
      have hi : ∀ j ∈ ({i} : Finset (Gamma0AllHeightSpectralIndex (r*s))),
          gamma0AllHeightGradientSpectralValue (r*s) j ≤ 1/4 := by
        intro j hj
        rw [Finset.mem_singleton.mp hj]
        exact heig
      have h := hWeil r s hcop {i} n hn hA hA₁ hY hYA hi
      have hAmpY := gamma0CuspBesselAmplitude_height_eq (r*s) i (gamma0CuspOneOver s)
        Y 1 hY one_pos m hm
      have hLeft : c^2*gamma0CuspExceptionalMoment (r*s) {i}
          (gamma0CuspOneOver s) Y hY n hn A = A^(-2*κ)*W := by
        unfold gamma0CuspExceptionalMoment
        dsimp only
        rw [Finset.sum_singleton]
        change c^2*(A^(-2*κ)*‖(Real.sqrt w : ℂ)*
          gamma0CuspBesselAmplitude (r*s) i (gamma0CuspOneOver s) Y hY m hm‖^2) = _
        rw [hAmpY]
        dsimp only [W,amp]
        ring
      have hRight : 1+8*D*(q/A)^ε*(n.natAbs.divisors.card : ℝ)*
          Real.sqrt (Nat.gcd (r*s) n.natAbs : ℝ)*Real.sqrt (q/A)/((r*s : ℕ) : ℝ) =
          1+C*(q/A)^ε*Real.sqrt (q/A) := by
        dsimp only [C]
        ring
      rw [← hLeft, ← hRight]
      exact h)
    have hSq := pow_le_pow_left₀ (Real.sqrt_nonneg (1/4-eig)) hκ 2
    change (Real.sqrt (1/4-eig))^2 ≤ (1/4 : ℝ)^2 at hSq
    rw [Real.sq_sqrt (sub_nonneg.mpr heig)] at hSq
    change 3/16 ≤ eig
    linarith
  · change 3/16 ≤ eig
    linarith

end ArtinMatthews
