module

public import ArtinMatthews.ReflectionGaussianWeight
public import ArtinMatthews.SourcePoissonTripleKernel
public import ArtinMatthews.SourceSLocalProbeMellin
public import ArtinMatthews.SourcePoissonContourProduct
public import ArtinMatthews.SourcePoissonMellinPowers
public import ArtinMatthews.SourceSLocalProbeInversion
public import ArtinMatthews.VaryingKummerAnalyticSmoothMellin
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

namespace ArtinMatthews.SourcePhysical
open MeasureTheory NumberField NumberField.InfinitePlace IsDedekindDomain
open VaryingKummerAnalytic
open scoped NumberField ContDiff
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (v : InfinitePlace F)

def sourcePoissonNormalization : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)

/-- The literal physical Gaussian, compact weight and Fourier sheet attached
to a single nonzero frequency and four exterior ideals. -/
def sourcePoissonOrbitWeight (W₁ : ℝ → ℂ) (X Y Z qc qn qs qr qu : ℝ) : ℂ :=
  let A := qc * qn ^ 3
  ((Real.sqrt X / (Y * Real.sqrt qc * qn * A) : ℝ) : ℂ) *
    (reflectionGaussian (A / Z) : ℂ) * W₁ (qs / Y) *
    sourceSLocalProbeSheet F hζ S v (X * qu * qr ^ 6 / A)

theorem sourcePoissonOrbitWeight_eq_initialContour
    (W₁ : ℝ → ℂ) (hcompact : HasCompactSupport W₁)
    (hpositive : tsupport W₁ ⊆ Set.Ioi 0) (hsmooth : ContDiff ℝ ∞ W₁)
    {X Y Z qc qn qs qr qu : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (hc : 0 < qc) (hn : 0 < qn) (hs : 0 < qs) (hr : 0 < qr) (hu : 0 < qu) :
    sourcePoissonOrbitWeight F S hζ v W₁ X Y Z qc qn qs qr qu =
      sourcePoissonNormalization ^ 3 * ∫ p : SourcePoissonHeights,
        sourcePoissonTripleKernel X Y Z 4 4 2
          (fun t => mellin W₁ (sourcePoissonVertical 4 t))
          (fun t => sourceSLocalProbeMellin F hζ S v (sourcePoissonVertical 2 t))
          (fun p =>
            (qu : ℂ) ^ (-sourcePoissonVertical 2 p.1.2) *
            (qc : ℂ) ^ (-1 / 2 - sourcePoissonVertical 4 p.2) *
            (qn : ℂ) ^ (-1 - 3 * sourcePoissonVertical 4 p.2) *
            (qs : ℂ) ^ (-sourcePoissonVertical 4 p.1.1) *
            (qr : ℂ) ^ (-(6 * sourcePoissonVertical 2 p.1.2))) p
        ∂sourcePoissonHeightMeasure := by
  let A : ℝ := qc * qn ^ 3
  let L : ℝ := X * qu * qr ^ 6 / A
  let C : ℂ := (Real.sqrt X / (Y * Real.sqrt qc * qn * A) : ℝ)
  let f (y : ℝ) := ((qs / Y : ℝ) : ℂ) ^ (-sourcePoissonVertical 4 y) *
    mellin W₁ (sourcePoissonVertical 4 y)
  let g (y : ℝ) := (L : ℂ) ^ (-sourcePoissonVertical 2 y) *
    sourceSLocalProbeMellin F hζ S v (sourcePoissonVertical 2 y)
  let h (y : ℝ) := ((A / Z : ℝ) : ℂ) ^ (-sourcePoissonVertical 5 y) *
    Complex.exp ((sourcePoissonVertical 5 y) ^ 2)
  have hA : 0 < A := mul_pos hc (pow_pos hn _)
  have hL : 0 < L := div_pos (mul_pos (mul_pos hX hu) (pow_pos hr _)) hA
  have hf : sourcePoissonNormalization * (∫ y : ℝ, f y) = W₁ (qs / Y) :=
    smoothMellin_inversion_integral W₁ hcompact hpositive hsmooth 4 (div_pos hs hY)
  have hg : sourceSLocalProbeSheet F hζ S v L =
      sourcePoissonNormalization * (∫ y : ℝ, g y) := by
    simpa only [Complex.real_smul, sourcePoissonNormalization, g, sourcePoissonVertical] using
      sourceSLocalProbeSheet_eq_verticalIntegral F hζ S v 2 (by norm_num) hL
  have hh : sourcePoissonNormalization * (∫ y : ℝ, h y) =
      (reflectionGaussian (A / Z) : ℂ) := reflectionGaussian_inverse_mellin (div_pos hA hZ) 5
  have hp (p : SourcePoissonHeights) :
      sourcePoissonTripleKernel X Y Z 4 4 2
        (fun t => mellin W₁ (sourcePoissonVertical 4 t))
        (fun t => sourceSLocalProbeMellin F hζ S v (sourcePoissonVertical 2 t))
        (fun q => (qu : ℂ) ^ (-sourcePoissonVertical 2 q.1.2) *
          (qc : ℂ) ^ (-1 / 2 - sourcePoissonVertical 4 q.2) *
          (qn : ℂ) ^ (-1 - 3 * sourcePoissonVertical 4 q.2) *
          (qs : ℂ) ^ (-sourcePoissonVertical 4 q.1.1) *
          (qr : ℂ) ^ (-(6 * sourcePoissonVertical 2 q.1.2))) p =
        C * (f p.1.1 * g p.1.2 * h (p.2 + p.1.2)) := by
    dsimp only [sourcePoissonTripleKernel, f, g, h]
    let ξ := sourcePoissonVertical 4 p.2
    let w := sourcePoissonVertical 4 p.1.1
    let z := sourcePoissonVertical 2 p.1.2
    have ht : sourcePoissonVertical 5 (p.2 + p.1.2) = ξ + z - 1 := by
      simpa only [ξ, z, show (4 + 2 - 1 : ℝ) = 5 by norm_num] using
        (sourcePoissonVertical_add_sub_one 4 2 p.2 p.1.2).symm
    rw [ht]
    let D := Complex.exp ((ξ + z - 1) ^ 2) * mellin W₁ w *
      sourceSLocalProbeMellin F hζ S v z
    calc
      _ = ((X : ℂ) ^ (1 / 2 - z) * (Z : ℂ) ^ (ξ + z - 1) * (Y : ℂ) ^ (w - 1) *
          (qu : ℂ) ^ (-z) * (qc : ℂ) ^ (-1 / 2 - ξ) * (qn : ℂ) ^ (-1 - 3 * ξ) *
          (qs : ℂ) ^ (-w) * (qr : ℂ) ^ (-(6 * z))) * D := by
        dsimp only [ξ, w, z, D]
        ac_rfl
      _ = _ := by
        rw [← sourcePoissonMellinPowers hX hY hZ hc hn hs hr hu ξ w z]
        dsimp only [ξ, w, z, D, A, C, L]
        ac_rfl
  have hIntegral :
      (∫ p : SourcePoissonHeights, C * (f p.1.1 * g p.1.2 * h (p.2 + p.1.2))
        ∂sourcePoissonHeightMeasure) =
      C * ((∫ y : ℝ, f y) * (∫ y : ℝ, g y) * (∫ y : ℝ, h y)) := by
    rw [integral_const_mul, sourcePoissonHeight_integral_shear]
  rw [show sourcePoissonOrbitWeight F S hζ v W₁ X Y Z qc qn qs qr qu =
      C * (reflectionGaussian (A / Z) : ℂ) * W₁ (qs / Y) *
      sourceSLocalProbeSheet F hζ S v L from rfl, ← hf, ← hh, hg]
  simp_rw [hp]
  rw [hIntegral, pow_succ, pow_succ, pow_one]
  ac_rfl

end
end ArtinMatthews.SourcePhysical
