module

public import ArtinMatthews.SpectralPeterssonFourierAtHeight
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.MeasureTheory.Integral.IntegrableOn
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
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

open Set MeasureTheory UpperHalfPlane
noncomputable section

private theorem spectralWeightTwo_height_continuous (y : ℝ) (hy : 0 < y) :
    Continuous (fun x : ℝ => spectralPeterssonHeightPoint x y hy) := by
  apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
  simp only [Function.comp_def, spectralPeterssonHeightPoint_coe]
  fun_prop

theorem spectralWeightTwoFourier_integrable (F : UpperHalfPlane → ℂ)
    (hF : Continuous F) (n : ℕ+) (y : ℝ) (hy : 0 < y) :
    IntegrableOn (fun x => F (spectralPeterssonHeightPoint x y hy) *
      spectralPeterssonFourierWeight n (spectralPeterssonHeightPoint x y hy)) (Ioc (0 : ℝ) 1) := by
  have hC : Continuous (fun x => F (spectralPeterssonHeightPoint x y hy) *
      spectralPeterssonFourierWeight n (spectralPeterssonHeightPoint x y hy)) := by
    apply (hF.comp (spectralWeightTwo_height_continuous y hy)).mul
    unfold spectralPeterssonFourierWeight
    simp_rw [spectralPeterssonHeightPoint_coe]
    fun_prop
  exact (hC.integrableOn_Icc (μ := volume) (a := 0) (b := 1)).mono_set Ioc_subset_Icc_self

theorem spectralWeightTwoFourier_add (F G : UpperHalfPlane → ℂ)
    (hF : Continuous F) (hG : Continuous G) (n : ℕ+) (y : ℝ) (hy : 0 < y) :
    spectralPeterssonFourierAtHeight (fun z => F z + G z) n y hy =
      spectralPeterssonFourierAtHeight F n y hy + spectralPeterssonFourierAtHeight G n y hy := by
  unfold spectralPeterssonFourierAtHeight
  simp only [add_mul]
  exact integral_add (spectralWeightTwoFourier_integrable F hF n y hy)
    (spectralWeightTwoFourier_integrable G hG n y hy)

theorem spectralWeightTwoFourier_sum {ι : Type*} [Fintype ι] (F : ι → UpperHalfPlane → ℂ)
    (hF : ∀ i, Continuous (F i)) (n : ℕ+) (y : ℝ) (hy : 0 < y) :
    spectralPeterssonFourierAtHeight (fun z => ∑ i, F i z) n y hy =
      ∑ i, spectralPeterssonFourierAtHeight (F i) n y hy := by
  classical
  unfold spectralPeterssonFourierAtHeight
  simp only [Finset.sum_mul]
  exact integral_finsetSum _ (fun i _ => spectralWeightTwoFourier_integrable (F i) (hF i) n y hy)

end
end ArtinMatthews
