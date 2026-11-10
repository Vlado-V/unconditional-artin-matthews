module

public import ArtinMatthews.SpectralPeterssonFourierAtHeight
public import ArtinMatthews.SpectralHolomorphicCuspSeed
public import ArtinMatthews.AtkinLehnerMixedWeight
public import ArtinMatthews.SpectralCuspTranslationAdmissibility
public import ArtinMatthews.SpectralFourierBruhatKernel
public import ArtinMatthews.SpectralPeterssonHeckeRescale
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact translation of the one-period Petersson coefficient, at the same height. -/

noncomputable section
open Matrix MeasureTheory Set UpperHalfPlane
open scoped Interval MatrixGroups

namespace ArtinMatthews

theorem spectralPeterssonHeightPoint_translate (x y : ℝ) (hy : 0 < y) (t : ℝ) :
    realTranslation t • spectralPeterssonHeightPoint x y hy =
      spectralPeterssonHeightPoint (x+t) y hy := by
  apply UpperHalfPlane.coe_injective
  rw [realTranslation_coe_smul, spectralPeterssonHeightPoint_coe, spectralPeterssonHeightPoint_coe]
  push_cast
  ring

theorem spectralPeterssonFourierWeight_translate (n : ℕ+) (t : ℝ) (z : UpperHalfPlane) :
    spectralPeterssonFourierWeight n (realTranslation t • z) =
      atkinPhase (-((n : ℝ)*t))*spectralPeterssonFourierWeight n z := by
  unfold spectralPeterssonFourierWeight atkinPhase
  rw [realTranslation_coe_smul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem spectralPeterssonFourierAtHeight_const_mul (v : ℂ) (F : UpperHalfPlane → ℂ)
    (n : ℕ+) (y : ℝ) (hy : 0 < y) :
    spectralPeterssonFourierAtHeight (fun z => v*F z) n y hy =
      v*spectralPeterssonFourierAtHeight F n y hy := by
  unfold spectralPeterssonFourierAtHeight
  simp_rw [mul_assoc, integral_const_mul]

theorem spectralPeterssonFourierAtHeight_translate (k : ℕ) (F : UpperHalfPlane → ℂ)
    (n : ℕ+) (y : ℝ) (hy : 0 < y) (t : ℝ)
    (hF : Function.Periodic (fun x => F (spectralPeterssonHeightPoint x y hy)) 1) :
    spectralPeterssonFourierAtHeight (spectralHolomorphicSlash k (realTranslation t) F) n y hy =
      atkinPhase ((n : ℝ)*t)*spectralPeterssonFourierAtHeight F n y hy := by
  let z (x : ℝ) := spectralPeterssonHeightPoint x y hy
  let f (x : ℝ) := F (z x)*spectralPeterssonFourierWeight n (z x)
  have hw (x d : ℝ) :
      spectralPeterssonFourierWeight n (z (x+d)) =
        atkinPhase (-((n : ℝ)*d))*spectralPeterssonFourierWeight n (z x) := by
    rw [show z (x+d) = realTranslation d • z x from (spectralPeterssonHeightPoint_translate x y hy d).symm,
      spectralPeterssonFourierWeight_translate]
  have hunit : atkinPhase (-((n : ℝ)*1)) = 1 := by
    simpa only [mul_one, Int.cast_neg, Int.cast_natCast] using atkinPhase_int (-(n : ℤ))
  have hf : Function.Periodic f 1 := by
    intro x
    dsimp only [f]
    rw [show F (z (x+1)) = F (z x) from hF x, hw x 1, hunit, one_mul]
  have hshift (x : ℝ) :
      F (realTranslation t • z x)*spectralPeterssonFourierWeight n (z x) =
        atkinPhase ((n : ℝ)*t)*f (x+t) := by
    have hback : spectralPeterssonFourierWeight n (z x) =
        atkinPhase ((n : ℝ)*t)*spectralPeterssonFourierWeight n (z (x+t)) := by
      rw [hw x t, ← mul_assoc, ← atkinPhase_add, add_neg_cancel, atkinPhase_zero, one_mul]
    rw [show realTranslation t • z x = z (x+t) from spectralPeterssonHeightPoint_translate x y hy t,
      hback]
    dsimp only [f]
    ring
  have hI : (∫ x in Ioc (0 : ℝ) 1, f (x+t)) = ∫ x in Ioc (0 : ℝ) 1, f x := by
    rw [← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_comp_add_right]
    simpa only [zero_add, add_comm (1 : ℝ) t] using hf.intervalIntegral_add_eq t 0
  unfold spectralPeterssonFourierAtHeight
  simp_rw [spectralHolomorphicSlash_realTranslation]
  change (∫ x in Ioc (0 : ℝ) 1, F (realTranslation t • z x)*spectralPeterssonFourierWeight n (z x)) =
    atkinPhase ((n : ℝ)*t)*(∫ x in Ioc (0 : ℝ) 1, f x)
  simp_rw [hshift]
  rw [integral_const_mul, hI]

theorem spectralPeterssonFourierAtHeight_periodic_of_gamma0 (N k : ℕ)
    (F : UpperHalfPlane → ℂ)
    (hF : ∀ γ : CongruenceSubgroup.Gamma0 N, spectralHolomorphicSlash k (atkinRealMap γ.val) F = F)
    (y : ℝ) (hy : 0 < y) :
    Function.Periodic (fun x => F (spectralPeterssonHeightPoint x y hy)) 1 := by
  let γ : CongruenceSubgroup.Gamma0 N := ⟨integerTranslation 1, by
    rw [CongruenceSubgroup.Gamma0_mem]
    change ((0 : ℤ) : ZMod N) = 0
    exact Int.cast_zero⟩
  have hγ : atkinRealMap γ.val = realTranslation 1 := by
    simp only [γ, atkinRealMap_integerTranslation, Int.cast_one]
  intro x
  have h := congrFun (hF γ) (spectralPeterssonHeightPoint x y hy)
  rw [hγ, spectralHolomorphicSlash_realTranslation, spectralPeterssonHeightPoint_translate] at h
  exact h

end ArtinMatthews
