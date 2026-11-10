module

public import Mathlib.NumberTheory.ModularForms.Petersson
public import ArtinMatthews.AtkinLehnerMixedPhase
public import ArtinMatthews.SpectralCuspTranslationAdmissibility
public import ArtinMatthews.SpectralFourierBruhatKernel
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

/-! The literal holomorphic cusp seed and determinant-one slash action,
with the Petersson measure convention of the native cusp charts. -/

noncomputable section
open Matrix UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace ArtinMatthews

def spectralHolomorphicCuspSeed (m : ℕ) (z : UpperHalfPlane) : ℂ :=
  Complex.exp (2*(Real.pi : ℂ)*Complex.I*(m : ℂ)*(z : ℂ))

def spectralHolomorphicSlash (k : ℕ) (g : SL(2, ℝ))
    (F : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  F ∣[(k : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ g

theorem spectralHolomorphicSlash_apply (k : ℕ) (g : SL(2, ℝ))
    (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    spectralHolomorphicSlash k g F z =
      F (g • z)/(((g 1 0 : ℝ) : ℂ)*(z : ℂ)+((g 1 1 : ℝ) : ℂ))^k := by
  have haction : Matrix.SpecialLinearGroup.mapGL ℝ g • z = g • z := rfl
  rw [spectralHolomorphicSlash, ModularForm.slash_apply]
  simp [UpperHalfPlane.σ, UpperHalfPlane.denom, _root_.zpow_neg, div_eq_mul_inv, haction]

theorem spectralHolomorphicSlash_mul (k : ℕ) (g h : SL(2, ℝ))
    (F : UpperHalfPlane → ℂ) :
    spectralHolomorphicSlash k (g*h) F =
      spectralHolomorphicSlash k h (spectralHolomorphicSlash k g F) := by
  simp only [spectralHolomorphicSlash, map_mul, SlashAction.slash_mul]

theorem spectralHolomorphicSlash_neg (k : ℕ) (hk : Even k) (g : SL(2, ℝ))
    (F : UpperHalfPlane → ℂ) :
    spectralHolomorphicSlash k (-g) F = spectralHolomorphicSlash k g F := by
  have hmap : Matrix.SpecialLinearGroup.mapGL ℝ (-g) =
      -(Matrix.SpecialLinearGroup.mapGL ℝ g) := by
    ext i j
    simp
  have hsm (z : UpperHalfPlane) : (-g) • z = g • z := by
    change Matrix.SpecialLinearGroup.mapGL ℝ (-g) • z =
      Matrix.SpecialLinearGroup.mapGL ℝ g • z
    rw [hmap, UpperHalfPlane.neg_smul]
  funext z
  rw [spectralHolomorphicSlash_apply, spectralHolomorphicSlash_apply, hsm]
  have hdenom : (((-g) 1 0 : ℝ) : ℂ)*(z : ℂ)+(((-g) 1 1 : ℝ) : ℂ) =
      -(((g 1 0 : ℝ) : ℂ)*(z : ℂ)+((g 1 1 : ℝ) : ℂ)) := by
    simp
    ring
  rw [hdenom, hk.neg_pow]

theorem spectralHolomorphicCuspSeed_norm (m : ℕ) (z : UpperHalfPlane) :
    ‖spectralHolomorphicCuspSeed m z‖ = Real.exp (-(2*Real.pi*(m : ℝ)*z.im)) := by
  rw [spectralHolomorphicCuspSeed, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem spectralHolomorphicCuspSeed_norm_le_one (m : ℕ) (z : UpperHalfPlane) :
    ‖spectralHolomorphicCuspSeed m z‖ ≤ 1 := by
  rw [spectralHolomorphicCuspSeed_norm, Real.exp_le_one_iff]
  exact neg_nonpos.mpr (by positivity)

theorem spectralHolomorphicCuspSeed_slash_translation (k m : ℕ) (l : ℤ) :
    spectralHolomorphicSlash k (realTranslation (l : ℝ)) (spectralHolomorphicCuspSeed m) =
      spectralHolomorphicCuspSeed m := by
  funext z
  rw [spectralHolomorphicSlash_apply]
  have hdenom : ((((realTranslation (l : ℝ)) 1 0 : ℝ) : ℂ)*(z : ℂ)+
      (((realTranslation (l : ℝ)) 1 1 : ℝ) : ℂ)) = 1 := by simp [realTranslation]
  rw [hdenom, one_pow, div_one]
  simp only [spectralHolomorphicCuspSeed, realTranslation_coe_smul, Complex.ofReal_intCast]
  rw [mul_add, Complex.exp_add]
  have hperiod : Complex.exp (2*(Real.pi : ℂ)*Complex.I*(m : ℂ)*(l : ℂ)) = 1 := by
    have h := atkinPhase_int ((m : ℤ)*l)
    simpa only [atkinPhase, Int.cast_mul, Int.cast_natCast, Complex.ofReal_intCast,
      Complex.ofReal_mul, Complex.ofReal_natCast, mul_assoc] using h
  rw [hperiod, mul_one]

theorem spectralHolomorphicPetersson_slash (k : ℕ) (g : SL(2, ℝ))
    (F G : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    UpperHalfPlane.petersson (k : ℤ) (spectralHolomorphicSlash k g F)
      (spectralHolomorphicSlash k g G) z =
        UpperHalfPlane.petersson (k : ℤ) F G (g • z) := by
  have haction : Matrix.SpecialLinearGroup.mapGL ℝ g • z = g • z := rfl
  rw [spectralHolomorphicSlash, spectralHolomorphicSlash, UpperHalfPlane.petersson_slash]
  simp [UpperHalfPlane.σ, haction]

end ArtinMatthews
