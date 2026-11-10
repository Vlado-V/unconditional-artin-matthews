module

public import ArtinMatthews.SpectralPeterssonCuspForm
public import ArtinMatthews.SpectralPeterssonCutRows
public import ArtinMatthews.SpectralPeterssonGammaTail
public import ArtinMatthews.SpectralPeterssonSourceGram
public import ArtinMatthews.SpectralPeterssonQCoefficient
public import ArtinMatthews.SpectralPeterssonSourceForms
public import ArtinMatthews.SpectralPeterssonTruncatedMass
public import ArtinMatthews.SpectralPeterssonTruncatedUnfold
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The cut vector pairs with every actual cusp form by the same fixed
incomplete-Gamma factor, at infinity and at the exact-divisor cusp. -/
noncomputable section
open Set Matrix UpperHalfPlane
open scoped MatrixGroups ModularForm Manifold

namespace ArtinMatthews

theorem gamma0PeterssonTruncatedInner_cuspForm (N k : ℕ) [NeZero N] (hk : 2 ≤ k)
    (a : SL(2, ℤ)) (n : ℕ+) (A : ℝ) (hA : 0 < A)
    (F : CuspForm (gamma0PeterssonRealGroup N) (k : ℤ)) :
    gamma0PeterssonInner N k (gamma0PeterssonTruncatedPoincare N a k n A) F =
      (spectralPeterssonTruncatedMass k n A : ℂ)*
        (UpperHalfPlane.qExpansion 1 (spectralHolomorphicSlash k (gamma0TrueCuspScaling N a) F)).coeff (n : ℕ) := by
  let σ := gamma0TrueCuspScaling N a
  obtain ⟨M,hM⟩ := gamma0PeterssonCuspForm_weighted_bound N k F
  have hD : MDiff (spectralHolomorphicSlash k σ F) :=
    F.holo'.slash (k : ℤ) (Matrix.SpecialLinearGroup.mapGL ℝ σ)
  refine gamma0PeterssonTruncatedInner_reproduce N a k hk n A hA F
    (gamma0PeterssonCuspForm_slash_gamma0 N k F) hD.continuous M (fun z => ?_) _
    (gamma0PeterssonCuspForm_trueChart_qCoefficient N k (by omega) a F n)
  change spectralPeterssonWeightedNorm k (spectralHolomorphicSlash k σ F) z ≤ M
  rw [spectralPeterssonWeightedNorm_slash]
  exact hM _

private theorem normalization_mul_mass (k : ℕ) (hk : 2 ≤ k) (n : ℕ+) :
    spectralPeterssonNormalization k n*spectralPeterssonReproducingMass k n =
      Real.sqrt (spectralPeterssonReproducingMass k n) := by
  let M := spectralPeterssonReproducingMass k n
  have hM : 0 < M := spectralPeterssonReproducingMass_pos k hk n
  change (Real.sqrt M)⁻¹*M = Real.sqrt M
  calc
    _ = (Real.sqrt M)⁻¹*(Real.sqrt M)^2 := by rw [Real.sq_sqrt hM.le]
    _ = _ := by rw [pow_two,← mul_assoc,inv_mul_cancel₀ (Real.sqrt_pos.mpr hM).ne',one_mul]

private theorem truncated_normalized_pair (N k : ℕ) [NeZero N] (hk : 2 ≤ k)
    (a : SL(2, ℤ)) (n : ℕ+) (A : ℝ) (hA : 0 < A)
    (F : CuspForm (gamma0PeterssonRealGroup N) (k : ℤ)) :
    gamma0PeterssonInner N k
      (fun z => (spectralPeterssonNormalization k n : ℂ)*gamma0PeterssonTruncatedPoincare N a k n A z) F =
      (spectralPeterssonGammaTailRatio k A : ℂ)*
        ((Real.sqrt (spectralPeterssonReproducingMass k n) : ℂ)*
          (UpperHalfPlane.qExpansion 1 (spectralHolomorphicSlash k (gamma0TrueCuspScaling N a) F)).coeff (n : ℕ)) := by
  have hs := gamma0PeterssonInner_scale_real N k (spectralPeterssonNormalization k n) 1
    (gamma0PeterssonTruncatedPoincare N a k n A) F
  simp only [Complex.ofReal_one,one_mul,mul_one] at hs
  rw [hs,gamma0PeterssonTruncatedInner_cuspForm N k hk a n A hA F,spectralPeterssonTruncatedMass_eq k hk]
  push_cast
  calc
    _ = ((spectralPeterssonNormalization k n*spectralPeterssonReproducingMass k n : ℝ) : ℂ)*
      (spectralPeterssonGammaTailRatio k A : ℂ)*
        (UpperHalfPlane.qExpansion 1 (spectralHolomorphicSlash k (gamma0TrueCuspScaling N a) F)).coeff (n : ℕ) := by
      push_cast
      ring
    _ = _ := by rw [normalization_mul_mass k hk n]; ring

theorem gamma0PeterssonCutSourceInfinity_pairing (N k : ℕ) [NeZero N]
    (hk : 2 ≤ k) (hEven : Even k) (n : ℕ+) (A : ℝ) (hA : 0 < A)
    (F : CuspForm (gamma0PeterssonRealGroup N) (k : ℤ)) :
    gamma0PeterssonInner N k
      (fun z => (spectralPeterssonNormalization k n : ℂ)*gamma0PeterssonTruncatedPoincare N 1 k n A z) F =
      (spectralPeterssonGammaTailRatio k A : ℂ)*gamma0PeterssonInner N k (gamma0PeterssonSourceInfinity N k n) F := by
  rw [gamma0PeterssonSourceInfinity_reproduce N k hk hEven n F]
  exact truncated_normalized_pair N k hk 1 n A hA F

theorem gamma0PeterssonCutSourceAtkin_pairing (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1)
    (k : ℕ) (hk : 2 ≤ k) (hEven : Even k) (n : ℕ+) (A : ℝ) (hA : 0 < A)
    (F : CuspForm (gamma0PeterssonRealGroup (r*s)) (k : ℤ)) :
    gamma0PeterssonInner (r*s) k
      (fun z => (spectralPeterssonNormalization k n : ℂ)*
        gamma0PeterssonTruncatedPoincare (r*s) (gamma0CuspOneOver s) k n A z) F =
      (spectralPeterssonGammaTailRatio k A : ℂ)*
        gamma0PeterssonInner (r*s) k (gamma0PeterssonSourceAtkin r s hab k n) F := by
  rw [gamma0PeterssonSourceAtkin_reproduce r s hcop hab k hk hEven n F]
  exact truncated_normalized_pair (r*s) k hk (gamma0CuspOneOver s) n A hA F

end ArtinMatthews
