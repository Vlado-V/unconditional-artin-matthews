module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.CubicMoment.Estimates.MellinWeights
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
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

namespace OAI

/-! The scalar factors on the symmetry line in the primitive Hecke
functional equation. These identities apply also to fixed infinity type.
They keep conductor-dependent phases outside the dual polynomial. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def heckeGammaRatio (k t : ℝ) : ℂ :=
  Complex.Gamma ((k+1/2:ℝ) - (t:ℂ)*Complex.I) /
    Complex.Gamma ((k+1/2:ℝ) + (t:ℂ)*Complex.I)

lemma norm_heckeGammaRatio {k : ℝ} (hk : 0 ≤ k) (t : ℝ) :
    ‖heckeGammaRatio k t‖ = 1 := by
  have hre : 0 < (((k+1/2:ℝ):ℂ) + (t:ℂ)*Complex.I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    linarith
  have hne := Complex.Gamma_ne_zero_of_re_pos hre
  have hc : ((k+1/2:ℝ):ℂ) - (t:ℂ)*Complex.I =
      starRingEnd ℂ (((k+1/2:ℝ):ℂ) + (t:ℂ)*Complex.I) := by
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
      sub_eq_add_neg]
  rw [heckeGammaRatio, hc, Complex.Gamma_conj, norm_div, Complex.norm_conj]
  exact div_self (norm_ne_zero_iff.mpr hne)

/-- `D` includes the fixed field factor in the completed L-function. -/
def heckeSymmetryFactor (ε : ℂ) (D Z k t τ : ℝ) : ℂ :=
  ε * mellinPhase (t-τ) D * mellinPhase τ Z * heckeGammaRatio k (τ-t)

lemma norm_heckeSymmetryFactor {ε : ℂ} (hε : ‖ε‖ = 1)
    (D Z k t τ : ℝ) (hk : 0 ≤ k) :
    ‖heckeSymmetryFactor ε D Z k t τ‖ = 1 := by
  simp [heckeSymmetryFactor, hε, norm_heckeGammaRatio hk]

/-- The entire character-dependent multiplier can be removed from the
square-sum norm before applying a common integral majorant. -/
lemma heckeSymmetry_square_sum {ι : Type*} (S : Finset ι)
    (ε : ι → ℂ) (D : ι → ℝ) (Z k t τ : ℝ) (v : ι → ℂ)
    (hε : ∀ i ∈ S, ‖ε i‖ = 1) (hk : 0 ≤ k) :
    (∑ i ∈ S, ‖heckeSymmetryFactor (ε i) (D i) Z k t τ * v i‖^2) =
      ∑ i ∈ S, ‖v i‖^2 := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [norm_mul, norm_heckeSymmetryFactor (hε i hi) _ _ _ _ _ hk, one_mul]

end CubicFirstMoment

end

end OAI
