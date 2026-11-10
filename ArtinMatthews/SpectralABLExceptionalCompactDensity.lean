module

public import ArtinMatthews.SpectralCuspExceptionalMoment
public import ArtinMatthews.SpectralMixedSameCuspDiagonalGramBound
public import ArtinMatthews.SpectralABLExceptionalCompactWeil
public import ArtinMatthews.SpectralGamma0UniformGap
public import ArtinMatthews.SpectralMixedCuspExceptionalBessel
public import ArtinMatthews.SpectralMixedCuspExceptionalWeil
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The uniform native gap controls the cosine denominator in the
actual compact true-width exceptional density. -/

noncomputable section
open scoped MatrixGroups BigOperators
namespace ArtinMatthews

theorem gamma0Cuspidal_complementary_parameter_le_quarter (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) :
    Real.sqrt (1/4-gamma0AllHeightGradientSpectralValue N i) ≤ 1/4 := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  linarith [gamma0AllHeightGradientSpectralValue_ge_three_sixteenths N i]

theorem gamma0Cuspidal_complementary_cos_lower (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) :
    Real.cos (Real.pi/4) ≤
      Real.cos (Real.pi*Real.sqrt (1/4-gamma0AllHeightGradientSpectralValue N i)) := by
  apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
  rw [show Real.pi/4 = Real.pi*(1/4 : ℝ) by ring]
  exact mul_le_mul_of_nonneg_left (gamma0Cuspidal_complementary_parameter_le_quarter N i) Real.pi_pos.le

def gamma0CuspCosineExceptionalMoment (N : ℕ) [NeZero N]
    (u : Finset (Gamma0AllHeightSpectralIndex N)) (b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (n : ℤ) (hn : n ≠ 0) (a : ℝ) : ℝ :=
  let w := (gamma0CuspTrueWidth N b : ℝ)
  let nN := (gamma0CuspFrequencyStep N b : ℤ)*n
  let κ (i : Gamma0AllHeightSpectralIndex N) := Real.sqrt (1/4-gamma0AllHeightGradientSpectralValue N i)
  ∑ i ∈ u, a^(-4*κ i)*‖(Real.sqrt w : ℂ)*gamma0CuspBesselAmplitude N i b Y hY nN
      (gamma0CuspFrequencyStep_mul_ne_zero N b hn)‖^2/Real.cos (Real.pi*κ i)

theorem gamma0CuspCosineExceptionalMoment_le (N : ℕ) [NeZero N]
    (u : Finset (Gamma0AllHeightSpectralIndex N)) (b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (n : ℤ) (hn : n ≠ 0) {a : ℝ} (ha : 0 < a) :
    Real.cos (Real.pi/4)*gamma0CuspCosineExceptionalMoment N u b Y hY n hn a ≤
      gamma0CuspExceptionalMoment N u b Y hY n hn (a^2/2) := by
  let e := Real.cos (Real.pi/4)
  have he : 0 < e := by dsimp only [e]; rw [Real.cos_pi_div_four]; positivity
  unfold gamma0CuspCosineExceptionalMoment gamma0CuspExceptionalMoment
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  let κ := Real.sqrt (1/4-gamma0AllHeightGradientSpectralValue N i)
  let W := ‖(Real.sqrt (gamma0CuspTrueWidth N b : ℝ) : ℂ)*
    gamma0CuspBesselAmplitude N i b Y hY ((gamma0CuspFrequencyStep N b : ℤ)*n)
      (gamma0CuspFrequencyStep_mul_ne_zero N b hn)‖^2
  have hcos : e ≤ Real.cos (Real.pi*κ) := gamma0Cuspidal_complementary_cos_lower N i
  have hpow : a^(-4*κ) ≤ (a^2/2)^(-2*κ) := by
    have heq : (a^2)^(-2*κ) = a^(-4*κ) := by
      simpa only [div_one] using spectralExceptionalABLWeight_eq a 1 κ (by positivity)
    rw [← heq]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [sq_nonneg a])
      (by dsimp only [κ]; linarith [Real.sqrt_nonneg (1/4-gamma0AllHeightGradientSpectralValue N i)])
  have hw : 0 ≤ W := sq_nonneg _
  have hf : 0 ≤ a^(-4*κ)*W := mul_nonneg (Real.rpow_nonneg ha.le _) hw
  change e*(a^(-4*κ)*W/Real.cos (Real.pi*κ)) ≤ (a^2/2)^(-2*κ)*W
  calc
    _ ≤ a^(-4*κ)*W := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (he.trans_le hcos)).mpr
      exact (mul_le_mul_of_nonneg_right hcos hf).trans_eq (mul_comm _ _)
    _ ≤ _ := mul_le_mul_of_nonneg_right hpow hw

theorem gamma0MixedCusp_exceptional_compact_cosine_prefix_le
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    (u : Finset (Gamma0AllHeightSpectralIndex (r*s))) (n : ℤ) (hn : n ≠ 0)
    {a Y : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hY : 0 < Y)
    (hYA : Y < (a^2/2)/(|cuspFourierFrequency 1 n| /
      (gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ)))
    (heig : ∀ i ∈ u, gamma0AllHeightGradientSpectralValue (r*s) i ≤ 1/4) :
    (Real.exp (-Real.exp 1)/16)^2 *
      (Real.cos (Real.pi/4)*gamma0CuspCosineExceptionalMoment (r*s) u (gamma0CuspOneOver s) Y hY n hn a) ≤
      1+8*spectralKloostermanDiagSum (r*s) n (|cuspFourierFrequency 1 n| / (a^2/2)) := by
  have hA : 0 < a^2/2 := by positivity
  have hA1 : 2*(a^2/2) ≤ 1 := by linarith [pow_le_pow_left₀ ha.le ha1 2]
  have h := gamma0MixedCusp_exceptional_singleton_compact_bound r s hcop u n hn
    (A := a^2/2) hA hA1 hY hYA heig
  have hm := gamma0CuspCosineExceptionalMoment_le (r*s) u (gamma0CuspOneOver s) Y hY n hn ha
  exact (mul_le_mul_of_nonneg_left hm (sq_nonneg _)).trans h

theorem gamma0MixedCusp_exceptional_compact_density_le {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (r s : ℕ) [NeZero r] [NeZero s], r.Coprime s →
      ∀ (u : Finset (Gamma0AllHeightSpectralIndex (r*s))) (n : ℤ) (hn : n ≠ 0)
        {a Y : ℝ}, 0 < a → a ≤ 1 → ∀ hY : 0 < Y,
      Y < (a^2/2)/(|cuspFourierFrequency 1 n| /
        (gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ)) →
      (∀ i ∈ u, gamma0AllHeightGradientSpectralValue (r*s) i ≤ 1/4) →
      (Real.exp (-Real.exp 1)/16)^2 *
        (Real.cos (Real.pi/4)*gamma0CuspCosineExceptionalMoment (r*s) u (gamma0CuspOneOver s) Y hY n hn a) ≤
        1+8*(D*(((r*s : ℕ) : ℝ)*(n.natAbs : ℝ)/a)^ε*
          (Real.sqrt ((n.natAbs : ℝ)*(Nat.gcd (r*s) n.natAbs : ℝ))/(((r*s : ℕ) : ℝ)*a))) := by
  obtain ⟨D,hD,hWeil⟩ := spectralABLExceptional_compact_prefix_weil hε
  refine ⟨D,hD,?_⟩
  intro r s ir is hcop u n hn a Y ha ha1 hY hYA heig
  exact (gamma0MixedCusp_exceptional_compact_cosine_prefix_le r s hcop u n hn ha ha1 hY hYA heig).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hWeil (r*s) n hn a ha ha1) (by norm_num)))

end ArtinMatthews
