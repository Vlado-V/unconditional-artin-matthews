module

public import ArtinMatthews.SpectralJHolomorphicCoefficient
public import ArtinMatthews.SpectralPeterssonGram
public import ArtinMatthews.SpectralJHolomorphicPetersson
public import ArtinMatthews.SpectralJOddSmallArgument
public import ArtinMatthews.SpectralPeterssonInfinityWeil
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

/-! Joint absolute convergence of the actual even-weight Petersson contribution
at the infinity cusp. Weight two is included in the natural odd-order bound. -/
noncomputable section
open Set Complex
open scoped MatrixGroups

namespace ArtinMatthews

theorem spectralJHolomorphicCoefficient_leftInfinity_summable_norm
    (f : ℝ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) (N : ℕ) [NeZero N]
    (b : SL(2, ℤ)) (m n : ℕ+) :
    Summable (fun p : ℕ × Ioi (0 : ℕ) =>
      ‖spectralJHolomorphicCoefficient f (2*p.1+2)*
        gamma0PeterssonGramModulusTerm N b 1 (2*p.1+2) m n p.2‖) := by
  let w : ℝ := Real.sqrt (gamma0CuspTrueWidth N b : ℝ)
  have hw : 0 < w := Real.sqrt_pos.mpr (by exact_mod_cast gamma0CuspTrueWidth_pos N b)
  let Q : ℝ := 4*Real.pi*Real.sqrt ((m : ℝ)*(n : ℝ))/w
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  obtain ⟨C,A,hC,hA,hsmall⟩ := spectralJOddSynthesisTerm_small_argument f hf hc hp Q hQ
  obtain ⟨K,hK,hweil⟩ := gamma0TrueWidthKloostermanSum_leftInfinity_weil N b m (1/4) (by norm_num)
  let a : ℕ → ℝ := fun j => (K/w)*(C*(A^(2*j+1)/((2*j+1).factorial : ℝ)))
  let d : Ioi (0 : ℕ) → ℝ := fun c => (c.val : ℝ)^(-5/4 : ℝ)
  have ha0 (j : ℕ) : 0 ≤ a j := by dsimp [a]; positivity
  have hd0 (c : Ioi (0 : ℕ)) : 0 ≤ d c := by dsimp [d]; positivity
  have ha : Summable a := (spectralJOddMajorant_summable C A).mul_left (K/w)
  have hd : Summable d := (Real.summable_nat_rpow.mpr (by norm_num : (-5/4 : ℝ) < -1)).subtype _
  have hprod : Summable (fun p : ℕ × Ioi (0 : ℕ) => a p.1*d p.2) := by
    apply (summable_prod_of_nonneg (fun p => mul_nonneg (ha0 p.1) (hd0 p.2))).mpr
    refine ⟨fun j => hd.mul_left (a j),?_⟩
    simpa only [tsum_mul_left] using ha.mul_right (∑' c, d c)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hprod
  intro p
  rcases p with ⟨j,c⟩
  letI : NeZero c.val := ⟨c.property.ne'⟩
  have hc0 : 0 < (c.val : ℝ) := by exact_mod_cast c.property
  have hc1 : 1 ≤ (c.val : ℝ) := by exact_mod_cast c.property
  have hmod : gamma0TrueWidthModulus N b 1 (c.val : ℝ) = (c.val : ℝ)*w := by
    simp only [gamma0TrueWidthModulus,gamma0CuspTrueWidth_infinity,Nat.cast_one,Real.sqrt_one,mul_one,w]
  have harg : spectralPeterssonBesselArgument m n
      (gamma0TrueWidthModulus N b 1 (c.val : ℝ)) = Q/(c.val : ℝ) := by
    rw [spectralPeterssonBesselArgument,hmod]
    dsimp [Q]
    ring
  have hmodnorm : ‖(gamma0TrueWidthModulus N b 1 (c.val : ℝ) : ℂ)‖ = (c.val : ℝ)*w := by
    rw [Complex.norm_real,Real.norm_eq_abs,hmod,abs_of_pos (mul_pos hc0 hw)]
  have hKc := hweil c.val (n : ℤ)
  norm_num at hKc
  have hpower : (c.val : ℝ)^(3/4 : ℝ)/((c.val : ℝ)*(c.val : ℝ)) =
      (c.val : ℝ)^(-5/4 : ℝ) := by
    rw [show (c.val : ℝ)*(c.val : ℝ) = (c.val : ℝ)^(2 : ℝ) by rw [Real.rpow_two]; ring,
      ← Real.rpow_sub hc0]
    norm_num
  rw [spectralJHolomorphicCoefficient_gram_modulus,norm_mul,norm_div,hmodnorm,harg]
  calc
    _ ≤ (K*(c.val : ℝ)^(3/4 : ℝ)/((c.val : ℝ)*w))*
        ((C*(A^(2*j+1)/((2*j+1).factorial : ℝ)))/(c.val : ℝ)) := by
      exact mul_le_mul
        (div_le_div_of_nonneg_right hKc (mul_pos hc0 hw).le)
        (hsmall j (c.val : ℝ) hc1) (norm_nonneg _) (by positivity)
    _ = a j*d c := by
      dsimp only [a,d]
      rw [← hpower]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

end ArtinMatthews
