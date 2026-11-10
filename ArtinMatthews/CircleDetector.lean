module

public import OAI.NumberTheory.JointDickman.Arithmetic.RamanujanDivisorFormula
public import ArtinMatthews.KloostermanRamanujan
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! A finite integer-frequency circle detector. At frequency zero its
normalization is exact; elsewhere the Ramanujan divisor bound controls the
error independently of the modulus. No spectral estimate is used here.
-/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

def primitiveCircleSum (q : ℕ) (n : ℤ) : ℂ :=
  if hq : q=0 then 0 else
    letI : NeZero q := ⟨hq⟩
    OAI.JointDickman.ramanujanSum q (n : ZMod q)

theorem primitiveCircleSum_eq (q : ℕ) [NeZero q] (n : ℤ) :
    primitiveCircleSum q n = OAI.JointDickman.ramanujanSum q (n : ZMod q) := by
  simp only [primitiveCircleSum,dite_eq_right (NeZero.ne q)]

theorem primitiveCircleSum_zero (q : ℕ) :
    primitiveCircleSum q 0 = (q.totient : ℂ) := by
  by_cases hq : q=0
  · subst q
    simp [primitiveCircleSum]
  · let : NeZero q := ⟨hq⟩
    rw [primitiveCircleSum_eq,Int.cast_zero,OAI.JointDickman.ramanujanSum_zero]

theorem primitiveCircleSum_norm_le (q : ℕ) {n : ℤ} (hn : n≠0) :
    ‖primitiveCircleSum q n‖ ≤ (n.natAbs : ℝ)^2 := by
  by_cases hq : q=0
  · subst q
    change ‖(0 : ℂ)‖ ≤ (n.natAbs : ℝ)^2
    rw [norm_zero]
    exact sq_nonneg _
  · let : NeZero q := ⟨hq⟩
    rw [primitiveCircleSum_eq,← ordinaryKloosterman_zero_eq_ramanujanSum]
    apply (ordinaryKloosterman_zero_norm_le_frequency_divisors q hn).trans
    calc
      _ ≤ ∑ _d∈n.natAbs.divisors, (n.natAbs : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hn))
          (Nat.dvd_of_mem_divisors hd)
      _ = (n.natAbs.divisors.card : ℝ)*(n.natAbs : ℝ) := by
        simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ (n.natAbs : ℝ)*(n.natAbs : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        exact_mod_cast Nat.card_divisors_le_self n.natAbs
      _ = _ := by ring

def circleNormalizer (Q : Finset ℕ) (ω : ℕ → ℝ) : ℝ :=
  ∑ q∈Q, ω q*(q.totient : ℝ)

def circleWeightMass (Q : Finset ℕ) (ω : ℕ → ℝ) : ℝ := ∑ q∈Q, ω q

def circleDetector (Q : Finset ℕ) (ω : ℕ → ℝ) (n : ℤ) : ℂ :=
  (∑ q∈Q, (ω q : ℂ)*primitiveCircleSum q n)/(circleNormalizer Q ω : ℂ)

theorem circleDetector_zero (Q : Finset ℕ) (ω : ℕ → ℝ)
    (hΛ : circleNormalizer Q ω ≠ 0) : circleDetector Q ω 0=1 := by
  unfold circleDetector
  simp_rw [primitiveCircleSum_zero]
  have heq : (∑ q∈Q, (ω q : ℂ)*(q.totient : ℂ)) = (circleNormalizer Q ω : ℂ) := by
    simp only [circleNormalizer,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_natCast]
  rw [heq,div_self (by exact_mod_cast hΛ)]

theorem circleWeightMass_nonneg (Q : Finset ℕ) (ω : ℕ → ℝ)
    (hω : ∀ q∈Q, 0≤ω q) : 0≤circleWeightMass Q ω :=
  Finset.sum_nonneg hω

theorem circleDetector_norm_le (Q : Finset ℕ) (ω : ℕ → ℝ)
    (hω : ∀ q∈Q, 0≤ω q) (hΛ : 0<circleNormalizer Q ω)
    {n : ℤ} (hn : n≠0) :
    ‖circleDetector Q ω n‖ ≤
      circleWeightMass Q ω*(n.natAbs : ℝ)^2/circleNormalizer Q ω := by
  unfold circleDetector
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hΛ]
  apply div_le_div_of_nonneg_right _ hΛ.le
  calc
    _ ≤ ∑ q∈Q, ‖(ω q : ℂ)*primitiveCircleSum q n‖ := norm_sum_le _ _
    _ ≤ ∑ q∈Q, ω q*(n.natAbs : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hω q hq)]
      exact mul_le_mul_of_nonneg_left (primitiveCircleSum_norm_le q hn) (hω q hq)
    _ = _ := by rw [circleWeightMass,Finset.sum_mul]

theorem circleDetector_error_le (Q : Finset ℕ) (ω : ℕ → ℝ)
    (hω : ∀ q∈Q, 0≤ω q) (hΛ : 0<circleNormalizer Q ω)
    (R : ℕ) (n : ℤ) (hn : n.natAbs≤R) :
    ‖circleDetector Q ω n - (if n=0 then 1 else 0)‖ ≤
      circleWeightMass Q ω*(R : ℝ)^2/circleNormalizer Q ω := by
  by_cases hz : n=0
  · subst n
    rw [circleDetector_zero Q ω hΛ.ne']
    simp only [ite_true,sub_self,norm_zero]
    exact div_nonneg (mul_nonneg (circleWeightMass_nonneg Q ω hω) (sq_nonneg _)) hΛ.le
  · simp only [ite_eq_right hz,sub_zero]
    apply (circleDetector_norm_le Q ω hω hΛ hz).trans
    apply div_le_div_of_nonneg_right _ hΛ.le
    apply mul_le_mul_of_nonneg_left _ (circleWeightMass_nonneg Q ω hω)
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hn) 2

end ArtinMatthews
