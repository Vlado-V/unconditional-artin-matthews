module

public import ArtinMatthews.GiantFixedResiduePolynomial
public import ArtinMatthews.MarkedTypeIICoefficients
public import Mathlib.NumberTheory.PrimeCounting
public import OAI.NumberTheory.Jacobsthal.Estimates.FundamentalBlockEstimate
public import ArtinMatthews.GiantRoughSieve
public import ArtinMatthews.MarkedSieveLevel
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import OAI.NumberTheory.Jacobsthal.Sieve.IntervalBoundingSieve
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Positive sieve for a fixed unit residue. Primes dividing the modulus
have zero local hit density, with the original rough test unchanged. -/
namespace ArtinMatthews
open MeasureTheory OAI.Erdos970.NumberTheoryLean
open scoped BigOperators
noncomputable section

def giantFixedResidueProgressionDiscrepancy (M a : ℕ) (H : ℕ → ℝ)
    (μ : ℝ) (Φ : ℝ → ℝ) (T x : ℝ) (R : ℕ) : ℝ :=
  ∑ r∈Finset.Icc 1 R,
    |(∑ u∈giantFixedResidueSet M a r (T*x),Φ ((u:ℝ)/x)*H u) -
      giantFixedResidueScale M r (x*∫ t in Set.Ioc 0 T,Φ t)*μ|

def giantFixedResidueRoughSum (M a : ℕ) (H : ℕ → ℝ) (Φ : ℝ → ℝ)
    (T x γ : ℝ) : ℝ := by
  classical
  exact ∑ u ∈ (giantFixedResidueSet M a 1 (T*x)).filter (fun u => MarkedRoughAbove (x^γ) (u+1)),
    Φ ((u:ℝ)/x)*H u

def giantFixedResidueHitDensity (M p : ℕ) : ℝ :=
  if p∣M then 0 else 1/(p:ℝ)

def giantFixedResidueEuler (M : ℕ) (y : ℝ) : ℝ :=
  ∏ p∈Nat.primesLE ⌊y⌋₊, (1-giantFixedResidueHitDensity M p)

theorem giantFixedResidueHitDensity_bounds (M p : ℕ) :
    0≤giantFixedResidueHitDensity M p ∧ giantFixedResidueHitDensity M p≤1/(p:ℝ) := by
  unfold giantFixedResidueHitDensity
  have h : (0:ℝ)≤1/(p:ℝ) := by positivity
  split_ifs
  · exact ⟨le_rfl,h⟩
  · exact ⟨h,le_rfl⟩

theorem giantFixedResidueEuler_pos (M : ℕ) (y : ℝ) : 0<giantFixedResidueEuler M y := by
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1:ℝ)<p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
  exact sub_pos.mpr ((giantFixedResidueHitDensity_bounds M p).2.trans_lt
    ((div_lt_one (by linarith)).mpr hp1))

theorem giantFixedResidueHitDensity_primeFactors (M : ℕ) {r : ℕ} (hr : Squarefree r) :
    (∏ p∈r.primeFactors,giantFixedResidueHitDensity M p) =
      if r.Coprime M then 1/(r:ℝ) else 0 := by
  classical
  by_cases hc : r.Coprime M
  · rw [ite_eq_left hc]
    calc
      _ = ∏ p∈r.primeFactors,1/(p:ℝ) := by
        apply Finset.prod_congr rfl
        intro p hp
        have hpc := Nat.Coprime.of_dvd_left (Nat.dvd_of_mem_primeFactors hp) hc
        exact ite_eq_right ((Nat.prime_of_mem_primeFactors hp).coprime_iff_not_dvd.mp hpc)
      _ = _ := by
        rw [Finset.prod_div_distrib,Finset.prod_const_one,← Nat.cast_prod,
          Nat.prod_primeFactors_of_squarefree hr]
  · rw [ite_eq_right hc]
    obtain ⟨p,hp,hpr,hpM⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    exact Finset.prod_eq_zero (Nat.mem_primeFactors.mpr ⟨hp,hpr,hr.ne_zero⟩) (ite_eq_left hpM)

theorem giantFixedResidueSet_filter_dvd (M a r : ℕ) (T : ℝ) :
    (giantFixedResidueSet M a 1 T).filter (fun u => r∣u+1) = giantFixedResidueSet M a r T := by
  ext u
  simp only [giantFixedResidueSet,Finset.mem_filter,one_dvd,true_and]
  tauto

theorem giantFixedResidue_integerRemainder (M a : ℕ) (w : ℕ → ℝ)
    (T I μ : ℝ) {d : ℕ} (hd : Squarefree d) :
    FundamentalBlockEstimate.integerRemainder (giantFixedResidueSet M a 1 T) w
      (fun p u => p∣u+1) (I*μ/(M:ℝ)) (giantFixedResidueHitDensity M) d =
      (∑ u∈giantFixedResidueSet M a d T,w u)-giantFixedResidueScale M d I*μ := by
  classical
  have hdiv (u : ℕ) : (∀ p∈d.primeFactors,p∣u+1) ↔ d∣u+1 := by
    constructor
    · intro h
      rw [← Nat.prod_primeFactors_of_squarefree hd,
        Nat.prod_primeFactors_dvd_iff (by omega : u+1≠0)]
      intro p hp
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,h p hp,by omega⟩
    · intro h p hp
      exact (Nat.dvd_of_mem_primeFactors hp).trans h
  unfold FundamentalBlockEstimate.integerRemainder BonferroniBlocks.intersectionRemainder
    BonferroniBlocks.intersectionMass BonferroniBlocks.intersectionValue
  simp only [hdiv,mul_ite,mul_one,mul_zero,← Finset.sum_filter]
  rw [giantFixedResidueSet_filter_dvd,giantFixedResidueHitDensity_primeFactors M hd]
  unfold giantFixedResidueScale
  by_cases hc : d.Coprime M
  · rw [ite_eq_left hc,ite_eq_left hc,Nat.cast_mul]
    ring
  · simp only [ite_eq_right hc,mul_zero,zero_mul]

theorem giantFixedResidue_rough_sieve_progression_bridge (M a : ℕ) (H : ℕ → ℝ)
    (μ : ℝ) (Φ : ℝ → ℝ) (T x γ c : ℝ) (m : ℕ)
    (hx : 1≤x) (hΦ : ∀ t,0≤Φ t) (hH : ∀ u,0≤H u) (hμ : 0≤μ)
    (hcut : 2 ≤ ⌊x ^ γ⌋₊) (hm : 20000 ≤ m)
    (hlevel : γ*((12*(m+1):ℕ):ℝ)≤c) :
    |giantFixedResidueRoughSum M a H Φ T x γ -
      ((x*(∫ t in Set.Ioc 0 T,Φ t)*μ)/(M:ℝ))*giantFixedResidueEuler M (x^γ)| ≤
      ((x*(∫ t in Set.Ioc 0 T,Φ t)*μ)/(M:ℝ))*giantFixedResidueEuler M (x^γ)*
        Real.exp (-(m:ℝ)/2) +
      giantFixedResidueProgressionDiscrepancy M a H μ Φ T x ⌊x ^ c⌋₊ := by
  classical
  let U := giantFixedResidueSet M a 1 (T*x)
  let w (u : ℕ) := Φ ((u:ℝ)/x)*H u
  let I := x*(∫ t in Set.Ioc 0 T,Φ t)
  let P := Nat.primesLE ⌊x ^ γ⌋₊
  have hP : ∀ p∈P,p.Prime := fun _ hp => Nat.prime_of_mem_primesLE hp
  have hX : 0≤I*μ/(M:ℝ) := div_nonneg
    (mul_nonneg (mul_nonneg (zero_le_one.trans hx) (integral_nonneg hΦ)) hμ) (Nat.cast_nonneg _)
  have h := FundamentalBlockEstimate.finite_fundamental_integer_level U w
    (fun u _ => mul_nonneg (hΦ _) (hH u)) (fun p u => p∣u+1)
    ⌊x ^ γ⌋₊ m P (I*μ/(M:ℝ)) (giantFixedResidueHitDensity M) hcut hm hX hP
    (fun _ hp => Nat.le_of_mem_primesLE hp)
    (fun p _ => (giantFixedResidueHitDensity_bounds M p).1)
    (fun p _ => (giantFixedResidueHitDensity_bounds M p).2.trans
      (div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg p)))
    (fun _ => (giantFixedResidueHitDensity_bounds M 2).2)
  have hsurv : (∑ u∈U,w u*BonferroniBlocks.survives P (fun p => p∣u+1)) =
      giantFixedResidueRoughSum M a H Φ T x γ := by
    simp only [P,marked_survives_eq_rough_indicator _ (Real.rpow_nonneg (zero_le_one.trans hx) γ)]
    simp only [giantFixedResidueRoughSum,Finset.sum_filter,mul_ite,mul_one,mul_zero,U,w]
  rw [hsurv] at h
  apply h.trans
  apply add_le_add le_rfl
  calc
    _ = ∑ d∈FundamentalBlockEstimate.levelDivisors P (⌊x ^ γ⌋₊ ^ (12*(m+1))),
      |(∑ u∈giantFixedResidueSet M a d (T*x),w u)-giantFixedResidueScale M d I*μ| := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdiv : d∣∏ p∈P,p := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
      exact congrArg abs (giantFixedResidue_integerRemainder M a w (T*x) I μ
        ((IntervalBoundingSieve.squarefree_primeSet_product P hP).squarefree_of_dvd hdiv))
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (marked_sieve_level_subset P x γ c (12*(m+1)) hx hlevel) (fun _ _ _ => abs_nonneg _)

end
end ArtinMatthews
