module

public import ArtinMatthews.MarkedPhysicalJointPrimeDamping
public import ArtinMatthews.MarkedRawRootArcGrowth
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

/-! The actual used-plus-selected prime modulus of each performed
Bonferroni monomial. It is squarefree, contains every required prime, and
the real prime-band/depth bounds put it in the proved root-count range. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalBonferroniModulus {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (T : Finset ℕ) : ℕ :=
  ∏ p ∈ markedPhysicalPathUsedPrimes I a ∪ T,p

theorem markedPhysicalBandPrimes_prime {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime) {p : ℕ} (hp : p ∈ markedPhysicalBandPrimes P) : p.Prime := by
  obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hp
  exact hP j p hj

theorem markedPhysicalBonferroniModulus_prime {J ι : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime) {M : ℕ}
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) {T : Finset ℕ}
    (hT : T ⊆ markedPhysicalBandPrimes P) {p : ℕ} (hp : p ∈ markedPhysicalPathUsedPrimes I a ∪ T) : p.Prime := by
  rcases Finset.mem_union.mp hp with hp | hp
  · exact markedPhysicalBandPrimes_prime hP (markedPhysicalPathUsedPrimes_subset I a hp)
  · exact markedPhysicalBandPrimes_prime hP (hT hp)

theorem markedPhysicalBonferroniModulus_pos {J ι : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime) {M : ℕ}
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) {T : Finset ℕ}
    (hT : T ⊆ markedPhysicalBandPrimes P) : 0 < markedPhysicalBonferroniModulus I a T :=
  Finset.prod_pos (fun _ hp => (markedPhysicalBonferroniModulus_prime hP I a hT hp).pos)

theorem markedPhysicalBonferroniModulus_squarefree {J ι : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime) {M : ℕ}
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) {T : Finset ℕ}
    (hT : T ⊆ markedPhysicalBandPrimes P) : Squarefree (markedPhysicalBonferroniModulus I a T) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    apply Nat.coprime_iff_isRelPrime.mp
    exact (Nat.coprime_primes (markedPhysicalBonferroniModulus_prime hP I a hT hp)
      (markedPhysicalBonferroniModulus_prime hP I a hT hq)).mpr hpq
  · intro p hp
    exact (markedPhysicalBonferroniModulus_prime hP I a hT hp).squarefree

theorem markedPhysicalBonferroniModulus_mem_primeFactors {J ι : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime) {M : ℕ}
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) {T : Finset ℕ}
    (hT : T ⊆ markedPhysicalBandPrimes P) {p : ℕ} (hp : p ∈ markedPhysicalPathUsedPrimes I a ∪ T) :
    p ∈ (markedPhysicalBonferroniModulus I a T).primeFactors := by
  exact Nat.mem_primeFactors.mpr ⟨markedPhysicalBonferroniModulus_prime hP I a hT hp,
    Finset.dvd_prod_of_mem (fun p => p) hp,(markedPhysicalBonferroniModulus_pos hP I a hT).ne'⟩

theorem markedPhysicalBonferroniModulus_eq_mul {J ι : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} (I : Finset ι) (a : ι → MarkedPhysicalMarking P M)
    {T : Finset ℕ} (hT : T ⊆ markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes I a) :
    markedPhysicalBonferroniModulus I a T = (∏ p ∈ markedPhysicalPathUsedPrimes I a,p)*(∏ p ∈ T,p) := by
  apply Finset.prod_union
  exact Finset.disjoint_left.mpr (fun p hp hpT => (Finset.mem_sdiff.mp (hT hpT)).2 hp)

def markedPhysicalBonferroniDepth (x : ℝ) : ℕ := ⌈(Real.log x)^(19/25:ℝ)⌉₊

theorem markedPhysicalBonferroni_extra_product_bound {J : Type*} [Fintype J]
    (e : J → ℝ) {β x : ℝ} (hlog : 1 ≤ Real.log x) (he : ∀ j,e j ≤ β)
    (hβ : β+(19/25:ℝ) ≤ 49/50) (T : Finset ℕ)
    (hT : T ⊆ markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x))
    (hc : T.card ≤ 2*markedPhysicalBonferroniDepth x+1) :
    ((∏ p ∈ T,p:ℕ):ℝ) ≤ Real.exp (10*(Real.log x)^(49/50:ℝ)) := by
  have hLp : 0 < Real.log x := zero_lt_one.trans_le hlog
  have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg hLp.le (19/25:ℝ))
  have hcard : (T.card:ℝ) ≤ 2*(Real.log x)^(19/25:ℝ)+3 := by
    have hh : (T.card:ℝ) ≤ 2*(markedPhysicalBonferroniDepth x:ℝ)+1 := by exact_mod_cast hc
    change (markedPhysicalBonferroniDepth x:ℝ) < (Real.log x)^(19/25:ℝ)+1 at hceil
    linarith
  have hp (p : ℕ) (hp : p ∈ T) : (p:ℝ) ≤ Real.exp (2*(Real.log x)^β) := by
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp (hT hp)
    exact markedRootArc_band_prime_le hlog (he j) hj
  have hm : (Real.log x)^(19/25:ℝ)*(Real.log x)^β ≤ (Real.log x)^(49/50:ℝ) := by
    rw [← Real.rpow_add hLp]
    exact Real.rpow_le_rpow_of_exponent_le hlog (by linarith)
  have hb : (Real.log x)^β ≤ (Real.log x)^(49/50:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlog (by linarith)
  calc
    _ = ∏ p ∈ T,(p:ℝ) := by simp only [Nat.cast_prod]
    _ ≤ ∏ _p ∈ T,Real.exp (2*(Real.log x)^β) := Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) hp
    _ = Real.exp (2*(T.card:ℝ)*(Real.log x)^β) := by
      rw [Finset.prod_const,← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hLp.le β)]

theorem markedPhysicalBonferroniModulus_actual_bound {J ι : Type*} [Fintype J]
    (e : J → ℝ) {β B x : ℝ} (hB : 0 ≤ B) (hlog : 1 ≤ Real.log x) (he : ∀ j,e j ≤ β)
    (hβ : β+(19/25:ℝ) ≤ 49/50) {M : ℕ}
    (I : Finset ι) (a : ι → MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) M)
    {T : Finset ℕ} (hT : T ⊆ markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \ markedPhysicalPathUsedPrimes I a)
    (hc : T.card ≤ 2*markedPhysicalBonferroniDepth x+1)
    (hused : ((∏ p ∈ markedPhysicalPathUsedPrimes I a,p:ℕ):ℝ) ≤ Real.exp (B*(Real.log x)^(18/25:ℝ))) :
    (markedPhysicalBonferroniModulus I a T:ℝ) ≤ Real.exp ((B+10)*(Real.log x)^(49/50:ℝ)) := by
  rw [markedPhysicalBonferroniModulus_eq_mul I a hT,Nat.cast_mul]
  calc
    _ ≤ Real.exp (B*(Real.log x)^(18/25:ℝ))*Real.exp (10*(Real.log x)^(49/50:ℝ)) :=
      mul_le_mul hused (markedPhysicalBonferroni_extra_product_bound e hlog he hβ T
        (fun p hp => (Finset.mem_sdiff.mp (hT hp)).1) hc) (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (B*(Real.log x)^(18/25:ℝ)+10*(Real.log x)^(49/50:ℝ)) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (18/25:ℝ) ≤ 49/50)) hB
      nlinarith

end ArtinMatthews
