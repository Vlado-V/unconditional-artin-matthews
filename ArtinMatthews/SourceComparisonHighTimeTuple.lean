module

public import ArtinMatthews.MarkedMajorArcPrimeNormalization
public import ArtinMatthews.MarkedSparsePhaseKernel
public import ArtinMatthews.MarkedMajorArcHighPrimeNormalized
public import ArtinMatthews.MarkedSparsePhaseContinuity
public import ArtinMatthews.SourceComparisonHighTimeCover
public import ArtinMatthews.SourceComparisonPolynomialMean
public import ArtinMatthews.SourceComparisonSparseEnergy
public import ArtinMatthews.SourceComparisonSparsePrime
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! High-time cancellation for the positive giant-prime dyadic factors. -/

namespace ArtinMatthews

open Finset Filter MeasureTheory Set
open scoped Topology

noncomputable section

def sourceComparisonHighTimes (T S : ℝ) : Set ℝ :=
  Set.Icc (-T) T ∩ {t | S ≤ |t|}

theorem sourceComparisonHighTimes_measurable (T S : ℝ) :
    MeasurableSet (sourceComparisonHighTimes T S) :=
  measurableSet_Icc.inter (isClosed_le continuous_const continuous_abs).measurableSet

/-- The actual normalized small-prime, giant-prime, and residual polynomials
have arbitrarily small high-time energy. The frequency threshold depends
only on the fixed scale exponents and requested saving. -/
theorem sourceComparisonHighTime_tuple
    (c C σ d a η τ D A : ℝ)
    (hc : 0 < c) (hC : 0 < C) (hσ : 0 ≤ σ) (hd : 0 < d)
    (ha : 0 ≤ a) (hη : 0 < η) (hτ : 0 < τ) (hD : 0 ≤ D) (hA : 0 ≤ A) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (P T H u v U : ℝ) (l r : ℕ) (β : ℕ → ℂ),
        1 < P → c*X^(1/(10:ℝ)) ≤ Real.log P → Real.log P ≤ C*X →
        1 < T → T ≤ Real.exp (2*X) →
        Real.exp (τ*X) ≤ H → H ≤ u → u ≤ v → v ≤ 2*H → v ≤ Real.exp (η*X) →
        Real.exp (d*X) ≤ U → U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U →
        T ≤ H*U → H*U ≤ Real.exp (σ*X) → (∀ n ∈ Finset.Icc l r, ‖β n‖ ≤ X^D) →
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), (q:ℝ) ≤ X^a →
        ∀ (k : ℕ) (χs : DirichletCharacter ℂ k) (ξ : ℝ) (S : Finset ℕ),
          (∀ p ∈ S, p.Prime) → (∀ p ∈ S, (p:ℝ) ≤ 2*P) →
          (∫ t in sourceComparisonHighTimes T (X^B),
            ‖markedPrimePolynomial S P χs ξ t * markedMajorNormalizedPrimeSum χ t H u v *
              markedDyadicPolynomial l r U β t‖^2) ≤ X^(-A) := by
  let J := A+D+4
  let R := A+D+3
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨B,hB,hprime⟩ := marked_major_high_prime_normalized a η τ R ha hη hτ hR
  obtain ⟨K,hK,hsparse⟩ := sourceComparisonSparse_unitInterval_energy d 2 1 3 hd (by norm_num)
  let Q := 1+Real.log 4+σ
  have hQ : 0 < Q := by
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
    dsimp [Q]
    linarith
  let E := 256*Real.exp 1*Q^3
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨B, hB, ?_⟩
  filter_upwards [hprime, hsparse,
    sourceComparisonPrime_exceptionalIntervals_card c C 2 J hc hC (by norm_num) hJ,
    eventually_ge_atTop (max 1 (E+200*K))] with X hprime hsparse hcount hX
  have hX1 : 1 ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < X := zero_lt_one.trans_le hX1
  have hXsum : E+200*K ≤ X := (le_max_right _ _).trans hX
  intro P T H u v U l r β hP hlo hhi hT hTcap hH hHu huv hvH hvhi hU hl hr hTprod hprod hβ
    q _ χ hq k χs ξ S hS hScap
  let F := markedPrimePolynomial S P χs ξ
  let M := fun t => markedMajorNormalizedPrimeSum χ t H u v
  let N := markedDyadicPolynomial l r U β
  let I := markedExceptionalUnitIntervals F T (X^(-J))
  let W := sourceComparisonHighTimes T (X^B)
  have hW : W ⊆ Set.Icc (-T) T := inter_subset_left
  have hFcont : Continuous F := markedPrimePolynomial_continuous S P χs ξ
  have hMcont : Continuous M := sourceComparisonNormalizedPrime_continuous χ H u v
  have hNcont : Continuous N := markedDyadicPolynomial_continuous l r U β
  have hHp : 0 < H := (Real.exp_pos _).trans_le hH
  have hUp : 0 < U := (Real.exp_pos _).trans_le hU
  have hHU : 1 ≤ H*U := hT.le.trans hTprod
  have hlog : 1+Real.log (4*H*U) ≤ Q*X := by
    have hh := (Real.log_le_iff_le_exp (mul_pos hHp hUp)).mpr hprod
    rw [show 4*H*U = 4*(H*U) by ring, Real.log_mul (by norm_num) (mul_pos hHp hUp).ne']
    dsimp [Q]
    nlinarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)]
  have hlog0 : 0 ≤ 1+Real.log (4*H*U) := by
    have hh : 1 ≤ 4*H*U := by nlinarith
    linarith [Real.log_nonneg hh]
  have hmean : (∫ t in W, ‖M t*N t‖^2) ≤ E*X^(2*D+3) := by
    calc
      _ ≤ ∫ t in Set.Icc (-T) T, ‖M t*N t‖^2 :=
        setIntegral_mono_set ((hMcont.mul hNcont).norm.pow 2).integrableOn_Icc
          (Eventually.of_forall (fun _ => sq_nonneg _)) (Eventually.of_forall (fun _ ht => hW ht))
      _ ≤ 128*Real.exp 1*(1+T/(H*U))*(X^D)^2*(1+Real.log (4*H*U))^3 :=
        sourceComparisonPrimeProduct_mean_square χ H u v U T (X^D) l r β
          hHp hUp hHU (by linarith) hHu hvH hl hr (by positivity) hβ
      _ ≤ 128*Real.exp 1*2*(X^D)^2*(Q*X)^3 := by
        have hratio : T/(H*U) ≤ 1 := (div_le_one (mul_pos hHp hUp)).mpr hTprod
        gcongr
        linarith
      _ = _ := by
        rw [Real.rpow_add hX0, show 2*D = D*2 by ring, Real.rpow_mul hX0.le,
          Real.rpow_two, show (3:ℝ) = (3:ℕ) by norm_num, Real.rpow_natCast]
        dsimp [E]
        ring
  have hcard : (I.card:ℝ) ≤ 3*Real.exp (1*X^(91/(100:ℝ))) := by
    simpa only [one_mul] using hcount P T hP hlo hhi hT hTcap k χs ξ S hS hScap
  have hmass := sourceComparisonDyadicCoefficient_square_mass l r U (X^D) β hUp hl hr hβ
  have henergy : (∑ z ∈ I, sSup ((fun t => ‖N t‖^2) '' Set.Icc (z:ℝ) ((z:ℝ)+1))) ≤
      2*K*X*(X^D)^2 := by
    have hwitness (z : ℤ) (hz : z ∈ I) : ∃ t ∈ Set.Icc (z:ℝ) ((z:ℝ)+1), |t| ≤ T := by
      obtain ⟨t, ht, htT, _⟩ := markedExceptionalUnitIntervals_witness F T (X^(-J)) z hz
      exact ⟨t, ht, htT⟩
    apply (hsparse U T l r β I hU hT.le hTcap hl hr hcard hwitness).trans
    calc
      _ ≤ K*X*U*(2*(X^D)^2/U) := mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = _ := by field_simp
  have hMb (t : ℝ) (ht : t ∈ W) : ‖M t‖ ≤ 5*X^(-R) :=
    hprime q hq χ t H u v ht.2 ((abs_le.mpr ht.1).trans hTcap) hH hHu huv hvH hvhi
  have h := sourceComparison_isolated_energy_subset F M N I T (X^(-J)) 2 (5*X^(-R))
    (E*X^(2*D+3)) (2*K*X*(X^D)^2) W (sourceComparisonHighTimes_measurable T (X^B))
    hW hFcont hMcont hNcont
    (fun t _ => markedPrimePolynomial_norm_le_two S (by linarith) χs ξ t hS hScap)
    hMb (fun t ht hlarge => markedExceptionalUnitIntervals_cover F T (X^(-J)) t ht.1 hlarge.le)
    hmean henergy
  have hsq (z : ℝ) : (X^z)^2 = X^(z*2) := by rw [Real.rpow_mul hX0.le, Real.rpow_two]
  have hgood : (X^(-J))^2*(E*X^(2*D+3)) ≤ E*X^(-A-1) := by
    rw [hsq, show X^(-J*2)*(E*X^(2*D+3)) = E*X^(-J*2+(2*D+3)) by
      rw [Real.rpow_add hX0 (-J*2) (2*D+3)]; ring]
    apply mul_le_mul_of_nonneg_left _ hE.le
    apply Real.rpow_le_rpow_of_exponent_le hX1
    dsimp [J]
    linarith
  have hbad : 2^2*(5*X^(-R))^2*(2*K*X*(X^D)^2) ≤ 200*K*X^(-A-1) := by
    have he : 2^2*(5*X^(-R))^2*(2*K*X*(X^D)^2) = 200*K*X^(-R*2+1+D*2) := by
      rw [Real.rpow_add hX0 (-R*2+1) (D*2), Real.rpow_add hX0 (-R*2) 1, Real.rpow_one,
        mul_pow, hsq, hsq]
      ring
    rw [he]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hX1
    dsimp [R]
    linarith
  apply h.trans
  calc
    _ ≤ E*X^(-A-1)+200*K*X^(-A-1) := add_le_add hgood hbad
    _ = (E+200*K)*X^(-A-1) := by ring
    _ ≤ X*X^(-A-1) := mul_le_mul_of_nonneg_right hXsum (by positivity)
    _ = X^(-A) := by
      conv_lhs => lhs; rw [← Real.rpow_one X]
      rw [← Real.rpow_add hX0]
      congr 1
      ring

end
end ArtinMatthews
