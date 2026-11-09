module

public import ArtinMatthews.VaryingKummerAnalyticSplitPrimeWeight


set_option backward.privateInPublic true
@[expose] public section

/-! An unconditional prime-splitting upper bound retaining the actual signed
Dedekind zero sum. This isolates the one-sided zero-sum estimate needed for
the paper's power saving without imposing a global zero-free half-plane. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField OAI.PrimeDegreePackets Complex MeasureTheory Set
open OAI.PrimeDegreePackets.AnalyticGrowth
open scoped Classical BigOperators ContDiff
noncomputable section
universe u

def splitPrimeMellinZeroSum (K : Type*) [Field K] [NumberField K] (x : ℝ) : ℂ :=
  ∑' ρ, (zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*
    mellin splitPrimeWeight ρ*(x : ℂ)^ρ

theorem splitPrimeMellinZeroSum_summable (K : Type*) [Field K] [NumberField K]
    {x : ℝ} (hx : 0 < x) :
    Summable (fun ρ => (zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*
      mellin splitPrimeWeight ρ*(x : ℂ)^ρ) := by
  obtain ⟨C,_hC,H⟩ := mixedCompletedDedekindXi_mellin_power_zero_uniform
    splitPrimeWeight splitPrimeWeight_compact splitPrimeWeight_positive_support splitPrimeWeight_smooth
  exact (H K x hx).1

theorem exists_splitPrime_smoothed_signed_zero_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K] (x : ℝ), 1 ≤ x →
      (∑' i : DedekindPrimePowerIndex K,
        (Real.log (Ideal.absNorm i.2.1.val) : ℂ)*
          splitPrimeWeight ((dedekindPrimePowerNorm K i : ℝ)/x)).re +
        (splitPrimeMellinZeroSum K x).re ≤
      C*x + C*(Real.log |(discr K : ℝ)| + (Module.finrank ℚ K : ℝ)) := by
  obtain ⟨A,hA,HA⟩ := dedekindPrimePower_explicitFormula_uniform_error
    splitPrimeWeight splitPrimeWeight_compact splitPrimeWeight_positive_support splitPrimeWeight_smooth
  let C := ‖mellin splitPrimeWeight 1‖ + ‖mellin splitPrimeWeight 0‖ + A + 1
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro K _ _ x hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  let d := Real.log |(discr K : ℝ)| + (Module.finrank ℚ K : ℝ)
  have hd : 0 ≤ d := add_nonneg (discr_log_nonneg K) (Nat.cast_nonneg _)
  have hnd : (Module.finrank ℚ K : ℝ) ≤ d := le_add_of_nonneg_left (discr_log_nonneg K)
  have hsmall : x^(-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
  have HR := (Complex.re_le_norm _).trans (HA K x hx0)
  have hrem : A*x^(-(1/2 : ℝ))*d ≤ A*d := by
    simpa using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsmall hA.le) hd
  have HR' := HR.trans hrem
  have hmain : ((x : ℂ)*mellin splitPrimeWeight 1).re ≤ x*‖mellin splitPrimeWeight 1‖ := by
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx0] using
      Complex.re_le_norm ((x : ℂ)*mellin splitPrimeWeight 1)
  have hzero : -((((InfinitePlace.nrRealPlaces K : ℤ) +
      InfinitePlace.nrComplexPlaces K-1 : ℤ) : ℂ)*mellin splitPrimeWeight 0).re ≤
      (Module.finrank ℚ K : ℝ)*‖mellin splitPrimeWeight 0‖ := by
    have H := Complex.re_le_norm (-((((InfinitePlace.nrRealPlaces K : ℤ) +
      InfinitePlace.nrComplexPlaces K-1 : ℤ) : ℂ)*mellin splitPrimeWeight 0))
    simp only [Complex.neg_re,norm_neg,norm_mul] at H
    exact H.trans (mul_le_mul_of_nonneg_right (mixedDedekindZeroOrder_norm_le_degree K)
      (norm_nonneg _))
  have hCX : x*‖mellin splitPrimeWeight 1‖ ≤ C*x := by
    have hc : ‖mellin splitPrimeWeight 1‖ ≤ C := by
      dsimp [C]
      linarith [norm_nonneg (mellin splitPrimeWeight 0)]
    nlinarith
  have hCD : d*(‖mellin splitPrimeWeight 0‖+A) ≤ C*d := by
    have hc : ‖mellin splitPrimeWeight 0‖+A ≤ C := by
      dsimp [C]
      linarith [norm_nonneg (mellin splitPrimeWeight 1)]
    exact mul_le_mul_of_nonneg_left hc hd |>.trans_eq (mul_comm d C)
  have hn0 := mul_le_mul_of_nonneg_right hnd (norm_nonneg (mellin splitPrimeWeight 0))
  simp only [Complex.add_re,Complex.sub_re] at HR'
  change _ ≤ C*x+C*d
  change _ + (∑' ρ, (zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*
    mellin splitPrimeWeight ρ*(x : ℂ)^ρ).re ≤ C*x+C*d
  linarith

theorem exists_splitPrime_count_signed_zero_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K]
      (x : ℝ) (S : Finset Nat.Primes), 1 < x →
      (∀ p ∈ S, x ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*x) →
      (∀ p ∈ S, ((idealsOverPrime K p).filter (fun Q => Ideal.absNorm Q = (p : ℕ))).card =
        Module.finrank ℚ K) →
      (S.card : ℝ)*(Module.finrank ℚ K : ℝ)*Real.log x +
        (splitPrimeMellinZeroSum K x).re ≤
      C*x + C*(Real.log |(discr K : ℝ)|+(Module.finrank ℚ K : ℝ)) := by
  obtain ⟨C,hC,HC⟩ := exists_splitPrime_smoothed_signed_zero_bound.{u}
  refine ⟨C,hC,?_⟩
  intro K _ _ x S hx hS hcard
  have H := normPrimeFiber_log_count_le_smoothed K splitPrimeWeight splitPrimeWeight_compact
    splitPrimeWeight_positive_support splitPrimeWeight_smooth splitPrimeWeight_nonneg
    splitPrimeWeight_majorant S hx hS
  have hfib : Fintype.card (NormPrimeFiber K S) = S.card*Module.finrank ℚ K := by
    rw [normPrimeFiber_card]
    calc
      _ = ∑ _p ∈ S, Module.finrank ℚ K := Finset.sum_congr rfl hcard
      _ = _ := by simp
  rw [hfib,Nat.cast_mul] at H
  have H' := HC K x hx.le
  linarith

end
end ArtinMatthews.VaryingKummerAnalytic
