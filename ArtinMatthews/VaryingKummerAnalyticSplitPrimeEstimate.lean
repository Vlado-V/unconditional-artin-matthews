module

public import ArtinMatthews.VaryingKummerAnalyticSplitPrimeWeight


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine finite rational-prime count reduction, using the constructed
fixed smooth weight and actual norm-p prime-ideal fibers.  The varying-field
zero-free region is explicitly required, and is not assumed by a definition. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField OAI.PrimeDegreePackets Complex MeasureTheory Set
open scoped Classical ContDiff BigOperators
noncomputable section
universe u

theorem exists_splitPrime_count_bound_of_zero_region :
    ∃ C : ℝ,0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K],
      ∀ (x β : ℝ) (S : Finset Nat.Primes),1 < x → 0 ≤ β →
      (∀ ρ : ℂ,mixedCompletedDedekindXi K ρ = 0 → ρ.re ≤ β) →
      (∀ p ∈ S,x ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*x) →
      (∀ p ∈ S,((idealsOverPrime K p).filter (fun Q => Ideal.absNorm Q = (p : ℕ))).card =
        Module.finrank ℚ K) →
      (S.card : ℝ) ≤ C*(x+x^β*(Real.log |(discr K : ℝ)|+(Module.finrank ℚ K : ℝ)))/
        ((Module.finrank ℚ K : ℝ)*Real.log x) := by
  obtain ⟨C,hC,hbound⟩ := dedekindPrimePower_smoothed_bound_of_zero_region
    splitPrimeWeight splitPrimeWeight_compact splitPrimeWeight_positive_support splitPrimeWeight_smooth
  refine ⟨C,hC,?_⟩
  intro K _ _ x β S hx hβ hregion hS hcard
  have hcount := normPrimeFiber_log_count_le_smoothed K splitPrimeWeight splitPrimeWeight_compact
    splitPrimeWeight_positive_support splitPrimeWeight_smooth splitPrimeWeight_nonneg
    splitPrimeWeight_majorant S hx hS
  have hfib : Fintype.card (NormPrimeFiber K S) = S.card*Module.finrank ℚ K := by
    rw [normPrimeFiber_card]
    calc
      _ = ∑ p ∈ S,Module.finrank ℚ K := Finset.sum_congr rfl hcard
      _ = _ := by simp
  rw [hfib,Nat.cast_mul] at hcount
  have hmain := hbound K x β hx.le hβ hregion
  have hfull := hcount.trans ((Complex.re_le_norm _).trans hmain)
  have hn : 0 < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hden : 0 < (Module.finrank ℚ K : ℝ)*Real.log x := mul_pos hn (Real.log_pos hx)
  apply (le_div_iff₀ hden).mpr
  simpa only [mul_assoc] using hfull

end
end ArtinMatthews.VaryingKummerAnalytic
