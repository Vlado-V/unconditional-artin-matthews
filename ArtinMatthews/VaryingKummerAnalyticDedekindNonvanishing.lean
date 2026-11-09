module

public import ArtinMatthews.VaryingKummerAnalyticDedekindNonvanishingLocal
public import ArtinMatthews.VaryingKummerAnalyticDedekindSeries


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine general-field Dedekind-zeta nonvanishing in Re(s)>1. -/

namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section
open NumberField Finset
open OAI.PrimeDegreePackets
open scoped NumberField nonZeroDivisors Classical BigOperators

lemma dedekindZeta_ne_zero_of_one_lt_re (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) : NumberField.dedekindZeta K s ≠ 0 := by
  classical
  let H := riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs)
  let f (m : ℕ) : ℂ := (idealCoefficient K m : ℂ) * H m
  have hf (m : ℕ) : f m = LSeries.term (fun k => (idealCoefficientReal K k : ℂ)) s m := by
    by_cases hm : m = 0
    · subst m
      simp [f]
    · simp only [f,H,riemannZetaSummandHom,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk,
        LSeries.term_of_ne_zero hm,idealCoefficientReal,ArithmeticFunction.coe_mk,
        Complex.ofReal_natCast,Complex.cpow_neg,div_eq_mul_inv]
  have hS : Summable (fun m => ‖f m‖) := by
    simpa only [hf] using (idealCoefficient_LSeriesSummable K hs).norm
  have h0 : f 0 = 0 := by simp [f]
  have h1 : f 1 = 1 := by simp [f,idealCoefficient_one]
  have hm {m n : ℕ} (h : m.Coprime n) : f (m*n) = f m * f n := by
    simp only [f,(idealCoefficient_multiplicative K).map_mul_of_coprime h,
      Nat.cast_mul,map_mul]
    ring
  have hE (p : Nat.Primes) : (∑' k : ℕ, f ((p:ℕ)^k)) ≠ 0 := by
    change (∑' k : ℕ, (idealCoefficient K ((p:ℕ)^k) : ℂ) * H ((p:ℕ)^k)) ≠ 0
    rw [ideal_local_complex_euler K hs p.property]
    apply Finset.prod_ne_zero_iff.mpr
    intro P _
    apply inv_ne_zero
    intro he
    have hn := zetaSummand_norm_lt_one hs (idealsOverPrime_norm_two_le K P.2)
    rw [←sub_eq_zero.mp he,norm_one] at hn
    exact (lt_irrefl _ hn)
  have HN := complex_multiplicative_tsum_ne_zero f h0 h1 (fun h => hm h) hS hE
  have he : (∑' m : ℕ, f m) = NumberField.dedekindZeta K s := by
    calc
      _ = LSeries (fun k => (idealCoefficientReal K k : ℂ)) s := tsum_congr hf
      _ = _ := idealCoefficient_LSeries_eq K s
  rwa [he] at HN


theorem dedekindZeta_analyticAt_of_one_lt_re
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (NumberField.dedekindZeta K) s :=
  dedekindZeta_analyticOnNhd K s hs

theorem dedekindZeta_differentiableAt_of_one_lt_re
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (NumberField.dedekindZeta K) s :=
  (dedekindZeta_analyticAt_of_one_lt_re K hs).differentiableAt

theorem dedekindZeta_logDeriv_analyticAt_of_one_lt_re
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (fun z => deriv (NumberField.dedekindZeta K) z /
      NumberField.dedekindZeta K z) s := by
  have ha := dedekindZeta_analyticAt_of_one_lt_re K hs
  exact ha.deriv.div ha (dedekindZeta_ne_zero_of_one_lt_re K hs)

end
end ArtinMatthews.VaryingKummerAnalytic
