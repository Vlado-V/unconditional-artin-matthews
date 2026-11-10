module

public import ArtinMatthews.GiantPrimeShift
public import ArtinMatthews.GiantProgressionPrimeAnnular
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.FixedFinitePrimeExceptions
public import ArtinMatthews.GiantBoundedProgression
public import ArtinMatthews.GiantProgressionPrimeMean
public import ArtinMatthews.MarkedCorrelationNormalization
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
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


set_option backward.privateInPublic true
@[expose] public section

/-! The actual fixed-modulus smooth prime mean with its p-1 argument.
This consumes the proved residue-class PNT, the exact unit indicator,
and the negligible shift; it does not assume the centered giant law. -/
namespace ArtinMatthews
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology Asymptotics

theorem giant_unshifted_test_eq_annular {M : ℕ} (U : Finset (ZMod M)ˣ)
    (Φ : ℝ → ℝ) {a b x : ℝ} (ha : 0<a) (hab : a≤b)
    (hsupp : Function.support Φ ⊆ Set.Ioo a b) (hx : 0<x) :
    giantUnshiftedPrimeTest U Φ b x = (giantUnitPrimeAnnular U Φ a b x : ℂ) := by
  classical
  let f (p : ℕ) : ℂ := (Φ ((p : ℝ)/x) : ℂ)*giantUnitResidueIndicator U p
  have hsub : giantUnitAnnularPrimes U a b x ⊆ giantPrimeMeanRange b x := by
    intro p hp
    obtain ⟨hpI,hpP,hpU⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _,?_⟩,hpP⟩
    simpa only [mul_comm] using (Finset.mem_Ioc.mp hpI).2.trans (Nat.le_succ ⌊x*b⌋₊)
  have hsum : (∑ p ∈ giantUnitAnnularPrimes U a b x, f p) =
      ∑ p ∈ giantPrimeMeanRange b x, f p := by
    apply Finset.sum_subset hsub
    intro p hp hnot
    by_cases hpU : (p : ZMod M) ∈ U.image (fun u : (ZMod M)ˣ => (u : ZMod M))
    · have hΦp : Φ ((p : ℝ)/x)=0 := by
        by_contra hn
        have hs := hsupp hn
        have hlo : ⌊x*a⌋₊<p := (Nat.floor_lt (mul_nonneg hx.le ha.le)).mpr
          (by nlinarith [(lt_div_iff₀ hx).mp hs.1])
        have hhi : p≤⌊x*b⌋₊ := (Nat.le_floor_iff (mul_nonneg hx.le (ha.le.trans hab))).mpr
          (by nlinarith [(div_lt_iff₀ hx).mp hs.2])
        exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hlo,hhi⟩,
          (Finset.mem_filter.mp hp).2,hpU⟩)
      simp only [f,hΦp,Complex.ofReal_zero,zero_mul]
    · simp only [f,giantUnitResidueIndicator,ite_eq_right hpU,mul_zero]
  rw [giantUnshiftedPrimeTest, ← hsum]
  simp only [giantUnitPrimeAnnular, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpU := (Finset.mem_filter.mp hp).2.2
  simp only [f,giantUnitResidueIndicator,ite_eq_left hpU,mul_one]

theorem giant_normalized_complex_of_isLittleO (F : ℝ → ℂ)
    (h : F =o[atTop] (fun x : ℝ => x/Real.log x)) :
    Tendsto (fun x : ℝ => ((Real.log x/x : ℝ) : ℂ)*F x) atTop (𝓝 0) := by
  apply marked_complex_normalized_tendsto
  have hn := (Asymptotics.isLittleO_norm_left.mpr h).tendsto_div_nhds_zero
  apply hn.congr'
  filter_upwards [] with x
  rw [div_div_eq_mul_div]
  ring

theorem giant_unshifted_prime_mean {M : ℕ} [NeZero M] (U : Finset (ZMod M)ˣ)
    (Φ : ℝ → ℝ) (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ))
    {a b : ℝ} (ha : 0<a) (hab : a≤b) (hsupp : Function.support Φ ⊆ Set.Ioo a b) :
    Tendsto (fun x : ℝ => ((Real.log x/x : ℝ) : ℂ)*giantUnshiftedPrimeTest U Φ b x) atTop
      (𝓝 (((U.card : ℝ)/M.totient * ∫ t : ℝ, Φ t : ℝ) : ℂ)) := by
  have hΦa : Φ a=0 := Function.notMem_support.mp (fun h => (hsupp h).1.false)
  have hΦb : Φ b=0 := Function.notMem_support.mp (fun h => (hsupp h).2.false)
  have hint : (∫ t in a..b, Φ t) = ∫ t : ℝ, Φ t := by
    rw [intervalIntegral.integral_of_le hab]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    exact Function.notMem_support.mp (fun h => ht ⟨(hsupp h).1,(hsupp h).2.le⟩)
  have hreal := giant_unit_prime_annular_mean U Φ hΦ hderiv ha hab hΦa hΦb
  rw [hint] at hreal
  have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  apply hcomplex.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [giant_unshifted_test_eq_annular U Φ ha hab hsupp hx]
  simp only [Function.comp_apply]
  push_cast
  ring

/-- The literal shifted smooth prime progression mean, including nonunits. -/
theorem giant_shifted_prime_mean {M : ℕ} [NeZero M] (U : Finset (ZMod M)ˣ)
    (Φ : ℝ → ℝ) (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ))
    (hc : HasCompactSupport Φ) {a b : ℝ} (ha : 0<a) (hab : a≤b)
    (hsupp : Function.support Φ ⊆ Set.Ioo a b) :
    Tendsto (fun x : ℝ => ((Real.log x/x : ℝ) : ℂ)*giantShiftedPrimeTest U Φ b x) atTop
      (𝓝 (((U.card : ℝ)/M.totient * ∫ t : ℝ, Φ t : ℝ) : ℂ)) := by
  have hshift := giant_normalized_complex_of_isLittleO _
    (giant_prime_shift_isLittleO U Φ hΦ hderiv hc (ha.le.trans hab))
  have hmean := giant_unshifted_prime_mean U Φ hΦ hderiv ha hab hsupp
  have h := hshift.add hmean
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [] with x
  ring

def giantShiftedPrimeTestDeleted {M : ℕ} (U : Finset (ZMod M)ˣ) (E : Finset ℕ)
    (Φ : ℝ → ℝ) (T x : ℝ) : ℂ :=
  ∑ p ∈ giantPrimeMeanRange T x \ E,
    (Φ (((p : ℝ)-1)/x) : ℂ) * giantUnitResidueIndicator U p

/-- Any fixed finite ramification set can be deleted from the actual mean. -/
theorem giant_shifted_prime_mean_delete_fixed {M : ℕ} [NeZero M]
    (U : Finset (ZMod M)ˣ) (E : Finset ℕ)
    (Φ : ℝ → ℝ) (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ))
    (hc : HasCompactSupport Φ) {a b : ℝ} (ha : 0<a) (hab : a≤b)
    (hsupp : Function.support Φ ⊆ Set.Ioo a b) :
    Tendsto (fun x : ℝ => ((Real.log x/x : ℝ) : ℂ)*giantShiftedPrimeTestDeleted U E Φ b x) atTop
      (𝓝 (((U.card : ℝ)/M.totient * ∫ t : ℝ, Φ t : ℝ) : ℂ)) := by
  have hcC : HasCompactSupport (fun t => (Φ t : ℂ)) :=
    hc.comp_left (g := Complex.ofReal) rfl
  have hdel := smooth_prime_sum_delete_fixed_isLittleO E (giantPrimeMeanRange b)
    (fun t => (Φ t : ℂ)) (Complex.continuous_ofReal.comp hΦ.continuous) hcC
    (fun _ p => giantUnitResidueIndicator U p) (fun _ p _ => giantUnitResidueIndicator_norm_le U p)
  have hsmall := giant_normalized_complex_of_isLittleO _ hdel
  have hmean := giant_shifted_prime_mean U Φ hΦ hderiv hc ha hab hsupp
  have h := hmean.sub hsmall
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with x
  dsimp [giantShiftedPrimeTestDeleted,giantShiftedPrimeTest]
  ring

end
end ArtinMatthews
