module

public import ArtinMatthews.CubicThetaDyadic
public import ArtinMatthews.ShiftedABLDualPartition
public import ArtinMatthews.ShiftedDualDyadic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! A finite rectangle of the original smooth dual blocks and its exact
quantitative remainder, before specializing the circle and cutoff powers. -/

noncomputable section
open Set OAI
open scoped BigOperators

namespace ArtinMatthews

/-- The finite rectangle of the original two smooth dyadic indices. -/
def shiftedABLDualRectangle (J : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (J+1)).product (Finset.range (J+1))

private theorem shiftedABLDual_partial_sum (a : ℕ × ℕ → ℂ) (ha : Summable a)
    (h₁ : ∀ k, a k ≠ 0 → 1 ≤ k.1) (h₂ : ∀ k, a k ≠ 0 → 1 ≤ k.2) (J : ℕ) :
    (∑ d ∈ shiftedABLDualRectangle J, ∑' k : ℕ × ℕ,
      spectralDyadicCoefficient (a k) k.1 k.2 d) =
      ∑' k : ℕ × ℕ, a k *
        ((shiftedABLDualPartial J k.1 * shiftedABLDualPartial J k.2 : ℝ) : ℂ) := by
  have hall := spectralDyadic_expansion_summable a Prod.fst Prod.snd ha h₁ h₂
  have hd (d : ℕ × ℕ) : Summable (fun k : ℕ × ℕ =>
      spectralDyadicCoefficient (a k) k.1 k.2 d) :=
    hall.comp_injective (i := fun k : ℕ × ℕ => (k,d)) (fun _ _ h => congrArg Prod.fst h)
  rw [← Summable.tsum_finsetSum (s := shiftedABLDualRectangle J) (fun d _ => hd d)]
  congr 1
  funext k
  simp only [spectralDyadicCoefficient, ← Finset.mul_sum, ← Complex.ofReal_sum,
    shiftedABLDualRectangle, shiftedABLDualPartial]
  let S := Finset.range (J+1)
  let u (i : ℕ) := spectralDyadicBlock i k.1
  let v (i : ℕ) := spectralDyadicBlock i k.2
  exact congrArg (fun x : ℝ => a k*(x : ℂ))
    ((Finset.sum_product S S (fun i : ℕ × ℕ => u i.1*v i.2)).trans
      (Finset.sum_mul_sum S S u v).symm)

private theorem shiftedABLDualNonzero_norm_le (q : ℕ) [NeZero q] (D m3 m4 : ℕ)
    (a b : ℕ → ℂ) (k : ℕ × ℕ) :
    ‖shiftedDualNonzeroTerm q D m3 m4 a b k‖ ≤ (q : ℝ)*‖a k.1‖*‖b k.2‖ := by
  unfold shiftedDualNonzeroTerm shiftedDualTerm
  split_ifs
  · rw [norm_zero]; positivity
  · simp only [one_mul, norm_mul]
    have h := ordinaryKloosterman_norm_le_card q
      ((m3 : ZMod q)-(m4 : ZMod q))
      (((m3 : ZMod q)*(m4 : ZMod q))⁻¹*((m4 : ZMod q)*k.2-(m3 : ZMod q)*k.1))
    rw [ZMod.card_units_eq_totient] at h
    calc
      _ ≤ (‖a k.1‖*‖b k.2‖)*(q : ℝ) :=
        mul_le_mul_of_nonneg_left (h.trans (Nat.cast_le.mpr (Nat.totient_le q))) (by positivity)
      _ = _ := by ring
  · simp only [zero_mul, mul_zero, norm_zero]
    positivity

private theorem shiftedABLDual_partial_error (q : ℕ) [NeZero q] (D m3 m4 J B : ℕ)
    (a b : ℕ → ℂ) (ha0 : a 0 = 0) (hb0 : b 0 = 0)
    (S U C : ℝ) (hS : 0 < S) (hU : 0 < U) (hC : 0 ≤ C)
    (hJ : U ≤ (2 : ℝ)^J)
    (ha : ∀ k : ℕ, ‖a k‖ ≤ C*(1/(k : ℝ)^2)/(1+(k : ℝ)/S)^B)
    (hb : ∀ k : ℕ, ‖b k‖ ≤ C*(1/(k : ℝ)^2)/(1+(k : ℝ)/S)^B) :
    ‖(∑' k, shiftedDualNonzeroTerm q D m3 m4 a b k) -
      ∑ d ∈ shiftedABLDualRectangle J, ∑' k : ℕ × ℕ,
        spectralDyadicCoefficient (shiftedDualNonzeroTerm q D m3 m4 a b k)
          k.1 k.2 d‖ ≤
      (q : ℝ)*C^2*(S/U)^B*(∑' k : ℕ, 1/(k : ℝ)^2)^2 := by
  let v (k : ℕ) : ℝ := 1/(k : ℝ)^2
  have hv (k : ℕ) : 0 ≤ v k := by dsimp [v]; positivity
  have hvs : Summable v := Real.summable_one_div_nat_pow.mpr (by decide)
  have ht (k : ℕ) : 1 ≤ 1+(k : ℝ)/S :=
    le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg k) hS.le)
  have htotal (z : ℕ → ℂ)
      (hz : ∀ k : ℕ, ‖z k‖ ≤ C*v k/(1+(k : ℝ)/S)^B) (k : ℕ) :
      ‖z k‖ ≤ C*v k := (hz k).trans
    (div_le_self (mul_nonneg hC (hv k)) (one_le_pow₀ (ht k)))
  have htail (z : ℕ → ℂ)
      (hz : ∀ k : ℕ, ‖z k‖ ≤ C*v k/(1+(k : ℝ)/S)^B) (k : ℕ) (hk : U ≤ k) :
      ‖z k‖ ≤ C*v k*(S/U)^B := by
    have hle : U/S ≤ 1+(k : ℝ)/S := by
      linarith [div_le_div_of_nonneg_right hk hS.le]
    calc
      _ ≤ C*v k/(1+(k : ℝ)/S)^B := hz k
      _ ≤ C*v k/(U/S)^B := div_le_div_of_nonneg_left (mul_nonneg hC (hv k))
        (pow_pos (div_pos hU hS) B) (pow_le_pow_left₀ (by positivity) hle B)
      _ = _ := by rw [div_pow, div_pow]; field_simp [hS.ne', hU.ne']
  have has : Summable a := (hvs.mul_left C).of_norm_bounded (htotal a ha)
  have hbs : Summable b := (hvs.mul_left C).of_norm_bounded (htotal b hb)
  let f := shiftedDualNonzeroTerm q D m3 m4 a b
  let w (k : ℕ × ℕ) : ℝ := shiftedABLDualPartial J k.1 * shiftedABLDualPartial J k.2
  have hw (k : ℕ × ℕ) : 0 ≤ w k ∧ w k ≤ 1 := by
    obtain ⟨h₁,h₁'⟩ := shiftedABLDualPartial_bounds J k.1
    obtain ⟨h₂,h₂'⟩ := shiftedABLDualPartial_bounds J k.2
    exact ⟨mul_nonneg h₁ h₂, by dsimp [w]; nlinarith [mul_le_mul h₁' h₂' h₂ zero_le_one]⟩
  have hf : Summable f := shiftedDualNonzeroTerm_summable q D m3 m4 a b has hbs
  have hp₁ : ∀ k, f k ≠ 0 → 1 ≤ k.1 := shiftedDualNonzeroTerm_fst_pos q D m3 m4 a b ha0
  have hp₂ : ∀ k, f k ≠ 0 → 1 ≤ k.2 := shiftedDualNonzeroTerm_snd_pos q D m3 m4 a b hb0
  have hfcut : Summable (fun k : ℕ × ℕ => f k * (w k : ℂ)) := by
    apply hf.norm.of_norm_bounded
    intro k
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw k).1]
    exact mul_le_of_le_one_right (norm_nonneg _) (hw k).2
  rw [shiftedABLDual_partial_sum f hf hp₁ hp₂, ← hf.tsum_sub hfcut]
  let E := (q : ℝ)*C^2*(S/U)^B
  let F (k : ℕ × ℕ) : ℂ := f k - f k * (w k : ℂ)
  change ‖∑' k, F k‖ ≤ E*(∑' k, v k)^2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hpoint (k : ℕ × ℕ) : ‖F k‖ ≤ E*(v k.1*v k.2) := by
    by_cases hf0 : f k = 0
    · simp only [F,hf0,zero_mul,sub_zero,norm_zero]
      positivity
    have hw' : ‖F k‖ ≤ ‖f k‖ := by
      have he : F k = f k * ((1-w k : ℝ) : ℂ) := by
        simp only [F, Complex.ofReal_sub, Complex.ofReal_one]
        ring
      rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr (hw k).2)]
      exact mul_le_of_le_one_right (norm_nonneg _) (by linarith [(hw k).1])
    have hd := shiftedABLDualNonzero_norm_le q D m3 m4 a b k
    by_cases hk₁ : (k.1 : ℝ) ≤ (2 : ℝ)^J
    · by_cases hk₂ : (k.2 : ℝ) ≤ (2 : ℝ)^J
      · have hz : w k = 1 := by
          simp only [w, shiftedABLDualPartial_eq_one (hp₁ k hf0) hk₁,
            shiftedABLDualPartial_eq_one (hp₂ k hf0) hk₂, mul_one]
        simp only [F,hz,Complex.ofReal_one,mul_one,sub_self,norm_zero]
        positivity
      · apply hw'.trans (hd.trans _)
        calc
          _ ≤ (q : ℝ)*(C*v k.1)*(C*v k.2*(S/U)^B) := by
            gcongr
            exacts [htotal a ha _, htail b hb _ (hJ.trans (lt_of_not_ge hk₂).le)]
          _ = _ := by dsimp [E]; ring
    · apply hw'.trans (hd.trans _)
      calc
        _ ≤ (q : ℝ)*(C*v k.1*(S/U)^B)*(C*v k.2) := by
          gcongr
          exacts [htail a ha _ (hJ.trans (lt_of_not_ge hk₁).le), htotal b hb _]
        _ = _ := by dsimp [E]; ring
  have hprod : Summable (fun k : ℕ × ℕ => v k.1*v k.2) :=
    summable_mul_of_summable_norm hvs.norm hvs.norm
  have hsum := (hprod.mul_left E)
  have hFs := hsum.of_norm_bounded hpoint
  calc
    _ ≤ ∑' k, ‖F k‖ := norm_tsum_le_tsum_norm hFs.norm
    _ ≤ ∑' k : ℕ × ℕ, E*(v k.1*v k.2) := hFs.norm.tsum_le_tsum hpoint hsum
    _ = _ := by rw [tsum_mul_left, pow_two, hvs.tsum_mul_tsum hvs hprod]

/-- Exact truncation of the literal normalized nonzero dual at one
modulus. The phase, congruence and Kloosterman argument are retained. -/
theorem shiftedABLThetaDualNormalized_partial_error
    (χ : SevenEighths.HeckeFamily.Character) (W1 W2 : SchwartzMap ℝ ℂ)
    (K1 K2 : ℝ) (D m3 m4 q J B : ℕ) (hq : 0 < q)
    (S U C : ℝ) (hS : 0 < S) (hU : 0 < U) (hC : 0 ≤ C)
    (hJ : U ≤ (2 : ℝ)^J)
    (ha : ∀ k : ℕ, ‖thetaBesselCoeff χ W1 K1 ((q : ℝ)^2) k‖ ≤
      C*(1/(k : ℝ)^2)/(1+(k : ℝ)/S)^B)
    (hb : ∀ k : ℕ, ‖thetaBesselCoeff χ W2 K2 ((q : ℝ)^2) k‖ ≤
      C*(1/(k : ℝ)^2)/(1+(k : ℝ)/S)^B) :
    ‖thetaDualNonzeroNormalized χ W1 W2 K1 K2 D m3 m4 q -
      ∑ d ∈ shiftedABLDualRectangle J, thetaDualDyadicNormalized χ W1 W2 K1 K2 D m3 m4 q d‖ ≤
      C^2*(S/U)^B*(∑' k : ℕ, 1/(k : ℝ)^2)^2 := by
  let : NeZero q := ⟨hq.ne'⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  simp only [thetaDualNonzeroNormalized, thetaDualDyadicNormalized, dite_eq_right hq.ne',
    ← Finset.mul_sum, ← mul_sub, norm_mul, norm_div, norm_pow, Complex.norm_natCast]
  have h := shiftedABLDual_partial_error q D m3 m4 J B
    (thetaBesselCoeff χ W1 K1 ((q : ℝ)^2)) (thetaBesselCoeff χ W2 K2 ((q : ℝ)^2))
    (thetaBesselCoeff_zero _ _ _ _) (thetaBesselCoeff_zero _ _ _ _) S U C hS hU hC hJ ha hb
  have hψ : ‖cubicThetaNebentypus (-((m3 : ℕ) : ℤ) * m4)‖ ≤ 1 :=
    cubicThetaNebentypus_norm_le_one _
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans_le hq1
  calc
    _ ≤ (1/(q : ℝ)^2)*((q : ℝ)*C^2*(S/U)^B*(∑' k : ℕ, 1/(k : ℝ)^2)^2) :=
      mul_le_mul (div_le_div_of_nonneg_right hψ (sq_nonneg _)) h (norm_nonneg _) (by positivity)
    _ = (1/(q : ℝ))*(C^2*(S/U)^B*(∑' k : ℕ, 1/(k : ℝ)^2)^2) := by
      field_simp [hq0.ne']
    _ ≤ _ := mul_le_of_le_one_left (by positivity) ((div_le_one hq0).2 hq1)

end ArtinMatthews
