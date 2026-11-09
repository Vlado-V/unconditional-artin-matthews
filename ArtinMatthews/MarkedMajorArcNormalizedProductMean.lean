module

public import ArtinMatthews.MarkedMajorArcProductMean
public import ArtinMatthews.MarkedMajorArcCoefficientBounds
public import Mathlib.NumberTheory.Harmonic.Bounds


set_option backward.privateInPublic true
@[expose] public section

/-! Product mean square with the literal centered prime-minus-rough
polynomial and an arbitrary bounded dyadic coefficient polynomial. -/
namespace ArtinMatthews
open Finset MeasureTheory

 theorem marked_centered_dyadic_product_mean {q : ℕ} (χ : DirichletCharacter ℂ q)
    (W modulation H u v U T ξ B : ℝ) (l r : ℕ) (a : ℕ → ℂ)
    (hH : 0 < H) (hU : 0 < U) (hT : 0 < T) (hB : 0 ≤ B)
    (hHu : H ≤ u) (hv : v ≤ 2*H) (hlog : 1 ≤ Real.log u)
    (hl : U ≤ (l:ℝ)) (hr : (r:ℝ) ≤ 2*U) (ha : ∀ n ∈ Icc l r, ‖a n‖ ≤ B) :
    (∫ t in -T..T,
      ‖markedMajorCenteredSum χ W modulation (t+ξ) H u v*
        markedDyadicPolynomial l r U a (t+ξ)‖^2) ≤
      8*Real.exp 1*(T+(⌊4*H*U⌋₊:ℝ))*
        ((((1+(markedSieveEulerProduct W)⁻¹)/H)*(B/U))^2*(⌊4*H*U⌋₊:ℝ)*
          (1+Real.log (⌊4*H*U⌋₊:ℝ))^3) := by
  let A := 1+(markedSieveEulerProduct W)⁻¹
  let N := ⌊4*H*U⌋₊
  let c := fun n => (H:ℂ)⁻¹*(markedMajorCenteredCoefficient W modulation n*χ (n:ZMod q))
  let b := fun n => a n/(U:ℂ)
  have hV := markedSieveEulerProduct_pos W
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hu : 0 < u := hH.trans_le hHu
  have hS : ∀ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, 0 < n := by
    intro n hn
    have := (mem_Ioc.mp hn).1
    omega
  have hR : ∀ n ∈ Icc l r, 0 < n := by
    intro n hn
    have hnl : (l:ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    exact_mod_cast hU.trans_le (hl.trans hnl)
  have hsupport : ∀ m ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, ∀ n ∈ Icc l r, m*n ≤ N := by
    intro m hm n hn
    have hmv : (m:ℝ) ≤ 2*H := by
      have hmf : (m:ℝ) ≤ (⌊v⌋₊:ℝ) := by exact_mod_cast (mem_Ioc.mp hm).2
      have hv0 : 0 ≤ v := by
        have huf : ⌊u⌋₊ < ⌊v⌋₊ := (mem_Ioc.mp hm).1.trans_le (mem_Ioc.mp hm).2
        have : 0 < ⌊v⌋₊ := lt_of_le_of_lt (Nat.zero_le _) huf
        have := Nat.floor_pos.mp this
        linarith
      exact hmf.trans ((Nat.floor_le hv0).trans hv)
    have hnu : (n:ℝ) ≤ 2*U := (show (n:ℝ) ≤ r by exact_mod_cast (mem_Icc.mp hn).2).trans hr
    apply (Nat.le_floor_iff (by positivity : (0:ℝ) ≤ 4*H*U)).mpr
    rw [Nat.cast_mul]
    nlinarith [mul_le_mul hmv hnu (Nat.cast_nonneg n) (by positivity : (0:ℝ) ≤ 2*H)]
  have hc : ∀ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, ‖c n‖ ≤ A/H :=
    fun n hn => marked_centered_normalized_coefficient_bound χ W modulation hH hu hlog n hn
  have hb : ∀ n ∈ Icc l r, ‖b n‖ ≤ B/U := by
    intro n hn
    dsimp [b]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hU]
    exact div_le_div_of_nonneg_right (ha n hn) hU.le
  have he (t : ℝ) : markedDyadicPolynomial l r U a t = markedNaturalPolynomial (Icc l r) b t := by
    unfold markedDyadicPolynomial markedNaturalPolynomial
    rw [sum_div]
    apply sum_congr rfl
    intro n _
    dsimp [b]
    ring
  simp_rw [marked_centered_sum_eq_natural,he]
  have hh := markedNaturalPolynomial_product_mean_square (Ioc ⌊u⌋₊ ⌊v⌋₊) (Icc l r) c b
    N (A/H) (B/U) ξ T (div_nonneg hA hH.le) (div_nonneg hB hU.le) hT hS hR hsupport hc hb
  have hharm : (∑ d ∈ Icc 1 N,1/(d:ℝ)) ≤ 1+Real.log (N:ℝ) := by
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
      using harmonic_le_one_add_log N
  exact hh.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sum_nonneg (fun _ _ => by positivity)) hharm 3)
      (by positivity)) (by positivity))

end ArtinMatthews
