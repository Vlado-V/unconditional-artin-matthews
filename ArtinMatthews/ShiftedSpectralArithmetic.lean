module

public import ArtinMatthews.ShiftedCommonPrimePartSquarefree
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-!
# The actual arithmetic factors in ABL Theorem 2.4

The modulus is the literal `N * shiftedCommonPrimePart m₁ m₂ ^ 2` and the
Kloosterman fixed frequency is the difference of the actual gcd quotients.
The divisibility below removes the apparent additional spectral gcd loss.
This module contains no spectral estimate.
-/

namespace ArtinMatthews

/-- A difference of two coprime integers is coprime to their product. -/
theorem shifted_reduced_difference_coprime {a b : ℕ} (hab : a.Coprime b) :
    (((a : ℤ)-b).natAbs).Coprime (a*b) := by
  have ha : (((a : ℤ)-b).natAbs).Coprime a := by
    change Nat.gcd (((a : ℤ)-b).natAbs) a = 1
    calc
      _ = Int.gcd ((a : ℤ)-b) (a : ℤ) := by simp only [Int.gcd,Int.natAbs_natCast]
      _ = Int.gcd (b : ℤ) (a : ℤ) := Int.gcd_self_sub_left _ _
      _ = 1 := by rw [Int.gcd_natCast_natCast]; exact hab.symm
  have hb : (((a : ℤ)-b).natAbs).Coprime b := by
    change Nat.gcd (((a : ℤ)-b).natAbs) b = 1
    calc
      _ = Int.gcd ((a : ℤ)-b) (b : ℤ) := by simp only [Int.gcd,Int.natAbs_natCast]
      _ = Int.gcd (a : ℤ) (b : ℤ) := Int.gcd_sub_self_left _ _
      _ = 1 := by rw [Int.gcd_natCast_natCast]; exact hab
  exact ha.mul_right hb

/-- The full common-prime part, rather than a squarefree radical, is exactly
the gcd with the square of its enlarged supporting modulus. -/
theorem gcd_commonPrimePart_enlarged_square {n : ℕ} (hn : n ≠ 0) (d : ℕ) :
    Nat.gcd n ((d*commonPrimePart n d)^2) = commonPrimePart n d := by
  let R := commonPrimePart n d
  let A := n/R
  have hAR : A*R = n := Nat.div_mul_cancel (commonPrimePart_dvd n d)
  have hdA : d.Coprime A := coprime_commonPrimePart_quotient hn d
  have hRA : R.Coprime A := commonPrimePart_coprime hn hdA
  have hAD : A.Coprime (d*R) := hdA.symm.mul_right hRA.symm
  have hRd : R ∣ d*R := Nat.dvd_mul_left _ _
  have hRpow : R ∣ (d*R)^2 := hRd.trans (dvd_pow_self _ (by norm_num : 2 ≠ 0))
  change Nat.gcd n ((d*R)^2) = R
  rw [← hAR]
  exact Nat.gcd_mul_of_coprime_of_dvd (hAD.pow_right 2) hRpow

/-- Exact factorization of the manuscript's actual common-prime part after
taking the actual gcd quotients. Squarefreeness is not needed for this identity. -/
theorem shiftedCommonPrimePart_eq_gcd_mul_reduced {m₁ m₂ : ℕ}
    (hm₁ : 0 < m₁) (hne : m₁ ≠ m₂) :
    let d := m₁.gcd m₂
    let m₃ := m₁/d
    let m₄ := m₂/d
    shiftedCommonPrimePart m₁ m₂ = d*commonPrimePart (((m₃ : ℤ)-m₄).natAbs) d := by
  dsimp only
  let d := m₁.gcd m₂
  let m₃ := m₁/d
  let m₄ := m₂/d
  have hd : 0 < d := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left m₁ m₂) hm₁
  have h₁ : m₁ = d*m₃ := (Nat.mul_div_cancel' (Nat.gcd_dvd_left m₁ m₂)).symm
  have h₂ : m₂ = d*m₄ := (Nat.mul_div_cancel' (Nat.gcd_dvd_right m₁ m₂)).symm
  have hn : ((m₃ : ℤ)-m₄).natAbs ≠ 0 := by
    apply Int.natAbs_ne_zero.mpr
    intro hh
    have heq : m₃ = m₄ := by exact_mod_cast sub_eq_zero.mp hh
    exact hne (h₁.trans (by rw [heq,← h₂]))
  have habs : ((m₁ : ℤ)-m₂).natAbs = d*((m₃ : ℤ)-m₄).natAbs := by
    have heq : (m₁ : ℤ)-m₂ = (d : ℤ)*((m₃ : ℤ)-m₄) := by
      have hz₁ : (m₁ : ℤ) = (d : ℤ)*m₃ := by exact_mod_cast h₁
      have hz₂ : (m₂ : ℤ) = (d : ℤ)*m₄ := by exact_mod_cast h₂
      rw [hz₁,hz₂]
      ring
    simpa only [Int.natAbs_mul,Int.natAbs_natCast] using congrArg Int.natAbs heq
  change commonPrimePart ((m₁ : ℤ)-m₂).natAbs d =
    d*commonPrimePart (((m₃ : ℤ)-m₄).natAbs) d
  rw [habs,commonPrimePart_mul hd.ne' hn,commonPrimePart_self hd.ne']

/-- The spectral gcd without the fixed level is exactly `D/d`, for the actual
squarefree source pair and actual full common-prime part. -/
theorem squarefree_shifted_spectral_gcd_eq {m₁ m₂ : ℕ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hne : m₁ ≠ m₂)
    (hs₁ : Squarefree m₁) (hs₂ : Squarefree m₂) :
    let d := m₁.gcd m₂
    let m₃ := m₁/d
    let m₄ := m₂/d
    Nat.gcd (((m₃ : ℤ)-m₄).natAbs)
      ((shiftedCommonPrimePart m₁ m₂)^2*(m₃*m₄)) = shiftedCommonPrimePart m₁ m₂/d := by
  dsimp only
  let d := m₁.gcd m₂
  let m₃ := m₁/d
  let m₄ := m₂/d
  let n := ((m₃ : ℤ)-m₄).natAbs
  let R := commonPrimePart n d
  obtain ⟨_R₀,_A₀,_hR₀,_hD₀,_hfactor,_hcop,_hcopd,hcop₃₄⟩ :=
    squarefree_commonPrimePart_factors hm₁ hm₂ hne hs₁ hs₂
  have hd : 0 < d := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left m₁ m₂) hm₁
  have hD : shiftedCommonPrimePart m₁ m₂ = d*R :=
    shiftedCommonPrimePart_eq_gcd_mul_reduced hm₁ hne
  have hn : n ≠ 0 := by
    intro hn
    have heq : m₃ = m₄ := by exact_mod_cast sub_eq_zero.mp (Int.natAbs_eq_zero.mp hn)
    have hh₁ := Nat.mul_div_cancel' (Nat.gcd_dvd_left m₁ m₂)
    have hh₂ := Nat.mul_div_cancel' (Nat.gcd_dvd_right m₁ m₂)
    change d*m₃ = m₁ at hh₁
    change d*m₄ = m₂ at hh₂
    exact hne (hh₁.symm.trans (by rw [heq,hh₂]))
  have hnp : n.Coprime (m₃*m₄) := shifted_reduced_difference_coprime hcop₃₄
  have hg := gcd_commonPrimePart_enlarged_square hn d
  have hdiv := Nat.gcd_mul_right_dvd_mul_gcd n ((d*R)^2) (m₃*m₄)
  rw [hnp.gcd_eq_one,mul_one,hg] at hdiv
  have hreverse : R ∣ Nat.gcd n ((d*R)^2*(m₃*m₄)) := by
    apply Nat.dvd_gcd (commonPrimePart_dvd n d)
    exact (Nat.dvd_gcd_iff.mp (show R ∣ Nat.gcd n ((d*R)^2) by rw [hg])).2.trans
      (Nat.dvd_mul_right _ _)
  change Nat.gcd n ((shiftedCommonPrimePart m₁ m₂)^2*(m₃*m₄)) = shiftedCommonPrimePart m₁ m₂/d
  rw [hD,Nat.mul_div_cancel_left R hd]
  exact Nat.dvd_antisymm hdiv hreverse

/-- The actual ABL fixed-frequency gcd divides `N*(D/d)`. -/
theorem squarefree_shifted_spectral_gcd_dvd {m₁ m₂ : ℕ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hne : m₁ ≠ m₂)
    (hs₁ : Squarefree m₁) (hs₂ : Squarefree m₂) (N : ℕ) :
    let d := m₁.gcd m₂
    let m₃ := m₁/d
    let m₄ := m₂/d
    Nat.gcd (((m₃ : ℤ)-m₄).natAbs)
      (N*(shiftedCommonPrimePart m₁ m₂)^2*(m₃*m₄)) ∣ N*(shiftedCommonPrimePart m₁ m₂/d) := by
  dsimp only
  let n := (((m₁/(m₁.gcd m₂) : ℕ) : ℤ)-(m₂/(m₁.gcd m₂) : ℕ)).natAbs
  let P := (shiftedCommonPrimePart m₁ m₂)^2*((m₁/(m₁.gcd m₂))*(m₂/(m₁.gcd m₂)))
  have hg := squarefree_shifted_spectral_gcd_eq hm₁ hm₂ hne hs₁ hs₂
  have hdiv := Nat.gcd_mul_right_dvd_mul_gcd n N P
  rw [mul_assoc]
  change Nat.gcd n (N*P) ∣ N*(shiftedCommonPrimePart m₁ m₂/(m₁.gcd m₂))
  refine hdiv.trans ?_
  rw [show Nat.gcd n P = shiftedCommonPrimePart m₁ m₂/(m₁.gcd m₂) from hg]
  exact Nat.mul_dvd_mul (Nat.gcd_dvd_right n N) dvd_rfl

/-- The corresponding genuine numerical bound has only the fixed-level loss. -/
theorem squarefree_shifted_spectral_gcd_le {m₁ m₂ : ℕ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hne : m₁ ≠ m₂)
    (hs₁ : Squarefree m₁) (hs₂ : Squarefree m₂) {N : ℕ} (hN : 0 < N) :
    let d := m₁.gcd m₂
    let m₃ := m₁/d
    let m₄ := m₂/d
    Nat.gcd (((m₃ : ℤ)-m₄).natAbs)
      (N*(shiftedCommonPrimePart m₁ m₂)^2*(m₃*m₄)) ≤ N*(shiftedCommonPrimePart m₁ m₂/d) := by
  obtain ⟨R,_A,hR,hD,_hfactor,_hcop,_hcopd,_hcop₃₄⟩ :=
    squarefree_commonPrimePart_factors hm₁ hm₂ hne hs₁ hs₂
  have hd : 0 < m₁.gcd m₂ := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left m₁ m₂) hm₁
  have hpos : 0 < N*(shiftedCommonPrimePart m₁ m₂/(m₁.gcd m₂)) := by
    rw [hD,Nat.mul_div_cancel_left R hd]
    exact Nat.mul_pos hN (Nat.pos_of_ne_zero hR)
  exact Nat.le_of_dvd hpos (squarefree_shifted_spectral_gcd_dvd hm₁ hm₂ hne hs₁ hs₂ N)

/-- The real form used under ABL's fourth root, with its actual `D/d` ratio. -/
theorem squarefree_shifted_spectral_gcd_le_real {m₁ m₂ : ℕ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hne : m₁ ≠ m₂)
    (hs₁ : Squarefree m₁) (hs₂ : Squarefree m₂) {N : ℕ} (hN : 0 < N) :
    let d := m₁.gcd m₂
    let m₃ := m₁/d
    let m₄ := m₂/d
    (Nat.gcd (((m₃ : ℤ)-m₄).natAbs)
      (N*(shiftedCommonPrimePart m₁ m₂)^2*(m₃*m₄)) : ℝ) ≤
        (N : ℝ)*(shiftedCommonPrimePart m₁ m₂ : ℝ)/(d : ℝ) := by
  dsimp only
  obtain ⟨R,_A,_hR,hD,_hfactor,_hcop,_hcopd,_hcop₃₄⟩ :=
    squarefree_commonPrimePart_factors hm₁ hm₂ hne hs₁ hs₂
  have hd : 0 < m₁.gcd m₂ := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left m₁ m₂) hm₁
  have hdR : (m₁.gcd m₂ : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hg := squarefree_shifted_spectral_gcd_le hm₁ hm₂ hne hs₁ hs₂ hN
  dsimp only at hg
  rw [hD,Nat.mul_div_cancel_left R hd] at hg
  have hcast := (show ((Nat.gcd (((m₁/(m₁.gcd m₂) : ℕ) : ℤ)-
      (m₂/(m₁.gcd m₂) : ℕ)).natAbs)
      (N*((m₁.gcd m₂)*R)^2*((m₁/(m₁.gcd m₂))*(m₂/(m₁.gcd m₂)))) : ℝ) ≤
        (N : ℝ)*(R : ℝ) by exact_mod_cast hg)
  calc
    _ ≤ (N : ℝ)*(R : ℝ) := by rw [hD]; exact hcast
    _ = (N : ℝ)*(shiftedCommonPrimePart m₁ m₂ : ℝ)/(m₁.gcd m₂ : ℝ) := by
      rw [hD,Nat.cast_mul]
      field_simp [hdR]

/-- Coprimality of the literal circle modulus with the actual reduced product. -/
theorem squarefree_shifted_circle_coprime {m₁ m₂ : ℕ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hne : m₁ ≠ m₂)
    (hs₁ : Squarefree m₁) (hs₂ : Squarefree m₂) {N : ℕ}
    (hN : (m₁*m₂).Coprime N) :
    (N*(shiftedCommonPrimePart m₁ m₂)^2).Coprime
      ((m₁/(m₁.gcd m₂))*(m₂/(m₁.gcd m₂))) := by
  obtain ⟨_R,_A,_hR,_hD,_hfactor,_hcop,hcopd,_hcop₃₄⟩ :=
    squarefree_commonPrimePart_factors hm₁ hm₂ hne hs₁ hs₂
  have hn : ((m₁ : ℤ)-m₂).natAbs ≠ 0 := by
    apply Int.natAbs_ne_zero.mpr
    intro hh
    exact hne (by exact_mod_cast sub_eq_zero.mp hh)
  have hD := commonPrimePart_coprime hn hcopd
  have hprod : (m₁/(m₁.gcd m₂))*(m₂/(m₁.gcd m₂)) ∣ m₁*m₂ :=
    Nat.mul_dvd_mul (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left m₁ m₂))
      (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right m₁ m₂))
  exact (hN.symm.of_dvd_right hprod).mul_left (hD.pow_left 2)

end ArtinMatthews
