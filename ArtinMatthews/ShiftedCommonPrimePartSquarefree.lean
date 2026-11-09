module

public import ArtinMatthews.ShiftedCommonPrimePartInteger


set_option backward.privateInPublic true
@[expose] public section

/-! The actual squarefree gcd factorization used in the double Voronoi sum. -/

namespace ArtinMatthews

/-- The manuscript's literal `(m₁-m₂,(m₁,m₂)^∞)`. -/
def shiftedCommonPrimePart (m₁ m₂ : ℕ) : ℕ :=
  commonPrimePart ((m₁ : ℤ) - m₂).natAbs (m₁.gcd m₂)

/-- All factors in the stationary congruence are obtained from the actual
common-prime part and the actual gcd quotients. -/
theorem squarefree_commonPrimePart_factors {m₁ m₂ : ℕ}
    (hm₁ : 0 < m₁) (_hm₂ : 0 < m₂) (hne : m₁ ≠ m₂)
    (hs₁ : Squarefree m₁) (hs₂ : Squarefree m₂) :
    let d := m₁.gcd m₂
    let m₃ := m₁ / d
    let m₄ := m₂ / d
    ∃ (R : ℕ) (A₀ : ℤ), R ≠ 0 ∧
      shiftedCommonPrimePart m₁ m₂ = d * R ∧
      (m₃ : ℤ) - m₄ = (R : ℤ) * A₀ ∧
      IsCoprime (d : ℤ) ((m₃ : ℤ) * A₀) ∧
      d.Coprime (m₃ * m₄) ∧ m₃.Coprime m₄ := by
  let d := m₁.gcd m₂
  let m₃ := m₁ / d
  let m₄ := m₂ / d
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left m₁ m₂) hm₁
  have hd0 : d ≠ 0 := hdpos.ne'
  have h₁ : m₁ = d * m₃ := (Nat.mul_div_cancel' (Nat.gcd_dvd_left m₁ m₂)).symm
  have h₂ : m₂ = d * m₄ := (Nat.mul_div_cancel' (Nat.gcd_dvd_right m₁ m₂)).symm
  have hcop₃ : d.Coprime m₃ := Nat.coprime_of_squarefree_mul (by rwa [← h₁])
  have hcop₄ : d.Coprime m₄ := Nat.coprime_of_squarefree_mul (by rwa [← h₂])
  have hv : (m₃ : ℤ) - m₄ ≠ 0 := by
    intro h
    have heq : m₃ = m₄ := by exact_mod_cast sub_eq_zero.mp h
    exact hne (h₁.trans (by rw [heq, ← h₂]))
  let R := commonPrimePart ((m₃ : ℤ) - m₄).natAbs d
  have hR0 : R ≠ 0 := commonPrimePart_ne_zero (Int.natAbs_ne_zero.mpr hv) d
  obtain ⟨A₀, hA₀, hcopA₀⟩ := exists_commonPrimePart_integer_complement hv d
  have habs : ((m₁ : ℤ) - m₂).natAbs = d * ((m₃ : ℤ) - m₄).natAbs := by
    have heq : (m₁ : ℤ) - m₂ = (d : ℤ) * ((m₃ : ℤ) - m₄) := by
      have h₁z : (m₁ : ℤ) = (d : ℤ) * m₃ := by exact_mod_cast h₁
      have h₂z : (m₂ : ℤ) = (d : ℤ) * m₄ := by exact_mod_cast h₂
      rw [h₁z, h₂z]
      ring
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using congrArg Int.natAbs heq
  have hD : shiftedCommonPrimePart m₁ m₂ = d * R := by
    unfold shiftedCommonPrimePart
    change commonPrimePart ((m₁ : ℤ) - m₂).natAbs d = d * R
    rw [habs, commonPrimePart_mul hd0 (Int.natAbs_ne_zero.mpr hv), commonPrimePart_self hd0]
  refine ⟨R, A₀, hR0, hD, hA₀, hcop₃.isCoprime.mul_right hcopA₀,
    hcop₃.mul_right hcop₄, ?_⟩
  exact Nat.coprime_div_gcd_div_gcd hdpos

end ArtinMatthews
