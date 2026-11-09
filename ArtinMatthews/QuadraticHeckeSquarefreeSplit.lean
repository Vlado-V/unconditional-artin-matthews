module

public import ArtinMatthews.QuadraticHeckeMainTermEuler


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]

private theorem ideal_isCoprime_iff_isRelPrime (I J : Ideal (𝓞 K)) :
    IsCoprime I J ↔ IsRelPrime I J := by
  rw [Ideal.isCoprime_iff_gcd, ← gcd_isUnit_iff_isRelPrime, Ideal.isUnit_iff, Ideal.one_eq_top]

private theorem gcd_mul_eq_of_coprime {g h d : Ideal (𝓞 K)}
    (hc : IsCoprime h g) (hd : d ∣ g) : gcd (h * d) g = d := by
  obtain ⟨j, hj⟩ := hd
  have hcop := hc.of_isCoprime_of_dvd_right (show j ∣ g by rw [hj]; exact dvd_mul_left _ _)
  rw [Ideal.isCoprime_iff_gcd] at hcop
  rw [hj, mul_comm h d, gcd_mul_left, normalize_eq, hcop, mul_one]

private theorem split_squarefree_exists {a g : Ideal (𝓞 K)}
    (ha : Squarefree a) : ∃ h d : Ideal (𝓞 K),
      Squarefree h ∧ IsCoprime h g ∧ d ∣ g ∧ h * d = a := by
  let d := gcd a g
  obtain ⟨h, hh⟩ : d ∣ a := gcd_dvd_left _ _
  obtain ⟨j, hj⟩ : d ∣ g := gcd_dvd_right _ _
  have hd : d ≠ 0 := ne_zero_of_dvd_ne_zero ha.ne_zero (gcd_dvd_left a g)
  have hdh : Squarefree (d * h) := hh ▸ ha
  have hhj : gcd h j = 1 := by
    have hd' : d = gcd (d * h) (d * j) := by change gcd a g = _; rw [← hh, ← hj]
    rw [gcd_mul_left, normalize_eq] at hd'
    nth_rw 1 [← mul_one d] at hd'
    exact (mul_left_cancel₀ hd hd').symm
  refine ⟨h, d, hdh.of_mul_right, ?_, gcd_dvd_right _ _, (mul_comm h d).trans hh.symm⟩
  have hcd : IsCoprime h d := (ideal_isCoprime_iff_isRelPrime K _ _).2
    (IsRelPrime.of_squarefree_mul hdh).symm
  have hcj : IsCoprime h j := Ideal.isCoprime_iff_gcd.mpr hhj
  rw [hj, IsCoprime.mul_right_iff]
  exact ⟨hcd, hcj⟩

/-- Split a squarefree ideal by the prime support of the fixed squarefree
common ideal. The second factor is precisely its ideal gcd. -/
def quadraticHeckeSquarefreeCoprimeSplit (g : Ideal (𝓞 K)) (hg : Squarefree g) :
    ({h : Ideal (𝓞 K) // Squarefree h ∧ IsCoprime h g} × {d : Ideal (𝓞 K) // d ∣ g}) ≃
      {a : Ideal (𝓞 K) // Squarefree a} :=
  Equiv.ofBijective (fun p =>
    ⟨p.1.val * p.2.val, squarefree_mul_iff.mpr
      ⟨(ideal_isCoprime_iff_isRelPrime K _ _).1
        (p.1.property.2.of_isCoprime_of_dvd_right p.2.property),
        p.1.property.1, hg.squarefree_of_dvd p.2.property⟩⟩)
    ⟨fun p q hpq => by
      have h : p.1.val * p.2.val = q.1.val * q.2.val := congrArg Subtype.val hpq
      have hd : p.2.val = q.2.val := by
        rw [← gcd_mul_eq_of_coprime K p.1.property.2 p.2.property,
          ← gcd_mul_eq_of_coprime K q.1.property.2 q.2.property, h]
      have hq : q.2.val ≠ 0 := ne_zero_of_dvd_ne_zero hg.ne_zero q.2.property
      rw [hd] at h
      exact Prod.ext (Subtype.ext (mul_right_cancel₀ hq h)) (Subtype.ext hd),
    fun a => by
      obtain ⟨h, d, hs, hc, hd, he⟩ := split_squarefree_exists K a.property
      exact ⟨(⟨h, hs, hc⟩, ⟨d, hd⟩), Subtype.ext he⟩⟩

theorem quadraticHeckeSquarefreeCoprimeSplit_val (g : Ideal (𝓞 K)) (hg : Squarefree g)
    (p : {h : Ideal (𝓞 K) // Squarefree h ∧ IsCoprime h g} × {d : Ideal (𝓞 K) // d ∣ g}) :
    (quadraticHeckeSquarefreeCoprimeSplit K g hg p).val = p.1.val * p.2.val := rfl

end
end ArtinMatthews
