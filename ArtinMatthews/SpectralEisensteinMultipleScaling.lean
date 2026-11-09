module

public import ArtinMatthews.SpectralGamma0EisensteinTotientSeries


set_option backward.privateInPublic true
@[expose] public section

/-! Exact rescaling of the actual positive-multiple index, before Euler-factor algebra. -/
noncomputable section
namespace ArtinMatthews

abbrev SpectralEisensteinMultipleIndex (N : ℕ) := {c : ℕ // 0<c ∧ N∣c}

def spectralEisensteinMultipleScale (N p : ℕ) (hp : 0<p) :
    SpectralEisensteinMultipleIndex N ≃ SpectralEisensteinMultipleIndex (p*N) :=
  Equiv.ofBijective
    (fun n => ⟨p*n.val,Nat.mul_pos hp n.property.1,Nat.mul_dvd_mul_left p n.property.2⟩)
    ⟨by
      intro a b h
      apply Subtype.ext
      have he : p*a.val=p*b.val := congrArg Subtype.val h
      exact Nat.eq_of_mul_eq_mul_left hp he,by
      rintro ⟨c,hc,⟨k,rfl⟩⟩
      have hnk : 0<N*k := by
        by_contra h
        have hz : N*k=0 := by omega
        rw [mul_assoc,hz,mul_zero] at hc
        exact Nat.not_lt_zero _ hc
      refine ⟨⟨N*k,hnk,dvd_mul_right N k⟩,Subtype.ext ?_⟩
      exact (mul_assoc p N k).symm⟩

theorem spectralEisensteinMultipleScale_apply (N p : ℕ) (hp : 0<p)
    (n : SpectralEisensteinMultipleIndex N) :
    (spectralEisensteinMultipleScale N p hp n).val=p*n.val := rfl

theorem gamma0EisensteinTotientSeries_scale (N p : ℕ) (hp : 0<p) (s : ℂ) :
    gamma0EisensteinTotientSeries (p*N) s = (p:ℂ)^(-2*s)*
      ∑' n : SpectralEisensteinMultipleIndex N, ((p*n.val).totient:ℂ)*(n.val:ℂ)^(-2*s) := by
  let e := spectralEisensteinMultipleScale N p hp
  unfold gamma0EisensteinTotientSeries
  rw [← e.tsum_eq (fun c : SpectralEisensteinMultipleIndex (p*N) =>
    (c.val.totient:ℂ)*(c.val:ℂ)^(-2*s))]
  simp only [e,spectralEisensteinMultipleScale_apply,Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

theorem spectralTotient_prime_linear (p : ℕ) (hp : p.Prime) (n : ℕ) :
    ((p*n).totient:ℂ)=((p:ℂ)-1)*(n.totient:ℂ)+if p∣n then (n.totient:ℂ) else 0 := by
  by_cases hd : p∣n
  · rw [Nat.totient_mul_of_prime_of_dvd hp hd,ite_eq_left hd,Nat.cast_mul]
    ring
  · rw [Nat.totient_mul_of_prime_of_not_dvd hp hd,ite_eq_right hd,Nat.cast_mul,Nat.cast_sub hp.one_le]
    simp

end ArtinMatthews
