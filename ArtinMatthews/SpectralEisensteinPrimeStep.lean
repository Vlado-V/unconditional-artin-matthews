module

public import ArtinMatthews.SpectralEisensteinMultipleScaling


set_option backward.privateInPublic true
@[expose] public section

/-! Actual convergent totient-series recurrences when a prime is adjoined to the level. -/
noncomputable section
open Set
namespace ArtinMatthews

def gamma0EisensteinTotientPrimePart (N p : ℕ) (s : ℂ) : ℂ :=
  ∑' n : SpectralEisensteinMultipleIndex N,
    if p∣n.val then (n.val.totient:ℂ)*(n.val:ℂ)^(-2*s) else 0

theorem gamma0EisensteinTotientPrimePart_summable (N p : ℕ) (s : ℂ) (hs : 1<s.re) :
    Summable (fun n : SpectralEisensteinMultipleIndex N =>
      if p∣n.val then (n.val.totient:ℂ)*(n.val:ℂ)^(-2*s) else 0) := by
  have h := (gamma0EisensteinTotientSeries_summable N s hs).indicator
    {n : SpectralEisensteinMultipleIndex N | p∣n.val}
  change Summable (fun n : SpectralEisensteinMultipleIndex N =>
    ({n : SpectralEisensteinMultipleIndex N | p∣n.val}).indicator
      (fun c => (c.val.totient:ℂ)*(c.val:ℂ)^(-2*s)) n) at h
  simpa only [Set.indicator_apply,Set.mem_ofPred_eq] using h

theorem gamma0EisensteinTotientSeries_prime_linear (N p : ℕ) (hp : p.Prime)
    (s : ℂ) (hs : 1<s.re) :
    (∑' n : SpectralEisensteinMultipleIndex N, ((p*n.val).totient:ℂ)*(n.val:ℂ)^(-2*s)) =
      ((p:ℂ)-1)*gamma0EisensteinTotientSeries N s+gamma0EisensteinTotientPrimePart N p s := by
  have he (n : SpectralEisensteinMultipleIndex N) :
      ((p*n.val).totient:ℂ)*(n.val:ℂ)^(-2*s) =
        ((p:ℂ)-1)*((n.val.totient:ℂ)*(n.val:ℂ)^(-2*s))+
          if p∣n.val then (n.val.totient:ℂ)*(n.val:ℂ)^(-2*s) else 0 := by
    rw [spectralTotient_prime_linear p hp n.val]
    split_ifs <;> ring
  simp_rw [he]
  rw [Summable.tsum_add ((gamma0EisensteinTotientSeries_summable N s hs).mul_left _)
    (gamma0EisensteinTotientPrimePart_summable N p s hs),tsum_mul_left]
  rfl

theorem gamma0EisensteinTotientPrimePart_of_dvd (N p : ℕ) (hpN : p∣N) (s : ℂ) :
    gamma0EisensteinTotientPrimePart N p s=gamma0EisensteinTotientSeries N s := by
  unfold gamma0EisensteinTotientPrimePart gamma0EisensteinTotientSeries
  apply tsum_congr
  intro n
  rw [ite_eq_left (dvd_trans hpN n.property.2)]

def spectralEisensteinJointMultipleEquiv (N p : ℕ) (hcop : Nat.Coprime p N) :
    SpectralEisensteinMultipleIndex (p*N) ≃ ({n : SpectralEisensteinMultipleIndex N | p∣n.val}) where
  toFun n := ⟨⟨n.val,n.property.1,dvd_trans (dvd_mul_left N p) n.property.2⟩,
    dvd_trans (dvd_mul_right p N) n.property.2⟩
  invFun n := ⟨n.val.val,n.val.property.1,hcop.mul_dvd_of_dvd_of_dvd n.property n.val.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem gamma0EisensteinTotientPrimePart_of_coprime (N p : ℕ) (hcop : Nat.Coprime p N) (s : ℂ) :
    gamma0EisensteinTotientPrimePart N p s=gamma0EisensteinTotientSeries (p*N) s := by
  let f : SpectralEisensteinMultipleIndex N → ℂ := fun n => (n.val.totient:ℂ)*(n.val:ℂ)^(-2*s)
  calc
    _ = ∑' n : ({n : SpectralEisensteinMultipleIndex N | p∣n.val}), f n.val := by
      symm
      rw [tsum_subtype]
      unfold gamma0EisensteinTotientPrimePart
      apply tsum_congr
      intro n
      simp [Set.indicator_apply,f]
    _ = _ := (spectralEisensteinJointMultipleEquiv N p hcop).tsum_eq (fun n => f n.val) |>.symm

theorem gamma0EisensteinTotientSeries_prime_existing (N p : ℕ) (hp : p.Prime) (hpN : p∣N)
    (s : ℂ) (hs : 1<s.re) :
    gamma0EisensteinTotientSeries (p*N) s=(p:ℂ)*(p:ℂ)^(-2*s)*gamma0EisensteinTotientSeries N s := by
  rw [gamma0EisensteinTotientSeries_scale N p hp.pos s,
    gamma0EisensteinTotientSeries_prime_linear N p hp s hs,
    gamma0EisensteinTotientPrimePart_of_dvd N p hpN s]
  ring

theorem gamma0EisensteinTotientSeries_prime_new (N p : ℕ) (hp : p.Prime) (hpN : ¬p∣N)
    (s : ℂ) (hs : 1<s.re) :
    (1-(p:ℂ)^(-2*s))*gamma0EisensteinTotientSeries (p*N) s=
      ((p:ℂ)-1)*(p:ℂ)^(-2*s)*gamma0EisensteinTotientSeries N s := by
  have h := gamma0EisensteinTotientSeries_scale N p hp.pos s
  rw [gamma0EisensteinTotientSeries_prime_linear N p hp s hs,
    gamma0EisensteinTotientPrimePart_of_coprime N p (hp.coprime_iff_not_dvd.mpr hpN) s] at h
  linear_combination h

end ArtinMatthews
