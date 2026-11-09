module

public import ArtinMatthews.QuadraticHeckeCutoffSquarePart
public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusBound


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField VaryingKummerAnalytic UniqueFactorizationMonoid
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
open HeckeIdealMobius (divisors primeSupport)

/-- A squarefree ideal has at most its norm many divisors. -/
theorem quadraticHecke_divisor_card_le_norm (g : Ideal (𝓞 K)) (hg : Squarefree g) :
    (divisors K g).card ≤ Ideal.absNorm g := by
  have hfilter : (divisors K g).filter Squarefree = divisors K g := by
    apply Finset.filter_eq_self.mpr
    intro d hd
    exact hg.squarefree_of_dvd ((HeckeIdealMobius.mem_divisors K hg.ne_zero).1 hd)
  have hcard : (divisors K g).card ≤ 2 ^ (primeSupport K g).card := by
    rw [← hfilter]
    exact HeckeIdealMobius.squarefree_divisor_card_le K g hg.ne_zero
  have hp (P : Ideal (𝓞 K)) (hP : P ∈ primeSupport K g) : 2 ≤ Ideal.absNorm P := by
    have hprime := HeckeIdealMobius.support_prime K hP
    have hzero : Ideal.absNorm P ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hprime.ne_zero
    have hone : Ideal.absNorm P ≠ 1 := by
      intro h
      exact hprime.not_isUnit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp h))
    omega
  apply hcard.trans
  calc
    2 ^ (primeSupport K g).card = ∏ _P ∈ primeSupport K g, (2 : ℕ) := by simp
    _ ≤ ∏ P ∈ primeSupport K g, Ideal.absNorm P :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) hp
    _ = Ideal.absNorm (∏ P ∈ primeSupport K g, P) := by rw [map_prod]
    _ = Ideal.absNorm g := by rw [HeckeIdealMobius.squarefree_support_product_self K hg]

private theorem coefficient_fiber_norm_le_one {g d e b : Ideal (𝓞 K)} (hg : g ≠ ⊥)
    (hd : d ∣ g) (he : e ∣ g) (H : ℝ) :
    ‖∑ h ∈ quadraticHeckeCoprimeCutoff K g H,
      if h * d * e = b ∧ H < (Ideal.absNorm (h * d) : ℝ) then -(moebius e : ℂ) else 0‖ ≤ 1 := by
  have hd₀ : d ≠ ⊥ := ne_zero_of_dvd_ne_zero hg hd
  have he₀ : e ≠ ⊥ := ne_zero_of_dvd_ne_zero hg he
  let S := quadraticHeckeCoprimeCutoff K g H
  have hcard : (S.filter (fun h => h * d * e = b)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro h hh j hj
    have hh' := (Finset.mem_filter.mp hh).2
    have hj' := (Finset.mem_filter.mp hj).2
    exact mul_right_cancel₀ hd₀ (mul_right_cancel₀ he₀ (hh'.trans hj'.symm))
  have hterm (h : Ideal (𝓞 K)) :
      ‖if h * d * e = b ∧ H < (Ideal.absNorm (h * d) : ℝ) then -(moebius e : ℂ) else 0‖ ≤
        if h * d * e = b then (1 : ℝ) else 0 := by
    by_cases hc : h * d * e = b ∧ H < (Ideal.absNorm (h * d) : ℝ)
    · rw [ite_eq_left hc, ite_eq_left hc.1, norm_neg]
      exact HeckeIdealMobius.norm_moebius_le_one K e
    · rw [ite_eq_right hc, norm_zero]
      split_ifs <;> norm_num
  calc
    _ ≤ ∑ h ∈ S,
        ‖if h * d * e = b ∧ H < (Ideal.absNorm (h * d) : ℝ) then -(moebius e : ℂ) else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ h ∈ S, if h * d * e = b then (1 : ℝ) else 0 :=
      Finset.sum_le_sum (fun h _ => hterm h)
    _ = ((S.filter (fun h => h * d * e = b)).card : ℝ) := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ 1 := by exact_mod_cast hcard

/-- Each pair of divisors contributes at most one cutoff ideal to a grouped coefficient. -/
theorem quadraticHeckeCutoffCoefficient_norm_le_divisor_card_sq
    {g : Ideal (𝓞 K)} (hg : g ≠ ⊥) (H : ℝ) (b : Ideal (𝓞 K)) :
    ‖quadraticHeckeCutoffCoefficient K g H b‖ ≤ ((divisors K g).card : ℝ) ^ 2 := by
  have heq : quadraticHeckeCutoffCoefficient K g H b =
      ∑ d ∈ divisors K g, ∑ e ∈ divisors K g, ∑ h ∈ quadraticHeckeCoprimeCutoff K g H,
        if h * d * e = b ∧ H < (Ideal.absNorm (h * d) : ℝ) then -(moebius e : ℂ) else 0 := by
    unfold quadraticHeckeCutoffCoefficient
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.sum_comm]
  rw [heq]
  calc
    _ ≤ ∑ d ∈ divisors K g, ‖∑ e ∈ divisors K g, ∑ h ∈ quadraticHeckeCoprimeCutoff K g H,
        if h * d * e = b ∧ H < (Ideal.absNorm (h * d) : ℝ) then -(moebius e : ℂ) else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ d ∈ divisors K g, ∑ e ∈ divisors K g, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro e he
      exact coefficient_fiber_norm_le_one K hg
        ((HeckeIdealMobius.mem_divisors K hg).1 hd)
        ((HeckeIdealMobius.mem_divisors K hg).1 he) H
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one, pow_two]

/-- A crude norm-square loss in the common ideal uniformly controls every coefficient. -/
theorem quadraticHeckeCutoffCoefficient_norm_le_norm_sq
    {g : Ideal (𝓞 K)} (hg : Squarefree g) (H : ℝ) (b : Ideal (𝓞 K)) :
    ‖quadraticHeckeCutoffCoefficient K g H b‖ ≤ (Ideal.absNorm g : ℝ) ^ 2 := by
  apply (quadraticHeckeCutoffCoefficient_norm_le_divisor_card_sq K hg.ne_zero H b).trans
  exact pow_le_pow_left₀ (Nat.cast_nonneg _)
    (by exact_mod_cast quadraticHecke_divisor_card_le_norm K g hg) 2

/-- The finite support has at most one image for each cutoff ideal and pair of divisors. -/
theorem quadraticHeckeCutoffCoefficient_support_card
    {g : Ideal (𝓞 K)} (H : ℝ) :
    ((quadraticHeckeCutoffAnnulus K g H).filter
      (fun b => quadraticHeckeCutoffCoefficient K g H b ≠ 0)).card ≤
        (quadraticHeckeCoprimeCutoff K g H).card * (divisors K g).card ^ 2 := by
  let T := ((quadraticHeckeCoprimeCutoff K g H ×ˢ divisors K g) ×ˢ divisors K g)
  let f (p : (Ideal (𝓞 K) × Ideal (𝓞 K)) × Ideal (𝓞 K)) := p.1.1 * p.1.2 * p.2
  have hsub : (quadraticHeckeCutoffAnnulus K g H).filter
      (fun b => quadraticHeckeCutoffCoefficient K g H b ≠ 0) ⊆ T.image f := by
    intro b hb
    have hn := (Finset.mem_filter.mp hb).2
    unfold quadraticHeckeCutoffCoefficient at hn
    obtain ⟨h, hh, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    obtain ⟨d, hd, hdne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨e, he, hene⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdne
    have hc : h * d * e = b ∧ H < (Ideal.absNorm (h * d) : ℝ) := by
      by_contra hc
      exact hene (ite_eq_right hc)
    exact Finset.mem_image.mpr ⟨((h, d), e), Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨hh, hd⟩, he⟩, hc.1⟩
  calc
    _ ≤ (T.image f).card := Finset.card_le_card hsub
    _ ≤ T.card := Finset.card_image_le
    _ = _ := by simp only [T, Finset.card_product, pow_two, mul_assoc]

/-- On its support, the normalized coefficient gains the reciprocal square root of the cutoff. -/
theorem quadraticHeckeCutoffCoefficient_div_sqrt_bound
    {g : Ideal (𝓞 K)} (hg : Squarefree g) {H : ℝ} (hH : 0 < H) (b : Ideal (𝓞 K)) :
    ‖quadraticHeckeCutoffCoefficient K g H b‖ / Real.sqrt (Ideal.absNorm b : ℝ) ≤
      (Ideal.absNorm g : ℝ) ^ 2 / Real.sqrt H := by
  by_cases hb : quadraticHeckeCutoffCoefficient K g H b = 0
  · rw [hb, norm_zero, zero_div]
    positivity
  · have hs := quadraticHeckeCutoffCoefficient_support K hg hb
    have hroot : 0 < Real.sqrt H := Real.sqrt_pos.mpr hH
    have hbroot : Real.sqrt H ≤ Real.sqrt (Ideal.absNorm b : ℝ) :=
      Real.sqrt_le_sqrt hs.1.le
    apply (div_le_div_of_nonneg_right
      (quadraticHeckeCutoffCoefficient_norm_le_norm_sq K hg H b)
      (Real.sqrt_nonneg _)).trans
    exact div_le_div_of_nonneg_left (sq_nonneg _) hroot hbroot

end
end ArtinMatthews
