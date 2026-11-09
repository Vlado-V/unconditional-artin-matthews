module

public import ArtinMatthews.QuadraticHeckeCutoffSquarePart


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField VaryingKummerAnalytic UniqueFactorizationMonoid
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
open HeckeIdealMobius (divisors)

omit [NumberField K] in
private theorem coprime_cutoff_product {g m h d e : Ideal (𝓞 K)}
    (hgm : IsCoprime g m) (hd : d ∣ g) (he : e ∣ g) :
    IsCoprime (h * d * e) m ↔ IsCoprime h m := by
  rw [IsCoprime.mul_left_iff, IsCoprime.mul_left_iff]
  simp only [hgm.of_isCoprime_of_dvd_left hd, hgm.of_isCoprime_of_dvd_left he, and_true]

/-- Group the literal omitted triples against any ideal test function. -/
theorem quadraticHeckeCutoffCoefficient_sum (g : Ideal (𝓞 K)) (hg : Squarefree g)
    (H : ℝ) (f : Ideal (𝓞 K) → ℂ) :
    (∑ b ∈ quadraticHeckeCutoffAnnulus K g H, quadraticHeckeCutoffCoefficient K g H b * f b) =
      ∑ h ∈ quadraticHeckeCoprimeCutoff K g H, ∑ d ∈ divisors K g, ∑ e ∈ divisors K g,
        if H < (Ideal.absNorm (h * d) : ℝ) then -(moebius e : ℂ) * f (h * d * e) else 0 := by
  simp only [quadraticHeckeCutoffCoefficient, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hcut : H < (Ideal.absNorm (h * d) : ℝ)
  · have hb : h * d * e ∈ quadraticHeckeCutoffAnnulus K g H :=
      (mem_quadraticHeckeCutoffAnnulus K).2
        (quadraticHeckeCutoffTail_norm_bounds K hg hh
          ((HeckeIdealMobius.mem_divisors K hg.ne_zero).1 hd)
          ((HeckeIdealMobius.mem_divisors K hg.ne_zero).1 he) hcut)
    simp only [hcut, and_true, ite_true, ite_mul, zero_mul, Finset.sum_ite_eq, hb]
  · simp only [hcut, and_false, ite_false, zero_mul, Finset.sum_const_zero]

/-- Exact cutoff cancellation while retaining an auxiliary coprimality mask. -/
theorem quadraticHeckeMainTerm_maskedCutoffTail {M : Ideal (𝓞 K)}
    (ψ : EvenIdealRayCharacter K M)
    (hχ : ∀ J : Ideal (𝓞 K), J ≠ ⊥ → IsCoprime J M → ψ.allCoefficient J ^ 2 = 1)
    (g m : Ideal (𝓞 K)) (hg : Squarefree g) (hgM : IsCoprime g M)
    (hgm : IsCoprime g m) (H : ℝ) :
    (∑ a ∈ quadraticHeckeSquarefreeCutoff K H,
      if IsCoprime a m then quadraticHeckeHalfCoefficient K ψ a else 0) *
        (∑ e ∈ divisors K g, (moebius e : ℂ) * quadraticHeckeHalfCoefficient K ψ e) -
      (∑ h ∈ quadraticHeckeCoprimeCutoff K g H,
        if IsCoprime h m then quadraticHeckeHalfCoefficient K ψ h else 0) *
          quadraticHeckeCoprimeDensity K g =
      ∑ h ∈ quadraticHeckeCoprimeCutoff K g H, ∑ d ∈ divisors K g, ∑ e ∈ divisors K g,
        if IsCoprime h m ∧ H < (Ideal.absNorm (h * d) : ℝ) then
          -(moebius e : ℂ) * quadraticHeckeHalfCoefficient K ψ (h * d * e) else 0 := by
  let A := quadraticHeckeHalfCoefficient K ψ
  have heuler := quadraticHeckeMainTermEuler_self K ψ hχ g hg hgM
  have hlocal (h : Ideal (𝓞 K)) :
      A h * quadraticHeckeCoprimeDensity K g =
        ∑ d ∈ divisors K g, ∑ e ∈ divisors K g, (moebius e : ℂ) * A (h * d * e) := by
    rw [← heuler, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    simp only [A, map_mul]
    ring
  have hsplit : (∑ a ∈ quadraticHeckeSquarefreeCutoff K H, if IsCoprime a m then A a else 0) =
      ∑ h ∈ quadraticHeckeCoprimeCutoff K g H,
        if IsCoprime h m then
          ∑ d ∈ divisors K g, if (Ideal.absNorm (h * d) : ℝ) ≤ H then A (h * d) else 0
        else 0 := by
    rw [quadraticHeckeSquarefreeCutoff_split K g hg H]
    apply Finset.sum_congr rfl
    intro h _
    have hcop (d : Ideal (𝓞 K)) (hd : d ∈ divisors K g) :
        IsCoprime (h * d) m ↔ IsCoprime h m := by
      rw [IsCoprime.mul_left_iff]
      simp only [hgm.of_isCoprime_of_dvd_left ((HeckeIdealMobius.mem_divisors K hg.ne_zero).1 hd), and_true]
    by_cases hh : IsCoprime h m
    · rw [ite_eq_left hh]
      apply Finset.sum_congr rfl
      intro d hd
      rw [hcop d hd]
      simp only [hh, ite_true]
    · rw [ite_eq_right hh]
      apply Finset.sum_eq_zero
      intro d hd
      rw [hcop d hd]
      simp only [hh, ite_false, ite_self]
  change (∑ a ∈ quadraticHeckeSquarefreeCutoff K H, if IsCoprime a m then A a else 0) *
      (∑ e ∈ divisors K g, (moebius e : ℂ) * A e) -
    (∑ h ∈ quadraticHeckeCoprimeCutoff K g H, if IsCoprime h m then A h else 0) *
      quadraticHeckeCoprimeDensity K g = _
  rw [hsplit]
  simp only [Finset.sum_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hh : IsCoprime h m
  · simp only [hh, ite_true, true_and]
    rw [hlocal h, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hc : (Ideal.absNorm (h * d) : ℝ) ≤ H
    · rw [ite_eq_left hc, ite_eq_right (not_lt.mpr hc)]
      simp only [A, map_mul]
      ring
    · rw [ite_eq_right hc, ite_eq_left (lt_of_not_ge hc)]
      simp only [zero_mul, zero_sub, A, map_mul]
      ring
  · simp only [hh, ite_false, false_and, zero_mul, sub_self, Finset.sum_const_zero]

/-- The auxiliary mask remains on the grouped ideal itself. -/
theorem quadraticHeckeMainTerm_maskedCutoffGrouped {M : Ideal (𝓞 K)}
    (ψ : EvenIdealRayCharacter K M)
    (hχ : ∀ J : Ideal (𝓞 K), J ≠ ⊥ → IsCoprime J M → ψ.allCoefficient J ^ 2 = 1)
    (g m : Ideal (𝓞 K)) (hg : Squarefree g) (hgM : IsCoprime g M)
    (hgm : IsCoprime g m) (H : ℝ) :
    (∑ a ∈ quadraticHeckeSquarefreeCutoff K H,
      if IsCoprime a m then quadraticHeckeHalfCoefficient K ψ a else 0) *
        (∑ e ∈ divisors K g, (moebius e : ℂ) * quadraticHeckeHalfCoefficient K ψ e) -
      (∑ h ∈ quadraticHeckeCoprimeCutoff K g H,
        if IsCoprime h m then quadraticHeckeHalfCoefficient K ψ h else 0) *
          quadraticHeckeCoprimeDensity K g =
      ∑ b ∈ quadraticHeckeCutoffAnnulus K g H, if IsCoprime b m then
        quadraticHeckeCutoffCoefficient K g H b * quadraticHeckeHalfCoefficient K ψ b else 0 := by
  rw [quadraticHeckeMainTerm_maskedCutoffTail K ψ hχ g m hg hgM hgm H]
  have heq := quadraticHeckeCutoffCoefficient_sum K g hg H
    (fun b => if IsCoprime b m then quadraticHeckeHalfCoefficient K ψ b else 0)
  calc
    _ = ∑ h ∈ quadraticHeckeCoprimeCutoff K g H, ∑ d ∈ divisors K g, ∑ e ∈ divisors K g,
        if H < (Ideal.absNorm (h * d) : ℝ) then -(moebius e : ℂ) *
          (if IsCoprime (h * d * e) m then quadraticHeckeHalfCoefficient K ψ (h * d * e) else 0)
        else 0 := by
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      rw [coprime_cutoff_product K hgm
        ((HeckeIdealMobius.mem_divisors K hg.ne_zero).1 hd)
        ((HeckeIdealMobius.mem_divisors K hg.ne_zero).1 he)]
      by_cases hm : IsCoprime h m
      · simp only [hm, true_and, ite_true]
      · simp only [hm, false_and, ite_false, mul_zero, ite_self]
    _ = ∑ b ∈ quadraticHeckeCutoffAnnulus K g H, quadraticHeckeCutoffCoefficient K g H b *
        (if IsCoprime b m then quadraticHeckeHalfCoefficient K ψ b else 0) := heq.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      rw [mul_ite, mul_zero]

end
end ArtinMatthews
