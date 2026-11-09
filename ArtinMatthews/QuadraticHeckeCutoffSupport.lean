module

public import ArtinMatthews.QuadraticHeckeCutoffCancellation


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField VaryingKummerAnalytic UniqueFactorizationMonoid
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
open HeckeIdealMobius (divisors)

/-- Every surviving term lies in the finite multiplicative annulus from (7.3). -/
theorem quadraticHeckeCutoffTail_norm_bounds
    {g h d e : Ideal (𝓞 K)} {H : ℝ} (hg : Squarefree g)
    (hh : h ∈ quadraticHeckeCoprimeCutoff K g H)
    (hd : d ∣ g) (he : e ∣ g) (hcut : H < (Ideal.absNorm (h * d) : ℝ)) :
    H < (Ideal.absNorm (h * d * e) : ℝ) ∧
      (Ideal.absNorm (h * d * e) : ℝ) ≤ H * (Ideal.absNorm g : ℝ) ^ 2 := by
  have hh' := (mem_quadraticHeckeCoprimeCutoff K).1 hh
  have he₀ : e ≠ ⊥ := ne_zero_of_dvd_ne_zero hg.ne_zero he
  have hgpos : 0 < Ideal.absNorm g :=
    Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hg.ne_zero)
  have hdN : (Ideal.absNorm d : ℝ) ≤ Ideal.absNorm g := by
    exact_mod_cast Nat.le_of_dvd hgpos (map_dvd Ideal.absNorm hd)
  have heN : (Ideal.absNorm e : ℝ) ≤ Ideal.absNorm g := by
    exact_mod_cast Nat.le_of_dvd hgpos (map_dvd Ideal.absNorm he)
  have hH : 0 ≤ H := (Nat.cast_nonneg (Ideal.absNorm h)).trans hh'.2.1
  refine ⟨hcut.trans_le (quadraticHeckeNorm_le_norm_mul_right K (h * d) he₀), ?_⟩
  simp only [map_mul, Nat.cast_mul]
  calc
    (Ideal.absNorm h : ℝ) * Ideal.absNorm d * Ideal.absNorm e ≤
        (H * Ideal.absNorm g) * Ideal.absNorm g :=
      mul_le_mul (mul_le_mul hh'.2.1 hdN (Nat.cast_nonneg _) hH) heN
        (Nat.cast_nonneg _) (mul_nonneg hH (Nat.cast_nonneg _))
    _ = H * (Ideal.absNorm g : ℝ) ^ 2 := by ring

/-- The actual finite annulus supporting the cutoff discrepancy. -/
def quadraticHeckeCutoffAnnulus (g : Ideal (𝓞 K)) (H : ℝ) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K)
    (Nat.ceil (H * (Ideal.absNorm g : ℝ) ^ 2))).toFinset.filter
      (fun b => H < (Ideal.absNorm b : ℝ) ∧
        (Ideal.absNorm b : ℝ) ≤ H * (Ideal.absNorm g : ℝ) ^ 2)

theorem mem_quadraticHeckeCutoffAnnulus {g b : Ideal (𝓞 K)} {H : ℝ} :
    b ∈ quadraticHeckeCutoffAnnulus K g H ↔
      H < (Ideal.absNorm b : ℝ) ∧
        (Ideal.absNorm b : ℝ) ≤ H * (Ideal.absNorm g : ℝ) ^ 2 := by
  simp only [quadraticHeckeCutoffAnnulus, Finset.mem_filter,
    Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  constructor
  · exact And.right
  · intro hb
    refine ⟨?_, hb⟩
    exact_mod_cast hb.2.trans (Nat.le_ceil _)

/-- Collect the divisor triples with the same resulting integral ideal. -/
def quadraticHeckeCutoffCoefficient (g : Ideal (𝓞 K)) (H : ℝ)
    (b : Ideal (𝓞 K)) : ℂ :=
  ∑ h ∈ quadraticHeckeCoprimeCutoff K g H, ∑ d ∈ divisors K g, ∑ e ∈ divisors K g,
    if h * d * e = b ∧ H < (Ideal.absNorm (h * d) : ℝ) then -(moebius e : ℂ) else 0

/-- A grouped coefficient vanishes outside the genuine norm annulus. -/
theorem quadraticHeckeCutoffCoefficient_eq_zero_of_not_mem
    {g b : Ideal (𝓞 K)} {H : ℝ} (hg : Squarefree g)
    (hb : b ∉ quadraticHeckeCutoffAnnulus K g H) :
    quadraticHeckeCutoffCoefficient K g H b = 0 := by
  unfold quadraticHeckeCutoffCoefficient
  apply Finset.sum_eq_zero
  intro h hh
  apply Finset.sum_eq_zero
  intro d hd
  apply Finset.sum_eq_zero
  intro e he
  apply ite_eq_right
  rintro ⟨rfl, hcut⟩
  apply hb
  exact (mem_quadraticHeckeCutoffAnnulus K).2
    (quadraticHeckeCutoffTail_norm_bounds K hg hh
      ((HeckeIdealMobius.mem_divisors K hg.ne_zero).1 hd)
      ((HeckeIdealMobius.mem_divisors K hg.ne_zero).1 he) hcut)

/-- Grouping the finite triples gives a single finite ideal sum with controlled support. -/
theorem quadraticHeckeMainTerm_cutoffGrouped {M : Ideal (𝓞 K)}
    (ψ : EvenIdealRayCharacter K M)
    (hχ : ∀ J : Ideal (𝓞 K), J ≠ ⊥ → IsCoprime J M → ψ.allCoefficient J ^ 2 = 1)
    (g : Ideal (𝓞 K)) (hg : Squarefree g) (hgM : IsCoprime g M) (H : ℝ) :
    (∑ a ∈ quadraticHeckeSquarefreeCutoff K H, quadraticHeckeHalfCoefficient K ψ a) *
        (∑ e ∈ divisors K g, (moebius e : ℂ) * quadraticHeckeHalfCoefficient K ψ e) -
      (∑ h ∈ quadraticHeckeCoprimeCutoff K g H, quadraticHeckeHalfCoefficient K ψ h) *
        quadraticHeckeCoprimeDensity K g =
      ∑ b ∈ quadraticHeckeCutoffAnnulus K g H,
        quadraticHeckeCutoffCoefficient K g H b * quadraticHeckeHalfCoefficient K ψ b := by
  rw [quadraticHeckeMainTerm_cutoffTail K ψ hχ g hg hgM H]
  simp only [quadraticHeckeCutoffCoefficient, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  conv_rhs => rw [Finset.sum_comm]
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

end
end ArtinMatthews
