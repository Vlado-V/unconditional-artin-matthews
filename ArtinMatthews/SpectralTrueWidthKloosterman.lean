module

public import ArtinMatthews.SpectralCuspWidthRefinement
public import ArtinMatthews.SpectralTrueWidthNormalizedMatrices
public import ArtinMatthews.SpectralCuspWidthCharacters


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite multiplicities in the passage from common-period N phases
to the normalized primitive cusp phases. -/

noncomputable section
open Matrix
open scoped MatrixGroups BigOperators

namespace ArtinMatthews

theorem cuspGeometricPhase_trueWidth_translate (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (m n c : ℤ) (hc : c ≠ 0) (M : SL(2, ℤ))
    (hM : M 1 0 = c) (l k : ℤ) :
    cuspGeometricPhase N m n c
      (integerTranslation ((gamma0CuspTrueWidth N s : ℤ)*l) * M *
        integerTranslation ((gamma0CuspTrueWidth N r : ℤ)*k)) =
      cuspGeometricPhase N m n c M *
        atkinPhase ((n : ℝ)*(gamma0CuspTrueWidth N s : ℝ)*l/N) *
        atkinPhase ((m : ℝ)*(gamma0CuspTrueWidth N r : ℝ)*k/N) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  obtain ⟨hA,_,hD⟩ := integerTranslation_entries
    ((gamma0CuspTrueWidth N s : ℤ)*l) ((gamma0CuspTrueWidth N r : ℤ)*k) M
  have he :
      ((m : ℝ)*((integerTranslation ((gamma0CuspTrueWidth N s : ℤ)*l) * M *
        integerTranslation ((gamma0CuspTrueWidth N r : ℤ)*k)) 1 1 : ℝ) +
      (n : ℝ)*((integerTranslation ((gamma0CuspTrueWidth N s : ℤ)*l) * M *
        integerTranslation ((gamma0CuspTrueWidth N r : ℤ)*k)) 0 0 : ℝ)) / ((N : ℝ)*c) =
      ((m : ℝ)*(M 1 1 : ℝ)+(n : ℝ)*(M 0 0 : ℝ))/((N : ℝ)*c) +
      (n : ℝ)*(gamma0CuspTrueWidth N s : ℝ)*l/N +
      (m : ℝ)*(gamma0CuspTrueWidth N r : ℝ)*k/N := by
    rw [hA,hD,hM]
    push_cast
    field_simp [hN,hcR]
    ring
  unfold cuspGeometricPhase
  rw [he,atkinPhase_add,atkinPhase_add]

theorem gamma0PeriodKloostermanSum_width_characters (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] (m n : ℤ) :
    gamma0PeriodKloostermanSum N r s c m n =
      (∑ a : Fin (gamma0CuspFrequencyStep N s),
        atkinPhase ((n : ℝ)*(gamma0CuspTrueWidth N s : ℝ)*a.val/N)) *
      (∑ b : Fin (gamma0CuspFrequencyStep N r),
        atkinPhase ((m : ℝ)*(gamma0CuspTrueWidth N r : ℝ)*b.val/N)) *
      ∑ R : gamma0TrueWidthReducedMatrix N r s c, cuspGeometricPhase N m n c R.val := by
  unfold gamma0PeriodKloostermanSum
  rw [gamma0CuspReducedMatrix_sum_trueWidth]
  calc
    _ = ∑ R : gamma0TrueWidthReducedMatrix N r s c,
        (cuspGeometricPhase N m n c R.val *
          (∑ a : Fin (gamma0CuspFrequencyStep N s),
            atkinPhase ((n : ℝ)*(gamma0CuspTrueWidth N s : ℝ)*a.val/N))) *
          (∑ b : Fin (gamma0CuspFrequencyStep N r),
            atkinPhase ((m : ℝ)*(gamma0CuspTrueWidth N r : ℝ)*b.val/N)) := by
      apply Finset.sum_congr rfl
      intro R _
      simp only [Finset.sum_mul,Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact cuspGeometricPhase_trueWidth_translate N r s m n (c : ℤ)
        (by exact_mod_cast NeZero.ne c) R.val R.property.2.1 a.val b.val
    _ = _ := by
      rw [← Finset.sum_mul,← Finset.sum_mul]
      ring

theorem gamma0PeriodKloostermanSum_eq_zero_of_inadmissible (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] (m n : ℤ)
    (h : ¬ (gamma0CuspFrequencyStep N r : ℤ) ∣ m ∨
      ¬ (gamma0CuspFrequencyStep N s : ℤ) ∣ n) :
    gamma0PeriodKloostermanSum N r s c m n = 0 := by
  rw [gamma0PeriodKloostermanSum_width_characters,cuspWidth_character_sum,cuspWidth_character_sum]
  rcases h with h | h <;> simp [h]

def gamma0TrueWidthKloostermanSum (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] (m n : ℤ) : ℂ :=
  ∑ R : gamma0TrueWidthReducedMatrix N r s c,
    cuspTrueWidthGeometricPhase N r s m n c R.val

theorem gamma0PeriodKloostermanSum_trueWidth (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] (m n : ℤ) :
    gamma0PeriodKloostermanSum N r s c
      ((gamma0CuspFrequencyStep N r : ℤ)*m) ((gamma0CuspFrequencyStep N s : ℤ)*n) =
      ((gamma0CuspFrequencyStep N s : ℂ)*(gamma0CuspFrequencyStep N r : ℂ)) *
        gamma0TrueWidthKloostermanSum N r s c m n := by
  unfold gamma0PeriodKloostermanSum
  rw [gamma0CuspReducedMatrix_sum_trueWidth]
  calc
    _ = ∑ R : gamma0TrueWidthReducedMatrix N r s c,
        ∑ _a : Fin (gamma0CuspFrequencyStep N s),
          ∑ _b : Fin (gamma0CuspFrequencyStep N r),
            cuspTrueWidthGeometricPhase N r s m n c R.val := by
      apply Finset.sum_congr rfl
      intro R _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [cuspGeometricPhase_trueWidth N r s m n (c : ℤ) (by exact_mod_cast NeZero.ne c),
        cuspTrueWidthGeometricPhase_translate N r s m n (c : ℤ)
          (by exact_mod_cast NeZero.ne c) R.val R.property.2.1]
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      unfold gamma0TrueWidthKloostermanSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro R _
      ring

theorem gamma0PeriodKloostermanSum_of_admissible (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] (m n : ℤ)
    (hm : (N : ℤ) ∣ m*(gamma0CuspTrueWidth N r : ℤ))
    (hn : (N : ℤ) ∣ n*(gamma0CuspTrueWidth N s : ℤ)) :
    ∃ j k : ℤ, m = (gamma0CuspFrequencyStep N r : ℤ)*j ∧
      n = (gamma0CuspFrequencyStep N s : ℤ)*k ∧
      gamma0PeriodKloostermanSum N r s c m n =
        ((gamma0CuspFrequencyStep N s : ℂ)*(gamma0CuspFrequencyStep N r : ℂ)) *
          gamma0TrueWidthKloostermanSum N r s c j k := by
  obtain ⟨j,hj⟩ := (gamma0CuspFrequencyStep_admissible_iff N r m).mp hm
  obtain ⟨k,hk⟩ := (gamma0CuspFrequencyStep_admissible_iff N s n).mp hn
  refine ⟨j,k,hj,hk,?_⟩
  rw [hj,hk]
  exact gamma0PeriodKloostermanSum_trueWidth N r s c j k

theorem gamma0TrueWidthKloostermanSum_normalized (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] (m n : ℤ) :
    gamma0TrueWidthKloostermanSum N r s c m n =
      ∑ R : gamma0TrueWidthReducedMatrix N r s c,
        atkinPhase (((m : ℝ)*gamma0TrueWidthMatrix N r s R.val 1 1 +
          (n : ℝ)*gamma0TrueWidthMatrix N r s R.val 0 0) /
            gamma0TrueWidthModulus N r s c) := by
  unfold gamma0TrueWidthKloostermanSum
  apply Finset.sum_congr rfl
  intro R _
  rw [cuspTrueWidthGeometricPhase_normalized N r s R.val m n (c : ℤ)
    (by exact_mod_cast NeZero.ne c) R.property.2.1,
    gamma0TrueWidthMatrix_lower N r s R.val (c : ℤ) R.property.2.1]
  rfl

theorem gamma0TrueWidthKloostermanSum_trivial_bound (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] (m n : ℤ) :
    ‖gamma0TrueWidthKloostermanSum N r s c m n‖ ≤
      Fintype.card (gamma0TrueWidthReducedMatrix N r s c) := by
  unfold gamma0TrueWidthKloostermanSum
  calc
    _ ≤ ∑ R : gamma0TrueWidthReducedMatrix N r s c,
        ‖cuspTrueWidthGeometricPhase N r s m n c R.val‖ := norm_sum_le _ _
    _ = _ := by
      simp only [cuspTrueWidthGeometricPhase,atkinPhase_norm,Finset.sum_const,
        Finset.card_univ,nsmul_eq_mul,mul_one]

end ArtinMatthews
