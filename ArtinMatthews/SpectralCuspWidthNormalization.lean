module

public import ArtinMatthews.SpectralCuspWidthDilation


set_option backward.privateInPublic true
@[expose] public section

/-! The normalized cusp translation subgroup is exactly the integer lattice,
and admissible common-period frequencies become the corresponding integer mode. -/

noncomputable section
open Matrix Set
open scoped MatrixGroups

namespace ArtinMatthews

theorem atkinRealMap_injective : Function.Injective atkinRealMap := by
  intro M R h
  ext i j
  have he := congrArg (fun A : SL(2, ℝ) => A i j) h
  change (M i j : ℝ) = (R i j : ℝ) at he
  exact_mod_cast he

theorem gamma0TrueCuspScaling_period_iff (N : ℕ) [NeZero N] (r : SL(2, ℤ)) (t : ℝ) :
    (∃ γ : CongruenceSubgroup.Gamma0 N,
      atkinRealMap γ.val = gamma0TrueCuspScaling N r * realTranslation t *
        (gamma0TrueCuspScaling N r)⁻¹) ↔ ∃ k : ℤ, t = (k : ℝ) := by
  constructor
  · rintro ⟨γ,hγ⟩
    let δ : SL(2, ℤ) := r * γ.val * r⁻¹
    have hδ : atkinRealMap δ = realTranslation ((gamma0CuspTrueWidth N r : ℝ)*t) := by
      dsimp [δ]
      rw [map_mul,map_mul,map_inv,hγ,gamma0TrueCuspScaling_conjugate_translation]
      group
    have hδ01 := congrArg (fun A : SL(2, ℝ) => A 0 1) hδ
    change (δ 0 1 : ℝ) = (gamma0CuspTrueWidth N r : ℝ)*t at hδ01
    have hδT : δ = integerTranslation (δ 0 1) := by
      apply atkinRealMap_injective
      rw [atkinRealMap_integerTranslation,hδ,hδ01]
    have hγid : r⁻¹ * δ * r = γ.val := by dsimp [δ]; group
    have hm : r⁻¹ * integerTranslation (δ 0 1) * r ∈ CongruenceSubgroup.Gamma0 N := by
      rw [← hδT,hγid]
      exact γ.property
    obtain ⟨k,hk⟩ := (gamma0CuspTrueWidth_translation_iff N r (δ 0 1)).mp hm
    have hkR : (δ 0 1 : ℝ) = (gamma0CuspTrueWidth N r : ℝ)*(k : ℝ) := by exact_mod_cast hk
    refine ⟨k,?_⟩
    exact mul_left_cancel₀ (by exact_mod_cast (gamma0CuspTrueWidth_pos N r).ne')
      (hδ01.symm.trans hkR)
  · rintro ⟨k,rfl⟩
    exact gamma0TrueCuspScaling_integer_period N r k

theorem cuspFourierFrequency_trueWidth (N : ℕ) [NeZero N] (r : SL(2, ℤ)) (j : ℤ) :
    cuspFourierFrequency (N : ℝ) ((gamma0CuspFrequencyStep N r : ℤ)*j) *
      (gamma0CuspTrueWidth N r : ℝ) = cuspFourierFrequency 1 j := by
  have hp : (gamma0CuspTrueWidth N r : ℝ)*(gamma0CuspFrequencyStep N r : ℝ) = (N : ℝ) := by
    exact_mod_cast gamma0CuspFrequencyStep_mul_width N r
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  unfold cuspFourierFrequency
  push_cast
  field_simp [hN]
  linear_combination (j : ℝ)*hp

theorem cuspFourierPhase_trueWidth (N : ℕ) [NeZero N] (r : SL(2, ℤ)) (j : ℤ) (x : ℝ) :
    cuspFourierPhase (N : ℝ) ((gamma0CuspFrequencyStep N r : ℤ)*j)
      ((gamma0CuspTrueWidth N r : ℝ)*x) = cuspFourierPhase 1 j x := by
  have h := congrArg (fun t : ℝ => (t : ℂ)) (cuspFourierFrequency_trueWidth N r j)
  push_cast at h
  unfold cuspFourierPhase
  congr 1
  push_cast
  linear_combination -(Complex.I*(x : ℂ))*h

theorem cuspFourierFrequency_abs_trueWidth (N : ℕ) [NeZero N] (r : SL(2, ℤ)) (j : ℤ) :
    |cuspFourierFrequency (N : ℝ) ((gamma0CuspFrequencyStep N r : ℤ)*j)| *
      (gamma0CuspTrueWidth N r : ℝ) = |cuspFourierFrequency 1 j| := by
  have h := congrArg abs (cuspFourierFrequency_trueWidth N r j)
  have hw : 0 < (gamma0CuspTrueWidth N r : ℝ) := by exact_mod_cast gamma0CuspTrueWidth_pos N r
  rwa [abs_mul,abs_of_pos hw] at h

theorem cuspBesselKernel_trueWidth (N : ℕ) [NeZero N] (r : SL(2, ℤ))
    (ν : ℂ) (j : ℤ) (y : ℝ) :
    cuspBesselKernel ν |cuspFourierFrequency (N : ℝ) ((gamma0CuspFrequencyStep N r : ℤ)*j)|
      ((gamma0CuspTrueWidth N r : ℝ)*y) =
      (Real.sqrt (gamma0CuspTrueWidth N r : ℝ) : ℂ) *
        cuspBesselKernel ν |cuspFourierFrequency 1 j| y := by
  unfold cuspBesselKernel
  rw [← mul_assoc |cuspFourierFrequency (N : ℝ) ((gamma0CuspFrequencyStep N r : ℤ)*j)|,
    cuspFourierFrequency_abs_trueWidth,Real.sqrt_mul (by positivity),Complex.ofReal_mul]
  ring

end ArtinMatthews
