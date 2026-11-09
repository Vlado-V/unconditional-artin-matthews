module

public import ArtinMatthews.MarkedMajorArcEnergyCover


set_option backward.privateInPublic true
@[expose] public section

/-! Exceptional intervals in a measurable high-time part of the window. -/

namespace ArtinMatthews

open Finset MeasureTheory Set

theorem sourceComparison_isolated_energy_subset (P M N : ℝ → ℂ) (I : Finset ℤ)
    (T ε p m E B : ℝ) (D : Set ℝ) (hD : MeasurableSet D)
    (hDT : D ⊆ Set.Icc (-T) T) (hP : Continuous P) (hM : Continuous M) (hN : Continuous N)
    (hPb : ∀ t ∈ D, ‖P t‖ ≤ p)
    (hMb : ∀ t ∈ D, ‖M t‖ ≤ m)
    (hcover : ∀ t ∈ D, ε < ‖P t‖ →
      ∃ z ∈ I, t ∈ Set.Icc (z:ℝ) ((z:ℝ)+1))
    (hmean : (∫ t in D, ‖M t*N t‖^2) ≤ E)
    (hsparse : (∑ z ∈ I, sSup ((fun t => ‖N t‖^2) ''
      Set.Icc (z:ℝ) ((z:ℝ)+1))) ≤ B) :
    (∫ t in D, ‖P t*M t*N t‖^2) ≤ ε^2*E+p^2*m^2*B := by
  have hmaj := markedUnitEnergyMajorant_integrable I hN
  have hpoint (t : ℝ) (ht : t ∈ D) :
      ‖P t*M t*N t‖^2 ≤ ε^2*‖M t*N t‖^2+p^2*m^2*markedUnitEnergyMajorant I N t := by
    have hmaj0 := markedUnitEnergyMajorant_nonneg I N t
    by_cases hsmall : ‖P t‖ ≤ ε
    · have hb : ‖P t*M t*N t‖^2 ≤ ε^2*‖M t*N t‖^2 := by
        rw [mul_assoc,norm_mul,mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hsmall 2) (sq_nonneg _)
      exact hb.trans (le_add_of_nonneg_right (by positivity))
    · have hb : ‖P t*M t*N t‖^2 ≤ p^2*m^2*markedUnitEnergyMajorant I N t := by
        simp only [norm_mul,mul_pow]
        apply mul_le_mul
        · exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hPb t ht) 2)
            (pow_le_pow_left₀ (norm_nonneg _) (hMb t ht) 2) (sq_nonneg _) (sq_nonneg _)
        · exact markedUnitEnergyMajorant_dominates I N t (hcover t ht (lt_of_not_ge hsmall))
        · positivity
        · positivity
      exact hb.trans (le_add_of_nonneg_left (by positivity))
  have hf : IntegrableOn (fun t => ‖P t*M t*N t‖^2) D :=
    (((hP.mul hM).mul hN).norm.pow 2).integrableOn_Icc.mono_set hDT
  have hg1 : IntegrableOn (fun t => ε^2*‖M t*N t‖^2) D :=
    (((hM.mul hN).norm.pow 2).integrableOn_Icc.mono_set hDT).const_mul (ε^2)
  have hg2 : IntegrableOn (fun t => p^2*m^2*markedUnitEnergyMajorant I N t) D :=
    hmaj.integrableOn.const_mul (p^2*m^2)
  have hg := hg1.add hg2
  calc
    _ ≤ ∫ t in D,
        ε^2*‖M t*N t‖^2+p^2*m^2*markedUnitEnergyMajorant I N t :=
      setIntegral_mono_on hf hg hD hpoint
    _ = ε^2*(∫ t in D, ‖M t*N t‖^2)+
        p^2*m^2*(∫ t in D, markedUnitEnergyMajorant I N t) := by
      rw [integral_add hg1 hg2,integral_const_mul,integral_const_mul]
    _ ≤ ε^2*E+p^2*m^2*B := add_le_add
      (mul_le_mul_of_nonneg_left hmean (sq_nonneg _))
      (mul_le_mul_of_nonneg_left
        ((setIntegral_le_integral hmaj (Filter.Eventually.of_forall
          (markedUnitEnergyMajorant_nonneg I N))).trans
          ((markedUnitEnergyMajorant_integral_le I hN).trans hsparse)) (by positivity))

end ArtinMatthews
