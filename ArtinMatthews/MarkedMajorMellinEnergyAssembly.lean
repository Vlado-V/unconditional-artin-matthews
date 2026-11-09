module

public import ArtinMatthews.MarkedMajorMellinEnergyCore
public import ArtinMatthews.MarkedMajorMellinDecay


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set
noncomputable section

theorem markedMajorFourierWeight_le_one {W : ℝ} (hW : 0 < W) (n : ℕ) (t : ℝ) :
    markedMajorFourierWeight W n t ≤ 1 :=
  inv_le_one_of_one_le₀ (one_le_pow₀ (le_add_of_nonneg_right (div_nonneg (abs_nonneg t) hW.le)))

theorem markedMajorFourierPlaneWeight_le_one {W : ℝ} (hW : 0 < W) (n : ℕ) (p : ℝ × ℝ) :
    markedMajorFourierPlaneWeight W n p ≤ 1 := by
  exact (mul_le_mul (markedMajorFourierWeight_le_one hW n p.1)
    (markedMajorFourierWeight_le_one hW n p.2)
    (markedMajorFourierWeight_nonneg hW n p.2) zero_le_one).trans_eq (one_mul 1)

/-- The entire two-endpoint integral is controlled by its small central square
means and its coarse translated weighted means. All integrals are genuine. -/
theorem markedMajor_scaled_endpoint_L1_energy
    (F : SchwartzMap (ℝ × ℝ) ℂ) {W X T C E M : ℝ}
    (hW : 0 < W) (hX : 1 ≤ X) (hT : 0 ≤ T) (hC : 0 ≤ C) (n : ℕ)
    (hF : ∀ p, ‖F p‖ ≤ C*markedMajorFourierPlaneWeight W (n+2) p)
    (Q Q' : ℝ → ℂ) (hQ : Continuous Q) (hQ' : Continuous Q')
    {B B' : ℝ} (hB : ∀ t, ‖Q t‖ ≤ B) (hB' : ∀ t, ‖Q' t‖ ≤ B')
    (he : (∫ t in Icc (-(2*X*T)) (2*X*T), ‖Q t‖^2) ≤ E)
    (he' : (∫ t in Icc (-(2*X*T)) (2*X*T), ‖Q' t‖^2) ≤ E)
    (hm : ∀ c, (∫ t, markedMajorFourierWeight (W*X) 2 (t-c)*‖Q t‖^2) ≤ M)
    (hm' : ∀ c, (∫ t, markedMajorFourierWeight (W*X) 2 (t-c)*‖Q' t‖^2) ≤ M) :
    (∫ p : ℝ × ℝ, ‖F (p.1/X,p.2)*(Q p.1*Q' (p.2-p.1))‖) ≤
      C*(2*T)*E + C*((1+T/W)^n)⁻¹*M*(W*markedMajorFourierWeightMass) := by
  have hXp : 0 < X := by linarith
  let f := fun p : ℝ × ℝ => F (p.1/X,p.2)*(Q p.1*Q' (p.2-p.1))
  let S : Set (ℝ × ℝ) := Icc (-(X*T)) (X*T) ×ˢ Icc (-T) T
  have hS : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  have hi : Integrable f := markedMajor_scaled_endpoint_integrable F hXp Q Q' hQ hQ' hB hB'
  have hprod : IntegrableOn (fun p : ℝ × ℝ => ‖Q p.1‖*‖Q' (p.2-p.1)‖) S :=
    ((hQ.comp continuous_fst).norm.mul (hQ'.comp (continuous_snd.sub continuous_fst)).norm).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hcore : (∫ p in S, ‖f p‖) ≤ C*(2*T)*E := by
    have hb : ∀ p, ‖F p‖ ≤ C := fun p => (hF p).trans
      ((mul_le_mul_of_nonneg_left (markedMajorFourierPlaneWeight_le_one hW (n+2) p) hC).trans_eq (mul_one C))
    calc
      _ ≤ ∫ p in S, C*(‖Q p.1‖*‖Q' (p.2-p.1)‖) :=
        setIntegral_mono_on hi.norm.integrableOn (hprod.const_mul C) hS (fun p _ => by
          dsimp [f]
          rw [norm_mul,norm_mul]
          exact mul_le_mul_of_nonneg_right (hb _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      _ = C*(∫ p in S, ‖Q p.1‖*‖Q' (p.2-p.1)‖) := integral_const_mul _ _
      _ ≤ C*(2*T*E) := mul_le_mul_of_nonneg_left
        (markedMajor_endpoint_core_energy Q Q' hQ hQ' hX hT he he') hC
      _ = _ := by ring
  have hsub : Sᶜ ⊆ {p : ℝ × ℝ | T ≤ |p.1/X| ∨ T ≤ |p.2|} := by
    intro p hp
    by_cases ht : T ≤ |p.1/X|
    · exact Or.inl ht
    right
    by_contra hs
    apply hp
    have h₁ : |p.1| ≤ X*T := by
      have ht' := (lt_of_not_ge ht).le
      rw [abs_div,abs_of_pos hXp] at ht'
      have := (div_le_iff₀ hXp).mp ht'
      nlinarith
    exact ⟨abs_le.mp h₁,abs_le.mp (lt_of_not_ge hs).le⟩
  have htail : (∫ p in Sᶜ, ‖f p‖) ≤
      C*((1+T/W)^n)⁻¹*M*(W*markedMajorFourierWeightMass) := by
    apply le_trans (setIntegral_mono_set hi.norm.integrableOn
      (Filter.Eventually.of_forall (fun p => norm_nonneg (f p)))
      (Filter.Eventually.of_forall (fun p hp => hsub hp)))
    exact markedMajor_scaled_endpoint_tail F hW hXp hT hC n hF Q Q' hQ hQ' hB hB' hm hm'
  calc
    _ = (∫ p in S, ‖f p‖)+(∫ p in Sᶜ, ‖f p‖) := (integral_add_compl hS hi.norm).symm
    _ ≤ _ := add_le_add hcore htail

theorem markedMajor_scaled_endpoint_energy
    (F : SchwartzMap (ℝ × ℝ) ℂ) {W X T C E M : ℝ}
    (hW : 0 < W) (hX : 1 ≤ X) (hT : 0 ≤ T) (hC : 0 ≤ C) (n : ℕ)
    (hF : ∀ p, ‖F p‖ ≤ C*markedMajorFourierPlaneWeight W (n+2) p)
    (Q Q' : ℝ → ℂ) (hQ : Continuous Q) (hQ' : Continuous Q')
    {B B' : ℝ} (hB : ∀ t, ‖Q t‖ ≤ B) (hB' : ∀ t, ‖Q' t‖ ≤ B')
    (he : (∫ t in Icc (-(2*X*T)) (2*X*T), ‖Q t‖^2) ≤ E)
    (he' : (∫ t in Icc (-(2*X*T)) (2*X*T), ‖Q' t‖^2) ≤ E)
    (hm : ∀ c, (∫ t, markedMajorFourierWeight (W*X) 2 (t-c)*‖Q t‖^2) ≤ M)
    (hm' : ∀ c, (∫ t, markedMajorFourierWeight (W*X) 2 (t-c)*‖Q' t‖^2) ≤ M) :
    ‖∫ p : ℝ × ℝ, F (p.1/X,p.2)*(Q p.1*Q' (p.2-p.1))‖ ≤
      C*(2*T)*E + C*((1+T/W)^n)⁻¹*M*(W*markedMajorFourierWeightMass) := by
  exact (norm_integral_le_integral_norm _).trans
    (markedMajor_scaled_endpoint_L1_energy F hW hX hT hC n hF Q Q' hQ hQ' hB hB' he he' hm hm')

/-- Uniform actual major kernel energy. The coefficient and its rapid decay
are constructed from the supplied compactly supported smoothing function. -/
theorem markedMajor_constructed_endpoint_energy (ψ : SchwartzMap ℝ ℂ)
    {a b R : ℝ} (ha : 0 < a) (hab : a < b) (hψ : tsupport ψ ⊆ Icc (-R) R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X ≥ 1, ∀ hX : 0 < X, ∀ theta T E M : ℝ, 0 ≤ T →
      ∀ Q Q' : ℝ → ℂ, Continuous Q → Continuous Q' →
      (∃ B, ∀ t, ‖Q t‖ ≤ B) → (∃ B', ∀ t, ‖Q' t‖ ≤ B') →
      (∫ t in Icc (-(2*X*T)) (2*X*T), ‖Q t‖^2) ≤ E →
      (∫ t in Icc (-(2*X*T)) (2*X*T), ‖Q' t‖^2) ≤ E →
      (∀ c, (∫ t, markedMajorFourierWeight ((1+|theta|)*X) 2 (t-c)*‖Q t‖^2) ≤ M) →
      (∀ c, (∫ t, markedMajorFourierWeight ((1+|theta|)*X) 2 (t-c)*‖Q' t‖^2) ≤ M) →
      ‖∫ p : ℝ × ℝ, markedMajorConstructedCoefficient ψ ha hab hψ hX theta (p.1/X,p.2)*
        (Q p.1*Q' (p.2-p.1))‖ ≤
        C*(2*T)*E + C*((1+T/(1+|theta|))^n)⁻¹*M*((1+|theta|)*markedMajorFourierWeightMass) := by
  obtain ⟨C,hC,hF⟩ := markedMajorConstructedCoefficient_scaled_decay ψ ha hab hψ (n+2)
  refine ⟨C,hC,?_⟩
  intro X hX hXp theta T E M hT Q Q' hQ hQ' hB hB' he he' hm hm'
  obtain ⟨B,hB⟩ := hB
  obtain ⟨B',hB'⟩ := hB'
  exact markedMajor_scaled_endpoint_energy (markedMajorConstructedCoefficient ψ ha hab hψ hXp theta)
    (by positivity) hX hT hC.le n (hF X hX hXp theta) Q Q' hQ hQ' hB hB' he he' hm hm'

theorem markedMajor_constructed_endpoint_L1_energy (ψ : SchwartzMap ℝ ℂ)
    {a b R : ℝ} (ha : 0 < a) (hab : a < b) (hψ : tsupport ψ ⊆ Icc (-R) R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X ≥ 1, ∀ hX : 0 < X, ∀ theta T E M : ℝ, 0 ≤ T →
      ∀ Q Q' : ℝ → ℂ, Continuous Q → Continuous Q' →
      (∃ B, ∀ t, ‖Q t‖ ≤ B) → (∃ B', ∀ t, ‖Q' t‖ ≤ B') →
      (∫ t in Icc (-(2*X*T)) (2*X*T), ‖Q t‖^2) ≤ E →
      (∫ t in Icc (-(2*X*T)) (2*X*T), ‖Q' t‖^2) ≤ E →
      (∀ c, (∫ t, markedMajorFourierWeight ((1+|theta|)*X) 2 (t-c)*‖Q t‖^2) ≤ M) →
      (∀ c, (∫ t, markedMajorFourierWeight ((1+|theta|)*X) 2 (t-c)*‖Q' t‖^2) ≤ M) →
      (∫ p : ℝ × ℝ, ‖markedMajorConstructedCoefficient ψ ha hab hψ hX theta (p.1/X,p.2)*
        (Q p.1*Q' (p.2-p.1))‖) ≤
        C*(2*T)*E + C*((1+T/(1+|theta|))^n)⁻¹*M*((1+|theta|)*markedMajorFourierWeightMass) := by
  obtain ⟨C,hC,hF⟩ := markedMajorConstructedCoefficient_scaled_decay ψ ha hab hψ (n+2)
  refine ⟨C,hC,?_⟩
  intro X hX hXp theta T E M hT Q Q' hQ hQ' hB hB' he he' hm hm'
  obtain ⟨B,hB⟩ := hB
  obtain ⟨B',hB'⟩ := hB'
  exact markedMajor_scaled_endpoint_L1_energy (markedMajorConstructedCoefficient ψ ha hab hψ hXp theta)
    (by positivity) hX hT hC.le n (hF X hX hXp theta) Q Q' hQ hQ' hB hB' he he' hm hm'

end
end ArtinMatthews
