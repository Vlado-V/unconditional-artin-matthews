module

public import ArtinMatthews.MarkedMajorMellinCutoff
public import ArtinMatthews.MarkedMajorMellinUniform


set_option backward.privateInPublic true
@[expose] public section

/-! The literal source Mellin coefficient using constructed positive-support cutoffs. -/
namespace ArtinMatthews
open Set MeasureTheory Complex
noncomputable section

def markedMajorConstructedKernel (ψ : SchwartzMap ℝ ℂ) {a b R X : ℝ}
    (ha : 0 < a) (hab : a < b) (hψ : tsupport ψ ⊆ Icc (-R) R)
    (hX : 0 < X) (theta : ℝ) : SchwartzMap (ℝ × ℝ) ℂ :=
  markedMajorMellinKernel (majorMellinPositiveCutoff a b ha hab)
    (majorMellinPositiveCutoff a b ha hab) ψ (half_pos ha) hX
    (majorMellinPositiveCutoff_tsupport a b ha hab)
    (majorMellinPositiveCutoff_tsupport a b ha hab) hψ theta

def markedMajorConstructedCoefficient (ψ : SchwartzMap ℝ ℂ) {a b R X : ℝ}
    (ha : 0 < a) (hab : a < b) (hψ : tsupport ψ ⊆ Icc (-R) R)
    (hX : 0 < X) (theta : ℝ) : SchwartzMap (ℝ × ℝ) ℂ :=
  markedMajorFourierCoefficient (markedMajorConstructedKernel ψ ha hab hψ hX theta)

theorem markedMajor_constructed_mellin_separation (ψ : SchwartzMap ℝ ℂ)
    {a b R X w w' : ℝ} (ha : 0 < a) (hab : a < b)
    (hψ : tsupport ψ ⊆ Icc (-R) R) (hX : 0 < X) (theta : ℝ)
    (hw : w ∈ Icc a b) (hw' : w' ∈ Icc a b) :
    ψ (X*(w-w'))*OAI.Problem337.RealPhase.phase (theta*(X*(w-w'))) =
      (X : ℂ)⁻¹ * ∫ t : ℝ, ∫ s : ℝ,
        markedMajorConstructedCoefficient ψ ha hab hψ hX theta (t/X,s) *
          (Complex.exp (I*(t : ℂ)*(Real.log w : ℂ)) *
            Complex.exp (I*((s-t : ℝ) : ℂ)*(Real.log w' : ℂ))) :=
  markedMajor_actual_mellin_separation _ _ ψ (half_pos ha) hX
    (majorMellinPositiveCutoff_tsupport a b ha hab)
    (majorMellinPositiveCutoff_tsupport a b ha hab) hψ theta (ha.trans_le hw.1) (ha.trans_le hw'.1)
    (majorMellinPositiveCutoff_plateau a b ha hab hw)
    (majorMellinPositiveCutoff_plateau a b ha hab hw')

theorem markedMajor_constructed_mellin_integrable (ψ : SchwartzMap ℝ ℂ)
    {a b R X w w' : ℝ} (ha : 0 < a) (hab : a < b)
    (hψ : tsupport ψ ⊆ Icc (-R) R) (hX : 0 < X) (theta : ℝ)
    (hw : w ∈ Icc a b) (hw' : w' ∈ Icc a b) :
    Integrable (fun p : ℝ × ℝ =>
      markedMajorConstructedCoefficient ψ ha hab hψ hX theta (p.1/X,p.2) *
        (Complex.exp (I*(p.1 : ℂ)*(Real.log w : ℂ)) *
          Complex.exp (I*((p.2-p.1 : ℝ) : ℂ)*(Real.log w' : ℂ)))) :=
  markedMajor_actual_mellin_integrable _ _ ψ (half_pos ha) hX
    (majorMellinPositiveCutoff_tsupport a b ha hab)
    (majorMellinPositiveCutoff_tsupport a b ha hab) hψ theta (ha.trans_le hw.1) (ha.trans_le hw'.1)

theorem markedMajorConstructedKernel_uniform_L1_bounds (ψ : SchwartzMap ℝ ℂ)
    {a b R : ℝ} (ha : 0 < a) (hab : a < b)
    (hψ : tsupport ψ ⊆ Icc (-R) R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k ≤ n, ∀ X ≥ 1, ∀ hX : 0 < X, ∀ theta : ℝ,
      (∫ p : ℝ × ℝ, ‖iteratedFDeriv ℝ k
        (markedMajorConstructedKernel ψ ha hab hψ hX theta) p‖) ≤ C*(1+|theta|)^k := by
  obtain ⟨C,hC,hb⟩ := markedMajorMellinKernel_uniform_L1_bounds
    (majorMellinPositiveCutoff a b ha hab) (majorMellinPositiveCutoff a b ha hab) ψ (half_pos ha)
    (majorMellinPositiveCutoff_tsupport a b ha hab)
    (majorMellinPositiveCutoff_tsupport a b ha hab) hψ n
  exact ⟨C,hC,fun k hk X hX _ theta => hb k hk X hX theta⟩

end
end ArtinMatthews
