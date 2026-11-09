module

public import ArtinMatthews.SpectralMixedPacketPrincipalCore


set_option backward.privateInPublic true
@[expose] public section

/-! The actual principal cusp packet and its mixed singleton satisfy
weighted Cauchy--Schwarz with uniform level and frequency overlap. -/

noncomputable section
open Set MeasureTheory OAI.CubicEisenstein
open scoped MatrixGroups BigOperators
namespace ArtinMatthews

theorem gamma0MixedPacket_principal_cusp_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (r s : ℕ) [NeZero r] [NeZero s], r.Coprime s →
      ∀ (h : SpectralEnergyTest) (v : Finset ι) (α : ι → ℂ) (m : ι → ℤ)
        (hm : ∀ j, m j ≠ 0), Function.Injective m →
      ∀ (n : ℤ) (hn : n ≠ 0) {B Z H Y : ℝ},
      0 < B → 1 ≤ Z → 0 ≤ H → ∀ hY : 0 < Y,
      Y < (1/16)/B →
      Y < (1/16)/(|cuspFourierFrequency 1 n|/
        (gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ)) →
      (∀ j, |cuspFourierFrequency 1 (m j)| ≤ B) →
      (∀ t : ℝ, ‖spectralContinuousTestSymbol h t‖ ≤
        H*spectralPrincipalDecayWeight Z t/Real.cosh (Real.pi*t)) →
      let N := r*s
      let F (i : Gamma0HeatPrincipalCuspidalIndex N) :=
        gamma0MixedPacketCuspidalTerm N h (gamma0CuspOneOver s) Y hY n hn v α m hm i.val
      Summable (fun i => ‖F i‖) ∧
        ‖∑' i, F i‖ ≤ C*H*gamma0MixedPacketPrincipalSize N B |cuspFourierFrequency 1 n| Z
          (∑ j ∈ v, ‖α j‖^2) := by
  classical
  obtain ⟨C₁,hC₁,hLeft⟩ := gamma0Infinity_packet_principal_density_cutoff
  obtain ⟨C₂,hC₂,hRight⟩ := gamma0MixedCusp_principal_cutoff_orbit_bessel
  refine ⟨Real.sqrt (8*C₁)*Real.sqrt (8*C₂)/4,by positivity,?_⟩
  intro ι r s ir is hcop h v α m hm hinj n hn B Z H Y hB hZ hH hY hYL hYR hfreq hSym
  have hcutL : ∀ (u : Finset (Gamma0HeatPrincipalCuspidalIndex (r*s))) (R : ℝ), 1 ≤ R →
      (∑ i ∈ u.filter (fun j => 1+|gamma0CuspPrincipalParameter (r*s) j.val| ≤ R),
        gamma0InfinityPacketPrincipalDensity (r*s) v α m hm Y hY i) ≤
        (C₁*(∑ j ∈ v, ‖α j‖^2))*(R^2+(B/((r*s : ℕ) : ℝ))*R) :=
    hLeft (r*s) v α m hm hinj hB hY hYL hfreq
  have hcutR (u : Finset (Gamma0HeatPrincipalCuspidalIndex (r*s))) (R : ℝ) (hR : 1 ≤ R) :
      (∑ i ∈ u.filter (fun j => 1+|gamma0CuspPrincipalParameter (r*s) j.val| ≤ R),
        gamma0NativePrincipalDensity (r*s) (gamma0CuspOneOver s) Y hY n hn i) ≤
        C₂*(R^2+(|cuspFourierFrequency 1 n| / ((r*s : ℕ) : ℝ))*R) := by
    refine gamma0NativePrincipalDensity_cutoff_of_moment (r*s)
      (gamma0CuspOneOver s) Y hY n hn u R _ ?_
    intro V hp hcap
    exact (hRight r s hcop V n hn hR hY hYR hp hcap).trans_eq
      (show C₂*(R^2+|cuspFourierFrequency 1 n| * R / ((r*s : ℕ) : ℝ)) =
        C₂*(R^2+(|cuspFourierFrequency 1 n| / ((r*s : ℕ) : ℝ))*R) by ring)
  have hq : 0 ≤ |cuspFourierFrequency 1 n| := abs_nonneg _
  exact gamma0MixedPacket_principal_cusp_bound_of_cutoffs (r*s)
    (gamma0CuspOneOver s) h v α m hm n hn Y hY
    (B := B) (q := |cuspFourierFrequency 1 n|)
    (C₁ := C₁) (C₂ := C₂) (Z := Z) (H := H)
    hB.le hq hC₁.le hC₂.le hZ hH hSym hcutL hcutR

end ArtinMatthews
