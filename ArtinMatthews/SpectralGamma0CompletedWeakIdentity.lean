module

public import ArtinMatthews.SpectralGamma0GradientSeparation


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compact-test weak identity on every vector of the completed
Γ₀ energy graph. It is inherited from literal smooth periodizations through
bounded L² test functionals, rather than imposed on the completion. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem gamma0Energy_completed_weak_identity (N : ℕ) [NeZero N]
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
    {Y : ℝ} (hY : 0 < Y) (φ : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ)
    (hheight : tsupport φ ⊆ {p : ℝ × ℝ | Y < p.2})
    (hchart : ∀ p ∈ tsupport φ,
      q.out • UpperHalfPlane.ofComplex (Complex.equivRealProdCLM.symm p) ∈ ModularGroup.fd)
    (i : Fin 2) (u : gamma0EnergySpace N) :
    (∫ z in ModularGroup.fd, (gamma0EnergyMassChart N q u) z *
      modularPlaneTest q.out (spectralWeakValueTest φ i) z) =
      -∫ z in ModularGroup.fd, (gamma0EnergyGradientChart N q i u) z *
        modularPlaneTest q.out (spectralWeakGradientTest φ) z := by
  let A := (modularL2Pairing _ (modularWeakValueTest_memLp q.out φ hφ hs i)).comp
    (gamma0EnergyMassChart N q)
  let B := (modularL2Pairing _ (modularWeakGradientTest_memLp q.out φ hφ.continuous hs)).comp
    (gamma0EnergyGradientChart N q i)
  have hclosed : IsClosed {v : gamma0EnergySpace N | A v = -B v} :=
    isClosed_eq A.continuous B.continuous.neg
  have hall : ∀ v : gamma0EnergySpace N, A v = -B v := by
    apply isClosed_property (gamma0EnergyTest_dense N) hclosed
    intro ψ
    change A (gamma0EnergyTest N ψ) = -B (gamma0EnergyTest N ψ)
    dsimp only [A,B,ContinuousLinearMap.comp_apply]
    rw [modularL2Pairing_apply,modularL2Pairing_apply]
    have hm : (∫ z in ModularGroup.fd, (gamma0EnergyMassChart N q (gamma0EnergyTest N ψ)) z *
        modularPlaneTest q.out (spectralWeakValueTest φ i) z) =
        ∫ z in ModularGroup.fd, (q.out⁻¹ • z).im^2 •
          (gamma0PoincareSeed N ψ.val (q.out⁻¹ • z) *
            fderiv ℝ φ ((q.out⁻¹ • z).re,(q.out⁻¹ • z).im) (spectralPlaneDirection i)) := by
      apply integral_congr_ae
      filter_upwards [gamma0EnergyMassChart_test_ae N q ψ] with z hz
      rw [hz]
      simp only [modularPlaneTest,spectralWeakValueTest,Complex.real_smul]
      ring
    have hg : (∫ z in ModularGroup.fd, (gamma0EnergyGradientChart N q i (gamma0EnergyTest N ψ)) z *
        modularPlaneTest q.out (spectralWeakGradientTest φ) z) =
        ∫ z in ModularGroup.fd, h2SectionGradient (gamma0PoincareSeed N ψ.val) (q.out⁻¹ • z) i *
          ((q.out⁻¹ • z).im • φ ((q.out⁻¹ • z).re,(q.out⁻¹ • z).im)) := by
      apply integral_congr_ae
      filter_upwards [gamma0EnergyGradientChart_test_ae N q i ψ] with z hz
      rw [hz]
      rfl
    rw [hm,hg]
    exact h2_section_modular_weak_pairing hY q.out (gamma0PoincareSeed N ψ.val)
      (gamma0PoincareSeed_smooth N ψ.val ψ.property) φ hφ hs hheight hchart i
  simpa only [A,B,ContinuousLinearMap.comp_apply,modularL2Pairing_apply] using hall u

/-- A completed vector with zero actual mass has zero pairing of every
actual gradient coordinate with every compact chart test. -/
theorem gamma0Energy_gradient_test_zero_of_mass_zero (N : ℕ) [NeZero N]
    (u : gamma0EnergySpace N) (hu : gamma0EnergyInclusion N u = 0)
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
    {Y : ℝ} (hY : 0 < Y) (φ : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ)
    (hheight : tsupport φ ⊆ {p : ℝ × ℝ | Y < p.2})
    (hchart : ∀ p ∈ tsupport φ,
      q.out • UpperHalfPlane.ofComplex (Complex.equivRealProdCLM.symm p) ∈ ModularGroup.fd)
    (i : Fin 2) :
    (∫ z in ModularGroup.fd, (gamma0EnergyGradientChart N q i u) z *
      modularPlaneTest q.out (spectralWeakGradientTest φ) z) = 0 := by
  have h := gamma0Energy_completed_weak_identity N q hY φ hφ hs hheight hchart i u
  have hm : gamma0EnergyMassChart N q u = 0 := by
    change (gamma0EnergyInclusion N u) q = 0
    rw [hu]
    rfl
  have hz : (∫ z in ModularGroup.fd, (gamma0EnergyMassChart N q u) z *
      modularPlaneTest q.out (spectralWeakValueTest φ i) z) = 0 := by
    rw [hm]
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict ModularGroup.fd)] with z hz
    simp only [hz,Pi.zero_apply,zero_mul]
  rw [hz] at h
  exact neg_eq_zero.mp h.symm

end ArtinMatthews
