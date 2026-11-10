module

public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
public import ArtinMatthews.SpectralBesselKWhittaker
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine arbitrary-order K transform of a compact vertical test.
Its integrability follows from the actual Schlaefli K derivative theorem. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

def cuspBesselKernel (ν : ℂ) (q y : ℝ) : ℂ :=
  (Real.sqrt y : ℂ) * OAI.CubicEisenstein.schlafliBesselK ν (q * y)

theorem cuspBesselKernel_continuousAt (ν : ℂ) {q y : ℝ} (hq : 0 < q) (hy : 0 < y) :
    ContinuousAt (cuspBesselKernel ν q) y := by
  have hk := (spectralScaledBesselK_hasDerivAt ν q y hq hy).continuousAt
  exact (Complex.continuous_ofReal.continuousAt.comp Real.continuous_sqrt.continuousAt).mul hk

def cuspBesselTransformIntegrand (ν : ℂ) (q : ℝ) (ρ : ℝ → ℝ) (y : ℝ) : ℂ :=
  (ρ y / y ^ 2 : ℝ) * cuspBesselKernel ν q y

theorem cuspBesselTransformIntegrand_continuous (ν : ℂ) {q Y : ℝ}
    (hq : 0 < q) (hY : 0 < Y) (ρ : ℝ → ℝ) (hρ : Continuous ρ)
    (hs : tsupport ρ ⊆ Ioi Y) : Continuous (cuspBesselTransformIntegrand ν q ρ) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ tsupport ρ
  · have hy0 : 0 < y := hY.trans (hs hy)
    exact (Complex.continuous_ofReal.continuousAt.comp
      (hρ.continuousAt.div (continuousAt_id.pow 2) (pow_ne_zero 2 hy0.ne'))).mul
        (cuspBesselKernel_continuousAt ν hq hy0)
  · have hz : cuspBesselTransformIntegrand ν q ρ =ᶠ[𝓝 y] 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with t ht
      simp only [cuspBesselTransformIntegrand, Pi.zero_apply] at ht ⊢
      rw [ht, zero_div, Complex.ofReal_zero, zero_mul]
    exact continuousAt_const.congr hz.symm

theorem cuspBesselTransformIntegrand_compact (ν : ℂ) (q : ℝ) (ρ : ℝ → ℝ)
    (hcρ : HasCompactSupport ρ) : HasCompactSupport (cuspBesselTransformIntegrand ν q ρ) := by
  apply hcρ.mono'
  intro y hy
  by_contra hρ
  exact hy (by simp [cuspBesselTransformIntegrand, image_eq_zero_of_notMem_tsupport hρ])

theorem cuspBesselTransformIntegrand_integrable (ν : ℂ) {q Y : ℝ}
    (hq : 0 < q) (hY : 0 < Y) (ρ : ℝ → ℝ) (hρ : Continuous ρ)
    (hcρ : HasCompactSupport ρ) (hs : tsupport ρ ⊆ Ioi Y) :
    Integrable (cuspBesselTransformIntegrand ν q ρ) :=
  (cuspBesselTransformIntegrand_continuous ν hq hY ρ hρ hs).integrable_of_hasCompactSupport
    (cuspBesselTransformIntegrand_compact ν q ρ hcρ)

def cuspBesselTransform (ν : ℂ) (q Y : ℝ) (ρ : ℝ → ℝ) : ℂ :=
  ∫ y in Ioi Y, cuspBesselTransformIntegrand ν q ρ y

theorem cuspBesselTransform_smul (ν : ℂ) (q Y c : ℝ) (ρ : ℝ → ℝ) :
    cuspBesselTransform ν q Y (fun y => c * ρ y) = c • cuspBesselTransform ν q Y ρ := by
  unfold cuspBesselTransform
  rw [← integral_smul]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    simp only [cuspBesselTransformIntegrand, Complex.real_smul, Complex.ofReal_div,
      Complex.ofReal_mul]
    ring

end ArtinMatthews
