module

public import ArtinMatthews.SpectralKLPhysicalCompactData


set_option backward.privateInPublic true
@[expose] public section

/-! The physical test for the actual cusp-height Bessel integral.
It is rho(y)*sqrt(y)/y, followed by the literal frequency dilation x/q. -/

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace ArtinMatthews

def spectralKLHeightBaseTest (ρ : ℝ → ℝ) (y : ℝ) : ℂ :=
  ((ρ y*Real.sqrt y : ℝ) : ℂ)/(y : ℂ)

def spectralKLHeightPhysicalTest (q : ℝ) (ρ : ℝ → ℝ) (x : ℝ) : ℂ :=
  spectralKLHeightBaseTest ρ (x/q)

theorem spectralKLHeightBaseTest_tsupport (ρ : ℝ → ℝ) :
    tsupport (spectralKLHeightBaseTest ρ) ⊆ tsupport ρ := by
  unfold tsupport
  apply closure_mono
  intro y hy
  have hy' : spectralKLHeightBaseTest ρ y ≠ 0 := hy
  exact fun hρ0 => hy' (by simp [spectralKLHeightBaseTest,hρ0])

theorem spectralKLHeightBaseTest_properties (ρ : ℝ → ℝ) (hρ : Continuous ρ)
    (hcρ : HasCompactSupport ρ) (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) :
    Continuous (spectralKLHeightBaseTest ρ) ∧ HasCompactSupport (spectralKLHeightBaseTest ρ) ∧
      tsupport (spectralKLHeightBaseTest ρ) ⊆ Ioi (0 : ℝ) := by
  have hnum : Continuous (fun y : ℝ => ((ρ y*Real.sqrt y : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hρ.mul Real.continuous_sqrt)
  have hs : tsupport (fun y : ℝ => ((ρ y*Real.sqrt y : ℝ) : ℂ)) ⊆ tsupport ρ := by
    unfold tsupport
    apply closure_mono
    intro y hy
    have hy' : ((ρ y*Real.sqrt y : ℝ) : ℂ) ≠ 0 := hy
    exact fun hρ0 => hy' (by simp [hρ0])
  have hcont := spectralKLPhysicalCompactDiv_continuous _ hnum (hs.trans hpρ)
  exact ⟨hcont,hcρ.of_isClosed_subset (isClosed_tsupport _) (spectralKLHeightBaseTest_tsupport ρ),
    (spectralKLHeightBaseTest_tsupport ρ).trans hpρ⟩

theorem spectralKLHeightPhysicalTest_properties {q : ℝ} (hq : 0 < q) (ρ : ℝ → ℝ)
    (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) :
    Continuous (spectralKLHeightPhysicalTest q ρ) ∧ HasCompactSupport (spectralKLHeightPhysicalTest q ρ) ∧
      tsupport (spectralKLHeightPhysicalTest q ρ) ⊆ Ioi (0 : ℝ) := by
  obtain ⟨hb,hbc,hbp⟩ := spectralKLHeightBaseTest_properties ρ hρ hcρ hpρ
  have hcont : Continuous (spectralKLHeightPhysicalTest q ρ) := hb.comp (by fun_prop)
  have hK : IsCompact ((fun y : ℝ => q*y) '' tsupport (spectralKLHeightBaseTest ρ)) :=
    hbc.image (by fun_prop)
  have hs : tsupport (spectralKLHeightPhysicalTest q ρ) ⊆
      (fun y : ℝ => q*y) '' tsupport (spectralKLHeightBaseTest ρ) := by
    unfold tsupport
    apply closure_minimal _ hK.isClosed
    intro x hx
    have hx' : spectralKLHeightBaseTest ρ (x/q) ≠ 0 := hx
    refine ⟨x/q,subset_tsupport _ hx',?_⟩
    exact mul_div_cancel₀ x hq.ne'
  have hpos : tsupport (spectralKLHeightPhysicalTest q ρ) ⊆ Ioi (0 : ℝ) := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := hs hx
    exact mul_pos hq (hbp hy)
  exact ⟨hcont,hK.of_isClosed_subset (isClosed_tsupport _) hs,hpos⟩

theorem spectralKLHeightBaseTest_energy (ρ : ℝ → ℝ) {y : ℝ} (hy : 0 < y) :
    ‖spectralKLHeightBaseTest ρ y‖^2/y = (ρ y)^2/y^2 := by
  unfold spectralKLHeightBaseTest
  rw [norm_div,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    div_pow,sq_abs,sq_abs,mul_pow,Real.sq_sqrt hy.le]
  field_simp

end ArtinMatthews
