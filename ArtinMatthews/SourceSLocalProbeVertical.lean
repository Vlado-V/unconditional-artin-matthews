module

public import ArtinMatthews.SourceSLocalVerticalArch
public import ArtinMatthews.SourceSLocalProbeMellin
public import ArtinMatthews.SourceLocalAnnularMellinBounds


set_option backward.privateInPublic true
@[expose] public section

/-! The actual probe has arbitrary positive strip decay and positive vertical (L^1). -/

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField Classical SchwartzMap
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (v : InfinitePlace K)

local notation "μa" => sourceSLocalArchUnitMeasure K hζ
local notation "μf" => sourceSLocalFiniteUnitMeasure K S
local notation "ga" => sourceProbeArchFactor K hζ
local notation "gf" => sourceProbeFiniteFactor K S

theorem sourceSLocalProbeMellin_eq_retained_product (s : ℂ) :
    sourceSLocalProbeMellin K hζ S v s =
      sourceSLocalMellinProduct S v μa μf ga gf sourceProbeArchFourier s := by
  rw [sourceSLocalProbeMellin, sourceSLocalWholeMellin_eq_product]
  rfl

private theorem probeFiniteMellin_strip_bound (lo hi : ℝ) (hlo : 0 < lo) (p : S) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ s : ℂ, lo ≤ s.re → s.re ≤ hi → ‖sourceSheetFiniteMellin S μf gf p s‖ ≤ B := by
  refine ⟨max 0 (sourceLocalAnnularMellinBandBound K p.val lo hi), le_max_left _ _, ?_⟩
  intro s hl hh
  rw [sourceSheetFiniteMellin, sourceProbeFiniteFactor_mellin_eq]
  exact (sourceLocalAnnularMellin_norm_le_band K p.val lo hi hlo s hl hh).trans (le_max_right _ _)

private theorem probeFiniteMellin_continuous_line (σ : ℝ) (hσ : 0 < σ) (p : S) :
    Continuous (fun t : ℝ => sourceSheetFiniteMellin S μf gf p ((σ : ℂ) + t * Complex.I)) := by
  simp only [sourceSheetFiniteMellin, sourceProbeFiniteFactor_mellin_eq]
  refine continuous_iff_continuousAt.mpr fun t => ?_
  let z := (σ : ℂ) + t * Complex.I
  have hz : 0 < z.re := by simpa [z, Complex.mul_re] using hσ
  have hM := (sourceLocalAnnularMellin_differentiableOn K p.val).continuousOn z hz
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have ht : Continuous (fun u : ℝ => (σ : ℂ) + u * Complex.I) := by fun_prop
  exact ContinuousAt.comp' (f := fun u : ℝ => (σ : ℂ) + u * Complex.I)
    (g := sourceLocalAnnularMellin K p.val) (x := t)
    (hM.continuousAt (hU.mem_nhds hz)) ht.continuousAt

/-- The exact whole S-local Mellin transform decays rapidly on any positive strip. -/
theorem sourceSLocalProbeMellin_vertical_rapid (n : ℕ) (lo hi : ℝ) (hlo : 0 < lo) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, lo ≤ s.re → s.re ≤ hi →
      (1 + |s.im|) ^ n * ‖sourceSLocalProbeMellin K hζ S v s‖ ≤ C := by
  have : IsTotallyComplex K := source_isTotallyComplex K hζ
  simp only [sourceSLocalProbeMellin_eq_retained_product]
  exact sourceSLocalMellinProduct_vertical_rapid_of_archMellin S v μa μf ga gf
    (fun _ => sourceProbeArchFourier) (fun w s _ => sourceProbeArchFactor_mellin_eq K hζ w.val s)
    n sourceProbeArchFourier lo hi hlo (probeFiniteMellin_strip_bound K S lo hi hlo)

/-- The exact whole S-local Mellin transform belongs to L1 on every positive vertical line. -/
theorem sourceSLocalProbeMellin_verticalIntegrable (σ : ℝ) (hσ : 0 < σ) :
    Complex.VerticalIntegrable (sourceSLocalProbeMellin K hζ S v) σ := by
  have : IsTotallyComplex K := source_isTotallyComplex K hζ
  rw [funext (sourceSLocalProbeMellin_eq_retained_product K hζ S v)]
  apply sourceSLocalMellinProduct_verticalIntegrable_of_archMellin S v μa μf ga gf
    (fun _ => sourceProbeArchFourier) (fun w s _ => sourceProbeArchFactor_mellin_eq K hζ w.val s)
    sourceProbeArchFourier σ hσ _ (probeFiniteMellin_continuous_line K S σ hσ)
  intro p
  obtain ⟨B, hB, h⟩ := probeFiniteMellin_strip_bound K S σ σ hσ p
  refine ⟨B, hB, fun t => ?_⟩
  have hr : ((σ : ℂ) + t * Complex.I).re = σ := by simp [Complex.mul_re]
  exact h _ hr.ge hr.le

end
end ArtinMatthews.SourcePhysical
