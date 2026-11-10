module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import ArtinMatthews.SpectralBoundedMomentTesting
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.SpecialFunctions.Bernstein


set_option backward.privateInPublic true
@[expose] public section

/-! The positive spectral ray is separated by moments of its actual
Green coordinate. The proof pulls compact tests back through a clamped
inverse coordinate and uses the fundamental lemma for integrable functions. -/
noncomputable section
open Set Filter MeasureTheory
namespace ArtinMatthews

def spectralPositiveGreenCoordinate (t : ℝ) : ℝ := (5/4+t^2)⁻¹

theorem spectralPositiveGreenCoordinate_pos (t : ℝ) : 0<spectralPositiveGreenCoordinate t :=
  inv_pos.mpr (by positivity)

theorem spectralPositiveGreenCoordinate_mem (t : ℝ) : spectralPositiveGreenCoordinate t∈Icc (0:ℝ) 1 := by
  refine ⟨(spectralPositiveGreenCoordinate_pos t).le,?_⟩
  change (5/4+t^2)⁻¹≤1
  apply (inv_le_one₀ (by positivity : (0:ℝ)<5/4+t^2)).mpr
  nlinarith [sq_nonneg t]

theorem spectralPositiveGreenCoordinate_antitone {a b : ℝ} (ha : 0≤a) (hab : a≤b) :
    spectralPositiveGreenCoordinate b≤spectralPositiveGreenCoordinate a := by
  change (5/4+b^2)⁻¹≤(5/4+a^2)⁻¹
  apply (inv_le_inv₀ (by positivity : (0:ℝ)<5/4+b^2) (by positivity : (0:ℝ)<5/4+a^2)).mpr
  nlinarith

theorem spectralPositiveGreenCoordinate_inverse {t : ℝ} (ht : 0≤t) :
    Real.sqrt ((spectralPositiveGreenCoordinate t)⁻¹-5/4)=t := by
  rw [spectralPositiveGreenCoordinate,inv_inv]
  rw [show (5/4:ℝ)+t^2-5/4=t^2 by ring,Real.sqrt_sq ht]

theorem spectralPositiveGreen_compact_test (κ : ℝ → ℝ) (hκ : Continuous κ) (hc : HasCompactSupport κ) :
    ∃ F : ℝ → ℝ,Continuous F ∧ ∀ t : ℝ,0≤t → F (spectralPositiveGreenCoordinate t)=κ t := by
  obtain ⟨b,hb⟩ := hc.isCompact.bddAbove
  let B := max 1 b+1
  have hB : 0<B := by dsimp [B];linarith [le_max_left (1:ℝ) b]
  have hBb : b<B := by dsimp [B];linarith [le_max_right (1:ℝ) b]
  have hzero (t : ℝ) (ht : B≤t) : κ t=0 := by
    by_contra h
    have hm : t∈tsupport κ := subset_closure h
    have htb : t≤b := hb hm
    linarith
  let e := spectralPositiveGreenCoordinate B
  have he : 0<e := spectralPositiveGreenCoordinate_pos B
  let F (x : ℝ) := κ (Real.sqrt ((max x e)⁻¹-5/4))
  refine ⟨F,?_,?_⟩
  · apply hκ.comp
    apply Real.continuous_sqrt.comp
    exact ((continuous_id.max continuous_const).inv₀ (fun x =>
      ne_of_gt (he.trans_le (le_max_right x e)))).sub continuous_const
  · intro t ht
    by_cases htb : t≤B
    · have hw : e≤spectralPositiveGreenCoordinate t := spectralPositiveGreenCoordinate_antitone ht htb
      change κ (Real.sqrt ((max (spectralPositiveGreenCoordinate t) e)⁻¹-5/4))=κ t
      rw [max_eq_left hw,spectralPositiveGreenCoordinate_inverse ht]
    · have hw : spectralPositiveGreenCoordinate t≤e :=
        spectralPositiveGreenCoordinate_antitone hB.le (le_of_not_ge htb)
      change κ (Real.sqrt ((max (spectralPositiveGreenCoordinate t) e)⁻¹-5/4))=κ t
      rw [max_eq_right hw]
      change κ (Real.sqrt ((spectralPositiveGreenCoordinate B)⁻¹-5/4))=κ t
      rw [spectralPositiveGreenCoordinate_inverse hB.le,hzero B le_rfl,hzero t (le_of_not_ge htb)]

theorem spectralPositiveGreen_moment_unique {μ : Measure ℝ} {f : ℝ → ℂ}
    (hf : Integrable f μ) (hpos : ∀ᵐ t ∂μ,0≤t)
    (hm : ∀ n : ℕ,(∫ t,(spectralPositiveGreenCoordinate t)^n • f t ∂μ)=0) :
    f=ᵐ[μ] 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable
  intro κ hκ hc
  obtain ⟨F,hF,he⟩ := spectralPositiveGreen_compact_test κ hκ.continuous hc
  have hmeas : Measurable spectralPositiveGreenCoordinate :=
    ((measurable_const.add (measurable_id.pow_const 2)).inv)
  have h := spectralUnitWeight_continuous_moment_zero hf hmeas.aemeasurable
    (ae_of_all _ spectralPositiveGreenCoordinate_mem) hm F hF
  calc
    (∫ t,κ t • f t ∂μ)=∫ t,F (spectralPositiveGreenCoordinate t) • f t ∂μ := by
      apply integral_congr_ae
      filter_upwards [hpos] with t ht
      rw [he t ht]
    _ = 0 := h

end ArtinMatthews
