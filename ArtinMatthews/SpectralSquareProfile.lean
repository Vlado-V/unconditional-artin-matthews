module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper


set_option backward.privateInPublic true
@[expose] public section

/-! The positive square coordinate and its exact half-line Jacobian. -/
namespace ArtinMatthews
open Set Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section

def spectralSquareProfile (f : ℝ → ℂ) (s : ℝ) : ℂ :=
  if 0 < s then f (Real.sqrt s) / (Real.sqrt s : ℂ) else 0

theorem spectralSquareProfile_recovery (f : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) * spectralSquareProfile f (x ^ 2) = f x := by
  rw [spectralSquareProfile, ite_eq_left (sq_pos_of_pos hx), Real.sqrt_sq hx.le, mul_div_cancel₀]
  exact_mod_cast hx.ne'

theorem spectralSquareProfile_support {f : ℝ → ℂ}
    (hc : HasCompactSupport f) (hpos : tsupport f ⊆ Ioi (0 : ℝ)) :
    HasCompactSupport (spectralSquareProfile f) ∧
      tsupport (spectralSquareProfile f) ⊆ Ioi (0 : ℝ) := by
  let K := (fun x : ℝ => x ^ 2) '' tsupport f
  have hK : IsCompact K := hc.isCompact.image
    ((continuous_id : Continuous (id : ℝ → ℝ)).pow 2)
  have hsupp : Function.support (spectralSquareProfile f) ⊆ K := by
    intro s hs
    have hp : 0 < s := by
      by_contra h
      exact hs (ite_eq_right h)
    refine ⟨Real.sqrt s, subset_tsupport f ?_, Real.sq_sqrt hp.le⟩
    intro hz
    exact hs (by simp only [spectralSquareProfile, ite_eq_left hp, hz, zero_div])
  have ht : tsupport (spectralSquareProfile f) ⊆ K := closure_minimal hsupp hK.isClosed
  refine ⟨hK.of_isClosed_subset (isClosed_tsupport _) ht, ?_⟩
  intro s hs
  obtain ⟨x, hx, rfl⟩ := ht hs
  exact mem_Ioi.mpr (pow_pos (mem_Ioi.mp (hpos hx)) 2)

theorem spectralSquareProfile_contDiff {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hpos : tsupport f ⊆ Ioi (0 : ℝ)) :
    ContDiff ℝ ∞ (spectralSquareProfile f) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hs : 0 < s
  · have hsq : ContDiffAt ℝ ∞ Real.sqrt s := Real.contDiffAt_sqrt hs.ne'
    have hInv : ContDiffAt ℝ ∞ (fun t : ℝ => (Real.sqrt t)⁻¹) s :=
      hsq.inv (Real.sqrt_pos_of_pos hs).ne'
    have hcast : ContDiffAt ℝ ∞ (fun t : ℝ => (((Real.sqrt t)⁻¹ : ℝ) : ℂ)) s :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp s hInv
    have hnum : ContDiffAt ℝ ∞ (fun t : ℝ => f (Real.sqrt t)) s := hf.contDiffAt.comp s hsq
    have hcomp : ContDiffAt ℝ ∞ (fun t : ℝ => f (Real.sqrt t) * (((Real.sqrt t)⁻¹ : ℝ) : ℂ)) s :=
      hnum.mul hcast
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hs] with t ht
    have ht' : 0 < t := ht
    rw [spectralSquareProfile, ite_eq_left ht', Complex.ofReal_inv, div_eq_mul_inv]
  · have h0 : (0 : ℝ) ∉ tsupport f := fun h => (lt_irrefl (0 : ℝ)) (mem_Ioi.mp (hpos h))
    have hf0 := notMem_tsupport_iff_eventuallyEq.mp h0
    have hs0 : Real.sqrt s = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_not_gt hs)
    have hlim : Tendsto Real.sqrt (𝓝 s) (𝓝 0) := by
      rw [← hs0]
      exact Real.continuous_sqrt.continuousAt
    have hz : ∀ᶠ t in 𝓝 s, f (Real.sqrt t) = 0 := hlim.eventually hf0
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℂ)) s).congr_of_eventuallyEq
    filter_upwards [hz] with t ht
    simp [spectralSquareProfile, ht]

theorem spectralSquare_integrable (g : ℝ → ℂ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) * g (x ^ 2)) (Ioi 0) ↔ IntegrableOn g (Ioi 0) := by
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two,
    Complex.real_smul] using! integrableOn_Ioi_comp_rpow_iff' g (p := 2) (by norm_num)

theorem spectralSquare_integral (g : ℝ → ℂ) :
    (∫ x : ℝ in Ioi 0, (x : ℂ) * g (x ^ 2)) = (1 / 2 : ℂ) * ∫ s : ℝ in Ioi 0, g s := by
  calc
    _ = ∫ x : ℝ in Ioi 0, (2 * x) • ((1 / 2 : ℂ) * g (x ^ 2)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      dsimp only
      rw [Complex.real_smul]
      push_cast
      ring
    _ = ∫ s : ℝ in Ioi 0, (1 / 2 : ℂ) * g s := by
      simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two] using!
        integral_comp_rpow_Ioi_of_pos (g := fun s : ℝ => (1 / 2 : ℂ) * g s) (p := 2) (by norm_num)
    _ = _ := integral_const_mul _ _

end
end ArtinMatthews
