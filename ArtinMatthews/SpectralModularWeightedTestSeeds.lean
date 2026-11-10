module

public import ArtinMatthews.SpectralGamma0Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan


set_option backward.privateInPublic true
@[expose] public section

/-! Actual smooth compact seed operations used to remove the nonvanishing
height multiplier in the modular weak-gradient tests. -/

noncomputable section
open Set Filter Topology
open scoped CompactlySupported ContDiff MatrixGroups

namespace ArtinMatthews

def h2ConjugateSmoothSeed (ψ : h2SmoothCompactSeeds) : h2SmoothCompactSeeds :=
  ⟨{ toFun := fun z => star (ψ.val z)
     continuous_toFun := Complex.continuous_conj.comp ψ.val.continuous
     hasCompactSupport' := ψ.val.hasCompactSupport.comp_left (by simp) },
    Complex.conjCLE.contDiff.comp_contDiffOn ψ.property⟩

theorem h2ConjugateSmoothSeed_apply (ψ : h2SmoothCompactSeeds) (z : UpperHalfPlane) :
    (h2ConjugateSmoothSeed ψ).val z = star (ψ.val z) := rfl

theorem h2ConjugateSmoothSeed_support (ψ : h2SmoothCompactSeeds) :
    tsupport (h2ConjugateSmoothSeed ψ).val ⊆ tsupport ψ.val := by
  apply closure_mono
  intro z hz
  change star (ψ.val z) ≠ 0 at hz
  exact fun h => hz (by rw [h, star_zero])

def h2DivideHeightSmoothSeed (ψ : h2SmoothCompactSeeds) : h2SmoothCompactSeeds := by
  refine ⟨{ toFun := fun z => z.im⁻¹ • ψ.val z
            continuous_toFun := (UpperHalfPlane.continuous_im.inv₀
              (fun z => z.im_ne_zero)).smul ψ.val.continuous
            hasCompactSupport' := ?_ }, ?_⟩
  · apply ψ.val.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _)
    exact tsupport_smul_subset_right (fun z : UpperHalfPlane => z.im⁻¹) ψ.val
  · intro z hz
    have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
    have hn : ContDiffAt ℝ ∞ (fun w : ℂ => ψ.val (UpperHalfPlane.ofComplex w)) z :=
      ψ.property.contDiffAt (hopen.mem_nhds hz)
    have hd : ContDiffAt ℝ ∞ (fun w : ℂ => w.im⁻¹) z :=
      Complex.imCLM.contDiff.contDiffAt.inv (ne_of_gt hz)
    have hbase : ContDiffAt ℝ ∞
        (fun w : ℂ => w.im⁻¹ • ψ.val (UpperHalfPlane.ofComplex w)) z := hd.smul hn
    apply (hbase.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hopen.mem_nhds hz] with w hw
    change (UpperHalfPlane.ofComplex w).im⁻¹ • ψ.val (UpperHalfPlane.ofComplex w) =
      w.im⁻¹ • ψ.val (UpperHalfPlane.ofComplex w)
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    rfl

theorem h2DivideHeightSmoothSeed_apply (ψ : h2SmoothCompactSeeds) (z : UpperHalfPlane) :
    (h2DivideHeightSmoothSeed ψ).val z = ψ.val z / (z.im : ℂ) := by
  change z.im⁻¹ • ψ.val z = ψ.val z / (z.im : ℂ)
  simp [Complex.real_smul, div_eq_mul_inv, mul_comm]

theorem h2DivideHeightSmoothSeed_support (ψ : h2SmoothCompactSeeds) :
    tsupport (h2DivideHeightSmoothSeed ψ).val ⊆ tsupport ψ.val := by
  exact tsupport_smul_subset_right (fun z : UpperHalfPlane => z.im⁻¹) ψ.val

end ArtinMatthews
