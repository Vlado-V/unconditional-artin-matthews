module

public import ArtinMatthews.SourceKPReflectionDifferential


set_option backward.privateInPublic true
@[expose] public section

/-! Height-weighted Wirtinger derivatives of the actual signed action. -/
namespace ArtinMatthews
open NumberField SourceArchJacquet SourceHyperbolicGreen OAI.CubicEisenstein Filter
open scoped NumberField MatrixGroups AdeleRing Classical Topology ContDiff
noncomputable section

def sourceHorizontalOrientation (positive : Bool) : ℂ :=
  if positive then Complex.I else -Complex.I

def sourceProductHorizontal {ι : Type*} [Fintype ι] (positive : Bool) (v : ι)
    (F : ProductSpace ι → ℂ) (p : ProductSpace ι) : ℂ :=
  (p v 2 : ℂ) * (productPartial F v 0 p + sourceHorizontalOrientation positive *
    productPartial F v 1 p) / 2

private theorem horizontal_linear (ε : Bool) (u x y : ℂ) :
    (- (u.re : ℂ) * x - (u.im : ℂ) * y) + sourceHorizontalOrientation ε *
      (-(u.im : ℂ) * x + (u.re : ℂ) * y) =
    -(if ε then u else star u) * (x + sourceHorizontalOrientation (!ε) * y) := by
  have hu : (u.re : ℂ) + (u.im : ℂ) * Complex.I = u := Complex.re_add_im u
  have hs : (u.re : ℂ) - (u.im : ℂ) * Complex.I = star u := by
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  cases ε
  · simp only [sourceHorizontalOrientation,Bool.false_eq_true,if_false,Bool.not_false,if_true]
    rw [← hs]
    linear_combination -((u.im : ℂ) * y) * Complex.I_sq
  · simp only [sourceHorizontalOrientation,if_true,Bool.not_true,Bool.false_eq_true,if_false]
    conv_rhs => rw [← hu]
    linear_combination -((u.im : ℂ) * y) * Complex.I_sq

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "V" => InfinitePlace K
local notation "X" => ProductSpace V
local notation "Ω" => productUpper V
local notation "σ" => sourceKPCuspRationalComplexUnit K hζ

def sourceKPReflectionHorizontalPhase (b : Kˣ) (ε : Bool) (v : V) : ℂ :=
  let B := (σ b v : ℂ)⁻¹
  Neg.neg (if ε then B^2 else star (B^2)) / (Complex.normSq B : ℂ)

theorem sourceKPReflectionHorizontalPhase_norm (b : Kˣ) (ε : Bool) (v : V) :
    ‖sourceKPReflectionHorizontalPhase K hζ b ε v‖ = 1 := by
  let B := (σ b v : ℂ)⁻¹
  have hB : B ≠ 0 := inv_ne_zero (σ b v).ne_zero
  have h : ‖B‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hB)
  change ‖-(if ε then B^2 else star (B^2)) / (Complex.normSq B : ℂ)‖ = 1
  rw [norm_div,norm_neg,Complex.norm_real,Real.norm_of_nonneg (Complex.normSq_nonneg _),
    Complex.normSq_eq_norm_sq]
  cases ε <;> simp [h]

theorem sourceKPReflectionHorizontal_comp (b : Kˣ) (ε : Bool) (v : V)
    (F : X → ℂ) (p : X) (hp : p ∈ Ω)
    (h0 : p v 0 = 0) (h1 : p v 1 = 0)
    (hF : DifferentiableAt ℝ F (sourceKPReflectionArch K hζ b p)) :
    sourceProductHorizontal ε v (F ∘ sourceKPReflectionArch K hζ b) p =
      sourceKPReflectionHorizontalPhase K hζ b ε v *
        sourceProductHorizontal (!ε) v F (sourceKPReflectionArch K hζ b p) := by
  let B := (σ b v : ℂ)⁻¹
  let A := sourceKPReflectionArch K hζ b
  let L := fderiv ℝ F (A p)
  have hB : B ≠ 0 := inv_ne_zero (σ b v).ne_zero
  have hN : (Complex.normSq B : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Complex.normSq_pos.mpr hB).ne'
  have hy := productUpper_pos hp v
  have hyC : (p v 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hH : A p v 2 = Complex.normSq B / p v 2 := by
    change sourceKPArchEuclideanAction K hζ
      (sourceKPRationalArchMap K hζ (sourceKPReflectionWeyl K b)) p v 2 = _
    rw [sourceKPReflectionWeyl_euclidean K hζ b p hp v]
    change sourceArchReflection B (p v) 2 = _
    rw [sourceArchReflection_vertical B (p v) h0 h1 hy]
    rfl
  have hD : fderiv ℝ (F ∘ A) p = L.comp (sourceKPReflectionDifferential K hζ b p) :=
    (HasFDerivAt.comp (f := A) (g := F) p hF.hasFDerivAt
      (sourceKPReflectionArch_hasFDerivAt K hζ b p hp)).fderiv
  obtain ⟨hX,hY⟩ := sourceKPReflectionDifferential_horizontal K hζ b p hp v h0 h1
  change sourceKPReflectionDifferential K hζ b p (productDirection v 0) =
    ((p v 2)⁻¹)^2 • (-((B^2).re) • productDirection v 0 - (B^2).im • productDirection v 1) at hX
  change sourceKPReflectionDifferential K hζ b p (productDirection v 1) =
    ((p v 2)⁻¹)^2 • (-((B^2).im) • productDirection v 0 + (B^2).re • productDirection v 1) at hY
  change sourceProductHorizontal ε v (F ∘ A) p = _ * sourceProductHorizontal (!ε) v F (A p)
  rw [sourceProductHorizontal,sourceProductHorizontal]
  simp only [productPartial,hD,ContinuousLinearMap.comp_apply,hX,hY,map_smul,map_add,map_sub,
    Complex.real_smul,Complex.ofReal_pow,Complex.ofReal_inv,Complex.ofReal_neg,hH,Complex.ofReal_div]
  let x := L (productDirection v 0)
  let y := L (productDirection v 1)
  change (p v 2 : ℂ) * (((p v 2 : ℂ)⁻¹)^2 * (-( (B^2).re : ℂ) * x - ((B^2).im : ℂ) * y) +
    sourceHorizontalOrientation ε * (((p v 2 : ℂ)⁻¹)^2 *
      (-((B^2).im : ℂ) * x + ((B^2).re : ℂ) * y))) / 2 =
    (-(if ε then B^2 else star (B^2)) / (Complex.normSq B : ℂ)) *
      ((Complex.normSq B : ℂ) / (p v 2 : ℂ) * (x + sourceHorizontalOrientation (!ε) * y) / 2)
  calc
    _ = (p v 2 : ℂ) * ((p v 2 : ℂ)⁻¹)^2 *
        ((-((B^2).re : ℂ) * x - ((B^2).im : ℂ) * y) +
          sourceHorizontalOrientation ε * (-((B^2).im : ℂ) * x + ((B^2).re : ℂ) * y)) / 2 := by ring
    _ = _ := by
      rw [horizontal_linear]
      field_simp [hN,hyC]

end
end ArtinMatthews
