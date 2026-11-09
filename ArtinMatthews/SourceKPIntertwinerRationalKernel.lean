module

public import ArtinMatthews.SourceKPAdelicTraceConstantTerm
public import ArtinMatthews.SourceKPAdelicTorusUpper
public import Mathlib.MeasureTheory.Group.Integral


set_option backward.privateInPublic true
@[expose] public section

/-! Exact changes of the adelic integration variable under left
upper and rational diagonal multiplication of the original section. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain Matrix MeasureTheory
open scoped NumberField MatrixGroups AdeleRing

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceKPRationalKernelMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance sourceKPRationalKernelBorel : BorelSpace 𝔸[K] := ⟨rfl⟩

theorem sourceKPAdelicCompactScalar_rationalBorel (s : ℂ) (b : PGL(2, K))
    (hb : b ∈ sourceKPRationalBorel K) (g : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicCompactScalar K hζ s
      (sourceKPAdelicProjectiveRationalLift K hζ b * g) =
        sourceKPAdelicCompactScalar K hζ s g :=
  (sourceKPAdelicPrincipalSeriesScalar K hζ s
    (sourceKPAdelicCompactSection K hζ s)).property b hb g

theorem sourceKPAdelicIntertwiningKernel_left_upper (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (x y : 𝔸[K]) :
    sourceKPAdelicIntertwiningKernel K hζ s
      (sourceKPAdelicUpperLift K hζ x * g) y =
        sourceKPAdelicIntertwiningKernel K hζ s g (y + x) := by
  simp only [sourceKPAdelicIntertwiningKernel, sourceKPAdelicUpperLift_add, mul_assoc]

theorem sourceKPAdelicIntertwiningKernel_rational_diagonal (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (a : Kˣ) (y : 𝔸[K]) :
    sourceKPAdelicIntertwiningKernel K hζ s
      (sourceKPAdelicProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K a) * g) y =
        sourceKPAdelicIntertwiningKernel K hζ s g
          (algebraMap K 𝔸[K] (↑(a⁻¹) : K) * y) := by
  let u := IdeleGroup.unitEmbedding (𝓞 K) K a
  let D := sourceKPAdelicProjectiveDiagonalLift K hζ
  let N := sourceKPAdelicUpperLift K hζ
  let W := sourceKPAdelicProjectiveWeyl K hζ
  have hupper : D u * N ((↑(u⁻¹) : 𝔸[K]) * y) = N y * D u := by
    dsimp only [D, N]
    rw [sourceKPAdelicProjectiveDiagonalLift_upper]
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  have hweyl : W * D u = D u⁻¹ * W :=
    sourceKPAdelicProjectiveWeyl_diagonal K hζ u
  have harg : (↑(u⁻¹) : 𝔸[K]) = algebraMap K 𝔸[K] (↑(a⁻¹) : K) := rfl
  have hdiag : D u⁻¹ =
      sourceKPAdelicProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K a⁻¹) := by
    rw [sourceKPAdelicProjectiveRationalLift_diagonal, map_inv]
  have hmatrix : W * N y * (D u * g) =
      D u⁻¹ * (W * N ((↑(u⁻¹) : 𝔸[K]) * y) * g) := by
    calc
      W * N y * (D u * g) = W * (N y * D u) * g := by group
      _ = W * (D u * N ((↑(u⁻¹) : 𝔸[K]) * y)) * g := by rw [hupper]
      _ = (W * D u) * N ((↑(u⁻¹) : 𝔸[K]) * y) * g := by group
      _ = D u⁻¹ * (W * N ((↑(u⁻¹) : 𝔸[K]) * y) * g) := by rw [hweyl]; group
  unfold sourceKPAdelicIntertwiningKernel
  rw [sourceKPAdelicProjectiveRationalLift_diagonal]
  change sourceKPAdelicCompactScalar K hζ s (W * N y * (D u * g)) = _
  rw [hmatrix, hdiag, harg]
  apply sourceKPAdelicCompactScalar_rationalBorel K hζ s
  change ProjGenLinGroup.mk (sourceKPDiagonalHom K a⁻¹) ∈ sourceKPRationalBorel K
  rw [sourceKPDiagonalHom_field]
  exact sourceKPRationalBorel_diagonal K a⁻¹

theorem sourceKPAdelicIntertwiner_left_upper (μ : Measure 𝔸[K]) [μ.IsAddHaarMeasure]
    (s : ℂ) (g : SourceKPAdelicProjective K hζ) (x : 𝔸[K]) :
    sourceKPAdelicIntertwiner K hζ μ s (sourceKPAdelicUpperLift K hζ x * g) =
      sourceKPAdelicIntertwiner K hζ μ s g := by
  unfold sourceKPAdelicIntertwiner
  simp_rw [sourceKPAdelicIntertwiningKernel_left_upper]
  exact integral_add_right_eq_self (sourceKPAdelicIntertwiningKernel K hζ s g) x

theorem sourceKPAdelicTraceIntertwiner_left_upper (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (x : 𝔸[K]) :
    sourceKPAdelicTraceIntertwiner K hζ s (sourceKPAdelicUpperLift K hζ x * g) =
      sourceKPAdelicTraceIntertwiner K hζ s g := by
  unfold sourceKPAdelicTraceIntertwiner
  rw [sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ]
  exact sourceKPAdelicIntertwiner_left_upper K hζ _ s g x

end
end ArtinMatthews
