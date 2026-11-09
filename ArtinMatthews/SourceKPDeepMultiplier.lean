module

public import ArtinMatthews.SourceKPDeepNonzero


set_option backward.privateInPublic true
@[expose] public section

/-! Triviality of the actual local cubic multiplier on matrices with
deep cube diagonal data, including every zero lower-row branch. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups
noncomputable section

structure SourceKPMatrixCubeData {F : Type*} [Field F] (g : GL (Fin 2) F) : Prop where
  top_cube : ∃ a : Fˣ, g 0 0 = ((a^3 : Fˣ) : F)
  bottom_cube : ∃ d : Fˣ, g 1 1 = ((d^3 : Fˣ) : F)
  det_cube : GeneralLinearGroup.det g ∈ sourceKPUnitCubes F

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

theorem sourceFiniteKP2Multiplier_deep_zero_left
    (g h : GL (Fin 2) (P.adicCompletion K)) (hg : g 1 0 = 0)
    (hdata : SourceKPMatrixCubeData g) : sourceFiniteKP2Multiplier K hζ P g h = 1 := by
  let B := sourceFiniteKPHilbert K hζ P
  let x := sourceKubotaX g
  let y := sourceKubotaX h
  obtain ⟨d,hd⟩ := hdata.bottom_cube
  have hx : x = d^3 := by
    apply Units.ext
    rw [sourceKubotaX_val_right g hg]
    exact hd
  have hxC : x ∈ sourceKPUnitCubes (P.adicCompletion K) := by rw [hx]; exact ⟨d,rfl⟩
  have hratio : x / GeneralLinearGroup.det g ∈ sourceKPUnitCubes (P.adicCompletion K) :=
    (sourceKPUnitCubes _).div_mem hxC hdata.det_cube
  have he : (x*y)/(y*GeneralLinearGroup.det g) = x/GeneralLinearGroup.det g := by
    rw [mul_comm x y, mul_div_mul_left_eq_div]
  change B (sourceKubotaX (g*h)/x)
    (sourceKubotaX (g*h)/(y*GeneralLinearGroup.det g)) *
      B (GeneralLinearGroup.det g) (GeneralLinearGroup.det h)^2 = 1
  rw [sourceKubotaX_mul_left_triangular g h hg]
  change B ((x*y)/x) ((x*y)/(y*GeneralLinearGroup.det g)) *
    B (GeneralLinearGroup.det g) (GeneralLinearGroup.det h)^2 = 1
  rw [mul_div_cancel_left, he,
    sourceFiniteKPHilbert_of_cube_right K hζ P y _ hratio,
    sourceFiniteKPHilbert_of_cube_left K hζ P _ _ hdata.det_cube, one_pow, one_mul]

theorem sourceFiniteKP2Multiplier_deep_zero_right
    (g h : GL (Fin 2) (P.adicCompletion K)) (hg : g 1 0 ≠ 0) (hh : h 1 0 = 0)
    (hgData : SourceKPMatrixCubeData g) (hhData : SourceKPMatrixCubeData h) :
    sourceFiniteKP2Multiplier K hζ P g h = 1 := by
  let B := sourceFiniteKPHilbert K hζ P
  let x := sourceKubotaX g
  obtain ⟨a,ha⟩ := hhData.top_cube
  have hgh : (g*h) 1 0 ≠ 0 := by
    rw [sourceGL2_bottom_left_mul, hh, mul_zero, add_zero, ha]
    exact mul_ne_zero hg (a^3).ne_zero
  have he : sourceKubotaX (g*h) = x*a^3 := by
    apply Units.ext
    rw [Units.val_mul, sourceKubotaX_val_left _ hgh,
      sourceKubotaX_val_left _ hg, sourceGL2_bottom_left_mul, hh, mul_zero, add_zero, ha]
  have haC : a^3 ∈ sourceKPUnitCubes (P.adicCompletion K) := ⟨a,rfl⟩
  change B (sourceKubotaX (g*h)/x)
    (sourceKubotaX (g*h)/(sourceKubotaX h*GeneralLinearGroup.det g)) *
      B (GeneralLinearGroup.det g) (GeneralLinearGroup.det h)^2 = 1
  rw [he, mul_div_cancel_left,
    sourceFiniteKPHilbert_of_cube_left K hζ P (a^3) _ haC,
    sourceFiniteKPHilbert_of_cube_left K hζ P _ _ hgData.det_cube, one_pow, one_mul]

theorem sourceFiniteKP2Multiplier_deep_zero_product
    (g h : GL (Fin 2) (P.adicCompletion K)) (hg : g 1 0 ≠ 0) (hh : h 1 0 ≠ 0)
    (hgh : (g*h) 1 0 = 0) (hgData : SourceKPMatrixCubeData g)
    (hhData : SourceKPMatrixCubeData h) (hghData : SourceKPMatrixCubeData (g*h)) :
    sourceFiniteKP2Multiplier K hζ P g h = 1 := by
  let B := sourceFiniteKPHilbert K hζ P
  let x := sourceKubotaX g
  let y := sourceKubotaX h
  let z := sourceKubotaX (g*h)
  let m := sourceMinusOneUnit (P.adicCompletion K)
  obtain ⟨d,hd⟩ := hghData.bottom_cube
  have hz : z = d^3 := by
    apply Units.ext
    rw [sourceKubotaX_val_right _ hgh]
    exact hd
  have hzC : z ∈ sourceKPUnitCubes (P.adicCompletion K) := by rw [hz]; exact ⟨d,rfl⟩
  have hcross : x * GeneralLinearGroup.det h = (m*z)*y := by
    apply Units.ext
    change (sourceKubotaX g : P.adicCompletion K) * (GeneralLinearGroup.det h : P.adicCompletion K) =
      (-1 * (sourceKubotaX (g*h) : P.adicCompletion K)) * (sourceKubotaX h : P.adicCompletion K)
    rw [sourceKubotaX_val_left _ hg, sourceKubotaX_val_left _ hh,
      sourceKubotaX_val_right _ hgh, sourceKubota_det_cross, hgh, zero_mul, zero_sub]
    ring
  have hratioEq : x/y = (m*z)/GeneralLinearGroup.det h := by
    calc
      x/y = (x*GeneralLinearGroup.det h)/(y*GeneralLinearGroup.det h) :=
        (mul_div_mul_right_eq_div x y (GeneralLinearGroup.det h)).symm
      _ = ((m*z)*y)/(y*GeneralLinearGroup.det h) := by rw [hcross]
      _ = (m*z)/GeneralLinearGroup.det h := by rw [mul_comm (m*z) y, mul_div_mul_left_eq_div]
  have hratio : x/y ∈ sourceKPUnitCubes (P.adicCompletion K) := by
    rw [hratioEq]
    exact (sourceKPUnitCubes _).div_mem
      ((sourceKPUnitCubes _).mul_mem (sourceKPUnitCubes_minusOne _) hzC) hhData.det_cube
  have he : (z/x)/(z/(y*GeneralLinearGroup.det g)) = GeneralLinearGroup.det g/(x/y) := by
    apply Additive.ofMul.injective
    simp only [ofMul_div, ofMul_mul]
    abel
  have hargs : (z/x)/(z/(y*GeneralLinearGroup.det g)) ∈ sourceKPUnitCubes (P.adicCompletion K) := by
    rw [he]
    exact (sourceKPUnitCubes _).div_mem hgData.det_cube hratio
  change B (z/x) (z/(y*GeneralLinearGroup.det g)) *
    B (GeneralLinearGroup.det g) (GeneralLinearGroup.det h)^2 = 1
  rw [sourceFiniteKPHilbert_of_cube_ratio K hζ P _ _ hargs,
    sourceFiniteKPHilbert_of_cube_left K hζ P _ _ hgData.det_cube, one_pow, one_mul]

theorem sourceFiniteKP2Multiplier_deep_cubes
    (g h : GL (Fin 2) (P.adicCompletion K))
    (hgData : SourceKPMatrixCubeData g) (hhData : SourceKPMatrixCubeData h)
    (hghData : SourceKPMatrixCubeData (g*h)) : sourceFiniteKP2Multiplier K hζ P g h = 1 := by
  by_cases hg : g 1 0 = 0
  · exact sourceFiniteKP2Multiplier_deep_zero_left K hζ P g h hg hgData
  by_cases hh : h 1 0 = 0
  · exact sourceFiniteKP2Multiplier_deep_zero_right K hζ P g h hg hh hgData hhData
  by_cases hgh : (g*h) 1 0 = 0
  · exact sourceFiniteKP2Multiplier_deep_zero_product K hζ P g h hg hh hgh hgData hhData hghData
  obtain ⟨a,ha⟩ := hhData.top_cube
  obtain ⟨d,hd⟩ := hgData.bottom_cube
  exact sourceFiniteKP2Multiplier_deep_nonzero K hζ P g h hg hh hgh a d ha hd hgData.det_cube

end
end ArtinMatthews
