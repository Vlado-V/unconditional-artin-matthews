module

public import ArtinMatthews.SourceKPProjectiveBruhatCells
public import ArtinMatthews.SourceKPAdeleLocalCover


set_option backward.privateInPublic true
@[expose] public section

/-! The exact Weyl conjugate of an upper root in the genuine local
cubic cover, including its image in the full adelic cover. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups
noncomputable section

theorem sourceGL2Weyl_upper_weyl {F : Type*} [Field F] (x : F) :
    sourceGL2Weyl * sourceGL2Upper x * sourceGL2Weyl = sourceGL2Lower x := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceGL2Weyl, sourceGL2Upper, sourceGL2Lower, Matrix.mul_apply, Fin.sum_univ_two]

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

local notation "L" => P.adicCompletion K
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P

theorem sourceFiniteKP2Multiplier_weyl_upper_weyl (x : L) :
    sourceFiniteKP2Multiplier K hζ P (sourceGL2Weyl * sourceGL2Upper x) sourceGL2Weyl = 1 := by
  change sourceKP2Multiplier (sourceFiniteKPHilbert K hζ P)
    (sourceGL2Weyl * sourceGL2Upper x) sourceGL2Weyl = 1
  rw [sourceKP2Multiplier_right_weyl_formula _ (sourceFiniteKPHilbert_minus_right K hζ P),
    sourceGL2Weyl_upper_weyl, sourceKubotaX_weyl_upper, div_one, map_mul,
    sourceGL2Weyl_det, sourceGL2Upper_det, mul_one]
  rw [map_div, sourceFiniteKPHilbert_diag, sourceFiniteKPHilbert_minus_right, div_one]

theorem sourceFiniteKP2ProjectiveLift_weyl_upper_weyl (x : L) :
    l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x) * l₀ sourceGL2Weyl = l₀ (sourceGL2Lower x) := by
  rw [sourceFiniteKP2ProjectiveLift_mul_of_phase_one K hζ P _ _
    (sourceKP2Multiplier_weyl_upper (sourceFiniteKPHilbert K hζ P) x),
    sourceFiniteKP2ProjectiveLift_mul_of_phase_one K hζ P _ _
      (sourceFiniteKP2Multiplier_weyl_upper_weyl K hζ P x), sourceGL2Weyl_upper_weyl]

theorem sourceKPAdelicLocalProjective_weyl_upper_weyl (x : L) :
    sourceKPAdelicLocalProjective K hζ P (l₀ sourceGL2Weyl) *
        sourceKPAdelicLocalProjective K hζ P (l₀ (sourceGL2Upper x)) *
        sourceKPAdelicLocalProjective K hζ P (l₀ sourceGL2Weyl) =
      sourceKPAdelicLocalProjective K hζ P (l₀ (sourceGL2Lower x)) := by
  rw [← map_mul, ← map_mul, sourceFiniteKP2ProjectiveLift_weyl_upper_weyl]

end
end ArtinMatthews
