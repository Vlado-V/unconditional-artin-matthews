module

public import ArtinMatthews.SourceKPAdelicCompactSection
public import ArtinMatthews.SourceArchSphericalSection
public import Mathlib.Topology.Algebra.Group.Units


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

theorem sourceArchMatrixEntry_continuous (i j : Fin 2) :
    Continuous (fun g : GL (Fin 2) ℂ => g i j) :=
  (_root_.continuous_apply j).comp (GeneralLinearGroup.continuous_apply id continuous_id i)

theorem sourceArchBottomNorm_continuous : Continuous sourceArchBottomNorm :=
  ((sourceArchMatrixEntry_continuous 1 0).norm.pow 2).add
    ((sourceArchMatrixEntry_continuous 1 1).norm.pow 2)

theorem sourceArchDetNorm_continuous :
    Continuous (fun g : GL (Fin 2) ℂ => ‖(GeneralLinearGroup.det g : ℂ)‖) := by
  simpa only [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Pi.mul_apply, Pi.sub_apply] using
    (((sourceArchMatrixEntry_continuous 0 0).mul (sourceArchMatrixEntry_continuous 1 1)).sub
      ((sourceArchMatrixEntry_continuous 0 1).mul (sourceArchMatrixEntry_continuous 1 0))).norm

theorem sourceArchHeight_continuous : Continuous sourceArchHeight :=
  sourceArchDetNorm_continuous.div sourceArchBottomNorm_continuous
    (fun g => (sourceArchBottomNorm_pos g).ne')

theorem sourceArchSphericalGL_continuous (s : ℂ) : Continuous (sourceArchSphericalGL s) := by
  have he : sourceArchSphericalGL s = fun g : GL (Fin 2) ℂ =>
      Complex.exp ((Real.log (sourceArchHeight g) : ℂ) * (2*s+1)) := by
    funext g
    rw [sourceArchSphericalGL, Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (sourceArchHeight_pos g).ne'),
      ← Complex.ofReal_log (sourceArchHeight_pos g).le]
  rw [he]
  exact Complex.continuous_exp.comp
    (((Complex.continuous_ofReal.comp (sourceArchHeight_continuous.log
      (fun g => (sourceArchHeight_pos g).ne'))).mul continuous_const))

end
end ArtinMatthews.SourceArchJacquet
