module

public import ArtinMatthews.UnitTorusLocalRellich
public import ArtinMatthews.VaryingKummerAnalyticPoisson
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Basify


set_option backward.privateInPublic true
@[expose] public section

/-! Coordinate derivatives of a smooth periodic real lift descend to
continuous functions on the same normalized unit torus. -/
namespace ArtinMatthews
open MeasureTheory UnitAddTorus
open scoped ContDiff
noncomputable section

local instance unitTorusSmoothCoordinateMeasure : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

theorem unitTorus_smooth_coordinate_derivatives (f : C(UnitAddTorus ι, ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ι → ℝ => f (unitTorusUnitCellProjection ι x))) :
    ∃ g : ι → C(UnitAddTorus ι, ℂ),
      (∀ j x, g j (unitTorusUnitCellProjection ι x) =
        fderiv ℝ (fun y : ι → ℝ => f (unitTorusUnitCellProjection ι y)) x (Pi.single j 1)) ∧
      (∀ j, ContDiff ℝ ∞ (fun x : ι → ℝ => g j (unitTorusUnitCellProjection ι x))) ∧
      (∀ j n, mFourierCoeff (g j) n =
        (2 * (Real.pi : ℂ) * Complex.I * (n j : ℂ)) * mFourierCoeff f n) := by
  let lift (x : ι → ℝ) := f (unitTorusUnitCellProjection ι x)
  let D (j : ι) (x : ι → ℝ) := fderiv ℝ lift x (Pi.single j 1)
  have hD (j : ι) : ContDiff ℝ ∞ (D j) :=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  have hperiod (j : ι) (x : ι → ℝ) (k : ι → ℤ) :
      D j (x + ReusedTheta.integerVector k) = D j x := by
    have he : (fun y => lift (y + ReusedTheta.integerVector k)) = lift :=
      funext fun y => congrArg f (ReusedTheta.torusProjection_add_integer y k)
    change fderiv ℝ lift (x + ReusedTheta.integerVector k) (Pi.single j 1) = D j x
    rw [← fderiv_comp_add_right (f := lift), he]
  let G (j : ι) (z : UnitAddTorus ι) := D j (ReusedTheta.torusRepresentative z)
  have hG (j : ι) (x : ι → ℝ) : G j (unitTorusUnitCellProjection ι x) = D j x := by
    change D j (ReusedTheta.torusRepresentative (ReusedTheta.torusProjection x)) = D j x
    obtain ⟨k, hk⟩ := (ReusedTheta.torusProjection_eq_iff x _).mp
      (ReusedTheta.torusProjection_representative (ReusedTheta.torusProjection x)).symm
    rw [hk, hperiod]
  have hGS (j : ι) : ContDiff ℝ ∞ (fun x : ι → ℝ => G j (unitTorusUnitCellProjection ι x)) := by
    simp_rw [hG]
    exact hD j
  let g (j : ι) : C(UnitAddTorus ι, ℂ) := ⟨G j,
    (ReusedTheta.torusProjection_openQuotient (d := ι)).isQuotientMap.continuous_iff.mpr
      (hGS j).continuous⟩
  refine ⟨g, hG, hGS, ?_⟩
  apply unitTorus_fourier_coordinate_derivative ι f g
  intro j z t
  let x := ReusedTheta.torusRepresentative z
  have hx : unitTorusUnitCellProjection ι x = z := ReusedTheta.torusProjection_representative z
  have hslice (u : ℝ) : unitTorusUnitCellProjection ι (Function.update x j u) =
      Function.update z j (u : UnitAddCircle) := by
    funext i
    by_cases hi : i = j
    · subst i
      simp only [unitTorusUnitCellProjection, Function.update_self]
    · have hxi := congrFun hx i
      simpa only [unitTorusUnitCellProjection, Function.update_of_ne hi] using hxi
  have hd := (hf.differentiable (by simp) (Function.update x j t)).hasFDerivAt.comp_hasDerivAt
    t (hasDerivAt_update x j t)
  change HasDerivAt (fun u => f (unitTorusUnitCellProjection ι (Function.update x j u)))
    (D j (Function.update x j t)) t at hd
  rw [← hG j (Function.update x j t)] at hd
  change HasDerivAt (fun u : ℝ => f (Function.update z j (u : UnitAddCircle)))
    (G j (Function.update z j (t : UnitAddCircle))) t
  simpa only [hslice] using hd

end
end ArtinMatthews
