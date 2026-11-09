module

public import ArtinMatthews.SLocalNormOneHaar
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section

variable {K : Type} [Field K]
variable {v : InfinitePlace K} (hv : IsComplex v)

/-- At a chosen complex place, the normalized local norm of this unit is `exp t`. -/
def sourceComplexPlaceRadialUnit (t : ℝ) : v.Completionˣ :=
  Units.map (ringEquivComplexOfIsComplex hv).symm.toMonoidHom
    (Units.mk0 (Real.exp (t / 2) : ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)))

theorem sourceComplexPlaceRadialUnit_norm (t : ℝ) :
    ‖(sourceComplexPlaceRadialUnit hv t : v.Completion)‖ = Real.exp (t / 2) := by
  change ‖(ringEquivComplexOfIsComplex hv).symm (Real.exp (t / 2) : ℂ)‖ = _
  have hzero : (isometryEquivComplexOfIsComplex hv).symm (0 : ℂ) = 0 :=
    map_zero (ringEquivComplexOfIsComplex hv).symm
  have hn (z : ℂ) : ‖(ringEquivComplexOfIsComplex hv).symm z‖ = ‖z‖ :=
    (isometryEquivComplexOfIsComplex hv).symm.isometry.norm_map_of_map_zero hzero z
  rw [hn, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem sourceComplexPlaceRadialUnit_zero : sourceComplexPlaceRadialUnit hv 0 = 1 := by
  apply Units.ext
  change (ringEquivComplexOfIsComplex hv).symm (Real.exp (0 / 2) : ℂ) = 1
  simp

theorem sourceComplexPlaceRadialUnit_add (a b : ℝ) :
    sourceComplexPlaceRadialUnit hv (a + b) =
      sourceComplexPlaceRadialUnit hv a * sourceComplexPlaceRadialUnit hv b := by
  apply Units.ext
  change (ringEquivComplexOfIsComplex hv).symm (Real.exp ((a + b) / 2) : ℂ) =
    (ringEquivComplexOfIsComplex hv).symm (Real.exp (a / 2) : ℂ) *
      (ringEquivComplexOfIsComplex hv).symm (Real.exp (b / 2) : ℂ)
  rw [add_div, Real.exp_add, Complex.ofReal_mul, map_mul]

variable [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- A section of the literal S-local norm, supported at a single complex place. -/
def sourceSLocalRadial (t : ℝ) : SWholeUnits K S :=
  (Pi.mulSingle v (sourceComplexPlaceRadialUnit hv t), 1)

theorem sourceSLocalRadial_zero : sourceSLocalRadial hv S 0 = 1 := by
  simp [sourceSLocalRadial, sourceComplexPlaceRadialUnit_zero]

theorem sourceSLocalRadial_add (a b : ℝ) :
    sourceSLocalRadial hv S (a + b) = sourceSLocalRadial hv S a * sourceSLocalRadial hv S b := by
  simp [sourceSLocalRadial, sourceComplexPlaceRadialUnit_add, Pi.mulSingle_mul]

theorem sourceSLocalRadial_norm (t : ℝ) : sLocalNorm K S (sourceSLocalRadial hv S t) = Real.exp t := by
  rw [sLocalNorm_eq_prod]
  have hw : (∏ w : InfinitePlace K, ‖(Pi.mulSingle (M := fun w => w.Completionˣ) v (sourceComplexPlaceRadialUnit hv t) w :
      w.Completion)‖ ^ w.mult) =
      ‖(sourceComplexPlaceRadialUnit hv t : v.Completion)‖ ^ v.mult := by
    rw [Finset.prod_eq_single v]
    · rw [Pi.mulSingle_eq_same]
    · intro w _ hw
      simp [Pi.mulSingle_eq_of_ne hw]
    · simp
  change (∏ w : InfinitePlace K, ‖(Pi.mulSingle (M := fun w => w.Completionˣ) v (sourceComplexPlaceRadialUnit hv t) w :
    w.Completion)‖ ^ w.mult) * (∏ p : S, ‖(1 : p.1.adicCompletion K)‖) = _
  rw [hw, sourceComplexPlaceRadialUnit_norm, hv.mult_eq_two, ← Real.exp_nat_mul]
  simp
  ring

end
end ArtinMatthews.SourcePhysical
