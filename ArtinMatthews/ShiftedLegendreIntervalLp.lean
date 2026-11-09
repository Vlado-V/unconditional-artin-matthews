module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.RingTheory.Polynomial.ShiftedLegendre
public import Mathlib.Topology.Algebra.Polynomial


set_option backward.privateInPublic true
@[expose] public section

/-! Shifted Legendre functions in complex Lebesgue (L^2) on the unit interval. -/
namespace ArtinMatthews
open MeasureTheory Set
open scoped ENNReal Topology unitInterval
noncomputable section

abbrev ShiftedLegendreL2 := Lp ℂ 2 (volume : Measure I)

def shiftedLegendreToLp : C(I, ℂ) →L[ℂ] ShiftedLegendreL2 :=
  ContinuousMap.toLp 2 volume ℂ

def shiftedLegendreRestrict (f : ℝ → ℂ) (hf : ContinuousOn f I) : C(I, ℂ) :=
  ⟨fun x => f x, continuousOn_iff_continuous_domRestrict.mp hf⟩

theorem shiftedLegendreToLp_inner (f g : C(I, ℂ)) :
    inner ℂ (shiftedLegendreToLp f) (shiftedLegendreToLp g) =
      ∫ x : I, star (f x) * g x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume f,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume g] with x hx hy
  change inner ℂ ((ContinuousMap.toLp 2 volume ℂ f) x)
    ((ContinuousMap.toLp 2 volume ℂ g) x) = _
  rw [hx, hy]
  exact RCLike.inner_apply' _ _

theorem shiftedLegendreToLp_inner_interval {f g : ℝ → ℂ}
    (hf : ContinuousOn f I) (hg : ContinuousOn g I) :
    inner ℂ (shiftedLegendreToLp (shiftedLegendreRestrict f hf))
      (shiftedLegendreToLp (shiftedLegendreRestrict g hg)) =
      ∫ x in (0 : ℝ)..1, star (f x) * g x := by
  rw [shiftedLegendreToLp_inner]
  change (∫ x : I, star (f x) * g x ∂volume) = _
  rw [unitInterval.volume_def, integral_subtype_comap measurableSet_Icc
    (fun x : ℝ => star (f x) * g x), integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le zero_le_one]

def shiftedLegendreValue (n : ℕ) (x : ℝ) : ℝ :=
  Polynomial.aeval x (Polynomial.shiftedLegendre n)

theorem shiftedLegendreValue_continuous (n : ℕ) : Continuous (shiftedLegendreValue n) :=
  (Polynomial.shiftedLegendre n).continuous_aeval

def shiftedLegendreContinuous (n : ℕ) : C(I, ℂ) :=
  shiftedLegendreRestrict (fun x => (shiftedLegendreValue n x : ℂ))
    (Complex.continuous_ofReal.comp (shiftedLegendreValue_continuous n)).continuousOn

@[simp] theorem shiftedLegendreContinuous_apply (n : ℕ) (x : I) :
    shiftedLegendreContinuous n x = (shiftedLegendreValue n x : ℂ) := rfl

def shiftedLegendreVector (n : ℕ) : ShiftedLegendreL2 :=
  shiftedLegendreToLp (shiftedLegendreContinuous n)

theorem shiftedLegendreVector_inner_toLp (n : ℕ) {g : ℝ → ℂ} (hg : ContinuousOn g I) :
    inner ℂ (shiftedLegendreVector n) (shiftedLegendreToLp (shiftedLegendreRestrict g hg)) =
      ∫ x in (0 : ℝ)..1, (shiftedLegendreValue n x : ℂ) * g x := by
  simp only [shiftedLegendreVector, shiftedLegendreContinuous,
    shiftedLegendreToLp_inner_interval, Complex.star_def, Complex.conj_ofReal]

theorem shiftedLegendreVector_inner_interval (n m : ℕ) :
    inner ℂ (shiftedLegendreVector n) (shiftedLegendreVector m) =
      ((∫ x in (0 : ℝ)..1, shiftedLegendreValue n x * shiftedLegendreValue m x : ℝ) : ℂ) := by
  simp only [shiftedLegendreVector, shiftedLegendreContinuous, shiftedLegendreToLp_inner_interval,
    Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, intervalIntegral.integral_ofReal]

end
end ArtinMatthews
