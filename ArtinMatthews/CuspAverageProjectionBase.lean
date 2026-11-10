module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis


set_option backward.privateInPublic true
@[expose] public section

/-! Actual unnormalized hyperbolic period-strip measure and horizontal
average representatives. The operator construction is separate. -/
noncomputable section
namespace ArtinMatthews

open MeasureTheory Set

def cuspHorizontalMeasure (w : ℝ) : Measure ℝ :=
  volume.restrict (Ioc 0 w)

def cuspVerticalMeasure (Y : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi Y)).withDensity (fun y : ℝ => ENNReal.ofReal (y ^ (-2 : ℤ)))

def cuspStripMeasure (w Y : ℝ) : Measure (ℝ × ℝ) :=
  (cuspHorizontalMeasure w).prod (cuspVerticalMeasure Y)

def cuspHorizontalMean (w : ℝ) (F : ℝ × ℝ → ℂ) (y : ℝ) : ℂ :=
  (w : ℂ)⁻¹ * ∫ t in Ioc 0 w, F (t, y)

def cuspAverageRepresentative (w : ℝ) (F : ℝ × ℝ → ℂ) (z : ℝ × ℝ) : ℂ :=
  cuspHorizontalMean w F z.2

def cuspMeanZeroRepresentative (w : ℝ) (F : ℝ × ℝ → ℂ) (z : ℝ × ℝ) : ℂ :=
  F z - cuspAverageRepresentative w F z

end ArtinMatthews
