module

public import ArtinMatthews.SpectralCuspLocalFourier
public import ArtinMatthews.SpectralCuspTwoCellMeasure
public import ArtinMatthews.SpectralCuspHyperbolicProjectionRepresentative
public import ArtinMatthews.SpectralCuspTwoCellFourier
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.UniformSpace.Uniformizable


set_option backward.privateInPublic true
@[expose] public section

/-! Exact measure transport from one period to the interior period of the
two-cell strip.  Translation and folding preserve the normalized coefficient. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal

namespace ArtinMatthews

theorem spectralIoc_add_preserving (a b c : ℝ) :
    MeasurePreserving (fun x : ℝ => x + c) (volume.restrict (Ioc a b))
      (volume.restrict (Ioc (a + c) (b + c))) := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) c).restrict_preimage
    (s := Ioc (a + c) (b + c)) measurableSet_Ioc
  have he : (fun x : ℝ => x + c) ⁻¹' Ioc (a + c) (b + c) = Ioc a b := by
    ext x
    simp only [mem_preimage, mem_Ioc, add_lt_add_iff_right, add_le_add_iff_right]
  rw [he] at h
  exact h

theorem spectralIoc_restrict_split (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
    volume.restrict (Ioc a c) = volume.restrict (Ioc a b) + volume.restrict (Ioc b c) := by
  have hu : Ioc a b ∪ Ioc b c = Ioc a c := by
    ext x
    simp only [mem_union, mem_Ioc]
    constructor
    · rintro (⟨h0,h1⟩ | ⟨h1,h2⟩) <;> constructor <;> linarith
    · rintro ⟨h0,h2⟩
      by_cases hx : x ≤ b
      · exact Or.inl ⟨h0,hx⟩
      · exact Or.inr ⟨lt_of_not_ge hx,h2⟩
  have hd : Disjoint (Ioc a b) (Ioc b c) :=
    disjoint_left.mpr fun _ hx hy => (not_lt_of_ge hx.2) hy.1
  rw [← hu, Measure.restrict_union hd measurableSet_Ioc]

def cuspInteriorHorizontalMeasure (w : ℝ) : Measure ℝ := volume.restrict (Ioc (w / 2) (3 * w / 2))

theorem cuspInteriorTranslate_preserving (w : ℝ) :
    MeasurePreserving (fun x : ℝ => x + w / 2) (cuspHorizontalMeasure w)
      (cuspInteriorHorizontalMeasure w) := by
  have h := spectralIoc_add_preserving 0 w (w / 2)
  simpa only [cuspHorizontalMeasure, cuspInteriorHorizontalMeasure,
    zero_add, show w + w / 2 = 3 * w / 2 by ring] using h

theorem cuspInteriorFold_preserving (w : ℝ) (hw : 0 < w) :
    MeasurePreserving (spectralTwoCellFold w) (cuspInteriorHorizontalMeasure w)
      (cuspHorizontalMeasure w) := by
  have hfirst : Measure.map (spectralTwoCellFold w) (volume.restrict (Ioc (w / 2) w)) =
      volume.restrict (Ioc (w / 2) w) := by
    calc
      _ = Measure.map id (volume.restrict (Ioc (w / 2) w)) := Measure.map_congr (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        exact spectralTwoCellFold_first hx.2)
      _ = _ := Measure.map_id
  have hsecond : Measure.map (spectralTwoCellFold w) (volume.restrict (Ioc w (3 * w / 2))) =
      volume.restrict (Ioc 0 (w / 2)) := by
    have ht := spectralIoc_add_preserving w (3 * w / 2) (-w)
    have ht' : MeasurePreserving (fun x : ℝ => x - w)
        (volume.restrict (Ioc w (3 * w / 2))) (volume.restrict (Ioc 0 (w / 2))) := by
      simpa only [sub_eq_add_neg, add_neg_cancel, show 3 * w / 2 + -w = w / 2 by ring] using ht
    calc
      _ = Measure.map (fun x : ℝ => x - w) (volume.restrict (Ioc w (3 * w / 2))) :=
        Measure.map_congr (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
          exact spectralTwoCellFold_second hx.1)
      _ = _ := ht'.map_eq
  refine ⟨spectralTwoCellFold_measurable w, ?_⟩
  rw [cuspInteriorHorizontalMeasure,
    spectralIoc_restrict_split (w / 2) w (3 * w / 2) (by linarith) (by linarith),
    Measure.map_add _ _ (spectralTwoCellFold_measurable w), hfirst, hsecond, add_comm]
  exact (spectralIoc_restrict_split 0 (w / 2) w (by linarith) (by linarith)).symm

theorem cuspInteriorRotation_preserving (w : ℝ) (hw : 0 < w) :
    MeasurePreserving (fun x : ℝ => spectralTwoCellFold w (x + w / 2))
      (cuspHorizontalMeasure w) (cuspHorizontalMeasure w) :=
  (cuspInteriorFold_preserving w hw).comp (cuspInteriorTranslate_preserving w)

theorem cuspInteriorTranslate_product_preserving (w Y : ℝ) :
    MeasurePreserving (fun p : ℝ × ℝ => (p.1 + w / 2, p.2)) (cuspStripMeasure w Y)
      ((cuspInteriorHorizontalMeasure w).prod (cuspVerticalMeasure Y)) :=
  (cuspInteriorTranslate_preserving w).prod (MeasurePreserving.id _)

theorem cuspInteriorMeasure_le_twoCell (w Y : ℝ) (hw : 0 < w) :
    (cuspInteriorHorizontalMeasure w).prod (cuspVerticalMeasure Y) ≤ cuspStripMeasure (2 * w) Y :=
  Measure.prod_mono (Measure.restrict_mono_set _ (by
    intro x hx
    constructor <;> linarith [hx.1, hx.2])) le_rfl

theorem cuspInteriorFourierCoefficient_congr_ae (w Y : ℝ) (hw : 0 < w) (n : ℤ)
    {F G : ℝ × ℝ → ℂ} (hFG : F =ᵐ[cuspStripMeasure (2 * w) Y] G) :
    cuspInteriorFourierCoefficient w n F =ᵐ[cuspVerticalMeasure Y]
      cuspInteriorFourierCoefficient w n G := by
  have h := (cuspInteriorTranslate_product_preserving w Y).quasiMeasurePreserving.ae_eq_comp
    (hFG.filter_mono (ae_mono (cuspInteriorMeasure_le_twoCell w Y hw)))
  have hm := cuspHorizontalMean_congr_ae w Y (by
    filter_upwards [h] with p hp
    exact congrArg (fun z => cuspFourierPhase w n p.1 * z) hp)
  exact hm.mono fun y hy => congrArg (fun z => cuspFourierPhase w n (w / 2) * z) hy

theorem cuspInteriorFourierCoefficient_fold (w : ℝ) (hw : 0 < w) (n : ℤ)
    (F : ℝ × ℝ → ℂ) (y : ℝ)
    (hF : AEStronglyMeasurable (fun x => F (x, y)) (cuspHorizontalMeasure w)) :
    cuspInteriorFourierCoefficient w n (fun p => F (spectralTwoCellFold w p.1, p.2)) y =
      cuspHorizontalWeightedMean w (cuspFourierPhase w n) F y := by
  have hm := cuspInteriorRotation_preserving w hw
  have hmeas : AEStronglyMeasurable (fun x => cuspFourierPhase w n x * F (x, y))
      (cuspHorizontalMeasure w) :=
    (cuspFourierPhase_contDiff w n).continuous.aestronglyMeasurable.mul hF
  have hmap : AEStronglyMeasurable (fun x => cuspFourierPhase w n x * F (x, y))
      (Measure.map (fun x => spectralTwoCellFold w (x + w / 2)) (cuspHorizontalMeasure w)) := by
    rwa [hm.map_eq]
  have he := (integral_map hm.aemeasurable hmap).symm
  rw [hm.map_eq] at he
  simp only [cuspFourierPhase_fold w hw n, cuspFourierPhase_add] at he
  unfold cuspInteriorFourierCoefficient cuspHorizontalWeightedMean cuspHorizontalMean
  change cuspFourierPhase w n (w / 2) *
    ((w : ℂ)⁻¹ * ∫ x, cuspFourierPhase w n x * F (spectralTwoCellFold w (x + w / 2), y)
      ∂cuspHorizontalMeasure w) = _
  have he' : (∫ x, cuspFourierPhase w n (w / 2) *
      (cuspFourierPhase w n x * F (spectralTwoCellFold w (x + w / 2), y))
        ∂cuspHorizontalMeasure w) =
      ∫ x, cuspFourierPhase w n x * F (x, y) ∂cuspHorizontalMeasure w := by
    convert he using 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  calc
    _ = (w : ℂ)⁻¹ * (∫ x, cuspFourierPhase w n (w / 2) *
        (cuspFourierPhase w n x * F (spectralTwoCellFold w (x + w / 2), y))
          ∂cuspHorizontalMeasure w) := by rw [integral_const_mul]; ring
    _ = _ := by rw [he']; rfl

end ArtinMatthews
