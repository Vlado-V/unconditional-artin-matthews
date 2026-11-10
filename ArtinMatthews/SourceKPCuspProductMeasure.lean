module

public import ArtinMatthews.SourceKPCuspProductCoordinates
public import ArtinMatthews.SourceFiniteDensityProduct
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The native hyperbolic product measure in the actual Minkowski cusp
coordinates has horizontal Lebesgue measure and the literal positive height
density, up to one positive Haar scalar. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Module.Free MeasureTheory Set
open OAI.CubicEisenstein SourceHyperbolicGreen MeasureTheory.Measure
open scoped NumberField AdeleRing ENNReal NNReal BigOperators
noncomputable section

/-- The one-place positive height measure in the native chart. -/
def sourceKPCuspHeightMeasure : Measure ℝ :=
  ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).withDensity
    (fun y => ENNReal.ofReal ((y ^ 3)⁻¹))

instance sourceKPCuspHeightMeasure_sigmaFinite : SigmaFinite sourceKPCuspHeightMeasure := by
  unfold sourceKPCuspHeightMeasure
  infer_instance

def sourceKPCuspProductHeightMeasure (K : Type) [Field K] [NumberField K] :
    Measure (InfinitePlace K → ℝ) :=
  Measure.pi (fun _ => sourceKPCuspHeightMeasure)

instance sourceKPCuspProductHeightMeasure_sigmaFinite (K : Type) [Field K] [NumberField K] :
    SigmaFinite (sourceKPCuspProductHeightMeasure K) := by
  unfold sourceKPCuspProductHeightMeasure
  infer_instance

private def heightPositive (ι : Type*) : Set (ι → ℝ) :=
  Set.univ.pi (fun _ => Ioi (0 : ℝ))

private def heightPiDensity {ι : Type*} [Fintype ι] (y : ι → ℝ) : ℝ≥0∞ :=
  ∏ v, ENNReal.ofReal (((y v) ^ 3)⁻¹)

private theorem heightDensity_measurable :
    Measurable (fun y : ℝ => ENNReal.ofReal ((y ^ 3)⁻¹)) := by fun_prop

private theorem heightPiDensity_measurable (ι : Type*) [Fintype ι] :
    Measurable (heightPiDensity (ι := ι)) := by
  unfold heightPiDensity
  apply Finset.measurable_prod
  intro v _
  exact heightDensity_measurable.comp (measurable_pi_apply v)

private theorem productHeightMeasure_eq_density (K : Type) [Field K] [NumberField K] :
    sourceKPCuspProductHeightMeasure K =
      Measure.withDensity
        ((volume : Measure (InfinitePlace K → ℝ)).restrict (heightPositive (InfinitePlace K)))
        (heightPiDensity (ι := InfinitePlace K)) := by
  have h := @finite_pi_withDensity (InfinitePlace K) ℝ _ _
    (fun _ => (volume : Measure ℝ).restrict (Ioi (0 : ℝ))) (fun _ => inferInstance)
    (fun _ y => ENNReal.ofReal ((y ^ 3)⁻¹)) (fun _ => heightDensity_measurable)
    (fun _ => inferInstanceAs (SigmaFinite sourceKPCuspHeightMeasure))
  rw [← Measure.restrict_pi_pi] at h
  exact h

private theorem map_withDensity_comp_equiv {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    (e : X ≃ᵐ Z) (μ : Measure X) (g : Z → ℝ≥0∞) (hg : Measurable g) :
    Measure.map e (μ.withDensity (g ∘ e)) = (Measure.map e μ).withDensity g := by
  ext S hS
  rw [Measure.map_apply e.measurable hS, withDensity_apply _ (e.measurable hS),
    withDensity_apply _ hS, Measure.restrict_map e.measurable hS]
  exact (lintegral_map hg e.measurable).symm

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0)

local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K
local notation "X" => (I → ℝ)
local notation "Y" => (V → ℝ)
local notation "e" => sourceKPCuspProductCoordinates K hζ d hd

/-- The inverse native chart pushes the actual hyperbolic product measure
to a positive finite multiple of horizontal Lebesgue measure times the
product of the positive height measures. -/
theorem sourceKPCuspProductCoordinates_map_productVolume :
    ∃ c : ℝ≥0, 0 < c ∧
      Measure.map (e).symm (productVolume V) =
        (c : ℝ≥0∞) • (volume : Measure X).prod (sourceKPCuspProductHeightMeasure K) := by
  let E := (e).toHomeomorph.toMeasurableEquiv
  let μ : Measure (ProductSpace V) := volume
  let ν : Measure (X × Y) := (volume : Measure X).prod (volume : Measure Y)
  let P : Set Y := heightPositive V
  let S : Set (X × Y) := Set.univ ×ˢ P
  have hP : MeasurableSet P := MeasurableSet.univ_pi fun _ => measurableSet_Ioi
  have hS : MeasurableSet S := MeasurableSet.univ.prod hP
  have : IsAddHaarMeasure (μ.map E.symm) := (e).symm.isAddHaarMeasure_map μ
  have : IsAddHaarMeasure (volume : Measure X) := isAddHaarMeasure_volume_pi I
  have : IsAddHaarMeasure (volume : Measure Y) := isAddHaarMeasure_volume_pi V
  have : IsAddHaarMeasure ν :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure X) (volume : Measure Y)
  let c := addHaarScalarFactor (μ.map E.symm) ν
  have hc : 0 < c := addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hbase : μ.map E.symm = (c : ℝ≥0∞) • ν := isAddLeftInvariant_eq_smul _ _
  have hpre : e ⁻¹' productUpper V = S := by
    ext a
    rcases a with ⟨x, y⟩
    simp only [mem_preimage, productUpper, heightPositive, S, P, mem_prod, mem_univ,
      true_and, mem_pi, euclideanUpperHalf, mem_ofPred_eq, mem_Ioi,
      sourceKPCuspProductCoordinates_height]
  have hU : productUpper V = E.symm ⁻¹' S := by
    rw [← hpre]
    ext p
    change p ∈ productUpper V ↔ e ((e).symm p) ∈ productUpper V
    rw [(e).apply_symm_apply]
  have hden (a : X × Y) : productDensity (e a) = heightPiDensity a.2 := by
    rcases a with ⟨x, y⟩
    simp only [productDensity, hyperbolicDensity, heightPiDensity,
      sourceKPCuspProductCoordinates_height]
  have hD : productDensity (ι := V) = ((heightPiDensity (ι := V)) ∘ Prod.snd) ∘ E.symm := by
    funext p
    have hp := hden ((e).symm p)
    rw [(e).apply_symm_apply] at hp
    exact hp
  have hR : Measure.map E.symm (μ.restrict (productUpper V)) =
      (c : ℝ≥0∞) • (volume : Measure X).prod ((volume : Measure Y).restrict P) := by
    rw [hU, ← Measure.restrict_map E.symm.measurable hS, hbase,
      Measure.restrict_smul]
    change (c : ℝ≥0∞) •
        ((volume : Measure X).prod (volume : Measure Y)).restrict (Set.univ ×ˢ P) = _
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  refine ⟨c, hc, ?_⟩
  change Measure.map E.symm (productVolume V) = _
  rw [productVolume_eq_density, hD,
    map_withDensity_comp_equiv E.symm _
      ((heightPiDensity (ι := V)) ∘ Prod.snd) ((heightPiDensity_measurable V).comp measurable_snd)]
  change (Measure.map E.symm (μ.restrict (productUpper V))).withDensity
    (fun a : X × Y => heightPiDensity a.2) = _
  rw [hR, withDensity_smul_measure, ← prod_withDensity_right (heightPiDensity_measurable V),
    productHeightMeasure_eq_density K]

/-- Restricting to a horizontal set and a height set preserves the same Haar scalar. -/
theorem sourceKPCuspProductCoordinates_map_restrict
    (c : ℝ≥0)
    (h : Measure.map (e).symm (productVolume V) =
      (c : ℝ≥0∞) • (volume : Measure X).prod (sourceKPCuspProductHeightMeasure K))
    (S : Set X) (B : Set Y) (hS : MeasurableSet S) (hB : MeasurableSet B) :
    Measure.map (e).symm ((productVolume V).restrict ((e).symm ⁻¹' (S ×ˢ B))) =
      (c : ℝ≥0∞) • ((volume : Measure X).restrict S).prod
        ((sourceKPCuspProductHeightMeasure K).restrict B) := by
  rw [← Measure.restrict_map (e).symm.continuous.measurable (hS.prod hB), h,
    Measure.restrict_smul, ← Measure.prod_restrict]

/-- Restricting the horizontal coordinate preserves the same Haar scalar. -/
theorem sourceKPCuspProductCoordinates_map_restrict_horizontal
    (c : ℝ≥0)
    (h : Measure.map (e).symm (productVolume V) =
      (c : ℝ≥0∞) • (volume : Measure X).prod (sourceKPCuspProductHeightMeasure K))
    (S : Set X) (hS : MeasurableSet S) :
    Measure.map (e).symm ((productVolume V).restrict ((e).symm ⁻¹' (S ×ˢ (Set.univ : Set Y)))) =
      (c : ℝ≥0∞) • ((volume : Measure X).restrict S).prod (sourceKPCuspProductHeightMeasure K) := by
  rw [sourceKPCuspProductCoordinates_map_restrict K hζ d hd c h S Set.univ hS MeasurableSet.univ,
    Measure.restrict_univ]

/-- The scaled principal cell uses the half-open interval `(0,1]` in each
horizontal coordinate, with the same scalar on every measurable height band. -/
theorem sourceKPCuspProductCoordinates_map_restrict_unitCell
    (c : ℝ≥0)
    (h : Measure.map (e).symm (productVolume V) =
      (c : ℝ≥0∞) • (volume : Measure X).prod (sourceKPCuspProductHeightMeasure K))
    (B : Set Y) (hB : MeasurableSet B) :
    Measure.map (e).symm ((productVolume V).restrict ((e).symm ⁻¹'
      ((Set.univ.pi fun _ : I => Ioc (0 : ℝ) 1) ×ˢ B))) =
      (c : ℝ≥0∞) • (Measure.pi fun _ : I => (volume : Measure ℝ).restrict (Ioc 0 1)).prod
        ((sourceKPCuspProductHeightMeasure K).restrict B) := by
  rw [sourceKPCuspProductCoordinates_map_restrict K hζ d hd c h _ B
    (MeasurableSet.univ_pi fun _ => measurableSet_Ioc) hB]
  rw [← Measure.restrict_pi_pi]
  rfl

end
end ArtinMatthews
