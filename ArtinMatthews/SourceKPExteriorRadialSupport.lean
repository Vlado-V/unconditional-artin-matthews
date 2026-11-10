module

public import ArtinMatthews.SourceKPHighCuspMeasure
public import ArtinMatthews.SourceKPRadialHighFlow
public import ArtinMatthews.SourceExteriorRadialWindow
public import ArtinMatthews.SourceKPHighCuspRadialMeasure
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


set_option backward.privateInPublic true
@[expose] public section

/-! Compact support and norm scaling for the actual exterior radial curve. -/
namespace ArtinMatthews
open NumberField Matrix Topology Filter Set MeasureTheory
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPHighCuspRadialValue_threshold (t T U : ℝ) (hT : 1 < T) (hU : 1 < U)
    (q : SourceKPHighCuspAutomorphic K hζ T) (r : SourceKPHighCuspAutomorphic K hζ U)
    (he : q.val = r.val) :
    sourceKPHighCuspRadialValue K hζ t T hT q = sourceKPHighCuspRadialValue K hζ t U hU r := by
  have hr : U < sourceKPAutomorphicOrbitHeight K hζ q.val := he.symm ▸ r.property
  let p : SourceKPHighCuspAutomorphic K hζ (max T U) :=
    ⟨q.val,max_lt_iff.mpr ⟨q.property,hr⟩⟩
  obtain ⟨x,hx⟩ := sourceKPHighCusp_representative K hζ (max T U) p
  let xT : SourceKPHighCuspFinite K hζ T := ⟨x.val,(le_max_left T U).trans_lt x.property⟩
  let xU : SourceKPHighCuspFinite K hζ U := ⟨x.val,(le_max_right T U).trans_lt x.property⟩
  have hxval := congrArg Subtype.val hx
  have hTq : sourceKPHighCuspProjection K hζ T xT = q := Subtype.ext hxval
  have hUr : sourceKPHighCuspProjection K hζ U xU = r := Subtype.ext (hxval.trans he)
  rw [← hTq, ← hUr, sourceKPHighCuspRadialValue_rep, sourceKPHighCuspRadialValue_rep]

theorem sourceKPHighCuspRadialValue_measurable (t T : ℝ) (hT : 1 < T) :
    Measurable (sourceKPHighCuspRadialValue K hζ t T hT) := by
  have harg : Continuous (fun q : SourceKPHighCuspAutomorphic K hζ T => (t,q)) :=
    continuous_const.prodMk continuous_id
  have h := (sourceKPHighCuspRadialValue_continuous K hζ T hT).comp harg
  simpa only [Function.comp_def] using h.measurable

theorem sourceKPHighCuspMeasure_val_preserving (T : ℝ) :
    MeasurePreserving (Subtype.val : SourceKPHighCuspAutomorphic K hζ T → SourceKPAutomorphicLevel K hζ)
      (sourceKPHighCuspMeasure K hζ T)
      ((sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ)).restrict
        {x | T < sourceKPAutomorphicOrbitHeight K hζ x}) :=
  ⟨measurable_subtype_coe,sourceKPHighCuspMeasure_map_val K hζ T⟩

theorem sourceKPExteriorRadial_threshold_window (T : ℝ) (hT : 1 < T)
    {f : SourceKPAutomorphicLevel K hζ → ℂ} (hc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ {x | T < sourceKPAutomorphicOrbitHeight K hζ x}) :
    ∀ᶠ t : ℝ in 𝓝 0, 1 < sourceKPRadialHeightScale K t*T ∧
      tsupport f ⊆ {x | sourceKPRadialHeightScale K t*T < sourceKPAutomorphicOrbitHeight K hζ x} := by
  simpa only [sourceKPRadialHeightScale_eq_nrComplex K hζ] using
    sourceKPAutomorphic_radial_threshold_window K hζ T hT hc hsupp

theorem sourceKPExteriorRadial_compact_hull (T : ℝ) (hT : 1 < T)
    {f : SourceKPAutomorphicLevel K hζ → ℂ} (hc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ {x | T < sourceKPAutomorphicOrbitHeight K hζ x}) :
    ∃ s : Set ℝ, s ∈ 𝓝 0 ∧ ∃ C : Set (SourceKPAutomorphicLevel K hζ),
      IsCompact C ∧ ∀ t ∈ s, ∀ q : SourceKPHighCuspAutomorphic K hζ T,
        f (sourceKPHighCuspRadialValue K hζ t T hT q) ≠ 0 → q.val ∈ C := by
  obtain ⟨ε,hε,hwin⟩ := Metric.mem_nhds_iff.mp
    (sourceKPExteriorRadial_threshold_window K hζ T hT hc hsupp)
  let s := Metric.closedBall (0 : ℝ) (ε/2)
  have hs : s ∈ 𝓝 (0 : ℝ) := Metric.closedBall_mem_nhds 0 (half_pos hε)
  have hsb : s ⊆ Metric.ball 0 ε := Metric.closedBall_subset_ball (half_lt_self hε)
  let S : Set (SourceKPHighCuspAutomorphic K hζ T) := Subtype.val ⁻¹' tsupport f
  have hS : IsCompact S := IsInducing.subtypeVal.isCompact_preimage' hc (by
    intro x hx
    exact ⟨⟨x,hsupp hx⟩,rfl⟩)
  let F : ℝ × SourceKPHighCuspAutomorphic K hζ T → SourceKPAutomorphicLevel K hζ :=
    fun p => sourceKPHighCuspRadialValue K hζ (-p.1) T hT p.2
  have hF : Continuous F := by
    have harg : Continuous (fun p : ℝ × SourceKPHighCuspAutomorphic K hζ T => (-p.1,p.2)) :=
      continuous_fst.neg.prodMk continuous_snd
    have h := (sourceKPHighCuspRadialValue_continuous K hζ T hT).comp harg
    simpa only [F, Function.comp_def] using h
  refine ⟨s,hs,F '' (s ×ˢ S),((isCompact_closedBall _ _).prod hS).image hF,?_⟩
  intro t ht q hq
  have htT : 1 < sourceKPRadialHeightScale K t*T := (hwin (hsb ht)).1
  have hmem : sourceKPHighCuspRadialValue K hζ t T hT q ∈ tsupport f := subset_tsupport _ hq
  let r : SourceKPHighCuspAutomorphic K hζ T :=
    ⟨sourceKPHighCuspRadialValue K hζ t T hT q,hsupp hmem⟩
  let u := sourceKPHighCuspRadialHomeomorph K hζ t T hT htT q
  have hru : r.val = u.val := (sourceKPHighCuspRadialHomeomorph_value K hζ t T hT htT q).symm
  refine ⟨(t,r),⟨ht,hmem⟩,?_⟩
  change sourceKPHighCuspRadialValue K hζ (-t) T hT r = q.val
  rw [sourceKPHighCuspRadialValue_threshold K hζ (-t) T _ hT htT r u hru]
  simpa only [u,neg_add_cancel,sourceKPHighCuspRadialValue_zero] using
    sourceKPHighCuspRadialValue_add K hζ (-t) t T hT htT q

theorem sourceKPExteriorRadial_normSq_integral_eventually (T : ℝ) (hT : 1 < T)
    {f : SourceKPAutomorphicLevel K hζ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ {x | T < sourceKPAutomorphicOrbitHeight K hζ x}) :
    ∀ᶠ t : ℝ in 𝓝 0,
      (∫ q, ‖f (sourceKPHighCuspRadialValue K hζ t T hT q)‖^2 ∂sourceKPHighCuspMeasure K hζ T) =
        sourceKPRadialHeightScale K t *
          ∫ x, ‖f x‖^2 ∂sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ) := by
  let φ : SourceKPAutomorphicLevel K hζ → ℝ := fun x => ‖f x‖^2
  have hφ : Continuous φ := hf.norm.pow 2
  filter_upwards [sourceKPExteriorRadial_threshold_window K hζ T hT hc hsupp] with t ht
  have hm := sourceKPHighCuspRadialValue_measurable K hζ t T hT
  have hzero : ∀ x, x ∉ {x | sourceKPRadialHeightScale K t*T < sourceKPAutomorphicOrbitHeight K hζ x} →
      φ x = 0 := by
    intro x hx
    have hx0 : f x = 0 := by
      by_contra hn
      exact hx (ht.2 (subset_tsupport _ hn))
    simp [φ,hx0]
  calc
    _ = ∫ x, φ x ∂Measure.map (sourceKPHighCuspRadialValue K hζ t T hT) (sourceKPHighCuspMeasure K hζ T) :=
      (integral_map hm.aemeasurable hφ.aestronglyMeasurable).symm
    _ = _ := by
      rw [sourceKPHighCuspRadialValue_map_measure K hζ t T hT ht.1,
        integral_smul_measure, ENNReal.toReal_ofReal (sourceKPRadialHeightScale_pos K t).le,
        setIntegral_eq_integral_of_forall_compl_eq_zero hzero, smul_eq_mul]

end
end ArtinMatthews
