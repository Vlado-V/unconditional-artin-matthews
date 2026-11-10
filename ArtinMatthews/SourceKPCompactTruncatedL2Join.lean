module

public import ArtinMatthews.SourceEisensteinHighRemainderContinuity
public import ArtinMatthews.SourceKPArchHaar
public import ArtinMatthews.SourceKPAutomorphicCompactTruncated
public import ArtinMatthews.SourceEisensteinHighOutgoingL2
public import ArtinMatthews.SourceKPArithmeticDiscreteness
public import ArtinMatthews.SourceKPAutomorphicHeightCompact
public import ArtinMatthews.SourceKPAutomorphicMeasureRegularity
public import ArtinMatthews.SourceKPCompactEisensteinContinuity
public import ArtinMatthews.SourceKPHighCuspMeasure
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Exact low-core and outgoing-term assembly for the initial truncated family. -/
namespace ArtinMatthews
open NumberField MeasureTheory Set Filter
open scoped NumberField MatrixGroups AdeleRing Topology ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "X" => SourceKPAutomorphicLevel K hζ
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "H" => sourceKPAutomorphicOrbitHeight K hζ
local notation "μX" => sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ)
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

theorem sourceKPHighCuspNonconstantEisenstein_include (s : ℂ) {T A : ℝ}
    (hT : 1 < T) (hA : 1 < A) (hTA : T ≤ A) (x : SourceKPHighCuspAutomorphic K hζ A) :
    sourceKPHighCuspNonconstantEisenstein K hζ s T hT ⟨x.val,hTA.trans_lt x.property⟩ =
      sourceKPHighCuspNonconstantEisenstein K hζ s A hA x := by
  obtain ⟨z,rfl⟩ := sourceKPHighCusp_representative K hζ A x
  rw [sourceKPHighCuspNonconstantEisenstein_rep]
  change sourceKPHighCuspNonconstantEisenstein K hζ s T hT
    (sourceKPHighCuspProjection K hζ T ⟨z.val,hTA.trans_lt z.property⟩) = _
  rw [sourceKPHighCuspNonconstantEisenstein_rep]

theorem sourceKPAutomorphicInitialDifference_memLp_of_high_remainder {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀) (T A : ℝ) (hT : 1 < T) (hA : 1 < A)
    (hTA : T ≤ A) (hcut : 2*T₀ ≤ A)
    (hR : MemLp (sourceKPHighRemainderExtension K hζ s T hT) 2
      (Measure.restrict μX {x | A < H x})) :
    MemLp (fun x : X => sourceKPAutomorphicEisenstein K hζ s x -
      sourceKPAutomorphicCutoffEisenstein K hζ T₀ s x) 2 μX := by
  let R := sourceKPHighRemainderExtension K hζ s T hT
  let M := sourceKPHighOutgoingExtension K hζ s A hA
  let S : Set X := {x | A < H x}
  let F : X → ℂ := fun x => sourceKPAutomorphicEisenstein K hζ s x -
    sourceKPAutomorphicCutoffEisenstein K hζ T₀ s x
  have hF : Continuous F := by
    have h := (sourceKPAutomorphicCompactTruncatedEisenstein_continuous K hζ (zero_lt_one.trans_le hT₀) hs).comp
      (sourceKPAutomorphicCompactMk_isOpenQuotientMap K hζ).continuous
    simpa only [Function.comp_def,sourceKPAutomorphicCompactTruncatedEisenstein_mk,F] using h
  have hs₀ : 0 < s.re := by
    have hdeg : 0 ≤ (Module.finrank ℚ K : ℝ) := Nat.cast_nonneg _
    push_cast at hs
    linarith
  have hS : MeasurableSet S := (sourceKPHighCuspAutomorphic_isOpen K hζ A).measurableSet
  have hM : MemLp M 2 (Measure.restrict μX S) := sourceKPHighOutgoingExtension_memLp K hζ hs₀ A hA
  have hHigh : MemLp F 2 (Measure.restrict μX S) := by
    apply MemLp.ae_eq ?_ (MemLp.add hR hM)
    filter_upwards [ae_restrict_mem hS] with x hx
    let y : SourceKPHighCuspAutomorphic K hζ A := ⟨x,hx⟩
    have hR' := sourceKPHighRemainderExtension_apply K hζ s T hT ⟨x,hTA.trans_lt hx⟩
    have hM' := sourceKPHighOutgoingExtension_apply K hζ s A hA y
    change R x = _ at hR'
    change M x = _ at hM'
    change R x+M x = F x
    rw [hR',hM',sourceKPHighCuspNonconstantEisenstein_include K hζ s hT hA hTA y]
    exact (sourceKPAutomorphicInitialDifference_high_split K hζ s T₀ A hT₀ hA hcut y).symm
  let C : Set X := {x | H x ≤ A}
  have hC : IsCompact C := sourceKPAutomorphicOrbitHeight_sublevel_isCompact K hζ A
  have hCm : MeasurableSet C := (sourceKPAutomorphicOrbitHeight_sublevel_closed K hζ A).measurableSet
  have hCf : μX C < ∞ := hC.measure_lt_top
  let : IsFiniteMeasure (Measure.restrict μX C) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hCf⟩
  obtain ⟨B,hB⟩ := hC.exists_bound_of_continuousOn hF.continuousOn
  have hLow : MemLp F 2 (Measure.restrict μX C) := by
    apply MemLp.of_bound hF.aestronglyMeasurable.restrict B
    filter_upwards [ae_restrict_mem hCm] with x hx
    exact hB x hx
  have hiC : IntegrableOn (fun x => ‖F x‖^2) C μX :=
    (memLp_two_iff_integrable_sq_norm hLow.aestronglyMeasurable).mp hLow
  have hiS : IntegrableOn (fun x => ‖F x‖^2) S μX :=
    (memLp_two_iff_integrable_sq_norm hHigh.aestronglyMeasurable).mp hHigh
  have hi := IntegrableOn.union hiC hiS
  have hUnion : C ∪ S = Set.univ := by
    ext x
    simp only [C,S,Set.mem_union,Set.mem_setOf_eq,Set.mem_univ,iff_true]
    exact le_or_gt _ _
  rw [hUnion,integrableOn_univ] at hi
  exact (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mpr hi

theorem sourceKPAutomorphicCompactTruncatedEisenstein_memLp_of_high_remainder {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀) (T A : ℝ) (hT : 1 < T) (hA : 1 < A)
    (hTA : T ≤ A) (hcut : 2*T₀ ≤ A)
    (hR : MemLp (sourceKPHighRemainderExtension K hζ s T hT) 2
      (Measure.restrict μX {x | A < H x})) :
    MemLp (sourceKPAutomorphicCompactTruncatedEisenstein K hζ T₀ s) 2 μY := by
  let f := sourceKPAutomorphicCompactTruncatedEisenstein K hζ T₀ s
  let m := sourceKPAutomorphicCompactMk K hζ
  have hm : Measurable m := sourceKPAutomorphicCompactMk_measurable K hζ
  have hf : Continuous f :=
    sourceKPAutomorphicCompactTruncatedEisenstein_continuous K hζ (zero_lt_one.trans_le hT₀) hs
  change MemLp f 2 (Measure.map m μX)
  apply (memLp_map_measure_iff hf.aestronglyMeasurable hm.aemeasurable).mpr
  simpa only [Function.comp_def,f,m,sourceKPAutomorphicCompactTruncatedEisenstein_mk] using
    sourceKPAutomorphicInitialDifference_memLp_of_high_remainder K hζ hs T₀ hT₀ T A hT hA hTA hcut hR

end
end ArtinMatthews
