module

public import ArtinMatthews.SourceKPCuspFiniteFiberCover
public import ArtinMatthews.SourceKPCuspRepresentativeHaar
public import ArtinMatthews.SourceKPCuspFundamentalSection
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


set_option backward.privateInPublic true
@[expose] public section

/-! The measurable exact high section can be chosen in the same fixed finite
set of actual level fibers at every height. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCuspFixedFiniteFibers_exists_section (v₀ : InfinitePlace K) (T : ℝ) :
    ∃ F : Set (SourceKPHighCuspFinite K hζ T),
      MeasurableSet F ∧
      (∀ x ∈ F, x.val.2 ∈ sourceKPCuspFixedFiniteFibers K hζ v₀) ∧
      Set.InjOn (sourceKPHighCuspProjection K hζ T) F ∧
      sourceKPHighCuspProjection K hζ T '' F = Set.univ := by
  let C : Set (SourceKPHighCuspFinite K hζ T) :=
    {x | x.val.2 ∈ sourceKPCuspFixedFiniteFibers K hζ v₀}
  have hc : MeasurableSet C := by
    have h : Continuous (fun x : SourceKPHighCuspFinite K hζ T => x.val.2) :=
      continuous_snd.comp continuous_subtype_val
    exact (isOpen_discrete (sourceKPCuspFixedFiniteFibers K hζ v₀)).measurableSet.preimage h.measurable
  have hcover : sourceKPHighCuspProjection K hζ T '' C = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨x,hx⟩ := sourceKPHighCusp_representative K hζ T q
    obtain ⟨γ,hγ⟩ := sourceKPCuspFixedFiniteFibers_representative K hζ v₀ T x
    exact ⟨γ • x,hγ,(sourceKPCuspHighProjection_rational K hζ T γ x).trans hx⟩
  obtain ⟨F,hF,hsub,hinj,hproj⟩ := sourceKPCuspHighProjection_exists_section K hζ T C hc hcover
  exact ⟨F,hF,fun x hx => hsub hx,hinj,hproj⟩

end
end ArtinMatthews
