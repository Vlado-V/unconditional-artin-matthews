module

public import ArtinMatthews.SourceKPAdelicOutgoingContinuationSection
public import ArtinMatthews.SourceKPLocalCompactProductEvaluation
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

/-! Compact retained right translates of the actual regularized
section descend to the simultaneous genuine deep cosets as full
adelic section vectors. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K)))

local notation "Vₚ" => SourceKPAdelicPrincipalSeries K hζ
local notation "π" => sourceKPAdelicPrincipalSeriesRepresentation K hζ
local notation "D" => sourceKPAdelicDeepCompact K hζ
local notation "R" => sourceKPAdelicOutgoingRegularizedSection K hζ
local notation "Gₛ" => SourceKPLocalCompactProductGroup K hζ S
local notation "Cₛ" => SourceKPLocalCompactProductCompact K hζ S
local notation "Jₛ" => SourceKPLocalCompactProductDeep K hζ S
local notation "Qₛ" => SourceKPLocalCompactProductCosets K hζ S
local notation "L" => sourceKPLocalCompactProductLift K hζ S

local instance sourceKPAdelicOutgoingContinuedTranslateAddCommGroup (s : ℂ) :
    AddCommGroup (Vₚ s) := Submodule.addCommGroup _

def sourceKPAdelicOutgoingRegularizedCompactTranslate (s : ℂ) (hs : 0 < s.re) (q : Qₛ) : Vₚ (-s) :=
  π (-s) (L (fun P => (q P).out.val)) (R s hs)

local notation "tr" => sourceKPAdelicOutgoingRegularizedCompactTranslate K hζ S

theorem sourceKPAdelicOutgoingRegularizedCompactTranslate_apply (s : ℂ) (hs : 0 < s.re) (k : Cₛ) :
    tr s hs (fun P => QuotientGroup.mk (k P)) = π (-s) (L (fun P => (k P).val)) (R s hs) := by
  let q : Qₛ := fun P => QuotientGroup.mk (k P)
  choose j hj using fun P : S =>
    QuotientGroup.mk_out_eq_mul (s := sourceKPLocalCompactDeep K hζ P.val) (k P)
  let j₀ : Gₛ := fun P => (j P).val.val
  have he : (fun P : S => (q P).out.val) = (fun P : S => (k P).val)*j₀ := by
    funext P
    exact congrArg Subtype.val (hj P)
  let d : D := ⟨L j₀,sourceKPLocalCompactProductDeep_mem K hζ S j⟩
  apply Subtype.ext
  funext x
  let k₀ : Gₛ := fun P => (k P).val
  have hfix := congrArg (fun f : Vₚ (-s) => f.val (x*L k₀))
    (sourceKPAdelicOutgoingRegularizedSection_right K hζ s hs d)
  change (R s hs).val ((x*L k₀)*L j₀) = (R s hs).val (x*L k₀) at hfix
  have hx : x*L (fun P => (q P).out.val) = (x*L k₀)*L j₀ := by
    rw [he,map_mul L,mul_assoc]
  change (R s hs).val (x*L (fun P => (q P).out.val)) = (R s hs).val (x*L k₀)
  exact (congrArg (R s hs).val hx).trans hfix

def sourceKPAdelicOutgoingRegularizedCompactTranslateSpan (s : ℂ) (hs : 0 < s.re) : Submodule ℂ (Vₚ (-s)) :=
  Submodule.span ℂ (Set.range (tr s hs))

local notation "W" => sourceKPAdelicOutgoingRegularizedCompactTranslateSpan K hζ S

theorem sourceKPAdelicOutgoingRegularizedCompactTranslateSpan_finiteDimensional (s : ℂ) (hs : 0 < s.re) :
    FiniteDimensional ℂ (W s hs) := by
  let : Finite Qₛ := sourceKPLocalCompactProductCosets_finite K hζ S
  exact Module.Finite.span_of_finite ℂ (Set.finite_range (tr s hs))

theorem sourceKPAdelicOutgoingRegularizedCompactTranslateSpan_finrank_le (s : ℂ) (hs : 0 < s.re) :
    Module.finrank ℂ (W s hs) ≤ Nat.card Qₛ := by
  let : Finite Qₛ := sourceKPLocalCompactProductCosets_finite K hζ S
  let : Fintype Qₛ := Fintype.ofFinite _
  let : Fintype (Set.range (tr s hs)) := Fintype.ofFinite _
  refine (finrank_span_le_card (Set.range (tr s hs))).trans ?_
  rw [Set.toFinset_card,Nat.card_eq_fintype_card]
  convert Fintype.card_range_le (tr s hs)

theorem sourceKPAdelicOutgoingRegularizedCompactTranslateSpan_mem (s : ℂ) (hs : 0 < s.re) (k : Cₛ) :
    π (-s) (L (fun P => (k P).val)) (R s hs) ∈ W s hs := by
  rw [← sourceKPAdelicOutgoingRegularizedCompactTranslate_apply K hζ S s hs k]
  exact Submodule.subset_span ⟨_,rfl⟩

end
end ArtinMatthews
