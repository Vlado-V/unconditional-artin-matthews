module

public import ArtinMatthews.SourceKPAdelicCompactSection
public import ArtinMatthews.SourceKPFiniteUnipotentCompact
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


set_option backward.privateInPublic true
@[expose] public section

/-! Local constancy in the finite unipotent variable of the actual
adelic compact section, and Borel measurability of its scalar
coordinate. The covering group is used only algebraically. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Topology MeasureTheory
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "G₀" => SourceKPAdelicProjective K hζ
local notation "n₀" => fun t : 𝔸ᶠ[K] => sourceKPAdelicUpperLift K hζ ((0, t) : 𝔸[K])

theorem sourceKPAdelicCompactSection_eval_right (s : ℂ)
    (k : sourceKPAdelicDeepCompact K hζ) (a : G₀) :
    (sourceKPAdelicCompactSection K hζ s).val (a * k.val) =
      (sourceKPAdelicCompactSection K hζ s).val a :=
  congrArg (fun f : SourceKPAdelicPrincipalSeries K hζ s => f.val a)
    (sourceKPAdelicCompactSection_right K hζ s k)

theorem sourceKPAdelicCompactSection_finite_shift (s : ℂ) (a g : G₀) (y t : 𝔸ᶠ[K])
    (ht : g⁻¹ * n₀ t * g ∈ sourceKPAdelicDeepCompact K hζ) :
    (sourceKPAdelicCompactSection K hζ s).val (a * n₀ (y + t) * g) =
      (sourceKPAdelicCompactSection K hζ s).val (a * n₀ y * g) := by
  have hp : ((0, y) : 𝔸[K]) + (0, t) = (0, y + t) := by
    apply Prod.ext
    · exact zero_add 0
    · rfl
  have hn : n₀ (y + t) = n₀ y * n₀ t :=
    (congrArg (sourceKPAdelicUpperLift K hζ) hp).symm.trans
      (sourceKPAdelicUpperLift_add K hζ ((0, y) : 𝔸[K]) ((0, t) : 𝔸[K]))
  have hm : (a * n₀ y * g) * (g⁻¹ * n₀ t * g) = a * n₀ (y + t) * g := by
    calc
      _ = a * (n₀ y * n₀ t) * g := by simp only [mul_assoc, mul_inv_cancel_left]
      _ = _ := congrArg (fun b : G₀ => a * b * g) hn.symm
  have h := sourceKPAdelicCompactSection_eval_right K hζ s
    ⟨g⁻¹ * n₀ t * g, ht⟩ (a * n₀ y * g)
  exact (congrArg (sourceKPAdelicCompactSection K hζ s).val hm).symm.trans h

theorem sourceKPAdelicCompactSection_finite_locallyConstant (s : ℂ) (a g : G₀) :
    IsLocallyConstant (fun t : 𝔸ᶠ[K] =>
      (sourceKPAdelicCompactSection K hζ s).val (a * n₀ t * g)) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro y
  have hs : ∀ᶠ t : 𝔸ᶠ[K] in nhds 0,
      (sourceKPAdelicCompactSection K hζ s).val (a * n₀ (y + t) * g) =
        (sourceKPAdelicCompactSection K hζ s).val (a * n₀ y * g) := by
    filter_upwards [sourceKPAdelicFiniteConjugate_eventually_compact K hζ g] with t ht
    exact sourceKPAdelicCompactSection_finite_shift K hζ s a g y t ht
  have ht : Filter.Tendsto (fun z : 𝔸ᶠ[K] => z - y) (nhds y) (nhds 0) := by
    have hc : Continuous (fun z : 𝔸ᶠ[K] => z - y) := continuous_id.sub continuous_const
    simpa only [sub_self] using hc.tendsto y
  filter_upwards [ht.eventually hs] with z hz
  have he : y + (z - y) = z := by abel
  exact (congrArg (fun t : 𝔸ᶠ[K] => (sourceKPAdelicCompactSection K hζ s).val (a * n₀ t * g)) he).symm.trans hz

theorem sourceKPAdelicCompactScalar_finite_locallyConstant (s : ℂ) (a g : G₀) :
    IsLocallyConstant (fun t : 𝔸ᶠ[K] => sourceKPAdelicCompactScalar K hζ s (a * n₀ t * g)) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro y
  filter_upwards [(sourceKPAdelicCompactSection_finite_locallyConstant K hζ s a g).eventually_eq y] with z hz
  exact congrArg (fun v : SourceKPAdelicTorusInducedSpace K hζ s => v.val 1) hz

theorem sourceKPAdelicCompactScalar_finite_continuous (s : ℂ) (a g : G₀) :
    Continuous (fun t : 𝔸ᶠ[K] => sourceKPAdelicCompactScalar K hζ s (a * n₀ t * g)) :=
  (sourceKPAdelicCompactScalar_finite_locallyConstant K hζ s a g).continuous

theorem sourceKPAdelicCompactScalar_finite_borelMeasurable (s : ℂ) (a g : G₀) :
    @Measurable 𝔸ᶠ[K] ℂ (borel 𝔸ᶠ[K]) (borel ℂ)
      (fun t : 𝔸ᶠ[K] => sourceKPAdelicCompactScalar K hζ s (a * n₀ t * g)) :=
  (sourceKPAdelicCompactScalar_finite_continuous K hζ s a g).borel_measurable

end
end ArtinMatthews
