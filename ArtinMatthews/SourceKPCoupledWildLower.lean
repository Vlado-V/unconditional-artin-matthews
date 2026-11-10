module

public import ArtinMatthews.SourceKPLocalRestCommute
public import ArtinMatthews.SourceKPWildCompactSupport
public import ArtinMatthews.StandardLocalConductor
public import ArtinMatthews.StandardLocalFourier
public import ArtinMatthews.SourceKPAdelicKernelContinuity
public import ArtinMatthews.SourceKPDeepIdealHaar
public import ArtinMatthews.SourceKPDeepLowerSupport
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
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual wild lower-root support criterion with an arbitrary
global remainder whose projective component at this place is trivial. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory SourcePhysical Set
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

local notation "L" => P.adicCompletion K
local notation "J₀" => sourceKPDeepIdealImage K P
local notation "q₀" => sourceKPAdelicProjectiveAt K hζ P

theorem sourceKPCoupledDeepIdeal_subset_integer_ball : J₀ ⊆ sourceLocalBall K P 0 := by
  rintro _ ⟨x, _, rfl⟩
  change sourceKPFiniteVal K P (x : L) ≤ WithZero.exp (0 : ℤ)
  rw [WithZero.exp_zero]
  exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K P).mp x.property

theorem sourceKPCoupledWildLower_indicator (hP : (6 : 𝓞 K) ∈ P.asIdeal) (s : ℂ)
    (r : SourceKPAdelicProjective K hζ) (hr : sourceKPAdelicLocalBase K hζ P r = 1) (x : L) :
    sourceKPAdelicCompactScalar K hζ s (sourceKPAdelicLowerAt K hζ P x * r) =
      (J₀).indicator (fun _ => sourceKPAdelicCompactScalar K hζ s r) x := by
  classical
  by_cases hx : x ∈ J₀
  · let k : sourceKPAdelicDeepCompact K hζ := ⟨sourceKPAdelicLowerAt K hζ P x,
      sourceKPAdelicLowerAt_mem_compact K hζ P hx⟩
    have hc : Commute (sourceKPAdelicLowerAt K hζ P x) r :=
      sourceKPAdelicLocalProjective_commute_of_base_one K hζ P _ r hr
    rw [Set.indicator_of_mem hx, hc.eq]
    exact sourceKPAdelicCompactScalar_right K hζ s r k
  · rw [Set.indicator_of_notMem hx]
    apply sourceKPAdelicCompactScalar_zero
    rintro ⟨b, k, he⟩
    obtain ⟨m, hm⟩ := k.property
    obtain ⟨kp, hkp⟩ := m.property.2 P hP
    obtain ⟨bp, hbp⟩ := sourceKPAdelicProjectiveAt_borel K hζ P b
    have h := congrArg q₀ he
    have hr' : q₀ r = 1 := hr
    change q₀ (sourceKPAdelicLocalProjective K hζ P
      (sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Lower x)) * r) = q₀ (b.val * k.val) at h
    rw [map_mul, map_mul, hr', mul_one, sourceKPAdelicProjectiveAt_local_same, hbp, ← hm,
      sourceKPAdelicProjectiveAt_deep_compact, ← hkp] at h
    exact hx ((sourceKPDeepLower_projective_iff K P x).mp ⟨bp, kp, h⟩)

theorem sourceKPCoupledWildLower_full_eq_unit (hP : (6 : 𝓞 K) ∈ P.asIdeal) (s : ℂ)
    (r : SourceKPAdelicProjective K hζ) (hr : sourceKPAdelicLocalBase K hζ P r = 1)
    (μ : Measure L) :
    (∫ x : L, sourceKPAdelicCompactScalar K hζ s (sourceKPAdelicLowerAt K hζ P x * r) ∂μ) =
      ∫ x : L in sourceLocalBall K P 0,
        sourceKPAdelicCompactScalar K hζ s (sourceKPAdelicLowerAt K hζ P x * r) ∂μ := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [sourceKPCoupledWildLower_indicator K hζ P hP s r hr,
    Set.indicator_of_notMem (fun h => hx (sourceKPCoupledDeepIdeal_subset_integer_ball K P h))]

theorem sourceKPCoupledWildLower_integral (hP : (6 : 𝓞 K) ∈ P.asIdeal) (s : ℂ)
    (r : SourceKPAdelicProjective K hζ) (hr : sourceKPAdelicLocalBase K hζ P r = 1)
    (μ : Measure L) :
    (∫ x : L, sourceKPAdelicCompactScalar K hζ s (sourceKPAdelicLowerAt K hζ P x * r) ∂μ) =
      (μ.real J₀ : ℂ) * sourceKPAdelicCompactScalar K hζ s r := by
  simp_rw [sourceKPCoupledWildLower_indicator K hζ P hP s r hr]
  rw [integral_indicator (sourceKPDeepIdealImage_isCompact K P).measurableSet, integral_const,
    Measure.real, Measure.restrict_apply_univ]
  rfl

end
end ArtinMatthews
