module

public import ArtinMatthews.SourceKPLocalNegativeCyclicRelation
public import ArtinMatthews.SourceFiniteFiberScattering
public import ArtinMatthews.SourceFiniteWindowStep
public import ArtinMatthews.SourceFiniteIntertwinerFubini
public import ArtinMatthews.SourceFiniteWindowHolomorphic
public import ArtinMatthews.SourceKPFiniteCyclicFiber
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

/-! The finite-window scattering residue respects every relation in the
actual local negative cyclic representation. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical
open scoped NumberField AdeleRing Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local instance cyclicWindowFiniteMeasurable : MeasurableSpace 𝔸ᶠ[K] := borel _
local instance cyclicWindowFiniteBorel : BorelSpace 𝔸ᶠ[K] := ⟨rfl⟩
local instance cyclicWindowCompletionMeasurable (P : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (P.adicCompletion K) := borel _
local instance cyclicWindowCompletionBorel (P : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (P.adicCompletion K) := ⟨rfl⟩

local notation "Places" => HeightOneSpectrum (𝓞 K)

theorem sourceKPFiniteWindow_integral_full_of_integrableOn (S : Finset Places)
    (P : Places) (hP : P ∈ S) (f : 𝔸ᶠ[K] → ℂ)
    (hf : IntegrableOn f (sourceKPFiniteWindow K S) (sourceKPFiniteStandardHaar K)) :
    sourceKPFiniteWindowIntegral K f S =
      ∫ r in sourceKPFiniteWindowRemainderSet K P S,
        (∫ x : P.adicCompletion K, f (sourceKPFiniteAdditiveSingle K P x + r.val)
          ∂sourceJacquetHaar K P) ∂sourceKPFinitePlaceRemainderStandardHaar K P := by
  have hS := (sourceKPFiniteWindow_isClosed K S).measurableSet
  have h := sourceKPFiniteStandardHaar_integral_place K P ((sourceKPFiniteWindow K S).indicator f)
    ((integrable_indicator_iff hS).mpr hf)
  rw [integral_indicator hS] at h
  simp_rw [sourceKPFiniteWindow_full_inner K S P hP f] at h
  rw [integral_indicator (sourceKPFiniteWindowRemainderSet_measurable K P S)] at h
  exact h

local notation "L" => P.val.adicCompletion K
local notation "G₀" => SourceFiniteKP2Projective K hζ P.val
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "ι₀" => sourceKPAdelicLocalProjective K hζ P.val
local notation "kernel" => sourceKPFiniteIntertwiningKernel K hζ (1 / 6)

theorem sourceKPFiniteCyclicWindow_relation
    (hP : P.val ∉ traceBadPlaces K) (qf : Gf) {I : Type*} [Fintype I]
    (g : I → G₀) (c : I → ℂ) (hrel : SourceKPLocalNegativeCyclicRelation K hζ S₀ P g c)
    (S : Finset Places) (hPS : P.val ∈ S) :
    ∑ i, c i * sourceKPFiniteWindowIntegral K (kernel (qf * (ι₀ (g i)).2)) S = 0 := by
  let f (i : I) := kernel (qf * (ι₀ (g i)).2)
  let μ := (sourceKPFiniteStandardHaar K).restrict (sourceKPFiniteWindow K S)
  have hf (i : I) : Integrable (fun y => c i * f i y) μ :=
    (sourceKPFiniteIntertwiningKernel_window_integrable K hζ
      (by norm_num : 0 < (1 / 6 : ℂ).re) (qf * (ι₀ (g i)).2) S).const_mul (c i)
  have hsum : IntegrableOn (fun y => ∑ i, c i * f i y) (sourceKPFiniteWindow K S)
      (sourceKPFiniteStandardHaar K) := integrable_finsetSum _ (fun i _ => hf i)
  have hzero (r : sourceKPFinitePlaceRemainder K P.val) :
      (∫ x : L, ∑ i, c i * f i (sourceKPFiniteAdditiveSingle K P.val x + r.val)
        ∂sourceJacquetHaar K P.val) = 0 := by
    have hr := sourceKPFiniteCyclicFiber_relation K hζ S₀ P hP qf g c
      ((sourceKPLocalNegativeCyclicRelation_iff K hζ S₀ P g c).mp hrel) r.val r.property
    have hlocal (i : I) : Integrable
        (fun x : L => c i * f i (sourceKPFiniteAdditiveSingle K P.val x + r.val))
        (sourceJacquetHaar K P.val) := (hr.1 i).const_mul (c i)
    rw [integral_finsetSum Finset.univ (fun i _ => hlocal i)]
    simpa only [integral_const_mul, f] using hr.2
  calc
    _ = sourceKPFiniteWindowIntegral K (fun y => ∑ i, c i * f i y) S := by
      unfold sourceKPFiniteWindowIntegral
      rw [integral_finsetSum _ (fun i _ => hf i)]
      simp only [integral_const_mul, f, μ]
    _ = 0 := by
      refine (sourceKPFiniteWindow_integral_full_of_integrableOn K S P.val hPS
        (fun y => ∑ i, c i * f i y) hsum).trans ?_
      simp_rw [hzero, integral_zero]

theorem sourceKPFiniteFiberScatteringResidue_cyclic_relation
    (hP : P.val ∉ traceBadPlaces K) (qf : Gf) {I : Type*} [Fintype I]
    (g : I → G₀) (c : I → ℂ) (hrel : SourceKPLocalNegativeCyclicRelation K hζ S₀ P g c)
    (S : Finset Places) (hPS : P.val ∈ S) :
    ∑ i, c i * sourceKPFiniteFiberScatteringResidue K hζ (qf * (ι₀ (g i)).2) S = 0 := by
  let a := ((Real.pi : ℂ) / (1 / 6)) ^ Fintype.card (InfinitePlace K)
  let b := sourceKPExteriorScatteringResidue S
  calc
    _ = (a * b) * ∑ i, c i * sourceKPFiniteWindowIntegral K (kernel (qf * (ι₀ (g i)).2)) S := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      unfold sourceKPFiniteFiberScatteringResidue
      change c i * (a * (b * _)) = (a * b) * (c i * _)
      ring
    _ = 0 := by
      rw [sourceKPFiniteCyclicWindow_relation K hζ S₀ P hP qf g c hrel S hPS, mul_zero]

end
end ArtinMatthews
