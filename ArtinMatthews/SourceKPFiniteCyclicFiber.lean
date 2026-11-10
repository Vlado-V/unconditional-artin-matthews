module

public import ArtinMatthews.SourceIntertwinerArchFinite
public import ArtinMatthews.SourceKPExteriorUpperCompatibility
public import ArtinMatthews.SourceKPLocalReceiverIntegral
public import ArtinMatthews.SourceKPLocalRestBase
public import ArtinMatthews.SourceKPLocalRestSection
public import ArtinMatthews.SourceKPTameWeylBasisFlip
public import ArtinMatthews.SourceKPLocalFiniteKernel
public import ArtinMatthews.SourceKPTameCyclicUpperAverage
public import ArtinMatthews.SourceKPTameParametricOpenCell
public import ArtinMatthews.SourceKPTameSphericalTranslatedIntegral
public import ArtinMatthews.SourceKPTraceJacquetTranslatedFiber
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

/-! The unweighted finite-place fiber at an arbitrary translated input.
The local outgoing section is evaluated by the receiver attached to the
literal other-place remainder. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical QuadraticWeil
open scoped NumberField AdeleRing Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "G₀" => SourceFiniteKP2Projective K hζ P.val
local notation "G" => SourceKPAdelicProjective K hζ
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "ι₀" => sourceKPAdelicLocalProjective K hζ P.val
local notation "base₀" => sourceKPAdelicLocalBase K hζ P.val
local notation "single₀" => sourceKPFiniteAdditiveSingle K P.val
local notation "μ₀" => sourceJacquetHaar K P.val
local notation "h₆" => source_exterior_six_not_mem K S₀ P.val P.property
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "sphere" => sourceKPTameParametricSphericalSection K hζ P.val h₆ π₀ hπ₀
local notation "kernel" => sourceKPFiniteIntertwiningKernel K hζ

theorem sourceKPFiniteCyclicFiber_integral
    (hP : P.val ∉ traceBadPlaces K) {s : ℂ} (hs : 0 < s.re)
    (g : Gf) (q : G₀) (g₀ : G) (hg₀ : base₀ g₀ = 1) (hg : (1, g) = ι₀ q * g₀)
    (r : 𝔸ᶠ[K]) (hr : r P.val = 0) :
    let R := sourceKPLocalFiberRest K hζ P.val r g₀
    let hR := sourceKPLocalFiberRest_base K hζ P.val r hr g₀ hg₀
    Integrable (fun x : L => kernel s g (single₀ x + r)) μ₀ ∧
    (∫ x : L, kernel s g (single₀ x + r) ∂μ₀) =
      sourceKPUnramifiedScatteringFactor P.val s *
        sourceKPLocalReceiverCoordinate K hζ S₀ P s
          (sourceKPLocalRestVector K hζ S₀ P s R hR) 1
          (sourceKPTameWeylBasisFlip ((sphere (-s)).val q)) := by
  let R := sourceKPLocalFiberRest K hζ P.val r g₀
  let hR := sourceKPLocalFiberRest_base K hζ P.val r hr g₀ hg₀
  let A := sourceKPLocalReceiverCoordinate K hζ S₀ P s
    (sourceKPLocalRestVector K hζ S₀ P s R hR) 1
  let I := sourceKPTameSphericalPlainIntegrand K hζ S₀ P s q
  have hi := sourceKPTameSphericalPlainIntegrand_integrable K hζ S₀ P hP hs q
  have he : (fun x : L => kernel s g (single₀ x + r)) = fun x => A (I x) := by
    funext x
    rw [← sourceKPLocalFiniteKernel_eq_full, hg,
      sourceKPTraceJacquetGlobalFiber_factor_translated K hζ S₀ P x r hr q g₀ hg₀]
    change ((sourceKPAdelicCompactSection K hζ s).val (_ * R)).val 1 = A (I x)
    rw [sourceKPLocalRest_section K hζ S₀ P s R hR,
      sourceKPLocalReceiverIntertwining_apply]
    rfl
  dsimp only
  rw [he]
  refine ⟨A.integrable_comp hi, ?_⟩
  rw [A.integral_comp_comm hi]
  have hraw : (∫ x, I x ∂μ₀) = sourceKPTameWeylBasisFlip
      (sourceKPUnramifiedScatteringFactor P.val s • (sphere (-s)).val q) := by
    have h := congrArg (fun v => sourceKPTameWeylBasisFlip v)
      (sourceKPTameSphericalTranslatedIntertwiner K hζ S₀ P hP hs q)
    simpa only [sourceKPTameWeylBasisFlip_involutive] using h
  change A (∫ x, I x ∂μ₀) = _
  rw [hraw, map_smul, map_smul, smul_eq_mul]

local notation "C₋" => sourceKPTameSphericalCyclicSpace K hζ S₀ P
local notation "r₋" => sourceKPTameSphericalCyclicRepresentation K hζ S₀ P
local notation "v₋" => sourceKPTameCyclicSphericalVector K hζ S₀ P
local notation "f₋" => sourceKPTameExteriorSphericalSection K hζ S₀ P
local notation "s₀" => (1 / 6 : ℂ)

theorem sourceKPFiniteCyclicFiber_relation
    (hP : P.val ∉ traceBadPlaces K) (qf : Gf)
    {I : Type*} [Fintype I] (g : I → G₀) (c : I → ℂ)
    (hrel : (∑ i, c i • r₋ (g i) v₋ : C₋) = 0)
    (r : 𝔸ᶠ[K]) (hr : r P.val = 0) :
    (∀ i, Integrable (fun x : L => kernel s₀ (qf * (ι₀ (g i)).2) (single₀ x + r)) μ₀) ∧
    ∑ i, c i * (∫ x : L, kernel s₀ (qf * (ι₀ (g i)).2) (single₀ x + r) ∂μ₀) = 0 := by
  obtain ⟨h, g₀, hg₀, hqf⟩ :=
    sourceKPTraceJacquetGlobalFiber_split_right K hζ S₀ P (1, qf)
  have hshift (i : I) : (1, qf * (ι₀ (g i)).2) = ι₀ (h * g i) * g₀ := by
    have hc := sourceKPAdelicLocalProjective_commute_of_base_one K hζ P.val (g i) g₀ hg₀
    calc
      _ = (show G from (1, qf)) * ι₀ (g i) := by
        apply Prod.ext
        · change (1 : _) = 1 * 1
          rw [mul_one]
        · rfl
      _ = _ := by rw [hqf, mul_assoc, ← hc.eq, ← mul_assoc, ← map_mul]
  have hfib (i : I) := sourceKPFiniteCyclicFiber_integral K hζ S₀ P hP
    (by norm_num : 0 < (s₀).re) (qf * (ι₀ (g i)).2) (h * g i) g₀ hg₀ (hshift i) r hr
  refine ⟨fun i => (hfib i).1, ?_⟩
  let R := sourceKPLocalFiberRest K hζ P.val r g₀
  let hR := sourceKPLocalFiberRest_base K hζ P.val r hr g₀ hg₀
  let A := sourceKPLocalReceiverCoordinate K hζ S₀ P s₀
    (sourceKPLocalRestVector K hζ S₀ P s₀ R hR) 1
  have hneg : -(1 / 6 : ℂ) = -1 / 6 := by ring
  have hsection (q : G₀) : (sphere (-s₀)).val q = f₋.val q := by
    rw [hneg, sourceKPTameParametricSpherical_base]
  have hvalues : ∑ i, c i • f₋.val (h * g i) = 0 := by
    have hv := congrArg (sourceKPTameCyclicEval K hζ S₀ P h) hrel
    rw [map_sum, map_zero] at hv
    have heval (i : I) : sourceKPTameCyclicEval K hζ S₀ P h (r₋ (g i) v₋) =
        f₋.val (h * g i) := rfl
    simpa only [map_smul, heval] using hv
  calc
    _ = sourceKPUnramifiedScatteringFactor P.val s₀ *
        A (sourceKPTameWeylBasisFlip (∑ i, c i • f₋.val (h * g i))) := by
      simp only [map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [(hfib i).2, hsection, map_smul, map_smul, smul_eq_mul]
      ring
    _ = 0 := by rw [hvalues, map_zero, map_zero, mul_zero]

end
end ArtinMatthews
