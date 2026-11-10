module

public import ArtinMatthews.SourceKPAdelicCompactSection
public import ArtinMatthews.SourceKPExteriorScattering
public import ArtinMatthews.SourceKPExteriorUpperCompatibility
public import ArtinMatthews.SourceKPLocalRestCommute
public import ArtinMatthews.SourceKPLocalFiberFactor
public import ArtinMatthews.SourceKPLocalRestIntegral
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

/-! The literal adelic upper fiber has the genuine unramified
scattering factor at every torus coordinate. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical
open scoped NumberField AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀) (s : ℂ)

local notation "L" => P.val.adicCompletion K
local notation "μ₀" => sourceJacquetHaar K P.val
local notation "F₀" => sourceKPAdelicCompactSection K hζ s
local notation "W₀" => sourceKPAdelicProjectiveWeyl K hζ
local notation "single₀" => sourceKPFiniteAdditiveSingle K P.val

theorem sourceKPLocalFiber_integrable (r : 𝔸ᶠ[K]) (hr : r P.val = 0)
    (g : SourceKPAdelicProjective K hζ) (hg : sourceKPAdelicLocalBase K hζ P.val g = 1)
    (t : sourceKPAdelicCoveringTorus K hζ)
    (hP : P.val ∉ traceBadPlaces K) (hs : 0 < s.re) :
    Integrable (fun x : L => ((F₀).val (W₀ *
      sourceKPAdelicUpperLift K hζ (0, (single₀ x : 𝔸ᶠ[K])+r) * g)).val t) μ₀ := by
  simp_rw [sourceKPLocalFiber_factor K hζ P.val]
  exact sourceKPLocalRest_integrable K hζ S₀ P s
    (sourceKPLocalFiberRest K hζ P.val r g)
    (sourceKPLocalFiberRest_base K hζ P.val r hr g hg) t hP hs

theorem sourceKPLocalFiber_integral_eq_factor_unit_ball (r : 𝔸ᶠ[K]) (hr : r P.val = 0)
    (g : SourceKPAdelicProjective K hζ) (hg : sourceKPAdelicLocalBase K hζ P.val g = 1)
    (t : sourceKPAdelicCoveringTorus K hζ)
    (hP : P.val ∉ traceBadPlaces K) (hs : 0 < s.re) :
    (∫ x : L, ((F₀).val (W₀ *
      sourceKPAdelicUpperLift K hζ (0, (single₀ x : 𝔸ᶠ[K])+r) * g)).val t ∂μ₀) =
        sourceKPUnramifiedScatteringFactor P.val s *
          ∫ x : L in sourceLocalBall K P.val 0, ((F₀).val (W₀ *
            sourceKPAdelicUpperLift K hζ (0, (single₀ x : 𝔸ᶠ[K])+r) * g)).val t ∂μ₀ := by
  simp_rw [sourceKPLocalFiber_factor K hζ P.val]
  exact sourceKPLocalRest_integral_eq_factor_unit_ball K hζ S₀ P s
    (sourceKPLocalFiberRest K hζ P.val r g)
    (sourceKPLocalFiberRest_base K hζ P.val r hr g hg) t hP hs

end
end ArtinMatthews
