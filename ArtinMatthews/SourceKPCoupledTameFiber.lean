module

public import ArtinMatthews.SourceIntertwinerArchFinite
public import ArtinMatthews.SourceKPCoupledLocalProduct
public import ArtinMatthews.SourceKPCoupledTameRest
public import ArtinMatthews.SourceKPExteriorScattering
public import ArtinMatthews.SourceKPExteriorUpperCompatibility
public import ArtinMatthews.SourceKPLocalRestBase
public import ArtinMatthews.SourceKPCoupledTameIntegral
public import ArtinMatthews.SourceKPLocalFiberFactor
public import ArtinMatthews.SourceKPLocalFiniteKernel
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

/-! At every tame place the literal wild-test kernel has the checked
scattering law. The remaining global section is kept in each fiber. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory SourcePhysical
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (s : ℂ)

local notation "L" => P.adicCompletion K
local notation "g₀" => sourceKPCoupledWildWeyl K hζ
local notation "W₀" => sourceKPAdelicProjectiveWeyl K hζ
local notation "f₀" => sourceKPFiniteIntertwiningKernel K hζ s (g₀).2

theorem sourceKPCoupledTameFiber_kernel (r : 𝔸ᶠ[K]) (x : L) :
    f₀ (sourceKPFiniteAdditiveSingle K P x+r) =
      sourceKPCoupledTameRestKernel K hζ P s (sourceKPLocalFiberRest K hζ P r g₀) x := by
  let y := sourceKPFiniteAdditiveSingle K P x+r
  have hg : g₀ = (1,(g₀).2) := Prod.ext (sourceKPCoupledWildWeyl_arch K hζ) rfl
  calc
    _ = sourceKPAdelicCompactScalar K hζ s (W₀ * sourceKPAdelicUpperLift K hζ (0,y) * (1,(g₀).2)) :=
      (sourceKPLocalFiniteKernel_eq_full K hζ s (g₀).2 y).symm
    _ = sourceKPAdelicCompactScalar K hζ s (W₀ * sourceKPAdelicUpperLift K hζ (0,y) * g₀) :=
      congrArg (fun a => sourceKPAdelicCompactScalar K hζ s (W₀ * sourceKPAdelicUpperLift K hζ (0,y) * a)) hg.symm
    _ = _ := congrArg (sourceKPAdelicCompactScalar K hζ s) (sourceKPLocalFiber_factor K hζ P x r g₀)

theorem sourceKPCoupledTameFiber_full_eq_factor_unit (h6 : (6 : 𝓞 K) ∉ P.asIdeal)
    (r : 𝔸ᶠ[K]) (hr : r P = 0) (hs : 0 < s.re) :
    (∫ x : L, f₀ (sourceKPFiniteAdditiveSingle K P x+r) ∂sourceJacquetHaar K P) =
      sourceKPUnramifiedScatteringFactor P s *
      ∫ x : L in sourceLocalBall K P 0, f₀ (sourceKPFiniteAdditiveSingle K P x+r) ∂sourceJacquetHaar K P := by
  have hrest := sourceKPLocalFiberRest_base K hζ P r hr g₀ (sourceKPCoupledWildWeyl_outside K hζ P h6)
  simp_rw [sourceKPCoupledTameFiber_kernel K hζ P s r]
  exact sourceKPCoupledTameKernel_full_eq_factor_unit K hζ P s h6 _ hrest hs

end
end ArtinMatthews
