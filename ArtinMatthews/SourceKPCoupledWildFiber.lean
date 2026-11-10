module

public import ArtinMatthews.SourceKPCoupledLocalProduct
public import ArtinMatthews.SourceIntertwinerArchFinite
public import ArtinMatthews.SourceKPExteriorUpperCompatibility
public import ArtinMatthews.SourceKPLocalRestBase
public import ArtinMatthews.SourceKPWildCompactSupport
public import ArtinMatthews.SourceKPCoupledWildLower
public import ArtinMatthews.SourceKPLocalFiberFactor
public import ArtinMatthews.SourceKPLocalFiniteKernel
public import ArtinMatthews.SourceKPWeylLower
public import ArtinMatthews.SourceKubotaGL2Generation
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

/-! Each wild fiber of the literal coupled test is supported on its
actual deep ideal, with the remaining global factor still present. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory SourcePhysical Matrix
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

local notation "L" => P.adicCompletion K
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P
local notation "ι₀" => sourceKPAdelicLocalProjective K hζ P
local notation "w₀" => ι₀ (l₀ sourceGL2Weyl)
local notation "W₀" => sourceKPAdelicProjectiveWeyl K hζ
local notation "g₀" => sourceKPCoupledWildWeyl K hζ
local notation "b₀" => sourceKPAdelicLocalBase K hζ P

def sourceKPCoupledWildFiberRest (r : 𝔸ᶠ[K]) : SourceKPAdelicProjective K hζ :=
  sourceKPLocalFiberRest K hζ P r g₀ * w₀⁻¹

theorem sourceKPCoupledWildFiberRest_base (hP : (6 : 𝓞 K) ∈ P.asIdeal)
    (r : 𝔸ᶠ[K]) (hr : r P = 0) : b₀ (sourceKPCoupledWildFiberRest K hζ P r) = 1 := by
  have hw : b₀ w₀ = ProjGenLinGroup.mk (sourceGL2Weyl : GL (Fin 2) L) :=
    sourceKPAdelicLocalBase_local K hζ P _
  have hn : b₀ (sourceKPAdelicUpperLift K hζ (0,r)) = 1 := by
    have he := sourceKPAdelicLocalBase_upper K hζ P (show 𝔸[K] from (0,r))
    change b₀ (sourceKPAdelicUpperLift K hζ (0,r)) = ProjGenLinGroup.mk (sourceGL2Upper (r P)) at he
    rw [he, hr, sourceGL2Upper_zero, map_one]
  unfold sourceKPCoupledWildFiberRest sourceKPLocalFiberRest
  simp only [map_mul, map_inv, hw, sourceKPAdelicLocalBase_weyl K hζ P, hn,
    sourceKPCoupledWildWeyl_at K hζ P hP]
  group

theorem sourceKPCoupledWildFiber_factor (hP : (6 : 𝓞 K) ∈ P.asIdeal)
    (r : 𝔸ᶠ[K]) (hr : r P = 0) (x : L) :
    W₀ * sourceKPAdelicUpperLift K hζ (0,sourceKPFiniteAdditiveSingle K P x+r) * g₀ =
      sourceKPAdelicLowerAt K hζ P x * sourceKPCoupledWildFiberRest K hζ P r := by
  let R := sourceKPCoupledWildFiberRest K hζ P r
  have hR : b₀ R = 1 := sourceKPCoupledWildFiberRest_base K hζ P hP r hr
  have hc : Commute w₀ R := sourceKPAdelicLocalProjective_commute_of_base_one K hζ P _ R hR
  have he : sourceKPLocalFiberRest K hζ P r g₀ = R*w₀ := by
    change sourceKPLocalFiberRest K hζ P r g₀ = (sourceKPLocalFiberRest K hζ P r g₀ * w₀⁻¹)*w₀
    rw [inv_mul_cancel_right]
  calc
    _ = ι₀ (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)) * sourceKPLocalFiberRest K hζ P r g₀ :=
      sourceKPLocalFiber_factor K hζ P x r g₀
    _ = ι₀ (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)) * (R*w₀) :=
      congrArg (fun a => ι₀ (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x))*a) he
    _ = (w₀ * ι₀ (l₀ (sourceGL2Upper x)) * w₀) * R := by
      simp only [← hc.eq, map_mul, mul_assoc]
    _ = _ := congrArg (fun a => a*R) (sourceKPAdelicLocalProjective_weyl_upper_weyl K hζ P x)

theorem sourceKPCoupledWildFiber_kernel (hP : (6 : 𝓞 K) ∈ P.asIdeal) (s : ℂ)
    (r : 𝔸ᶠ[K]) (hr : r P = 0) (x : L) :
    sourceKPFiniteIntertwiningKernel K hζ s (g₀).2 (sourceKPFiniteAdditiveSingle K P x+r) =
      sourceKPAdelicCompactScalar K hζ s
        (sourceKPAdelicLowerAt K hζ P x * sourceKPCoupledWildFiberRest K hζ P r) := by
  let y := sourceKPFiniteAdditiveSingle K P x+r
  have hg : g₀ = (1,(g₀).2) := Prod.ext (sourceKPCoupledWildWeyl_arch K hζ) rfl
  calc
    _ = sourceKPAdelicCompactScalar K hζ s (W₀ * sourceKPAdelicUpperLift K hζ (0,y) * (1,(g₀).2)) :=
      (sourceKPLocalFiniteKernel_eq_full K hζ s (g₀).2 y).symm
    _ = sourceKPAdelicCompactScalar K hζ s (W₀ * sourceKPAdelicUpperLift K hζ (0,y) * g₀) :=
      congrArg (fun a => sourceKPAdelicCompactScalar K hζ s (W₀ * sourceKPAdelicUpperLift K hζ (0,y) * a)) hg.symm
    _ = _ := congrArg (sourceKPAdelicCompactScalar K hζ s)
      (sourceKPCoupledWildFiber_factor K hζ P hP r hr x)

theorem sourceKPCoupledWildFiber_full_eq_unit (hP : (6 : 𝓞 K) ∈ P.asIdeal) (s : ℂ)
    (r : 𝔸ᶠ[K]) (hr : r P = 0) (μ : Measure L) :
    (∫ x : L, sourceKPFiniteIntertwiningKernel K hζ s (g₀).2 (sourceKPFiniteAdditiveSingle K P x+r) ∂μ) =
      ∫ x : L in sourceLocalBall K P 0,
        sourceKPFiniteIntertwiningKernel K hζ s (g₀).2 (sourceKPFiniteAdditiveSingle K P x+r) ∂μ := by
  simp_rw [sourceKPCoupledWildFiber_kernel K hζ P hP s r hr]
  exact sourceKPCoupledWildLower_full_eq_unit K hζ P hP s (sourceKPCoupledWildFiberRest K hζ P r)
    (sourceKPCoupledWildFiberRest_base K hζ P hP r hr) μ

end
end ArtinMatthews
