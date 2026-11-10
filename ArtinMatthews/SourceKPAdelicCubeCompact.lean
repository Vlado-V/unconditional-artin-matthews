module

public import ArtinMatthews.SourceKPAdelicCompactSplit
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

/-! Cubing removes the actual cubic central ambiguity in a lift
to the global compact subgroup. No topology on the covering group
is required for this algebraic step. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicProjectiveCenter_cube (z : rootsOfUnity 3 K) :
    (sourceKPAdelicProjectiveCenter K hζ z) ^ (3 : ℕ) = 1 := by
  have hz : z ^ (3 : ℕ) = 1 := by
    apply Subtype.ext
    exact z.property
  rw [← map_pow, hz, map_one]

theorem sourceKPAdelicCube_mem_compact_of_projection
    (g : SourceKPAdelicProjective K hζ) (k : sourceKPAdelicDeepCompact K hζ)
    (h : sourceKPAdelicProjectiveProjection K hζ g = sourceKPAdelicProjectiveProjection K hζ k.val) :
    g ^ (3 : ℕ) ∈ sourceKPAdelicDeepCompact K hζ := by
  have hk : g * k.val⁻¹ ∈ (sourceKPAdelicProjectiveProjection K hζ).ker := by
    change sourceKPAdelicProjectiveProjection K hζ (g * k.val⁻¹) = 1
    rw [map_mul, map_inv, h, mul_inv_cancel]
  rw [← sourceKPAdelicProjective_exact K hζ] at hk
  obtain ⟨z, hz⟩ := hk
  have hg : g = sourceKPAdelicProjectiveCenter K hζ z * k.val := by
    rw [hz, inv_mul_cancel_right]
  rw [hg, (sourceKPAdelicProjectiveCenter_commute K hζ z k.val).mul_pow,
    sourceKPAdelicProjectiveCenter_cube, one_mul]
  exact (sourceKPAdelicDeepCompact K hζ).pow_mem k.property 3

theorem sourceKPAdelicFiniteUpper_cube (t : 𝔸ᶠ[K]) :
    (sourceKPAdelicUpperLift K hζ (0, t)) ^ (3 : ℕ) =
      sourceKPAdelicUpperLift K hζ (0, (3 : 𝔸ᶠ[K]) * t) := by
  let x : 𝔸[K] := (0, t)
  have hx : x + x + x = (0, (3 : 𝔸ᶠ[K]) * t) := by
    apply Prod.ext
    · change (0 : InfiniteAdeleRing K) + 0 + 0 = 0
      simp
    · change t + t + t = (3 : 𝔸ᶠ[K]) * t
      ring
  calc
    _ = (sourceKPAdelicUpperLift K hζ x * sourceKPAdelicUpperLift K hζ x) *
        sourceKPAdelicUpperLift K hζ x := by rw [pow_succ, pow_two]
    _ = sourceKPAdelicUpperLift K hζ (x + x) * sourceKPAdelicUpperLift K hζ x :=
      congrArg (fun a => a * sourceKPAdelicUpperLift K hζ x)
        (sourceKPAdelicUpperLift_add K hζ x x).symm
    _ = sourceKPAdelicUpperLift K hζ (x + x + x) :=
      (sourceKPAdelicUpperLift_add K hζ (x + x) x).symm
    _ = _ := congrArg (sourceKPAdelicUpperLift K hζ) hx

theorem sourceKPAdelicFiniteConjugate_cube (g : SourceKPAdelicProjective K hζ) (t : 𝔸ᶠ[K]) :
    (g⁻¹ * sourceKPAdelicUpperLift K hζ (0, t) * g) ^ (3 : ℕ) =
      g⁻¹ * sourceKPAdelicUpperLift K hζ (0, (3 : 𝔸ᶠ[K]) * t) * g := by
  calc
    _ = g⁻¹ * (sourceKPAdelicUpperLift K hζ (0, t)) ^ (3 : ℕ) * g := by
      have h := map_pow (MulAut.conj g⁻¹) (sourceKPAdelicUpperLift K hζ (0, t)) 3
      simpa only [MulAut.conj_apply, inv_inv] using h.symm
    _ = _ := by rw [sourceKPAdelicFiniteUpper_cube]

end
end ArtinMatthews
