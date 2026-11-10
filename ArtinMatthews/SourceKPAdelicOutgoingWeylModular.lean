module

public import ArtinMatthews.SourceKPAdelicPrincipalSeries
public import ArtinMatthews.SourceKPAdelicTorusWeyl
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

/-! The actual Weyl conjugation inverts the torus idele. Its half
modular factor is converted back by the positive full idele norm. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "T" => sourceKPAdelicCoveringTorus K hζ
local notation "W" => sourceKPAdelicProjectiveWeyl K hζ
local notation "w" => sourceKPAdelicCoveringTorusWeyl K hζ
local notation "Z" => sourceKPAdelicProjectiveCenter K hζ
local notation "a₀" => sourceKPAdelicTorusIdele K hζ
local notation "d₀" => sourceKPAdelicBorelTorusInclusion K hζ
local notation "δ" => sourceKPAdelicBorelModularHalf K hζ

theorem sourceKPAdelicOutgoingWeyl_idele (t : T) : a₀ (w t) = (a₀ t)⁻¹ := by
  obtain ⟨z,a,ha⟩ := (sourceKPAdelicCoveringTorus_mem_iff K hζ t.val).mp t.property
  have h₀ : a₀ t = a := by
    apply sourceKPProjectiveDiagonalHom_injective 𝔸[K]
    rw [← sourceKPAdelicTorusIdele_projection,ha,map_mul,sourceKPAdelicProjectiveCenter_projection_one,
      one_mul,sourceKPAdelicProjectiveDiagonalLift_projection]
  rw [h₀]
  apply sourceKPProjectiveDiagonalHom_injective 𝔸[K]
  rw [← sourceKPAdelicTorusIdele_projection,sourceKPAdelicCoveringTorusWeyl_val,ha,
    (sourceKPAdelicProjectiveCenter_commute K hζ z W).symm.left_comm,mul_assoc,
    sourceKPAdelicProjectiveWeyl_conj_diagonal,map_mul,sourceKPAdelicProjectiveCenter_projection_one,
    one_mul,sourceKPAdelicProjectiveDiagonalLift_projection]

theorem sourceKPAdelicOutgoingWeyl_half (t : T) :
    (sourceKPIdeleAbsoluteNorm K (a₀ t) : ℂ)*δ (d₀ (w t)) = δ (d₀ t) := by
  let q := sourceKPIdeleComplexNorm K (1/2 : ℂ)
  have hsq : (q (a₀ t) : ℂ)*(q (a₀ t) : ℂ) = (sourceKPIdeleAbsoluteNorm K (a₀ t) : ℂ) := by
    rw [← Units.val_mul]
    change ((sourceKPIdeleComplexNorm K (1/2 : ℂ) (a₀ t) *
      sourceKPIdeleComplexNorm K (1/2 : ℂ) (a₀ t) : ℂˣ) : ℂ) = _
    rw [← sourceKPIdeleComplexNorm_add K,show (1/2 : ℂ)+(1/2 : ℂ) = 1 by ring]
    have h := sourceKPIdeleComplexNorm_real K (1 : ℝ) (a₀ t)
    simpa only [Complex.ofReal_one,Real.rpow_one] using h
  have hδ (u : T) : δ (d₀ u) = (q (a₀ u) : ℂ) := by
    change (q (a₀ (sourceKPAdelicBorelTorusProjection K hζ (d₀ u))) : ℂ) = _
    rw [sourceKPAdelicBorelTorusProjection_inclusion]
  rw [hδ,hδ,sourceKPAdelicOutgoingWeyl_idele K hζ t,map_inv q,← hsq,mul_assoc,
    Units.val_inv_eq_inv_val,mul_inv_cancel₀ (Units.ne_zero _),mul_one]

end
end ArtinMatthews
