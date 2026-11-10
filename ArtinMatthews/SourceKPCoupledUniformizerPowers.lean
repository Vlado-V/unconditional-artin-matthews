module

public import ArtinMatthews.SourceKPLocalUniformizerAction
public import ArtinMatthews.SourceKPLocalUnitFixed
public import ArtinMatthews.SourceKPLocalBorelRelations
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual local diagonal action on the global carrier in uniformizer
and unit coordinates. The cubic orbit and every unit phase stay explicit. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (π : (P.adicCompletion K)ˣ) (s : ℂ)

local notation "V" => SourceKPAdelicTorusInducedSpace K hζ s
local notation "σ₀" => sourceKPAdelicLocalBorelRepresentation K hζ P s
local notation "D₀" => sourceFiniteKPProjectiveBorelDiagonal K hζ P
local notation "A₀" => sourceKPLocalUniformizerCycle K hζ P π s

theorem sourceKPCoupledUniformizer_action_zpow (j : ℤ) :
    σ₀ (D₀ (π^j)) =
      Complex.exp (-(s+1/2)*(j : ℂ)*(Real.log (Ideal.absNorm P.asIdeal : ℝ) : ℂ)) • (A₀^j).val := by
  let ρ := sourceKPLocalNormalizedUniformizerAction K hζ P π s
  have hj : (Multiplicative.ofAdd (1 : ℤ))^j = Multiplicative.ofAdd j := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul, Int.cast_id, mul_one]
  have h : A₀^j = ρ.asGroupHom (Multiplicative.ofAdd j) := by
    change (ρ.asGroupHom (Multiplicative.ofAdd (1 : ℤ)))^j = _
    rw [← map_zpow, hj]
  have hv := congrArg (fun a : (Module.End ℂ V)ˣ => a.val) h
  rw [Representation.asGroupHom_apply] at hv
  change (A₀^j).val = Complex.exp ((s+1/2)*(j : ℂ)*
    (Real.log (Ideal.absNorm P.asIdeal : ℝ) : ℂ)) • σ₀ (D₀ (π^j)) at hv
  rw [hv, smul_smul, ← Complex.exp_add]
  rw [show -(s+1/2)*(j : ℂ)*(Real.log (Ideal.absNorm P.asIdeal : ℝ) : ℂ) +
    (s+1/2)*(j : ℂ)*(Real.log (Ideal.absNorm P.asIdeal : ℝ) : ℂ) = 0 by ring,
    Complex.exp_zero, one_smul]

theorem sourceKPCoupledUniformizer_diagonal_unit (j : ℤ) (u : (P.adicCompletion K)ˣ)
    (hu : sourceKPFiniteVal K P (u : P.adicCompletion K) = 1)
    (v : V) (hv : v ∈ sourceKPLocalUnitFixed K hζ P s) :
    σ₀ (D₀ (π^j*u)) v =
      (((sourceKPTameUniformizerCharacter K hζ P π u) ^ (-j) : ℂˣ) : ℂ) • σ₀ (D₀ (π^j)) v := by
  let H := sourceFiniteKPHilbert K hζ P
  let z := H (π^j) u ^ 2
  let c := sourceKPTameUniformizerCharacter K hζ P π u
  have hz : sourceKPCentralComplex K hζ P z = c^j := by
    rw [show c = sourceKPCentralComplex K hζ P (H π u ^ 2) from
      sourceKPTameUniformizerCharacter_apply K hζ P π u, ← map_zpow]
    apply congrArg (sourceKPCentralComplex K hζ P)
    change H (π^j) u ^ 2 = (H π u ^ 2)^j
    rw [map_zpow, MonoidHom.zpow_apply]
    exact map_zpow (powMonoidHom 2) (H π u) j
  have h := congrArg (fun d => σ₀ d v) (sourceKPLocalBorelDiagonal_mul K hζ P (π^j) u)
  rw [map_mul, Module.End.mul_apply, hv u hu, map_mul, Module.End.mul_apply,
    sourceKPAdelicLocalBorelRepresentation_center] at h
  change σ₀ (D₀ (π^j)) v = (sourceKPCentralComplex K hζ P z : ℂ) • σ₀ (D₀ (π^j*u)) v at h
  rw [hz] at h
  have hc : ((c^j : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have he := congrArg (fun w : V => ((c^j : ℂˣ) : ℂ)⁻¹ • w) h
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at he
  rw [zpow_neg, Units.val_inv_eq_inv_val]
  exact he.symm

end
end ArtinMatthews
