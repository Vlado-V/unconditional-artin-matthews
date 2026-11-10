module

public import ArtinMatthews.SourceKPJacquetFrequency
public import ArtinMatthews.SourceKPJacquetStableMap
public import ArtinMatthews.SourceJacquetBallShells
public import ArtinMatthews.SourceKPProjectiveSections
public import ArtinMatthews.SourceLocalHaarGeneralDilation
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
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Exact diagonal transport in the actual cover, followed by dilation
of the self-dual Haar on the literal valuation ball. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic SourcePhysical MeasureTheory Filter
open scoped NumberField SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "G" => SourceFiniteKP2Projective K hζ P
local notation "B₀" => SourceFiniteKPProjectiveBorel K hζ P
local notation "B" => sourceLocalBall K P
local notation "ν₀" => sourceLocalValuation K P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P
local notation "n₀" => fun t : L => l₀ (sourceGL2Upper t)
local notation "d₀" => sourceFiniteKPProjectiveBorelDiagonal K hζ P
local notation "a₀" => fun t : Lˣ => l₀ (sourceGL2Diagonal t)
local notation "w₀" => l₀ sourceGL2Weyl
local notation "ψ₀" => localFiniteCharacter K P
local notation "μ₀" => sourceLocalSelfDual K P

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (SourceFiniteKPProjectiveBorel K hζ P) V)
local notation "I₀" => sourceAlgebraicInducedSpace B₀ ρ

theorem sourceKPJacquet_open_diagonal_eval (z : Lˣ) (f : I₀) (x : L) :
    f.val ((w₀ * n₀ x) * a₀ z) = ρ (d₀ z⁻¹) (f.val (w₀ * n₀ (x / (z : L)))) := by
  rw [mul_assoc, sourceFiniteKP2ProjectiveLift_upper_diagonal,
    ← mul_assoc, sourceFiniteKP2ProjectiveLift_weyl_diagonal, mul_assoc,
    ← sourceFiniteKPProjectiveBorelDiagonal_val, f.property]

variable (C : Submodule ℂ (sourceAlgebraicInducedSpace _ ρ))
    {ι : Type*} [Fintype ι] (e : V ≃ₗ[ℂ] (ι → ℂ))
    (hC : ∀ (g : SourceFiniteKP2Projective K hζ P) (f : sourceAlgebraicInducedSpace _ ρ),
      f ∈ C → sourceAlgebraicInducedRepresentation (SourceFiniteKPProjectiveBorel K hζ P) ρ g f ∈ C)
local notation "r₀" => sourceKPJacquetRight K hζ P ρ C hC
local notation "Tr" => sourceKPJacquetTruncation K hζ P ρ C e
local notation "E₀" => sourceKPJacquetCoordinateIntegrand K hζ P ρ C e
local notation "Ez" => sourceKPJacquetFrequencyIntegrand K hζ P ρ e
local notation "Fz" => sourceKPJacquetFrequencyTruncation K hζ P ρ e

theorem sourceKPJacquetTruncation_diagonal (hSmooth : SourceKPJacquetRootSmooth K hζ P ρ C)
    (z : Lˣ) (R : ℕ) (f : C) :
    Tr R (r₀ (a₀ z) f) = (‖(z : L)‖ : ℂ) •
      ρ (d₀ z⁻¹) (Fz z ((R : ℤ) - WithZero.log (ν₀ (z : L))) f.val) := by
  let d := WithZero.log (ν₀ (z : L))
  let r : ℤ := (R : ℤ) - d
  let f' := r₀ (a₀ z) f
  let A : (ι → ℂ) →L[ℂ] (ι → ℂ) := LinearMap.toContinuousLinearMap
    (e.toLinearMap.comp ((ρ (d₀ z⁻¹)).comp e.symm.toLinearMap))
  have hA (v : V) : A (e v) = e (ρ (d₀ z⁻¹) v) := by
    change e (ρ (d₀ z⁻¹) (e.symm (e v))) = _
    rw [e.symm_apply_apply]
  have hset : (fun x : L => (z : L) * x) '' B r = B (R : ℤ) := by
    rw [sourceJacquetBall_mul_image K P r d z
      (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr z.ne_zero)).symm]
    simp only [r, sub_add_cancel]
  have hcomp : (fun x : L => E₀ f' w₀ ((z : L) * x)) = fun x => A (Ez z f.val x) := by
    funext x
    unfold sourceKPJacquetCoordinateIntegrand sourceKPJacquetFrequencyIntegrand
    rw [sourceKPJacquetRight_eval, sourceKPJacquet_open_diagonal_eval K hζ P ρ, map_smul, hA]
    rw [show (z : L) * x / (z : L) = x by field_simp [z.ne_zero]]
  obtain ⟨M, hM⟩ := hSmooth f
  have hi := sourceKPJacquetFrequencyIntegrand_integrableOn K hζ P ρ e z f.val M
    (fun t ht g => (hM t ht g).1) r
  let : (μ₀).IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  have h := sourceLocalAddHaar_setIntegral_dilation K P μ₀ z (B r) (E₀ f' w₀)
  rw [hset, hcomp, A.integral_comp_comm hi, RCLike.real_smul_eq_coe_smul (K := ℂ)] at h
  apply e.injective
  unfold sourceKPJacquetTruncation sourceKPJacquetFrequencyTruncation
  rw [e.apply_symm_apply, h, map_smul]
  change (‖(z : L)‖ : ℂ) • e (ρ (d₀ z⁻¹) (e.symm (∫ x in B r, Ez z f.val x ∂μ₀))) = _
  rfl

def SourceKPJacquetFrequencyHasStableValue (z : Lˣ) (f : I₀) (v : V) : Prop :=
  ∀ᶠ R : ℕ in atTop, Fz z (R : ℤ) f = v

variable (hUpper : ∀ x : P.adicCompletion K, ∀ v : V,
      ρ (sourceFiniteKPProjectiveBorelUpper K hζ P x) v = v)
    (hCube : ∀ y : (P.adicCompletion K)ˣ,
      sourceLocalValuation K P (((y ^ 3 : (P.adicCompletion K)ˣ) : P.adicCompletion K)) = 1 →
      ∀ v : V, ρ (sourceFiniteKPProjectiveBorelDiagonal K hζ P (y ^ 3)) v = v)
    (hSmooth : SourceKPJacquetRootSmooth K hζ P ρ C)
local notation "J" => sourceKPJacquetStableMap K hζ P ρ C e hUpper hCube hSmooth

theorem sourceKPJacquetStableMap_diagonal_of_frequency (z : Lˣ) (f : C) (v : V)
    (hv : SourceKPJacquetFrequencyHasStableValue K hζ P ρ e z f.val v) :
    J (r₀ (a₀ z) f) = (‖(z : L)‖ : ℂ) • ρ (d₀ z⁻¹) v := by
  let d := WithZero.log (ν₀ (z : L))
  let f' := r₀ (a₀ z) f
  have hj := sourceKPJacquetStableMap_hasStableValue K hζ P ρ C e hUpper hCube hSmooth f'
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp hv
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.mp hj
  let R := max R₁ (R₀ + d.natAbs)
  have hR : R₁ ≤ R := le_max_left _ _
  have hr : (R₀ : ℤ) ≤ (R : ℤ) - d := by
    have h := le_max_right R₁ (R₀ + d.natAbs)
    change R₀ + d.natAbs ≤ R at h
    omega
  let r := ((R : ℤ) - d).toNat
  have hr' : (r : ℤ) = (R : ℤ) - d := Int.toNat_of_nonneg (by omega)
  have hval := hR₀ r (by omega)
  calc
    _ = Tr R f' := (hR₁ R hR).symm
    _ = _ := by
      rw [sourceKPJacquetTruncation_diagonal K hζ P ρ C e hC hSmooth]
      change (‖(z : L)‖ : ℂ) • ρ (d₀ z⁻¹) (Fz z ((R : ℤ) - d) f.val) = _
      rw [← hr', hval]

end
end ArtinMatthews
