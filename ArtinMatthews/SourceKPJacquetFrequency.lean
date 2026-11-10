module

public import ArtinMatthews.SourceAlgebraicInduction
public import ArtinMatthews.SourceFiniteKPProjectiveBorel
public import ArtinMatthews.StandardLocalConductor
public import ArtinMatthews.StandardLocalFourier
public import ArtinMatthews.SourceJacquetAdditiveTranslation
public import ArtinMatthews.SourceKPJacquetBallCancellation
public import ArtinMatthews.SourceKPProjectiveCanonicalFactors
public import ArtinMatthews.StandardLocalBall
public import ArtinMatthews.StandardLocalBallDilation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The frequency-scaled Jacquet truncation uses the actual self-dual Haar
and the same canonical open cell at every finite place. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic SourcePhysical MeasureTheory Filter Topology
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
local notation "w₀" => l₀ sourceGL2Weyl
local notation "ψ₀" => localFiniteCharacter K P
local notation "μ₀" => sourceLocalSelfDual K P

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (SourceFiniteKPProjectiveBorel K hζ P) V)
    {ι : Type*} [Fintype ι] (e : V ≃ₗ[ℂ] (ι → ℂ))
local notation "I₀" => sourceAlgebraicInducedSpace B₀ ρ

def sourceKPJacquetFrequencyIntegrand (z : Lˣ) (f : I₀) (x : L) : ι → ℂ :=
  ψ₀ (-((z : L) * x)) • e (f.val (w₀ * n₀ x))

local notation "E" => sourceKPJacquetFrequencyIntegrand K hζ P ρ e

def sourceKPJacquetFrequencyTruncation (z : Lˣ) (R : ℤ) (f : I₀) : V :=
  e.symm (∫ x in B R, E z f x ∂μ₀)

theorem sourceKPJacquetFrequencyIntegrand_norm (z : Lˣ) (f : I₀) (x : L) :
    ‖E z f x‖ = ‖e (f.val (w₀ * n₀ x))‖ := by
  rw [sourceKPJacquetFrequencyIntegrand, norm_smul, localFiniteCharacter_unitary, one_mul]

theorem sourceKPJacquetFrequencyIntegrand_shift (z : Lˣ) (f : I₀) (x a : L)
    (hf : f.val (w₀ * n₀ (x + a)) = f.val (w₀ * n₀ x)) :
    E z f (x + a) = ψ₀ (-((z : L) * a)) • E z f x := by
  unfold sourceKPJacquetFrequencyIntegrand
  rw [hf, mul_add, neg_add, AddChar.map_add_eq_mul, mul_comm (ψ₀ (-((z : L) * x))), smul_smul]

theorem sourceKPJacquetFrequencyIntegrand_continuous (z : Lˣ) (f : I₀) (M : ℕ)
    (hFix : ∀ t ∈ B (-(M : ℤ)), ∀ g : G, f.val (g * n₀ t) = f.val g) :
    Continuous (E z f) := by
  have hψ : Continuous (fun x : L => ψ₀ (-((z : L) * x))) :=
    (localFiniteCharacter_continuous K P).comp (continuous_const.mul continuous_id).neg
  apply hψ.smul
  apply continuous_iff_continuousAt.mpr
  intro x
  apply continuousAt_const.congr_of_eventuallyEq
  have hU : IsOpen ((fun y : L => y - x) ⁻¹' B (-(M : ℤ))) :=
    (sourceLocalBall_isOpen K P _).preimage (continuous_id.sub continuous_const)
  have hx : x ∈ (fun y : L => y - x) ⁻¹' B (-(M : ℤ)) := by
    change ν₀ (x - x) ≤ WithZero.exp (-(M : ℤ))
    rw [sub_self, map_zero]
    exact zero_le
  filter_upwards [hU.mem_nhds hx] with y hy
  have h := hFix (y - x) hy (w₀ * n₀ x)
  rw [mul_assoc, sourceFiniteKP2ProjectiveLift_upper_add,
    show x + (y - x) = y by abel] at h
  exact congrArg e h

theorem sourceKPJacquetFrequencyIntegrand_integrableOn (z : Lˣ) (f : I₀) (M : ℕ)
    (hFix : ∀ t ∈ B (-(M : ℤ)), ∀ g : G, f.val (g * n₀ t) = f.val g) (R : ℤ) :
    IntegrableOn (E z f) (B R) μ₀ := by
  let : (μ₀).IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  exact (sourceKPJacquetFrequencyIntegrand_continuous K hζ P ρ e z f M hFix).continuousOn.integrableOn_compact
    (sourceLocalBall_isCompact K P R)

theorem sourceKPJacquetFrequencyTruncation_zero_of_large (z : Lˣ) (f : I₀) (M : ℕ)
    (hFix : ∀ t ∈ B (-(M : ℤ)), ∀ g : G, f.val (g * n₀ t) = f.val g)
    (hz : (z : L) ∉ B ((sourceDifferentExponent K P : ℤ) + (M : ℤ)))
    (R : ℕ) : sourceKPJacquetFrequencyTruncation K hζ P ρ e z (R : ℤ) f = 0 := by
  obtain ⟨b, hb, hψ⟩ := sourceLocalCharacter_next_ball_nontrivial K P
  let a : L := b / (z : L)
  have hz0 : ν₀ (z : L) ≠ 0 := (Valuation.ne_zero_iff _).mpr z.ne_zero
  have hlog : (sourceDifferentExponent K P : ℤ) + (M : ℤ) < WithZero.log (ν₀ (z : L)) := by
    apply WithZero.exp_lt_exp.mp
    rw [WithZero.exp_log hz0]
    exact lt_of_not_ge hz
  have ha : a ∈ B (-(M : ℤ)) := by
    apply (sourceLocalBall_div_mem K P (-(M : ℤ)) z b).mpr
    exact sourceKPJacquetSelfDual_ball_mono K P (by omega) hb
  have haR : a ∈ B (R : ℤ) := sourceKPJacquetSelfDual_ball_mono K P (by omega) ha
  have hza : (z : L) * a = b := by dsimp only [a]; field_simp [z.ne_zero]
  have hψa : ψ₀ (-((z : L) * a)) ≠ 1 := by
    rw [hza, AddChar.map_neg_eq_inv]
    exact fun h => hψ (by simpa only [inv_inv, inv_one] using congrArg Inv.inv h)
  have hI := sourceKPJacquetSelfDual_integral_zero_of_phase K P (B (R : ℤ))
    (sourceLocalBall_isOpen K P _).measurableSet a
    (fun x => sourceJacquetBall_translate_mem_iff K P (R : ℤ) a x haR) (E z f) _ hψa
    (fun x _ => sourceKPJacquetFrequencyIntegrand_shift K hζ P ρ e z f x a (by
      change f.val (w₀ * l₀ (sourceGL2Upper (x + a))) = f.val (w₀ * n₀ x)
      rw [← sourceFiniteKP2ProjectiveLift_upper_add, ← mul_assoc]
      exact hFix a ha (w₀ * n₀ x)))
  rw [sourceKPJacquetFrequencyTruncation, hI, map_zero]

end
end ArtinMatthews
