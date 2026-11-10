module

public import ArtinMatthews.GiantFixedCharacterReplacement
public import ArtinMatthews.MarkedPhysicalCanonicalRoots
public import ArtinMatthews.MarkedPhysicalEndpointNormActual
public import ArtinMatthews.MarkedPhysicalLocalizedMoment
public import ArtinMatthews.MarkedPhysicalTypeIIEndpointBounds
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The literal fixed-character replacement coefficient is multiplied
by the character after ordinary centering. Only its norm is compared;
no ordinary mean-zero assertion is made about that product. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Classical
noncomputable section
attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

theorem markedPhysicalEndpointVector_character_norm_le
    {J : Type*} [Fintype J] (P : J → Finset ℕ) (M : ℕ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (α β : ℕ → ℂ) (z : ℤ × ℤ) :
    ‖markedPhysicalEndpointVector P M (fun n => χ n*α n) (fun n => χ n*β n) z‖ ≤
      ‖markedPhysicalEndpointVector P M α β z‖ := by
  have hc (f : ℕ → ℂ) (n : ℕ) : ‖χ n*f n‖ ≤ ‖f n‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one n)
  unfold markedPhysicalEndpointVector
  split_ifs
  · simp only [norm_mul,Complex.norm_conj]
    exact mul_le_mul
      (by simpa only [norm_mul] using hc α (z.1.natAbs/markedPhysicalSupportedProduct P z.1.natAbs))
      (by simpa only [norm_mul] using hc β z.2.natAbs) (by positivity) (norm_nonneg _)
  · simp

theorem markedPhysicalEndpointEnergy_character_le
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (Vmass : J → ℝ)
    (hVmass : ∀ j,0 ≤ Vmass j) {q : ℕ} (χ : DirichletCharacter ℂ q) (α β : ℕ → ℂ) :
    markedPhysicalEndpointEnergy P M Z Vmass (fun n => χ n*α n) (fun n => χ n*β n) ≤
      markedPhysicalEndpointEnergy P M Z Vmass α β := by
  unfold markedPhysicalEndpointEnergy
  exact Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (markedPhysicalEndpointVector_character_norm_le P M χ α β s.1.1.1) 2)
    (markedPhysicalMass_nonneg Vmass M hVmass))

def markedPhysicalTypeIICharacterEndpoint {J : Type*} [Fintype J]
    (e : J → ℝ) (x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ) (z : ℤ × ℤ) : ℂ :=
  markedPhysicalEndpointVector (fun j => markedLogPowerBand (e j) x) (markedPadSlots x)
    (fun n => χ n*markedMajorRestrictedCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) modulation Sα n)
    (fun n => χ n*markedPhysicalRestrictedBeta Sβ β n) z

theorem markedPhysicalTypeIICharacterEndpoint_bounds
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,0 < e j) (hinj : Function.Injective e)
    (δ C : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop,∀ (U V : ℝ),0 < U → 0 < V →
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ),
      (∀ n∈Sα,x^δ ≤ (n:ℝ)) → (∀ n∈Sβ,‖β n‖ ≤ (Real.log x)^C) →
      (∀ z : ℤ × ℤ,‖markedPhysicalTypeIICharacterEndpoint e x χ Sα Sβ modulation β z‖^2 ≤
        (Real.log x)^(2*C+4)) ∧
      markedPhysicalEndpointEnergy (fun j => markedLogPowerBand (e j) x) (markedPadSlots x)
        (markedPhysicalPrimitiveBox U (16*U) V (2*V))
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
        (fun n => χ n*markedMajorRestrictedCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) modulation Sα n)
        (fun n => χ n*markedPhysicalRestrictedBeta Sβ β n) ≤ 32*(U*V)*(Real.log x)^(2*C+4) := by
  filter_upwards [markedPhysicalTypeIIEndpoint_bounds e he hinj δ C hδ] with x hx
  intro U V hU hV q χ Sα Sβ modulation β hSα hβ
  have hb := hx U V hU hV Sα Sβ modulation β hSα hβ
  constructor
  · intro z
    exact (pow_le_pow_left₀ (norm_nonneg _) (markedPhysicalEndpointVector_character_norm_le
      (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) χ _ _ z) 2).trans (hb.1 z)
  · exact (markedPhysicalEndpointEnergy_character_le _ _ _ _
      (fun _ => by unfold bandReciprocalMass; positivity) χ _ _).trans hb.2

theorem markedPhysicalTypeIICharacter_alpha_eq {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W modulation : ℝ) (S : Finset ℕ) (n : ℕ) :
    χ n*markedMajorRestrictedCoefficient W modulation S n =
      if n∈S then giantFixedCharacterReplacementCoefficient χ W modulation n else 0 := by
  unfold markedMajorRestrictedCoefficient giantFixedCharacterReplacementCoefficient
  split_ifs <;> simp

end
end ArtinMatthews
