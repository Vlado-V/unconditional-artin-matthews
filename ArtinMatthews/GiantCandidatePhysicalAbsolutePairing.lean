module

public import ArtinMatthews.GiantTwoSidedPhysicalAbsolutePairing
public import ArtinMatthews.GiantTwoSidedPatternAbsoluteActual
public import ArtinMatthews.MarkedPhysicalEndpointNorm
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Weighted finite Cauchy applies to the sum of the actual choice
norms, with the original constant state mass on both endpoints. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantTwoSidedPhysicalFamilyAbsolutePairing_le_of_rows_columns
    {I J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell) {Z : Finset ℕ} {B : ℝ}
    (hB : 0 ≤ B)
    (hrow : ∀ s : GiantTwoSidedEndpointState P (k+ell) Z,
      (∑ t : GiantTwoSidedEndpointState P (k+ell) Z,
        giantTwoSidedPhysicalFamilyAbsoluteEntry patterns C step q ζ K s t) ≤ B)
    (hcol : ∀ t : GiantTwoSidedEndpointState P (k+ell) Z,
      (∑ s : GiantTwoSidedEndpointState P (k+ell) Z,
        giantTwoSidedPhysicalFamilyAbsoluteEntry patterns C step q ζ K s t) ≤ B)
    (f : ℕ → ℂ) (g : GiantTwoSidedEndpointState P (k+ell) Z → ℂ) :
    giantTwoSidedPhysicalFamilyAbsolutePairing patterns C step q ζ K f g ≤
      B * Real.sqrt (∑ s : GiantTwoSidedEndpointState P (k+ell) Z,
        markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) * ‖f s.val.1.val‖^2) *
        Real.sqrt (∑ t : GiantTwoSidedEndpointState P (k+ell) Z,
          markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) * ‖g t‖^2) := by
  let State := GiantTwoSidedEndpointState P (k+ell) Z
  let σ := markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell)
  let A (s t : State) := giantTwoSidedPhysicalFamilyAbsoluteEntry patterns C step q ζ K s t
  let F (s : State) := ‖f s.val.1.val‖
  let G (t : State) := ‖g t‖
  let w (p : State × State) := σ * A p.1 p.2
  have hσ : 0 ≤ σ := markedPhysicalMass_nonneg _ _ (fun _ => sum_nonneg (fun _ _ => by positivity))
  have hw (p : State × State) : 0 ≤ w p :=
    mul_nonneg hσ (giantTwoSidedPhysicalFamilyAbsoluteEntry_nonneg patterns C step q ζ K p.1 p.2)
  let U (p : State × State) := Real.sqrt (w p) * F p.1
  let V (p : State × State) := Real.sqrt (w p) * G p.2
  have hUV (p : State × State) : U p * V p = w p * F p.1 * G p.2 := by
    calc
      _ = (Real.sqrt (w p))^2 * F p.1 * G p.2 := by dsimp only [U,V]; ring
      _ = _ := by rw [Real.sq_sqrt (hw p)]
  have hU (p : State × State) : U p ^ 2 = w p * F p.1 ^ 2 := by
    dsimp only [U]
    rw [mul_pow, Real.sq_sqrt (hw p)]
  have hV (p : State × State) : V p ^ 2 = w p * G p.2 ^ 2 := by
    dsimp only [V]
    rw [mul_pow, Real.sq_sqrt (hw p)]
  have hCS : (∑ s : State, ∑ t : State, w (s,t) * F s * G t) ≤
      Real.sqrt (∑ s : State, ∑ t : State, w (s,t) * F s ^ 2) *
        Real.sqrt (∑ s : State, ∑ t : State, w (s,t) * G t ^ 2) := by
    simpa only [hUV,hU,hV,Fintype.sum_prod_type] using
      Real.sum_mul_le_sqrt_mul_sqrt (univ : Finset (State × State)) U V
  have hquad (A' : State → State → ℝ) (hrow' : ∀ s, ∑ t, A' s t ≤ B) (v : State → ℝ) :
      (∑ s : State, ∑ t : State, σ * A' s t * (v s)^2) ≤ B * ∑ s : State, σ * (v s)^2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro s _
    calc
      _ = (σ * (v s)^2) * ∑ t : State, A' s t := by
        rw [mul_sum]
        apply sum_congr rfl
        intro t _
        ring
      _ ≤ (σ * (v s)^2) * B :=
        mul_le_mul_of_nonneg_left (hrow' s) (mul_nonneg hσ (sq_nonneg _))
      _ = _ := mul_comm _ _
  have hleft : (∑ s : State, ∑ t : State, w (s,t) * F s ^ 2) ≤
      B * ∑ s : State, σ * F s ^ 2 := hquad A hrow F
  have hright : (∑ s : State, ∑ t : State, w (s,t) * G t ^ 2) ≤
      B * ∑ t : State, σ * G t ^ 2 := by
    rw [sum_comm]
    exact hquad (fun t s => A s t) hcol G
  rw [giantTwoSidedPhysicalFamilyAbsolutePairing_eq_entries]
  change (∑ s : State, ∑ t : State, w (s,t) * F s * G t) ≤
    B * Real.sqrt (∑ s : State, σ * F s ^ 2) * Real.sqrt (∑ t : State, σ * G t ^ 2)
  calc
    _ ≤ Real.sqrt (∑ s : State, ∑ t : State, w (s,t) * F s ^ 2) *
        Real.sqrt (∑ s : State, ∑ t : State, w (s,t) * G t ^ 2) := hCS
    _ ≤ Real.sqrt (B * ∑ s : State, σ * F s ^ 2) *
        Real.sqrt (B * ∑ t : State, σ * G t ^ 2) :=
      mul_le_mul (Real.sqrt_le_sqrt hleft) (Real.sqrt_le_sqrt hright)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = (Real.sqrt B)^2 * Real.sqrt (∑ s : State, σ * F s ^ 2) *
        Real.sqrt (∑ t : State, σ * G t ^ 2) := by
      rw [Real.sqrt_mul hB, Real.sqrt_mul hB]
      ring
    _ = _ := by rw [Real.sq_sqrt hB]

theorem giantCandidatePhysicalFamily_absolute_pairing_eventually {I : Type*} (ell m₀ : ℕ)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (C₁ : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ x : ℝ in atTop, ∀ S : Finset (GiantCandidateGroupIndex x),
      let P (i : S) := giantCandidateGroup x i.val
      ∀ (k : ℕ) (patterns : Finset I) (C : I → S → Finset (Fin k)),
        (∀ ν ∈ patterns, ∀ i, (C ν i).card ≤ m₀) →
      ∀ (step : ℤ) (ζ : ℝ) (K : ∀ ν, GiantTwoSidedPatternCoefficient P (C ν) ell) (K₀ : I → ℝ),
        (∀ ν ∈ patterns, 0 ≤ K₀ ν ∧ ∀ b c a, ‖K ν b c a‖ ≤ K₀ ν) →
        (∑ ν ∈ patterns, K₀ ν) ≤ (Real.log x)^C₁ → ∀ (Z : Finset ℕ)
        (f : ℕ → ℂ) (g : GiantTwoSidedEndpointState P (k+ell) Z → ℂ),
        giantTwoSidedPhysicalFamilyAbsolutePairing patterns C step q ζ K f g ≤
          (Real.log x)^(C₁+A) *
            Real.sqrt (∑ s : GiantTwoSidedEndpointState P (k+ell) Z,
              markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) * ‖f s.val.1.val‖^2) *
            Real.sqrt (∑ t : GiantTwoSidedEndpointState P (k+ell) Z,
              markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) * ‖g t‖^2) := by
  obtain ⟨A,hA,hrows⟩ := giantCandidatePatternFamily_absolute_rows_columns_eventually (I := I) ell m₀ hq hq1 C₁
  refine ⟨A,hA,?_⟩
  filter_upwards [hrows, Real.tendsto_log_atTop.eventually_gt_atTop (0 : ℝ)] with x hx hL
  intro S
  dsimp only
  intro k patterns C hC step ζ K K₀ hK hmass Z f g
  have h := hx S k patterns C hC step ζ K K₀ hK hmass Z Z
  exact giantTwoSidedPhysicalFamilyAbsolutePairing_le_of_rows_columns patterns C step q ζ K
    (Real.rpow_nonneg hL.le (C₁+A)) h.1 h.2 f g

end
end ArtinMatthews
