module

public import ArtinMatthews.GiantTwoSidedPatternSlotAverage
public import ArtinMatthews.GiantCandidateGroups
public import ArtinMatthews.GiantCandidateSelectedGroups
public import ArtinMatthews.GiantTwoSidedPatternAbsoluteRows
public import ArtinMatthews.GiantTwoSidedPatternDamping
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

/-! The actual candidate groups supply the reciprocal masses and the
logarithmic bound on their number. The absolute physical Schur exponent
is independent of the copied-list length and the chosen pattern. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantCandidatePattern_absolute_rows_columns_eventually (ell m₀ : ℕ)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    ∃ A : ℝ,0≤A ∧ ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (i : S) := giantCandidateGroup x i.val
      ∀ (k : ℕ) (C : S → Finset (Fin k)), (∀ i,(C i).card ≤ m₀) →
      ∀ (step : ℤ) (ζ : ℝ) (K : GiantTwoSidedPatternCoefficient P C ell) (K₀ : ℝ),
        0≤K₀ → (∀ b c a,‖K b c a‖≤K₀) → ∀ Z Z' : Finset ℕ,
        (∀ s : GiantTwoSidedEndpointState P (k+ell) Z,
          (∑ t : GiantTwoSidedEndpointState P (k+ell) Z',giantTwoSidedSlotAverage
            (giantTwoSidedPatternAbsoluteEntry step q ζ K) s t) ≤ K₀*(Real.log x)^A) ∧
        (∀ t : GiantTwoSidedEndpointState P (k+ell) Z',
          (∑ s : GiantTwoSidedEndpointState P (k+ell) Z,giantTwoSidedSlotAverage
            (giantTwoSidedPatternAbsoluteEntry step q ζ K) s t) ≤ K₀*(Real.log x)^A) := by
  let v := Real.log 2/2
  have hv : 0<v := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  obtain ⟨B,hB,hslot⟩ := exists_giantTwoSidedPattern_slot_bound hq hq1 hv (ell+m₀)
  let A := giantCandidateGroupLogRate*Real.log B
  refine ⟨A,mul_nonneg (by unfold giantCandidateGroupLogRate; positivity) (Real.log_nonneg hB),?_⟩
  filter_upwards [giantCandidateSelectedGroups_geometry_eventually,giantCandidateFullPrimes_prime_upper_eventually,
    giantCandidateSelectedGroups_exponential_cost_eventually B hB] with x hgeo hprime hcost
  intro S
  let P (i : S) := giantCandidateGroup x i.val
  dsimp only
  intro k C hC step ζ K K₀ hK₀ hK Z Z'
  have hP (i : S) (p : ℕ) (hp : p∈P i) : p.Prime :=
    (hprime p (mem_giantCandidateFullPrimes.mpr ⟨i.val,hp⟩)).1
  have hV (i : S) : 0 < bandReciprocalMass (P i) := hv.trans ((hgeo S).2.1 i).1
  have hbudget (i : S) (z : ℕ) :
      (bandReciprocalMass (P i))⁻¹^(ell+(C i).card)*
      ((z:ℝ)+((ell+(C i).card:ℕ):ℝ))^(ell+(C i).card)*q^((z:ℝ)/2) ≤ B :=
    hslot _ _ _ ((hgeo S).2.1 i).1.le (Nat.add_le_add_left (hC i) _)
  have hBpow : B^Fintype.card S ≤ (Real.log x)^A := by rw [Fintype.card_coe]; exact hcost S
  have hrow (step : ℤ) (K : GiantTwoSidedPatternCoefficient P C ell)
      (hK : ∀ b c a,‖K b c a‖≤K₀) {U : Finset ℕ} (U' : Finset ℕ)
      (s : GiantTwoSidedEndpointState P (k+ell) U) :
      giantTwoSidedPatternAbsoluteRow step q ζ K U' s ≤ K₀*(Real.log x)^A :=
    (giantTwoSidedPatternAbsoluteRow_le hP (hgeo S).1 hV step hq hq1.le
      (zero_le_one.trans hB) hK₀ ζ K hK hbudget U' s).trans (mul_le_mul_of_nonneg_left hBpow hK₀)
  constructor
  · intro s
    apply giantTwoSidedSlotAverage_row_le
    intro u
    simp only [giantTwoSidedPatternAbsoluteEntry]
    rw [sum_comm]
    exact hrow step K hK Z' u
  · intro t
    apply giantTwoSidedSlotAverage_column_le
    intro u
    simp only [giantTwoSidedPatternAbsoluteEntry]
    rw [sum_comm]
    change giantTwoSidedPatternAbsoluteColumn step q ζ K Z u ≤ K₀*(Real.log x)^A
    rw [giantTwoSidedPatternAbsoluteColumn_eq_reverse hP hV step hq.le ζ K]
    exact hrow (-step) (fun b c a => K c b a) (fun b c a => hK c b a) Z u

theorem giantCandidatePatternFamily_absolute_rows_columns_eventually {I : Type*} (ell m₀ : ℕ)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (C₁ : ℝ) :
    ∃ A : ℝ,0≤A ∧ ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (i : S) := giantCandidateGroup x i.val
      ∀ (k : ℕ) (patterns : Finset I) (C : I → S → Finset (Fin k)),
        (∀ ν∈patterns,∀ i,(C ν i).card ≤ m₀) →
      ∀ (step : ℤ) (ζ : ℝ) (K : ∀ ν,GiantTwoSidedPatternCoefficient P (C ν) ell) (K₀ : I → ℝ),
        (∀ ν∈patterns,0≤K₀ ν ∧ ∀ b c a,‖K ν b c a‖≤K₀ ν) →
        (∑ ν∈patterns,K₀ ν) ≤ (Real.log x)^C₁ → ∀ Z Z' : Finset ℕ,
        (∀ s : GiantTwoSidedEndpointState P (k+ell) Z,
          (∑ t : GiantTwoSidedEndpointState P (k+ell) Z',∑ ν∈patterns,giantTwoSidedSlotAverage
            (giantTwoSidedPatternAbsoluteEntry step q ζ (K ν)) s t) ≤ (Real.log x)^(C₁+A)) ∧
        (∀ t : GiantTwoSidedEndpointState P (k+ell) Z',
          (∑ s : GiantTwoSidedEndpointState P (k+ell) Z,∑ ν∈patterns,giantTwoSidedSlotAverage
            (giantTwoSidedPatternAbsoluteEntry step q ζ (K ν)) s t) ≤ (Real.log x)^(C₁+A)) := by
  obtain ⟨A,hA,h⟩ := giantCandidatePattern_absolute_rows_columns_eventually ell m₀ hq hq1
  refine ⟨A,hA,?_⟩
  filter_upwards [h,Real.tendsto_log_atTop.eventually_gt_atTop (0:ℝ)] with x hx hL
  intro S
  dsimp only
  intro k patterns C hC step ζ K K₀ hK hmass Z Z'
  have hsum : (∑ ν∈patterns,K₀ ν*(Real.log x)^A) ≤ (Real.log x)^(C₁+A) := by
    rw [← sum_mul,Real.rpow_add hL]
    exact mul_le_mul_of_nonneg_right hmass (Real.rpow_nonneg hL.le _)
  constructor
  · intro s
    rw [sum_comm]
    exact (sum_le_sum fun ν hν => (hx S k (C ν) (hC ν hν) step ζ (K ν) (K₀ ν)
      (hK ν hν).1 (hK ν hν).2 Z Z').1 s).trans hsum
  · intro t
    rw [sum_comm]
    exact (sum_le_sum fun ν hν => (hx S k (C ν) (hC ν hν) step ζ (K ν) (K₀ ν)
      (hK ν hν).1 (hK ν hν).2 Z Z').2 t).trans hsum

end
end ArtinMatthews
