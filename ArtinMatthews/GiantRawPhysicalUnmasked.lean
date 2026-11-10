module

public import ArtinMatthews.GiantRawPhysicalPattern
public import ArtinMatthews.GiantTwoSidedPhysicalResidualExpansion
public import ArtinMatthews.GiantTwoSidedRawCorrelation
public import ArtinMatthews.GiantRawPhysicalCutoff
public import ArtinMatthews.GiantTwoSidedSharedLists
public import ArtinMatthews.MarkedPhysicalEndpointRecovery
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

/-! The raw cutoff itself restricts both positions to the original boxes.
This lets the comparison family use the larger common carrier with unmasked endpoints. -/

namespace ArtinMatthews
open Finset
open scoped BigOperators ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k : ℕ} {U : Finset ℕ}

private theorem raw_positions_of_nonzero_cutoff
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T) (Ψ : ℝ → ℂ) (hΨ : ∀ t, T < t → Ψ t = 0)
    (s t : GiantTwoSidedEndpointState P (k+1) U) (hs : 0 < s.val.1.val)
    (he : GiantTwoSidedRawPhysicalCondition s t)
    (hcut : Ψ ((s.val.1.val : ℝ) / (x * (giantTwoSidedRawPrefixProduct s.val.2 : ℝ))) ≠ 0) :
    s.val.1.val ∈ giantTwoSidedRawPositionBox P k ⌊T*x⌋₊ ∧
      t.val.1.val ∈ giantTwoSidedRawPositionBox P k (⌊T*x⌋₊+1) := by
  let a := markedPhysicalMarkingSplit k s.val.2
  let D := markedPhysicalMarkingProduct a.1
  have ha : (markedPhysicalMarkingSplit k).symm (a.1, a.2) = s.val.2 :=
    (markedPhysicalMarkingSplit k).symm_apply_apply _
  have hdist := (giantTwoSidedSplit_distinct_iff a.1 a.2).mp (by simpa only [ha] using s.property.1)
  have hdiv := (giantTwoSidedSplit_divisibility_iff (n := s.val.1.val) a.1 a.2).mp
    (by simpa only [ha] using s.property.2)
  obtain ⟨w, hn⟩ := markedPhysicalMarkingProduct_dvd hP hdis a.1 hdist.1 hdiv.1
  change s.val.1.val = D*w at hn
  have hD : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (markedPhysicalMarkingProduct_pos hP a.1).ne'
  have hw : 0 < w := Nat.pos_of_ne_zero (by intro hw; simp [hn, hw] at hs)
  have harg : (s.val.1.val : ℝ) / (x * (giantTwoSidedRawPrefixProduct s.val.2 : ℝ)) = (w : ℝ)/x := by
    change (s.val.1.val : ℝ) / (x * (D : ℝ)) = (w : ℝ)/x
    rw [hn, Nat.cast_mul]
    field_simp [hD, hx.ne']
  have hwN : w ≤ ⌊T*x⌋₊ := by
    apply le_of_not_gt
    intro hwN
    have hreal := (Nat.floor_lt (mul_nonneg hT hx.le)).mp hwN
    apply hcut
    rw [harg]
    exact hΨ _ ((lt_div_iff₀ hx).mpr hreal)
  have htarget : t.val.1.val = D*(w+1) := by
    have heq : t.val.1.val = s.val.1.val + D := he.2
    rw [heq, hn, Nat.mul_add, Nat.mul_one]
  have hbox := giantTwoSidedRawPositionBox_cover hP a.1 ⟨w, mem_Ioc.mpr ⟨hw, hwN⟩⟩
  rw [hn, htarget]
  exact hbox

private theorem raw_empty_dilation_eq_prefix (a : MarkedPhysicalMarking P (k+1))
    (aux : GiantTwoSidedPatternAuxiliary P (giantTwoSidedRawEmptyPattern J k)) :
    giantTwoSidedPatternDilation (giantTwoSidedRawEmptyPattern J k) a aux =
      giantTwoSidedRawPrefixProduct a := by
  simp [giantTwoSidedPatternDilation, giantTwoSidedRaw_copiedProduct,
    giantTwoSidedPatternAuxiliaryProduct]

/-- The two masks are redundant on the actual raw pattern whenever the
common position set is positive. The cutoff and the edge condition supply
both box bounds for every summand. -/
theorem giantTwoSidedPhysicalRawCutoffPairing_remove_box_masks
    (hP : ∀ j p, p ∈ P j → p.Prime) (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hU : ∀ n ∈ U, 0 < n) {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T)
    (Ψ : ℝ → ℂ) (hΨ : ∀ t, T < t → Ψ t = 0) (q ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P (giantTwoSidedRawEmptyPattern J k) 1) (f g : ℕ → ℂ) :
    giantTwoSidedPhysicalPatternCutoffPairing (P := P) (Z := U) (giantTwoSidedRawEmptyPattern J k) 1 q ζ K Ψ x
      (fun n => if n ∈ giantTwoSidedRawPositionBox P k ⌊T*x⌋₊ then f n else 0)
      (fun t => if t.val.1.val ∈ giantTwoSidedRawPositionBox P k (⌊T*x⌋₊+1) then g t.val.1.val else 0) =
    giantTwoSidedPhysicalPatternCutoffPairing (P := P) (Z := U) (giantTwoSidedRawEmptyPattern J k) 1 q ζ K Ψ x f
      (fun t => g t.val.1.val) := by
  classical
  unfold giantTwoSidedPhysicalPatternCutoffPairing
  refine congrArg (fun v : ℂ => (markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+1) : ℂ) *
    (giantTwoSidedResidueSlotNormalization (J := J) (k+1) : ℂ) * v) ?_
  refine Finset.sum_congr rfl fun π _ => ?_
  refine Finset.sum_congr rfl fun τ _ => ?_
  refine Finset.sum_congr rfl fun aux _ => ?_
  refine Finset.sum_congr rfl fun s _ => ?_
  refine Finset.sum_congr rfl fun t _ => ?_
  let s' := giantTwoSidedEndpointPermute π s
  let t' := giantTwoSidedEndpointPermute τ t
  let C := giantTwoSidedRawEmptyPattern J k
  by_cases he : GiantTwoSidedPatternCondition C 1 s' t' aux
  · rw [raw_empty_dilation_eq_prefix]
    by_cases hcut : Ψ ((s.val.1.val : ℝ)/(x*(giantTwoSidedRawPrefixProduct s'.val.2 : ℝ))) = 0
    · dsimp only [s'] at hcut
      simp only [hcut, zero_div, mul_zero, zero_mul]
    · have hraw := (giantTwoSidedRaw_patternCondition_iff s' t' aux).mp he
      have hbox := raw_positions_of_nonzero_cutoff hP hdis hx hT Ψ hΨ s' t'
        (hU _ s.val.1.property) hraw hcut
      have hs : s.val.1.val ∈ giantTwoSidedRawPositionBox P k ⌊T*x⌋₊ := hbox.1
      have ht : t.val.1.val ∈ giantTwoSidedRawPositionBox P k (⌊T*x⌋₊+1) := hbox.2
      simp only [ite_eq_left hs, ite_eq_left ht]
  · have hz : giantTwoSidedPatternPhysicalCoefficient 1 q ζ K s' t' aux = 0 := by
      unfold giantTwoSidedPatternPhysicalCoefficient
      exact ite_eq_right he
    simp only [s', t'] at hz
    simp only [hz, zero_mul]

theorem giantTwoSidedRawPhysical_sum_eq_unmasked_patternCutoffPairing
    (hP : ∀ j p, p ∈ P j → p.Prime) (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hU : ∀ n ∈ U, 0 < n) {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T)
    (hZ : giantTwoSidedRawPositionBox P k ⌊T*x⌋₊ ⊆ U)
    (hZ' : giantTwoSidedRawPositionBox P k (⌊T*x⌋₊+1) ⊆ U)
    (q : ℝ) (Ψ : ℝ → ℂ) (hΨ : ∀ t, T < t → Ψ t = 0)
    {m : ℕ} (χ : DirichletCharacter ℂ m) (F G L : ℕ → ℂ) :
    (∑ e : GiantTwoSidedRawPhysicalEdge P k (giantTwoSidedRawPositionBox P k ⌊T*x⌋₊)
        (giantTwoSidedRawPositionBox P k (⌊T*x⌋₊+1)),
      L e.val.1.val.1.val * giantTwoSidedRawPhysicalTerm x q Ψ χ F G e) =
      giantTwoSidedPhysicalPatternCutoffPairing (P := P) (Z := U) (giantTwoSidedRawEmptyPattern J k)
        1 q 0 (giantTwoSidedRawPatternCoefficient χ) Ψ x (giantTwoSidedRawPairLeft P k q F L)
        (fun t => giantTwoSidedRawPairRight P k q χ G t.val.1.val) :=
  (giantTwoSidedRawPhysical_sum_eq_patternCutoffPairing hZ hZ' x q Ψ χ F G L).trans
    (giantTwoSidedPhysicalRawCutoffPairing_remove_box_masks hP hdis hU hx hT Ψ hΨ q 0
      (giantTwoSidedRawPatternCoefficient χ) (giantTwoSidedRawPairLeft P k q F L)
      (giantTwoSidedRawPairRight P k q χ G))

theorem giantCandidateActualRawPhysicalSum_eq_unmasked_patternCutoffPairing
    {ι : Type*} [Fintype ι] (e : ι → ℝ) (C : Finset ℕ) {m : ℕ} (χ : DirichletCharacter ℂ m)
    (ε : ℝ) (Φ : ℝ → ℝ) {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T) (hΦ : ∀ t, T < t → Φ t = 0)
    (γ q : ℝ) (j : ℕ)
    (hP : ∀ j p, p ∈ P j → p.Prime) (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hU : ∀ n ∈ U, 0 < n) (hZ : giantTwoSidedRawPositionBox P k ⌊T*x⌋₊ ⊆ U)
    (hZ' : giantTwoSidedRawPositionBox P k (⌊T*x⌋₊+1) ⊆ U) :
    let F := giantCandidateFirstEndpoint e ε x
    let G := giantCandidateAllocationCore C (univ.biUnion P)
      (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j
    let Ψ (t : ℝ) : ℂ := ((t*Φ t : ℝ) : ℂ)
    let d (n : ℕ) : ℂ := giantTwoSidedEndpointDamping P (k+1) q n
    giantCandidateActualRawPhysicalSum C P e χ ε Φ T γ q j k x =
      giantTwoSidedPhysicalPatternCutoffPairing (P := P) (Z := U) (giantTwoSidedRawEmptyPattern J k)
        1 q 0 (giantTwoSidedRawPatternCoefficient χ) Ψ x (fun n => d n * conj (F n))
        (fun t => d t.val.1.val * (χ t.val.1.val * G t.val.1.val)) := by
  intro F G Ψ d
  have hΨ (t : ℝ) (ht : T < t) : Ψ t = 0 := by simp only [Ψ, hΦ _ ht, mul_zero, Complex.ofReal_zero]
  have h := giantTwoSidedRawPhysical_sum_eq_unmasked_patternCutoffPairing hP hdis hU hx hT hZ hZ'
    q Ψ hΨ χ F G (fun _ => 1)
  have hf : giantTwoSidedRawPairLeft P k q F (fun _ => 1) = (fun n => d n * conj (F n)) := by
    funext n
    simp only [giantTwoSidedRawPairLeft, map_one, mul_one, d]
    exact mul_comm _ _
  have hg (n : ℕ) : giantTwoSidedRawPairRight P k q χ G n = d n * (χ n * G n) := mul_comm _ _
  rw [hf] at h
  simpa only [one_mul, giantCandidateActualRawPhysicalSum, hg, F, G, Ψ] using h

end
end ArtinMatthews
