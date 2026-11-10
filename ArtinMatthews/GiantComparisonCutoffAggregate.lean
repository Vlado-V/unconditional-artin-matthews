module

public import ArtinMatthews.GiantCandidateRetainedCorrelationAssembly
public import ArtinMatthews.GiantComparisonCellIdentity
public import ArtinMatthews.GiantComparisonCellAggregate
public import ArtinMatthews.GiantComparisonCellCountBudget
public import ArtinMatthews.GiantComparisonOccupiedCell
public import ArtinMatthews.GiantComparisonPerformedRestoration
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Topology.UniformSpace.Uniformizable


set_option backward.privateInPublic true
@[expose] public section

/-! Sum all occupied cells and return the discarded copied-label
collision contribution to the original smooth physical cutoff. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators ComplexConjugate ContDiff
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

private theorem comparison_restoration_cost_le {L CQ Cξ ξ : ℝ} {Q : ℕ}
    (hL : 0 < L) (hQ : (Q:ℝ) ≤ L^CQ) (hξ : L^(-Cξ) ≤ ξ) :
    (((Q:ℝ)^2)/ξ)^2 ≤ L^(4*CQ+2*Cξ) := by
  have hξ₀ : 0 < ξ := (Real.rpow_pos_of_pos hL _).trans_le hξ
  have hInv : ξ⁻¹ ≤ L^Cξ := by
    have h := inv_anti₀ (Real.rpow_pos_of_pos hL (-Cξ)) hξ
    rwa [Real.rpow_neg hL.le, inv_inv] at h
  have hBound : ((Q:ℝ)^2)/ξ ≤ (L^CQ)^2*L^Cξ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hQ _) hInv
      (inv_nonneg.mpr hξ₀.le) (sq_nonneg _)
  calc
    _ ≤ ((L^CQ)^2*L^Cξ)^2 :=
      pow_le_pow_left₀ (div_nonneg (sq_nonneg _) hξ₀.le) hBound _
    _ = _ := by
      rw [← Real.rpow_two (L^CQ), ← Real.rpow_mul hL.le, ← Real.rpow_add hL,
        ← Real.rpow_two, ← Real.rpow_mul hL.le]
      congr 1
      ring

theorem giantCandidatePerformedComparisonLogSaving_of_cell_bounds
    {I : Type*} [Fintype I] (e : I → ℝ)
    (he : ∀ i, (1/10:ℝ) < e i ∧ e i < 1/5)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    {M : ℕ} (hM : 0 < M) (χ : DirichletCharacter ℂ M)
    {γ : ℝ} (hγ : 0 < γ) (j : ℕ) (hj : 0 < j) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (Ψ : ℝ → ℂ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hΨ : ContDiff ℝ ∞ Ψ) (hsupp : Function.support Ψ ⊆ Set.Icc a b)
    (hCell : ∀ (m : ℕ) (E : ℝ), 0 ≤ E → ∀ᶠ x : ℝ in atTop,
      ∀ (S : Finset (GiantCandidateGroupIndex x)), Nonempty (GiantCandidatePerformedSmall S) →
      ∀ {k : ℕ} (A B : Finset (GiantCandidatePerformedBig S × Fin k)), A.Nonempty → B.Nonempty →
      (∀ g, (idealResidualCopied (some (A,B)) g).card ≤ m) →
      ∀ (Q : ℕ) (h ξ : ℝ), 0 < h → Real.exp h ≤ 2 → 0 < ξ →
      let PB := giantCandidatePerformedBigBand S
      let P (i : S) := giantCandidateGroup x i.val
      ∀ (i : GiantComparisonCellIndex (idealResidualBands PB A) h Q)
        (l : GiantComparisonCellIndex (idealResidualBands PB B) h Q),
      ‖giantCandidateComparisonWeightedCell S (ell:=1) A B χ (giantCandidateFirstEndpoint e ε x)
        (giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
          (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j) Ψ q ⌊x^2⌋₊ ξ i l‖ ≤
        (Real.log x)^(-E)) :
    GiantCandidatePerformedComparisonLogSaving e χ ε γ q j Ψ := by
  intro k m CQ Ch Cξ E hCQ hCh hCξ hE
  let C₀ := giantCandidateGroupLogRate
  have hC₀ : 0 ≤ C₀ := by unfold C₀ giantCandidateGroupLogRate; positivity
  let Erest := E+4*CQ+2*Cξ+2
  obtain ⟨Ecost,hEc,hCount⟩ := giantComparisonCellCountBudget_eventually m C₀ (45/100)
    CQ Ch Cξ hC₀ (by norm_num) hCQ hCh hCξ
  let Ecell := E+Ecost+1
  have hEcell : 0 ≤ Ecell := by unfold Ecell; positivity
  have hΨc : HasCompactSupport Ψ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  obtain ⟨BΨ,hBΨ⟩ := hΨc.exists_bound_of_continuous hΨ.continuous
  have hzero (z : ℝ) (hz : z ∉ Set.Icc a b) : Ψ z = 0 :=
    Function.notMem_support.mp (fun hm => hz (hsupp hm))
  obtain ⟨K,hK,hRestore⟩ := giantCandidatePerformedComparisonCutoff_restored_eventually
    e (fun i => ⟨by linarith [(he i).1], (he i).2.le⟩) hε hεq hM χ hγ j hj k hq hq1
    Ψ ha (ha.le.trans hab) hzero hBΨ Erest
  filter_upwards [hRestore, hCell m Ecell hEcell, Real.tendsto_log_atTop.eventually hCount,
    giantCandidateSelectedGroups_geometry_eventually, giantCandidateGroup_total_count_eventually,
    eventually_gt_atTop (1:ℝ), Real.tendsto_log_atTop.eventually_ge_atTop (max 2 K)]
    with x hrestore hcell hcount hgeo hcard hx hL
  intro L S hsmall Big PB P A B hA hB hAB hcap Q h ξ hQ hhL hhexp hξL C K₀ F G d
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hL
  have hL1 : 1 ≤ L := (by norm_num : (1:ℝ) ≤ 2).trans hL2
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hK' : K ≤ L := (le_max_right _ _).trans hL
  have hh : 0 < h := (Real.rpow_pos_of_pos hLp _).trans_le hhL
  have hξ : 0 < ξ := (Real.rpow_pos_of_pos hLp _).trans_le hξL
  have hPB (g : Big) (p : ℕ) (hp : p ∈ PB g) : p.Prime :=
    (giantCandidateBigGroup_range hx hL1 hp).1
  have hPBupper (g : Big) (p : ℕ) (hp : p ∈ PB g) :
      (p:ℝ) ≤ Real.exp (L^(45/100:ℝ)) := (giantCandidateBigGroup_range hx hL1 hp).2.2.le
  have hPBcard : (Fintype.card Big:ℝ) ≤ C₀*Real.log L :=
    (Nat.cast_le.mpr (giantCandidateComparisonBig_card_le S)).trans hcard
  obtain ⟨hcapA,hcapB⟩ := giantComparisonCopied_cap A B hcap
  have hbudget := hcount PB A B hPBcard hcapA hcapB hPB hPBupper Q h ξ hQ hh hhL hξL
  let SumI := ∑ aux : GiantTwoSidedPatternAuxiliary P C,
    giantComparisonIndependentAuxiliarySum ⌊x^2⌋₊ x q Ψ χ F G
      (giantCandidateComparisonIndependentCoefficient S (ell:=1) A B Q h ξ) aux
  let Raw := giantTwoSidedPhysicalPatternCutoffPairing (Z := Ioc 0 ⌊x^2⌋₊) C 1 q 0
    (giantComparisonCharacterCoefficient χ K₀) Ψ x (fun n => d n*conj (F n))
    (fun t => d t.val.1.val*(χ t.val.1.val*G t.val.1.val))
  have hErr : ‖Raw-SumI‖ ≤ L^(-(E+1)) := by
    have hs : ‖Raw-SumI‖ ≤ K*(((Q:ℝ)^2)/ξ)^2*L^(-Erest) := by
      have hs' := hrestore S A B Q h ξ hξ
      change ‖giantTwoSidedPhysicalPatternCutoffPairing (Z := Ioc 0 ⌊x^2⌋₊) C 1 q 0
        (giantComparisonCharacterCoefficient χ K₀) Ψ x (fun n => d n*conj (F n))
        (fun t => d t.val.1.val*χ t.val.1.val*G t.val.1.val) - SumI‖ ≤ _ at hs'
      simpa only [Raw,mul_assoc] using hs' 
    have ht : (((Q:ℝ)^2)/ξ)^2 ≤ L^(4*CQ+2*Cξ) := comparison_restoration_cost_le hLp hQ hξL
    calc
      _ ≤ _ := hs
      _ ≤ L*L^(4*CQ+2*Cξ)*L^(-Erest) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hK' ht (sq_nonneg _) hLp.le)
          (Real.rpow_nonneg hLp.le _)
      _ = (L^(1:ℝ)*L^(4*CQ+2*Cξ))*L^(-Erest) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add hLp, ← Real.rpow_add hLp]
        congr 1
        dsimp only [Erest]
        ring
  have hInd : ‖SumI‖ ≤ L^(-(E+1)) := by
    have h := giantCandidateComparisonIndependent_norm_le S (ell:=1) A B hAB Q h hξ χ F G Ψ q
      ⌊x^2⌋₊ (hgeo S).1 (W:=L^(-Ecell))
      (hcell S hsmall A B hA hB hcap Q h ξ hh hhexp hξ)
    refine h.trans ((mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg hLp.le _)).trans_eq ?_)
    rw [← Real.rpow_add hLp]
    congr 1
    dsimp only [Ecell]
    ring
  change ‖Raw‖ ≤ L^(-E)
  calc
    _ ≤ ‖Raw-SumI‖+‖SumI‖ := by simpa only [sub_add_cancel] using norm_add_le (Raw-SumI) SumI
    _ ≤ L^(-(E+1))+L^(-(E+1)) := add_le_add hErr hInd
    _ = (2*L⁻¹)*L^(-E) := by
      rw [show -(E+1)=-E+(-1) by ring, Real.rpow_add hLp, Real.rpow_neg_one]
      ring
    _ ≤ L^(-E) := mul_le_of_le_one_left (Real.rpow_nonneg hLp.le _)
      (by rw [← div_eq_mul_inv, div_le_one hLp]; exact hL2)

end
end ArtinMatthews
