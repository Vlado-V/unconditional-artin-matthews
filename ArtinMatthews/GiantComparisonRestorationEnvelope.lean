module

public import ArtinMatthews.GiantCandidateAllocationCore
public import ArtinMatthews.GiantCandidateFirstEndpoint
public import ArtinMatthews.GiantComparisonListRestoration
public import ArtinMatthews.GiantSignedJoinedSourceFamily
public import ArtinMatthews.GiantComparisonAuxiliaryScale
public import ArtinMatthews.GiantComparisonOrderedMoment
public import ArtinMatthews.GiantComparisonRestorationBudget
public import ArtinMatthews.GiantComparisonRestorationRows
public import ArtinMatthews.GiantComparisonRowWeights
public import ArtinMatthews.GiantComparisonSharedLoss
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

/-! The actual unmasked row error has arbitrary logarithmic saving.
Both the copied collision and auxiliary divisibility estimates act on
the original ordered endpoint weights at their literal scale. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantCandidateComparisonRestorationEnvelope_eventually {I : Type*} [Fintype I]
    (e : I → ℝ) (he : ∀ i, 0 < e i ∧ e i < 1) {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    {m : ℕ} (hm : 0 < m) (χ : DirichletCharacter ℂ m)
    {γ : ℝ} (hγ : 0 < γ) (j : ℕ) (hj : 0 < j) (k : ℕ)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (Ψ : ℝ → ℂ)
    {a b B : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hΨ : ∀ y ∉ Set.Icc a b, Ψ y = 0) (hB : ∀ y, ‖Ψ y‖ ≤ B) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (S : Finset (GiantCandidateGroupIndex x))
        (CB : GiantCandidatePerformedBig S → Finset (Fin k)),
      let P (g : S) := giantCandidateGroup x g.val
      let C₀ := giantCandidatePerformedPattern S CB
      let W := giantComparisonOrderedFreeWeight P C₀ 1 q
      let F := giantCandidateFirstEndpoint e ε x
      let G := giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
        (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j
      ∀ (aux : GiantTwoSidedPatternAuxiliary P C₀),
      let d := giantTwoSidedPatternAuxiliaryProduct aux
      (∑ w ∈ Ioc 0 ⌊x^2⌋₊, ‖giantComparisonPositionKernel x Ψ χ F G d w‖*W w*W (w+d)*
        giantComparisonRestorationLoss aux q w (w+d)) ≤ C*(Real.log x)^(-A) := by
  letI : NeZero m := ⟨hm.ne'⟩
  let R := b+1
  have hR : 1 ≤ R := by dsimp [R]; linarith
  obtain ⟨C,hC,D,_hD,hmom⟩ := giantCandidateComparisonOrderedFourth_eventually
    e he hε hεq χ hγ hR j hj k
  let H := (B*Real.sqrt b/a)*C^(1/2:ℝ)
  let K := (k:ℝ)*giantCandidateGroupLogRate
  have hB0 : 0 ≤ B := (norm_nonneg (Ψ 0)).trans (hB 0)
  have hH : 0 ≤ H := mul_nonneg (div_nonneg (mul_nonneg hB0 (Real.sqrt_nonneg _)) ha.le)
    (Real.rpow_nonneg hC.le _)
  refine ⟨H+1,by linarith,?_⟩
  filter_upwards [hmom,giantCandidateComparisonAuxiliaryScale_eventually k,
    giantCandidateComparisonSharedLoss_eventually k 3 (by norm_num) hq hq1 (A+D/2),
    giantCandidateComparisonAuxiliarySlots_log_bound k,
    giantComparisonRestorationLogBudget_eventually A (D/2) H K,
    giantCandidateSelectedGroups_geometry_eventually,
    eventually_ge_atTop (2:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)]
    with x hmoment hscale hshared hslot hbudget hgeo hx hlog
  intro S CB
  dsimp only
  intro aux
  let P (g : S) := giantCandidateGroup x g.val
  let C₀ := giantCandidatePerformedPattern S CB
  let W := giantComparisonOrderedFreeWeight P C₀ 1 q
  let F := giantCandidateFirstEndpoint e ε x
  let G := giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
    (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j
  let d := giantTwoSidedPatternAuxiliaryProduct aux
  let Y := x*(d:ℝ)
  let L := Real.log x
  let η := L^(-(A+D/2))
  let U (n : ℕ) := F n*(W n:ℂ)
  let V (n : ℕ) := (χ n*G n)*(W n:ℂ)
  let Z := Ioc 0 ⌊x^2⌋₊
  let T := Z ∩ Ioc 0 ⌊b*Y⌋₊
  let f (w : ℕ) := ‖giantComparisonPositionKernel x Ψ χ F G d w‖*W w*W (w+d)*
    giantComparisonRestorationLoss aux q w (w+d)
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num) hx
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hL : 0 < L := zero_lt_one.trans_le hlog
  obtain ⟨hdpos,hd,hY,hYX⟩ := hscale S C₀ aux
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hV (g : S) : 0 < bandReciprocalMass (P g) :=
    (div_pos (Real.log_pos (by norm_num)) (by norm_num)).trans ((hgeo S).2.1 g).1
  have hW (n : ℕ) : 0 ≤ W n := giantComparisonOrderedFreeWeight_nonneg C₀ 1 n hV hq.le
  have hdy : (d:ℝ) ≤ Y := calc
    _ = 1*(d:ℝ) := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hx1.le (Nat.cast_nonneg _)
  have hRarg : b*Y+(d:ℝ) ≤ R*Y := by dsimp only [R]; nlinarith only [hdy]
  have hZR : Ioc 0 ⌊b*Y+(d:ℝ)⌋₊ ⊆ Ioc 0 ⌊R*Y⌋₊ := by
    intro n hn
    exact mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1,(mem_Ioc.mp hn).2.trans (Nat.floor_mono hRarg)⟩
  have hZL : Ioc 0 ⌊b*Y⌋₊ ⊆ Ioc 0 ⌊R*Y⌋₊ := by
    intro n hn
    have ha' : b*Y ≤ R*Y := (le_add_of_nonneg_right (Nat.cast_nonneg d)).trans hRarg
    exact mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1,(mem_Ioc.mp hn).2.trans (Nat.floor_mono ha')⟩
  have hfourth := hmoment S C₀ Y hY hYX q ⟨hq.le,hq1⟩ _ _ hZL hZR
  have hU4 : sourceComparisonFourthMass ⌊b*Y⌋₊ U ≤ C*Y*L^D := hfourth.1
  have hV4 : sourceComparisonFourthMass ⌊b*Y+(d:ℝ)⌋₊ V ≤ C*Y*L^D := hfourth.2
  have hT : T ⊆ Ioc 0 ⌊b*Y⌋₊ := inter_subset_right
  have hη : 0 ≤ η := Real.rpow_nonneg hL.le _
  have hQ : ∀ w ∈ T, ((q⁻¹)^(2*(k*Fintype.card S))+1)*giantComparisonSharedBadMass aux w (w+d) ≤ η := by
    intro w hw
    have hwZ := mem_Ioc.mp (mem_inter.mp hw).1
    have hwp : 0 < w+d := by omega
    have hwx : (w:ℝ) ≤ x^2 := (Nat.cast_le.mpr hwZ.2).trans (Nat.floor_le (sq_nonneg _))
    have hxx : x ≤ x^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hx1.le) hx0.le]
    have hxt : 2*x^2 ≤ x^3 := by nlinarith only [mul_le_mul_of_nonneg_right hx (sq_nonneg x)]
    have hwx3 : (w:ℝ) ≤ x^(3:ℝ) := by
      rw [show x^(3:ℝ) = x^3 by norm_num]
      linarith only [hwx,hxt,sq_nonneg x]
    have hwx3' : ((w+d:ℕ):ℝ) ≤ x^(3:ℝ) := by
      rw [show x^(3:ℝ) = x^3 by norm_num,Nat.cast_add]
      linarith only [hwx,hd,hxx,hxt]
    exact hshared S C₀ aux w (w+d) hwZ.1 hwp hwx3 hwx3'
  have hclip : (∑ w ∈ Z, f w) = ∑ w ∈ T, f w := by
    symm
    apply sum_subset inter_subset_left
    intro w hw hwt
    have hzero : Ψ ((w:ℝ)/Y) = 0 := by
      apply hΨ
      intro hs
      apply hwt
      exact mem_inter.mpr ⟨hw,mem_Ioc.mpr ⟨(mem_Ioc.mp hw).1,
        Nat.le_floor ((div_le_iff₀ hY0).mp hs.2)⟩⟩
    change Ψ ((w:ℝ)/(x*(d:ℝ))) = 0 at hzero
    simp only [f,giantComparisonPositionKernel,hzero,zero_div,zero_mul,norm_zero]
  let E₀ := (B*Real.sqrt b/a)*Y^(-(1/2:ℝ))*
    (sourceComparisonFourthMass ⌊b*Y⌋₊ U)^(1/4:ℝ)*
    (sourceComparisonFourthMass ⌊b*Y+(d:ℝ)⌋₊ V)^(1/4:ℝ)
  let E := Real.exp (-(L^(39/100:ℝ))/2)
  let M := (Fintype.card (Σ g : S, ↥(C₀ g)):ℝ)
  have hE₀ : E₀ ≤ H*L^(D/2) := by
    have hU0 : 0 ≤ sourceComparisonFourthMass ⌊b*Y⌋₊ U := by
      unfold sourceComparisonFourthMass
      positivity
    have hV0 : 0 ≤ sourceComparisonFourthMass ⌊b*Y+(d:ℝ)⌋₊ V := by
      unfold sourceComparisonFourthMass
      positivity
    have hs := giantComparisonFourthFactors_le hC hY0 hL hU0 hV0 hU4 hV4
    unfold E₀ H
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs
      (div_nonneg (mul_nonneg hB0 (Real.sqrt_nonneg _)) ha.le)
  change (∑ w ∈ Z, f w) ≤ (H+1)*L^(-A)
  calc
    _ = ∑ w ∈ T, f w := hclip
    _ ≤ E₀*(η+M*E) := giantCandidateComparisonRestorationRows_le hx1 hlog S CB aux
      hV hq Ψ χ F G W hW ha hb hη hΨ hB T hT hQ
    _ ≤ H*L^(D/2)*(η+(K*L)*E) := by
      apply mul_le_mul hE₀
      · exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (hslot S C₀) (Real.exp_nonneg _))
      · exact add_nonneg hη (mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _))
      · exact mul_nonneg hH (Real.rpow_nonneg hL.le _)
    _ ≤ _ := hbudget

end
end ArtinMatthews
