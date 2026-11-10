module

public import ArtinMatthews.GiantCandidateCoinSets
public import ArtinMatthews.GiantCandidateUnguardedCorrelation
public import ArtinMatthews.GiantComparisonCutoffPairing
public import ArtinMatthews.GiantSignedJoinedSourceFamily
public import ArtinMatthews.GiantCandidatePerformedRetention
public import ArtinMatthews.GiantCandidateRawResidualComposition
public import ArtinMatthews.GiantCandidateRetainedResidualCutoff
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


set_option backward.privateInPublic true
@[expose] public section

/-! After the full residual cutoff has been bounded, it suffices to
estimate each literal nonempty comparison on the same smooth cutoff.
The selected family's original size bound pays for their sum. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators ComplexConjugate ContDiff
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

def GiantCandidatePerformedComparisonLogSaving {I : Type*} [Fintype I] (e : I → ℝ)
    {M : ℕ} (χ : DirichletCharacter ℂ M) (ε γ q : ℝ) (j : ℕ) (Ψ : ℝ → ℂ) : Prop :=
  ∀ (k m : ℕ) (CQ Ch Cξ E : ℝ), 0 ≤ CQ → 0 ≤ Ch → 0 ≤ Cξ → 0 ≤ E →
    ∀ᶠ x : ℝ in atTop,
    let L := Real.log x
    ∀ groups : Finset (GiantCandidateGroupIndex x), Nonempty (GiantCandidatePerformedSmall groups) →
    let B := GiantCandidatePerformedBig groups
    let PB := giantCandidatePerformedBigBand groups
    let P := fun g : ↥groups => giantCandidateGroup x g.val
    ∀ first second : Finset (B × Fin k), first.Nonempty → second.Nonempty → Disjoint first second →
      (∀ g, (idealResidualCopied (some (first,second)) g).card ≤ m) →
    ∀ (Q : ℕ) (h ξ : ℝ), (Q : ℝ) ≤ L^CQ → L^(-Ch) ≤ h → Real.exp h ≤ 2 → L^(-Cξ) ≤ ξ →
    let C := giantCandidatePerformedPattern groups (idealResidualCopied (some (first,second)))
    let K : GiantTwoSidedPatternCoefficient P C 1 := giantCandidatePerformedCoefficient groups
      (idealResidualCoefficient PB Q h ξ (some (first,second)))
    let F := giantCandidateFirstEndpoint e ε x
    let G := giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
      (Real.exp (L^(6/25 : ℝ))) (x^γ) j
    let d (n : ℕ) := (giantTwoSidedEndpointDamping P (k+1) q n : ℂ)
    ‖giantTwoSidedPhysicalPatternCutoffPairing (Z := Ioc 0 ⌊x^2⌋₊) C 1 q 0
      (giantComparisonCharacterCoefficient χ K) Ψ x (fun n => d n * conj (F n))
      (fun t => d t.val.1.val * (χ t.val.1.val * G t.val.1.val))‖ ≤ L^(-E)

theorem giantResidualComparison_norm_sum_log_saving {B : Type*} [DecidableEq B] {k : ℕ}
    (probes₁ probes₂ : Finset (B × Fin k)) (f : Finset (B × Fin k) → Finset (B × Fin k) → ℂ)
    {L W E cost : ℝ} (hL : 0 < L) (hW : 1 ≤ W)
    (hcost : ((idealResidualPatterns probes₁ probes₂).card : ℝ)*W ≤ L^cost)
    (h : ∀ A ∈ probes₁.powerset.erase ∅, ∀ B' ∈ probes₂.powerset.erase ∅,
      ‖f A B'‖ ≤ L^(-(E+cost))) :
    (∑ A ∈ probes₁.powerset.erase ∅, ∑ B' ∈ probes₂.powerset.erase ∅, ‖f A B'‖) ≤ L^(-E) := by
  let S := probes₁.powerset.erase ∅
  let T := probes₂.powerset.erase ∅
  let family := idealResidualPatterns probes₁ probes₂
  have hc : S.card * T.card ≤ family.card := by
    rw [← card_product, ← card_image_of_injective (S ×ˢ T) (fun _ _ h => Option.some.inj h)]
    exact card_le_card subset_union_right
  have hc' : (S.card : ℝ) * (T.card : ℝ) ≤ (family.card : ℝ) := by exact_mod_cast hc
  have hf : (family.card : ℝ) ≤ L^cost :=
    (le_mul_of_one_le_right (Nat.cast_nonneg _) hW).trans hcost
  let R := L^(-(E+cost))
  have hR : 0 ≤ R := Real.rpow_nonneg hL.le _
  calc
    _ ≤ ∑ A ∈ S, ∑ B' ∈ T, R := sum_le_sum fun A hA => sum_le_sum fun B' hB => h A hA B' hB
    _ = ((S.card : ℝ) * (T.card : ℝ))*R := by simp only [sum_const,nsmul_eq_mul,mul_assoc]
    _ ≤ L^cost * R := mul_le_mul_of_nonneg_right (hc'.trans hf) hR
    _ = _ := by
      dsimp only [R]
      rw [← Real.rpow_add hL]
      congr 1
      ring

-- Elaboration specializes the dependent family coefficient at each probe pair.
set_option maxHeartbeats 800000 in
theorem giantCandidateRetainedCorrelationLogSaving_of_comparison
    {I : Type*} [Fintype I] (e : I → ℝ) (he : ∀ i, 0 < e i ∧ e i ≤ 1/5)
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) {a T γ q threshold : ℝ} (ha : 0 < a) (hT : 0 < T)
    (hsupp : Function.support Φ ⊆ Set.Icc a T) (hγ : 0 < γ) (hq : 0 < q) (hq1 : q < 1)
    (hthreshold : 0 < threshold) (j : ℕ) (hj : 0 < j)
    (hcomparison : GiantCandidatePerformedComparisonLogSaving e χ ε γ q j (fun t => ((t*Φ t : ℝ) : ℂ))) :
    ∀ A : ℝ, ∀ᶠ x : ℝ in atTop, ∀ S ∈ giantCandidateRetainedOutcomes x threshold,
      ‖giantCandidateActualUnguardedShiftedCorrelation (giantCandidateFullPrimes x)
        (fun i : ↥S => giantCandidateGroup x i.val) e χ ε Φ T γ q j x‖ ≤ (Real.log x)^(-A) := by
  intro A
  let save := max A 0 + 1
  let Ψ (t : ℝ) : ℂ := ((t*Φ t : ℝ) : ℂ)
  have hΨ : ContDiff ℝ ∞ Ψ := Complex.ofRealCLM.contDiff.comp (contDiff_id.mul hΦ)
  have hΨs : Function.support Ψ ⊆ Set.Icc a T := by
    intro t ht
    apply hsupp
    intro h
    exact ht (by simp [Ψ,h])
  have hhigh : ∀ t, T < t → Φ t = 0 := by
    intro t ht
    by_contra h
    exact (not_le_of_gt ht) (hsupp h).2
  have he' (i : I) : 0 < e i ∧ e i < 1 := ⟨(he i).1, (he i).2.trans_lt (by norm_num)⟩
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  obtain ⟨Eid,hEid,m,k,_,_,hselect⟩ := giantCandidateRetainedResidualCutoff_eventually e he'
    hε hεq χ threshold save γ hthreshold hγ j hj hq hq1 Ψ ha hΨs hΨ
  let C₀ := giantCandidateGroupLogRate
  let vmin := Real.log 2/2
  let d : ℝ := 45/100
  let CQ := idealSourceRationalExponent (Eid+1) C₀ vmin d m
  let Ch := idealSourceWidthExponent (Eid+1) C₀ vmin d 2 m
  let Cξ := idealSourceThresholdExponent (Eid+1) C₀ vmin d 2 m
  let cost := idealSourceCostExponent (Eid+1) C₀ vmin d 2 m
  have hC₀ : 0 ≤ C₀ := by unfold C₀ giantCandidateGroupLogRate; positivity
  have ⟨_,hCQ,hCh,hCξ,hcost0⟩ := idealSourceParameters_nonnegative (v₀ := vmin) (d := d) (C := 2)
    (show 0 ≤ Eid+1 by linarith) hC₀ (by norm_num [d]) (by norm_num) m
  have hsave : 0 ≤ save := (le_max_right A 0).trans (le_add_of_nonneg_right zero_le_one)
  have hcompare := hcomparison k m CQ Ch Cξ (save+cost) hCQ (zero_le_one.trans hCh) hCξ
    (add_nonneg hsave hcost0)
  filter_upwards [hselect k le_rfl, hcompare,
    giantCandidateActualRawPhysicalSum_norm_le_mappedResidual_eventually e χ ε Φ hT hhigh γ q j k,
    giantCandidateActualRawPhysicalSum_log_saving e he hε hεq hM χ Φ hΦ.continuous hT.le
      hhigh hγ hq hq1 j hj k save,
    Real.tendsto_log_atTop.eventually_ge_atTop ((M : ℝ)+2),
    Real.tendsto_log_atTop.eventually_ge_atTop (1/Real.log 2)]
    with x hselect hcompare hraw herror hlarge hwidth
  intro S hS
  let L := Real.log x
  let P := fun g : ↥S => giantCandidateGroup x g.val
  let B := GiantCandidatePerformedBig S
  let PB := giantCandidatePerformedBigBand S
  have hL1 : 1 < L := (show (1 : ℝ) < (M : ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) M]).trans_le hlarge
  have hL : 0 < L := zero_lt_one.trans hL1
  have hsmall : Nonempty (GiantCandidatePerformedSmall S) :=
    Fintype.card_pos_iff.mp (Nat.cast_pos.mp
      ((mul_pos hthreshold (Real.log_pos hL1)).trans_le ((giantCandidatePerformed_retained_iff S).mp hS).1))
  obtain ⟨B₁,B₂,hmk,hdis,_,hcap,hcost,hcut⟩ := hselect S hS
  let probes₁ := idealSourceProbes B₁ hmk
  let probes₂ := idealSourceProbes B₂ hmk
  let family := idealResidualPatterns probes₁ probes₂
  let Q := ⌊L^CQ⌋₊
  let h := L^(-Ch)
  let ξ := L^(-Cξ)
  let W := 1 + ((Q : ℝ)^2/ξ)^2
  let copied (p : IdealResidualPattern B k) := giantCandidatePerformedPattern S (idealResidualCopied p)
  let K (p : IdealResidualPattern B k) : GiantTwoSidedPatternCoefficient P (copied p) 1 :=
    giantCandidatePerformedCoefficient S (idealResidualCoefficient PB Q h ξ p)
  let F := giantCandidateFirstEndpoint e ε x
  let G := giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
    (Real.exp (L^(6/25 : ℝ))) (x^γ) j
  let damp (n : ℕ) := (giantTwoSidedEndpointDamping P (k+1) q n : ℂ)
  let Z := Ioc 0 ⌊x^2⌋₊
  let cmp (first second : Finset (B × Fin k)) := giantTwoSidedPhysicalPatternCutoffPairing (Z:=Z)
    (copied (some (first,second))) 1 q 0 (giantComparisonCharacterCoefficient χ (K (some (first,second))))
    Ψ x (fun n => damp n*conj (F n)) (fun t => damp t.val.1.val*(χ t.val.1.val*G t.val.1.val))
  have hexp : Real.exp h ≤ 2 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    calc
      h ≤ L^(-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1.le (neg_le_neg hCh)
      _ ≤ Real.log 2 := by
        rw [Real.rpow_neg_one, ← one_div]
        exact (div_le_iff₀ hL).mpr (by
          rw [mul_comm]
          exact (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ)<2))).mp hwidth)
  have hsum : (∑ first ∈ probes₁.powerset.erase ∅, ∑ second ∈ probes₂.powerset.erase ∅,
      ‖cmp first second‖) ≤ L^(-save) := by
    apply giantResidualComparison_norm_sum_log_saving probes₁ probes₂ cmp hL
      (le_add_of_nonneg_right (sq_nonneg _)) hcost
    intro first hfirst second hsecond
    have hA := mem_erase.mp hfirst
    have hB := mem_erase.mp hsecond
    have hd : Disjoint first second := (idealSourceProbes_disjoint B₁ B₂ hmk hdis).mono
      (mem_powerset.mp hA.2) (mem_powerset.mp hB.2)
    have hp : some (first,second) ∈ family := (idealResidualPatterns_comparison probes₁ probes₂ first second).mpr
      ⟨hfirst,hsecond⟩
    exact hcompare S hsmall first second (nonempty_iff_ne_empty.mpr hA.1)
      (nonempty_iff_ne_empty.mpr hB.1) hd (hcap _ hp) Q h ξ
      (Nat.floor_le (Real.rpow_nonneg hL.le _)) le_rfl hexp le_rfl
  have hraw' := hraw S probes₁ probes₂ Q h ξ (L^(-save)) (by
    intro r
    let u (n : ℕ) := conj (giantCharacterEndpointPhase r n)
    have hu (n : ℕ) : ‖u n‖ ≤ 1 := by
      simpa only [u,mul_one,norm_one] using (giant_character_endpoint_phase_norms r n (1 : ℂ)).2.le
    simpa only [u,mul_left_comm] using hcut u u hu hu)
  let raw := giantCandidateActualRawPhysicalSum (giantCandidateFullPrimes x) P e χ ε Φ T γ q j k x
  let corr := giantCandidateActualUnguardedShiftedCorrelation (giantCandidateFullPrimes x) P e χ ε Φ T γ q j x
  change ‖corr‖ ≤ L^(-A)
  have hraw'' : ‖raw‖ ≤ (M : ℝ)*L^(-save) + L^(-save) := hraw'.trans (add_le_add le_rfl hsum)
  calc
    _ ≤ ‖raw‖+‖raw-corr‖ := by simpa only [sub_sub_cancel] using norm_sub_le raw (raw-corr)
    _ ≤ (M : ℝ)*L^(-save)+L^(-save)+L^(-save) := add_le_add hraw'' (herror S)
    _ = ((M : ℝ)+2)*L^(-save) := by ring
    _ ≤ L*L^(-save) := mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hL.le _)
    _ = L^(-max A 0) := by
      calc
        _ = L^(1 : ℝ)*L^(-save) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hL]; congr 1; dsimp only [save]; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1.le (neg_le_neg (le_max_left _ _))

end
end ArtinMatthews
