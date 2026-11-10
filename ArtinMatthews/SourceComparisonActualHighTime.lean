module

public import ArtinMatthews.SourceComparisonActualLowTime
public import ArtinMatthews.SourceComparisonHighTimeTuple
public import ArtinMatthews.SourceComparisonSmallMarkReindex
public import ArtinMatthews.SourceComparisonActualModel
public import ArtinMatthews.SourceComparisonActualSmallMark
public import ArtinMatthews.SourceComparisonCenteredHighAssembly
public import ArtinMatthews.SourceComparisonPolynomialMean
public import ArtinMatthews.SourceComparisonProductBranches
public import ArtinMatthews.SourceComparisonSquareErrorEnergy
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

/-! The original ordinary centered Mellin sum has arbitrary logarithmic
saving on its high-time band. -/

namespace ArtinMatthews

open Finset Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

universe u v
variable {J : Type u} [Fintype J]

private theorem centeredMellinSum_eq_highMellin {G : Type v} [Fintype G]
    (e : J → ℝ) (ε x Y σ B : ℝ) (ψ : ℝ → ℂ)
    (P : G → Finset ℕ) (t : G → ℕ) (q : G → ℝ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ) (k : ℕ) [NeZero k] (h : ℤ) (τ : ℝ) :
    sourceComparisonCenteredMellinSum e ε x Y σ B ψ P t q b k h τ =
      sourceComparisonHighMellin (h:ZMod k) (fun n =>
        sourceComparisonInertActiveMarks e x P t q b n*(giantMarkedCenteredCore ε x n:ℂ))
        ψ Y B (τ+σ) := by
  unfold sourceComparisonCenteredMellinSum sourceComparisonHighMellin
  congr 1
  apply sum_congr rfl
  intro n hn
  have hn₀ := (mem_Ioc.mp hn).1
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn₀.ne'
  dsimp only
  rw [sourceComparisonCenteredEndpoint, giantCandidateFirstEndpoint,
    sourceComparisonRationalPhase, sourceComparisonInertActiveMarks_eq,
    sourceComparisonPrimePhase_eq_cpow hn₀, Complex.ofReal_add, add_mul,
    Complex.cpow_add _ _ hnC]
  ring

/-- Uniform high-time energy of the literal centered comparison endpoint
with one distinguished small mark. The upper time is (L Y/H). -/
theorem sourceComparisonCenteredMellinSum_high_energy (e : J → ℝ)
    (he : ∀ j, (1/10:ℝ) < e j ∧ e j < 1/5) (heinj : Function.Injective e)
    (m : ℕ) {r : ℝ} (hr : (1/2:ℝ) ≤ r) (hr₁ : r < 1)
    (ψ : ℝ → ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hsupp : Function.support ψ ⊆ Set.Icc a b) (hψ : ContDiff ℝ ∞ ψ)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    (C Q A : ℝ) (hQ : 0 ≤ Q) (hA : 0 ≤ A) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℝ in atTop,
      ∀ {G : Type v} [Fintype G] (s : GiantCandidateSmallGroupIndex x)
        (i : G ↪ GiantCandidateGroupIndex x)
        (hout : (Sum.inl s : GiantCandidateGroupIndex x) ∉ Set.range i)
        (t : G → ℕ), (∀ g, t g ≤ m) →
        ∀ (q₀ : ℝ), 0 ≤ q₀ → q₀ ≤ r →
        ∀ (q : G → ℝ), (∀ g, 0 ≤ q g ∧ q g ≤ r) →
        ∀ (test : ((g : G) → Fin (t g) → ℕ) → ℂ),
          (∀ l ∈ sourceComparisonMarkChoices (giantCandidateGroup x ∘ i) t, ‖test l‖ ≤ 1) →
          ∀ (Y H σ : ℝ), x ≤ Y → Y ≤ x^(1+ε/4) →
            Real.exp ((Real.log x)^(38/100:ℝ)) ≤ H → H ≤ Real.exp (Real.log x/2) →
            |σ| ≤ (Real.log x)^C →
            ∀ (k : ℕ) [NeZero k] (h : ℤ), (k:ℝ) ≤ (Real.log x)^Q →
              (∫ τ in sourceComparisonHighTimes (Real.log x*Y/H) ((Real.log x)^B),
                ‖sourceComparisonCenteredMellinSum e ε x Y σ b ψ
                  (giantCandidateGroup x ∘ sourceComparisonDistinguishedGroupEmbedding s i hout)
                  (Sum.elim (fun _ => 1) t) (Sum.elim (fun _ => q₀) q)
                  (fun l => test (fun g => l (.inr g))) k h τ‖^2) ≤ (Real.log x)^(-A) := by
  obtain ⟨D,E,K,hD,hE,_,hmodel⟩ := sourceComparisonActualInertActiveModel_eventually.{u,v}
    e he heinj m hr hr₁ (A+16+2*Q)
  obtain ⟨_,_,hsquare⟩ := sourceComparisonActualSmallMark_square_error_eventually.{u,v}
    e he heinj m hr hr₁ (A+3)
  obtain ⟨B,hB,henergy⟩ := sourceComparisonProductBranches_high_energy ψ ha hsupp hψ ε C D Q E K (A+3)
    hε hεq hD hQ hE (by linarith)
  let δ := 2*(1-ε)-(1+ε/4)
  let V₀ := Real.log 2/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hV₀ : 0 < V₀ := by dsimp [V₀]; positivity
  refine ⟨B,hB,?_⟩
  filter_upwards [hmodel, hsquare, Real.tendsto_log_atTop.eventually henergy,
    sourceComparisonActualBands_geometry_eventually.{u,v} e he heinj,
    sourceComparisonActualBands_long_eventually.{u,v} e he heinj hε hεq Q,
    Real.tendsto_log_atTop.eventually (sourceComparisonHighMellin_square_error ψ hb hsupp hψ.continuous A),
    (tendsto_rpow_atTop hδ).eventually (eventually_ge_atTop b),
    eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 9 V₀⁻¹))]
    with x hmodel hsquare henergy hgeo hlong herr hcap hx hL
  intro G _ s i hout t ht q₀ hq₀ hq₀r q hq test htest Y H σ hY hYcap hH hHcap hσ k _ h hk
  let L := Real.log x
  let T := L*Y/H
  let S := giantCandidateSmallGroup x s
  let i' := sourceComparisonDistinguishedGroupEmbedding s i hout
  let t₀ : Unit ⊕ G → ℕ := Sum.elim (fun _ => 0) t
  let q' : Unit ⊕ G → ℝ := Sum.elim (fun _ => q₀) q
  let test₀ (l : (g : Unit ⊕ G) → Fin (t₀ g) → ℕ) := test (fun g => l (.inr g))
  let P := sourceComparisonActualBands e x i'
  let u' : J ⊕ (Unit ⊕ G) → ℕ := Sum.elim (fun _ => 1) t₀
  let r' : J ⊕ (Unit ⊕ G) → ℝ := Sum.elim (fun _ => 1/2) q'
  let test' (l : (g : J ⊕ (Unit ⊕ G)) → Fin (u' g) → ℕ) := test₀ (fun g => l (.inr g))
  let j := ⌊L^(1/100:ℝ)⌋₊
  let I := sourceComparisonDivisorIndices P u' j
  let β := sourceComparisonActualSmallMarkWeight e s i 0 t q₀ q test
  let W := sourceComparisonActualSmallMarkWeight e s i 1 t q₀ q test
  have hL9 : 9 ≤ L := (le_max_left _ _).trans hL
  have hL1 : 1 ≤ L := by linarith
  have hx0 : 0 < x := by linarith
  have hY0 : 0 < Y := hx0.trans_le hY
  have ht₀ (g : Unit ⊕ G) : t₀ g ≤ m := by
    rcases g with g | g
    · exact Nat.zero_le _
    · exact ht g
  have hq' (g : Unit ⊕ G) : 0 ≤ q' g ∧ q' g ≤ r := by
    rcases g with g | g
    · exact ⟨hq₀,hq₀r⟩
    · exact hq g
  have htest₀ : ∀ l ∈ sourceComparisonMarkChoices (giantCandidateGroup x ∘ i') t₀, ‖test₀ l‖ ≤ 1 := by
    intro l hl
    have hh := (mem_sourceComparisonMarkChoices (giantCandidateGroup x ∘ i') t₀ l).mp hl
    exact htest _ ((mem_sourceComparisonMarkChoices (giantCandidateGroup x ∘ i) t
      (fun g => l (.inr g))).mpr ⟨fun g j => hh.1 (.inr g) j, fun g => hh.2 (.inr g)⟩)
  have hβeq : β = sourceComparisonInertActiveMarks e x (giantCandidateGroup x ∘ i') t₀ q' test₀ :=
    sourceComparisonActualSmallMarkWeight_eq e s i hout 0 t q₀ q test
  obtain ⟨hβ,hd,hm,herror⟩ := hmodel i' t₀ ht₀ q' hq' test₀ htest₀
  rw [← hβeq] at hβ herror
  have hS (p : ℕ) (hp : p ∈ S) : p.Prime ∧ Real.exp (L^(28/100:ℝ)) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ Real.exp (L^(36/100:ℝ)) := by
    obtain ⟨hpr,hlo,hhi⟩ := giantCandidateSmallGroup_range hx hL1 hp
    exact ⟨hpr,hlo,hhi.le.trans (Real.exp_le_exp.mpr
      (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)))⟩
  have hYexp : Real.exp L ≤ Y := by simpa only [L, Real.exp_log hx0] using hY
  have hYcapexp : Y ≤ Real.exp ((1+ε/4)*L) := by
    apply hYcap.trans_eq
    rw [Real.rpow_def_of_pos hx0, mul_comm]
  have hmodelErr (N : ℕ) :
      (∑ n ∈ Ioc 0 N, ‖β n - markedMajorDivisorPolynomial I sourceComparisonDivisor
        (sourceComparisonDivisorCoefficient P u' r' test') n‖^2) ≤
        (N:ℝ)*L^(-((A+3)+13+2*Q)) := by
    have he : (A+3)+13+2*Q=A+16+2*Q := by ring
    rw [he]
    simpa only [markedMajorDivisorPolynomial, sourceComparisonDivisorModel] using herror N
  have hbranches := henergy Y H σ hYexp hYcapexp hH hHcap hσ S β hS (fun n _ => hβ n)
    I sourceComparisonDivisor (sourceComparisonDivisorCoefficient P u' r' test')
    (fun z hz => ⟨(hd z hz).1,(hd z hz).2.1⟩) hm hmodelErr k (h:ZMod k) hk
  obtain ⟨hG,hGdis,_,hCx,_⟩ := hlong i'
  have hSsub : S ⊆ univ.biUnion P := fun p hp =>
    mem_biUnion.mpr ⟨Sum.inr (.inl ()), mem_univ _, hp⟩
  have hdis : Disjoint S (giantPrimeWindow x ε) :=
    Finset.disjoint_left.mpr (fun p hp hg => Finset.disjoint_left.mp hGdis hg (hSsub hp))
  have hinv (ell : ℕ) (hell : ell ∈ giantPrimeWindow x ε) (n : ℕ) : β (ell*n)=β n := by
    rw [hβeq]
    exact sourceComparisonMarkWeight_mul_outside P u' r' test'
      (fun g p hp => ((hgeo i').2.2.1 p (mem_biUnion.mpr ⟨g,mem_univ _,hp⟩)).1)
      (hG ell hell) (fun g hp => Finset.disjoint_left.mp hGdis hell
        (mem_biUnion.mpr ⟨g,mem_univ _,hp⟩)) n
  have hVlo : V₀ < bandReciprocalMass S := ((hgeo i').2.1 (.inr (.inl ()))).1
  have hVpos : 0 < bandReciprocalMass S := hV₀.trans hVlo
  have hV : ‖(bandReciprocalMass S:ℂ)⁻¹‖ ≤ L := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hVpos.le, ← one_div]
    exact (one_div_le_one_div_of_le hV₀ hVlo.le).trans (by simpa only [one_div] using (le_max_right 9 V₀⁻¹).trans hL)
  have hCxnorm : ‖(giantPrimeReciprocalSum x ε:ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hCx.1]
    exact hCx.2
  have hcap' (n : ℕ) (hn : n ∈ Ioc 0 ⌊b*Y⌋₊) : (n:ℝ) ≤ (x^(1-ε))^2 := by
    calc
      _ ≤ (⌊b*Y⌋₊:ℝ) := by exact_mod_cast (mem_Ioc.mp hn).2
      _ ≤ b*Y := Nat.floor_le (by positivity)
      _ ≤ b*x^(1+ε/4) := mul_le_mul_of_nonneg_left hYcap hb
      _ ≤ x^δ*x^(1+ε/4) := mul_le_mul_of_nonneg_right hcap (by positivity)
      _ = _ := by
        rw [← Real.rpow_add hx0, ← Real.rpow_two (x^(1-ε)), ← Real.rpow_mul hx0.le]
        congr 1
        dsimp [δ]
        ring
  let error (n : ℕ) := (W n-sourceComparisonRemovedWeight S β n)*(giantMarkedCenteredCore ε x n:ℂ)
  have hsq := (hsquare s i hout t ht q₀ hq₀ hq₀r q hq test htest).2 ⌊b*Y⌋₊
  have hE (n : ℕ) :
      ‖error n‖^2 ≤ ‖W n-sourceComparisonActualRemovedSmallMark e s i t q₀ q test n‖^2 := by
    have hnorm : ‖(giantMarkedCenteredCore ε x n:ℂ)‖ ≤ 1 := by
      rw [giantMarkedCenteredCore, Complex.norm_real, Real.norm_eq_abs]
      exact boundedGiantIndicator_sub_abs_le_one n x ε _ hCx.1 hCx.2
    have heq : sourceComparisonRemovedWeight S β n =
        sourceComparisonActualRemovedSmallMark e s i t q₀ q test n :=
      (sourceComparisonActualRemovedSmallMark_eq_sum e s i t q₀ q test n).symm
    dsimp only [error]
    rw [heq, norm_mul]
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_of_le_one_right (norm_nonneg _) hnorm) 2
  have hsq' : (∑ n ∈ Ioc 0 ⌊b*Y⌋₊, ‖error n‖^2) ≤
      (⌊b*Y⌋₊:ℝ)*L^(-(A+3)) :=
    (sum_le_sum fun n _ => hE n).trans hsq
  have hH1 : 1 ≤ H := (Real.one_le_exp (by positivity)).trans hH
  have hT0 : 0 < T := div_pos (mul_pos (by linarith) hY0) (by linarith)
  have hTle : T ≤ L*Y := div_le_self (by positivity) hH1
  have hErr := herr Y T (L^B) σ hY0 hT0 hTle k (h:ZMod k) error hsq'
  have hex : Real.exp L = x := Real.exp_log hx0
  rw [hex] at hbranches
  have hresult := sourceComparisonCentered_high_energy_of_branches (h:ZMod k)
    W β S ψ a b Y x ε σ T (L^B) L A hx0.le hY0 hL9 hsupp
    (fun p hp => (hS p hp).1) hdis hinv hcap' hV hCxnorm hbranches.1 hbranches.2 hErr
  simp_rw [centeredMellinSum_eq_highMellin,
    ← sourceComparisonActualSmallMarkWeight_eq e s i hout 1 t q₀ q test]
  exact hresult

end
end ArtinMatthews
