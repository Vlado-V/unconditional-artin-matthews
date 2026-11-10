module

public import ArtinMatthews.GiantCandidateAllocationCore
public import ArtinMatthews.GiantCandidateFirstEndpoint
public import ArtinMatthews.GiantCandidateGroups
public import ArtinMatthews.GiantComparisonEndpointMarkMoment
public import ArtinMatthews.GiantCandidateAllocationParts
public import ArtinMatthews.GiantCandidateSquareCore
public import ArtinMatthews.GiantComparisonEndpointFiberMoment
public import ArtinMatthews.GiantComparisonEndpointGroupBudget
public import ArtinMatthews.GiantTwoSidedEndpointActual
public import ArtinMatthews.GiantTwoSidedEndpointCore
public import ArtinMatthews.SourceComparisonDivisorMass
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

/-! Global coefficient moments for both literal normalized comparison
endpoints. The Mellin twist, ordered mark tests and Dirichlet character
are present in the functions whose powers are summed. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section

def giantCandidateComparisonLeftEndpoint
    {I G : Type*} [Fintype I] [Fintype G]
    (e : I → ℝ) (ε x Y σ : ℝ) (ψ : ℝ → ℂ) (P : G → Finset ℕ) (t : G → ℕ)
    (q : G → ℝ) (b : ((g : G) → Fin (t g) → ℕ) → ℂ) : ℕ → ℂ :=
  giantComparisonWeightedEndpoint P t q b ψ
    (fun n => (n:ℂ)^(Complex.I*(σ:ℂ))*giantCandidateFirstEndpoint e ε x n) Y

def giantCandidateComparisonRightEndpoint
    {G : Type*} [Fintype G] {M : ℕ} (χ : DirichletCharacter ℂ M)
    (γ : ℝ) (j : ℕ) (x Y : ℝ) (ψ : ℝ → ℂ) (P : G → Finset ℕ) (t : G → ℕ)
    (q : G → ℝ) (b : ((g : G) → Fin (t g) → ℕ) → ℂ) : ℕ → ℂ :=
  giantComparisonWeightedEndpoint P t q b ψ (fun n =>
    χ n*giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
      (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j n) Y

private theorem comparison_endpoint_mellin_norm (n : ℕ) (hn : 0 < n) (σ : ℝ) :
    ‖(n:ℂ)^(Complex.I*(σ:ℂ))‖ = 1 := by
  rw [← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hn)]
  simp [Complex.mul_re]

/-- Uniform global position moments for the actual comparison endpoints.
Order `d=1` is the squared norm, and `d=2` is the fourth moment. -/
theorem giantCandidateComparisonEndpointPower_eventually
    {I : Type*} [Fintype I] (e : I → ℝ) (he : ∀ i, 0 < e i ∧ e i < 1)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    {Mχ : ℕ} (χ : DirichletCharacter ℂ Mχ)
    {γ A R : ℝ} (hγ : 0 < γ) (hA : 0 < A) (hR : 1 ≤ R)
    (j : ℕ) (hj : 0 < j) (m d : ℕ) (ψL ψR : ℝ → ℂ)
    (hψL : Continuous ψL) (hcL : HasCompactSupport ψL)
    (hψR : Continuous ψR) (hcR : HasCompactSupport ψR) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (S : Finset (GiantCandidateGroupIndex x)) (Y : ℝ), 1 ≤ Y → Y ≤ x^A →
      let P (g : S) := giantCandidateGroup x g.val
      ∀ (t : S → ℕ) (q : S → ℝ), (∀ g, t g ≤ m+1) →
      (∀ g, 0 ≤ q g ∧ q g ≤ 1) →
      ∀ (bL bR : ((g : S) → Fin (t g) → ℕ) → ℂ),
      (∀ l ∈ sourceComparisonMarkChoices P t, ‖bL l‖ ≤ 1) →
      (∀ l ∈ sourceComparisonMarkChoices P t, ‖bR l‖ ≤ 1) →
      ∀ (σ : ℝ) (ZL ZR : Finset ℕ), ZL ⊆ Ioc 0 ⌊R*Y⌋₊ → ZR ⊆ Ioc 0 ⌊R*Y⌋₊ →
      (∑ n ∈ ZL, ‖giantCandidateComparisonLeftEndpoint e ε x Y σ ψL P t q bL n‖^(2^d:ℕ)) ≤
        C*Y*(Real.log x)^D ∧
      (∑ n ∈ ZR, ‖giantCandidateComparisonRightEndpoint χ γ j x Y ψR P t q bR n‖^(2^d:ℕ)) ≤
        C*Y*(Real.log x)^D := by
  obtain ⟨ML,hML⟩ := hcL.exists_bound_of_continuous hψL
  obtain ⟨MR,hMR⟩ := hcR.exists_bound_of_continuous hψR
  let M := max 1 (max ML MR)
  let k : ℕ := 2^d
  let J : ℕ := j^(2^(d+1):ℕ)
  let Fmax := (2/Real.log 2)^Fintype.card I
  let Fbudget := max 1 (Fmax^(2*k))
  let L := 1+Real.log (R+1)+A
  let B := giantCandidateGroupLogRate*Real.log (giantComparisonEndpointGroupBase m k)
  let C := M^k*(Fbudget+1)*R*L^J
  have hk : 2*k = 2^(d+1) := by
    unfold k
    rw [pow_succ,Nat.mul_comm]
  have hM : 1 ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hFmax : 0 ≤ Fmax := by unfold Fmax; positivity
  have hFbudget : 1 ≤ Fbudget := le_max_left _ _
  have hFbudget0 : 0 ≤ Fbudget := zero_le_one.trans hFbudget
  have hL : 1 ≤ L := by
    unfold L
    linarith [Real.log_nonneg (show 1 ≤ R+1 by linarith)]
  have hB : 0 ≤ B := by
    unfold B giantCandidateGroupLogRate
    exact mul_nonneg (by positivity)
      (Real.log_nonneg (giantComparisonEndpointGroupBase_one_le m k))
  have hC : 0 < C := by
    unfold C
    exact mul_pos (mul_pos (mul_pos (pow_pos (zero_lt_one.trans_le hM) _)
      (by linarith)) (zero_lt_one.trans_le hR)) (pow_pos (zero_lt_one.trans_le hL) _)
  refine ⟨C,hC,B+(J:ℝ),add_nonneg hB (Nat.cast_nonneg _),?_⟩
  filter_upwards [giantCandidateComparisonMarkMomentBudget_eventually m k,
    giantCandidateSelectedGroups_geometry_eventually,giantCandidateFullPrimes_prime_upper_eventually,
    giantCandidateFirstEndpoint_norm_eventually e he hε hεq,
    giantCandidateAllocationCore_character_actual_norm_le_stripped_fiber χ γ hγ j,
    eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)]
    with x hgroup hgeo hprime hleft hright hx hlog
  intro S Y hY hYA
  dsimp only
  intro t q ht hq bL bR hbL hbR σ ZL ZR hZL hZR
  let P (g : S) := giantCandidateGroup x g.val
  let N := ⌊R*Y⌋₊
  let LN := 1+Real.log ((N:ℝ)+1)
  let Vhit := Real.exp ((Real.exp (2*(k:ℝ))-1)*∑ p ∈ univ.biUnion P, 1/(p:ℝ))
  let W := sourceComparisonMarkFactorialMass P t
  let FL (n : ℕ) := (n:ℂ)^(Complex.I*(σ:ℂ))*giantCandidateFirstEndpoint e ε x n
  let FR (n : ℕ) := χ n*giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
    (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j n
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hN : (N:ℝ) ≤ R*Y := Nat.floor_le (by positivity)
  have hN0 : 0 ≤ (N:ℝ) := Nat.cast_nonneg _
  have hLN : 1 ≤ LN := by
    unfold LN
    linarith [Real.log_nonneg (show 1 ≤ (N:ℝ)+1 by linarith)]
  have hLN0 : 0 ≤ LN := zero_le_one.trans hLN
  have hlogcap : LN ≤ L*Real.log x := by
    have h := giantTwoSidedEndpoint_log_cap (τ:=A⁻¹) hx hlog hR hY
      (by simpa only [one_div,inv_inv] using hYA)
    simpa only [LN,N,L,one_div,inv_inv] using h
  have hV : ∀ g, 0 < bandReciprocalMass (P g) := fun g =>
    (div_pos (Real.log_pos (by norm_num)) (by norm_num)).trans ((hgeo S).2.1 g).1
  have hP : ∀ p ∈ univ.biUnion P, p.Prime := fun p hp =>
    (hprime p ((hgeo S).2.2 hp)).1
  have hVhit : 1 ≤ Vhit := by
    unfold Vhit
    apply Real.one_le_exp_iff.mpr
    have hbase : 1 ≤ Real.exp (2*(k:ℝ)) := Real.one_le_exp_iff.mpr (by positivity)
    exact mul_nonneg (sub_nonneg.mpr hbase) (sum_nonneg fun _ _ => by positivity)
  have hBudget : W^k*Vhit ≤ (Real.log x)^B := hgroup S t ht
  have hFL (n : ℕ) (hn : 0 < n) : ‖FL n‖ ≤ Fmax := by
    unfold FL
    rw [norm_mul,comparison_endpoint_mellin_norm n hn,one_mul]
    exact hleft n
  have hFR (n : ℕ) (hn : 0 < n) : ‖FR n‖ ≤ ((giantOrderedProductFiber j n).card:ℝ) :=
    (hright _ _ n).trans (Nat.cast_le.mpr
      (giantOrderedProductFiber_card_le_of_dvd j hj hn (giantCandidateStrip_dvd (univ.biUnion P) n)))
  have hFLmom : (∑ n ∈ ZL, ‖FL n‖^(2*k)) ≤ (N:ℝ)*Fbudget*LN^J := by
    have hc : ZL.card ≤ N := by
      simpa only [Nat.card_Ioc,Nat.sub_zero] using card_le_card hZL
    calc
      _ ≤ ∑ _n ∈ ZL, Fmax^(2*k) := sum_le_sum (fun n hn =>
        pow_le_pow_left₀ (norm_nonneg _) (hFL n (mem_Ioc.mp (hZL hn)).1) _)
      _ = (ZL.card:ℝ)*Fmax^(2*k) := by simp only [sum_const,nsmul_eq_mul]
      _ ≤ (N:ℝ)*Fbudget := mul_le_mul (Nat.cast_le.mpr hc) (le_max_right _ _)
        (pow_nonneg hFmax _) hN0
      _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hN0 hFbudget0) (one_le_pow₀ hLN)
  have hFRmom : (∑ n ∈ ZR, ‖FR n‖^(2*k)) ≤ (N:ℝ)*Fbudget*LN^J := by
    calc
      _ ≤ ∑ n ∈ ZR, ((giantOrderedProductFiber j n).card:ℝ)^(2*k) :=
        sum_le_sum (fun n hn => pow_le_pow_left₀ (norm_nonneg _)
          (hFR n (mem_Ioc.mp (hZR hn)).1) _)
      _ ≤ ∑ n ∈ Ioc 0 N, ((giantOrderedProductFiber j n).card:ℝ)^(2*k) :=
        sum_le_sum_of_subset_of_nonneg hZR (fun _ _ _ => by positivity)
      _ ≤ (N:ℝ)*LN^J := by rw [hk]; exact giant_ordered_product_fiber_pow_two_moment j (d+1) N
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_right hN0 hFbudget) (pow_nonneg hLN0 _)
  have hbnd (Z : Finset ℕ) (hZ : Z ⊆ Ioc 0 N) (F : ℕ → ℂ)
      (hF : (∑ n ∈ Z, ‖F n‖^(2*k)) ≤ (N:ℝ)*Fbudget*LN^J)
      (ψ : ℝ → ℂ) (hψ : ∀ r, ‖ψ r‖ ≤ M) (b : ((g : S) → Fin (t g) → ℕ) → ℂ)
      (hb : ∀ l ∈ sourceComparisonMarkChoices P t, ‖b l‖ ≤ 1) :
      (∑ n ∈ Z, ‖giantComparisonWeightedEndpoint P t q b ψ F Y n‖^k) ≤
        C*Y*(Real.log x)^(B+(J:ℝ)) := by
    have hW : 0 ≤ W := by
      unfold W sourceComparisonMarkFactorialMass
      exact div_nonneg (prod_nonneg fun _ _ => Nat.cast_nonneg _)
        (sourceComparisonMarkMass_pos P t hV).le
    have hs : (N:ℝ)*Fbudget*LN^J+(N:ℝ)*Vhit ≤ (N:ℝ)*(Fbudget+1)*LN^J*Vhit := by
      calc
        _ ≤ ((N:ℝ)*Fbudget*LN^J)*Vhit+((N:ℝ)*LN^J)*Vhit :=
          add_le_add (le_mul_of_one_le_right (by positivity) hVhit)
            (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hN0 (one_le_pow₀ hLN))
              (zero_le_one.trans hVhit))
        _ = _ := by ring
    have hscale : (N:ℝ)*(Fbudget+1)*LN^J ≤ R*Y*(Fbudget+1)*(L*Real.log x)^J :=
      mul_le_mul (mul_le_mul_of_nonneg_right hN (by positivity))
        (pow_le_pow_left₀ hLN0 hlogcap _) (pow_nonneg hLN0 _) (by positivity)
    calc
      _ ≤ M^k*W^k*((∑ n ∈ Z, ‖F n‖^(2*k))+(N:ℝ)*Vhit) :=
        giantComparisonWeightedEndpoint_power_sum_le P t q (hgeo S).1 hP hq hV b hb ψ hM0 hψ F Y k N Z hZ
      _ ≤ M^k*W^k*((N:ℝ)*(Fbudget+1)*LN^J*Vhit) :=
        mul_le_mul_of_nonneg_left ((add_le_add hF le_rfl).trans hs) (by positivity)
      _ = M^k*((N:ℝ)*(Fbudget+1)*LN^J)*(W^k*Vhit) := by ring
      _ ≤ M^k*(R*Y*(Fbudget+1)*(L*Real.log x)^J)*(Real.log x)^B :=
        mul_le_mul (mul_le_mul_of_nonneg_left hscale (pow_nonneg hM0 _)) hBudget
          (mul_nonneg (pow_nonneg hW _) (zero_le_one.trans hVhit)) (by positivity)
      _ = _ := by
        rw [Real.rpow_add (zero_lt_one.trans_le hlog),Real.rpow_natCast,mul_pow]
        unfold C
        ring
  exact ⟨hbnd ZL hZL FL hFLmom ψL (fun r => (hML r).trans
    ((le_max_left ML MR).trans (le_max_right 1 (max ML MR)))) bL hbL,
    hbnd ZR hZR FR hFRmom ψR (fun r => (hMR r).trans
      ((le_max_right ML MR).trans (le_max_right 1 (max ML MR)))) bR hbR⟩

end
end ArtinMatthews
