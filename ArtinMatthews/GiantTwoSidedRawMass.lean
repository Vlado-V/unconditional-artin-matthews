module

public import ArtinMatthews.GiantTwoSidedRawSharedAggregation
public import ArtinMatthews.GiantCandidateOneMarkBounds
public import ArtinMatthews.GiantCandidateFirstEndpoint
public import ArtinMatthews.GiantCandidateSquareCore
public import ArtinMatthews.GiantOrderedProductCount
public import ArtinMatthews.GiantOrderedProductMoment
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

/-! The literal absolute weighted sum after raw stripping has fixed
logarithmic growth. The shifted right endpoint is controlled by the
actual ordered positive-product fibers. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section

theorem giantTwoSidedRawPositionKernel_source {m w : ℕ} {x : ℝ}
    (hx : 0 < x) (hw : 0 < w) (Φ : ℝ → ℝ) (χ : DirichletCharacter ℂ m)
    (F G : ℕ → ℂ) :
    giantTwoSidedRawPositionKernel x (fun t => ((t*Φ t:ℝ):ℂ)) χ F G w =
      ((Φ ((w:ℝ)/x):ℂ)/(x:ℂ))*F w*χ (w+1:ℕ)*G (w+1) := by
  unfold giantTwoSidedRawPositionKernel
  have h : ((((w:ℝ)/x*Φ ((w:ℝ)/x):ℝ):ℂ))/(w:ℂ) = (Φ ((w:ℝ)/x):ℂ)/(x:ℂ) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hx.ne',Nat.cast_ne_zero.mpr hw.ne']
  rw [h]

theorem giantTwoSidedRaw_shiftedFiberMass_le (j N : ℕ) :
    (∑ w ∈ Ioc 0 N,((giantOrderedProductFiber j (w+1)).card:ℝ)) ≤
      ((N+1:ℕ):ℝ)*(1+Real.log ((N+1:ℕ):ℝ))^j := by
  classical
  let E : ℕ ↪ ℕ := ⟨Nat.succ,fun _ _ => Nat.succ.inj⟩
  have hsub : (Ioc 0 N).map E ⊆ Ioc 0 (N+1) := by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := mem_map.mp hw
    exact mem_Ioc.mpr ⟨Nat.succ_pos _,Nat.succ_le_succ (mem_Ioc.mp hv).2⟩
  calc
    _ = ∑ n ∈ (Ioc 0 N).map E,((giantOrderedProductFiber j n).card:ℝ) :=
      (sum_map _ _ _).symm
    _ ≤ ∑ n ∈ Ioc 0 (N+1),((giantOrderedProductFiber j n).card:ℝ) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
    _ = ((giantOrderedProductTuples j (N+1)).card:ℝ) := giant_ordered_product_fiber_card_sum _ _
    _ ≤ _ := giant_ordered_product_count_le _ _

theorem giantCandidateRawHarmonic_absolute_mass {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ i,0 < e i ∧ e i < 1) {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    {m : ℕ} (χ : DirichletCharacter ℂ m) (Φ : ℝ → ℝ) (hΦ : Continuous Φ)
    {T γ q : ℝ} (hT : 0 ≤ T) (hγ : 0 < γ) (hq : 0 ≤ q) (hq1 : q < 1) (j : ℕ) (hj : 0 < j) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (i : S) := giantCandidateGroup x i.val
      let F := giantCandidateFirstEndpoint e ε x
      let G := giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
        (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j
      (∑ w ∈ Ioc 0 ⌊T*x⌋₊,
        ‖giantTwoSidedRawPositionKernel x (fun t => ((t*Φ t:ℝ):ℂ)) χ F G w‖ *
          (giantCandidateActiveOneMark P q w*giantCandidateActiveOneMark P q (w+1))) ≤
        C*(Real.log x)^(2*(giantCandidateGroupLogRate*Real.log (giantCandidateOneMarkBound q))+(j:ℝ)) := by
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hΦ.continuousOn : ContinuousOn Φ (Set.Icc 0 T))
  let F₀ := (2/Real.log 2)^Fintype.card J
  let c := giantCandidateGroupLogRate*Real.log (giantCandidateOneMarkBound q)
  have hF₀ : 0 ≤ F₀ := pow_nonneg (div_nonneg (by norm_num) (Real.log_nonneg (by norm_num))) _
  have hB0 : 0 ≤ B := (norm_nonneg (Φ 0)).trans (hB 0 ⟨le_rfl,hT⟩)
  refine ⟨B*F₀*(T+1)*2^j,by positivity,?_⟩
  filter_upwards [giantCandidateFirstEndpoint_norm_eventually e he hε hεq,
    giantCandidateActiveOneMark_actual_bound hq hq1,
    giantCandidateAllocationCore_actual_norm_le_fiber γ hγ j hj,
    eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1+Real.log (T+1))]
    with x hF hmark hG hx hL
  intro S
  let P (i : S) := giantCandidateGroup x i.val
  let F := giantCandidateFirstEndpoint e ε x
  let G := giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
    (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j
  let L := Real.log x
  let N := ⌊T*x⌋₊
  have hx0 := zero_lt_one.trans_le hx
  have hL0 : 0 < L := (by linarith only [Real.log_nonneg (show 1≤T+1 by linarith)] :
      0 < 1+Real.log (T+1)).trans_le hL
  have hcap : ((N+1:ℕ):ℝ) ≤ (T+1)*x := by
    rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul]
    exact add_le_add (Nat.floor_le (mul_nonneg hT hx0.le)) hx
  have hlog : 1+Real.log ((N+1:ℕ):ℝ) ≤ 2*L := by
    have hlog' := Real.log_le_log (by positivity : 0<((N+1:ℕ):ℝ)) hcap
    rw [Real.log_mul (by positivity : T+1≠0) hx0.ne'] at hlog'
    linarith only [hlog',hL]
  let A := B*F₀*(L^c*L^c)/x
  have hA : 0 ≤ A := by positivity
  have hwgt (w : ℕ) : giantCandidateActiveOneMark P q w ≤ L^c := by
    have h := hmark S w
    change ‖(giantCandidateActiveOneMark P q w:ℂ)‖ ≤ L^c at h
    rw [Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (giantCandidateActiveOneMark_nonneg P hq w)] at h
    exact h
  have hterm (w : ℕ) (hw : w∈Ioc 0 N) :
      ‖giantTwoSidedRawPositionKernel x (fun t => ((t*Φ t:ℝ):ℂ)) χ F G w‖ *
        (giantCandidateActiveOneMark P q w*giantCandidateActiveOneMark P q (w+1)) ≤
        A*((giantOrderedProductFiber j (w+1)).card:ℝ) := by
    have hw0 := (mem_Ioc.mp hw).1
    have harg : (w:ℝ)/x ∈ Set.Icc 0 T :=
      ⟨div_nonneg (Nat.cast_nonneg _) hx0.le,(div_le_iff₀ hx0).mpr
        ((Nat.le_floor_iff (mul_nonneg hT hx0.le)).mp (mem_Ioc.mp hw).2)⟩
    rw [giantTwoSidedRawPositionKernel_source hx0 hw0,norm_mul,norm_mul,norm_mul,norm_div,
      Complex.norm_real,Complex.norm_real x,Real.norm_eq_abs x,abs_of_nonneg hx0.le]
    have hbound : ‖Φ ((w:ℝ)/x)‖/x*‖F w‖*‖χ (w+1:ℕ)‖*‖G (w+1)‖ ≤
        B/x*F₀*1*((giantOrderedProductFiber j (w+1)).card:ℝ) :=
      mul_le_mul (mul_le_mul
        (mul_le_mul (div_le_div_of_nonneg_right (hB _ harg) hx0.le) (hF w) (norm_nonneg _) (by positivity))
        (χ.norm_le_one _) (norm_nonneg _) (by positivity))
        (hG _ _ _ (Nat.succ_pos _)) (norm_nonneg _) (by positivity)
    calc
      _ ≤ (B/x*F₀*1*((giantOrderedProductFiber j (w+1)).card:ℝ))*(L^c*L^c) :=
        mul_le_mul hbound (mul_le_mul (hwgt w) (hwgt (w+1))
          (giantCandidateActiveOneMark_nonneg P hq _) (Real.rpow_nonneg hL0.le _))
          (mul_nonneg (giantCandidateActiveOneMark_nonneg P hq _) (giantCandidateActiveOneMark_nonneg P hq _))
          (by positivity)
      _ = _ := by unfold A; ring
  change (∑ w ∈ Ioc 0 N,_) ≤ B*F₀*(T+1)*2^j*L^(2*c+(j:ℝ))
  calc
    _ ≤ ∑ w ∈ Ioc 0 N,A*((giantOrderedProductFiber j (w+1)).card:ℝ) := sum_le_sum hterm
    _ ≤ A*(((N+1:ℕ):ℝ)*(1+Real.log ((N+1:ℕ):ℝ))^j) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (giantTwoSidedRaw_shiftedFiberMass_le j N) hA
    _ ≤ A*(((T+1)*x)*(2*L)^j) := by
      apply mul_le_mul_of_nonneg_left _ hA
      have hN : 1≤((N+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
      have hlog0 := add_nonneg zero_le_one (Real.log_nonneg hN)
      exact mul_le_mul hcap (pow_le_pow_left₀ hlog0 hlog _) (by positivity) (by positivity)
    _ = _ := by
      unfold A
      rw [Real.rpow_add hL0,show 2*c=c+c by ring,Real.rpow_add hL0,Real.rpow_natCast,mul_pow]
      field_simp [hx0.ne']

end
end ArtinMatthews
