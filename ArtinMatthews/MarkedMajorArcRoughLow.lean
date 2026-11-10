module

public import ArtinMatthews.RoughCharacterCounting
public import ArtinMatthews.MarkedSieveMertens
public import ArtinMatthews.MarkedMajorArcRoughLowBudget
public import ArtinMatthews.MarkedMajorArcRoughMertens
public import ArtinMatthews.MarkedRoughBonferroniBudget
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

/-! Actual low-frequency rough-character distribution, with the finite
prime-avoidance predicate and Mertens normalization retained. -/
namespace ArtinMatthews
open Finset Filter
open scoped Topology

 theorem marked_major_rough_prefix_low (a τ P c : ℝ)
    (ha : 0 ≤ a) (hτ : 0 < τ) (hP : 0 ≤ P) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ),
        (q:ℝ) ≤ L^a → Real.exp (τ*L) ≤ x →
        ‖(markedSieveEulerProduct (Real.exp (L^(6/25:ℝ))):ℂ)⁻¹*
          roughCharacterIocSum χ (Nat.primesLE ⌊Real.exp (L^(6/25:ℝ))⌋₊) 0 ⌊x⌋₊-
          (if χ=1 then ((⌊x⌋₊:ℝ):ℂ) else 0)‖ ≤ c*x*L^(-P) := by
  classical
  let E := Real.exp (Real.eulerMascheroniConstant+1)
  obtain ⟨D,hD,hbudget⟩ := marked_rough_bonferroni_uniform_power E (6/25) τ (6/25) P (c/2)
    (by norm_num) hP hτ (by norm_num) (half_pos hc)
  filter_upwards [hbudget,marked_rough_count_endpoint_budget a D (6/25) ha hD.le (by norm_num),
    marked_rough_density_inverse_cutoff (6/25) (by norm_num),
    marked_rough_prime_reciprocal_cutoff_le (6/25) (by norm_num) (by norm_num),
    eventually_ge_atTop (1:ℝ)] with L hbudget hendpoint hVbound hrec hL
  have hLp : 0 < L := zero_lt_one.trans_le hL
  intro q _ χ x hq hx
  let W := Real.exp (L^(6/25:ℝ))
  let V := markedSieveEulerProduct W
  let r := ⌊D*Real.log L⌋₊
  let s := ∑ p ∈ Nat.primesLE ⌊W⌋₊, 1/(p:ℝ)
  let F := markedFactorialTail s (r+1)
  have hW1 : 1 ≤ W := Real.one_le_exp_iff.mpr (Real.rpow_nonneg hLp.le _)
  have hWp : 0 < W := Real.exp_pos _
  have hV : 0 < V := markedSieveEulerProduct_pos W
  have hxp : 0 < x := (Real.exp_pos _).trans_le hx
  have hs : 0 ≤ s := sum_nonneg (fun _ _ => by positivity)
  have hF : 0 ≤ F := markedFactorialTail_nonneg hs _
  have hend : ((q:ℝ)+2)*((r+1:ℕ):ℝ) ≤ W := hendpoint (q:ℝ) (Nat.cast_nonneg _) hq
  have hqW : (q:ℝ) ≤ W := by
    have hr : (1:ℝ) ≤ ((r+1:ℕ):ℝ) := by exact_mod_cast (Nat.succ_pos r)
    nlinarith [show (0:ℝ) ≤ q from Nat.cast_nonneg q]
  have hcover (p : ℕ) (hp : p.Prime) (hpq : p ∣ q) : p ∈ Nat.primesLE ⌊W⌋₊ := by
    apply Nat.mem_primesLE.mpr
    refine ⟨?_,hp⟩
    apply (Nat.le_floor_iff hWp.le).2
    have hpqR : (p:ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) hpq
    exact hpqR.trans hqW
  have hv : 1 ≤ ⌊W⌋₊ := (Nat.le_floor_iff hWp.le).2 (by exact_mod_cast hW1)
  have hb := rough_character_Ioc_error_numeric χ (Nat.primesLE ⌊W⌋₊) r 0 ⌊x⌋₊ ⌊W⌋₊
    (fun _ hp => Nat.prime_of_mem_primesLE hp) (fun _ hp => (Nat.mem_primesLE.mp hp).1) hv hcover
  have hpow (k : ℕ) : (⌊W⌋₊:ℝ)^k ≤ W^k := pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hWp.le) k
  have hlast : ((q:ℝ)+2)*((r+1:ℕ):ℝ)*(⌊W⌋₊:ℝ)^r ≤ W^(r+1) := by
    calc
      _ ≤ W*W^r := mul_le_mul hend (hpow r) (by positivity) hWp.le
      _ = _ := by rw [pow_succ]; ring
  have hcount : ‖roughCharacterIocSum χ (Nat.primesLE ⌊W⌋₊) 0 ⌊x⌋₊-
      (if χ=1 then (((⌊x⌋₊:ℝ)*V:ℝ):ℂ) else 0)‖ ≤ 2*x*F+2*W^(r+1) := by
    apply hb.trans
    change 2*(⌊x⌋₊:ℝ)*F+(⌊W⌋₊:ℝ)^(r+1)+
      ((q:ℝ)+2)*((r+1:ℕ):ℝ)*(⌊W⌋₊:ℝ)^r ≤ _
    have hfirst : 2*(⌊x⌋₊:ℝ)*F ≤ 2*x*F := by gcongr; exact Nat.floor_le hxp.le
    linarith [hpow (r+1)]
  have hnum := hbudget s V x hs hrec hV (by simpa only [one_div] using hVbound) hx
  have hscaled := mul_le_mul_of_nonneg_left hnum (by positivity : 0 ≤ 2*x*V)
  have hscaleEq : 2*x*V*(2*F/V+W^(r+1)/(x*V)) = 4*x*F+2*W^(r+1) := by
    field_simp [hxp.ne',hV.ne']; ring
  change 2*x*V*(2*F/V+W^(r+1)/(x*V)) ≤ 2*x*V*((c/2)*L^(-P)) at hscaled
  rw [hscaleEq] at hscaled
  have hcount' : ‖roughCharacterIocSum χ (Nat.primesLE ⌊W⌋₊) 0 ⌊x⌋₊-
      (if χ=1 then (((⌊x⌋₊:ℝ)*V:ℝ):ℂ) else 0)‖ ≤ c*x*V*L^(-P) := by
    nlinarith [mul_nonneg hxp.le hF]
  have hVC : (V:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hV.ne'
  have he : (V:ℂ)⁻¹*roughCharacterIocSum χ (Nat.primesLE ⌊W⌋₊) 0 ⌊x⌋₊-
      (if χ=1 then ((⌊x⌋₊:ℝ):ℂ) else 0) =
      (V:ℂ)⁻¹*(roughCharacterIocSum χ (Nat.primesLE ⌊W⌋₊) 0 ⌊x⌋₊-
        (if χ=1 then (((⌊x⌋₊:ℝ)*V:ℝ):ℂ) else 0)) := by
    by_cases hχ : χ=1
    · simp only [ite_eq_left hχ,Complex.ofReal_mul]
      field_simp [hVC]
    · simp only [ite_eq_right hχ,sub_zero]
  change ‖(V:ℂ)⁻¹*roughCharacterIocSum χ (Nat.primesLE ⌊W⌋₊) 0 ⌊x⌋₊-
    (if χ=1 then ((⌊x⌋₊:ℝ):ℂ) else 0)‖ ≤ _
  rw [he,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hV]
  calc
    _ ≤ V⁻¹*(c*x*V*L^(-P)) := mul_le_mul_of_nonneg_left hcount' (inv_nonneg.mpr hV.le)
    _ = _ := by field_simp [hV.ne']

end ArtinMatthews
