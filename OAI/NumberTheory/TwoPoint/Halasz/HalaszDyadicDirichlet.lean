module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.NumberTheory.Chebyshev
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import OAI.NumberTheory.TwoPoint.Halasz.HalaszDyadicPrefix
public import OAI.NumberTheory.TwoPoint.Halasz.HalaszLogDirichletBlock
public import OAI.NumberTheory.TwoPoint.Halasz.HalaszWeakStripScale


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! The actual shifted Dirichlet polynomial at an exponential cutoff.
All prefixes, including the small dyadic blocks, are retained. -/
namespace TwoPointCorrelations

open Finset Complex

theorem halasz_dyadic_dirichlet : ∃ C : ℝ, 1≤C ∧ ∀ K : ℕ, ∀ L : ℝ,
    1≤L → (K:ℝ)*Real.log 2≤(100/49:ℝ)*L → ∀ a : ℝ,
    a∈Set.Icc (0:ℝ) 1 → ∀ s : ℂ, 2/3≤s.re → |s.im|=Real.exp L →
    max (1-s.re) 0≤4*L^(-(2/3:ℝ)) →
    ‖∑ n∈range (2^K-1),(((n+1:ℕ):ℝ)+a:ℂ)^(-s)‖≤
      ((K:ℝ)+1)*C*(L+1)^6 := by
  obtain ⟨C₀,hC₀,hblock⟩ := halasz_log_dirichlet_block
  let D := (10^9:ℝ)*(4:ℝ)^(3/2:ℝ)
  let C := C₀*Real.exp D+8
  have hCE : 0≤C₀*Real.exp D := mul_nonneg (by linarith) (Real.exp_pos _).le
  have hC : 1≤C := by dsimp only [C]; linarith
  refine ⟨C,hC,?_⟩
  intro K L hL hKL a ha s hσ ht hδ
  have hL0 : 0<L := by linarith
  have hpow : 1≤(L+1)^6 := one_le_pow₀ (by linarith)
  have hB0 : 0≤C*(L+1)^6 := by positivity
  let f : ℕ → ℂ := fun n => if n=0 then 0 else (((n:ℝ)+a:ℝ):ℂ)^(-s)
  have hf0 : ‖f 0‖≤C*(L+1)^6 := by simpa [f] using hB0
  have hblocks : ∀ k<K, ∀ H : ℕ, H≤2^k →
      ‖∑ i∈range H,f (2^k+i)‖≤C*(L+1)^6 := by
    intro k hk H hH
    have hNk : 1≤2^k := Nat.one_le_pow _ _ (by norm_num)
    have heq : (∑ i∈range H,f (2^k+i))=
        ∑ i∈range H,((((2^k:ℕ):ℝ)+a+i:ℝ):ℂ)^(-s) := by
      apply sum_congr rfl
      intro i _
      have hn : 2^k+i≠0 := by omega
      simp only [f,ite_eq_right hn,Nat.cast_add]
      congr 2
      ring
    rw [heq]
    by_cases hsmall : k<3
    · have hNH : H≤4 := by interval_cases k <;> norm_num at hH ⊢ <;> omega
      have hs : ‖∑ i∈range H,((((2^k:ℕ):ℝ)+a+i:ℝ):ℂ)^(-s)‖≤H := by
        apply (norm_sum_le _ _).trans
        calc
          _ ≤ ∑ _i∈range H,(1:ℝ) := by
            apply sum_le_sum
            intro i _
            have hx : (1:ℝ)≤((2^k:ℕ):ℝ)+a+i := by
              have hNR : (1:ℝ)≤(2^k:ℕ) := by exact_mod_cast hNk
              have hi : (0:ℝ)≤ i := Nat.cast_nonneg _
              linarith [ha.1]
            rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith :
              (0:ℝ)<((2^k:ℕ):ℝ)+a+i)]
            simp only [Complex.neg_re]
            exact Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
          _ = _ := by simp
      have hHR : (H:ℝ)≤4 := by exact_mod_cast hNH
      have hCB : 8≤C*(L+1)^6 := by
        have hC8 : 8≤C := by dsimp only [C]; linarith
        nlinarith
      linarith
    · have hk3 : 3≤k := by omega
      obtain ⟨hlog,hhalf⟩ := halasz_dyadic_size hk3
      have hy : 0<Real.log ((2^k:ℕ):ℝ) := by linarith
      let lam := L/Real.log ((2^k:ℕ):ℝ)
      have hLy : L=lam*Real.log ((2^k:ℕ):ℝ) := by dsimp only [lam]; field_simp
      have hlam : 49/100≤lam := by
        apply (le_div_iff₀ hy).mpr
        have hkR : (k:ℝ)≤K := by exact_mod_cast hk.le
        have hlog2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
        have hh := mul_le_mul_of_nonneg_right hkR hlog2
        rw [halasz_dyadic_log]
        nlinarith
      have ht' : |s.im|=((2^k:ℕ):ℝ)^lam := by
        rw [Real.rpow_def_of_pos (by positivity : (0:ℝ)<(2^k:ℕ)),ht]
        congr 1
        dsimp only [lam]
        field_simp
      have hb := hblock (2^k) H hNk hH a ha s hσ L lam hL0 hlog hLy hlam hhalf ht'
      have hcost := halasz_weak_strip_cost (show 0≤max (1-s.re) 0 from le_max_right _ _) hL0 hδ
      have hexp : Real.exp ((10^9:ℝ)*(max (1-s.re) 0)^(3/2:ℝ)*L)≤Real.exp D := by
        apply Real.exp_le_exp.mpr
        dsimp only [D]
        nlinarith
      have hc : C₀*(L+1)^6*Real.exp ((10^9:ℝ)*(max (1-s.re) 0)^(3/2:ℝ)*L)≤
          C₀*(L+1)^6*Real.exp D := mul_le_mul_of_nonneg_left hexp (by positivity)
      apply hb.trans
      dsimp only [C]
      nlinarith
  have hp := halasz_dyadic_prefix f hB0 hf0 K hblocks (2^K) le_rfl
  have heq : (∑ n∈range (2^K),f n)=
      ∑ n∈range (2^K-1),(((n+1:ℕ):ℝ)+a:ℂ)^(-s) := by
    have hK : 2^K=(2^K-1)+1 := by have := Nat.one_le_pow K 2 (by norm_num); omega
    rw [hK,sum_range_succ']
    simp only [f,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false,ite_true,Nat.add_sub_cancel,Complex.ofReal_add,
      Nat.cast_zero,add_zero]
  rw [heq] at hp
  simpa only [mul_assoc] using hp

end TwoPointCorrelations

end OAI
