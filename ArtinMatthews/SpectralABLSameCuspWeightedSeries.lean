module

public import ArtinMatthews.SpectralABLSameCuspBareReindex
public import ArtinMatthews.SpectralABLWeightedWeil
public import ArtinMatthews.SpectralGamma0LocalFourierBessel
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

/-! The weighted arithmetic estimate for the actual same-cusp ABL
geometric series, in the physical Bessel variable. -/

noncomputable section
open Set
open scoped MatrixGroups
open OAI.Erdos970.ErdosKloosterman

namespace ArtinMatthews

theorem spectralABL_diagonal_argument_scale (n : ℤ) :
    2*|cuspFourierFrequency 1 n| = 4*Real.pi*(n.natAbs : ℝ) := by
  rw [cuspFourierFrequency, div_one, abs_mul,
    abs_of_nonneg (show 0 ≤ 2*Real.pi by positivity), ← Int.cast_abs, ← Nat.cast_natAbs]
  ring


theorem spectralABLOrdinaryDiagonal_bareSeries_weighted {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (n : ℤ), n ≠ 0 →
      ∀ (a : ℝ), 0 < a → a ≤ 1 →
      ∀ (A : ℕ), 1 ≤ A → ∀ (H : ℂ → ℂ) (B : ℝ), 0 ≤ B →
      (∀ X : ℝ, 0 < X →
        ‖spectralABLDiagonalBareAmplitude H n X‖ ≤ B*min 1 ((X/a^2)^(2*A))) →
      let f := gamma0AtkinSameCuspBareSummand N n H
      let M := C*B*((N : ℝ)*(n.natAbs : ℝ)/a)^ε*
        (Real.sqrt ((n.natAbs : ℝ)*(Nat.gcd N n.natAbs : ℝ))/((N : ℝ)*a))
      Summable (fun k => ‖f k‖) ∧ (∑' k, ‖f k‖) ≤ M ∧ ‖∑' k, f k‖ ≤ M := by
  obtain ⟨C,hC,hW⟩ := spectralABLWeightedDiagSum_weil_physical hε
  refine ⟨C,hC,?_⟩
  intro N inst n hn a ha ha1 A hA H B hB hkernel
  dsimp only
  let L := 4*Real.pi*(n.natAbs : ℝ)/((N : ℝ)*a^2)
  let f := gamma0AtkinSameCuspBareSummand N n H
  let w := spectralABLWeightedDiagWeight N n L A
  have hfreq : 0 < |cuspFourierFrequency 1 n| :=
    abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn)
  have hpoint (k : ℕ) : ‖f k‖ ≤ B*w k := by
    let d := k+1
    let Q := N*d
    let X := 2*|cuspFourierFrequency 1 n|/(Q : ℝ)
    let _ : NeZero d := ⟨Nat.succ_ne_zero k⟩
    have hQ : 0 < (Q : ℝ) := Nat.cast_pos.mpr (NeZero.pos Q)
    have hX : 0 < X := div_pos (mul_pos two_pos hfreq) hQ
    have hratio : X/a^2 = L/(d : ℝ) := by
      dsimp only [X,L,Q]
      rw [spectralABL_diagonal_argument_scale, Nat.cast_mul, div_div, div_div]
      congr 1
      ring
    change ‖standardSum Q n n/(Q : ℂ)*spectralABLDiagonalBareAmplitude H n X‖ ≤
      B*(‖standardSum Q n n‖/(Q : ℝ)*min 1 ((L/(d : ℝ))^(2*A)))
    rw [norm_mul,norm_div,Complex.norm_natCast]
    have hK := hkernel X hX
    rw [hratio] at hK
    calc
      _ ≤ (‖standardSum Q n n‖/(Q : ℝ))*(B*min 1 ((L/(d : ℝ))^(2*A))) :=
        mul_le_mul_of_nonneg_left hK (div_nonneg (norm_nonneg _) hQ.le)
      _ = _ := by ring
  obtain ⟨hsW,hWbd⟩ := hW N n hn a ha ha1 A hA
  have hsBw : Summable (fun k => B*w k) := hsW.mul_left B
  have hsF : Summable (fun k => ‖f k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hpoint hsBw
  have hbd : (∑' k, ‖f k‖) ≤ C*B*((N : ℝ)*(n.natAbs : ℝ)/a)^ε*
      (Real.sqrt ((n.natAbs : ℝ)*(Nat.gcd N n.natAbs : ℝ))/((N : ℝ)*a)) := by
    calc
      _ ≤ ∑' k, B*w k := hsF.tsum_le_tsum hpoint hsBw
      _ = B*(∑' k, w k) := tsum_mul_left
      _ ≤ B*(C*((N : ℝ)*(n.natAbs : ℝ)/a)^ε*
          (Real.sqrt ((n.natAbs : ℝ)*(Nat.gcd N n.natAbs : ℝ))/((N : ℝ)*a))) :=
        mul_le_mul_of_nonneg_left hWbd hB
      _ = _ := by ring
  exact ⟨hsF,hbd,(norm_tsum_le_tsum_norm hsF).trans hbd⟩

theorem gamma0AtkinSameCusp_bareSeries_weighted {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r s : ℕ) [NeZero r] [NeZero s],
      r.Coprime s → ∀ (n : ℤ), n ≠ 0 → ∀ (a : ℝ), 0 < a → a ≤ 1 →
      ∀ (A : ℕ), 1 ≤ A → ∀ (H : ℂ → ℂ) (B : ℝ), 0 ≤ B →
      (∀ X : ℝ, 0 < X →
        ‖spectralABLDiagonalBareAmplitude H n X‖ ≤ B*min 1 ((X/a^2)^(2*A))) →
      let N := r*s
      let f (c : Ioi (0 : ℕ)) := gamma0TrueWidthBareFibre N
        (gamma0CuspOneOver s) (gamma0CuspOneOver s) c n n H
      let M := C*B*((N : ℝ)*(n.natAbs : ℝ)/a)^ε*
        (Real.sqrt ((n.natAbs : ℝ)*(Nat.gcd N n.natAbs : ℝ))/((N : ℝ)*a))
      Summable (fun c => ‖f c‖) ∧ (∑' c, ‖f c‖) ≤ M ∧ ‖∑' c, f c‖ ≤ M := by
  obtain ⟨C,hC,hW⟩ := spectralABLOrdinaryDiagonal_bareSeries_weighted hε
  refine ⟨C,hC,?_⟩
  intro r s instR instS hcop n hn a ha ha1 A hA H B hB hkernel
  dsimp only
  let f (c : Ioi (0 : ℕ)) := gamma0TrueWidthBareFibre (r*s)
    (gamma0CuspOneOver s) (gamma0CuspOneOver s) c n n H
  let e := gamma0AtkinSameCuspIndex s
  let F := gamma0AtkinSameCuspBareSummand (r*s) n H
  obtain ⟨hs, hbd, hnorm⟩ := hW (r*s) n hn a ha ha1 A hA H B hB hkernel
  have hzero (c : Ioi (0 : ℕ)) (hc : c ∉ range e) : ‖f c‖ = 0 := by
    have h := gamma0AtkinSameCusp_bareFibre_zero r s c
      (fun h => hc ((gamma0AtkinSameCuspIndex_range s c).mpr h)) n H
    change ‖gamma0TrueWidthBareFibre (r*s) (gamma0CuspOneOver s)
      (gamma0CuspOneOver s) c n n H‖ = 0
    rw [h,norm_zero]
  have heq : (fun k => ‖f (e k)‖) = fun k => ‖F k‖ :=
    funext (fun k => congrArg norm (gamma0AtkinSameCusp_bareFibre_index r s hcop k n H))
  have hsE : Summable (fun k => ‖f (e k)‖) := heq.symm ▸ hs
  have hsF : Summable (fun c => ‖f c‖) :=
    (e.injective.summable_iff (f := fun c => ‖f c‖) hzero).mp hsE
  have hsup : Function.support (fun c => ‖f c‖) ⊆ range e := by
    intro c hc
    by_contra h
    exact hc (hzero c h)
  have htsum : (∑' c, ‖f c‖) = ∑' k, ‖F k‖ := by
    calc
      _ = ∑' k, ‖f (e k)‖ := (e.injective.tsum_eq hsup).symm
      _ = _ := congrArg tsum heq
  have hsum : (∑' c, f c) = ∑' k, F k :=
    (gamma0AtkinSameCusp_bareSeries_reindex r s hcop n H).2
  exact ⟨hsF, htsum.symm ▸ hbd, hsum.symm ▸ hnorm⟩

end ArtinMatthews
