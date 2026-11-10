module

public import ArtinMatthews.GiantMarkedCharacterCriterion
public import ArtinMatthews.GiantSlotCutoffCore
public import ArtinMatthews.PrimeExtractionMellinBilinear
public import ArtinMatthews.PrimeExtractionRelevantBoxes
public import ArtinMatthews.GiantSlotMellinPhase
public import ArtinMatthews.MarkedTypeIIActualRectangle
public import ArtinMatthews.PrimeExtractionRelevantGeometry
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
public import Mathlib.Tactic.Monotonicity.Lemmas
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
public import Mathlib.Topology.Sheaves.Presheaf


set_option backward.privateInPublic true
@[expose] public section

/-! Apply the proved actual fixed-character Type II estimate to each
Mellin phase on its exact shortened rectangle. -/

namespace ArtinMatthews
noncomputable section
open Filter Finset
open scoped BigOperators

theorem giant_slot_mellin_rectangle_log_saving {J : Type} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (hinj : Function.Injective e)
    (he : ∀ j,(1/10:ℝ) < e j ∧ e j < (1/5:ℝ))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (a T γ C G : ℝ) (hT : 0 < T) (hγ : 0 < γ) (hC : 2 ≤ C) (hG : 0 ≤ G)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    (hdepth : 100*(5*(2*G+2*C+19)+36) < (Fintype.card J:ℝ)) :
    ∀ᶠ x : ℝ in atTop,
      let X := ⌊T*x⌋₊
      let L := Real.log x
      let W := Real.exp (L^(6/25:ℝ))
      ∀ kl ∈ primeExtractionRelevantBoxes X a γ x,
        ∀ β : ℕ → ℂ, (∀ n,‖β n‖ ≤ L^C) →
        (∀ n,β n≠0 → MarkedRoughAbove W n) →
        ∀ t ∈ Set.Icc (-L) L,
          ‖primeExtractionBilinearPhaseSum (primeExtractionDyadicBlock X kl.1)
            (primeExtractionDyadicBlock X kl.2)
            (giantOrdinarySlotCore e χ (giantMarkedCenteredCore ε) x γ β) t‖ ≤
              primeExtractionDyadicHeight kl.1 kl.2 * L^(-G) := by
  filter_upwards [giant_marked_character_giant_typeII_log_saving_x e hinj he χ
    (γ/2) C T G (half_pos hγ) (by linarith) hT hG hε hεq hdepth,
    primeExtractionRelevantBoxes_geometry_eventually (a:=a) hT.le hγ,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (2*Real.pi))),
    eventually_gt_atTop (0:ℝ)] with x hrect hbox hlog hx
  dsimp only
  intro kl hkl β hβ hrough t ht
  let L := Real.log x
  let X := ⌊T*x⌋₊
  let Hm := (2:ℝ)^kl.1
  let Hn := (2:ℝ)^kl.2
  let M : ℕ := max (2^kl.1) (⌊x^γ⌋₊+1)
  let N : ℕ := min X (2*2^kl.1-1)
  let U : ℕ := 2^kl.2
  let V : ℕ := min X (2*2^kl.2-1)
  let W := Real.exp (L^(6/25:ℝ))
  let βt (n : ℕ) := β n * primeExtractionMellinPhase t n
  have hL₁ : 1 ≤ L := (le_max_left _ _).trans hlog
  have hL₂ : 2*Real.pi ≤ L := (le_max_right _ _).trans hlog
  have hL : 0 < L := zero_lt_one.trans_le hL₁
  have hH : Hm*Hn = primeExtractionDyadicHeight kl.1 kl.2 := by
    simp only [Hm,Hn,primeExtractionDyadicHeight,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  have hgeo := hbox kl hkl
  have hmod : |2*Real.pi*t| ≤ L^C := by
    calc
      _ = (2*Real.pi)*|t| := by rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*Real.pi)]
      _ ≤ (2*Real.pi)*L := mul_le_mul_of_nonneg_left (abs_le.mpr ht) (by positivity)
      _ ≤ L*L := mul_le_mul_of_nonneg_right hL₂ hL.le
      _ = L^(2:ℝ) := by rw [Real.rpow_two,pow_two]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL₁ hC
  have hβt (n : ℕ) : ‖βt n‖ ≤ L^C := by
    simpa only [βt,norm_mul,primeExtractionMellinPhase_norm,mul_one] using hβ n
  have hrough' (n : ℕ) (hn : βt n ≠ 0) :
      ∀ p ∈ Nat.primesLE ⌊W⌋₊, ¬p ∣ n := by
    intro p hp hd
    have hβn : β n ≠ 0 := (mul_ne_zero_iff.mp hn).1
    obtain ⟨hpW,hpP⟩ := Nat.mem_primesLE.mp hp
    have hpW' : (p:ℝ) ≤ W := (Nat.cast_le.mpr hpW).trans (Nat.floor_le (Real.exp_nonneg _))
    exact (not_lt_of_ge hpW') (hrough n hβn p hpP hd)
  rw [giant_slot_mellin_phase_eq_interval e χ (giantMarkedCenteredCore ε) x γ t X kl.1 kl.2
    (Real.rpow_nonneg hx.le γ) β,← hH]
  change ‖∑ m ∈ Icc M N,∑ n ∈ Icc U V,
    χ (m*n)*markedMajorCenteredCoefficient W (2*Real.pi*t) m*βt n*
      giantMarkedCenteredCore ε x (m*n-1)*(literalMarkedArrayWeight e x (m*n-1):ℂ)‖ ≤
    Hm*Hn*L^(-G)
  by_cases hMN : M ≤ N
  · have hm : Hm ≤ (M:ℝ) := by
      have h : ((2^kl.1:ℕ):ℝ) ≤ (M:ℝ) := Nat.cast_le.mpr (le_max_left _ _)
      simpa only [Hm,Nat.cast_pow,Nat.cast_ofNat] using h
    have hn : (N:ℝ) ≤ 2*Hm := by
      have h : (N:ℝ) ≤ ((2*2^kl.1:ℕ):ℝ) := Nat.cast_le.mpr
        ((min_le_right X (2*2^kl.1-1)).trans (Nat.sub_le _ _))
      simpa only [Hm,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using h
    have hu : Hn ≤ (U:ℝ) := by simp only [Hn,U,Nat.cast_pow,Nat.cast_ofNat,le_refl]
    have hv : (V:ℝ) ≤ 2*Hn := by
      have h : (V:ℝ) ≤ ((2*2^kl.2:ℕ):ℝ) := Nat.cast_le.mpr
        ((min_le_right X (2*2^kl.2-1)).trans (Nat.sub_le _ _))
      simpa only [Hn,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using h
    exact hrect Hm Hn (2*Real.pi*t) M N U V βt hgeo.2.2.1 hgeo.2.2.2
      (hH.trans_le hgeo.2.1) hm hMN hn hu hv hmod (fun n _ => hβt n)
      (fun n _ => hrough' n)
  · rw [Icc_eq_empty_of_lt (lt_of_not_ge hMN),sum_empty,norm_zero]
    positivity

end
end ArtinMatthews
