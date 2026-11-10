module

public import ArtinMatthews.GiantMarkedCharacterCriterion
public import ArtinMatthews.MarkedTypeIIActualDeterminant
public import ArtinMatthews.MarkedTypeIILabelDyadBudget
public import ArtinMatthews.MarkedTypeIIQuotientDampedSaving
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

/-! The literal fixed-character centered-giant Type II rectangle, with
the actual determinant input now discharged on every occupied label dyad. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section

theorem giant_marked_character_giant_typeII_log_saving
    {J : Type} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (hinj : Function.Injective e)
    (he : ∀ j,(1/10:ℝ)<e j ∧ e j<(1/5:ℝ))
    {Mχ : ℕ} [NeZero Mχ] (ξ : DirichletCharacter ℂ Mχ)
    (δ C Kbox G : ℝ) (hδ : 0<δ) (hC : 0≤C) (hKbox : 0<Kbox) (hG : 0≤G)
    {ε : ℝ} (hε : 0<ε) (hεq : ε<1/4)
    (hdepth : 100*(5*(2*G+2*C+19)+36)<(Fintype.card J:ℝ)) :
    ∀ᶠ L : ℝ in atTop,∀ Hm Hn modulation : ℝ,∀ M N l r : ℕ,∀ β : ℕ → ℂ,
      Real.exp (δ*L)≤Hm → Real.exp (δ*L)≤Hn → Hm*Hn≤Kbox*Real.exp L →
      Hm≤(M:ℝ) → M≤N → (N:ℝ)≤2*Hm → Hn≤(l:ℝ) → (r:ℝ)≤2*Hn →
      |modulation|≤L^C → (∀ n∈Icc l r,‖β n‖≤L^C) →
      (∀ n∈Icc l r,β n≠0 → ∀ p∈Nat.primesLE ⌊Real.exp (L^(6/25:ℝ))⌋₊,¬p∣n) →
      let x := Real.exp L
      let W := Real.exp (L^(6/25:ℝ))
      ‖∑ m∈Icc M N,∑ n∈Icc l r,
        ξ (m*n)*markedMajorCenteredCoefficient W modulation m*β n*
          giantMarkedCenteredCore ε x (m*n-1)*(literalMarkedArrayWeight e x (m*n-1):ℂ)‖ ≤
        Hm*Hn*L^(-G) := by
  have heLo : ∀ j,(1/10:ℝ)≤e j := fun j => (he j).1.le
  have heHi : ∀ j,e j≤(1/5:ℝ) := fun j => (he j).2.le
  have hgroups : 2≤Fintype.card J := by
    have h : (2:ℝ)≤(Fintype.card J:ℝ) :=
      (show (2:ℝ)≤100*(5*(2*G+2*C+19)+36) by linarith).trans hdepth.le
    exact_mod_cast h
  let B := max 8 (2*(Fintype.card J:ℝ))
  have hB : 8≤B := le_max_left _ _
  have hB' : 2*(Fintype.card J:ℝ)≤B := le_max_right _ _
  have hdep : 100*(5*((2*G+7)+2*C+12)+36)<(Fintype.card J:ℝ) := by
    have h : (2*G+7)+2*C+12=2*G+2*C+19 := by ring
    rwa [h]
  have hdet := markedTypeII_actual_fixed_determinant_log_saving e hinj he ξ δ C B Kbox (2*G+7)
    hδ hC hB hKbox (by linarith) hdep
  have hrect := giant_marked_character_giant_typeII_log_saving_of_determinants e hinj he hgroups
    δ Kbox C G hδ hKbox hε hεq
  have hlabels := Real.tendsto_exp_atTop.eventually (markedTypeII_actual_label_dyads e heLo heHi hgroups)
  filter_upwards [hdet,hrect,hlabels,eventually_ge_atTop (0:ℝ)] with L hd hr hy hL
  intro Hm Hn modulation M N l r β hHm hHn hX hHM hMN hNH hl hu hmod hβ hrough
  dsimp only
  have hS (m : ℕ) (hm : m∈Icc M N) : Hm≤(m:ℝ) ∧ (m:ℝ)≤2*Hm :=
    ⟨hHM.trans (Nat.cast_le.mpr (mem_Icc.mp hm).1),(Nat.cast_le.mpr (mem_Icc.mp hm).2).trans hNH⟩
  have hT (n : ℕ) (hn : n∈Icc l r) : Hn≤(n:ℝ) ∧ (n:ℝ)≤2*Hn :=
    ⟨hl.trans (Nat.cast_le.mpr (mem_Icc.mp hn).1),(Nat.cast_le.mpr (mem_Icc.mp hn).2).trans hu⟩
  apply hr Mχ ξ Hm Hn modulation (Icc M N) (Icc l r) β hHm hHn hX hS hT hβ
  intro j hj
  dsimp only
  have hyj := hy.2.1 j hj
  have hYlo : Real.exp (L^(1/10:ℝ))≤(2:ℝ)^j := by
    simpa only [Real.log_exp] using hyj.1
  have hYhi : (2:ℝ)^j≤Real.exp (B*L^(1/5:ℝ)) := by
    have hb : (2:ℝ)^j≤Real.exp (2*(Fintype.card J:ℝ)*L^(1/5:ℝ)) := by
      simpa only [Real.log_exp] using hyj.2
    exact hb.trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hB' (Real.rpow_nonneg hL _)))
  exact hd Hm Hn ((2:ℝ)^j) modulation M N l r β hHm hHn hX hHM hMN hNH hl hu hYlo hYhi hmod hβ hrough

theorem giant_marked_character_giant_typeII_log_saving_x
    {J : Type} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (hinj : Function.Injective e)
    (he : ∀ j,(1/10:ℝ)<e j ∧ e j<(1/5:ℝ))
    {Mχ : ℕ} [NeZero Mχ] (ξ : DirichletCharacter ℂ Mχ)
    (δ C Kbox G : ℝ) (hδ : 0<δ) (hC : 0≤C) (hKbox : 0<Kbox) (hG : 0≤G)
    {ε : ℝ} (hε : 0<ε) (hεq : ε<1/4)
    (hdepth : 100*(5*(2*G+2*C+19)+36)<(Fintype.card J:ℝ)) :
    ∀ᶠ x : ℝ in atTop,∀ Hm Hn modulation : ℝ,∀ M N l r : ℕ,∀ β : ℕ → ℂ,
      x^δ≤Hm → x^δ≤Hn → Hm*Hn≤Kbox*x →
      Hm≤(M:ℝ) → M≤N → (N:ℝ)≤2*Hm → Hn≤(l:ℝ) → (r:ℝ)≤2*Hn →
      |modulation|≤(Real.log x)^C → (∀ n∈Icc l r,‖β n‖≤(Real.log x)^C) →
      (∀ n∈Icc l r,β n≠0 → ∀ p∈Nat.primesLE ⌊Real.exp ((Real.log x)^(6/25:ℝ))⌋₊,¬p∣n) →
      let W := Real.exp ((Real.log x)^(6/25:ℝ))
      ‖∑ m∈Icc M N,∑ n∈Icc l r,
        ξ (m*n)*markedMajorCenteredCoefficient W modulation m*β n*
          giantMarkedCenteredCore ε x (m*n-1)*(literalMarkedArrayWeight e x (m*n-1):ℂ)‖ ≤
        Hm*Hn*(Real.log x)^(-G) := by
  filter_upwards [Real.tendsto_log_atTop.eventually
      (giant_marked_character_giant_typeII_log_saving e hinj he ξ δ C Kbox G hδ hC hKbox hG hε hεq hdepth),
    eventually_gt_atTop (0:ℝ)] with x hx hxp
  have hscale : Real.exp (δ*Real.log x)=x^δ := by
    rw [Real.rpow_def_of_pos hxp,mul_comm]
  simpa only [Real.exp_log hxp,hscale] using hx

end
end ArtinMatthews
