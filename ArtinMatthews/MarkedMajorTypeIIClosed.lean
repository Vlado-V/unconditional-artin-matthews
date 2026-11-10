module

public import ArtinMatthews.MarkedMajorClosedIntervalSplit
public import ArtinMatthews.MarkedMajorTypeIIMixed
public import ArtinMatthews.MarkedMajorTypeIIParameters
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The actual major bound for the full closed coefficient interval. The
integer lower endpoint is kept in four exact bulk/singleton pairings. -/
namespace ArtinMatthews
open Filter Finset
open scoped ContDiff

 theorem markedMajor_typeII_option_closed {J : Type} [Fintype J] [DecidableEq J]
    (e : Option J → ℝ) (hinj : Function.Injective e)
    (he : ∀ i,(1/10:ℝ)<e i ∧ e i<(1/5:ℝ))
    (δ C A Kx P : ℝ) (hδ : 0 < δ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hP : 0 ≤ P)
    (cutoff : ℝ → ℂ) (hcutoff : ContDiff ℝ ∞ cutoff) (hnorm : ∀ y,‖cutoff y‖ ≤ 1)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) (hinterval : lo/2 < 8*hi)
    (hsupp : Function.support cutoff ⊆ Set.Icc lo hi)
    (ψ : SchwartzMap ℝ ℂ) {R : ℝ} (hψ : tsupport ψ ⊆ Set.Icc (-R) R) :
    ∀ᶠ L : ℝ in atTop, ∀ H U Y modulation : ℝ, ∀ M N l r : ℕ, ∀ β : ℕ → ℂ,
      Real.exp (δ*L) ≤ H → Real.exp (δ*L) ≤ U → H*U ≤ Kx*Real.exp L →
      H ≤ (M:ℝ) → M ≤ N → (N:ℝ) ≤ 2*H → U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U →
      0 < Y → |modulation| ≤ L^C → (∀ n ∈ Icc l r,‖β n‖ ≤ L^C) →
      (∀ n ∈ Icc l r,β n ≠ 0 → ∀ p ∈ Nat.primesLE ⌊Real.exp (L^(6/25:ℝ))⌋₊,¬p∣n) →
      ‖markedMajorIntervalPairSum (fun i => markedLogPowerBand (e i) (Real.exp L))
        cutoff ψ (L^A) Y (Real.exp (L^(6/25:ℝ))) modulation
        (Icc M N) (Icc M N) l r β‖ ≤ (Y*(H*U))*L^(-P) := by
  have hhalf := (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (half_pos hδ))).eventually
    (eventually_ge_atTop (2:ℝ))
  filter_upwards [markedMajor_typeII_option_mixed e hinj he δ C A Kx (P+1) hδ hC hA
    (by linarith) cutoff hcutoff hnorm hlo hhi hinterval hsupp ψ hψ,
    markedMajorTypeII_scale_budget δ Kx hδ,hhalf,eventually_ge_atTop (4:ℝ)] with L hs hrange htwo hL
  change 2 ≤ Real.exp ((δ/2)*L) at htwo
  intro H U Y modulation M N l r β hH hU hX hHM hMN hNH hl hr hY hmod hβ hrough
  have hHp : 0 < H := (Real.exp_pos _).trans_le hH
  have hUp : 0 < U := (Real.exp_pos _).trans_le hU
  have hscale := hrange H U (N:ℝ) hH hU hX hNH
  have hH2 : 2 ≤ H := by linarith [hscale.2.2.2.1]
  have hMNreal : (M:ℝ) ≤ N := by exact_mod_cast hMN
  have hsingle := markedMajor_singleton_scale hH2 hHM (hMNreal.trans hNH)
  have hM1 : 1 ≤ M := by exact_mod_cast (by linarith : (1:ℝ) ≤ M)
  let F := markedMajorIntervalPairSum (fun i => markedLogPowerBand (e i) (Real.exp L))
    cutoff ψ (L^A) Y (Real.exp (L^(6/25:ℝ))) modulation
  let E := (Y*(H*U))*L^(-(P+1))
  have hblock (H₁ H₂ u₁ v₁ u₂ v₂ : ℝ)
      (h₁lo : H/2 ≤ H₁) (h₁hi : H₁ ≤ H) (h₂lo : H/2 ≤ H₂) (h₂hi : H₂ ≤ H)
      (h₁u : H₁ ≤ u₁) (huv₁ : u₁ ≤ v₁) (hv₁ : v₁ ≤ 2*H₁)
      (h₂u : H₂ ≤ u₂) (huv₂ : u₂ ≤ v₂) (hv₂ : v₂ ≤ 2*H₂) :
      ‖F (Ioc ⌊u₁⌋₊ ⌊v₁⌋₊) (Ioc ⌊u₂⌋₊ ⌊v₂⌋₊) l r β‖ ≤ E := by
    have hb := hs H₁ H₂ U u₁ v₁ u₂ v₂ Y modulation l r β
      (hscale.2.2.2.1.trans h₁lo) (hscale.2.2.2.1.trans h₂lo) hscale.2.2.2.2.1
      ((mul_le_mul_of_nonneg_right h₁hi hUp.le).trans hX)
      ((mul_le_mul_of_nonneg_right h₂hi hUp.le).trans hX)
      (by linarith) (by linarith) h₁u huv₁ hv₁ h₂u huv₂ hv₂ hl hr hY hmod hβ hrough
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h₁hi hUp.le) hY.le)
      (Real.rpow_nonneg (by linarith) _))
  have hh : H/2 ≤ H := half_le_self hHp.le
  have hbb : ‖F (Ioc M N) (Ioc M N) l r β‖ ≤ E := by
    simpa only [Nat.floor_natCast] using hblock H H M N M N hh le_rfl hh le_rfl
      hHM hMNreal hNH hHM hMNreal hNH
  have hsb : ‖F {M} (Ioc M N) l r β‖ ≤ E := by
    rw [markedMajor_singleton_interval hM1]
    simpa only [Nat.floor_natCast] using hblock ((M:ℝ)/2) H ((M:ℝ)-1) M M N
      hsingle.1 hsingle.2.1 hh le_rfl hsingle.2.2.1 hsingle.2.2.2.1
      hsingle.2.2.2.2 hHM hMNreal hNH
  have hbs : ‖F (Ioc M N) {M} l r β‖ ≤ E := by
    rw [markedMajor_singleton_interval hM1]
    simpa only [Nat.floor_natCast] using hblock H ((M:ℝ)/2) M N ((M:ℝ)-1) M
      hh le_rfl hsingle.1 hsingle.2.1 hHM hMNreal hNH
      hsingle.2.2.1 hsingle.2.2.2.1 hsingle.2.2.2.2
  have hss : ‖F {M} {M} l r β‖ ≤ E := by
    rw [markedMajor_singleton_interval hM1]
    exact hblock ((M:ℝ)/2) ((M:ℝ)/2) ((M:ℝ)-1) M ((M:ℝ)-1) M
      hsingle.1 hsingle.2.1 hsingle.1 hsingle.2.1
      hsingle.2.2.1 hsingle.2.2.2.1 hsingle.2.2.2.2
      hsingle.2.2.1 hsingle.2.2.2.1 hsingle.2.2.2.2
  have hall : ‖F (Icc M N) (Icc M N) l r β‖ ≤ 4*E := by
    have heq : F (Icc M N) (Icc M N) l r β =
        F (Ioc M N) (Ioc M N) l r β+F {M} (Ioc M N) l r β+
        F (Ioc M N) {M} l r β+F {M} {M} l r β :=
      markedMajorIntervalPairSum_closed_split _ _ _ _ _ _ _ M N hMN l r β
    rw [heq]
    have ht₁ := norm_add_le (F (Ioc M N) (Ioc M N) l r β) (F {M} (Ioc M N) l r β)
    have ht₂ := norm_add_le (F (Ioc M N) (Ioc M N) l r β+F {M} (Ioc M N) l r β)
      (F (Ioc M N) {M} l r β)
    have ht₃ := norm_add_le (F (Ioc M N) (Ioc M N) l r β+F {M} (Ioc M N) l r β+
      F (Ioc M N) {M} l r β) (F {M} {M} l r β)
    linarith
  have hlog : 4*L^(-(P+1)) ≤ L^(-P) := by
    calc
      _ ≤ L*L^(-(P+1)) := mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg (by linarith) _)
      _ = _ := by
        conv_lhs => lhs; rw [← Real.rpow_one L]
        rw [← Real.rpow_add (by linarith : 0 < L)]
        congr 1
        ring
  exact hall.trans (by
    dsimp only [E]
    nlinarith [mul_le_mul_of_nonneg_left hlog (mul_pos hY (mul_pos hHp hUp)).le])

end ArtinMatthews
