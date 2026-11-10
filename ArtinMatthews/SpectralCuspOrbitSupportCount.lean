module

public import ArtinMatthews.SpectralCuspHeightRowCount
public import ArtinMatthews.SpectralCuspEisensteinParabolic
public import ArtinMatthews.SpectralInfinityOrbitalWeil
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine compact cusp seed meets only the stated number of group
translates. The integer horizontal cell resolves every source-row fiber. -/

noncomputable section
open Matrix Set
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0_cusp_orbit_support_card_le (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (z : UpperHalfPlane) {A : ℝ} (hA : 0 < A)
    (t : Finset (CongruenceSubgroup.Gamma0 N))
    (ht : ∀ γ ∈ t, ((a*γ.val) • z).re ∈ Icc 0 (2*(N : ℝ)) ∧
      A ≤ ((a*γ.val) • z).im) :
    (t.card : ℝ) ≤
      (2*(gamma0CuspFrequencyStep N a : ℝ)+1)*
        ((cuspEisensteinHeightRows N a z A hA).card : ℝ) := by
  let w := (gamma0CuspTrueWidth N a : ℝ)
  let d := gamma0CuspFrequencyStep N a
  let x (γ : CongruenceSubgroup.Gamma0 N) := ((a*γ.val) • z).re
  let R := cuspEisensteinHeightRows N a z A hA
  let J := Finset.Icc (0 : ℤ) (2*(d : ℤ))
  let f (γ : CongruenceSubgroup.Gamma0 N) := (cuspEisensteinSourceRow N a γ,⌊x γ/w⌋)
  have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N a)
  have hdw : w*(d : ℝ) = (N : ℝ) := by
    change (gamma0CuspTrueWidth N a : ℝ)*(gamma0CuspFrequencyStep N a : ℝ) = (N : ℝ)
    exact_mod_cast gamma0CuspFrequencyStep_mul_width N a
  have hmap : Set.MapsTo f (t : Set (CongruenceSubgroup.Gamma0 N))
      ((R ×ˢ J : Finset (Gamma0CuspEisensteinRows N 1 a × ℤ)) : Set _) := by
    intro γ hγ
    apply Finset.mem_product.mpr
    constructor
    · apply (cuspEisensteinHeightRows_mem N a z hA _).mpr
      rw [cuspEisensteinRowHeight_of_row N 1 a _ (a*γ.val) rfl]
      exact (ht γ hγ).2
    · apply Finset.mem_Icc.mpr
      have hγx := (ht γ hγ).1
      have h₀ : 0 ≤ x γ/w := div_nonneg hγx.1 hw.le
      have h₁ : x γ/w ≤ ((2*(d : ℤ) : ℤ) : ℝ) := by
        apply (div_le_iff₀ hw).mpr
        have h : (((2*(d : ℤ) : ℤ) : ℝ))*w = 2*(N : ℝ) := by
          push_cast
          rw [mul_assoc,mul_comm (d : ℝ) w,hdw]
        exact hγx.2.trans_eq h.symm
      exact ⟨Int.floor_nonneg.mpr h₀,by
        simpa only [Int.floor_intCast] using Int.floor_le_floor h₁⟩
  have hinj : (t : Set (CongruenceSubgroup.Gamma0 N)).InjOn f := by
    intro γ _ δ _ he
    let M (γ : CongruenceSubgroup.Gamma0 N) : gamma0CuspCorrespondence N 1 a :=
      ⟨a*γ.val,by
        change a⁻¹*(a*γ.val)*1 ∈ CongruenceSubgroup.Gamma0 N
        simpa only [inv_mul_cancel_left,mul_one] using γ.property⟩
    have hr : (M γ).val 1 = (M δ).val 1 :=
      congrArg Subtype.val (congrArg Prod.fst he)
    obtain ⟨k,hk⟩ := (cuspEisenstein_same_row_iff_source_translation N 1 a (M γ) (M δ)).mp hr
    have hx := congrArg (fun g : SL(2, ℤ) => (g • z).re) hk
    change x δ = ((integerTranslation ((gamma0CuspTrueWidth N a : ℤ)*k)*(a*γ.val)) • z).re at hx
    rw [mul_smul,integerTranslation_eq_T_zpow,ModularGroup.re_T_zpow_smul] at hx
    simp only [Int.cast_mul,Int.cast_natCast] at hx
    have hx' : x δ/w = x γ/w+(k : ℝ) := by
      rw [hx]
      change (x γ+w*(k : ℝ))/w = _
      field_simp [hw.ne']
    have hf : ⌊x γ/w⌋ = ⌊x δ/w⌋ := congrArg Prod.snd he
    rw [hx',Int.floor_add_intCast] at hf
    have hk₀ : k = 0 := by omega
    rw [hk₀,mul_zero,integerTranslation_eq_T_zpow,zpow_zero,one_mul] at hk
    apply Subtype.ext
    exact (mul_left_cancel (show a*δ.val = a*γ.val from hk)).symm
  have hcard := Finset.card_le_card_of_injOn f hmap hinj
  have hJ : (J.card : ℝ) = 2*(d : ℝ)+1 := by
    have h : (J.card : ℤ) = 2*(d : ℤ)+1 := by
      change ((Finset.Icc (0 : ℤ) (2*(d : ℤ))).card : ℤ) = _
      rw [Int.card_Icc_of_le 0 _ (by positivity),sub_zero]
    exact_mod_cast h
  calc
    _ ≤ ((R ×ˢ J : Finset (Gamma0CuspEisensteinRows N 1 a × ℤ)).card : ℝ) := by exact_mod_cast hcard
    _ = _ := by rw [Finset.card_product,Nat.cast_mul,hJ,mul_comm]

theorem gamma0Infinity_orbit_support_card_le (N : ℕ) [NeZero N]
    (z : UpperHalfPlane) {A : ℝ} (hA : 0 < A) (t : Finset (CongruenceSubgroup.Gamma0 N))
    (ht : ∀ γ ∈ t, (γ.val • z).re ∈ Icc 0 (2*(N : ℝ)) ∧ A ≤ (γ.val • z).im) :
    (t.card : ℝ) ≤ (2*(N : ℝ)+1)*(4*(1+2/((N : ℝ)*A))) := by
  have h := gamma0_cusp_orbit_support_card_le N 1 z hA t (by simpa only [one_mul] using ht)
  rw [gamma0CuspFrequencyStep_identity] at h
  exact h.trans (mul_le_mul_of_nonneg_left (gamma0Infinity_heightRows_card_le N z hA) (by positivity))

end ArtinMatthews
