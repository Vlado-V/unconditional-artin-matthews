module

public import ArtinMatthews.CircleNormalizerDefinitions
public import Mathlib.Data.Nat.Totient
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-! Complete reduced-residue blocks inside the actual smooth-cutoff plateau. -/

noncomputable section
namespace ArtinMatthews

theorem circleBlockModulus_injective {F r L : ℕ} (hF : 0 < F) (hr : 0 < r) :
    Set.InjOn (circleBlockModulus F r L) (circleResidueBlocks F r L) := by
  intro p hp q hq hpq
  have hpa : p.2 < r := Finset.mem_range.mp (Finset.mem_filter.mp
    (Finset.mem_product.mp hp).2).1
  have hqa : q.2 < r := Finset.mem_range.mp (Finset.mem_filter.mp
    (Finset.mem_product.mp hq).2).1
  have heq : r * (4 * L / (F * r) + 1 + p.1) + p.2 =
      r * (4 * L / (F * r) + 1 + q.1) + q.2 :=
    Nat.eq_of_mul_eq_mul_left hF hpq
  have hres := congrArg (fun x => x % r) heq
  simp only [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hpa,
    Nat.mod_eq_of_lt hqa] at hres
  apply Prod.ext
  · have hm : r * (4 * L / (F * r) + 1 + p.1) =
        r * (4 * L / (F * r) + 1 + q.1) := by omega
    exact Nat.add_left_cancel (Nat.eq_of_mul_eq_mul_left hr hm)
  · exact hres

theorem circlePlateauModuli_card {F r L : ℕ} (hF : 0 < F) (hr : 0 < r) :
    (circlePlateauModuli F r L).card = circleBlockLength F r L * r.totient := by
  rw [circlePlateauModuli, Finset.card_image_of_injOn (circleBlockModulus_injective hF hr),
    circleResidueBlocks, Finset.product_eq_sprod, Finset.card_product, Finset.card_range]
  rfl

theorem circleBlockLength_lower {F r L : ℕ} (hF : 0 < F) (hr : 0 < r)
    (hL : 4 * (F * r) ≤ L) :
    L ≤ 4 * (F * r) * circleBlockLength F r L := by
  have hD : 0 < F * r := Nat.mul_pos hF hr
  have hm := Nat.mod_add_div L (2 * (F * r))
  have hmod := Nat.mod_lt L (by positivity : 0 < 2 * (F * r))
  have hB : 1 ≤ circleBlockLength F r L := by
    by_contra hB
    have hz : circleBlockLength F r L = 0 := by omega
    unfold circleBlockLength at hz
    rw [hz, mul_zero, add_zero] at hm
    nlinarith
  have hDB : F * r ≤ (F * r) * circleBlockLength F r L := by
    simpa using Nat.mul_le_mul_left (F * r) hB
  unfold circleBlockLength at hDB ⊢
  nlinarith

theorem circleBlockModulus_plateau {F r L : ℕ} (hF : 0 < F) (hr : 0 < r)
    (hL : 4 * (F * r) ≤ L) {p : ℕ × ℕ} (hp : p ∈ circleResidueBlocks F r L) :
    4 * L ≤ circleBlockModulus F r L p ∧ circleBlockModulus F r L p ≤ 5 * L := by
  have hi : p.1 < circleBlockLength F r L := Finset.mem_range.mp (Finset.mem_product.mp hp).1
  have ha : p.2 < r := Finset.mem_range.mp (Finset.mem_filter.mp
    (Finset.mem_product.mp hp).2).1
  have hD : 0 < F * r := Nat.mul_pos hF hr
  have hdiv := Nat.mod_add_div (4 * L) (F * r)
  have hmod := Nat.mod_lt (4 * L) hD
  have hlow : 4 * L < (F * r) * (4 * L / (F * r) + 1) := by nlinarith
  have hi' : (F * r) * (1 + p.1) ≤ (F * r) * circleBlockLength F r L :=
    Nat.mul_le_mul_left _ (by omega)
  have ha' : F * p.2 ≤ F * r := Nat.mul_le_mul_left F (Nat.le_of_lt ha)
  have hcut := Nat.div_mul_le_self L (2 * (F * r))
  have hbase := Nat.div_mul_le_self (4 * L) (F * r)
  unfold circleBlockLength at hi'
  unfold circleBlockModulus
  constructor <;> nlinarith

theorem circlePlateauModuli_subset {F r L : ℕ} (hF : 0 < F) (hr : 0 < r)
    (hFr : F.Coprime r) (hL : 4 * (F * r) ≤ L) :
    circlePlateauModuli F r L ⊆ circleModuli F r L := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  have hpq := circleBlockModulus_plateau hF hr hL hp
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_, ?_⟩
  · exact dvd_mul_right F _
  · have ha : r.Coprime p.2 := (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).2
    have hc : (r * (4 * L / (F * r) + 1 + p.1) + p.2).Coprime r := by
      simpa only [Nat.coprime_mul_left_add_left] using ha.symm
    exact hFr.mul_left hc

end ArtinMatthews
