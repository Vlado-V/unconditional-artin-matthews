module

public import ArtinMatthews.GiantSignedGhostMemoryProduct
public import ArtinMatthews.GiantSignedGhostWeight
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

/-! Uniform finite-group ghost energy, with no bound on pending degrees. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

theorem giantSignedGhostMemory_uniform_energy
    (aMax cMax dMax massMax : ℝ) (ha : aMax < 1) (hc : 0 ≤ cMax) (hd : 0 ≤ dMax) :
    ∃ v : ℝ, 1 < v ∧ ∀ (B : Type*) [Fintype B] [DecidableEq B]
      (P : B → Finset ℕ) [∀ (g : B) (p : P g), NeZero p.val]
      (ν : ∀ g, P g → ℝ), (∀ g p, 0 ≤ ν g p) → (∀ g, (∑ p : P g, ν g p) ≤ massMax) →
      ∀ A C D z : B → ℂ,
        (∀ g, ‖A g‖ ≤ aMax) → (∀ g, ‖C g‖ ≤ cMax) →
        (∀ g, ‖D g‖ ≤ dMax) → (∀ g, ‖z g‖ ≤ 2) →
      ∀ f : GiantSignedMemory P → ℂ, GiantSignedMemorySymmetric f →
      ∀ Cf u : ℝ, 0 ≤ Cf → 0 < u → (∀ m, ‖f m‖ ≤ Cf * u ^ (∑ g, m.1 g)) →
        giantSignedGhostMemoryEnergy ν (giantSignedGhostMemoryApply ν A (fun g => z g * C g) D f) ≤
          ENNReal.ofReal (Real.exp ((2 * cMax + dMax) * massMax * v)) ^ Fintype.card B *
            giantSignedGhostMemoryEnergy ν f := by
  obtain ⟨v, hv, hvbound⟩ := giantSignedGhostWeight_exists aMax cMax dMax ha
  refine ⟨v, hv, ?_⟩
  intro B instB instDec P instP ν hν hmass A C D z hA hC hD hz f hfs Cf u hCf hu hf
  have hv0 : 0 < v := lt_trans zero_lt_one hv
  have hb (g : B) := hvbound ‖A g‖ ‖C g‖ ‖D g‖ (hA g)
    (by simpa only [abs_of_nonneg (norm_nonneg _)] using hC g)
    (by simpa only [abs_of_nonneg (norm_nonneg _)] using hD g)
  simp only [abs_of_nonneg (norm_nonneg _)] at hb
  have hzc (g : B) : ‖z g * C g‖ ≤ 2 * ‖C g‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hz g) (norm_nonneg _)
  have hcolumn (g : B) : ‖A g‖ + ‖z g * C g‖ / v ≤ 1 := by
    have hh := div_le_div_of_nonneg_right (hzc g) hv0.le
    linarith [(hb g).2]
  have he := giantSignedGhostMemoryApply_energy ν hν A (fun g => z g * C g) D v hv0
    (fun g => (hb g).1.le) hcolumn f hfs Cf u hCf hu hf
  have hbound (g : B) : ENNReal.ofReal (Real.exp ((‖z g * C g‖ + ‖D g‖) *
      (∑ p : P g, ν g p) * v)) ≤
      ENNReal.ofReal (Real.exp ((2 * cMax + dMax) * massMax * v)) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ hv0.le
    exact mul_le_mul
      (add_le_add ((hzc g).trans (mul_le_mul_of_nonneg_left (hC g) (by norm_num))) (hD g))
      (hmass g) (Finset.sum_nonneg fun p _ => hν g p)
      (add_nonneg (mul_nonneg (by norm_num) hc) hd)
  have hp := Finset.prod_le_prod (fun g (_ : g ∈ (Finset.univ : Finset B)) => hbound g)
  simp only [Finset.prod_const, Finset.card_univ] at hp
  exact he.trans (mul_le_mul' hp le_rfl)

def giantSignedGhostMemoryGroup {B : Type*} [Fintype B] [DecidableEq B]
    {P : B → Finset ℕ} (ν : ∀ g, P g → ℝ) (V : B → ℝ) (q ρ : ℝ)
    (f : GiantSignedMemory P → ℂ) : GiantSignedMemory P → ℂ :=
  giantSignedGhostMemoryApply ν (fun _ => ((q / ρ ^ 2 : ℝ) : ℂ))
    (fun g => ((-(1-q) * V g / ρ : ℝ) : ℂ)) (fun _ => ((-(1-q) / ρ : ℝ) : ℂ)) f

theorem giantSignedGhostMemoryGroup_energy
    {B : Type*} [Fintype B] [DecidableEq B] {P : B → Finset ℕ}
    [∀ (g : B) (p : P g), NeZero p.val]
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ) (q ρ v : ℝ) (hv : 0 < v)
    (hrow : |q / ρ ^ 2| + |-(1-q) / ρ| / v ≤ 1)
    (hcol : ∀ g, |q / ρ ^ 2| + |-(1-q) * V g / ρ| / v ≤ 1)
    (f : GiantSignedMemory P → ℂ) (hfs : GiantSignedMemorySymmetric f)
    (Cf u : ℝ) (hCf : 0 ≤ Cf) (hu : 0 < u)
    (hf : ∀ m, ‖f m‖ ≤ Cf * u ^ (∑ g, m.1 g)) :
    giantSignedGhostMemoryEnergy ν (giantSignedGhostMemoryGroup ν V q ρ f) ≤
      (∏ g, ENNReal.ofReal (Real.exp ((|-(1-q) * V g / ρ| + |-(1-q) / ρ|) *
        (∑ p : P g, ν g p) * v))) * giantSignedGhostMemoryEnergy ν f := by
  have he := giantSignedGhostMemoryApply_energy ν hν
    (fun _ => ((q / ρ ^ 2 : ℝ) : ℂ)) (fun g => ((-(1-q) * V g / ρ : ℝ) : ℂ))
    (fun _ => ((-(1-q) / ρ : ℝ) : ℂ)) v hv
    (fun _ => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hrow)
    (fun g => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hcol g) f hfs Cf u hCf hu hf
  simpa only [giantSignedGhostMemoryGroup, Complex.norm_real, Real.norm_eq_abs] using he

end
end ArtinMatthews
