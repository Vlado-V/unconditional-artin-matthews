module

public import ArtinMatthews.MarkedPhysicalEndpointState
public import ArtinMatthews.MarkedPhysicalEndpointVectors
public import ArtinMatthews.MarkedPhysicalEndpointRecovery
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Lemmas
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

/-! Exact position counting at a fixed original ordered physical list.
The quotient map retains the scalar coefficients and all physical tests;
only a nonnegative extension to the containing rectangle is used. -/
noncomputable section
open scoped BigOperators
namespace ArtinMatthews
attribute [local instance] Classical.propDecidable

abbrev MarkedPhysicalPositions {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (Z : Finset (ℤ × ℤ)) (a : MarkedPhysicalMarking P M) :=
  {z : Z // MarkedPhysicalStateCondition z.1 a}

def markedPhysicalStatePositionsEquiv {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) :
    MarkedPhysicalState P M Z ≃ Σ a : MarkedPhysicalMarking P M, MarkedPhysicalPositions Z a where
  toFun s := ⟨s.1.2, s.1.1, s.2⟩
  invFun s := ⟨(s.2.1, s.1), s.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def markedPhysicalPositionQuotient {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} {Z : Finset (ℤ × ℤ)}
    (a : MarkedPhysicalMarking P M) (z : MarkedPhysicalPositions Z a) : ℕ × ℕ :=
  (z.1.1.1.natAbs / markedPhysicalMarkingProduct a, z.1.1.2.natAbs)

theorem markedPhysical_position_nat_bounds {Z : Finset (ℤ × ℤ)} {A B : ℕ}
    (hZ : ∀ z ∈ Z, 0 < z.1 ∧ z.1 ≤ (A : ℤ) ∧ 0 < z.2 ∧ z.2 ≤ (B : ℤ))
    (z : Z) : 0 < z.1.1.natAbs ∧ z.1.1.natAbs ≤ A ∧
      0 < z.1.2.natAbs ∧ z.1.2.natAbs ≤ B := by
  obtain ⟨h₁, hA, h₂, hB⟩ := hZ z.1 z.2
  refine ⟨Int.natAbs_pos.mpr h₁.ne', ?_, Int.natAbs_pos.mpr h₂.ne', ?_⟩
  · have : (z.1.1.natAbs : ℤ) ≤ A := by
      simpa only [Int.natCast_natAbs, abs_of_pos h₁] using hA
    exact_mod_cast this
  · have : (z.1.2.natAbs : ℤ) ≤ B := by
      simpa only [Int.natCast_natAbs, abs_of_pos h₂] using hB
    exact_mod_cast this

theorem markedPhysicalPosition_product_dvd {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    {M : ℕ} {Z : Finset (ℤ × ℤ)} (a : MarkedPhysicalMarking P M)
    (z : MarkedPhysicalPositions Z a) : markedPhysicalMarkingProduct a ∣ z.1.1.1.natAbs := by
  apply markedPhysicalMarkingProduct_dvd hP hdis a z.2.2.1
  intro j k
  simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr (z.2.2.2 j k)

theorem markedPhysicalPositionQuotient_mem {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    {M : ℕ} {Z : Finset (ℤ × ℤ)} {A B : ℕ}
    (hZ : ∀ z ∈ Z, 0 < z.1 ∧ z.1 ≤ (A : ℤ) ∧ 0 < z.2 ∧ z.2 ≤ (B : ℤ))
    (a : MarkedPhysicalMarking P M) (z : MarkedPhysicalPositions Z a) :
    markedPhysicalPositionQuotient a z ∈
      (Finset.Ioc 0 (A / markedPhysicalMarkingProduct a)) ×ˢ (Finset.Ioc 0 B) := by
  have hb := markedPhysical_position_nat_bounds hZ z.1
  have hd := markedPhysicalPosition_product_dvd hP hdis a z
  exact Finset.mem_product.mpr ⟨Finset.mem_Ioc.mpr
    ⟨Nat.div_pos (Nat.le_of_dvd hb.1 hd) (markedPhysicalMarkingProduct_pos hP a),
      Nat.div_le_div_right hb.2.1⟩, Finset.mem_Ioc.mpr hb.2.2⟩

theorem markedPhysicalPositionQuotient_injective {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    {M : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, 0 ≤ z.1 ∧ 0 ≤ z.2) (a : MarkedPhysicalMarking P M) :
    Function.Injective (markedPhysicalPositionQuotient (Z := Z) a) := by
  intro z w h
  have hu : z.1.1.1.natAbs = w.1.1.1.natAbs := by
    have h₁ := congrArg Prod.fst h
    change z.1.1.1.natAbs / markedPhysicalMarkingProduct a =
      w.1.1.1.natAbs / markedPhysicalMarkingProduct a at h₁
    have h₂ := congrArg (fun t => markedPhysicalMarkingProduct a * t) h₁
    simpa only [Nat.mul_div_cancel' (markedPhysicalPosition_product_dvd hP hdis a z),
      Nat.mul_div_cancel' (markedPhysicalPosition_product_dvd hP hdis a w)] using h₂
  have hv : z.1.1.2.natAbs = w.1.1.2.natAbs := congrArg Prod.snd h
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext
    ((Int.natAbs_inj_of_nonneg_of_nonneg (hZ _ z.1.2).1 (hZ _ w.1.2).1).mp hu)
    ((Int.natAbs_inj_of_nonneg_of_nonneg (hZ _ z.1.2).2 (hZ _ w.1.2).2).mp hv)

/-- Genuine counting of positions at a fixed full list, with the exact
integer quotient `A/G`; no counting estimate is a premise. -/
theorem markedPhysicalPositions_card_le {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    {M : ℕ} {Z : Finset (ℤ × ℤ)} {A B : ℕ}
    (hZ : ∀ z ∈ Z, 0 < z.1 ∧ z.1 ≤ (A : ℤ) ∧ 0 < z.2 ∧ z.2 ≤ (B : ℤ))
    (a : MarkedPhysicalMarking P M) :
    Fintype.card (MarkedPhysicalPositions Z a) ≤ (A / markedPhysicalMarkingProduct a) * B := by
  classical
  let f : MarkedPhysicalPositions Z a →
      ↥((Finset.Ioc 0 (A / markedPhysicalMarkingProduct a)) ×ˢ (Finset.Ioc 0 B)) :=
    fun z => ⟨markedPhysicalPositionQuotient a z, markedPhysicalPositionQuotient_mem hP hdis hZ a z⟩
  have hf : Function.Injective f := fun z w h =>
    markedPhysicalPositionQuotient_injective hP hdis
      (fun z hz => ⟨(hZ z hz).1.le, (hZ z hz).2.2.1.le⟩) a (congrArg Subtype.val h)
  simpa only [Fintype.card_coe, Finset.card_product, Nat.card_Ioc, Nat.sub_zero] using
    Fintype.card_le_of_injective f hf

theorem markedPhysicalEndpointVector_sq_le_coefficients {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} {Z : Finset (ℤ × ℤ)}
    (a : MarkedPhysicalMarking P M) (z : MarkedPhysicalPositions Z a) (α β : ℕ → ℂ) :
    ‖markedPhysicalEndpointVector P M α β z.1.1‖ ^ 2 ≤
      ‖α (markedPhysicalPositionQuotient a z).1‖ ^ 2 *
        ‖β (markedPhysicalPositionQuotient a z).2‖ ^ 2 := by
  classical
  have hd : ∀ j k, (a j k : ℕ) ∣ z.1.1.1.natAbs := fun j k => by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr (z.2.2.2 j k)
  by_cases hs : MarkedPhysicalEndpointSupport P M z.1.1.1.natAbs
  · rw [markedPhysicalEndpointVector, ite_eq_left hs,
      markedPhysicalSupportedProduct_of_support a z.2.2.1 hd hs,
      norm_mul, Complex.norm_conj, mul_pow]
    rfl
  · simp only [markedPhysicalEndpointVector, ite_eq_right hs, norm_zero, zero_pow (by omega : 2 ≠ 0)]
    positivity

/-- The coefficient-sensitive fixed-list estimate keeps the original
scalar norm sums, including their zeros and supports. -/
theorem markedPhysicalPositions_energy_le_coefficients {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    {M : ℕ} {Z : Finset (ℤ × ℤ)} {A B : ℕ}
    (hZ : ∀ z ∈ Z, 0 < z.1 ∧ z.1 ≤ (A : ℤ) ∧ 0 < z.2 ∧ z.2 ≤ (B : ℤ))
    (a : MarkedPhysicalMarking P M) (α β : ℕ → ℂ) :
    (∑ z : MarkedPhysicalPositions Z a, ‖markedPhysicalEndpointVector P M α β z.1.1‖ ^ 2) ≤
      (∑ m ∈ Finset.Ioc 0 (A / markedPhysicalMarkingProduct a), ‖α m‖ ^ 2) *
        ∑ s ∈ Finset.Ioc 0 B, ‖β s‖ ^ 2 := by
  classical
  have hh := Finset.sum_le_sum_of_injOn (s := Finset.univ)
    (t := (Finset.Ioc 0 (A / markedPhysicalMarkingProduct a)) ×ˢ (Finset.Ioc 0 B))
    (f := fun z : MarkedPhysicalPositions Z a => ‖markedPhysicalEndpointVector P M α β z.1.1‖ ^ 2)
    (g := fun v : ℕ × ℕ => ‖α v.1‖ ^ 2 * ‖β v.2‖ ^ 2)
    (markedPhysicalPositionQuotient a)
    (markedPhysicalPositionQuotient_injective hP hdis
      (fun z hz => ⟨(hZ z hz).1.le, (hZ z hz).2.2.1.le⟩) a).injOn
    (by
      intro v hv
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hv
      exact markedPhysicalPositionQuotient_mem hP hdis hZ a z)
    (fun z _ => markedPhysicalEndpointVector_sq_le_coefficients a z α β)
    (fun v _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  simpa only [Finset.sum_product, ← Finset.mul_sum, ← Finset.sum_mul] using hh

end ArtinMatthews
