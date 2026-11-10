module

public import ArtinMatthews.MarkedMinorArcDirtyTargetChoices
public import ArtinMatthews.MarkedMinorArcBanNeighbors
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! The exceptional-draw target count uses only actual fixed-determinant
neighbors and the normalized source omission average. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

theorem markedRawDirtyTargetChoices_fiber_card_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M : ℕ} (source : MarkedRawActive P M)
    {Pstar : Finset Nat.Primes} (a : MarkedRawParticle Pstar)
    (Zs : Finset ℕ) (V : Finset (ℤ × ℤ)) (hV : ∀ v ∈ V, IsCoprime v.1 v.2)
    (z w : ℤ × ℤ) (T : ℤ) (Q : Finset ℤ) (r : ℝ)
    (hd : markedMinorIntegerDet z w=1) (hz : markedMinorIntegerTau r z ≠ 0)
    (hbox : ∀ v ∈ V, |markedMinorIntegerTau r v/markedMinorIntegerTau r z| ≤ 16)
    (oZ : (J → Fin M) × ℕ) :
    ((markedRawDirtyTargetChoices source a Zs V hV z T Q).filter (fun c => c.1=oZ)).card ≤ 33 := by
  classical
  let F := (markedRawDirtyTargetChoices source a Zs V hV z T Q).filter (fun c => c.1=oZ)
  let W := F.image (fun c => c.2.1)
  have hcard : F.card=W.card := by
    symm
    apply Finset.card_image_iff.mpr
    intro c hc d hdd he
    exact Prod.ext ((Finset.mem_filter.mp hc).2.trans (Finset.mem_filter.mp hdd).2.symm) (Subtype.ext he)
  change F.card ≤ 33
  rw [hcard]
  apply markedBan_targets_card_le r z w
    (markedMinorDirtyDeterminant (markedSourceFullProduct (markedRawNumericActive source):ℤ)
      (markedSourceCopiedProduct (markedRawNumericActive source) oZ.1:ℤ) (a.1.1:ℕ) (oZ.2:ℤ) T) hd hz W
  intro v hv
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hv
  refine ⟨?_,hbox _ c.2.2⟩
  have hj := (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).2.2.2.1
  rw [(Finset.mem_filter.mp hc).2] at hj
  exact hj

theorem markedRawDirtyTargetChoices_crude_card_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M : ℕ} (source : MarkedRawActive P M)
    {Pstar : Finset Nat.Primes} (a : MarkedRawParticle Pstar)
    (Zs : Finset ℕ) (V : Finset (ℤ × ℤ)) (hV : ∀ v ∈ V, IsCoprime v.1 v.2)
    (z w : ℤ × ℤ) (T : ℤ) (Q : Finset ℤ) (r : ℝ)
    (hd : markedMinorIntegerDet z w=1) (hz : markedMinorIntegerTau r z ≠ 0)
    (hbox : ∀ v ∈ V, |markedMinorIntegerTau r v/markedMinorIntegerTau r z| ≤ 16) :
    (markedRawDirtyTargetChoices source a Zs V hV z T Q).card ≤ 33*(M^(Fintype.card J)*Zs.card) := by
  classical
  let F := markedRawDirtyTargetChoices source a Zs V hV z T Q
  have hmap : (F : Set (((J → Fin M) × ℕ) × V)).MapsTo Prod.fst
      ((Finset.univ.product Zs : Finset ((J → Fin M) × ℕ)) : Set ((J → Fin M) × ℕ)) := by
    intro c hc
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hc).1).1
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc
    _ ≤ ∑ _oZ ∈ Finset.univ.product Zs, 33 := Finset.sum_le_sum (fun oZ _ =>
      markedRawDirtyTargetChoices_fiber_card_le source a Zs V hV z w T Q r hd hz hbox oZ)
    _ = _ := by simp [Nat.mul_comm]

theorem markedRawDirtyTargetChoices_crude_weight_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M : ℕ} (hM : 0 < M) (source : MarkedRawActive P M)
    {Pstar : Finset Nat.Primes} (a : MarkedRawParticle Pstar)
    (Zs : Finset ℕ) (V : Finset (ℤ × ℤ)) (hV : ∀ v ∈ V, IsCoprime v.1 v.2)
    (z w : ℤ × ℤ) (T : ℤ) (Q : Finset ℤ) (r : ℝ)
    (hd : markedMinorIntegerDet z w=1) (hz : markedMinorIntegerTau r z ≠ 0)
    (hbox : ∀ v ∈ V, |markedMinorIntegerTau r v/markedMinorIntegerTau r z| ≤ 16) :
    (∑ c ∈ markedRawDirtyTargetChoices source a Zs V hV z T Q,
      markedUniformOmissionWeight M c.1.1) ≤ 33*(Zs.card:ℝ) := by
  have hc : ((markedRawDirtyTargetChoices source a Zs V hV z T Q).card:ℝ) ≤
      33*((M:ℝ)^(Fintype.card J)*(Zs.card:ℝ)) := by
    exact_mod_cast markedRawDirtyTargetChoices_crude_card_le source a Zs V hV z w T Q r hd hz hbox
  have hpow : (M:ℝ)^(Fintype.card J)*(M:ℝ)⁻¹^(Fintype.card J)=1 := by
    rw [← mul_pow,mul_inv_cancel₀ (by exact_mod_cast hM.ne'),one_pow]
  simp only [markedUniformOmissionWeight_eq,Finset.sum_const,nsmul_eq_mul]
  calc
    _ ≤ (33*((M:ℝ)^(Fintype.card J)*(Zs.card:ℝ)))*(M:ℝ)⁻¹^(Fintype.card J) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 33*(Zs.card:ℝ)*((M:ℝ)^(Fintype.card J)*(M:ℝ)⁻¹^(Fintype.card J)) := by ring
    _ = _ := by rw [hpow,mul_one]

end ArtinMatthews
