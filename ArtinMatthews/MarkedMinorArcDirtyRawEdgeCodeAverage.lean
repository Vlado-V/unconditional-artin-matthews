module

public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeFreshInteger
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeCoreGate
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeOmissionAverage
public import ArtinMatthews.MarkedEstimateVariance
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeFiniteSums
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

/-! The actual source permutation average of independent edge-choice
coordinates is bounded by the proved literal dirty choice expectation. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

abbrev MarkedDirtyIndependentCode {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B) (I : Finset J) (Z : Finset (ℤ × ℤ)) :=
  Z × ((J → Bool) × (MarkedRawPromotionTuple m I × ((j : ↥(Finset.univ \ I)) → ↥(P j.1))))

def markedDirtyRawDeltaCodeMass {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} (source : MarkedRawActive P M)
    (m : MarkedRawMemory P B) (I : Finset J) (jstar : J) (hstar : jstar ∈ I)
    (ν : (j : J) → ↥(P j) → ℝ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (z : ℤ × ℤ) (Q : Finset ℤ) (ρ : ℝ) (o : J → Fin M) (code : MarkedDirtyIndependentCode m I Z) : ℝ :=
  finiteProductMass (fun j : ↥(Finset.univ \ I) => ν j.1) code.2.2.2 *
    markedDirtyRawCoreGate source m jstar (I.erase jstar) Z hZ z
      (markedDirtyRawFreshIntegerProduct code.2.2.2) Q ρ o
      (code.2.2.1 ⟨jstar,hstar⟩) code.1 (markedDirtyPromotionTupleErase code.2.2.1 jstar)

private theorem dirty_weighted_sum_comm {A B : Type*} [Fintype A] [Fintype B]
    (w : B → ℝ) (f : A → B → ℝ) :
    (∑ a, ∑ b, w b*f a b) = ∑ b, w b*∑ a, f a b := by
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

set_option backward.isDefEq.respectTransparency false in
theorem markedDirtyRawDeltaCodeMass_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} (source : MarkedRawActive P M)
    (m : MarkedRawMemory P B) (I : Finset J) (jstar : J) (hstar : jstar ∈ I)
    (ν : (j : J) → ↥(P j) → ℝ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (z : ℤ × ℤ) (Q : Finset ℤ) (ρ : ℝ) (o : J → Fin M) :
    (∑ code : MarkedDirtyIndependentCode m I Z, markedDirtyRawDeltaCodeMass source m I jstar hstar ν Z hZ z Q ρ o code)=
      (2:ℝ)^(Fintype.card J)*∑ fresh : (j : ↥(Finset.univ \ I)) → ↥(P j.1),
        finiteProductMass (fun j : ↥(Finset.univ \ I) => ν j.1) fresh *
          ∑ k : Fin (m.1.1 jstar:ℕ), ∑ v : Z, ∑ t : MarkedRawPromotionTuple m (I.erase jstar),
            markedDirtyRawCoreGate source m jstar (I.erase jstar) Z hZ z
              (markedDirtyRawFreshIntegerProduct fresh) Q ρ o k v t := by
  classical
  let F := (j : ↥(Finset.univ \ I)) → ↥(P j.1)
  let μ : F → ℝ := finiteProductMass (fun j : ↥(Finset.univ \ I) => ν j.1)
  let G (fresh : F) (k : Fin (m.1.1 jstar:ℕ)) (v : Z) (t : MarkedRawPromotionTuple m (I.erase jstar)) :=
    markedDirtyRawCoreGate source m jstar (I.erase jstar) Z hZ z
      (markedDirtyRawFreshIntegerProduct fresh) Q ρ o k v t
  have hsplit (v : Z) :
      (∑ t : MarkedRawPromotionTuple m I, ∑ fresh : F,
        μ fresh*G fresh (t ⟨jstar,hstar⟩) v (markedDirtyPromotionTupleErase t jstar)) =
      ∑ k : Fin (m.1.1 jstar:ℕ), ∑ t : MarkedRawPromotionTuple m (I.erase jstar), ∑ fresh : F,
        μ fresh*G fresh k v t := by
    have hh := Equiv.sum_comp (markedDirtyPromotionTupleSplit m I jstar hstar)
      (fun p => ∑ fresh : F, μ fresh*G fresh p.1 v p.2)
    simpa only [markedDirtyPromotionTupleSplit,Equiv.coe_fn_mk,Fintype.sum_prod_type] using hh
  unfold markedDirtyRawDeltaCodeMass
  simp only [Fintype.sum_prod_type]
  change (∑ v : Z, ∑ _store : J → Bool, ∑ t : MarkedRawPromotionTuple m I, ∑ fresh : F,
    μ fresh*G fresh (t ⟨jstar,hstar⟩) v (markedDirtyPromotionTupleErase t jstar))=_
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Nat.cast_pow,Nat.cast_ofNat,nsmul_eq_mul]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [hsplit,dirty_weighted_sum_comm]
  apply Finset.sum_congr rfl
  intro fresh _
  congr 1
  rw [Finset.sum_comm]

set_option backward.isDefEq.respectTransparency false in
theorem markedDirtyRawDeltaCodeMass_average_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} (source : MarkedRawActive P (pads+1))
    (m : MarkedRawMemory P B) (I : Finset J) (jstar : J) (hstar : jstar ∈ I)
    (ν : (j : J) → ↥(P j) → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (z : ℤ × ℤ) (Q : Finset ℤ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (∑ σ : J → Equiv.Perm (Fin (pads+1)), markedDirtySourceSlotWeight pads σ*
      ∑ code : MarkedDirtyIndependentCode m I Z,
        markedDirtyRawDeltaCodeMass source m I jstar hstar ν Z hZ z Q ρ (fun j => σ j (Fin.last pads)) code) ≤
      (2:ℝ)^(Fintype.card J)*∑ fresh : (j : ↥(Finset.univ \ I)) → ↥(P j.1),
        finiteProductMass (fun j : ↥(Finset.univ \ I) => ν j.1) fresh *
          markedRawDirtyGoodChoiceMass source m jstar (I.erase jstar) Z hZ z
            (markedDirtyRawFreshIntegerProduct fresh) Q ρ (fun _ _ _ => 0) := by
  classical
  rw [markedDirtySourceOmission_expectation pads (Fin.last pads)
    (fun o => ∑ code : MarkedDirtyIndependentCode m I Z,
      markedDirtyRawDeltaCodeMass source m I jstar hstar ν Z hZ z Q ρ o code)]
  simp_rw [markedDirtyRawDeltaCodeMass_sum]
  let F := (j : ↥(Finset.univ \ I)) → ↥(P j.1)
  let μ : F → ℝ := finiteProductMass (fun j : ↥(Finset.univ \ I) => ν j.1)
  let G (o : J → Fin (pads+1)) (fresh : F) :=
    ∑ k : Fin (m.1.1 jstar:ℕ), ∑ v : Z, ∑ t : MarkedRawPromotionTuple m (I.erase jstar),
      markedDirtyRawCoreGate source m jstar (I.erase jstar) Z hZ z
        (markedDirtyRawFreshIntegerProduct fresh) Q ρ o k v t
  have he : (∑ o : J → Fin (pads+1), markedUniformOmissionWeight (pads+1) o*
      ((2:ℝ)^(Fintype.card J)*∑ fresh : F, μ fresh*G o fresh)) =
      (2:ℝ)^(Fintype.card J)*∑ fresh : F, μ fresh*
        ∑ o : J → Fin (pads+1), markedUniformOmissionWeight (pads+1) o*G o fresh := by
    calc
      _ = (2:ℝ)^(Fintype.card J)*∑ o : J → Fin (pads+1), ∑ fresh : F,
          μ fresh*(markedUniformOmissionWeight (pads+1) o*G o fresh) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro o _
        apply Finset.sum_congr rfl
        intro fresh _
        ring
      _ = _ := by rw [dirty_weighted_sum_comm]
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro fresh _
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun j _ => hν _ _))
  simp only [G,Finset.mul_sum]
  exact markedDirtyRawCoreGate_sum_le source m jstar (I.erase jstar) Z hZ z _ Q hρ

end ArtinMatthews
