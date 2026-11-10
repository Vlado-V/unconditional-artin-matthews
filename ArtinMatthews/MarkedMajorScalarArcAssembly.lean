module

public import ArtinMatthews.MarkedMajorScalarEndpointSource
public import ArtinMatthews.MarkedMajorArcCoverBound
public import ArtinMatthews.MarkedMajorArcCoverBudget
public import ArtinMatthews.MarkedMajorBandReindex
public import ArtinMatthews.MarkedMajorCharacterBudget
public import ArtinMatthews.MarkedMajorUnitSupport
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The six unit characters and the original finite major cover are
applied to the exact scalar form, with both coefficient supports. -/
namespace ArtinMatthews
open Finset
open scoped ComplexConjugate
noncomputable section

theorem markedTypeIIScalarFullMajor_reindex {I J : Type*} [Fintype I] [Fintype J]
    (E : I ≃ J) (P : J → Finset ℕ) (S T : Finset ℕ)
    (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (Q Y : ℝ) (α β : ℕ → ℂ) :
    markedTypeIIScalarFullMajor (fun i => P (E i)) S T η ψ Q Y α β =
      markedTypeIIScalarFullMajor P S T η ψ Q Y α β := by
  simp only [markedTypeIIScalarFullMajor,markedTypeIIScalarMajorOn,
    markedMajorLabelSet_reindex,markedMajorLabelMass_reindex]

private theorem scalarRoughUnit {q n : ℕ} {W : ℝ}
    (hq : 0 < q) (hW : (q:ℝ)<W) (hn : MarkedPhysicalRoughAt W n) :
    IsUnit (n:ZMod q) := by
  apply (ZMod.isUnit_iff_coprime n q).mpr
  by_contra h
  obtain ⟨p,hp,hpn,hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hpq' : (p:ℝ) ≤ q := Nat.cast_le.mpr (Nat.le_of_dvd hq hpq)
  exact (not_lt_of_ge (hn p hp hpn)) (hpq'.trans_lt hW)

theorem markedTypeIIScalarFullMajor_norm_of_character_terms
    {J : Type*} [Fintype J] (bands : J → Finset ℕ)
    (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (S T : Finset ℕ) (α β : ℕ → ℂ)
    {L a D X Y W Q : ℝ} (hL : 4 ≤ L) (hX : 0 < X) (hY : 0 < Y)
    (hQ : 0 ≤ Q) (hQa : Q ≤ L^a) (hQW : Q < W)
    (hη : Function.support η ⊆ Set.Icc 1 4)
    (hP : ∀ j p,p ∈ bands j → p.Prime)
    (hQp : ∀ j p,p ∈ bands j → Q < (p:ℝ))
    (hrα : ∀ m ∈ S,α m ≠ 0 → MarkedPhysicalRoughAt W m)
    (hrβ : ∀ n ∈ T,β n ≠ 0 → MarkedPhysicalRoughAt W n)
    (hterm : ∀ (q : ℕ) [NeZero q], (q:ℝ) ≤ Q →
      ∀ (χ : AddChar (MarkedUnitTuple q) ℂ) (θ : ℝ), |θ| ≤ 2*Q →
      ‖(Y:ℂ)⁻¹*markedMajorArcCharacterTerm (markedMajorScalarTripleSet bands Y S T)
        (markedMajorScalarTripleSet bands Y S T) (markedMajorScalarBare bands η Y α β)
        (markedMajorScalarBare bands η Y (fun m => conj (α m)) (fun n => conj (β n))) ψ q χ θ Y‖ ≤
        (Y*X)*L^(-(D+3*a+1+6*a))) :
    ‖markedTypeIIScalarFullMajor bands S T η ψ Q Y α β‖ ≤ (Y*X)*L^(-D) := by
  rw [markedTypeIIScalarFullMajor_eq_kernelSource bands S T η ψ Q Y α β hY hη]
  let K := markedMajorScalarTripleSet bands Y S T
  let A := markedMajorScalarBare bands η Y α β
  let B := markedMajorScalarBare bands η Y (fun m => conj (α m)) (fun n => conj (β n))
  have hLp : 0 < L := (by norm_num : (0:ℝ)<4).trans_le hL
  have hArc (q : ℕ) (hq : 0 < q) (hqQ : (q:ℝ) ≤ Q) (h : ℤ) (θ : ℝ) (hθ : |θ| ≤ 2*Q) :
      ‖(Y:ℂ)⁻¹*markedMajorArcSourceSum K K A B ψ q h θ Y‖ ≤ (Y*X)*L^(-(D+3*a+1)) := by
    let : NeZero q := ⟨Nat.ne_of_gt hq⟩
    have hqP (j : J) (p : ℕ) (hp : p∈bands j) : q < p :=
      Nat.cast_lt.mp (hqQ.trans_lt (hQp j p hp))
    have hu (z : ℕ×(ℕ×ℕ)) (hz : z∈K) (ha : α z.2.1 ≠ 0) (hb : β z.2.2 ≠ 0) :
        IsUnit (z.1:ZMod q) ∧ IsUnit (z.2.1:ZMod q) ∧ IsUnit (z.2.2:ZMod q) := by
      obtain ⟨hs,hm,hn⟩ := by simpa only [K,markedMajorScalarTripleSet,mem_product] using hz
      exact ⟨marked_label_isUnit bands hP hqP (mem_filter.mp hs).1,
        scalarRoughUnit hq (hqQ.trans_lt hQW) (hrα _ hm ha),
        scalarRoughUnit hq (hqQ.trans_lt hQW) (hrβ _ hn hb)⟩
    have hA (z : ℕ×(ℕ×ℕ)) (hz : z∈K) (ha : A z ≠ 0) :=
      hu z hz (fun hzero => ha (by simp only [A,markedMajorScalarBare,hzero,mul_zero,zero_mul]))
        (fun hzero => ha (by simp only [A,markedMajorScalarBare,hzero,mul_zero]))
    have hB (z : ℕ×(ℕ×ℕ)) (hz : z∈K) (hb : B z ≠ 0) :=
      hu z hz (fun hzero => hb (by simp only [B,markedMajorScalarBare,hzero,map_zero,mul_zero,zero_mul]))
        (fun hzero => hb (by simp only [B,markedMajorScalarBare,hzero,map_zero,mul_zero]))
    rw [markedMajor_arc_character_expansion K K A B ψ q h θ Y hA hB,mul_sum]
    let c := fun χ : AddChar (MarkedUnitTuple q) ℂ => markedFourierCoeff (markedResiduePhase q h) χ
    let t := fun χ : AddChar (MarkedUnitTuple q) ℂ => markedMajorArcCharacterTerm K K A B ψ q χ θ Y
    let E := (Y*X)*L^(-(D+3*a+1+6*a))
    have hE : 0 ≤ E := by dsimp only [E]; positivity
    change ‖∑ χ : AddChar (MarkedUnitTuple q) ℂ,(Y:ℂ)⁻¹*(c χ*t χ)‖ ≤ _
    calc
      _ ≤ ∑ χ : AddChar (MarkedUnitTuple q) ℂ,‖(Y:ℂ)⁻¹*(c χ*t χ)‖ := norm_sum_le _ _
      _ ≤ ∑ χ : AddChar (MarkedUnitTuple q) ℂ,‖c χ‖*E := by
        apply sum_le_sum
        intro χ _
        rw [mul_left_comm ((Y:ℂ)⁻¹),norm_mul]
        exact mul_le_mul_of_nonneg_left (hterm q hqQ χ θ hθ) (norm_nonneg _)
      _ = (∑ χ : AddChar (MarkedUnitTuple q) ℂ,‖c χ‖)*E := (sum_mul ..).symm
      _ ≤ (q:ℝ)^6*E := mul_le_mul_of_nonneg_right (markedResiduePhase_total_norm_le q h) hE
      _ ≤ _ := markedMajor_character_cost hLp (hqQ.trans hQa) hY.le hX.le
  have hC : 0 ≤ (Y*X)*L^(-(D+3*a+1)) := by positivity
  exact (markedMajorKernelSource_norm_of_arcs K K A B ψ hQ hY hC hArc).trans
    (markedMajor_cover_cost hL hQ hQa hY.le hX.le)

end
end ArtinMatthews
