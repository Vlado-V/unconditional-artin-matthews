module

public import ArtinMatthews.MarkedPhysicalBadArcFamily
public import ArtinMatthews.MarkedPhysicalRootStripGeometry


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite root summation of the literal positive bad-root majorant.
The canonical root set and every target strip are kept in the equality. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalRootStripPoints_card_sum {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (A B α β C D : ℝ) (z : ℤ × ℤ) :
    ((markedPhysicalRootStripPoints g₀ A B α β C D z).card : ℝ) =
      ∑ p ∈ fixedURootMatrixBoxPoints g₀ A B 0 1 C D true true true true true true,
        if (p.2.1 : ℝ)/(p.1 : ℝ) ∈ Set.Icc α β ∧
          |markedMinorIntegerTau ((p.2.1 : ℝ)/(p.1 : ℝ)) z| ≤ 16 then (1 : ℝ) else 0 := by
  simp only [Finset.sum_boole, markedPhysicalRootStripPoints]

theorem markedPhysicalBadRootArc_root_sum {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ)
    (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
    (d₀ Y : ℝ) {S : ℕ} (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (A B C D : ℝ) (hA : 1 < A) (z : ℤ × ℤ)
    (hfirst : Y^(-7/10 : ℝ) < (1/2 : ℝ))
    (hbeta : ∀ j,100*Real.exp (-((Real.log x)^(e j))) < (1/2 : ℝ)) :
    (∑ p ∈ fixedURootMatrixBoxPoints g₀ A B 0 1 C D true true true true true true,
      if |markedMinorIntegerTau ((p.2.1 : ℝ)/(p.1 : ℝ)) z| ≤ 16 then
        markedRawBadRootArcMajorant e x d₀ Y source
          (((p.2.1 : ℝ)/(p.1 : ℝ)) : AddCircle (1 : ℝ)) else 0) =
    ∑ i : MarkedPhysicalBadArcIndex e x source d₀ Y,
      markedPhysicalBadArcCoefficient e x source d₀ Y i *
        ((markedPhysicalRootStripPoints g₀ A B
          (markedPhysicalBadArcLower e x source d₀ Y i)
          (markedPhysicalBadArcUpper e x source d₀ Y i) C D z).card : ℝ) := by
  symm
  simp_rw [markedPhysicalRootStripPoints_card_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have hr := ((fixedURootMatrixBox_mem_ratio g₀ A B 0 1 C D hA
    (by norm_num) (by norm_num) p).mp hp).2
  have heq := markedPhysicalBadArcFamily_eq e x source d₀ Y hr.1 hr.2 hfirst hbeta
  by_cases hs : |markedMinorIntegerTau ((p.2.1 : ℝ)/(p.1 : ℝ)) z| ≤ 16
  · simpa only [hs, and_true, ite_true, mul_ite, mul_one, mul_zero] using heq
  · simp only [hs, and_false, ite_false, mul_zero, Finset.sum_const_zero]

theorem markedPhysicalBadRootArc_weighted_root_sum {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ)
    (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
    (d₀ Y : ℝ) {S : ℕ} (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (A B C D : ℝ) (hA : 1 < A) (V : Finset (ℤ × ℤ)) (w : (ℤ × ℤ) → ℝ)
    (hfirst : Y^(-7/10 : ℝ) < (1/2 : ℝ))
    (hbeta : ∀ j,100*Real.exp (-((Real.log x)^(e j))) < (1/2 : ℝ)) :
    (∑ p ∈ fixedURootMatrixBoxPoints g₀ A B 0 1 C D true true true true true true,
      ∑ z ∈ V, w z * (if |markedMinorIntegerTau ((p.2.1 : ℝ)/(p.1 : ℝ)) z| ≤ 16 then
        markedRawBadRootArcMajorant e x d₀ Y source
          (((p.2.1 : ℝ)/(p.1 : ℝ)) : AddCircle (1 : ℝ)) else 0)) =
    ∑ i : MarkedPhysicalBadArcIndex e x source d₀ Y, ∑ z ∈ V,
      markedPhysicalBadArcCoefficient e x source d₀ Y i * w z *
        ((markedPhysicalRootStripPoints g₀ A B
          (markedPhysicalBadArcLower e x source d₀ Y i)
          (markedPhysicalBadArcUpper e x source d₀ Y i) C D z).card : ℝ) := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, markedPhysicalBadRootArc_root_sum e x source d₀ Y g₀ A B C D hA _ hfirst hbeta,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro z _
  ring

end ArtinMatthews
