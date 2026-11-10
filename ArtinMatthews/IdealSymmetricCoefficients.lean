module

public import Mathlib.Analysis.Complex.Norm
public import ArtinMatthews.IdealProbeSupports
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
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


set_option backward.privateInPublic true
@[expose] public section

/-! Symmetric Fourier coefficients obey the exact Hoeffding support
count. The coefficient mask records the actual probe and tail events. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def idealCoefficientSupport {α : Type*} {M : ℕ} (a₀ : α) (t : Fin M → α) : Finset (Fin M) :=
  univ.filter (fun i => t i≠a₀)

def idealCoefficientPermutation {α : Type*} {M : ℕ} (π : Equiv.Perm (Fin M)) :
    (Fin M → α) ≃ (Fin M → α) where
  toFun t i := t (π i)
  invFun t i := t (π.symm i)
  left_inv t := by funext i; simp
  right_inv t := by funext i; simp

theorem idealCoefficientSupport_permute {α : Type*} {M : ℕ}
    (a₀ : α) (π : Equiv.Perm (Fin M)) (t : Fin M → α) :
    idealCoefficientSupport a₀ (idealCoefficientPermutation π.symm t)=
      (idealCoefficientSupport a₀ t).map π.toEmbedding := by
  ext i
  simp only [idealCoefficientSupport,idealCoefficientPermutation,Equiv.coe_fn_mk,mem_map_equiv]
  change (i ∈ (univ.filter fun q : Fin M => t (π.symm q) ≠ a₀)) ↔
    (π.symm i ∈ (univ.filter fun q : Fin M => t q ≠ a₀))
  rw [Finset.mem_filter,Finset.mem_filter]
  simp only [Finset.mem_univ,true_and]

def idealCoefficientSupportEnergy {α : Type*} [Fintype α] {M : ℕ}
    (a₀ : α) (c : (Fin M → α) → ℂ) (S : Finset (Fin M)) : ℝ :=
  ∑ t : Fin M → α,if idealCoefficientSupport a₀ t=S then ‖c t‖^2 else 0

theorem idealCoefficientSupportEnergy_nonneg {α : Type*} [Fintype α] {M : ℕ}
    (a₀ : α) (c : (Fin M → α) → ℂ) (S : Finset (Fin M)) :
    0 ≤ idealCoefficientSupportEnergy a₀ c S :=
  sum_nonneg fun _ _ => by split_ifs <;> positivity

theorem idealCoefficientSupportEnergy_permute {α : Type*} [Fintype α] {M : ℕ}
    (a₀ : α) (c : (Fin M → α) → ℂ)
    (hc : ∀ π t,c (idealCoefficientPermutation π t)=c t)
    (π : Equiv.Perm (Fin M)) (S : Finset (Fin M)) :
    idealCoefficientSupportEnergy a₀ c (S.map π.toEmbedding)=idealCoefficientSupportEnergy a₀ c S := by
  unfold idealCoefficientSupportEnergy
  rw [← (idealCoefficientPermutation π.symm).sum_comp]
  apply sum_congr rfl
  intro t _
  rw [idealCoefficientSupport_permute,hc]
  have he : (idealCoefficientSupport a₀ t).map π.toEmbedding=S.map π.toEmbedding ↔
      idealCoefficientSupport a₀ t=S :=
        ⟨fun h => Finset.map_injective π.toEmbedding h,fun h => congrArg _ h⟩
  simp only [he]

theorem idealCoefficientSupportEnergy_total {α : Type*} [Fintype α] {M : ℕ}
    (a₀ : α) (c : (Fin M → α) → ℂ) :
    (∑ S∈(univ : Finset (Fin M)).powerset,idealCoefficientSupportEnergy a₀ c S)=
      ∑ t : Fin M → α,‖c t‖^2 := by
  unfold idealCoefficientSupportEnergy
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  rw [sum_eq_single (idealCoefficientSupport a₀ t)]
  · simp
  · intro S _ hS
    exact ite_eq_right (Ne.symm hS)
  · intro h
    exact (h (mem_powerset.mpr (subset_univ _))).elim

theorem idealCoefficientSupportEnergy_selected {α : Type*} [Fintype α] {M : ℕ}
    (a₀ : α) (c : (Fin M → α) → ℂ) (P T : Finset (Fin M)) :
    (∑ S∈(univ : Finset (Fin M)).powerset,
      if P ⊆ S ∧ Disjoint S T then idealCoefficientSupportEnergy a₀ c S else 0)=
      ∑ t : Fin M → α,if P ⊆ idealCoefficientSupport a₀ t ∧
        Disjoint (idealCoefficientSupport a₀ t) T then ‖c t‖^2 else 0 := by
  unfold idealCoefficientSupportEnergy
  have hsum (S : Finset (Fin M)) :
      (if P ⊆ S ∧ Disjoint S T then
        ∑ t : Fin M → α,if idealCoefficientSupport a₀ t=S then ‖c t‖^2 else 0
      else 0) =
        ∑ t : Fin M → α,if P ⊆ S ∧ Disjoint S T then
          (if idealCoefficientSupport a₀ t=S then ‖c t‖^2 else 0) else 0 := by
    split_ifs <;> simp
  simp_rw [hsum]
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  rw [sum_eq_single (idealCoefficientSupport a₀ t)]
  · split_ifs <;> simp_all
  · intro S _ hS
    rw [ite_eq_right (Ne.symm hS)]
    split_ifs <;> rfl
  · intro h
    exact (h (mem_powerset.mpr (subset_univ _))).elim

theorem idealCoefficientSupportEnergy_probe_bound {α : Type*} [Fintype α] {M : ℕ}
    (a₀ : α) (c : (Fin M → α) → ℂ)
    (hc : ∀ π t,c (idealCoefficientPermutation π t)=c t)
    (P T : Finset (Fin M)) (hPT : Disjoint P T) (hM : 0 < M)
    (hm : 1 ≤ P.card) (hell : 1 ≤ T.card)
    (hlarge : (P.card+T.card)*(P.card+T.card-1) ≤ M) :
    (∑ t : Fin M → α,if P ⊆ idealCoefficientSupport a₀ t ∧
        Disjoint (idealCoefficientSupport a₀ t) T then ‖c t‖^2 else 0) ≤
      (2/(P.card+1 : ℕ))*∑ t : Fin M → α,‖c t‖^2 := by
  let w := idealCoefficientSupportEnergy a₀ c
  have hw : ∀ S∈(univ : Finset (Fin M)).powerset,0 ≤ w S :=
    fun S _ => idealCoefficientSupportEnergy_nonneg a₀ c S
  have hsym (j : ℕ) (S : Finset (Fin M)) (hS : S∈(univ : Finset (Fin M)).powersetCard j)
      (S' : Finset (Fin M)) (hS' : S'∈(univ : Finset (Fin M)).powersetCard j) : w S=w S' := by
    obtain ⟨π,hπ⟩ := Equiv.Perm.exists_map_finset_eq S S'
      ((mem_powersetCard.mp hS).2.trans (mem_powersetCard.mp hS').2.symm)
    rw [← hπ]
    exact (idealCoefficientSupportEnergy_permute a₀ c hc π S).symm
  rw [← idealCoefficientSupportEnergy_selected,← idealCoefficientSupportEnergy_total]
  rw [Finset.sum_powerset,Finset.sum_powerset,mul_sum]
  apply sum_le_sum
  intro j _
  rw [← sum_filter]
  change (∑ S∈idealProbeSupports univ P T j,w S) ≤ _
  exact idealProbeSupports_uniform_weight (subset_univ _) (subset_univ _) hPT
    (by simpa using hM) hm hell (by simpa using hlarge) j w
    (fun S hS => hw S (mem_powerset.mpr (mem_powersetCard.mp hS).1)) (hsym j)

end
end ArtinMatthews
