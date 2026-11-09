module

public import ArtinMatthews.AtkinLehnerMixedModuli
public import ArtinMatthews.AtkinLehnerResidues


set_option backward.privateInPublic true
@[expose] public section

/-! Actual mixed-cusp residue representatives and the inverse-r ordinary kernel. -/
namespace ArtinMatthews

open Matrix CongruenceSubgroup
open scoped BigOperators

theorem atkinMixedSL_diagonal {r s : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (A B c D : ℤ)
    (hdet : (r : ℤ)*A*D-(s : ℤ)*c*B = 1) :
    (atkinMixedSL hr hab A B c D hdet) 0 0 = Real.sqrt (r : ℝ)*(A : ℝ) ∧
    (atkinMixedSL hr hab A B c D hdet) 1 1 = Real.sqrt (r : ℝ)*(D : ℝ) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have ht : Real.sqrt (r : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hrR).ne'
  constructor
  · rw [atkinMixedSL_coe]
    change (1/Real.sqrt (r : ℝ))*(((r : ℤ)*A : ℤ) : ℝ) = _
    push_cast
    field_simp [ht]
    linear_combination -(A : ℝ)*(Real.sq_sqrt hrR.le)
  · rw [atkinMixedSL_coe]
    change (1/Real.sqrt (r : ℝ))*(((r : ℤ)*D : ℤ) : ℝ) = _
    push_cast
    field_simp [ht]
    linear_combination -(D : ℝ)*(Real.sq_sqrt hrR.le)

noncomputable def atkinMixedResiduePairs {r s : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (c : ℕ) [NeZero (s*c)] :
    Finset (ZMod (s*c) × ZMod (s*c)) := by
  classical
  exact Finset.univ.filter fun ad => ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
    γ ∈ Gamma0 (r*s) ∧ ∃ A D : ℤ,
      (atkinRealMap γ * atkinScaling hr hab) 0 0 = Real.sqrt (r : ℝ)*(A : ℝ) ∧
      (atkinRealMap γ * atkinScaling hr hab) 1 0 =
        (s : ℝ)*Real.sqrt (r : ℝ)*(c : ℝ) ∧
      (atkinRealMap γ * atkinScaling hr hab) 1 1 = Real.sqrt (r : ℝ)*(D : ℝ) ∧
      (A : ZMod (s*c)) = ad.1 ∧ (D : ZMod (s*c)) = ad.2

/-- The inverse-r residue constraint is derived from the actual Gamma0 coset. -/
theorem mem_atkinMixedResiduePairs_iff {r s : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (c : ℕ) [NeZero (s*c)]
    (ad : ZMod (s*c) × ZMod (s*c)) :
    ad ∈ atkinMixedResiduePairs hr hab c ↔ (r : ZMod (s*c))*ad.1*ad.2 = 1 := by
  classical
  have ht : Real.sqrt (r : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hr)).ne'
  have hs : (s : ℝ) ≠ 0 := by
    exact_mod_cast left_ne_zero_of_mul (NeZero.ne (s*c))
  have hscale : (s : ℝ)*Real.sqrt (r : ℝ) ≠ 0 := mul_ne_zero hs ht
  simp only [atkinMixedResiduePairs,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨γ,hγ,A,D,hA,hc,hD,ha,hd⟩
    obtain ⟨A',B,c',D',hdet,heq⟩ := atkinMixedSL_parameterization hr hab γ hγ
    obtain ⟨hdiagA,hdiagD⟩ := atkinMixedSL_diagonal hr hab A' B c' D' hdet
    have hlower := atkinMixedSL_lower hr hab A' B c' D' hdet
    rw [heq,hA] at hdiagA
    rw [heq,hD] at hdiagD
    rw [heq,hc] at hlower
    have hAi : A = A' := by exact_mod_cast mul_left_cancel₀ ht hdiagA
    have hDi : D = D' := by exact_mod_cast mul_left_cancel₀ ht hdiagD
    have hci : (c : ℤ) = c' := by exact_mod_cast mul_left_cancel₀ hscale hlower
    rw [← hAi,← hDi,← hci] at hdet
    have hz := congrArg (fun z : ℤ => (z : ZMod (s*c))) hdet
    simp only [Int.cast_mul,Int.cast_sub,Int.cast_one,Int.cast_natCast] at hz
    have hsc : (s : ZMod (s*c))*(c : ZMod (s*c)) = 0 := by
      rw [← Nat.cast_mul]; exact ZMod.natCast_self _
    rw [hsc,zero_mul,sub_zero,ha,hd] at hz
    exact hz
  · intro had
    let A : ℤ := ad.1.val
    let D : ℤ := ad.2.val
    have hA : (A : ZMod (s*c)) = ad.1 := by simp [A]
    have hD : (D : ZMod (s*c)) = ad.2 := by simp [D]
    have hdiv : ((s*c : ℕ) : ℤ) ∣ (r : ℤ)*A*D-1 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      rw [hA,hD,had]
      simp
    obtain ⟨B,hB⟩ := hdiv
    have hdet : (r : ℤ)*A*D-(s : ℤ)*(c : ℤ)*B = 1 := by
      push_cast at hB
      linear_combination hB
    obtain ⟨hdiagA,hdiagD⟩ := atkinMixedSL_diagonal hr hab A B c D hdet
    exact ⟨atkinMixedPreimageSL r s a b A B c D hab hdet,
      atkinMixedPreimageSL_mem r s a b A B c D hab hdet,A,D,hdiagA,
      atkinMixedSL_lower hr hab A B c D hdet,hdiagD,hA,hD⟩

noncomputable def atkinMixedResidueSum {r s : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (c : ℕ) [NeZero (s*c)]
    (m n : ZMod (s*c)) : ℂ :=
  ∑ ad ∈ atkinMixedResiduePairs hr hab c, ZMod.stdAddChar (m*ad.1+n*ad.2)

set_option backward.isDefEq.respectTransparency false in
/-- The exact mixed-cusp inverse-r kernel, with no spectral assertion. -/
theorem atkinMixedResidueSum_eq_ordinary {r s : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (c : ℕ) [NeZero (s*c)]
    (hrq : r.Coprime (s*c)) (m n : ZMod (s*c)) :
    atkinMixedResidueSum hr hab c m n =
      OAI.Erdos970.ErdosKloosterman.sum ZMod.stdAddChar
        (m*(↑(ZMod.unitOfCoprime r hrq)⁻¹ : ZMod (s*c))) n := by
  classical
  let ur := ZMod.unitOfCoprime r hrq
  have hur : (ur : ZMod (s*c)) = r := ZMod.coe_unitOfCoprime r hrq
  have hri : (↑ur⁻¹ : ZMod (s*c))*(r : ZMod (s*c)) = 1 := by rw [← hur]; exact ur.inv_val
  have hrr : (r : ZMod (s*c))*(↑ur⁻¹ : ZMod (s*c)) = 1 := by rw [← hur]; exact ur.val_inv
  unfold atkinMixedResidueSum OAI.Erdos970.ErdosKloosterman.sum
  symm
  apply Finset.sum_bij (fun (u : (ZMod (s*c))ˣ) _hu =>
    ((↑ur⁻¹ : ZMod (s*c))*(u : ZMod (s*c)),(↑u⁻¹ : ZMod (s*c))))
  · intro u _hu
    apply (mem_atkinMixedResiduePairs_iff hr hab c _).mpr
    calc
      _ = ((r : ZMod (s*c))*(↑ur⁻¹ : ZMod (s*c)))*((u : ZMod (s*c))*(↑u⁻¹ : ZMod (s*c))) := by ring
      _ = 1 := by rw [hrr,one_mul]; exact u.val_inv
  · intro u _hu v _hv huv
    apply Units.ext
    exact (ur⁻¹).isUnit.mul_left_cancel (congrArg Prod.fst huv)
  · intro ad had
    have hp := (mem_atkinMixedResiduePairs_iff hr hab c ad).mp had
    let u : (ZMod (s*c))ˣ := ⟨(r : ZMod (s*c))*ad.1,ad.2,hp,by simpa only [mul_comm] using hp⟩
    refine ⟨u,by simp,?_⟩
    apply Prod.ext
    · change (↑ur⁻¹ : ZMod (s*c))*((r : ZMod (s*c))*ad.1) = ad.1
      rw [← mul_assoc,hri,one_mul]
    · rfl
  · intro u _hu
    congr 1
    ring

end ArtinMatthews
