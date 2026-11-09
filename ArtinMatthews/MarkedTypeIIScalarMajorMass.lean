module

public import ArtinMatthews.MarkedTypeIIDeterminantBandMass
public import ArtinMatthews.MarkedMajorCharacterPhase
public import ArtinMatthews.MarkedMinorArcBanMajor


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute mass of the literal major detector on one pair of label
products. The additional factor retains any endpoint, primitive, dyad
or cofactor flags in the signed sum and contracts them in the bound. -/
namespace ArtinMatthews
noncomputable section
open Finset
open scoped ComplexConjugate
attribute [local instance] Classical.propDecidable

def markedTypeIIScalarMajorTerm (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ)
    (Q Y : ℝ) (α β : ℕ → ℂ) (b a : ℕ) (v w : ℕ×ℕ) : ℂ :=
  let t := markedMajorIntegerDeterminant (b,v) (a,w)
  η ((b:ℝ)/Y)*η ((a:ℝ)/Y)*α v.1*conj (α w.1)*β v.2*conj (β w.2)*
    ψ ((t:ℝ)/Y)*markedBanMajorKernel Q Y (t-(b:ℤ)+(a:ℤ))

theorem markedTypeIIScalarMajorTerm_norm_le
    (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) {Q Y R W A B : ℝ}
    (hQ : 0 ≤ Q) (hY : 0 < Y) (hW : 0 ≤ W) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hη : ∀ u, ‖η u‖ ≤ 1) (hψ : ∀ u, ‖ψ u‖ ≤ W)
    (hsupp : Function.support ψ ⊆ Set.Icc (-R) R)
    (α β : ℕ → ℂ) (b a : ℕ) (v w : ℕ×ℕ) (G : ℂ)
    (hG : ‖G‖ ≤ 1) (hv : ‖α v.1‖ ≤ A) (hw : ‖α w.1‖ ≤ A)
    (hv' : ‖β v.2‖ ≤ B) (hw' : ‖β w.2‖ ≤ B) :
    ‖G*markedTypeIIScalarMajorTerm η ψ Q Y α β b a v w‖ ≤
      if MarkedTypeIIDeterminantBand a b Y R (v.1*v.2) (w.1*w.2)
      then (A*B)^2*W*(4*Q^3/Y) else 0 := by
  by_cases ht : MarkedTypeIIDeterminantBand a b Y R (v.1*v.2) (w.1*w.2)
  · rw [ite_eq_left ht]
    unfold markedTypeIIScalarMajorTerm
    dsimp only
    simp only [norm_mul, Complex.norm_conj]
    calc
      _ ≤ 1*(1*1*A*A*B*B*W*(4*Q^3/Y)) := by
        gcongr
        all_goals
          first
          | exact hG
          | exact hη _
          | exact hv
          | exact hw
          | exact hv'
          | exact hw'
          | exact hψ _
          | exact markedBanMajorKernel_norm_le hQ hY _
      _ = _ := by ring
  · rw [ite_eq_right ht]
    have hzero : ψ ((markedMajorIntegerDeterminant (b,v) (a,w):ℝ)/Y)=0 := by
      by_contra hn
      have h := hsupp hn
      change -(R) ≤ (markedMajorIntegerDeterminant (b,v) (a,w):ℝ)/Y ∧
        (markedMajorIntegerDeterminant (b,v) (a,w):ℝ)/Y ≤ R at h
      rw [← abs_le,abs_div,abs_of_pos hY,div_le_iff₀ hY] at h
      apply ht
      simpa only [MarkedTypeIIDeterminantBand,markedMajorIntegerDeterminant,Int.cast_sub,
        Int.cast_mul,Int.cast_natCast,Nat.cast_mul,mul_assoc] using h
    simp only [markedTypeIIScalarMajorTerm,hzero,mul_zero,zero_mul,norm_zero,le_refl]

theorem markedTypeIIScalarMajorPair_abs_le
    (S T N : Finset ℕ) (Z : ℕ)
    (hS : ∀ v ∈ S×ˢN, v.1*v.2 ∈ Icc 1 Z)
    (hT : ∀ v ∈ T×ˢN, v.1*v.2 ∈ Icc 1 Z)
    (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) {Q Y R W A B : ℝ}
    (hQ : 0 ≤ Q) (hY : 0 < Y) (hR : 0 ≤ R) (hW : 0 ≤ W)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hη : ∀ u, ‖η u‖ ≤ 1) (hψ : ∀ u, ‖ψ u‖ ≤ W)
    (hsupp : Function.support ψ ⊆ Set.Icc (-R) R)
    (α β : ℕ → ℂ) (hαS : ∀ m ∈ S, ‖α m‖ ≤ A) (hαT : ∀ m ∈ T, ‖α m‖ ≤ A)
    (hβ : ∀ n ∈ N, ‖β n‖ ≤ B)
    (b a : ℕ) (hb : Y ≤ (b:ℝ)) (ha : Y ≤ (a:ℝ))
    (G : (ℕ×ℕ) → (ℕ×ℕ) → ℂ) (hG : ∀ v ∈ S×ˢN, ∀ w ∈ T×ˢN, ‖G v w‖ ≤ 1) :
    (∑ v ∈ S×ˢN, ∑ w ∈ T×ˢN, ‖G v w*markedTypeIIScalarMajorTerm η ψ Q Y α β b a v w‖) ≤
      ((A*B)^2*W*(4*Q^3/Y))*((2*R+1)*(Z:ℝ)*(∑ d ∈ Icc 1 Z,1/(d:ℝ))^3) := by
  let C := (A*B)^2*W*(4*Q^3/Y)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hsum :
      (∑ v ∈ S×ˢN, ∑ w ∈ T×ˢN,
        if MarkedTypeIIDeterminantBand a b Y R (v.1*v.2) (w.1*w.2) then C else 0) =
        C*∑ v ∈ S×ˢN, ∑ w ∈ T×ˢN,
          if MarkedTypeIIDeterminantBand a b Y R (v.1*v.2) (w.1*w.2) then 1 else 0 := by
    simp only [mul_sum,mul_ite,mul_one,mul_zero]
  calc
    _ ≤ ∑ v ∈ S×ˢN, ∑ w ∈ T×ˢN,
        if MarkedTypeIIDeterminantBand a b Y R (v.1*v.2) (w.1*w.2) then C else 0 := by
      apply sum_le_sum
      intro v hv
      apply sum_le_sum
      intro w hw
      obtain ⟨hvm,hvn⟩ := mem_product.mp hv
      obtain ⟨hwm,hwn⟩ := mem_product.mp hw
      exact markedTypeIIScalarMajorTerm_norm_le η ψ hQ hY hW hA hB hη hψ hsupp
        α β b a v w (G v w) (hG v hv w hw) (hαS _ hvm) (hαT _ hwm) (hβ _ hvn) (hβ _ hwn)
    _ = _ := hsum
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (markedTypeIIEndpointDeterminantBand_count S N T N Z a b hS hT hY hR ha hb) hC

end
end ArtinMatthews
