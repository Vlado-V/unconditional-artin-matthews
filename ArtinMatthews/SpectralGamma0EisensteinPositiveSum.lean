module

public import ArtinMatthews.SpectralGamma0EisensteinSignedRows
public import ArtinMatthews.SpectralGamma0EisensteinConvergence


set_option backward.privateInPublic true
@[expose] public section

/-! The actual half-row sum equals its leading term plus the positive-first-coordinate sum. -/
noncomputable section
open Set
namespace ArtinMatthews

theorem gamma0Eisenstein_signed_tsum (N : ℕ)
    (f : Gamma0EisensteinPrimitiveRows N → ℂ) (hf : Summable f)
    (hneg : ∀ v, f (gamma0EisensteinNegPrimitiveRow N v)=f v) :
    (∑' v, f v) = f (gamma0EisensteinZeroPrimitiveRow N false)+
      f (gamma0EisensteinZeroPrimitiveRow N true)+
      2*(∑' v : Gamma0EisensteinPositiveRows N, f v.val) := by
  let e := gamma0EisensteinSignedRowEquiv N
  have hg : Summable (fun i => f (e i)) := e.summable_iff.mpr hf
  have hL : Summable (fun b : Bool => f (e (.inl b))) :=
    hg.comp_injective (i := Sum.inl) Sum.inl_injective
  have hR : Summable (fun p : Gamma0EisensteinPositiveRows N × Bool => f (e (.inr p))) :=
    hg.comp_injective (i := Sum.inr) Sum.inr_injective
  have hsplit := Summable.tsum_sum (f := fun i : Gamma0EisensteinSignedRowIndex N => f (e i)) hL hR
  have hprod := Summable.tsum_prod (f := fun p : Gamma0EisensteinPositiveRows N × Bool => f (e (.inr p))) hR
  rw [← e.tsum_eq f,hsplit,hprod]
  simp [e,gamma0EisensteinSignedRowEquiv,gamma0EisensteinSignedRow,hneg,
    ← two_mul,tsum_mul_left]
  exact add_comm _ _

def gamma0EisensteinPrimitiveTerm (N : ℕ) (s : ℂ) (v : Gamma0EisensteinPrimitiveRows N)
    (z : UpperHalfPlane) : ℂ :=
  ((z.im/‖(v.val 0:ℂ)*z+v.val 1‖^2:ℝ):ℂ)^s

theorem gamma0EisensteinPrimitiveTerm_eq (N : ℕ) (s : ℂ) (v : Gamma0EisensteinRows N)
    (z : UpperHalfPlane) :
    gamma0EisensteinPrimitiveTerm N s (gamma0EisensteinPrimitiveEquiv N v) z =
      gamma0EisensteinSummand N s v z := by
  rw [gamma0EisensteinSummand,gamma0EisensteinHeight_row]
  rfl

theorem gamma0EisensteinPrimitiveTerm_summable (N : ℕ) (s : ℂ) (hs : 1<s.re)
    (z : UpperHalfPlane) : Summable (fun v => gamma0EisensteinPrimitiveTerm N s v z) := by
  apply (gamma0EisensteinPrimitiveEquiv N).summable_iff.mp
  change Summable (fun v : Gamma0EisensteinRows N =>
    gamma0EisensteinPrimitiveTerm N s (gamma0EisensteinPrimitiveEquiv N v) z)
  simpa only [gamma0EisensteinPrimitiveTerm_eq] using gamma0EisensteinSummand_summable N s hs z

theorem gamma0EisensteinPrimitiveTerm_neg (N : ℕ) (s : ℂ)
    (v : Gamma0EisensteinPrimitiveRows N) (z : UpperHalfPlane) :
    gamma0EisensteinPrimitiveTerm N s (gamma0EisensteinNegPrimitiveRow N v) z =
      gamma0EisensteinPrimitiveTerm N s v z := by
  unfold gamma0EisensteinPrimitiveTerm gamma0EisensteinNegPrimitiveRow
  simp only [Pi.neg_apply,Int.cast_neg,neg_mul,← neg_add,norm_neg]

theorem gamma0EisensteinPrimitiveTerm_zero (N : ℕ) (s : ℂ) (b : Bool) (z : UpperHalfPlane) :
    gamma0EisensteinPrimitiveTerm N s (gamma0EisensteinZeroPrimitiveRow N b) z = (z.im:ℂ)^s := by
  cases b <;> simp [gamma0EisensteinPrimitiveTerm,gamma0EisensteinZeroPrimitiveRow]

theorem gamma0Eisenstein_positive_row_formula (N : ℕ) (s : ℂ) (hs : 1<s.re)
    (z : UpperHalfPlane) :
    gamma0Eisenstein N s z = (z.im:ℂ)^s+
      ∑' v : Gamma0EisensteinPositiveRows N, gamma0EisensteinPrimitiveTerm N s v.val z := by
  rw [gamma0Eisenstein_primitive_row_formula]
  change (1/2:ℂ)*(∑' v, gamma0EisensteinPrimitiveTerm N s v z)=_
  rw [gamma0Eisenstein_signed_tsum N _ (gamma0EisensteinPrimitiveTerm_summable N s hs z)
    (fun v => gamma0EisensteinPrimitiveTerm_neg N s v z)]
  rw [gamma0EisensteinPrimitiveTerm_zero,gamma0EisensteinPrimitiveTerm_zero]
  ring

end ArtinMatthews
