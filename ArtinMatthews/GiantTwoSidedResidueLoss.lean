module

public import ArtinMatthews.GiantTwoSidedPatternPathDamping
public import ArtinMatthews.MarkedPhysicalPrimeLossMean


set_option backward.privateInPublic true
@[expose] public section

/-! Repeated path offsets are grouped in the actual residue ring.
The resulting loss is between zero and one, with total residue mass
bounded by the sum of the original visit losses. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantTwoSidedResidueLoss {ι : Type*} (I : Finset ι) (r : ι → ℝ) (offset : ι → ℤ)
    (p : ℕ) (a : ZMod p) : ℝ :=
  markedFiniteLineLoss I r (fun v => -(offset v:ZMod p)) a

def giantTwoSidedResidueLossNat {ι : Type*} (I : Finset ι) (r : ι → ℝ) (offset : ι → ℤ)
    (p a : ℕ) : ℝ := giantTwoSidedResidueLoss I r offset p (a:ZMod p)

theorem giantTwoSidedResidueLoss_bounds {ι : Type*} (I : Finset ι) (r : ι → ℝ)
    (hr : ∀ v∈I,0≤r v ∧ r v≤1) (offset : ι → ℤ) (p : ℕ) (a : ZMod p) :
    0≤giantTwoSidedResidueLoss I r offset p a ∧ giantTwoSidedResidueLoss I r offset p a≤1 :=
  markedFiniteLineLoss_mem_unitInterval I r hr _ a

def giantTwoSidedResidueRepresentative (p : ℕ) [NeZero p] : ↥(range p) ≃ ZMod p where
  toFun a := (a.val:ZMod p)
  invFun a := ⟨a.val,mem_range.mpr (ZMod.val_lt a)⟩
  left_inv a := by
    apply Subtype.ext
    change (a.val:ZMod p).val=a.val
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt (mem_range.mp a.property)]
  right_inv a := ZMod.natCast_zmod_val a

theorem giantTwoSidedResidueLoss_mass {ι : Type*} (I : Finset ι) (r : ι → ℝ)
    (hr : ∀ v∈I,0≤r v ∧ r v≤1) (offset : ι → ℤ) (p : ℕ) [NeZero p] :
    (∑ a∈range p,giantTwoSidedResidueLossNat I r offset p a) ≤ ∑ v∈I,(1-r v) := by
  have hs : (∑ a∈range p,giantTwoSidedResidueLossNat I r offset p a) =
      ∑ a : ZMod p,giantTwoSidedResidueLoss I r offset p a := by
    rw [← Finset.sum_coe_sort]
    exact (giantTwoSidedResidueRepresentative p).sum_comp (giantTwoSidedResidueLoss I r offset p)
  rw [hs]
  calc
    _ ≤ ∑ a : ZMod p,∑ v∈I,(1-r v)*(if -(offset v:ZMod p)=a then (1:ℝ) else 0) :=
      sum_le_sum fun a _ => markedFiniteLineLoss_le_hits I r hr _ a
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro v _
      simp only [mul_ite,mul_one,mul_zero,sum_ite_eq,mem_univ,ite_true]

theorem giantTwoSidedResidueLoss_mass_le_visits {ι : Type*} (I : Finset ι) (r : ι → ℝ)
    (hr : ∀ v∈I,0≤r v ∧ r v≤1) (offset : ι → ℤ) (p : ℕ) [NeZero p] :
    (∑ a∈range p,giantTwoSidedResidueLossNat I r offset p a) ≤ I.card :=
  (giantTwoSidedResidueLoss_mass I r hr offset p).trans (by
    simpa only [sum_const,nsmul_eq_mul,mul_one] using
      sum_le_sum (s:=I) (f:=fun v => 1-r v) (g:=fun _ => (1:ℝ)) (fun v hv => sub_le_self _ (hr v hv).1))

theorem giantTwoSidedResidueLossNat_periodic {ι : Type*} (I : Finset ι) (r : ι → ℝ)
    (offset : ι → ℤ) (p n : ℕ) :
    giantTwoSidedResidueLossNat I r offset p (n%p)=giantTwoSidedResidueLossNat I r offset p n := by
  unfold giantTwoSidedResidueLossNat
  rw [ZMod.natCast_mod]

theorem giantTwoSidedResidueLossNat_eq_offset_product {ι : Type*} (I : Finset ι)
    (r : ι → ℝ) (offset : ι → ℤ) (p n : ℕ) :
    1-giantTwoSidedResidueLossNat I r offset p (n%p) =
      ∏ v∈I,if (p:ℤ)∣(n:ℤ)+offset v then r v else 1 := by
  rw [giantTwoSidedResidueLossNat_periodic]
  unfold giantTwoSidedResidueLossNat giantTwoSidedResidueLoss markedFiniteLineLoss
  rw [sub_sub_cancel]
  apply prod_congr rfl
  intro v _
  have hh : (-(offset v:ZMod p)=(n:ZMod p)) ↔ (p:ℤ)∣(n:ℤ)+offset v := by
    constructor
    · intro he
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      rw [← he,neg_add_cancel]
    · intro hd
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
      push_cast at hz
      linear_combination -hz
  simp only [hh]

end
end ArtinMatthews
