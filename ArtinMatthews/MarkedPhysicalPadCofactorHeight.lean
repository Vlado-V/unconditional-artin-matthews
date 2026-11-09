module

public import ArtinMatthews.MarkedPhysicalPadSourceSupport


set_option backward.privateInPublic true
@[expose] public section

/-! One actual integer height contains both scalar cofactor products
with the required lower and upper source scales. -/
namespace ArtinMatthews
noncomputable section

theorem markedPhysicalPadCofactor_height {x δ K Hm Hn : ℝ}
    (hx : 1 ≤ x) (hδ : 0 ≤ δ) (hm : x^δ ≤ Hm) (hn : x^δ ≤ Hn) (hX : Hm*Hn ≤ K*x)
    (S T : Finset ℕ)
    (hS : ∀ m∈S,Hm ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*Hm)
    (hT : ∀ n∈T,Hn ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*Hn) :
    let Z := ⌊4*(Hm*Hn)⌋₊
    x^δ ≤ (Z:ℝ) ∧ (Z:ℝ) ≤ 4*K*x ∧ (Z:ℝ) ≤ 4*(Hm*Hn) ∧
      ∀ v ∈ S.product T,v.1*v.2 ∈ Finset.Icc 1 Z := by
  let Z := ⌊4*(Hm*Hn)⌋₊
  have hxδ : 1 ≤ x^δ := Real.one_le_rpow hx hδ
  have hm1 := hxδ.trans hm
  have hn1 := hxδ.trans hn
  have hmp := zero_lt_one.trans_le hm1
  have hnp := zero_lt_one.trans_le hn1
  have hmX := le_mul_of_one_le_right hmp.le hn1
  have hXl : x^δ ≤ Hm*Hn := hm.trans hmX
  have hX1 := hxδ.trans hXl
  have h4 : 0 ≤ 4*(Hm*Hn) := by positivity
  have hfloor := Nat.floor_le h4
  have hfloor' := Nat.lt_floor_add_one (4*(Hm*Hn))
  refine ⟨by linarith, hfloor.trans (by linarith), hfloor, ?_⟩
  intro v hv
  obtain ⟨hvm,hvn⟩ := Finset.mem_product.mp hv
  have hm1' : 1 ≤ (v.1:ℝ) := hm1.trans (hS v.1 hvm).1
  have hn1' : 1 ≤ (v.2:ℝ) := hn1.trans (hT v.2 hvn).1
  apply Finset.mem_Icc.mpr
  constructor
  · have h₁ : (1:ℕ) ≤ v.1 := by exact_mod_cast hm1'
    have h₂ : (1:ℕ) ≤ v.2 := by exact_mod_cast hn1'
    simpa only [one_mul] using Nat.mul_le_mul h₁ h₂
  · apply (Nat.le_floor_iff h4).mpr
    rw [Nat.cast_mul]
    calc
      _ ≤ (2*Hm)*(2*Hn) :=
        mul_le_mul (hS v.1 hvm).2 (hT v.2 hvn).2 (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring

end
end ArtinMatthews
