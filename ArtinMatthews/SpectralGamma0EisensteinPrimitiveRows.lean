module

public import ArtinMatthews.SpectralGamma0EisensteinSeries


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Γ₀(N) row index is exactly the primitive congruence-row index. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0Eisenstein_row_mem_iff (N : ℕ) (v : Fin 2 → ℤ) :
    v ∈ Set.range (gamma0EisensteinRow N) ↔
      IsCoprime (v 0) (v 1) ∧ (v 0 : ZMod N) = 0 := by
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨Matrix.SpecialLinearGroup.isCoprime_row (g : SL(2,ℤ)) 1,
      CongruenceSubgroup.Gamma0_mem.mp g.property⟩
  · rintro ⟨hc,hm⟩
    obtain ⟨g,hg0,hg1⟩ := hc.exists_SL2_row 1
    have hg : g ∈ CongruenceSubgroup.Gamma0 N := by
      rw [CongruenceSubgroup.Gamma0_mem,hg0]
      exact hm
    refine ⟨⟨g,hg⟩,?_⟩
    funext i
    fin_cases i
    · exact hg0
    · exact hg1

abbrev Gamma0EisensteinPrimitiveRows (N : ℕ) :=
  {v : Fin 2 → ℤ // IsCoprime (v 0) (v 1) ∧ (v 0 : ZMod N) = 0}

def gamma0EisensteinPrimitiveEquiv (N : ℕ) :
    Gamma0EisensteinRows N ≃ Gamma0EisensteinPrimitiveRows N where
  toFun v := ⟨v.val,(gamma0Eisenstein_row_mem_iff N v.val).mp v.property⟩
  invFun v := ⟨v.val,(gamma0Eisenstein_row_mem_iff N v.val).mpr v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem gamma0Eisenstein_primitive_row_formula (N : ℕ) (s : ℂ) (z : UpperHalfPlane) :
    gamma0Eisenstein N s z = (1/2 : ℂ)*
      ∑' v : Gamma0EisensteinPrimitiveRows N,
        ((z.im / ‖(v.val 0 : ℂ)*z+v.val 1‖^2 : ℝ) : ℂ)^s := by
  unfold gamma0Eisenstein
  congr 1
  calc
    _ = ∑' v : Gamma0EisensteinRows N,
        ((z.im / ‖(v.val 0 : ℂ)*z+v.val 1‖^2 : ℝ) : ℂ)^s := by
      apply tsum_congr
      intro v
      rw [gamma0EisensteinSummand,gamma0EisensteinHeight_row]
    _ = _ := (gamma0EisensteinPrimitiveEquiv N).tsum_eq
      (fun v : Gamma0EisensteinPrimitiveRows N =>
        ((z.im / ‖(v.val 0 : ℂ)*z+v.val 1‖^2 : ℝ) : ℂ)^s)

end ArtinMatthews
