module

public import Mathlib.NumberTheory.Modular


set_option backward.privateInPublic true
@[expose] public section

/-! A modular matrix is determined by its bottom row and the integer part
of the real coordinate of its action on any fixed upper-half-plane point. -/
noncomputable section
open Set UpperHalfPlane
open scoped MatrixGroups
namespace ArtinMatthews

theorem spectralModular_eq_translation_of_bottom_row_eq (g h : SL(2,ℤ))
    (hc : h 1 0 = g 1 0) (hd : h 1 1 = g 1 1) :
    ∃ k : ℤ, h = ModularGroup.T^k*g := by
  let k := h 0 1*g 0 0-h 0 0*g 0 1
  have hg : g 0 0*g 1 1-g 0 1*g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.det_coe
  have hh : h 0 0*g 1 1-h 0 1*g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two,hc,hd] using h.det_coe
  have ha : h 0 0 = g 0 0+k*g 1 0 := by
    dsimp only [k]
    linear_combination (g 0 0)*hh-(h 0 0)*hg
  have hb : h 0 1 = g 0 1+k*g 1 1 := by
    dsimp only [k]
    linear_combination (g 0 1)*hh-(h 0 1)*hg
  refine ⟨k,?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,ModularGroup.coe_T_zpow,ha,hb,hc,hd]

def spectralModularStripCode (z : UpperHalfPlane) (g : SL(2,ℤ)) : ℤ × ℤ × ℤ :=
  (g 1 0,g 1 1,⌊(g • z).re⌋)

theorem spectralModularStripCode_injective (z : UpperHalfPlane) :
    Function.Injective (spectralModularStripCode z) := by
  intro g h he
  have hc : h 1 0 = g 1 0 := (congrArg (fun p : ℤ×ℤ×ℤ => p.1) he).symm
  have hd : h 1 1 = g 1 1 := (congrArg (fun p : ℤ×ℤ×ℤ => p.2.1) he).symm
  have hf : ⌊(g • z).re⌋ = ⌊(h • z).re⌋ := congrArg (fun p : ℤ×ℤ×ℤ => p.2.2) he
  obtain ⟨k,hkg⟩ := spectralModular_eq_translation_of_bottom_row_eq g h hc hd
  have hk : k = 0 := by
    rw [hkg,mul_smul,ModularGroup.re_T_zpow_smul,Int.floor_add_intCast] at hf
    omega
  simpa [hk] using hkg.symm

end ArtinMatthews
