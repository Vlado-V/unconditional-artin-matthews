module

public import ArtinMatthews.SpectralSameCuspZeroTranslations
public import ArtinMatthews.SpectralCuspEisensteinSeries


set_option backward.privateInPublic true
@[expose] public section

/-! Two distinct actual source rows are antipodal or have a nonzero
determinant divisible by the same-cusp lower-entry modulus. -/

noncomputable section
open Matrix Set
open scoped MatrixGroups BigOperators

namespace ArtinMatthews

set_option backward.isDefEq.respectTransparency false in
theorem cuspEisensteinRows_det_antipodal_or_lower_bound (N D : ℕ) (a : SL(2, ℤ))
    (hD : ∀ M ∈ gamma0CuspCorrespondence N a a, (D : ℤ) ∣ M 1 0)
    (u v : Gamma0CuspEisensteinRows N 1 a) (hne : u ≠ v) :
    u.val = -v.val ∨ (D : ℤ) ≤ |u.val 0*v.val 1-u.val 1*v.val 0| := by
  let M := gamma0CuspEisensteinRowRepresentative N 1 a u
  let L := gamma0CuspEisensteinRowRepresentative N 1 a v
  let g := M.val*L.val⁻¹
  have hM : M.val 1 = u.val := gamma0CuspEisensteinRowRepresentative_spec N 1 a u
  have hL : L.val 1 = v.val := gamma0CuspEisensteinRowRepresentative_spec N 1 a v
  have hrel : g ∈ gamma0CuspCorrespondence N a a := by
    have hm : a⁻¹*M.val ∈ CongruenceSubgroup.Gamma0 N := by
      simpa only [gamma0CuspCorrespondence,mem_ofPred_eq,mul_one] using M.property
    have hl : a⁻¹*L.val ∈ CongruenceSubgroup.Gamma0 N := by
      simpa only [gamma0CuspCorrespondence,mem_ofPred_eq,mul_one] using L.property
    change a⁻¹*g*a ∈ CongruenceSubgroup.Gamma0 N
    rw [show a⁻¹*g*a = (a⁻¹*M.val)*(a⁻¹*L.val)⁻¹ by dsimp only [g]; group]
    exact (CongruenceSubgroup.Gamma0 N).mul_mem hm ((CongruenceSubgroup.Gamma0 N).inv_mem hl)
  have hdet : g 1 0 = u.val 0*v.val 1-u.val 1*v.val 0 := by
    change ((M.val : Matrix (Fin 2) (Fin 2) ℤ) *
      Matrix.adjugate (L.val : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 = _
    rw [Matrix.mul_apply,Fin.sum_univ_two,Matrix.adjugate_fin_two]
    change M.val 1 0*L.val 1 1+M.val 1 1*(-L.val 1 0) = _
    rw [congrFun hM 0,congrFun hM 1,congrFun hL 0,congrFun hL 1]
    ring
  by_cases hg : g 1 0 = 0
  · have heq (j : Fin 2) : u.val j = g 1 1*v.val j := by
      have hh : g*L.val = M.val := by dsimp only [g]; group
      have he := congrArg (fun X : SL(2, ℤ) => X 1 j) hh
      change (∑ i : Fin 2, g 1 i*L.val i j) = M.val 1 j at he
      rw [Fin.sum_univ_two,hg,zero_mul,zero_add,congrFun hM j,congrFun hL j] at he
      exact he.symm
    rcases spectral_SL2_lower_zero_eq_signed_translation g hg with ⟨hd,_⟩ | ⟨hd,_⟩
    · exact (hne (Subtype.ext (funext (fun j => by rw [heq j,hd,one_mul])))).elim
    · left
      funext j
      rw [heq j,hd,neg_one_mul,Pi.neg_apply]
  · right
    obtain ⟨l,hl⟩ := hD g hrel
    have hl0 : l ≠ 0 := by
      intro hz
      exact hg (by rw [hl,hz,mul_zero])
    rw [← hdet,hl,abs_mul,abs_of_nonneg (by positivity : (0 : ℤ) ≤ (D : ℤ))]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Int.one_le_abs hl0)
      (by positivity : (0 : ℤ) ≤ (D : ℤ))

theorem gamma0Infinity_sameCusp_lower_dvd (N : ℕ) (M : SL(2, ℤ))
    (hM : M ∈ gamma0CuspCorrespondence N 1 1) : (N : ℤ) ∣ M 1 0 := by
  have h : M ∈ CongruenceSubgroup.Gamma0 N := by
    simpa only [gamma0CuspCorrespondence,mem_ofPred_eq,inv_one,one_mul,mul_one] using hM
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp h)

set_option backward.isDefEq.respectTransparency false in
theorem gamma0MixedCusp_sameCusp_lower_dvd (r s : ℕ) (M : SL(2, ℤ))
    (hM : M ∈ gamma0CuspCorrespondence (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s)) :
    (s : ℤ) ∣ M 1 0 := by
  let a := gamma0CuspOneOver s
  have h : a⁻¹*M*a ∈ CongruenceSubgroup.Gamma0 (r*s) := hM
  have hd : ((r*s : ℕ) : ℤ) ∣ (a⁻¹*M*a : SL(2,ℤ)) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp h)
  have hdiv : (s : ℤ) ∣ (a⁻¹*M*a : SL(2,ℤ)) 1 0 :=
    (by rw [Nat.cast_mul]; exact dvd_mul_left _ _ : (s : ℤ) ∣ ((r*s : ℕ) : ℤ)).trans hd
  have he : (a⁻¹*M*a : SL(2,ℤ)) 1 0 =
      M 1 0+(s : ℤ)*(M 0 0-M 1 1-(s : ℤ)*M 0 1) := by
    change (Matrix.adjugate (a : Matrix (Fin 2) (Fin 2) ℤ) *
      (M : Matrix (Fin 2) (Fin 2) ℤ) * (a : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 = _
    rw [Matrix.adjugate_fin_two]
    simp only [Matrix.mul_apply,Fin.sum_univ_two]
    simp [a,gamma0CuspOneOver]
    ring
  rw [he] at hdiv
  have hsub := dvd_sub hdiv (dvd_mul_right (s : ℤ) (M 0 0-M 1 1-(s : ℤ)*M 0 1))
  simpa only [add_sub_cancel_right] using hsub

end ArtinMatthews
