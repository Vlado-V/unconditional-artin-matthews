module

public import ArtinMatthews.AtkinLehnerModuli
public import ArtinMatthews.KloostermanDoubleCoset
public import ArtinMatthews.KloostermanWeakBound


set_option backward.privateInPublic true
@[expose] public section

/-! Finite residue representatives from actual same-cusp conjugated matrices. -/
namespace ArtinMatthews

open Matrix CongruenceSubgroup
open scoped BigOperators

/-- The residue pairs which actually occur in integral determinant-one matrices
of the prescribed level and lower-left entry. -/
noncomputable def gamma0ResiduePairs (N c : ℕ) [NeZero c] : Finset (ZMod c × ZMod c) := by
  classical
  exact Finset.univ.filter fun ad => ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
    γ ∈ Gamma0 N ∧ γ 1 0 = (c : ℤ) ∧ (γ 0 0 : ZMod c) = ad.1 ∧ (γ 1 1 : ZMod c) = ad.2

/-- The finite pairs are derived from actual integer completions, including
the direction from an arbitrary invertible residue to an actual matrix. -/
theorem mem_gamma0ResiduePairs_iff {N c : ℕ} [NeZero c] (hNc : N ∣ c)
    (ad : ZMod c × ZMod c) : ad ∈ gamma0ResiduePairs N c ↔ ad.1*ad.2 = 1 := by
  classical
  simp only [gamma0ResiduePairs,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨γ,_hγ,hc,ha,hd⟩
    have hh := γ.prop
    rw [Matrix.det_fin_two] at hh
    have hz := congrArg (fun z : ℤ => (z : ZMod c)) hh
    simp only [Int.cast_sub,Int.cast_mul,Int.cast_one] at hz
    rw [hc] at hz
    simpa only [Int.cast_natCast,ZMod.natCast_self,mul_zero,sub_zero,ha,hd] using hz
  · intro had
    let A : ℤ := ad.1.val
    let D : ℤ := ad.2.val
    have hA : (A : ZMod c) = ad.1 := by simp [A]
    have hD : (D : ZMod c) = ad.2 := by simp [D]
    have hdiv : (c : ℤ) ∣ A*D-1 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      rw [hA,hD,had]
      simp
    obtain ⟨B,hB⟩ := hdiv
    let γ : Matrix.SpecialLinearGroup (Fin 2) ℤ := ⟨!![A,B;(c : ℤ),D],by
      rw [Matrix.det_fin_two]
      simp only [Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      linear_combination hB⟩
    have hγ : γ ∈ Gamma0 N := by
      rw [Gamma0_mem,ZMod.intCast_zmod_eq_zero_iff_dvd]
      change (N : ℤ) ∣ (c : ℤ)
      exact_mod_cast hNc
    exact ⟨γ,hγ,rfl,hA,hD⟩

/-- These finite residue pairs classify the genuine upper-unipotent double
cosets, so the finite pair model has exactly one term per actual double coset. -/
theorem gamma0_residuePair_eq_iff_double_coset {c : ℕ} [NeZero c]
    (γ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hγ : γ 1 0 = (c : ℤ)) (hδ : δ 1 0 = (c : ℤ)) :
    (((γ 0 0 : ZMod c),(γ 1 1 : ZMod c)) = ((δ 0 0 : ZMod c),(δ 1 1 : ZMod c))) ↔
      ∃ l k : ℤ, δ = integerTranslation l * γ * integerTranslation k := by
  rw [Prod.mk.injEq,ZMod.intCast_eq_intCast_iff,ZMod.intCast_eq_intCast_iff]
  exact integerTranslation_double_coset_iff (by exact_mod_cast NeZero.ne c) γ δ hγ hδ

/-- Actual conjugated-group matrices define the same-cusp finite residue set. -/
noncomputable def atkinSameCuspResiduePairs {r s : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (c : ℕ) [NeZero c] : Finset (ZMod c × ZMod c) := by
  classical
  exact Finset.univ.filter fun ad => ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
    γ ∈ Gamma0 (r*s) ∧ ∃ A D : ℤ,
      ((atkinScaling hr hab)⁻¹ * atkinRealMap γ * atkinScaling hr hab) 0 0 = (A : ℝ) ∧
      ((atkinScaling hr hab)⁻¹ * atkinRealMap γ * atkinScaling hr hab) 1 0 = (c : ℝ) ∧
      ((atkinScaling hr hab)⁻¹ * atkinRealMap γ * atkinScaling hr hab) 1 1 = (D : ℝ) ∧
      (A : ZMod c) = ad.1 ∧ (D : ZMod c) = ad.2

theorem atkinSameCuspResiduePairs_eq {r s : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (c : ℕ) [NeZero c] :
    atkinSameCuspResiduePairs hr hab c = gamma0ResiduePairs (r*s) c := by
  classical
  ext ad
  simp only [atkinSameCuspResiduePairs,gamma0ResiduePairs,Finset.mem_filter,
    Finset.mem_univ,true_and]
  constructor
  · rintro ⟨γ,hγ,A,D,hA,hc,hD,ha,hd⟩
    obtain ⟨δ,hδ,hconj⟩ := atkinScaling_normalizes_forward hr hab γ hγ
    rw [hconj] at hA hc hD
    change (δ 0 0 : ℝ) = (A : ℝ) at hA
    change (δ 1 0 : ℝ) = (c : ℝ) at hc
    change (δ 1 1 : ℝ) = (D : ℝ) at hD
    have hAi : δ 0 0 = A := by exact_mod_cast hA
    have hci : δ 1 0 = (c : ℤ) := by exact_mod_cast hc
    have hDi : δ 1 1 = D := by exact_mod_cast hD
    exact ⟨δ,hδ,hci,by rwa [hAi],by rwa [hDi]⟩
  · rintro ⟨δ,hδ,hc,ha,hd⟩
    obtain ⟨γ,hγ,hback⟩ := atkinScaling_normalizes_backward hr hab δ hδ
    have hconj : (atkinScaling hr hab)⁻¹ * atkinRealMap γ * atkinScaling hr hab =
        atkinRealMap δ := by rw [← hback]; group
    refine ⟨γ,hγ,δ 0 0,δ 1 1,?_,?_,?_,ha,hd⟩
    · rw [hconj]; rfl
    · rw [hconj]; change (δ 1 0 : ℝ) = (c : ℝ); exact_mod_cast hc
    · rw [hconj]; rfl

/-- This finite phase sum uses actual same-cusp matrix residue representatives. -/
noncomputable def atkinSameCuspResidueSum {r s : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (c : ℕ) [NeZero c] (m n : ZMod c) : ℂ :=
  ∑ ad ∈ atkinSameCuspResiduePairs hr hab c, ZMod.stdAddChar (m*ad.1+n*ad.2)

set_option backward.isDefEq.respectTransparency false in
/-- The exact ordinary-kernel reduction follows from actual integral matrix
completion and unit parametrization, rather than an assumed cusp formula. -/
theorem atkinSameCuspResidueSum_eq_ordinary {r s : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (c : ℕ) [NeZero c]
    (hNc : r*s ∣ c) (m n : ZMod c) :
    atkinSameCuspResidueSum hr hab c m n =
      OAI.Erdos970.ErdosKloosterman.sum ZMod.stdAddChar m n := by
  classical
  unfold atkinSameCuspResidueSum
  rw [atkinSameCuspResiduePairs_eq]
  unfold OAI.Erdos970.ErdosKloosterman.sum
  symm
  apply Finset.sum_bij (fun (u : (ZMod c)ˣ) _hu => ((u : ZMod c),(↑u⁻¹ : ZMod c)))
  · intro u _hu
    exact (mem_gamma0ResiduePairs_iff hNc _).mpr u.val_inv
  · intro u _hu v _hv huv
    exact Units.ext (congrArg Prod.fst huv)
  · intro ad had
    have hp := (mem_gamma0ResiduePairs_iff hNc ad).mp had
    exact ⟨⟨ad.1,ad.2,hp,by simpa only [mul_comm] using hp⟩,by simp,rfl⟩
  · intro u _hu
    rfl

/-- The existing proved weak bound transfers to the actual same-cusp finite
sum. This is deliberately the `3/4+ε` bound, not the missing Weil bound. -/
theorem atkinSameCuspResidueSum_weak_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r s : ℕ) (hr : 0 < r) (a b : ℤ)
      (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (c : ℕ) [NeZero c], r*s ∣ c →
      ∀ h k : ℤ, ‖atkinSameCuspResidueSum hr hab c (h : ZMod c) (k : ZMod c)‖ ≤
        C*(c : ℝ)^((3/4 : ℝ)+ε)*(Nat.gcd c (Int.gcd h k) : ℝ)^(1/4 : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := standardKloosterman_weak_bound hε
  refine ⟨C,hC,?_⟩
  intro r s hr a b hab c _hc hNc h k
  rw [atkinSameCuspResidueSum_eq_ordinary hr hab c hNc]
  exact hbound c h k

end ArtinMatthews
