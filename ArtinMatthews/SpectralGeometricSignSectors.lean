module

public import ArtinMatthews.SpectralPositiveOrbitalKloosterman


set_option backward.privateInPublic true
@[expose] public section

/-! The zero-modulus sector remains literal.  Negative moduli are paired
with positive ones by the actual central sign, adding a second factor two. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups InnerProductSpace

namespace ArtinMatthews

theorem gamma0CuspCorrespondence_neg_iff (N : ℕ) (r s M : SL(2, ℤ)) :
    -M ∈ gamma0CuspCorrespondence N r s ↔ M ∈ gamma0CuspCorrespondence N r s := by
  simp only [gamma0CuspCorrespondence,Set.mem_ofPred_eq,mul_neg,neg_mul,
    CongruenceSubgroup.Gamma0_mem,Matrix.SpecialLinearGroup.coe_neg,Matrix.neg_apply,
    Int.cast_neg,neg_eq_zero]

def gamma0CuspCorrespondenceNeg (N : ℕ) (r s : SL(2, ℤ)) :
    gamma0CuspCorrespondence N r s ≃ gamma0CuspCorrespondence N r s where
  toFun M := ⟨-M.val,(gamma0CuspCorrespondence_neg_iff N r s M.val).mpr M.property⟩
  invFun M := ⟨-M.val,(gamma0CuspCorrespondence_neg_iff N r s M.val).mpr M.property⟩
  left_inv M := by apply Subtype.ext; exact neg_neg M.val
  right_inv M := by apply Subtype.ext; exact neg_neg M.val

theorem finiteSupport_indicator {ι : Type*} (p : ι → Prop) [DecidablePred p] (F : ι → ℂ)
    (hF : Function.HasFiniteSupport F) :
    Function.HasFiniteSupport (fun i => if p i then F i else 0) := by
  classical
  apply hF.subset
  intro i hi hzero
  by_cases hp : p i <;> simp [hp,hzero] at hi

theorem gamma0GeometricSum_sign_split (N : ℕ) (r s : SL(2, ℤ))
    (F : gamma0CuspCorrespondence N r s → ℂ) (hF : Function.HasFiniteSupport F)
    (hneg : ∀ M, F (gamma0CuspCorrespondenceNeg N r s M) = F M) :
    (∑ᶠ M, F M) =
      (∑ᶠ M, if M.val 1 0 = 0 then F M else 0) +
      2 * ∑ᶠ M, if 0 < M.val 1 0 then F M else 0 := by
  classical
  let F0 := fun M : gamma0CuspCorrespondence N r s => if M.val 1 0 = 0 then F M else 0
  let Fp := fun M : gamma0CuspCorrespondence N r s => if 0 < M.val 1 0 then F M else 0
  let Fn := fun M : gamma0CuspCorrespondence N r s => if M.val 1 0 < 0 then F M else 0
  have h0 := finiteSupport_indicator (fun M : gamma0CuspCorrespondence N r s => M.val 1 0 = 0) F hF
  have hp := finiteSupport_indicator (fun M : gamma0CuspCorrespondence N r s => 0 < M.val 1 0) F hF
  have hn := finiteSupport_indicator (fun M : gamma0CuspCorrespondence N r s => M.val 1 0 < 0) F hF
  have he (M : gamma0CuspCorrespondence N r s) : F M = F0 M + Fp M + Fn M := by
    rcases lt_trichotomy (M.val 1 0) 0 with h | h | h
    · simp [F0,Fp,Fn,h,h.ne,not_lt_of_ge h.le]
    · simp [F0,Fp,Fn,h]
    · simp [F0,Fp,Fn,h,Ne.symm h.ne,not_lt_of_ge h.le]
  have hs : (∑ᶠ M, Fn M) = ∑ᶠ M, Fp M := by
    have ht : ∀ M, Fp (gamma0CuspCorrespondenceNeg N r s M) = Fn M := by
      intro M
      have hlow : (gamma0CuspCorrespondenceNeg N r s M).val 1 0 = -M.val 1 0 := rfl
      change (if 0 < (gamma0CuspCorrespondenceNeg N r s M).val 1 0 then
        F (gamma0CuspCorrespondenceNeg N r s M) else 0) = (if M.val 1 0 < 0 then F M else 0)
      simp only [hlow,neg_pos,hneg]
    exact (finsum_congr ht).symm.trans (finsum_comp_equiv (f := Fp) (gamma0CuspCorrespondenceNeg N r s))
  calc
    _ = ∑ᶠ M, (F0 M + Fp M + Fn M) := finsum_congr he
    _ = (∑ᶠ M, F0 M) + (∑ᶠ M, Fp M) + (∑ᶠ M, Fn M) := by
      have ha := finsum_add_distrib (f := F0 + Fp) (g := Fn) (h0.add hp) hn
      have hb := finsum_add_distrib (f := F0) (g := Fp) h0 hp
      simp only [Pi.add_apply] at ha hb
      rw [ha,hb]
    _ = _ := by rw [hs]; ring

def gamma0ZeroGeometricSum (N : ℕ) (r s : SL(2, ℤ)) (ψ φ : h2SmoothCompactSeeds) : ℂ :=
  ∑ᶠ M : gamma0CuspCorrespondence N r s,
    if M.val 1 0 = 0 then compactPoincareGeometricKernel ψ φ M.val else 0

def gamma0PositiveGeometricSum (N : ℕ) (r s : SL(2, ℤ)) (ψ φ : h2SmoothCompactSeeds) : ℂ :=
  ∑ᶠ M : gamma0CuspCorrespondence N r s,
    if 0 < M.val 1 0 then compactPoincareGeometricKernel ψ φ M.val else 0

theorem gamma0SmoothSeedMass_pairing_sign_sectors (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (ψ φ : h2SmoothCompactSeeds) :
    inner ℂ (gamma0SmoothSeedMass N (modularTranslateSmoothSeed r ψ))
      (gamma0SmoothSeedMass N (modularTranslateSmoothSeed s φ)) =
      2 * gamma0ZeroGeometricSum N r s ψ φ + 4 * gamma0PositiveGeometricSum N r s ψ φ := by
  rw [gamma0SmoothSeedMass_pairing_geometric]
  have hf : Function.HasFiniteSupport (fun M : gamma0CuspCorrespondence N r s =>
      compactPoincareGeometricKernel ψ φ M.val) :=
    Function.HasFiniteSupport.fun_comp_of_injective (g := Subtype.val) Subtype.val_injective
      (compactPoincareGeometricKernel_all_hasFiniteSupport ψ φ)
  rw [gamma0GeometricSum_sign_split N r s _ hf (fun M => compactPoincareGeometricKernel_neg ψ φ M.val)]
  change 2 * (gamma0ZeroGeometricSum N r s ψ φ + 2 * gamma0PositiveGeometricSum N r s ψ φ) = _
  ring

end ArtinMatthews
