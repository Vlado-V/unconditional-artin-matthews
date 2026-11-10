module

public import ArtinMatthews.SpectralCuspDoubleCosetPeriod
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-! Canonical finite representatives for common-period N double cosets.
Both diagonal entries lie in [0,N*c), with c positive. -/

noncomputable section
open Matrix
open scoped MatrixGroups

namespace ArtinMatthews

def gamma0CuspMatrixFibre (N : ℕ) (r s : SL(2, ℤ)) (c : ℕ) :=
  {M : SL(2, ℤ) // M ∈ gamma0CuspCorrespondence N r s ∧ M 1 0 = (c : ℤ)}

def gamma0CuspReducedMatrix (N : ℕ) (r s : SL(2, ℤ)) (c : ℕ) :=
  {M : SL(2, ℤ) // M ∈ gamma0CuspCorrespondence N r s ∧ M 1 0 = (c : ℤ) ∧
    0 ≤ M 0 0 ∧ M 0 0 < (N : ℤ) * c ∧ 0 ≤ M 1 1 ∧ M 1 1 < (N : ℤ) * c}

theorem specialLinear_eq_of_diagonal_lower {c : ℤ} (hc : c ≠ 0)
    (M R : SL(2, ℤ)) (hM : M 1 0 = c) (hR : R 1 0 = c)
    (hA : M 0 0 = R 0 0) (hD : M 1 1 = R 1 1) : M = R := by
  have hB : M 0 1 = R 0 1 := by
    have hm := M.prop
    have hr := R.prop
    rw [Matrix.det_fin_two,hM,hA,hD] at hm
    rw [Matrix.det_fin_two,hR] at hr
    apply mul_right_cancel₀ hc
    nlinarith
  ext i j
  fin_cases i <;> fin_cases j
  · exact hA
  · exact hB
  · exact hM.trans hR.symm
  · exact hD

def gamma0CuspDoubleCosetExpand (N : ℕ) (r s : SL(2, ℤ)) (c : ℕ)
    (p : gamma0CuspReducedMatrix N r s c × ℤ × ℤ) : gamma0CuspMatrixFibre N r s c :=
  ⟨integerTranslation ((N : ℤ) * p.2.1) * p.1.val * integerTranslation ((N : ℤ) * p.2.2),
    gamma0CuspCorrespondence_period_translate N r s p.1.val p.1.property.1 p.2.1 p.2.2,
    (integerTranslation_entries ((N : ℤ) * p.2.1) ((N : ℤ) * p.2.2) p.1.val).2.1.trans
      p.1.property.2.1⟩

theorem gamma0CuspReducedMatrix_diagonal_injective (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] :
    Function.Injective (fun R : gamma0CuspReducedMatrix N r s c =>
      ((R.val 0 0 : ZMod (N * c)), (R.val 1 1 : ZMod (N * c)))) := by
  intro M R h
  have hA := (ZMod.intCast_eq_intCast_iff _ _ _).mp (congrArg Prod.fst h)
  have hD := (ZMod.intCast_eq_intCast_iff _ _ _).mp (congrArg Prod.snd h)
  have hA' : M.val 0 0 = R.val 0 0 := by
    change M.val 0 0 % ((N * c : ℕ) : ℤ) = R.val 0 0 % ((N * c : ℕ) : ℤ) at hA
    push_cast at hA
    simpa only [Int.emod_eq_of_lt M.property.2.2.1 M.property.2.2.2.1,
      Int.emod_eq_of_lt R.property.2.2.1 R.property.2.2.2.1] using hA
  have hD' : M.val 1 1 = R.val 1 1 := by
    change M.val 1 1 % ((N * c : ℕ) : ℤ) = R.val 1 1 % ((N * c : ℕ) : ℤ) at hD
    push_cast at hD
    simpa only [Int.emod_eq_of_lt M.property.2.2.2.2.1 M.property.2.2.2.2.2,
      Int.emod_eq_of_lt R.property.2.2.2.2.1 R.property.2.2.2.2.2] using hD
  apply Subtype.ext
  exact specialLinear_eq_of_diagonal_lower (by exact_mod_cast NeZero.ne c)
    M.val R.val M.property.2.1 R.property.2.1 hA' hD'

instance gamma0CuspReducedMatrix_finite (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] : Finite (gamma0CuspReducedMatrix N r s c) :=
  Finite.of_injective _ (gamma0CuspReducedMatrix_diagonal_injective N r s c)

instance gamma0CuspReducedMatrix_fintype (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] : Fintype (gamma0CuspReducedMatrix N r s c) :=
  Fintype.ofFinite _

theorem gamma0CuspDoubleCosetExpand_surjective (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] :
    Function.Surjective (gamma0CuspDoubleCosetExpand N r s c) := by
  intro M
  let L : ℤ := (N : ℤ) * c
  have hL : 0 < L := mul_pos (by exact_mod_cast NeZero.pos N) (by exact_mod_cast NeZero.pos c)
  let l : ℤ := -(M.val 0 0 / L)
  let k : ℤ := -(M.val 1 1 / L)
  let R := integerTranslation ((N : ℤ) * l) * M.val * integerTranslation ((N : ℤ) * k)
  obtain ⟨hRA,hRC,hRD⟩ := integerTranslation_entries ((N : ℤ) * l) ((N : ℤ) * k) M.val
  have hA : R 0 0 = M.val 0 0 % L := by
    rw [hRA,M.property.2]
    have he := Int.emod_add_ediv_mul (M.val 0 0) L
    dsimp [l,L] at *
    nlinarith
  have hD : R 1 1 = M.val 1 1 % L := by
    rw [hRD,M.property.2]
    have he := Int.emod_add_ediv_mul (M.val 1 1) L
    dsimp [k,L] at *
    nlinarith
  let R₀ : gamma0CuspReducedMatrix N r s c := ⟨R,
    gamma0CuspCorrespondence_period_translate N r s M.val M.property.1 l k,
    hRC.trans M.property.2,
    (by rw [hA]; exact Int.emod_nonneg _ hL.ne'), (by rw [hA]; exact Int.emod_lt_of_pos _ hL),
    (by rw [hD]; exact Int.emod_nonneg _ hL.ne'), (by rw [hD]; exact Int.emod_lt_of_pos _ hL)⟩
  have hAM : Int.ModEq L (R₀.val 0 0) (M.val 0 0) := by
    change R 0 0 % L = M.val 0 0 % L
    rw [hA,Int.emod_emod]
  have hDM : Int.ModEq L (R₀.val 1 1) (M.val 1 1) := by
    change R 1 1 % L = M.val 1 1 % L
    rw [hD,Int.emod_emod]
  obtain ⟨a,b,hab⟩ := (integerTranslation_period_double_coset_iff N
    (by exact_mod_cast NeZero.ne c) R₀.val M.val R₀.property.2.1 M.property.2).mp ⟨hAM,hDM⟩
  refine ⟨(R₀,a,b),?_⟩
  apply Subtype.ext
  exact hab.symm

theorem gamma0CuspDoubleCosetExpand_injective (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] :
    Function.Injective (gamma0CuspDoubleCosetExpand N r s c) := by
  rintro ⟨R,l,k⟩ ⟨S,a,b⟩ h
  have hA := congrArg (fun M : gamma0CuspMatrixFibre N r s c => M.val 0 0) h
  have hD := congrArg (fun M : gamma0CuspMatrixFibre N r s c => M.val 1 1) h
  change (integerTranslation ((N : ℤ) * l) * R.val * integerTranslation ((N : ℤ) * k)) 0 0 =
    (integerTranslation ((N : ℤ) * a) * S.val * integerTranslation ((N : ℤ) * b)) 0 0 at hA
  change (integerTranslation ((N : ℤ) * l) * R.val * integerTranslation ((N : ℤ) * k)) 1 1 =
    (integerTranslation ((N : ℤ) * a) * S.val * integerTranslation ((N : ℤ) * b)) 1 1 at hD
  rw [(integerTranslation_entries _ _ _).1,(integerTranslation_entries _ _ _).1,
    R.property.2.1,S.property.2.1] at hA
  rw [(integerTranslation_entries _ _ _).2.2,(integerTranslation_entries _ _ _).2.2,
    R.property.2.1,S.property.2.1] at hD
  have hAR : Int.ModEq ((N : ℤ) * c) (R.val 0 0) (S.val 0 0) := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨l-a,by nlinarith [hA]⟩
  have hDR : Int.ModEq ((N : ℤ) * c) (R.val 1 1) (S.val 1 1) := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨k-b,by nlinarith [hD]⟩
  have hRS : R = S := by
    apply gamma0CuspReducedMatrix_diagonal_injective N r s c
    apply Prod.ext
    · apply (ZMod.intCast_eq_intCast_iff _ _ _).mpr
      simpa only [Nat.cast_mul] using hAR
    · apply (ZMod.intCast_eq_intCast_iff _ _ _).mpr
      simpa only [Nat.cast_mul] using hDR
  cases hRS
  have hNc : (N : ℤ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast NeZero.ne N) (by exact_mod_cast NeZero.ne c)
  have hl : l = a := by apply mul_left_cancel₀ hNc; nlinarith [hA]
  have hk : k = b := by apply mul_left_cancel₀ hNc; nlinarith [hD]
  exact Prod.ext rfl (Prod.ext hl hk)

def gamma0CuspDoubleCosetEquiv (N : ℕ) [NeZero N] (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] :
    (gamma0CuspReducedMatrix N r s c × ℤ × ℤ) ≃ gamma0CuspMatrixFibre N r s c :=
  Equiv.ofBijective _ ⟨gamma0CuspDoubleCosetExpand_injective N r s c,
    gamma0CuspDoubleCosetExpand_surjective N r s c⟩

theorem gamma0CuspDoubleCoset_finsum (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (c : ℕ) [NeZero c] (F : gamma0CuspMatrixFibre N r s c → ℂ) :
    (∑ᶠ p : gamma0CuspReducedMatrix N r s c × ℤ × ℤ, F (gamma0CuspDoubleCosetExpand N r s c p)) =
      ∑ᶠ M : gamma0CuspMatrixFibre N r s c, F M :=
  finsum_comp_equiv (f := F) (gamma0CuspDoubleCosetEquiv N r s c)

end ArtinMatthews
