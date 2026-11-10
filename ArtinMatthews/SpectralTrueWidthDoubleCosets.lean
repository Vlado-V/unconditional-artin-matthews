module

public import ArtinMatthews.SpectralCuspTrueWidth
public import ArtinMatthews.SpectralCuspDoubleCosetRepresentatives
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Canonical double-coset representatives for the actual least cusp periods.
The two diagonal residue moduli are w_s*c and w_r*c, respectively. -/

noncomputable section
open Matrix
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0CuspCorrespondence_trueWidth_translate (N : ℕ) [NeZero N]
    (r s M : SL(2, ℤ)) (hM : M ∈ gamma0CuspCorrespondence N r s) (l k : ℤ) :
    integerTranslation ((gamma0CuspTrueWidth N s : ℤ) * l) * M *
      integerTranslation ((gamma0CuspTrueWidth N r : ℤ) * k) ∈
        gamma0CuspCorrespondence N r s := by
  have hs := (gamma0CuspTrueWidth_translation_iff N s _).mpr (dvd_mul_right _ l)
  have hr := (gamma0CuspTrueWidth_translation_iff N r _).mpr (dvd_mul_right _ k)
  have h := (CongruenceSubgroup.Gamma0 N).mul_mem
    ((CongruenceSubgroup.Gamma0 N).mul_mem hs hM) hr
  change s⁻¹ * (integerTranslation ((gamma0CuspTrueWidth N s : ℤ) * l) * M *
    integerTranslation ((gamma0CuspTrueWidth N r : ℤ) * k)) * r ∈ CongruenceSubgroup.Gamma0 N
  convert h using 1
  group

def gamma0TrueWidthReducedMatrix (N : ℕ) [NeZero N] (r s : SL(2, ℤ)) (c : ℕ) :=
  {M : SL(2, ℤ) // M ∈ gamma0CuspCorrespondence N r s ∧ M 1 0 = (c : ℤ) ∧
    0 ≤ M 0 0 ∧ M 0 0 < (gamma0CuspTrueWidth N s : ℤ) * c ∧
    0 ≤ M 1 1 ∧ M 1 1 < (gamma0CuspTrueWidth N r : ℤ) * c}

theorem integer_interval_translate_unique {L x y a b : ℤ} (hL : 0 < L)
    (hx : 0 ≤ x ∧ x < L) (hy : 0 ≤ y ∧ y < L)
    (h : x + L * a = y + L * b) : x = y ∧ a = b := by
  have hm := congrArg (fun z : ℤ => z % L) h
  simp only [Int.add_emod, Int.mul_emod, Int.emod_self, zero_mul,
    Int.zero_emod, add_zero,
    Int.emod_eq_of_lt hx.1 hx.2, Int.emod_eq_of_lt hy.1 hy.2] at hm
  refine ⟨hm,?_⟩
  apply mul_left_cancel₀ hL.ne'
  omega

theorem gamma0TrueWidthReducedMatrix_diagonal_injective (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] :
    Function.Injective (fun R : gamma0TrueWidthReducedMatrix N r s c =>
      ((R.val 0 0 : ZMod (gamma0CuspTrueWidth N s * c)),
        (R.val 1 1 : ZMod (gamma0CuspTrueWidth N r * c)))) := by
  intro M R h
  have hA := (ZMod.intCast_eq_intCast_iff _ _ _).mp (congrArg Prod.fst h)
  have hD := (ZMod.intCast_eq_intCast_iff _ _ _).mp (congrArg Prod.snd h)
  have hA' : M.val 0 0 = R.val 0 0 := by
    change M.val 0 0 % ((gamma0CuspTrueWidth N s * c : ℕ) : ℤ) =
      R.val 0 0 % ((gamma0CuspTrueWidth N s * c : ℕ) : ℤ) at hA
    push_cast at hA
    simpa only [Int.emod_eq_of_lt M.property.2.2.1 M.property.2.2.2.1,
      Int.emod_eq_of_lt R.property.2.2.1 R.property.2.2.2.1] using hA
  have hD' : M.val 1 1 = R.val 1 1 := by
    change M.val 1 1 % ((gamma0CuspTrueWidth N r * c : ℕ) : ℤ) =
      R.val 1 1 % ((gamma0CuspTrueWidth N r * c : ℕ) : ℤ) at hD
    push_cast at hD
    simpa only [Int.emod_eq_of_lt M.property.2.2.2.2.1 M.property.2.2.2.2.2,
      Int.emod_eq_of_lt R.property.2.2.2.2.1 R.property.2.2.2.2.2] using hD
  apply Subtype.ext
  exact specialLinear_eq_of_diagonal_lower (by exact_mod_cast NeZero.ne c)
    M.val R.val M.property.2.1 R.property.2.1 hA' hD'

instance gamma0TrueWidthReducedMatrix_finite (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] :
    Finite (gamma0TrueWidthReducedMatrix N r s c) := by
  let _ : NeZero (gamma0CuspTrueWidth N s * c) :=
    ⟨Nat.mul_ne_zero (gamma0CuspTrueWidth_pos N s).ne' (NeZero.ne c)⟩
  let _ : NeZero (gamma0CuspTrueWidth N r * c) :=
    ⟨Nat.mul_ne_zero (gamma0CuspTrueWidth_pos N r).ne' (NeZero.ne c)⟩
  exact Finite.of_injective _ (gamma0TrueWidthReducedMatrix_diagonal_injective N r s c)

instance gamma0TrueWidthReducedMatrix_fintype (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] :
    Fintype (gamma0TrueWidthReducedMatrix N r s c) := Fintype.ofFinite _

def gamma0TrueWidthDoubleCosetExpand (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ)
    (p : gamma0TrueWidthReducedMatrix N r s c × ℤ × ℤ) :
    gamma0CuspMatrixFibre N r s c :=
  ⟨integerTranslation ((gamma0CuspTrueWidth N s : ℤ) * p.2.1) * p.1.val *
      integerTranslation ((gamma0CuspTrueWidth N r : ℤ) * p.2.2),
    gamma0CuspCorrespondence_trueWidth_translate N r s p.1.val p.1.property.1 p.2.1 p.2.2,
    (integerTranslation_entries _ _ p.1.val).2.1.trans p.1.property.2.1⟩

theorem gamma0TrueWidthDoubleCosetExpand_surjective (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] :
    Function.Surjective (gamma0TrueWidthDoubleCosetExpand N r s c) := by
  intro M
  let L : ℤ := (gamma0CuspTrueWidth N s : ℤ) * c
  let K : ℤ := (gamma0CuspTrueWidth N r : ℤ) * c
  have hL : 0 < L := mul_pos (by exact_mod_cast gamma0CuspTrueWidth_pos N s)
    (by exact_mod_cast NeZero.pos c)
  have hK : 0 < K := mul_pos (by exact_mod_cast gamma0CuspTrueWidth_pos N r)
    (by exact_mod_cast NeZero.pos c)
  let l : ℤ := -(M.val 0 0 / L)
  let k : ℤ := -(M.val 1 1 / K)
  let R := integerTranslation ((gamma0CuspTrueWidth N s : ℤ) * l) * M.val *
    integerTranslation ((gamma0CuspTrueWidth N r : ℤ) * k)
  obtain ⟨hRA,hRC,hRD⟩ := integerTranslation_entries
    ((gamma0CuspTrueWidth N s : ℤ) * l) ((gamma0CuspTrueWidth N r : ℤ) * k) M.val
  have hA : R 0 0 = M.val 0 0 % L := by
    rw [hRA,M.property.2]
    have he := Int.emod_add_ediv_mul (M.val 0 0) L
    dsimp [l,L] at *
    nlinarith
  have hD : R 1 1 = M.val 1 1 % K := by
    rw [hRD,M.property.2]
    have he := Int.emod_add_ediv_mul (M.val 1 1) K
    dsimp [k,K] at *
    nlinarith
  let R₀ : gamma0TrueWidthReducedMatrix N r s c := ⟨R,
    gamma0CuspCorrespondence_trueWidth_translate N r s M.val M.property.1 l k,
    hRC.trans M.property.2,
    (by rw [hA]; exact Int.emod_nonneg _ hL.ne'),
    (by rw [hA]; exact Int.emod_lt_of_pos _ hL),
    (by rw [hD]; exact Int.emod_nonneg _ hK.ne'),
    (by rw [hD]; exact Int.emod_lt_of_pos _ hK)⟩
  refine ⟨(R₀,-l,-k),?_⟩
  apply Subtype.ext
  change integerTranslation ((gamma0CuspTrueWidth N s : ℤ) * -l) * R *
    integerTranslation ((gamma0CuspTrueWidth N r : ℤ) * -k) = M.val
  dsimp [R]
  simp only [mul_neg,integerTranslation_neg]
  group

theorem gamma0TrueWidthDoubleCosetExpand_injective (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] :
    Function.Injective (gamma0TrueWidthDoubleCosetExpand N r s c) := by
  rintro ⟨R,l,k⟩ ⟨S,a,b⟩ h
  have hA := congrArg (fun M : gamma0CuspMatrixFibre N r s c => M.val 0 0) h
  have hD := congrArg (fun M : gamma0CuspMatrixFibre N r s c => M.val 1 1) h
  change (integerTranslation ((gamma0CuspTrueWidth N s : ℤ) * l) * R.val *
    integerTranslation ((gamma0CuspTrueWidth N r : ℤ) * k)) 0 0 =
    (integerTranslation ((gamma0CuspTrueWidth N s : ℤ) * a) * S.val *
    integerTranslation ((gamma0CuspTrueWidth N r : ℤ) * b)) 0 0 at hA
  change (integerTranslation ((gamma0CuspTrueWidth N s : ℤ) * l) * R.val *
    integerTranslation ((gamma0CuspTrueWidth N r : ℤ) * k)) 1 1 =
    (integerTranslation ((gamma0CuspTrueWidth N s : ℤ) * a) * S.val *
    integerTranslation ((gamma0CuspTrueWidth N r : ℤ) * b)) 1 1 at hD
  rw [(integerTranslation_entries _ _ _).1,(integerTranslation_entries _ _ _).1,
    R.property.2.1,S.property.2.1] at hA
  rw [(integerTranslation_entries _ _ _).2.2,(integerTranslation_entries _ _ _).2.2,
    R.property.2.1,S.property.2.1] at hD
  have hL : 0 < (gamma0CuspTrueWidth N s : ℤ) * c := mul_pos
    (by exact_mod_cast gamma0CuspTrueWidth_pos N s) (by exact_mod_cast NeZero.pos c)
  have hK : 0 < (gamma0CuspTrueWidth N r : ℤ) * c := mul_pos
    (by exact_mod_cast gamma0CuspTrueWidth_pos N r) (by exact_mod_cast NeZero.pos c)
  have ha := integer_interval_translate_unique hL
    ⟨R.property.2.2.1,R.property.2.2.2.1⟩
    ⟨S.property.2.2.1,S.property.2.2.2.1⟩
    (show R.val 0 0 + ((gamma0CuspTrueWidth N s : ℤ)*c)*l =
      S.val 0 0 + ((gamma0CuspTrueWidth N s : ℤ)*c)*a by nlinarith [hA])
  have hd := integer_interval_translate_unique hK
    ⟨R.property.2.2.2.2.1,R.property.2.2.2.2.2⟩
    ⟨S.property.2.2.2.2.1,S.property.2.2.2.2.2⟩
    (show R.val 1 1 + ((gamma0CuspTrueWidth N r : ℤ)*c)*k =
      S.val 1 1 + ((gamma0CuspTrueWidth N r : ℤ)*c)*b by nlinarith [hD])
  have hRS : R = S := Subtype.ext (specialLinear_eq_of_diagonal_lower
    (by exact_mod_cast NeZero.ne c) R.val S.val R.property.2.1 S.property.2.1 ha.1 hd.1)
  exact Prod.ext hRS (Prod.ext ha.2 hd.2)

def gamma0TrueWidthDoubleCosetEquiv (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] :
    (gamma0TrueWidthReducedMatrix N r s c × ℤ × ℤ) ≃ gamma0CuspMatrixFibre N r s c :=
  Equiv.ofBijective _ ⟨gamma0TrueWidthDoubleCosetExpand_injective N r s c,
    gamma0TrueWidthDoubleCosetExpand_surjective N r s c⟩

end ArtinMatthews
