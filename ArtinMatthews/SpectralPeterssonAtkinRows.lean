module

public import ArtinMatthews.SpectralCuspEisensteinWidthFormula
public import ArtinMatthews.SpectralPeterssonCuspRows
public import ArtinMatthews.SpectralABLSameCuspAtkinLehner
public import ArtinMatthews.SpectralCuspBruhatKernel
public import ArtinMatthews.SpectralCuspEisensteinInfinity
public import ArtinMatthews.SpectralCuspWidthNormalization
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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

/-! The actual signed Petersson rows under the exact-divisor Atkin–Lehner normalizer. -/

noncomputable section
open Matrix
open scoped MatrixGroups

namespace ArtinMatthews

def gamma0PeterssonGroupRow (N : ℕ) (a : SL(2, ℤ)) (γ : CongruenceSubgroup.Gamma0 N) :
    Gamma0PeterssonSignedRow N 1 a :=
  gamma0PeterssonRowOfMatrix N 1 a (gamma0CuspMatrixEquiv N 1 a γ)

private def gamma0PeterssonGroupRowRep (N : ℕ) (a : SL(2, ℤ))
    (p : Gamma0PeterssonSignedRow N 1 a) : CongruenceSubgroup.Gamma0 N :=
  (gamma0CuspMatrixEquiv N 1 a).symm (gamma0PeterssonRowMatrix N 1 a p)

private theorem gamma0PeterssonGroupRow_rep (N : ℕ) (a : SL(2, ℤ))
    (p : Gamma0PeterssonSignedRow N 1 a) :
    gamma0PeterssonGroupRow N a (gamma0PeterssonGroupRowRep N a p) = p := by
  unfold gamma0PeterssonGroupRow gamma0PeterssonGroupRowRep
  rw [Equiv.apply_symm_apply]
  exact Subtype.ext (gamma0PeterssonRowMatrix_row N 1 a p)

theorem gamma0PeterssonGroupRow_surjective (N : ℕ) (a : SL(2, ℤ)) :
    Function.Surjective (gamma0PeterssonGroupRow N a) :=
  fun p => ⟨gamma0PeterssonGroupRowRep N a p, gamma0PeterssonGroupRow_rep N a p⟩

def gamma0PeterssonGroupMatrix (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (γ : CongruenceSubgroup.Gamma0 N) : SL(2, ℝ) :=
  (gamma0TrueCuspScaling N a)⁻¹ * atkinRealMap γ.val

theorem gamma0PeterssonGroupMatrix_eq (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (γ : CongruenceSubgroup.Gamma0 N) :
    gamma0TrueWidthMatrix N 1 a (gamma0CuspMatrixEquiv N 1 a γ).val =
      gamma0PeterssonGroupMatrix N a γ := by
  change gamma0TrueWidthMatrix N 1 a (a * γ.val * (1 : SL(2, ℤ))⁻¹) = _
  rw [gamma0TrueWidthMatrix_correspondence, gamma0TrueCuspScaling_identity, mul_one]
  rfl

private theorem groupRow_eq_iff_real (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (γ η : CongruenceSubgroup.Gamma0 N) :
    gamma0PeterssonGroupRow N a γ = gamma0PeterssonGroupRow N a η ↔
      (fun j => gamma0PeterssonGroupMatrix N a γ 1 j) =
        fun j => gamma0PeterssonGroupMatrix N a η 1 j := by
  let M := (gamma0CuspMatrixEquiv N 1 a γ).val
  let R := (gamma0CuspMatrixEquiv N 1 a η).val
  let p := Real.sqrt (gamma0CuspTrueWidth N (1 : SL(2, ℤ)) : ℝ)
  let q := Real.sqrt (gamma0CuspTrueWidth N a : ℝ)
  have hp : p ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast gamma0CuspTrueWidth_pos N 1)).ne'
  have hq : q ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast gamma0CuspTrueWidth_pos N a)).ne'
  have hC (X : SL(2, ℤ)) :
      gamma0TrueWidthMatrix N 1 a X 1 0 = (X 1 0 : ℝ) * p * q :=
    (gamma0TrueWidthMatrix_entries N 1 a X).2.1
  have hD (X : SL(2, ℤ)) :
      gamma0TrueWidthMatrix N 1 a X 1 1 = (X 1 1 : ℝ) * q / p :=
    (gamma0TrueWidthMatrix_entries N 1 a X).2.2
  rw [← gamma0PeterssonGroupMatrix_eq N a γ, ← gamma0PeterssonGroupMatrix_eq N a η]
  change _ ↔ (fun j => gamma0TrueWidthMatrix N 1 a M 1 j) =
    fun j => gamma0TrueWidthMatrix N 1 a R 1 j
  constructor
  · intro h
    have hrow := congrArg Subtype.val h
    change (fun j => M 1 j) = (fun j => R 1 j) at hrow
    funext j
    fin_cases j
    · change gamma0TrueWidthMatrix N 1 a M 1 0 = gamma0TrueWidthMatrix N 1 a R 1 0
      rw [hC M, hC R, congrFun hrow 0]
    · change gamma0TrueWidthMatrix N 1 a M 1 1 = gamma0TrueWidthMatrix N 1 a R 1 1
      rw [hD M, hD R, congrFun hrow 1]
  · intro h
    have hc : gamma0TrueWidthMatrix N 1 a M 1 0 = gamma0TrueWidthMatrix N 1 a R 1 0 :=
      congrFun h 0
    have hd : gamma0TrueWidthMatrix N 1 a M 1 1 = gamma0TrueWidthMatrix N 1 a R 1 1 :=
      congrFun h 1
    rw [hC, hC] at hc
    rw [hD, hD] at hd
    have hd' := congrArg (fun x : ℝ => x * p) hd
    simp only [div_mul_cancel₀ _ hp] at hd'
    apply Subtype.ext
    change (fun j => M 1 j) = fun j => R 1 j
    funext j
    fin_cases j
    · exact_mod_cast mul_right_cancel₀ hp (mul_right_cancel₀ hq hc)
    · exact_mod_cast mul_right_cancel₀ hq hd'

/-- Conjugation by the actual Atkin–Lehner matrix on the integral congruence group. -/
def gamma0PeterssonAtkinConjugate (r s : ℕ) [NeZero r] {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (γ : CongruenceSubgroup.Gamma0 (r*s)) :
    CongruenceSubgroup.Gamma0 (r*s) :=
  ⟨Classical.choose (atkinScaling_normalizes_forward (NeZero.pos r) hab γ.val γ.property),
    (Classical.choose_spec (atkinScaling_normalizes_forward (NeZero.pos r) hab γ.val γ.property)).1⟩

theorem gamma0PeterssonAtkinConjugate_real (r s : ℕ) [NeZero r] {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (γ : CongruenceSubgroup.Gamma0 (r*s)) :
    atkinRealMap (gamma0PeterssonAtkinConjugate r s hab γ).val =
      (atkinScaling (NeZero.pos r) hab)⁻¹ * atkinRealMap γ.val * atkinScaling (NeZero.pos r) hab :=
  (Classical.choose_spec (atkinScaling_normalizes_forward (NeZero.pos r) hab γ.val γ.property)).2.symm

theorem gamma0PeterssonAtkinConjugate_surjective (r s : ℕ) [NeZero r] {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) :
    Function.Surjective (gamma0PeterssonAtkinConjugate r s hab) := by
  intro η
  obtain ⟨γ,hγ,he⟩ := atkinScaling_normalizes_backward (NeZero.pos r) hab η.val η.property
  refine ⟨⟨γ,hγ⟩, Subtype.ext (atkinRealMap_injective ?_)⟩
  rw [gamma0PeterssonAtkinConjugate_real]
  change (atkinScaling (NeZero.pos r) hab)⁻¹ * atkinRealMap γ * atkinScaling (NeZero.pos r) hab = _
  rw [← he]
  group

theorem gamma0PeterssonAtkinGroupMatrix (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (γ : CongruenceSubgroup.Gamma0 (r*s)) :
    gamma0PeterssonGroupMatrix (r*s) (gamma0CuspOneOver s) γ =
      realTranslation ((b : ℝ)/(r : ℝ)) *
        gamma0PeterssonGroupMatrix (r*s) 1 (gamma0PeterssonAtkinConjugate r s hab γ) *
        (atkinScaling (NeZero.pos r) hab)⁻¹ := by
  unfold gamma0PeterssonGroupMatrix
  rw [gamma0TrueCuspScaling_identity, inv_one, one_mul, gamma0PeterssonAtkinConjugate_real,
    gamma0AtkinSameCusp_scaling r s hcop hab]
  group

private theorem bottomRow_mul (A B : SL(2, ℝ)) :
    (fun j => (A * B) 1 j) = (fun j => A 1 j) ᵥ* B.val := rfl

private theorem bottomRow_translate (t : ℝ) (A : SL(2, ℝ)) :
    (fun j => (realTranslation t * A) 1 j) = fun j => A 1 j := by
  funext j
  change ((realTranslation t).val * A.val) 1 j = A 1 j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  change (0 : ℝ) * A 0 j + 1 * A 1 j = A 1 j
  simp

private theorem bottomRow_translate_mul (t : ℝ) (A B : SL(2, ℝ)) :
    (fun j => (realTranslation t * A * B) 1 j) = (fun j => A 1 j) ᵥ* B.val :=
  (bottomRow_mul (realTranslation t * A) B).trans
    (congrArg (fun v : Fin 2 → ℝ => v ᵥ* B.val) (bottomRow_translate t A))

private theorem atkin_groupRow_eq_iff (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (γ η : CongruenceSubgroup.Gamma0 (r*s)) :
    gamma0PeterssonGroupRow (r*s) (gamma0CuspOneOver s) γ =
      gamma0PeterssonGroupRow (r*s) (gamma0CuspOneOver s) η ↔
    gamma0PeterssonGroupRow (r*s) 1 (gamma0PeterssonAtkinConjugate r s hab γ) =
      gamma0PeterssonGroupRow (r*s) 1 (gamma0PeterssonAtkinConjugate r s hab η) := by
  rw [groupRow_eq_iff_real, groupRow_eq_iff_real]
  let W := atkinScaling (NeZero.pos r) hab
  let t : ℝ := (b : ℝ)/(r : ℝ)
  have hback (ξ : CongruenceSubgroup.Gamma0 (r*s)) :
      gamma0PeterssonGroupMatrix (r*s) 1 (gamma0PeterssonAtkinConjugate r s hab ξ) =
        realTranslation (-t) * gamma0PeterssonGroupMatrix (r*s) (gamma0CuspOneOver s) ξ * W := by
    rw [gamma0PeterssonAtkinGroupMatrix r s hcop hab ξ]
    change _ = realTranslation (-t) * (realTranslation t * _ * W⁻¹) * W
    rw [← mul_assoc (realTranslation (-t)), ← mul_assoc (realTranslation (-t)),
      realTranslation_mul, neg_add_cancel, realTranslation_zero, one_mul]
    group
  constructor
  · intro h
    rw [hback γ, hback η, bottomRow_translate_mul, bottomRow_translate_mul, h]
  · intro h
    rw [gamma0PeterssonAtkinGroupMatrix r s hcop hab γ, gamma0PeterssonAtkinGroupMatrix r s hcop hab η,
      bottomRow_translate_mul, bottomRow_translate_mul, h]

private def atkin_signedRowMap (r s : ℕ) [NeZero r] {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (p : Gamma0PeterssonSignedRow (r*s) 1 (gamma0CuspOneOver s)) :
    Gamma0PeterssonSignedRow (r*s) 1 1 :=
  gamma0PeterssonGroupRow (r*s) 1 (gamma0PeterssonAtkinConjugate r s hab
    (gamma0PeterssonGroupRowRep (r*s) (gamma0CuspOneOver s) p))

private theorem atkin_signedRowMap_groupRow (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (γ : CongruenceSubgroup.Gamma0 (r*s)) :
    atkin_signedRowMap r s hab (gamma0PeterssonGroupRow (r*s) (gamma0CuspOneOver s) γ) =
      gamma0PeterssonGroupRow (r*s) 1 (gamma0PeterssonAtkinConjugate r s hab γ) :=
  (atkin_groupRow_eq_iff r s hcop hab _ γ).1 (gamma0PeterssonGroupRow_rep _ _ _)

def gamma0PeterssonAtkinSignedRowEquiv (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1) :
    Gamma0PeterssonSignedRow (r*s) 1 (gamma0CuspOneOver s) ≃ Gamma0PeterssonSignedRow (r*s) 1 1 := by
  apply Equiv.ofBijective (atkin_signedRowMap r s hab)
  constructor
  · intro p q hpq
    have h := (atkin_groupRow_eq_iff r s hcop hab
      (gamma0PeterssonGroupRowRep _ _ p) (gamma0PeterssonGroupRowRep _ _ q)).2 hpq
    simpa only [gamma0PeterssonGroupRow_rep] using h
  · intro q
    obtain ⟨η,rfl⟩ := gamma0PeterssonGroupRow_surjective (r*s) 1 q
    obtain ⟨γ,rfl⟩ := gamma0PeterssonAtkinConjugate_surjective r s hab η
    exact ⟨gamma0PeterssonGroupRow (r*s) (gamma0CuspOneOver s) γ,
      atkin_signedRowMap_groupRow r s hcop hab γ⟩

theorem gamma0PeterssonAtkinSignedRowEquiv_groupRow (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (γ : CongruenceSubgroup.Gamma0 (r*s)) :
    gamma0PeterssonAtkinSignedRowEquiv r s hcop hab
        (gamma0PeterssonGroupRow (r*s) (gamma0CuspOneOver s) γ) =
      gamma0PeterssonGroupRow (r*s) 1 (gamma0PeterssonAtkinConjugate r s hab γ) :=
  atkin_signedRowMap_groupRow r s hcop hab γ

end ArtinMatthews
