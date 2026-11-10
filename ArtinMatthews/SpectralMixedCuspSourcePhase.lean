module

public import ArtinMatthews.SpectralMixedCuspReducedResidues
public import ArtinMatthews.SpectralTrueWidthKloosterman
public import ArtinMatthews.SpectralMixedCuspNormalization
public import ArtinMatthews.SpectralMixedCuspResidueInverse
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact identification with the actual ABL section 6 mixed arithmetic
kernel. The two frequency conventions are made explicit and the
inverse-s compensation is kept as a literal additive phase. -/

noncomputable section
open Matrix Set
open scoped MatrixGroups BigOperators
open OAI.Erdos970.ErdosKloosterman

namespace ArtinMatthews

theorem spectral_atkinPhase_integer_linear_mod {q : ℕ} [NeZero q] (m n A D : ℤ) :
    atkinPhase (((m : ℝ)*(A : ℝ)+(n : ℝ)*(D : ℝ))/(q : ℝ)) =
      ZMod.stdAddChar ((m : ZMod q)*(A : ZMod q)+(n : ZMod q)*(D : ZMod q)) := by
  simpa only [Int.cast_add,Int.cast_mul] using (stdAddChar_eq_atkinPhase (q := q) (m*A+n*D)).symm

theorem gamma0MixedReduced_phase_source (r s c : ℕ) [NeZero r] [NeZero s] [NeZero c]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (m n : ℤ)
    (R : gamma0TrueWidthReducedMatrix (r*s) (gamma0CuspOneOver s) 1 (s*c)) :
    let ad := (gamma0MixedReducedResiduePair r s c hab R).val
    cuspTrueWidthGeometricPhase (r*s) (gamma0CuspOneOver s) 1 n m (s*c : ℕ) R.val =
      atkinPhase (((m : ℝ)*(ad.1.val : ℝ)+(n : ℝ)*(ad.2.val : ℝ))/((s*c : ℕ) : ℝ)-
        (n : ℝ)*(b : ℝ)/(r : ℝ)) := by
  let q := s*c
  let A := R.val 0 0
  let D := R.val 1 1
  let d := gamma0MixedReducedShiftedRight r s c b R
  let ad := (gamma0MixedReducedResiduePair r s c hab R).val
  have hr : 0 < (r : ℝ) := Nat.cast_pos.mpr (NeZero.pos r)
  have hq : 0 < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos (s*c))
  have hD : (r : ℝ)*(d : ℝ) = (D : ℝ)+(q : ℝ)*(b : ℝ) := by
    exact_mod_cast gamma0MixedReduced_shifted_right_eq r s c hab R
  have he : (n : ℝ)*(D : ℝ)/((r : ℝ)*(q : ℝ))+(m : ℝ)*(A : ℝ)/(q : ℝ) =
      ((m : ℝ)*(A : ℝ)+(n : ℝ)*(d : ℝ))/(q : ℝ)+(-(n : ℝ)*(b : ℝ)/(r : ℝ)) := by
    field_simp [hr.ne',hq.ne']
    linear_combination -(n : ℝ)*hD
  have hph : atkinPhase (((m : ℝ)*(A : ℝ)+(n : ℝ)*(d : ℝ))/(q : ℝ)) =
      atkinPhase (((m : ℝ)*(ad.1.val : ℝ)+(n : ℝ)*(ad.2.val : ℝ))/(q : ℝ)) := by
    have hrep := spectral_atkinPhase_integer_linear_mod (q := q) m n (ad.1.val : ℤ) (ad.2.val : ℤ)
    have hrep' : atkinPhase (((m : ℝ)*(ad.1.val : ℝ)+(n : ℝ)*(ad.2.val : ℝ))/(q : ℝ)) =
        ZMod.stdAddChar ((m : ZMod q)*ad.1+(n : ZMod q)*ad.2) := by
      simpa only [Int.cast_natCast,ZMod.natCast_zmod_val] using hrep
    rw [spectral_atkinPhase_integer_linear_mod,hrep']
    rfl
  dsimp only
  unfold cuspTrueWidthGeometricPhase
  simp only [gamma0MixedCusp_trueWidth r s hcop,gamma0CuspTrueWidth_identity,Nat.cast_one,one_mul,Int.cast_natCast]
  change atkinPhase ((n : ℝ)*(D : ℝ)/((r : ℝ)*(q : ℝ))+(m : ℝ)*(A : ℝ)/(q : ℝ)) = _
  rw [he,atkinPhase_add,hph,← atkinPhase_add]
  congr 1
  dsimp only [ad,q]
  ring_nf

theorem gamma0MixedKloosterman_eq_source_lowerTri (r s c : ℕ) [NeZero r] [NeZero s] [NeZero c]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (m n : ℤ) :
    gamma0TrueWidthKloostermanSum (r*s) (gamma0CuspOneOver s) 1 (s*c) n m =
      lowerTriMixedResidueSum (NeZero.pos r) hab c m n := by
  classical
  unfold gamma0TrueWidthKloostermanSum lowerTriMixedResidueSum
  apply Finset.sum_bij (fun R _ => (gamma0MixedReducedResiduePair r s c hab R).val)
  · intro R _
    exact (gamma0MixedReducedResiduePair r s c hab R).property
  · intro R _ S _ h
    exact gamma0MixedReducedResiduePair_injective r s c hcop hab (Subtype.ext h)
  · intro ad had
    obtain ⟨R,hR⟩ := gamma0MixedReducedResiduePair_surjective r s c hcop hab ⟨ad,had⟩
    exact ⟨R,Finset.mem_univ _,congrArg Subtype.val hR⟩
  · intro R _
    exact gamma0MixedReduced_phase_source r s c hcop hab m n R

theorem gamma0MixedKloosterman_eq_source_ordinary (r s c : ℕ) [NeZero r] [NeZero s] [NeZero c]
    (hcop : r.Coprime s) (hrc : r.Coprime c) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (m n : ℤ) :
    let hrq : r.Coprime (s*c) := Nat.coprime_mul_iff_right.mpr ⟨hcop,hrc⟩
    gamma0TrueWidthKloostermanSum (r*s) (gamma0CuspOneOver s) 1 (s*c) n m =
      atkinPhase (-(n : ℝ)*(b : ℝ)/(r : ℝ))*
        sum ZMod.stdAddChar
          ((m : ZMod (s*c))*(((ZMod.unitOfCoprime r hrq)⁻¹ : (ZMod (s*c))ˣ) : ZMod (s*c)))
          (n : ZMod (s*c)) := by
  dsimp only
  rw [gamma0MixedKloosterman_eq_source_lowerTri r s c hcop hab]
  exact lowerTriMixedResidueSum_eq_ordinary (NeZero.pos r) hab c
    (Nat.coprime_mul_iff_right.mpr ⟨hcop,hrc⟩) m n

theorem gamma0MixedKloosterman_source_compensation (r s c : ℕ) [NeZero r] [NeZero s] [NeZero c]
    (hcop : r.Coprime s) (hrc : r.Coprime c) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (m n : ℤ) :
    let hrq : r.Coprime (s*c) := Nat.coprime_mul_iff_right.mpr ⟨hcop,hrc⟩
    atkinPhase ((n : ℝ)*(b : ℝ)/(r : ℝ))*
        gamma0TrueWidthKloostermanSum (r*s) (gamma0CuspOneOver s) 1 (s*c) n m =
      sum ZMod.stdAddChar
        ((m : ZMod (s*c))*(((ZMod.unitOfCoprime r hrq)⁻¹ : (ZMod (s*c))ˣ) : ZMod (s*c)))
        (n : ZMod (s*c)) := by
  dsimp only
  rw [gamma0MixedKloosterman_eq_source_ordinary r s c hcop hrc hab,← mul_assoc,← atkinPhase_add]
  have he : (n : ℝ)*(b : ℝ)/(r : ℝ)+(-(n : ℝ)*(b : ℝ)/(r : ℝ)) = 0 := by ring_nf
  rw [he]
  simp [atkinPhase]

theorem gamma0MixedKloosterman_zero_off_source_moduli (r s q : ℕ) [NeZero r] [NeZero s] [NeZero q]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (m n : ℤ)
    (h : ¬ ∃ c : ℕ, 0 < c ∧ q = s*c ∧ r.Coprime c) :
    gamma0TrueWidthKloostermanSum (r*s) (gamma0CuspOneOver s) 1 q n m = 0 := by
  let _ : IsEmpty (gamma0TrueWidthReducedMatrix (r*s) (gamma0CuspOneOver s) 1 q) :=
    ⟨fun R => h ((gamma0MixedReduced_nonempty_iff r s q hcop hab).mp ⟨R⟩)⟩
  simp only [gamma0TrueWidthKloostermanSum,Finset.univ_eq_empty,Finset.sum_empty]

end ArtinMatthews
