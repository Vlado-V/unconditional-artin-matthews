module

public import ArtinMatthews.SourceActualCrossCancellation
public import ArtinMatthews.SourceKPExteriorCofactor
public import ArtinMatthews.SourceReflectionExpansion
public import ArtinMatthews.SourceKPSIntegerLocalResidue
public import ArtinMatthews.SourceQuadraticHeckeSymbols
public import ArtinMatthews.SourceQuadraticPrimeResidue
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Directed characters of the literal omitted-prime generators. -/

namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain VaryingKummerAnalytic AllowedGenerators
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
  (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

local notation "E" => SourcePrimeExponents F S₀
local notation "Pr" => SourceExteriorPrime F S₀
local notation "X" => sourcePrimeCrossDiagonalUnit F hζ S₀
local notation "C" => reflectionPrimeCrossCharacter F hζ S₀

def sourceReflectionDirectedCofactor (P : Pr) (e : E) : ℂˣ :=
  e.prod fun Q m => X P Q ^ m

local notation "D" => sourceReflectionDirectedCofactor F S₀ hζ

theorem sourceReflectionDirectedCofactor_add (P : Pr) (e f : E) :
    D P (e + f) = D P e * D P f :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem sourceReflectionDirectedCofactor_nsmul (P : Pr) (n : ℕ) (e : E) :
    D P (n • e) = D P e ^ n := by
  induction n with
  | zero => simp [sourceReflectionDirectedCofactor]
  | succ n ih => rw [succ_nsmul, sourceReflectionDirectedCofactor_add, ih, pow_succ]

theorem sourceReflectionDirectedCofactor_pow_six (P : Pr) (e : E) :
    D P e ^ 6 = 1 := by
  unfold sourceReflectionDirectedCofactor Finsupp.prod
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro Q _
  rw [pow_right_comm, sourcePrimeCrossDiagonalUnit_pow_six, one_pow]

theorem sourceReflectionDirectedCofactor_norm (P : Pr) (e : E) :
    ‖(D P e : ℂ)‖ = 1 := by
  apply Complex.norm_eq_one_of_mem_rootsOfUnity (n := 6)
  rw [mem_rootsOfUnity]
  exact sourceReflectionDirectedCofactor_pow_six F S₀ hζ P e

theorem sourceReflectionDirectedCofactor_val (P : Pr) (e : E) :
    (D P e : ℂ) = ∏ Q ∈ e.support.erase P, C P Q ^ e Q := by
  unfold sourceReflectionDirectedCofactor Finsupp.prod
  rw [show (↑(∏ Q ∈ e.support, X P Q ^ e Q) : ℂ) = _ from
    map_prod (Units.coeHom ℂ) _ _]
  have hd : (↑(X P P ^ e P) : ℂ) = 1 := by
    rw [sourcePrimeCrossDiagonalUnit_diag, one_pow, Units.val_one]
  calc
    _ = ∏ Q ∈ e.support.erase P, (↑(X P Q ^ e Q) : ℂ) :=
      (Finset.prod_erase e.support (f := fun Q : Pr => (↑(X P Q ^ e Q) : ℂ)) hd).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro Q hQ
      rw [sourcePrimeCrossDiagonalUnit, dite_eq_right (Finset.mem_erase.mp hQ).1.symm,
        Units.val_pow_eq_pow_val, sourcePrimeCrossUnit_val]

theorem sourceReflectionDirectedCofactor_eq_residue (P : Pr) (e : E) :
    (D P e : ℂ) = reflectionPrimeCharacters F hζ S₀ P
      (sourceKPLocalUnitResidue F P.val (sourceKPCompletedExponentUnit F hζ S₀ P (e.erase P))
        (sourceKPCompletedExponentUnit_erase_valuation F hζ S₀ P e)) := by
  rw [sourceReflectionDirectedCofactor_val,
    sourceKPCompletedExponentUnit_erase_character F hζ S₀ P e e.support (Finset.Subset.refl _)]

theorem sourceReflectionDirectedCofactor_eq_exponent_residue (d : ReflectionSquarefreeExponents F S₀)
    (c : E) (hdc : Disjoint d.val.support c.support) :
    (↑(∏ P ∈ d.val.support, D P c) : ℂ) =
      reflectionExponentResidueValue F hζ S₀ d.val (sourcePrimeExponentGenerator F hζ S₀ c) := by
  unfold reflectionExponentResidueValue sourcePrimeExponentWeight Finsupp.prod
  rw [show (↑(∏ P ∈ d.val.support, D P c) : ℂ) = _ from
    map_prod (Units.coeHom ℂ) _ _]
  apply Finset.prod_congr rfl
  intro P hP
  have hP0 : P ∉ c.support := Finset.disjoint_left.mp hdc hP
  have hP1 := reflectionSquarefreeExponent_support_one F S₀ d ⟨P, hP⟩
  change (D P c : ℂ) = sourcePrimeExponentLocalWeight F hζ S₀
    (reflectionPrimeCharacters F hζ S₀) P (d.val P) (sourcePrimeExponentGenerator F hζ S₀ c)
  rw [hP1]
  refine Eq.trans ?_ (sourceQuadraticLocalWeight_positive F S₀ hζ P 1 Nat.one_pos
    (sourcePrimeExponentGenerator F hζ S₀ c)).symm
  rw [pow_one, sourceReflectionDirectedCofactor_eq_residue,
    sourceKPLocalUnitResidue_eq_sInteger F hζ S₀ P
      (sourcePrimeExponentGenerator F hζ S₀ (c.erase P)) _ _
      (sourceKPCompletedExponentUnit_val F hζ S₀ P _),
    Finsupp.erase_of_notMem_support hP0]
  rfl

/-- The row-to-column exponent is one and the column-to-row exponent is
minus four. Reciprocity gives the cube of the actual exterior residue. -/
theorem sourceReflectionDirectedCofactor_pairing (d c : ReflectionSquarefreeExponents F S₀)
    (hdc : Disjoint d.val.support c.val.support) :
    (↑((∏ P ∈ d.val.support, D P c.val) *
      (∏ Q ∈ c.val.support, D Q d.val ^ (-4 : ℤ))) : ℂ) =
      sourceReflectionQuadraticSymbol F S₀ hζ d.val c.val := by
  let U : ℂˣ := ∏ P ∈ d.val.support, D P c.val
  let V : ℂˣ := ∏ Q ∈ c.val.support, D Q d.val
  have hUV : U = V := by
    apply Units.ext
    rw [sourceReflectionDirectedCofactor_eq_exponent_residue F S₀ hζ d c.val hdc,
      sourceReflectionDirectedCofactor_eq_exponent_residue F S₀ hζ c d.val hdc.symm]
    exact sourceReflectionExponentResidueValue_symmetric F S₀ hζ d.val c.val
  have hU6 : U ^ (6 : ℤ) = 1 := by
    rw [show (6 : ℤ) = ((6 : ℕ) : ℤ) from rfl, zpow_natCast]
    change (∏ P ∈ d.val.support, D P c.val) ^ 6 = 1
    rw [← Finset.prod_pow]
    simp only [sourceReflectionDirectedCofactor_pow_six, Finset.prod_const_one]
  change (↑(U * (∏ Q ∈ c.val.support, D Q d.val ^ (-4 : ℤ))) : ℂ) = _
  rw [Finset.prod_zpow]
  change (↑(U * V ^ (-4 : ℤ)) : ℂ) = _
  have hpower : U * U ^ (-4 : ℤ) = U ^ (3 : ℕ) := by
    calc
      _ = U ^ ((1 : ℤ) + -4) := by simpa only [zpow_one] using (zpow_add U 1 (-4)).symm
      _ = U ^ (3 : ℕ) := by
        rw [show (1 : ℤ) + -4 = ((3 : ℕ) : ℤ) - 6 by decide, zpow_sub, hU6,
          inv_one, mul_one, zpow_natCast]
  rw [← hUV, hpower, Units.val_pow_eq_pow_val]
  change (↑(∏ P ∈ d.val.support, D P c.val) : ℂ) ^ 3 = _
  rw [sourceReflectionDirectedCofactor_eq_exponent_residue F S₀ hζ d c.val hdc]
  rfl

theorem sourceReflectionQuadraticSymbol_eq_zero_of_not_disjoint (d c : E)
    (h : ¬ Disjoint d.support c.support) :
    sourceReflectionQuadraticSymbol F S₀ hζ d c = 0 :=
  not_ne_iff.mp (fun hz => h ((sourceReflectionQuadraticSymbol_ne_zero_iff F S₀ hζ d c).mp hz))

end
end ArtinMatthews.SourceEulerAssembly
