module

public import ArtinMatthews.SourceJacquetFiniteUpperQuotient
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Orthogonality on the actual finite quotient of the retained-place
Jacquet ball. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain StandardAdelic SourcePhysical
open scoped NumberField SourcePhysical BigOperators Classical

noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))

local notation "L" => P.adicCompletion K
local notation "B" => sourceLocalBall K P
local notation "ψ" => localFiniteCharacter K P
local notation "Q" => SourceJacquetUpperQuotient K P
local notation "U" => sourceJacquetUpperBall K P
local notation "red" => sourceJacquetUpperReduction K P
local notation "rep" => sourceJacquetUpperRepresentative K P

instance sourceKPRetainedUpperQuotient_fintype (R M : ℕ) : Fintype (Q R M) :=
  letI := sourceJacquetUpperQuotient_finite K P R M
  Fintype.ofFinite _

private def quotientChar (R M : ℕ) (y : L)
    (hsmall : ∀ x ∈ B (-(M:ℤ)), ψ (y*x) = 1) : AddChar (Q R M) ℂ where
  toFun := Quotient.lift (fun x : U R => ψ (y * (x : L))) (by
    intro x z hx
    have he : red R M x = red R M z := Quotient.sound hx
    have hd : (z : L) - (x : L) ∈ B (-(M:ℤ)) :=
      (sourceJacquetUpperReduction_eq_iff K P R M x z).mp he
    calc
      _ = ψ (y * (x : L)) * ψ (y * ((z : L) - (x : L))) := by rw [hsmall _ hd, mul_one]
      _ = _ := by rw [← AddChar.map_add_eq_mul]; congr 1; ring)
  map_zero_eq_one' := by
    change ψ (y * 0) = 1
    rw [mul_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' := by
    intro x z
    refine Quotient.inductionOn₂ x z fun a b => ?_
    change ψ (y * ((a : L)+(b : L))) = ψ (y*(a:L)) * ψ (y*(b:L))
    rw [mul_add, AddChar.map_add_eq_mul]

private theorem quotientChar_eq_zero_iff (R M : ℕ) (y : L)
    (hsmall : ∀ x ∈ B (-(M:ℤ)), ψ (y*x) = 1) :
    quotientChar K P R M y hsmall = 0 ↔ y ∈ B ((sourceDifferentExponent K P:ℤ)-(R:ℤ)) := by
  rw [← sourceLocalBall_annihilator_iff K P (R:ℤ) y]
  constructor
  · intro h x hx
    exact DFunLike.congr_fun h (red R M (⟨x,hx⟩ : U R))
  · intro h
    apply AddChar.ext
    intro q
    calc
      quotientChar K P R M y hsmall q =
          quotientChar K P R M y hsmall (red R M (rep R M q)) :=
        congrArg _ (sourceJacquetUpperRepresentative_class K P R M q).symm
      _ = 1 := h _ (rep R M q).prop
      _ = (0 : AddChar (Q R M) ℂ) q := rfl

def sourceKPRetainedPhaseAverage (R M : ℕ) (y : L) : ℂ :=
  (Fintype.card (Q R M) : ℂ)⁻¹ * ∑ q : Q R M, ψ (y * (rep R M q : L))

theorem sourceKPRetainedPhaseAverage_eq_indicator (R M : ℕ) (y : L)
    (hsmall : ∀ x ∈ B (-(M:ℤ)), ψ (y*x) = 1) :
    sourceKPRetainedPhaseAverage K P R M y =
      if y ∈ B ((sourceDifferentExponent K P:ℤ)-(R:ℤ)) then 1 else 0 := by
  classical
  let χ := quotientChar K P R M y hsmall
  have he (q : Q R M) : ψ (y * (rep R M q : L)) = χ q :=
    congrArg χ (sourceJacquetUpperRepresentative_class K P R M q)
  unfold sourceKPRetainedPhaseAverage
  simp_rw [he]
  rw [AddChar.sum_eq_ite]
  have hiff := quotientChar_eq_zero_iff K P R M y hsmall
  by_cases hy : y ∈ B ((sourceDifferentExponent K P:ℤ)-(R:ℤ))
  · rw [if_pos (show χ = 0 from hiff.mpr hy), if_pos hy]
    exact inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)
  · rw [if_neg (show χ ≠ 0 from fun h => hy (hiff.mp h)), if_neg hy, mul_zero]

end
end ArtinMatthews
