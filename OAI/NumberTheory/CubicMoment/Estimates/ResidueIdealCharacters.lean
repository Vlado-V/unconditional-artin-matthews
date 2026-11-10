module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.CubicMoment.Estimates.PrimitiveConductor
public import OAI.NumberTheory.CubicMoment.Estimates.IdealEulerExclusion
public import OAI.NumberTheory.CubicMoment.Estimates.PrimaryHeckeCharacter
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.NumberTheory.CubicGram.IntegerBasis
public import OAI.NumberTheory.CubicMoment.Estimates.IdealMellinSeries
public import OAI.NumberTheory.CubicMoment.Estimates.PrimeToThreeIdeals


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! The finite residue character as an actual complete ideal character,
and exact restoration of Euler factors after primitive reduction. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def residueIdealChar (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (ν : EisensteinIdealExponent) : ℂ :=
  χ (Ideal.Quotient.mk (modulus q) (idealExponentGenerator ν))

lemma residueIdealChar_add (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (ν κ : EisensteinIdealExponent) :
    residueIdealChar q χ (ν+κ) = residueIdealChar q χ ν*residueIdealChar q χ κ := by
  simp only [residueIdealChar,idealExponentGenerator_add,map_mul]

lemma residueChar_norm_le_one {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (x : Residues q) : ‖χ x‖ ≤ 1 := by
  let : Finite (Residues q) := finite_residues hq
  let : Fintype (Residues q) := Fintype.ofFinite _
  by_cases hx : IsUnit x
  · obtain ⟨u,rfl⟩ := hx
    have he : ‖χ (u : Residues q)‖ = 1 :=
      Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)
    exact he.le
  · rw [MulChar.map_nonunit χ hx,norm_zero]
    exact zero_le_one

lemma residueIdealChar_norm_le_one {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (ν : EisensteinIdealExponent) :
    ‖residueIdealChar q χ ν‖ ≤ 1 := residueChar_norm_le_one hq χ _

lemma residueIdealChar_primaryMixed {a b : Eisenstein}
    (ha : primary a) (hb : primary b) (ν : EisensteinIdealExponent) :
    residueIdealChar (3*(a*b)) (primaryMixedResidueChar a b ha hb) ν =
      primaryMixedIdealChar a b ν := primaryMixedResidueChar_mk ha hb _

lemma ideal_coprime_support {q : Eisenstein} (hq : q ≠ 0)
    (ν : EisensteinIdealExponent) :
    IsCoprime q (idealExponentGenerator ν) ↔
      ∀ p ∈ (idealExponentOf q).support, ν p = 0 := by
  rw [isCoprime_comm,isCoprime_iff_idealExponent_disjoint (idealExponentGenerator_ne_zero ν) hq,
    idealExponentOf_generator]
  constructor
  · intro h p hp
    rcases h p with hn | hq
    · exact hn
    · exact False.elim ((Finsupp.mem_support_iff.mp hp) hq)
  · intro h p
    by_cases hp : p ∈ (idealExponentOf q).support
    · exact Or.inl (h p hp)
    · exact Or.inr (Finsupp.notMem_support_iff.mp hp)

lemma induced_residueIdealChar {q d : Eisenstein} (hq : q ≠ 0)
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ) (ν : EisensteinIdealExponent) :
    residueIdealChar q χ ν =
      if ∀ p ∈ (idealExponentOf q).support, ν p = 0 then residueIdealChar d ψ ν else 0 := by
  simpa only [residueIdealChar,ideal_coprime_support hq] using
    h.restriction (idealExponentGenerator ν)

/-- Primitive reduction gives an exact finite Euler inclusion-exclusion
for the original complete smooth sum, with every rescaling retained. -/
theorem induced_residue_smooth_euler {q d : Eisenstein} (hq : q ≠ 0)
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) {Z : ℝ} (hZ : 0 < Z) :
    (∑' ν, residueIdealChar q χ ν*W (idealExponentNorm ν/Z)) =
      ∑ T ∈ (idealExponentOf q).support.powerset,
        (-1:ℂ)^T.card*residueIdealChar d ψ (primeSetExponent T)*
          ∑' κ, residueIdealChar d ψ κ*
            W (idealExponentNorm κ/(Z/idealExponentNorm (primeSetExponent T))) := by
  have he := smooth_ideal_euler_exclusion (idealExponentOf q).support (residueIdealChar d ψ)
    (residueIdealChar_add d ψ) W hW hZ
  rw [← he]
  apply tsum_congr
  intro ν
  rw [induced_residueIdealChar hq h]
  split <;> simp

end CubicFirstMoment

end

end OAI
