module

public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaFourier
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Generator compatibility of the actual finite trace labels. This relates
all ideal classes to the same direct residue on dual(M), a necessary step
for a common, rather than class-dependent, Hecke root number. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)

/-- The direct residue of a trace frequency on O/M. -/
def idealTraceDualResidue
    (β : (dual ℤ ℚ (M : FractionalIdeal (𝓞 K)⁰ K)).val) : (𝓞 K) ⧸ M :=
  idealModuleDualResidue K ⊤ M top_ne_bot hM β
    (by rw [Ideal.mul_top]; exact β.property) *
      idealResidueCoordinate ⊤ M top_ne_bot hM (⟨1,by trivial⟩ : (⊤ : Ideal (𝓞 K)))

theorem idealTraceDualResidue_character
    (β : (dual ℤ ℚ (M : FractionalIdeal (𝓞 K)⁰ K)).val) (a : 𝓞 K) :
    fieldTraceAddChar K β a = idealTraceAddChar K M hM
      (idealTraceDualResidue K M hM β * Ideal.Quotient.mk M a) := by
  let a' : (⊤ : Ideal (𝓞 K)) := ⟨a,by trivial⟩
  let one' : (⊤ : Ideal (𝓞 K)) := ⟨1,by trivial⟩
  have ha : a' = a • one' := by apply Subtype.ext; simp [a',one']
  have H := idealModuleDualResidue_character K ⊤ M top_ne_bot hM β
    (by rw [Ideal.mul_top]; exact β.property) a'
  change fieldTraceAddChar K β a = _ at H
  rw [H,ha,map_smul]
  congr 1
  change idealModuleDualResidue K ⊤ M top_ne_bot hM β _ *
      (Ideal.Quotient.mk M a * idealResidueCoordinate ⊤ M top_ne_bot hM one') = _
  unfold idealTraceDualResidue
  ring

variable (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)

def idealModuleGeneratorDualMap
    (β : (dual ℤ ℚ ((M*I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)).val) :
    (dual ℤ ℚ (M : FractionalIdeal (𝓞 K)⁰ K)).val :=
  ⟨(β : K) * (idealModuleGenerator I M hI hM : 𝓞 K), by
    change (β : K) * (idealModuleGenerator I M hI hM : 𝓞 K) ∈
      dual ℤ ℚ (M : FractionalIdeal (𝓞 K)⁰ K)
    rw [FractionalIdeal.mem_dual (FractionalIdeal.coeIdeal_ne_zero.mpr hM)]
    intro y hy
    obtain ⟨a,ha,rfl⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hy
    have hprod : a * idealModuleGenerator I M hI hM ∈ M*I :=
      Ideal.mul_mem_mul ha (idealModuleGenerator_mem I M hI hM)
    have H := (FractionalIdeal.mem_dual
      (FractionalIdeal.coeIdeal_ne_zero.mpr (mul_ne_zero hM hI))).mp β.property
        ((a * idealModuleGenerator I M hI hM : 𝓞 K) : K)
        (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ hprod)
    have he : ((β : K) * (idealModuleGenerator I M hI hM : 𝓞 K)) * (a : K) =
        (β : K) * ((a * idealModuleGenerator I M hI hM : 𝓞 K) : K) := by
      push_cast
      ring
    change Algebra.trace ℚ K (((β : K) * (idealModuleGenerator I M hI hM : 𝓞 K)) *
      (a : K)) ∈ (algebraMap ℤ ℚ).range
    rw [he]
    exact H⟩

/-- Exact compatibility with the canonical module generator: all varying
ideal labels reduce to the same direct trace-residue coordinate on dual(M). -/
theorem idealModuleDualResidue_generator
    (β : (dual ℤ ℚ ((M*I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)).val) :
    idealModuleDualResidue K I M hI hM β β.property =
      idealTraceDualResidue K M hM (idealModuleGeneratorDualMap K M hM I hI β) := by
  apply AddChar.to_mulShift_inj_of_isPrimitive (idealTraceAddChar_isPrimitive K M hM)
  ext x
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  let g : I := ⟨idealModuleGenerator I M hI hM,idealModuleGenerator_mem I M hI hM⟩
  have H := idealModuleDualResidue_character K I M hI hM β β.property (a • g)
  have hg : idealResidueCoordinate I M hI hM g = 1 :=
    idealResidueCoordinate_generator I M hI hM
  rw [(idealResidueCoordinate I M hI hM).map_smul, hg] at H
  change idealModuleTraceChar K I β (a • g) =
    idealTraceAddChar K M hM (idealModuleDualResidue K I M hI hM β β.property *
      (Ideal.Quotient.mk M a * 1)) at H
  rw [mul_one] at H
  change idealTraceAddChar K M hM
    (idealModuleDualResidue K I M hI hM β β.property * Ideal.Quotient.mk M a) = _
  simp only [AddChar.mulShift_apply]
  rw [← H, ← idealTraceDualResidue_character]
  simp only [idealModuleTraceChar_apply,fieldTraceAddChar_apply]
  congr 3
  congr 1
  change (β : K) * ((a * idealModuleGenerator I M hI hM : 𝓞 K) : K) =
    ((β : K) * (idealModuleGenerator I M hI hM : 𝓞 K)) * (a : K)
  push_cast
  ring

end
end ArtinMatthews.VaryingKummerAnalytic
